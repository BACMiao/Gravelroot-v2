#
# Copyright (c) 2020 Vitalis Salis.
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
import os
import time
import yaml
import json

from collections import deque
from pathlib import Path
from pycg import utils
from pycg.machinery.callgraph import CallGraph
from pycg.machinery.classes import ClassManager
from pycg.machinery.condition import ConditionManager
from pycg.machinery.contexts import ContextManager
from pycg.machinery.definitions import DefinitionManager
from pycg.machinery.imports import ImportManager
from pycg.machinery.intersections import IntersectionManager
from pycg.machinery.key_err import KeyErrors
from pycg.machinery.middles import MiddleManager
from pycg.machinery.modules import ModuleManager
from pycg.machinery.scopes import ScopeManager
from pycg.machinery.sinks import SinkManager
from pycg.machinery.sources import SourceManager
from pycg.processing.cgprocessor import CallGraphProcessor
from pycg.processing.importprocessor import ImportProcessor
from pycg.processing.keyerrprocessor import KeyErrProcessor
from pycg.processing.postprocessor import PostProcessor
from pycg.processing.preprocessor import PreProcessor
from pycg.processing.locationprocessor import LocationProcessor
from pycg.utils.common import trans_frozenset_to_dict

current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)

class CallGraphGenerator(object):
    def __init__(self, entry_points, sink_points, package, name, max_iter, operation):
        self.entry_points = entry_points
        self.sink_points = sink_points
        self.code_contents = dict()
        self.save_sink = dict()
        self.save_middle = dict()
        self.save_if_stmt = dict()
        self.save_loop_stmt = dict()
        self.package = package
        self.project_name = name
        self.state = None
        self.max_iter = max_iter
        self.operation = operation
        self.import_chain = []
        self.location_messages = {"sup_class": dict(), "import_message": dict()}
        self.analyzed_queue = deque(maxlen=10)
        self.setUp()

    def setUp(self):
        self.source_manager = SourceManager()
        self.middle_manager = MiddleManager()
        self.intersection_manager = IntersectionManager()
        self.sink_manager = SinkManager()
        self.import_manager = ImportManager()
        self.scope_manager = ScopeManager()
        self.def_manager = DefinitionManager()
        self.class_manager = ClassManager()
        self.module_manager = ModuleManager()
        self.condition_manager = ConditionManager()
        self.context_manager = ContextManager()
        self.cg = CallGraph()
        self.key_errs = KeyErrors()
        self.middle_manager.set_class_messages(self.module_manager.get_internal_modules())

    def extract_state(self):
        state = {}
        state["defs"] = {}
        for key, defi in self.def_manager.get_defs().items():
            state["defs"][key] = {
                "names": defi.get_name_pointer().get().copy(),
                "lit": defi.get_lit_pointer().get().copy(),
            }

        state["scopes"] = {}
        for key, scope in self.scope_manager.get_scopes().items():
            state["scopes"][key] = set([
                x.get_ns() for (_, x) in scope.get_defs().items()
            ])

        state["classes"] = {}
        for key, ch in self.class_manager.get_classes().items():
            state["classes"][key] = ch.get_mro().copy()
        return state

    def reset_counters(self):
        for key, scope in self.scope_manager.get_scopes().items():
            scope.reset_counters()

    def has_converged(self):
        if not self.state:
            return False

        curr_state = self.extract_state()

        # check defs
        for key, defi in curr_state["defs"].items():
            if key not in self.state["defs"]:
                return False
            if defi["names"] != self.state["defs"][key]["names"]:
                return False
            if defi["lit"] != self.state["defs"][key]["lit"]:
                return False

        # check scopes
        for key, scope in curr_state["scopes"].items():
            if key not in self.state["scopes"]:
                return False
            if scope != self.state["scopes"][key]:
                return False

        # check classes
        for key, ch in curr_state["classes"].items():
            if key not in self.state["classes"]:
                return False
            if ch != self.state["classes"][key]:
                return False

        return True

    def remove_import_hooks(self):
        self.import_manager.remove_hooks()

    def tearDown(self):
        self.remove_import_hooks()

    def _get_mod_name(self, entry, pkg):
        # We do this because we want __init__ modules to
        # only contain the parent module
        # since pycg can't differentiate between functions
        # coming from __init__ files.

        input_mod = utils.to_mod_name(os.path.relpath(entry, pkg))
        if input_mod.endswith("__init__"):
            input_mod = ".".join(input_mod.split(".")[:-1])

        return input_mod

    def find_entry_and_sink(self):
        search_list = self.sink_manager.get_sink_points()
        search_middle_list = self.middle_manager.get_middle_methods()
        matching_files = []
        middle_files = []
        entry_files = []
        config_jsons = {}
        for root, dirs, files in os.walk(self.package):
            if any(x in root for x in
                   ('paper_experiments', 'tests', 'benchmark', 'venv', 'WareHouse/', 'testevals/', 'benchmarks',
                    'examples', 'test/', 'camel/test', 'scripts', 'llama_datasets')):
                # if any(x in root for x in ('venv/', 'WareHouse/')):
                continue
            for file in files:
                if not file.endswith('.py'):
                    if file.endswith('.yaml'):
                        config_file_path = os.path.join(root, file)
                        with open(config_file_path, 'r', encoding='utf-8') as yaml_file:
                            data = yaml.safe_load(yaml_file)
                            if not data:
                                continue
                            config_jsons[config_file_path] = data
                    continue
                file_path = os.path.join(root, file)
                try:
                    skip = False
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        for search_string in search_list:
                            if file_path in matching_files:
                                continue
                            sink_module, sink_name, param_index = search_string.split(':')
                            if sink_name + '(' in content:
                                matching_files.append(file_path)
                                skip = True
                            if sink_module in content:
                                matching_files.append(file_path)
                                skip = True
                        for middle_search_string in search_middle_list:
                            if file_path in middle_files:
                                continue
                            middle_module, middle_name, param_index = middle_search_string.split(':')
                            if any(prefix + middle_module in content for prefix in ("import ", "from ")):
                                if middle_name + '(' in content:
                                    middle_files.append(file_path)
                                    skip = True
                        if not skip:
                            entry_files.append(file_path)
                except Exception as e:
                    print(f"Error reading {file_path}: {e}")

        entry_files[:0] = middle_files
        entry_files[:0] = matching_files
        return entry_files, matching_files, middle_files, config_jsons

    def do_pass(self, cls, install_hooks=False, *args, **kwargs):
        modules_analyzed = set()
        for index, entry_point in enumerate(self.entry_points):
            input_pkg = self.package
            input_mod = self._get_mod_name(entry_point, input_pkg)
            input_file = os.path.abspath(entry_point)

            if not input_mod:
                continue

            if not input_pkg:
                input_pkg = os.path.dirname(input_file)

            if input_mod not in modules_analyzed:
                if install_hooks:
                    self.import_manager.set_pkg(input_pkg)
                    self.import_manager.install_hooks()

                processor = cls(
                    input_file,
                    input_mod,
                    modules_analyzed=modules_analyzed,
                    *args,
                    **kwargs,
                )
                processor.analyze()
                modules_analyzed = modules_analyzed.union(
                    processor.get_modules_analyzed()
                )

                if install_hooks:
                    self.remove_import_hooks()

    def load_sink_points(self):
        try:
            with open(self.sink_points, 'r', encoding='utf-8') as file:
                sink_list = [line.strip() for line in file]
            return sink_list
        except FileNotFoundError:
            print(f"ERROR: File {self.sink_points} not found!")
        except IOError as e:
            print(f"{e}")

    def load_llm_api(self):
        split_path = self.sink_points.rsplit('/', 2)
        llm_api_path = f"{split_path[0]}/llm_api/llm-apis"
        try:
            with open(llm_api_path, 'r', encoding='utf-8') as file:
                llm_api_list = [line.strip() for line in file]
            return llm_api_list
        except FileNotFoundError:
            print(f"ERROR: File {llm_api_path} not found!")
        except IOError as e:
            print(f"{e}")

    def load_predefined_taints(self):
        split_path = self.sink_points.rsplit('/', 2)
        taints_path = f"{split_path[0]}/taint_edges/{self.project_name}_taints.json"
        if not Path(taints_path).is_file():
            return {}
        with open(taints_path, "r", encoding="utf-8") as f:
            return json.load(f)

    def analyze(self):
        total_start_time = time.time()
        self.sink_manager.set_resource_methods(self.load_sink_points())
        self.middle_manager.set_resource_methods(self.load_llm_api())
        self.sink_manager.set_load_taints(self.load_predefined_taints())
        # Consider all methods within the large model framework as entry points,
        # and designate those containing risky substrings as target points.
        entry_files, matching_files, middle_files, config_jsons = self.find_entry_and_sink()

        self.middle_manager.set_potent_files(middle_files)
        self.sink_manager.set_potent_files(matching_files)
        self.sink_manager.set_config_jsons(config_jsons)

        self.entry_points = middle_files + matching_files
        self.sink_manager.replace_all()
        print('total files: ' + str(len(list(set(entry_files)))))
        print("start location processor")
        llm_start_time = time.time()
        self.do_pass(
            LocationProcessor,
            True,
            self.import_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.source_manager,
            self.middle_manager,
            self.sink_manager,
            self.location_messages,
            self.code_contents,
            self.save_middle
        )
        self.sink_manager.filter_potent_sink_module()
        llm_end_time = time.time()
        print(f"llm processor execution time: {llm_end_time - llm_start_time} seconds")

        self.entry_points = entry_files
        print("start import processor-1")
        import_start_time = time.time()
        # Construct the import graph and eliminate modules that do not belong
        # to the subgraph containing the suspected sink.
        self.do_pass(
            ImportProcessor,
            True,
            self.import_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.source_manager,
            self.middle_manager,
            self.sink_manager,
            self.import_chain,
            self.analyzed_queue,
            self.code_contents,
            self.save_if_stmt,
            self.save_loop_stmt
        )

        import_end_time = time.time()
        print(f"import processor-1 execution time: {import_end_time - import_start_time} seconds")

        if_stmt_output = trans_frozenset_to_dict(self.save_if_stmt)
        with open(f'{parent_dir}/path_result/{self.project_name}-if-output.json', "w+") as f:
            f.write(json.dumps(if_stmt_output))
        loop_stmt_output = trans_frozenset_to_dict(self.save_loop_stmt)
        with open(f'{parent_dir}/path_result/{self.project_name}-loop-output.json', "w+") as f:
            f.write(json.dumps(loop_stmt_output))

        print("start import processor-2")
        import_start_time = time.time()
        add_sources = self.sink_manager.filter_potent_sink_method()
        self.source_manager.set_source_files(list(add_sources))
        self.middle_manager.transitive_potent_method(self.module_manager)
        self.middle_manager.filter_potent_middle_method()
        self.sink_manager.filter_config_json()
        self.sink_manager.print_sink()

        import_end_time = time.time()
        print(f"import processor-2 execution time: {import_end_time - import_start_time} seconds")

        for _middle in list(self.save_middle.keys()):
            mod_name, meth_name = _middle.split('#')
            middle_node = self.middle_manager.get_node(mod_name)
            if not middle_node:
                self.save_middle.pop(_middle)
            elif meth_name not in middle_node['potent_method']:
                self.save_middle.pop(_middle)

        middle_output = trans_frozenset_to_dict(self.save_middle)
        with open(f'{parent_dir}/path_result/{self.project_name}-middle-output.json', "w+") as f:
            f.write(json.dumps(middle_output))

        print("start pre processor")
        pre_start_time = time.time()
        self.entry_points = self.source_manager.get_source_files()
        self.do_pass(
            PreProcessor,
            True,
            self.import_manager,
            self.scope_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.sink_manager,
            self.code_contents
        )
        self.def_manager.complete_definitions()
        pre_end_time = time.time()
        print(f"pre processor execution time: {pre_end_time - pre_start_time} seconds")

        print("start post processor")
        post_start_time = time.time()
        iter_cnt = 0
        while (self.max_iter < 0 or iter_cnt < self.max_iter) and (not self.has_converged()):
            self.state = self.extract_state()
            self.reset_counters()
            self.do_pass(
                PostProcessor,
                False,
                self.import_manager,
                self.scope_manager,
                self.def_manager,
                self.class_manager,
                self.module_manager,
                self.source_manager,
                self.middle_manager,
                self.intersection_manager,
                self.sink_manager,
                self.condition_manager,
                self.code_contents
            )

            self.def_manager.complete_definitions()
            self.sink_manager.transitive_potent_method()
            iter_cnt += 1
        post_end_time = time.time()
        print(f"post processor execution time: {post_end_time - post_start_time} seconds")
        print('sink files: ' + str(len(self.sink_manager.get_nodes())))
        print("start callgraph processor")
        cg_start_time = time.time()
        self.reset_counters()
        if self.operation == utils.constants.CALL_GRAPH_OP:
            self.do_pass(
                CallGraphProcessor,
                False,
                self.import_manager,
                self.scope_manager,
                self.def_manager,
                self.class_manager,
                self.module_manager,
                self.sink_manager,
                self.condition_manager,
                self.intersection_manager,
                self.middle_manager,
                self.context_manager,
                self.code_contents,
                self.save_sink,
                call_graph=self.cg,
            )
        else:
            raise Exception("Invalid operation: " + self.operation)
        cg_end_time = time.time()
        print(f"cg processor execution time: {cg_end_time - cg_start_time} seconds")
        total_end_time = time.time()
        print(f"total execution time: {total_end_time - total_start_time} seconds")

    def output(self):
        return self.cg.get()

    def output_re(self):
        return self.cg.get_re()

    def output_hierarchy_graph(self):
        return self.cg.get_hierarchy_graph()

    def output_intersections(self):
        return self.cg.get_intersections()

    def output_middles(self):
        return self.cg.get_middles()

    def output_sink_file(self):
        return self.cg.get_sink_save()

    def output_key_errs(self):
        return self.key_errs.get()

    def output_conditions(self):
        return self.cg.get_conditions()

    def output_edges(self):
        return self.cg.get_edges()

    def _generate_mods(self, mods):
        res = {}
        for mod, node in mods.items():
            res[mod] = {
                "filename": (
                    os.path.relpath(node.get_filename(), self.package)
                    if node.get_filename()
                    else None
                ),
                "methods": node.get_methods(),
            }
        return res

    def output_internal_mods(self):
        return self._generate_mods(self.module_manager.get_internal_modules())

    def output_external_mods(self):
        return self._generate_mods(self.module_manager.get_external_modules())

    def output_functions(self):
        functions = []
        for ns, defi in self.def_manager.get_defs().items():
            if defi.is_function_def():
                functions.append(ns)
        return functions

    def output_classes(self):
        classes = {}
        for cls, node in self.class_manager.get_classes().items():
            classes[cls] = {"mro": node.get_mro(), "module": node.get_module()}
        return classes

    def get_as_graph(self):
        return self.def_manager.get_defs().items()
