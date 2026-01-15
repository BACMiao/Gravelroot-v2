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
from calendar import different_locale

from pycg import utils
from pycg.machinery.pointers import LiteralPointer, NamePointer, TaintPointer
from pycg.utils.constants import NO_CHANGE


class DefinitionManager(object):
    def __init__(self):
        self.defs = {}
        self.change_named_defs = set()
        self.change_taint_defs = set()
        self.re_taint_graph = {}
        self.pre_closured = {}
        self.pre_reversed_closured = {}
        self.pre_taints = {}
        self.pre_reversed_taints = {}

    def create(self, ns, def_type, mn):
        if not ns or not isinstance(ns, str):
            raise DefinitionError("Invalid namespace argument")
        if def_type not in Definition.types:
            raise DefinitionError("Invalid def type argument")
        if self.get(ns):
            raise DefinitionError("Definition already exists")
        if not mn or not isinstance(mn, str):
            raise DefinitionError("Invalid module name argument")

        self.defs[ns] = Definition(ns, def_type, mn, self)
        return self.defs[ns]

    def assign(self, ns, defi, mn):
        self.defs[ns] = Definition(ns, defi.get_type(), mn, self)
        self.defs[ns].merge(defi)

        # if it is a function def, we need to create a return pointer
        if defi.is_function_def():
            return_ns = utils.join_ns(ns, utils.constants.RETURN_NAME)
            defi_return = utils.join_ns(defi.get_ns(), utils.constants.RETURN_NAME)
            self.defs[return_ns] = Definition(return_ns, utils.constants.NAME_DEF, mn, self)
            self.defs[return_ns].get_name_pointer().add(defi_return)
            if defi_return not in self.defs:
                self.defs[defi_return] = Definition(defi_return, utils.constants.NAME_DEF, defi.get_module_name(), self)
            self.defs[defi_return].get_taint_pointer().add(return_ns)
            defi.get_taint_pointer().add(defi_return)
            self.defs[ns].get_taint_pointer().add(return_ns)

        return self.defs[ns]

    def get(self, ns):
        if ns in self.defs:
            return self.defs[ns]

    def get_defs(self):
        return self.defs

    def add_change_named_defs(self, defi):
        self.change_named_defs.add(defi)

    def add_change_taint_defs(self, defi):
        self.change_taint_defs.add(defi)

    def handle_function_def(self, parent_ns, fn_name, mn):
        full_ns = utils.join_ns(parent_ns, fn_name)
        defi = self.get(full_ns)
        if not defi:
            defi = self.create(full_ns, utils.constants.FUN_DEF, mn)
            defi.decorator_names = set()

        return_ns = utils.join_ns(full_ns, utils.constants.RETURN_NAME)
        if not self.get(return_ns):
            self.create(return_ns, utils.constants.NAME_DEF, defi.get_module_name())
            defi.get_taint_pointer().add(return_ns)

        return defi

    def handle_class_def(self, parent_ns, cls_name, mn):
        full_ns = utils.join_ns(parent_ns, cls_name)
        defi = self.get(full_ns)
        if not defi:
            defi = self.create(full_ns, utils.constants.CLS_DEF, mn)

        return defi

    def trace_final_defi(self, defi, traced=None):
        if traced is None:
            traced = set()
        trace_set = set()
        pointers = defi.get_name_pointer().get()
        defi_ns = defi.get_ns()
        if defi_ns in traced:
            return trace_set
        traced.add(defi_ns)
        if len(pointers) == 0 and not defi_ns.endswith('<RETURN>'):
            trace_set.add(defi.get_ns())
        for value in pointers:
            next_defi = self.get(value)
            if next_defi and next_defi.get_type() == defi.get_type():
                trace_set.update(self.trace_final_defi(next_defi, traced))
            elif not defi_ns.endswith('<RETURN>'):
                trace_set.add(defi.get_ns())
        return trace_set

    def transitive_closure(self):
        closured = self.pre_closured
        reversed_closured = self.pre_reversed_closured
        CHANGED = (utils.constants.NAME_CHANGE, utils.constants.BOTH_CHANGE)
        global_process_list = []
        analyzed = set()

        def dfs(defi):
            # bottom
            if closured.get(defi.get_ns(),
                            None) is not None and defi.get_change_state() not in CHANGED or defi.get_ns() in analyzed:
                return closured[defi.get_ns()]
            if defi.get_change_state() in (utils.constants.BOTH_CHANGE, utils.constants.TAINT_CHANGE):
                defi.turn_change_toTaint()
            else:
                defi.turn_change_toNochange()
            analyzed.add(defi.get_ns())

            name_pointer = defi.get_name_pointer()
            new_set = set()

            if not name_pointer.get():
                new_set.add(defi.get_ns())

            if not closured.get(defi.get_ns()):
                closured[defi.get_ns()] = new_set

            if len(global_process_list) == 0:
                for name in name_pointer.get():
                    next_defi = self.defs.get(name, None)
                    if not next_defi:
                        continue
                    items = dfs(next_defi)
                    if not items:
                        items = set([name])
                    new_set = new_set.union(items)
            else:
                added_names = defi.get_added_names()
                full_closure = closured.get(defi.get_ns(), set())
                remaining_names = full_closure - added_names
                for name in added_names:
                    next_defi = self.defs.get(name, None)
                    if not next_defi or name in new_set:
                        continue
                    items = dfs(next_defi)
                    if not items:
                        items = set([name])
                    new_set = new_set.union(items)
                    if name not in reversed_closured:
                        reversed_closured[name] = set()
                    reversed_closured[name].add(defi.get_ns())
                defi.clear_added_names()
                for name in remaining_names:
                    next_closured = self.defs.get(name, None)
                    if not next_closured or name in new_set:
                        continue
                    items = dfs(next_closured)
                    if not items:
                        items = set([name])
                    new_set = new_set.union(items)
            old_different_set = closured[defi.get_ns()] - new_set
            new_different_set = new_set - closured[defi.get_ns()]
            closured[defi.get_ns()] = new_set

            for dep in old_different_set:
                if dep not in reversed_closured or defi.get_ns() not in reversed_closured[dep]:
                    continue
                reversed_closured[dep].remove(defi.get_ns())

            for dep in new_different_set:
                if dep not in reversed_closured:
                    reversed_closured[dep] = set()
                reversed_closured[dep].add(defi.get_ns())

            return closured[defi.get_ns()]

        def reversed_dfs(ns, closured, visited=None, process_list=None, depth=0, max_depth=5):
            if visited is None:
                visited = set()
            if process_list is None:
                process_list = []

            if ns in visited or depth > max_depth or ns in global_process_list:
                return

            visited.add(ns)

            if depth == 0:
                process_list.append(ns)

            for upstream in reversed_closured.get(ns, []):
                if upstream == ns:
                    continue
                if depth == 0 and closured.get(upstream):
                    closured[upstream].add(ns)
                reversed_dfs(upstream, closured, visited, process_list, depth=depth + 1, max_depth=max_depth)

            if depth > 0:
                process_list.append(ns)

            return process_list

        if len(closured) == 0:
            for ns, current_def in self.defs.items():
                current_def.turn_change_toNochange()
                if closured.get(ns, None) is None:
                    dfs(current_def)
        else:
            for current_def in self.change_named_defs:
                ns = current_def.get_ns()
                global_process_list.extend(current_def.get_added_names())
                if ns in global_process_list:
                    continue
                if current_def.get_change_state() in CHANGED or ns not in closured:
                    global_process_list += reversed_dfs(ns, closured)
            self.change_named_defs.clear()
            global_process_list = list(dict.fromkeys(global_process_list))
            for affected in global_process_list:
                affected_defi = self.defs.get(affected, None)
                if not affected_defi:
                    continue
                if affected_defi.get_change_state() in (utils.constants.TAINT_CHANGE, utils.constants.BOTH_CHANGE):
                    affected_defi.turn_change_toBoth()
                else:
                    affected_defi.turn_change_toName()
            for affected in global_process_list:
                affected_defi = self.defs.get(affected, None)
                if not affected_defi:
                    continue
                if affected in analyzed:
                    if affected_defi.get_change_state() in (utils.constants.NAME_CHANGE, utils.constants.NO_CHANGE):
                        affected_defi.turn_change_toNochange()
                    else:
                        affected_defi.turn_change_toTaint()
                    continue
                dfs(affected_defi)

        self.pre_closured = closured
        self.pre_reversed_closured = reversed_closured
        return closured

    def transitive_taints(self):
        taints = self.pre_taints
        reversed_taints = self.pre_reversed_taints
        CHANGED = (utils.constants.TAINT_CHANGE, utils.constants.BOTH_CHANGE)
        global_process_list = []
        analyzed = set()

        def dfs(defi):
            if taints.get(defi.get_ns(), None) is not None and defi.get_change_state() not in CHANGED:
                return taints[defi.get_ns()]

            if defi.get_change_state() in (utils.constants.BOTH_CHANGE, utils.constants.NAME_CHANGE):
                defi.turn_change_toName()
            else:
                defi.turn_change_toNochange()
            analyzed.add(defi.get_ns())

            taint_pointer = defi.get_taint_pointer()
            new_set = set()

            if not taint_pointer.get():
                new_set.add(defi.get_ns())

            if not taints.get(defi.get_ns()):
                taints[defi.get_ns()] = new_set
            replace_taints = set()
            if len(global_process_list) == 0:
                for name in taint_pointer.get():
                    if name.startswith('Taint-Sink-'):
                        items = [name]
                        new_set = set(items)
                        break
                    elif not self.defs.get(name, None):
                        continue
                    else:
                        items = dfs(self.defs[name])
                        if not items:
                            items = set([name])
                    new_set = new_set.union(items)
            else:
                added_taints = defi.get_added_taints()
                full_taints = taints.get(defi.get_ns(), set())
                remaining_taints = full_taints - added_taints
                for name in added_taints.copy():
                    if name.startswith('Taint-Sink-'):
                        items = [name]
                        new_set = set(items)
                        break
                    elif not self.defs.get(name, None) or name in new_set:
                        continue
                    else:
                        items = dfs(self.defs[name])
                        if not items:
                            items = set([name])
                    new_set = new_set.union(items)
                replace_taints = added_taints - new_set
                remaining_taints = remaining_taints - new_set
                defi.clear_added_taints()

                if not any(s.startswith("Taint-Sink-") for s in new_set):
                    for name in remaining_taints:
                        if name.startswith('Taint-Sink-'):
                            items = [name]
                            new_set = set(items)
                            break
                        elif not self.defs.get(name, None) or name in new_set or name == defi.get_ns():
                            continue
                        else:
                            items = dfs(self.defs[name])
                            if not items:
                                items = set([name])
                        new_set = new_set.union(items)
                elif not any(s.startswith("Taint-Sink-") for s in full_taints):
                    for reversed_taint in reversed_taints.get(defi.get_ns()) or []:
                        reversed_def = self.defs.get(reversed_taint, None)
                        if reversed_def:
                            if reversed_def.get_change_state() == utils.constants.NAME_CHANGE:
                                reversed_def.turn_change_toBoth()
                            else:
                                reversed_def.turn_change_toTaint()

            old_different_set = taints[defi.get_ns()] - new_set
            new_different_set = new_set - taints[defi.get_ns()]
            taints[defi.get_ns()] = new_set

            for dep in old_different_set:
                if dep not in reversed_taints or defi.get_ns() not in reversed_taints[dep]:
                    continue
                reversed_taints[dep].remove(defi.get_ns())

            for dep in new_different_set | replace_taints:
                if dep not in reversed_taints:
                    reversed_taints[dep] = set()
                reversed_taints[dep].add(defi.get_ns())
            return taints[defi.get_ns()]

        def reversed_dfs(ns, visited=None, process_list=None, depth=0, max_depth=10):
            if visited is None:
                visited = set()
            if process_list is None:
                process_list = []

            if ns in visited or depth > max_depth or ns in global_process_list:
                return

            visited.add(ns)

            for upstream in reversed_taints.get(ns, []):
                affected_defi = self.defs.get(upstream, None)
                if affected_defi and upstream != ns:
                    affected_defi.add_added_taints(ns)
                reversed_dfs(upstream, visited, process_list, depth=depth + 1, max_depth=max_depth)

            process_list.append(ns)

            return process_list

        if len(taints) == 0:
            for ns, current_def in self.defs.items():
                current_def.turn_change_toNochange()
                if taints.get(ns, None) is None:
                    dfs(current_def)
        else:
            for current_def in list(self.change_taint_defs):
                ns = current_def.get_ns()
                global_process_list.extend(current_def.get_added_taints())
                if ns in global_process_list:
                    continue
                if current_def.get_change_state() in CHANGED or ns not in taints:
                    global_process_list += reversed_dfs(ns)
            self.change_taint_defs.clear()
            global_process_list = list(dict.fromkeys(global_process_list))
            for affected in global_process_list:
                affected_defi = self.defs.get(affected, None)
                if not affected_defi:
                    continue
                if affected_defi.get_change_state() in (utils.constants.NAME_CHANGE, utils.constants.BOTH_CHANGE):
                    affected_defi.turn_change_toBoth()
                else:
                    affected_defi.turn_change_toTaint()
            for affected in global_process_list:
                affected_defi = self.defs.get(affected, None)
                if not affected_defi:
                    continue
                if affected in analyzed:
                    if affected_defi.get_change_state() in (utils.constants.TAINT_CHANGE, utils.constants.NO_CHANGE):
                        affected_defi.turn_change_toNochange()
                    else:
                        affected_defi.turn_change_toName()
                    continue
                dfs(affected_defi)
        self.pre_taints = taints
        self.pre_reversed_taints = reversed_taints
        return taints

    def complete_definitions(self):
        print("execute complete_definitions (worklist version)")

        defs = self.defs
        worklist = set(defs.keys())
        MIN_THRESHOLD = 20
        MAX_ITER = max(len(self.defs), MIN_THRESHOLD)

        def update_pointsto_args(pointsto_args, arg, name):
            changed_something = False
            if arg == pointsto_args:
                return False

            for pointsto_arg in pointsto_args:
                if pointsto_arg == name or pointsto_arg not in defs:
                    continue

                pointsto_arg_def = defs[pointsto_arg].get_name_pointer()
                if pointsto_arg_def == pointsto_args:
                    continue

                if pointsto_arg in arg:
                    arg.remove(pointsto_arg)

                current_items = pointsto_arg_def.get()
                for item in arg:
                    if item not in current_items:
                        if item in defs:
                            changed_something = True
                            pointsto_arg_def.add(item)
            return changed_something

        for iteration in range(MAX_ITER):
            next_worklist = set()
            changed_count = 0

            for ns in worklist:
                current_def = defs[ns]
                current_pointer = current_def.get_name_pointer()

                for name in current_pointer.get().copy():
                    if name == ns or name not in defs:
                        continue

                    pointsto_pointer = defs[name].get_name_pointer()

                    for arg_name, arg in current_pointer.get_args().items():
                        pos = current_pointer.get_pos_of_name(arg_name)
                        if pos is not None:
                            pointsto_args = pointsto_pointer.get_pos_arg(pos)
                            if not pointsto_args:
                                pointsto_pointer.add_pos_arg(pos, None, arg)
                                continue
                        else:
                            pointsto_args = pointsto_pointer.get_arg(arg_name)
                            if not pointsto_args:
                                pointsto_pointer.add_arg(arg_name, arg)
                                continue

                        if update_pointsto_args(pointsto_args, arg, ns):
                            next_worklist.add(name)
                            changed_count += 1

            if not next_worklist:
                print(f"complete_definitions converged in {iteration + 1} iterations")
                break

            worklist = next_worklist
        else:
            print(f"⚠️ complete_definitions reached max {MAX_ITER} iterations without full convergence")

        print("execute complete_definitions completed")


class Definition(object):
    types = [
        utils.constants.FUN_DEF,
        utils.constants.MOD_DEF,
        utils.constants.NAME_DEF,
        utils.constants.CLS_DEF,
        utils.constants.EXT_DEF,
        utils.constants.INS_DEF,
    ]

    def __init__(self, fullns, def_type, module_name, def_manager):
        self.def_manager = def_manager
        self.fullns = fullns
        self.points_to = {"lit": LiteralPointer(self), "name": NamePointer(self), "taint": TaintPointer(self)}
        self.def_type = def_type
        self.module_name = module_name
        self.potent_type = set()
        self.change = utils.constants.NO_CHANGE
        self.added_names = set()
        self.added_taints = set()
        self.context_defi = set()
        self.added_context_defs = set()

    def get_def_manager(self):
        return self.def_manager

    def get_added_names(self):
        return self.added_names

    def get_added_taints(self):
        return self.added_taints

    def add_added_names(self, added_name):
        self.added_names.add(added_name)

    def add_added_taints(self, added_taint):
        self.added_taints.add(added_taint)

    def clear_added_names(self):
        self.added_names.clear()

    def clear_added_taints(self):
        self.added_taints.clear()

    def get_change_state(self):
        return self.change

    def turn_change_toNochange(self):
        self.change = utils.constants.NO_CHANGE

    def turn_change_toName(self):
        self.change = utils.constants.NAME_CHANGE

    def turn_change_toTaint(self):
        self.change = utils.constants.TAINT_CHANGE

    def turn_change_toBoth(self):
        self.change = utils.constants.BOTH_CHANGE

    def get_type(self):
        return self.def_type

    def set_type(self, def_type):
        self.def_type = def_type

    def is_function_def(self):
        return self.def_type == utils.constants.FUN_DEF

    def is_ext_def(self):
        return self.def_type == utils.constants.EXT_DEF

    def is_callable(self):
        return self.is_function_def() or self.is_ext_def()

    def get_lit_pointer(self):
        return self.points_to["lit"]

    def get_name_pointer(self):
        return self.points_to["name"]

    def get_taint_pointer(self):
        return self.points_to["taint"]

    def get_name(self):
        return self.fullns.split(".")[-1]

    def get_ns(self):
        return self.fullns

    def merge(self, to_merge):
        for name, pointer in to_merge.points_to.items():
            self.points_to[name].merge(pointer)

    def get_module_name(self):
        return self.module_name

    def add_potent_type(self, potent_type):
        if isinstance(potent_type, str):
            self.potent_type.add(potent_type)
        else:
            self.potent_type.update(potent_type)

    def get_potent_type(self):
        return self.potent_type

    def add_context_def(self, context_def):
        if context_def.get_ns() in self.added_context_defs:
            return
        self.added_context_defs.add(context_def.get_ns())
        self.context_defi.add(context_def)

    def get_context_def(self):
        return self.context_defi


class DefinitionError(Exception):
    pass
