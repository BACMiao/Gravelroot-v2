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
from .base import BaseFormatter
from ..machinery.definitions import DefinitionManager


class Simple(BaseFormatter):
    def __init__(self, cg_generator):
        self.cg_generator = cg_generator
        self.print_stmts = {}
        self.all_paths = []
        self.is_path_end = False
        self.hierarchy_graph = self.cg_generator.output_hierarchy_graph()
        self.def_manager = self.cg_generator.def_manager
        self.module_manager = self.cg_generator.module_manager
        self.sink_manager = self.cg_generator.sink_manager
        self.middle_list = self.cg_generator.middle_manager.get_resource_points()
        self.conditions = self.cg_generator.condition_manager.get_nodes()
        self.sink_files = self.cg_generator.output_sink_file()

    def generate(self):
        output_re = self.cg_generator.output_re()
        sinks = self.sink_manager.get_sink_points()
        middles = self.cg_generator.output_middles()
        for sink in sinks:
            if sink not in output_re:
                continue
            self.find_all_paths(sink, [], output_re, dict())
        output_cg = {"FILE": self.sink_files}
        for index, path in enumerate(self.all_paths):
            path_key = f'Path{index + 1}'
            path_str = ' -> '.join(reversed(path))
            print(path_key)
            print(path_str)
            self.is_path_end = False
            output_cg.setdefault('PATH', {})[path_key] = {'condition': [], 'path': path_str, 'middles': [],
                                                          'taints': []}
            self.print_condition(path[1], path, output_cg['PATH'][path_key]['condition'], output_re)
            print('Taints and Attack Graph:')
            self.print_stmt(path[-1], path, output_cg['PATH'][path_key], middles, [])

        return output_cg

    def find_all_paths(self, current_node, current_path, data, find_conflict):
        if current_node in current_path:
            current_path.append('LOOP PATH: ' + current_node)
            self.all_paths.append(current_path.copy())
            current_path.pop()
            return

        if 'HypotheticalDocumentEmbedder.embed_query' in current_node:
            return

        current_path.append(current_node)

        if not data[current_node]:
            self.all_paths.append(current_path.copy())
        else:
            add_node_set = set()
            for next_node in data[current_node]:
                call_line = -1
                if '%' in next_node:
                    next_node, call_line = next_node.split('%')

                add_conflict = False
                cls_name = ''
                if ':' in next_node:
                    obj_ctx, wo_ctx_next_node = next_node.split(':')
                    obj_ctx = obj_ctx.split('@')[1]
                    cls_name = wo_ctx_next_node.rsplit('.', 1)[0]

                    if cls_name not in find_conflict:
                        find_conflict[cls_name] = obj_ctx
                        add_conflict = True
                    elif find_conflict[cls_name] != obj_ctx:
                        continue
                else:
                    wo_ctx_next_node = next_node
                if wo_ctx_next_node in self.sink_files:
                    pre_call_line = self.sink_files[wo_ctx_next_node]['call_line']
                    if int(call_line) > int(pre_call_line):
                        self.sink_files[wo_ctx_next_node]['call_line'] = int(call_line)
                        if current_node in self.sink_manager.get_sink_points():
                            self.sink_files[wo_ctx_next_node]['is_sink'].append(int(call_line))

                if (next_node in add_node_set
                        or len(data[next_node]) == 0 and self.combine_node(next_node, data[current_node])):
                    if add_conflict:
                        find_conflict.pop(cls_name)
                    continue
                add_node_set.add(next_node)
                self.find_all_paths(next_node, current_path, data, find_conflict)
                if add_conflict:
                    find_conflict.pop(cls_name)
        current_path.pop()

    def combine_node(self, next_node, all_nodes):
        for node in all_nodes:
            if '%' in node:
                node = node.split('%')[0]
            if next_node == node:
                continue
            if node.endswith(next_node):
                return True
        return False

    def has_conflicts(self, sig_cls, last, second_last):
        return self.hierarchy_graph.is_subclass(second_last, last) and self.hierarchy_graph.is_subclass(sig_cls, last)

    def iter_has_conflicts(self, sig_meth, last, second_last):
        must_cls_list = self.hierarchy_graph.get_exist_cls_edge(sig_meth)
        if second_last in must_cls_list:
            return False
        for must_cls in must_cls_list:
            if self.hierarchy_graph.is_subclass(second_last, last) and self.hierarchy_graph.is_subclass(must_cls,
                                                                                                        last) and must_cls != last:
                return True

    def print_stmt(self, node, path, output_cg, middles, find_loop, indent=0, need_subt=False):
        taint_path = output_cg['taints']
        if node in find_loop:
            return
        find_loop.append(node)
        if ':' in node:
            pnode = node.split(':')[1]
        else:
            pnode = node
        edges_with_name = self.cg_generator.cg.get_edges_with_name(pnode)
        taint_with_name = self.cg_generator.cg.get_taints_with_name(pnode)
        ori_node = node
        if not taint_with_name:
            indent_str = '   ' * indent
            taint_path.append(indent_str + 'method: ' + pnode)
            print(indent_str + 'method: ' + pnode)
            if edges_with_name:
                self.print_middle_path(edges_with_name, path, middles, node, output_cg, indent)
            if node not in path:
                return
            index = path.index(node)
            if index > 0:
                node = path[index - 1]
                if ':' in node:
                    node = node.split(':')[1]
                else:
                    node = node
                edges_with_name = self.cg_generator.cg.get_edges_with_name(node)
                taint_with_name = self.cg_generator.cg.get_taints_with_name(node)
            else:
                self.is_path_end = True
                return

        call_next_sink = False
        next_sink_node = None
        if ori_node in path:
            index = path.index(ori_node)
            if index > 0:
                next_sink_node = path[index - 1]
        if need_subt:
            indent -= 1
        indent_str = '   ' * indent

        if taint_with_name is None:
            return

        for line, stmt in taint_with_name.items():
            if self.is_path_end:
                break
            taint_path.append(indent_str + 'method: ' + node)
            taint_path.append(indent_str + '----->' + stmt + '  ' + line)
            print(indent_str + 'method: ' + node)
            print(indent_str + '----->' + stmt + '  ' + line)
            is_middle = False
            if intersection := self.get_intersection(node):
                for call_mid_method in intersection['line_num'].get(int(line.replace('line: ', '')), []):
                    if call_mid_method in path:
                        continue
                    mod_name, method = call_mid_method.split(':')
                    potent_mid_method = middles[mod_name]['potent_method']
                    middle_callee = potent_mid_method[method]['callee']
                    result_callee = self.determine_skip_middle(path, node, middle_callee)
                    self.iter_middle(path, result_callee, middles, [call_mid_method], output_cg, indent)
                    is_middle = True
                if is_middle:
                    continue
            elif stmt and next_sink_node and next_sink_node not in stmt and '@' in stmt:
                taint_method = stmt.split('@')[1]
                for _line, _stmt in (self.cg_generator.cg.get_taints_with_name(taint_method) or {}).items():
                    if '@' in _stmt:
                        next_taint_method = _stmt.split('@')[1]
                        find_loop.append(next_taint_method)
                        self.print_stmt(taint_method, find_loop, output_cg, middles, find_loop, indent + 1)
            if line in edges_with_name:
                for sub_index, call_next_method in enumerate(edges_with_name[line]):
                    if len(edges_with_name[line]) > 1:
                        inter = set(edges_with_name[line]) & set(path)
                        if inter and call_next_method not in inter:
                            continue
                    if next_sink_node and next_sink_node == call_next_method and next_sink_node == node:
                        call_next_sink = True
                    self.print_stmt(call_next_method, path, output_cg, middles, find_loop, indent + 1, call_next_sink)

        if next_sink_node and not call_next_sink:
            self.print_stmt(next_sink_node, path, output_cg, middles, find_loop)

    def print_middle_path(self, edges_with_name, path, middles, node, output_cg, indent):
        for _, _method in edges_with_name.items():
            if intersection := self.get_intersection(_method[0]):
                for call_mid_methods in intersection['line_num'].values():
                    for _item in path:
                        if _item.endswith(_method[0]):
                            return
                    middle_path = [_method[0]]
                    for call_mid_method in call_mid_methods:
                        tmp_method_name = call_mid_method.replace(':', '.')
                        if tmp_method_name in path:
                            continue
                        middle_path.append(call_mid_method)
                        mod_name, method = call_mid_method.split(':')
                        potent_mid_method = middles[mod_name]['potent_method']
                        middle_callee = potent_mid_method[method]['callee']
                        result_callee = self.determine_skip_middle(path, node, middle_callee)
                        return_flag = self.iter_middle(path, result_callee, middles, middle_path, output_cg, indent)
                        if return_flag:
                            return
    def get_intersection(self, node):
        intersection = self.cg_generator.output_intersections().get(node)
        if intersection or ':' not in node:
            return intersection
        sub_node = node.split(':')[1]
        intersection = self.cg_generator.output_intersections().get(sub_node)
        if intersection:
            return intersection
        sub_node = '@' + node.split('@')[1]
        intersection = self.cg_generator.output_intersections().get(sub_node)
        if intersection:
            return intersection
        return None

    def determine_skip_middle(self, path, call_next_method, middle_callee):
        result = set()
        if call_next_method not in path:
            return middle_callee
        index = path.index(call_next_method)

        if index < len(path):
            next_path_class = path[index - 1].rsplit('.', 1)[0]
            for middle_method in middle_callee:
                mod_name, met_name = middle_method.split(':')
                cls_name = met_name.rsplit('.', 1)[0]
                if (
                        self.hierarchy_graph.have_common_parent(next_path_class, mod_name + '.' + cls_name)
                        and not self.hierarchy_graph.is_subclass(mod_name + '.' + cls_name, next_path_class)
                ):
                    continue
                result.add(middle_method)
        return result

    def iter_middle(self, call_path, caller_message, middles, path, output_cg, indent=0):
        return_value = False
        indent_str = '   ' * indent
        for caller in caller_message:
            if caller in path:
                continue
            mod_name, met_name = caller.split(':')
            path.append(caller)
            if mod_name == 'openai':
                print(indent_str + 10 * '===============')
                print(indent_str + 'path of call openai: ' + ' -> '.join(path))
                print(indent_str + 10 * '===============')
                output_cg['middles'].append(' -> '.join(path))
                return True
            middle_callee = middles[mod_name]['potent_method'][met_name]['callee']
            return_value = self.iter_middle(call_path, middle_callee, middles, path, output_cg, indent)
            if return_value:
                return True
            if any(keyword.replace(':-1', '') in path for keyword in self.middle_list):
                return True
            path.pop()
        return return_value

    def print_condition(self, node, sink_path, condition_path, cg, path=None, print_count=0, max_print=5):
        path_str = '.'.join(sink_path)
        entry_node = sink_path[-1]
        for key, value in self.conditions.items():
            if entry_node.startswith(key):
                condis = value['condition']
                if ':' in key:
                    cls_method = key.split(':')[1] + '.__init__'
                else:
                    cls_method = key
                need = ''
                for condi in condis:
                    if '@' in condi:
                        cs_ctx, obj_ctx = condi.split('@')
                        need = cs_ctx if cs_ctx != '' else obj_ctx
                        if need in path_str:
                            break
                print('Condition: ')
                condi_path = 'Args Initialization: ' + cls_method + ' -> ' + need
                condition_path.append(condi_path)
                print(condi_path)
                return

        if path is None:
            have_condition = False
            node, _, _ = node.rpartition('.')
            node += ".__init__"
            pre_node = node
            for _ in range(3):
                if self.module_manager.get(node):
                    node = pre_node
                    break
                if node in cg:
                    have_condition = True
                    break
                pre_node = node
                node, _, _ = node.rpartition('.')
            if not have_condition:
                parent_classes = self.hierarchy_graph.get_parent_class(pre_node)
                for sink_node in reversed(sink_path):
                    sink_defi = self.def_manager.get(sink_node)
                    if not sink_defi:
                        continue
                    sink_cls_node, _, _ = sink_node.rpartition('.')
                    sink_cls_defi = self.def_manager.get(sink_cls_node)
                    for arg in sink_defi.get_name_pointer().get_args():
                        arg_defi_name = f'{sink_node}.{arg}'
                        arg_defi = self.def_manager.get(arg_defi_name)
                        if not arg_defi:
                            continue
                        potent_type_set = arg_defi.get_potent_type()
                        if parent_classes & potent_type_set:
                            print('Condition: ')
                            condi_path = 'Args Initialization: ' + arg_defi_name + ' -> ' + pre_node
                            condition_path.append(condi_path)
                            print(condi_path)
                            return
                    if not sink_cls_defi:
                        return
                    for index, field_set in sink_cls_defi.get_name_pointer().get_args().items():
                        for field_defi_name in field_set:
                            if field_defi:=self.def_manager.get(field_defi_name):
                                if parent_classes & field_defi.get_potent_type():
                                    print('Condition: ')
                                    condi_path = 'Field Initialization: ' + field_defi_name + ' -> ' + pre_node
                                    condition_path.append(condi_path)
                                    print(condi_path)
                                    return
                return
            path = []

        if node in path:
            return

        path.append(node)

        if node not in cg or not cg[node]:
            if len(path) > 0:
                if print_count < max_print:
                    print('Condition: ')
                    condi_path = ' -> '.join(reversed(path))
                    print(condi_path)
                    print_count += 1
                condition_path.append(' -> '.join(reversed(path)))
                path.pop()
            return

        for condition in cg[node]:
            condition_class = condition.rsplit('.', 1)[0]
            node_class = node.rsplit('.', 1)[0]
            if self.hierarchy_graph.is_subclass(node_class, condition_class):
                condition = node_class
            self.print_condition(node, condition, condition_path, cg, path, print_count, max_print)

        path.pop()
