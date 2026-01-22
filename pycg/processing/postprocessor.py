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
import ast
import re

from copy import deepcopy
from pycg import utils
from pycg.machinery.definitions import Definition
from pycg.processing.base import ProcessingBase
from pycg.processing.preprocessor import PreProcessor


class PostProcessor(ProcessingBase):
    def __init__(
            self,
            input_file,
            modname,
            import_manager,
            scope_manager,
            def_manager,
            class_manager,
            module_manager,
            source_manager,
            middle_manager,
            intersection_manager,
            sink_manager,
            condition_manager,
            code_contents,
            modules_analyzed=None,
    ):
        super().__init__(input_file, modname, modules_analyzed, code_contents)
        self.import_manager = import_manager
        self.scope_manager = scope_manager
        self.def_manager = def_manager
        self.class_manager = class_manager
        self.module_manager = module_manager
        self.source_manager = source_manager
        self.middle_manager = middle_manager
        self.intersection_manager = intersection_manager
        self.sink_manager = sink_manager
        self.condition_manager = condition_manager
        self.code_contents = code_contents
        self.closured = self.def_manager.transitive_closure()
        self.taints = self.def_manager.transitive_taints()
        self.middle_skip = dict()
        self.hierarchy_graph = self.sink_manager.get_hierarchy_graph()
        self.extra_mods = set()
        self.exec_preProcessor_flag = False
        self.is_call_middle = False
        self.super_object = None

    def visit_Lambda(self, node):
        counter = self.scope_manager.get_scope(self.current_ns).inc_lambda_counter()
        lambda_name = utils.get_lambda_name(counter)
        self.module_manager.get(self.modname).add_classes_and_methods(lambda_name)
        super().visit_Lambda(node, lambda_name)

    def visit_Call(self, node):
        self.visit(node.func)
        func_name = self.determine_method_to_analyze(node)
        if self.exec_preProcessor_flag:
            self.closured = self.def_manager.transitive_closure()
            self.exec_preProcessor_flag = False
        if func_name == 'skip':
            return
        cur_defi = self.def_manager.get(self.current_ns)
        if cur_defi and len(cur_defi.get_context_def()) > 0:
            for ctx_current_ns_def in list(cur_defi.get_context_def()):
                cs_ctx = obj_ctx = ''
                if '@' in ctx_current_ns_def.get_ns():
                    cs_ctx, obj_ctx, _ = re.split(r'[@:]', ctx_current_ns_def.get_ns())
                self._visit_call(node, func_name, cs_ctx=cs_ctx, obj_ctx=obj_ctx)
        else:
            self._visit_call(node, func_name)

    def _visit_call(self, node, func_name, cs_ctx='', obj_ctx=''):
        names = self.retrieve_call_names(node, cs_context=cs_ctx, obj_context=obj_ctx)
        delete = {name.split(':')[1] for name in names if '@' in name}
        names = type(names)(name for name in names if name not in delete)
        if not names or bool(set(self.sink_manager.get_resource_points()) & names):
            self.process_no_names_fun(node, func_name)
            return

        field_anno_cls = None
        if isinstance(node.func, ast.Attribute):
            re_decode = self.decode_node(node.func.value)
            for re in re_decode:
                if re.get_type() == utils.constants.CLS_DEF:
                    re_cls = re.get_ns()
                    if not field_anno_cls or self.hierarchy_graph.is_subclass(field_anno_cls, re_cls):
                        field_anno_cls = re_cls
                elif re.get_ns() in self.sink_manager.get_node(self.modname)['sink_field']:
                    field_cls = self.sink_manager.get_node(self.modname)['sink_field'].get(re.get_ns())
                    if not field_anno_cls or self.hierarchy_graph.is_subclass(field_anno_cls, field_cls):
                        field_anno_cls = field_cls

        sig_caller_cls = '.'.join([self.modname] + self.class_stack)
        class_name = ''
        nfv = getattr(node.func, 'value', None)
        if isinstance(nfv, ast.Call) and isinstance(nfv.func, ast.Name):
            class_name = nfv.func.id

        self.last_called_names = names

        del_flag = True
        for name in names:
            parts = name.split('.')
            times = min(3, len(parts))
            is_middle = False
            for i in range(1, times + 1):
                sig_name = '.'.join(parts[-i:])
                if sig_name in self.sink_manager.get_potent_method_nodes():
                    break
                if sig_name in self.middle_manager.get_potent_method_nodes():
                    self.is_call_middle = True
                    is_middle = True
                    inter = self.intersection_manager.create_node(self.current_ns)
                    if field_mods := self.middle_manager.get_potent_method_node(sig_name):
                        sig_name_list = sig_name.split('.')
                        if len(sig_name_list) > 1:
                            add_value = sig_name_list[1]
                        else:
                            add_value = sig_name
                        self.middle_skip.setdefault(self.current_ns, set()).add(add_value)
                        self.save_callee_info(inter, field_mods, [], sig_name, node.lineno)
                    break
            if is_middle:
                continue

            cls_name = name.rsplit('.', 1)[0]
            if (
                    (field_anno_cls
                     and not self.hierarchy_graph.is_subclass(cls_name, field_anno_cls)
                     and not self.hierarchy_graph.is_subclass(field_anno_cls, cls_name)
                     and self.hierarchy_graph.have_common_parent(cls_name, field_anno_cls))
                    or (class_name == 'super' and not self.hierarchy_graph.is_subclass(sig_caller_cls, cls_name))
            ):  # todo
                continue

            defi = self.def_manager.get(name)
            if not defi:
                continue
            ctx = ''
            if defi.get_type() == utils.constants.CLS_DEF:
                self.update_parent_classes(defi)
                origin_defi = defi
                defi = self.def_manager.get(
                    utils.join_ns(origin_defi.get_ns(), utils.constants.CLS_INIT)
                )
                if self.sink_manager.in_need_context(name) and defi:
                    ctx = self.current_ns + '+' + str(node.lineno) + '@' + name + ':'
                    defi_mod = defi.get_module_name()
                    ctx_cls_ns = ctx + origin_defi.get_ns()
                    if not self.def_manager.get(ctx_cls_ns):
                        ctx_cls_def = self.def_manager.create(ctx_cls_ns, utils.constants.CLS_DEF, defi_mod)
                        origin_defi.add_context_def(ctx_cls_def)
                        origin_defi.add_context_def(origin_defi)
                    ctx_target_ns = ctx + defi.get_ns()
                    if func_name == 'super':
                        self.super_object = ctx_cls_ns
                        self.sink_manager.add_module_nodes_dict(self.current_ns + '+' + str(node.lineno), ctx.replace(':', ''))
                    origin_defi = defi
                    defi = self.def_manager.get(ctx_target_ns)
                    if not defi:
                        defi = self.def_manager.create(ctx_target_ns, utils.constants.FUN_DEF, defi_mod)
                    origin_defi.add_context_def(defi)
                if not defi:
                    self.iterate_call_args_class_filed(origin_defi, node)
                    continue
            elif name.endswith('.__init__') and class_name == 'super':
                name = name[:-len('.__init__')]
                cls_defi = self.def_manager.get(name)
                ctx = '@' + sig_caller_cls + ':'
                defi_mod = defi.get_module_name()
                ctx_cls_ns = ctx + cls_defi.get_ns()
                if not self.def_manager.get(ctx_cls_ns):
                    ctx_cls_def = self.def_manager.create(ctx_cls_ns, utils.constants.CLS_DEF, defi_mod)
                    cls_defi.add_context_def(ctx_cls_def)
                    cls_defi.add_context_def(cls_defi)
                ctx_target_ns = ctx + defi.get_ns()
                origin_defi = defi
                defi = self.def_manager.get(ctx_target_ns)
                if not defi:
                    defi = self.def_manager.create(ctx_target_ns, utils.constants.FUN_DEF, defi_mod)
                origin_defi.add_context_def(defi)
                if not defi:
                    self.iterate_call_args_class_filed(origin_defi, node)
                    continue

            if "copy_context.run" in names and del_flag and len(node.args) > 0:
                del node.args[0]
                del_flag = False

            self.iterate_call_args(defi, node, ctx)

    def process_no_names_fun(self, node, func_name):
        self.last_chance_to_save(node)
        if isinstance(func_name, set):
            import_set = self.import_manager.get_node(self.modname)['imports']
            for field in func_name:
                if field_mods := self.middle_manager.get_potent_method_node(field):
                    inter = self.intersection_manager.create_node(self.current_ns)
                    self.middle_skip.setdefault(self.current_ns, set()).add(field.split('.')[1])
                    self.save_callee_info(inter, field_mods, import_set, field, node.lineno)
        elif func_name == 'eval' and len(node.args) == 1 and isinstance(node.args[0], ast.Constant):
            for stmt in ast.parse(node.args[0].value).body:
                self.generic_visit(stmt)
        elif func_name in self.sink_manager.get_resource_methods():
            param_index_set = self.sink_manager.get_resource_param_index().get(func_name)
            self.iterate_taint_args(None, node, param_index_set)
        elif func_name == 'map' and len(node.args) == 2 and isinstance(node.args[1], ast.List):
            func = node.args[0]
            for iter in node.args[1].elts:
                call_node = ast.Call(func=func, args=[iter], keywords=[])
                self.visit(call_node)
        elif func_name == 'append' and len(node.args) == 1 and isinstance(node.func, ast.Attribute):
            decodes = self.decode_node(node.func.value)
            append_decodes = self.decode_node(node.args[0])
            arg_defi_name_list = []
            if isinstance(node.args[0], ast.Call) and len(append_decodes) == 0:
                if len(node.args[0].args) > 0:
                    append_decodes = self.decode_node(node.args[0].args[0])

            for append_decode in append_decodes or []:
                if isinstance(append_decode, Definition):
                    arg_defi_name = append_decode.get_ns()
                    arg_defi_name_list.append(arg_defi_name)
            for decode in decodes:
                if not isinstance(decode, Definition) or not arg_defi_name_list:
                    continue
                for list_name in self.closured.get(decode.get_ns(), []):
                    list_def = self.def_manager.get(list_name)
                    if '<list' in list_name:
                        for arg_defi_name in arg_defi_name_list:
                            list_def.get_name_pointer().add(arg_defi_name)
                    elif list_def.get_type() != utils.constants.CLS_DEF:
                        for arg_defi_name in arg_defi_name_list:
                            arg_defi = self.def_manager.get(arg_defi_name)
                            list_def.get_name_pointer().add(arg_defi_name)
                            arg_defi.get_taint_pointer().add(list_name)
        elif func_name == 'Process' and getattr(node.func.value, 'id', None) == 'multiprocessing':
            arg_fun = args_args = None
            for arg in node.keywords:
                if arg.arg == 'target':
                    arg_fun = arg.value
                elif arg.arg == 'args':
                    args_args = arg.value.dims
            call_node = ast.Call(func=arg_fun, args=args_args, keywords=[])
            self.visit_Call(call_node)

    def last_chance_to_save(self, node):
        if (
                self.current_ns.endswith('__init__')
                and getattr(node.func, 'attr', None) == '__init__'
                and getattr(getattr(node.func, 'value', None), 'func', None)
                and getattr(node.func.value.func, 'id', None) == 'super'
        ):
            mod_class = self.current_ns.rsplit('.', 1)[0]
            class_name = mod_class.replace(self.modname + ".", "")
            module = self.module_manager.get(self.modname)

            if class_name not in module.get_classes():
                return

            fields = module.get_class(class_name)['fields']
            for keyword in node.keywords:
                if keyword.arg and mod_class + "." + keyword.arg in fields.keys():
                    keyword_defi = self.def_manager.get(self.current_ns + "." + keyword.arg)
                    if not keyword_defi:
                        continue
                    field_defi = self.def_manager.get(mod_class + "." + keyword.arg)
                    if not field_defi:
                        continue
                    field_defi.get_name_pointer().merge(keyword_defi.get_name_pointer())

    def iterate_taint_args(self, defi, node, param_index=None):
        for pos, arg in enumerate(node.args):
            if param_index and pos not in param_index:
                continue
            self.visit(arg)
            decoded = self.decode_node(arg)
            if not defi:
                if not decoded:
                    if isinstance(arg, ast.Call):
                        self.iterate_taint_args(defi, arg)
                        continue
                    elif isinstance(arg, ast.Attribute):
                        decoded = self.decode_node(arg.value)
                for param_def in decoded:
                    if isinstance(param_def, Definition):
                        lit_values = param_def.get_lit_pointer().get()
                        if not lit_values or (lit_value == 'UNKNOWN' for lit_value in lit_values):
                            param_def.get_taint_pointer().add('Taint-Sink-' + self.current_ns)
                        else:
                            continue

        for pos, keyword in enumerate(node.keywords):
            if param_index and pos not in param_index:
                continue
            self.visit(keyword.value)
            decoded = self.decode_node(keyword.value)
            if not defi:
                if not decoded and isinstance(keyword.value, ast.Call):
                    self.iterate_taint_args(defi, keyword.value)
                    continue
                for param_def in decoded:
                    if isinstance(param_def, Definition):
                        lit_values = param_def.get_lit_pointer().get()
                        if not lit_values or any(not isinstance(lit_value, (str, int)) for lit_value in lit_values):
                            param_def.get_taint_pointer().add('Taint-Sink-' + self.current_ns)
                        else:
                            continue

    def iterate_call_args_class_filed(self, defi, node):
        for pos, arg in enumerate(node.args):
            self.visit(arg)
            decoded = self.decode_node(arg)
            if defi.get_type() == utils.constants.CLS_DEF:
                arg_names = defi.get_name_pointer().get_pos_arg(pos)
                if not arg_names:
                    continue
                for arg_name in arg_names:
                    arg_def = self.def_manager.get(arg_name)
                    if not arg_def:
                        continue
                    for d in decoded:
                        if isinstance(d, Definition):
                            arg_def.get_name_pointer().add(d.get_ns())
                            d.get_taint_pointer().add(arg_name)
                        else:
                            arg_def.get_lit_pointer().add(d)
            else:
                for d in decoded:
                    if isinstance(d, Definition):
                        defi.get_name_pointer().add_pos_arg(pos, None, d.get_ns())
                    else:
                        defi.get_name_pointer().add_pos_lit_arg(pos, None, d)

        for keyword in node.keywords:
            self.visit(keyword.value)
            decoded = self.decode_node(keyword.value)
            if defi.get_type() == utils.constants.CLS_DEF and keyword.arg:
                arg_names = defi.get_ns() + '.' + keyword.arg
                arg_def = self.def_manager.get(arg_names)
                if not arg_def:
                    continue
                for d in decoded:
                    if isinstance(d, Definition):
                        arg_def.get_name_pointer().add(d.get_ns())
                    else:
                        arg_def.get_lit_pointer().add(d)
            else:
                for d in decoded:
                    if isinstance(d, Definition):
                        defi.get_name_pointer().add_arg(keyword.arg, d.get_ns())
                    else:
                        defi.get_name_pointer().add_lit_arg(keyword.arg, d)

    # For identifying methods related to sink methods that require both pre-processing and post-processing
    def determine_method_to_analyze(self, node):
        caller = None
        fun_name = None
        if isinstance(node.func, ast.Subscript):
            if not fun_name and hasattr(node.func, "value") and hasattr(node.func.value, "id"):
                fun_name = node.func.value.id
        else:
            fun_name = getattr(node.func, "attr", getattr(node.func, "id", None))
            if not fun_name and hasattr(node.func, 'func') and hasattr(node.func.func, 'id'):
                fun_name = node.func.func.id
                if fun_name not in self.sink_manager.get_potent_method_nodes():
                    orig_args = deepcopy(node.func.args)
                    node.func.args.extend(node.args)
                    self.determine_method_to_analyze(node.func)
                    node.func.args = orig_args
                    retrieve_names = self.retrieve_call_names(node)
                    if retrieve_names:
                        fun_name = retrieve_names.pop().split('.')[-1]
            if hasattr(node.func, "value"):
                caller = getattr(node.func.value, "id", getattr(node.func.value, "attr", None))

        if not fun_name:
            return None

        if fun_name in {'isinstance', 'print', 'error'}:
            return 'skip'

        if (not caller and fun_name in __builtins__) or caller in self.sink_manager.get_resource_modules():
            if fun_name in self.sink_manager.get_resource_methods() and hasattr(node.func, "id"):
                return fun_name
            elif caller and f'{caller}.{fun_name}' in self.sink_manager.get_resource_points():
                return fun_name
            elif fun_name in __builtins__:
                return fun_name
            return None

        caller_point_values = []
        current_method = self.current_method
        while current_method:
            if not caller:
                caller_name = current_method + '.' + fun_name
            else:
                caller_name = current_method + "." + caller
            caller_point_values = self.closured.get(caller_name, [])
            tmp_point_values = caller_point_values.copy()
            for caller_point_value in tmp_point_values:
                if re.search(r'<dict\d+>$', caller_point_value) is not None:
                    caller_point_values |= self.closured.get(caller_point_value + '.<all>', set())  # todo
            if caller_point_values:
                break
            last_dot_index = current_method.rfind('.')
            if last_dot_index == -1:
                break
            current_method = current_method[:last_dot_index]
        input_mod = None
        caller_part_name = None
        if caller_point_values:
            for caller_point_value in caller_point_values:
                if caller_point_value in self.sink_manager.get_resource_modules():
                    return None

                caller_def = self.def_manager.get(caller_point_value)
                if not caller_def:
                    continue
                input_mod = caller_def.get_module_name()
                if caller_def.get_type() == utils.constants.CLS_DEF and caller_point_value.endswith(fun_name):
                    fun_name = '__init__'  # If the called entity is a class, it implies that its __init__ method will be invoked.

                caller_part_name = caller_point_value.replace(input_mod + ".", "")
                if input_mod in self.sink_manager.get_nodes():
                    potent_methods = self.sink_manager.get_nodes()[input_mod]["sink_method_user"]
                    # If present, this indicates that the method has already undergone pre-processing.
                    if (
                            (not caller and caller_part_name in potent_methods)
                            or caller_part_name + '.' + fun_name in potent_methods
                    ):
                        return fun_name

        self.iter_taints(caller_point_values, fun_name)
        sink_node = self.sink_manager.get_node(input_mod)
        for pos, arg in enumerate(node.args):
            self.visit(arg)
            decoded = self.decode_node(arg)
            if self.iter_args(decoded, caller_point_values, fun_name, arg):
                if isinstance(arg, ast.Name):
                    # Taint variable passing via constructors
                    self.is_sink_by_field_taint(input_mod, caller_part_name, pos)
                return fun_name

            if not caller_part_name:
                continue
            current_ns = caller_part_name if caller_part_name.endswith(fun_name) else f"{caller_part_name}.{fun_name}"
            if sink_node and current_ns in sink_node["sink_method_user"]:
                break

        for keyword in node.keywords:
            self.visit(keyword.value)
            decoded = self.decode_node(keyword.value)
            if self.iter_args(decoded, caller_point_values, fun_name, keyword.value):
                self.is_sink_by_field_taint(input_mod, caller_part_name, keyword.arg)
                return fun_name

        if self.class_stack and caller:
            module_manager = self.module_manager.get(self.modname)
            field_cls = module_manager.get_field_to_cls_name(self.class_stack[0] + '.' + caller)
            if field_cls:
                return {f'{cls_name}.{fun_name}' for cls_name in field_cls if cls_name}
        return fun_name

    def iter_taints(self, caller_point_values, fun_name):
        for caller_point_value in caller_point_values:
            if not caller_point_value.endswith(fun_name):
                caller_point_value = caller_point_value + "." + fun_name
            caller_taint = self.taints.get(caller_point_value)
            if caller_taint and any(element.startswith("Taint-Sink") for element in caller_taint):
                input_mod = self.def_manager.get(caller_point_value).get_module_name()
                caller_part_name = caller_point_value.replace(input_mod + '.', '')
                if (
                        input_mod in self.middle_manager.get_nodes()
                        and caller_part_name in self.middle_manager.get_potent_method_nodes()
                ):
                    # It is classified as middle, and therefore will not be analyzed further.
                    # print("no taint, because find middle " + input_mod + "." + caller_part_name)
                    return
                self.init_potent_sink_method(input_mod, caller_part_name, fun_name)

    def iter_args(self, decoded, caller_point_values, fun_name, arg):
        current_cls = '.'.join([self.modname] + self.class_stack)
        caller_method = self.current_method.replace(self.modname + '.', '')
        for d in decoded:
            if isinstance(d, str) or not self.determine_method_according_to_args(d, arg):
                continue
            if not caller_point_values:
                current_module_import = self.import_manager.get_node(self.modname)
                method_imports = current_module_import["method_imports"]
                sink_import = None
                if fun_name in method_imports:
                    sink_import = method_imports[fun_name]
                else:
                    if caller_method not in current_module_import["sink_imports"]:
                        return False
                    for item_import in current_module_import["sink_imports"][caller_method]:
                        if (
                                self.module_manager.get(item_import)
                                and fun_name in self.module_manager.get(item_import).get_methods()
                        ):
                            sink_import = item_import
                            break

                if not sink_import:
                    return True

                if sink_import not in self.sink_manager.get_nodes():
                    input_file = self.import_manager.get_node(sink_import)["filename"]
                    self.sink_manager.create_node(sink_import)
                    self.sink_manager.set_filepath(sink_import, input_file)
                    self.source_manager.add_source_file(input_file)
                if caller_method in self.sink_manager.get_node(self.modname)["pre_analyzed"]:
                    self.sink_manager.get_node(self.modname)["pre_analyzed"].remove(caller_method)
                self.exec_preProcessor(self.filename, self.modname, self.get_modules_analyzed())
                return True

            has_potent_sink = False
            for caller_point_value in caller_point_values:
                caller_point_def = self.def_manager.get(caller_point_value)
                if not caller_point_def:
                    continue
                input_mod = caller_point_def.get_module_name()
                if (
                        self.hierarchy_graph.have_common_parent(current_cls, caller_point_value)
                        and input_mod not in self.sink_manager.get_nodes()
                        and not self.hierarchy_graph.is_subclass(current_cls, caller_point_value)
                        and not self.hierarchy_graph.is_subclass(caller_point_value, current_cls)
                ):
                    continue
                caller_part_name = caller_point_value.replace(input_mod + '.', '')
                self.init_potent_sink_method(input_mod, caller_part_name, fun_name)
                has_potent_sink = True
            if has_potent_sink:
                return True

        if self.sink_manager.has_json_to_object(caller_method):
            for key, value in self.sink_manager.get_json_to_object(caller_method).items():
                if isinstance(arg, ast.Name) and arg.id in value:
                    for caller_point_value in caller_point_values:
                        input_mod = self.def_manager.get(caller_point_value).get_module_name()
                        caller_part_name = caller_point_value.replace(input_mod + '.', '')
                        self.init_potent_sink_method(input_mod, caller_part_name, fun_name)
                    return False

        return False

    def determine_method_according_to_args(self, d, arg):
        def_name = d.get_ns() if isinstance(d, Definition) else d
        if isinstance(def_name, list):
            for def_name_single in def_name:
                if self.determine_arg_in_sink(def_name_single):
                    return True
        elif isinstance(arg, ast.Starred):
            point_values = self.closured.get(def_name, [])
            for point_value in point_values:
                for count in range(0, 10):
                    elem = point_value + '.<r' + str(count) + '>'
                    elem_defi = self.def_manager.get(elem)
                    if not elem_defi:
                        break
                    if self.determine_arg_in_sink(elem_defi.get_ns()):
                        return True
        else:
            if self.determine_arg_in_sink(def_name):
                return True
        return False

    def init_potent_sink_method(self, input_mod, caller_part_name, fun_name, count=0):
        get_module = self.module_manager.get(input_mod)
        if not get_module or count > 2:
            return
        input_file = get_module.get_filename()
        if input_mod not in self.sink_manager.get_nodes():
            self.sink_manager.create_node(input_mod)
            self.sink_manager.set_filepath(input_mod, input_file)
            self.source_manager.add_source_file(input_file)
            if self.module_manager.get(self.modname):
                caller_message = self.module_manager.get(self.modname).get_caller_messages()
                self.sink_manager.update_caller_message(self.modname, caller_message)
        current_ns = caller_part_name if caller_part_name.endswith(fun_name) else f"{caller_part_name}.{fun_name}"
        sink_node = self.sink_manager.get_node(input_mod)
        if current_ns in sink_node["sink_method_user"]:
            return
        sink_node["sink_method_user"][current_ns] = {'callee': set(), 'caller': set()}
        self.sink_manager.add_potent_method_node(current_ns, {input_mod})
        self.extract_and_store_potential_sink_methods(current_ns, input_mod, sink_node)
        for sup_cls, sup_mod in get_module.get_class(caller_part_name)['sup_classes'].items():
            sup_cls_name = sup_cls.replace(sup_mod + '.', '')
            self.init_potent_sink_method(sup_mod, sup_cls_name, fun_name, count + 1)
        for caller_node in sink_node['caller_message'].get(current_ns) or []:
            if '#' in caller_node:
                caller_node, caller_method = caller_node.split('#')
            else:
                caller_node, caller_method = input_mod, caller_node
            self.init_potent_sink_method(caller_node, caller_method, caller_method)
        self.get_modules_analyzed().discard(input_mod)
        self.exec_preProcessor(input_file, input_mod, self.get_modules_analyzed())
        self.extra_mods.add(input_mod)

    def exec_preProcessor(self, input_file, input_mod, modules_analyzed):
        processor = PreProcessor(
            input_file,
            input_mod,
            self.import_manager,
            self.scope_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.sink_manager,
            self.code_contents,
            modules_analyzed=modules_analyzed,
        )
        processor.analyze()
        self.exec_preProcessor_flag = True

    def is_sink_by_field_taint(self, input_mod, caller_part_name, field_name):
        if not input_mod or not caller_part_name:
            return
        input_node = self.module_manager.get(input_mod)
        if not input_node:
            return
        fields = input_node.get_class(caller_part_name)['fields']
        if isinstance(field_name, int) and len(fields) >= field_name + 1:
            key_field = list(fields.keys())[field_name]
        else:
            key_field = f'{input_mod}.{caller_part_name}.{field_name}'
        for taint_method in fields.get(key_field, []):
            taint_method = taint_method.replace(caller_part_name + '.', '')
            self.init_potent_sink_method(input_mod, caller_part_name, taint_method)

    def visit_Assign(self, node):
        for target in node.targets:
            self.do_taint(node.value, target)
        self._visit_assign(node.value, node.targets)

    def do_taint(self, value, target):
        decoded = self.decode_node(value)

        if isinstance(target, ast.Tuple):
            for pos, elt in enumerate(target.elts):
                self.do_taint(value, elt)
        else:
            targetns = self._get_target_ns(target)
            for tns in targetns:
                if not tns:
                    continue
                defi = self.def_manager.get(tns)
                if not defi:
                    continue
                if isinstance(value, ast.Call) and (
                        not decoded or any(d and d.get_type() == utils.constants.EXT_DEF for d in decoded)):
                    for pos, arg in enumerate(value.args):
                        self.visit(arg)
                        arg_decoded = self.decode_node(arg)
                        for arg_def in arg_decoded:
                            if isinstance(arg_def, Definition):
                                arg_def.get_taint_pointer().add(defi.get_ns())
                        if isinstance(arg, ast.Subscript) and hasattr(arg.value, "value"):
                            parent_decoded = self.decode_node(arg.value.value)
                            for parent_def in parent_decoded:
                                if not parent_def:
                                    continue
                                parent_def.get_taint_pointer().add(defi.get_ns())
                elif isinstance(value, (ast.JoinedStr, ast.Attribute, ast.Dict, ast.Subscript)):
                    self.iter_add_taint(value, defi)

    def iter_add_taint(self, node, defi):
        if not node:
            return
        if isinstance(node, ast.Dict):
            for key in node.keys:
                self.iter_add_taint(key, defi)
            for value in node.values:
                self.iter_add_taint(value, defi)
        elif isinstance(node, ast.JoinedStr):
            for elem in node.values:
                if not isinstance(elem, ast.FormattedValue):
                    continue
                self.iter_add_taint(elem.value, defi)
        elif isinstance(node, ast.Attribute):
            self.iter_add_taint(node.value, defi)
        elif isinstance(node, ast.Subscript):
            self.iter_add_taint(node.value, defi)
        else:
            decode = self.decode_node(node)
            for d in decode:
                if isinstance(d, Definition):  # except Exception as e:
                    d.get_taint_pointer().add(defi.get_ns())

    def visit_For(self, node):
        is_call_middle = False
        func_name = None
        if isinstance(node.iter, ast.Call):
            self.visit_Call(node.iter)
            func_name = (getattr(node.iter.func, 'attr', None) or getattr(node.iter.func, 'id', None))
            if not self.retrieve_call_names(node.iter) and func_name in self.middle_skip.get(self.current_ns, set()):
                is_call_middle = True
        elif isinstance(node.iter, ast.BoolOp):
            if hasattr(node.iter, 'values'):
                for value in node.iter.values:
                    self.visit(value)
        elif isinstance(node.iter, ast.ListComp):
            self.visit_ListComp(node.iter)

        cur_defi = self.def_manager.get(self.current_ns)
        if cur_defi and len(cur_defi.get_context_def()) > 0:
            for ctx_current_ns_def in cur_defi.get_context_def():
                cs_ctx = obj_ctx = ''
                if '@' in ctx_current_ns_def.get_ns():
                    cs_ctx, obj_ctx, _ = re.split(r'[@:]', ctx_current_ns_def.get_ns())
                self._visit_for(node, func_name, is_call_middle, cs_ctx=cs_ctx, obj_ctx=obj_ctx)
        else:
            self._visit_for(node, func_name, is_call_middle)

        if hasattr(node, 'body'):
            super().visit_For(node)

    def _visit_for(self, node, func_name, is_call_middle, cs_ctx='', obj_ctx=''):
        # only handle name targets
        if isinstance(node.target, ast.Name):
            target_def = self.def_manager.get(utils.join_ns(self.current_ns, node.target.id))
            # if the target definition exists
            if target_def:
                iter_decoded = self.decode_node(node.iter)
                if len(iter_decoded) == 0 and isinstance(node.iter, ast.Attribute):
                    iter_decoded = self.decode_node(node.iter.value)
                self.handle_for_targets(iter_decoded, target_def)
                if is_call_middle:
                    for arg in node.iter.args:
                        self.iter_add_taint(arg, target_def)
        elif isinstance(node.target, ast.Tuple):
            for pos, elt in enumerate(node.target.elts):
                if not hasattr(elt, "id"):
                    continue
                target_def = self.def_manager.get(utils.join_ns(self.current_ns, elt.id))
                if not target_def:
                    continue
                iter_decoded = self.decode_node(node.iter)
                self.handle_for_targets(iter_decoded, target_def)

                if not iter_decoded and isinstance(node.iter, ast.Call):
                    func = getattr(node.iter.func, "id", func_name)
                    if func == 'enumerate' and node.iter.args:
                        self.visit(node.iter.args[0])
                        iter_decoded = self.decode_node(node.iter.args[0], cs_ctx, obj_ctx)
                        for item in filter(None, iter_decoded):
                            if len(item.get_context_def()) > 0:
                                for ctx_def in item.get_context_def():
                                    context_def = self.create_context_def(ctx_def, target_def)
                                    for name in self.closured.get(ctx_def.get_ns(), []):
                                        context_def.get_name_pointer().add(name)
                                        ctx_def.get_taint_pointer().add(context_def.get_ns())
                            elif '@' in item.get_ns():
                                context_def = self.create_context_def(item, target_def)
                                for name in self.closured.get(item.get_ns(), []):
                                    context_def.get_name_pointer().add(name)
                                    item.get_taint_pointer().add(context_def.get_ns())
                            else:
                                for name in self.closured.get(item.get_ns(), []):
                                    target_def.get_name_pointer().add(name)
                                    item.get_taint_pointer().add(target_def.get_ns())
                    elif func == 'items' and len(node.iter.args) == 0:
                        iter_decoded = self.decode_node(node.iter.func.value)
                        for item in filter(None, iter_decoded):
                            if isinstance(item, list):
                                for _item in item:
                                    for name in self.closured.get(_item.get_ns(), []):
                                        target_def.get_name_pointer().add(name)
                                        _item.get_taint_pointer().add(target_def.get_ns())
                            else:
                                for name in self.closured.get(item.get_ns(), []):
                                    target_def.get_name_pointer().add(name)
                                    item.get_taint_pointer().add(target_def.get_ns())

    def handle_for_targets(self, iter_decoded, target_def):
        def process_item(item):
            if not isinstance(item, Definition):
                return
            # return value for generators
            for name in self.closured.get(item.get_ns(), []):
                # If there exists a next method on the iterable
                # and if yes, add a pointer to it
                next_defi = self.def_manager.get(
                    utils.join_ns(
                        name,
                        utils.constants.NEXT_METHOD,
                        utils.constants.RETURN_NAME,
                    )
                )
                if next_defi:
                    for name in self.closured.get(next_defi.get_ns(), []):
                        target_def.get_name_pointer().add(name)
                        item.get_taint_pointer().add(target_def.get_ns())
                else:  # otherwise, add a pointer to the name
                    # (e.g. a yield)
                    target_def.get_name_pointer().add(name)
                    item.get_taint_pointer().add(target_def.get_ns())

        # assign the target to the return value
        # of the next function
        for item in iter_decoded:
            if isinstance(item, list):
                for sub_item in item:
                    process_item(sub_item)
            else:
                process_item(item)

    def visit_Return(self, node):
        self._visit_return(node)

    def visit_Yield(self, node):
        self._visit_return(node)

    def visit_YieldFrom(self, node):
        self._visit_return(node)

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):

        name_stack = self.name_stack[:]
        class_name = ".".join(name_stack[1:])
        fun_name = f"{class_name}.{node.name}" if class_name else node.name

        target_sinks = self.sink_manager.get_node(self.modname)
        if (
                target_sinks
                and (node.name != '__init__' and fun_name not in target_sinks["sink_method_user"])
                or (node.name == '__init__' and class_name not in target_sinks["sink_method_user"])
        ):
            return

        # here we iterate decorators
        if node.decorator_list:
            fn_def = self.def_manager.get(utils.join_ns(self.current_ns, node.name))
            reversed_decorators = list(reversed(node.decorator_list))

            # add to the name pointer of the function definition
            # the return value of the first decorator
            # since, now the function is a namespace to that point
            if hasattr(fn_def, "decorator_names") and reversed_decorators:
                last_decoded = self.decode_node(reversed_decorators[-1])
                for d in last_decoded:
                    if not isinstance(d, Definition):
                        continue
                    fn_def.decorator_names.add(
                        utils.join_ns(d.get_ns(), utils.constants.RETURN_NAME)
                    )

            previous_names = self.closured.get(fn_def.get_ns(), set())
            for decorator in reversed_decorators:
                # assign the previous_def
                # as the first parameter of the decorator
                decoded = self.decode_node(decorator)
                new_previous_names = set()
                for d in decoded:
                    if not isinstance(d, Definition):
                        continue
                    for name in self.closured.get(d.get_ns(), []):
                        return_ns = utils.join_ns(name, utils.constants.RETURN_NAME)

                        if d.get_ns() not in self.module_manager.get(self.modname).get_methods():
                            d = self.def_manager.get(name)

                        if self.closured.get(return_ns, None) is None:
                            continue

                        new_previous_names = new_previous_names.union(
                            self.closured.get(return_ns)
                        )

                        for prev_name in previous_names:
                            pos_arg_names = d.get_name_pointer().get_pos_arg(0)
                            if not pos_arg_names:
                                continue
                            for name in pos_arg_names:
                                arg_def = self.def_manager.get(name)
                                arg_def.get_name_pointer().add(prev_name)
                previous_names = new_previous_names

                if getattr(decorator, "id", None) == "property":
                    return_ns = utils.join_ns(fn_def.get_ns(), utils.constants.RETURN_NAME)
                    fn_def.get_name_pointer().add(return_ns)
        # todo This step needs to be executed before designating new target methods for taint variables,
        #  but it is uncertain whether this step will have an impact on performance.
        self.taints = self.def_manager.transitive_taints()
        super().visit_FunctionDef(node)
        self.super_object = None

    def visit_ClassDef(self, node):
        name_stack = self.name_stack[:]
        name_stack.append(node.name)
        class_name = ".".join(name_stack[1:])
        # self.resource_field = dict()
        target_sinks = self.sink_manager.get_node(self.modname)
        if not target_sinks or class_name not in target_sinks["sink_method_user"]:
            return

        # create a definition for the class (node.name)
        cls_def = self.def_manager.handle_class_def(self.current_ns, node.name, self.modname)

        # iterate bases to compute MRO for the class
        cls = self.class_manager.get(cls_def.get_ns())
        if not cls:
            cls = self.class_manager.create(cls_def.get_ns(), self.modname)

        cls.clear_mro()
        sup_class_fields = {}
        for base in node.bases:
            self.module_manager.get('langchain_community.tools.sql_database.tool')
            # all bases are of the type ast.Name
            self.visit(base)

            bases = self.decode_node(base)
            for base_def in bases:
                if not isinstance(base_def, Definition):
                    continue
                for final_class in self.closured.get(base_def.get_ns()) or []:
                    self.hierarchy_graph.add_edge(self.modname + '.' + class_name, final_class)
                names = set()
                if base_def.get_name_pointer().get():
                    names = base_def.get_name_pointer().get()
                else:
                    names.add(base_def.get_ns())
                for name in names:
                    # add the base as a parent
                    cls.add_parent(name)

                    # add the base's parents
                    parent_cls = self.class_manager.get(name)
                    if parent_cls:
                        cls.add_parent(parent_cls.get_mro())
                        self.extra_mods.add(parent_cls.get_module())
                        if parent_cls_defi := self.def_manager.get(name):
                            sup_class_fields.update(parent_cls_defi.get_name_pointer().get_args())

        cls.compute_mro()
        mod_cls = self.current_ns + '.' + class_name
        init_def = self.def_manager.get(utils.join_ns(mod_cls, utils.constants.CLS_INIT))
        defi = self.def_manager.get(mod_cls)
        if not init_def and defi:
            pos = len(defi.get_name_pointer().get_pos_names())
            for sup_cls_field in sup_class_fields.values():
                if not sup_cls_field:
                    break
                defi.get_name_pointer().add_pos_arg(pos, None, sup_cls_field.pop())
                pos += 1
        super().visit_ClassDef(node)

        class_fields = self.module_manager.get(self.modname).get_class(class_name)['fields']
        self.find_potent_sink_method_by_field(class_fields)

    def find_potent_sink_method_by_field(self, fields_dict):
        for field in fields_dict:
            if not fields_dict[field]:
                continue
            point_values = self.closured.get(field, set()).copy()
            if field_def := self.def_manager.get(field):
                for ctx_def in field_def.get_context_def():
                    point_values.update(self.closured.get(ctx_def.get_ns(), set()))
            find_loop = []
            self.iter_point_values(point_values, fields_dict, field, find_loop)

    def iter_point_values(self, point_values, fields_dict, field, find_loop):
        for point_value in point_values or set():
            if point_value in find_loop:
                continue
            find_loop.append(point_value)
            if re.search(r'<dict\d+>$', point_value) is not None:
                self.iter_point_values(self.closured.get(point_value + '.<all>'), fields_dict, field, find_loop)
                continue
            point_def = self.def_manager.get(point_value)
            if not point_def:
                continue
            mod_name = point_def.get_module_name()
            part_name = point_value.replace(mod_name + ".", "")
            if (
                    mod_name in self.sink_manager.get_nodes()
                    and
                    (
                            part_name in self.sink_manager.get_potent_method_nodes()
                            or part_name in self.sink_manager.get_node(mod_name)['sink_method_user']
                            or mod_name in self.sink_manager.get_resource_modules()
                    )
            ):
                for potent_method in fields_dict[field]:
                    self.init_potent_sink_method(self.modname, potent_method, potent_method)

    def visit_List(self, node):
        # Works similarly with dicts
        current_scope = self.scope_manager.get_scope(self.current_ns)
        list_counter = node.end_lineno
        list_name = utils.get_list_name(list_counter)
        list_full_ns = utils.join_ns(self.current_ns, list_name)

        # create a scope for the list
        self.scope_manager.create_scope(list_full_ns, current_scope)

        # create a list definition
        list_def = self.def_manager.get(list_full_ns)
        if not list_def:
            list_def = self.def_manager.create(list_full_ns, utils.constants.NAME_DEF, self.modname)
        current_scope.add_def(list_name, list_def)

        self.name_stack.append(list_name)
        for idx, elt in enumerate(node.elts):
            self.visit(elt)
            key_full_ns = utils.join_ns(list_def.get_ns(), utils.get_int_name(idx))
            key_def = self.def_manager.get(key_full_ns)
            if not key_def:
                key_def = self.def_manager.create(key_full_ns, utils.constants.NAME_DEF, self.modname)

            decoded_elt = self.decode_node(elt)
            for v in decoded_elt:
                if not v:
                    continue
                if isinstance(v, Definition):
                    key_def.get_name_pointer().add(v.get_ns())
                    list_def.get_name_pointer().add(v.get_ns())
                    v.get_taint_pointer().add(list_full_ns)
                else:
                    key_def.get_lit_pointer().add(v)
                    if isinstance(v, list):
                        for item in v:
                            if isinstance(item, Definition):
                                list_def.get_name_pointer().add(item.get_ns())
                                item.get_taint_pointer().add(list_full_ns)
                            else:
                                if isinstance(v, list):
                                    continue
                                list_def.get_name_pointer().add(item)
                    else:
                        list_def.get_name_pointer().add(v)

        self.name_stack.pop()

    def visit_ListComp(self, node):
        target_node = None
        if hasattr(node, "generators"):
            for gen_node in node.generators:
                self.visit(gen_node)
                if isinstance(gen_node.target, ast.Name):
                    target_node = gen_node.target
        if hasattr(node, 'elt'):
            current_scope = self.scope_manager.get_scope(self.current_ns)
            list_counter = node.end_lineno
            list_name = utils.get_list_name(list_counter)
            list_full_ns = utils.join_ns(self.current_ns, list_name)
            self.scope_manager.create_scope(list_full_ns, current_scope)
            list_def = self.def_manager.get(list_full_ns)
            if not list_def:
                list_def = self.def_manager.create(list_full_ns, utils.constants.NAME_DEF, self.modname)
            current_scope.add_def(list_name, list_def)
            decoded_elt = self.decode_node(target_node)
            for v in decoded_elt:
                if not v:
                    continue
                if isinstance(v, Definition):
                    list_def.get_name_pointer().add(v.get_ns())
                    v.get_taint_pointer().add(list_full_ns)

    def visit_Dict(self, node):
        # 1. create a scope using a counter
        # 2. Iterate keys and add them as children of the scope
        # 3. Iterate values and makes a points to connection with the keys
        current_scope = self.scope_manager.get_scope(self.current_ns)
        dict_counter = node.end_lineno
        dict_name = utils.get_dict_name(dict_counter)
        dict_full_ns = utils.join_ns(self.current_ns, dict_name)
        dict_full_value_ns = utils.join_ns(dict_full_ns, '<all>')

        # create a scope for the dict
        dict_scope = self.scope_manager.create_scope(dict_full_ns, current_scope)

        # Create a dict definition
        dict_def = self.def_manager.get(dict_full_ns)
        if not dict_def:
            dict_def = self.def_manager.create(dict_full_ns, utils.constants.NAME_DEF, self.modname)
        # add it to the current scope
        current_scope.add_def(dict_name, dict_def)

        dict_values_def = self.def_manager.get(dict_full_value_ns)
        if not dict_values_def:
            dict_values_def = self.def_manager.create(dict_full_value_ns, utils.constants.NAME_DEF, self.modname)
        dict_scope.add_def(dict_full_value_ns, dict_values_def)

        self.name_stack.append(dict_name)

        keys = getattr(node, 'keys', None) or [getattr(node, 'key', None)]
        values = getattr(node, 'values', None) or [getattr(node, 'value', None)]
        for key, value in zip(keys, values):
            if key:
                self.visit(key)
            if value:
                self.visit(value)
            decoded_key = self.decode_node(key)
            decoded_value = self.decode_node(value)

            # iterate decoded keys and values
            # to do the assignment operation
            for k in decoded_key:
                if isinstance(k, Definition):
                    # get literal pointer
                    names = k.get_lit_pointer().get()
                else:
                    names = set()
                    if isinstance(k, list):
                        continue
                    names.add(k)
                for name in names:
                    # create a definition for the key
                    if isinstance(name, int):
                        name = utils.get_int_name(name)
                    key_full_ns = utils.join_ns(dict_def.get_ns(), str(name))
                    key_def = self.def_manager.get(key_full_ns)
                    if not key_def:
                        key_def = self.def_manager.create(
                            key_full_ns, utils.constants.NAME_DEF, self.modname
                        )
                    dict_scope.add_def(str(name), key_def)
                    for v in decoded_value:
                        if isinstance(v, Definition):
                            key_def.get_name_pointer().add(v.get_ns())
                            dict_values_def.get_name_pointer().add(v.get_ns())
                        else:
                            key_def.get_lit_pointer().add(v)
                            dict_values_def.get_lit_pointer().add(v)
                if not names:
                    for v in decoded_value:
                        if isinstance(v, Definition):
                            dict_values_def.get_name_pointer().add(v.get_ns())
                        else:
                            dict_values_def.get_lit_pointer().add(v)
            if len(decoded_key) == 0:
                for v in decoded_value:
                    if isinstance(v, Definition):
                        dict_values_def.get_name_pointer().add(v.get_ns())
        self.name_stack.pop()

    def visit_DictComp(self, node):
        if hasattr(node, "generators"):
            for gen_node in node.generators:
                self.visit(gen_node)
        if hasattr(node, 'key') and hasattr(node, 'value'):
            self.visit_Dict(node)

    def visit_AnnAssign(self, node):
        is_call = False
        if isinstance(node.value, ast.Call):
            is_call = True
            for item in self.decode_node(node.value):
                if isinstance(item, Definition) and item.get_type() == utils.constants.EXT_DEF:
                    is_call = False
                    break

        if isinstance(node.value, ast.Dict) or is_call:
            self._visit_assign(node.value, [node.target])
        else:
            self.generic_visit(node)
            current_scope = self.scope_manager.get_scope(self.current_ns)
            if current_scope and hasattr(node.target, 'id'):
                init_def = self.def_manager.get(utils.join_ns(current_scope.get_ns(), utils.constants.CLS_INIT))
                ann_def = self.def_manager.get(utils.join_ns(current_scope.get_ns(), node.target.id))
                if hasattr(node.annotation, 'id') and ann_def:
                    ann_cls_def = self.def_manager.get(utils.join_ns(current_scope.get_ns(), node.annotation.id))
                    if ann_cls_def:
                        ann_def.get_name_pointer().add(ann_cls_def.get_ns())

                anno_type_set = self.identify_anno_class(node.annotation)
                if anno_type_set:
                    ann_def.add_potent_type(anno_type_set)

                if not init_def:
                    defi = self.def_manager.get(current_scope.get_ns())
                    pos = len(defi.get_name_pointer().get_pos_names())
                    for _pos, _values in defi.get_name_pointer().get_args().items():
                        if (ann_def and ann_def.get_ns() in _values) or node.target.id in _values:
                            pos = _pos
                            break

                    if ann_def:
                        defi.get_name_pointer().add_pos_arg(pos, None, ann_def.get_ns())
                    else:
                        defi.get_name_pointer().add_pos_arg(pos, None, node.target.id)

                    sink_node = self.sink_manager.get_node(self.modname)

                    if (
                            sink_node
                            and node.target.id in sink_node["sink_field"]
                            and hasattr(node.annotation, "id")
                    ):
                        self.import_manager.get_node(self.modname)["method_imports"]
                        field_defi = self.decode_node(node.annotation)[0]

                        field_type = None
                        if not field_defi:
                            anmod = self.import_manager.get_node(self.modname)["method_imports"].get(node.annotation.id)
                            if anmod:
                                field_type = anmod + "." + node.annotation.id
                        else:
                            field_type = field_defi.get_ns()

                        if field_type:
                            ann_def.get_name_pointer().add(field_type)
                            sink_node["sink_field"][ann_def.get_ns()] = field_type

    def identify_anno_class(self, node):
        type_set = set()
        if isinstance(node, ast.Subscript):
            type_set.update(self.identify_anno_class(node.slice))
        elif isinstance(node, ast.Tuple):
            for _node in node.elts:
                type_set.update(self.identify_anno_class(_node))
        elif isinstance(node, ast.Name):
            mod_set = self.sink_manager.get_potent_method_node(node.id)
            for mod_name in mod_set or []:
                type_set.add(f'{mod_name}.{node.id}')
        return type_set

    def visit_comprehension(self, node):
        if isinstance(node.target, ast.Name):
            target_ns = utils.join_ns(self.current_ns, node.target.id)
            if not self.def_manager.get(target_ns):
                defi = self.def_manager.create(target_ns, utils.constants.NAME_DEF, self.modname)
                self.scope_manager.get_scope(self.current_ns).add_def(
                    node.target.id, defi
                )
            self.visit_For(node)

    def visit_With(self, node):
        for item in node.items:
            self.visit(item)

        for stmt in node.body:
            self.visit(stmt)

    def visit_NamedExpr(self, node):
        self.visit(node.value)
        self.visit(node.target)
        self.do_taint(node.value, node.target)
        self._visit_assign(node.value, [node.target])

    def visit_withitem(self, node):
        value = node.context_expr
        target = node.optional_vars

        self.visit(value)
        decoded = self.decode_node(value)
        if not decoded:
            caller = None
            if hasattr(value, "func"):
                if hasattr(value.func, "value"):
                    class_name = None
                    if hasattr(value.func.value, "value") and getattr(value.func.value.value, "id", None) == "self":
                        class_name = ".".join(self.class_stack)
                    caller = getattr(value.func.value, "id", getattr(value.func.value, "attr", None))
                    if class_name:
                        caller = f"{self.modname}.{class_name}.{caller}"
                elif hasattr(value.func, "id") and value.func.id == "copy_context":
                    caller = value.func.id
            if caller:
                defi = self.def_manager.get(caller)
                if hasattr(self, "closured") and not defi:
                    defi = self.closured.get(self.current_ns + "." + caller)
                if defi:
                    if isinstance(defi, set):
                        decoded = []
                        for single_defi in defi:
                            decoded.append(self.def_manager.get(single_defi))
                    else:
                        decoded = [defi]
                elif caller in self.sink_manager.get_resource_modules() or caller == "copy_context":
                    defi = self.def_manager.create(caller, utils.constants.MOD_DEF, caller)
                    decoded = [defi]

        def do_assign(decoded, target):
            self.visit(target)
            targetns = self._get_target_ns(target)
            for tns in targetns:
                if not tns:
                    continue
                defi = self._handle_assign(tns, decoded)
                splitted = tns.split(".")
                self.scope_manager.handle_assign(
                    ".".join(splitted[:-1]), splitted[-1], defi
                )

        if target:
            do_assign(decoded, target)

    def update_parent_classes(self, defi):
        cls = self.class_manager.get(defi.get_ns())
        if not cls:
            return
        current_scope = self.scope_manager.get_scope(defi.get_ns())
        for parent in cls.get_mro():
            parent_def = self.def_manager.get(parent)
            if not parent_def:
                continue
            parent_scope = self.scope_manager.get_scope(parent)
            if not parent_scope:
                continue
            list(parent_scope.get_defs().keys())
            for key, child_def in current_scope.get_defs().items():
                if key == "__init__":
                    continue
                # resolve name from the parent_def
                names = self.find_cls_fun_ns(parent_def.get_ns(), key)

                new_ns = utils.join_ns(parent_def.get_ns(), key)
                new_def = self.def_manager.get(new_ns)
                if not new_def:
                    new_def = self.def_manager.create(new_ns, utils.constants.NAME_DEF, parent_def.get_module_name())

                # new_def.get_name_pointer().add_set(names) todo this is a problem
                # new_def.get_name_pointer().add(child_def.get_ns())

    def analyze_submodules(self):
        for imp in self.extra_mods:
            self.analyze_submodule(
                PostProcessor,
                imp,
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
                self.code_contents,
                modules_analyzed=self.get_modules_analyzed(),
            )
        self.extra_mods.clear()

    def analyze_submodule(self, cls, imp, *args, **kwargs):
        super().analyze_submodule(cls, imp, *args, **kwargs)

    def analyze(self):
        self.extra_mods.clear()
        self.visit(ast.parse(self.contents, self.filename))
        module_fields = self.module_manager.get(self.modname).get_fields()
        self.find_potent_sink_method_by_field(module_fields)
        self.analyze_submodules()
