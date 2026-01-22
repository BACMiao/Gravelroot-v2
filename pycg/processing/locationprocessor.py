import ast
import re

from pycg.utils.constants import BUILTIN_NAME

from pycg.processing.base import ProcessingBase


class LocationProcessor(ProcessingBase):
    def __init__(
            self,
            filename,
            modname,
            import_manager,
            def_manager,
            class_manager,
            module_manager,
            source_manager,
            middle_manager,
            sink_manager,
            location_messages,
            code_contents,
            save_middle,
            modules_analyzed=None,
    ):
        super().__init__(filename, modname, modules_analyzed, code_contents)

        self.modname = modname
        self.mod_dir = "/".join(self.filename.split("/")[:-1])

        self.import_manager = import_manager
        self.def_manager = def_manager
        self.class_manager = class_manager
        self.module_manager = module_manager
        self.source_manager = source_manager
        self.middle_manager = middle_manager
        self.sink_manager = sink_manager
        self.code_contents = code_contents
        self.save_middle = save_middle
        self.current_class = []
        self.location_messages = location_messages
        self.func_local_messages = dict()
        self.cls_local_messages = dict()
        self.have_return = False
        self.taint_variables = []
        self.taint_field = []
        self.is_assign_stmt = False

    def analyze_submodule(self, modname):
        super().analyze_submodule(
            LocationProcessor,
            modname,
            self.import_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.source_manager,
            self.middle_manager,
            self.sink_manager,
            self.location_messages,
            self.code_contents,
            self.save_middle,
            modules_analyzed=self.get_modules_analyzed(),
        )

    def visit_Module(self, node):
        self.import_manager.set_current_mod(self.modname, self.filename)
        mod = self.module_manager.get(self.modname)
        if not mod:
            mod = self.module_manager.create(self.modname, self.filename)

        self.generic_visit(node)

    def visit_ImportFrom(self, node):
        self.visit_Import(node, prefix=node.module, level=node.level)

    def visit_Import(self, node, prefix="", level=0):

        def handle_src_name(name):
            # Get the module name and prepend prefix if necessary
            src_name = name
            if prefix:
                src_name = prefix + '.' + src_name
            return src_name

        for import_item in node.names:
            src_name = handle_src_name(import_item.name)  # import *
            tgt_name = import_item.asname if import_item.asname else import_item.name  # as *
            imported_name = self.import_manager.handle_import(src_name, level)  # from *
            if not imported_name:
                if src_name in self.sink_manager.get_resource_modules():
                    self.find_sink_module(src_name, None)
                elif "." in src_name and src_name.split(".")[0] in self.sink_manager.get_resource_modules():
                    mod_name = src_name.split(".")[0]
                    if mod_name in ['os']:
                        continue
                    if tgt_name:
                        self.find_sink_module(mod_name, tgt_name)
                        self.location_messages["import_message"].setdefault(tgt_name, set()).add(mod_name)
                    else:
                        self.find_sink_module(mod_name, src_name.split(".")[-1])

                self.location_messages["import_message"].setdefault(tgt_name, set()).add(src_name)
                continue
            else:
                self.taint_variables.append(tgt_name)

            if not self.import_manager.get_filepath(imported_name):
                continue

            self.location_messages["import_message"].setdefault(tgt_name, set()).add(imported_name)

    def visit_ClassDef(self, node):
        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        self.current_class.append(node.name)
        module_manager = self.module_manager.get(self.modname)

        for base in node.bases:
            sup_name = None
            if isinstance(base, ast.Subscript):
                if hasattr(base, 'value') and hasattr(base.value, 'id'):
                    sup_name = base.value.id
                    self.location_messages['sup_class'].setdefault(node.name, set()).add(base.value.id)
            elif hasattr(base, 'id'):
                sup_name = base.id
                self.location_messages['sup_class'].setdefault(node.name, set()).add(sup_name)
            else:
                self.location_messages['sup_class'].setdefault(node.name, set())

            for sup_filed, cls_names in self.cls_local_messages.items():
                if sup_name and sup_name in sup_filed:
                    cur_filed = sup_filed.replace(sup_name, node.name)
                    module_manager.add_field_to_cls_name(cur_filed, cls_names)

        if (
                self.modname in self.middle_manager.get_nodes()
                and node.name in self.middle_manager.get_potent_method_nodes()
        ):
            self.current_class.pop()
            self.method_stack.pop()
            self.name_stack.pop()
            return

        for stmt in node.body:
            self.visit(stmt)

        self.taint_field.clear()
        self.current_class.pop()
        self.method_stack.pop()
        self.name_stack.pop()

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):
        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        self.have_return = False
        for pos, arg in enumerate(node.args.args):
            arg_name = getattr(arg, 'arg', None)
            if arg_name != 'cls' and arg_name != 'self':
                self.taint_variables.append(arg_name)
            if node.name == '__init__':
                self.taint_field.append(arg_name)

            arg_anno = getattr(arg, 'annotation', None)
            if isinstance(arg_anno, ast.Subscript):
                while isinstance(arg_anno.slice, ast.Subscript):
                    arg_anno = arg_anno.slice
                arg_anno = arg_anno.slice
                if isinstance(arg_anno, ast.Tuple):
                    for dim in arg_anno.dims:
                        anno_name = getattr(dim, 'id', None)
                        if not anno_name:
                            continue
                        self.func_local_messages.setdefault(arg_name, set()).add(anno_name)
            else:
                anno_name = getattr(arg_anno, 'id', None)
                if not anno_name:
                    continue
                self.func_local_messages.setdefault(arg_name, set()).add(anno_name)

        if node.args.kwarg:
            self.taint_variables.append('kwargs')

        for stmt in node.body:
            self.visit(stmt)

        sink_node = self.sink_manager.get_node(self.modname)
        if not self.have_return and sink_node:
            sink_node['no_return'].add(self.current_ns)

        self.taint_variables.clear()
        self.func_local_messages.clear()
        self.method_stack.pop()
        self.name_stack.pop()

    def find_middle_module(self, mod_met_name):
        middle = self.middle_manager.create_node(self.modname)
        root_middle = self.middle_manager.create_root_node(self.modname)
        middle['filename'] = self.filename
        init_temp = {'callee': set(), 'caller': set()}
        middle['potent_method'].setdefault(self.current_ns, init_temp)['callee'].add(mod_met_name)
        root_middle['potent_method'].setdefault(self.current_ns, init_temp)['callee'].add(mod_met_name)

    def find_sink_module(self, module_name, method_name):
        if self.modname not in self.sink_manager.get_nodes():
            self.init_sink_node()
        if method_name:
            sink_node = self.sink_manager.get_node(self.modname)
            sink_node['sink_module_user'].setdefault(method_name, set()).add(module_name)
            self.sink_manager.add_exist_mod(module_name)

    def find_sink_method(self, method_name):
        if self.modname not in self.sink_manager.get_nodes():
            self.init_sink_node()
        self.source_manager.add_source_file(self.filename)
        sink_node = self.sink_manager.get_node(self.modname)
        sink_root_node = self.sink_manager.get_root_node(self.modname)
        for sink_module in self.sink_manager.get_modules_by_method(method_name):
            sink_value = sink_module + ':' + method_name
            init_temp = {'callee': set(), 'caller': set()}
            sink_node['sink_method_user'].setdefault(self.current_ns, init_temp)['callee'].add(sink_value)
            sink_root_node['sink_method_user'].setdefault(self.current_ns, {'callee': set()})['callee'].add(sink_value)
            self.sink_manager.add_exist_meth_to_mod(sink_module)
            if sink_module in '<builtin>':
                self.sink_manager.add_exist_mod(sink_module)

    def visit_For(self, node):
        try:
            iter = ast.unparse(node.iter)
            target = ast.unparse(node.target)
        except Exception as e:
            print(e)
            return
        if 'self.' in iter:
            self.taint_variables.append(target)
        else:
            for taint_variable in self.taint_variables:
                if taint_variable in iter:
                    self.taint_variables.append(target)
                    break

        for item in node.body:
            self.visit(item)

    def visit_With(self, node):
        remove_local = None
        for item in node.items:
            if isinstance(item, ast.withitem):
                context_expr = item.context_expr
                receiver = ast.unparse(context_expr).split('.')[0]
                if (
                        item.optional_vars
                        and receiver in self.location_messages['import_message']
                        and receiver not in self.sink_manager.get_resource_modules()
                ):
                    delete_module = ast.unparse(item.optional_vars)
                    self.location_messages['import_message'][delete_module] = set()
                    remove_local = delete_module
                if item.optional_vars and 'open' in receiver and self.taint_edge(context_expr):
                    delete_module = ast.unparse(item.optional_vars)
                    self.taint_variables.append(delete_module)
                if isinstance(context_expr, ast.Call):
                    self.visit(context_expr)
            else:
                self.visit(item)

        for item in node.body:
            self.visit(item)

        if remove_local:
            self.location_messages['import_message'].pop(remove_local)

    def visit_Call(self, node):
        self.visit(node.func)
        method_name = getattr(node.func, 'attr', getattr(node.func, 'id', None))

        if not method_name:
            return

        if method_name == '__import__' and hasattr(node.args[0], 'value'):
            full = node.args[0].value
            top = full.split('.')[0]  # __import__ 返回顶层包
            self.find_sink_module(top, self.current_ns)
            return

        receiver = None
        call_obj = None
        if hasattr(node.func, 'value'):
            func_id = getattr(node.func.value, 'id', getattr(node.func.value, 'attr', None))
            self.add_sink_module_user(func_id, method_name)
            receiver = func_id

            if hasattr(node.func.value, 'value') and hasattr(node.func.value.value, 'id'):
                call_obj = node.func.value.value.id

        for import_name in self.location_messages['import_message'].get(method_name, set()):
            src_name = import_name.split('.')[0]
            if src_name in self.sink_manager.get_resource_modules():
                self.find_sink_module(src_name, self.current_ns)

        if (
                self.filename in self.middle_manager.get_potent_files()
                and method_name in self.middle_manager.get_resource_methods()
                and not self.filter_invalid_module_name(receiver, call_obj)
        ):
            line_num = {
                'filename': self.filename,
                'short_method': self.method_stack[-1],
                'method': f'{self.modname}.{self.current_method}',
                'call_line': node.lineno
            }
            self.save_middle.setdefault(f'{self.modname}#{self.current_method}', set()).add(frozenset(line_num.items()))
            self.find_middle_module('openai:' + method_name)

        sink_resources = self.sink_manager.get_resource_methods().get(method_name)
        sink_param_index = self.sink_manager.get_resource_param_index().get(method_name)
        if (
                sink_resources
                and not self.filter_invalid_sink_name(receiver, call_obj, sink_resources, method_name, node.func)
                and len(node.args) > 0
        ):
            skip = True
            for param_index in sink_param_index:
                if param_index >= len(node.args):
                    continue
                node_arg = node.args[param_index]
                if self.taint_edge(node_arg):
                    skip = False
                    break

            if skip:
                print('delete the method in sink ' + self.modname + '.' + self.current_ns)
                return

            self.find_sink_method(method_name)

    def filter_invalid_sink_name(self, receiver, call_obj, sink_resources, method_name, call_message):
        import_message = self.location_messages['import_message']
        if not receiver:
            is_sink = False
            if method_name in import_message:
                for import_name in import_message.get(method_name):
                    src_name = import_name.split('.')[0]
                    if src_name in sink_resources:
                        self.find_sink_module(src_name, self.current_ns)
                        is_sink = True
                        break
            if BUILTIN_NAME not in sink_resources and isinstance(call_message, ast.Name) and not is_sink:
                return True
            return False

        sink_resource_methods = self.sink_manager.get_resource_methods()

        if receiver == 'self':
            return True
        elif method_name in sink_resource_methods and receiver in sink_resource_methods.get(method_name):
            return False

        module_manager = self.module_manager.get(self.modname)
        current_class = '.'.join(self.current_class)
        full_name = f"{current_class}.{receiver}"
        module_fields = module_manager.get_field_to_cls_name(full_name)
        if not module_fields:
            module_fields = self.cls_local_messages.get(full_name)

        if module_fields:
            for type in module_fields:
                if type not in import_message:
                    last_method = type.split('.')[-1]
                    if last_method not in import_message:
                        continue
                    type = last_method
                tmodules = import_message[type]
                for tmodule in tmodules:
                    tmodule = tmodule.split('.')[0] if '.' in tmodule else tmodule
                    if tmodule in self.sink_manager.get_resource_modules():
                        return False
            return True

        if (
                receiver in import_message
                and receiver not in self.sink_manager.get_resource_modules()
        ):
            return True

        if receiver in self.func_local_messages:
            for rmodule in self.func_local_messages[receiver]:
                rmodule = rmodule.split('.')[0] if '.' in rmodule else rmodule
                if rmodule in self.sink_manager.get_resource_modules():
                    return False
            return True

        if call_obj and call_obj in self.func_local_messages:
            for rmodule in self.func_local_messages[call_obj]:
                rmodule = rmodule.split('.')[0] if '.' in rmodule else rmodule
                if rmodule in self.sink_manager.get_resource_modules():
                    return False
            return True

        if BUILTIN_NAME in sink_resources and receiver:
            return True

    def filter_invalid_module_name(self, receiver, call_obj):
        if not receiver:
            return False

        if receiver == 'self':
            return True

    def judge_filename(self, var_name, s):
        pattern = re.compile(rf"^{re.escape(var_name)}[_a-zA-Z]+$")
        if pattern.match(s):
            return False
        return True

    def taint_edge(self, arg_node):
        if isinstance(arg_node, list):
            for item in arg_node:
                return_flag = self.taint_edge(item)
                if return_flag:
                    return True
            return False
        elif isinstance(arg_node, ast.JoinedStr):
            for value in arg_node.values:
                if isinstance(value, ast.FormattedValue):
                    up_value = ast.unparse(value.value)
                    if 'self.' in up_value or up_value in self.taint_variables:
                        return True
            return False
        elif isinstance(arg_node, ast.IfExp):
            return self.taint_edge(arg_node.body)
        elif isinstance(arg_node, ast.Call):
            flag = True
            if arg_node.args:
                flag = self.taint_edge(arg_node.args)
            if isinstance(arg_node.func, ast.Attribute) and not flag:
                if self.taint_edge(arg_node.func) and 'group' in ast.unparse(arg_node.func):
                    flag = True
            return flag
        elif isinstance(arg_node, ast.List):
            return self.taint_edge(arg_node.elts)
        elif isinstance(arg_node, ast.BinOp):
            return self.taint_edge(arg_node.left) or self.taint_edge(arg_node.right)
        elif isinstance(arg_node, ast.ListComp):
            return self.taint_edge(arg_node.generators)
        elif isinstance(arg_node, ast.comprehension):
            return self.taint_edge(arg_node.iter)
        elif isinstance(arg_node, ast.GeneratorExp):
            return self.taint_edge(arg_node.elt)
        elif isinstance(arg_node, ast.Await):
            return self.taint_edge(arg_node.value)
        elif isinstance(arg_node, ast.Subscript):
            return self.taint_edge(arg_node.value)
        elif isinstance(arg_node, ast.Name) and arg_node.id == 'self':
            return True
        # elif isinstance(arg_node, ast.Name) and 'sqlalchemy' in (self.func_local_messages.get(arg_node.id) or ''):
        #     return False
        else:
            try:
                arg_names = ast.unparse(arg_node)
            except Exception as e:
                return False

        if 'self.' in arg_names:
            return True
        else:
            for taint_variable in self.taint_variables:
                if self.judge_filename(taint_variable, arg_names) and (
                        taint_variable in arg_names or arg_names in taint_variable):
                    return True

    def visit_Assign(self, node):
        self.is_assign_stmt = True
        self._visit_assign(node.value, node.targets)
        self.is_assign_stmt = False

    def _visit_assign(self, value, targets):
        self.visit(value)

        if isinstance(value, ast.Name):
            self.add_sink_module_user(value.id, None)

        if self.taint_edge(value):
            for target in targets:
                self.taint_variables.append(ast.unparse(target))

        module_manager = self.module_manager.get(self.modname)
        current_class = '.'.join(self.current_class)

        def inject_target_type(targets, module_set):
            for target in targets:
                if isinstance(target, ast.Name):
                    target_name = getattr(target, 'id')
                    self.func_local_messages.setdefault(target_name, set()).update(module_set)
                elif isinstance(target, ast.Attribute):
                    obj = getattr(getattr(target, 'value', None), 'id', None)
                    target_name = getattr(target, 'attr', None)
                    if obj and target_name:
                        module_manager.add_field_to_cls_name(current_class + '.' + target_name, module_set)
                        self.cls_local_messages.setdefault(current_class + '.' + target_name, set()).update(module_set)

        if isinstance(value, ast.Name) and value.id in self.func_local_messages:
            module_name_set = self.func_local_messages.get(value.id)
            inject_target_type(targets, module_name_set)
        elif isinstance(value, ast.Call):
            func_name = getattr(value.func, 'id', None)
            if not func_name:
                func_name = getattr(getattr(value.func, 'value', None), 'id', None)
            if func_name and func_name in self.location_messages['import_message']:
                module_name_set = self.location_messages['import_message'][func_name]
                inject_target_type(targets, module_name_set)
        elif (
                isinstance(value, ast.Attribute)
                and isinstance(value.value, ast.Name)
                and value.value.id == 'self'
                and current_class
        ):
            field_set = module_manager.get_field_to_cls_name(current_class + '.' + value.attr)
            if not field_set:
                return
            for target in targets:
                if isinstance(target, ast.Name):
                    self.cls_local_messages.setdefault(current_class + '.' + target.id, set()).update(field_set)

    def visit_Return(self, node):
        if not node or not node.value:
            return

        self.have_return = True

        if hasattr(node.value, 'id'):
            self.add_sink_module_user(node.value.id, None)
        self.visit(node.value)

    def add_sink_module_user(self, potent_module, method_name):
        resource_methods = self.sink_manager.get_resource_methods()
        if not potent_module or (not self.is_assign_stmt and method_name not in resource_methods):
            return
        if method_name and potent_module in ['os'] and method_name not in resource_methods:
            return
        sink_node = self.sink_manager.get_node(self.modname)
        module_name_set = self.location_messages['import_message'].get(potent_module)
        if sink_node and module_name_set:
            resource_modules = self.sink_manager.get_resource_modules()
            matching_modules = module_name_set.intersection(resource_modules)
            for sink_module in matching_modules:
                self.find_sink_module(sink_module, self.current_ns)

    def visit_AnnAssign(self, node):
        field_name = None
        if hasattr(node, 'target') and hasattr(node.target, 'id'):
            field_name = node.target.id
            self.taint_field.append(field_name)

        if not field_name or not self.current_class:
            return

        current_class = '.'.join(self.current_class)
        sign_field = current_class + '.' + field_name
        module_manager = self.module_manager.get(self.modname)

        def decode_node(node):
            if isinstance(node, ast.Subscript):
                if not decode_node(node.value):
                    decode_node(node.slice)
            elif isinstance(node, ast.Tuple):
                decode_node(node.elts)
            elif isinstance(node, list):
                for elem in node:
                    decode_node(elem)
            elif isinstance(node, ast.Constant):
                pass
            elif isinstance(node, ast.Call):
                decode_node(node.func)
            else:
                anno_name = getattr(node, 'id', None)
                if anno_name not in {'Optional', 'Union', 'SerializeAsAny', 'Any', None}:
                    module_manager.add_field_to_cls_name(sign_field, anno_name)
                    self.cls_local_messages.setdefault(sign_field, set()).add(anno_name)
                else:
                    return False

        decode_node(node.annotation)

        if (
                hasattr(node, "target")
                and hasattr(node, "value")
                and node.value and node.target
        ):
            self._visit_assign(node.value, [node.target])

    def visit_Subscript(self, node):
        pass

    def visit_Lambda(self, node, lambda_name=None):
        pass

    def visit_Dict(self, node):
        pass

    def visit_List(self, node):
        pass

    def analyze(self):
        if not self.import_manager.get_node(self.modname):
            self.import_manager.create_node(self.modname)
            self.import_manager.set_filepath(self.modname, self.filename)
        self.visit(ast.parse(self.contents, self.filename))
