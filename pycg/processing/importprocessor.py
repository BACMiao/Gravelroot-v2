import ast
import re

from pycg.processing.base import ProcessingBase
from pycg.utils.constants import CALL_Method
from pycg.utils.match import is_base_class_name


class ImportProcessor(ProcessingBase):
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
            import_chain,
            code_contents,
            save_if_stmt,
            save_loop_stmt,
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
        self.current_class = []
        self.import_chain = import_chain
        self.code_contents = code_contents
        self.save_if_stmt = save_if_stmt
        self.save_loop_stmt = save_loop_stmt
        self.is_init = False
        self.have_all_init = False
        self.import_names = []
        self.sink_module_variable = dict()
        self.sink_variable = dict()
        self.sink_field = dict()
        self.sink_method_field = dict()
        self.analyzed_call = None
        self.invoke_ext_met = set()
        self.assign_return_to_field = dict()
        self.hierarchy_graph = self.sink_manager.get_hierarchy_graph()
        self.func_global_param = set()
        self.abb_method = dict()
        self.sup_sink_method = set()
        self.assign_sink_field = set()

    def analyze_submodule(self, modname):
        super().analyze_submodule(
            ImportProcessor,
            modname,
            self.import_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.source_manager,
            self.middle_manager,
            self.sink_manager,
            self.import_chain,
            self.code_contents,
            self.save_if_stmt,
            self.save_loop_stmt,
            modules_analyzed=self.get_modules_analyzed(),
        )

    def visit_Module(self, node):
        self.import_manager.set_current_mod(self.modname, self.filename)

        mod = self.module_manager.get(self.modname)
        if not mod:
            mod = self.module_manager.create(self.modname, self.filename)
        get_sink = self.sink_manager.get_node(self.modname)
        if get_sink:
            self.sink_manager.update_caller_message(self.modname, mod.get_caller_messages())
        elif self.modname in self.middle_manager.get_nodes():
            self.middle_manager.update_caller_message(self.modname, mod.get_caller_messages())

        first = 1
        last = len(
            self.contents.splitlines())  # Here, self.contents can retrieve the contents of the Python file referenced by the entry point
        if last == 0:
            first = 0
        mod.add_method(self.modname, first, last)
        self.import_chain.append(self.modname)
        for item in node.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                mod.add_classes_and_methods(item.name)
        self.generic_visit(node)

        if self.filename.endswith("__init__.py") and not self.have_all_init:
            list_node = ast.List(elts=self.import_names, ctx=ast.Load())
            assign_node = ast.Assign(targets=[ast.Name(id="__all__", ctx=ast.Store())], value=list_node)
            self.visit(assign_node)

        self.import_names.clear()
        self.have_all_init = False
        self.import_chain.pop()
        self.modules_analyzed = self.modules_analyzed - self.sink_manager.get_nodes().keys()
        self.sink_manager.transitive_single_potent_method(self.modname)

    def visit_ImportFrom(self, node):
        self.visit_Import(node, prefix=node.module, level=node.level)

    def visit_Import(self, node, prefix="", level=0):

        def handle_src_name(name):
            # Get the module name and prepend prefix if necessary
            src_name = name
            if prefix:
                src_name = prefix + '.' + src_name
            return src_name

        if self.import_chain.count(self.modname) > 1:
            return

        analyzed_import = []
        for import_item in node.names:
            src_name = handle_src_name(import_item.name)  # import *
            tgt_name = import_item.asname if import_item.asname else import_item.name  # as *
            imported_name = self.import_manager.handle_import(src_name, level)
            if not imported_name:
                prefix = self.modname.split('.', 1)[0]
                if not src_name.startswith(prefix):
                    imported_name = self.import_manager.handle_import(prefix + '.' + src_name, level)
            ori_imported_name = imported_name
            if not imported_name:
                imported_name = src_name.replace('.' + tgt_name, '')
                self.invoke_ext_met.add(tgt_name)

            self.import_names.append(ast.Constant(value=tgt_name))

            fname = self.import_manager.get_filepath(imported_name)  #

            if not fname or (fname not in self.code_contents and not ori_imported_name):
                continue

            self.import_names.append(ast.Constant(value=tgt_name))

            if (
                    imported_name in self.import_chain
                    and imported_name not in analyzed_import
                    and imported_name in self.sink_manager.get_nodes()
                    and not fname.endswith('__init__.py')
            ):
                self.get_modules_analyzed().remove(imported_name)
                analyzed_import.append(imported_name)

            import_node = self.import_manager.get_node(self.modname)
            import_node['imports_nodes'][imported_name] = node

            if tgt_name != '*':
                full_key = imported_name + '.' + tgt_name
                import_node['imports_nodes'][full_key] = node
                import_node['method_imports'][tgt_name] = imported_name

            # only analyze modules under the current directory
            if self.import_manager.get_mod_dir() in fname:
                if imported_name not in self.modules_analyzed:
                    self.analyze_submodule(imported_name)

            import_node['import_tree'].add(imported_name)
            import_node['import_tree'].update(self.import_manager.get_node(imported_name)['import_tree'])

            if import_item.asname:
                tgt_name = import_item.name
                self.sink_variable[import_item.asname] = tgt_name

            if (
                    imported_name in self.sink_manager.get_nodes()
                    and
                    (
                            not tgt_name
                            or tgt_name == '*'
                            or tgt_name in self.sink_manager.get_node(imported_name)['sink_method_user']
                            or imported_name == tgt_name
                    )
                    and self.modname not in self.sink_manager.get_nodes()
            ):
                self.init_sink_node()
                self.source_manager.add_source_file(self.filename)

            if (
                    imported_name in self.middle_manager.get_nodes()
                    and (not tgt_name or tgt_name in self.middle_manager.get_node(imported_name)['potent_method'])
                    and self.modname not in self.middle_manager.get_nodes()
            ):
                self.middle_manager.create_node(self.modname)
                self.middle_manager.set_filepath(self.modname, self.filename)
                get_module = self.module_manager.get(self.modname)
                if get_module:
                    self.middle_manager.update_caller_message(self.modname, get_module.get_caller_messages())

    def visit_ClassDef(self, node):
        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        self.current_class.append(node.name)
        self.assign_return_to_field.clear()
        self.abb_method.clear()
        self.sup_sink_method.clear()
        get_module = self.module_manager.get(self.modname)
        get_module.add_class(self.current_ns)
        get_module.add_classes_and_methods(self.current_ns)
        get_module.add_classes_and_methods(node.name)

        for stmt in node.body:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                get_module.add_classes_and_methods(node.name + '.' + stmt.name)

        sup_class_dict = get_module.get_class(self.current_ns)['sup_classes']
        for base in node.bases:
            if len(sup_class_dict) >= len(node.bases):
                break
            base_name = None
            if isinstance(base, ast.Subscript):
                if hasattr(base, 'value') and hasattr(base.value, 'id'):
                    base_name = base.value.id
            elif hasattr(base, 'id'):
                base_name = base.id

            if not base_name:
                continue

            if base_name in get_module.get_classes_and_methods():
                parent_name = self.modname + '.' + base_name
                sup_class_dict[parent_name] = self.modname
                self.hierarchy_graph.add_edge(self.modname + '.' + self.current_ns, parent_name)
                continue

            import_node = self.import_manager.get_node(self.modname)
            method_imports = import_node['method_imports']
            import_part_name = None
            sup_mod_name = None
            if base_name in method_imports:
                sup_mod_name = method_imports[base_name]
                import_part_name = sup_mod_name + '.' + base_name
                sup_class_dict[import_part_name] = sup_mod_name
                self.import_manager.create_sink_edge(self.current_ns, import_part_name)
                self.hierarchy_graph.add_edge(self.modname + '.' + self.current_ns, import_part_name)
            else:
                import_nodes = import_node['imports_nodes']
                for import_module in import_node['imports']:
                    if (
                            import_module in self.module_manager.get_internal_modules()
                            and base_name in self.module_manager.get(import_module).get_classes()
                    ):
                        import_part_name = import_module
                        break
                if import_part_name and import_part_name in import_nodes:
                    sup_mod_name = import_part_name
                    sup_class = import_part_name + '.' + base_name
                    sup_class_dict[sup_class] = import_part_name
                    self.import_manager.create_sink_edge(self.current_ns, import_part_name)
                    self.hierarchy_graph.add_edge(self.modname + '.' + self.current_ns, sup_class)

            if sup_sink_node := self.sink_manager.get_node(sup_mod_name):
                cur_sink_node = self.sink_manager.get_node(self.modname)
                sup_user_message = sup_sink_node['sink_method_user']
                for sup_sink_method, sink_set in sup_user_message.items():
                    if sup_sink_method == base_name or sup_sink_method not in self.sink_manager.get_no_super_add():
                        continue
                    ss_meth_name = sup_sink_method.replace(base_name + '.', '')
                    if not node.name + '.' + ss_meth_name in get_module.get_classes_and_methods():
                        sub_meth = self.current_ns + '.' + ss_meth_name
                        if not cur_sink_node:
                            self.init_sink_node()
                            cur_sink_node = self.sink_manager.get_node(self.modname)
                        init_temp = {'callee': set(), 'caller': set()}
                        full_sup_met = f'{sup_mod_name}:{sup_sink_method}'
                        cur_sink_node['sink_method_user'].setdefault(sub_meth, init_temp)['callee'].add(full_sup_met)
                        sup_user_message[sup_sink_method]['caller'].add(self.modname + ':' + sub_meth)
                        self.extract_and_store_potential_sink_methods(sub_meth, self.modname, cur_sink_node)
                        self.sink_manager.add_potent_method_node(sub_meth, {self.modname})
                if cur_sink_node:
                    cur_sink_node['sink_field'] = sup_sink_node['sink_field'].copy()

        for stmt in node.body:
            self.visit(stmt)

        current_class = '.'.join(self.current_class)
        module_node = self.module_manager.get(self.modname).get_class(current_class)
        fields = module_node['fields']
        sink_node = self.sink_manager.get_node(self.modname)
        if not sink_node:
            self.class_clear()
            return
        for key, value in self.sink_field.items():
            for sink_module_user in fields[key]:
                sink_field = key.replace(self.modname + '.', '')
                sink_node['sink_field'][sink_field] = value
                if not isinstance(value, set):
                    value = {value}
                sink_node['sink_module_user'].setdefault(sink_module_user, set()).update(value)
                self.sink_manager.add_potent_module_node(sink_module_user, value)

        # for key, value in self.sink_method_field.items():
        #     for sink_module_user in fields.get(key) or {}:
        #         init_temp = {'callee': set(), 'caller': set()}
        #         sink_node['sink_method_user'].setdefault(sink_module_user, init_temp)['callee'].update(value)

        prefix = self.modname + '.' + current_class + '.'
        for sup_class, super_mod in module_node['sup_classes'].items():
            sup_class = sup_class.replace(super_mod + '.', '')
            sup_sink_node = self.sink_manager.get_node(super_mod)
            for sup_sink_field, sink_set in (sup_sink_node or {}).get('sink_field', {}).items():
                if not isinstance(sink_set, set):
                    continue
                target_filed = prefix + sup_sink_field.replace(sup_class + '.', '')
                for need_add_method in fields.get(target_filed, []):
                    if not sink_node:
                        sink_node = self.sink_manager.create_node(self.modname)
                    sink_node['sink_module_user'].setdefault(need_add_method, set()).update(sink_set)
                    self.sink_manager.add_potent_module_node(need_add_method, sink_set)

        self.class_clear()

    def class_clear(self):
        self.current_class.pop()
        self.method_stack.pop()
        self.name_stack.pop()
        self.sink_field.clear()
        self.sink_method_field.clear()

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):
        name_stack = self.name_stack[:]
        class_name = '.'.join(name_stack)
        outer_meth_flag = False
        func_global_param = set()

        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        module_node = self.module_manager.get(self.modname)
        self.module_manager.add_methods(node.name, self.current_ns)
        if class_name:
            module_node.get_class(class_name)['methods'].add(self.current_ns)
            caller_messages = module_node.get_caller_messages()
            if self.current_ns not in caller_messages:
                caller_messages[self.current_ns] = []
        else:
            module_node.add_module_method(self.current_ns)
        module_node.add_classes_and_methods(self.current_ns)
        module_node.add_classes_and_methods(node.name)
        self.abb_method[node.name] = self.current_ns

        decorator_list = getattr(node, 'decorator_list', [])
        for decorator in decorator_list:
            if isinstance(decorator, ast.Name):
                if decorator.id == 'abstractmethod':
                    module_node.add_abstract_methods(self.current_ns)
                    self.analyzed_call = None
                    self.method_stack.pop()
                    self.name_stack.pop()
                    self.sink_module_variable.clear()
                    self.sink_variable.clear()
                    return

                if candidate := self.resolve_qualified_method(decorator.id, module_node.get_classes_and_methods()):
                    module_node.get_caller_messages().setdefault(self.current_ns, []).append(candidate)

        self.init_sink_root_method(node)
        self.init_middle_root_method()

        for arg in node.args.args:
            func_global_param.add(arg.arg)
            annotated_id = None
            if isinstance(arg.annotation, ast.Subscript):
                if isinstance(arg.annotation.slice, ast.Name):
                    annotated_id = arg.annotation.slice.id
                elif isinstance(arg.annotation.slice, ast.Tuple):
                    for item in arg.annotation.slice.dims:
                        if isinstance(item, ast.Name):
                            annotated_id = item.id
            elif isinstance(arg.annotation, ast.Name):
                annotated_id = arg.annotation.id
            # if annotated_id in (self.sink_manager.get_potent_method_nodes() | self.middle_manager.get_potent_method_nodes()):
            if node.name == '__init__':
                module_node.add_field_to_cls_name(class_name + '.' + arg.arg, annotated_id)
            else:
                module_node.add_field_to_cls_name(self.current_method + '.' + arg.arg, annotated_id)

        self.analyzed_call = set()
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef) or isinstance(stmt, ast.AsyncFunctionDef) and not outer_meth_flag:
                outer_meth_flag = True
                self.func_global_param = func_global_param
                module_node.add_class(node.name)
            self.visit(stmt)

        if outer_meth_flag:
            self.func_global_param.clear()

        self.analyzed_call = None
        self.method_stack.pop()
        self.name_stack.pop()
        self.sink_module_variable.clear()
        self.sink_variable.clear()

    def init_sink_root_method(self, node):
        sink_node = self.sink_manager.get_node(self.modname)
        if sink_node:
            if self.current_ns in sink_node['sink_method_user']:
                sink_set = sink_node['sink_method_user'][self.current_ns]['callee']
                self.find_potent_sink(sink_set, False)
                self.sink_manager.add_no_super_add(self.current_ns)

            sink_set = sink_node.get('sink_module_user', {}).get(self.current_ns)
            if sink_set:
                self.find_potent_sink_module(sink_set)

            sink_module_user = sink_node['sink_module_user']
            if not sink_module_user:
                return
            for arg in node.args.args:
                if arg.annotation and hasattr(arg.annotation, 'id'):
                    arg_type = arg.annotation.id
                    if arg_type in sink_module_user:
                        self.sink_module_variable[arg.arg] = sink_module_user[arg_type]
                    if arg_type in self.sink_manager.get_potent_method_nodes():
                        self.sink_variable[arg.arg] = arg_type

    def init_middle_root_method(self):
        middle_node = self.middle_manager.get_node(self.modname)
        if middle_node:
            if (
                    self.current_ns in middle_node['potent_method']
                    and self.current_ns not in self.middle_manager.get_potent_method_nodes()
            ):
                sink_set = middle_node['potent_method'][self.current_ns]['callee']
                self.find_potent_middle(sink_set)

    def resolve_qualified_method(self, method, valid_keys):
        parts = self.current_ns.split(".")
        for i in range(len(parts), 0, -1):
            prefix = ".".join(parts[:i])
            candidate = f"{prefix}.{method}"
            if candidate in valid_keys:
                return candidate

        if method in valid_keys:
            return method

        return None

    def visit_Call(self, node):
        if isinstance(node.func, str):
            return
        self.visit(node.func)
        method_name = getattr(node.func, 'attr', None) or getattr(node.func, 'id', None)
        get_module = self.module_manager.get(self.modname)
        class_name = getattr(node.func.value, 'id', None) if hasattr(node.func, 'value') else None
        _current_class = '.'.join(self.current_class)
        current_class_name = _current_class
        index = self.current_ns.find(current_class_name)
        if index > 0:
            current_class_name = self.current_ns[:index + len(current_class_name)]
            _current_class = current_class_name
        if _current_class == '' and len(self.func_global_param) > 0 and len(self.method_stack) > 0:
            cls_module_message = get_module.get_class(self.method_stack[0])
        else:
            cls_module_message = get_module.get_class(_current_class)
        potent_method_nodes = self.sink_manager.get_potent_method_nodes()

        if not method_name:
            return

        for arg in node.args:
            self.visit(arg)
            self.process_attribute(arg, _current_class, cls_module_message, method_name, get_module)
            self.identify_vuln_param(arg, potent_method_nodes, get_module, class_name, method_name)
            if method_name == 'eval' and isinstance(arg, ast.Constant):
                for stmt in ast.parse(arg.value).body:
                    self.generic_visit(stmt)
        for keyword in node.keywords:
            self.visit(keyword)
            self.process_attribute(keyword.value, _current_class, cls_module_message, method_name, get_module)
            self.identify_vuln_param(keyword.value, potent_method_nodes, get_module, class_name, method_name)

        current_sink_module = self.sink_manager.get_node(self.modname)
        sink_field_flag = False
        if not class_name and current_sink_module:
            value = getattr(node.func, 'value', None)
            class_name = getattr(value, 'attr', None)

            if isinstance(value, ast.Attribute):
                inner_value = getattr(value, 'value', None)
                class_name = getattr(inner_value, 'attr', class_name)
            class_name = current_sink_module['sink_field'].get(class_name, class_name)
            if class_name in self.assign_return_to_field:
                class_name = self.assign_return_to_field[class_name]
            if class_name and class_name.endswith('-ext_met'):
                return
            sink_field_flag = True

        have_cls_value = False
        if class_name in self.sink_variable:
            class_name = self.sink_variable.get(class_name)
            have_cls_value = True
        method_name = self.sink_variable.get(method_name, method_name)

        call_self = False
        parent_cls = None
        if class_name in ['cls', 'self', _current_class]:
            call_self = True
            if method_name not in cls_module_message['methods']:
                parent_cls = self.hierarchy_graph.get_parent_class(f'{self.modname}.{current_class_name}')

        nfv = getattr(node.func, 'value', None)
        if isinstance(nfv, ast.Attribute) and isinstance(nfv.value, ast.Attribute):
            nfv = getattr(nfv, 'value', None)
        if isinstance(nfv, ast.Call) and isinstance(nfv.func, ast.Name):
            class_name = nfv.func.id
        elif nfv and getattr(nfv, 'value', None) and getattr(nfv.value, 'id', None) == 'self':
            # Take into account that a class’s instance variables may become tainted,
            # and their usage in other contexts could also invoke risky functions.
            if isinstance(nfv, ast.Subscript):
                return
            sign_field = f"{_current_class}.{nfv.attr}"
            self.find_field_in_self(sign_field, cls_module_message)

            if (result := get_module.get_field_to_cls_name(sign_field)) is not None:
                class_name = next(iter(result))
        elif nfv and getattr(nfv, 'id', None) == 'self':
            sign_field = f"{_current_class}.{method_name}"
            self.find_field_in_self(sign_field, cls_module_message)
        elif class_name and (
                result := get_module.get_field_to_cls_name(
                    f"{self.current_method + '.' if self.current_method else ''}{class_name}")) is not None:
            class_name = next(iter(result))
        elif isinstance(nfv, ast.Name) and nfv.id in self.func_global_param:
            out_method_name = self.current_method.split('.')[0]
            sign_field = f"{out_method_name}.{nfv.id}"
            self.find_field_in_self(sign_field, cls_module_message)

        receiver_mod, final_save_class = self.identify_receiver_class(node.func, current_class_name, method_name)
        if final_save_class and final_save_class != current_class_name:
            class_name = final_save_class

        import_node = self.import_manager.get_node(self.modname)
        be_analyzed_call = False

        if self.analyzed_call is not None:
            if method_name in self.analyzed_call:
                be_analyzed_call = True
            else:
                self.analyzed_call.add(method_name)

        if current_sink_module and not be_analyzed_call:
            potent_method_nodes = self.sink_manager.get_potent_method_nodes()
            tmp_class_name = None
            if (
                    (method_name in potent_method_nodes and not have_cls_value)
                    or (isinstance(node.func, ast.Name) and method_name + '-l' in potent_method_nodes)
                    or (method_name == 'cls' and current_class_name in potent_method_nodes)
                    or (class_name and class_name + '.' + method_name in potent_method_nodes)
                    or (
                    parent_cls
                    and
                    (tmp_class_name := self.invoke_parent_sink_method(parent_cls, method_name, potent_method_nodes))
            )
            ):
                self.assign_sink_field.add(method_name)
                is_invoke_cls = method_name == 'cls'
                if is_invoke_cls:
                    method_name = current_class_name + '.__init__'
                elif tmp_class_name:
                    method_name = tmp_class_name + '.' + method_name
                elif (method_name not in potent_method_nodes and not (method_name + '-l' in potent_method_nodes)) or (
                        class_name and class_name + '.' + method_name in potent_method_nodes):
                    method_name = class_name + '.' + method_name
                if sink_field_flag:
                    sink_modules = current_sink_module['sink_module_user'].get(current_class_name + '.__init__')
                    if sink_modules:
                        current_sink_module['sink_module_user'].setdefault(self.current_ns, set()).update(sink_modules)

                callee_mod_list = self.sink_manager.get_potent_method_node(method_name)
                if not callee_mod_list:
                    if method_name.endswith('.__init__'):
                        callee_mod_list = self.sink_manager.get_potent_method_node(method_name.replace('.__init__', ''))
                    elif isinstance(node.func, ast.Name) and method_name + '-l' in potent_method_nodes:
                        callee_mod_list = self.sink_manager.get_potent_method_node(method_name + '-l')
                callee_mod_list_copy = callee_mod_list.copy()
                for callee_mod in callee_mod_list_copy:
                    if '#' in callee_mod:
                        callee_mod, method_name = callee_mod.split('#')
                    sig_callee_cls = callee_mod + '.' + method_name.split('.')[0]
                    sig_caller_cls = self.modname + '.' + _current_class
                    if (
                            (self.hierarchy_graph.have_common_parent(sig_callee_cls, sig_caller_cls)
                             and not self.hierarchy_graph.is_subclass(sig_callee_cls, sig_caller_cls)
                             and not self.hierarchy_graph.is_subclass(sig_caller_cls, sig_callee_cls)
                             and call_self
                             and sig_callee_cls != sig_caller_cls)
                            or
                            (class_name == 'super'
                             and (not self.hierarchy_graph.is_subclass(sig_caller_cls, sig_callee_cls)
                                  or sig_caller_cls == sig_callee_cls))
                    ):
                        continue
                    callee_smu = self.sink_manager.get_node(callee_mod)['sink_method_user']
                    call_message = callee_smu.setdefault(method_name, {'callee': set(), 'caller': set()})
                    if method_name.endswith('__init__'):
                        replace_init_name = method_name.replace('.__init__', '')
                        call_message['callee'].add(self.modname + ':' + replace_init_name)
                        if is_invoke_cls:
                            callee_smu.get(replace_init_name)['caller'].add(self.modname + ':' + method_name)
                    call_message['caller'].add(self.modname + ':' + self.current_ns)
                    self.find_potent_sink({callee_mod + ':' + method_name}, is_invoke_cls)
                    self.sink_manager.add_no_super_add(self.current_ns)

            potent_module_nodes = self.sink_manager.get_potent_module_nodes()
            sink_module_mod = self.sink_manager.get_module_nodes_mod(method_name)
            if (
                    (method_name in potent_module_nodes
                     or (isinstance(node.func, ast.Name) and method_name + '-l' in potent_module_nodes)
                     or (method_name == 'cls' and current_class_name in potent_method_nodes)
                     or (class_name and class_name + '.' + method_name in potent_module_nodes))
                    and (not sink_module_mod or self.have_target_mod(sink_module_mod, import_node['import_tree']))
            ):
                if isinstance(node.func, ast.Name) and method_name + '-l' in potent_module_nodes:
                    suffix_method = method_name + '-l'
                else:
                    suffix_method = method_name
                global_module = self.sink_manager.get_potent_module_node(suffix_method, class_name)
                if len(global_module) > 0:
                    self.find_potent_sink_module(global_module)

        if not be_analyzed_call and self.modname in self.middle_manager.get_nodes():
            potent_nodes = self.middle_manager.get_potent_method_nodes()
            middle_met_name = method_name
            if not class_name and middle_met_name != 'cls':
                middle_met_name += '-l'

            callee_mod_list = None
            if middle_met_name in potent_nodes:
                callee_mod_list = self.middle_manager.get_potent_method_node(middle_met_name)
            elif method_name == 'cls' and current_class_name in potent_nodes:
                callee_mod_list = self.middle_manager.get_potent_method_node(current_class_name)
            elif class_name and class_name + '.' + method_name in potent_nodes:
                callee_mod_list = self.middle_manager.get_potent_method_node(class_name + '.' + method_name)
            elif class_name == 'self' and current_class_name + '.' + method_name in potent_nodes:
                callee_mod_list = self.middle_manager.get_potent_method_node(current_class_name + '.' + method_name)
            elif len(method_name) > 10 and (key := next((k for k in potent_nodes if k.endswith(method_name)), None)):
                callee_mod_list = self.middle_manager.get_potent_method_node(key)
                current_class_name = key.replace('.' + method_name, '')

            if callee_mod_list:
                copy_list = callee_mod_list.copy()
                for callee_mod in copy_list:
                    callee_smu = self.middle_manager.get_node(callee_mod)['potent_method']
                    if middle_met_name.endswith('-l'):
                        mid_meth_name = method_name
                    else:
                        mid_meth_name = f'{current_class_name}.{method_name}'
                    call_message = callee_smu.setdefault(mid_meth_name, {'callee': set(), 'caller': set()})
                    call_message['caller'].add(self.modname + ':' + self.current_ns)
                    self.find_potent_middle({callee_mod + ':' + mid_meth_name})

        if self.modname + '.' + method_name in get_module.get_fields():
            get_module.get_field(self.modname + '.' + method_name).add(self.current_ns)

        if _current_class and not method_name.startswith(f"{_current_class}."):
            curcls_met = f"{_current_class}.{method_name}"
        else:
            curcls_met = method_name
        # Inter-method calls within a class do not involve module imports; therefore,
        # import analysis is not conducted in such cases
        if nfv and hasattr(nfv, 'func') and hasattr(nfv.func, 'id') and nfv.func.id == 'super':
            for sup_class, sup_mod in get_module.get_class(_current_class)['sup_classes'].items():
                super_method = sup_class.replace(sup_mod + '.', '') + '.' + method_name
                caller_msg = self.module_manager.get(sup_mod).get_caller_messages()
                if super_method in caller_msg:
                    caller_msg[super_method].append(self.modname + '#' + self.current_ns)
        elif method_name == 'self' and _current_class + '.' + CALL_Method in get_module.get_caller_messages():
            _call_meth = f"{_current_class}.{CALL_Method}"
            if self.current_ns not in get_module.get_caller_messages()[_call_meth]:
                get_module.get_caller_messages()[_call_meth].append(self.current_ns)
            return
        elif (
                curcls_met in get_module.get_caller_messages() and self.current_ns not in
                get_module.get_caller_messages()[curcls_met] and curcls_met != self.current_ns
        ):
            get_module.get_caller_messages()[curcls_met].append(self.current_ns)
            return
        elif getattr(nfv, 'id', None) == 'self' or class_name == 'self' or class_name == _current_class:
            if curcls_met not in get_module.get_classes_and_methods():
                self.invoke_super_method_by_self(get_module, _current_class, method_name)
            messages = get_module.get_caller_messages().setdefault(curcls_met, [])
            if self.current_ns not in messages:
                messages.append(self.current_ns)
            return
        elif method_name in get_module.get_classes_and_methods() and (not final_save_class or call_self):
            method_name = self.abb_method.get(method_name, method_name)
            messages = get_module.get_caller_messages().setdefault(method_name, [])
            if self.current_ns not in messages:
                messages.append(self.current_ns)
            return
        elif receiver_mod and final_save_class and method_name:
            receiver_module = self.module_manager.get(receiver_mod)
            if method_name.startswith(final_save_class):
                receiver_method = method_name
            else:
                receiver_method = f'{final_save_class}.{method_name}'
            add_msg = self.modname + '#' + self.current_ns
            caller_msg = receiver_module.get_caller_messages().setdefault(receiver_method, [])
            if add_msg not in caller_msg:
                caller_msg.append(add_msg)

        import_part_name = None
        method_imports = import_node['method_imports']
        if method_name in method_imports:
            import_part_name = method_imports[method_name] + '.' + method_name
        elif nfv and hasattr(nfv, 'id') and nfv.id in method_imports:
            import_part_name = method_imports[nfv.id] + '.' + nfv.id
        else:
            for import_module in import_node['imports']:
                if import_module in import_node['sink_imports']:
                    continue
                if (
                        import_module in self.module_manager.get_internal_modules()
                        and method_name in self.module_manager.get(import_module).get_classes_and_methods()
                ):
                    import_part_name = import_module
                    break
        if import_part_name:
            current_ns = self.current_ns
            if not self.current_ns:
                current_ns = self.modname
            self.import_manager.create_sink_edge(current_ns, import_part_name)

    def invoke_parent_sink_method(self, parent_cls, method_name, potent_method_nodes):
        for parent in parent_cls:
            parent = parent.rsplit('.', 1)[1]
            if f'{parent}.{method_name}' in potent_method_nodes:
                return parent
        return None

    def have_target_mod(self, targets, import_tree):
        if not targets:
            return False
        for target in targets:
            if target in import_tree:
                return True
        return False

    def identify_vuln_param(self, arg, potent_method_nodes, get_module, class_name, method_name):
        if isinstance(arg, ast.Name):
            arg_name = getattr(arg, 'id')
            if arg_name == 'self':
                arg_name = '.'.join(self.current_class)
            callee_mods = potent_method_nodes.get(arg_name + '-l')
            if callee_mods:
                for callee_mod in callee_mods:
                    callee_smu = self.sink_manager.get_node(callee_mod)['sink_method_user']
                    call_message = callee_smu.setdefault(arg_name, {'callee': set(), 'caller': set()})
                    call_message['caller'].add(self.modname + ':' + self.current_ns)
                    self.find_potent_sink({callee_mod + ':' + arg_name}, False)
                    self.sink_manager.add_no_super_add(self.current_ns)
            elif arg_name in get_module.get_classes_and_methods():
                get_module.get_caller_messages().setdefault(arg_name, []).append(self.current_ns)
        elif isinstance(arg, ast.Attribute) and class_name == 'multiprocessing' and method_name == 'Process':
            call_node = ast.Call(func=arg, args=[], keywords=[])
            self.visit_Call(call_node)

    def process_attribute(self, arg, current_class, cls_module_message, method_name, get_module):
        """ Process parameters of type ast.Attribute and extract the self.xxx access information. """
        if isinstance(arg, ast.Attribute) and getattr(arg.value, 'id', None) == 'self':
            sign_field = f"{current_class}.{arg.attr}"
            self.find_field_in_self(sign_field, cls_module_message)
            if method_name == 'run':
                get_module.get_caller_messages().setdefault(sign_field, []).append(self.current_ns)

    def invoke_super_method_by_self(self, pre_module, current_class_name, method_name):
        for super_class_sig, super_modname in pre_module.get_class(current_class_name)['sup_classes'].items():
            super_class_name = super_class_sig.replace(super_modname + '.', '')
            if super_class_name == current_class_name:
                continue
            super_module = self.module_manager.get(super_modname)
            if super_class_name + '.' + method_name in super_module.get_classes_and_methods():
                key = super_class_name + '.' + method_name
                value = self.modname + '#' + self.current_ns
                caller_messages = super_module.get_caller_messages().setdefault(key, [])
                if value not in caller_messages:
                    caller_messages.append(value)
                return
            else:
                self.invoke_super_method_by_self(super_module, super_class_name, method_name)

    def find_field_in_self(self, sign_field, cls_module_message):
        cls_module_message['fields'].setdefault(self.modname + '.' + sign_field, set()).add(self.current_ns)

    def find_potent_middle(self, middle_set):
        current_ns = self.current_ns
        middle_node = self.middle_manager.get_node(self.modname)
        if not middle_node:
            middle_node = self.middle_manager.create_node(self.modname)
        init_temp = {'callee': set(), 'caller': set()}
        middle_node['potent_method'].setdefault(current_ns, init_temp)['callee'].update(middle_set)
        if not self.current_class:
            current_ns += '-l'
        self.middle_manager.add_potent_method_node(current_ns, {self.modname})
        self.extract_and_store_potential_methods(self.current_ns, self.modname, middle_node, current_ns.endswith('-l'))
        method_name = None
        if self.name_stack and len(self.name_stack) == len(self.current_class) + 1:
            method_name = self.name_stack[-1]
        current_class = '.'.join(self.current_class)
        self.find_potent_middle_in_supcls(self.modname,
                                          self.module_manager.get_internal_modules(),
                                          method_name,
                                          current_class)

    def find_potent_middle_in_supcls(self, modname, internal_modules, method_name, current_class):
        if not method_name:
            return
        sub_module_sup_msg = internal_modules[modname].get_class(current_class)['sup_classes']
        for sup_class in sub_module_sup_msg:
            module_name = sub_module_sup_msg[sup_class]
            if module_name in internal_modules:
                cls_name = sup_class.replace(module_name + '.', '')
                sup_module_msg = internal_modules[module_name]
                if module_name not in self.middle_manager.get_nodes():
                    self.middle_manager.create_node(module_name)
                    filename = sup_module_msg.get_filename()
                    self.middle_manager.set_filepath(module_name, filename)
                    self.source_manager.add_source_file(filename)
                    get_module = self.module_manager.get(module_name)
                    if get_module:
                        self.middle_manager.update_caller_message(module_name, get_module.get_caller_messages())

                middle_node = self.middle_manager.get_node(module_name)
                sub_node = self.middle_manager.get_node(modname)
                sub_method = current_class + '.' + method_name
                cls_method = cls_name + '.' + method_name

                init_temp = {'callee': set(), 'caller': set()}
                sig_callee_method = modname + ':' + sub_method
                middle_node['potent_method'].setdefault(cls_method, init_temp)['callee'].add(sig_callee_method)
                sig_caller_method = module_name + ':' + cls_method
                sub_node['potent_method'].get(sub_method)['caller'].add(sig_caller_method)
                self.middle_manager.add_potent_method_node(cls_method, {module_name})
                self.extract_and_store_potential_methods(cls_method, module_name, middle_node, False)
                if sup_module_msg.get_filename().endswith('__init__.py'):
                    realmod = self.import_manager.get_node(module_name)['method_imports'].get(cls_name)
                    if not realmod:
                        continue
                    sup_module_msg.get_class(cls_name)['sup_classes'][realmod + '.' + cls_name] = realmod
                    self.find_potent_middle_in_supcls(module_name, internal_modules, method_name, cls_name)
                else:
                    self.find_potent_middle_in_supcls(module_name, internal_modules, method_name, cls_name)
            else:
                self.find_potent_middle_in_supcls(module_name, internal_modules, module_name, current_class)

    def find_potent_sink(self, sink_set, skip_extract):
        current_ns = self.current_ns
        sink_node = self.sink_manager.get_node(self.modname)
        if not sink_node:
            return
        init_temp = {'callee': set(), 'caller': set()}
        sink_node['sink_method_user'].setdefault(current_ns, init_temp)['callee'].update(sink_set)
        if not skip_extract:
            self.extract_and_store_potential_sink_methods(current_ns, self.modname, sink_node)
        if not self.current_class:  # this is a local method
            current_ns += '-l'
        self.sink_manager.add_potent_method_node(current_ns, {self.modname})
        method_name = None
        if self.name_stack and len(self.name_stack) == len(self.current_class) + 1:
            method_name = self.name_stack[-1]
        current_class = '.'.join(self.current_class)
        self.find_potent_sink_in_supclass(self.modname,
                                          self.module_manager.get_internal_modules(),
                                          method_name,
                                          sink_set,
                                          'method',
                                          current_class)

    def find_potent_sink_module(self, sink_set):
        current_ns = self.current_ns
        sink_node = self.sink_manager.get_node(self.modname)
        if current_ns in sink_node['no_return']:
            return
        sink_node['sink_module_user'].setdefault(current_ns, set()).update(sink_set)
        self.extract_and_store_potential_sink_modules(current_ns, sink_node)
        if not self.current_class:  # this is a local method
            current_ns += '-l'
        self.sink_manager.add_potent_module_node(current_ns, sink_set)
        method_name = None
        if self.name_stack:
            method_name = self.name_stack[-1]
        current_class = '.'.join(self.current_class)
        self.find_potent_sink_in_supclass(self.modname,
                                          self.module_manager.get_internal_modules(),
                                          method_name,
                                          sink_set,
                                          'module',
                                          current_class)

    def find_potent_sink_in_supclass(self, modname, internal_modules, method_name, sink_set, sink_scope, current_class):
        if not method_name or method_name == current_class or sink_scope == 'module':
            return
        for sup_class in internal_modules[modname].get_class(current_class)['sup_classes']:
            init_temp = {"callee": set(), "caller": set()}
            module_name = internal_modules[modname].get_class(current_class)['sup_classes'][sup_class]
            cls_name = sup_class.replace(module_name + '.', '')
            if sup_class == modname + '.' + current_class:
                continue
            self.sink_manager.get_node(modname)['super_module'].setdefault(current_class, set()).add(
                module_name + '#' + cls_name)
            if module_name in internal_modules:
                if module_name not in self.sink_manager.get_nodes():
                    self.sink_manager.create_node(module_name)
                    self.sink_manager.set_filepath(module_name, internal_modules[module_name].get_filename())
                    self.source_manager.add_source_file(internal_modules[module_name].get_filename())
                    get_module = self.module_manager.get(module_name)
                    if get_module:
                        caller_message = get_module.get_caller_messages()
                        self.sink_manager.update_caller_message(module_name, caller_message)
                sink_node = self.sink_manager.get_node(module_name)
                sub_method = current_class + '.' + method_name
                sup_method = cls_name + '.' + method_name
                if sink_scope == 'method':
                    sup_call_message = sink_node['sink_method_user'].setdefault(sup_method, init_temp)
                    sup_call_message['callee'].add(modname + ':' + sub_method)
                    self.find_call_super_method(sup_method, internal_modules[module_name], sup_call_message)
                    self.sink_manager.add_potent_method_node(sup_method, {module_name})
                    sup_method_name = module_name + ':' + sup_method
                    self.sink_manager.get_node(modname)['sink_method_user'][sub_method]['caller'].add(sup_method_name)
                    self.extract_and_store_potential_sink_methods(sup_method, module_name, sink_node)
                else:
                    sink_node['sink_module_user'].setdefault(sup_method, set()).update(sink_set)
                    self.sink_manager.add_potent_module_node(sup_method, sink_set)
                    self.extract_and_store_potential_sink_modules(sup_method, sink_node)

                if internal_modules[module_name].get_filename().endswith('__init__.py'):
                    realmod = self.import_manager.get_node(module_name)['method_imports'].get(cls_name)
                    if not realmod:
                        continue
                    internal_modules[module_name].get_class(cls_name)['sup_classes'][realmod + '.' + cls_name] = realmod
                    self.find_potent_sink_in_supclass(module_name, internal_modules, method_name, sink_set, sink_scope,
                                                      cls_name)
                else:
                    self.find_potent_sink_in_supclass(module_name, internal_modules, method_name, sink_set, sink_scope,
                                                      cls_name)
                continue
            self.find_potent_sink_in_supclass(module_name, internal_modules, module_name, sink_set, sink_scope,
                                              current_class)

    def find_call_super_method(self, sup_method, sup_module, sup_call_message):
        for caller in sup_module.get_caller_messages().get(sup_method, {}):
            if '#' in caller:
                init_temp = {'callee': set(), 'caller': set()}
                sub_mod, sub_method = caller.split('#')
                sub_node = self.sink_manager.get_node(sub_mod)
                if not sub_node:
                    continue
                sub_sink_method_user = sub_node['sink_method_user']
                sub_sink_method_user.setdefault(sub_method, init_temp)['callee'].add(
                    sup_module.get_name() + ':' + sup_method)
                sup_call_message['caller'].add(sub_mod + ':' + sub_method)

    def visit_Assign(self, node):
        self._visit_assign(node.value, node.targets)

    def _visit_assign(self, value, targets):
        sign_field = None
        current_class = None
        field_name = None
        self.assign_sink_field.clear()
        get_module = self.module_manager.get(self.modname)
        is_filed = False
        if self.current_class:
            current_class = '.'.join(self.current_class)
            index = self.current_ns.find(current_class)
            if index > 0:
                current_class = self.current_ns[:index + len(current_class)]
            cls_module_message = get_module.get_class(current_class)
        for target in targets:
            self.visit(target)
            if current_class and isinstance(target, ast.Attribute) and getattr(target.value, 'id', None) == 'self':
                short_field = current_class + '.' + target.attr
                sign_field = self.modname + '.' + short_field
                field_name = short_field
                is_filed = True
                self.find_field_in_self(short_field, cls_module_message)
            elif hasattr(target, 'id'):
                field_name = target.id
                if field_name == '__all__':
                    self.is_init = True
                    self.have_all_init = True
                elif not self.current_ns:
                    sign_field = self.modname + '.' + field_name
                    get_module.add_field(sign_field)

        add_field_name_stack = False
        if not self.current_ns and field_name:
            self.name_stack.append(field_name)
            add_field_name_stack = True
        self.visit(value)
        if add_field_name_stack:
            self.name_stack.clear()

        self.process_assign_value(value, sign_field, field_name, get_module, current_class, targets, is_filed)
        self.is_init = False

    def process_assign_value(self, value, sign_field, field_name, get_module, current_class, targets, is_filed=False):
        target_0 = targets[0]
        potent_method_nodes = self.sink_manager.get_potent_method_nodes()
        if len(self.assign_sink_field) > 0 and isinstance(target_0, ast.Attribute):
            self.sink_method_field.setdefault(sign_field, {}).setdefault(self.current_ns, self.assign_sink_field.copy())

        if isinstance(value, ast.Name):
            name_id = getattr(value, 'id')
            if name_id in self.sink_module_variable and sign_field:
                self.sink_field[sign_field] = self.sink_module_variable[value.id]
            elif name_id == 'self' and field_name:
                self.sink_variable[field_name] = 'self'
            elif name_id in (pnodes := self.sink_manager.get_potent_method_nodes()) or f"{name_id}-l" in pnodes:
                call_node = ast.Call(func=value, args=[], keywords=[])
                self.visit(call_node)
            method_imports = self.import_manager.get_node(self.modname)['method_imports']
            if name_id in method_imports:
                current_ns = self.current_ns or self.modname
                self.import_manager.create_sink_edge(current_ns, method_imports[name_id] + '.' + name_id)
            if not self.current_ns and name_id in get_module.get_classes_and_methods() and field_name:
                get_module.get_caller_messages().setdefault(field_name, []).append(name_id)
                get_module.add_classes_and_methods(field_name)
        elif isinstance(value, ast.Call):
            method_name = getattr(value.func, 'attr', None) or getattr(value.func, 'id', None)
            constant_elements = {item for item in value.args if isinstance(item, ast.Constant)}
            if sign_field:
                sink_module = self.sink_manager.get_node(self.modname)
                if isinstance(value.func, ast.Name) and value.func.id in self.invoke_ext_met and sink_module:
                    sink_module['sink_field'][sign_field.rsplit('.', 1)[1]] = value.func.id + '-ext_met'
                elif isinstance(value.func, ast.Attribute) and getattr(value.func.value, 'id', None) == 'self':
                    self.assign_return_to_field[value.func.attr] = sign_field.rsplit('.', 1)[1]
                cur_class = '.'.join(self.current_class)
                if field_name.startswith(cur_class):
                    get_module.add_field_to_cls_name(field_name, method_name)
                else:
                    get_module.add_field_to_cls_name(self.current_ns + '.' + field_name, method_name)
            elif isinstance(value.func, ast.Name) and value.func.id == 'cls':
                if var_name := getattr(target_0, 'id', None):
                    self.sink_variable[var_name] = current_class
            elif method_name == 'get' and len(constant_elements) > 0:
                config_jsons = self.sink_manager.get_config_jsons()
                json_to_object = self.sink_manager.get_json_to_object(self.current_ns)
                for file_name, config_json in config_jsons.items():
                    for key_name in constant_elements:
                        if key_name.value not in config_json or not field_name:
                            continue
                        config_value = config_json[key_name.value]
                        if not isinstance(config_value, str):
                            continue
                        if file_name not in json_to_object:
                            json_to_object[file_name] = {}
                        save_json = json_to_object[file_name]
                        save_json[field_name] = config_value
                        if self.current_ns in potent_method_nodes:
                            continue

                        for mod_name in self.sink_manager.get_potent_method_node(config_value) or []:
                            callee_smu = self.sink_manager.get_node(mod_name)['sink_method_user']
                            call_message = callee_smu.setdefault(config_value, {'callee': set(), 'caller': set()})
                            call_message['caller'].add(self.modname + ':' + self.current_ns)
                            if not self.sink_manager.get_node(self.modname):
                                self.init_sink_node()
                            self.find_potent_sink({mod_name + ':' + config_value}, False)
            elif method_name and (method_name in potent_method_nodes or method_name + '-l' in potent_method_nodes):
                self.sink_module_variable[field_name] = method_name
        elif isinstance(value, ast.Attribute):
            if sign_field and getattr(value.value, 'id', None) == 'self':
                value_method = current_class + '.' + value.attr
                target_method = current_class + '.' + sign_field.rsplit('.', 1)[1]
                get_module.get_caller_messages().setdefault(value_method, []).append(target_method)
                if current_class + '.' + value.attr in potent_method_nodes:
                    call_node = ast.Call(func=value.attr, args=[], keywords=[])
                    self.visit(call_node)
        elif isinstance(value, ast.Subscript) and field_name:
            cur_class = '.'.join(self.current_class)
            return_cls_set = self.identify_value_class(value, cur_class, get_module)
            if len(return_cls_set) > 0:
                if field_name.startswith(cur_class):
                    get_module.add_field_to_cls_name(field_name, return_cls_set)
                else:
                    get_module.add_field_to_cls_name(self.current_ns + '.' + field_name, return_cls_set)
        elif isinstance(value, ast.ListComp) or isinstance(value, ast.DictComp) and isinstance(value.generators, list):
            for generator in value.generators:
                if not isinstance(generator, ast.comprehension):
                    continue

                _iter = generator.iter
                if isinstance(_iter, ast.Call):
                    self.process_assign_value(_iter, sign_field, field_name, get_module, current_class, targets,
                                              is_filed)
                elif isinstance(_iter, ast.Name) and is_filed:
                    _method = self.sink_module_variable.get(_iter.id)
                    if not _method:
                        return
                    get_module = self.module_manager.get(self.modname)
                    cls_module_message = get_module.get_class(current_class)
                    field_impact_methods = cls_module_message['fields'].get(sign_field, [])
                    mod_list = self.sink_manager.get_potent_method_node(
                        _method) or self.sink_manager.get_potent_method_node(_method + '-l')
                    current_smu = self.sink_manager.get_node(self.modname)['sink_method_user']
                    for mod_name in mod_list:
                        call_message = self.sink_manager.get_node(mod_name)['sink_method_user'].get(_method, [])
                        if len(call_message) == 0:
                            return
                        for impact_method in field_impact_methods:
                            call_message['caller'].add(self.modname + ':' + impact_method)
                            if impact_method not in current_smu:
                                cur_call_message = current_smu.setdefault(impact_method,
                                                                          {'callee': set(), 'caller': set()})
                            else:
                                cur_call_message = current_smu.get(impact_method)
                            cur_call_message['callee'].add(mod_name + ':' + _method)
                            self.sink_manager.add_potent_method_node(impact_method, {self.modname})

    def identify_value_class(self, node, class_name, get_module):
        if hasattr(node, 'value'):
            return_value = self.identify_value_class(node.value, class_name, get_module)
            if 'self' in return_value and class_name and isinstance(node, ast.Attribute):
                field_classes = get_module.get_field_to_cls_name(f'{class_name}.{node.attr}') or []
                return {fc for fc in field_classes if not is_base_class_name(fc)}
            return return_value
        elif isinstance(node, ast.Name) and node.id == 'self':
            return {'self'}
        return set()

    def visit_AnnAssign(self, node):
        if isinstance(node.value, ast.Dict):
            self._visit_assign(node.value, [node.target])
        else:
            self.generic_visit(node)

        field_name = None
        if hasattr(node, 'target') and (hasattr(node.target, 'id') or hasattr(node.target, 'attr')):
            field_name = getattr(node.target, 'id', None) or getattr(node.target, 'attr', None)

        if not field_name or not self.current_class:
            return

        current_class = '.'.join(self.current_class)
        sign_field = current_class + '.' + field_name
        module_manager = self.module_manager.get(self.modname)

        field_to_cls_list = module_manager.get_field_to_cls_name(sign_field)
        field_cls = getattr(node, 'annotation', None)
        if not field_to_cls_list and field_cls:
            field_to_cls_list = set()
            if isinstance(field_cls, ast.Subscript):
                anno_sub_value = field_cls.value
                if isinstance(anno_sub_value, ast.Name) and anno_sub_value.id == 'Optional':
                    anno_sub_slice = field_cls.slice
                    if isinstance(anno_sub_slice, ast.Name):
                        module_manager.add_field_to_cls_name(sign_field, anno_sub_slice.id)
                        field_to_cls_list.add(anno_sub_slice.id)
            elif isinstance(field_cls, ast.Name):
                module_manager.add_field_to_cls_name(sign_field, field_cls.id)
                field_to_cls_list.add(field_cls.id)

        for ann_name in field_to_cls_list:
            if ann_name in self.sink_manager.get_potent_module_nodes():
                caller_module = self.sink_manager.get_potent_module_node(ann_name, current_class)
                if current_class not in self.sink_manager.get_potent_module_nodes():
                    if self.modname not in self.sink_manager.get_nodes():
                        self.init_sink_node()
                        self.source_manager.add_source_file(self.filename)
                    sink_module = self.sink_manager.get_node(self.modname)
                    sink_module['sink_field'][field_name] = ann_name
                    sink_module['sink_module_user'].setdefault(current_class + '.__init__', set()).update(caller_module)
                    self.find_potent_sink_module(caller_module)

    def visit_Subscript(self, node):
        self.visit(node.value)
        variable_name = getattr(node.value, 'attr', None) or getattr(node.value, 'id', None)
        get_module = self.module_manager.get(self.modname)
        if variable_name and self.modname + '.' + variable_name in get_module.get_fields():
            get_module.get_field(self.modname + '.' + variable_name).add(self.current_ns)

    def visit_Dict(self, node):
        for key in node.keys:
            if not key:
                continue
            self.visit(key)

        for value in node.values:
            if not value:
                continue
            self.visit(value)

    def visit_List(self, node):
        self.import_manager.get_node(self.modname)
        module_manager = self.module_manager.get(self.modname)
        current_class = None
        cls_module_message = None
        if self.current_class:
            current_class = '.'.join(self.current_class)
            cls_module_message = module_manager.get_class(current_class)
        for idx, elt in enumerate(node.elts):
            self.visit(elt)
            if self.is_init and isinstance(elt, ast.Constant):
                module_manager.add_classes_and_methods(elt.value)
            elif current_class and isinstance(elt, ast.Attribute) and getattr(elt.value, 'id', None) == 'self':
                short_field = current_class + '.' + elt.attr
                self.find_field_in_self(short_field, cls_module_message)
            elif isinstance(elt, ast.Name) and getattr(elt, 'id', None) in self.sink_manager.get_potent_method_nodes():
                method_name = getattr(elt, 'id', None)
                for mod_name in self.sink_manager.get_potent_method_node(method_name) or []:
                    mod_sink_node = self.sink_manager.get_node(mod_name)
                    if not mod_sink_node:
                        continue
                    callee_smu = mod_sink_node['sink_method_user']
                    call_message = callee_smu.setdefault(method_name, {'callee': set(), 'caller': set()})
                    call_message['caller'].add(self.modname + ':' + self.current_ns)
                    self.find_potent_sink({mod_name + ':' + method_name}, False)
                    import_part_name = mod_name + '.' + method_name
                    if self.current_ns == '':
                        continue
                    self.import_manager.create_sink_edge(self.current_ns, import_part_name)
        if self.is_init:
            if self.modname in self.sink_manager.get_nodes():
                self.add_init_into_potent_sink_method()
            if self.modname in self.middle_manager.get_nodes():
                self.add_init_into_potent_method()

        self.is_init = False

    def add_init_into_potent_method(self):
        current_middle = self.middle_manager.get_node(self.modname)['potent_method']
        for import_name in self.import_manager.get_node(self.modname)['imports'].copy():
            if import_name not in self.middle_manager.get_nodes():
                continue
            potent_method = self.middle_manager.get_node(import_name)['potent_method']
            for user_name, call_message in potent_method.items():
                user_data = current_middle.setdefault(user_name, {'callee': set(), 'caller': set()})
                user_data['callee'].update(call_message['callee'])
                user_data['caller'].update(call_message['caller'])
                self.middle_manager.add_potent_method_node(user_name, {self.modname})

    def add_init_into_potent_sink_method(self):
        potent_method_dict = {}
        potent_module_dict = {}
        for import_name in self.import_manager.get_node(self.modname)['imports']:
            sink_import_node = self.sink_manager.get_node(import_name)
            if not sink_import_node:
                continue
            for user_name, use_method in sink_import_node['sink_method_user'].items():
                if user_name in self.module_manager.get(self.modname).get_classes_and_methods():
                    potent_method_dict[user_name] = use_method['callee']
                    potent_module_dict[user_name] = sink_import_node['sink_module_user'].get(user_name)

        sink_node = self.sink_manager.get_node(self.modname)
        sink_module_user = sink_node['sink_module_user']
        sink_method_user = sink_node['sink_method_user']
        for potent, method_set in potent_method_dict.items():
            if not method_set:
                continue
            sink_method_user[potent] = {'callee': method_set, 'caller': set()}
            sink_import_node = None
            pre_mod_name = None
            mod_prefix = self.modname + ':' + potent
            for method in method_set:
                if method.replace(':', '.') in self.sink_manager.get_resource_points() or ':' not in method:
                    continue
                mod_name, met_name = method.split(':')
                if pre_mod_name != mod_name:
                    sink_import_node = self.sink_manager.get_node(mod_name) or self.sink_manager.create_node(mod_name)
                sink_import_node['sink_method_user'][met_name]['caller'].add(mod_prefix)
                pre_mod_name = mod_name
        for potent, module_set in potent_module_dict.items():
            if module_set:
                sink_module_user[potent] = module_set

    def visit_Lambda(self, node, lambda_name=None):
        pass

    def visit_If(self, node):
        condi_in_method = self.method_stack[-1] if self.method_stack else ''
        try:
            expr = ast.unparse(node.test) if hasattr(node, 'test') else ''
            line_num = {'start_line': node.lineno, 'end_line': node.end_lineno, 'method': condi_in_method, 'expr': expr}
            self.save_if_stmt.setdefault(self.filename, set()).add(frozenset(line_num.items()))
        except Exception:
            pass
        self.generic_visit(node)

    def visit_ExceptHandler(self, node):
        condi_in_method = self.method_stack[-1] if self.method_stack else ''
        try:
            expr = re.split(r'(?<!\\)\n', self.contents)[node.lineno - 1].strip()
            if ':' in expr:
                expr = expr.split(':')[0]
            line_num = {'start_line': node.lineno, 'end_line': node.end_lineno, 'method': condi_in_method, 'expr': expr}
            self.save_if_stmt.setdefault(self.filename, set()).add(frozenset(line_num.items()))
        except Exception:
            pass
        self.generic_visit(node)

    def visit_While(self, node):
        if len(self.method_stack) > 0:
            for_in_method = self.method_stack[-1]
            line_num = {'start_line': node.lineno, 'end_line': node.end_lineno, 'method': for_in_method}
            self.save_loop_stmt.setdefault(self.filename, set()).add(frozenset(line_num.items()))
        self.generic_visit(node)

    def visit_For(self, node):
        if len(self.method_stack) > 0:
            for_in_method = self.method_stack[-1]
            line_num = {'start_line': node.lineno, 'end_line': node.end_lineno, 'method': for_in_method}
            self.save_loop_stmt.setdefault(self.filename, set()).add(frozenset(line_num.items()))

        if isinstance(node.iter, ast.Call):
            self.visit(node.iter)
        elif isinstance(node.iter, ast.Attribute):
            if hasattr(node.iter, 'value') and hasattr(node.iter.value, 'id') and node.iter.value.id == 'self':
                current_class = '.'.join(self.current_class)
                cls_module_message = self.module_manager.get(self.modname).get_class(current_class)
                sign_field = f"{current_class}.{node.iter.attr}"
                self.find_field_in_self(sign_field, cls_module_message)
        elif isinstance(node.iter, ast.BoolOp):
            if hasattr(node.iter, 'values'):
                for value in node.iter.values:
                    self.visit(value)

        for item in node.body:
            self.visit(item)

    def visit_Yield(self, node):
        self.visit_Return(node)

    def visit_Return(self, node):
        if not node or not node.value:
            return
        self.visit(node.value)
        if (
                isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and node.value.func.id in self.invoke_ext_met
                and self.assign_return_to_field
        ):
            ns = self.current_ns
            suffix = ns.rsplit('.', 1)[1] if '.' in ns else ns
            if suffix in self.assign_return_to_field:
                field = self.assign_return_to_field[suffix]
                self.assign_return_to_field[field] = node.value.func.id + '-ext_met'

        if isinstance(node.value, ast.Attribute):
            caller = node.value.value
            if isinstance(caller, ast.Name) and caller.id == 'self':
                caller = '.'.join(self.current_class)
                attr = node.value.attr
                method_name = caller + '.' + attr
                if method_name in self.sink_manager.get_potent_method_nodes():
                    callee_smu = self.sink_manager.get_node(self.modname)['sink_method_user']
                    call_message = callee_smu.setdefault(method_name, {'callee': set(), 'caller': set()})
                    call_message['caller'].add(self.modname + ':' + self.current_ns)
                    self.find_potent_sink({self.modname + ':' + method_name}, False)
                    self.sink_manager.add_no_super_add(self.current_ns)
        elif isinstance(node.value, ast.Name):
            get_module = self.module_manager.get(self.modname)
            if candicate := self.resolve_qualified_method(node.value.id, get_module.get_classes_and_methods()):
                get_module.get_caller_messages().setdefault(candicate, []).append(self.current_ns)
                get_module.get_caller_messages().setdefault(self.current_ns, []).append(candicate)

    def analyze(self):
        self.invoke_ext_met.clear()
        if not self.import_manager.get_node(self.modname):
            self.import_manager.create_node(self.modname)
            self.import_manager.set_filepath(self.modname, self.filename)

        self.visit(ast.parse(self.contents, self.filename))
