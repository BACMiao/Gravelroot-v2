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

from pycg import utils
from pycg.machinery.definitions import Definition
from pycg.processing.base import ProcessingBase


class PreProcessor(ProcessingBase):
    def __init__(
            self,
            filename,
            modname,
            import_manager,
            scope_manager,
            def_manager,
            class_manager,
            module_manager,
            sink_manager,
            code_contents,
            modules_analyzed=None,
    ):
        super().__init__(filename, modname, modules_analyzed, code_contents)

        self.modname = modname
        self.mod_dir = "/".join(self.filename.split("/")[:-1])
        self.import_manager = import_manager
        self.scope_manager = scope_manager
        self.def_manager = def_manager
        self.class_manager = class_manager
        self.module_manager = module_manager
        self.sink_manager = sink_manager
        self.code_contents = code_contents
        self.has_all_field = False
        self.call_stmt_in_try = set()
        self.in_try_body = False
        self.hierarchy_graph = self.sink_manager.get_hierarchy_graph()

    def _get_fun_defaults(self, node):
        defaults = {}
        # PyCG cannot process positional arguments in Python, resulting in array out-of-bounds errors during analysis.
        start = len(node.args.posonlyargs) + len(node.args.args) - len(node.args.defaults)
        index = 0
        for cnt, d in enumerate(node.args.defaults, start=start):
            if not d:
                continue

            self.visit(d)

            if len(node.args.posonlyargs) > index:
                defaults[node.args.posonlyargs[cnt].arg] = self.decode_node(d)
                index = index + 1
            else:
                defaults[node.args.args[cnt].arg] = self.decode_node(d)

        start = len(node.args.kwonlyargs) - len(node.args.kw_defaults)
        for cnt, d in enumerate(node.args.kw_defaults, start=start):
            if not d:
                continue
            self.visit(d)
            defaults[node.args.kwonlyargs[cnt].arg] = self.decode_node(d)

        return defaults

    def analyze_submodule(self, modname):
        fname = self.import_manager.get_filepath(modname)

        if not fname.endswith(".py"):
            return

        self.import_manager.set_current_mod(modname, fname)

        visitor = PreProcessor(
            fname,
            modname,
            self.import_manager,
            self.scope_manager,
            self.def_manager,
            self.class_manager,
            self.module_manager,
            self.sink_manager,
            self.code_contents,
            modules_analyzed=self.get_modules_analyzed(),
        )

        if modname in self.sink_manager.get_nodes():
            visitor.analyze()
        else:
            visitor.init_scope_defi()

        self.merge_modules_analyzed(visitor.get_modules_analyzed())
        self.import_manager.set_current_mod(self.modname, self.filename)

    def init_scope_defi(self):
        def iterate_mod_items(items, const):
            for item in items:
                defi = self.def_manager.get(item)
                if not defi:
                    defi = self.def_manager.create(item, const, self.modname)

                if const == utils.constants.FUN_DEF:
                    return_ns = utils.join_ns(item, utils.constants.RETURN_NAME)
                    if not self.def_manager.get(return_ns):
                        self.def_manager.create(return_ns, utils.constants.NAME_DEF, defi.get_module_name())
                        defi.get_taint_pointer().add(return_ns)

                splitted = item.split(".")
                name = splitted[-1]
                parentns = ".".join(splitted[:-1])
                self.scope_manager.get_scope(parentns).add_def(name, defi)

        self.import_manager.set_current_mod(self.modname, self.filename)
        root_sc = self.scope_manager.get_scope(self.modname)
        if not root_sc:
            items = self.scope_manager.handle_module(
                self.modname, self.filename, self.contents
            )

            root_sc = self.scope_manager.get_scope(self.modname)
            root_defi = self.def_manager.get(self.modname)
            if not root_defi:
                root_defi = self.def_manager.create(
                    self.modname, utils.constants.MOD_DEF, self.modname
                )
            root_sc.add_def(self.modname.split(".")[-1], root_defi)

            # create function and class defs and add them to their scope
            # we do this here, because scope_manager doesn't have an
            # interface with def_manager, and we want function definitions
            # to have the correct points_to set
            iterate_mod_items(items["functions"], utils.constants.FUN_DEF)
            iterate_mod_items(items["classes"], utils.constants.CLS_DEF)

        defi = self.def_manager.get(self.modname)
        if not defi:
            defi = self.def_manager.create(self.modname, utils.constants.MOD_DEF)

    def visit_Module(self, node):
        self.init_scope_defi()
        super().visit_Module(node)
        if self.filename.endswith("__init__.py") and not self.has_all_field:
            imports_nodes = self.import_manager.get_node(self.modname)['imports_nodes']
            for import_name, import_node in imports_nodes.items():
                if hasattr(import_node, "module"):
                    self.process_ImportFrom(import_node)
                else:
                    self.process_Import(import_node)

    def process_Import(self, node, prefix="", level=0):
        """
        For imports of the form
            `from something import anything`
        prefix is set to "something".
        For imports of the form
            `from .relative import anything`
        level is set to a number indicating the number
        of parent directories (e.g. in this case level=1)
        """

        def handle_src_name(name):
            # Get the module name and prepend prefix if necessary
            src_name = name
            if prefix:
                src_name = prefix + "." + src_name
            return src_name

        def handle_scopes(imp_name, tgt_name, modname):
            def create_def(scope, name, imported_def):
                if imported_def.get_type() == utils.constants.CLS_DEF:
                    cls = self.class_manager.get(imported_def.get_ns())
                    if not cls:
                        cls = self.class_manager.create(imported_def.get_ns(), imported_def.get_module_name())
                if name not in scope.get_defs():
                    def_ns = utils.join_ns(scope.get_ns(), name)
                    defi = self.def_manager.get(def_ns)
                    if not defi:
                        defi = self.def_manager.assign(def_ns, imported_def, self.modname)
                    defi.get_name_pointer().add(imported_def.get_ns())
                    imported_def.get_taint_pointer().add(defi.get_ns())
                    current_scope.add_def(name, defi)

            current_scope = self.scope_manager.get_scope(self.current_ns)
            imported_scope = self.scope_manager.get_scope(modname)
            if tgt_name == "*":
                for name, defi in imported_scope.get_defs().items():
                    create_def(current_scope, name, defi)
                    current_scope.get_def(name).get_name_pointer().add(defi.get_ns())
            else:
                # if it exists in the imported scope then copy it
                defi = imported_scope.get_def(imp_name)
                if not defi:
                    # maybe its a full namespace
                    defi = self.def_manager.get(imp_name)

                if defi and current_scope:
                    create_def(current_scope, tgt_name, defi)
                    current_scope.get_def(tgt_name).get_name_pointer().add(
                        defi.get_ns()
                    )

        def add_external_def(name, target):
            # In case we encounter an external import in the form of:
            #  "import package.module.module...
            # we want to treat it as: "import package"
            # and save it as such in the definition manager,
            # so that we will be able to later map it
            #  with its corresponding calls
            if (name == target) & (len(name.split(".")) > 1):
                name = name.split(".")[0]
                target = target.split(".")[0]
            # add an external def for the name
            defi = self.def_manager.get(name)
            if not defi:
                defi = self.def_manager.create(name, utils.constants.EXT_DEF, name)
            scope = self.scope_manager.get_scope(self.current_ns)
            if target != "*" and scope:
                # add a def for the target that points to the name
                tgt_ns = utils.join_ns(scope.get_ns(), target)
                tgt_defi = self.def_manager.get(tgt_ns)
                if not tgt_defi:
                    tgt_defi = self.def_manager.create(tgt_ns, utils.constants.EXT_DEF, self.modname)
                tgt_defi.get_name_pointer().add(defi.get_ns())
                scope.add_def(target, tgt_defi)

        for import_item in node.names:
            src_name = handle_src_name(import_item.name)  # import *
            tgt_name = import_item.asname if import_item.asname else import_item.name  # as *
            imported_name = self.import_manager.handle_import_from_graph(src_name, level)
            if not imported_name:
                prefix = self.modname.split('.', 1)[0]
                if not src_name.startswith(prefix):
                    imported_name = self.import_manager.handle_import(prefix + '.' + src_name, level)

            if not imported_name:
                add_external_def(src_name, tgt_name)
                continue

            fname = self.import_manager.get_filepath(imported_name)
            if not fname:
                add_external_def(src_name, tgt_name)
                continue
            # only analyze modules under the current directory
            if self.import_manager.get_mod_dir() in fname:
                if imported_name not in self.modules_analyzed:
                    self.analyze_submodule(imported_name)
                handle_scopes(import_item.name, tgt_name, imported_name)
            else:
                add_external_def(src_name, tgt_name)

    def process_ImportFrom(self, node):
        if not hasattr(node, 'module'):
            return
        self.process_Import(node, prefix=node.module, level=node.level)

    def _get_last_line(self, node):
        lines = sorted(
            list(ast.walk(node)),
            key=lambda x: x.lineno if hasattr(x, "lineno") else 0,
            reverse=True,
        )
        if not lines:
            return node.lineno

        last = getattr(lines[0], "lineno", node.lineno)
        if last < node.lineno:
            return node.lineno

        return last

    def _handle_function_def(self, node, fn_name):
        current_def = self.def_manager.get(self.current_ns)

        defaults = self._get_fun_defaults(node)

        fn_def = self.def_manager.handle_function_def(self.current_ns, fn_name, self.modname)

        mod = self.module_manager.get(self.modname)
        if not mod:
            mod = self.module_manager.create(self.modname, self.filename)
        mod.add_method(fn_def.get_ns(), node.lineno, self._get_last_line(node))

        defs_to_create = []
        name_pointer = fn_def.get_name_pointer()
        context_name_pointer = set()
        for context_defi in fn_def.get_context_def():
            context_name_pointer.add(context_defi.get_name_pointer())

        # TODO: static methods can be created using
        # the staticmethod() function too
        is_static_method = False
        if hasattr(node, "decorator_list"):
            for decorator in node.decorator_list:
                if (
                        isinstance(decorator, ast.Name)
                        and decorator.id == utils.constants.STATIC_METHOD
                ):
                    is_static_method = True

        if (
                current_def.get_type() == utils.constants.CLS_DEF
                and not is_static_method
                and node.args.args
        ):
            arg_ns = utils.join_ns(fn_def.get_ns(), node.args.args[0].arg)
            arg_def = self.def_manager.get(arg_ns)
            if not arg_def:
                # Add processing logic such that if a method’s first parameter is cls, it will be treated as a class.
                if arg_ns.endswith(".cls"):
                    arg_def = self.def_manager.create(arg_ns, utils.constants.CLS_DEF, self.modname)
                elif arg_ns.endswith(".self"):
                    arg_def = self.def_manager.create(arg_ns, utils.constants.NAME_DEF, self.modname)
            if arg_def:
                arg_def.get_name_pointer().add(current_def.get_ns())

                self.construct_obj_context(fn_def, arg_ns, arg_def)

                self.scope_manager.handle_assign(
                    fn_def.get_ns(), arg_def.get_name(), arg_def
                )
                node.args.args = node.args.args[1:]

        sink_node = None
        if self.modname in self.sink_manager.get_nodes():
            sink_node = self.sink_manager.get_node(self.modname)

        sink_variable = dict()

        for pos, arg in enumerate(node.args.args):
            arg_ns = utils.join_ns(fn_def.get_ns(), arg.arg)
            name_pointer.add_pos_arg(pos, arg.arg, arg_ns)
            for cxt_name_pointer in context_name_pointer:
                cxt_name_pointer.add_pos_arg(pos, arg.arg, arg_ns)
            defs_to_create.append(arg_ns)
            arg_type = None
            if isinstance(arg.annotation, ast.Subscript) and isinstance(arg.annotation.slice, ast.Name):
                arg_type = arg.annotation.slice.id
            elif isinstance(arg.annotation, ast.Name):
                arg_type = arg.annotation.id
            if sink_node and arg_type:
                if arg_type in sink_node["sink_module_user"]:
                    sink_variable[arg_ns] = sink_node["sink_module_user"][arg_type]
                arg_mod_name = self.import_manager.get_node(self.modname)['method_imports'].get(arg_type)
                if (
                        arg_mod_name
                        and arg_mod_name in self.sink_manager.get_nodes()
                        and arg_type in self.sink_manager.get_potent_method_nodes()
                ):
                    sink_variable[arg_ns] = {arg_mod_name + '.' + arg_type}

        if node.args.vararg:
            arg_ns = utils.join_ns(fn_def.get_ns(), node.args.vararg.arg)
            defs_to_create.append(arg_ns)
            name_pointer.add_name_arg(node.args.vararg.arg, arg_ns)

        for arg in node.args.kwonlyargs:
            arg_ns = utils.join_ns(fn_def.get_ns(), arg.arg)
            # TODO: add_name_arg function
            name_pointer.add_name_arg(arg.arg, arg_ns)
            for cxt_name_pointer in context_name_pointer:
                cxt_name_pointer.add_name_arg(arg.arg, arg_ns)
            defs_to_create.append(arg_ns)

        if node.args.kwarg:
            arg = node.args.kwarg
            arg_ns = utils.join_ns(fn_def.get_ns(), arg.arg)
            name_pointer.add_name_arg(arg.arg, arg_ns)
            for cxt_name_pointer in context_name_pointer:
                cxt_name_pointer.add_name_arg(arg.arg, arg_ns)
            defs_to_create.append(arg_ns)

        # TODO: Add support for varargs
        # if node.args.vararg:
        #    pass

        for arg_ns in defs_to_create:
            arg_def = self.def_manager.get(arg_ns)
            if not arg_def:
                arg_def = self.def_manager.create(arg_ns, utils.constants.NAME_DEF, self.modname)

            for context_def in fn_def.get_context_def():
                context_arg_ns = context_def.get_ns().split(':')[0] + ':' + arg_ns
                context_arg_def = self.def_manager.get(context_arg_ns)
                if not context_arg_def:
                    context_arg_def = self.def_manager.create(context_arg_ns, utils.constants.NAME_DEF, self.modname)
                    arg_def.add_context_def(context_arg_def)

            self.scope_manager.handle_assign(
                fn_def.get_ns(), arg_def.get_name(), arg_def
            )

            sink_points = sink_variable.get(arg_ns)
            if sink_points:
                for sink_pont in sink_points:
                    arg_def.get_name_pointer().add(sink_pont)

            # has a default
            arg_name = arg_ns.split(".")[-1]
            if defaults.get(arg_name, None):
                for default in defaults[arg_name]:
                    if isinstance(default, Definition):
                        arg_def.get_name_pointer().add(default.get_ns())
                        if default.is_function_def():
                            arg_def.get_name_pointer().add(default.get_ns())
                        else:
                            arg_def.merge(default)
                    else:
                        arg_def.get_lit_pointer().add(default)
        return fn_def

    def construct_obj_context(self, fn_def, arg_ns, arg_def):
        func_name = fn_def.get_ns().replace(self.current_ns, '')
        subclasses = self.hierarchy_graph.get_subclasses(self.current_ns)
        not_add_ori = False
        for subclass in subclasses:
            cls_ctx_arg = '@' + subclass + ':' + arg_ns
            sub_mod_n, sub_class_n = subclass.rsplit('.', 1)
            sub_mod = self.module_manager.get(sub_mod_n)
            if not sub_mod:
                continue
            cls_ctx_fn = None
            if sub_class_n + func_name not in sub_mod.get_classes_and_methods():
                cls_ctx_fn = '@' + subclass + ':' + fn_def.get_ns()

            if not self.def_manager.get(cls_ctx_arg):
                ctx_arg_def = self.def_manager.create(cls_ctx_arg, arg_def.get_type(), self.modname)
                ctx_arg_def.get_name_pointer().add(subclass)
                arg_def.add_context_def(ctx_arg_def)

            if cls_ctx_fn and not self.def_manager.get(cls_ctx_fn):
                not_add_ori = True
                ctx_cls_def = self.def_manager.create(cls_ctx_fn, fn_def.get_type(), self.modname)
                fn_def.add_context_def(ctx_cls_def)

        if len(subclasses) > 0 and arg_def not in arg_def.get_context_def():
            arg_def.add_context_def(arg_def)
            if not_add_ori:
                fn_def.add_context_def(fn_def)
                base_ctx_arg = '@' + self.current_ns + ':' + arg_ns
                base_ctx_fn = '@' + self.current_ns + ':' + fn_def.get_ns()
                if not self.def_manager.get(base_ctx_arg):
                    ctx_arg_def = self.def_manager.create(base_ctx_arg, arg_def.get_type(), self.modname)
                    ctx_arg_def.get_name_pointer().add(self.current_ns)
                    arg_def.add_context_def(ctx_arg_def)

                if base_ctx_fn and not self.def_manager.get(base_ctx_fn):
                    ctx_cls_def = self.def_manager.create(base_ctx_fn, fn_def.get_type(), self.modname)
                    fn_def.add_context_def(ctx_cls_def)

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):
        name_stack = self.name_stack[:]
        class_name = ".".join(name_stack[1:])
        fun_name = f"{class_name}.{node.name}" if class_name else node.name

        sink_node = self.sink_manager.get_node(self.modname)
        if not sink_node:
            return

        if (
                (node.name != '__init__'
                 and fun_name not in sink_node["sink_method_user"])
                or
                (node.name == '__init__'
                 and class_name not in sink_node["sink_method_user"])
        ):
            self._handle_function_def(node, node.name)
            return

        sink_node["pre_analyzed"].add(fun_name)

        if fun_name in self.import_manager.get_node(self.modname)['sink_imports']:
            for imported_name in self.import_manager.get_node(self.modname)['sink_imports'][fun_name]:
                if imported_name not in self.import_manager.get_node(self.modname)['imports_nodes']:
                    continue
                import_node = self.import_manager.get_node(self.modname)['imports_nodes'][imported_name]
                if hasattr(import_node, "module"):
                    self.process_ImportFrom(import_node)
                else:
                    self.process_Import(import_node)

        self._handle_function_def(node, node.name)

        super().visit_FunctionDef(node)

    def visit_For(self, node):
        # just create the definition for target
        if isinstance(node.target, ast.Name):
            target_ns = utils.join_ns(self.current_ns, node.target.id)
            if not self.def_manager.get(target_ns):
                defi = self.def_manager.create(target_ns, utils.constants.NAME_DEF, self.modname)
                self.scope_manager.get_scope(self.current_ns).add_def(node.target.id, defi)
        elif isinstance(node.target, ast.Tuple):
            for pos, elt in enumerate(node.target.elts):
                if not hasattr(elt, "id"):
                    continue
                target_ns = utils.join_ns(self.current_ns, elt.id)
                if not self.def_manager.get(target_ns):
                    defi = self.def_manager.create(target_ns, utils.constants.NAME_DEF, self.modname)
                    self.scope_manager.get_scope(self.current_ns).add_def(elt.id, defi)
        super().visit_For(node)

    def visit_Assign(self, node):
        process_import = False
        for target in node.targets:
            if hasattr(target, 'id') and target.id == '__all__':
                process_import = True
                self.has_all_field = True
                imports_nodes = self.import_manager.get_node(self.modname)['imports_nodes']
                for import_name, import_node in imports_nodes.items():
                    self.process_ImportFrom(import_node)
            if process_import:
                break

        self._visit_assign(node.value, node.targets)

    def visit_Return(self, node):
        self._visit_return(node)

    def visit_AnnAssign(self, node):
        field_name = getattr(node, 'target', None) and getattr(node.target, 'id', None)
        field_cls = getattr(node, 'annotation', None) and getattr(node.annotation, 'id', None)

        if not field_name or field_cls and field_cls == 'bool':
            return

        import_node = self.import_manager.get_node(self.modname)
        if field_cls in self.sink_manager.get_potent_method_nodes():
            if import_module := import_node['method_imports'].get(field_cls):
                import_ast_node = import_node['imports_nodes'][import_module + '.' + field_cls]
                if hasattr(import_ast_node, "module"):
                    self.process_ImportFrom(import_ast_node)
                else:
                    self.process_Import(import_ast_node)

        target = utils.join_ns(self.current_ns, field_name)
        defi = self._handle_assign(target, [])
        splitted = target.split(".")
        self.scope_manager.handle_assign(
            ".".join(splitted[:-1]), splitted[-1], defi
        )
        collect = set()
        module_manager = self.module_manager.get(self.modname)
        if len(self.class_stack) > 0:
            for field_cls in module_manager.get_field_to_cls_name(self.class_stack[0] + '.' + field_name) or []:
                if import_module := import_node['method_imports'].get(field_cls):
                    collect.update(self.collect_potent_cls(import_module + '.' + field_cls))
        for _item in collect:
            defi.get_name_pointer().add(_item)

        if (
                hasattr(node, "target")
                and hasattr(node, "value")
                and isinstance(node.value, ast.Constant)
                and isinstance(node.target, ast.Name)
        ):
            self._visit_assign(node.value, [node.target])

    def collect_potent_cls(self, import_name, visited=None):
        if visited is None:
            visited = set()
        if import_name in visited:
            return set()
        visited.add(import_name)
        collect = set()
        module, method = import_name.rsplit(".", 1)
        if mgs := self.sink_manager.get_node(module):
            if method in mgs['sink_method_user']:
                collect.add(import_name)
        for subclass in self.hierarchy_graph.get_subclasses(import_name):
            if subclass == import_name:
                continue
            collect.update(self.collect_potent_cls(subclass, visited))
        return collect

    def visit_Yield(self, node):
        self._visit_return(node)

    def visit_YieldFrom(self, node):
        self._visit_return(node)

    def visit_Call(self, node):
        if self.in_try_body:
            self.call_stmt_in_try.add(node)

        self.visit(node.func)
        # if it is not a name there's nothing we can do here
        # ModuleVisitor will be able to resolve those calls
        # since it'll have the name tracking information
        if not isinstance(node.func, ast.Name):
            return

        defi = self.scope_manager.get_def(self.current_ns, node.func.id)
        if node.func.id == 'super':
            target_ns = utils.join_ns(self.current_ns, node.func.id)
            defi = self.def_manager.get(target_ns)
            if not defi:
                defi = self.def_manager.create(target_ns, utils.constants.CLS_DEF, self.modname)
            sup_classes = self.module_manager.get(self.modname).get_class('.'.join(self.class_stack))['sup_classes']
            for sup_class, sup_mod in sup_classes.items():
                sup_class_name = sup_class.replace(sup_mod + '.', '')
                sup_ns = utils.join_ns(self.modname, sup_class_name)
                sup_defi = self.def_manager.get(sup_ns)
                if sup_defi:
                    defi.get_name_pointer().add(sup_ns)
            splitted = target_ns.split(".")
            self.scope_manager.handle_assign(".".join(splitted[:-1]), splitted[-1], defi)
        if not defi:
            return

        for added_name in defi.get_added_names():
            self.sink_manager.add_to_need_context(added_name)

        if defi.get_type() == utils.constants.CLS_DEF:
            defi = self.def_manager.get(
                utils.join_ns(defi.get_ns(), utils.constants.CLS_INIT)
            )
            if not defi:
                return

        if defi.get_ns().endswith(".self") and defi.get_type() == utils.constants.NAME_DEF:
            defi = self.def_manager.get(
                utils.join_ns(self.current_method.rsplit('.', 1)[0], utils.constants.CALL_Method)
            )
            if not defi:
                return

        self.iterate_call_args(defi, node)

    def get_sink_message(self):
        return self.sink_manager

    def visit_Lambda(self, node):
        # The name of a lambda is defined by the counter of the current scope
        current_scope = self.scope_manager.get_scope(self.current_ns)
        lambda_counter = current_scope.inc_lambda_counter()
        lambda_name = utils.get_lambda_name(lambda_counter)
        lambda_full_ns = utils.join_ns(self.current_ns, lambda_name)

        # create a scope for the lambda
        self.scope_manager.create_scope(lambda_full_ns, current_scope)
        lambda_def = self._handle_function_def(node, lambda_name)
        # add it to the current scope
        current_scope.add_def(lambda_name, lambda_def)

        super().visit_Lambda(node, lambda_name)

    def visit_Try(self, node):
        self.in_try_body = True
        self.call_stmt_in_try.clear()
        self.generic_visit(node)
        self.in_try_body = False

    def visit_ExceptHandler(self, node):
        self.in_try_body = False
        for call_stmt in self.call_stmt_in_try:
            for call_return in self.decode_node(call_stmt):
                call_raise = call_return.get_ns().replace(utils.constants.RETURN_NAME, utils.constants.EXCEPTION_NAME)
                if (raise_df := self.def_manager.get(call_raise)) and node.name:
                    raise_as_name = utils.join_ns(self.current_ns, node.name)
                    defi = self._handle_assign(raise_as_name, [raise_df])
                    splitted = raise_as_name.split(".")
                    self.scope_manager.handle_assign(".".join(splitted[:-1]), splitted[-1], defi)
        self.generic_visit(node)

    def visit_Raise(self, node):
        self._visit_raise(node)

    def visit_ClassDef(self, node):
        name_stack = self.name_stack[:]
        name_stack.append(node.name)
        class_name = ".".join(name_stack[1:])
        sinks = self.sink_manager.get_node(self.modname)
        if not sinks or class_name not in sinks["sink_method_user"]:
            return

        if class_name not in sinks["pre_analyzed"]:
            if class_name in self.import_manager.get_node(self.modname)['sink_imports']:
                for imported_name in self.import_manager.get_node(self.modname)['sink_imports'][class_name]:
                    if imported_name not in self.import_manager.get_node(self.modname)['imports_nodes']:
                        continue
                    import_node = self.import_manager.get_node(self.modname)['imports_nodes'][imported_name]
                    self.process_ImportFrom(import_node)

            # create a definition for the class (node.name)
            cls_def = self.def_manager.handle_class_def(self.current_ns, node.name, self.modname)

            mod = self.module_manager.get(self.modname)
            if not mod:
                mod = self.module_manager.create(self.modname, self.filename)
            mod.add_method(cls_def.get_ns(), node.lineno, self._get_last_line(node))

            # iterate bases to compute MRO for the class
            cls = self.class_manager.get(cls_def.get_ns())
            if not cls:
                cls = self.class_manager.create(cls_def.get_ns(), self.modname)

            self.sink_manager.get_node(self.modname)["pre_analyzed"].add(class_name)

        for base in node.bases:
            self.visit(base)
            bases = self.decode_node(base)
            for base_def in bases:
                if not base_def:
                    continue
                for added_name in base_def.get_added_names():
                    self.sink_manager.add_to_need_context(added_name)
                    self.sink_manager.add_to_need_context(added_name)

        super().visit_ClassDef(node)

    def analyze(self):
        self.visit(ast.parse(self.contents, self.filename))
