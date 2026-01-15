from pycg.machinery.resources import Resource, ResourceManagerError


class MiddleManager(Resource):
    def __init__(self):
        self.middles = {}
        self.root_middles = {}
        self.class_messages = None
        super().__init__()

    def get_middle_methods(self):
        return self.resource_points

    def get_nodes(self):
        return self.middles

    def get_root_nodes(self):
        return self.root_middles

    def get_node(self, name):
        if name in self.middles:
            return self.middles[name]

    def get_root_node(self, name):
        if name in self.root_middles:
            return self.root_middles[name]

    def create_node(self, name):
        if name in self.middles:
            return self.middles[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError('Invalid node name')
        self.middles[name] = {'filename': '', 'potent_method': dict(), 'caller_message': dict()}
        return self.middles[name]

    def create_root_node(self, name):
        if name in self.root_middles:
            return self.root_middles[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError('Invalid node name')
        self.root_middles[name] = {'filename': '', 'potent_method': dict()}
        return self.root_middles[name]

    def set_class_messages(self, cls_messages):
        self.class_messages = cls_messages

    def transitive_potent_method(self, module_manager):
        to_process = list(self.get_nodes().items())
        seen_nodes = set()

        while to_process:
            mid_name, mid_module = to_process.pop(0)
            if mid_name in seen_nodes:
                continue
            seen_nodes.add(mid_name)

            potent_methods = mid_module['potent_method']
            seen_methods = set()
            while True:
                new_methods = set(potent_methods.keys()) - seen_methods
                if not new_methods:
                    break
                for potent_method in new_methods:
                    seen_methods.add(potent_method)
                    if potent_method not in mid_module['caller_message']:
                        continue
                    for caller_method in mid_module['caller_message'][potent_method]:
                        init_param = {'callee': set(), 'caller': set()}
                        if '#' in caller_method:
                            caller_modname, caller_methname = caller_method.split('#')
                            if caller_modname not in self.get_nodes():
                                middle_node = self.create_node(caller_modname)
                                get_module = module_manager.get(caller_modname)
                                self.update_caller_message(caller_modname, get_module.get_caller_messages())
                                if caller_modname not in seen_nodes:
                                    to_process.append((caller_modname, middle_node))
                            caller_methods = self.get_node(caller_modname)['potent_method']
                            if caller_methname not in caller_methods:
                                caller_methods[caller_methname] = init_param
                            caller_methods[caller_methname]['callee'].add(mid_name + ':' + potent_method)
                            potent_callee = potent_methods[potent_method]
                            potent_callee['caller'].add(caller_modname + ':' + caller_methname)
                            self.add_potent_method_node(caller_methname, {caller_modname})
                            if '.' in caller_methname:
                                potent_cls, met_name = caller_methname.split('.', 1)
                                sup_msg = self.class_messages.get(caller_modname).get_class(potent_cls)['sup_classes']
                                sig_callee_name = mid_name + ':' + potent_method
                                self.trans_super_method(sig_callee_name, met_name, sup_msg, potent_callee)
                        elif caller_method not in potent_methods and '.' in caller_method:
                            potent_caller = potent_methods[caller_method] = init_param
                            sig_callee_name = mid_name + ':' + potent_method
                            potent_caller['callee'].add(sig_callee_name)
                            potent_callee = potent_methods[potent_method]
                            sig_caller_name = mid_name + ':' + caller_method
                            potent_callee['caller'].add(sig_caller_name)
                            potent_cls, met_name = caller_method.split('.', 1)
                            sup_msg = self.class_messages.get(mid_name).get_class(potent_cls)['sup_classes']
                            self.add_potent_method_node(caller_method, {mid_name})
                            self.trans_super_method(sig_callee_name, met_name, sup_msg, potent_callee)

    def trans_super_method(self, sig_callee_name, met_name, classes_msg, sub_call_msg):
        for cls_name, mod in classes_msg.items():
            cls_name = cls_name.replace(mod + '.', '')
            sup_cls_msg = self.class_messages.get(mod).get_class(cls_name)
            init_param = {'callee': set(), 'caller': set()}
            if mod not in self.get_nodes():
                continue
            sup_call_msg = self.get_node(mod)['potent_method'].setdefault(cls_name + '.' + met_name, init_param)
            sup_call_msg['callee'].add(sig_callee_name)
            sub_call_msg['caller'].add(mod + ':' + cls_name + '.' + met_name)
            self.add_potent_method_node(cls_name + '.' + met_name, {mod})
            self.trans_super_method(sig_callee_name, met_name, sup_cls_msg['sup_classes'], sub_call_msg)

    def filter_potent_middle_method(self):
        delete_module = set()
        for mid_name, mid_module in self.get_nodes().items():
            if not mid_module['potent_method']:
                delete_module.add(mid_name)

        for module_key in delete_module:
            self.get_nodes().pop(module_key)
