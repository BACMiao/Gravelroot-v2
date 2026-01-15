class Resource(object):
    def __init__(self):
        self.resource_points = None
        self.origin_points = None
        self.module_to_methods = {}
        self.method_to_modules = {}
        self.method_index_param = {}
        self.potent_method_nodes = {}
        self.potent_files = None

    def get_potent_files(self):
        return self.potent_files

    def set_potent_files(self, files):
        self.potent_files = files

    def set_filepath(self, node_name, filename):
        if not filename or not isinstance(filename, str):
            raise ResourceManagerError("Invalid node name")

        node = self.get_node(node_name)
        if not node:
            raise ResourceManagerError("Node does not exist")

        node["filename"] = filename

    def get_resource_points(self):
        return self.resource_points

    def replace_all(self):
        strings = self.resource_points
        self.resource_points = [s.rsplit(":", 1)[0].replace(":", ".") for s in strings]

    def get_resource_modules(self):
        return self.module_to_methods

    def get_resource_methods(self):
        return self.method_to_modules

    def get_resource_param_index(self):
        return self.method_index_param

    def set_resource_methods(self, strings):
        self.resource_points = strings
        self.origin_points = strings
        for resource_point in self.resource_points:
            resource_module, resource_method, param_index = resource_point.split(':')
            self.module_to_methods.setdefault(resource_module, set()).add(resource_method)
            self.method_to_modules.setdefault(resource_method, set()).add(resource_module)
            self.method_index_param.setdefault(resource_method, set()).add(int(param_index))

    def get_potent_method_nodes(self):
        return self.potent_method_nodes

    def add_potent_method_node(self, node, mod_set):
        if node not in self.potent_method_nodes:
            self.potent_method_nodes[node] = mod_set
        else:
            delete = {mod_name for mod_name in mod_set for cur_name in self.potent_method_nodes[node] if
                      cur_name.startswith(mod_name)}
            mod_set.difference_update(delete)
            self.potent_method_nodes[node].update(mod_set)

    def get_potent_method_node(self, node):
        return self.potent_method_nodes.get(node)

    def remove_potent_method_node(self, node):
        self.potent_method_nodes.pop(node, None)

    def get_node(self, name):
        pass

    def update_caller_message(self, node_name, caller_message):
        node = self.get_node(node_name)
        if not node:
            raise ResourceManagerError("Node does not exist")
        node["caller_message"] = caller_message


class ResourceManagerError(Exception):
    pass
