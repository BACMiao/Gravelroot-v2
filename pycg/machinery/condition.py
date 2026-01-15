from pycg.machinery.resources import Resource, ResourceManagerError


class ConditionManager(Resource):
    def __init__(self):
        self.condition = {}
        super().__init__()

    def get_nodes(self):
        return self.condition

    def get_node(self, name):
        if name in self.condition:
            return self.condition[name]

    def create_node(self, name):
        if name in self.condition:
            return self.condition[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError('Invalid node name')
        self.condition[name] = {'condition': dict()}
        return self.condition[name]