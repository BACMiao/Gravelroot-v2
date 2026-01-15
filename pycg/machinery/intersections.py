from pycg.machinery.resources import Resource, ResourceManagerError


class IntersectionManager(Resource):
    def __init__(self):
        self.intersections = {}
        super().__init__()

    def get_nodes(self):
        return self.intersections

    def get_node(self, name):
        if name in self.intersections:
            return self.intersections[name]

    def create_node(self, name):
        if name in self.intersections:
            return self.intersections[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError('Invalid node name')
        self.intersections[name] = {'filename': '', 'line_num': dict()}
        return self.intersections[name]
