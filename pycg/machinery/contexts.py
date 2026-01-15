class ContextManager:
    def __init__(self):
        self.contexts = {}
        super().__init__()

    def get_nodes(self):
        return self.contexts

    def get_node(self, name):
        if name in self.contexts:
            return self.contexts[name]

    def create_node(self, name):
        if name in self.contexts:
            return self.contexts[name]
        self.contexts[name] = {'context': '', 'pointer': ''}
        return self.contexts[name]

    def set_context(self, name, context, pointer):
        context_node = self.create_node(name)
        context_node['context'] = context
        context_node['pointer'] = pointer
