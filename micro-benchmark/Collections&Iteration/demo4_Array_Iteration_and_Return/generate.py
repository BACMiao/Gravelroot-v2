class Generator:
    @classmethod
    def factory(cls, tools):
        for tool in tools:
            return tool
