class Generator:
    def __init__(self):
        self.instance = None
        self.test_instance = None
    
    def factory(self, tools):
        for tool in tools:
            self.instance = tool
        return self.instance
    
    def execute(self, code: str):
        self.instance.exec_remote_code(code)
