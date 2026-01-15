class Generator:
    def __init__(self):
        self.instance = None
    
    def factory(self, acls, processor):
        self.instance = acls()
        return self.instance
    
    def execute(self, code: str):
        self.instance.exec_remote_code(code)