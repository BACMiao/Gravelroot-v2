class Generator:
    def __init__(self):
        self.instance = None
        self.test_instance = None
    
    def factory(self, acls, processor):
        self.instance = acls()
    
    def execute(self, code: str):
        print("----execute instance----")
        self.instance.exec_remote_code(code)
        print("----execute instance----")