class Generator:
    def __init__(self):
        super().__init__()
        self.instance = None
    
    def factory(self, acls, processor):
        self.instance = processor
    
    def execute(self, code: str):
        print("----execute instance----")
        self.instance.exec_remote_code(code)
        print("----execute instance----")