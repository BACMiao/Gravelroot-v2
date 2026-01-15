from base_generate import BaseGenerator

class Generator(BaseGenerator):
    def __init__(self):
        super().__init__()
        self.instance = None
        self.test_instance = None
    
    def factory(self, acls, processor):
        self.super_instance = acls()
    
    def execute(self, code: str):
        print("----execute super instance----")
        self.super_instance.exec_remote_code(code)
        print("----execute super instance----")