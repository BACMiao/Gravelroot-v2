import traceback
from base import ProcessingBase

class Processor(ProcessingBase):
    def __init__(self, code):
        self.code = code

    def exec_remote_code(self):
        print("Executing remote code...")
        exec(self.code)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")