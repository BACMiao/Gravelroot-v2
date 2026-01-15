from base import ProcessingBase
import traceback

class Processor(ProcessingBase):
    def __init__(self):
        pass

    def exec_remote_code(self, code: str):
        print("Executing remote code...")
        exec(code)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

    @classmethod
    def exec_test_code(cls):
        return cls()
