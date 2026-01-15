import traceback
from base import ProcessingBase

class Processor(ProcessingBase):
    def exec_remote_code(self, code: str):
        print("Executing remote code...")
        exec(code)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

    def exec_test_code(self, code: str):
        print("Executing test code...")

class Processor2(ProcessingBase):
    def print_something():
        print("Processor2 print something")
