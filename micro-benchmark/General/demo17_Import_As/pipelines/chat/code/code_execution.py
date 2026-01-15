# code_execution.py

import traceback

class CodeExecution:
    def execute(self, data):
        print("Running the CodeExecution...")
        exec(data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
