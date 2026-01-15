import traceback

class Processor:
    def __init__(self):
        pass

    def exec_remote_code(self, code: str):
        print("Executing remote code...")
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(code)
