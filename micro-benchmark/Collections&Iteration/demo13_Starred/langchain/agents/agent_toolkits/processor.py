import traceback

class Processor:
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing remote code...")
        exec(self.data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

    def exec_test_code(self):
        print("Executing test code...")
