import traceback

class Coder:
    def __init__(self, data):
        self.data = data
        
    def exec_check_code(self):
        print("Executing test code...")
        exec(self.data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
