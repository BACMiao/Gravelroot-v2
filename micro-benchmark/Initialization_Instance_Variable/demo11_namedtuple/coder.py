import traceback

class Coder:
    def exec_check_code(self, data):
        print("Executing test code...")
        exec(data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
