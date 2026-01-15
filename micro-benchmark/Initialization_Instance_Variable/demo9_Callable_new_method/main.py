import traceback

class A:
    def __init__(self):
        print("[A] __init__ called")

    def execute(self, cmd):
        print("[A] execute() called")
        exec(cmd)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

class Factory:
    def __new__(cls, *args, **kwargs):
        return A()

    def __init__(self):
        print("[Factory] __init__ called")

    def execute(self, cmd):
        print("[Factory] execute() called")
        exec(cmd)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

def main(cmd):
    obj = Factory()
    obj.execute(cmd)

if __name__ == "__main__":
    cmd = "print('This is a risky operation!')"
    main(cmd)