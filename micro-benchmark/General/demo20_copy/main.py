import traceback
import copy

class Factory:
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
    user2 = copy.copy(obj) 
    user2.execute(cmd)

if __name__ == "__main__":
    cmd = "print('This is a risky operation!')"
    main(cmd)