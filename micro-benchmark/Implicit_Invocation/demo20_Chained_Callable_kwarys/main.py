import traceback

def func3(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)

def func2(cmd, a=func3):
    a(cmd)

def func1(cmd, a, b=func2):
    a(cmd, b)
    
def main():
    cmd = "print('Method in method')"
    func1(cmd, a=func2, b=func3)

if __name__ == "__main__":
    main()
