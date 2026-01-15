import traceback

def method(func_name):
    print('external method')
    cmd = "print('Hello world!')"
    func_name(cmd)

decorator = method

@decorator
def method1(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)


def func():
    def method(func_name):
        print('internal method')
        cmd = "print('Hello world with Gravelroot!')"
        func_name(cmd)

    @method
    def inner(cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

def main():
    func()

if __name__ == "__main__":
    main()