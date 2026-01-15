import traceback

def decorator1(func_name):
    def inner():
        print('decorator1 method')
        cmd = "print('Hello world with decorator1!')"
        func_name(cmd)
    return inner

def decorator2(func_name):
    def inner(cmd):
        print('decorator2 method')
        func_name(cmd)
    return inner

@decorator1
@decorator2
def method1(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)

method1()  