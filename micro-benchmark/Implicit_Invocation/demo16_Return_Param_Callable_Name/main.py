import traceback


def method(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)

def method2(func):
    return func

def method3():
    return method2
    
def main():
    cmd = "print('Method in method')"
    method3()(method)(cmd)

if __name__ == "__main__":
    main()
