import traceback


def method(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)
    
def main(cmd):
    eval("method(cmd)")

if __name__ == "__main__":
    cmd = "print('Method in method')"
    main(cmd)
