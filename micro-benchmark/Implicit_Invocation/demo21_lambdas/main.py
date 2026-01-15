import traceback

def func_tmp1(a, b, c, cmd):
    a(10)
    func_tmp2(b, c, cmd)

def func_tmp2(a, b, cmd):
    a(10)
    b(func, cmd)

def func(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)

def main(cmd):
    func_tmp1(lambda x: x + 1, lambda x: x + 2, lambda f, cmd: f(cmd), cmd)

if __name__ == "__main__":
    cmd = "print('Method in method')"
    main(cmd)


