import traceback

class CodeExecution:
    def method(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

class MyClass:
    def method2(self):
        ce = CodeExecution()
        yield ce

    def method3(self):
        yield from self.method2()
    
def main():
    cmd = "print('Method in MyClass')"
    object = MyClass()
    func_name = next(object.method3())
    func_name.method(cmd)

if __name__ == "__main__":
    main()
