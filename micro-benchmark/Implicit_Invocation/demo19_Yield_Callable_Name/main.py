import traceback

class MyClass1:
    def method(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

    def method2(self):
        yield self.method
    
def main():
    object = MyClass1()
    cmd = "print('Method in MyClass1')"
    func_name = next(object.method2())
    func_name(cmd)

if __name__ == "__main__":
    main()
