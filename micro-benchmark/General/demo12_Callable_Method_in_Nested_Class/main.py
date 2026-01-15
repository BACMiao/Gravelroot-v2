import traceback

class MyClass1:
    class MyClass2:
        def method1(self, cmd):
            print("====call stack end====")
            traceback.print_stack()
            print("====call stack end====")
            exec(cmd)

class MyClass3(MyClass1.MyClass2):
    def method2(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)


class MyClass4:
    def method3(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

def main():
    object = MyClass3()
    cmd = "print('Method in MyClass1')"
    object.method2(cmd)
    object.method1(cmd)
    MyClass4().method3(cmd)

if __name__ == "__main__":
    main()
