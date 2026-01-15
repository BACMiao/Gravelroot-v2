import traceback

class MyClass1:
    def method1(self, cmd):
        self.child(cmd)

class MyClass2(MyClass1):
    def __init__(self):
        self.child = self.method2
    def method2(self, cmd):
        print("====call stack Class2====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

class MyClass3(MyClass2):
    def __init__(self):
        self.child = self.method3
    def method3(self, cmd):
        print("====call stack Class3====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

def main():
    cmd = "print('Method in MyClass1')"
    object2 = MyClass2()
    object2.method1(cmd)
    object3 = MyClass3()
    object3.method1(cmd)

if __name__ == "__main__":
    main()
