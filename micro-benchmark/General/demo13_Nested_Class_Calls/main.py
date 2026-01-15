import traceback

class MyClass1:
    def method(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

class MyClass2():
    def __init__(self, c):
        self.c = c
    def method(self, cmd):
        self.c.method(cmd)

class MyClass3:
    def __init__(self):
        self.c = MyClass1()    
    def method(self, cmd):
        object2 = MyClass2(self.c)
        object2.method(cmd)

def main():
    object = MyClass3()
    cmd = "print('Method in MyClass1')"
    object.method(cmd)

if __name__ == "__main__":
    main()
