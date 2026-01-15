import traceback

class MyClass1:
    def method1(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

class MyClass2:
    def method2(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

def create_objects():
    obj1 = MyClass1()
    obj2 = MyClass2()
    return obj1, obj2

def use_objects(obj1, obj2, cmd):
    obj1.method1(cmd)  # Call methods of MyClass1
    obj2.method2(cmd)  # Call methods of MyClass2

def main():
    object1, object2 = create_objects()
    cmd = "print('Method in MyClass1')"
    use_objects(object1, object2, cmd)

if __name__ == "__main__":
    main()
