import traceback

class MyClass1:
    def method(self, cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

    def method2(self):
        return self.method
    
def main():
    object = MyClass1()
    cmd = "print('Method in MyClass1')"
    object.method2()(cmd)

if __name__ == "__main__":
    main()
