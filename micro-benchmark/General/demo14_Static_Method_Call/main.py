import traceback

class MyClass1:
    @staticmethod
    def method(cmd):
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(cmd)

def main():
    cmd = "print('Method in MyClass1')"
    MyClass1().method(cmd)

if __name__ == "__main__":
    main()
