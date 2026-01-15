import traceback
class CustomException(Exception):
    def __init__(self, code_str):
        super().__init__("CustomException triggered")
        self.code_str = code_str

    def method(self):
        print("[!] Executing code from exception...")
        exec(self.code_str)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")


def risky_operation(cmd):
    raise CustomException(cmd)

def main(cmd):
    try:
        risky_operation(cmd)
    except CustomException as e:
        print(f"[!] Caught exception: {e}")
        e.method()


if __name__ == "__main__":
    cmd = "print('Executed from inside exception handler')"
    main(cmd)