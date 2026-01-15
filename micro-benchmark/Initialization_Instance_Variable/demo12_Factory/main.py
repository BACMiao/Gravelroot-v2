from coder import Coder

class CodeRunner:
    def run(self, cmd):
        return Coder(cmd)

def main(cmd):
    runner = CodeRunner()
    runner.run(cmd).exec_check_code()

if __name__ == "__main__":
    cmd = "print('Hello from exec!')"
    main(cmd)