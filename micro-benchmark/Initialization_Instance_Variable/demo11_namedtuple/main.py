from collections import namedtuple
from coder import Coder

Base = namedtuple("Base", ["tool"])

class CodeRunner(Base):
    def run(self, cmd):
        print("Running exec with code:")
        self.tool.exec_check_code(cmd)

def main(cmd):
    coder = Coder()
    runner = CodeRunner(coder)
    runner.run(cmd)

if __name__ == "__main__":
    cmd = "print('Hello from exec!')"
    main(cmd)