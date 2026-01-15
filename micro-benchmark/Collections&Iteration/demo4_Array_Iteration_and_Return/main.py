from generate import Generator
from processor import Processor
import math

def main(code: str):
    tools = [Processor()]
    processor_instance = Generator.factory(tools)
    processor_instance.exec_remote_code(code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
