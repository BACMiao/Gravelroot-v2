from generate import *
from processor import Processor
from base import ProcessingBase

def main(code: str):
    generator = Generator()
    processor = Processor()
    generator.factory(Processor, processor)
    generator.execute(code)

def execute_test(code: str, processor: ProcessingBase):
    processor.exec_remote_code(code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
