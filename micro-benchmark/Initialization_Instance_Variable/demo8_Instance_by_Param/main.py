from generate import Generator
from processor import Processor
from base import ProcessingBase

def main(code: str):
    generator = Generator()
    processor = Processor()
    processor_instance = generator.factory(Processor, processor)

    processor_instance.exec_remote_code(code_to_execute)
    generator.execute(code_to_execute)
    execute_test(code, processor_instance)

def execute_test(code: str, processor: ProcessingBase):
    processor.exec_remote_code(code)

def test_main(code: str):
    processor = Processor()
    processor.exec_test_code(code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
    test_main(code_to_execute)
