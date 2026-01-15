from processor import Processor
from generate import Generator

def main(code: str):
    processor_instance = Processor.exec_test_code()
    processor_instance.exec_remote_code(code)

def main2(code: str):
    generate_instance = Generator.exec_test_code()
    generate_instance.exec_remote_code(code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
    main2(code_to_execute)
