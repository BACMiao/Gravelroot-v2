from processor import Processor

def main(code: str):
    processor_name = Processor.exec_test_code()
    processor_name().exec_remote_code(code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
