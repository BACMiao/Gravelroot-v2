from abc import ABC

class ProcessingBase(ABC):
    def exec_remote_code(self):
        print('ProcessingBase exec_remote_code')
        self.exec_test_code()

    def exec_test_code(self):
        print('ProcessingBase exec_test_code')

    def run(self):
        self.exec_remote_code()

