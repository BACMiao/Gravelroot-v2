from abc import ABC

class Agent(ABC):
    def exec_remote_code(self):
        print('ProcessingBase exec_remote_code')
        self.exec_check_code()

    def exec_check_code(self):
        print('ProcessingBase exec_test_code')

    def run(self):
        self.exec_remote_code()

