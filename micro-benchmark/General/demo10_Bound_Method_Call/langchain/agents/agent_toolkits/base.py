from abc import ABC, abstractmethod

class ProcessingBase(ABC):
    def exec_remote_code(self):
        print("ProcessingBase")

    def run(self):
        self.exec_remote_code()

