from abc import ABC, abstractmethod

class ProcessingBase(ABC):
    @abstractmethod
    def exec_remote_code(self):
        pass

    def run(self):
        self.exec_remote_code()

