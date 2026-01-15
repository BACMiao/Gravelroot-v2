from abc import ABC, abstractmethod

class ProcessingBase(ABC):
    @abstractmethod
    def exec_remote_code(self, code: str):
        pass
