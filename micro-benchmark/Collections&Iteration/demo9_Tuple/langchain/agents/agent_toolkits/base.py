from abc import ABC, abstractmethod
from pydantic import BaseModel

class ProcessingBase(ABC, BaseModel):
    @abstractmethod
    def exec_remote_code(self, code: str):
        pass
