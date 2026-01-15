import traceback
from langchain.agents.agent_toolkits.base import ProcessingBase

class BaseProcessor(ProcessingBase):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing BaseProcessor code...")