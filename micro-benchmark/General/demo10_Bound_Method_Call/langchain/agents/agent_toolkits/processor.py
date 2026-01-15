import traceback
from langchain.agents.agent_toolkits.base import ProcessingBase
from langchain.agents.agent_toolkits.base_processor import BaseProcessor

class Processor(BaseProcessor, ProcessingBase):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing remote code...")
        exec(self.data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

    def exec_test_code(self):
        print("Executing test code...")
