import traceback
from langchain.agents.agent_toolkits.base import ProcessingBase

class Processor(ProcessingBase):
    data: str 

    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing remote code...")
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(self.data)

    def exec_test_code(self):
        print("Executing test code...")
