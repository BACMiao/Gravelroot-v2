import traceback
from langchain.agents.agent_toolkits.base import ProcessingBase

class Processor(ProcessingBase):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing Processor remote code...")
        super().exec_remote_code()

    def exec_test_code(self):
        print("Executing Processor test code...")
        exec(self.data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
