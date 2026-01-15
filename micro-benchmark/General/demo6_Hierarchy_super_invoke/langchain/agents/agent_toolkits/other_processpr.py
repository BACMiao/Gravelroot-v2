from langchain.agents.agent_toolkits.base import ProcessingBase

class Other_Processor(ProcessingBase):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing Other_Processor remote code...")
        self.exec_test_code()

    def exec_test_code(self):
        print("Executing Other_Processor test code...")
        exec(self.data)
