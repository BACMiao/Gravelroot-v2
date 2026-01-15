# agent_executor.py

class AgentExecutor:
    def __init__(self, tool):
        self.tool = tool

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        test0 = "test0"
        test1 = "Execution completed"
        return test0, (test1, self.tool)
    
    def run2(self, *args, **kwargs):
        test0, test1 =  testa, testn = "Execution completed", self.tool
        return (test0, test1)