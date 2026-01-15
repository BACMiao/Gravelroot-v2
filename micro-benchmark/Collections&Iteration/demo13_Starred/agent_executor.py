# agent_executor.py

class AgentExecutor:
    def __init__(self, tool, other_tool):
        self.tool = tool
        self.other_tool = other_tool

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        test0 = "test0"
        test1 = "Execution completed"
        return test0, test1, self.tool, self.other_tool