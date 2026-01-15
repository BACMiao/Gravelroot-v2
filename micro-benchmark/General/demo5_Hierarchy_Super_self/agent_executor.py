# agent_executor.py

class AgentExecutor:
    def __init__(self, tool):
        self.tool = tool

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        self.tool.run()
