# agent_executor.py

class AgentExecutor:
    def __init__(self, tool):
        self.tool = tool

    def _take_next_step(self):
        return self._iter_next_step()

    def _iter_next_step(self):
        self.run()
        return [1,2,3]

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        self.tool.run()
        return "Execution completed"
