# agent_executor.py

class AgentExecutor:
    testcm = None
    def __init__(self, tool):
        self.tool = tool

    def _take_next_step(self):
        return self._consume_next_step(
            [
                a 
                for a in self._iter_next_step()
            ]
        )

    def _consume_next_step(self, valus):
        print("get the values")
        pass 

    def _iter_next_step(self):
        self.run()
        return [1,2,3]

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        self.tool.run()
        return "Execution completed"

    @classmethod
    def from_agent_and_tools(cls, tool):
        print("Creating AgentExecutor using from_agent_and_tools...")
        return cls(tool)
