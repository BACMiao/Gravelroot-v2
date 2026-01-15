# agent_executor.py
from typing import Sequence
from langchain.agents.agent_toolkits.base import ProcessingBase

class AgentExecutor:
    def __init__(self, tool):
        self.tool = tool

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        test1 = "Execution completed"
        return (test1, self.tool)