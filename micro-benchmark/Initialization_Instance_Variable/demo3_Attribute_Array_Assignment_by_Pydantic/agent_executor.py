# agent_executor.py
from typing import Sequence
from langchain.agents.agent_toolkits.base import ProcessingBase
from serializable import Serializable

class AgentExecutor(Serializable):
    tools: Sequence[ProcessingBase]
    
    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        for tool in self.tools:
            tool.exec_remote_code()
        return "Execution completed"
