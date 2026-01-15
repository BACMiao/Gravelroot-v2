# agent_executor.py
from typing import Sequence
from langchain.agents.agent_toolkits.base import ProcessingBase
from serializable import Serializable

class AgentExecutor(Serializable):
    tool: ProcessingBase
    
    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        self.tool.exec_remote_code()
        return "Execution completed"
