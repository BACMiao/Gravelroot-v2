# create_agent.py

from agent_executor import AgentExecutor
from langchain.agents.agent_toolkits.processor import Processor

def create_pandas_dataframe_agent(data) -> AgentExecutor:
    tool = Processor(data)
    print("Creating AgentExecutor with provided DataFrame...")
    return AgentExecutor(tool)