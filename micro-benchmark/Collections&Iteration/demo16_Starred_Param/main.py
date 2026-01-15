# main.py

from agent_executor import AgentExecutor
from processor import Processor
from other_processor import Other_Processor

def _to_args_and_kwargs(tool, other_tool):
    return (tool,other_tool), {}

def main(data):
    tool = Processor(data)
    other_tool = Other_Processor(data)
    tool_args, tool_kwargs = _to_args_and_kwargs(tool, other_tool)
    agent = AgentExecutor()
    agent.run(*tool_args, 'gravelroot')

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
