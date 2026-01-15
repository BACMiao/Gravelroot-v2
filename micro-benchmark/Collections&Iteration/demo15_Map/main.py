# main.py

from agent_executor import AgentExecutor
from processor import Processor
from other_processor import Other_Processor

def main(data):
    tool = Processor(data)
    other_tool = Other_Processor(data)
    agent = AgentExecutor()
    for _ in map(agent.run, [tool, other_tool]):
        pass

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
