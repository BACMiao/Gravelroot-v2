# main.py

from agent_executor import AgentExecutor
from processor import Processor

def main(data):
    tool = Processor(data)
    agent = AgentExecutor()
    func_name = agent.run
    func_name(tool)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
