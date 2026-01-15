# main.py

from agent_executor import AgentExecutor
from processor import Processor
from other_processor import Other_Processor

def main(data):
    tool = Processor(data)
    other_tool = Other_Processor(data)
    str1 = "test1"
    str2 = "test2"
    agent = AgentExecutor()
    agent.run(str1, str2, tool=tool, other_tool=other_tool)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
