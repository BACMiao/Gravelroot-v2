# main.py

from agent_executor import AgentExecutor
from coder import Coder
from drawer import Drawer

def main(data):
    tool = Coder(data)
    test = Drawer(data)
    AgentExecutor(tool).run()

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
