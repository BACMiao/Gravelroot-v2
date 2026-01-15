# main.py

from langchain.agents.agent_toolkits.processor import Processor

def main(data):
    def inner_method():
        tool = Processor(data)
        tool.exec_remote_code()
    inner_method()

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
