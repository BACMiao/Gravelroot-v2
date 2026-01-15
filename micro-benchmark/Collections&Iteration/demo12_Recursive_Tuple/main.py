# main.py

from langchain.agents import create_pandas_dataframe_agent

def main_1(data):
    agent = create_pandas_dataframe_agent(data)
    re0, (re1, tool) = agent.run()
    tool.exec_remote_code()
    print(re0)

def main_2(data):
    agent = create_pandas_dataframe_agent(data)
    re1, tool = agent.run2()
    tool.exec_remote_code()
    print(re1)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main_1(code_to_execute)
    main_2(code_to_execute)
