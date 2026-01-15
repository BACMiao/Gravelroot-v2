# main.py

from langchain.agents import create_pandas_dataframe_agent

def main_1(data):
    agent = create_pandas_dataframe_agent(data)
    agent.run()

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main_1(code_to_execute)
