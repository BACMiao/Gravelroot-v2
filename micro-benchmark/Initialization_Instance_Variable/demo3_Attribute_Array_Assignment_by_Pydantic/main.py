# main.py

from langchain.agents import create_pandas_dataframe_agent

def main(data):
    agent = create_pandas_dataframe_agent(data)
    result = agent.run()
    print(result)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)

