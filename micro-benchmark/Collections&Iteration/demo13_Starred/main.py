# main.py

from langchain.agents import create_pandas_dataframe_agent

def main(data):
    agent = create_pandas_dataframe_agent(data)
    re0, *re_value, other_tool = agent.run()
    re_value[1].exec_remote_code()
    print(re0)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)
