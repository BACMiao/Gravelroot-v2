# main.py

from agent import Agent

def main_1(data):
    agent = Agent(context='123', logger='zxc')
    agent.execute_code(data)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main_1(code_to_execute)

