# main.py

from agent import SemanticAgent

def main(data):
    agent = SemanticAgent(context='123', logger='zxc')
    agent.query(data)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec code!')"
    main(code_to_execute)

