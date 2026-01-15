import traceback
from agent import Agent

class Coder(Agent):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing remote code...")
        self.exec_check_code()

    def exec_check_code(self):
        print("Executing test code...")
        exec(self.data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
