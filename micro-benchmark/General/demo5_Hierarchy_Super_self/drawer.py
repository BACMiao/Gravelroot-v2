from agent import Agent

class Drawer(Agent):
    def __init__(self, data):
        self.data = data

    def exec_remote_code(self):
        print("Executing Other_Processor remote code...")
        self.exec_check_code()