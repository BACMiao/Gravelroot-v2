# base.py
import traceback

class Chain:
    def __init__(self, initial_value):
        self.value = initial_value

    def __call__(self, increment):
        exec(self.value)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        return self.value
    
    def run(self, increment):
        self(increment)
