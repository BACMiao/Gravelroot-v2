# base.py
from parent import Parent

class Chain(Parent):
    def __init__(self, initial_value):
        self.value = initial_value

    def run(self, increment):
        print("Running the chain...")
        chain = self.inner_test(increment)
        self(self.value)
