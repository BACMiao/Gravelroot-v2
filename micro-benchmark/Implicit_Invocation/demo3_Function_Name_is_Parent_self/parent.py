import traceback
class Parent:
    def __init__(self, initial_value):
        self.value = initial_value

    def __call__(self, prompt):
        print("Called Parent's __call__ method")
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(prompt)
    
    def inner_test(self, data):
        print("parent inner test")
        return Parent(data)
