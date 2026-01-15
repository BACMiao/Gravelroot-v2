# main.py
import traceback

class RiskyOperations:
    def __init__(self):
        self.name = "RiskyOperations"

    def execute(self, cmd):
        print(f"Executing command: {cmd}")
        exec(cmd)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")

def dynamic_execution(obj, cmd):
    execute_method = getattr(obj, "execute")
    execute_method(cmd)

def main():
    risky_instance = RiskyOperations()
    user_input_cmd = "print('This is a risky operation!')"
    dynamic_execution(risky_instance, user_input_cmd)

if __name__ == "__main__":
    main()