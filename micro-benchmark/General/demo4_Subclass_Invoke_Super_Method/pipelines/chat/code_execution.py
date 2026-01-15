# agent_executor.py
import traceback

class CodeExecution:
    def execute(self, data):
        print("Running the AgentExecutor...")
        exec(data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
