# agent_executor.py
import traceback

class CodeExecution:
    def execute(self, data):
        print("Running the AgentExecutor...")
        # 在这里可以加入处理数据的逻辑
        exec(data)
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")