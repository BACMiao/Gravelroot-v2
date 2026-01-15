# agent_executor.py

class AgentExecutor:
    def __init__(self):
        pass

    def run(self, *args, **kwargs):
        kwargs['tool'].exec_remote_code()