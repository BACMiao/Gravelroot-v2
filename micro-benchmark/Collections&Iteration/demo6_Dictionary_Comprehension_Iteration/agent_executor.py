# agent_executor.py

class AgentExecutor:
    def __init__(self, tool):
        self.tool = tool

    def run(self, *args, **kwargs):
        print("Running the AgentExecutor...")
        list_tools = [self.tool]
        dict_test3 = {tool_iter.name : tool_iter for tool_iter in list_tools}
        for tool in dict_test3.values():
            tool.exec_remote_code()
