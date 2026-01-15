from tool import PythonAstREPLTool
from other_tool import PythonTool
from agent import AgentAction


def main(rce_str):
    pytool = PythonAstREPLTool()
    othtool = PythonTool()
    output = AgentAction(pytool, othtool, 'abc', '123')
    output.super_instance.run(rce_str)
    output.tool.run(rce_str)

if __name__ == '__main__':
    rce_str = "print('Hello world from exec!')"
    main(rce_str)