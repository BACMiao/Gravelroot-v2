from tool import PythonAstREPLTool
from agent import AgentAction


def main(rce_str):
    pytool = PythonAstREPLTool()
    output = AgentAction(pytool, 'abc', '123')
    actions = [output]
    for agent_action in actions:
        agent_action.tool.run(rce_str)


if __name__ == '__main__':
    rce_str = "print('Hello world from exec!')"
    main(rce_str)