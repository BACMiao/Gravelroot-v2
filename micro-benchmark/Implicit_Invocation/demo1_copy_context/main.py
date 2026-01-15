from tool import PythonAstREPLTool

def main(rce_str):
    pytool = PythonAstREPLTool()
    pytool.run(rce_str)


if __name__ == '__main__':
    rce_str = "print('Hello world from exec!')"
    main(rce_str)