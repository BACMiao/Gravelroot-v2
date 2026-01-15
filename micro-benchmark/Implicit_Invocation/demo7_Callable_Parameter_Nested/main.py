# main.py

from prompt.loading import load_prompt
from chains.loading import load_chain

def main_1(data):
    result = load_prompt(data)
    print(result)

def main_2(data):
    result = load_chain(data)
    print(result)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main_1(code_to_execute)
    main_2(code_to_execute)
