from processor import Processor
from generate import Generator

def main(code: str):
    return Generator(
        name="PAL-COLOR-OBJ",
        description="A language model that is really good at reasoning about position and the color attributes of objects. Input should be a fully worded hard reasoning problem. Make sure to include all information about the objects AND the final question you want to answer.",
        func=Processor(code).exec_remote_code,
    )

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute).test()
