from processor import Processor

def _get_pal_colored_objects(code: str):
    return Processor(code)

def _get_pal_objects(code):
    pass

def _get_pal_writer_objects(code):
    pass

_LLM_TOOLS = [[_get_pal_writer_objects, _get_pal_colored_objects], _get_pal_objects]

def load_tools(code: str, index):
    return_tool = _LLM_TOOLS[0][index](code)
    return_tool.exec_remote_code()


if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    load_tools(code_to_execute, 1)
