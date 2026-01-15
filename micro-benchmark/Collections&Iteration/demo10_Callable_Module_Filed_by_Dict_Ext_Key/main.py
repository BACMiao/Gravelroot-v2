from processor import Processor
from ext_key import key

def _get_pal_colored_objects(code: str):
    return Processor(code)

def _get_pal_objects(code):
    pass

_LLM_TOOLS = {
    "pal-colored-objects": _get_pal_colored_objects,
    "pal-objects": _get_pal_objects,
}

def load_tools(code: str):
    return_tool = _LLM_TOOLS[key](code)
    return_tool.exec_remote_code()


if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    load_tools(code_to_execute)
