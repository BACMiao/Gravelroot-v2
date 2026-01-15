from processor import Processor

def _get_pal_colored_objects(code: str):
    return Processor(code)

def _get_pal_objects(code):
    pass

def new_key(key = "pal-colored-objects"):
    _LLM_TOOLS[key] = _get_pal_colored_objects
    return key

_LLM_TOOLS = {
    "pal-objects": _get_pal_objects,
}

def load_tools(code: str):
    return_key = new_key()
    return_tool = _LLM_TOOLS[return_key](code)
    return_tool.exec_remote_code()


if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    load_tools(code_to_execute)
