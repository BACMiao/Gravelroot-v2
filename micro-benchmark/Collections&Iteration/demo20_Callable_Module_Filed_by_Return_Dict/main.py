from processor import Processor

def _get_pal_colored_objects(code: str):
    return Processor(code)

def _get_pal_objects(code):
    pass

def new_key(key = "pal-colored-objects"):
    _LLM_TOOLS = {
        "pal-objects": _get_pal_objects,
    }
    _LLM_TOOLS[key] = _get_pal_colored_objects
    return _LLM_TOOLS

def exec_tool(llm_dict, code):
    llm_dict["pal-colored-objects"](code).exec_remote_code()

def load_tools(code: str):
    llm_dict = new_key()
    exec_tool(llm_dict, code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    load_tools(code_to_execute)
