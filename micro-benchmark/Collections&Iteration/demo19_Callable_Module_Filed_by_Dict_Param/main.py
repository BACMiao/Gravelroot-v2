from processor import Processor

def _get_pal_colored_objects(code: str):
    return Processor(code)

def _get_pal_objects(code):
    pass

def new_key(llm_dict, key = "pal-colored-objects"):
    llm_dict[key] = _get_pal_colored_objects
    return key

def exec_tool(llm_dict, key, code):
    llm_dict[key](code).exec_remote_code()

def load_tools(code: str):
    _LLM_TOOLS = {
        "pal-objects": _get_pal_objects,
    }
    return_key = new_key(_LLM_TOOLS)
    exec_tool(_LLM_TOOLS, return_key, code)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    load_tools(code_to_execute)
