import traceback
from utilities.loading import try_load_from_hub

def load_prompt(message):
    """Unified method for loading a prompt from LangChainHub or local fs."""
    hub_result = try_load_from_hub(message, _load_prompt_from_file2)
    
    assign_func = _load_prompt_from_file
    try_load_from_hub(message, assign_func)
    if hub_result:
        print("exec try_load_from_hub")
        return hub_result
    else:
        print("exec else")
        return _load_prompt_from_file(message)

def _load_prompt_from_file(message):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(message)
    return True

def _load_prompt_from_file2(message):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(message)
    return True
