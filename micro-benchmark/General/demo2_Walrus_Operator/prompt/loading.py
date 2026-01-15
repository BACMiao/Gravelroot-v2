import traceback
from utilities.loading import try_load_from_hub

def load_prompt(message):
    """Unified method for loading a prompt from LangChainHub or local fs."""
    if hub_result := try_load_from_hub(message):
        print("exec try_load_from_hub")
        return hub_result
    else:
        print("exec else")
        return _load_prompt_from_file(message)

def _load_prompt_from_file(message):
    exec(message)
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    return True


