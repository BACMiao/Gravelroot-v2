from utilities.loading import try_load_from_hub

def load_chain(message):
    """Unified method for loading a prompt from LangChainHub or local fs."""
    if hub_result := try_load_from_hub(message):
        print("exec try_load_from_hub")
        return hub_result
    else:
        print("exec else")
        return _load_chain_from_file(message)

def _load_chain_from_file(message):
    print(message)
    return True
