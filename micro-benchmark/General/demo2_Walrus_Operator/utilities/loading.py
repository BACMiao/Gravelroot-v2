import traceback

def try_load_from_hub(
    message,
    **kwargs,
):
    return _load_prompt_from_file2(str(message), **kwargs)

def _load_prompt_from_file2(message):
    exec(message)
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    return True

