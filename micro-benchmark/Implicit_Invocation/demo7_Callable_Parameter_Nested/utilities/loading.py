def try_load_from_hub(
    message,
    loader,
    **kwargs,
):
    return loader(str(message), **kwargs)

