def is_base_class_name(name: str) -> bool:
    if not isinstance(name, str):
        return False
    name = name.strip().casefold()

    if name in ('str', 'int', 'float', 'bool', 'dict', 'list', 'tuple', 'set', 'bytes', 'union', 'optional', 'object',
                'any'):
        return True
    return False
