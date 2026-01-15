from typing import Any, Callable

class Generator():
    func: Callable[..., str]
    def __init__(
        self, name: str, func: Callable, description: str, **kwargs: Any
    ) -> None:
        self.func = func

    def test(self):
        self.func()
