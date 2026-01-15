from abc import ABC
from typing import Any, Callable
from pydantic import BaseModel

class Generator(ABC, BaseModel):
    func: Callable[..., str]
    def __init__(
        self, name: str, func: Callable, description: str, **kwargs: Any
    ) -> None:
        """Initialize tool."""
        super(Generator, self).__init__(
            name=name, func=func, description=description, **kwargs
        )

    def test(self):
        self.func()
