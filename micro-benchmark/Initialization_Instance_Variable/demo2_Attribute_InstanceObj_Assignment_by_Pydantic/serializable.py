from abc import ABC
from typing import Any, Dict, List, Literal, TypedDict, Union, cast
from pydantic import BaseModel

class Serializable(BaseModel, ABC):
    class Config:
        arbitrary_types_allowed = True

    def __init__(self, **kwargs: Any) -> None:
        super().__init__(**kwargs)