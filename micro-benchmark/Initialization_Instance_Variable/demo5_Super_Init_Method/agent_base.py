from __future__ import annotations

from dataclasses import dataclass
from typing import Union


class BaseAction:
    def __init__(self, tool1, tool_input1, log1):
        self.tool = tool1
        self.tool_input = tool_input1
        self.log = log1