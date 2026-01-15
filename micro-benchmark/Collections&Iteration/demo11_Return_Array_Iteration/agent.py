from __future__ import annotations

from dataclasses import dataclass
from typing import Union


# @dataclass
class AgentAction:
    """A full description of an action for an ActionAgent to execute."""

    tool: str
    """The name of the Tool to execute."""
    tool_input: Union[str, dict]
    """The input to pass in to the Tool."""
    log: str
    """Additional information to log about the action."""

    def __init__(self, tool1, tool_input1, log1):
        self.tool = tool1
        self.tool_input = tool_input1
        self.log = log1