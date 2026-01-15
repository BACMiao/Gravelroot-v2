from __future__ import annotations

from typing import Union


# @dataclass
class AgentAction:
    """A full description of an action for an ActionAgent to execute."""

    def __init__(self, tool1, tool_input1, log1):
        self.tool = tool1
        self.tool_input = tool_input1
        self.log = log1