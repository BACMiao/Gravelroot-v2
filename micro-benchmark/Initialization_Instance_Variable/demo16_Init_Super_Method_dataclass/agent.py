from __future__ import annotations

from dataclasses import dataclass
from typing import Union
from base_agent import BaseAgentAction


@dataclass
class AgentAction(BaseAgentAction):
    """A full description of an action for an ActionAgent to execute."""

    tool: str
    """The name of the Tool to execute."""
    tool_input: Union[str, dict]
    """The input to pass in to the Tool."""
    log: str
    """Additional information to log about the action."""