"""Base implementation for tools or skills."""
from abc import ABC, abstractmethod


class BaseTool(ABC):
    def _to_args_and_kwargs(self, tool_input):
        # For backwards compatibility, if run_input is a string,
        # pass as a positional argument.
        test_input = "abc"
        if isinstance(tool_input, str):
            return (tool_input,test_input), {}
        else:
            return (), tool_input
        # return tool_input, test_input 

    def run(
            self,
            tool_input,
            *,
            metadata: str = None,
            **kwargs,
    ):
        """Run the tool."""
        tool_args, tool_kwargs = self._to_args_and_kwargs(tool_input)
        observation = self._run(*tool_args, 'cm1')