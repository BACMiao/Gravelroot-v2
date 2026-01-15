# agent_executor.py
from typing import Any, List

class Pipeline:
    _steps: List

    def __init__(self, context, steps, logger):
        self._steps = steps
        self._logger = logger
        self.context = context

    def run(self, data):
        self._steps.execute(data)