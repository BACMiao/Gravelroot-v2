# agent_executor.py
from typing import Any, List

class Pipeline:
    _steps: List

    def __init__(self, context, step, logger):
        self._step = step
        self._logger = logger
        self.context = context

    def run(self, data):
        self._step.execute(data)