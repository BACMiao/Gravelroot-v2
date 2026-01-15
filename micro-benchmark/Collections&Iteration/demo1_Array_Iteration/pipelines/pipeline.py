# pipeline.py
from typing import Any, List

class Pipeline:
    _steps: List

    def __init__(self, context, steps, logger):
        self._steps = steps or []
        self._logger = logger
        self.context = context

    def run(self, data):
        for index, logic in enumerate(self._steps):
            logic.execute(data)