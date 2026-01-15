# generate_chat_pipeline.py
from .code_execution import CodeExecution
from ..pipeline import Pipeline

class GenerateChatPipeline:
    def __init__(self, context, logger):
        self.code_execution_pipeline = Pipeline(
            context=context,
            logger=logger,
            steps=[
                CodeExecution(),
            ],
        )

    def run_execute_code(self, input):
        self.code_execution_pipeline.run(input)