# generate_chat_pipeline.py
from .code_execution import CodeExecution

class GenerateChatPipeline:
    def __init__(self, context, logger):
        self.code_execution = CodeExecution()
           

    def run_execute_code(self, input):
        self.code_execution.execute(input)