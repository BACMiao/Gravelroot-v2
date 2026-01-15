# generate_chat_pipeline.py
from pipelines.chat.code_execution import code_init

class GenerateChatPipeline:
    def __init__(self, context, logger):
        self.code_execution = code_init

    def run_execute_code(self, input):
        self.code_execution.execute(input)