# generate_chat_pipeline.py
from pipelines.chat.code.code_execution import CodeExecution as CE

class GenerateChatPipeline:
    def __init__(self, context, logger):
        self.code_execution = CE()

    def run_execute_code(self, input):
        self.code_execution.execute(input)