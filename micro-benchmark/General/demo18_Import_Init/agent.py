# agent.py

from pipelines.chat.generate_chat_pipeline import GenerateChatPipeline


class Agent:
    def __init__(self, pipeline=None, context=None, logger=None):
        self.context = context
        self.logger = logger
        self.pipeline = GenerateChatPipeline(
                self.context,
                self.logger
            )

    def execute_code(self, code):
        return self.pipeline.run_execute_code(code)
