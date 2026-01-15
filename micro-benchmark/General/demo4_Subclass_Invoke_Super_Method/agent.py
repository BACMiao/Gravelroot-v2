# main.py

from pipelines.chat.generate_chat_pipeline import GenerateChatPipeline
from base import BaseAgent


class SemanticAgent(BaseAgent):
    def __init__(self, pipeline=None, context=None, logger=None):
        self.context = context
        self.logger = logger
        self.pipeline =  GenerateChatPipeline(self.context, self.logger)

    def query(self, code):
        return self.execute_code(code)
