import traceback
from base import BaseTool

class PythonAstREPLTool(BaseTool):
    def _run(
        self,
        query: str,
        test_query: str,
        test_key_param,
    ) -> str:
        print("====call stack end====")
        traceback.print_stack()
        print("====call stack end====")
        exec(query)  # type: ignore