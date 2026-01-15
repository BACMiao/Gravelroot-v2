import traceback
from base import BaseTool

class PythonTool(BaseTool):
    def _run(
        self,
        query: str,
        test_query: str,
        test_key_param,
    ) -> str:
        exec(query)  # type: ignore
        print("====call stack end PythonTool====")
        traceback.print_stack()
        print("====call stack end PythonTool====")