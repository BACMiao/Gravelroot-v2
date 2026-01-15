# main.py

from pipelines.chat.generate_chat_pipeline import GenerateChatPipeline

def main(data):
    pipeline = GenerateChatPipeline('123', 'zxc')
    pipeline.run_generate_code(data)

if __name__ == "__main__":
    code_to_execute = "print('Hello from exec!')"
    main(code_to_execute)

