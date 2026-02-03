import os
import json
import subprocess
from pathlib import Path

agent_names = ['pandas-ai', 'vanna', 'Adala', 'camel', 'AgentForge', 'MetaGPT', 'ChatDev', 'aider', 'autogen',
               'AutoGPT', 'AgentGPT', 'gpt-engineer', 'SuperAGI', 'OpenHands', 'SWE-agent', 'OpenAgents', 'llama_index',
               'letta', 'open-interpreter', 'Langchain']
sink_rules = ['RCE', 'SQLi', 'SSTI', 'ID']
base_dir = "/data/OpenAgentBenchmarks/"
sinks_dir = "/root/Gravelroot/rules/sink_files"
output_base_dir = '/root/result/'
python_env = "/root/venv/bin/python"

current_dir = os.path.dirname(os.path.abspath(__file__))
result_dir = os.path.join(current_dir, "path_result")


def read_config(file_path):
    with open(file_path, 'r') as file:
        config = json.load(file)
    return config


for agent_name in agent_names:
    project_path = os.path.join(base_dir, agent_name)
    if agent_name == 'AutoGPT':
        project_path = os.path.join(project_path, '/autogpt_platform/backend/')
    print(f"🔍 Processing project: {agent_name}")
    for sink_rule in sink_rules:
        sinks_file = sinks_dir + '/' + sink_rule + '-sinks'
        _sink_rule = sink_rule.lower()
        out_json_file = os.path.join(result_dir, f'{agent_name}-path-output-{_sink_rule}.json')
        old_json_file = f'{output_base_dir}{agent_name}-path-output-{_sink_rule}.json'

        log_file = os.path.join(result_dir, f"{agent_name}-{sink_rule}.log")

        command = [
            python_env, "-m", "pycg",
            "--package", project_path,
            "--output", out_json_file,
            "--sinks", sinks_file,
            "--name", agent_name
        ]

        print(f"  ➡ Running with sinks: {sink_rule}")
        print(' '.join(command))
        with open(log_file, "w") as log:
            result = subprocess.run(command, stdout=log, stderr=log, text=True)
            if result.returncode == 0:
                print(f"  ✅ Successfully processed {agent_name} with {sink_rule}, results saved to {out_json_file}")
            else:
                print(f"  ❌ Failed processing {agent_name} with {sink_rule}")
