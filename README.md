# Gravelroot

**python version: 3.12**

## 1. Analysis all Agent projects in the specified directory

```shell
$ cd Gravelroot
```

To modify the run.py file to include the directory paths for the following:

* The directory path for the files to be tested.
* The path for the sinks location (which is pre-provided by the project).
* The output directory path where the results will be stored.
* The path of the Python execution environment.

```python
base_dir = "/data/OpenAgentBenchmarks/"
sinks_dir = "/root/Gravelroot/rules/sink_files"
output_base_dir = "/root/result"
python_env = "/root/venv/bin/python"
```

After the configuration is complete, execute the following command to start the analysis:

```shell
$ python run.py
```

## 2. Analyze the single Agent project in the specified path
```shell
$ cd Gravelroot
$ python -m pycg --package [project_path] --sinks [sink] --output [output_path] --name [AgentName]
```
* `project_path` is any project path within `/data/OpenAgentBenchmarks/`, such as `/data/OpenAgentBenchmarks/pandas-ai`.
* `sink` is any rule file under the path `/root/Gravelroot/rules/sink_files`, such as `/root/Gravelroot/rules/sink_files/RCE-sinks`.
* `--max-iter` is used to control the number of incremental analysis iterations. By default, the analysis stops when a fixed point is reached. You can also set `--max-iter 30` to terminate after 30 iterations.