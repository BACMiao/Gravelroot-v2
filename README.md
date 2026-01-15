# Gravelroot

**python version: 3.12**

## 1. Analysis all Agent projects in the specified directory

To modify the run.py file to include the directory paths for the following:

* The directory path for the files to be tested.
* The path for the sinks location (which is pre-provided by the project).
* The output directory path where the results will be stored.

```python
base_dir = "/data/OpenAgentBenchmarks/"
sinks_dir = "/root/PyCG/sink_files"
output_base_dir = "/root/result"
```

After the configuration is complete, execute the following command to start the analysis:

```shell
$ python run.py
```

## 2. Analyze the single Agent project in the specified path
```shell
$ cd pycg
$ python -m pycg --package [project_path] --sinks [sinks/RCE.txt] --output [output_path] --max-iter [Number]
```