class SourceManager(object):
    def __init__(self):
        self.sources_files = []

    def get_source_files(self):
        return self.sources_files

    def set_source_files(self, files):
        self.sources_files = files

    def add_source_file(self, file):
        if file not in self.sources_files:
            self.sources_files.append(file)
