#
# Copyright (c) 2020 Vitalis Salis.
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
class CallGraph(object):
    def __init__(self):
        self.cg = {}
        self.re_cg = {}
        self.modnames = {}
        self.taints = {}
        self.edges = {}
        self.hierarchy_graph = {}
        self.intersections = set()
        self.middles = {}
        self.conditions = {}
        self.sink_save = {}

    def add_node(self, name, modname=""):
        if not isinstance(name, str):
            raise CallGraphError("Only string node names allowed")
        if not name:
            raise CallGraphError("Empty node name")

        if name not in self.cg:
            self.cg[name] = []
            self.modnames[name] = modname

        if name not in self.re_cg:
            self.re_cg[name] = set()

        if name in self.cg and not self.modnames[name]:
            self.modnames[name] = modname

        if name not in self.taints:
            self.taints[name] = {}

        if name not in self.edges:
            self.edges[name] = {}

    def add_edge(self, src, dest, end_lineno):
        self.add_node(src)
        self.add_node(dest)
        if dest not in self.cg[src]:
            self.cg[src].append(dest)
        self.re_cg[dest].add(src + '%' + str(end_lineno))

    def get_subsequent_edge(self, src):
        if src not in self.cg:
            return None
        return self.cg[src]

    def get(self):
        return self.cg

    def get_re(self):
        return self.re_cg

    def get_hierarchy_graph(self):
        return self.hierarchy_graph

    def set_hierarchy_graph(self, hierarchy_graph):
        self.hierarchy_graph = hierarchy_graph

    def get_intersections(self):
        return self.intersections

    def set_intersections(self, intersections):
        self.intersections = intersections

    def get_middles(self):
        return self.middles

    def set_middles(self, middles):
        self.middles = middles

    def get_conditions(self):
        return self.conditions

    def set_conditions(self, conditions):
        self.conditions = conditions

    def get_sink_save(self):
        return self.sink_save

    def set_sink_save(self, sink_save):
        self.sink_save = sink_save

    def get_edges(self):
        output = []
        for src in self.cg:
            for dst in self.cg[src]:
                output.append([src, dst])
        return output

    def get_re_edges(self):
        output = []
        for dst in self.re_cg:
            for src in self.re_cg[dst]:
                output.append([dst, src])
        return output

    def get_modules(self):
        return self.modnames

    def get_taints_with_name(self, name):
        if name in self.taints:
            return self.taints[name]

    def get_edges_with_name(self, name):
        if name in self.edges:
            return self.edges[name]


class CallGraphError(Exception):
    pass
