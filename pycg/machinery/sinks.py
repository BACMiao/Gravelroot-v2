from pycg.utils.constants import BUILTIN_NAME

from pycg.machinery.resources import Resource, ResourceManagerError
from collections import defaultdict
import copy


class SinkManager(Resource):
    def __init__(self):
        self.caller_sink_methods = set()
        self.sinks = {}
        self.root_sinks = {}
        self.potent_method_nodes = {}
        self.potent_module_nodes = {}
        self.module_nodes_mod = {}
        self.config_jsons = {}
        self.json_to_object = dict()
        self.extra_mods = []
        self.class_re_context = dict()
        self.hierarchy_graph = ClassInheritanceGraph()
        self.exist_meth_to_mods = set()
        self.exist_mods = set()
        self.no_super_add = set()
        self.need_context = dict()
        self.super_object_dict = dict()
        self.load_taints = dict()
        super().__init__()

    def set_load_taints(self, taints):
        self.load_taints = taints

    def get_load_taints(self):
        return self.load_taints

    def get_taints_by_method(self, method_name):
        if method_name in self.load_taints:
            return self.load_taints[method_name]
        else:
            return None

    def get_super_object_dict(self):
        return self.super_object_dict

    def add_module_nodes_dict(self, site, context):
        self.super_object_dict[site] = context

    def get_no_super_add(self):
        return self.no_super_add

    def add_no_super_add(self, modname):
        self.no_super_add.add(modname)

    def get_exist_mods(self):
        return self.exist_mods

    def add_exist_mod(self, mod):
        if mod not in self.exist_mods:
            self.exist_mods.add(mod)

    def get_exist_meth_to_mods(self):
        return self.exist_meth_to_mods

    def add_exist_meth_to_mod(self, mod):
        if mod not in self.exist_meth_to_mods:
            self.exist_meth_to_mods.add(mod)

    def get_extra_mods(self):
        return self.extra_mods

    def add_extra_mod(self, mod):
        if mod not in self.extra_mods:
            self.extra_mods.append(mod)

    def get_potent_module_nodes(self):
        return self.potent_module_nodes

    def add_potent_module_node(self, node, sink_set):
        self.potent_module_nodes.setdefault(node, set()).update(sink_set)

    def get_potent_module_node(self, node, class_name):
        try:
            ret_value = self.potent_module_nodes[node]
        except Exception as e:
            ret_value = self.potent_module_nodes[class_name + "." + node]
        return ret_value

    def get_module_nodes_mods(self):
        return self.module_nodes_mod

    def add_module_nodes_mod(self, node, mod_set):
        if node not in self.module_nodes_mod:
            self.module_nodes_mod[node] = mod_set
        else:
            self.module_nodes_mod[node].update(mod_set)

    def get_module_nodes_mod(self, node):
        return self.module_nodes_mod.get(node)

    def get_hierarchy_graph(self):
        return self.hierarchy_graph

    def get_config_jsons(self):
        return self.config_jsons

    def set_config_jsons(self, config_jsons):
        self.config_jsons = config_jsons

    def get_json_to_object(self, method_name):
        if method_name not in self.json_to_object:
            self.json_to_object[method_name] = dict()
        return self.json_to_object[method_name]

    def has_json_to_object(self, method_name):
        return method_name in self.json_to_object

    def add_json_to_object(self, json_key, json_value):
        self.json_to_object[json_key] = json_value

    def get_nodes(self):
        return self.sinks

    def get_root_nodes(self):
        return self.root_sinks

    def get_sink_points(self):
        return self.resource_points

    def get_methods_by_module(self, module):
        return self.module_to_methods.get(module, set())

    def get_modules_by_method(self, method):
        return self.method_to_modules.get(method, set())

    def get_node(self, name):
        if name in self.sinks:
            return self.sinks[name]

    def get_root_node(self, name):
        if name in self.root_sinks:
            return self.root_sinks[name]
        else:
            return self.create_root_node(name)

    def create_node(self, name):
        if name in self.sinks:
            return self.sinks[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError("Invalid node name")
        self.sinks[name] = {'filename': '', 'module': '', 'super_module': dict(), 'sink_field': dict(), 'potent_num': 0,
                            'sink_method_user': dict(), 'sink_module_user': dict(), 'sink_method': set(),
                            'pre_analyzed': set(), 'no_return': set(), 'caller_message': dict()}
        return self.sinks[name]

    def create_root_node(self, name):
        if name in self.root_sinks:
            return self.root_sinks[name]
        if not name or not isinstance(name, str):
            raise ResourceManagerError("Invalid node name")
        self.root_sinks[name] = {"sink_method_user": dict()}
        return self.root_sinks[name]

    def get_caller_sink_methods(self):
        return self.caller_sink_methods

    def add_class_re_context(self, caller, callee):
        self.class_re_context.setdefault(caller, set()).add(callee)

    def add_to_need_context(self, method_name):
        if method_name not in self.need_context:
            self.need_context[method_name] = False
        else:
            self.need_context[method_name] = True

    def get_need_context(self):
        return self.need_context

    def in_need_context(self, method_name):
        if method_name in self.need_context:
            return self.need_context[method_name]
        return False

    def build_sink_transitive_trees(self):
        tree_roots = {}
        method_parents = {}
        for module_name, module_data in self.sinks.items():
            for method, called_methods in module_data["sink_method_user"].items():
                for called_method in called_methods:
                    method_parents[called_method] = method

        # Determine the root nodes, namely methods that are not invoked by any other methods
        for module_name, module_data in self.sinks.items():
            for method in module_data["sink_method_user"]:
                if method not in method_parents:  # If a method is not in the call set of any other method, then it is a root.
                    if module_name not in tree_roots:
                        tree_roots[module_name] = []
                    tree_roots[module_name].append(method)

        return tree_roots

    def transitive_single_potent_method(self, modname):
        sink_module = self.get_node(modname)
        if not sink_module:
            return
        potent_methods = sink_module["sink_method_user"]
        potent_modules = sink_module["sink_module_user"]

        if len(potent_methods) == sink_module["potent_num"]:
            return
        seen_methods = set()
        while True:
            new_methods = set(potent_methods.keys()) - seen_methods
            if not new_methods:
                break
            for potent_method in new_methods:
                init_temp = {"callee": set(), "caller": set()}
                seen_methods.add(potent_method)
                if potent_method in sink_module["caller_message"]:
                    for caller_method in sink_module["caller_message"][potent_method]:
                        if caller_method.startswith(potent_method) and '.' not in potent_method: #todo
                            continue
                        if '#' not in caller_method:
                            potent_methods.setdefault(caller_method, init_temp)['callee'].add(
                                modname + ':' + potent_method)
                            self.add_potent_method_node(caller_method, {modname})
                            potent_methods[potent_method]["caller"].add(modname + ':' + caller_method)
                            if potent_method in potent_modules:
                                potent_modules[caller_method] = potent_modules[potent_method]
            sink_module["potent_num"] = len(potent_methods)

    def transitive_potent_method(self):
        print("transitive_potent_method starting")
        for sink_name, sink_module in self.get_nodes().items():
            potent_methods = sink_module["sink_method_user"]
            if len(potent_methods) == sink_module["potent_num"]:
                continue
            seen_methods = set()
            while True:
                new_methods = set(potent_methods.keys()) - seen_methods
                if not new_methods:
                    break
                for potent_method in new_methods:
                    seen_methods.add(potent_method)
                    if potent_method in sink_module["caller_message"]:
                        for caller_method in sink_module["caller_message"][potent_method]:
                            if '#' in caller_method:
                                caller_modname, caller_methname = caller_method.split("#")
                                if caller_modname not in self.get_nodes():
                                    continue
                                caller_potent_methods = self.get_node(caller_modname)['sink_method_user']
                                if caller_methname not in caller_potent_methods:
                                    caller_potent_methods[caller_methname] = {'callee': set(), 'caller': set()}
                                    self.get_node(caller_modname)['potent_num'] = len(caller_potent_methods)
                            elif caller_method not in potent_methods:
                                potent_methods[caller_method] = {'callee': set(), 'caller': set()}
                sink_module["potent_num"] = len(potent_methods)
        print("transitive_potent_method ended")

    def print_sink(self):
        for sink_root_mod_name, sink_root_module in self.get_root_nodes().items():
            if sink_root_mod_name in self.get_nodes():
                node_sink_mu = self.get_nodes().get(sink_root_mod_name)['sink_method_user']
                for method_name, method_msg in sink_root_module['sink_method_user'].items():
                    if method_name in node_sink_mu:
                        sink_method_name = sink_root_mod_name + '.' + method_name
                        print('found sink in \"' + sink_method_name + str(method_msg) + '\"')
                        self.caller_sink_methods.add(sink_method_name)

    def filter_potent_sink_module(self):
        delete_sinks = set()
        for potent_sink_mod, potent_sink_message in self.sinks.items():
            delete_methods = set()
            delete_methods2 = set()
            for method_name, import_mods in potent_sink_message['sink_module_user'].items():
                for import_mod in import_mods:
                    if import_mod in self.exist_meth_to_mods:
                        break
                    delete_methods.add(method_name)
            for method_name, callee_mgs in potent_sink_message['sink_method_user'].items():
                for callee in callee_mgs['callee']:
                    if callee.split(':')[0] in self.exist_mods:
                        if method_name in delete_methods2:
                            delete_methods2.remove(method_name)
                        break
                    delete_methods2.add(method_name)

            for delete_method in delete_methods:
                potent_sink_message['sink_module_user'].pop(delete_method)

            for delete_method in delete_methods2:
                potent_sink_message['sink_method_user'].pop(delete_method)

            if len(potent_sink_message['sink_module_user']) == 0 and len(potent_sink_message['sink_method_user']) == 0:
                delete_sinks.add(potent_sink_mod)

        for delete_sink in delete_sinks:
            self.sinks.pop(delete_sink)

    def filter_potent_sink_method(self):
        self.get_overlap_methods()
        add_source = []
        trace_methods = dict()
        for sink_root_mod_name, sink_root_module in self.get_root_nodes().items():
            sink_root_nodes = sink_root_module['sink_method_user']
            sink_node = self.get_node(sink_root_mod_name)
            if not sink_node:
                continue
            sink_node['module'] = sink_root_mod_name
            sink_method_nodes = sink_node['sink_method_user']
            for sink_method_name in sink_root_nodes.keys():
                if sink_method_name not in sink_method_nodes:
                    continue
                find_loop_methods = []
                call_message = sink_method_nodes[sink_method_name]
                sink_method = sink_root_mod_name + ':' + sink_method_name
                find_loop_methods.append(sink_method)
                if call_message['callee']:
                    sig_cls = sink_root_mod_name + '.' + sink_method_name.split('.')[0]
                    trace_methods.setdefault(sink_root_mod_name, set()).add(sink_method_name)
                    self.trace_method_callers(trace_methods, find_loop_methods, call_message, sink_node, [sig_cls])
                    continue
                self.delete_invalid_nodes(call_message, find_loop_methods, sink_method, sink_node)
                del sink_method_nodes[sink_method_name]
            if not sink_method_nodes:
                self.get_nodes().pop(sink_root_mod_name)

        all_nodes = self.get_nodes().copy()

        for sink_name, sink_module in all_nodes.items():
            if sink_name not in self.get_nodes():
                continue

            if sink_name not in trace_methods:
                for method_name, call_message in sink_module['sink_method_user'].copy().items():
                    delete_method = sink_name + ':' + method_name
                    find_loop_methods = [delete_method]
                    self.delete_invalid_nodes(call_message, find_loop_methods, delete_method, sink_module)
                self.get_nodes().pop(sink_name, None)
                continue

            cur_smu = sink_module['sink_method_user'].copy()
            for method_name, call_message in cur_smu.items():
                if method_name not in sink_module['sink_method_user']:
                    continue
                if not call_message['callee']:
                    delete_method = sink_name + ':' + method_name
                    find_loop_methods = [delete_method]
                    self.delete_invalid_nodes(call_message, find_loop_methods, delete_method, sink_module)
                    del sink_module['sink_method_user'][method_name]

            if not sink_module['sink_method_user']:
                self.get_nodes().pop(sink_name)
                continue
            add_source.append(sink_module['filename'])
        return add_source

    def get_overlap_methods(self):
        # get overlap which use sink_method and sink_module
        overlap_set = set()
        for sink_root_mod_name, sink_root_module in self.get_root_nodes().items():
            sink_node = self.get_node(sink_root_mod_name)
            if not sink_node:
                continue
            sink_module_user = sink_node['sink_module_user']
            sink_method_user = sink_node['sink_method_user']
            sink_root_method = sink_root_module['sink_method_user']
            for sink_root_method_name, call_message in sink_root_method.items():
                not_match_sink = copy.copy(call_message['callee'])
                if any(item.startswith(BUILTIN_NAME) for item in not_match_sink):
                    not_match_sink.clear()
                elif sink_root_method_name in sink_module_user:
                    has_sink_module = sink_module_user[sink_root_method_name]
                    for callee in call_message['callee']:
                        callee_mod, callee_method = callee.split(':')
                        if callee_mod in has_sink_module:
                            not_match_sink.clear()
                            break

                if not not_match_sink or sink_root_method_name not in sink_method_user:
                    continue
                loop_message = sink_method_user[sink_root_method_name]
                find_loop = [sink_root_mod_name + '.' + sink_root_method_name]
                overlap_set.update(self.find_overlap_methods(not_match_sink, loop_message, sink_node, find_loop))
                loop_message['callee'].difference_update(not_match_sink)
        return overlap_set

    def find_overlap_methods(self, not_match_sink, loop_message, sink_node, find_loop):
        overlap_set = set()
        if len(not_match_sink) == 0 or len(loop_message['caller']) == 0:
            return overlap_set
        for caller in loop_message['caller']:
            if caller in find_loop:
                continue
            find_loop.append(caller)
            caller_mod, caller_method = caller.split(':')
            caller_sink_node = sink_node
            if sink_node['module'] != caller_mod:
                caller_sink_node = self.get_node(caller_mod)
                if not caller_sink_node:
                    continue
                caller_sink_node['module'] = caller_mod
            caller_sink_mod_user = caller_sink_node['sink_module_user']
            caller_sink_met_user = caller_sink_node['sink_method_user']
            if caller_method not in caller_sink_mod_user:
                continue
            has_sink_module = caller_sink_mod_user[caller_method]
            remove_match_sink = set()
            for sink in not_match_sink:
                sink_mod, sink_method = sink.split(':')
                if sink_mod in has_sink_module:
                    overlap_set.add(caller)
                    remove_match_sink.add(sink)
            not_match_sink.difference_update(remove_match_sink)
            next_loop_message = caller_sink_met_user[caller_method]
            return_set = self.find_overlap_methods(not_match_sink, next_loop_message, caller_sink_node, find_loop)
            overlap_set.update(return_set)
        return overlap_set

    def trace_method_callers(self, trace_methods, find_loop_methods, loop_message, sink_node, call_cls_list):
        if not loop_message:
            return
        remove_nodes = set()
        callers_copy = loop_message['caller'].copy()
        for caller in callers_copy:
            caller_mod, caller_method = caller.split(':')
            if caller in find_loop_methods:
                remove_nodes.add(caller)
                caller_node = self.get_node(caller_mod)
                if not caller_node:
                    continue
                callee_remove = caller_node['sink_method_user'].get(caller_method)['callee']
                remove_callee = find_loop_methods[-1]
                if remove_callee in callee_remove:
                    callee_remove.remove(remove_callee)
                continue
            else:
                find_loop_methods.append(caller)
            caller_sink_node = sink_node
            if caller_mod in trace_methods and caller_method in trace_methods[caller_mod]:
                find_loop_methods.pop()
                continue
            trace_methods.setdefault(caller_mod, set()).add(caller_method)
            if sink_node['module'] != caller_mod:
                caller_sink_node = self.get_node(caller_mod)
                if not caller_sink_node:
                    continue
                caller_sink_node['module'] = caller_mod
            caller_sink_met_user = caller_sink_node['sink_method_user']
            caller_node = caller_sink_met_user.get(caller_method)
            self.trace_method_callers(trace_methods, find_loop_methods, caller_node, caller_sink_node, call_cls_list)
            find_loop_methods.pop()
        loop_message['caller'].difference_update(remove_nodes)

    def delete_invalid_nodes(self, loop_message, find_loop_methods, delete_method, sink_node):
        remove_nodes = set()
        for caller in list(loop_message['caller']):
            if caller in find_loop_methods:
                continue
            find_loop_methods.append(caller)
            caller_mod, caller_method = caller.split(':')
            caller_sink_node = sink_node
            if sink_node['module'] != caller_mod:
                caller_sink_node = self.get_node(caller_mod)
                if not caller_sink_node:
                    continue
                caller_sink_node['module'] = caller_mod
            caller_sink_met_user = caller_sink_node['sink_method_user']
            caller_node = caller_sink_met_user.get(caller_method)

            if not caller_node:
                remove_nodes.add(caller)
                continue

            if delete_method in caller_node['callee']:
                caller_node['callee'].remove(delete_method)
                self.remove_potent_method_node(delete_method.split(':')[1])
            if not caller_node['callee']:
                self.delete_invalid_nodes(caller_node, find_loop_methods, caller, caller_sink_node)
                del caller_sink_met_user[caller_method]
            if not caller_sink_met_user:
                self.get_nodes().pop(caller_sink_node['module'])
            find_loop_methods.pop()
        loop_message['caller'].difference_update(remove_nodes)

    def filter_config_json(self):
        delete_json = set()
        for key, value in self.json_to_object.items():
            if len(value) == 0:
                delete_json.add(key)

        for key in delete_json:
            self.json_to_object.pop(key)


class ClassInheritanceGraph:
    def __init__(self):
        self.graph = defaultdict(set)
        self.root_classes = set()
        self.must_exist_edges = dict()
        self.must_exist_cls_edges = dict()

    def add_exist_edge(self, src_edge, tgt_edge):
        self.must_exist_edges.setdefault(tgt_edge, set()).add(src_edge)

    def get_exist_edge(self, src_edge, tgt_edge):
        if tgt_edge in self.must_exist_edges:
            return src_edge in self.must_exist_edges[tgt_edge]
        else:
            return False

    def add_exist_cls_edge(self, src_edge, tgt_cls_edge):
        self.must_exist_cls_edges.setdefault(src_edge, set()).add(tgt_cls_edge)

    def get_exist_cls_edge(self, src_cls_edge):
        if src_cls_edge not in self.must_exist_cls_edges:
            return set()
        return self.must_exist_cls_edges[src_cls_edge]

    def add_edge(self, child, parent):
        self.graph[child].add(parent)
        if child in self.root_classes:
            self.root_classes.remove(child)
        if parent not in self.graph:
            self.root_classes.add(parent)

    def have_common_parent(self, class1, class2):
        parents1 = self.graph.get(class1, set())
        parents2 = self.graph.get(class2, set())
        if parents1 & parents2:
            return True

        if self.is_subclass(class1, class2) or self.is_subclass(class2, class1):
            return True

        return False

    def is_subclass(self, child, parent, visited=None):
        if visited is None:
            visited = set()
        if child == parent:
            return True
        if child in visited or child not in self.graph:
            return False
        visited.add(child)
        return any(self.is_subclass(p, parent, visited) for p in self.graph[child])

    def has_class(self, class_name):
        return class_name in self.graph or any(class_name in parents for parents in self.graph.values())

    def get_parent_class(self, class_name):
        all_parents = set()

        def dfs(current):
            parents = self.graph.get(current, set())
            for parent in parents:
                if parent not in all_parents:
                    all_parents.add(parent)
                    dfs(parent)

        dfs(class_name)
        return all_parents

    def get_subclasses(self, parent_class):
        subclasses = set()

        def dfs(current):
            for cls, parents in self.graph.items():
                if parent_class in parents and cls not in subclasses:
                    subclasses.add(cls)
                    dfs(cls)

        dfs(parent_class)
        return subclasses
