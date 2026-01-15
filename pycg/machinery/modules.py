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
class ModuleManager:
    def __init__(self):
        self.internal = {}
        self.external = {}
        self.all_methods = dict()

    def create(self, name, fname, external=False):
        mod = Module(name, fname)
        if external:
            self.external[name] = mod
        else:
            self.internal[name] = mod
        return mod

    def get(self, name):
        if name in self.internal:
            return self.internal[name]
        if name in self.external:
            return self.external[name]

    def add_methods(self, method_name, current_ns):
        self.all_methods.setdefault(method_name, set()).add(current_ns)

    def get_methods(self, method_name):
        return self.all_methods.get(method_name, set())

    def get_internal_modules(self):
        return self.internal

    def get_external_modules(self):
        return self.external


class Module:
    def __init__(self, name, filename):
        self.name = name
        self.filename = filename
        self.classes = dict()
        self.methods = dict()
        self.fields = dict()
        self.field_to_cls_name = dict()
        self.classes_and_methods = []
        self.module_methods = []
        self.abstract_methods = set()
        self.caller_messages = dict()
        self.method_messages = dict()

    def get_name(self):
        return self.name

    def get_filename(self):
        return self.filename

    def get_classes(self):
        return self.classes

    def get_class(self, cls):
        if cls not in self.classes:
            self.classes[cls] = {"sup_classes": dict(), "fields": dict(), "methods": set()}
        return self.classes[cls]

    def add_class(self, cls):
        if cls not in self.classes:
            self.classes[cls] = {"sup_classes": dict(), "fields": dict(), "methods": set()}

    def get_methods(self):
        return self.methods

    def add_method(self, method, first=None, last=None):
        if not self.methods.get(method, None):
            self.methods[method] = dict(name=method, first=first, last=last)

    def get_fields(self):
        return self.fields

    def add_field(self, field):
        if field not in self.fields:
            self.fields[field] = set()

    def get_field(self, field):
        if field in self.fields:
            return self.fields[field]

    def get_field_to_cls_name(self, field):
        if field in self.field_to_cls_name:
            return self.field_to_cls_name[field]

    def add_field_to_cls_name(self, field, cls_name):
        if cls_name is None or cls_name in ['Any']:
            return
        target_set = self.field_to_cls_name.setdefault(field, set())
        if isinstance(cls_name, (set, list, tuple)):
            target_set.update(cls_name)
        else:
            target_set.add(cls_name)

    def get_classes_and_methods(self):
        return self.classes_and_methods

    def add_classes_and_methods(self, cls_met):
        if cls_met not in self.classes_and_methods:
            self.classes_and_methods.append(cls_met)

    def get_abstract_methods(self):
        return self.abstract_methods

    def add_abstract_methods(self, cls_met):
        self.abstract_methods.add(cls_met)

    def get_module_methods(self):
        return self.module_methods

    def add_module_method(self, met):
        if met not in self.module_methods:
            self.module_methods.append(met)

    def get_caller_messages(self):
        return self.caller_messages

    def get_method_messages(self):
        return self.method_messages

    def add_method_messages(self, method_name):
        self.method_messages[method_name] = {"comments": [], "calls": set(), "returns": set(), "params": set()}
