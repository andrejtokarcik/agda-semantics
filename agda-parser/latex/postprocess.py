#!/usr/bin/env python

import re
import sys
import fileinput

filename = sys.argv[1]

class TagGenerator(object):
    def __init__(self):
        self.begin_tag = r'%%<*%s:\1>\n' % self.tag_sort
        self.end_tag = r'\n%%</%s:\1>' % self.tag_sort
        self.regex = re.compile(self.regex, re.DOTALL)

    def match_rewrite(self, data):
        repl = ''.join([self.begin_tag, r'\g<0>', self.end_tag])
        return re.sub(self.regex, repl, data)

class Module(TagGenerator):
    regex = r'\\begin{module}{\\moduleName{([A-Z0-9\-]+)}}(.*?)\\end{module}'
    tag_sort = 'module'

class CommandTagGenerator(TagGenerator):
    def __init__(self):
        self.regex = self.begin + r'(.*?)(?=\n(\n|\\begin|\\krule|\\kcontext|\\kconfig|%<))'
        super(CommandTagGenerator, self).__init__()

class Rule(CommandTagGenerator):
    begin = r'\\krule\[([a-z\-]+)\]'
    tag_sort = 'rule'

class Context(CommandTagGenerator):
    begin = r'\\kcontext{\n(?:[^\n]*?){\\kattribute{((?!result)[a-z0-9\-]+)}'
    tag_sort = 'context'

tag_generators = [Module(), Rule(), Context()]

fileobj = open(filename, 'r')
data = fileobj.read()
for generator in tag_generators:
    data = generator.match_rewrite(data)
print data
