#! /usr/bin/env python

from __future__ import print_function

import os, sys, uuid

import itertools
from io import open
from collections import defaultdict

from version_guard import isString

import zlib
try:
    import cPickle as pickle
except:
    import pickle

try:
    import ujson as json
except:
    print('UltraJSON not available; falling back to Python library.')
    import json

from rmBitmasks import *
from renderJustification import printOp

Version = u'5.1'
DatabaseVersion = u'5.1'

class VersionError(Exception):
    def __init__(self, targetVersion, actualVersion):
        super(VersionError, self).__init__(u'Version mismatch: found v{0}, targeting v{1}'.format(actualVersion, targetVersion))

class Zoo:
    _nextUID = 0
    
    nodes = {}
    meta = {'edgeKinds': [],
            'colorings': [],
            'graphviz': {}}
    
    def addNode(label, definition='', key=None, uid=None, edges={}, properties={}, tags=[]):
        if uid is None:
            uid = _nextUID
            _nextUID += 1
        
        n = Node(uid, label, definition, key, edges, properties, tags)
        if key is None:
            nodes[label] = n
        else:
            nodes[key] = n
    
    def addEdgeKind(label, functionBody):
        self.meta['edgeKinds'].append({'label': label, 'functionBody': functionBody})
    
    def addColoring(self, name, colors, labels, coloringFunction):
        self.meta['colorings'].append(Coloring(name, colors, labels, coloringFunction))
    
    def __getitem__(self, key):
        return self.nodes[key]
    
    def __setitem__(self, key, item):
        self.nodes[key] = item
    
    def __contains__(self, key):
        return (key in self.nodes)
    
    def __init__(self, edgeKinds=[], rankdir='TB'):
        self.meta['edgeKinds'] = edgeKinds
        self.meta['graphviz'] = {'rankdir': rankdir}

class Coloring:
    def __init__(self, name, colors, labels, coloringFunction):
        self.label = name
        self.colors = [{'color': color, 'label': label} for color,label in zip(colors,labels)]
        self.coloring = coloringFunction

class Node:
    def __init__(self, uid, label, definition='', key=None, edges={}, properties={}, tags=[]):
        if key is None:
            key = label
        
        self.uid = uid
        self.label = label
        self.definition = definition
        self.key = key
        self.edges = edges
        self.properties = properties
        self.tags = tags
    
    def addEdge(self, dstKey, properties={}):
        self.edges[dstKey] = Edge(self.key, dstKey, properties)
    
    def addProperty(self, name, justification, value=None, description='', uid=None):
        self.properties[name] = Property(justification, value, description, uid)

class Edge:
    def __init__(self, srcKey, dstKey, properties={}):
        self.srcKey = srcKey
        self.dstKey = dstKey
        self.properties = properties
    
    def addProperty(self, name, justification, value=None, description='', uid=None):
        self.properties[name] = Property(justification, value, description, uid)

class Property:
    def __init__(self, justification, value=None, description='', uid=None):
        if uid is None:
            uid = uuid.uuid4()
        
        self.value = value
        self.justification = justification
        self.description = description
        self.uid = uid

class Justification:
    weight = 0
    direct = None
    composite = None
    
    def __init__(self, direct=None, composite=None, weight=None):
        if direct is None and composite is None:
            raise ValueError('Justifications must contain some justification.')
        if direct is not None and composite is not None:
            raise ValueError('Justifications are either direct or composite, not both.')
        
        if direct is not None:
            self.weight = 1
            self.direct = direct
        
        if composite is not None:
            if weight is None:
                raise ValueError('Composite justifications must specify their weights.')
            
            self.weight = weight
            self.composite = composite
        
def loadDatabase(databaseName, quiet=False):
    with open(databaseName, mode='rb') as databaseFile:
        compressedDatabase = databaseFile.read()
        pickledDatabase = zlib.decompress(compressedDatabase)
        setDatabase(pickle.loads(pickledDatabase))

def getDatabase():
    return {'version': DatabaseVersion,
            'principles': principles,
            'implication': (implies, notImplies),
            'conservation': (conservative, nonConservative),
            'form': form,
            'primary': (primary, primaryIndex),
            'justify': justify}
def setDatabase(database):
    if database['version'] != DatabaseVersion:
        raise VersionError(DatabaseVersion, database['version'])
    
    global principles
    principles = database['principles']
    
    global implies, notImplies
    implies, notImplies = database['implication']
    
    global conservative, nonConservative
    conservative, nonConservative = database['conservation']
    
    global form
    form = database['form']
    
    global primary, primaryIndex
    primary, primaryIndex = database['primary']
    
    global justify
    justify = database['justify']

if __name__ == '__main__':
    databaseTitle = 'database'
    if os.path.splitext(databaseTitle)[1] == '':
        databaseName = databaseTitle + os.extsep + 'dat'
    else:
        databaseName = databaseTitle
    loadDatabase(databaseName)
    
    primaryIndex += sorted(principles - primary)
    
    meta = {
             'tags': [],
             'edgeKinds': [],
             'colorings': [],
             'about': {'description': 'The <a href="https://rmzoo.math.uconn.edu/">RM Zoo</a> is a program to help organize reverse-mathematical relations between mathematical principles, particularly those that fail to be equivalent to any of the big five subsystems of second-order arithmetic. Its primary goal is to make it easier to see known results and open questions, and thus hopefully to serve as a useful tool to researchers in the field. As a secondary goal, the Zoo provides an interactive annotated bibliography of the field, collecting results in a standard machine-readable format.'},
             'graphviz': {}
           }
    for red in Reduction:
        if red == Reduction.none: continue
        
        posName = red.name + u'i'
        negName = red.name + u'ni'
        
        kindNode = {'label': '$\rightarrow_{\rm ' + red.name + '}$',
                    'key': posName,
                    'edges': [r.name + u'i' for r in Reduction.list(Reduction.weaker(red) & ~red)]}
        kind = {'label': '$\rightarrow_{\rm ' + red.name + '}$',
                'functionBody': """if({0} in edge.properties) return 1;
                                   else if({1} in edge.properties) return 0;
                                   else return 2;""".format(posName, negName),
                'node': kindNode}
        meta['edgeKinds'].append(kind)
    for f in Form:
        if f == Form.none: continue
        
        posName = f.name + u'c'
        negName = f.name + u'nc'
        
        #TODO: Implement better labels for conservation results
        kindNode = {'label': posName,
                    'key': posName,
                    'edges': [r.name + u'i' for r in Reduction.list(Reduction.weaker(red) & ~red)]}
        kind = {'label': posName,
                'functionBody': """if({0} in edge.properties) return 1;
                                   else if({1} in edge.properties) return 0;
                                   else return 2;""".format(posName, negName),
                'node': kindNode}
        
    nodes = {}
    for i,p in enumerate(primaryIndex):
        nodes[p] = dict()
        nodes[p]['uid'] = i
        
        #TODO: Implement labels
        nodes[p]['label'] = p
        
        #TODO: Implement definitions
        nodes[p]['definition'] = ''
        
        nodes[p]['edges'] = {dst:{'srcKey':p,
                                  'dstKey':dst,
                                  'properties':dict()} for dst in principles}
        nodes[p]['properties'] = {}
        nodes[p]['tags'] = []
    uid = i+1
    
    properties = {}
    for p in sorted(principles):
        for f in Form.list(form[p]):
            #TODO: Implement justifications for forms
            properties[(p, u'form', f)] = {'uid': uid,
                                           'value': f.name,
                                           'justification': {'weight': 1,
                                                             'direct': 'Observed'}}
            nodes[p]['properties'][f.name] = properties[(p, u'form', f)]
            uid += 1
    
    for f,j in justify.items():
        if f in properties:
            continue
        
        toJustify = [(f, j, {'uid': uid})]
        uid += 1
        while toJustify:
            fact,jst,prop = toJustify.pop()
            done = True
            if isString(jst):
                prop['justification'] = {'weight': 1, 'direct': jst}
            elif all(ref in properties for ref in jst):
                prop['justification'] = {'weight': 1 + sum(properties[ref]['justification']['weight'] for ref in jst),
                                         'composite': [properties[ref]['uid'] for ref in jst]}
            else:
                done = False
                toJustify.append((fact, jst, prop))
                for ref in jst:
                    if ref in properties:
                        continue
                    toJustify.append((ref, justify[ref], {'uid': uid}))
                    uid += 1
            if done:
                properties[fact] = prop
                
                a,op,b = fact
                opCtx,opCore = op
                if opCore in u'->':
                    coreName = u'i'
                elif opCore == u'-|>':
                    coreName = u'ni'
                else:
                    coreName = opCore
                opName = opCtx.name + coreName
                nodes[a]['edges'][b]['properties'][opName] = prop
    
    with open('rmzoo.json', 'w') as f:
        json.dump({'nodes': nodes, 'meta': meta}, f)
