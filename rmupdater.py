#! /usr/bin/env python

##################################################################################
#
#   The Reverse Mathematics Zoo Updater
#   by Damir Dzhafarov
#   - Version 1.0 started August, 2010
#   - Version 2.0 started August, 2013
#   Revised by Eric Astor
#   - Version 3.0 - 29 May 2016
#   - Version 4.0 - started 30 May 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function

import sys
import time
from collections import defaultdict

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

Error = False
def warning(s):
    global Error
    Error = True
    eprint(s)

def error(s):    # Just quit
    warning(s)
    quit()

Date = '30 May 2016'
Version = '4.0'

from rmBitmasks import *

implies = defaultdict(noReduction)
notImplies = defaultdict(noReduction)

def addReduction(a,reduction,b):
    implies[(a,b)] |= Reduction.weaker(reduction)

def addNonReduction(a,reduction,b):
    notImplies[(a,b)] |= Reduction.stronger(reduction)

conservative = defaultdict(noForm)
nonConservative = defaultdict(noForm)

def addConservative(a,frm,b):
    conservative[(a,b)] |= Form.weaker(frm)

def addNonConservative(a,frm,b):
    nonConservative[(a,b)] |= Form.stronger(frm)

form = defaultdict(noForm)

primary = set()
primaryIndex = []

justify = {}

justMarker = '*@'
def indentJust(jst):
    return jst.replace('*@','*@@')

def justReference(a, op, b):
    return justMarker + '{0} {1} {2}: '.format(a, printOp(op), b) + indentJust(justify[(a,op,b)])

def printJust(a):
    a = a.replace('@','    ')
    a = a.replace('*','\n')
    return a

principles = set(['RCA'])

def addPrinciple(a):
    setA = set(a.split('+'))
    a = '+'.join(sorted(setA))
    principles.add(a)
    principles.update(setA)
    return a

def printOp(op):
    if op[1] == 'nc':
        return 'n{0}c'.format(op[0])
    else:
        return '{0}{1}'.format(*op)

def addUnjustified(a, op, b):
    error('Error: The fact "{0} {1} {2}" is not justified.'.format(a, printOp(op), b))

def addJustification(a, op, b, jst):
    if (a, op, b) not in justify:
        justify[(a, op, b)] = jst

def addFact(a, op, b, jst):
    addJustification(a, op, b, jst)
    justRef = justMarker + '{0} {1} {2}: {3}'.format(a, printOp(op), b, justify[(a, op, b)])
    
    if op[1] == '->': # reduction
        r = Reduction.fromString(op[0])
        if Reduction.isPresent(r, implies[(a,b)]):
            return
        addReduction(a, r, b)
        for x in Reduction.iterate(Reduction.weaker(r)):
            addJustification(a, (x.name, op[1]), b, justRef)
            if Reduction.isPresent(x, notImplies[(a,b)]):
                error('Error: The following facts are contradictory.\n\n' + 
                        '{0} {1}-> {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'->'),b)]) + '\n' + 
                        '{0} {1}-|> {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'-|>'),b)]))
    elif op[1] == '-|>': # non-reduction
        r = Reduction.fromString(op[0])
        if Reduction.isPresent(r, notImplies[(a,b)]):
            return
        addNonReduction(a, r, b)
        for x in Reduction.iterate(Reduction.stronger(r)):
            addJustification(a, (x.name, op[1]), b, justRef)
            if Reduction.isPresent(x, implies[(a,b)]):
                error('Error: The following facts are contradictory.\n\n' + 
                        '{0} {1}-> {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'->'),b)]) + '\n' + 
                        '{0} {1}-|> {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'-|>'),b)]))
    elif op[1] == '<->': # equivalence
        r = Reduction.fromString(op[0])
        if not Reduction.isPresent(r, implies[(a,b)]):
            addFact(a, (op[0], '->'), b, justRef)
        if not Reduction.isPresent(r, implies[(b,a)]):
            addFact(b, (op[0], '->'), a, justRef)
    elif op[1] == 'c': # conservation
        frm = Form.fromString(op[0])
        if Form.isPresent(frm, conservative[(a,b)]):
            return
        addConservative(a, frm, b)
        for x in Form.iterate(Form.weaker(frm)):
            addJustification(a, (x.name, op[1]), b, justRef)
            if Reduction.isPresent(x, nonConservative[(a,b)]):
                error('Error: The following facts are contradictory.\n\n' + 
                        '{0} {1}c {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'c'),b)]) + '\n' + 
                        '{0} n{1}c {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'nc'),b)]))
    elif op[1] == 'nc': # non-conservation
        frm = Form.fromString(op[0])
        if Form.isPresent(frm, nonConservative[(a,b)]):
            return
        addNonConservative(a, frm, b)
        for x in Form.iterate(Form.stronger(frm)):
            addJustification(a, (x.name, op[1]), b, justRef)
            if Reduction.isPresent(x, conservative[(a,b)]):
                error('Error: The following facts are contradictory.\n\n' + 
                        '{0} {1}c {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'c'),b)]) + '\n' + 
                        '{0} n{1}c {2}: '.format(a, x.name, b) + printJust(justify[(a,(x.name,'nc'),b)]))
    else:
        error('Unrecognized operator: {0}'.format(op))

def addForm(a, frm):
    form[a] |= Form.weaker(frm)

def addPrimary(a):
    primary.add(a)
    primaryIndex.append(a)

from pyparsing import *
def parseDatabase(databaseFile):
    start = time.clock()
    eprint('Parsing database...')
    # Name parsed strings
    name = Word( alphas+"_+^{}\\$", alphanums+"_+^{}$\\").setParseAction(lambda s,l,t: addPrinciple(t[0]))

    parenth = Literal('"')
    justification = QuotedString('"""',multiline=True) | quotedString.setParseAction(removeQuotes)

    _reductionName = NoMatch()
    for r in Reduction:
        if r != Reduction.none:
            _reductionName |= Literal(r.name)
    reductionName = Optional(_reductionName, default=Reduction.RCA.name)

    reduction = (reductionName + Literal("->")) | (Literal("<=") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "->"])
    nonReduction = reductionName + Literal("-|>")
    equivalence = reductionName + Literal("<->")

    _formName = NoMatch()
    for f in Form:
        if f != Form.none:
            _formName |= Literal(f.name)
    formName = _formName

    conservation = formName + Literal("c")
    nonConservation = (Literal("n") + formName + Literal("c")).setParseAction(lambda s,l,t: [t[1], "nc"])

    operator = reduction | nonReduction | equivalence | conservation | nonConservation

    # Database lines
    unjustified = (name + Group(operator) + name + ~justification).setParseAction(lambda s,l,t: addUnjustified(t[0], t[1], t[2]))
    fact = (name + Group(operator) + name + justification).setParseAction(lambda s,l,t: addFact(t[0], tuple(t[1]), t[2], t[3]))

    formDef = (name + Literal("form") + formName).setParseAction(lambda s,l,t: addForm(t[0], Form.fromString(t[2])))
    primary = (name + Literal("is primary")).setParseAction(lambda s,l,t: addPrimary(t[0]))

    comments = Suppress(Literal( "#" ) + SkipTo( LineEnd()))

    # Represent and parse database file
    entry = fact | formDef | primary | unjustified | comments
    database = ZeroOrMore( entry ) + StringEnd()
    database.parseFile(databaseFile)
    eprint('Elapsed: {0:.6f} s\n'.format(time.clock() - start))

# No inputs; affects '->' and 'c'.
def addTrivialFacts():
    for a in principles:
        addFact(a, ('sW', '->'), a, '')
        addFact(a, ('RCA', '->'), a, '')
        addFact(a, ('rPi12', 'c'), a, '')
        if a != 'RCA':
            addFact(a, ('sW', '->'), 'RCA', '')
            addFact(a, ('RCA', '->'), 'RCA', '')

# No inputs; affects '->'
def weakenConjunctions():
    for a in principles:
        splitA = a.split('+')
        if len(splitA) == 1: continue # a is not a conjunction
        setA = set(splitA)
        
        for b in principles:
            splitB = b.split('+')
            if len(splitB) >= len(splitA): continue # b cannot be a strict subset of a
            setB = set(splitB)
            
            if setB <= setA:
                addFact(a,('sW','->'),b,'')
                addFact(a,('RCA','->'),b,'')

# Uses '->', affects '->'
def reductionConjunction(): # Conjunctions follow from their conjuncts
    r = 0
    for b in principles:
        splitB = b.split('+')
        if len(splitB) == 1: continue # b is not a conjunction
        setB = set(splitB)
        
        for a in principles:
            if a == b: continue
            
            conj = ~0
            for x in splitB:
                conj &= implies[(a,x)]
            change = conj & ~implies[(a,b)]
            if change == 0: continue
            
            r = 1
            for x in Reduction.iterate(change):
                addFact(a, (x.name, '->'), b,
                        ''.join(justReference(a, (x.name, '->'), t) for t in splitB))
    return r

# Complete (current) transitive closure of array, using Floyd-Warshall
def transitiveClosure(cls, array, opName): # Take the transitive closure
    r = 0
    for c in principles:
        for a in principles:
            if a == c: continue
            for b in principles:
                if b == a or a == c: continue
                
                transitive = array[(a,c)] & array[(c,b)]
                change = transitive & ~array[(a,b)]
                if change == 0: continue
                
                r = 1
                for x in cls.iterate(change):
                    addFact(a, (x.name, opName), b,
                            justReference(a, (x.name, opName), c) + justReference(c, (x.name, opName), b))
    return r

# Uses '->' and 'c', affects '->' and 'c'
def rcClosure(): # Connect implication and conservativity
    imp = 0
    con = 0
    for c in principles:
        for a in principles:
            if a == c: continue
            for b in principles:
                if b == a or b == c: continue
                
                # If c -> a and c is conservative over b, then a is conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(c,a)]):
                    change = conservative[(c,b)] & ~conservative[(a,b)]
                    if change == 0: continue
                    
                    con = 1
                    for x in Form.iterate(change):
                        addFact(a, (x.name, 'c'), b,
                                justReference(c, ('RCA', '->'), a) + justReference(c, (x.name, 'c'), b))
                
                # If b -> c and a is conservative over c, then a is conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(b,c)]):
                    change = conservative[(a,c)] & ~conservative[(a,b)]
                    if change == 0: continue
                    
                    con = 1
                    for x in Form.iterate(change):
                        addFact(a, (x.name, 'c'), b,
                                justReference(b, ('RCA', '->'), c) + justReference(a, (x.name, 'c'), c))
                
                # If c -> b, c is (form)-conservative over a, and b is (form), then a -> b.
                frm = form[b] & conservative[(c,a)]
                if frm != Form.none and Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                    if not Reduction.isPresent(Reduction.RCA, implies[(a,b)]):
                        imp = 1
                        addFact(a, ('RCA', '->'), b,
                                justReference(c, ('RCA', '->'), b) + justReference(c, (Form.strongest(frm).name, 'c'), a))
    return (imp, con)

# Uses '->', affects ONLY justify
def extractEquivalences(): # Convert bi-implications to equivalences
    r = 0
    for a in principles:
        for b in principles:
            if b == a: continue
            
            equiv = implies[(a,b)] & implies[(b,a)]
            if equiv == 0: continue
            
            for x in Reduction.iterate(equiv):
                if (a, (x.name, '<->'), b) not in justify:
                    r = 1
                    addFact(a, (x.name, '<->'), b,
                            justReference(a, (x.name, '->'), b) + justReference(b, (x.name, '->'), a))
    return r

# Uses '-|>' and '->', affects '-|>'
def conjunctionSplit(): # Split non-implications over conjunctions
    r = 0
    for b in principles:
        splitB = b.split('+')
        setB = set(splitB)
        for c in principles:
            if b == c: continue
            
            splitC = c.split('+')
            setC = set(splitC)
            
            setBC = setB | setC
            bc = '+'.join(sorted(setBC))
            if bc not in principles: continue
            
            for a in principles:
                change = (notImplies[(a,bc)] & implies[(a,c)]) & ~notImplies[(a,b)]
                if change == 0: continue
                
                r = 1
                for x in Reduction.iterate(change):
                    addFact(a, (x.name, '-|>'), b,
                            justReference(a, (x.name, '-|>'), bc) + justReference(a, (x.name, '->'), c))
    return r

# Uses '->' and '-|>', affects '-|>'
def nonImplicationClosure(): # "transitive" non-implications
    r = 0
    for a in principles:
        for b in principles:
            if b == a: continue
            
            for c in principles:
                if c == a or c == b: continue
                
                bcChange = (implies[(a,b)] & notImplies[(a,c)]) & ~notImplies[(b,c)]
                if bcChange != 0:
                    r = 1
                    for x in Reduction.iterate(bcChange):
                        addFact(b, (x.name, '-|>'), c,
                                justReference(a, (x.name, '->'), b) + justReference(a, (x.name, '-|>'), c))
                
                caChange = (implies[(a,b)] & notImplies[(c,b)]) & ~notImplies[(c,a)]
                if caChange != 0:
                    r = 1
                    for x in Reduction.iterate(caChange):
                        addFact(c, (x.name, '-|>'), a,
                                justReference(a, (x.name, '->'), b) + justReference(c, (x.name, '-|>'), b))
    return r

# Uses '-|>' and 'c', affects '-|>'
def conservativeClosure(): # Close non-implications over conservativity results
    r = 0
    for c in principles:
        for b in principles:
            if b == c: continue
            
            if not Reduction.isPresent(Reduction.RCA, notImplies[(c,b)]): continue
            # c does not imply b
            for a in principles:
                if a == b or a == c: continue
                
                # If c does not imply b, b is (form), and a is (form)-conversative over c, then a does not imply b.
                frm = form[b] & conservative[(a,c)]
                if frm != Form.none:
                    if not Reduction.isPresent(Reduction.RCA, notImplies[(a,b)]):
                        r = 1
                        addFact(a, ('RCA', '-|>'), b,
                                justReference(c, ('RCA', '-|>'), b) + justReference(a, (Form.strongest(frm).name, 'c'), c))
                    
    return r

# Uses '->' and '-|>', affects 'nc'
def extractNonConservation(): # Transfer non-implications to non-conservation facts
    r = 0
    for c in principles:
        for a in principles:
            if a == c: continue
            
            for b in principles:
                if b == a or b == c: continue
                
                # If a implies c, but b does not imply c, and c is (form), then a is not (form)-conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(a,c)]) and Reduction.isPresent(Reduction.RCA, notImplies[(b,c)]):
                    for x in Form.iterate(form[c]):
                        addFact(a, (x.name, 'nc'), b,
                                justReference(a, ('RCA', '->'), c) + justReference(b, ('RCA', '-|>'), c))
    return r

def deriveInferences():
    start = time.clock()
    eprint('Adding trivial facts...')
    addTrivialFacts()
    eprint('Weakening conjunctions...')
    weakenConjunctions()
    eprint('Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    eprint('Looping over implications and conservation facts:')
    i = 1 # implies updated
    c = 1 # conservative updated
    n = 0
    while i != 0 or c != 0:
        n += 1
        io = i
        co = c
        
        i = 0
        c = 0
        
        if io != 0:
            eprint('Reducing implications over conjunctions...')
            i = max(i, reductionConjunction())
            
            eprint('Finding transitive implications...')
            i = max(i, transitiveClosure(Reduction, implies, '->'))
        if co != 0:
            eprint('Finding transitive conservation facts...')
            c = max(c, transitiveClosure(Form, conservative, 'c'))
        
        eprint('Relating implications and conservation facts...')
        (ip, cp) = rcClosure()
        i = max(i, ip)
        c = max(c, cp)
    eprint('Finished with implications.')
    eprint('Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    eprint('Extracting equivalences...')
    extractEquivalences()
    eprint('Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    eprint('Looping over non-implications and conservation facts:')
    r = 1
    n = 0
    while r != 0:
        n += 1
        r = 0
        
        eprint('Splitting over conjunctions...')
        r = max(r, conjunctionSplit())
        
        eprint('Closing over implications...')
        r = max(r, nonImplicationClosure())
        
        eprint('Closing over conservation facts...')
        r = max(r, conservativeClosure())
    eprint('Finished with non-implications.')
    eprint('Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    eprint('Extracting non-conservation facts...')
    extractNonConservation()
    eprint('Elapsed: {0:.6f} s\n'.format(time.clock() - start))

if sys.version_info < (3,):
    import cPickle as pickle
else:
    import pickle
def databaseDump(dumpFile):
    start = time.clock()
    eprint('Dumping updated database to binary file...')
    with open(dumpFile, 'wb') as f:
        pickle.dump(Version, f, pickle.HIGHEST_PROTOCOL)
        pickle.dump({'principles': principles,
                     'implication': (implies, notImplies),
                     'conservation': (conservative, nonConservative),
                     'form': form,
                     'primary': (primary, primaryIndex),
                     'justify': justify}, f, pickle.HIGHEST_PROTOCOL)
    eprint('Elapsed: {0:.6f} s\n'.format(time.clock() - start))

from optparse import OptionParser, OptionGroup
def main():
    absoluteStart = time.clock()
    eprint('\nRM Zoo (v{0})\n'.format(Version))

    parser = OptionParser('Usage: %prog [options] database output', version='%prog ' + Version + ' (' + Date + ')')

    parser.set_defaults()

    (options, args) = parser.parse_args()
    if len(args)>2:
        parser.error('Too many arguments provided.')
    if len(args)<1:
        parser.error('No database file specified.')
    if len(args)<2:
        parser.error('No output file specified.')

    import os
    databaseFile = args[0]
    outputFile = args[1]
    if not os.path.exists(databaseFile):
        parser.error('Database file "' + databaseFile + '" does not exist.')
    
    parseDatabase(databaseFile)
    deriveInferences()
    databaseDump(outputFile)
    eprint('Total elapsed time: {0:.6f} s'.format(time.clock() - absoluteStart))

if __name__ == '__main__':
    main()