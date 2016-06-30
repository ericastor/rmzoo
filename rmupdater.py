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

from __future__ import print_function, unicode_literals

import sys
import time
from codecs import open
from collections import defaultdict, deque
from functools import lru_cache

if sys.version_info < (3,):
    import cPickle as pickle
else:
    import pickle

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

Error = False
def warning(s):
    global Error
    Error = True
    eprint(s)

def error(s):    # Throw exception
    raise Exception(s)

Date = u'30 May 2016'
Version = u'4.0'

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
justComplexity = {}
justDependencies = defaultdict(set)

printedJustify = {}

def _refComplexity(jst):
    complexity = 1
    if not isinstance(jst, str):
        for ref in jst:
            if isinstance(ref, str):
                complexity += 1
            else:
                complexity += getComplexity(*ref)
    return complexity

def getComplexity(a, op, b):
    fact = (a, op, b)
    
    if fact not in justComplexity:
        justComplexity[fact] = _refComplexity(justify[fact])
    
    return justComplexity[fact]

minimizeComplexity = False

def addJustification(a, op, b, jst):
    fact = (a, op, b)
    if not minimizeComplexity:
        if fact in justify:
            return 0
        else:
            justify[fact] = jst
            return 1
    
    dependencies = set([ref for ref in jst if not isinstance(ref, str)])
    
    if fact not in justify:
        justify[fact] = jst
        for f in dependencies:
            justDependencies[f].add(fact)
        return 1
    else:
        if jst == justify[fact]:
            return 0
        
        complexity = _refComplexity(jst)
        if complexity >= getComplexity(*fact):
            return 0
        else:
            # Remove cached complexities dependent on the justification of 'a op b'
            Q = deque([fact])
            exhausted = set()
            while len(Q) > 0:
                f = Q.popleft()
                if f in justComplexity:
                    del justComplexity[f]
                exhausted.add(f)
                Q.extend(justDependencies[f] - exhausted)
            
            # Set new dependencies
            if fact in justify:
                oldDependencies = set([ref for ref in justify[fact] if not isinstance(ref, str)])
            else:
                oldDependencies = set()
            for f in (oldDependencies - dependencies):
                justDependencies[f].remove(fact)
            for f in (dependencies - oldDependencies):
                justDependencies[f].add(fact)
            
            justify[fact] = jst
            justComplexity[fact] = complexity
            return 1

_justLineMarker = u'*'
_justIndentMarker = u'@'
justMarker = _justLineMarker + _justIndentMarker
_justIndented = justMarker + _justIndentMarker
_justFormat = justMarker + u'{0}: '
def indentJust(jst):
    return jst.replace(justMarker, _justIndented)
def printJustification(a, op, b, formatted=True):
    fact = (a, op, b)
    
    if fact not in printedJustify:
        jst = justify[fact]
        if isinstance(jst, str):
            printedJustify[fact] = _justFormat.format(printFact(*fact)) + jst
        else:
            printedJustify[fact] = _justFormat.format(printFact(*fact)) \
                                 + u''.join((_justIndented+f if isinstance(f, str) else indentJust(printJustification(*f, formatted=False))) for f in jst)
    
    if formatted:
        return printedJustify[fact].replace(_justLineMarker, u'\n').replace(_justIndentMarker, u'    ')
    else:
        return printedJustify[fact]

principles = set([u'RCA'])
principlesList = []

def addPrinciple(a):
    setA = set(a.split(u'+'))
    a = u'+'.join(sorted(setA))
    principles.add(a)
    principles.update(setA)
    return a

def printFact(a, op, b):
    return u'{0} {1} {2}'.format(a, printOp(op), b)

def printOp(op):
    if op[1] == u'nc':
        return u'n{0}c'.format(op[0])
    else:
        return u'{0}{1}'.format(*op)

def addUnjustified(a, op, b):
    error(u'The fact "{0}" is not justified.'.format(printFact(a, op, b)))

def addFact(a, op, b, jst):
    ret = addJustification(a, op, b, jst)
    if ret == 0:
        return 0
    
    fact = (a, op, b)
    if op[1] == u'->': # reduction
        r = Reduction.fromString(op[0])
        addReduction(a, r, b)
        for x in Reduction.iterate(Reduction.weaker(r)):
            if x == r: continue
            
            addJustification(a, (x.name, op[1]), b, (fact,))
            if Reduction.isPresent(x, notImplies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'->'),b) + u'\n\n' + 
                        printJustification(a,(x.name,u'-|>'),b))
    elif op[1] == u'-|>': # non-reduction
        r = Reduction.fromString(op[0])
        addNonReduction(a, r, b)
        for x in Reduction.iterate(Reduction.stronger(r)):
            if x == r: continue
            
            addJustification(a, (x.name, op[1]), b, (fact,))
            if Reduction.isPresent(x, implies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'->'),b) + u'\n\n' + 
                        printJustification(a,(x.name,u'-|>'),b))
    elif op[1] == u'<->': # equivalence
        r = Reduction.fromString(op[0])
        addFact(a, (op[0], u'->'), b, (fact,))
        addFact(b, (op[0], u'->'), a, (fact,))
    elif op[1] == u'c': # conservation
        frm = Form.fromString(op[0])
        addConservative(a, frm, b)
        for x in Form.iterate(Form.weaker(frm)):
            if x == frm: continue
            
            addJustification(a, (x.name, op[1]), b, (fact,))
            if Reduction.isPresent(x, nonConservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'c'),b) + u'\n\n' + 
                        printJustification(a,(x.name,u'nc'),b))
    elif op[1] == u'nc': # non-conservation
        frm = Form.fromString(op[0])
        addNonConservative(a, frm, b)
        for x in Form.iterate(Form.stronger(frm)):
            if x == frm: continue
            
            addJustification(a, (x.name, op[1]), b, (fact,))
            if Reduction.isPresent(x, conservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'c'),b) + u'\n\n' + 
                        printJustification(a,(x.name,u'nc'),b))
    else:
        error(u'Unrecognized operator {0}'.format(op))
    
    return 1

def addForm(a, frm):
    form[a] |= Form.stronger(frm)

def addPrimary(a):
    primary.add(a)
    primaryIndex.append(a)

from pyparsing import *
def parseDatabase(databaseString, quiet=False):
    start = time.clock()
    if not quiet: eprint(u'Parsing database...')
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

    comments = Suppress(Literal( "#" ) + SkipTo(LineEnd()))

    # Represent and parse database file
    entry = fact | formDef | primary | unjustified | comments
    database = ZeroOrMore( entry ) + StringEnd()
    
    database.parseString(databaseString)
    
    global principlesList
    principlesList = sorted(principles)
    
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

# No inputs; affects '->' and 'c'.
def addTrivialFacts():
    for a in principlesList:
        addFact(a, (u'sW', u'->'), a, u'')
        addFact(a, (u'RCA', u'->'), a, u'')
        addFact(a, (u'rPi12', u'c'), a, u'')
        if a != u'RCA':
            addFact(a, (u'sW', u'->'), u'RCA', u'')
            addFact(a, (u'RCA', u'->'), u'RCA', u'')

# No inputs; affects '->'
def weakenConjunctions():
    for a in principlesList:
        splitA = a.split(u'+')
        if len(splitA) == 1: continue # a is not a conjunction
        setA = set(splitA)
        
        for b in principlesList:
            splitB = b.split(u'+')
            if len(splitB) >= len(splitA): continue # b cannot be a strict subset of a
            setB = set(splitB)
            
            if setB <= setA:
                addFact(a,(u'sW',u'->'),b,u'')
                addFact(a,(u'RCA',u'->'),b,u'')

# Uses '->', affects '->'
def reductionConjunction(): # Conjunctions follow from their conjuncts
    r = 0
    for b in principlesList:
        splitB = b.split(u'+')
        if len(splitB) == 1: continue # b is not a conjunction
        setB = set(splitB)
        
        for a in principlesList:
            if a == b: continue
            
            conj = ~0
            for x in splitB:
                conj &= implies[(a,x)]
            if conj == 0: continue
            
            for x in Reduction.iterate(conj):
                r |= addFact(a, (x.name, u'->'), b,
                             tuple([(a, (x.name, u'->'), t) for t in splitB]))
    return r

# Complete (current) transitive closure of array, using Floyd-Warshall
def transitiveClosure(cls, array, opName): # Take the transitive closure
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            for b in principlesList:
                if b == a or a == c: continue
                
                transitive = array[(a,c)] & array[(c,b)]
                if transitive == 0: continue
                
                for x in cls.iterate(transitive):
                    r |= addFact(a, (x.name, opName), b,
                                 ((a, (x.name, opName), c), (c, (x.name, opName), b)))
    return r

# Uses '->' and 'c', affects '->' and 'c'
def rcClosure(): # Connect implication and conservativity
    imp = 0
    con = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            for b in principlesList:
                if b == a or b == c: continue
                
                # If c -> a and c is conservative over b, then a is conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(c,a)]):
                    if conservative[(c,b)] == 0: continue
                    
                    for x in Form.iterate(conservative[(c,b)]):
                        con |= addFact(a, (x.name, u'c'), b,
                                       ((c, (u'RCA', u'->'), a), (c, (x.name, u'c'), b)))
                
                # If b -> c and a is conservative over c, then a is conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(b,c)]):
                    if conservative[(a,c)] == 0: continue
                    
                    for x in Form.iterate(conservative[(a,c)]):
                        con |= addFact(a, (x.name, u'c'), b,
                                       ((b, (u'RCA', u'->'), c), (a, (x.name, u'c'), c)))
                
                # If c -> b, c is (form)-conservative over a, and b is (form), then a -> b.
                frms = form[b] & conservative[(c,a)]
                if frms != Form.none and Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                    frm = Form.strongest(frms)
                    imp |= addFact(a, (u'RCA', u'->'), b,
                                   ((c, (u'RCA', u'->'), b), (c, (frm.name, u'c'), a), u'{0} form {1}'.format(b, frm.name)))
    return (imp, con)

# Uses '->', affects ONLY justify
def extractEquivalences(): # Convert bi-implications to equivalences
    r = 0
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            equiv = implies[(a,b)] & implies[(b,a)]
            if equiv == 0: continue
            
            for x in Reduction.iterate(equiv):
                r |= addFact(a, (x.name, u'<->'), b,
                             ((a, (x.name, u'->'), b), (b, (x.name, u'->'), a)))
    return r

# Uses '-|>' and '->', affects '-|>'
def conjunctionSplit(): # Split non-implications over conjunctions
    r = 0
    for b in principlesList:
        splitB = b.split(u'+')
        setB = set(splitB)
        for c in principlesList:
            if b == c: continue
            
            splitC = c.split(u'+')
            setC = set(splitC)
            
            setBC = setB | setC
            bc = u'+'.join(sorted(setBC))
            if bc not in principles: continue
            
            for a in principlesList:
                splitImp = notImplies[(a,bc)] & implies[(a,c)]
                if splitImp == 0: continue
                
                for x in Reduction.iterate(splitImp):
                    r |= addFact(a, (x.name, u'-|>'), b,
                                 ((a, (x.name, u'-|>'), bc), (a, (x.name, u'->'), c)))
    return r

# Uses '->' and '-|>', affects '-|>'
def nonImplicationClosure(): # "transitive" non-implications
    r = 0
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            for c in principlesList:
                if c == a or c == b: continue
                
                bcClosure = implies[(a,b)] & notImplies[(a,c)]
                if bcClosure != 0:
                    for x in Reduction.iterate(bcClosure):
                        r |= addFact(b, (x.name, u'-|>'), c,
                                     ((a, (x.name, u'->'), b), (a, (x.name, u'-|>'), c)))
                
                caClosure = implies[(a,b)] & notImplies[(c,b)]
                if caClosure != 0:
                    for x in Reduction.iterate(caClosure):
                        r |= addFact(c, (x.name, u'-|>'), a,
                                     ((a, (x.name, u'->'), b), (c, (x.name, u'-|>'), b)))
    return r

# Uses '-|>' and 'c', affects '-|>'
def conservativeClosure(): # Close non-implications over conservativity results
    r = 0
    for c in principlesList:
        for b in principlesList:
            if b == c: continue
            
            if Reduction.isPresent(Reduction.RCA, notImplies[(c,b)]): # c does not imply b
                for a in principlesList:
                    if a == b or a == c: continue
                    
                    # If c does not imply b, b is (form), and a is (form)-conversative over c, then a does not imply b.
                    frms = form[b] & conservative[(a,c)]
                    if frms != Form.none:
                        frm = Form.strongest(frms)
                        r |= addFact(a, (u'RCA', u'-|>'), b,
                                     ((c, (u'RCA', u'-|>'), b), (a, (frm.name, u'c'), c), u'{0} form {1}'.format(b, frm.name)))
    return r

# Uses '->' and '-|>', affects 'nc'
def extractNonConservation(): # Transfer non-implications to non-conservation facts
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            for b in principlesList:
                if b == a or b == c: continue
                
                # If a implies c, but b does not imply c, and c is (form), then a is not (form)-conservative over b.
                if Reduction.isPresent(Reduction.RCA, implies[(a,c)]) and Reduction.isPresent(Reduction.RCA, notImplies[(b,c)]):
                    for x in Form.iterate(form[c]):
                        r |= addFact(a, (x.name, u'nc'), b,
                                     ((a, (u'RCA', u'->'), c), (b, (u'RCA', u'-|>'), c), u'{0} form {1}'.format(c, x.name)))
    return r

def deriveInferences(quiet=False):
    start = time.clock()
    if not quiet: eprint(u'Adding trivial facts...')
    addTrivialFacts()
    if not quiet: eprint(u'Weakening conjunctions...')
    weakenConjunctions()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Looping over implications and conservation facts:')
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
            if not quiet: eprint(u'Reducing implications over conjunctions...')
            i = max(i, reductionConjunction())
            
            if not quiet: eprint(u'Finding transitive implications...')
            i = max(i, transitiveClosure(Reduction, implies, u'->'))
        if co != 0:
            if not quiet: eprint(u'Finding transitive conservation facts...')
            c = max(c, transitiveClosure(Form, conservative, u'c'))
        
        if not quiet: eprint(u'Relating implications and conservation facts...')
        (ip, cp) = rcClosure()
        i = max(i, ip)
        c = max(c, cp)
    if not quiet: eprint(u'Finished with implications.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    if not quiet: eprint(u'Extracting equivalences...')
    extractEquivalences()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Looping over non-implications and conservation facts:')
    r = 1
    n = 0
    while r != 0:
        n += 1
        r = 0
        
        if not quiet: eprint(u'Splitting over conjunctions...')
        r = max(r, conjunctionSplit())
        
        if not quiet: eprint(u'Closing over implications...')
        r = max(r, nonImplicationClosure())
        
        if not quiet: eprint(u'Closing over conservation facts...')
        r = max(r, conservativeClosure())
    if not quiet: eprint(u'Finished with non-implications.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    if not quiet: eprint(u'Extracting non-conservation facts...')
    extractNonConservation()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

def databaseDump(dumpFile, quiet=False):
    start = time.clock()
    if not quiet: eprint(u'Formatting justifications...')
    for fact in justify:
        printJustification(*fact)
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Dumping updated database to binary file...')
    with open(dumpFile, 'wb') as f:
        pickle.dump(Version, f, pickle.HIGHEST_PROTOCOL)
        pickle.dump({'principles': principles,
                     'implication': (implies, notImplies),
                     'conservation': (conservative, nonConservative),
                     'form': form,
                     'primary': (primary, primaryIndex),
                     'justify': printedJustify}, f, pickle.HIGHEST_PROTOCOL)
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

from optparse import OptionParser, OptionGroup
def main():
    absoluteStart = time.clock()
    eprint(u'\nRM Zoo (v{0})\n'.format(Version))

    parser = OptionParser('Usage: %prog [options] database output', version='%prog ' + Version + ' (' + Date + ')')

    parser.set_defaults(minimizeComplexity=False, quiet=False, verbose=False)
    
    parser.add_option('-q', action='store_true', dest='quiet',
        help = 'Suppress progress/timing indicators.')
    parser.add_option('-s', action='store_true', dest='minimizeComplexity',
        help = 'Find the shortest proofs between principles. (WARNING: much slower)')
    parser.add_option('-v', action='store_true', dest='verbose',
        help = 'Report additional execution information.')

    (options, args) = parser.parse_args()
    if len(args)>2:
        parser.error(u'Too many arguments provided.')
    if len(args)<1:
        parser.error(u'No database file specified.')
    if len(args)<2:
        parser.error(u'No output file specified.')
    
    if options.quiet and options.verbose:
        parser.error(u'Options -q and -v are incompatible.')
    
    global minimizeComplexity
    minimizeComplexity = options.minimizeComplexity
    
    import os
    databaseFile = args[0]
    outputFile = args[1]
    if not os.path.exists(databaseFile):
        parser.error(u'Database file "' + databaseFile + u'" does not exist.')
    
    with open(databaseFile, encoding='utf-8') as f:
        parseDatabase(f.read(), options.quiet)
    deriveInferences(options.quiet)
    databaseDump(outputFile, options.quiet)
    if not options.quiet: eprint(u'Total elapsed time: {0:.6f} s'.format(time.clock() - absoluteStart))
    
        eprint(u'\nCache report: ')
        eprint(u'   Reduction.strongest: {0}'.format(Reduction.strongest.cache_info()))
        eprint(u'   Reduction.iterate: {0}'.format(Reduction.iterate.cache_info()))
        eprint(u'   Form.strongest: {0}'.format(Form.strongest.cache_info()))
        eprint(u'   Form.iterate: {0}'.format(Form.iterate.cache_info()))
        eprint(u'   printOp: {0}'.format(printOp.cache_info()))

if __name__ == '__main__':
    main()