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
#   - Version 4.1 - optimizations & refactoring, started 2 July 2016
#   - Version 4.2 - new forms and reasoning, started 12 July 2016
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

Date = u'12 July 2016'
Version = u'4.2'

from rmBitmasks import *
from renderJustification import *

principles = set([u'RCA'])
principlesList = []

def addPrinciple(a):
    setA = set(a.split(u'+'))
    a = u'+'.join(sorted(setA))
    principles.add(a)
    principles.update(setA)
    return a

implies = defaultdict(noReduction)
notImplies = defaultdict(noReduction)

def addReduction(a,reduction,b):
    implies[(a,b)] |= Reduction.weaker(reduction)

def addNonReduction(a,reduction,b):
    notImplies[(a,b)] |= Reduction.stronger(reduction)

conservative = defaultdict(noForm)
nonConservative = defaultdict(noForm)

def addConservative(a,frm,b):
    conservative[(a,b)] |= Form.stronger(frm)

def addNonConservative(a,frm,b):
    nonConservative[(a,b)] |= Form.weaker(frm)

form = defaultdict(noForm)

primary = set()
primaryIndex = []

def addForm(a, frm):
    form[a] |= Form.weaker(frm)

def addPrimary(a):
    primary.add(a)
    primaryIndex.append(a)

justify = {}
justComplexity = {}
justDependencies = defaultdict(set)

def addJustification(fact, jst):
    if fact in justify:
        return 0
    else:
        justify[fact] = jst
        return 1

def _refComplexity(jst):
    if isinstance(jst, str):
        return 1
    
    complexity = 1
    for fact in jst:
        try:
            complexity += justComplexity[fact]
        except KeyError:
            if isinstance(fact, str):
                complexity += 1
            else:
                c = _refComplexity(justify[fact])
                justComplexity[fact] = c
                complexity += c
    return complexity
def getComplexity(fact):
    try:
        return justComplexity[fact]
    except KeyError:
        complexity = _refComplexity(justify[fact])
        justComplexity[fact] = complexity
        return complexity

def optimizeJustification(fact, jst):
    complexity = None
    if fact in justify:
        if jst == justify[fact]:
            return 0
        
        complexity = _refComplexity(jst)
        if complexity >= getComplexity(fact):
            return 0
    
        # Remove cached complexities dependent on the justification of 'fact'
        Q = deque([fact])
        exhausted = set()
        while len(Q) > 0:
            f = Q.popleft()
            if f in justComplexity:
                del justComplexity[f]
            exhausted.add(f)
            Q.extend(justDependencies[f] - exhausted)
        
        # Remove old dependencies
        for f in justify[fact]:
            if not isinstance(f, str):
                justDependencies[f].discard(fact)
    
    # Add justification
    justify[fact] = jst
    for f in jst:
        if not isinstance(f, str):
            justDependencies[f].add(fact)
    if complexity is not None:
        justComplexity[fact] = complexity
    return 1

def addUnjustified(a, op, b):
    error(u'The fact "{0}" is not justified.'.format(printFact(a, op, b)))

def addFact(a, op, b, jst):
    fact = (a, op, b)
    ret = addJustification(fact, jst)
    if op[1] == u'<->': # equivalence
        ret |= addJustification((b, op, a), jst)
    if ret == 0:
        return 0
    
    if op[1] == u'->': # reduction
        r = Reduction.fromString(op[0])
        addReduction(a, r, b)
        for x in Reduction.list(Reduction.weaker(r)):
            if x == r: continue
            
            ret |= addJustification((a, (x.name, op[1]), b), (fact,))
            if Reduction.isPresent(x, notImplies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'->'),b, justify) + u'\n\n' + 
                        printJustification(a,(x.name,u'-|>'),b, justify))
    elif op[1] == u'-|>': # non-reduction
        r = Reduction.fromString(op[0])
        addNonReduction(a, r, b)
        for x in Reduction.list(Reduction.stronger(r)):
            if x == r: continue
            
            ret |= addJustification((a, (x.name, op[1]), b), (fact,))
            if Reduction.isPresent(x, implies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'->'),b, justify) + u'\n\n' + 
                        printJustification(a,(x.name,u'-|>'),b, justify))
    elif op[1] == u'<->': # equivalence
        r = Reduction.fromString(op[0])
        ret |= addFact(a, (op[0], u'->'), b, (fact,))
        ret |= addFact(b, (op[0], u'->'), a, (fact,))
    elif op[1] == u'c': # conservation
        frm = Form.fromString(op[0])
        addConservative(a, frm, b)
        for x in Form.list(Form.stronger(frm)):
            if x == frm: continue
            
            ret |= addJustification((a, (x.name, op[1]), b), (fact,))
            if Reduction.isPresent(x, nonConservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'c'),b, justify) + u'\n\n' + 
                        printJustification(a,(x.name,u'nc'),b, justify))
    elif op[1] == u'nc': # non-conservation
        frm = Form.fromString(op[0])
        addNonConservative(a, frm, b)
        for x in Form.list(Form.weaker(frm)):
            if x == frm: continue
            
            ret |= addJustification((a, (x.name, op[1]), b), (fact,))
            if Reduction.isPresent(x, conservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification(a,(x.name,u'c'),b, justify) + u'\n\n' + 
                        printJustification(a,(x.name,u'nc'),b, justify))
    else:
        error(u'Unrecognized operator {0}'.format(op))
    
    return 1

def standardizePrinciple(a):
    return u'+'.join(sorted(set(a.split(u'+'))))
def standardizeFact(a, op, b):
    a = standardizePrinciple(a)
    b = standardizePrinciple(b)
    if op[1] == u'<=':
        op = (op[0], u'->')
        a,b = b,a
    elif op[1] == u'</=':
        op = (op[0], u'-|>')
        a,b = b,a
    return a, op, b

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
    
    implication = (reductionName + Literal("->")) | (Literal("=>") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "->"])
    nonImplication = (reductionName + Literal("-|>")) | (Literal("=/>") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "-|>"])
    equivalence = (reductionName + Literal("<->")) | (Literal("<=>") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "<->"])
    
    reduction = (Literal("<=") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "<="])
    nonReduction = (Literal("</=") + Optional(Suppress(Literal("_")) + _reductionName, default=Reduction.RCA.name)).setParseAction(lambda s,l,t: [t[1], "</="])
    
    _formName = NoMatch()
    for f in Form:
        if f != Form.none:
            _formName |= Literal(f.name)
    formName = _formName
    
    conservation = formName + Literal("c")
    nonConservation = (Literal("n") + formName + Literal("c")).setParseAction(lambda s,l,t: [t[1], "nc"])
    
    operator = implication | nonImplication | reduction | nonReduction | equivalence | conservation | nonConservation
    
    # Database lines
    unjustified = (name + Group(operator) + name + ~justification).setParseAction(lambda s,l,t: addUnjustified(*standardizeFact(t[0], tuple(t[1]), t[2])))
    fact = (name + Group(operator) + name + justification).setParseAction(lambda s,l,t: addFact(*standardizeFact(t[0], tuple(t[1]), t[2]), t[3]))

    formDef = (name + Literal("form") + formName).setParseAction(lambda s,l,t: addForm(t[0], Form.fromString(t[2])))
    primary = (name + Literal("is primary")).setParseAction(lambda s,l,t: addPrimary(t[0]))
    
    comments = Suppress(Literal( "#" ) + SkipTo(LineEnd()))
    
    # Represent and parse database file
    entry = fact | formDef | primary | unjustified | comments
    database = ZeroOrMore( entry ) + StringEnd()
    
    database.parseString(databaseString)
    
    global principlesList
    principlesList = sorted(principles)
    
    if not quiet: eprint(u'Principles found: {0:,d}'.format(len(principlesList)))
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

# No inputs; affects '->' and 'c'.
def addTrivialFacts():
    for a in principlesList:
        for r in Reduction:
            addFact(a, (r.name, u'->'), a, u'')
            addFact(a, (r.name, u'<->'), a, u'')
        for f in Form:
            addFact(a, (f.name, u'c'), a, u'')
        if a != u'RCA':
            for r in Reduction:
                addFact(a, (r.name, u'->'), u'RCA', u'')

# No inputs; affects '->'
def weakenConjunctions():
    for a in principlesList:
        splitA = a.split(u'+')
        if len(splitA) == 1: continue # a is not a conjunction
        setA = set(splitA)
        
        for b in principlesList:
            if a == b: continue
            
            splitB = b.split(u'+')
            if len(splitB) >= len(splitA): continue # b cannot be a strict subset of a
            setB = set(splitB)
            
            if setB <= setA:
                for r in Reduction:
                    addFact(a, (r.name, u'->'), b, u'')

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
            if conj == Reduction.none: continue
            
            for x in Reduction.list(conj):
                r |= addFact(a, (x.name, u'->'), b,
                             tuple([(a, (x.name, u'->'), t) for t in splitB]))
    return r

# Complete (current) transitive closure of array, using Floyd-Warshall
def transitiveClosure(cls, array, opName): # Take the transitive closure
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            acRelation = array[(a,c)]
            if acRelation == cls.none: continue
            for b in principlesList:
                if b == a or b == c: continue
                
                transitive = acRelation & array[(c,b)]
                if transitive == cls.none: continue
                
                for x in cls.list(transitive):
                    r |= addFact(a, (x.name, opName), b,
                                 ((a, (x.name, opName), c), (c, (x.name, opName), b)))
    return r

# Uses '->' and 'c', affects 'c'
def liftConservation(): # Lift conservation facts over known implications
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c:
                # If b implies a, then a is conservative over b
                for b in principlesList:
                    if b == a: continue
                    
                    if Reduction.isPresent(Reduction.RCA, implies[(b,a)]):
                        for x in Form:
                            r |= addFact(a, (x.name, u'c'), b,
                                         ((b, (u'RCA', u'->'), a),))
                continue
            
            cImpliesA = Reduction.isPresent(Reduction.RCA, implies[(c,a)])
            acConservative = conservative[(a,c)]
            acConservativeForms = Form.list(acConservative)
            for b in principlesList:
                if b == a or b == c: continue
                
                # If c is conservative over b, and c implies a, then a is conservative over b.
                if cImpliesA:
                    cbConservative = conservative[(c,b)]
                    if cbConservative != Form.none:
                        for x in Form.list(cbConservative):
                            r |= addFact(a, (x.name, u'c'), b,
                                         ((c, (x.name, u'c'), b), (c, (u'RCA', u'->'), a)))
                
                # If a is conservative over c, and b implies c, then a is conservative over b.
                if acConservative != Form.none:
                    if Reduction.isPresent(Reduction.RCA, implies[(b,c)]):
                        for x in acConservativeForms:
                            r |= addFact(a, (x.name, u'c'), b,
                                         ((a, (x.name, u'c'), c), (b, (u'RCA', u'->'), c)))
    return r

# Uses '->' and 'c', affects '->'
def implementPositiveConservation(): # Apply known conservation facts to implications
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            caConservative = conservative[(c,a)]
            if caConservative == Form.none: continue
            for b in principlesList:
                if b == a: continue
                
                # If c is (form)-conservative over a, c implies b, and b is a (form) statement, then a implies b.
                frms = form[b] & caConservative
                if frms != Form.none and Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                    for x in Form.list(frms):
                        r |= addFact(a, (u'RCA', u'->'), b,
                                     ((c, (u'RCA', u'->'), b), (c, (x.name, u'c'), a), u'{0} form {1}'.format(b, x.name)))
    return r

# Uses '->', affects ONLY justify
def extractEquivalences(): # Convert bi-implications to equivalences
    r = 0
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            equiv = implies[(a,b)] & implies[(b,a)]
            if equiv == Reduction.none: continue
            
            for x in Reduction.list(equiv):
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
                if splitImp == Reduction.none: continue
                
                # If a does not imply b+c, but a implies c, then a does not imply b.
                for x in Reduction.list(splitImp):
                    r |= addFact(a, (x.name, u'-|>'), b,
                                 ((a, (x.name, u'-|>'), bc), (a, (x.name, u'->'), c)))
    return r

# Uses '->' and '-|>', affects '-|>'
def nonImplicationClosure(): # "transitive" non-implications
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            cImpliesA = implies[(c,a)]
            aNotImpliesC = notImplies[(a,c)]
            for b in principlesList:
                if b == a or b == c: continue
                
                # If c implies a, but c does not imply b, then a does not imply b
                abClosure = cImpliesA & notImplies[(c,b)]
                if abClosure != Reduction.none:
                    for x in Reduction.list(abClosure):
                        r |= addFact(a, (x.name, u'-|>'), b,
                                     ((c, (x.name, u'->'), a), (c, (x.name, u'-|>'), b)))
                
                # If a does not imply c, but b implies c, then a does not imply b
                abClosure = aNotImpliesC & implies[(b,c)]
                if abClosure != Reduction.none:
                    for x in Reduction.list(abClosure):
                        r |= addFact(a, (x.name, u'-|>'), b,
                                     ((a, (x.name, u'-|>'), c), (b, (x.name, u'->'), c)))
    return r

# Uses '-|>' and 'c', affects '-|>'
def implementNegativeConservation(): # Apply known conservation facts to non-implications
    r = 0
    for c in principlesList:
        for b in principlesList:
            if b == c: continue
            
            formB = form[b]
            if formB == Form.none: continue
            if Reduction.isPresent(Reduction.RCA, notImplies[(c,b)]): # c does not imply b
                for a in principlesList:
                    if a == b or a == c: continue
                    
                    # If c does not imply b, b is (form), and a is (form)-conversative over c, then a does not imply b.
                    frms = form[b] & conservative[(a,c)]
                    for x in Form.list(frms):
                        r |= addFact(a, (u'RCA', u'-|>'), b,
                                     ((c, (u'RCA', u'-|>'), b), (a, (x.name, u'c'), c), u'{0} form {1}'.format(b, x.name)))
    return r

# Uses '->' and '-|>', affects 'nc'
def extractNonConservation(): # Transfer non-implications to non-conservation facts
    r = 0
    for c in principlesList:
        cForm = form[c]
        if cForm == Form.none: continue
        cForms = Form.list(cForm)
        for a in principlesList:
            # If a implies c, but b does not imply c, and c is (form), then a is not (form)-conservative over b.
            if Reduction.isPresent(Reduction.RCA, implies[(a,c)]):
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    if Reduction.isPresent(Reduction.RCA, notImplies[(b,c)]):
                        for x in cForms:
                            r |= addFact(a, (x.name, u'nc'), b,
                                         ((a, (u'RCA', u'->'), c), (b, (u'RCA', u'-|>'), c), u'{0} form {1}'.format(c, x.name)))
    return r

# Uses 'nc' and '->', affects 'nc'
def liftNonConservation(): # Lift non-conservation facts over known implications
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            aImpliesC = Reduction.isPresent(Reduction.RCA, implies[(a,c)])
            acNonConservative = nonConservative[(a,c)]
            acNonConservativeForms = Form.list(acNonConservative)
            for b in principlesList:
                if b == a or b == c: continue
                
                # If a implies c, and c is not conservative over b, then a is not conservative over b.
                if aImpliesC:
                    cbNonConservative = nonConservative[(c,b)]
                    if cbNonConservative != Form.none:
                        for x in Form.list(cbNonConservative):
                            r |= addFact(a, (x.name, u'nc'), b,
                                         ((a, (u'RCA', u'->'), c), (c, (x.name, u'nc'), b)))
                
                # If a is not conservative over c, and c implies b, then a is not conservative over b.
                if acNonConservative != Form.none:
                    if Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                        for x in acNonConservativeForms:
                            r |= addFact(a, (x.name, u'nc'), b,
                                         ((a, (x.name, u'nc'), c), (c, (u'RCA', u'->'), b)))
    return r

# Uses 'c' and 'nc', affects 'nc'
def conservationConflict():
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            acNonConservative = nonConservative[(a,c)]
            for b in principlesList:
                if b == a or b == c: continue
                
                # If a is not conservative over c, but b is conservative over c, then a is not conservative over b.
                conflict = acNonConservative & conservative[(b,c)]
                if conflict == Form.none: continue
                for x in Form.list(conflict):
                    r |= addFact(a, (x.name, u'nc'), b,
                                 ((a, (x.name, u'nc'), c), (b, (x.name, u'c'), c)))
    return r

# Uses 'nc', affects '-|>'
def extractNonImplication(): # Transfer non-conservation facts to non-implications
    r = 0
    for a in principlesList:
        for b in principlesList:
            if b == a: continue
            
            # If b is not conservative over a, then a does not imply b.
            baNonConservative = nonConservative[(b,a)]
            if baNonConservative == Form.none: continue
            for x in Form.list(baNonConservative):
                r |= addFact(a, (u'RCA', u'-|>'), b,
                             ((b, (x.name, u'nc'), a),))
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
    i,c = 1,1 # implies updated and conservative updated
    n = 0
    while i != 0 or c != 0:
        n += 1
        
        io = i
        co = c
        i,c = 0,0
        
        if io != 0:
            if not quiet: eprint(u'Reducing implications over conjunctions...')
            i |= reductionConjunction() # Uses '->', affects '->'
            
            if not quiet: eprint(u'Finding transitive implications...')
            i |= transitiveClosure(Reduction, implies, u'->') # Uses '->', affects '->'
        if co != 0:
            if not quiet: eprint(u'Finding transitive conservation facts...')
            c |= transitiveClosure(Form, conservative, u'c') # Uses 'c', affects 'c'
        
        if not quiet: eprint(u'Lifting conservation facts over known implications...')
        c |= liftConservation() # Uses '->' and 'c', affects 'c'
        
        if not quiet: eprint(u'Applying known conservation facts...')
        i |= implementPositiveConservation() # Uses '->' and 'c', affects '->'
    if not quiet: eprint(u'Finished with implications and conservation facts.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))
    
    start = time.clock()
    if not quiet: eprint(u'Extracting equivalences...')
    extractEquivalences()
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))
    
    start = time.clock()
    if not quiet: eprint(u'Looping over non-implications and conservation facts:')
    ni,nc = 1,1 # notImplies updated and nonConservative updated
    n = 0
    while ni != 0 or nc != 0:
        n += 1
        
        nio = ni
        nco = nc
        ni,nc = 0,0
        
        if nio != 0:
            if not quiet: eprint(u'Splitting over conjunctions...')
            ni |= conjunctionSplit() # Uses '-|>' and '->', affects '-|>'
            
            if not quiet: eprint(u'Closing over implications...')
            ni |= nonImplicationClosure() # Uses '->' and '-|>', affects '-|>'
            
            if not quiet: eprint(u'Applying known conservation facts to non-implications...')
            ni |= implementNegativeConservation() # Uses '-|>' and 'c', affects '-|>'
            
            if not quiet: eprint(u'Extracting non-conservation facts...')
            nc |= extractNonConservation() # Uses '->' and '-|>', affects 'nc'
        
        if nco != 0:
            if not quiet: eprint(u'Lifting non-conservation facts over implications...')
            nc |= liftNonConservation() # Uses 'nc' and '->', affects 'nc'
            
            if not quiet: eprint(u'Lifting non-conservation facts over conservations...')
            nc |= conservationConflict() # Uses 'c' and 'nc', affects 'nc'
            
            if not quiet: eprint(u'Extracting non-implications...')
            ni |= extractNonImplication() # Uses 'nc', affects '-|>'
    if not quiet: eprint(u'Finished with non-implications and non-conservation facts.')
    if not quiet: eprint(u'Elapsed: {0:.6f} s (with {1} repeats)\n'.format(time.clock() - start, n))

def getDatabase():
    return {'principles': principles,
            'implication': (implies, notImplies),
            'conservation': (conservative, nonConservative),
            'form': form,
            'primary': (primary, primaryIndex),
            'justify': justify}

def setDatabase(database):
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

def databaseDump(dumpFile, quiet=False):
    if not quiet: eprint(u'Facts known: {0:,d}\n'.format(len(justify)))
    
    start = time.clock()
    if not quiet: eprint(u'Dumping updated database to binary file...')
    with open(dumpFile, 'wb') as f:
        pickle.dump(Version, f, pickle.HIGHEST_PROTOCOL)
        pickle.dump(getDatabase(), f, pickle.HIGHEST_PROTOCOL)
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

def databaseLoad(dumpFile, quiet=False):
    with open(dumpFile, 'rb') as f:
        fileVersion = pickle.load(f)
        if fileVersion != Version:
            raise VersionError(fileVersion, Version)
        database = pickle.load(f)
    
    setDatabase(database)
    
    global principlesList
    principlesList = sorted(principles)

from optparse import OptionParser, OptionGroup
def main():
    absoluteStart = time.clock()
    eprint(u'\nRM Zoo (v{0})\n'.format(Version))

    parser = OptionParser('Usage: %prog [options] database output', version='%prog ' + Version + ' (' + Date + ')')

    parser.set_defaults(ignoreComplexity=False, quiet=False, verbose=False)
    
    parser.add_option('-q', action='store_true', dest='quiet',
        help = 'Suppress progress/timing indicators.')
    parser.add_option('-f', action='store_true', dest='ignoreComplexity',
        help = 'Do not optimize for shorter proofs; runs about twice as fast.')
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
    
    global addJustification
    if not options.ignoreComplexity:
        addJustification = optimizeJustification
    
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
    
    if options.verbose:
        eprint(u'\nCache report: ')
        eprint(u'\tReduction.strongest: {0}'.format(Reduction.strongest.cache_info()))
        eprint(u'\tReduction.list: {0}'.format(Reduction.list.cache_info()))
        eprint(u'\tForm.strongest: {0}'.format(Form.strongest.cache_info()))
        eprint(u'\tForm.list: {0}'.format(Form.list.cache_info()))
        eprint(u'\tprintOp: {0}'.format(printOp.cache_info()))

if __name__ == '__main__':
    main()