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
#   - Version 4.3 - changed internal representations, started 21 July 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function, unicode_literals

import sys
import time
from io import open
from collections import defaultdict

from version_guard import lru_cache

try:
    import cPickle as pickle
except ImportError:
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

Date = u'21 July 2016'
Version = u'4.3'

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

def addJustification(fact, jst, cplx):
    if fact not in justify or cplx < justComplexity[fact]:
        justify[fact] = jst
        justComplexity[fact] = cplx
        return 1
    else:
        return 0

def unoptimizedJustification(fact, jst, cplx):
    if fact not in justify:
        justify[fact] = jst
        return 1
    else:
        return 0

def addUnjustified(a, op, b):
    error(u'The fact "{0}" is not justified.'.format(printFact(a, op, b)))

def addFact(a, op, b, jst, cplx):
    fact = (a, op, b)
    ret = addJustification(fact, jst, cplx)
    if op[1] == u'<->': # equivalence
        ret |= addJustification((b, op, a), jst, cplx)
    if ret == 0:
        return 0
    
    if op[1] == u'->': # reduction
        r = op[0]
        addReduction(a, r, b)
        for x in Reduction.list(Reduction.weaker(r)):
            if x == r: continue
            
            ret |= addJustification((a, (x, op[1]), b),
                                    (fact,), 1 + cplx)
            if Reduction.isPresent(x, notImplies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'->'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'-|>'),b), justify))
    elif op[1] == u'-|>': # non-reduction
        r = op[0]
        addNonReduction(a, r, b)
        for x in Reduction.list(Reduction.stronger(r)):
            if x == r: continue
            
            ret |= addJustification((a, (x, op[1]), b),
                                    (fact,), 1 + cplx)
            if Reduction.isPresent(x, implies[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'->'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'-|>'),b), justify))
    elif op[1] == u'<->': # equivalence
        r = op[0]
        ret |= addFact(a, (op[0], u'->'), b,
                       (fact,), 1 + cplx)
        ret |= addFact(b, (op[0], u'->'), a,
                       (fact,), 1 + cplx)
    elif op[1] == u'c': # conservation
        frm = op[0]
        addConservative(a, frm, b)
        for x in Form.list(Form.stronger(frm)):
            if x == frm: continue
            
            ret |= addJustification((a, (x, op[1]), b),
                                    (fact,), 1 + cplx)
            if Reduction.isPresent(x, nonConservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'c'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'nc'),b), justify))
    elif op[1] == u'nc': # non-conservation
        frm = op[0]
        addNonConservative(a, frm, b)
        for x in Form.list(Form.weaker(frm)):
            if x == frm: continue
            
            ret |= addJustification((a, (x, op[1]), b),
                                    (fact,), 1 + cplx)
            if Reduction.isPresent(x, conservative[(a,b)]):
                error(u'The following facts are contradictory.\n\n' + 
                        printJustification((a,(x,u'c'),b), justify) + u'\n\n' + 
                        printJustification((a,(x,u'nc'),b), justify))
    else:
        error(u'Unrecognized operator {0}'.format(op))
    
    return 1

def standardizePrinciple(a):
    return u'+'.join(sorted(set(a.split(u'+'))))
def standardizeFact(a, op, b):
    a = standardizePrinciple(a)
    if op != u'form':
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
    _reductionType = _reductionName.setParseAction(lambda s,l,t: [Reduction.fromString(t[0])])
    reductionType = Optional(_reductionType, default=Reduction.RCA)
    postfixReductionType = Optional(Suppress(Literal("_")) + _reductionType, default=Reduction.RCA)
    
    implication = (reductionType + Literal("->")) | (Literal("=>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "->"])
    nonImplication = (reductionType + Literal("-|>")) | (Literal("=/>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "-|>"])
    equivalence = (reductionType + Literal("<->")) | (Literal("<=>") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "<->"])
    
    reduction = (Literal("<=") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "<="])
    nonReduction = (Literal("</=") + postfixReductionType).setParseAction(lambda s,l,t: [t[1], "</="])
    
    _formName = NoMatch()
    for f in Form:
        if f != Form.none:
            _formName |= Literal(f.name)
    formType = _formName.setParseAction(lambda s,l,t: [Form.fromString(t[0])])
    
    conservation = formType + Literal("c")
    nonConservation = (Literal("n") + formType + Literal("c")).setParseAction(lambda s,l,t: [t[1], "nc"])
    
    operator = implication | nonImplication | reduction | nonReduction | equivalence | conservation | nonConservation
    
    # Database lines
    unjustified = (name + Group(operator) + name + ~justification).setParseAction(lambda s,l,t: addUnjustified(*standardizeFact(t[0], tuple(t[1]), t[2])))
    
    def _addFactParseAction(s,l,t):
        a,op,b = standardizeFact(t[0], tuple(t[1]), t[2])
        addFact(a, op, b, t[3], 1)
    fact = (name + Group(operator) + name + justification).setParseAction(_addFactParseAction)

    formDef = (name + Literal("form") + formType).setParseAction(lambda s,l,t: addForm(t[0], t[2]))
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
            addFact(a, (r, u'->'), a, u'', 1)
            addFact(a, (r, u'<->'), a, u'', 1)
        for f in Form:
            addFact(a, (f, u'c'), a, u'', 1)
        if a != u'RCA':
            for r in Reduction:
                addFact(a, (r, u'->'), u'RCA', u'', 1)

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
                    addFact(a, (r, u'->'), b, u'', 1)

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
                aImpConjuncts = tuple([(a, (x, u'->'), t) for t in splitB])
                r |= addFact(a, (x, u'->'), b,
                             aImpConjuncts, sum(justComplexity[aImpX] for aImpX in aImpConjuncts))
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
                    aOpC = (a, (x, opName), c)
                    cOpB = (c, (x, opName), b)
                    
                    r |= addFact(a, (x, opName), b,
                                 (aOpC, cOpB), 1 + justComplexity[aOpC] + justComplexity[cOpB])
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
                            bImpA = (b, (Reduction.RCA, u'->'), a)
                            r |= addFact(a, (x, u'c'), b,
                                         (bImpA,), 1 + justComplexity[bImpA])
                continue
            
            cImpliesA = Reduction.isPresent(Reduction.RCA, implies[(c,a)])
            cImpA = (c, (Reduction.RCA, u'->'), a)
            acConservative = conservative[(a,c)]
            acConservativeForms = Form.list(acConservative)
            for b in principlesList:
                if b == a or b == c: continue
                
                # If c is conservative over b, and c implies a, then a is conservative over b.
                if cImpliesA:
                    cbConservative = conservative[(c,b)]
                    if cbConservative != Form.none:
                        for x in Form.list(cbConservative):
                            cConsB = (c, (x, u'c'), b)
                            r |= addFact(a, (x, u'c'), b,
                                         (cConsB, cImpA), 1 + justComplexity[cConsB] + justComplexity[cImpA])
                
                # If a is conservative over c, and b implies c, then a is conservative over b.
                if acConservative != Form.none:
                    if Reduction.isPresent(Reduction.RCA, implies[(b,c)]):
                        for x in acConservativeForms:
                            aConsC = (a, (x, u'c'), c)
                            bImpC = (b, (Reduction.RCA, u'->'), c)
                            r |= addFact(a, (x, u'c'), b,
                                         (aConsC, bImpC), 1 + justComplexity[aConsC] + justComplexity[bImpC])
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
                if b == c:
                    # If b is (form)-conservative over a and b is a (form) statement, then a implies b.
                    frms = form[b] & caConservative
                    if frms != Form.none:
                        for x in Form.list(frms):
                            bConsA = (b, (x, u'c'), a)
                            r |= addFact(a, (Reduction.RCA, u'->'), b,
                                         (bConsA, (b, u'form', x)), 2 + justComplexity[bConsA])
                    continue
                
                # If c is (form)-conservative over a, c implies b, and b is a (form) statement, then a implies b.
                frms = form[b] & caConservative
                if frms != Form.none and Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                    for x in Form.list(frms):
                        cImpB = (c, (Reduction.RCA, u'->'), b)
                        cConsA = (c, (x, u'c'), a)
                        r |= addFact(a, (Reduction.RCA, u'->'), b,
                                     (cImpB, cConsA, (b, u'form', x)), 2 + justComplexity[cImpB] + justComplexity[cConsA])
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
                aImpB = (a, (x, u'->'), b)
                bImpA = (b, (x, u'->'), a)
                r |= addFact(a, (x, u'<->'), b,
                             (aImpB, bImpA), 1 + justComplexity[aImpB] + justComplexity[bImpA])
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
                    aNImpBC = (a, (x, u'-|>'), bc)
                    aImpC = (a, (x, u'->'), c)
                    r |= addFact(a, (x, u'-|>'), b,
                                 (aNImpBC, aImpC), 1 + justComplexity[aNImpBC] + justComplexity[aImpC])
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
                        cImpA = (c, (x, u'->'), a)
                        cNImpB = (c, (x, u'-|>'), b)
                        r |= addFact(a, (x, u'-|>'), b,
                                     (cImpA, cNImpB), 1 + justComplexity[cImpA] + justComplexity[cNImpB])
                
                # If a does not imply c, but b implies c, then a does not imply b
                abClosure = aNotImpliesC & implies[(b,c)]
                if abClosure != Reduction.none:
                    for x in Reduction.list(abClosure):
                        aNImpC = (a, (x, u'-|>'), c)
                        bImpC = (b, (x, u'->'), c)
                        r |= addFact(a, (x, u'-|>'), b,
                                     (aNImpC, bImpC), 1 + justComplexity[aNImpC] + justComplexity[bImpC])
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
                        cImpB = (c, (Reduction.RCA, u'-|>'), b)
                        aConsC = (a, (x, u'c'), c)
                        r |= addFact(a, (Reduction.RCA, u'-|>'), b,
                                     (cImpB, aConsC, (b, u'form', x)), 2 + justComplexity[cImpB] + justComplexity[aConsC])
    return r

# Uses '->' and '-|>', affects 'nc'
def extractNonConservation(): # Transfer non-implications to non-conservation facts
    r = 0
    for c in principlesList:
        cForm = form[c]
        if cForm == Form.none: continue
        cForms = Form.list(cForm)
        for a in principlesList:
            if a == c:
                for b in principlesList:
                    if b == a: continue
                    
                    # If b does not imply a, and a is (form), then a is not (form)-conservative over b.
                    if Reduction.isPresent(Reduction.RCA, notImplies[(b,a)]):
                        bNImpA = (b, (Reduction.RCA, u'-|>'), a)
                        for x in cForms:
                            r |= addFact(a, (x, u'nc'), b,
                                         (bNImpA, (a, u'form', x)), 2 + justComplexity[bNImpA])
                continue
            # If a implies c, but b does not imply c, and c is (form), then a is not (form)-conservative over b.
            if Reduction.isPresent(Reduction.RCA, implies[(a,c)]):
                aImpC = (a, (Reduction.RCA, u'->'), c)
                for b in principlesList:
                    if b == a or b == c: continue
                    
                    if Reduction.isPresent(Reduction.RCA, notImplies[(b,c)]):
                        bNImpC = (b, (Reduction.RCA, u'-|>'), c)
                        for x in cForms:
                            r |= addFact(a, (x, u'nc'), b,
                                         (aImpC, bNImpC, (c, u'form', x)), 2 + justComplexity[aImpC] + justComplexity[bNImpC])
    return r

# Uses 'nc' and '->', affects 'nc'
def liftNonConservation(): # Lift non-conservation facts over known implications
    r = 0
    for c in principlesList:
        for a in principlesList:
            if a == c: continue
            
            aImpliesC = Reduction.isPresent(Reduction.RCA, implies[(a,c)])
            aImpC = (a, (Reduction.RCA, u'->'), c)
            acNonConservative = nonConservative[(a,c)]
            acNonConservativeForms = Form.list(acNonConservative)
            for b in principlesList:
                if b == a or b == c: continue
                
                # If a implies c, and c is not conservative over b, then a is not conservative over b.
                if aImpliesC:
                    cbNonConservative = nonConservative[(c,b)]
                    if cbNonConservative != Form.none:
                        for x in Form.list(cbNonConservative):
                            cNConsB = (c, (x, u'nc'), b)
                            r |= addFact(a, (x, u'nc'), b,
                                         (aImpC, cNConsB), 1 + justComplexity[aImpC] + justComplexity[cNConsB])
                
                # If a is not conservative over c, and c implies b, then a is not conservative over b.
                if acNonConservative != Form.none:
                    if Reduction.isPresent(Reduction.RCA, implies[(c,b)]):
                        for x in acNonConservativeForms:
                            aNConsC = (a, (x, u'nc'), c)
                            cImpB = (c, (Reduction.RCA, u'->'), b)
                            r |= addFact(a, (x, u'nc'), b,
                                         (aNConsC, cImpB), 1 + justComplexity[aNConsC] + justComplexity[cImpB])
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
                    aNConsC = (a, (x, u'nc'), c)
                    bConsC = (b, (x, u'c'), c)
                    r |= addFact(a, (x, u'nc'), b,
                                 (aNConsC, bConsC), 1 + justComplexity[aNConsC] + justComplexity[bConsC])
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
                bNConsA = (b, (x, u'nc'), a)
                r |= addFact(a, (Reduction.RCA, u'-|>'), b,
                             (bNConsA,), 1 + justComplexity[bNConsA])
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
    return {'version': Version,
            'principles': principles,
            'implication': (implies, notImplies),
            'conservation': (conservative, nonConservative),
            'form': form,
            'primary': (primary, primaryIndex),
            'justify': justify}

def setDatabase(database):
    if database['version'] != Version:
        raise VersionError(database['version'], Version)
    
    global principles, principlesList
    principles = database['principles']
    principlesList = sorted(principles)
    
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

def dumpDatabase(dumpFile, quiet=False):
    if not quiet: eprint(u'Facts known: {0:,d}\n'.format(len(justify)))
    
    start = time.clock()
    if not quiet: eprint(u'Dumping updated database to binary file...')
    with open(dumpFile, 'wb') as f:
        pickle.dump(getDatabase(), f, pickle.HIGHEST_PROTOCOL)
    if not quiet: eprint(u'Elapsed: {0:.6f} s\n'.format(time.clock() - start))

def loadDatabase(dumpFile, quiet=False):
    with open(dumpFile, 'rb') as f:
        database = pickle.load(f)
    
    setDatabase(database)

from optparse import OptionParser, OptionGroup
def main():
    absoluteStart = time.clock()
    eprint(u'\nRM Zoo (v{0})\n'.format(Version))

    parser = OptionParser('Usage: %prog [options] database output', version='%prog ' + Version + ' (' + Date + ')')

    parser.set_defaults(quiet=False, verbose=False)
    
    parser.add_option('-q', action='store_true', dest='quiet',
        help = 'Suppress progress/timing indicators.')
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
    
    import os
    databaseFile = args[0]
    outputFile = args[1]
    if not os.path.exists(databaseFile):
        parser.error(u'Database file "' + databaseFile + u'" does not exist.')
    
    with open(databaseFile, encoding='utf-8') as f:
        parseDatabase(f.read(), options.quiet)
    deriveInferences(options.quiet)
    dumpDatabase(outputFile, options.quiet)
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