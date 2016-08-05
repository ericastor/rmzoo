#! /usr/bin/env python

##################################################################################
#
#   The Reverse Mathematics Zoo
#   by Damir Dzhafarov
#   - Version 1.0 started August, 2010
#   - Version 2.0 started August, 2013
#   Revised by Eric Astor
#   - Version 3.0 - 29 May 2016
#   - Version 4.0 - started 30 May 2016
#   - Version 4.1 - optimizations & refactoring, started 2 July 2016
#   - Version 4.2 - new forms and reasoning, started 12 July 2016
#   - Version 4.3 - changed internal representations, started 21 July 2016
#   - Version 4.4 - moved to a shelf database, started 25 July 2016
#   - Version 5.0 - clean implementation of inference rules, started 1 August 2016
#   Documentation and support: http://rmzoo.uconn.edu
#
##################################################################################

from __future__ import print_function

import sys

import itertools
from io import open
from collections import defaultdict

from version_guard import isString, closingWrapper

from rmupdater import standardizeFact

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

Error = False
def warning(s):
    global Error
    Error = True
    eprint(s)

def error(s):    # Throw exception
    raise Exception(s)

Date = u'1 August 2016'
Version = u'5.0'
DatabaseVersion = u'5.0'

from rmBitmasks import *
from renderJustification import *

_FORM_COLOR = {Form.none: "white",
  Form.weaker(Form.Pi11): "pink",
 Form.weaker(Form.rPi12): "cyan"}
_CONS_COLOR = {Form.none: "white",
  Form.weaker(Form.Pi11): "pink",
 Form.weaker(Form.rPi12): "cyan"}
    
##################################################################################
#
#   GET OPTIONS
#
##################################################################################
    
eprint(u'\nRM Zoo (v{0})'.format(Version))

from optparse import OptionParser, OptionGroup

parser = OptionParser(u'Usage: %prog [options] [database]', version=u'%prog {0} ({1})'.format(Version, Date))

parser.set_defaults(implications=False,nonimplications=False,omega=False,onlyprimary=False,weak=False,strong=False,showform=False,conservation=False,add_principles=False)

parser.add_option('-i', action='store_true', dest='implications',
    help=u'Display implications between principles.')
parser.add_option('-n', action='store_true', dest='nonimplications',
    help=u'Display non-implications between principles.')
parser.add_option('-w', action='store_true', dest='weak',
    help=u'Display weakest non-redundant open implications.')
parser.add_option('-s', action='store_true', dest='strong',
    help=u'Display strongest non-redundant open implications.')
parser.add_option('-t', dest='reducibility', default='RCA',
    help=u'Display facts relative to REDUCIBILITY-implications.')
parser.add_option('-o', action='store_const', dest='reducibility', const='w',
    help=u'Display only facts that hold in omega models.')
parser.add_option('-p', action='store_true', dest='onlyprimary',
    help=u'Display only facts about primary principles.')
    
parser.add_option('-f', action='store_true', dest='showform',
    help=u'Indicate syntactic forms of principles.')
parser.add_option('-c', action='store_true', dest='conservation',
    help=u'Display known conservation results.')
    
parser.add_option('-r', dest='restrict_string', metavar='CLASS',
    help=u'Resrict to only the principles in CLASS.')

parser.add_option('-q', dest='query_string', metavar='FACT',
    help=u'Show whether FACT is known, and if so, its justification.')
parser.add_option('-F', dest='query_file', metavar='FILE',
    help=u'Query whether all facts in FILE are known, and return a list of all unknown facts.')

parser.add_option('--force', action='store_true', dest='add_principles',
    help=u'Allow queries involving novel conjunctions from the database. (WARNING: slow)')

(options, args) = parser.parse_args()

Implications = options.implications
NonImplications = options.nonimplications
Weak = options.weak
Strong = options.strong
Reducibility = Reduction.fromString(options.reducibility)
OnlyPrimary = options.onlyprimary
ShowForm = options.showform
Conservation = options.conservation
Restrict = options.restrict_string
if Restrict:
    rSet = set()
    for p in Restrict.split():
        splitP = p.split(u'+')
        setP = set(splitP)
        p = u'+'.join(sorted(setP))
        
        rSet.add(p)
        rSet.update(splitP)
    Restrict = rSet
Query = options.query_string
QueryFile = options.query_file
AddPrinciples = options.add_principles
    
# Give errors if bad options chosen

if not Implications and not NonImplications and not OnlyPrimary and not Restrict and not Weak and not Strong and not ShowForm and not Conservation and not Query and not QueryFile:
    parser.error(u'Error: No options selected.')
if OnlyPrimary:
    if not Implications and not NonImplications and not Weak and not Strong and not ShowForm and not Conservation:
        parser.error(u'Error: Option -p only works if one of -i, -n, -w, -s, -f, or -c is selected.')
if Restrict:
    if not Implications and not NonImplications and not Weak and not Strong and not ShowForm and not Conservation:
        parser.error(u'Error: Option -r only works if one of -i, -n, -w, -s, -f, or -c is selected.')
if Query:
    if Implications or NonImplications or Weak or Strong or ShowForm or Conservation or Restrict or OnlyPrimary or QueryFile:
        parser.error(u'Error: Option -q does not work with any other option (except --force).')
if QueryFile:
    if Implications or NonImplications or Weak or Strong or ShowForm or Conservation or Restrict or OnlyPrimary or Query:
        parser.error(u'Error: Option -F does not work with any other option (except --force).')

if len(args) > 1:
    parser.error(u'Too many arguments.')
if len(args) > 0:
    shelfTitle = args[0]
else:
    eprint(u'No database title specified; defaulting to "database".')
    shelfTitle = 'database'
    
##################################################################################
#
#   IMPORT AND ORGANIZE DATA
#
##################################################################################

eprint(u'Importing and organizing data...')

class VersionError(Exception):
    def __init__(self, targetVersion, actualVersion):
        super(VersionError, self).__init__(u'Version mismatch: found v{0}, targeting v{1}'.format(actualVersion, targetVersion))

import shelve

principles = {}
implies, notImplies = {}, {}
conservative, nonConservative = {}, {}
form = {}
primary, primaryIndex = {}, {}
justify = {}
def getDatabase():
    return {'version': DatabaseVersion,
            'principles': principles,
            'implication': (implies, notImplies),
            'conservation': (conservative, nonConservative),
            'form': form,
            'primary': (primary, primaryIndex),
            'justify': justify}

equivalent = defaultdict(set)
def setDatabase(database):
    if database['version'] != DatabaseVersion:
        raise VersionError(DatabaseVersion, database['version'])
    
    global principles
    principles = database['principles']
    
    global implies, notImplies
    implies, notImplies = database['implication']
    
    global equivalent
    for a in principles:
        for b in principles:
            for r in Reduction.list(implies[(a,b)] & implies[(b,a)]):
                equivalent[(a, r)].add(b)
    
    global conservative, nonConservative
    conservative, nonConservative = database['conservation']
    
    global form
    form = database['form']
    
    global primary, primaryIndex
    primary, primaryIndex = database['primary']
    
    global justify
    justify = database['justify']

def loadDatabase(shelfTitle):
    with closingWrapper(shelve.open(shelfTitle, flag='r', protocol=2)) as shelf:
        setDatabase(shelf)
loadDatabase(shelfTitle)

def knownEquivalent(a, reduction, justification=True):
    if a in principles:
        if justification:
            return (a, None)
        else:
            return a
    
    splitA = a.split(u'+')
    if any((p not in principles) for p in splitA):
        if justification:
            return (None, None)
        else:
            return None
    
    aPrime = None
    for equiv in itertools.product(*(equivalent[(p, reduction)] for p in splitA)):
        aPrime = u'+'.join(sorted(set(equiv)))
        if aPrime in principles:
            if justification:
                equivJst = tuple((p, (reduction, u'<->'), q) for (p,q) in zip(splitA, equiv) if p != q)
                return (aPrime, equivJst)
            else:
                return aPrime
    
    if justification:
        return (None, None)
    else:
        return None
    
def queryDatabase(a, op, b, justification=True):
    if op[1] in (u'c', u'nc'):
        reduction = Reduction.RCA
    else:
        reduction = op[0]
    
    if justification:
        aPrime, aJst = knownEquivalent(a, reduction, justification)
        bPrime, bJst = knownEquivalent(b, reduction, justification)
        if aJst is not None:
            justify[(a, (reduction, u'<->'), aPrime)] = aJst
        if bJst is not None:
            justify[(b, (reduction, u'<->'), bPrime)] = bJst
    else:
        aPrime = knownEquivalent(a, reduction, justification)
        bPrime = knownEquivalent(b, reduction, justification)
    
    aKnown = aPrime is not None
    bKnown = bPrime is not None
    
    aConjunct = (not aKnown) and all((p in principles) for p in a.split(u'+'))
    bConjunct = (not bKnown) and all((p in principles) for p in b.split(u'+'))
    
    s = u''
    if not aKnown and not bKnown:
        s += u'Error: {0} and {1} are unknown principles.'.format(a, b)
    elif not aKnown:
        s += u'Error: {0} is an unknown principle.'.format(a)
    elif not bKnown:
        s += u'Error: {0} is an unknown principle.'.format(b)
    if aConjunct and bConjunct:
        s += u'\n\tHOWEVER: {0} and {1} are conjunctions of known principles; try running with --force.'.format(a, b)
    elif aConjunct and bKnown:
        s += u'\n\tHOWEVER: {0} is a conjunction of known principles; try running with --force.'.format(a)
    elif bConjunct and aKnown:
        s += u'\n\tHOWEVER: {0} is a conjunction of known principles; try running with --force.'.format(b)
    if len(s) > 0: error(s)
    
    if (aPrime, op, bPrime) in justify:
        if not justification:
            return True
        else:
            r = []
            if a != aPrime or b != bPrime:
                r.append(u'\n')
                if a != aPrime:
                    r.append(u'NOTE: {0} is not a known principle, but is equivalent to {1}\n'.format(a, aPrime))
                if b != bPrime:
                    r.append(u'NOTE: {0} is not a known principle, but is equivalent to {1}\n'.format(b, bPrime))
            
            if a != aPrime:
                r.append(printJustification((a, (reduction, u'<->'), aPrime), justify))
            if b != bPrime:
                r.append(printJustification((b, (reduction, u'<->'), bPrime), justify))
            r.append(printJustification((aPrime, op, bPrime), justify))
            return u''.join(r)
    else:
        return False

##################################################################################
#
#   IF RESTRICT OR QUERY: VALIDATE CLASS
#
##################################################################################

if Restrict:
    
    for a in Restrict:  # Give warnings if CLASS is not a subset of principles
        if a not in principles:
            error(u'Error: '+a+u' is not in the database.')

##################################################################################
#
#   IF QUERY: GIVE ANSWER
#
##################################################################################

from pyparsing import *

name = Word( alphas+"_+^{}\\$", alphanums+"_+^{}$\\")

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

if Query:
    query = name + Group(operator) + name + StringEnd()
    Query = query.parseString(Query)
    
    op = Query[1]
    if not isString(op):
        op = tuple(op)
    a, op, b = standardizeFact(Query[0], op, Query[2])
    
    if not (a in principles and b in principles) and AddPrinciples:
        abort = False
        for p in a.split(u'+'):
            if p not in principles:
                abort = True
                break
        for p in b.split(u'+'):
            if p not in principles:
                abort = True
                break
        if not abort:
            eprint(u'Adding new principles...')
            import rmupdater
            rmupdater.setDatabase(getDatabase())
            if a not in principles:
                rmupdater.addPrinciple(a)
            if b not in principles:
                rmupdater.addPrinciple(b)
            rmupdater.principlesList = sorted(rmupdater.principles)
            rmupdater.deriveInferences(quiet=False)
            setDatabase(rmupdater.getDatabase())
    
#    try:
    jst = queryDatabase(a, op, b)
    if jst:
        print(u'Justification for the fact "{0}":\n{1}'.format(printFact(a, op, b), jst))
    else:
        print(u'\nError: Unknown fact "{0}"'.format(printFact(a, op, b)))
        opp = None # opposite operation
        if op[1] == u'->':
            opp = (op[0], u'-|>')
        elif op[1] == u'-|>':
            opp = (op[0], u'->')
        elif op[1] == u'c':
            opp = (op[0], u'nc')
        elif op[1] == u'nc':
            opp = (op[0], u'c')
        
        if opp is not None:
            jst = queryDatabase(a, opp, b)
            if jst:
                print(u'CONTRADICTING fact known! Justification for the fact "{0}":\n{1}'.format(printFact(a, opp, b), jst))
        if op[1] == u'<->':
            opp = (op[0], u'-|>')
            jst = queryDatabase(a, opp, b)
            if jst:
                print(u'CONTRADICTING fact known! Justification for the fact "{0}":\n{1}'.format(printFact(a, opp, b), jst))
            else:
                jst = queryDatabase(b, opp, a)
                if jst:
                    print(u'CONTRADICTING fact known! Justification for the fact "{0}":\n{1}'.format(printFact(b, opp, a), jst))
#    except Exception as e:
#        print(e)

if QueryFile:
    parenth = Literal('"')
    justification = QuotedString('"""',multiline=True) | quotedString.setParseAction(removeQuotes)
    
    fact = name + ((Group(operator) + name + Suppress(Optional(justification))) | (Literal('form') + formType) | (Literal('is') + Literal('primary')))
    
    queries = []
    with open(QueryFile, encoding='utf-8') as f:
        for q in f.readlines():
            q = q.strip()
            if len(q) == 0 or q[0] == u'#': continue
            
            Q = fact.parseString(q)
            if Q[1] == u'is' and Q[2] == u'primary': continue
            
            a,op,b = Q
            if not isString(op):
                op = tuple(op)
                a,op,b = standardizeFact(a, op, b)
            
            queries.append((a, op, b, q))
    
    if AddPrinciples:
        newPrinciples = set()
        unknownPrinciples = set()
        for (a, op, b, q) in queries:
            unknown = False
            
            Q = a.split(u'+')
            if op != u'form':
                Q.extend(b.split(u'+'))
            for p in Q:
                if p not in principles:
                    unknownPrinciples.add(p)
                    unknown = True
            if not unknown:
                if a not in principles: newPrinciples.add(a)
                if op != u'form' and b not in principles: newPrinciples.add(b)
        
        if len(unknownPrinciples) > 0:
            warning(u'Unknown principles: {0}\n'.format(u', '.join(sorted(unknownPrinciples))))
        if len(newPrinciples) > 0:
            eprint(u'Adding {0:,d} new principles...'.format(len(newPrinciples)))
            import rmupdater
            rmupdater.setDatabase(getDatabase())
            for p in newPrinciples:
                rmupdater.addPrinciple(p)
            rmupdater.principlesList = sorted(rmupdater.principles)
            rmupdater.deriveInferences(quiet=False)
            setDatabase(rmupdater.getDatabase())
    
    for (a, op, b, q) in queries:
        s = u''
        known = False
        if op == u'form':
            known = Form.isPresent(b, form[a])
        else:
            try:
                known = queryDatabase(a, op, b, justification=False)
            except Exception as e:
                s += u'\n' + str(e)
            
        if not known:
            s += u'\nUnknown fact: ' + q
            
        if len(s) > 0:
            warning(s)
    eprint(u'\nFinished.')

##################################################################################
#
#   IF RESTRICT: DELETE PRINCIPLES NOT IN CLASS
#
##################################################################################

if Restrict:
    principles &= Restrict
    
##################################################################################
#
#   IF DIAGRAM: REMOVE REDUNDANT IMPLICATIONS AND NON-IMPLICATIONS 
#
##################################################################################

if Implications or NonImplications or Weak or Strong:

    eprint(u'Removing redundant facts for clarity...')
    
    # Create print versions of functions
    
    simpleImplies = defaultdict(bool)
    printImplies = defaultdict(bool)
    
    simpleNotImplies = defaultdict(bool)
    printNotImplies = defaultdict(bool)
    
    equivalent = defaultdict(bool)
    
    simpleConservative = defaultdict(noForm)
    printConservative = defaultdict(noForm)
    
    printWeakOpen = defaultdict(bool)
    printStrongOpen = defaultdict(bool)
    
    for a in principles:
        for b in principles:
            if a == b: # Remove self-relations to not confuse DOT reader
                continue
            
            simpleImplies[(a,b)] = Reduction.isPresent(Reducibility, implies[(a,b)])
            printImplies[(a,b)] = simpleImplies[(a,b)]
            
            simpleNotImplies[(a,b)] = Reduction.isPresent(Reducibility, notImplies[(a,b)])
            printNotImplies[(a,b)] = simpleNotImplies[(a,b)]
            
            if simpleImplies[(a,b)] and simpleImplies[(b,a)]:
                equivalent[(a,b)] = True
                equivalent[(b,a)] = True
            
            simpleConservative[(a,b)] = conservative[(a,b)]
            printConservative[(a,b)] = simpleConservative[(a,b)]
            
    # Assign primaries and make them unique
    
    for a in sorted(principles):
        currentPrimary = a
        currentIndex = len(primaryIndex)
        for b in principles:
            if equivalent[(a,b)] and b in primary:
                if primaryIndex.index(b) < currentIndex:
                    if currentPrimary in primary:
                        primary.remove(currentPrimary)
                    currentPrimary = b
                    currentIndex = primaryIndex.index(b)
                else:
                    primary.remove(b)
        if currentPrimary not in primary:
            primary.add(currentPrimary)
            primaryIndex.append(currentPrimary)
    
    for a in principles: # Remove facts involving non-primary principles
        if a not in primary:
            for b in principles:
                printImplies[(a,b)] = False
                printImplies[(b,a)] = False
                
                printNotImplies[(a,b)] = False
                printNotImplies[(b,a)] = False
                
                printConservative[(a,b)] = Form.none

    # Remove redundant implications
            
    for a in primary:
        for b in primary:
            for c in primary: # Remove implications obtained by transitivity
                if simpleImplies[(b,a)] and simpleImplies[(a,c)]:
                    printImplies[(b,c)] = False

    # Remove redundant non-implications

    for a in primary:
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleNotImplies[(a,c)] and simpleImplies[(b,c)]: # If a -|> c, but b -> c, then a -|> b.
                    printNotImplies[(a,b)] = False
                if simpleImplies[(c,a)] and simpleNotImplies[(c,b)]: # If c -> a, but c -|> b, then a -|> b.
                    printNotImplies[(a,b)] = False
                
    # Remove redundant conservation facts

    for a in primary:  # Remove conservation results obtained by transitivity
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleImplies[(a,b)]:
                    printConservative[(b,c)] &= ~simpleConservative[(a,c)]
                if simpleImplies[(b,c)]:
                    printConservative[(a,b)] &= ~simpleConservative[(a,c)]
    
    # Generate open implications

    for a in primary:
        for b in primary:
            if b == a: continue
            
            if not simpleImplies[(a,b)] and not simpleNotImplies[(a,b)]:
                printWeakOpen[(a,b)] = True
                printStrongOpen[(a,b)] = True

    for a in primary:
        for b in primary:
            if b == a: continue
            for c in primary:
                if c == a or c == b: continue
                
                if simpleImplies[(c,a)] and not simpleImplies[(c,b)] and not simpleNotImplies[(c,b)]: # c -> a, c ? b
                    printWeakOpen[(a,b)] = False
                if simpleImplies[(c,a)] and not simpleImplies[(b,a)] and not simpleNotImplies[(b,a)]: # c -> a, b ? a
                    printWeakOpen[(b,c)] = False
                
                if simpleImplies[(a,c)] and not simpleImplies[(c,b)] and not simpleNotImplies[(c,b)]: # a -> c, c ? b
                    printStrongOpen[(a,b)] = False
                if simpleImplies[(a,c)] and not simpleImplies[(b,a)] and not simpleNotImplies[(b,a)]: # a -> c, b ? a
                    printStrongOpen[(b,c)] = False
    
    # Find all equivalent principles
    
    equivSet = defaultdict(set)
    for a in primary:
        for b in principles:
            if equivalent[(a,b)]:
                equivSet[a].add(b)
 
##################################################################################
#
#   IF DIAGRAM: PRINT OUT THE DOT FILE
#
##################################################################################   

if Implications or NonImplications or Weak or Strong or ShowForm or Conservation:

    eprint(u'Printing DOT file...')

    print("""//
// RM Zoo (v""" + Version + """)
//

digraph G {

graph [
    rankdir = TB        // put stronger principles higher up
  ranksep = 1.5
      ]

//
// Node Styles
//

node [shape=none,color=white];

//
// Data
//""")

    if Implications:
        
        for a in primary:
            for b in primary:
                if printImplies[(a,b)]:
                    style = []
                    if printNotImplies[(b,a)] and not NonImplications:
                        style.append(u'color = "black:white:black"')
                    if len(equivSet[a]) > 0:
                        style.append(u'minlen = 2')
                    s = u''
                    if len(style) > 0:
                        s = u' [{0}]'.format(u', '.join(style))
                    print(u'" {0} " -> " {1} "{2}'.format(a,b,s))
                        
    if NonImplications:
        
        for a in primary:
            for b in primary:
                if printNotImplies[(a,b)]:
                        print(u'" {0} " -> " {1} " [color = "red"]'.format(a,b))
    
    if not OnlyPrimary:
        for a in primary:
            for b in equivSet[a]:
                print(u'" {0} " -> " {1} "  [dir = both]'.format(a,b))
                    
    if Weak:
        for a in primary:
            for b in primary:
                if printWeakOpen[(a,b)]:
                    print(u'" {0} " -> " {1} "  [color = "green"]'.format(a,b))
                
    if Strong:
        for a in primary:
            for b in primary:
                if printStrongOpen[(a,b)]:
                    print(u'" {0} " -> " {1} "  [color = "orange"]'.format(a,b))
        
    if ShowForm:
        for a in principles:
            if a in form:
                if form[a] != Form.none:
                    print(u'" {0} " [shape=box, style=filled, fillcolor={1}]'.format(a, _FORM_COLOR[form[a]]))
                
    
    if Conservation:
        for a in primary:
            for b in primary:
                if a == b: continue
                
                if printConservative[(a,b)] != Form.none:
                    print(u'" {0} " -> " {1} "  [color = "{2}"]'.format(a,b, _CONS_COLOR[printConservative[(a,b)]]))

    print(u'}')
    eprint(u'Finished.')

