from functools import lru_cache

_justLineMarker = u'*'
_justIndentMarker = u'@'
justMarker = _justLineMarker + _justIndentMarker
_justIndented = justMarker + _justIndentMarker
_justFormat = justMarker + u'{0}: '
def indentJust(jst):
    return jst.replace(justMarker, _justIndented)

@lru_cache(maxsize=1024)
def printOp(op):
    if op[1] == u'nc':
        return u'n{0}c'.format(op[0])
    else:
        return u'{0}{1}'.format(*op)

def printFact(a, op, b):
    return u'{0} {1} {2}'.format(a, printOp(op), b)

printedJustify = {}
def printJustification(a, op, b, justify, formatted=True):
    fact = (a, op, b)
    
    r = ''
    try:
        r = printedJustify[fact]
    except KeyError:
        jst = justify[fact]
        if isinstance(jst, str):
            r = _justFormat.format(printFact(*fact)) + jst
        else:
            r = _justFormat.format(printFact(*fact)) \
                + u''.join((_justIndented+f if isinstance(f, str) else indentJust(printJustification(*f, justify, formatted=False))) for f in jst)
        printedJustify[fact] = r
    
    if formatted:
        return r.replace(_justLineMarker, u'\n').replace(_justIndentMarker, u'    ')
    else:
        return r