from __future__ import print_function, unicode_literals

from enum import Enum

from version_guard import lru_cache

class BitmaskEnum(int, Enum):
    def __new__(cls, value=None):
        if value is None:
            if len(cls.__members__) == 0:
                value = 0
            else:
                value = 1 << (len(cls.__members__) - 1)
        
        obj = int.__new__(cls, value)
        obj._value_ = value
        return obj
    
    @staticmethod
    def isPresent(x,magic_num):
        return (x & magic_num) != 0
    
    @classmethod
    @lru_cache(maxsize=256)
    def strongest(cls,magic_num):
        if magic_num == 0:
            return cls(0)
        else:
            return cls(1 << (magic_num.bit_length() - 1))
    
    @classmethod
    @lru_cache(maxsize=256)
    def weakest(cls,magic_num):
        if magic_num == 0:
            return cls.none
        else:
            return cls(magic_num & -magic_num)
    
    @classmethod
    @lru_cache(maxsize=256)
    def list(cls,magic_num):
        return [x for x in cls if cls.isPresent(x, magic_num)]
    
    @classmethod
    def fromString(cls,s):
        try:
            return getattr(cls, s)
        except AttributeError:
            raise NotImplementedError("The {0} `{1}` is not implemented.".format(cls.__name__, s))

class Reduction(BitmaskEnum):
    none = 0
    w = 1 << 0
    RCA = 1 << 1
    c = 1 << 2
    sc = 1 << 3
    gW = 1 << 4
    W = 1 << 5
    sW = 1 << 6
    
    @classmethod
    def fromString(cls,s):
        alias = {u'': cls.RCA,
                 u'gc': cls.w}
        if s in alias:
            return alias[s]
        else:
            try:
                return getattr(cls, s)
            except AttributeError:
                raise NotImplementedError("The reduction `{}` is not implemented.".format(s))

def noReduction():
    return Reduction.none

class Form(BitmaskEnum):
    none = 0
    Sig02 = 1 << 10
    Pi02 = 1 << 9
    Sig03 = 1 << 8
    Pi03 = 1 << 7
    uPi03 = 1 << 6
    Sig04 = 1 << 5
    Pi04 = 1 << 4
    Pi11 = 1 << 3
    rPi12 = 1 << 2
    Pi12 = 1 << 1
    Pi13 = 1 << 0

def noForm():
    return Form.none

def _completeImplications(enum, forward):
    for c in enum:
        if c == enum.none: continue
        for a in enum:
            if a == enum.none: continue
            
            if enum.isPresent(c, forward[a]):
                forward[a] |= forward[c]

def _reverseImplications(enum, forward):
    reverse = {enum.none: enum.none}
    for p0 in enum:
        if p0 == enum.none: continue
        
        reverse[p0] = enum.none
        for p1 in enum:
            if p1 == enum.none: continue
            
            if enum.isPresent(p0, forward[p1]):
                reverse[p0] |= p1
    return reverse

_R_WEAKER = {r:r for r in Reduction}

_R_WEAKER[Reduction.RCA] |= Reduction.w # RCA -> w

_R_WEAKER[Reduction.sc] |= Reduction.c # sc -> c
_R_WEAKER[Reduction.c] |= Reduction.w # c -> w

_R_WEAKER[Reduction.sW] |= Reduction.W | Reduction.sc # sW -> W, sc
_R_WEAKER[Reduction.W] |= Reduction.gW | Reduction.c # W -> gW, c
_R_WEAKER[Reduction.gW] |= Reduction.w # gW -> w

_completeImplications(Reduction, _R_WEAKER)

_R_STRONGER = _reverseImplications(Reduction, _R_WEAKER)

Reduction.weaker = lambda r: _R_WEAKER[r]
Reduction.stronger = lambda r: _R_STRONGER[r]

_F_STRONGER = {f:f for f in Form}

_F_STRONGER[Form.Pi13] |= Form.Pi12 # Pi12 implies Pi13
_F_STRONGER[Form.Pi12] |= Form.rPi12 # rPi12 implies Pi12
_F_STRONGER[Form.rPi12] |= Form.Pi11 # Pi11 implies rPi12
_F_STRONGER[Form.Pi11] |= Form.Sig04 # Sig04 implies Pi11
_F_STRONGER[Form.Pi11] |= Form.Pi04 # Pi04 implies Pi11
_F_STRONGER[Form.Pi11] |= Form.uPi03 # uPi03 implies Pi11
_F_STRONGER[Form.Sig04] |= Form.Sig03 # Sig03 implies Sig04
_F_STRONGER[Form.Sig04] |= Form.Pi03 # Pi03 implies Sig04
_F_STRONGER[Form.Pi04] |= Form.Sig03 # Sig03 implies Pi04
_F_STRONGER[Form.Pi04] |= Form.Pi03 # Pi03 implies Pi04
_F_STRONGER[Form.uPi03] |= Form.Pi03 # Pi03 implies uPi03
_F_STRONGER[Form.Sig03] |= Form.Sig02 # Sig02 implies Sig03
_F_STRONGER[Form.Sig03] |= Form.Pi02 # Pi02 implies Sig03
_F_STRONGER[Form.Pi03] |= Form.Sig02 # Sig02 implies Pi03
_F_STRONGER[Form.Pi03] |= Form.Pi02 # Pi02 implies Pi03

_completeImplications(Form, _F_STRONGER)

_F_WEAKER = _reverseImplications(Form, _F_STRONGER)

Form.weaker = lambda f: _F_WEAKER[f]
Form.stronger = lambda f: _F_STRONGER[f]