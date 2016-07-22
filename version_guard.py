import sys
if sys.version_info >= (3,):
    def isString(value):
        return isinstance(value, str)
else:
    def isString(value):
        return isinstance(value, basestring)

def lru_cache(*args, **kwargs):
    def empty_decorator(f):
        f.__wrapped__ = f
        return f
    return empty_decorator
try:
    from functools import lru_cache
except ImportError:
    import platform
    if platform.python_implementation() != u'PyPy':
        try:
            from backports.functools_lru_cache import lru_cache
        except ImportError:
            pass
