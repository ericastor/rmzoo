import sys
if sys.version_info >= (3,):
    def isString(value):
        return isinstance(value, str)
else:
    def isString(value):
        return isinstance(value, basestring)

# Mock "lru_cache"; actually just a pass-through decorator
def lru_cache(*args, **kwargs):
    def empty_decorator(f):
        f.__wrapped__ = f
        return f
    return empty_decorator
try:
    from functools import lru_cache
except ImportError:
    try:
        from repoze.lru import lru_cache
    except ImportError:
        pass
