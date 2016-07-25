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
    try:
        from repoze.lru import lru_cache
    except ImportError:
        pass

class closingWrapper(object):
    def __init__(self, thing):
        self.thing = thing
    def __enter__(self):
        try:
            return self.thing.__enter__()
        except AttributeError:
            return self.thing
    def __exit__(self, *exc_info):
        try:
            self.thing.__exit__(*exc_info)
        except AttributeError:
            self.thing.close()
