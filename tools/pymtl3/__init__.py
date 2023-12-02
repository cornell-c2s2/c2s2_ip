import pkgutil
import pymtl3

__all__ = []
for loader, module_name, is_pkg in pkgutil.walk_packages(pymtl3.__path__):
    __all__.append(module_name)
    try:
        _module = loader.find_spec(module_name).loader.load_module(module_name)
        globals()[module_name] = _module
    except ImportError:
        pass

print(globals())
