# File management utilities
import yaml
import json
from os import path


# Load a YAML or JSON file
def load_config(filename):
    if filename.endswith(".yml") or filename.endswith(".yaml"):
        with open(filename, "r") as f:
            return yaml.safe_load(f)
    elif filename.endswith(".json"):
        with open(filename, "r") as f:
            return json.load(f)
    else:
        raise ValueError(
            "Unknown file type for {}, expected .json or .yml".format(filename)
        )


def root_dir() -> str:
    """
    Get the root directory of the project
    """
    return path.abspath(path.join(path.dirname(__file__), "..", "..", ".."))


# From https://stackoverflow.com/questions/7204805/deep-merge-dictionaries-of-dictionaries-in-python
def merge_dict(dict1: dict, dict2: dict) -> dict:
    def merge_dict_inner(dict1: dict, dict2: dict):
        for k in set(dict1.keys()).union(dict2.keys()):
            if k in dict1 and k in dict2:
                if isinstance(dict1[k], dict) and isinstance(dict2[k], dict):
                    yield (k, dict(merge_dict(dict1[k], dict2[k])))
                else:
                    # If one of the values is not a dict, you can't continue merging it.
                    # Value from second dict overrides one in first and we move on.
                    yield (k, dict2[k])
                    # Alternatively, replace this with exception raiser to alert you of value conflicts
            elif k in dict1:
                yield (k, dict1[k])
            else:
                yield (k, dict2[k])

    return dict(merge_dict_inner(dict1, dict2))


# From https://stackoverflow.com/questions/3167154/how-to-split-a-dos-path-into-its-components-in-python
def split_path(p: str) -> list:
    """
    Split a path into its components
    """
    h, t = path.split(p)
    return (split_path(h) if len(h) and len(t) else []) + [t]
