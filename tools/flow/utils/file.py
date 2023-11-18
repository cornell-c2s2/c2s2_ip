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


def root() -> str:
    """
    Get the root directory of the project
    """
    return path.abspath(path.join(path.dirname(__file__), "..", "..", ".."))
