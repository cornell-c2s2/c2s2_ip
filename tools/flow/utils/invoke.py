from .config import get_user
import logging as log
from os import path
from invoke import run as invoke_run

"""
Helper file to run commands on the ecelinux servers
"""


def run(command, **kwargs):
    if "env" not in kwargs:
        kwargs["env"] = {}
    kwargs["env"] = {
        "OPENLANE_ROOT": "/classes/c2s2/openlane",
        "PDK_ROOT": "/classes/c2s2/pdks",
        **kwargs["env"],
    }
    return invoke_run(command, **kwargs)


def link(src, dst):
    log.debug(f"Linking {src} to {dst}")
    run(f"ln -sf {src} {dst}")


# Custom directory where caravel is installed
def caravel_dir() -> str:
    return path.join("/scratch", "caravel", get_user())


def caravel_link() -> str:
    return path.join(path.dirname(__file__), "..", "..", "..", "caravel")


def caravel_installed() -> bool:
    exists = invoke_run(f'if [ ! -d "{caravel_dir()}" ]; then false; fi;', warn=True)
    if exists.failed:
        return False
    # Link the caravel directory to the local directory
    link(caravel_dir(), caravel_link())
    return True
