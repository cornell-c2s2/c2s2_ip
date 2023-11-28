from fabric import Connection as FabricConnection
from .config import get_user
import logging as log
from os import path

"""
Helper file to run remote commands on the ecelinux servers
"""


class Connection(FabricConnection):
    def run(self, command, **kwargs):
        if "env" not in kwargs:
            kwargs["env"] = {}
        kwargs["env"] = {
            "OPENLANE_ROOT": "/classes/c2s2/openlane",
            "PDK_ROOT": "/classes/c2s2/pdks",
            **kwargs["env"],
        }
        return super().run(command, **kwargs)


# Custom directory where caravel is installed
def caravel_dir() -> str:
    return path.join("/scratch", "caravel", get_user())


def caravel_installed(connection: Connection) -> bool:
    exists = connection.run(
        f'if [ ! -d "{caravel_dir()}" ]; then false; fi;', warn=True
    )
    return exists.exited == 0


# Get a connection to the server
def connect() -> Connection:
    user = get_user()
    log.info("Connecting to c2s2-dev.ece.cornell.edu as %s", user)
    connection = Connection("c2s2-dev.ece.cornell.edu", user=user)

    return connection
