#!/usr/bin/env python

from fabric import Connection
from .config import get_user
import logging as log

"""
Helper file to run remote commands on the ecelinux servers
"""


def connect():
    user = get_user()
    log.info("Connecting to c2s2-dev.ece.cornell.edu as %s", user)
    return Connection("c2s2-dev.ece.cornell.edu", user=user)


if __name__ == "__main__":
    connection = connect()
    result = connection.run("echo hello world!", hide=True)
    print(result.stdout)
    connection.close()
