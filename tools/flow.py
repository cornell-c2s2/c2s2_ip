#!/usr/bin/env python
from utils.config import get_user
from utils.remote import connect as connect_native
from utils.utils import setup_logging
from os import path
import logging as log
import argparse
import sys
from fabric import Connection

def caravel_dir():
    return path.join("/scratch", "caravel", get_user())

def connect():
    connection = connect_native()

    # Install if necessary
    exists = connection.run(f'if [ ! -d "{caravel_dir()}" ]; then false; fi;', warn=True)
    if exists.exited != 0:
        install(connection)
    
    return connection

def install(connection: Connection):
    """Install caravel in a custom location."""
    log.info("Installing caravel in %s", caravel_dir())

    connection.run(f"rm -rf {caravel_dir()}")
    connection.run(f"mkdir -p {caravel_dir()}")
    connection.run(f"cd {caravel_dir()} && git clone --depth 1 https://github.com/efabless/caravel_user_project.git .")

    return connection



if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Custom script to run the flow.")
    parser.add_argument("-v", "--verbose", action="count", default=0)
    parser.add_argument("--reinstall", action="store_true", default=False)
    args = parser.parse_args()
    setup_logging(args)
    connection = connect()
    if args.reinstall:
        install(connection)