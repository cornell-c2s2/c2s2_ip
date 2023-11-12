from os import path
import json
import logging as log

CONFIG_FILE = path.join(path.dirname(__file__), "config.json")

def get_config():
    """
    Get the configuration fil
    """
    if not path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, 'w') as config_file:
            json.dump({}, config_file)

    with open(CONFIG_FILE, 'r') as config_file:
        config = json.load(config_file)
    return config

def get_user():
    """
    Get the username from the config file
    """
    config = get_config()
    user = config.get("user", None)
    if user is None:
        print("No user found in the config file. Please type in your cornell NetID:")
        config["user"] = input("> ")
        with open(CONFIG_FILE, "w") as config_file:
            json.dump(config, config_file)
        user = config["user"]
    
    return user