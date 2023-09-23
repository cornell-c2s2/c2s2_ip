# Python script to convert the ip name from
import os
import sys
import re

### ANSI escape codes for colored output ###
red = "\033[0;31m"
green = "\033[0;32m"
cyan = "\033[0;36m"
reset = "\033[0m"

template_dir = "template"
src_dir = "src"
ip_name = sys.argv[1]

# Regex that matches either PascalCase or snake_case word
pascal_or_snake = (
    r"[a-z0-9]+|[A-Z][a-z0-9]+|[A-Z][A-Z]+[0-9]*(?=-|_|[A-Z]|$)|[a-z0-9]+(?=_|-|$)"
)

words = re.findall(pascal_or_snake, ip_name)

snake_case = "_".join(words).lower()

print(
    f'{green}IP name converted to "{snake_case}".\n- Does this look correct? (y/n):{reset}'
)
inp = input("> ").lower()

while True:
    if inp in ["y", "yes"]:
        break
    elif inp in ["n", "no"]:
        print(f"{red}Try separating the words in your name with underscores.{reset}")
        exit(1)
    else:
        print(f"{red}Invalid input. Please type 'y' or 'n':{reset}")
        inp = input("> ").lower()

print(f"{green}Using IP:{reset}\n{snake_case}")
