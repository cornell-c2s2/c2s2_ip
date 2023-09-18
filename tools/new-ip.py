# Python script to generate the default folder structure for a new ip
import os
import sys
import re

### ANSI escape codes for colored output ###
red = "\033[0;31m"
green = "\033[0;32m"

template_dir = "template"
src_dir = "src"
ip_name = sys.argv[1]

# Split ip_name into words
ip_name_words = ip_name.split("_")
# ip_name in lowercase, with words separated by underscores
ip_name_lower = ip_name
# ip_name in PascalCase
ip_name_pascal = "".join([word.title() for word in ip_name_words])
# ip_name in all caps, separated by underscores
ip_name_upper = "_".join([word.upper() for word in ip_name_words])


# Replaces all instances of "template" with the ip name
#   instances in lowercase are replaced by the ip name in lowercase, with words separated by dashes
#   capitalized instances are replaced by the ip name in PascalCase
#   instances in all caps are replaced by the ip name in all caps, separated by underscores
def replace_template(s):
    return (
        s.replace("template", ip_name_lower)
        .replace("Template", ip_name_pascal)
        .replace("TEMPLATE", ip_name_upper)
    )


print(f"{green} - Starter IP created at src/{ip_name_lower}/{ip_name_lower}.v")
for dir in os.walk(template_dir):
    (dirpath, _, filenames) = dir

    # Replace "template" with ip_name in dirpath
    rdirpath = replace_template(dirpath)
    # Create the directory if it doesn't exist
    os.makedirs(os.path.join(src_dir, rdirpath), exist_ok=True)

    # Replace "template" with ip_name in filenames
    for filename in filenames:
        rfilename = replace_template(filename)
        # Copy the file
        with open(os.path.join(dirpath, filename), "r") as f:
            with open(os.path.join(src_dir, rdirpath, rfilename), "w") as rf:
                rf.write(replace_template(f.read()))

        print(f"{green} - Created src/{rdirpath}/{rfilename}")
