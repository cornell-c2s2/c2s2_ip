#!/usr/bin/env python3
# Parses verible's verilog syntax tree
from argparse import ArgumentParser
import os
import subprocess
import json
import logging as log
from tools.flow.utils.logging import setup_logging


# Parent class for all syntax tree nodes
class Node:
    def __init__(self, tag: str):
        self.tag = tag


# A syntax tree node that contains children
class ControlNode(Node):
    def __init__(self, tag: str, children: list[Node]):
        super().__init__(tag)
        self.children = children


# A syntax tree node that contains no children
class LeafNode(Node):
    def __init__(self, tag: str, text: str):
        super().__init__(tag)
        self.text = text


def parse(file: str) -> dict[str, Node]:
    """
    Parses a verilog file into a syntax tree.

    Args:
        file: The verilog file to parse.
    Returns:
        A dictionary mapping file names to syntax trees.
    """

    def parse_tree(j):
        if "children" in j:
            return ControlNode(
                j["tag"], [parse_tree(c) for c in j["children"] if c is not None]
            )
        else:
            return LeafNode(j["tag"], j.get("text", j["tag"]))

    trees = subprocess.run(
        ["verible-verilog-syntax", "--printtree", "--export_json", file],
        stdout=subprocess.PIPE,
    )
    trees = json.loads(trees.stdout)

    trees = {
        filename: parse_tree(filedata["tree"]) for filename, filedata in trees.items()
    }

    return trees


def main():
    parser = ArgumentParser()
    parser.add_argument("file", type=str, help="Verilog file to parse")
    parser.add_argument(
        "-v",
        "--verbose",
        action="count",
        default=0,
        help="Increase logging level.",
    )
    args = parser.parse_args()
    setup_logging(args)

    print("Parsing file: " + args.file)
    print(parse(args.file))


if __name__ == "__main__":
    main()
