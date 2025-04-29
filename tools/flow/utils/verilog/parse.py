#!/usr/bin/env python3
# Parses verible's verilog syntax tree
from abc import abstractmethod
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

    @abstractmethod
    def rename_symbol(self, old: str, new: str):
        """
        Renames a symbol in the syntax tree.

        Args:
            old: The old symbol name.
            new: The new symbol name.
        """


# A syntax tree node that contains children
class ControlNode(Node):
    def __init__(self, tag: str, children: list[Node]):
        super().__init__(tag)
        self.children = children

    def __str__(self):
        return " ".join(str(c) for c in self.children)

    def rename_symbol(self, old: str, new: str):
        for c in self.children:
            c.rename_symbol(old, new)


# A syntax tree node that contains no children
class LeafNode(Node):
    def __init__(self, tag: str, text: str):
        super().__init__(tag)
        self.text = text

    def __str__(self):
        line_end_tags = set([";", "endgenerate", "end", "endmodule", "endcase"])
        return (self.text + "\n") if self.tag in line_end_tags else self.text

    def rename_symbol(self, old: str, new: str):
        if self.tag == "SymbolIdentifier" and self.text == old:
            self.text = new


class VerilogAST(ControlNode):
    def __init__(self, tag: str, children: list[Node]):
        super().__init__(tag, children)

    @property
    def modules(self) -> list[ControlNode]:
        return [c for c in self.children if c.tag == "kModuleDeclaration"]

    @staticmethod
    def module_name(module: ControlNode) -> str:
        assert module.children[0].tag == "module"
        assert module.children[1].tag == "SymbolIdentifier"

        return module.children[1].text

    def __str__(self):
        # Convert the syntax tree to a string
        s = "\n".join(str(c) for c in self.children)
        # format using verible
        s = subprocess.run(
            ["verible-verilog-format", "-"],
            input=s.encode("utf-8"),
            stdout=subprocess.PIPE,
        )
        return s.stdout.decode("utf-8")


def parse(file: str) -> VerilogAST:
    """
    Parses a verilog file into a syntax tree.

    Args:
        file: The verilog file to parse.
    Returns:
        A dictionary mapping file names to syntax trees.
    """

    def parse_tree_rec(j):
        if "children" in j:
            return ControlNode(
                j["tag"], [parse_tree_rec(c) for c in j["children"] if c is not None]
            )
        else:
            return LeafNode(j["tag"], j.get("text", j["tag"]))

    def parse_tree(j):
        return VerilogAST(j["tag"], [parse_tree_rec(c) for c in j["children"]])

    # Run verilator to get rid of `line macros
    trees = subprocess.run(["verilator", "-E", "-P", file], stdout=subprocess.PIPE)

    trees = subprocess.run(
        ["verible-verilog-syntax", "--printtree", "--export_json", "-"],
        input=trees.stdout,
        stdout=subprocess.PIPE,
    )
    trees = json.loads(trees.stdout)

    trees = {
        filename: parse_tree(filedata["tree"]) for filename, filedata in trees.items()
    }

    assert len(trees) == 1, "Expected exactly one file to be parsed"

    return list(trees.values())[0]


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

    print("// Parsing file: " + args.file)
    print(str(parse(args.file)))


if __name__ == "__main__":
    main()
