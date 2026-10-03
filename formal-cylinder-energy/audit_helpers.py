# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lucas Valbuena
# Adapted from the local bounded-seed and Gao compatibility audit helpers.

from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parent / "source"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def scrub_lean(contents):
    """Remove comments and strings, preserving line numbers and token spacing."""
    output = list(contents)
    i = 0
    depth = 0
    in_string = False
    while i < len(contents):
        if depth:
            if contents.startswith("/-", i):
                depth += 1
                output[i:i + 2] = "  "
                i += 2
            elif contents.startswith("-/", i):
                depth -= 1
                output[i:i + 2] = "  "
                i += 2
            else:
                if contents[i] != "\n":
                    output[i] = " "
                i += 1
        elif in_string:
            if contents[i] == "\\" and i + 1 < len(contents):
                output[i] = " "
                if contents[i + 1] != "\n":
                    output[i + 1] = " "
                i += 2
            else:
                if contents[i] == '"':
                    in_string = False
                if contents[i] != "\n":
                    output[i] = " "
                i += 1
        elif contents.startswith("/-", i):
            depth = 1
            output[i:i + 2] = "  "
            i += 2
        elif contents.startswith("--", i):
            while i < len(contents) and contents[i] != "\n":
                output[i] = " "
                i += 1
        elif contents[i] == '"':
            in_string = True
            output[i] = " "
            i += 1
        else:
            i += 1
    require(depth == 0 and not in_string, "Unclosed Lean comment or string")
    return "".join(output)

def source_inventory(module):
    path = ROOT / (module + ".lean")
    clean = scrub_lean(path.read_text())
    namespace = []
    frames = []
    declarations = []
    private_declarations = []
    anonymous_instances = []
    imports = []
    ident = r"(?:«[^»]+»|[\w'][\w'?!]*)(?:\.(?:«[^»]+»|[\w'][\w'?!]*))*"
    decl = re.compile(
        r"^(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|"
        r"scoped|local)\s+)*)"
        r"(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|instance)\b"
        r"(?:\s+(?P<name>" + ident + r"))?")
    for lineno, raw in enumerate(clean.splitlines(), 1):
        line = raw.strip()
        if line.startswith("import "):
            imports.extend(line.removeprefix("import ").split())
        if line.startswith("namespace "):
            name = line.removeprefix("namespace ").strip()
            frames.append(("namespace", name, list(namespace)))
            namespace = (name.removeprefix("_root_.").split(".")
                         if name.startswith("_root_.") else namespace + name.split("."))
            continue
        section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(\S+))?", line)
        if section:
            frames.append(("section", section.group(1) or "", list(namespace)))
            continue
        end = re.fullmatch(r"end(?:\s+(\S+))?", line)
        if end:
            require(bool(frames), f"{module}:{lineno}: unmatched end")
            _, name, previous = frames.pop()
            require(not end.group(1) or end.group(1) in {name, name.split(".")[-1]},
                    f"{module}:{lineno}: mismatched end {end.group(1)}")
            namespace = previous
            continue
        if line == "mutual":
            raise RuntimeError(f"{module}:{lineno}: add explicit mutual-block parser support")
        while line.startswith("@["):
            closing = line.find("]")
            require(closing >= 0, f"{module}:{lineno}: multiline attribute requires review")
            line = line[closing + 1:].strip()
        match = decl.match(line)
        if not match:
            continue
        kind, name = match.group("kind"), match.group("name")
        if kind == "instance" and name is None:
            anonymous_instances.append(lineno)
            continue
        require(name is not None, f"{module}:{lineno}: missing declaration name")
        qualified = (name.removeprefix("_root_.") if name.startswith("_root_.")
                     else ".".join(namespace + [name]))
        item = {"name": qualified, "kind": kind, "line": lineno}
        require(kind != "axiom", f"New axiom declaration is forbidden: {qualified}")
        target = private_declarations if "private" in match.group("mods").split() else declarations
        target.append(item)
    require(all(kind == "section" and not name for kind, name, _ in frames),
            f"{module}: unclosed named namespace/section")
    return {
        "module": module, "sha256": sha(path), "imports": imports,
        "named_declarations": declarations, "private_declarations": private_declarations,
        "anonymous_instance_lines": anonymous_instances,
    }
