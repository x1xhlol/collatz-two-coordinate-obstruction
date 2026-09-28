"""Source lexer and strict axiom-output parser reused from this project's verifier."""
import re

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_OUTPUT = re.compile(
    r"'([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)' "
    r"(?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))"
)

def lean_code(source):
    """Erase strings and nested comments, preserving line numbers and token boundaries."""
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\":
                if i + 1 >= len(source):
                    raise ValueError("Unterminated Lean string escape")
                result.extend("\n" if c == "\n" else " " for c in source[i:i + 2])
                i += 2
            else:
                quoted = char != '"'
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.extend(" " * (end - i))
            i = end
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif char == '"':
            quoted = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)

def audit_output(output, expected):
    axioms = {}
    for name, entries, no_axioms in AXIOM_OUTPUT.findall(output):
        if name in axioms:
            raise ValueError("Duplicate axiom report: " + name)
        declared = set() if no_axioms else {item.strip() for item in entries.split(",") if item.strip()}
        if not declared <= STANDARD_AXIOMS:
            raise ValueError("Nonstandard axioms: " + name + " " + repr(declared))
        axioms[name] = sorted(declared)
    if set(axioms) != set(expected) or AXIOM_OUTPUT.sub("", output).strip():
        raise ValueError("Wrong axiom coverage or unexpected compiler output:\n" + output)
    return axioms
