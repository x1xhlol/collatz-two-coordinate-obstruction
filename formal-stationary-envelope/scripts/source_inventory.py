"""Lexical source inventory supplementing the complete Lean module-header constant audit."""
from pathlib import Path
import hashlib
import re


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def scrub_lean(contents):
    """Blank nested comments and escaped strings while preserving offsets and line numbers."""
    output = list(contents)
    index, depth, in_string = 0, 0, False
    while index < len(contents):
        if depth:
            if contents.startswith('/-', index):
                depth += 1
                output[index:index + 2] = '  '
                index += 2
            elif contents.startswith('-/', index):
                depth -= 1
                output[index:index + 2] = '  '
                index += 2
            else:
                if contents[index] != '\n':
                    output[index] = ' '
                index += 1
        elif in_string:
            if contents[index] == '\\' and index + 1 < len(contents):
                output[index] = ' '
                if contents[index + 1] != '\n':
                    output[index + 1] = ' '
                index += 2
            else:
                if contents[index] == '"':
                    in_string = False
                if contents[index] != '\n':
                    output[index] = ' '
                index += 1
        elif contents.startswith('/-', index):
            depth = 1
            output[index:index + 2] = '  '
            index += 2
        elif contents.startswith('--', index):
            while index < len(contents) and contents[index] != '\n':
                output[index] = ' '
                index += 1
        elif contents[index] == '"':
            in_string = True
            output[index] = ' '
            index += 1
        else:
            index += 1
    require(depth == 0 and not in_string, 'Unclosed Lean comment or string')
    return ''.join(output)


def _mask_attributes(clean):
    """Blank balanced attributes before recognizing namespace, section, and declaration commands."""
    output = list(clean)
    index = 0
    while index < len(clean):
        if not clean.startswith('@[', index):
            index += 1
            continue
        start, depth = index, 1
        index += 2
        while index < len(clean) and depth:
            if clean[index] == '[':
                depth += 1
            elif clean[index] == ']':
                depth -= 1
            index += 1
        require(depth == 0, 'Unclosed Lean attribute')
        for position in range(start, index):
            if output[position] != '\n':
                output[position] = ' '
    return ''.join(output)


def source_inventory(path: Path, module: str) -> dict:
    """Inventory source declarations; compiler-generated constants are covered by the header audit."""
    path = Path(path)
    contents = path.read_text()
    clean = _mask_attributes(scrub_lean(contents))
    namespace, frames = [], []
    declarations, private_declarations, anonymous_instances, imports = [], [], [], []
    section_visibility = 'public'
    ident = r"(?:«[^»]+»|[\w'][\w'?!]*)(?:\.(?:«[^»]+»|[\w'][\w'?!]*))*"
    modifiers = r'(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*'
    declaration = re.compile(
        r'^(?P<mods>' + modifiers + r')'
        r'(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|instance)\b'
        r'(?:\s+(?P<name>' + ident + r'))?')
    clean_lines = clean.splitlines()
    for lineno, raw in enumerate(clean_lines, 1):
        line = raw.strip()
        imported = re.fullmatch(r'(?:public\s+)?import\s+(?:all\s+)?(.+)', line)
        if imported:
            names = imported.group(1).split()
            require(all(re.fullmatch(ident, name) for name in names),
                    f'{module}:{lineno}: unsupported import syntax')
            imports.extend(names)
            continue
        opened = re.fullmatch(r'namespace\s+(' + ident + r')', line)
        if opened:
            name = opened.group(1)
            frames.append(('namespace', name, list(namespace), section_visibility))
            namespace = (name.removeprefix('_root_.').split('.') if name.startswith('_root_.')
                         else namespace + name.split('.'))
            continue
        section = re.fullmatch(r'(?P<mods>' + modifiers + r')section(?:\s+(' + ident + r'))?', line)
        if section:
            frames.append(('section', section.group(2) or '', list(namespace), section_visibility))
            words = section.group('mods').split()
            if 'private' in words:
                section_visibility = 'private'
            elif 'public' in words:
                section_visibility = 'public'
            continue
        ended = re.fullmatch(r'end(?:\s+(' + ident + r'))?', line)
        if ended:
            require(bool(frames), f'{module}:{lineno}: unmatched end')
            _, name, namespace, section_visibility = frames.pop()
            require(not ended.group(1) or ended.group(1) in {name, name.split('.')[-1]},
                    f'{module}:{lineno}: mismatched end {ended.group(1)}')
            continue
        require(line != 'mutual', f'{module}:{lineno}: explicit mutual-block support required')
        match = declaration.match(line)
        if not match:
            continue
        kind, name = match.group('kind'), match.group('name')
        if name is None and not line[match.end('kind'):].strip():
            following = next((part.strip() for part in clean_lines[lineno:] if part.strip()), '')
            continued_name = re.match(ident + r'(?=\s|$|[({:])', following)
            if continued_name is not None:
                name = continued_name.group(0)
        if kind == 'instance' and name is None:
            anonymous_instances.append(lineno)
            continue
        require(name is not None, f'{module}:{lineno}: missing declaration name')
        require(kind != 'axiom', f'{module}:{lineno}: new axiom declaration is forbidden')
        qualified = (name.removeprefix('_root_.') if name.startswith('_root_.')
                     else '.'.join(namespace + [name]))
        words = match.group('mods').split()
        private = 'private' in words or ('public' not in words and section_visibility == 'private')
        target = private_declarations if private else declarations
        target.append({'name': qualified, 'kind': kind, 'line': lineno})
    require(all(kind == 'section' and not name for kind, name, _, _ in frames),
            f'{module}: unclosed named namespace or section')
    return {'module': module, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'imports': imports, 'named_declarations': declarations,
            'private_declarations': private_declarations, 'anonymous_instance_lines': anonymous_instances}
