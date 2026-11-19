"""Read imports from the header of a generated Lean module."""
import re

HEADER_ITEM = re.compile(
    r"(?:(?:public |private |meta )*import (?:all )?(\S+)[^\S\n]*(?:\n|$)"
    r"|(?:module|prelude)[^\S\n]*(?:\n|$)|--[^\n]*(?:\n|$)|\s+)"
)


def imports(source):
    pos, dependencies = 0, []
    while pos < len(source):
        if source.startswith("/-", pos):
            depth = 1
            pos += 2
            while depth:
                marker = re.search(r"/-|-/", source[pos:])
                if marker is None:
                    raise ValueError("Unclosed Lean header comment")
                depth += 1 if marker[0] == "/-" else -1
                pos += marker.end()
            continue
        item = HEADER_ITEM.match(source, pos)
        if item is None:
            break
        if item[1] is not None:
            dependencies.append(item[1])
        pos = item.end()
    return dependencies


def local_closure(roots, graph):
    seen = set()
    todo = list(roots)
    while todo:
        name = todo.pop()
        if name in graph and name not in seen:
            seen.add(name)
            todo.extend(graph[name])
    return seen
