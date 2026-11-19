"""Apply the projection-only edits to lower-builder batches."""
from pathlib import Path
import hashlib
import re

HERE = Path(__file__).resolve().parent
HELPER = "Papers.ProjectionIncidenceSpeed"
MODES = ("baseline", "incidence", "numeric")
BATCH = re.compile(r"Batches\.B\d{3}\Z")
SCHEMA = Path("LowerSchemas/Batches/Part0.lean")
ORIGINAL_INC = (
    'noncomputable def incidenceProof : IncidenceCertificate boundary :=\n'
    '  incidenceCertificateOfChecks boundary priority priority_injective '
    '(by decide +kernel) (by decide +kernel)'
)
NEW_INC = ORIGINAL_INC.replace("incidenceCertificateOfChecks", "projectionIncidenceOfChecks")
COMMAND = "cert_incidenceProof\n"
SOURCE_HEADER = "import Papers.FiniteProjectionChecks\n"
EXTRA_HEADER = f"public import {HELPER}\n"
PRIORITY = re.compile(
    r"(?<=^noncomputable def planePriority \(p : PlaneNode boundary\) : ℕ :=\n)"
    r"((?:  if p\.val = \((?:true|false), vertices_\d+\) then \d+ else\n)+)  0(?=\n)",
    re.M,
)
ROW = re.compile(r"  if p\.val = \((true|false), vertices_(\d+)\) then (\d+) else")
PAIR = re.compile(r"\((true|false), vertices_(\d+)\)")
CACHE = re.compile(r"^  planeCache := literalFinset \[(.+)\] \(by decide \+kernel\)$", re.M)
POOL = re.compile(r"^projection_vertex_sets \[(\d+(?:, \d+)*)\]$", re.M)
ENDPOINT = re.compile(
    r"^(?:public )?theorem (certified_B\d{3}) \(j : Fin (\d+)\) :\n"
    r"    Certifies \((\d+) \+ j.val\) := by$", re.M,
)


def module_path(name):
    return Path(*name.split(".")).with_suffix(".lean")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify_schema(source):
    expected = ('elab "cert_incidenceProof " args:num* : command =>\n'
                '  NumericProofSchema.elaborate\n    r###"' + ORIGINAL_INC + '"### args')
    if source.count(expected) != 1:
        raise ValueError("Unsupported cert_incidenceProof expansion")


def endpoint_metadata(source, module):
    endpoints = ENDPOINT.findall(source)
    published = [[name, int(target)] for name, target in re.findall(
        r"^(?:public )?theorem (projection_\d+) : Certifies (\d+) ", source, re.M)]
    if not endpoints and not published:
        theorem, theorem_type, start = None, None, None
    elif len(endpoints) == 1:
        endpoint, size, start = endpoints[0]
        size, start = int(size), int(start)
        if (endpoint != f"certified_{module.split('.')[-1]}"
                or [n for _, n in published] != list(range(start, start + size))
                or any(int(name.split("_")[-1]) != n for name, n in published)):
            raise ValueError(f"Target schedule mismatch: {module}")
        theorem = f"Nonrational.TerminalVerification.{endpoint}"
        theorem_type = f"∀ j : Fin {size}, Nonrational.TerminalVerification.Certifies ({start} + j.val)"
    else:
        raise ValueError(f"Unsupported batch endpoint: {module}")
    return {"theorem": theorem, "type": theorem_type, "published_projections": published,
            "targets": len(published), "start": start}


def transform(source, module, mode):
    if mode not in MODES or not BATCH.fullmatch(module):
        raise ValueError(f"Unsupported mode or batch: {mode}, {module}")
    parts = re.split(r"(?=^section BundlePart\d+\n)", source, flags=re.M)
    if len(parts) < 2:
        raise ValueError(f"Missing pooled certificate bundles: {module}")
    if parts[0].count(SOURCE_HEADER) != 1 or EXTRA_HEADER in parts[0]:
        raise ValueError(f"Unexpected projection imports: {module}")
    out = [parts[0].replace(SOURCE_HEADER, SOURCE_HEADER + EXTRA_HEADER)
           if mode != "baseline" else parts[0]]
    restored = [out[0].replace(EXTRA_HEADER, "")]
    entries, incidences = 0, 0
    for index, part in enumerate(parts[1:]):
        pools, caches, priorities = POOL.findall(part), CACHE.findall(part), list(PRIORITY.finditer(part))
        if (not part.startswith(f"section BundlePart{index}\n") or len(pools) != 1
                or len(caches) != 1 or len(priorities) != 1 or part.count("\n" + COMMAND) != 1):
            raise ValueError(f"Unexpected pooled bundle layout: {module}/{index}")
        masks = [int(m) for m in pools[0].split(", ")]
        cache = PAIR.findall(caches[0])
        match = priorities[0]
        rows = ROW.findall(match[1])
        tagged = [(tag, mask) for tag, mask, _ in rows]
        if (len(masks) != len(set(masks)) or any(m >= 1024 for m in masks)
                or caches[0] != ", ".join(f"({t}, vertices_{m})" for t, m in cache)
                or len(set(cache)) != len(cache) or len(set(tagged)) != len(tagged)
                or set(cache) != set(tagged) or any(int(m) not in masks for _, m in tagged)):
            raise ValueError(f"Pooled masks and priority domain disagree: {module}/{index}")
        entries += len(rows)
        incidences += sum((int(mask) >> 1).bit_count() for _, mask in tagged)
        changed = part
        if mode == "numeric":
            keys = [(int(mask) + (1024 if tag == "true" else 0), int(rank))
                    for tag, mask, rank in rows]
            slots = ", ".join(f"({k}, {r})" for k, r in keys)
            body = f"  (([{slots}] : List (Nat × Nat)).lookup (projectionPlaneKey p.val)).getD 0"
            if len(dict(keys)) != len(cache) or body in part:
                raise ValueError(f"Numeric key collision: {module}/{index}")
            changed = part[:match.start()] + body + part[match.end():]
        if mode != "baseline":
            changed = changed.replace("\n" + COMMAND, "\n" + NEW_INC + "\n")
        out.append(changed)
        if mode != "baseline":
            changed = changed.replace("\n" + NEW_INC + "\n", "\n" + COMMAND)
        if mode == "numeric":
            changed = changed.replace(body, match[0])
        restored.append(changed)
    if "".join(restored) != source:
        raise ValueError(f"Round trip changed unrelated text: {module}")
    return "".join(out), {**endpoint_metadata(source, module),
                          "bundles": len(parts) - 1, "plane_priorities": entries,
                          "incident_pairs": incidences, "candidate_pairs": entries * 9}
