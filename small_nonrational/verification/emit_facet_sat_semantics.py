#!/usr/bin/env python3
"""Emit kernel-checkable meanings for typed facet SAT certificate inputs.

This producer proves nothing itself.  Every emitted initial clause is an
application of a geometric or counter theorem; the RUP elaborator then emits
ordinary Lean proof terms checked by the kernel.  A malformed JSON witness
therefore fails elaboration or kernel checking rather than becoming an axiom.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from compress_certificate_numerals import encode as sparse_encode
from generate_clique_certificates import pack


def natural(value: int) -> str:
    if not isinstance(value, int) or value < 0:
        raise ValueError("expected a nonnegative integer")
    if value < 1 << 64:
        return str(value)
    return f'sparse_nat% "{sparse_encode(value)}"'


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def fin(value: int, size: str = "data.count") -> str:
    if value < 0:
        raise ValueError("negative finite index")
    if size == "data.count":
        return f"(facetIndex {value})"
    if size == "1024":
        return f"(ridgeIndex {value})"
    return f"(⟨{value}, by decide⟩ : Fin {size})"


def fin_list(values: list[int]) -> str:
    return "[" + ", ".join(fin(value) for value in values) + "]"


def table(expressions: list[str], start: int = 0) -> str:
    if not expressions:
        raise ValueError("empty balanced table")
    if len(expressions) == 1:
        return f"(.leaf ({expressions[0]}))"
    left = len(expressions) // 2
    return f"(.branch {start + left}\n {table(expressions[:left], start)}\n {table(expressions[left:], start + left)})"


def atom_type(variable: int, negative: bool = False) -> str:
    value = f"model S {variable}"
    return f"({value} → False)" if negative else value


def clause_type(clause: list[int]) -> str:
    return " → ".join([atom_type(abs(lit), lit > 0) for lit in clause] + ["False"])


class Emitter:
    def __init__(self, case: dict, namespace: str, full_result: bool, *,
                 raw_record: bool = False, raw_metadata: bool = True,
                 raw_import: str | None = None, direct_expr: bool = False,
                 diagnostics: bool = False):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", namespace):
            raise ValueError("invalid Lean namespace")
        if case.get("status") != "unsat":
            raise ValueError("only a completed unsatisfiability certificate can be emitted")
        self.case, self.namespace, self.full_result = case, namespace, full_result
        self.cells = case["cells"]
        self.core = case["core"]
        self.lower = bool(case["lower_only"])
        self.raw = raw_record
        if full_result and not raw_record:
            raise ValueError("complete graph certificates require --raw-record to preserve original metadata and leaves")
        self.raw_metadata = raw_metadata
        self.record = case.get("record") if self.raw else None
        if self.raw and not self.record:
            raise ValueError("raw-record emission requires an original record name")
        self.raw_import = raw_import
        self.direct_expr = direct_expr
        self.diagnostics = diagnostics
        self.edge_cover = any(rule["tag"] == "edge" for rule in self.core["rules"])
        if self.edge_cover and not self.raw:
            raise ValueError("required-edge clauses currently require original graph metadata")
        self.orbits = case.get("orbits", [])
        self.coverage = self.raw or "orbits" in case
        if self.lower and self.orbits:
            raise ValueError("leaf blockers require exact quotas")
        if self.raw and full_result and not self.raw_metadata:
            raise ValueError("DirectCore assembly requires the original metadata proofs")
        self.kind_lists = {kind: [i for i, cell in enumerate(self.cells) if cell["kind"] == kind]
                           for kind in range(len(case["quota"]))}
        self.groupings = {grouping["kind"]: grouping for grouping in case.get("groupings", [])}
        groups = {tuple(atom["vertices"]) for atom in self.core["atoms"] if atom["tag"] == "totalizer"}
        counter_groups = {(atom["kind"], tuple(atom["vertices"])) for atom in self.core["atoms"]
                          if atom["tag"] == "group_totalizer"}
        for rule in self.core["rules"]:
            if rule["tag"] == "merge":
                if rule.get("grouped"):
                    counter_groups.update((rule["kind"], tuple(vertices)) for vertices in
                                          (rule["left"], rule["right"], rule["left"] + rule["right"]))
                else:
                    groups.update((tuple(rule["left"]), tuple(rule["right"]),
                                   tuple(rule["left"] + rule["right"])))
        self.groups = {vertices: f"group{index:04d}"
                       for index, vertices in enumerate(sorted(groups))}
        self.counter_groups = {key: f"grouped{key[0]}_{index:04d}"
                               for index, key in enumerate(sorted(counter_groups))}
        self.lines: list[str] = []

    def add(self, *lines: str) -> None:
        self.lines.extend(lines)

    def context(self) -> str:
        quota = "actualQuota" if self.lower else "requirements"
        extra = " (actualQuota : Nat → Nat)" if self.lower else ""
        budget = " (hbudget : ∀ j, requirements j ≤ actualQuota j)" if self.lower else ""
        escape = ("\n    (noSame : ∀ j : Fin leafCount, ¬GrowthDAG.Same "
                  "(SparseGrowthDAG.family (leaves j)) (SparseGrowthDAG.family S))") if self.coverage else ""
        edges = "\n    (edgeCover : FacetSat.EdgeCover requiredEdges edgeRows S)" if self.edge_cover else ""
        return (f"(S : List (Fin data.count)){extra}\n"
                f"    (H : FacetSat.Boundary data.toData.kind data.toData.relation data.ridges {quota} S){budget}{edges}{escape}")

    def arguments(self) -> str:
        return (("S actualQuota H hbudget" if self.lower else "S H") +
                (" edgeCover" if self.edge_cover else "") + (" noSame" if self.coverage else ""))

    def vertices(self, values: list[int], *, grouped: bool = False, kind: int | None = None) -> str:
        if grouped:
            if kind not in self.groupings:
                raise ValueError("missing checked grouping for a grouped counter")
            if values == list(range(self.groupings[kind]["count"])):
                return f"groupKind{kind}"
            return self.counter_groups.get((kind, tuple(values)), str(values))
        for kind, vertices in self.kind_lists.items():
            if vertices == values:
                return f"kind{kind}"
        return self.groups.get(tuple(values), fin_list(values))

    def data(self) -> None:
        if self.raw:
            self.add("def vertexColumn : PackedGraphCertificate.Fields :=",
                     f"  ⟨10, {natural(pack([c['vertices'] for c in self.cells], 10))}⟩",
                     "def kindColumn : PackedGraphCertificate.Fields :=",
                     f"  ⟨3, {natural(pack([c['kind'] for c in self.cells], 3))}⟩",
                     "def data : FacetSat.Data :=",
                     f"  FacetSat.RawProjection.data {self.record} vertexColumn kindColumn",
                     "theorem projection_checked :",
                     f"    FacetSat.RawProjection.check {self.record} vertexColumn kindColumn = true := by",
                     "  decide +kernel")
        else:
            self.add("def data : FacetSat.Data where", f"  count := {len(self.cells)}")
            fields = [("embedding", 16, [c["index"] for c in self.cells]),
                      ("vertices", 10, [c["vertices"] for c in self.cells]),
                      ("faces", 1024, [c["faces"] for c in self.cells]),
                      ("kinds", 3, [c["kind"] for c in self.cells]),
                      ("cellCodes", 512, [c["cell_code"] for c in self.cells])]
            for name, width, values in fields:
                self.add(f"  {name} := ⟨{width}, {natural(pack(values, width))}⟩")
            matrix = sum(1 << (len(self.cells) * ridge + index)
                         for index, cell in enumerate(self.cells) for ridge in cell["ridges"])
            self.add(f"  ridgeMatrix := {natural(matrix)}")
        self.add("", "def facetIndex (i : Nat) : Fin data.count :=",
                 "  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩",
                 "def ridgeIndex (i : Nat) : Fin 1024 :=",
                 "  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩")
        if self.edge_cover:
            self.add("def edgeCount : Nat := 45",
                     f"def requiredEdges : Nat := {self.record}.data.requiredEdges",
                     f"def edgeRows : Fin edgeCount → Nat := {self.record}.data.edgeRows",
                     "def edgeIndex (i : Nat) : Fin edgeCount :=",
                     "  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩")
        if self.raw:
            self.add("", f"def requirements : Nat → Nat := {self.record}.data.quota", "")
        else:
            self.add("", "def requirements (j : Nat) : Nat :=",
                     "  (" + str(self.case["quota"]) + " : List Nat).getD j 0", "")
        used_kinds = {a["kind"] for a in self.core["atoms"] if "kind" in a}
        used_kinds.update(r["kind"] for r in self.core["rules"] if "kind" in r)
        enumerate_kinds = self.raw and (self.case.get("counter") == "totalizer" or
                                       any(a["tag"] == "totalizer" for a in self.core["atoms"]))
        for kind in sorted(used_kinds):
            if kind in self.groupings:
                grouping = self.groupings[kind]
                self.add(f"def groupMembers{kind} : ConcreteGrowth.Table (List (Fin data.count)) :=",
                         table([fin_list(members) for members in grouping["members"]] or ["[]"]),
                         f"def groupColors{kind} : PackedGraphCertificate.Fields :=",
                         f"  ⟨{max(1, (grouping['count'] - 1).bit_length())}, "
                         f"{natural(pack(grouping['color'], max(1, (grouping['count'] - 1).bit_length())))}⟩",
                         f"def grouping{kind} : FacetSat.Grouping data.count where",
                         f"  count := {grouping['count']}",
                         f"  members := fun g => groupMembers{kind}.get g",
                         f"  color := fun c => groupColors{kind}.get c.val",
                         f"def groupKind{kind} : List Nat := List.range grouping{kind}.count")
                if not self.direct_expr:
                    self.add(f"theorem grouping{kind}_checked :",
                             f"    grouping{kind}.check data.toData.kind data.toData.relation {kind} = true := by",
                             "  decide +kernel")
                self.add("")
                continue
            if enumerate_kinds:
                self.add(f"def kind{kind} : List (Fin data.count) :=",
                         f"  (List.finRange data.count).filter fun c => decide (data.toData.kind c = {kind})",
                         f"theorem kind{kind}_checked :",
                         f"    FacetSat.Boundary.kindListCheck data.toData.kind {kind} kind{kind} = true :=",
                         "  FacetSat.RawProjection.kindListCheck_enumerated _ _", "")
            else:
                self.add(f"def kind{kind} : List (Fin data.count) := {fin_list(self.kind_lists[kind])}",
                         f"theorem kind{kind}_checked :",
                         f"    FacetSat.Boundary.kindListCheck data.toData.kind {kind} kind{kind} = true := by",
                         "  decide +kernel", "")
        for vertices, name in self.groups.items():
            if self.vertices(list(vertices)) == name:
                self.add(f"def {name} : List (Fin data.count) := {fin_list(list(vertices))}")
        for (kind, vertices), name in self.counter_groups.items():
            if self.vertices(list(vertices), grouped=True, kind=kind) == name:
                self.add(f"def {name} : List Nat := {list(vertices)}")
        if self.groups or self.counter_groups:
            self.add("")
        self.add("theorem ridge_matrix_checked :",
                 "    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=")
        if self.raw and self.raw_metadata:
            self.add(f"  FacetSat.RawProjection.ridge_matrix {self.record} vertexColumn kindColumn",
                     f"    {self.record}_matrix_checked", "")
        else:
            self.add("  by decide +kernel", "")
        if self.coverage:
            self.add(f"def leafCount : Nat := {len(self.orbits)}")
            if self.raw:
                self.add(f"def kindKeys : List Nat := {sorted({c['kind'] for c in self.cells})}",
                         "theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by",
                         "  decide +kernel")
            for index, orbit in enumerate(self.orbits):
                self.add(f"def leaf{index:04d} : List (Fin data.count) := {fin_list(orbit['vertices'])}")
                if self.raw:
                    self.add(f"theorem leaf{index:04d}_counts_checked :",
                             f"    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf{index:04d} = true := by",
                             "  decide +kernel",
                             f"theorem leaf{index:04d}_checked :",
                             f"    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf{index:04d} = true :=",
                             f"  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf{index:04d}_counts_checked")
                else:
                    self.add(f"theorem leaf{index:04d}_checked :",
                             f"    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf{index:04d} = true := by",
                             "  decide +kernel")
            if self.orbits:
                self.add("def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=",
                         table([f"leaf{i:04d}" for i in range(len(self.orbits))]),
                         "def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val", "")
            else:
                self.add("def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j", "")

    def model(self) -> None:
        if self.direct_expr:
            atoms = []
            for original in self.core["atoms"]:
                atom = original.copy()
                if atom["tag"] in ("totalizer", "group_totalizer"):
                    atom["list_name"] = self.vertices(atom.pop("vertices"),
                        grouped=atom["tag"] == "group_totalizer", kind=atom.get("kind"))
                atoms.append(atom)
            manifest = json.dumps({"atoms": atoms}, separators=(",", ":"))
            self.add(f"facet_model% {lean_string(self.namespace)} {lean_string(manifest)}",
                     f"facet_atoms% {lean_string(self.namespace)} {len(atoms)}", "")
            return
        expressions = ["False"]
        for atom in self.core["atoms"]:
            if atom["tag"] == "facet":
                expressions.append(f"{fin(atom['index'])} ∈ S")
            elif atom["tag"] == "counter":
                expressions.append("SequentialCounter.reached (fun c => c ∈ S) "
                                   f"(kind{atom['kind']}.take {atom['prefix']}) {atom['threshold']}")
            elif atom["tag"] == "totalizer":
                expressions.append("SequentialCounter.reached (fun c => c ∈ S) "
                                   f"{self.vertices(atom['vertices'])} {atom['threshold']}")
            elif atom["tag"] == "group":
                expressions.append(f"grouping{atom['kind']}.selected S {atom['index']}")
            elif atom["tag"] == "group_totalizer":
                expressions.append(f"SequentialCounter.reached (grouping{atom['kind']}.selected S) "
                    f"{self.vertices(atom['vertices'], grouped=True, kind=atom['kind'])} {atom['threshold']}")
            else:
                raise ValueError(f"unknown SAT atom: {atom!r}")
        self.atom_expressions = expressions
        # Keep the table closed.  Selecting a leaf before applying S avoids
        # substituting a fresh boundary through every atom at each lookup.
        self.add("def modelTable : ConcreteGrowth.Table (List (Fin data.count) → Prop) :=",
                 table([f"fun S => {expression}" for expression in expressions]), "",
                 "def model (S : List (Fin data.count)) (atomIndex : Nat) : Prop :=",
                 "  (modelTable.get atomIndex) S", "")
        if not self.direct_expr:
            for index, expression in enumerate(expressions[1:], start=1):
                self.add(f"theorem atom{index:05d}_eq (S : List (Fin data.count)) :",
                         f"    model S {index} = ({expression}) := rfl")
            self.add("")
        else:
            self.add(f"facet_atoms% {lean_string(self.namespace)} {len(self.core['atoms'])}", "")

    def facts(self) -> None:
        ridges = set()
        for rule in self.core["rules"]:
            if rule["tag"] == "mate":
                ridges.add((rule["a"], rule["ridge"]))
            elif rule["tag"] == "three":
                ridges.update((a, rule["ridge"]) for a in rule["vertices"])
        if not self.direct_expr:
            for a, q in sorted(ridges):
                self.add(f"theorem ridge_{a}_{q} : data.ridges {fin(a)} {fin(q, '1024')} = true :=",
                         f"  (data.ridgeRows_exact ridge_matrix_checked {fin(q, '1024')} {fin(a)}).symm.trans",
                         "    (by decide +kernel)")
        if ridges and not self.direct_expr:
            self.add("")
        owner_pairs = []
        for rule in self.core["rules"]:
            if rule["tag"] != "mate":
                continue
            a, q, owners = rule["a"], rule["ridge"], rule["owners"]
            dropped = [i for i, cell in enumerate(self.cells)
                       if q in cell["ridges"] and i != a and i not in owners]
            if not self.direct_expr:
                self.add(f"def owners_{a}_{q} : List (Fin data.count) := {fin_list(owners)}",
                         f"def dropped_{a}_{q} : List (Fin data.count) := {fin_list(dropped)}")
                self.add(f"theorem owners_{a}_{q}_checked :",
                         "    FacetSat.Boundary.packedOwnersCheck data.toData.relation",
                         f"      (data.ridgeRows {fin(q, '1024')}) {fin(a)} owners_{a}_{q} dropped_{a}_{q} = true := by",
                         "  decide +kernel")
                self.add("")
            owner_pairs.append((a, q, owners, dropped))
        edge_pairs = [(rule["edge"], rule["owners"]) for rule in self.core["rules"] if rule["tag"] == "edge"]
        if not self.direct_expr:
            for edge, owners in edge_pairs:
                self.add(f"def edgeOwners_{edge} : List (Fin data.count) := {fin_list(owners)}",
                         f"theorem edge_{edge}_required : requiredEdges.testBit (edgeIndex {edge}).val = true := by",
                         "  decide +kernel",
                         f"theorem edge_{edge}_owners_checked :",
                         f"    FacetSat.EdgeCover.ownersCheck (edgeRows (edgeIndex {edge})) edgeOwners_{edge} = true := by",
                         "  decide +kernel")
        if self.direct_expr:
            facts = json.dumps({"ridges": sorted(ridges), "owners": owner_pairs, "edges": edge_pairs,
                                "groupings": sorted({r["kind"] for r in self.core["rules"]
                                                     if r.get("grouped")})}, separators=(",", ":"))
            self.add("facet_facts% " + lean_string(self.namespace) + " " + lean_string(facts), "")

    def initial(self, number: int, clause: list[int], rule: dict) -> None:
        names = {lit: f"h{i}" for i, lit in enumerate(clause)}
        if len(names) != len(clause):
            raise ValueError("an emitted clause contains duplicate literals")
        self.add(f"private theorem initial{number:05d} {self.context()} :",
                 f"    {clause_type(clause)} := by")
        if clause:
            self.add("  intro " + " ".join(names[lit] for lit in clause))
        # Each opaque equality selects one semantic atom once.  Its uses do
        # not reopen the balanced table while checking every initial clause.
        for index, literal in enumerate(clause):
            expression = self.atom_expressions[abs(literal)]
            old = names[literal]
            new = f"a{index}"
            equality = f"(atom{abs(literal):05d}_eq S)"
            if literal > 0:
                self.add(f"  have {new} : ({expression}) → False :=",
                         f"    fun h => {old} (Eq.mpr {equality} h)")
            else:
                self.add(f"  have {new} : {expression} := Eq.mp {equality} {old}")
            names[literal] = new
        tag = rule["tag"]
        if tag == "incompatible":
            a, b = rule["a"], rule["b"]
            self.add(f"  exact H.incompatible {fin(a)} {fin(b)} (by decide) (by decide +kernel) "
                     + " ".join(names[lit] for lit in clause))
        elif tag == "three":
            a, b, c = rule["vertices"]; q = rule["ridge"]
            self.add(f"  exact H.three {fin(q, '1024')} {fin(a)} {fin(b)} {fin(c)}",
                     "    (by decide) (by decide) (by decide)",
                     f"    ridge_{a}_{q} ridge_{b}_{q} ridge_{c}_{q} "
                     + " ".join(names[lit] for lit in clause))
        elif tag == "mate":
            a, q, owners = rule["a"], rule["ridge"], rule["owners"]
            # Each positive owner literal has its falsity as a clause hypothesis.
            selected = "(fun c : Fin data.count => c ∈ S)"
            all_false = f"(FacetSat.not_mem_nil {selected})"
            for offset in range(len(owners) - 1, -1, -1):
                owner = owners[offset]
                proof = names[clause[offset + 1]]
                all_false = (f"(FacetSat.not_mem_cons {selected} {fin(owner)} "
                             f"{fin_list(owners[offset + 1:])} {proof} {all_false})")
            self.add("  exact H.packed_mate data.ridgeRows",
                     "    (data.ridgeRows_exact ridge_matrix_checked)",
                     f"    {fin(q, '1024')} {fin(a)} owners_{a}_{q} dropped_{a}_{q}",
                     f"    ridge_{a}_{q} owners_{a}_{q}_checked {names[clause[0]]} {all_false}")
        elif tag == "counter":
            k, pos, threshold, gate = (rule[key] for key in ("kind", "position", "threshold", "gate"))
            selected = "(fun c : Fin data.count => c ∈ S)"
            arguments = []
            for index, literal in enumerate(rule["full_literals"]):
                if literal is True:
                    raise ValueError("a tautological counter clause survived trimming")
                if literal is not False:
                    arguments.append(names[literal]); continue
                if gate == "take" and index == 1 and threshold == 1:
                    arguments.append(f"(SequentialCounter.reached_zero {selected} (kind{k}.take {pos}))")
                elif gate in ("previous_or_selected", "previous_or_lower") and pos == 0 and index in (1, 2):
                    bound = threshold if index == 1 else threshold - 1
                    if bound <= 0:
                        raise ValueError("invalid false empty-prefix atom")
                    arguments.append(f"(SequentialCounter.not_reached_empty {selected} {bound} (by decide))")
                else:
                    raise ValueError(f"unsupported reduced counter literal: {rule!r}")
            self.add(f"  exact SequentialCounter.prefix_{gate} {selected} kind{k} {pos} {threshold}",
                     "    (by decide) (by decide) " + " ".join(arguments))
        elif tag == "edge":
            edge, owners = rule["edge"], rule["owners"]
            selected = "(fun c : Fin data.count => c ∈ S)"
            all_false = f"(FacetSat.not_mem_nil {selected})"
            for offset in range(len(owners) - 1, -1, -1):
                all_false = (f"(FacetSat.not_mem_cons {selected} {fin(owners[offset])} "
                             f"{fin_list(owners[offset + 1:])} {names[clause[offset]]} {all_false})")
            self.add(f"  exact FacetSat.EdgeCover.clause edgeCover (edgeIndex {edge}) edgeOwners_{edge}",
                     f"    edge_{edge}_required edge_{edge}_owners_checked {all_false}")
        elif tag == "group_take":
            k, g, c = rule["kind"], rule["index"], rule["member"]
            self.add(f"  exact FacetSat.Grouping.group_take grouping{k} S {g} {fin(c)} (by decide) "
                     + " ".join(names[lit] for lit in clause))
        elif tag == "group_or":
            k, g, members = rule["kind"], rule["index"], rule["members"]
            selected = "(fun c : Fin data.count => c ∈ S)"
            all_false = f"(FacetSat.not_mem_nil {selected})"
            for offset in range(len(members) - 1, -1, -1):
                all_false = (f"(FacetSat.not_mem_cons {selected} {fin(members[offset])} "
                             f"{fin_list(members[offset + 1:])} {names[clause[offset + 1]]} {all_false})")
            self.add(f"  exact FacetSat.Grouping.group_or grouping{k} S {g} {names[clause[0]]} {all_false}")
        elif tag == "merge":
            left, right, a, b = (rule[key] for key in ("left", "right", "a", "b"))
            grouped = bool(rule.get("grouped"))
            selected = f"(grouping{rule['kind']}.selected S)" if grouped else "(fun c : Fin data.count => c ∈ S)"
            vertices_name = lambda values: self.vertices(values, grouped=grouped, kind=rule.get("kind"))
            def reached_argument(vertices, threshold, literal, negative=False):
                if literal is True:
                    raise ValueError("a tautological totalizer clause survived trimming")
                if literal is False:
                    if negative:
                        return (f"(SequentialCounter.not_reached_above_length {selected} "
                                f"{vertices_name(vertices)} {threshold} (by decide))")
                    if threshold != 0:
                        raise ValueError("a nonzero totalizer threshold was replaced by true")
                    return f"(SequentialCounter.reached_zero {selected} {vertices_name(vertices)})"
                atom = self.core["atoms"][abs(literal) - 1]
                hypothesis = names[literal]
                if atom["tag"] in ("facet", "group"):
                    if len(vertices) != 1 or atom["index"] != vertices[0] or threshold != 1:
                        raise ValueError("a totalizer leaf does not match its selected atom")
                    if grouped != (atom["tag"] == "group"):
                        raise ValueError("a totalizer leaf has the wrong index type")
                    vertex = str(vertices[0]) if grouped else fin(vertices[0])
                    if negative:
                        return f"(fun hx => {hypothesis} (SequentialCounter.leaf_upper {selected} {vertex} hx))"
                    return f"(SequentialCounter.leaf_lower {selected} {vertex} {hypothesis})"
                return hypothesis
            literals = rule["full_literals"]
            if rule["direction"] == "forward":
                arguments = [reached_argument(left, a, literals[0]),
                             reached_argument(right, b, literals[1]),
                             reached_argument(left + right, a + b, literals[2], True)]
            elif rule["direction"] == "backward":
                arguments = [reached_argument(left + right, a + b + 1, literals[0]),
                             reached_argument(left, a + 1, literals[1], True),
                             reached_argument(right, b + 1, literals[2], True)]
            else:
                raise ValueError("unknown totalizer merge direction")
            self.add(f"  exact SequentialCounter.merge_{rule['direction']} {selected} "
                     f"{vertices_name(left)} {vertices_name(right)} {a} {b}",
                     "    " + " ".join(arguments))
        elif tag in ("quota_lower", "quota_upper"):
            k, quota = rule["kind"], rule["quota"]
            grouped = bool(rule.get("grouped"))
            selected = f"(grouping{k}.selected S)" if grouped else "(fun c : Fin data.count => c ∈ S)"
            vertices_name = f"groupKind{k}" if grouped else f"kind{k}"
            count = (f"(H.group_count grouping{k} {k} grouping{k}_checked)" if grouped else
                     f"(H.quota_count {k} kind{k} kind{k}_checked)")
            if self.lower:
                if tag != "quota_lower":
                    raise ValueError("an upper quota clause occurred in a lower-only certificate")
                bound = f"(Nat.le_trans (hbudget {k}) (Nat.le_of_eq {count}.symm))"
                fn = f"SequentialCounter.quota_lower_of_le {selected} {vertices_name} {quota} {bound}"
            else:
                fn = f"SequentialCounter.{tag} {selected} {vertices_name} {quota} {count}"
            if clause:
                arguments = []
                for literal in clause:
                    atom = self.core["atoms"][abs(literal) - 1]
                    argument = names[literal]
                    if atom["tag"] in ("facet", "group"):
                        if grouped != (atom["tag"] == "group"):
                            raise ValueError("a singleton quota has the wrong selected index type")
                        vertex = str(atom["index"]) if grouped else fin(atom["index"])
                        if tag == "quota_lower":
                            argument = f"(fun hx => {argument} (SequentialCounter.leaf_upper {selected} {vertex} hx))"
                        else:
                            argument = f"(SequentialCounter.leaf_lower {selected} {vertex} {argument})"
                    arguments.append(argument)
                self.add("  exact " + fn + " " + " ".join(arguments))
            elif tag == "quota_lower" and quota > (self.groupings[k]["count"] if grouped else len(self.kind_lists[k])):
                self.add("  exact " + fn + f" (SequentialCounter.not_reached_above_length {selected} {vertices_name} {quota} (by decide))")
            else:
                raise ValueError("unsupported empty quota clause")
        elif tag == "block":
            index, vertices = rule["leaf"], rule["vertices"]
            selected = "(fun c : Fin data.count => c ∈ S)"
            all_selected = f"(FacetSat.all_mem_nil {selected})"
            for offset in range(len(vertices) - 1, -1, -1):
                all_selected = (f"(FacetSat.all_mem_cons {selected} {fin(vertices[offset])} "
                                f"{fin_list(vertices[offset + 1:])} {names[clause[offset]]} {all_selected})")
            self.add(f"  exact H.block_leaf_checked leaf{index:04d} leaf{index:04d}_checked",
                     f"    (noSame (⟨{index}, by decide⟩ : Fin leafCount)) {all_selected}")
        else:
            raise ValueError(f"unknown initial-clause rule: {tag}")
        self.add("")

    def refutation(self) -> None:
        self.add(f"theorem boundary_unsat {self.context()} : False :=",
                 "  rup_proof% (model S) #[")
        arguments = self.arguments()
        self.add(",\n".join(f"    initial{i:05d} {arguments}"
                            for i in range(1, len(self.core["clauses"]) + 1)))
        self.add("  ] " + lean_string(self.core["cnf"]), "    " + lean_string(self.core["lrat"]), "")

    def raw_coverage(self) -> None:
        record = self.record
        self.add("theorem local_coverage",
                 f"    (valid : GraphGrowthInputs.Valid {record}.inputs)",
                 f"    (matrix : MatrixGraphProblem.Checked {record}.data)",
                 f"    (B : List (Fin {record}.n))",
                 f"    (H : GraphGrowthConstraints.Target ({record}.inputs.problem valid) B) :",
                 "    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))",
                 "      (SparseGrowthDAG.family B) := by",
                 f"  apply FacetSat.RawProjection.{'coverage_with_edges' if self.edge_cover else 'coverage'} {record} valid matrix",
                 "    vertexColumn kindColumn projection_checked leaves _ B H",
                 "  intro S HS" + (" edgeCover" if self.edge_cover else "") + " noSame")
        edges_arg = " edgeCover" if self.edge_cover else ""
        if self.lower:
            self.add("  exact boundary_unsat S requirements HS (fun _ => Nat.le_refl _)" + edges_arg + " noSame")
        else:
            self.add("  exact boundary_unsat S HS" + edges_arg + " noSame")
        if self.diagnostics:
            self.add("", "#print axioms local_coverage", "")
        if not self.full_result:
            return
        if self.orbits:
            self.add(f"def originalLeafTable : ConcreteGrowth.Table (Fin {record}.l) :=",
                     table([f"⟨{o['original_leaf']}, by decide⟩" for o in self.orbits]),
                     f"def originalLeaf (j : Fin leafCount) : Fin {record}.l := originalLeafTable.get j.val",
                     f"def orbitWordTable : ConcreteGrowth.Table (List (Fin {record}.g)) :=",
                     table(["[" + ", ".join(f"⟨{v}, by decide⟩" for v in o["word"]) + "]"
                            for o in self.orbits]),
                     f"def orbitWord (j : Fin leafCount) : List (Fin {record}.g) := orbitWordTable.get j.val")
        else:
            self.add(f"def originalLeaf (j : Fin leafCount) : Fin {record}.l := Fin.elim0 j",
                     f"def orbitWord (j : Fin leafCount) : List (Fin {record}.g) := Fin.elim0 j")
        self.add("theorem orbit_words_checked : ∀ j : Fin leafCount,",
                 f"    SparseGrowthDAG.sameCheck ({record}.leaf (originalLeaf j))",
                 f"      (GraphCaseCertificate.rawApplyWord {record}.maps (orbitWord j) (leaves j)) = true := by",
                 "  decide +kernel", "",
                 f"theorem direct_core : GraphCaseCertificate.DirectCore {record} where",
                 f"  matrix := {record}_matrix_checked",
                 f"  valid := {record}_validity",
                 f"  literal := {record}_literal",
                 "  leaf_nodup := by decide +kernel",
                 f"  frames := {record}_frames_supported {record}_cells_exact",
                 f"  leaves_checked := ⟨{record}_certificates, {record}_leaf_certificates_checked⟩",
                 f"  complete := GraphCaseCertificate.complete_of_orbits {record} {record}_validity",
                 "    leaves originalLeaf orbitWord orbit_words_checked",
                 f"    (local_coverage {record}_validity {record}_matrix_checked)", "")
        if self.diagnostics:
            self.add("#print axioms direct_core", "")

    def emit(self) -> str:
        self.add("module", "prelude", "public import FacetSatRaw" if self.raw else "public import FacetSat")
        if self.groupings:
            self.add("public import FacetSatGroups")
        if self.edge_cover:
            self.add("public import FacetSatEdges")
        if self.coverage and not self.raw:
            self.add("public import FacetSatCoverage")
        if self.raw:
            part = self.record.split(".")[-2]
            self.add("public import " + (self.raw_import or part + ("Metadata" if self.raw_metadata else "Data")))
            if self.full_result:
                self.add("public import GraphDirectCore", "public import " + part + "Frames",
                         "public import " + part + "Leaves")
        self.add("public meta import SparseNatLiteral", "public meta import RupProofTerm", "",
                 *( ["public meta import FacetSatFacts", "public meta import FacetSatInitials", ""] if self.direct_expr else [] ),
                 "@[expose] public section", "set_option maxHeartbeats 0", "set_option maxRecDepth 100000",
                 "set_option maxErrors 5", "set_option autoImplicit false",
                 "set_option linter.unusedVariables false",
                 f"namespace {self.namespace}", "open Papers.RationalityTen", "")
        self.data(); self.model(); self.facts()
        if len(self.core["clauses"]) != len(self.core["rules"]):
            raise ValueError("one typed rule is required for every initial clause")
        if self.direct_expr:
            manifest = json.dumps(compact_initial_manifest(self.case, self.namespace, raw_record=self.raw), separators=(",", ":"))
            self.add("facet_refute% " + lean_string(self.namespace) + " " + lean_string(manifest),
                     "  " + lean_string(self.core["cnf"]), "  " + lean_string(self.core["lrat"]), "")
        else:
            for index, (clause, rule) in enumerate(zip(self.core["clauses"], self.core["rules"]), start=1):
                self.initial(index, clause, rule)
            self.refutation()
        if self.raw:
            self.raw_coverage()
        elif self.diagnostics:
            self.add("#print axioms boundary_unsat")
        self.add("", f"end {self.namespace}", "")
        return "\n".join(self.lines)


def emit_case(case: dict, namespace: str = "Papers.RationalityTen.FacetSATGenerated.Pilot", *,
              full_result: bool = False, raw_record: bool = False,
              raw_metadata: bool = True, raw_import: str | None = None,
              direct_expr: bool = False, diagnostics: bool = False) -> str:
    return Emitter(case, namespace, full_result, raw_record=raw_record,
                   raw_metadata=raw_metadata, raw_import=raw_import,
                   direct_expr=direct_expr, diagnostics=diagnostics).emit()


def initial_manifest(case: dict, namespace: str = "Papers.RationalityTen.FacetSATGenerated.Pilot", *,
                     raw_record: bool = False) -> dict:
    """Names and typed rules consumed by the untrusted Expr proof producer."""
    emitter = Emitter(case, namespace, False, raw_record=raw_record)
    rules = []
    for original in case["core"]["rules"]:
        rule = original.copy()
        if rule["tag"] == "merge":
            opts = {"grouped": bool(rule.get("grouped")), "kind": rule.get("kind")}
            rule["left_name"] = emitter.vertices(rule["left"], **opts)
            rule["right_name"] = emitter.vertices(rule["right"], **opts)
            rule["joined_name"] = emitter.vertices(rule["left"] + rule["right"], **opts)
        rules.append(rule)
    return {"namespace": namespace, "lower_only": emitter.lower,
            "coverage": emitter.coverage, "edge_cover": emitter.edge_cover, "leaf_count": len(emitter.orbits),
            "orbits": emitter.orbits,
            "count": len(emitter.cells), "quota": case["quota"],
            "atoms": emitter.core["atoms"], "clauses": emitter.core["clauses"],
            "rules": rules,
            "kindlists": {str(k): v for k, v in emitter.kind_lists.items()},
            "groups": [{"vertices": list(vertices), "name": emitter.vertices(list(vertices))}
                       for vertices in emitter.groups]}


def compact_initial_manifest(case: dict, namespace: str, *, raw_record: bool = False) -> dict:
    """Keep only inputs read by the kernel-checkable proof producer."""
    manifest = initial_manifest(case, namespace, raw_record=raw_record)
    keys = {"incompatible": ("a", "b"), "mate": ("ridge", "a", "owners"),
            "three": ("ridge", "vertices"),
            "counter": ("kind", "position", "threshold", "gate", "full_literals"),
            "merge": ("left", "right", "left_name", "right_name", "joined_name",
                      "a", "b", "direction", "full_literals"),
            "quota_lower": ("kind", "quota"), "quota_upper": ("kind", "quota"),
            "block": ("leaf", "vertices"), "edge": ("edge", "owners"),
            "group_or": ("kind", "index", "members", "full_literals"),
            "group_take": ("kind", "index", "member", "full_literals")}
    return {"namespace": namespace, "lower_only": manifest["lower_only"],
            "coverage": manifest["coverage"], "edge_cover": manifest["edge_cover"], "clauses": manifest["clauses"],
            "atoms": [{"tag": atom["tag"],
                       **({"index": atom["index"]} if atom["tag"] in ("facet", "group") else {}),
                       **({"kind": atom["kind"]} if atom["tag"] in ("group", "group_totalizer") else {})}
                      for atom in manifest["atoms"]],
            "rules": [{"tag": rule["tag"], **{key: rule[key] for key in keys[rule["tag"]]},
                       **({"grouped": True, "kind": rule["kind"]} if rule.get("grouped") else {})}
                      for rule in manifest["rules"]]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Papers.RationalityTen.FacetSATGenerated.Pilot")
    parser.add_argument("--full-result", action="store_true")
    parser.add_argument("--raw-record", action="store_true")
    parser.add_argument("--raw-import")
    parser.add_argument("--no-raw-metadata", action="store_true")
    parser.add_argument("--direct-expr", action="store_true")
    parser.add_argument("--diagnostics", action="store_true")
    args = parser.parse_args()
    source = emit_case(json.loads(args.input.read_text()), args.namespace, full_result=args.full_result,
                       raw_record=args.raw_record, raw_metadata=not args.no_raw_metadata,
                       raw_import=args.raw_import, direct_expr=args.direct_expr,
                       diagnostics=args.diagnostics)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source)
    print(json.dumps({"output": str(args.output), "bytes": len(source.encode()),
                      "full_result": args.full_result}))


if __name__ == "__main__":
    main()
