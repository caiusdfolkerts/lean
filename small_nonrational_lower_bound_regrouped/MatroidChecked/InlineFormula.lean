module
public import Mathlib.Tactic.Sat.FromLRAT
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

/-!
# Exact data inlining for public CNF interfaces

The elaborator below returns only a definition of the data type `Sat.Fmla`.
It reads the private implementation only while constructing data; the returned
expression is subsequently checked in the caller's ordinary public environment.
It expands project definitions, never opaque theorems, using Lean's ordinary
`deltaExpand` operation. The resulting exposed definition and the subsequent
application of the original refutation are both checked by the kernel.

Keeping the original expression tree avoids rebuilding a large clause list
through numeral notation or arithmetic decoders. No proposition is asserted
by this elaborator, and it supplies no proof or axiom.
-/

public meta section
open Lean Elab Term Meta

elab "inline_cnf% " identifier:ident : term => withExporting (isExporting := false) do
  let name ← realizeGlobalConstNoOverloadWithInfo identifier
  let declaration ← getConstInfoDefn name
  unless declaration.levelParams.isEmpty do
    throwError "CNF data must be monomorphic"
  unless ← isDefEq declaration.type (mkConst ``Sat.Fmla) do
    throwError "Expected a definition of Sat.Fmla"
  return ← deltaExpand (mkConst name) fun n =>
    let text := n.toString
    text.startsWith "Papers." || text.startsWith "PureInputSemantics." ||
      text.startsWith "PureRup." || text.startsWith "PureClauseSemantics." ||
      text.startsWith "_private."
