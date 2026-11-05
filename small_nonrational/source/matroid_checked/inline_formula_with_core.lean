module
public import Mathlib.Tactic.Sat.FromLRAT
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

/-!
# Inlining input data while retaining its public generic semantics

Init-backed refutations use the proved generic conversion
`PureClauseSemantics.Formula.toSat`. Its definition is public, so the exposed
formula can retain that function and expand only its input-specific aliases.
Keeping this common function head avoids repeatedly normalizing a large map
during the final definitional-equality check.

This elaborator constructs only data. The resulting definition and the original
refutation application are checked by the ordinary Lean kernel. The default
`allowOpaque := false` of `deltaExpand` excludes theorem proof bodies.
-/

public meta section
open Lean Elab Term Meta

elab "inline_cnf_with_core% " identifier:ident : term =>
    withExporting (isExporting := false) do
  let name ← realizeGlobalConstNoOverloadWithInfo identifier
  let declaration ← getConstInfoDefn name
  unless declaration.levelParams.isEmpty do
    throwError "CNF data must be monomorphic"
  unless ← isDefEq declaration.type (mkConst ``Sat.Fmla) do
    throwError "Expected a definition of Sat.Fmla"
  return ← deltaExpand (mkConst name) fun n =>
    let text := n.toString
    !text.startsWith "Papers.RationalityTen.PureClauseSemantics." &&
      (text.startsWith "Papers." || text.startsWith "PureInputSemantics." ||
        text.startsWith "PureRup." || text.startsWith "PureClauseSemantics." ||
        text.startsWith "_private.")
