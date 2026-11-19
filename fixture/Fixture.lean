module
public import Lean
@[expose] public section
open Lean Elab Command Meta
/-- Record the complete literal kernel body of a visible safe definition as an equality.
Both sides are kernel checked. The right side is the actual lambda/body expression,
not a second reference to the definition; comparing this equation fixes its full value. -/
elab "literal_value " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some (.defnInfo d) := (← getEnv).find? name
    | throwError "literal_value requires a definition"
  unless d.safety == .safe do throwError "literal_value requires safe definitions"
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "literal_value requires kernel type checking"
  let lhs := mkConst name (d.levelParams.map Level.param)
  let eqType ← liftTermElabM <| mkEq lhs d.value
  let proof ← liftTermElabM <| mkEqRefl lhs
  let newName := name.appendAfter "_literal_value"
  liftCoreM <| addDecl (.thmDecl {
    name := newName, levelParams := d.levelParams, type := eqType, value := proof })
  addDocStringCore newName "Complete value equation for the literal definition above."
namespace Fixture
/-- A universe-polymorphic literal identity. -/
def identity {α : Sort u} (x : α) : α := x
literal_value identity
/-- A type-valued literal carrier. -/
def carrier (n : Nat) : Type := Fin (n+1)
literal_value carrier
/-- A proposition-valued literal predicate. -/
def positive (n : Nat) : Prop := 0 < n
literal_value positive
#print identity_literal_value
#print carrier_literal_value
#print positive_literal_value
#print axioms identity_literal_value
#print axioms carrier_literal_value
#print axioms positive_literal_value
run_cmd do
  let env ← getEnv
  for name in [`Fixture.identity, `Fixture.carrier, `Fixture.positive] do
    let some (.defnInfo d) := env.find? name | throwError "missing fixture definition"
    let some (.thmInfo t) := env.find? (name.appendAfter "_literal_value")
      | throwError "missing complete value equation"
    let lhs := mkConst name (d.levelParams.map Level.param)
    let selfEq ← liftTermElabM <| mkEq lhs lhs
    if t.type == selfEq then throwError "tautological name-only equation is not a literal constraint"
    let expected ← liftTermElabM <| mkEq lhs d.value
    unless t.type == expected do throwError "literal body did not survive into theorem type"
  logInfo "COMPLETE_LITERAL_VALUE_EQUATION_FIXTURE_PASS"
end Fixture
