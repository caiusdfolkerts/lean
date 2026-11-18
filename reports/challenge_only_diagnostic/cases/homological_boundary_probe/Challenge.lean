module
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public meta import Lean.Elab.Command
public meta import Lean.Data.Json
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CommAlg.Simplicial
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
end CommAlg.Simplicial

-- Three direct environment lookups only. No whole-environment enumeration,
-- dependency traversal, proof/value expansion, project import or source build.
run_cmd do
  let env ← Lean.getEnv
  for name in [`CommAlg.Simplicial.boundary._proof_1,
      `CommAlg.Simplicial.boundary._proof_2,
      `CommAlg.Simplicial.boundary._proof_3] do
    match env.find? name with
    | none =>
      let row := Lean.Json.mkObj [
        ("kind", Lean.toJson "BOUNDARY_AUXILIARY_TYPE"),
        ("name", Lean.toJson name.toString), ("found", Lean.toJson false)]
      Lean.logInfo m!"{row.compress}"
    | some ci =>
      let text := reprStr ci.type
      let row := Lean.Json.mkObj [
        ("kind", Lean.toJson "BOUNDARY_AUXILIARY_TYPE"),
        ("name", Lean.toJson name.toString), ("found", Lean.toJson true),
        ("level_params", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
        ("type_characters", Lean.toJson text.length),
        ("type_text_limit", Lean.toJson (8000 : Nat)),
        ("type_truncated", Lean.toJson (decide (8000 < text.length))),
        ("type_ast", Lean.toJson (String.ofList (text.toList.take 8000)))]
      Lean.logInfo m!"{row.compress}"
