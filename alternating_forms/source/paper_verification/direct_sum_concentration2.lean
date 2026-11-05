module

public import Mathlib.Algebra.DirectSum.Module
import all Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Basic
import all Mathlib.RingTheory.Finiteness.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.DirectSumConcentration -/

/-!
# Genuine direct sums concentrated in one degree

The inclusion from the only possible nonzero summand is a surjective linear
map. Consequently a finite relative group in that degree gives a finite
total direct sum, with the same rank bound. This uses the ordinary algebraic
direct sum over every degree, without a truncation or a degree bound.
-/

namespace PaperVerification.DirectSumConcentration

noncomputable section

open scoped DirectSum

variable {K ι : Type*} [Field K] [DecidableEq ι]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

theorem inclusion_surjective (d : ι)
    (hzero : ∀ i, i ≠ d → Subsingleton (V i)) :
    Function.Surjective (DirectSum.lof K ι V d) := by
  classical
  intro x
  refine ⟨x d, ?_⟩
  ext i
  by_cases hi : i = d
  · subst i
    change (DFinsupp.single d (x d)) d = x d
    exact DFinsupp.single_eq_same
  · letI := hzero i hi
    exact Subsingleton.elim _ _

/-- This equivalence is induced by the actual inclusion of the single
nonzero summand. -/
def equivalence (d : ι) (hzero : ∀ i, i ≠ d → Subsingleton (V i)) :
    V d ≃ₗ[K] ⨁ i, V i := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.lof K ι V d)
    ⟨DirectSum.of_injective (β := V) d, inclusion_surjective (K := K) V d hzero⟩

theorem finite_and_finrank_le (d : ι)
    (hzero : ∀ i, i ≠ d → Subsingleton (V i))
    [Module.Finite K (V d)] (b : ℕ) (hbound : Module.finrank K (V d) ≤ b) :
    Module.Finite K (⨁ i, V i) ∧ Module.finrank K (⨁ i, V i) ≤ b := by
  let e := equivalence (K := K) V d hzero
  exact ⟨Module.Finite.equiv e, by simpa only [← e.finrank_eq] using hbound⟩

/-- Degreewise exact maps remain exact on the genuine direct sums over
all degrees. -/
theorem range_eq_ker {A B C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (f : ∀ i, A i →ₗ[K] B i) (g : ∀ i, B i →ₗ[K] C i)
    (hexact : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i)) :
    LinearMap.range (DirectSum.lmap f) = LinearMap.ker (DirectSum.lmap g) := by
  simp only [DirectSum.range_lmap, DirectSum.ker_lmap, hexact]

end
end PaperVerification.DirectSumConcentration
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.DirectSumConcentration"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.DirectSumConcentration.finite_and_finrank_le, "theorem"),
    (`PaperVerification.DirectSumConcentration.range_eq_ker, "theorem"),
    (`PaperVerification.DirectSumConcentration.equivalence, "definition")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "bef2319cd27c820e4ee245fbe93f281f"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:bef2319cd27c820e4ee245fbe93f281f"
