module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Basic
public import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.DirectSumShift -/


/-!
# A genuine all-degree shift of a graded vector space

Removing an initial segment of zero groups preserves the actual direct sum.
The map is restriction of finitely supported functions, and its inverse is
extension by zero. This is the all-degree form of the Thom degree shift.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DirectSumShift

open scoped DirectSum

variable {K : Type*} [Field K] (V : ℕ → Type*)
  [∀ n, AddCommGroup (V n)] [∀ n, Module K (V n)]

/-- Restrict the actual finitely supported family to degrees at least `d`. -/
def restriction (d : ℕ) : (⨁ n : ℕ, V n) →ₗ[K] ⨁ n : ℕ, V (d+n) where
  toFun := DFinsupp.comapDomain (fun n => d+n) (fun _ _ h => Nat.add_left_cancel h)
  map_add' := DFinsupp.comapDomain_add _ _
  map_smul' := DFinsupp.comapDomain_smul _ _

@[simp] theorem restriction_apply (d : ℕ) (x : ⨁ n : ℕ, V n) (n : ℕ) :
    restriction (K := K) V d x n = x (d+n) := rfl

/-- Every shifted finitely supported family extends by zero. -/
theorem restriction_surjective (d : ℕ) : Function.Surjective (restriction (K := K) V d) := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0,map_zero _⟩
  | add x y hx hy =>
      obtain ⟨a,rfl⟩ := hx
      obtain ⟨b,rfl⟩ := hy
      exact ⟨a+b,map_add _ _ _⟩
  | of n x =>
      refine ⟨DirectSum.of V (d+n) x,?_⟩
      exact DFinsupp.comapDomain_single (fun n => d+n) (fun _ _ h => Nat.add_left_cancel h) n x

/-- Restriction loses nothing when precisely the discarded groups vanish. -/
theorem restriction_injective (d : ℕ)
    (hz : ∀ n < d, Subsingleton (V n)) :
    Function.Injective (restriction (K := K) V d) := by
  intro x y h
  ext n
  by_cases hn : n < d
  · letI := hz n hn
    exact Subsingleton.elim _ _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show d ≤ n from by omega)
    exact congrArg (fun z => z m) h

/-- The full direct sum is isomorphic to its genuine degree shift. -/
def equivalence (d : ℕ) (hz : ∀ n < d, Subsingleton (V n)) :
    (⨁ n : ℕ, V n) ≃ₗ[K] ⨁ n : ℕ, V (d+n) :=
  LinearEquiv.ofBijective (restriction V d)
    ⟨restriction_injective V d hz, restriction_surjective V d⟩

/-- Degreewise isomorphisms after a shift give an all-degree isomorphism. -/
def ofDegreewiseEquivalences (d : ℕ) (hz : ∀ n < d, Subsingleton (V n))
    (W : ℕ → Type*) [∀ n, AddCommGroup (W n)] [∀ n, Module K (W n)]
    (e : ∀ n, W n ≃ₗ[K] V (d+n)) :
    (⨁ n : ℕ, W n) ≃ₗ[K] ⨁ n : ℕ, V n :=
  (DirectSum.congrLinearEquiv e).trans (equivalence V d hz).symm

end PaperVerification.DirectSumShift
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.DirectSumShift"


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
    (`PaperVerification.DirectSumShift.restriction, "definition"),
    (`PaperVerification.DirectSumShift.restriction_surjective, "theorem"),
    (`PaperVerification.DirectSumShift.restriction_injective, "theorem"),
    (`PaperVerification.DirectSumShift.equivalence, "definition"),
    (`PaperVerification.DirectSumShift.ofDegreewiseEquivalences, "definition")
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
    ("nonce", toJson "115cb60b5c57006b3958b8b2dde4fc47"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:115cb60b5c57006b3958b8b2dde4fc47"
