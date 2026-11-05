module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import all Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Finsupp
import all Mathlib.RingTheory.Finiteness.Finsupp
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.ExactSequenceRank -/

/-!
# Dimension bounds at the middle of an exact sequence

The maps need only be exact at the middle term. In particular, the right map
need not be surjective. This is the form needed for the long exact sequence of
an actual pair of topological spaces.
-/

namespace PaperVerification.ExactSequenceRank

noncomputable section

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- Finiteness of the two outside terms implies finiteness of the middle. -/
theorem finite_middle (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Module.Finite K A] [Module.Finite K C] : Module.Finite K B := by
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
  · apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, h]
  · exact g.surjective_rangeRestrict

/-- The actual rank of the middle term is bounded by the sum of the
outside ranks, with no surjectivity assumption on either map. -/
theorem finrank_middle_le (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Module.Finite K A] [Module.Finite K C] :
    Module.finrank K B ≤ Module.finrank K A + Module.finrank K C := by
  letI := finite_middle f g h
  rw [← g.finrank_range_add_finrank_ker, ← h]
  exact (Nat.add_le_add (LinearMap.range g).finrank_le f.finrank_range_le).trans_eq
    (Nat.add_comm _ _)

/-- Zero outside terms force the actual middle vector space to vanish. -/
theorem subsingleton_middle (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Subsingleton A] [Subsingleton C] : Subsingleton B := by
  have hf : f = 0 := Subsingleton.elim _ _
  have hg : g = 0 := Subsingleton.elim _ _
  have hb : (⊥ : Submodule K B) = ⊤ := by
    simpa only [hf, hg, LinearMap.range_zero, LinearMap.ker_zero] using h
  have hzero (x : B) : x = 0 := by
    apply (Submodule.mem_bot K).mp
    rw [hb]
    trivial
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end
end PaperVerification.ExactSequenceRank
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExactSequenceRank"


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
    (`PaperVerification.ExactSequenceRank.finite_middle, "theorem"),
    (`PaperVerification.ExactSequenceRank.finrank_middle_le, "theorem"),
    (`PaperVerification.ExactSequenceRank.subsingleton_middle, "theorem")
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
    ("nonce", toJson "a5b9453d37c0f8643b3a7d24538fb366"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:a5b9453d37c0f8643b3a7d24538fb366"
