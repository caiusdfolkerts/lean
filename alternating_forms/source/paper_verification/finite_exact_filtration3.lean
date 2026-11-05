module

public import paper_verification.exact_sequence_rank2
import all paper_verification.exact_sequence_rank2
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import all Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.FiniteExactFiltration -/

/-!
# Rank bounds along a finite exact filtration

At each step the original three maps are required to be exact at the middle
term. The theorem does not assume that either outside map is surjective.
It applies to the actual pair sequence once its relative groups have been
computed from the geometry of a stratum.
-/

namespace PaperVerification.FiniteExactFiltration

noncomputable section

open scoped BigOperators

variable {K : Type*} [Field K]
  (V R : ℕ → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, AddCommGroup (R i)] [∀ i, Module K (R i)]
  (f : ∀ i, R i →ₗ[K] V (i + 1))
  (g : ∀ i, V (i + 1) →ₗ[K] V i)
  (hexact : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i))
  (hzero : Subsingleton (V 0))

include f g hexact hzero

/-- The dimension of a filtered object is bounded by the sum of the actual
relative dimensions. The first term is genuinely zero. -/
theorem finite_and_finrank_le_sum [∀ i, Module.Finite K (R i)] (n : ℕ) :
    Module.Finite K (V n) ∧
      Module.finrank K (V n) ≤ ∑ i ∈ Finset.range n, Module.finrank K (R i) := by
  induction n with
  | zero =>
      letI := hzero
      exact ⟨inferInstance, by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ n ih =>
      letI := ih.1
      letI := ExactSequenceRank.finite_middle (f n) (g n) (hexact n)
      refine ⟨inferInstance, ?_⟩
      calc
        Module.finrank K (V (n + 1)) ≤
            Module.finrank K (R n) + Module.finrank K (V n) :=
          ExactSequenceRank.finrank_middle_le (f n) (g n) (hexact n)
        _ ≤ Module.finrank K (R n) +
            ∑ i ∈ Finset.range n, Module.finrank K (R i) :=
          Nat.add_le_add_left ih.2 _
        _ = ∑ i ∈ Finset.range (n + 1), Module.finrank K (R i) := by
          rw [Finset.sum_range_succ, Nat.add_comm]

/-- A stratumwise bound can be substituted only after each actual relative
group has been proved finite and its rank has been bounded. -/
theorem finite_and_finrank_le_bound [∀ i, Module.Finite K (R i)]
    (b : ℕ → ℕ) (hbound : ∀ i, Module.finrank K (R i) ≤ b i) (n : ℕ) :
    Module.Finite K (V n) ∧
      Module.finrank K (V n) ≤ ∑ i ∈ Finset.range n, b i := by
  obtain ⟨hfinite, hrank⟩ := finite_and_finrank_le_sum V R f g hexact hzero n
  exact ⟨hfinite, hrank.trans (Finset.sum_le_sum fun i _ => hbound i)⟩

/-- If every relative group in a degree vanishes, every filtered stage
vanishes in that degree. -/
theorem subsingleton_of_relative_zero (hrelative : ∀ i, Subsingleton (R i)) (n : ℕ) :
    Subsingleton (V n) := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
      letI := ih
      letI := hrelative n
      exact ExactSequenceRank.subsingleton_middle (f n) (g n) (hexact n)

end
end PaperVerification.FiniteExactFiltration
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.FiniteExactFiltration"


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
    (`PaperVerification.FiniteExactFiltration.finite_and_finrank_le_sum, "theorem"),
    (`PaperVerification.FiniteExactFiltration.finite_and_finrank_le_bound, "theorem"),
    (`PaperVerification.FiniteExactFiltration.subsingleton_of_relative_zero, "theorem")
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
    ("nonce", toJson "c0833e0fe3fdd5d4422c6852443fde3c"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:c0833e0fe3fdd5d4422c6852443fde3c"
