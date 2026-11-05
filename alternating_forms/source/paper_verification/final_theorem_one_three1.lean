module

public import paper_verification.graded_characteristic1
import all paper_verification.graded_characteristic1
public import paper_verification.literal005
import all paper_verification.literal005
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsFinalTheoremOneThree -/


/-!
# The full Theorem 1.3, with the actual graded flat families

The exterior basis is asserted in every degree. The complete-section-ring
conclusions retain the original coordinate equations, coordinate sections,
quadratic Gröbner basis, and actual graded Tor statement. The additional
fields below give the two explicit graded flat degenerations.

The first degeneration is stated once for rank one and once for rank
`s=t+2`. These disjoint branches exhaust the full positive range and include
`k=0`. The second degeneration is stated uniformly for every positive rank.
Every family type displays its literal ideals, weights, and original
homogeneous grading. No existence of a degeneration is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MvPolynomial PaperVerification.WeightedInitialFiber

namespace PaperVerification.AlternatingForms

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The complete algebraic statement of Theorem 1.3 with genuine ordinary
gradings on both actual flat families and all their fiber isomorphisms. -/
theorem paper_theorem_1_3_fully_graded (k : ℕ) :
    (∀ s, ∃ B : Module.Basis (GoodOddIndex k s) K
        (OddExteriorQuotientDegree (K := K) k s),
      ∀ I, B I = Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2 * k + 1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0 < s) (hs : s ≤ k + 1),
      OddCompleteSectionConclusions (K := K) k s hs) ∧
    Nonempty (CoordinateGradedReesDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (matrixPluckerIdeal (s := 1) (n := 2 * k + 1))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))) ∧
    (∀ (t : ℕ) (hs : t + 2 ≤ k + 1),
      Nonempty (CoordinateGradedReesDegeneration
        (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
        (isotropicPluckerIdeal_isHomogeneous _)
        (pluckerVertexWeight (oddNatVertexWeight k))
        (isotropicPluckerIdeal (t := t) (oddPluckerForms k))
        (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
          (oddIntervalUpper k (t + 2) hs)))) ∧
    (∀ (s : ℕ) (hpos : 0 < s) (hs : s ≤ k + 1),
      Nonempty (CoordinateGradedReesDegeneration
        (Hibi.goodBandIdeal (K := K) (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (Hibi.goodBandIdeal_coordinate_homogeneous _ _
          (oddIntervalLower_strictMono k s hs).monotone
          (oddIntervalUpper_strictMono k s hs).monotone hpos)
        (Hibi.diagonalWeight (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))
        (Hibi.relationIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs)))) := by
  refine ⟨(paper_theorem_1_3_complete_section_ring (K := K) k).1,
    (paper_theorem_1_3_complete_section_ring (K := K) k).2,
    ⟨onePlaneOddRichardsonGradedFlatDegeneration (K := K) k⟩,
    ?_, ?_⟩
  · intro t hs
    exact ⟨oddRichardsonGradedFlatDegeneration (K := K) k t hs⟩
  · intro s hpos hs
    exact ⟨Hibi.hibiGradedFlatDegeneration (K := K)
      (oddIntervalLower k s hs) (oddIntervalUpper k s hs)
      (oddIntervalLower_strictMono k s hs).monotone
      (oddIntervalUpper_strictMono k s hs).monotone hpos⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsFinalTheoremOneThree"


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
    (`PaperVerification.AlternatingForms.paper_theorem_1_3_fully_graded, "theorem")
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
    ("nonce", toJson "8427023cc4fae60db61fdb5f4c07df3b"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:8427023cc4fae60db61fdb5f4c07df3b"
