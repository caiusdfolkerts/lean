module

public import paper_verification.literal004
import all paper_verification.literal004
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.MainStatements -/

/-!
# A reader-facing form of Theorem 1.1

The polynomial in this theorem is nonzero and has an explicitly proved
nonempty nonvanishing locus in the full coefficient space of pairs of
two-forms. The same locus controls every degree. The last clause states
literal vanishing of every element in degrees above the cutoff, in addition
to the complete formal-power-series identity.
-/

namespace PaperVerification.MainStatements

noncomputable section

open MvPolynomial PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The complete Hilbert series and actual high-degree vanishing hold
on one nonempty principal open of the full space of pairs of quadrics.
Taking `M = V*` gives exactly the exterior algebra in the paper. -/
theorem genericHilbertSeriesAndVanishing (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            exteriorPairHilbertSeries
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 =
              paperExteriorHilbertSeries n ∧
            ∀ s : ℕ, (n + 1) / 2 < s →
              ∀ x : ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s,
                x = 0 := by
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  obtain ⟨hzero, hlow, hhigh⟩ := h y hy
  refine ⟨(exteriorPairHilbertSeries_eq_iff _ _ n).mpr
    ⟨hzero, fun s hs hd => (hlow s hs hd).1, hhigh⟩, ?_⟩
  intro s hs x
  letI : Subsingleton (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) :=
    (Module.finrank_zero_iff (R := K)).mp (hhigh s hs)
  exact Subsingleton.elim x 0

end
end PaperVerification.MainStatements
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.MainStatements"


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
    (`PaperVerification.MainStatements.genericHilbertSeriesAndVanishing, "theorem")
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
    ("nonce", toJson "0fee8899d0d03874e121a59086835c4a"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:0fee8899d0d03874e121a59086835c4a"
