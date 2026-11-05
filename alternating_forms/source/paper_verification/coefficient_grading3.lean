module

public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.PolynomialCoefficientGrading -/


/-!
# Polynomial extension with a parameter of degree zero

For an internally graded coefficient algebra, the degree-`d` piece of its
polynomial extension consists exactly of polynomials whose coefficients
all have degree `d`. The parameter has degree zero. The internal direct
sum and the graded multiplication are proved from the coefficient
grading; no grading of the extension is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Polynomial DirectSum

namespace PaperVerification.PolynomialCoefficientGrading

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- Ordinary coefficient degree, with the polynomial parameter in degree zero. -/
def piece (G : TauCeti.InternalGrading K A ℕ) (d : ℕ) :
    Submodule K (Polynomial A) where
  carrier := {p | ∀ j, p.coeff j ∈ G.piece d}
  zero_mem' := by intro j; simpa using (G.piece d).zero_mem
  add_mem' := by
    intro p q hp hq j
    simpa only [coeff_add] using (G.piece d).add_mem (hp j) (hq j)
  smul_mem' := by
    intro c p hp j
    simpa only [coeff_smul] using (G.piece d).smul_mem c (hp j)

@[simp] theorem mem_piece_iff (G : TauCeti.InternalGrading K A ℕ)
    (d : ℕ) (p : Polynomial A) :
    p ∈ piece G d ↔ ∀ j, p.coeff j ∈ G.piece d := Iff.rfl

theorem monomial_mem (G : TauCeti.InternalGrading K A ℕ)
    (j : ℕ) {d : ℕ} {a : A} (ha : a ∈ G.piece d) :
    monomial j a ∈ piece G d := by
  intro l
  by_cases h : j = l
  · simpa [coeff_monomial, h] using ha
  · simp [coeff_monomial, h]

theorem isInternal (G : TauCeti.InternalGrading K A ℕ) :
    DirectSum.IsInternal (piece G) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply iSupIndep_def.mpr
    intro d
    apply Submodule.disjoint_def.mpr
    intro p hp hq
    apply Polynomial.ext
    intro j
    have hle : (⨆ e, ⨆ (_ : e ≠ d), piece G e) ≤
        (⨆ e, ⨆ (_ : e ≠ d), G.piece e).comap
          ((Polynomial.lcoeff A j).restrictScalars K) := by
      apply iSup_le
      intro e
      apply iSup_le
      intro he p hp
      exact Submodule.mem_iSup_of_mem e
        (Submodule.mem_iSup_of_mem he (hp j))
    have hz := Submodule.disjoint_def.mp
      (G.isInternal.submodule_iSupIndep d) (p.coeff j) (hp j) (hle hq)
    simpa only [coeff_zero] using hz
  · apply top_unique
    intro p hp
    clear hp
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | monomial j a =>
      have hsum : monomial j a =
          ∑ d ∈ (DirectSum.decompose G.piece a).support,
            monomial j (DirectSum.decompose G.piece a d : A) := by
        rw [← map_sum, DirectSum.sum_support_decompose]
      rw [hsum]
      apply Submodule.sum_mem
      intro d _
      exact Submodule.mem_iSup_of_mem d
        (monomial_mem G j (DirectSum.decompose G.piece a d).property)

/-- The genuine internal grading of the polynomial algebra by coefficient degree. -/
def grading (G : TauCeti.InternalGrading K A ℕ) :
    TauCeti.InternalGrading K (Polynomial A) ℕ :=
  ⟨piece G, isInternal G⟩

@[simp] theorem grading_piece (G : TauCeti.InternalGrading K A ℕ) (d : ℕ) :
    (grading G).piece d = piece G d := rfl

/-- Taking a coefficient preserves the coefficient grading. -/
theorem coefficient_homogeneous (G : TauCeti.InternalGrading K A ℕ) (j : ℕ) :
    TauCeti.LinearMap.IsHomogeneous ((Polynomial.lcoeff A j).restrictScalars K)
      (grading G).piece G.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d p hp
  simpa only [add_zero, LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply] using hp j

theorem decompose_coeff (G : TauCeti.InternalGrading K A ℕ)
    (p : Polynomial A) (d j : ℕ) :
    (DirectSum.decompose (grading G).piece p d : Polynomial A).coeff j =
      (DirectSum.decompose G.piece (p.coeff j) d : A) := by
  have h := (coefficient_homogeneous G j).map_decompose d p
  change (DirectSum.decompose (grading G).piece p d : Polynomial A).coeff j =
    (DirectSum.decompose G.piece (p.coeff j) (d + 0) : A) at h
  simpa only [Nat.add_zero] using h

instance gradedMonoid (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : SetLike.GradedMonoid (grading G).piece where
  one_mem := by
    intro j
    by_cases h : j = 0
    · subst j
      simpa only [coeff_one_zero] using
        (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)
    · simp only [coeff_one, h, ite_false]
      exact (G.piece 0).zero_mem
  mul_mem := by
    intro a b p q hp hq j
    rw [coeff_mul]
    exact (G.piece (a + b)).sum_mem fun uv _ ↦
      SetLike.GradedMul.mul_mem (hp uv.1) (hq uv.2)

instance gradedAlgebra (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : GradedAlgebra (grading G).piece :=
  (grading G).isInternal.gradedAlgebra

theorem C_mem (G : TauCeti.InternalGrading K A ℕ) {d : ℕ} {a : A}
    (ha : a ∈ G.piece d) : Polynomial.C a ∈ (grading G).piece d := by
  change Polynomial.C a ∈ piece G d
  simpa only [monomial_zero_left] using monomial_mem G 0 ha

theorem X_mem_zero (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : (Polynomial.X : Polynomial A) ∈ (grading G).piece 0 := by
  change (Polynomial.X : Polynomial A) ∈ piece G 0
  simpa only [monomial_one_one_eq_X] using
    monomial_mem G 1 (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)

end PaperVerification.PolynomialCoefficientGrading
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.PolynomialCoefficientGrading"


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
    (`PaperVerification.PolynomialCoefficientGrading.piece, "definition"),
    (`PaperVerification.PolynomialCoefficientGrading.mem_piece_iff, "theorem"),
    (`PaperVerification.PolynomialCoefficientGrading.monomial_mem, "theorem"),
    (`PaperVerification.PolynomialCoefficientGrading.isInternal, "theorem"),
    (`PaperVerification.PolynomialCoefficientGrading.grading, "definition"),
    (`PaperVerification.PolynomialCoefficientGrading.decompose_coeff, "theorem"),
    (`PaperVerification.PolynomialCoefficientGrading.X_mem_zero, "theorem")
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
    ("nonce", toJson "ad310acf61dfb618ce617823aa294756"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:ad310acf61dfb618ce617823aa294756"
