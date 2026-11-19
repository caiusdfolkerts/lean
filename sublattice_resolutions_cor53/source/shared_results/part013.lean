module
public import graph_foundation.part012
public import shared_results.part012

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphHomologicalGrading -/
section

/-!
# Homological projections for the actual integral ideal contraction

The source projection retains the literal exterior faces of cardinality
`p`. The target projection retains the actual homology quotients of degree
`p` in every ordinary degree. These projections intertwine the constructed
inclusion, projection, and homotopy; the latter raises degree by one.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical DirectSum

variable {R : Type*} [CommRing R]
  (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

/-- Retain exactly one actual summand of a nonnegative direct sum. -/
def directSumDegreeProjection (p : ℕ) : Module.End R (⨁ n, C n) :=
  DirectSum.lmap (fun n => if n = p then LinearMap.id else 0)

@[simp] theorem directSumDegreeProjection_lof (p r : ℕ) (x : C r) :
    directSumDegreeProjection (R := R) C p (DirectSum.lof R ℕ C r x) =
      if r = p then DirectSum.lof R ℕ C r x else 0 := by
  rw [directSumDegreeProjection, DirectSum.lmap_lof]
  by_cases h : r = p
  · rw [if_pos h, if_pos h, LinearMap.id_apply]
  · rw [if_neg h, if_neg h, LinearMap.zero_apply, map_zero]

@[simp] theorem directSumDegreeProjection_apply (p : ℕ) (x : ⨁ n, C n) (r : ℕ) :
    directSumDegreeProjection (R := R) C p x r = if r = p then x r else 0 := by
  change (if r = p then (LinearMap.id : Module.End R (C r)) else 0) (x r) = _
  split_ifs <;> rfl

theorem directSumDegreeProjection_idempotent (p : ℕ) :
    directSumDegreeProjection (R := R) C p * directSumDegreeProjection C p =
      directSumDegreeProjection C p := by
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro r
  change directSumDegreeProjection (R := R) C p
    (directSumDegreeProjection (R := R) C p x) r = directSumDegreeProjection (R := R) C p x r
  simp only [directSumDegreeProjection_apply]
  split_ifs <;> rfl

/-- Pointwise commutation follows from the two projection formulas.
This elementary function lemma keeps concrete linear maps out of rewrite search. -/
private theorem projection_commutes_at_of_formulas {X Y : Type*}
    (zeroX : X) (zeroY : Y) (f : X → Y) (sourceProjection : X → X)
    (targetProjection : Y → Y) (keep : Prop) [Decidable keep] (x : X) (y : Y)
    (hsource : sourceProjection x = if keep then x else zeroX)
    (hmap : f x = y)
    (htarget : targetProjection y = if keep then y else zeroY)
    (hzero : f zeroX = zeroY) :
    f (sourceProjection x) = targetProjection (f x) := by
  calc
    f (sourceProjection x) = f (if keep then x else zeroX) := congrArg f hsource
    _ = if keep then f x else f zeroX := apply_ite f keep x zeroX
    _ = if keep then y else zeroY :=
      congrArg₂ (fun a b => if keep then a else b) hmap hzero
    _ = targetProjection y := htarget.symm
    _ = targetProjection (f x) := congrArg targetProjection hmap.symm

end FourPapers

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial DirectSum
open HomologicalPerturbation
open scoped TensorProduct

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))

/-- The actual exterior-degree projection on the polynomial ideal tensor
Koszul module. It depends only on the original exterior basis. -/
def idealTensorHomologicalProjection (p : ℕ) :
    Module.End k (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal)) :=
  Grading.projection (idealTensorBasis P) (fun a => a.2.card) p

/-- Retain homological degree `p` in every ordinary-degree homology summand. -/
def idealHomologyProjection (p : ℕ) : Module.End k (IdealGradedHomology P hJ) :=
  DirectSum.lmap (fun q => directSumDegreeProjection
    (actualIdealOrdinaryHomology P hJ q) p)

abbrev idealHomologyLof (q p : ℕ) : actualIdealOrdinaryHomology P hJ q p →ₗ[k]
    IdealGradedHomology P hJ :=
  (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryHomology P hJ q p) q).comp
    (DirectSum.lof k ℕ (actualIdealOrdinaryHomology P hJ q) p)

@[simp] theorem idealHomologyProjection_lof (p q r : ℕ)
    (x : actualIdealOrdinaryHomology P hJ q r) :
    idealHomologyProjection P hJ p (idealHomologyLof P hJ q r x) =
      if r = p then idealHomologyLof P hJ q r x else 0 := by
  change DirectSum.lmap
    (fun q => directSumDegreeProjection (R := k) (actualIdealOrdinaryHomology P hJ q) p)
    (DirectSum.lof k ℕ (fun q => ⨁ r, actualIdealOrdinaryHomology P hJ q r) q
      (DirectSum.lof k ℕ (actualIdealOrdinaryHomology P hJ q) r x)) = _
  rw [DirectSum.lmap_lof, directSumDegreeProjection_lof]
  split_ifs <;> simp only [map_zero, idealHomologyLof, LinearMap.comp_apply]

theorem idealTensor_lift_homological (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val ∈
      Grading.Piece (idealTensorBasis P) (fun a => a.2.card) p := by
  simpa only [idealTensorBidegree] using!
    piece_regrade (R := k)
      (X := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (idealTensorBasis P) (idealTensorBidegree P) (q,p) Prod.snd
      (idealTensor_lift_bidegree P q p x)

@[simp] theorem idealTensorHomologicalProjection_lift (p q r : ℕ)
    (x : actualIdealOrdinaryPiece P q r) :
    idealTensorHomologicalProjection P p
      (TensorExteriorKoszul.lift (K := k) (M := P.ideal) r x.val) =
        if r = p then TensorExteriorKoszul.lift (K := k) r x.val else 0 := by
  by_cases hr : r = p
  · subst r
    rw [if_pos rfl]
    exact Grading.projection_eq_self (idealTensor_lift_homological P q p x)
  · rw [if_neg hr]
    exact Grading.projection_eq_zero (Ne.symm hr) (idealTensor_lift_homological P q r x)

variable (hfree : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p))

set_option backward.isDefEq.respectTransparency true in
theorem actualIdealTensorContraction_h_homological (a : IdealTensorIndex P) :
    (actualIdealTensorContraction P hJ hfree).h (idealTensorBasis P a) ∈
      Grading.Piece (idealTensorBasis P) (fun a => a.2.card) (a.2.card+1) := by
  have hle : Grading.Piece (idealTensorBasis P) (idealTensorBidegree P)
      (idealTensorOrdinaryDegree P a, a.2.card+1) ≤
      Grading.Piece (idealTensorBasis P)
        (fun i : IdealTensorIndex P => i.2.card) (a.2.card+1) := by
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi
    exact congrArg (Prod.snd : ℕ × ℕ → ℕ) hi
  exact hle (actualIdealTensorContraction_h_bidegree P hJ hfree a)

set_option backward.isDefEq.respectTransparency true in
/-- The actual homotopy raises exterior degree by one. -/
theorem actualIdealTensorContraction_h_projection (p : ℕ) :
    (actualIdealTensorContraction P hJ hfree).h * idealTensorHomologicalProjection P p =
      idealTensorHomologicalProjection P (p+1) *
        (actualIdealTensorContraction P hJ hfree).h := by
  apply (idealTensorBasis P).ext
  intro a
  change (actualIdealTensorContraction P hJ hfree).h
      (Grading.projection (idealTensorBasis P)
        (fun i : IdealTensorIndex P => i.2.card) p (idealTensorBasis P a)) =
    Grading.projection (idealTensorBasis P)
      (fun i : IdealTensorIndex P => i.2.card) (p+1)
      ((actualIdealTensorContraction P hJ hfree).h (idealTensorBasis P a))
  rw [Grading.projection_basis]
  by_cases ha : a.2.card = p
  · rw [if_pos ha, ← ha]
    exact (Grading.projection_eq_self
      (actualIdealTensorContraction_h_homological P hJ hfree a)).symm
  · rw [if_neg ha, map_zero]
    exact (Grading.projection_eq_zero
      (show p+1 ≠ a.2.card+1 from fun h => ha (Nat.add_right_cancel h).symm)
      (actualIdealTensorContraction_h_homological P hJ hfree a)).symm

/-- No image of the homotopy can lie in exterior degree zero. -/
theorem actualIdealTensorContraction_h_projection_zero :
    idealTensorHomologicalProjection P 0 * (actualIdealTensorContraction P hJ hfree).h = 0 := by
  apply (idealTensorBasis P).ext
  intro a
  exact Grading.projection_eq_zero (Nat.zero_ne_add_one a.2.card)
    (actualIdealTensorContraction_h_homological P hJ hfree a)

/-- Inclusion on a genuine homology summand has exactly its original
homological degree, through the constructed kernel/image section. -/
theorem actualIdealTensorContraction_inclusion_lof (q p : ℕ)
    (x : actualIdealOrdinaryHomology P hJ q p) :
    (actualIdealTensorContraction P hJ hfree).inclusion
      (idealHomologyLof P hJ q p x) =
    TensorExteriorKoszul.lift (K := k) (M := P.ideal) p
      (ProjectiveComplexSplitting.homologyInclusion (fun p => ↥(actualIdealOrdinaryPiece P q p))
        (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
        (actualIdealSplittingHomology_projective P hJ hfree q) p
        ((actualIdealSplittingHomologyEquiv P hJ q p).symm x)).val := by
  unfold actualIdealTensorContraction
  change idealGradedTotalEquiv P
    ((actualIdealGradedContraction P hJ hfree).inclusion
      (DirectSum.lof k ℕ _ q (DirectSum.lof k ℕ _ p x))) = _
  rw [actualIdealGradedContraction, LinearContraction.directSum_inclusion_lof]
  change idealGradedTotalEquiv P
    (DirectSum.lof k ℕ _ q
      (ProjectiveComplexSplitting.totalHomologyInclusion (fun p => ↥(actualIdealOrdinaryPiece P q p))
        (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
        (actualIdealSplittingHomology_projective P hJ hfree q)
        (DirectSum.lmap (fun p => (actualIdealSplittingHomologyEquiv P hJ q p).symm.toLinearMap)
          (DirectSum.lof k ℕ _ p x)))) = _
  rw [DirectSum.lmap_lof, ProjectiveComplexSplitting.totalHomologyInclusion_lof,
    idealGradedTotalEquiv_lof]
  rfl

/-- Projection of a homogeneous chain lands in the corresponding genuine
homology summand, including homological degree zero. -/
theorem actualIdealTensorContraction_projection_lift (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q p) :
    (actualIdealTensorContraction P hJ hfree).projection
      (TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val) =
    idealHomologyLof P hJ q p
      (actualIdealSplittingHomologyEquiv P hJ q p
        (ProjectiveComplexSplitting.homologyProjection (fun p => ↥(actualIdealOrdinaryPiece P q p))
          (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
          (actualIdealOrdinaryTerm_projective P q)
          (actualIdealSplittingHomology_projective P hJ hfree q) p x)) := by
  rw [← idealGradedTotalEquiv_lof P q p x]
  unfold actualIdealTensorContraction
  change (actualIdealGradedContraction P hJ hfree).projection
    ((idealGradedTotalEquiv P).symm (idealGradedTotalEquiv P _)) = _
  rw [LinearEquiv.symm_apply_apply, actualIdealGradedContraction,
    LinearContraction.directSum_projection_lof]
  change DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryHomology P hJ q p) q
    (DirectSum.lmap (fun p => (actualIdealSplittingHomologyEquiv P hJ q p).toLinearMap)
      (ProjectiveComplexSplitting.totalHomologyProjection (fun p => ↥(actualIdealOrdinaryPiece P q p))
        (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
        (actualIdealOrdinaryTerm_projective P q)
        (actualIdealSplittingHomology_projective P hJ hfree q)
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x))) = _
  rw [ProjectiveComplexSplitting.totalHomologyProjection_lof, DirectSum.lmap_lof]
  rfl

/-- Inclusion preserves actual homological degree. -/
theorem actualIdealTensorContraction_inclusion_projection (p : ℕ) :
    (actualIdealTensorContraction P hJ hfree).inclusion.comp
      (idealHomologyProjection P hJ p) =
    (idealTensorHomologicalProjection P p).comp
      (actualIdealTensorContraction P hJ hfree).inclusion := by
  apply DirectSum.linearMap_ext
  intro q
  apply DirectSum.linearMap_ext
  intro r
  ext x
  change (actualIdealTensorContraction P hJ hfree).inclusion
    (idealHomologyProjection P hJ p (idealHomologyLof P hJ q r x)) =
    idealTensorHomologicalProjection P p
      ((actualIdealTensorContraction P hJ hfree).inclusion (idealHomologyLof P hJ q r x))
  rw [idealHomologyProjection_lof, actualIdealTensorContraction_inclusion_lof,
    idealTensorHomologicalProjection_lift]
  split_ifs <;> simp only [map_zero, actualIdealTensorContraction_inclusion_lof]

set_option backward.isDefEq.respectTransparency true in
/-- Projection preserves actual homological degree. -/
theorem actualIdealTensorContraction_projection_projection (p : ℕ) :
    (actualIdealTensorContraction P hJ hfree).projection.comp
      (idealTensorHomologicalProjection P p) =
    (idealHomologyProjection P hJ p).comp
      (actualIdealTensorContraction P hJ hfree).projection := by
  let π : TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) →ₗ[k]
      IdealGradedHomology P hJ := (actualIdealTensorContraction P hJ hfree).projection
  change π.comp (idealTensorHomologicalProjection P p) =
    (idealHomologyProjection P hJ p).comp π
  have he : (π.comp (idealTensorHomologicalProjection P p)).comp
      (idealGradedTotalEquiv P).toLinearMap =
    ((idealHomologyProjection P hJ p).comp π).comp
      (idealGradedTotalEquiv P).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro q
    apply DirectSum.linearMap_ext
    intro r
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    let y : actualIdealOrdinaryHomology P hJ q r :=
      actualIdealSplittingHomologyEquiv P hJ q r
        (ProjectiveComplexSplitting.homologyProjection
          (fun r => ↥(actualIdealOrdinaryPiece P q r))
          (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
          (actualIdealOrdinaryTerm_projective P q)
          (actualIdealSplittingHomology_projective P hJ hfree q) r x)
    have hπ : π (TensorExteriorKoszul.lift (K := k) (M := P.ideal) r x.val) =
        idealHomologyLof P hJ q r y :=
      actualIdealTensorContraction_projection_lift P hJ hfree q r x
    have hcomm := projection_commutes_at_of_formulas
      (0 : TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (0 : IdealGradedHomology P hJ) π (idealTensorHomologicalProjection P p)
      (idealHomologyProjection P hJ p) (r = p)
      (TensorExteriorKoszul.lift (K := k) (M := P.ideal) r x.val)
      (idealHomologyLof P hJ q r y)
      (idealTensorHomologicalProjection_lift P p q r x) hπ
      (idealHomologyProjection_lof P hJ p q r y) (map_zero π)
    exact (congrArg
      (fun t : TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) =>
        π (idealTensorHomologicalProjection P p t) = idealHomologyProjection P hJ p (π t))
      (idealGradedTotalEquiv_lof P q r x)).mpr hcomm
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun he ((idealGradedTotalEquiv P).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hx

end FourPapers.Sublattice

end
end
end


end
