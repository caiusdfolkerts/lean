module
public import resolution_existence.part007

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialFineAugmentation -/
section

/-!
# The actual augmentation has the stated fine shifts

Fine preservation of the differential matrices alone does not identify the
graded module resolved by the complex. This file also identifies the
degree-zero augmentation with the literal monomial-ideal map and proves
its weighted homogeneity for every assignment of variable weights.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice.MonomialFineResolution
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial CategoryTheory
open HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct
attribute [local instance] Classical.propDecidable

section ProjectedAugmentation
universe w
variable {R₀ S₀ F₀ M₁ : Type w} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
  [AddCommGroup F₀] [Module S₀ F₀] [Module R₀ F₀] [IsScalarTower R₀ S₀ F₀]
  [AddCommGroup M₁] [Module S₀ M₁] [Module R₀ M₁] [IsScalarTower R₀ S₀ M₁]
  {I₁ : Type*} (b : Module.Basis I₁ S₀ F₀) (degree : I₁ → ℕ)
  (D : Module.End S₀ F₀) (ε : F₀ →ₗ[S₀] M₁)
  (C₁ : LinearDeformationRetract (R := R₀) (M := F₀) (H := M₁))
  (hD : C₁.sourceD = D.restrictScalars R₀)
  (hε : C₁.projection = ε.restrictScalars R₀) (ht : C₁.targetD = 0)
  (hlower : ∀ p, D.comp (Grading.projection b degree (p+1)) =
    (Grading.projection b degree p).comp D)
  (hzero : D.comp (Grading.projection b degree 0) = 0)
  (hεzero : ε.comp (Grading.projection b degree 0) = ε)

/-- The actual augmented resolution sends a degree-zero restricted basis
vector to the augmentation of that same original basis vector. -/
theorem projectedResolution_augmentation_basis (i : {i : I₁ // degree i = 0}) :
    (ProjectedFreeResolution.resolution b degree D ε C₁ hD hε ht hlower hzero hεzero).π.f 0
      (ProjectedFreeResolution.pieceBasis b degree 0 i) = ε (b i.val) := by
  rw [ProjectedFreeResolution.resolution_π_f_zero]
  change ε (ProjectedFreeResolution.pieceBasis b degree 0 i).val = _
  exact congrArg ε (ProjectedFreeResolution.pieceBasis_val b degree 0 i)

end ProjectedAugmentation

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V] (B : Family V)
local notation "S" => MvPolynomial V K
local notation "M" => monomialIdeal K B

def barAugmentationPolynomial : Bar (R := K) (V := V) M →ₗ[K] S :=
  ((monomialIdeal K B).subtype.restrictScalars K).comp
    ((PolynomialModuleResolution.augmentation M).restrictScalars K)

theorem barAugmentationPolynomial_basis (β : Exponent V)
    (a : {a : Exponent V // Contains B a}) (F : Finset V) :
    barAugmentationPolynomial (K := K) B (barFineBasis (K := K) B (β,a,F)) =
      if F = ∅ then monomial (β+a.val) 1 else 0 := by
  change (PolynomialModuleResolution.augmentation M
    (barFineBasis (K := K) B (β,a,F))).val = _
  rw [barFineBasis, polynomialTensorBasis_apply, tensorBasis_apply,
    PolynomialModuleResolution.augmentation_tmul_basis]
  split_ifs with h
  · change monomial β 1 * (monomialBasis B a).val = _
    rw [monomialBasis_val, monomial_mul_monomial, one_mul]
  · rfl

theorem barAugmentationPolynomial_fine (α : Exponent V)
    (x : Bar (R := K) (V := V) M)
    (hx : x ∈ Grading.Piece (barFineBasis (K := K) B) (barFineDegree B) α) :
    barAugmentationPolynomial (K := K) B x ∈ Grading.Piece (basisMonomials V K) id α := by
  apply map_mem_piece_of_basis (barFineBasis (K := K) B) (basisMonomials V K)
    (barFineDegree B) id (barAugmentationPolynomial (K := K) B) _ α hx
  rintro ⟨β,a,F⟩
  rw [barAugmentationPolynomial_basis]
  by_cases hF : F = ∅
  · subst F
    rw [if_pos rfl]
    have h := Grading.basis_mem_piece (basisMonomials V K) id (β+a.val)
    simpa only [barFineDegree, polynomialTensorFineDegree, fineDegree,
      faceExponent_empty, add_zero, coe_basisMonomials, id_eq] using h
  · rw [if_neg hF]
    exact Submodule.zero_mem _

theorem freeModel_inclusion_fine (α : Exponent V) (x : S ⊗[K] Homology (K := K) B)
    (hx : x ∈ Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) α) :
    (freeModel (K := K) B).inclusion x ∈ Grading.Piece (barFineBasis (K := K) B) (barFineDegree B) α := by
  change ((extended (K := K) B).restrictScalars K).transferredInclusion
    ((externalDifferential M).restrictScalars K) (fineUnit (K := K) B) x ∈ _
  exact ((extended (K := K) B).restrictScalars K).transferredInclusion_mem_finePiece
    (barFineBasis (K := K) B) (modelFineBasis (K := K) B) (barFineDegree B) (modelFineDegree (K := K) B)
    ((externalDifferential M).restrictScalars K) (fineUnit (K := K) B) (fineUnit_val (K := K) B)
    (extended_h_fine (K := K) B) (external_fine (K := K) B) (extended_inclusion_fine (K := K) B) α x hx

theorem augmentation_fine (α : Exponent V) (x : S ⊗[K] Homology (K := K) B)
    (hx : x ∈ Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) α) :
    (augmentation (K := K) B x).val ∈ Grading.Piece (basisMonomials V K) id α := by
  change barAugmentationPolynomial (K := K) B ((freeModel (K := K) B).inclusion x) ∈ _
  exact barAugmentationPolynomial_fine (K := K) B α _ (freeModel_inclusion_fine (K := K) B α x hx)

theorem augmentation_basis_weighted (w : V → ℕ) (i : HomologyIndex (K := K) B) :
    (augmentation (K := K) B (freeBasis (K := K) B i)).val.IsWeightedHomogeneous w (Finsupp.weight w i.1) := by
  have h := augmentation_fine (K := K) B i.1 _ (freeBasis_fine (K := K) B i)
  intro a ha
  have hc : (basisMonomials V K).repr (augmentation (K := K) B (freeBasis (K := K) B i)).val a ≠ 0 := ha
  have he : a = i.1 := (Grading.mem_piece (basisMonomials V K) id i.1 _).mp h a hc
  rw [he]

/-- This evaluates the actual Mathlib resolution augmentation. -/
theorem resolution_augmentation (i : ResolutionIndex (K := K) B 0) :
    (resolution (K := K) B).π.f 0 (resolutionBasis (K := K) B 0 i) = augmentation (K := K) B (freeBasis (K := K) B i.val) :=
  projectedResolution_augmentation_basis (R₀ := K) (S₀ := S)
    (F₀ := S ⊗[K] Homology (K := K) B) (M₁ := M)
    (I₁ := HomologyIndex (K := K) B)
    (freeBasis (K := K) B) (fun a => a.2.1)
    (freeModel (K := K) B).targetD (augmentation (K := K) B)
    (splitAugmentation (K := K) B) rfl
    (PolynomialPerturbation.splitAugmentation_projection M (contraction (K := K) B)
      (contraction_d (K := K) B) (monomialBasis B) (fun a => a.val.degree)
      (contraction_h_nonincreasing (K := K) B)) rfl
    (freeModel_basis_lowers (K := K) B) (freeModel_basis_zero (K := K) B)
    (augmentation_basis_zero (K := K) B) i

/-- The augmentation has exactly the same fine shifts as the free terms,
so these terms resolve the correctly graded literal ideal. -/
theorem resolution_augmentation_weighted (w : V → ℕ) (i : ResolutionIndex (K := K) B 0) :
    ((resolution (K := K) B).π.f 0 (resolutionBasis (K := K) B 0 i)).val.IsWeightedHomogeneous
      w (Finsupp.weight w i.val.1) :=
  (congrArg (fun x : M => x.val.IsWeightedHomogeneous w (Finsupp.weight w i.val.1))
    (resolution_augmentation (K := K) B i)).mpr
      (augmentation_basis_weighted (K := K) B w i.val)

end FourPapers.Sublattice.MonomialFineResolution

end
end
end

end
