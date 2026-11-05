module

public import PaperVerification.FermionNewtonRestrictionHilbert

/-!
# Surjectivity of the literal Newton restriction map

Rank-nullity is applied to each actual homogeneous piece. Its kernel is
identified with the corresponding deleted piece by division by the removed
coordinate. The proved full Hilbert identity then forces the image to equal
the smaller piece. Finally the actual monomial multiples of its Newton basis
span the entire target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial Module
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def numeratorRestrictionOnPiece
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) (D : ℕ) :=
  (numeratorRestriction β δ σ hβ q hq).domRestrict
    (GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) D)

def deletionOnPiece
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q) (D : ℕ) (hD : 1 ≤ D) :
    GradedHilbert.vectorHomogeneousPiece (numeratorModule β (deletedMultiplicity δ q) σ) (D - 1) →ₗ[F]
      GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) D :=
  LinearMap.codRestrict _ ((deletionMultiplication β δ σ q hq).domRestrict _)
    (fun a ↦ by
      change deletionMultiplication β δ σ q hq a.val ∈
        GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) D
      have h := deletionMultiplication_homogeneous β δ σ q hq a.val (D - 1) a.property
      simpa only [Nat.sub_add_cancel hD] using h)

theorem deletionOnPiece_injective
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q) (D : ℕ) (hD : 1 ≤ D) :
    Function.Injective (deletionOnPiece β δ σ q hq D hD) := by
  intro a b hab
  apply Subtype.ext
  exact deletionMultiplication_injective β δ σ q hq (congrArg Subtype.val hab)

theorem deletionOnPiece_range
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) (D : ℕ) (hD : 1 ≤ D) :
    LinearMap.range (deletionOnPiece β δ σ q hq D hD) =
      LinearMap.ker (numeratorRestrictionOnPiece β δ σ hβ q hq D) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    have h : deletionMultiplication β δ σ q hq a.val ∈
        LinearMap.range (deletionMultiplication β δ σ q hq) := ⟨a.val,rfl⟩
    rw [← numeratorRestriction_ker β δ σ hβ q hq] at h
    exact h
  · intro a ha
    have hker : a.val ∈ LinearMap.ker (numeratorRestriction β δ σ hβ q hq) := ha
    rw [numeratorRestriction_ker β δ σ hβ q hq] at hker
    obtain ⟨b,hb⟩ := hker
    have hbpiece : b ∈ GradedHilbert.vectorHomogeneousPiece
        (numeratorModule β (deletedMultiplicity δ q) σ) (D - 1) := by
      intro i
      exact homogeneous_quotient_of_relation (isHomogeneous_X F q) (X_ne_zero q)
        (a.property i) (congrArg (fun z ↦ z.val i) hb) hD
    exact ⟨⟨b,hbpiece⟩,Subtype.ext hb⟩

theorem restrictionOnPiece_ker_zero
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) :
    LinearMap.ker (numeratorRestrictionOnPiece β δ σ hβ q hq 0) = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hker : a.val ∈ LinearMap.ker (numeratorRestriction β δ σ hβ q hq) := ha
  rw [numeratorRestriction_ker β δ σ hβ q hq] at hker
  obtain ⟨b,hb⟩ := hker
  have hb0 : b = 0 := by
    apply Subtype.ext
    funext i
    exact quotient_zero_of_homogeneous_relation_lt (isHomogeneous_X F q) (X_ne_zero q)
      (a.property i) (congrArg (fun z ↦ z.val i) hb) (by omega)
  change a = 0
  apply Subtype.ext
  rw [← hb,hb0,map_zero]
  rfl

theorem restrictionOnPiece_ker_finrank
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) (D : ℕ) :
    Module.finrank F (LinearMap.ker (numeratorRestrictionOnPiece β δ σ hβ q hq D)) =
      if 1 ≤ D then Module.finrank F (GradedHilbert.vectorHomogeneousPiece
        (numeratorModule β (deletedMultiplicity δ q) σ) (D - 1)) else 0 := by
  by_cases hD : 1 ≤ D
  · rw [if_pos hD,← deletionOnPiece_range β δ σ hβ q hq D hD]
    exact (LinearEquiv.ofInjective (deletionOnPiece β δ σ q hq D hD)
      (deletionOnPiece_injective β δ σ q hq D hD)).finrank_eq.symm
  · have hz : D = 0 := by omega
    subst D
    rw [if_neg (by omega),restrictionOnPiece_ker_zero,finrank_bot]

set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction is onto in every homogeneous degree. -/
theorem numeratorRestriction_piece_range
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hc : Compatible δ σ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) (e : ℕ) :
    LinearMap.range (numeratorRestrictionOnPiece β δ σ
      (singleton_weight_ne_zero β hβ) q hq.1 (e + (negativeNeighbours σ q).card)) =
      GradedHilbert.vectorHomogeneousPiece
        (numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)) e := by
  letI := numeratorPiece_finite β δ σ hc hσ hβ (e + (negativeNeighbours σ q).card)
  letI := numeratorPiece_finite (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)
    (Compatible.restricted δ σ hσ hc q hq) (fun i ↦ hσ (q.succAbove i))
    (subset_weights_restricted β hβ q) e
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨a,rfl⟩
    exact numeratorRestriction_homogeneous β δ σ (singleton_weight_ne_zero β hβ) q hq.1
      a.val e a.property
  · have hr := LinearMap.finrank_range_add_finrank_ker (K := F)
      (V := GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ)
        (e + (negativeNeighbours σ q).card))
      (V₂ := numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q)
        (σ ∘ q.succAbove))
      (numeratorRestrictionOnPiece β δ σ (singleton_weight_ne_zero β hβ) q hq.1
        (e + (negativeNeighbours σ q).card))
    rw [restrictionOnPiece_ker_finrank] at hr
    have hd := numerator_restriction_piece_dimension β δ σ hc hσ hβ q hq e
    exact Nat.add_right_cancel (hr.trans hd)

/-- Restriction onto the complete smaller Newton module, with no degree
bound and no supplied surjectivity or Hilbert-series hypothesis. -/
theorem numeratorRestriction_surjective
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hc : Compatible δ σ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) :
    Function.Surjective (numeratorRestriction β δ σ (singleton_weight_ne_zero β hβ) q hq.1) := by
  let β' := β ∘ q.succAbove
  let δ' := restrictedMultiplicity δ σ q
  let σ' := σ ∘ q.succAbove
  let N := numeratorModule β' δ' σ'
  let B := newtonNumeratorBasis β' δ' σ' (Compatible.restricted δ σ hσ hc q hq)
    (fun i ↦ hσ (q.succAbove i)) (subset_weights_restricted β hβ q)
  let C : Basis ((Fin n →₀ ℕ) × Fin n) F N :=
    GradedHilbert.polynomialScalarBasis (K := F) (n := n) N B
  have hB (i k : Fin n) : ((B i : N).val k).IsHomogeneous (columnNumeratorDegree δ' σ' i) := by
    rw [newtonNumeratorBasis_apply]
    exact columnCommonNumerator_homogeneous β' δ' σ' _ i k
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← C.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  have ha : C a ∈ GradedHilbert.vectorHomogeneousPiece N
      (GradedHilbert.polynomialScalarDegree (columnNumeratorDegree δ' σ') a) :=
    GradedHilbert.polynomialScalarBasis_homogeneous (K := F) (n := n) N B (columnNumeratorDegree δ' σ') hB a
  rw [← numeratorRestriction_piece_range β δ σ hc hσ hβ q hq] at ha
  obtain ⟨x,hx⟩ := ha
  exact ⟨x.val,hx⟩

end PaperVerification.Fermion.Newton
