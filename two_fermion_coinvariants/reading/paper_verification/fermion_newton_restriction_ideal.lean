module

public import PaperVerification.FermionNewtonRestrictionSurjective

/-!
# Restriction of the actual contraction ideal

Surjective restriction of numerator fields gives equality with the smaller
contraction ideal, including the orientation scalar forced by the ordered
hyperplanes. Multiplying a deleted contraction by the removed variable lies
in the original ideal. These are the two facts needed for box spanning; its
independence will use the already proved complete-intersection length.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem removeCoordinate_surjective (q : Fin (n + 1)) :
    Function.Surjective (removeCoordinate (F := F) q) :=
  fun p ↦ ⟨rename q.succAbove p,removeCoordinate_rename q p⟩

theorem restriction_contraction_relation
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (p : MvPolynomial (Fin (n + 1)) F)
    (hp : (∑ i, C (β i) * a.val i) = negativeDenominator σ * p) :
    (∑ i : Fin n, C (β (q.succAbove i)) * restrictedNumerator β δ σ hβ q hq a i) =
      negativeDenominator (σ ∘ q.succAbove) *
        (C (restrictionOrientation (F := F) σ q) * removeCoordinate q p) := by
  have hnormal := removeCoordinate_normal_zero β δ σ q hq a.val a.property
  have hsum : removeCoordinate q (∑ i, C (β i) * a.val i) =
      ∑ i : Fin n, C (β (q.succAbove i)) * removeCoordinate q (a.val (q.succAbove i)) := by
    rw [map_sum,Fin.sum_univ_succAbove _ q]
    simp only [map_mul,removeCoordinate_C,hnormal,mul_zero,zero_add]
  apply mul_left_cancel₀ (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
  calc
    _ = ∑ i : Fin n, C (β (q.succAbove i)) *
        (coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq a i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = removeCoordinate q (∑ i, C (β i) * a.val i) := by
      simp_rw [restrictedNumerator_relation]
      exact hsum.symm
    _ = _ := by
      rw [hp,map_mul,removeCoordinate_negativeDenominator]
      ring

theorem removeCoordinate_contraction_mem
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    {p : MvPolynomial (Fin (n + 1)) F} (hp : p ∈ contractionIdeal β δ σ) :
    removeCoordinate q p ∈ contractionIdeal (β ∘ q.succAbove)
      (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) := by
  obtain ⟨a,ha,hap⟩ := hp
  have h : C (restrictionOrientation (F := F) σ q) * removeCoordinate q p ∈
      contractionIdeal (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) :=
    ⟨restrictedNumerator β δ σ hβ q hq ⟨a,ha⟩,
      restrictedNumerator_mem β δ σ hβ q hq ⟨a,ha⟩,
      restriction_contraction_relation β δ σ hβ q hq ⟨a,ha⟩ p hap⟩
  exact ((contractionIdeal (β ∘ q.succAbove) (restrictedMultiplicity δ σ q)
    (σ ∘ q.succAbove)).unit_mul_mem_iff_mem
      ((restrictionOrientation_isUnit (F := F) σ q).map MvPolynomial.C)).mp h

/-- The exact restricted ideal, proved from the actual surjective field
restriction rather than supplied as an additional basis hypothesis. -/
theorem map_contractionIdeal_removeCoordinate
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hc : Compatible δ σ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin (n + 1)), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) :
    Ideal.map (removeCoordinate (F := F) q).toRingHom (contractionIdeal β δ σ) =
      contractionIdeal (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (removeCoordinate (F := F) q).toRingHom (removeCoordinate_surjective q)).mp hp
    exact removeCoordinate_contraction_mem β δ σ (singleton_weight_ne_zero β hβ) q hq.1 ha
  · rintro p ⟨a,ha,hap⟩
    obtain ⟨b,hb⟩ := numeratorRestriction_surjective β δ σ hc hσ hβ q hq ⟨a,ha⟩
    obtain ⟨t,ht⟩ := denominator_dvd_contraction β δ σ b.property
    have htmem : t ∈ contractionIdeal β δ σ := ⟨b.val,b.property,ht⟩
    have he := restriction_contraction_relation β δ σ (singleton_weight_ne_zero β hβ) q hq.1 b t ht
    have hbval : restrictedNumerator β δ σ (singleton_weight_ne_zero β hβ) q hq.1 b = a :=
      congrArg Subtype.val hb
    rw [hbval] at he
    change (∑ i, C ((β ∘ q.succAbove) i) * a i) = _ at he
    rw [hap] at he
    have hp : p = C (restrictionOrientation (F := F) σ q) * removeCoordinate q t :=
      mul_left_cancel₀ (negativeDenominator_ne_zero (F := F) (σ ∘ q.succAbove)) he
    apply (Ideal.mem_map_iff_of_surjective
      (removeCoordinate (F := F) q).toRingHom (removeCoordinate_surjective q)).mpr
    refine ⟨C (restrictionOrientation (F := F) σ q) * t,
      Ideal.mul_mem_left _ _ htmem, ?_⟩
    change removeCoordinate q (C (restrictionOrientation (F := F) σ q) * t) = p
    rw [map_mul, removeCoordinate_C]
    exact hp.symm

/-- The deletion inclusion needed in the polynomial spanning induction. -/
theorem mul_deleted_contraction_mem
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (q : Fin n) (hq : 0 < δ q) {p : MvPolynomial (Fin n) F}
    (hp : p ∈ contractionIdeal β (deletedMultiplicity δ q) σ) :
    X q * p ∈ contractionIdeal β δ σ := by
  obtain ⟨a,ha,hap⟩ := hp
  refine ⟨X q • a,(smul_mem_numeratorModule_iff_deleted β δ σ q hq a).mpr ha,?_⟩
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    (∑ i, C (β i) * (X q * a i)) = X q * ∑ i, C (β i) * a i := by
      simp only [Finset.mul_sum,mul_left_comm]
    _ = _ := by rw [hap]; ring

theorem contractionIdeal_eq_top_of_zero_height
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (i : Fin n)
    (hi : δ i + (earlierPositive σ i).card = (earlierNegative σ i).card) :
    contractionIdeal β δ σ = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (columnContraction_mem_contractionIdeal β δ σ hc (singleton_weight_ne_zero β hβ) i)
    (columnContraction_isUnit_of_zero_height β δ σ i hβ hi)

end PaperVerification.Fermion.Newton
