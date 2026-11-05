module

public import PaperVerification.FermionFilteredBasis
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Regularity lifts from actual weighted highest forms

The quotient-regularity step subtracts a bounded lift of the highest
homogeneous component, strictly decreasing weighted degree. Applying that
step to every prefix proves regularity of the original sequence over an
arbitrary commutative coefficient ring. The weights may be zero; no field,
Noetherian, flatness, or finite-dimensionality hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators

variable {R ι : Type*} [CommRing R] (w : ι → ℕ) {m : ℕ}

/-- A regular highest form is regular modulo the actual deformed ideal. -/
theorem regular_quotient_of_regular_highest
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (a a₀ : MvPolynomial ι R) (e : ℕ) (ha : Bound w e a)
    (ha₀ : weightedHomogeneousComponent w e a = a₀)
    (hreg₀ : IsSMulRegular (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) a₀) :
    IsSMulRegular (MvPolynomial ι R ⧸ Ideal.span (Set.range f)) a := by
  classical
  have hhom (i : Fin m) : (g i).IsWeightedHomogeneous w (degree i) := by
    rw [← hg i]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hstep : ∀ D : ℕ, ∀ p : MvPolynomial ι R, Bound w D p →
      a * p ∈ Ideal.span (Set.range f) → p ∈ Ideal.span (Set.range f) := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro p hp hpI
      have htop := leading_component_mem_homogeneous_ideal w f g degree hf hg hreg
        (a * p) (e + D) (bound_mul w ha hp) hpI
      rw [component_mul_top w ha hp, ha₀] at htop
      have hmem : weightedHomogeneousComponent w D p ∈ Ideal.span (Set.range g) :=
        (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span (Set.range g)) a₀).mp
          hreg₀ _ (by simpa only [smul_eq_mul] using htop)
      have hrange : weightedHomogeneousComponent w D p ∈
          LinearMap.range (KoszulSyzygies.coefficient g) := by
        simpa only [KoszulSyzygies.coefficient, Fintype.range_linearCombination] using hmem
      obtain ⟨b, hb⟩ := hrange
      let b' := fun i ↦ shiftedProjection w (degree i) D (b i)
      have hb' : KoszulSyzygies.coefficient g b' = weightedHomogeneousComponent w D p := by
        rw [← component_homogeneous_coefficient w g degree hhom b D, hb]
        exact weightedHomogeneousComponent_eq_self
          (weightedHomogeneousComponent_isWeightedHomogeneous D p)
      let q := KoszulSyzygies.coefficient f b'
      have hbound (i : Fin m) : ShiftBound w (degree i) D (b' i) :=
        shiftBound_projection w (degree i) D (b i)
      have hqbound : Bound w D q := coefficient_bound w f degree hf D b' hbound
      have hqtop : weightedHomogeneousComponent w D q =
          weightedHomogeneousComponent w D p := by
        rw [shifted_top_coefficient w f g degree hf hg D b' hbound]
        have hid : (fun i ↦ shiftedProjection w (degree i) D (b' i)) = b' := by
          funext i
          exact shiftedProjection_idempotent w (degree i) D (b i)
        rw [hid, hb']
      have hqI : q ∈ Ideal.span (Set.range f) := by
        change (∑ i, b' i * f i) ∈ Ideal.span (Set.range f)
        exact Ideal.sum_mem _ (fun i _ ↦
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
      have hstrict : StrictBound w D (p - q) := by
        apply strict_of_bound_component_zero w (bound_sub w hp hqbound)
        rw [map_sub, hqtop, sub_self]
      have hpqI : a * (p - q) ∈ Ideal.span (Set.range f) := by
        rw [mul_sub]
        exact (Ideal.span (Set.range f)).sub_mem hpI
          (Ideal.mul_mem_left _ a hqI)
      have hpq : p - q ∈ Ideal.span (Set.range f) := by
        by_cases hD : D = 0
        · have hz : p - q = 0 := strictBound_zero_eq_zero w (by simpa only [hD] using hstrict)
          rw [hz]
          exact Ideal.zero_mem _
        · apply ih (D - 1) (by omega) (p - q) _ hpqI
          intro u hu
          have := hstrict u hu
          omega
      simpa only [sub_add_cancel] using (Ideal.span (Set.range f)).add_mem hpq hqI
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span (Set.range f)) a).mpr
  intro p hp
  exact hstep _ p (bound_weightedTotalDegree w p) (by simpa only [smul_eq_mul] using hp)

/-- The list-generated ideal of a finite tuple is its actual range span. -/
theorem ideal_ofList_ofFn (v : Fin m → MvPolynomial ι R) :
    Ideal.ofList (List.ofFn v) = Ideal.span (Set.range v) := by
  unfold Ideal.ofList
  congr 1
  ext p
  exact List.mem_ofFn' v p

/-- Every prefix is handled separately, so no permutation or finite-colength
argument is smuggled into the regularity conclusion. -/
theorem weaklyRegular_of_regular_highest
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g)) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn f) := by
  constructor
  intro i hi
  have hi' : i < m := by simpa only [List.length_ofFn] using hi
  have hle : i ≤ m := hi'.le
  have hprefix : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R)
      ((List.ofFn g).take i) := by
    apply ((RingTheory.Sequence.isWeaklyRegular_append_iff (MvPolynomial ι R)
      ((List.ofFn g).take i) ((List.ofFn g).drop i)).mp _).1
    simpa only [List.take_append_drop] using hreg
  rw [← Fin.ofFn_take_eq_take_ofFn hle g] at hprefix
  have hnext := hreg.regular_mod_prev i (by simpa only [List.length_ofFn] using hi')
  rw [← Fin.ofFn_take_eq_take_ofFn hle g, ideal_ofList_ofFn,
    Ideal.smul_eq_mul, Ideal.mul_top] at hnext
  have hnext' : IsSMulRegular
      (MvPolynomial ι R ⧸ Ideal.span (Set.range (Fin.take i hle g))) (g ⟨i, hi'⟩) := by
    simpa only [List.getElem_ofFn] using hnext
  rw [← Fin.ofFn_take_eq_take_ofFn hle f, ideal_ofList_ofFn,
    Ideal.smul_eq_mul, Ideal.mul_top]
  simpa only [List.getElem_ofFn] using
    regular_quotient_of_regular_highest w (Fin.take i hle f) (Fin.take i hle g)
      (Fin.take i hle degree) (fun j ↦ hf (j.castLE hle))
      (fun j ↦ hg (j.castLE hle)) hprefix (f ⟨i, hi'⟩) (g ⟨i, hi'⟩)
      (degree ⟨i, hi'⟩) (hf ⟨i, hi'⟩) (hg ⟨i, hi'⟩) hnext'

/-- Properness survives because the highest component of `1` is `1`. -/
theorem span_ne_top_of_regular_highest
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (hproper : Ideal.span (Set.range g) ≠ ⊤) : Ideal.span (Set.range f) ≠ ⊤ := by
  intro htop
  have hI : (1 : MvPolynomial ι R) ∈ Ideal.span (Set.range f) := by rw [htop]; trivial
  have h := leading_component_mem_homogeneous_ideal w f g degree hf hg hreg 1 0
    (homogeneous_bound w (isWeightedHomogeneous_one R w)) hI
  rw [weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one R w)] at h
  exact hproper (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)

/-- The original sequence is regular, with the usual nonzero-quotient clause,
whenever its actual highest forms are regular. -/
theorem regular_of_regular_highest
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial ι R) (List.ofFn g)) :
    RingTheory.Sequence.IsRegular (MvPolynomial ι R) (List.ofFn f) := by
  refine ⟨weaklyRegular_of_regular_highest w f g degree hf hg hreg.toIsWeaklyRegular, ?_⟩
  have hgproper : Ideal.span (Set.range g) ≠ ⊤ := by
    have h := hreg.top_ne_smul
    rw [ideal_ofList_ofFn, Ideal.smul_eq_mul, Ideal.mul_top] at h
    exact Ne.symm h
  rw [ideal_ofList_ofFn, Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ne.symm (span_ne_top_of_regular_highest w f g degree hf hg hreg.toIsWeaklyRegular hgproper)

end PaperVerification.Fermion.Filtered
