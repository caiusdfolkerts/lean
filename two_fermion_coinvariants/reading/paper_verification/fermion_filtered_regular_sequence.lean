module

public import PaperVerification.FermionWeightedLeading

/-!
# Complete leading-form reduction for a perturbed regular sequence

An arbitrary representation of a polynomial in the perturbed ideal is
corrected by a genuine Koszul boundary whenever its largest shifted degree
cancels. The measure decreases strictly. Consequently every ideal element
has a representation bounded by its own weighted degree, and its leading
component belongs to the homogeneous regular-sequence ideal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators Pointwise

variable {R ι : Type*} [CommRing R] (w : ι → ℕ)

def ShiftBound (s D : ℕ) (p : MvPolynomial ι R) : Prop :=
  ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a + s ≤ D

theorem ShiftBound.bound {s D : ℕ} {p : MvPolynomial ι R} (hp : ShiftBound w s D p) :
    Bound w (D - s) p := by
  intro a ha
  have h := hp a ha
  omega

theorem ShiftBound.mono {s D E : ℕ} {p : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hDE : D ≤ E) : ShiftBound w s E p :=
  fun a ha ↦ (hp a ha).trans hDE

theorem ShiftBound.eq_zero_of_lt {s D : ℕ} {p : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hDs : D < s) : p = 0 := by
  ext a
  by_contra ha
  have h := hp a (by simpa only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using ha)
  omega

theorem shiftBound_zero (s D : ℕ) : ShiftBound w s D (0 : MvPolynomial ι R) := by simp [ShiftBound]

theorem shiftBound_add {s D : ℕ} {p q : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hq : ShiftBound w s D q) : ShiftBound w s D (p + q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp0,zero_add] using ha)
  · exact hp a hp0

theorem shiftBound_sub {s D : ℕ} {p q : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hq : ShiftBound w s D q) : ShiftBound w s D (p - q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [coeff_sub,hp0,zero_sub,neg_ne_zero] using ha)
  · exact hp a hp0

theorem shiftBound_sum {J : Type*} (S : Finset J) (p : J → MvPolynomial ι R) (s D : ℕ)
    (hp : ∀ j ∈ S, ShiftBound w s D (p j)) : ShiftBound w s D (∑ j ∈ S, p j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using shiftBound_zero w s D
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact shiftBound_add w (hp j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ hp k (Finset.mem_insert_of_mem hk)))

theorem shiftBound_mul {s d D : ℕ} {p q : MvPolynomial ι R}
    (hp : ShiftBound w (s + d) D p) (hq : Bound w d q) : ShiftBound w s D (p * q) := by
  classical
  intro e he
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp
    (support_mul p q (mem_support_iff.mpr he))
  rw [map_add]
  have h1 := hp u (mem_support_iff.mp hu)
  have h2 := hq v (mem_support_iff.mp hv)
  omega

theorem shiftBound_projection (s D : ℕ) (p : MvPolynomial ι R) :
    ShiftBound w s D (shiftedProjection w s D p) := by
  by_cases hs : s ≤ D
  · rw [shiftedProjection,if_pos hs]
    intro a ha
    have he := weightedHomogeneousComponent_isWeightedHomogeneous (D - s) p ha
    omega
  · rw [shiftedProjection_eq_zero_of_lt w s D (Nat.lt_of_not_ge hs)]
    exact shiftBound_zero w s D

theorem shiftBound_of_fixed_projection {s D : ℕ} {p : MvPolynomial ι R}
    (hp : shiftedProjection w s D p = p) : ShiftBound w s D p := by
  rw [← hp]
  exact shiftBound_projection w s D p

theorem shifted_component_product {s D : ℕ} {p f g : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hf : Bound w s f)
    (hg : weightedHomogeneousComponent w s f = g) :
    weightedHomogeneousComponent w D (p * f) = shiftedProjection w s D p * g := by
  by_cases hs : s ≤ D
  · have hD : D = (D - s) + s := by omega
    conv_lhs => rw [hD,component_mul_top w (hp.bound w) hf,hg]
    simp only [shiftedProjection,if_pos hs]
  · have hp0 := hp.eq_zero_of_lt w (Nat.lt_of_not_ge hs)
    simp only [hp0,zero_mul,map_zero]

theorem shiftedProjection_mul_deformed {s d D : ℕ} {p f g : MvPolynomial ι R}
    (hp : shiftedProjection w (s + d) D p = p) (hf : Bound w d f)
    (hg : weightedHomogeneousComponent w d f = g) :
    shiftedProjection w s D (p * f) = p * g := by
  by_cases hsd : s + d ≤ D
  · have hs : s ≤ D := by omega
    have hhom := shiftedProjection_homogeneous w (s + d) D p
    rw [hp] at hhom
    have hdeg : D - s = (D - (s + d)) + d := by omega
    rw [shiftedProjection,if_pos hs,hdeg,
      component_mul_top w (homogeneous_bound w hhom) hf,
      weightedHomogeneousComponent_eq_self hhom,hg]
  · have hp0 : p = 0 := by
      rw [← hp,shiftedProjection_eq_zero_of_lt w (s + d) D (Nat.lt_of_not_ge hsd)]
    simp only [hp0,zero_mul,map_zero]

theorem shiftBound_lower_of_projection_zero {s D : ℕ} {p : MvPolynomial ι R}
    (hp : ShiftBound w s D p) (hz : shiftedProjection w s D p = 0) :
    ShiftBound w s (D - 1) p := by
  intro a ha
  have hle := hp a ha
  have hs : s ≤ D := by omega
  have hne : Finsupp.weight w a + s ≠ D := by
    intro he
    have hw : Finsupp.weight w a = D - s := by omega
    have hc := congrArg (fun q : MvPolynomial ι R ↦ q.coeff a) hz
    simp only [shiftedProjection,if_pos hs,coeff_weightedHomogeneousComponent,hw,
      if_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
    exact ha hc
  omega

variable {m : ℕ}

theorem shifted_top_coefficient
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (D : ℕ) (a : Fin m → MvPolynomial ι R)
    (ha : ∀ i, ShiftBound w (degree i) D (a i)) :
    weightedHomogeneousComponent w D (KoszulSyzygies.coefficient f a) =
      KoszulSyzygies.coefficient g (fun i ↦ shiftedProjection w (degree i) D (a i)) := by
  simp only [KoszulSyzygies.coefficient_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ shifted_component_product w (ha i) (hf i) (hg i))

theorem perturbed_boundary_bound
    (f : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i)) (D : ℕ)
    (B : Fin m → Fin m → MvPolynomial ι R)
    (hB : ∀ i j, shiftedProjection w (degree i + degree j) D (B i j) = B i j) (i : Fin m) :
    ShiftBound w (degree i) D (KoszulSyzygies.boundary f B i) := by
  apply shiftBound_sum w Finset.univ _ _ _
  intro j hj
  rw [mul_comm]
  apply shiftBound_mul w
  · exact shiftBound_sub w
      (by simpa only [Nat.add_comm] using shiftBound_of_fixed_projection w (hB j i))
      (shiftBound_of_fixed_projection w (hB i j))
  · exact hf j

theorem perturbed_boundary_top
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i) (D : ℕ)
    (B : Fin m → Fin m → MvPolynomial ι R)
    (hB : ∀ i j, shiftedProjection w (degree i + degree j) D (B i j) = B i j) (i : Fin m) :
    shiftedProjection w (degree i) D (KoszulSyzygies.boundary f B i) =
      KoszulSyzygies.boundary g B i := by
  simp only [KoszulSyzygies.boundary_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (f j),shiftedProjection_mul_deformed w]
  · exact mul_comm _ _
  · rw [map_sub,hB i j]
    congr 1
    simpa only [Nat.add_comm] using hB j i
  · exact hf j
  · exact hg j

/-- The terminating cancellation of all excess shifted degrees. -/
theorem bounded_representation_of_representation
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (p : MvPolynomial ι R) (N : ℕ) (hp : Bound w N p)
    (D : ℕ) (a : Fin m → MvPolynomial ι R)
    (ha : ∀ i, ShiftBound w (degree i) D (a i))
    (he : KoszulSyzygies.coefficient f a = p) :
    ∃ b : Fin m → MvPolynomial ι R,
      (∀ i, ShiftBound w (degree i) N (b i)) ∧ KoszulSyzygies.coefficient f b = p := by
  induction D using Nat.strong_induction_on generalizing a with
  | _ D ih =>
      by_cases hDN : D ≤ N
      · exact ⟨a,fun i ↦ (ha i).mono w hDN,he⟩
      · have hND : N < D := Nat.lt_of_not_ge hDN
        let t := fun i ↦ shiftedProjection w (degree i) D (a i)
        have ht : KoszulSyzygies.coefficient g t = 0 := by
          rw [← shifted_top_coefficient w f g degree hf hg D a ha,he]
          apply component_zero_of_strict w
          intro e he
          exact (hp e he).trans_lt hND
        have hhom (i : Fin m) : (g i).IsWeightedHomogeneous w (degree i) := by
          rw [← hg i]
          exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
        obtain ⟨B,hB,hBt⟩ := homogeneous_first_syzygy w g degree hhom hreg D t
          (fun i ↦ shiftedProjection_idempotent w _ _ _) ht
        let a' := a - KoszulSyzygies.boundary f B
        have ha' (i : Fin m) : ShiftBound w (degree i) (D - 1) (a' i) := by
          apply shiftBound_lower_of_projection_zero w
          · exact shiftBound_sub w (ha i) (perturbed_boundary_bound w f degree hf D B hB i)
          · change shiftedProjection w (degree i) D (a i - KoszulSyzygies.boundary f B i) = 0
            rw [map_sub,perturbed_boundary_top w f g degree hf hg D B hB,hBt]
            exact sub_self _
        have he' : KoszulSyzygies.coefficient f a' = p := by
          dsimp only [a']
          rw [map_sub,KoszulSyzygies.coefficient_boundary,sub_zero,he]
        exact ih (D - 1) (by omega) a' ha' he'

/-- A regular sequence of actual highest forms gives bounded ideal
representations for every polynomial in the perturbed ideal. -/
theorem bounded_representation
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (p : MvPolynomial ι R) (N : ℕ) (hp : Bound w N p)
    (hI : p ∈ Ideal.span (Set.range f)) :
    ∃ a : Fin m → MvPolynomial ι R,
      (∀ i, ShiftBound w (degree i) N (a i)) ∧ KoszulSyzygies.coefficient f a = p := by
  classical
  have hrange : p ∈ LinearMap.range (KoszulSyzygies.coefficient f) := by
    simpa only [KoszulSyzygies.coefficient,Fintype.range_linearCombination] using hI
  obtain ⟨a,ha⟩ := hrange
  let D := ∑ i, (weightedTotalDegree w (a i) + degree i)
  have hbound (i : Fin m) : ShiftBound w (degree i) D (a i) := by
    intro e he
    have hdeg := le_weightedTotalDegree w (mem_support_iff.mpr he)
    have hsum := Finset.single_le_sum (fun j _ ↦ Nat.zero_le
      (weightedTotalDegree w (a j) + degree j)) (Finset.mem_univ i)
    exact (Nat.add_le_add_right hdeg (degree i)).trans hsum
  exact bounded_representation_of_representation w f g degree hf hg hreg p N hp D a hbound ha

/-- The complete initial-ideal containment needed in Section 6.1. It is
derived from regularity and actual leading forms, not postulated as flatness. -/
theorem leading_component_mem_homogeneous_ideal
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (p : MvPolynomial ι R) (D : ℕ) (hp : Bound w D p)
    (hI : p ∈ Ideal.span (Set.range f)) :
    weightedHomogeneousComponent w D p ∈ Ideal.span (Set.range g) := by
  obtain ⟨a,ha,he⟩ := bounded_representation w f g degree hf hg hreg p D hp hI
  rw [← he,shifted_top_coefficient w f g degree hf hg D a ha,KoszulSyzygies.coefficient_apply]
  exact Ideal.sum_mem _ (fun i hi ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩))

end PaperVerification.Fermion.Filtered
