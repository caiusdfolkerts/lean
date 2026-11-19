module

public import PaperVerification.KoszulSyzygies
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Weighted leading components and shifted Koszul relations

All degree bounds are assertions about the actual polynomial coefficients.
The top product identity and the homogeneous first-syzygy lift are proved
for arbitrary nonnegative integer weights and every coefficient ring.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators Pointwise

variable {R ι : Type*} [CommRing R] (w : ι → ℕ)

def Bound (d : ℕ) (p : MvPolynomial ι R) : Prop :=
  ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a ≤ d

def StrictBound (d : ℕ) (p : MvPolynomial ι R) : Prop :=
  ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a < d

theorem bound_zero (d : ℕ) : Bound w d (0 : MvPolynomial ι R) := by simp [Bound]

theorem strictBound_zero (d : ℕ) : StrictBound w d (0 : MvPolynomial ι R) := by simp [StrictBound]

theorem Bound.mono {d e : ℕ} {p : MvPolynomial ι R} (hp : Bound w d p) (hde : d ≤ e) :
    Bound w e p := fun a ha ↦ (hp a ha).trans hde

theorem StrictBound.bound {d : ℕ} {p : MvPolynomial ι R} (hp : StrictBound w d p) :
    Bound w d p := fun a ha ↦ (hp a ha).le

theorem bound_add {d : ℕ} {p q : MvPolynomial ι R} (hp : Bound w d p) (hq : Bound w d q) :
    Bound w d (p + q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp0,zero_add] using ha)
  · exact hp a hp0

theorem bound_sub {d : ℕ} {p q : MvPolynomial ι R} (hp : Bound w d p) (hq : Bound w d q) :
    Bound w d (p - q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [coeff_sub,hp0,zero_sub,neg_ne_zero] using ha)
  · exact hp a hp0

theorem bound_sum {J : Type*} (S : Finset J) (p : J → MvPolynomial ι R) (d : ℕ)
    (hp : ∀ j ∈ S, Bound w d (p j)) : Bound w d (∑ j ∈ S, p j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact bound_add w (hp j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ hp k (Finset.mem_insert_of_mem hk)))

theorem bound_mul {a b : ℕ} {p q : MvPolynomial ι R} (hp : Bound w a p) (hq : Bound w b q) :
    Bound w (a + b) (p * q) := by
  classical
  intro e he
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp
    (support_mul p q (mem_support_iff.mpr he))
  rw [map_add]
  exact add_le_add (hp u (mem_support_iff.mp hu)) (hq v (mem_support_iff.mp hv))

theorem bound_component (d : ℕ) (p : MvPolynomial ι R) :
    Bound w d (weightedHomogeneousComponent w d p) :=
  fun a ha ↦ (weightedHomogeneousComponent_isWeightedHomogeneous d p ha).le

theorem homogeneous_bound {d : ℕ} {p : MvPolynomial ι R} (hp : p.IsWeightedHomogeneous w d) :
    Bound w d p := fun a ha ↦ (hp ha).le

theorem component_zero_of_strict {d : ℕ} {p : MvPolynomial ι R} (hp : StrictBound w d p) :
    weightedHomogeneousComponent w d p = 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  split_ifs with ha
  · by_contra hc
    have hh := hp a hc
    omega
  · rfl

theorem strict_of_bound_component_zero {d : ℕ} {p : MvPolynomial ι R}
    (hp : Bound w d p) (hz : weightedHomogeneousComponent w d p = 0) :
    StrictBound w d p := by
  intro a ha
  have hle := hp a ha
  have hne : Finsupp.weight w a ≠ d := by
    intro he
    have h := congrArg (fun q : MvPolynomial ι R ↦ q.coeff a) hz
    simp only [coeff_weightedHomogeneousComponent,he,if_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at h
    exact ha h
  omega

theorem subtract_component_strict {d : ℕ} {p : MvPolynomial ι R} (hp : Bound w d p) :
    StrictBound w d (p - weightedHomogeneousComponent w d p) := by
  apply strict_of_bound_component_zero w (bound_sub w hp (bound_component w d p))
  rw [map_sub,weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous d p),sub_self]

/-- The highest possible component of a product is the product of the
corresponding components. The coefficient proof needs no domain assumption. -/
theorem component_mul_top {a b : ℕ} {p q : MvPolynomial ι R}
    (hp : Bound w a p) (hq : Bound w b q) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent,coeff_mul,coeff_mul]
  by_cases he : Finsupp.weight w e = a + b
  · rw [if_pos he]
    apply Finset.sum_congr rfl
    intro uv huv
    have hsum := Finset.mem_antidiagonal.mp huv
    have hw : Finsupp.weight w uv.1 + Finsupp.weight w uv.2 = a + b := by
      rw [← map_add,hsum,he]
    by_cases hp0 : p.coeff uv.1 = 0
    · simp [coeff_weightedHomogeneousComponent,hp0]
    by_cases hq0 : q.coeff uv.2 = 0
    · simp [coeff_weightedHomogeneousComponent,hq0]
    have ha := hp uv.1 hp0
    have hb := hq uv.2 hq0
    have hea : Finsupp.weight w uv.1 = a := by omega
    have heb : Finsupp.weight w uv.2 = b := by omega
    simp only [coeff_weightedHomogeneousComponent,hea,heb,if_true]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro uv huv
    have hsum := Finset.mem_antidiagonal.mp huv
    by_cases ha : Finsupp.weight w uv.1 = a
    · have hb : Finsupp.weight w uv.2 ≠ b := by
        intro hb
        apply he
        rw [← hsum,map_add,ha,hb]
      simp only [coeff_weightedHomogeneousComponent,ha,if_true,if_neg hb,mul_zero]
    · simp only [coeff_weightedHomogeneousComponent,if_neg ha,zero_mul]

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem component_mul_homogeneous {d : ℕ} {q : MvPolynomial ι R}
    (hq : q.IsWeightedHomogeneous w d) (p : MvPolynomial ι R) (D : ℕ) :
    weightedHomogeneousComponent w D (p * q) =
      if d ≤ D then weightedHomogeneousComponent w (D - d) p * q else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (weightedHomogeneousSubmodule R w) D (a := p) hq
  have key (a : MvPolynomial ι R) (j : ℕ) :
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) a j : MvPolynomial ι R) =
        weightedHomogeneousComponent w j a :=
    weightedDecomposition.decompose'_apply R w a j
  simpa only [key] using h

def shiftedProjection (s D : ℕ) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  if s ≤ D then weightedHomogeneousComponent w (D - s) else 0

theorem shiftedProjection_mul {q : MvPolynomial ι R} {d : ℕ}
    (hq : q.IsWeightedHomogeneous w d) (s D : ℕ) (p : MvPolynomial ι R) :
    shiftedProjection w s D (p * q) = shiftedProjection w (s + d) D p * q := by
  by_cases hs : s ≤ D
  · rw [shiftedProjection,if_pos hs,component_mul_homogeneous w hq]
    by_cases hd : d ≤ D - s
    · have hsd : s + d ≤ D := by omega
      simp only [if_pos hd,shiftedProjection,if_pos hsd,Nat.sub_sub]
    · have hsd : ¬s + d ≤ D := by omega
      simp only [if_neg hd,shiftedProjection,if_neg hsd,LinearMap.zero_apply,zero_mul]
  · have hsd : ¬s + d ≤ D := by omega
    simp only [shiftedProjection,if_neg hs,if_neg hsd,LinearMap.zero_apply,zero_mul]

theorem shiftedProjection_idempotent (s D : ℕ) (p : MvPolynomial ι R) :
    shiftedProjection w s D (shiftedProjection w s D p) = shiftedProjection w s D p := by
  unfold shiftedProjection
  split_ifs
  · exact weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  · simp only [LinearMap.zero_apply]

theorem shiftedProjection_homogeneous (s D : ℕ) (p : MvPolynomial ι R) :
    (shiftedProjection w s D p).IsWeightedHomogeneous w (D - s) := by
  unfold shiftedProjection
  split_ifs
  · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem shiftedProjection_eq_zero_of_lt (s D : ℕ) (h : D < s) (p : MvPolynomial ι R) :
    shiftedProjection w s D p = 0 := by
  simp only [shiftedProjection,if_neg (Nat.not_le.mpr h),LinearMap.zero_apply]

/-- Every homogeneous first relation has a homogeneous alternating-matrix
preimage, with all low-degree zero cases included. -/
theorem homogeneous_first_syzygy {m : ℕ}
    (g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (degree i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (D : ℕ) (a : Fin m → MvPolynomial ι R)
    (ha : ∀ i, shiftedProjection w (degree i) D (a i) = a i)
    (hz : KoszulSyzygies.coefficient g a = 0) :
    ∃ B : Fin m → Fin m → MvPolynomial ι R,
      (∀ i j, shiftedProjection w (degree i + degree j) D (B i j) = B i j) ∧
      KoszulSyzygies.boundary g B = a := by
  have hm : a ∈ LinearMap.range (KoszulSyzygies.boundary g) := by
    rw [← KoszulSyzygies.kernel_eq_boundary_range g hreg]
    exact hz
  obtain ⟨A,hA⟩ := hm
  let B := fun i j ↦ shiftedProjection w (degree i + degree j) D (A i j)
  refine ⟨B,fun i j ↦ shiftedProjection_idempotent w _ _ _,?_⟩
  funext i
  calc
    KoszulSyzygies.boundary g B i =
        shiftedProjection w (degree i) D (KoszulSyzygies.boundary g A i) := by
      simp only [KoszulSyzygies.boundary_apply,map_sum,map_sub]
      apply Finset.sum_congr rfl
      intro j hj
      conv_rhs => rw [mul_comm (g j),shiftedProjection_mul w (hg j),map_sub]
      simp only [B,Nat.add_comm (degree j) (degree i),mul_comm]
    _ = shiftedProjection w (degree i) D (a i) := by rw [hA]
    _ = a i := ha i

end PaperVerification.Fermion.Filtered
