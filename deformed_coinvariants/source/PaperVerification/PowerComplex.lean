module

public import PaperVerification.PowerHomogeneity
public import PaperVerification.KoszulSyzygies
public import Mathlib.LinearAlgebra.Pi

/-!
# The genuine two-map deformation complex for power tails

These are the first two maps in the proof of Theorem 2.2. The second map includes
the characteristic-recurrence correction to the noncommuting Koszul relations.
The composite vanishes for all coefficients and parameters over every
commutative ring. At slope zero, the maps are the actual first Koszul maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R

def tailMap (c : Fin n → R) (lam : R) (m : ℕ) : (Fin n → P) →ₗ[R] P where
  toFun v := ∑ i, reversed c lam (m+i.val) (v i)
  map_add' v w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r v := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem tailMap_apply (c : Fin n → R) (lam : R) (m : ℕ) (v : Fin n → P) :
    tailMap c lam m v = ∑ i, reversed c lam (m+i.val) (v i) := rfl

@[simp] theorem tailMap_single (c : Fin n → R) (lam : R) (m : ℕ)
    (i : Fin n) (p : P) :
    tailMap c lam m (Pi.single i p) = reversed c lam (m+i.val) p := by
  classical
  rw [tailMap_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j hj hji
    simp only [Pi.single_eq_of_ne hji, map_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

def recurrenceVector (m : ℕ) (i j : Fin n) : P →ₗ[R] (Fin n → P) :=
  LinearMap.pi fun l => LinearMap.mulLeft R
    (homogeneousTailCoefficient (m+i.val+j.val) l)

@[simp] theorem recurrenceVector_apply (m : ℕ) (i j l : Fin n) (p : P) :
    recurrenceVector m i j p l = homogeneousTailCoefficient (m+i.val+j.val) l * p := rfl

theorem tailMap_recurrenceVector (c : Fin n → R) (lam : R) (m : ℕ)
    (i j : Fin n) (p : P) :
    tailMap c lam m (recurrenceVector m i j p) =
      reversed c lam ((m+i.val)+(m+j.val)) p := by
  rw [tailMap_apply]
  simp only [recurrenceVector_apply]
  rw [← reversed_homogeneous_tail_recurrence]
  congr 2
  omega

def elementarySyzygy (c : Fin n → R) (lam : R) (m : ℕ) (i j : Fin n) :
    P →ₗ[R] (Fin n → P) :=
  (LinearMap.single R (fun _ : Fin n => P) i).comp (reversed c lam (m+j.val)) -
  (LinearMap.single R (fun _ : Fin n => P) j).comp (reversed c lam (m+i.val)) -
  (lam * ((j.val : R) - (i.val : R))) • recurrenceVector m i j

@[simp] theorem elementarySyzygy_apply (c : Fin n → R) (lam : R) (m : ℕ)
    (i j : Fin n) (p : P) :
    elementarySyzygy c lam m i j p =
      Pi.single i (reversed c lam (m+j.val) p) -
      Pi.single j (reversed c lam (m+i.val) p) -
      (lam * ((j.val : R) - (i.val : R))) • recurrenceVector m i j p := rfl

theorem tailMap_elementarySyzygy (c : Fin n → R) (lam : R) (m : ℕ)
    (i j : Fin n) (p : P) : tailMap c lam m (elementarySyzygy c lam m i j p) = 0 := by
  rw [elementarySyzygy_apply, map_sub, map_sub, map_smul,
    tailMap_single, tailMap_single, tailMap_recurrenceVector, reversed_commutator]
  have he : lam * (((m+j.val : ℕ) : R) - ((m+i.val : ℕ) : R)) =
      lam * ((j.val : R) - (i.val : R)) := by push_cast; ring
  rw [he, sub_self]

/-- Ordered pairs avoid choosing an ordering or dividing by two. The redundancy
does not change the image, including in characteristic two. -/
def syzygyMap (c : Fin n → R) (lam : R) (m : ℕ) :
    (Fin n → Fin n → P) →ₗ[R] (Fin n → P) where
  toFun A := ∑ i, ∑ j, elementarySyzygy c lam m i j (A j i)
  map_add' A B := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r A := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem syzygyMap_apply (c : Fin n → R) (lam : R) (m : ℕ)
    (A : Fin n → Fin n → P) :
    syzygyMap c lam m A = ∑ i, ∑ j, elementarySyzygy c lam m i j (A j i) := rfl

/-- The polynomial deformation really is a complex; this is not a hypothesis
passed to the rank-specialization theorem. -/
theorem tailMap_syzygyMap (c : Fin n → R) (lam : R) (m : ℕ)
    (A : Fin n → Fin n → P) : tailMap c lam m (syzygyMap c lam m A) = 0 := by
  simp only [syzygyMap_apply, map_sum, tailMap_elementarySyzygy, Finset.sum_const_zero]

theorem tailMap_comp_syzygyMap (c : Fin n → R) (lam : R) (m : ℕ) :
    (tailMap c lam m).comp (syzygyMap c lam m) = 0 := by
  apply LinearMap.ext
  intro A
  exact tailMap_syzygyMap c lam m A

def weightedPower (c : Fin n → R) (k : ℕ) : P :=
  ∑ i, C (c i) * X i ^ k

theorem reversed_zero_slope (c : Fin n → R) (k : ℕ) (p : P) :
    reversed c 0 k p = weightedPower c k * p := by
  simp only [reversed_apply, component_apply, zero_mul, add_zero, zero_smul,
    weightedPower, Finset.sum_mul, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tailMap_zero_slope (c : Fin n → R) (m : ℕ) (v : Fin n → P) :
    tailMap c 0 m v = KoszulSyzygies.coefficient (fun i => weightedPower c (m+i.val)) v := by
  simp only [tailMap_apply, reversed_zero_slope, KoszulSyzygies.coefficient_apply, mul_comm]

theorem syzygyMap_zero_slope (c : Fin n → R) (m : ℕ) (A : Fin n → Fin n → P) :
    syzygyMap c 0 m A = KoszulSyzygies.boundary (fun i => weightedPower c (m+i.val)) A := by
  classical
  funext l
  simp only [syzygyMap_apply, elementarySyzygy_apply, zero_mul, zero_smul,
    sub_zero, reversed_zero_slope, Finset.sum_apply, Pi.sub_apply,
    Finset.sum_sub_distrib, KoszulSyzygies.boundary_apply, mul_sub]
  have hfirst : (∑ i, ∑ j, Pi.single i (weightedPower c (m+j.val) * A j i) l) =
      ∑ j, weightedPower c (m+j.val) * A j l := by
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  have hsecond : (∑ i, ∑ j, Pi.single j (weightedPower c (m+i.val) * A j i) l) =
      ∑ i, weightedPower c (m+i.val) * A l i := by simp [Pi.single_apply]
  rw [hfirst, hsecond]

/-- Exactness of the zero-slope fiber follows from the literal weakly regular
weighted-power sequence. Later applications establish this regularity from
nonzero subset sums of the independent coefficient indeterminates. -/
theorem zero_slope_exact_of_regular (c : Fin n → R) (m : ℕ)
    (hf : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin n => weightedPower c (m+i.val))) :
    LinearMap.range (syzygyMap c 0 m) = LinearMap.ker (tailMap c 0 m) := by
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  simp only [syzygyMap_zero_slope, tailMap_zero_slope]
  have he := KoszulSyzygies.kernel_eq_boundary_range
    (fun i : Fin n => weightedPower c (m+i.val)) hf
  exact (SetLike.ext_iff.mp he v).symm

end PaperVerification.PowerOperators
