module

public import Continuation.Runtime.R10MatroidData
public import Continuation.Runtime.RationalClosure
public import Continuation.Runtime.IncidenceRank
public import Continuation.Runtime.SparseDet
public import Continuation.R10.All
public import Mathlib.Combinatorics.Matroid.Dual
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false

section



set_option backward.isDefEq.respectTransparency false

/-!
# Maximality of the standard integral R₁₀ configuration

Every vector that can be appended to `[I₅ | B]` while preserving total
unimodularity is zero or parallel, with coefficient ±1, to an existing column.
The finite certificate concerns only a bounded coordinate vector; the final
theorem quantifies over every integral vector and every square minor.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Unimodular.R10Maximality


def covectors : Fin 14 → Fin 5 → ℤ :=
  ![![0,1,-1,1,-1], ![1,0,1,-1,-1], ![0,0,1,1,-1], ![0,1,0,-1,0],
    ![0,1,1,0,-1], ![0,1,-1,1,0], ![1,0,0,1,-1], ![1,0,-1,0,0],
    ![1,0,1,-1,0], ![1,1,0,0,-1], ![1,-1,0,-1,0], ![1,-1,0,-1,1],
    ![1,-1,1,0,0], ![1,-1,1,0,-1]]

def decode (w : Fin 5 → Fin 3) : Fin 5 → ℤ := fun i ↦ ((w i).val : ℤ) - 1

def Constraints (v : Fin 5 → ℤ) : Prop :=
  ∀ t, -1 ≤ ∑ i, covectors t i * v i ∧ (∑ i, covectors t i * v i) ≤ 1

def OldLine (v : Fin 5 → ℤ) : Prop :=
  v = 0 ∨ ∃ j, v = rays j ∨ v = -rays j

theorem finite_certificate :
    ∀ w : Fin 5 → Fin 3, Constraints (decode w) → OldLine (decode w) := by
  unfold Constraints OldLine
  decide +kernel

theorem maximal_of_constraints (v : Fin 5 → ℤ)
    (hc : ∀ i, -1 ≤ v i ∧ v i ≤ 1) (h : Constraints v) : OldLine v := by
  let w : Fin 5 → Fin 3 := fun i ↦ ⟨(v i + 1).toNat, by have := hc i; omega⟩
  have hw : decode w = v := by
    funext i
    change ((v i + 1).toNat : ℤ) - 1 = v i
    have := hc i
    omega
  rw [← hw] at h ⊢
  exact finite_certificate w h

def quartet : Fin 14 → Fin 4 → Fin 10 :=
  ![![0,5,8,9], ![1,5,6,9], ![1,0,6,8], ![0,2,4,9], ![3,0,5,7],
    ![4,0,6,7], ![2,1,5,7], ![1,3,4,9], ![1,4,7,8], ![2,3,6,8],
    ![4,2,5,8], ![2,6,7,9], ![3,4,5,6], ![3,7,8,9]]

def coordinateQuartet : Fin 5 → Fin 4 → Fin 10 :=
  ![![1,2,3,4], ![2,0,3,4], ![0,1,3,4], ![1,0,2,4], ![0,1,2,3]]

def minor (q : Fin 4 → Fin 10) (v : Fin 5 → ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j ↦ if h : j.val < 4 then rays (q ⟨j.val, h⟩) i else v i

def cofactor (q : Fin 4 → Fin 10) (i : Fin 5) : ℤ :=
  (-1) ^ ((i : ℕ) + 4) *
    Matrix.det ((minor q 0).submatrix i.succAbove (4 : Fin 5).succAbove)

lemma minor_last_col (q : Fin 4 → Fin 10) (v : Fin 5 → ℤ) (i : Fin 5) :
    minor q v i 4 = v i := rfl

lemma minor_submatrix (q : Fin 4 → Fin 10) (i : Fin 5) (v : Fin 5 → ℤ) :
    (minor q v).submatrix i.succAbove (4 : Fin 5).succAbove =
      (minor q 0).submatrix i.succAbove (4 : Fin 5).succAbove := by
  ext a b
  fin_cases b <;> rfl

lemma det_minor_formula (q : Fin 4 → Fin 10) (v : Fin 5 → ℤ) :
    Matrix.det (minor q v) = ∑ i, cofactor q i * v i := by
  rw [Matrix.det_succ_column _ (4 : Fin 5)]
  apply Finset.sum_congr rfl
  intro i _
  rw [minor_last_col, minor_submatrix]
  norm_num [cofactor] <;> ring

theorem quartet_cofactors :
    ∀ t i, cofactor (quartet t) i = covectors t i := by decide +kernel

theorem coordinate_cofactors :
    ∀ k i, cofactor (coordinateQuartet k) i = if i = k then 1 else 0 := by
  decide +kernel

lemma quartet_minor (t : Fin 14) (v : Fin 5 → ℤ) :
    Matrix.det (minor (quartet t) v) = ∑ i, covectors t i * v i := by
  simp_rw [det_minor_formula, quartet_cofactors]

lemma coordinate_minor (k : Fin 5) (v : Fin 5 → ℤ) :
    Matrix.det (minor (coordinateQuartet k) v) = v k := by
  simp [det_minor_formula, coordinate_cofactors]

theorem maximal_of_minors (v : Fin 5 → ℤ)
    (h : ∀ q : Fin 4 → Fin 10, |Matrix.det (minor q v)| ≤ 1) : OldLine v := by
  apply maximal_of_constraints v
  · intro i
    have hi := h (coordinateQuartet i)
    rw [coordinate_minor] at hi
    exact abs_le.mp hi
  · intro t
    have ht := h (quartet t)
    rw [quartet_minor] at ht
    exact abs_le.mp ht

def extend (v : Fin 5 → ℤ) : Matrix (Fin 5) (Option (Fin 10)) ℤ :=
  fun i j ↦ match j with | none => v i | some j => rays j i

theorem maximal_of_totallyUnimodular (v : Fin 5 → ℤ)
    (h : (extend v).IsTotallyUnimodular) : OldLine v := by
  apply maximal_of_minors v
  intro q
  let g : Fin 5 → Option (Fin 10) :=
    fun j ↦ if hj : j.val < 4 then some (q ⟨j.val, hj⟩) else none
  have hg : (extend v).submatrix id g = minor q v := by
    ext i j
    by_cases hj : j.val < 4 <;>
      simp [extend, g, minor, Matrix.submatrix_apply, hj]
  have ht := (Matrix.isTotallyUnimodular_iff _).mp h 5 id g
  rw [hg] at ht
  obtain ⟨s, hs⟩ := ht
  rw [← hs]
  cases s <;> norm_num


theorem block_binary : ∀ i j, block i j = 0 ∨ block i j = 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [block]

theorem block_last_row : ∀ i, block 4 i = 1 := by decide +kernel
theorem block_last_col : ∀ i, block i 4 = 1 := by decide +kernel

lemma sign_of_abs_one {x : ℤ} (h : |x| = 1) : x = 1 ∨ x = -1 := by
  rcases le_total 0 x with hx | hx
  · left; rwa [abs_of_nonneg hx] at h
  · right; rw [abs_of_nonpos hx] at h; omega

lemma sign_corner (a b c d : ℤ)
    (ha : |a| = 1) (hb : |b| = 1) (hc : |c| = 1) (hd : |d| = 1)
    (h : |a*b-c*d| ≤ 1) : c*a*d*b = 1 := by
  rcases sign_of_abs_one ha with rfl | rfl <;>
  rcases sign_of_abs_one hb with rfl | rfl <;>
  rcases sign_of_abs_one hc with rfl | rfl <;>
  rcases sign_of_abs_one hd with rfl | rfl <;>
  norm_num at *

theorem signed_block_normalization (A : Matrix (Fin 5) (Fin 5) ℤ)
    (hsupp : ∀ i j, |A i j| = block i j)
    (hcorner : ∀ i j, |A i j*A 4 4 - A i 4*A 4 j| ≤ 1) :
    (fun i j ↦ A i 4 * A i j * (A 4 j * A 4 4)) = block := by
  funext i j
  have hb : |A 4 4| = 1 := (hsupp 4 4).trans (block_last_row 4)
  have hc : |A i 4| = 1 := (hsupp i 4).trans (block_last_col i)
  have hd : |A 4 j| = 1 := (hsupp 4 j).trans (block_last_row j)
  rcases block_binary i j with hz | ho
  · have ha : A i j = 0 := abs_eq_zero.mp ((hsupp i j).trans hz)
    simp [ha, hz]
  · have ha : |A i j| = 1 := (hsupp i j).trans ho
    calc
      A i 4 * A i j * (A 4 j * A 4 4) = A i 4*A i j*A 4 j*A 4 4 := by ring
      _ = 1 := sign_corner _ _ _ _ ha hb hc hd (hcorner i j)
      _ = block i j := ho.symm

#print axioms maximal_of_totallyUnimodular
#print axioms signed_block_normalization
end Unimodular.R10Maximality
end

section



set_option backward.isDefEq.respectTransparency false

namespace Unimodular.R10Maximality
open Unimodular.FiniteMatrixCertificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block_minor_certificate : ∀ s t h,
    |laplaceDet s.card (filteredMinor block s t h)| ≤ 1 := by
  decide +kernel

theorem block_totallyUnimodular : block.IsTotallyUnimodular := by
  apply totallyUnimodular_of_orderedMinors
  intro s t h
  rw [← sortedMinor_eq_orderedMinor, ← filteredMinor_eq_sortedMinor, ← laplaceDet_eq_det]
  exact block_minor_certificate s t h

def canonicalIndex : Fin 10 → Fin 5 ⊕ Fin 5 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
    Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4]

theorem rays_as_block :
    (fun i j ↦ rays j i) =
      ((1 : Matrix (Fin 5) (Fin 5) ℤ).fromCols block).submatrix id canonicalIndex := by
  decide +kernel

theorem rays_totallyUnimodular : Matrix.IsTotallyUnimodular (fun i j ↦ rays j i) := by
  rw [rays_as_block]
  apply Matrix.IsTotallyUnimodular.submatrix
  exact (Matrix.one_fromCols_isTotallyUnimodular_iff block).mpr block_totallyUnimodular

#print axioms rays_totallyUnimodular
end Unimodular.R10Maximality
end

section



set_option backward.isDefEq.respectTransparency false

/-!
# Bases surviving deletion of three R₁₀ elements

The listed nineteen bases cover every deletion of at most three labels. The
proof checks the covering statement and each determinant in the Lean kernel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Unimodular.R10Maximality
open Unimodular.RepresentationBridge Unimodular.FiniteMatrixCertificates

def robustBases : Fin 19 → Fin 5 → Fin 10 :=
  ![![0,1,2,3,4], ![0,1,5,6,7], ![0,2,5,8,9], ![1,3,6,8,9],
    ![2,4,6,7,8], ![0,3,4,7,9], ![1,2,3,5,7], ![1,4,5,6,9],
    ![3,4,5,6,8], ![0,1,4,7,8], ![0,2,3,6,7], ![0,2,4,6,9],
    ![3,5,7,8,9], ![1,2,4,7,9], ![0,1,2,6,8], ![0,1,2,3,9],
    ![0,4,5,7,8], ![1,3,4,5,9], ![2,5,6,7,9]]

theorem robustBases_injective : ∀ k, Function.Injective (robustBases k) := by
  unfold Function.Injective
  decide +kernel

theorem robustBases_det :
    ∀ k, Matrix.det (fun i j ↦ rays (robustBases k j) i) ≠ 0 := by
  have h : ∀ k, sparseDet 5 (fun i j ↦ rays (robustBases k j) i) ≠ 0 := by
    decide +kernel
  simpa only [sparseDet_eq_det] using h

theorem robustBases_avoid :
    ∀ d : Finset (Fin 10), d.card ≤ 3 → ∃ k, ∀ i, robustBases k i ∉ d := by
  decide +kernel

/-- Every pair of labels occurs in one of the listed ordinary bases. -/
theorem robustBases_contains_pair :
    ∀ i j : Fin 10, ∃ k a b,
      robustBases k a = i ∧ robustBases k b = j := by
  decide +kernel

theorem robustBases_isBase_real (k : Fin 19) :
    (VectorMatroid.ofFamily (K := ℝ) (fun j i ↦ (rays j i : ℝ))).IsBase
      (Set.range (robustBases k)) := by
  rw [ofFamily_isBase_range_iff_det ℝ _ _ (robustBases_injective k)]
  let A : Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦ rays (robustBases k j) i
  change (A.map (fun z : ℤ ↦ (z : ℝ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast robustBases_det k

theorem small_deletion_has_base (d : Finset (Fin 10)) (hd : d.card ≤ 3) :
    ∃ k, (VectorMatroid.ofFamily (K := ℝ) (fun j i ↦ (rays j i : ℝ))).IsBase
      (Set.range (robustBases k)) ∧ ∀ i, robustBases k i ∉ d := by
  obtain ⟨k, hk⟩ := robustBases_avoid d hd
  exact ⟨k, robustBases_isBase_real k, hk⟩

#print axioms small_deletion_has_base
end Unimodular.R10Maximality
end

section



/-! # Endpoint counts for finite incidence families -/

open scoped BigOperators
namespace Unimodular.R10Maximality

def endpoints {V : Type*} [DecidableEq V] (a b : Fin 10 → V) : Finset V :=
  Finset.univ.image a ∪ Finset.univ.image b

lemma mem_endpoints_left {V : Type*} [DecidableEq V]
    (a b : Fin 10 → V) (j : Fin 10) : a j ∈ endpoints a b := by
  simp [endpoints]

lemma mem_endpoints_right {V : Type*} [DecidableEq V]
    (a b : Fin 10 → V) (j : Fin 10) : b j ∈ endpoints a b := by
  simp [endpoints]

lemma incidence_ne_zero_iff {V : Type*} [DecidableEq V] (a b v : V) (hne : a ≠ b) :
    ((if v = a then 1 else 0) - (if v = b then 1 else 0) : ℤ) ≠ 0 ↔
      v = a ∨ v = b := by
  by_cases ha : v = a <;> by_cases hb : v = b <;> simp_all

theorem incidence_degree_sum {V : Type*} [DecidableEq V]
    (a b : Fin 10 → V) (hne : ∀ j, a j ≠ b j) :
    (∑ v ∈ endpoints a b, (Finset.univ.filter (fun j ↦ v = a j ∨ v = b j)).card) =
      20 := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hsum (j : Fin 10) :
      (∑ v ∈ endpoints a b, if v = a j ∨ v = b j then 1 else 0) = (2 : ℕ) := by
    have hp (v : V) :
        (if v = a j ∨ v = b j then 1 else 0 : ℕ) =
          (if v = a j then 1 else 0) + (if v = b j then 1 else 0) := by
      by_cases ha : v = a j
      · subst v
        simp [hne j]
      · by_cases hb : v = b j
        · subst v
          simp [Ne.symm (hne j)]
        · simp [ha, hb]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    simp [mem_endpoints_left, mem_endpoints_right]
  simp_rw [hsum]
  norm_num

end Unimodular.R10Maximality
end

section



set_option backward.isDefEq.respectTransparency false

/-!
# The ordinary R₁₀ matroid is not graphic

The argument quantifies over arbitrary vertex sets and every directed incidence
family. It uses only equality of the represented ordinary matroids, with no
linear equivalence between the two representations assumed.
-/

namespace Unimodular.R10Maximality
open Set Submodule Unimodular.RepresentationBridge

theorem rays_has_unit_coordinate : ∀ j, ∃ i, rays j i = 1 := by decide +kernel

lemma realRays_nonzero (j : Fin 10) : realRays j ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := rays_has_unit_coordinate j
  have hh := congrFun h i
  norm_num [realRays, hi] at hh

def incidenceFamily {V : Type*} [DecidableEq V] (a b : Fin 10 → V) :
    Fin 10 → V → ℝ :=
  fun j v ↦ (if v = a j then 1 else 0) - (if v = b j then 1 else 0)

theorem no_graphic_family {V : Type*} [DecidableEq V] (a b : Fin 10 → V)
    (hM : r10Matroid = VectorMatroid.ofFamily (K := ℝ) (incidenceFamily a b)) : False := by
  let u := incidenceFamily a b
  have hne (j : Fin 10) : a j ≠ b j := by
    intro he
    have hi : r10Matroid.Indep {j} :=
      (VectorMatroid.ofFamily_indep realRays _).mpr
        ((linearIndepOn_singleton_iff ℝ).mpr (realRays_nonzero j))
    rw [hM, VectorMatroid.ofFamily_indep, linearIndepOn_singleton_iff] at hi
    exact hi (by ext v; simp [incidenceFamily, he])
  let t := endpoints a b
  let degree (v : V) : ℕ := (Finset.univ.filter (fun j ↦ v = a j ∨ v = b j)).card
  have hlarge_degree (v : V) (hv : v ∈ t) : 4 ≤ degree v := by
    by_contra hn
    let d : Finset (Fin 10) := Finset.univ.filter (fun j ↦ v = a j ∨ v = b j)
    have hd : d.card ≤ 3 := by change ¬ 4 ≤ d.card at hn; omega
    obtain ⟨k, hb, hk⟩ := small_deletion_has_base d hd
    change r10Matroid.IsBase (Set.range (robustBases k)) at hb
    rw [hM] at hb
    have hs := (ofFamily_isBase_iff ℝ u _).mp hb
    have hzero (i : Fin 5) : u (robustBases k i) v = 0 := by
      have hi := hk i
      simp only [d, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
      simp [u, incidenceFamily, hi.1, hi.2]
    have hspan : span ℝ (u '' Set.range (robustBases k)) ≤
        LinearMap.ker (LinearMap.proj v : (V → ℝ) →ₗ[ℝ] ℝ) := by
      apply span_le.mpr
      rintro _ ⟨j, ⟨i, rfl⟩, rfl⟩
      exact hzero i
    have hzero_all (j : Fin 10) : u j v = 0 := hspan (hs.2 j)
    change v ∈ Finset.univ.image a ∪ Finset.univ.image b at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      have hh := hzero_all j
      simp [u, incidenceFamily, hne j] at hh
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      have hh := hzero_all j
      simp [u, incidenceFamily, Ne.symm (hne j)] at hh
  have hsmall : t.card ≤ 5 := by
    have hb : 4 * t.card ≤ 20 := calc
      4 * t.card = ∑ v ∈ t, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ t, degree v := Finset.sum_le_sum hlarge_degree
      _ = 20 := incidence_degree_sum a b hne
    omega
  have hb : (VectorMatroid.ofFamily (K := ℝ) u).IsBase
      (Set.range (robustBases 0)) := by
    rw [← hM]
    exact robustBases_isBase_real 0
  have hli : LinearIndependent ℝ (u ∘ robustBases 0) :=
    (linearIndepOn_range_iff (robustBases_injective 0) u).mp
      ((VectorMatroid.ofFamily_indep u _).mp hb.indep)
  let L : (Fin 5 → ℝ) →ₗ[ℝ] (V → ℝ) :=
    (Pi.basisFun ℝ (Fin 5)).constr ℝ (u ∘ robustBases 0)
  have hinj : Function.Injective L :=
    (Pi.basisFun ℝ (Fin 5)).injective_constr_of_linearIndependent hli
  have hexp (z : Fin 5 → ℝ) (v : V) :
      L z v = ∑ i, z i * u (robustBases 0 i) v := by
    simp [L, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcol_support (j : Fin 10) (v : V) (hv : v ∉ t) : u j v = 0 := by
    have hna : v ≠ a j := by rintro rfl; exact hv (mem_endpoints_left a b j)
    have hnb : v ≠ b j := by rintro rfl; exact hv (mem_endpoints_right a b j)
    simp [u, incidenceFamily, hna, hnb]
  have hcol_sum (j : Fin 10) : (∑ v ∈ t, u j v) = 0 := by
    simp only [u, incidenceFamily]
    rw [Finset.sum_sub_distrib]
    simp [t, mem_endpoints_left, mem_endpoints_right]
  have hsupport (z : Fin 5 → ℝ) (v : V) (hv : v ∉ t) : L z v = 0 := by
    rw [hexp]
    apply Finset.sum_eq_zero
    intro i _
    rw [hcol_support _ v hv, mul_zero]
  have hsum (z : Fin 5 → ℝ) : (∑ v ∈ t, L z v) = 0 := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol_sum, mul_zero]
    simp
  have hlarge := Unimodular.IncidenceRank.dimension_lt_support_card
    L hinj t (a 0) (mem_endpoints_left a b 0) hsupport hsum
  omega

#print axioms no_graphic_family
end Unimodular.R10Maximality
end

section


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Every nontrivial R₁₀ separation has connectivity at least three

Twenty-one pairs of ordinary bases give a finite certificate. The certificate
is transferred to every representation of the same ordinary matroid over any
field, so it can be used directly in a binary port-space argument.
-/

namespace Unimodular.R10Maximality
open Set Submodule Unimodular.RepresentationBridge Unimodular.FiniteMatrixCertificates

def separationBases : Fin 21 → Fin 2 → Fin 5 → Fin 10 :=
  ![
    ![![0,1,2,4,7], ![3,5,6,8,9]],
    ![![0,1,2,5,8], ![3,4,6,7,9]],
    ![![0,1,2,6,9], ![3,4,5,7,8]],
    ![![0,1,4,8,9], ![2,3,5,6,7]],
    ![![0,2,4,6,8], ![1,3,5,7,9]],
    ![![0,1,6,7,8], ![0,2,4,5,9]],
    ![![1,3,4,5,6], ![2,3,7,8,9]],
    ![![0,5,6,7,9], ![1,2,3,4,8]],
    ![![0,1,2,3,6], ![2,4,5,7,8]],
    ![![0,3,4,5,7], ![1,2,6,7,9]],
    ![![0,1,3,7,8], ![1,2,4,5,9]],
    ![![0,2,3,4,9], ![1,4,6,7,8]],
    ![![0,1,2,5,7], ![1,3,4,8,9]],
    ![![0,4,6,7,9], ![2,3,5,6,8]],
    ![![0,1,2,3,4], ![0,5,6,8,9]],
    ![![0,2,3,7,9], ![1,4,5,6,7]],
    ![![0,1,3,4,6], ![2,4,7,8,9]],
    ![![0,1,5,8,9], ![2,3,4,6,9]],
    ![![0,3,5,7,8], ![1,2,5,6,9]],
    ![![0,2,3,4,5], ![1,2,6,7,8]],
    ![![0,1,2,3,4], ![0,4,5,6,7]]]

def separationLabels (k : Fin 21) (b : Fin 2) : Finset (Fin 10) :=
  Finset.univ.image (separationBases k b)

theorem separationBases_injective :
    ∀ k b, Function.Injective (separationBases k b) := by
  unfold Function.Injective
  decide +kernel

theorem separationBases_det :
    ∀ k b, Matrix.det (fun i j ↦ rays (separationBases k b j) i) ≠ 0 := by
  have h : ∀ k b, sparseDet 5 (fun i j ↦ rays (separationBases k b j) i) ≠ 0 := by
    decide +kernel
  simpa only [sparseDet_eq_det] using h

/-- Base-21 digits select one of the 21 explicitly displayed pairs of bases.
This is only a proposed witness table: its entire required property is checked
by the kernel in `separation_choice_certificate` below. -/
private def separationWitnessTable : ℕ := 9781633205303705312026642618603021125049117088004374030924672404984345803894310883064745326919663006023257459116554532431613157186506623895551626539931756001473928713228445374372745734658265605292331155127637194136965466512914986625185759995734686739661818442543166759488478160238209350367751494851463356054634641052526264208869096425410717376487553887821370241879325474457765923624583793294461509168315276400930015447331343991018569474277378186158150920443403105613278163579014800697343755613424220678940107614400128736629346757038396358762526779499234714522567343194386679065980952846491574507168773219739272251969169549476054417310804666150278573525934889189420257604676834543437350152961577897019768357297284947235482463616728993877140970307074263135999061427432514810639136234369287066217150253472166584156655292957615358902130356047885964414826989654189347242204034432209819851138240577586161945001470642670310658113445257585355933852298334539984507813383023349427968525643736964436144492269022371919000391871966046926660109541598969415869698316017521625440931659963383442108901298112841520430103216022658736004193430364704073637273676096364602337252822839957030328035280999721211074629606371003878344203509924226912572654681598990634918063428618515093053026184450830961494977006538917856633753070183565479313744735299276354534009530

private def subsetOfBits (b : Fin 1024) : Finset (Fin 10) :=
  Finset.univ.filter (fun i ↦ (BitVec.ofFin (w := 10) b).getLsbD i.val)

private theorem subsetOfBits_injective : Function.Injective subsetOfBits := by
  intro a b h
  have he : BitVec.ofFin (w := 10) a = BitVec.ofFin (w := 10) b := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    have hm := Eq.to_iff (congrArg (fun s : Finset (Fin 10) ↦ (⟨i, hi⟩ : Fin 10) ∈ s) h)
    simpa [subsetOfBits] using hm
  exact congrArg BitVec.toFin he

private theorem subsetOfBits_surjective : Function.Surjective subsetOfBits :=
  ((Fintype.bijective_iff_injective_and_card subsetOfBits).mpr
    ⟨subsetOfBits_injective, by norm_num [Fintype.card_finset]⟩).2

private def separationChoice (b : Fin 1024) : Fin 21 :=
  Fin.ofNat 21 (separationWitnessTable / 21 ^ b.val)

private theorem separation_choice_certificate :
    ∀ b : Fin 1024, 3 ≤ (subsetOfBits b).card → 3 ≤ (subsetOfBits b)ᶜ.card →
      8 ≤ (separationLabels (separationChoice b) 0 ∩ subsetOfBits b).card +
        (separationLabels (separationChoice b) 1 ∩ (subsetOfBits b)ᶜ).card ∨
      8 ≤ (separationLabels (separationChoice b) 1 ∩ subsetOfBits b).card +
        (separationLabels (separationChoice b) 0 ∩ (subsetOfBits b)ᶜ).card := by
  decide +kernel

theorem separation_certificate :
    ∀ s : Finset (Fin 10), 3 ≤ s.card → 3 ≤ sᶜ.card →
      ∃ k, 8 ≤ (separationLabels k 0 ∩ s).card +
        (separationLabels k 1 ∩ sᶜ).card ∨
        8 ≤ (separationLabels k 1 ∩ s).card +
          (separationLabels k 0 ∩ sᶜ).card := by
  intro s hs ht
  obtain ⟨b, rfl⟩ := subsetOfBits_surjective s
  exact ⟨separationChoice b, separation_choice_certificate b hs ht⟩


theorem separationBases_isBase (k : Fin 21) (b : Fin 2) :
    r10Matroid.IsBase (Set.range (separationBases k b)) := by
  rw [r10Matroid, ofFamily_isBase_range_iff_det ℝ _ _
    (separationBases_injective k b)]
  let A : Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦ rays (separationBases k b j) i
  change (A.map (fun z : ℤ ↦ (z : ℝ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast separationBases_det k b

section ArbitraryRepresentation
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  (v : Fin 10 → W)
  (hM : r10Matroid = VectorMatroid.ofFamily (K := K) v)

include hM

lemma robustBases_independent : ∀ k,
    LinearIndependent K (v ∘ robustBases k) := by
  intro k
  have hb := robustBases_isBase_real k
  change r10Matroid.IsBase (Set.range (robustBases k)) at hb
  rw [hM] at hb
  exact (linearIndepOn_range_iff (robustBases_injective k) v).mp
    ((VectorMatroid.ofFamily_indep v _).mp hb.indep)

theorem representation_nonzero (e : Fin 10) : v e ≠ 0 := by
  obtain ⟨k, a, b, ha, _⟩ := robustBases_contains_pair e e
  simpa only [Function.comp_apply, ha] using (robustBases_independent v hM k).ne_zero a

theorem representation_injective : Function.Injective v := by
  intro i j hij
  obtain ⟨k, a, b, ha, hb⟩ := robustBases_contains_pair i j
  have hab : a = b := (robustBases_independent v hM k).injective
    (by simpa only [Function.comp_apply, ha, hb] using hij)
  exact ha.symm.trans ((congrArg (robustBases k) hab).trans hb)

theorem realization_span_rank :
    Module.finrank K (span K (Set.range v)) = 5 := by
  have hb := separationBases_isBase 0 0
  rw [hM] at hb
  have hs := (ofFamily_isBase_iff K v _).mp hb
  have hli : LinearIndependent K (v ∘ separationBases 0 0) :=
    (linearIndepOn_range_iff (separationBases_injective 0 0) v).mp hs.1
  have heq : span K (Set.range v) = span K (Set.range (v ∘ separationBases 0 0)) := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨e, rfl⟩
      rw [Set.range_comp]
      exact hs.2 e
    · exact span_mono (Set.range_comp_subset_range _ _)
  rw [heq, finrank_span_eq_card hli]
  simp

omit hM in
lemma independent_card_le_span_rank (I s : Finset (Fin 10))
    (hI : LinearIndepOn K v (I : Set (Fin 10))) (hIs : I ⊆ s) :
    I.card ≤ Module.finrank K (span K (v '' (s : Set (Fin 10)))) := by
  letI : FiniteDimensional K (span K (v '' (s : Set (Fin 10)))) :=
    FiniteDimensional.span_of_finite K (s.finite_toSet.image v)
  have hi : Module.finrank K (span K (v '' (I : Set (Fin 10)))) = I.card := by
    rw [Set.image_eq_range]
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using finrank_span_eq_card hI
  rw [← hi]
  exact Submodule.finrank_mono (span_mono
    (Set.image_mono (Finset.coe_subset.mpr hIs)))

lemma separation_inter_card_le (k : Fin 21) (b : Fin 2) (s : Finset (Fin 10)) :
    (separationLabels k b ∩ s).card ≤
      Module.finrank K (span K (v '' (s : Set (Fin 10)))) := by
  have hb := separationBases_isBase k b
  rw [hM] at hb
  have hi : LinearIndepOn K v (separationLabels k b : Set (Fin 10)) := by
    simpa [separationLabels] using (VectorMatroid.ofFamily_indep v _).mp hb.indep
  apply independent_card_le_span_rank v _ s
  · exact hi.mono (Finset.coe_subset.mpr Finset.inter_subset_left)
  · exact Finset.inter_subset_right

theorem separation_intersection_dimension (s : Finset (Fin 10))
    (hs : 3 ≤ s.card) (ht : 3 ≤ sᶜ.card) :
    3 ≤ Module.finrank K
      (span K (v '' (s : Set (Fin 10))) ⊓
        span K (v '' (sᶜ : Finset (Fin 10)) : Set W) : Submodule K W) := by
  let A := span K (v '' (s : Set (Fin 10)))
  let B := span K (v '' (sᶜ : Finset (Fin 10)) : Set W)
  letI : FiniteDimensional K A :=
    FiniteDimensional.span_of_finite K (s.finite_toSet.image v)
  letI : FiniteDimensional K B :=
    FiniteDimensional.span_of_finite K (sᶜ.finite_toSet.image v)
  have hsup : A ⊔ B = span K (Set.range v) := by
    dsimp [A, B]
    rw [← span_union, ← Set.image_union]
    simp
  have hdim := A.finrank_sup_add_finrank_inf_eq B
  rw [hsup, realization_span_rank v hM] at hdim
  have hbound : 8 ≤ Module.finrank K A + Module.finrank K B := by
    obtain ⟨k, hk | hk⟩ := separation_certificate s hs ht
    · exact hk.trans (Nat.add_le_add
        (separation_inter_card_le v hM k 0 s)
        (separation_inter_card_le v hM k 1 sᶜ))
    · exact hk.trans (Nat.add_le_add
        (separation_inter_card_le v hM k 1 s)
        (separation_inter_card_le v hM k 0 sᶜ))
  change 3 ≤ Module.finrank K (A ⊓ B : Submodule K W)
  omega

theorem small_side_of_intersection_dimension (s : Finset (Fin 10))
    (hport : Module.finrank K
      (span K (v '' (s : Set (Fin 10))) ⊓
        span K (v '' (sᶜ : Finset (Fin 10)) : Set W) : Submodule K W) ≤ 2) :
    s.card ≤ 2 ∨ sᶜ.card ≤ 2 := by
  by_contra h
  have hs : 3 ≤ s.card := by omega
  have ht : 3 ≤ sᶜ.card := by omega
  have hh := separation_intersection_dimension v hM s hs ht
  omega

theorem complement_spans_of_small (s : Finset (Fin 10)) (hs : s.card ≤ 3) :
    span K (v '' (sᶜ : Finset (Fin 10)) : Set W) = span K (Set.range v) := by
  obtain ⟨k, hb, hk⟩ := small_deletion_has_base s hs
  change r10Matroid.IsBase (Set.range (robustBases k)) at hb
  rw [hM] at hb
  have hspan := (ofFamily_isBase_iff K v _).mp hb
  apply le_antisymm (span_mono (Set.image_subset_range _ _))
  apply span_le.mpr
  rintro _ ⟨e, rfl⟩
  apply (span_mono (Set.image_mono ?_)) (hspan.2 e)
  rintro j ⟨i, rfl⟩
  simpa using hk i

end ArbitraryRepresentation

#print axioms separation_intersection_dimension
#print axioms complement_spans_of_small
end Unimodular.R10Maximality

end

section



set_option backward.isDefEq.respectTransparency false

/-!
# Self-duality of the ordinary represented R₁₀ matroid

The finite test uses integer determinants. Its equivalence to bases of the
ordinary real vector matroid is proved before the certificate is used.
-/

namespace Unimodular.R10Maximality

open Set Function Submodule
open Unimodular.RepresentationBridge Unimodular.FiniteMatrixCertificates
open scoped Matroid

lemma realRays_basis (i : Fin 5) :
    realRays (Fin.castAdd 5 i) = Pi.basisFun ℝ (Fin 5) i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [realRays, rays, Pi.basisFun_apply, Pi.single_apply]

lemma realRays_span : span ℝ (range realRays) = ⊤ := by
  apply le_antisymm le_top
  calc
    ⊤ = span ℝ (range (Pi.basisFun ℝ (Fin 5))) :=
      (Pi.basisFun ℝ (Fin 5)).span_eq.symm
    _ ≤ span ℝ (range realRays) := span_mono (by
      rintro x ⟨i, rfl⟩
      exact ⟨Fin.castAdd 5 i, realRays_basis i⟩)

def basisMatrix (s : Finset (Fin 10)) (h : s.card = 5) :
    Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦ rays (enumerate s h j) i

def basisTest (s : Finset (Fin 10)) : Prop :=
  if h : s.card = 5 then sparseDet 5 (basisMatrix s h) ≠ 0 else False

theorem r10_isBase_iff_test (s : Finset (Fin 10)) :
    r10Matroid.IsBase (s : Set (Fin 10)) ↔ basisTest s := by
  classical
  unfold basisTest
  split_ifs with hs
  · have hchar := ofFamily_isBase_range_iff_det ℝ realRays
      (enumerate s hs) (enumerate_injective s hs)
    rw [range_enumerate] at hchar
    change (VectorMatroid.ofFamily (K := ℝ) realRays).IsBase (s : Set (Fin 10)) ↔ _
    rw [hchar, sparseDet_eq_det]
    change ((basisMatrix s hs).map (fun z : ℤ ↦ (z : ℝ))).det ≠ 0 ↔ _
    rw [← Int.cast_det]
    simp
  · exact iff_false_intro (fun hB ↦ hs
      ((ofFamily_isBase_iff_card ℝ realRays realRays_span s).mp hB).2)

def swapReflect : Equiv.Perm (Fin 10) where
  toFun := ![5,8,7,6,9,0,3,2,1,4]
  invFun := ![5,8,7,6,9,0,3,2,1,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basis_duality_certificate :
    ∀ s : Finset (Fin 10),
      basisTest sᶜ ↔ basisTest (s.map swapReflect.symm.toEmbedding) := by
  unfold basisTest
  decide +kernel

theorem r10_selfdual : r10Matroid✶ = r10Matroid.mapEquiv swapReflect := by
  classical
  apply Matroid.ext_isBase (by simp [r10Matroid])
  intro B hB
  let s : Finset (Fin 10) := B.toFinset
  have hc : r10Matroid.E \ B = ((sᶜ : Finset (Fin 10)) : Set (Fin 10)) := by
    simp [r10Matroid, s, compl_eq_univ_sdiff]
  have hm : swapReflect.symm '' B =
      ((s.map swapReflect.symm.toEmbedding : Finset (Fin 10)) : Set (Fin 10)) := by
    simp [s]
  rw [Matroid.dual_isBase_iff (by simp [r10Matroid]),
    Matroid.mapEquiv_isBase_iff, hc, hm, r10_isBase_iff_test, r10_isBase_iff_test]
  exact basis_duality_certificate s

#print axioms r10_selfdual
end Unimodular.R10Maximality
end

section



set_option backward.isDefEq.respectTransparency false

/-! # The self-dual R₁₀ obstruction is also not cographic -/

open scoped Matroid

namespace Unimodular.R10Maximality
open Unimodular.RepresentationBridge

theorem no_cographic_family {V : Type*} [DecidableEq V] (a b : Fin 10 → V)
    (hM : r10Matroid = (VectorMatroid.ofFamily (K := ℝ) (incidenceFamily a b))✶) :
    False := by
  have hd : r10Matroid.mapEquiv swapReflect =
      VectorMatroid.ofFamily (K := ℝ) (incidenceFamily a b) := by
    rw [← r10_selfdual, hM, Matroid.dual_dual]
  have hm := congrArg (fun M : Matroid (Fin 10) ↦ M.mapEquiv swapReflect.symm) hd
  rw [mapEquiv_symm_cancel, ofFamily_mapEquiv] at hm
  exact no_graphic_family (a ∘ swapReflect) (b ∘ swapReflect) hm

#print axioms no_cographic_family
end Unimodular.R10Maximality
end
