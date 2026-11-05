module

public import PaperVerification.FermionNewtonColumns

/-!
# A denominator-free coefficient calculation for Newton deletion

The negative first-row Schur complement is tested by its highest coefficient
after multiplication by the common nodal polynomial. This is the algebraic
version of the paper's evaluation at infinity. It uses neither analytic
limits nor a claim that the Schur complement is already a constant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators

variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

/-- The numerator of a residue row after multiplication by the full nodal
polynomial. The pole set and active set are disjoint in the actual columns. -/
def clearedResidueRow (y β : ι → L) (positive poles active : Finset ι) : L[X] :=
  ∑ k ∈ active, C (β k) *
    (Lagrange.nodal positive y * Lagrange.nodal (Finset.univ \ insert k poles) y)

theorem nodal_factor_complement (y : ι → L) (poles : Finset ι) (k : ι)
    (hk : k ∉ poles) :
    Lagrange.nodal Finset.univ y =
      Lagrange.nodal poles y * (X - C (y k)) *
        Lagrange.nodal (Finset.univ \ insert k poles) y := by
  have h := Finset.prod_sdiff (f := fun j ↦ (X - C (y j) : L[X]))
    (Finset.subset_univ (insert k poles))
  rw [Finset.prod_insert hk] at h
  change Lagrange.nodal (Finset.univ \ insert k poles) y *
    ((X - C (y k)) * Lagrange.nodal poles y) = Lagrange.nodal Finset.univ y at h
  rw [← h]
  ring

/-- Exact clearing of the denominators in the first-row residue expression. -/
theorem clearedResidueRow_eval (y β : ι → L) (positive poles active : Finset ι)
    (hdisj : Disjoint active poles) (z : L) (hz : ∀ j, z ≠ y j) :
    (clearedResidueRow y β positive poles active).eval z =
      (Lagrange.nodal Finset.univ y).eval z *
        ((Lagrange.nodal positive y).eval z / (Lagrange.nodal poles y).eval z *
          ∑ k ∈ active, β k / (z - y k)) := by
  have hden : (Lagrange.nodal poles y).eval z ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun j hj ↦ hz j)
  rw [clearedResidueRow, eval_finsetSum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ∉ poles := fun h ↦ Finset.disjoint_left.mp hdisj hk h
  have hfac := congrArg (fun p : L[X] ↦ p.eval z) (nodal_factor_complement y poles k hkN)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hfac ⊢
  rw [hfac]
  field_simp [hden, sub_ne_zero.mpr (hz k)]
  <;> ring

theorem nodal_complement_natDegree (y : ι → L) (poles : Finset ι) (k : ι)
    (hk : k ∉ poles) :
    (Lagrange.nodal (Finset.univ \ insert k poles) y).natDegree =
      Fintype.card ι - (poles.card + 1) := by
  rw [Lagrange.natDegree_nodal, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Finset.card_insert_of_notMem hk]

/-- A row of height below two contributes no top coefficient; a row of
height two contributes its complete active weight sum. -/
theorem clearedResidueRow_coeff_card (y β : ι → L) (positive poles active : Finset ι)
    (hdisj : Disjoint active poles) (hheight : positive.card ≤ poles.card + 1) :
    (clearedResidueRow y β positive poles active).coeff (Fintype.card ι) =
      if positive.card = poles.card + 1 then ∑ k ∈ active, β k else 0 := by
  rw [clearedResidueRow, finsetSum_coeff]
  have hterm (k : ι) (hk : k ∈ active) :
      (C (β k) * (Lagrange.nodal positive y *
        Lagrange.nodal (Finset.univ \ insert k poles) y)).coeff (Fintype.card ι) =
      if positive.card = poles.card + 1 then β k else 0 := by
    have hkN : k ∉ poles := fun h ↦ Finset.disjoint_left.mp hdisj hk h
    have hcard : poles.card + 1 ≤ Fintype.card ι := by
      simpa only [Finset.card_insert_of_notMem hkN, Finset.card_univ] using
        Finset.card_le_card (Finset.subset_univ (insert k poles))
    let p := Lagrange.nodal positive y * Lagrange.nodal (Finset.univ \ insert k poles) y
    have hp : p.Monic := Lagrange.nodal_monic.mul Lagrange.nodal_monic
    have hd : p.natDegree = positive.card + (Fintype.card ι - (poles.card + 1)) := by
      dsimp only [p]
      rw [natDegree_mul Lagrange.nodal_monic.ne_zero Lagrange.nodal_monic.ne_zero,
        Lagrange.natDegree_nodal, nodal_complement_natDegree y poles k hkN]
    rw [coeff_C_mul]
    change β k * p.coeff (Fintype.card ι) = _
    by_cases he : positive.card = poles.card + 1
    · have hd' : p.natDegree = Fintype.card ι := by omega
      rw [if_pos he, ← hd', hp.coeff_natDegree, mul_one]
    · have hd' : p.natDegree < Fintype.card ι := by omega
      rw [if_neg he, coeff_eq_zero_of_natDegree_lt hd', mul_zero]
  rw [Finset.sum_congr rfl hterm]
  split_ifs <;> simp

/-- The first column has no earlier signs. Multiplication by the deleted
variable raises its row's degree by one and exposes the full active sum. -/
theorem X_mul_clearedResidueRow_empty_coeff_card
    (y β : ι → L) (active : Finset ι) :
    (X * clearedResidueRow y β ∅ ∅ active).coeff (Fintype.card ι) =
      ∑ k ∈ active, β k := by
  rw [clearedResidueRow, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨k⟩
  have hp : (X * Lagrange.nodal (Finset.univ \ {k}) y).Monic :=
    monic_X.mul Lagrange.nodal_monic
  have hd : (X * Lagrange.nodal (Finset.univ \ {k}) y).natDegree = Fintype.card ι := by
    rw [natDegree_mul monic_X.ne_zero Lagrange.nodal_monic.ne_zero, natDegree_X]
    have h := nodal_complement_natDegree y ∅ k (by simp)
    simp only [Finset.card_empty, zero_add, Finset.insert_empty] at h
    rw [h]
    omega
  rw [show X * (C (β k) * (Lagrange.nodal ∅ y *
      Lagrange.nodal (Finset.univ \ insert k ∅) y)) =
      C (β k) * (X * Lagrange.nodal (Finset.univ \ {k}) y) by
        simp only [Lagrange.nodal, Finset.prod_empty, one_mul, Finset.insert_empty]
        ring,
    coeff_C_mul, ← hd, hp.coeff_natDegree, mul_one]

/-- The exact top coefficient in the cleared Schur numerator. The only
information needed about the suffix expansion is its vanishing above height
two; lower-height coefficients need not be polynomials in the suffix nodes. -/
theorem clearedSchur_coeff_card
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (y β : ι → L) (β₀ : L) (positive poles active : κ → Finset ι)
    (A : κ → L) (firstActive : Finset ι)
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hhigh : ∀ i, (poles i).card + 1 < (positive i).card → A i = 0) :
    (C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ firstActive).coeff (Fintype.card ι) =
      β₀ + (∑ k ∈ firstActive, β k) -
        ∑ i ∈ Finset.univ.filter (fun i ↦ (positive i).card = (poles i).card + 1),
          A i * ∑ k ∈ active i, β k := by
  have hD : (Lagrange.nodal Finset.univ y).coeff (Fintype.card ι) = 1 := by
    simpa only [Lagrange.natDegree_nodal, Finset.card_univ] using
      (Lagrange.nodal_monic (s := Finset.univ) (v := y)).coeff_natDegree
  rw [coeff_add, coeff_sub, coeff_C_mul, hD, mul_one,
    finsetSum_coeff, X_mul_clearedResidueRow_empty_coeff_card]
  have hterm (i : κ) :
      (C (A i) * clearedResidueRow y β (positive i) (poles i) (active i)).coeff
          (Fintype.card ι) =
      if (positive i).card = (poles i).card + 1 then A i * ∑ k ∈ active i, β k else 0 := by
    rw [coeff_C_mul]
    by_cases hh : (positive i).card ≤ (poles i).card + 1
    · rw [clearedResidueRow_coeff_card y β _ _ _ (hdisj i) hh]
      split_ifs <;> simp
    · rw [hhigh i (lt_of_not_ge hh), zero_mul]
      simp
  simp_rw [hterm]
  simp only [Finset.sum_filter]
  ring

/-- If the height-two expansion has one first nonzero coefficient, the
Schur numerator has the indicated nonempty prefix sum as its top
coefficient. This proves nonvanishing before any Cramer argument. -/
theorem clearedSchur_ne_zero_of_first_critical
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (y β : ι → L) (β₀ : L) (positive poles active : κ → Finset ι)
    (A : κ → L) (j : κ)
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hhigh : ∀ i, (poles i).card + 1 < (positive i).card → A i = 0)
    (hj : (positive j).card = (poles j).card + 1)
    (hcritical : ∀ i, (positive i).card = (poles i).card + 1 →
      A i = if i = j then 1 else 0)
    (hβ : β₀ + ∑ k ∈ Finset.univ \ active j, β k ≠ 0) :
    C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ Finset.univ ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun p : L[X] ↦ p.coeff (Fintype.card ι)) hz
  rw [clearedSchur_coeff_card y β β₀ positive poles active A Finset.univ hdisj hhigh,
    coeff_zero] at hcoeff
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i ↦ (positive i).card = (poles i).card + 1),
        A i * ∑ k ∈ active i, β k) = ∑ k ∈ active j, β k := by
    rw [Finset.sum_eq_single j]
    · rw [hcritical j hj, if_pos rfl, one_mul]
    · intro i hi hij
      rw [hcritical i (Finset.mem_filter.mp hi).2, if_neg hij, zero_mul]
    · intro hjnot
      exact False.elim (hjnot (by simp [hj]))
  rw [hsum] at hcoeff
  have hsplit := Finset.sum_sdiff (f := β) (Finset.subset_univ (active j))
  apply hβ
  rw [← hsplit] at hcoeff
  calc
    β₀ + ∑ k ∈ Finset.univ \ active j, β k =
        β₀ + ((∑ k ∈ Finset.univ \ active j, β k) + ∑ k ∈ active j, β k) -
          ∑ k ∈ active j, β k := by ring
    _ = 0 := hcoeff

/-- The alternative case in which the suffix has no height-two index. -/
theorem clearedSchur_ne_zero_of_no_critical
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (y β : ι → L) (β₀ : L) (positive poles active : κ → Finset ι)
    (A : κ → L)
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hhigh : ∀ i, (poles i).card + 1 < (positive i).card → A i = 0)
    (hcritical : ∀ i, (positive i).card ≠ (poles i).card + 1)
    (hβ : β₀ + ∑ k, β k ≠ 0) :
    C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ Finset.univ ≠ 0 := by
  intro hz
  have hcoeff := congrArg (fun p : L[X] ↦ p.coeff (Fintype.card ι)) hz
  rw [clearedSchur_coeff_card y β β₀ positive poles active A Finset.univ hdisj hhigh,
    coeff_zero] at hcoeff
  have hfilter : Finset.univ.filter
      (fun i ↦ (positive i).card = (poles i).card + 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact hcritical i
  rw [hfilter, Finset.sum_empty, sub_zero] at hcoeff
  exact hβ hcoeff

end PaperVerification.Fermion.Newton
