module

public import PaperVerification.FermionNewtonSchur

/-!
# The cleared Schur polynomial is the actual rational Schur complement

This bridge is valid for every injective polynomial specialization into a
field. In particular it applies to the fresh variable in the successive
fraction fields, and proves rational nonvanishing from the exact nonzero
top coefficient established in `FermionNewtonSchur`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators

variable {L E ι : Type*} [Field L] [Field E] [Fintype ι] [DecidableEq ι]

theorem map_nodal_eq_eval (φ : L[X] →+* E) (y : ι → L) (s : Finset ι) :
    φ (Lagrange.nodal s y) =
      (Lagrange.nodal s (fun i ↦ φ (C (y i)))).eval (φ X) := by
  simp only [Lagrange.nodal, map_prod, map_sub, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

def specializedResidueRow (φ : L[X] →+* E) (y β : ι → L)
    (positive poles active : Finset ι) : E :=
  φ (Lagrange.nodal positive y) / φ (Lagrange.nodal poles y) *
    ∑ k ∈ active, φ (C (β k)) / (φ X - φ (C (y k)))

theorem map_nodal_ne_zero (φ : L[X] →+* E) (y : ι → L)
    (hlinear : ∀ k, φ X - φ (C (y k)) ≠ 0) (s : Finset ι) :
    φ (Lagrange.nodal s y) ≠ 0 := by
  simp only [Lagrange.nodal, map_prod, map_sub]
  exact Finset.prod_ne_zero_iff.mpr (fun k hk ↦ hlinear k)

theorem map_clearedResidueRow (φ : L[X] →+* E) (y β : ι → L)
    (positive poles active : Finset ι) (hdisj : Disjoint active poles)
    (hlinear : ∀ k, φ X - φ (C (y k)) ≠ 0) :
    φ (clearedResidueRow y β positive poles active) =
      φ (Lagrange.nodal Finset.univ y) * specializedResidueRow φ y β positive poles active := by
  have hden := map_nodal_ne_zero φ y hlinear poles
  rw [clearedResidueRow, map_sum, specializedResidueRow, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ∉ poles := fun h ↦ Finset.disjoint_left.mp hdisj hk h
  have hfac := congrArg φ (nodal_factor_complement y poles k hkN)
  simp only [map_mul, map_sub] at hfac ⊢
  rw [hfac]
  field_simp [hden, hlinear k]
  <;> ring

def specializedSchur
    {κ : Type*} [Fintype κ] (φ : L[X] →+* E) (y β : ι → L) (β₀ : L)
    (positive poles active : κ → Finset ι) (A : κ → L) (firstActive : Finset ι) : E :=
  1 - ∑ i, (specializedResidueRow φ y β (positive i) (poles i) (active i) / φ (C β₀)) * φ (C (A i)) +
    φ X * (specializedResidueRow φ y β ∅ ∅ firstActive / φ (C β₀))

/-- The complete numerator identity; all denominator cancellations are
justified by the stated genuine nonvanishing conditions. -/
theorem specializedSchur_clear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : L[X] →+* E) (y β : ι → L) (β₀ : L)
    (positive poles active : κ → Finset ι) (A : κ → L) (firstActive : Finset ι)
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hlinear : ∀ k, φ X - φ (C (y k)) ≠ 0) (hβ₀ : φ (C β₀) ≠ 0) :
    (φ (C β₀) * φ (Lagrange.nodal Finset.univ y)) *
        specializedSchur φ y β β₀ positive poles active A firstActive =
      φ (C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ firstActive) := by
  have hrow (i : κ) :
      φ (Lagrange.nodal Finset.univ y) *
        specializedResidueRow φ y β (positive i) (poles i) (active i) =
      φ (clearedResidueRow y β (positive i) (poles i) (active i)) :=
    (map_clearedResidueRow φ y β _ _ _ (hdisj i) hlinear).symm
  have hfirst : φ (Lagrange.nodal Finset.univ y) *
      specializedResidueRow φ y β ∅ ∅ firstActive =
      φ (clearedResidueRow y β ∅ ∅ firstActive) :=
    (map_clearedResidueRow φ y β ∅ ∅ firstActive (by simp) hlinear).symm
  have hterm (i : κ) :
      (φ (C β₀) * φ (Lagrange.nodal Finset.univ y)) *
        ((specializedResidueRow φ y β (positive i) (poles i) (active i) / φ (C β₀)) *
          φ (C (A i))) =
      φ (C (A i)) * φ (clearedResidueRow y β (positive i) (poles i) (active i)) := by
    rw [← hrow]
    field_simp [hβ₀]
    <;> ring
  have hlast : (φ (C β₀) * φ (Lagrange.nodal Finset.univ y)) *
      (φ X * (specializedResidueRow φ y β ∅ ∅ firstActive / φ (C β₀))) =
      φ X * φ (clearedResidueRow y β ∅ ∅ firstActive) := by
    rw [← hfirst]
    field_simp [hβ₀]
    <;> ring
  rw [specializedSchur, mul_add, mul_sub, mul_one, Finset.mul_sum, hlast,
    map_add, map_sub, map_mul, map_sum, map_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  exact hterm i

/-- A nonzero cleared polynomial proves nonvanishing of the literal
Schur complement in a faithful specialization. -/
theorem specializedSchur_ne_zero_of_cleared
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : L[X] →+* E) (hφ : Function.Injective φ) (y β : ι → L) (β₀ : L)
    (positive poles active : κ → Finset ι) (A : κ → L) (firstActive : Finset ι)
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hlinear : ∀ k, φ X - φ (C (y k)) ≠ 0) (hβ₀ : φ (C β₀) ≠ 0)
    (hclear : C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ firstActive ≠ 0) :
    specializedSchur φ y β β₀ positive poles active A firstActive ≠ 0 := by
  intro hzero
  have h := specializedSchur_clear φ y β β₀ positive poles active A firstActive hdisj hlinear hβ₀
  rw [hzero, mul_zero] at h
  apply hclear
  apply hφ
  simpa only [map_zero] using h.symm

end PaperVerification.Fermion.Newton
