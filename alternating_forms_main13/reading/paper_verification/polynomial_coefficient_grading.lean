module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Polynomial extension with a parameter of degree zero

For an internally graded coefficient algebra, the degree-`d` piece of its
polynomial extension consists exactly of polynomials whose coefficients
all have degree `d`. The parameter has degree zero. The internal direct
sum and the graded multiplication are proved from the coefficient
grading; no grading of the extension is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Polynomial DirectSum

namespace PaperVerification.PolynomialCoefficientGrading

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- Ordinary coefficient degree, with the polynomial parameter in degree zero. -/
def piece (G : TauCeti.InternalGrading K A ℕ) (d : ℕ) :
    Submodule K (Polynomial A) where
  carrier := {p | ∀ j, p.coeff j ∈ G.piece d}
  zero_mem' := by intro j; simpa using (G.piece d).zero_mem
  add_mem' := by
    intro p q hp hq j
    simpa only [coeff_add] using (G.piece d).add_mem (hp j) (hq j)
  smul_mem' := by
    intro c p hp j
    simpa only [coeff_smul] using (G.piece d).smul_mem c (hp j)

@[simp] theorem mem_piece_iff (G : TauCeti.InternalGrading K A ℕ)
    (d : ℕ) (p : Polynomial A) :
    p ∈ piece G d ↔ ∀ j, p.coeff j ∈ G.piece d := Iff.rfl

theorem monomial_mem (G : TauCeti.InternalGrading K A ℕ)
    (j : ℕ) {d : ℕ} {a : A} (ha : a ∈ G.piece d) :
    monomial j a ∈ piece G d := by
  intro l
  by_cases h : j = l
  · simpa [coeff_monomial, h] using ha
  · simp [coeff_monomial, h]

theorem isInternal (G : TauCeti.InternalGrading K A ℕ) :
    DirectSum.IsInternal (piece G) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply iSupIndep_def.mpr
    intro d
    apply Submodule.disjoint_def.mpr
    intro p hp hq
    apply Polynomial.ext
    intro j
    have hle : (⨆ e, ⨆ (_ : e ≠ d), piece G e) ≤
        (⨆ e, ⨆ (_ : e ≠ d), G.piece e).comap
          ((Polynomial.lcoeff A j).restrictScalars K) := by
      apply iSup_le
      intro e
      apply iSup_le
      intro he p hp
      exact Submodule.mem_iSup_of_mem e
        (Submodule.mem_iSup_of_mem he (hp j))
    have hz := Submodule.disjoint_def.mp
      (G.isInternal.submodule_iSupIndep d) (p.coeff j) (hp j) (hle hq)
    simpa only [coeff_zero] using hz
  · apply top_unique
    intro p hp
    clear hp
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | monomial j a =>
      have hsum : monomial j a =
          ∑ d ∈ (DirectSum.decompose G.piece a).support,
            monomial j (DirectSum.decompose G.piece a d : A) := by
        rw [← map_sum, DirectSum.sum_support_decompose]
      rw [hsum]
      apply Submodule.sum_mem
      intro d _
      exact Submodule.mem_iSup_of_mem d
        (monomial_mem G j (DirectSum.decompose G.piece a d).property)

/-- The genuine internal grading of the polynomial algebra by coefficient degree. -/
def grading (G : TauCeti.InternalGrading K A ℕ) :
    TauCeti.InternalGrading K (Polynomial A) ℕ :=
  ⟨piece G, isInternal G⟩

@[simp] theorem grading_piece (G : TauCeti.InternalGrading K A ℕ) (d : ℕ) :
    (grading G).piece d = piece G d := rfl

/-- Taking a coefficient preserves the coefficient grading. -/
theorem coefficient_homogeneous (G : TauCeti.InternalGrading K A ℕ) (j : ℕ) :
    TauCeti.LinearMap.IsHomogeneous ((Polynomial.lcoeff A j).restrictScalars K)
      (grading G).piece G.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d p hp
  simpa only [add_zero, LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply] using hp j

theorem decompose_coeff (G : TauCeti.InternalGrading K A ℕ)
    (p : Polynomial A) (d j : ℕ) :
    (DirectSum.decompose (grading G).piece p d : Polynomial A).coeff j =
      (DirectSum.decompose G.piece (p.coeff j) d : A) := by
  have h := (coefficient_homogeneous G j).map_decompose d p
  change (DirectSum.decompose (grading G).piece p d : Polynomial A).coeff j =
    (DirectSum.decompose G.piece (p.coeff j) (d + 0) : A) at h
  simpa only [Nat.add_zero] using h

instance gradedMonoid (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : SetLike.GradedMonoid (grading G).piece where
  one_mem := by
    intro j
    by_cases h : j = 0
    · subst j
      simpa only [coeff_one_zero] using
        (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)
    · simp only [coeff_one, h, ite_false]
      exact (G.piece 0).zero_mem
  mul_mem := by
    intro a b p q hp hq j
    rw [coeff_mul]
    exact (G.piece (a + b)).sum_mem fun uv _ ↦
      SetLike.GradedMul.mul_mem (hp uv.1) (hq uv.2)

instance gradedAlgebra (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : GradedAlgebra (grading G).piece :=
  (grading G).isInternal.gradedAlgebra

theorem C_mem (G : TauCeti.InternalGrading K A ℕ) {d : ℕ} {a : A}
    (ha : a ∈ G.piece d) : Polynomial.C a ∈ (grading G).piece d := by
  change Polynomial.C a ∈ piece G d
  simpa only [monomial_zero_left] using monomial_mem G 0 ha

theorem X_mem_zero (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] : (Polynomial.X : Polynomial A) ∈ (grading G).piece 0 := by
  change (Polynomial.X : Polynomial A) ∈ piece G 0
  simpa only [monomial_one_one_eq_X] using
    monomial_mem G 1 (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)

end PaperVerification.PolynomialCoefficientGrading
