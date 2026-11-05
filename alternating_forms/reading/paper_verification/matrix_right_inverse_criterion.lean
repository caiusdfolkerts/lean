module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

/-!
# A global right inverse from independence in the residue fields

The proof uses the ideal of scalars `r` for which `A * B = r • 1` is solvable.
Modulo a maximal ideal, row independence supplies a right inverse. Lift that
matrix and multiply by the adjugate of its product with `A`: its determinant
belongs to the scalar ideal and is congruent to one modulo the maximal ideal.
Thus the scalar ideal is the unit ideal.

This avoids assuming a choice of pivot columns valid over the entire base.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace PaperVerification.GenericSectionDifferentials

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Scalars admitting a matrix right inverse after multiplication by that scalar. -/
def rightInverseScalarIdeal (A : Matrix κ ι R) : Ideal R where
  carrier := {r | ∃ B : Matrix ι κ R, A * B = r • (1 : Matrix κ κ R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro r s ⟨B,hB⟩ ⟨C,hC⟩
    exact ⟨B+C, by simp only [Matrix.mul_add,hB,hC,add_smul]⟩
  smul_mem' := by
    rintro r s ⟨B,hB⟩
    exact ⟨r • B, by simp only [Matrix.mul_smul,hB,smul_smul,smul_eq_mul]⟩

/-- Independent rows over every maximal residue field give a right inverse
over the original ring, including rings with nilpotents. -/
theorem matrix_rightInverse_of_residue_rows
    (A : Matrix κ ι R)
    (hA : ∀ (J : Ideal R) [J.IsMaximal],
      LinearIndependent (R ⧸ J) (A.map (Ideal.Quotient.mk J))) :
    ∃ B : Matrix ι κ R, A * B = 1 := by
  classical
  let I := rightInverseScalarIdeal A
  have hI : I = ⊤ := by
    by_contra hproper
    obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal I hproper
    letI : J.IsMaximal := hJ
    letI : Field (R ⧸ J) := Ideal.Quotient.field J
    let π := Ideal.Quotient.mk J
    have hrows : LinearIndependent (R ⧸ J) (A.map π).row := hA J
    obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
      hrows.mulVec_surjective
    choose C₀ hC using fun i j => Ideal.Quotient.mk_surjective (B i j)
    let C : Matrix ι κ R := C₀
    have hC' : C.map π = B := by
      ext i j
      exact hC i j
    let Q : Matrix κ κ R := A * C
    have hQ : Q.map π = 1 := by
      simpa only [Q,Matrix.map_mul,hC'] using hB
    have hdet : π Q.det = 1 := by
      rw [RingHom.map_det]
      change (Q.map π).det = 1
      rw [hQ,Matrix.det_one]
    have hmem : Q.det ∈ I := by
      refine ⟨C * Q.adjugate, ?_⟩
      rw [← Matrix.mul_assoc]
      exact Matrix.mul_adjugate Q
    have hz : π Q.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hmem)
    exact one_ne_zero (hdet.symm.trans hz)
  have h1 : (1 : R) ∈ I := by rw [hI]; trivial
  obtain ⟨B,hB⟩ := h1
  exact ⟨B, by simpa only [one_smul] using hB⟩

end PaperVerification.GenericSectionDifferentials
