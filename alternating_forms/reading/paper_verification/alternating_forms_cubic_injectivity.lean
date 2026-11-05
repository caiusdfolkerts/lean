module

public import PaperVerification.AlternatingFormsGenericHilbertCoordinates
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The actual cubic multiplication map in every dimension at least six

The degree-three determinant in Theorem 1.1 is exactly choose(n,3)-2n.
Rank-nullity therefore proves injectivity of the original exterior
multiplication map, on the same principal open, for every n≥6.  There is
no restriction to an even dimension or to a six-dimensional subspace.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped Matrix

theorem twice_choose_two_int (n : ℕ) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      linear_combination ih

theorem paperMatrix_three_det (w : ℕ) :
    (PathDeterminant.paperMatrix (w+2) 3).det =
      (w+2 : ℤ)^3 - 2*(w+2 : ℤ)*((w+1).choose 2 : ℤ) + (w.choose 3 : ℤ) := by
  have hm : PathDeterminant.paperMatrix (w+2) 3 =
      !![(w+2 : ℤ), ((w+1).choose 2 : ℤ), (w.choose 3 : ℤ);
         1, (w+2 : ℤ), ((w+1).choose 2 : ℤ);
         0, 1, (w+2 : ℤ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PathDeterminant.paperMatrix, Nat.choose_one_right]
  rw [hm, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

theorem paperWalkCount_three (n : ℕ) (hn : 6 ≤ n) :
    StripWalks.paperWalkCount n 3 + 2*n = n.choose 3 := by
  obtain ⟨w, rfl⟩ : ∃ w, n=w+6 := ⟨n-6, by omega⟩
  have hd := PathDeterminant.paperWalkCount_determinant (w+6) 3 (by omega)
  rw [show w+6+2-2*3=w+2 by omega, paperMatrix_three_det] at hd
  have htwo := twice_choose_two_int w
  have hshift : ((w+6).choose 3 : ℤ) =
      (w.choose 3 : ℤ)+6*(w.choose 2 : ℤ)+15*(w : ℤ)+20 := by
    simp only [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_one]
    ring
  have hnext : ((w+1).choose 2 : ℤ) = (w.choose 2 : ℤ)+(w : ℤ) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
    ring
  have he : (StripWalks.paperWalkCount (w+6) 3 : ℤ)+2*(w+6 : ℤ) =
      ((w+6).choose 3 : ℤ) := by
    rw [hd, hnext, hshift]
    linear_combination -(w+5 : ℤ)*htwo
  exact_mod_cast he

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The cubic dimension equality implies injectivity of the actual map
`(u,v) ↦ f∧u+g∧v`; it is not an assumed presentation of the relation space. -/
theorem cubic_wedge_injective_of_hilbert (n : ℕ) (hn : 6 ≤ n)
    (hdim : Module.finrank K M=n) (f g : ⋀[K]^2 M)
    (h3 : Module.finrank K (ExteriorQuotientDegree f g 3) =
      StripWalks.paperWalkCount n 3) :
    Function.Injective (orbitExteriorRelationMap f g 1) := by
  have hr := exteriorQuotientDegree_finrank_add_orbitRange f g 1
  change Module.finrank K (ExteriorQuotientDegree f g 3) +
    Module.finrank K (LinearMap.range (orbitExteriorRelationMap f g 1)) =
      Module.finrank K (⋀[K]^3 M) at hr
  rw [exteriorPower.finrank_eq, hdim, h3] at hr
  have hc := paperWalkCount_three n hn
  have hnull := (orbitExteriorRelationMap f g 1).finrank_range_add_finrank_ker
  simp only [Module.finrank_prod, exteriorPower.finrank_eq, Nat.choose_one_right, hdim] at hnull
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- One genuine nonzero coefficient polynomial controls cubic injectivity
throughout the full space of alternating-form pairs, in every n≥6. -/
theorem generic_cubic_wedge_injective (n : ℕ) (hn : 6 ≤ n)
    (hdim : Module.finrank K M=n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q ≠ 0 →
            Function.Injective (orbitExteriorRelationMap
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 1) := by
  classical
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  exact cubic_wedge_injective_of_hilbert n hn hdim _ _
    (((h y hy).2.1 3 (by decide) (by omega)).1)

end PaperVerification.AlternatingForms
