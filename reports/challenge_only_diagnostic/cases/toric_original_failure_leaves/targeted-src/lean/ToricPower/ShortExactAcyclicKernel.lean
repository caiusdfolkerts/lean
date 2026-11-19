module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso

/-! # The acyclic kernel of a quasi-isomorphism in a short exact sequence

The proof uses the actual long exact homology sequence. No replacement
of the short exact sequence by an assumed triangle is needed.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

variable {A : Type*} [Category* A] [Abelian A]

theorem shortExact_acyclic_left_of_quasiIso_g
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    [QuasiIso S.g] : S.X₁.Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  have hf : homologyMap S.f n = 0 := by
    apply (cancel_mono (homologyMap S.g n)).mp
    rw [zero_comp, ← homologyMap_comp, S.zero, homologyMap_zero]
  have relation : (ComplexShape.up ℤ).Rel (n-1) n := by simp
  have hd : hS.δ (n-1) n relation = 0 := by
    apply (cancel_epi (homologyMap S.g (n-1))).mp
    rw [comp_zero, hS.comp_δ]
  exact (hS.homology_exact₁ (n-1) n relation).isZero_of_both_zeros hd hf

end ToricPower

end
