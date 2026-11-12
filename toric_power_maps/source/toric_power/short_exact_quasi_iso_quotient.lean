module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # An actual acyclic kernel makes its quotient a quasi-isomorphism -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

variable {A : Type*} [Category* A] [Abelian A]

/-- The original quotient map in a short exact sequence of unbounded
complexes is a quasi-isomorphism when its actual kernel is acyclic. -/
theorem shortExact_quasiIso_g_of_acyclic_left
    (S : ShortComplex (CochainComplex A ℤ)) (exact : S.ShortExact)
    (acyclic : S.X₁.Acyclic) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro a
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have zero_a : IsZero (S.X₁.homology a) := (acyclic a).isZero_homology
  have zero_next : IsZero (S.X₁.homology (a+1)) := (acyclic (a+1)).isZero_homology
  letI : Mono (homologyMap S.g a) :=
    (exact.homology_exact₂ a).mono_g (zero_a.eq_of_src _ _)
  letI : Epi (homologyMap S.g a) :=
    (exact.homology_exact₃ a (a+1) (by simp)).epi_f (zero_next.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end ToricPower

end
