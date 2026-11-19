module

public import VolumePolynomials.HigherLiftForward
public import VolumePolynomials.BinarySemialgebraic
public import VolumePolynomials.ExtraVariables
public import VolumePolynomials.FullDimensionalPolytopes

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The sharp algebraic threshold

Both loci below retain every homogeneous coefficient. The polytope locus
requires each realizing body to be full dimensional and places no bound
on its number of vertices or facets.
-/

namespace VolumePolynomials.Main

theorem volumeLocus_not_semialgebraic {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | apply not_semialgebraic_volumeLocus_of_three hn
    have heq : 3 + (d - 3) = d := by omega
    rw [← heq]
    exact HigherLift.volumeLocus_not_semialgebraic (d - 3)

/-- Theorem 1.1, for every number of bodies and every dimension in the
stated range, with realizability defined by actual Lebesgue volume. -/
theorem semialgebraicity_iff {n d : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d) :
    TauCeti.IsSemialgebraic (VolumeLocus n d) ↔ n ≤ 2 := by
  first
  | constructor
    · intro h
      by_contra hn2
      exact volumeLocus_not_semialgebraic (by omega) hd h
    · exact isSemialgebraic_volumeLocus_of_le_two hn (by omega)

/-- The full-dimensional polytope clause of Theorem 1.1. -/
theorem polytope_locus_not_semialgebraic {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ TauCeti.IsSemialgebraic (FullDimensionalPolytopeLocus n d) :=
  fullDimensionalPolytopeLocus_not_semialgebraic_of_volumeLocus (by omega)
    (volumeLocus_not_semialgebraic hn hd)

end VolumePolynomials.Main
