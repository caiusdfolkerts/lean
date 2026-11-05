module

public import PaperVerification.ToricFanDifferentials
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

@[expose] public section

/-!
# The actual dimension of a smooth complete fan scheme

Full cones give actual open affine charts with polynomial coordinate
rings in `n` variables. Their union is the whole scheme. The upper
dimension bound follows from preservation of point coheight under open
immersions; the lower bound follows from any one of those open charts.
Thus the rank parameter is identified with ordinary topological Krull
dimension, including rank zero.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry TopologicalSpace

theorem scheme_topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X := by
  change Order.krullDim (IrreducibleCloseds X) = Order.krullDim X
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fullChart_ringKrullDim (s : «Σ».fullCones) :
    ringKrullDim (monoidChartAlgebra k (dualConeMonoid s.val)) = n := by
  rw [← ringKrullDim_eq_of_ringEquiv
    («Σ».fullChartPolynomialPresentation k s).toRingEquiv]
  simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add]

theorem fullChart_topologicalKrullDim (s : «Σ».fullCones) :
    topologicalKrullDim (coneChart k s.val) = n := by
  change topologicalKrullDim
    (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val))) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    «Σ».fullChart_ringKrullDim k s]

theorem fanScheme_orderKrullDim_le (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) ≤ n := by
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨s, y, rfl⟩ := «Σ».fullChartOpen_cover k hpure x
  rw [coheight_eq_of_isOpenImmersion]
  erw [← idealHeight_eq_coheight (CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid s.val)))
      (show Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))) from y)]
  have h := Ideal.height_le_ringKrullDim_of_ne_top y.isPrime.ne_top
  have hd : ringKrullDim
      (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val)) = n :=
    «Σ».fullChart_ringKrullDim k s
  rw [hd] at h
  exact h

/-- Dimension means chains of actual irreducible closed subsets of the
glued scheme, rather than a separately assigned lattice-rank invariant. -/
theorem fanScheme_topologicalKrullDim (hpure : «Σ».IsPure) :
    topologicalKrullDim («Σ».fanScheme k) = n := by
  apply le_antisymm
  · rw [scheme_topologicalKrullDim_eq_orderKrullDim]
    exact «Σ».fanScheme_orderKrullDim_le k hpure
  · obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
    let s' : «Σ».fullCones := ⟨s, hs⟩
    have h := ((«Σ».fanChartMap k («Σ».fullConeIndex s')).isOpenEmbedding.isEmbedding.isInducing).topologicalKrullDim_le
    change topologicalKrullDim (coneChart k s'.val) ≤
      topologicalKrullDim («Σ».fanScheme k) at h
    simpa only [«Σ».fullChart_topologicalKrullDim k s'] using h

theorem fanScheme_orderKrullDim (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) = n := by
  rw [← scheme_topologicalKrullDim_eq_orderKrullDim,
    «Σ».fanScheme_topologicalKrullDim k hpure]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_topologicalKrullDim
