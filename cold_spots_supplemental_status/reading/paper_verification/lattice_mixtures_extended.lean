module

public import PaperVerification.LatticeMixtures

@[expose] public section

/-!
# Corollary 1.2 including singular positive mixtures

Only existence of one finite lattice sum is required. The actual positive
measure may be infinite and need not be sigma finite. The nonnegative
integral-potential sums retain their ordinary extended values at singular
points. Whenever all values are finite, the previously proved real-valued
bridge recovers the literal real series.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory PaperVerification.PositiveMixtures
open scoped ENNReal

theorem mixture_coldSpot_ennreal_iff_of_exists_finite {n : ℕ}
    (L : Set (Fin n→ℝ))
    (hGauss : ∀ α : ℝ,0<α→∀ x,
      Summable (fun v : L=>Real.exp (-α*sqDist v.val x)))
    (hmain : ∀ α : ℝ,0<α→∀ x,IsColdSpot L α x↔IsDeepHole L x)
    (c : Fin n→ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal L ν y≠∞) (x : Fin n→ℝ) :
    (∀ y,setMixtureEnergyENNReal L ν x≤setMixtureEnergyENNReal L ν y) ↔
      IsDeepHole L x :=
  gaussian_mixture_minimizers_of_exists_finite
    (fun v : L=>fun y=>sqDist v.val y) (IsDeepHole L) ν hν
    (fun α y=>hGauss α α.property y) (fun α y=>hmain α α.property y)
    c hc hconv x

theorem mixture_coldSpot_dPlus_iff_exists_finite {n : ℕ}
    (hn : 8≤n) (heven : Even n) (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal (dPlusSet n) ν y≠∞) (x : Fin n→ℝ) :
    (∀ y,setMixtureEnergyENNReal (dPlusSet n) ν x≤setMixtureEnergyENNReal (dPlusSet n) ν y) ↔
      IsDeepHole (dPlusSet n) x := by
  obtain ⟨c,hc⟩ := exists_balancedHalfGrid heven
  have hdeep : IsDeepHole (dPlusSet n) c :=
    (isDeepHole_dPlus_iff_depth hn heven c).mpr (squaredDepth_dPlus_of_balanced hn hc)
  exact mixture_coldSpot_ennreal_iff_of_exists_finite (dPlusSet n)
    (fun α hα y=>summable_setGaussian_dPlus (by omega) hα y)
    (fun α hα y=>coldSpot_dPlus_iff_deepHole hn heven hα y) c hdeep ν hν hconv x

theorem mixture_coldSpot_E6_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal e6Set ν y≠∞) (x : Fin 6→ℝ) :
    (∀ y,setMixtureEnergyENNReal e6Set ν x≤setMixtureEnergyENNReal e6Set ν y) ↔
      IsDeepHole e6Set x := by
  have hc : IsDeepHole e6Set (e6PhysicalPoint e6HoleWitness) := by
    intro y
    rw [e6_covering_radius_attained]
    exact e6_covering_radius_squared y
  exact mixture_coldSpot_ennreal_iff_of_exists_finite e6Set
    (fun α hα y=>summable_setGaussian_E6 hα y)
    (fun α hα y=>coldSpot_E6_iff_deepHole hα y)
    (e6PhysicalPoint e6HoleWitness) hc ν hν hconv x

theorem mixture_coldSpot_bw16_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal bw16Set ν y≠∞) (x : Fin 16→ℝ) :
    (∀ y,setMixtureEnergyENNReal bw16Set ν x≤setMixtureEnergyENNReal bw16Set ν y) ↔
      IsDeepHole bw16Set x := by
  obtain ⟨hupper,c,hc⟩ := bw16_squared_covering_radius
  have hdeep : IsDeepHole bw16Set c := by
    intro y
    rw [hc]
    exact hupper y
  exact mixture_coldSpot_ennreal_iff_of_exists_finite bw16Set
    (fun α hα y=>summable_setGaussian_bw16 hα y)
    (fun α hα y=>coldSpot_bw16_iff_deepHole hα y) c hdeep ν hν hconv x

theorem mixture_coldSpot_E7_dual_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,e7MixtureEnergyENNReal ν y≠∞) (x : zeroSumSpace) :
    (∀ y,e7MixtureEnergyENNReal ν x≤e7MixtureEnergyENNReal ν y) ↔ IsE7DeepHole x := by
  have hc : IsE7DeepHole e7Witness := (isE7DeepHole_iff_depth _).mpr e7Witness_depth
  exact gaussian_mixture_minimizers_of_exists_finite
    (fun v : e7ProjectedSet=>fun y : zeroSumSpace=>sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α y=>summable_e7Gaussian α.property y)
    (fun α y=>coldSpot_E7_dual_iff_deepHole α.property y) e7Witness hc hconv x

/-- The complete positive-mixture corollary, in an extended-value form
which also covers convergent singular potentials. -/
theorem lattice_corollary_1_2_extended (ν : Measure PositiveParameter) (hν : ν≠0) :
    ((∃ y : Fin 6→ℝ,setMixtureEnergyENNReal e6Set ν y≠∞) →
      ∀ x : Fin 6→ℝ,(∀ y,setMixtureEnergyENNReal e6Set ν x≤setMixtureEnergyENNReal e6Set ν y) ↔
        IsDeepHole e6Set x) ∧
    ((∃ y : Fin 8→ℝ,setMixtureEnergyENNReal (dPlusSet 8) ν y≠∞) →
      ∀ x : Fin 8→ℝ,(∀ y,setMixtureEnergyENNReal (dPlusSet 8) ν x≤
        setMixtureEnergyENNReal (dPlusSet 8) ν y) ↔IsDeepHole (dPlusSet 8) x) ∧
    ((∃ y : zeroSumSpace,e7MixtureEnergyENNReal ν y≠∞) →
      ∀ x : zeroSumSpace,(∀ y,e7MixtureEnergyENNReal ν x≤e7MixtureEnergyENNReal ν y) ↔
        IsE7DeepHole x) ∧
    ((∃ y : Fin 16→ℝ,setMixtureEnergyENNReal bw16Set ν y≠∞) →
      ∀ x : Fin 16→ℝ,(∀ y,setMixtureEnergyENNReal bw16Set ν x≤setMixtureEnergyENNReal bw16Set ν y) ↔
        IsDeepHole bw16Set x) ∧
    (∀ n : ℕ,8≤n→Even n→
      (∃ y : Fin n→ℝ,setMixtureEnergyENNReal (dPlusSet n) ν y≠∞) →
      ∀ x : Fin n→ℝ,(∀ y,setMixtureEnergyENNReal (dPlusSet n) ν x≤
        setMixtureEnergyENNReal (dPlusSet n) ν y) ↔IsDeepHole (dPlusSet n) x) :=
  ⟨fun h x=>mixture_coldSpot_E6_iff_exists_finite ν hν h x,
    fun h x=>mixture_coldSpot_dPlus_iff_exists_finite (by decide) (by decide) ν hν h x,
    fun h x=>mixture_coldSpot_E7_dual_iff_exists_finite ν hν h x,
    fun h x=>mixture_coldSpot_bw16_iff_exists_finite ν hν h x,
    fun _ hn heven h x=>mixture_coldSpot_dPlus_iff_exists_finite hn heven ν hν h x⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.lattice_corollary_1_2_extended
