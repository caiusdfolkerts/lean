module

public import PaperVerification.GaussianMixtures
public import PaperVerification.BWNormalized
public import PaperVerification.E6Euclidean
public import PaperVerification.E7Theorems

@[expose] public section

/-! # Corollary 1.2 for every lattice in Theorem 1.1

Each specialization supplies actual Gaussian convergence and the actual theorem
for that lattice.  The only hypotheses on the mixing measure are nonzero
positivity (built into `Measure`) and convergence of the nonnegative energy.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory
open scoped ENNReal
open PaperVerification.PositiveMixtures

variable {n : ℕ}

def setMixtureEnergyENNReal (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : L => fun y => sqDist v.val y) ν x

def setMixtureEnergy (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ :=
  mixtureEnergy (fun v : L => fun y => sqDist v.val y) ν x

def IsMixtureColdSpot (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : Prop := ∀ y, setMixtureEnergy L ν x ≤ setMixtureEnergy L ν y

/-- Coordinate-space form of the exact positive-mixture transfer. -/
theorem mixture_coldSpot_iff_of_universal
    (L : Set (Fin n → ℝ))
    (hGauss : ∀ α : ℝ, 0 < α → ∀ x,
      Summable (fun v : L => Real.exp (-α * sqDist v.val x)))
    (hmain : ∀ α : ℝ, 0 < α → ∀ x, IsColdSpot L α x ↔ IsDeepHole L x)
    (c : Fin n → ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal L ν x ≠ ∞) (x : Fin n → ℝ) :
    IsMixtureColdSpot L ν x ↔ IsDeepHole L x := by
  exact gaussian_mixture_minimizers_real (fun v : L => fun y => sqDist v.val y)
    (IsDeepHole L) ν hν (fun α x => hGauss α α.property x)
    (fun α x => hmain α α.property x) c hc hconv x

/-- Extended-energy form, allowing singular potentials and infinite energy at
some ambient points.  Only one deep hole's energy must be finite. -/
theorem mixture_coldSpot_ennreal_iff_of_universal
    (L : Set (Fin n → ℝ))
    (hGauss : ∀ α : ℝ, 0 < α → ∀ x,
      Summable (fun v : L => Real.exp (-α * sqDist v.val x)))
    (hmain : ∀ α : ℝ, 0 < α → ∀ x, IsColdSpot L α x ↔ IsDeepHole L x)
    (c : Fin n → ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : setMixtureEnergyENNReal L ν c ≠ ∞) (x : Fin n → ℝ) :
    (∀ y, setMixtureEnergyENNReal L ν x ≤ setMixtureEnergyENNReal L ν y) ↔ IsDeepHole L x := by
  exact gaussian_mixture_minimizers (fun v : L => fun y => sqDist v.val y)
    (IsDeepHole L) ν hν (fun α x => hGauss α α.property x)
    (fun α x => hmain α α.property x) c hc hconv x

/-- Corollary 1.2 for every even D_n^+ with n≥8, including E8. -/
theorem mixture_coldSpot_dPlus_iff_deepHole (hn : 8 ≤ n) (heven : Even n)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal (dPlusSet n) ν x ≠ ∞) (x : Fin n → ℝ) :
    IsMixtureColdSpot (dPlusSet n) ν x ↔ IsDeepHole (dPlusSet n) x := by
  obtain ⟨c, hc⟩ := exists_balancedHalfGrid heven
  have hcdeep : IsDeepHole (dPlusSet n) c :=
    (isDeepHole_dPlus_iff_depth hn heven c).mpr (squaredDepth_dPlus_of_balanced hn hc)
  exact mixture_coldSpot_iff_of_universal (dPlusSet n)
    (fun α hα x => summable_setGaussian_dPlus (by omega) hα x)
    (fun α hα x => coldSpot_dPlus_iff_deepHole hn heven hα x) c hcdeep ν hν hconv x

theorem mixture_coldSpot_E8_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal (dPlusSet 8) ν x ≠ ∞) (x : Fin 8 → ℝ) :
    IsMixtureColdSpot (dPlusSet 8) ν x ↔ IsDeepHole (dPlusSet 8) x :=
  mixture_coldSpot_dPlus_iff_deepHole (by decide) (by decide) ν hν hconv x

/-- Corollary 1.2 for the usual integral BW16 lattice. -/
theorem mixture_coldSpot_bw16_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal bw16Set ν x ≠ ∞) (x : Fin 16 → ℝ) :
    IsMixtureColdSpot bw16Set ν x ↔ IsDeepHole bw16Set x := by
  obtain ⟨hupper, c, hc⟩ := bw16_squared_covering_radius
  have hcdeep : IsDeepHole bw16Set c := by intro y; rw [hc]; exact hupper y
  exact mixture_coldSpot_iff_of_universal bw16Set
    (fun α hα x => summable_setGaussian_bw16 hα x)
    (fun α hα x => coldSpot_bw16_iff_deepHole hα x) c hcdeep ν hν hconv x

theorem summable_setGaussian_l6Euclidean {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    Summable (fun v : l6EuclideanSet => Real.exp (-α * sqDist v.val (triTripleFlatten z))) := by
  apply (l6EuclideanIndexEquiv.summable_iff
    (f := fun v : l6EuclideanSet => Real.exp (-α * sqDist v.val (triTripleFlatten z)))).mp
  have hs := summable_l6Gaussian hα z
  convert hs using 1
  funext p
  change Real.exp (-α * sqDist (triTripleFlatten (l6Point p)) (triTripleFlatten z)) = _
  rw [triTripleFlatten_sqDist]

theorem summable_setGaussian_E6 {α : ℝ} (hα : 0 < α) (x : Fin 6 → ℝ) :
    Summable (fun v : e6Set => Real.exp (-α * sqDist v.val x)) := by
  obtain ⟨z, rfl⟩ := e6PhysicalPoint_surjective x
  unfold e6Set e6PhysicalPoint
  rw [summable_scaled_iff _ (by positivity), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact summable_setGaussian_l6Euclidean (by positivity) z

/-- Corollary 1.2 for the root-normalized E6 lattice in ordinary R6. -/
theorem mixture_coldSpot_E6_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal e6Set ν x ≠ ∞) (x : Fin 6 → ℝ) :
    IsMixtureColdSpot e6Set ν x ↔ IsDeepHole e6Set x := by
  have hcdeep : IsDeepHole e6Set (e6PhysicalPoint e6HoleWitness) := by
    intro y
    rw [e6_covering_radius_attained]
    exact e6_covering_radius_squared y
  exact mixture_coldSpot_iff_of_universal e6Set
    (fun α hα x => summable_setGaussian_E6 hα x)
    (fun α hα x => coldSpot_E6_iff_deepHole hα x)
    (e6PhysicalPoint e6HoleWitness) hcdeep ν hν hconv x

def e7MixtureEnergyENNReal (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

def e7MixtureEnergy (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ :=
  mixtureEnergy (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

/-- Corollary 1.2 for E7*, in its actual seven-dimensional Euclidean hyperplane. -/
theorem mixture_coldSpot_E7_dual_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, e7MixtureEnergyENNReal ν x ≠ ∞) (x : zeroSumSpace) :
    (∀ y, e7MixtureEnergy ν x ≤ e7MixtureEnergy ν y) ↔ IsE7DeepHole x := by
  have hcdeep : IsE7DeepHole e7Witness := (isE7DeepHole_iff_depth _).mpr e7Witness_depth
  exact gaussian_mixture_minimizers_real
    (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α x => summable_e7Gaussian α.property x)
    (fun α x => coldSpot_E7_dual_iff_deepHole α.property x) e7Witness hcdeep hconv x

/-- The same D_n^+ conclusion permits infinite energy away from the minimum
set.  Convergence is required only at a single actual deep hole. -/
theorem mixture_coldSpot_dPlus_ennreal_iff_deepHole (hn : 8 ≤ n) (heven : Even n)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole (dPlusSet n) c ∧ setMixtureEnergyENNReal (dPlusSet n) ν c ≠ ∞)
    (x : Fin n → ℝ) :
    (∀ y, setMixtureEnergyENNReal (dPlusSet n) ν x ≤ setMixtureEnergyENNReal (dPlusSet n) ν y) ↔
      IsDeepHole (dPlusSet n) x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal (dPlusSet n)
    (fun α hα x => summable_setGaussian_dPlus (by omega) hα x)
    (fun α hα x => coldSpot_dPlus_iff_deepHole hn heven hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E8_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole (dPlusSet 8) c ∧ setMixtureEnergyENNReal (dPlusSet 8) ν c ≠ ∞)
    (x : Fin 8 → ℝ) :
    (∀ y, setMixtureEnergyENNReal (dPlusSet 8) ν x ≤ setMixtureEnergyENNReal (dPlusSet 8) ν y) ↔
      IsDeepHole (dPlusSet 8) x :=
  mixture_coldSpot_dPlus_ennreal_iff_deepHole (by decide) (by decide) ν hν hconv x

theorem mixture_coldSpot_bw16_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole bw16Set c ∧ setMixtureEnergyENNReal bw16Set ν c ≠ ∞)
    (x : Fin 16 → ℝ) :
    (∀ y, setMixtureEnergyENNReal bw16Set ν x ≤ setMixtureEnergyENNReal bw16Set ν y) ↔
      IsDeepHole bw16Set x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal bw16Set
    (fun α hα x => summable_setGaussian_bw16 hα x)
    (fun α hα x => coldSpot_bw16_iff_deepHole hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E6_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole e6Set c ∧ setMixtureEnergyENNReal e6Set ν c ≠ ∞)
    (x : Fin 6 → ℝ) :
    (∀ y, setMixtureEnergyENNReal e6Set ν x ≤ setMixtureEnergyENNReal e6Set ν y) ↔
      IsDeepHole e6Set x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal e6Set
    (fun α hα x => summable_setGaussian_E6 hα x)
    (fun α hα x => coldSpot_E6_iff_deepHole hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E7_dual_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsE7DeepHole c ∧ e7MixtureEnergyENNReal ν c ≠ ∞) (x : zeroSumSpace) :
    (∀ y, e7MixtureEnergyENNReal ν x ≤ e7MixtureEnergyENNReal ν y) ↔ IsE7DeepHole x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact gaussian_mixture_minimizers
    (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α x => summable_e7Gaussian α.property x)
    (fun α x => coldSpot_E7_dual_iff_deepHole α.property x) c hc hfinite x

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.mixture_coldSpot_dPlus_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_bw16_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_E6_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_E7_dual_iff_deepHole
