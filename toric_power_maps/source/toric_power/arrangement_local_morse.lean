module

public import ToricPower.ArrangementHalfStar
public import ToricPower.CellularLocalMorse

/-!
# Actual local Morse fibers at maximal support cells

The region category contains exactly the genuine strata cut by the chosen
open half-neighborhood. Its map from the central coefficient uses every
actual face incidence. At a maximal cohomological support cell the full
derived sections on this cut region vanish, so the literal mapping fiber
recovers the nonzero central coefficient, in every unbounded degree.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ

/-- The literal inclusion of all strata which meet the chosen region. -/
def universalRegionInclusion (c : U) (region : Set E) :
    UniversalRegionStar A c region ⥤ U where
  obj d := d.val.val
  map f := homOfLE f.le

/-- Every retained stratum is an actual coface of the central cell. -/
def universalRegionInitialArrows (c : U) (region : Set E) :
    (Functor.const (UniversalRegionStar A c region)).obj c ⟶
      universalRegionInclusion A c region where
  app d := homOfLE d.val.property

variable (k : Type) [Field k]

/-- The full local Morse complex of the genuine cut face diagram. -/
def universalLocalMorse (c : U) (region : Set E) :
    CochainComplex (U ⥤ ModuleCat.{0} k) ℤ ⥤ CochainComplex (ModuleCat.{0} k) ℤ :=
  Cellular.localMorseComplexFunctor k (universalRegionInclusion A c region) c
    (universalRegionInitialArrows A c region)

/-- The actual relative-section projection onto the central coefficient. -/
def universalLocalMorseProjection (c : U) (region : Set E) :
    universalLocalMorse A k c region ⟶
      ((evaluation U (ModuleCat.{0} k)).obj c).mapHomologicalComplex (.up ℤ) :=
  Cellular.localMorseProjection k (universalRegionInclusion A c region) c
    (universalRegionInitialArrows A c region)

/-- All cut-region coefficients above a maximal support cell are
acyclic whenever the region misses the whole central closed cell. -/
theorem maximalSupport_regionCoefficients_acyclic
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ) (c : U)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1)
    (region : Set E)
    (misses : ¬ universalFaceStarMeets A c region (universalFaceStarPoint A c))
    (d : UniversalRegionStar A c region) :
    (K.asFunctor.obj d.val.val).Acyclic := by
  by_contra nonzero
  have different : c ≠ d.val.val := by
    intro same
    have sameStar : d.val = universalFaceStarPoint A c := Subtype.ext same.symm
    exact misses (sameStar ▸ d.property)
  exact (not_lt_of_ge (maximal d.val.val nonzero))
    (universalIncidence_dimension_lt A d.val.property different)

/-- The literal local Morse projection is a quasi-isomorphism; no
boundedness or finite-dimensional coefficient hypothesis is present. -/
theorem maximalSupport_localMorseProjection_quasiIso
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ) (c : U)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1)
    (region : Set E)
    (misses : ¬ universalFaceStarMeets A c region (universalFaceStarPoint A c)) :
    QuasiIso ((universalLocalMorseProjection A k c region).app K) :=
  Cellular.localMorseProjection_quasiIso_of_coefficients k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region) K
    (maximalSupport_regionCoefficients_acyclic A k K c maximal region misses)

/-- Every actual normal covector at a maximal support cell has the
same genuine relative coefficient complex as the central stalk. -/
theorem maximalSupport_negativeHalf_morse_quasiIso
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ) (c : U)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1)
    (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (normal : ξ ∈ cellNormal (augmentedForms A) c.2.val.2) :
    QuasiIso ((universalLocalMorseProjection A k c
      (universalNegativeHalf A c neighborhood ξ)).app K) :=
  maximalSupport_localMorseProjection_quasiIso A k K c maximal _
    (universalNegativeHalf_misses_base A c neighborhood ξ normal)

/-- Nonzero maximal support is detected by the actual local Morse
fiber in every normal direction, including the zero covector. -/
theorem maximalSupport_negativeHalf_morse_nonacyclic
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ) (c : U)
    (nonzero : ¬ (K.asFunctor.obj c).Acyclic)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1)
    (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (normal : ξ ∈ cellNormal (augmentedForms A) c.2.val.2) :
    ¬ ((universalLocalMorse A k c (universalNegativeHalf A c neighborhood ξ)).obj K).Acyclic := by
  let f := (universalLocalMorseProjection A k c
    (universalNegativeHalf A c neighborhood ξ)).app K
  letI : QuasiIso f := maximalSupport_negativeHalf_morse_quasiIso
    A k K c maximal neighborhood ξ normal
  intro acyclic
  apply nonzero
  intro q
  exact (exactAt_iff_of_quasiIsoAt f q).mp (acyclic q)

end ToricPower.IntegralArrangement

end
