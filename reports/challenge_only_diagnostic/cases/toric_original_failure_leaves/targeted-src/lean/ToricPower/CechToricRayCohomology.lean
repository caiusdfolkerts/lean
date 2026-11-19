module

public import ToricPower.CechToricCohomology
public import ToricPower.CechDowkerReduced
public import ToricPower.CechWitnessReindex
public import ToricPower.FanRayComplex

/-!
# Actual toric cohomology and the induced negative-ray complex

The source of the comparison is Zariski cohomology of the actual Cartier
line sheaf. Its target is the direct sum, over the entire integral
character lattice, of the reduced negative-ray cochain groups. Finite
enumeration changes only the ray witnesses; the complete relative
cochain isomorphism proves that this change loses no characters or tuples.

The face theorem identifies the displayed finite complex with exact ray
sets of actual fan cones. No completeness or full-dimensional-cone
assumption is made. These are additive-group isomorphisms; an equivariant
weight-space formulation also needs the actual torus action and its
compatibility, which is not inferred here.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
open ToricPower.NegativeSupportCech ToricPower.CechCanonicalAugmentation
open ToricPower.CechDowkerReduced
open scoped Classical DirectSum

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- A universe-small enumeration of every actual fan ray. The inverse
equivalence retains its original cone, primitive generator, and coefficient. -/
def toricFiniteRayEquiv : Fin (Nat.card fan.Ray) ≃ fan.Ray :=
  (Finite.equivFin fan.Ray).symm

variable {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (b : fan.Ray → ℤ) (m : N →+ ℤ)

def toricEnumeratedRayIncidence (ray : Fin (Nat.card fan.Ray)) (index : Index) : Prop :=
  toricCechRayIncidence fan charts (toricFiniteRayEquiv fan ray) index

def toricEnumeratedNegative (ray : Fin (Nat.card fan.Ray)) : Prop :=
  toricCharacterNegative fan b m (toricFiniteRayEquiv fan ray)

/-- The actual reduced cochain group of the induced negative-ray complex,
shifted so that index `p` means reduced degree `p - 1`. -/
def toricNegativeRayReduced (degree : ℕ) : AddCommGrpCat :=
  canonicalNegativeReducedShifted ℂ
    (negativeRayIncidence (toricEnumeratedRayIncidence fan charts)
      (toricEnumeratedNegative fan b m)) (fun _ => True) degree

def toricCechWeightRayReducedIso (anchor : Index) (degree : ℕ) :
    (toricCechWeightComplex fan charts b m).homology degree ≅
      toricNegativeRayReduced fan charts b m degree :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
    (relativeWitnessReindexIso ℂ (toricCechRayIncidence fan charts)
      (toricCharacterNegative fan b m) (toricFiniteRayEquiv fan)) ≪≫
    relativeChartRayReducedIso ℂ (toricEnumeratedRayIncidence fan charts)
      (toricEnumeratedNegative fan b m) anchor degree

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  (surjective : Function.Surjective charts)

/-- Every sheaf-cohomology degree, all integral characters, and the actual
negative-ray reduced cochain groups. The isomorphism is additive. -/
def toricCartierCohomologyNegativeRayIso (anchor : Index) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ)
        (fun character => ↑(toricNegativeRayReduced fan charts b character degree))) :=
  toricCartierCohomologyWeightSumIso fan nonempty regular charts surjective b degree ≪≫
    CechDirectSumHomology.directSumIso
      (fun character => (toricCechWeightComplex fan charts b character).homology degree)
      (fun character => toricNegativeRayReduced fan charts b character degree)
      (fun character => toricCechWeightRayReducedIso fan charts b character anchor degree)

include regular surjective in
/-- For a finite regular fan, the enumerated negative-ray complex has
exactly the nonempty ray sets of actual cones contained in the chosen
negative vertices. This is a proved geometric identification. -/
theorem toricEnumeratedNegativeFace_iff_cone_raySet
    (rays : Finset (NegativeRay (toricEnumeratedNegative fan b m))) :
    rays ∈ negativeRayComplex (toricEnumeratedRayIncidence fan charts)
      (toricEnumeratedNegative fan b m) ↔
      rays.Nonempty ∧ ∃ cone : fan.cones, ∀ ray : fan.Ray,
        ray.toCone ≤ cone ↔
          ∃ index ∈ rays, toricFiniteRayEquiv fan index.val = ray := by
  constructor
  · rintro ⟨rays_nonempty, chart, contains⟩
    let selected : Set fan.Ray :=
      {ray | ∃ index ∈ rays, toricFiniteRayEquiv fan index.val = ray}
    have inChart : ∀ ray ∈ selected, ray.toCone ≤ charts chart := by
      rintro ray ⟨index, present, rfl⟩
      exact contains index present
    obtain ⟨face, _, exactRays⟩ := exists_cone_raySet_eq_of_subset fan regular
      (charts chart) selected inChart
    exact ⟨rays_nonempty, face, exactRays⟩
  · rintro ⟨rays_nonempty, cone, exactRays⟩
    obtain ⟨chart, rfl⟩ := surjective cone
    refine ⟨rays_nonempty, chart, ?_⟩
    intro index present
    exact (exactRays (toricFiniteRayEquiv fan index.val)).mpr ⟨index, present, rfl⟩

/-- A nonempty fan provides an actual chart anchor under any surjective
chart enumeration; no negative-ray nonemptiness is inferred. -/
def toricCechAnchor : Index :=
  Classical.choose (surjective (Classical.choice nonempty))

/-- The full affine enumeration discharges the cover and anchor interfaces.
The target still ranges over the complete integral character lattice. -/
def toricCartierCohomologyAllNegativeRaysIso (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ) (fun character =>
        ↑(toricNegativeRayReduced fan (toricFiniteCechCharts fan) b character degree))) :=
  toricCartierCohomologyNegativeRayIso fan (toricFiniteCechCharts fan) b nonempty regular
    (toricFiniteCechCharts_surjective fan)
    (toricCechAnchor fan (toricFiniteCechCharts fan) nonempty
      (toricFiniteCechCharts_surjective fan)) degree

end ToricPower
