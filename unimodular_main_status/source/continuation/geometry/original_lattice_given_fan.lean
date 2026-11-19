module

public import Continuation.Geometry.OriginalLatticeBase
public import Continuation.Geometry.OriginalLatticeRays
public import Continuation.Geometry.OriginalLatticeInputs
public import Unimodular.FanTransport
public import Continuation.Divisor.FanoClosure

@[expose] public section

/-!
# The actual scheme interface for an arbitrary given original-lattice fan

The recovered general fan transport is applied to the integral basis. Its
inverse recovers every cone of the given fan exactly. The actual scheme
from the finite regular-fan interface is then proved to be the original
semigroup-chart gluing, over the unchanged field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry AlgebraicGeometry CategoryTheory
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (Φ : Fan ι) (hcomplete : Φ.IsComplete)

/-- The whole coordinate image of the given fan, with no omitted cones. -/
def coordinateFan (_hcomplete : Φ.IsComplete) :
    Fan (Unimodular.FanBridge.standardEmbedding n) := by
  letI : FiniteDimensional ℝ V := Φ.lattice.finiteDimensional
  exact Unimodular.FanTransport.transport b.equivFun.toAddEquiv
    (realCoordinates b Φ.lattice) (realCoordinates_lattice b Φ.lattice) Φ

/-- This is the actual integral and real equivalence of the given fans. -/
def coordinateFanEquiv : FanEquiv Φ (coordinateFan b Φ hcomplete) := by
  letI : FiniteDimensional ℝ V := Φ.lattice.finiteDimensional
  exact Unimodular.FanTransport.equivalence b.equivFun.toAddEquiv
    (realCoordinates b Φ.lattice) (realCoordinates_lattice b Φ.lattice) Φ

theorem coordinateFan_complete : (coordinateFan b Φ hcomplete).IsComplete :=
  (coordinateFanEquiv b Φ hcomplete).isComplete_iff.mpr hcomplete

theorem coordinateFan_regular_iff :
    (coordinateFan b Φ hcomplete).IsRegular ↔ Φ.IsRegular :=
  (coordinateFanEquiv b Φ hcomplete).isRegular_iff

/-- The checked finite geometric interface of the actual coordinate fan. -/
def geometricOriginalFan (hregular : Φ.IsRegular) : SmoothCompleteFan n :=
  Unimodular.FanInterfaces.geometricFan (coordinateFan b Φ hcomplete)
    (coordinateFan_complete b Φ hcomplete)
    ((coordinateFan_regular_iff b Φ hcomplete).mpr hregular)

theorem dictionary_geometricOriginalFan (hregular : Φ.IsRegular) :
    Unimodular.FanInterfaces.dictionaryToricFan
      (geometricOriginalFan b Φ hcomplete hregular) = coordinateFan b Φ hcomplete :=
  Unimodular.FanInterfaces.dictionaryToricFan_geometricFan _ _ _

/-- Returning to the original lattice recovers the entire original fan,
not only its ray configuration or its maximal cones. -/
theorem originalFan_geometricOriginalFan (hregular : Φ.IsRegular) :
    originalFan b Φ.lattice (geometricOriginalFan b Φ hcomplete hregular) = Φ := by
  letI : FiniteDimensional ℝ V := Φ.lattice.finiteDimensional
  let e := coordinateFanEquiv b Φ hcomplete
  apply Fan.ext
  ext C
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [dictionary_geometricOriginalFan] at hD
    have he : e.symm.realEquiv = (realCoordinates b Φ.lattice).symm := by
      rw [FanEquiv.symm_realEquiv]
      rfl
    simpa only [he] using (e.symm.map_mem D).mpr hD
  · intro hC
    refine ⟨C.map (realCoordinates b Φ.lattice).toLinearMap, ?_, ?_⟩
    · rw [dictionary_geometricOriginalFan]
      exact (e.map_mem C).mpr hC
    · change (C.map (realCoordinates b Φ.lattice).toLinearMap).map
        (realCoordinates b Φ.lattice).symm.toLinearMap = C
      rw [PointedCone.map_map]
      have hid : (realCoordinates b Φ.lattice).symm.toLinearMap.comp
          (realCoordinates b Φ.lattice).toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [hid, PointedCone.map_id]

theorem geometricOriginalFan_ray_iff (hregular : Φ.IsRegular) (w : N) :
    b.equivFun w ∈ (geometricOriginalFan b Φ hcomplete hregular).rays ↔
      Unimodular.ConeBases.IsRay Φ w := by
  rw [← originalFan_ray_iff b Φ.lattice, originalFan_geometricOriginalFan]

theorem geometricOriginalFan_ray_image (hregular : Φ.IsRegular) :
    b.equivFun '' {w : N | Unimodular.ConeBases.IsRay Φ w} =
      ((geometricOriginalFan b Φ hcomplete hregular).rays : Set (Lattice n)) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (geometricOriginalFan_ray_iff b Φ hcomplete hregular w).mpr hw
  · intro hy
    refine ⟨b.equivFun.symm y, ?_, b.equivFun.apply_symm_apply y⟩
    exact (geometricOriginalFan_ray_iff b Φ hcomplete hregular _).mp
      (by simpa only [LinearEquiv.apply_symm_apply, Finset.mem_coe] using hy)

theorem geometricOriginalFan_uniform (hregular : Φ.IsRegular)
    (hU : Unimodular.IntegralRigidity.Uniform b
      (fun w : {w : N | Unimodular.ConeBases.IsRay Φ w} => w.val)) :
    Unimodular.IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun w : ((geometricOriginalFan b Φ hcomplete hregular).rays :
        Set (Lattice n)) => w.val) := by
  intro a
  let a' : Fin n → {w : N | Unimodular.ConeBases.IsRay Φ w} := fun i =>
    ⟨b.equivFun.symm (a i).val,
      (geometricOriginalFan_ray_iff b Φ hcomplete hregular _).mp
        (by simpa only [LinearEquiv.apply_symm_apply, Finset.mem_coe] using (a i).property)⟩
  have h := hU a'
  change |b.det (fun i => (a' i).val)| ≤ 1 at h
  rw [← determinant_in_coordinates b (fun i => (a' i).val)] at h
  change |(Pi.basisFun ℤ (Fin n)).det (fun i => (a i).val)| ≤ 1
  have he : b.equivFun ∘ (fun i => (a' i).val) = (fun i => (a i).val) := by
    funext i
    exact b.equivFun.apply_symm_apply (a i).val
  rw [he] at h
  exact h

theorem geometricOriginalFan_ray_card (hregular : Φ.IsRegular) :
    (geometricOriginalFan b Φ hcomplete hregular).rays.card =
      Set.ncard {w : N | Unimodular.ConeBases.IsRay Φ w} := by
  rw [← Set.ncard_coe_finset, ← geometricOriginalFan_ray_image]
  exact Set.ncard_image_of_injective _ b.equivFun.injective

/-- The actual original cone set is precisely the cone set indexing the
actual original-character semigroup charts of this realization. -/
theorem givenFan_cones_eq_chart_cones (hregular : Φ.IsRegular) :
    Φ.cones = Set.range (fun s : OriginalConeIndex b
      (geometricOriginalFan b Φ hcomplete hregular) => latticeCone (ι := ι) s.val) := by
  calc
    Φ.cones = (originalFan b Φ.lattice
        (geometricOriginalFan b Φ hcomplete hregular)).cones :=
      congrArg (fun G : Fan ι => G.cones)
        (originalFan_geometricOriginalFan b Φ hcomplete hregular).symm
    _ = _ := originalFan_cones_eq_range b Φ.lattice _

/-- The actual original semigroup gluing is the constructed actual scheme
in the category over k. This is proved, not supplied as an input. -/
def givenFanGluingOverIso (hregular : Φ.IsRegular) (k : Type u) [CommRing k] :
    Over.mk (originalSchemeStructureMap b Φ.lattice k
      (geometricOriginalFan b Φ hcomplete hregular)) ≅
        (geometricOriginalFan b Φ hcomplete hregular).fanSchemeOver k :=
  originalGluingOverIso b Φ.lattice k _

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalFan_geometricOriginalFan
#print axioms PaperVerification.OriginalLatticeCharts.geometricOriginalFan_uniform
#print axioms PaperVerification.OriginalLatticeCharts.givenFanGluingOverIso
