module

public import ToricPower.GeometricCore
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # The actual open immersion associated to a subfan

The map is induced by the identity on the lattice. Its chart restrictions,
injectivity and range are proved directly from the actual fan gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan completion : Fan i)
  (hsub : fan.cones ⊆ completion.cones)

def subfanFanHom : FanHom fan completion where
  latticeMap := AddMonoidHom.id N
  realMap := LinearMap.id
  map_lattice _ := rfl
  map_cone := by
    intro σ hσ
    exact ⟨σ, hsub hσ, by rw [PointedCone.map_id]⟩

theorem subfanFanHom_leastCone (σ : fan.cones) :
    (subfanFanHom fan completion hsub).leastCone σ.property = σ.val := by
  apply le_antisymm
  · apply FanHom.leastCone_le _ σ.property (hsub σ.property)
    change σ.val.map LinearMap.id ≤ σ.val
    rw [PointedCone.map_id]
  · have h := (subfanFanHom fan completion hsub).map_le_leastCone σ.property
    change σ.val.map LinearMap.id ≤ _ at h
    simpa only [PointedCone.map_id] using h

def subfanSchemeMap : fan.algebraicRealization ⟶ completion.algebraicRealization :=
  (subfanFanHom fan completion hsub).algebraicMap

theorem subfanSchemeMap_chart (σ : fan.cones) :
    fan.affineToricChartι σ ≫ subfanSchemeMap fan completion hsub =
      completion.affineToricChartι ⟨σ.val, hsub σ.property⟩ := by
  have h := FanHom.affineToricChartι_comp_algebraicMap_of_leastCone_eq
    (subfanFanHom fan completion hsub) σ ⟨σ.val, hsub σ.property⟩
    (subfanFanHom_leastCone fan completion hsub σ) (fun _ hx => hx)
  simpa only [subfanSchemeMap, subfanFanHom, affineToricSchemeMap_id,
    Category.id_comp] using h

theorem subfanSchemeMap_chart_apply (σ : fan.cones) (x : fan.affineToricChart σ) :
    subfanSchemeMap fan completion hsub (fan.affineToricChartι σ x) =
      completion.affineToricChartι ⟨σ.val, hsub σ.property⟩ x :=
  congrArg (fun f => f x) (subfanSchemeMap_chart fan completion hsub σ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem subfanSchemeMap_injective :
    Function.Injective (subfanSchemeMap fan completion hsub) := by
  intro x y h
  obtain ⟨σ, x, rfl⟩ := fan.exists_affineToricChartι_apply_eq x
  obtain ⟨τ, y, rfl⟩ := fan.exists_affineToricChartι_apply_eq y
  rw [subfanSchemeMap_chart_apply, subfanSchemeMap_chart_apply] at h
  obtain ⟨z, hx, hy⟩ :=
    (completion.affineToricChartι_eq_affineToricChartι_iff
      (σ := ⟨σ.val, hsub σ.property⟩) (τ := ⟨τ.val, hsub τ.property⟩) x y).mp h
  apply (fan.affineToricChartι_eq_affineToricChartι_iff (σ := σ) (τ := τ) x y).mpr
  refine ⟨z, ?_, ?_⟩
  · simpa only [Fan.affineToricOverlapLeft_def] using hx
  · simpa only [Fan.affineToricOverlapRight_def] using hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem subfanSchemeMap_isOpenImmersion :
    IsOpenImmersion (subfanSchemeMap fan completion hsub) := by
  apply IsOpenImmersion.of_openCover_source _ fan.affineToricOpenCover
    (subfanSchemeMap_injective fan completion hsub)
  intro σ
  change IsOpenImmersion (fan.affineToricChartι σ ≫ subfanSchemeMap fan completion hsub)
  rw [subfanSchemeMap_chart]
  infer_instance

/-- The image consists exactly of the retained affine toric charts. -/
theorem subfanSchemeMap_range :
    Set.range (subfanSchemeMap fan completion hsub) =
      ⋃ σ : fan.cones, Set.range (completion.affineToricChartι ⟨σ.val, hsub σ.property⟩) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, x, rfl⟩ := fan.exists_affineToricChartι_apply_eq x
    exact Set.mem_iUnion.mpr ⟨σ, x, (subfanSchemeMap_chart_apply fan completion hsub σ x).symm⟩
  · intro hy
    obtain ⟨σ, x, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨fan.affineToricChartι σ x, subfanSchemeMap_chart_apply fan completion hsub σ x⟩

end ToricPower
