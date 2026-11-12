module

public import ToricPower.LatticeTraceRetraction
public import ToricPower.RestrictedFan
public import ToricPower.SubfanOpenImmersion

/-!
# An open neighbourhood with the transverse torus directions

Keep the cones contained in `W`, but retain the entire original lattice.
Their toric variety is an actual open subscheme of the original toric
variety. The linear toric subvariety maps to this open neighbourhood,
and the integral complement gives an actual scheme retraction onto it.

This construction does not assert a derived restriction theorem. It
provides the geometric maps on which the transverse Laurent-coordinate
and finite Koszul constructions are based.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The cones contained in `W`, with the original ambient lattice. -/
def linearAmbientFan (fan : Fan i) (W : Submodule ℝ V) : Fan i where
  lattice := fan.lattice
  cones := {σ | σ ∈ fan.cones ∧ σ ≤ (W : PointedCone ℝ V)}
  finite_cones := fan.finite_cones.subset (fun _ h => h.1)
  isToricCone := by
    intro σ hσ
    exact fan.isToricCone hσ.1
  mem_of_isFaceOf := by
    intro σ τ hσ hface
    exact ⟨fan.mem_of_isFaceOf hσ.1 hface, hface.le.trans hσ.2⟩
  inf_isFaceOf_left := by
    intro σ τ hσ hτ
    exact fan.inf_isFaceOf_left hσ.1 hτ.1

@[simp]
theorem mem_linearAmbientFan (fan : Fan i) (W : Submodule ℝ V)
    (σ : PointedCone ℝ V) :
    σ ∈ (linearAmbientFan fan W).cones ↔
      σ ∈ fan.cones ∧ σ ≤ (W : PointedCone ℝ V) := Iff.rfl

theorem linearAmbientFan_isRegular (fan : Fan i) (regular : fan.IsRegular)
    (W : Submodule ℝ V) : (linearAmbientFan fan W).IsRegular := by
  apply Fan.isRegular_iff.mpr
  intro σ hσ
  exact Fan.isRegular_iff.mp regular σ hσ.1

/-- The actual open immersion supplied by the retained subfan. -/
def linearAmbientOpenInclusion (fan : Fan i) (W : Submodule ℝ V) :
    (linearAmbientFan fan W).algebraicRealization ⟶ fan.algebraicRealization :=
  subfanSchemeMap (linearAmbientFan fan W) fan (fun _ h => h.1)

theorem linearAmbientOpenInclusion_isOpenImmersion (fan : Fan i)
    (W : Submodule ℝ V) : IsOpenImmersion (linearAmbientOpenInclusion fan W) :=
  subfanSchemeMap_isOpenImmersion (linearAmbientFan fan W) fan (fun _ h => h.1)

/-- The saturated-trace fan maps into the same-lattice open neighbourhood. -/
def restrictedFanAmbientLift (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    FanHom (restrictedFan fan W rational) (linearAmbientFan fan W) where
  latticeMap := (latticeTrace i W).subtype.toAddMonoidHom
  realMap := W.subtype
  map_lattice _ := rfl
  map_cone := by
    rintro τ ⟨σ, ⟨hσ, hσW⟩, rfl⟩
    exact ⟨σ, ⟨hσ, hσW⟩, (cone_map_comap_subtype W σ hσW).le⟩

/-- The original inclusion factors through the actual open neighbourhood. -/
theorem restrictedFanAmbientLift_comp_open (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    (restrictedFanAmbientLift fan W rational).algebraicMap ≫
        linearAmbientOpenInclusion fan W =
      (restrictedFanInclusion fan W rational).algebraicMap := by
  change (restrictedFanAmbientLift fan W rational).algebraicMap ≫
      (subfanFanHom (linearAmbientFan fan W) fan (fun _ h => h.1)).algebraicMap = _
  rw [← FanHom.algebraicMap_comp]
  congr 1
  apply FanHom.ext
  rw [FanHom.comp_latticeMap]
  rfl

/-- The integral projection gives a fan map from the open neighbourhood
back to the saturated-trace fan. -/
def linearAmbientProjectionFan (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    FanHom (linearAmbientFan fan W) (restrictedFan fan W rational) where
  latticeMap := (latticeTraceProjection fan.lattice W).toAddMonoidHom
  realMap := latticeTraceRealProjection fan.lattice W
  map_lattice n := latticeTraceRealProjection_lattice fan.lattice W n
  map_cone := by
    intro σ hσ
    refine ⟨σ.comap W.subtype, ⟨σ, hσ, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have he := latticeTraceRealProjection_subtype fan.lattice W rational ⟨x, hσ.2 hx⟩
    change ((latticeTraceRealProjection fan.lattice W x : W) : V) ∈ σ
    rw [he]
    exact hx

/-- The fan retraction is literal identity on the saturated lattice. -/
theorem linearAmbientProjectionFan_comp_lift (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    (linearAmbientProjectionFan fan W rational).comp
        (restrictedFanAmbientLift fan W rational) =
      FanHom.id (restrictedFan fan W rational) := by
  apply FanHom.ext
  rw [FanHom.comp_latticeMap, FanHom.id_latticeMap]
  apply DFunLike.ext
  intro n
  exact latticeTraceProjection_trace fan.lattice W n

/-- The resulting actual scheme morphism is a retraction, independently
of smoothness, properness or completeness of the original fan. -/
theorem restrictedFanAmbientLift_comp_projection (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    (restrictedFanAmbientLift fan W rational).algebraicMap ≫
        (linearAmbientProjectionFan fan W rational).algebraicMap =
      𝟙 (restrictedFan fan W rational).algebraicRealization := by
  rw [← FanHom.algebraicMap_comp, linearAmbientProjectionFan_comp_lift,
    FanHom.algebraicMap_id]

end ToricPower

end
