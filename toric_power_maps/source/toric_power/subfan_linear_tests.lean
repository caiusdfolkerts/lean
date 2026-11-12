module

public import ToricPower.RestrictedFan
public import ToricPower.SubfanOpenImmersion

/-! # Literal linear tests under an actual fan extension

Every linear test of an extending fan is already a linear test of the
original fan. Their saturated-trace fans form an actual subfan pair,
and the square of literal toric inclusions commutes. This is the
geometric interface needed by the noncomplete boundary-twist argument;
existence of a smooth completion is a separate theorem.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan extension : Fan i)
  (included : fan.cones ⊆ extension.cones)

include included

theorem subfan_isLinearSubspace (W : Submodule ℝ V)
    (linear : IsLinearSubspace extension W) : IsLinearSubspace fan W := by
  intro σ member
  exact fan.mem_of_isFaceOf member
    (extension.isFaceOf_of_le (included member) (linear σ (included member)) inf_le_left)

def subfanLinearSubspace (W : LinearSubspace extension) : LinearSubspace fan where
  space := W.space
  rational := W.rational
  linear := subfan_isLinearSubspace fan extension included W.space W.linear

theorem restrictedFan_cones_subset (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    (restrictedFan fan W rational).cones ⊆ (restrictedFan extension W rational).cones := by
  intro τ member
  obtain ⟨σ,hσ,contained,equal⟩ := (mem_restrictedFan_cones fan W rational τ).mp member
  exact (mem_restrictedFan_cones extension W rational τ).mpr
    ⟨σ,included hσ,contained,equal⟩

theorem subfanRestrictedInclusion_square (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    (subfanFanHom fan extension included).comp (restrictedFanInclusion fan W rational) =
      (restrictedFanInclusion extension W rational).comp
        (subfanFanHom (restrictedFan fan W rational) (restrictedFan extension W rational)
          (restrictedFan_cones_subset fan extension included W rational)) := by
  apply FanHom.ext
  ext a
  simp only [FanHom.comp_latticeMap,subfanFanHom,restrictedFanInclusion,
    AddMonoidHom.comp_apply,AddMonoidHom.id_apply]

/-- The actual scheme square used when comparing open restrictions of
linear toric subvarieties with their closures in an extension. -/
theorem subfanLinearToricInclusion_square (W : LinearSubspace extension) :
    linearToricInclusion fan (subfanLinearSubspace fan extension included W) ≫
        subfanSchemeMap fan extension included =
      subfanSchemeMap (restrictedFan fan W.space W.rational)
          (restrictedFan extension W.space W.rational)
          (restrictedFan_cones_subset fan extension included W.space W.rational) ≫
        linearToricInclusion extension W := by
  change (restrictedFanInclusion fan W.space W.rational).algebraicMap ≫
      (subfanFanHom fan extension included).algebraicMap =
    (subfanFanHom (restrictedFan fan W.space W.rational)
      (restrictedFan extension W.space W.rational)
      (restrictedFan_cones_subset fan extension included W.space W.rational)).algebraicMap ≫
      (restrictedFanInclusion extension W.space W.rational).algebraicMap
  rw [← FanHom.algebraicMap_comp,← FanHom.algebraicMap_comp,
    subfanRestrictedInclusion_square]

end ToricPower

end
