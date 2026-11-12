module

public import ToricPower.CartierAtlasSectionGluing

/-!
# Extending a section across a Cartier boundary

An effective Cartier boundary whose complement is an affine chart lets
every quasi-coherent section on that chart extend as a map from a line
bundle. The exponent is constructed by two finite pole-clearing steps.
The resulting map agrees with the original section in a genuine local
frame, not merely after passing to rational sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ToricPower.CartierEquationAtlas

universe u v

variable {X : Scheme.{u}} [IsIntegral X] (atlas : CartierEquationAtlas.{u,v} X)

/-- Negating the `n`th power of the Cartier equations. Its local frame is
the `n`th power of the original equation. -/
def negativePower (n : ℕ) : CartierEquationAtlas.{u,v} X where
  Index := atlas.Index
  chart := atlas.chart
  covers := atlas.covers
  nonempty_chart := atlas.nonempty_chart
  equation j := (atlas.equation j ^ n)⁻¹
  transition j k := (atlas.transition j k ^ n)⁻¹
  transition_equation j k := by
    letI := atlas.nonempty_chart j
    letI := atlas.nonempty_chart k
    letI := nonempty_integral_open_intersection (atlas.chart j) (atlas.chart k)
    simpa only [map_inv, map_pow, mul_pow, mul_inv_rev, mul_comm] using
      congrArg (fun value => (value ^ n)⁻¹) (atlas.transition_equation j k)

/-- The transition of the new frames is the positive power of the old
equation transition; this records the sign used in pole clearing. -/
theorem negativePower_frameRatio (n : ℕ) (j k : atlas.Index) :
    letI := atlas.nonempty_chart j
    letI := atlas.nonempty_chart k
    letI := nonempty_integral_open_intersection (atlas.chart j) (atlas.chart k)
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField X
      (atlas.chart j ⊓ atlas.chart k) (atlas.transition j k ^ n) *
      (atlas.negativePower n).equation j = (atlas.negativePower n).equation k := by
  letI := atlas.nonempty_chart j
  letI := atlas.nonempty_chart k
  letI := nonempty_integral_open_intersection (atlas.chart j) (atlas.chart k)
  change _ * (atlas.equation j ^ n)⁻¹ = (atlas.equation k ^ n)⁻¹
  rw [map_pow, ← atlas.transition_equation j k, mul_pow]
  simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- An actual section on the distinguished chart is the image of an
actual local basis of a global Cartier line bundle. -/
theorem exists_cartier_section_extension [Finite atlas.Index]
    (affine : ∀ j, IsAffineOpen (atlas.chart j))
    (affineOverlap : ∀ j k, IsAffineOpen (atlas.chart j ⊓ atlas.chart k))
    (chosen : atlas.Index) (f : ∀ j, Γ(X, atlas.chart j))
    (principal : ∀ j, X.basicOpen (f j) = atlas.chart j ⊓ atlas.chart chosen)
    (equations : ∀ j k,
      PoleClearing.restrictRing (inf_le_left : atlas.chart j ⊓ atlas.chart k ≤ atlas.chart j)
          (f j) =
        (atlas.transition j k : Γ(X, atlas.chart j ⊓ atlas.chart k)) *
          PoleClearing.restrictRing
            (inf_le_right : atlas.chart j ⊓ atlas.chart k ≤ atlas.chart k) (f k))
    (normalized : f chosen = 1) (M : X.Modules) [M.IsQuasicoherent]
    (s : Γ(M, atlas.chart chosen)) :
    ∃ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
      (frame : (SheafOfModules.unit X.ringCatSheaf).over (atlas.chart chosen) ≅
        D.sheaf.over (atlas.chart chosen)) (mapping : D.sheaf ⟶ M),
      frame.hom ≫ mapping.over (atlas.chart chosen) =
        overSectionHom M (atlas.chart chosen) s := by
  obtain ⟨n, t, localValues, compatible⟩ := PoleClearing.exists_compatible_power_sections M
    atlas.chart affine affineOverlap (atlas.chart chosen) f principal atlas.transition equations s
  let power := atlas.negativePower n
  let mapping : power.cartierDivisor.sheaf ⟶ M := power.sectionMap M t
    (fun j k => atlas.transition j k ^ n) (atlas.negativePower_frameRatio n)
    (by simpa only [power, negativePower, Units.val_pow_eq_pow_val] using compatible)
  have chosenValue : t chosen = s := by
    let h : atlas.chart chosen ⊓ atlas.chart chosen ≤ atlas.chart chosen := inf_le_left
    letI : IsIso (homOfLE h) := homOfLE_isIso_of_eq _ (inf_idem _)
    apply (ConcreteCategory.bijective_of_isIso (M.presheaf.map (homOfLE h).op)).injective
    simpa only [normalized, map_one, one_pow, one_smul] using localValues chosen
  refine ⟨power.cartierDivisor, power.chartTrivialization chosen, mapping, ?_⟩
  have value := power.sectionMap_frame M t (fun j k => atlas.transition j k ^ n)
    (atlas.negativePower_frameRatio n)
    (by simpa only [power, negativePower, Units.val_pow_eq_pow_val] using compatible) chosen
  simpa only [mapping, power, negativePower, chosenValue] using value

end ToricPower.CartierEquationAtlas

end
