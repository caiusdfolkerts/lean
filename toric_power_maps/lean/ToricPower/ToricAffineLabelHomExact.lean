module

public import ToricPower.AffineOpenLabelHomExact
public import ToricPower.ToricSeparated

/-!
# Exactness of actual label Hom on every toric affine chart

Every chart of the genuine fan scheme is an integral affine scheme, and
its inclusion is affine because the genuine fan scheme is separated.
Consequently the local Hom exactness theorem applies without an assumed
geometric exactness or acyclicity hypothesis. The label functor and all
its incidence maps remain arbitrary actual invertible-sheaf data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric

namespace ToricPower

/-- Any map from an affine scheme to a separated scheme is affine. -/
theorem affineSource_toSeparated_isAffineHom {U X : Scheme} [IsAffine U]
    [X.IsSeparated] (f : U ⟶ X) : IsAffineHom f := by
  letI : IsAffineHom (f ≫ terminal.from X) := by
    rw [terminal.comp_from]
    infer_instance
  exact IsAffineHom.of_comp f (terminal.from X)

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Actual toric chart inclusions are affine; separation is proved for
all fans upstream, with no completeness or regularity premise. -/
theorem toricChartInclusion_isAffineHom (fan : Fan i) (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := by
  letI := fan.algebraicRealization_isSeparated
  exact affineSource_toSeparated_isAffineHom (fan.affineToricChartι cone)

/-- The complete actual Hom diagram is exact on every actual toric
chart direct image, for arbitrary invertible labels and every incidence. -/
theorem toricChartLabelHom_exact (fan : Fan i) (cone : fan.cones)
    {C : Type} [Category.{0} C] (P : Cᵒᵖ ⥤ fan.algebraicRealization.Modules)
    (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      fan.algebraicRealization (P.obj (op c))) :
    letI := toricChartInclusion_isAffineHom fan cone
    PreservesFiniteLimits (quasicoherentOpenLabelHom ℂ (fan.affineToricChartι cone) P) ∧
      PreservesFiniteColimits (quasicoherentOpenLabelHom ℂ (fan.affineToricChartι cone) P) := by
  letI := toricChartInclusion_isAffineHom fan cone
  exact quasicoherentOpenLabelHom_exact ℂ (fan.affineToricChartι cone) P invertible

end ToricPower
