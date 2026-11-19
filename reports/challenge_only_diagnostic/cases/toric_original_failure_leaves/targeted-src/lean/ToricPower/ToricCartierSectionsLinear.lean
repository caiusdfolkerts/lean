module

public import ToricPower.CechDivisorSections
public import ToricPower.FiniteAffineIntersectionSections
public import ToricPower.SchemeModulesBaseLinear
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

/-!
# Actual complex-linear Cartier section coordinates

The Laurent coefficient coordinates carry the usual complex scalars.
The actual section space carries scalars pulled back through the scheme's
specified structure morphism to `Spec ℂ`. The affine chart inclusion is
a morphism over that base, so its coordinate comparison intertwines these
two specified actions. This proves linearity of the existing section
coordinates, without transporting a new scalar structure onto either side.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open TauCeti.Toric

namespace ToricPower

section BaseSections
universe u
variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The base-field section functor uses precisely restriction of the
specified global scalar, on every actual open. -/
theorem schemeBaseSections_smul (U : X.Opens) (M : X.Modules)
    (r : k) (x : (FiniteCover.schemeBaseSections k X U).obj M) :
    r • x = @SMul.smul Γ(X, U) Γ(M, U) inferInstance
      (X.presheaf.map U.leTop.op (Scheme.Modules.baseRingToGlobalSections k X r)) x := rfl

/-- The actual section functor is linear over the specified base field. -/
instance schemeBaseSections_linear (U : X.Opens) :
    (FiniteCover.schemeBaseSections k X U).Linear k where
  map_smul f r := by
    ext x
    exact Scheme.Modules.base_smul_app k X r f U x

end BaseSections

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The affine coordinate isomorphism respects the actual complex
structure map of the toric scheme. -/
theorem chartCoordinateSectionsEquiv_algebraMap (fan : Fan i) (cone : fan.cones) (a : ℂ) :
    chartCoordinateSectionsEquiv fan cone
        (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val) a) =
      fan.algebraicRealization.presheaf.map (fan.affineToricChartι cone).opensRange.leTop.op
        (Scheme.Modules.baseRingToGlobalSections ℂ fan.algebraicRealization a) := by
  let j := fan.affineToricChartι cone
  have over := congrArg Scheme.Hom.appTop
    (fan.affineToricChartι_comp_algebraicRealizationStructureMap cone)
  rw [Scheme.Hom.comp_appTop] at over
  have value := ConcreteCategory.congr_hom over ((Scheme.ΓSpecIso (.of ℂ)).inv a)
  have nat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val)))) a
  have pulled : j.appTop (Scheme.Modules.baseRingToGlobalSections ℂ fan.algebraicRealization a) =
      affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val) a) := by
    rw [Scheme.Modules.baseRingToGlobalSections_apply, fan.algebraicRealization_over]
    exact value.trans nat.symm
  have restricted := ConcreteCategory.congr_hom
    (openImmersion_sectionsIso_appLE j ⊤ le_top)
    (Scheme.Modules.baseRingToGlobalSections ℂ fan.algebraicRealization a)
  change (IsOpenImmersion.ΓIsoTop j).hom (j.appTop
    (Scheme.Modules.baseRingToGlobalSections ℂ fan.algebraicRealization a)) = _ at restricted
  change (IsOpenImmersion.ΓIsoTop j).hom
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
      (algebraMap ℂ (affineCoordinateRing fan.lattice cone.val) a)) = _
  rw [← pulled]
  exact restricted

/-- The pre-existing coefficient-to-coordinate-ring equivalence is
linear for the ordinary complex actions on its two sides. -/
def toricDivisorCoefficientRingLinearEquiv (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    (ToricChartDivisorWeight fan b cone →₀ ℂ) ≃ₗ[ℂ]
      affineCoordinateRing fan.lattice cone.val :=
  (Finsupp.domLCongr (R := ℂ) (toricChartDivisorShiftEquiv fan regular b cone)).trans
    (MonoidAlgebra.coeffLinearEquiv ℂ).symm

/-- The genuine Cartier frame is linear from ordinary coordinate-ring
scalars to the actual complex section action. -/
def toricDivisorOpenFrameLinearEquiv (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    affineCoordinateRing fan.lattice cone.val ≃ₗ[ℂ]
      (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  refine { toAddEquiv := toricDivisorOpenFrameEquiv fan nonempty regular b cone
           map_smul' := ?_ }
  intro a p
  let frame := ((SheafOfModules.evaluation
    (fan.algebraicRealization.ringCatSheaf.over (fan.affineToricChartι cone).opensRange)
    (op (Over.mk (𝟙 (fan.affineToricChartι cone).opensRange)))).mapIso
      (invariantCartierSheafChartTrivialization fan nonempty regular b cone)).toLinearEquiv
  change frame (chartCoordinateSectionsEquiv fan cone (a • p)) = _
  rw [Algebra.smul_def, map_mul, chartCoordinateSectionsEquiv_algebraMap]
  exact frame.map_smul _ _

/-- The actual character-section coordinates are complex-linear for the
specified scheme structure and the ordinary complex coefficient action. -/
def toricDivisorSectionCoefficientsLinearEquiv (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (ToricChartDivisorWeight fan b cone →₀ ℂ) ≃ₗ[ℂ]
      (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf :=
  (toricDivisorCoefficientRingLinearEquiv fan regular b cone).trans
    (toricDivisorOpenFrameLinearEquiv fan nonempty regular b cone)

/-- The linear comparison is exactly the previously checked additive
comparison, so all existing restriction and monomial formulas apply. -/
theorem toricDivisorSectionCoefficientsLinearEquiv_toAddEquiv (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    (toricDivisorSectionCoefficientsLinearEquiv fan nonempty regular b cone).toAddEquiv =
      toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone := rfl

end ToricPower
