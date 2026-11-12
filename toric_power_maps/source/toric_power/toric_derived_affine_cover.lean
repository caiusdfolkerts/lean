module

public import ToricPower.ToricAffineLabelHomExact
public import ToricPower.AffineLocalizationLabelExact

/-!
# The actual finite toric cover for unbounded right derivation

Every cone contributes its literal affine chart open. These opens cover
the actual fan scheme, their inclusions are affine by separation, and
each is integral. The fan itself supplies their finite enumeration.
Thus the affine exactness hypotheses for the intrinsic label-Hom diagram
are discharged geometrically, without completeness or projectivity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- The actual open image of a fan chart. -/
def toricDerivedChartOpen (cone : fan.cones) : fan.algebraicRealization.Opens :=
  (fan.affineToricChartι cone).opensRange

instance toricDerivedChartOpen_isAffine (cone : fan.cones) :
    IsAffine (toricDerivedChartOpen fan cone).toScheme :=
  isAffineOpen_opensRange (fan.affineToricChartι cone)

instance toricDerivedChartOpen_isIntegral (cone : fan.cones) :
    IsIntegral (toricDerivedChartOpen fan cone).toScheme :=
  IsIntegral.of_isIso (fan.affineToricChartι cone).isoOpensRange.hom

instance toricDerivedChartOpen_isAffineHom (cone : fan.cones) :
    IsAffineHom (toricDerivedChartOpen fan cone).ι := by
  letI := fan.algebraicRealization_isSeparated
  exact affineSource_toSeparated_isAffineHom (toricDerivedChartOpen fan cone).ι

/-- Coverage is proved on actual points of the glued fan scheme. -/
theorem toricDerivedChartOpen_covers : IsOpenCover (toricDerivedChartOpen fan) := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  intro x _
  obtain ⟨cone, y, rfl⟩ := fan.exists_affineToricChartι_apply_eq x
  exact Opens.mem_iSup.mpr ⟨cone, y, rfl⟩

/-- A finite list containing every actual cone; no chosen subcover or
additional finiteness assumption enters the construction. -/
def toricDerivedChartList : List fan.cones :=
  letI : Fintype fan.cones := Fintype.ofFinite _
  Finset.univ.toList

theorem mem_toricDerivedChartList (cone : fan.cones) : cone ∈ toricDerivedChartList fan := by
  simp [toricDerivedChartList]

variable {C : Type} [Category.{0} C]
  (P : Cᵒᵖ ⥤ QCoh fan.algebraicRealization)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
    fan.algebraicRealization (P.obj (op c)).obj)

include invertible

/-- All local exactness required by the actual finite affine right
derivation follows from invertibility of the genuine labels. -/
theorem toricDerivedLabelLocalExact (cone : fan.cones) :
    PreservesFiniteLimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.homDiagram ℂ P) ∧
    PreservesFiniteColimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.homDiagram ℂ P) :=
  quasicoherentOpenLocalizationLabelHom_exact ℂ (toricDerivedChartOpen fan cone).ι P invertible

end ToricPower

end
