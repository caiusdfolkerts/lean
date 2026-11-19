module

public import Continuation.Geometry.OriginalLatticeBase
public import Continuation.Geometry.SchemeIsoTransport

/-!
# Geometry on the chosen original-lattice colimit itself

The original character-monoid diagram has its own categorical colimit and
its own glued structural map. This module transports ordinary geometry and
the intrinsic top-Kähler dual to that very object, using the proved scheme
isomorphism over the field. Positivity is asserted literally on the chosen
original colimit, rather than only on an isomorphic representative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace PaperVerification.OriginalLatticeCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open TauCeti.Toric TauCeti.AlgebraicGeometry Unimodular.NefBig

variable {N : Type u} [AddCommGroup N]
  {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
  {ι : N →+ V} (hi : IsIntegralLattice ι)
  (k : Type u) [Field k] (F : SmoothCompleteFan n)

/-- The independently chosen colimit of the actual original dual-cone charts. -/
abbrev originalScheme : Scheme.{u} := colimit (originalDiagram b hi k F)

instance originalScheme_over :
    (originalScheme b hi k F).Over (Spec (CommRingCat.of k)) :=
  ⟨originalSchemeStructureMap b hi k F⟩

instance originalGluingIso_isOver :
    (originalGluingIso b hi k F).hom.IsOver (Spec (CommRingCat.of k)) :=
  ⟨originalGluingIso_toSpec b hi k F⟩

instance originalScheme_isIntegral : IsIntegral (originalScheme b hi k F) :=
  IsIntegral.of_isIso (originalGluingIso b hi k F).inv

/-- Smoothness of the literal glued structural map. -/
theorem originalScheme_smooth : Smooth (originalSchemeStructureMap b hi k F) := by
  letI : Smooth (F.fanSchemeStructureMap k) := fanScheme_smooth F k
  letI : Smooth (originalGluingIso b hi k F).hom := inferInstance
  rw [← originalGluingIso_toSpec b hi k F]
  infer_instance

/-- Properness transports to the literal glued structural map. -/
theorem originalScheme_proper (hF : IsProper (F.fanSchemeStructureMap k)) :
    IsProper (originalSchemeStructureMap b hi k F) := by
  letI := hF
  rw [← originalGluingIso_toSpec b hi k F]
  infer_instance

/-- The dimension is that of the original rank-n lattice. -/
theorem originalScheme_dimension : topologicalKrullDim (originalScheme b hi k F) = n :=
  (originalGluingIso b hi k F).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
    (F.fanScheme_topologicalKrullDim k F.isPure)

/-- The actual canonical line bundle on the original colimit, defined from
its own universal differential sheaf. -/
def originalCanonicalLineBundle : InvertibleSheaf (originalScheme b hi k F) := by
  refine ⟨topDifferentialSheaf k (originalScheme b hi k F) n, ?_⟩
  letI : SheafOfModules.isInvertible (F.fanScheme k)
      (topDifferentialSheaf k (F.fanScheme k) n) := (canonicalLineBundle F k).property
  let E := topDifferentialSheafPullbackIso (originalGluingIso b hi k F).hom n k
  exact (SheafOfModules.isInvertible (originalScheme b hi k F)).prop_of_iso E
    (SheafOfModules.isInvertible_pullback (originalGluingIso b hi k F).hom
      (canonicalLineBundle F k).obj)

/-- The intrinsic anticanonical line bundle on the original colimit. -/
def originalAnticanonicalLineBundle : InvertibleSheaf (originalScheme b hi k F) :=
  InvertibleSheaf.dual (originalCanonicalLineBundle b hi k F)

theorem originalAnticanonicalLineBundle_obj :
    (originalAnticanonicalLineBundle b hi k F).obj =
      (topDifferentialSheaf k (originalScheme b hi k F) n).dual := by
  exact InvertibleSheaf.dual_obj (originalCanonicalLineBundle b hi k F)

/-- The actual canonical pullback comparison, now with both ends packaged
as the intrinsic ordinary anticanonical line bundles. -/
def originalAnticanonicalPullbackIso :
    (Scheme.Modules.pullback (originalGluingIso b hi k F).hom).obj
        (anticanonicalLineBundle F k).obj ≅
      (originalAnticanonicalLineBundle b hi k F).obj :=
  fanAnticanonicalPullbackIso F k (originalGluingIso b hi k F).hom ≪≫
    Scheme.Modules.isoOfSheafIso _
      (eqToIso (originalAnticanonicalLineBundle_obj b hi k F)).symm

/-- Ordinary nefness and bigness on the chosen original colimit itself. -/
theorem originalScheme_anticanonical_nef_and_big
    (hnef : AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj)
    (hbig : IsBig k (anticanonicalLineBundle F k).obj) :
    AlgebraicGeometry.IsNef (baseField := k)
        (originalAnticanonicalLineBundle b hi k F).obj ∧
      IsBig k (originalAnticanonicalLineBundle b hi k F).obj := by
  let E := originalAnticanonicalPullbackIso b hi k F
  exact ⟨AlgebraicGeometry.IsNef.of_iso E
      ((isNef_pullback_schemeIso_iff k (originalGluingIso b hi k F)
        (anticanonicalLineBundle F k)).mpr hnef),
    (isBig_iff_of_iso k E).mp
      ((isBig_pullback_schemeIso_iff k (originalGluingIso b hi k F)
        (anticanonicalLineBundle F k)).mpr hbig)⟩

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalScheme_smooth
#print axioms PaperVerification.OriginalLatticeCharts.originalScheme_dimension
#print axioms PaperVerification.OriginalLatticeCharts.originalAnticanonicalPullbackIso
#print axioms PaperVerification.OriginalLatticeCharts.originalScheme_anticanonical_nef_and_big
