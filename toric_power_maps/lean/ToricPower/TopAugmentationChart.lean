module

public import ToricPower.TopHomologyFunctor
public import ToricPower.SingleAugmentationComponent

/-!
# The original top quotient in a canonical augmented chart

An exact functor, a specified complex isomorphism, and a specified
single-target quasi-isomorphism determine a canonical homology frame.
This generic identity retains the actual degree component of that map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (K : CochainComplex C ℕ) {L : CochainComplex D ℕ}
  {M : D} {n : ℕ}
  (e : (F.mapHomologicalComplex (.up ℕ)).obj K ≅ L)
  (f : L ⟶ (HomologicalComplex.single D (.up ℕ) n).obj M) [QuasiIso f]

/-- The original exact-functor, complex, and augmentation comparisons. -/
def topAugmentationChartIso : F.obj (K.homology n) ≅ M :=
  ((K.sc n).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℕ) n).mapIso e ≪≫
      homologyIsoOfQuasiIsoToSingle f

theorem topAugmentationChartIso_quotient (outgoing : K.d n (n+1) = 0) :
    F.map (K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv) ≫
      (topAugmentationChartIso F K e f).hom =
        e.hom.f n ≫ singleAugmentationComponent f := by
  simp only [topAugmentationChartIso, homologyIsoOfQuasiIsoToSingle,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
    HomologicalComplex.homologyFunctor_map, Category.assoc]
  rw [← Category.assoc, map_topHomologyQuotient]
  simpa only [HomologicalComplex.homologyMap_comp,
    singleAugmentationComponent_comp, Category.assoc] using
      topHomologyQuotient_toComponent
        (mapComplex_top_differential F K n outgoing) (e.hom ≫ f)

end ToricPower

end
