module

public import ToricPower.TopHomologyAugmentation
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The canonical top quotient under an exact functor

The comparison retains the canonical homology isomorphism and the
actual quotient from the cochain term. It applies equally to scalar
restriction, affine tilde, and open pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- The canonical comparison commutes with the genuine quotient from
cycles, not just with induced homology maps. -/
@[reassoc]
theorem mapHomologyIso_hom_homologyπ (S : ShortComplex C) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq F,
    S.homologyData.left.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    Category.assoc]
  change (S.homologyData.left.map F).cyclesIso.hom ≫
      F.map S.homologyData.left.π ≫ F.map S.homologyData.left.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
    F.map_comp, Category.assoc]

variable (K : CochainComplex C ℕ) (n : ℕ) (outgoing : K.d n (n+1) = 0)


include outgoing in
theorem mapComplex_top_differential : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d n (n+1) = 0 := by
  change F.map (K.d n (n+1)) = 0
  rw [outgoing, F.map_zero]

/-- Exact functors carry the actual top cochain quotient to the actual
top cochain quotient through their canonical homology comparison. -/
theorem map_topHomologyQuotient :
    F.map (K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv) ≫
        ((K.sc n).mapHomologyIso F).inv =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).pOpcycles n ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).isoHomologyι n (n+1) (by simp) (mapComplex_top_differential F K n outgoing)).inv := by
  letI : IsIso (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n) :=
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).isIso_iCycles n (n+1) (by simp) (mapComplex_top_differential F K n outgoing)
  have quotientK : K.iCycles n ≫ K.pOpcycles n ≫
      (K.isoHomologyι n (n+1) (by simp) outgoing).inv = K.homologyπ n := by
    rw [← HomologicalComplex.homology_π_ι_assoc,
      HomologicalComplex.isoHomologyι_hom_inv_id, Category.comp_id]
  have quotientL : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n ≫ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).pOpcycles n ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).isoHomologyι n (n+1) (by simp)
        (mapComplex_top_differential F K n outgoing)).inv = ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n := by
    rw [← HomologicalComplex.homology_π_ι_assoc,
      HomologicalComplex.isoHomologyι_hom_inv_id, Category.comp_id]
  have cycles : ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n :=
    ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) F
  have quotientMap : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n ≫
      ((K.sc n).mapHomologyIso F).hom =
        ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) :=
    mapHomologyIso_hom_homologyπ F (K.sc n)
  apply (cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n)).mp
  calc
    _ = ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) ≫
        F.map (K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv) ≫
          ((K.sc n).mapHomologyIso F).inv := by
      simp only [← Category.assoc, cycles]
    _ = ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) ≫
        ((K.sc n).mapHomologyIso F).inv := by
      have mapped := F.congr_map quotientK
      rw [F.map_comp] at mapped
      simpa only [Category.assoc] using congrArg
        (fun f => ((K.sc n).mapCyclesIso F).hom ≫ f ≫
          ((K.sc n).mapHomologyIso F).inv) mapped
    _ = ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n := by
      rw [← Category.assoc, ← quotientMap, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    _ = _ := quotientL.symm

end ToricPower
