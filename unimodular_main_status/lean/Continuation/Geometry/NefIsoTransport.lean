module

public import Continuation.Divisor.WeilCurveDegree

/-!
# Ordinary nefness under an actual closed immersion

An integral curve on the source remains the identical proper integral
curve after composing its inclusion with a closed immersion over the field.
The degree comparison is therefore on the same curve, using the actual
pullback-composition isomorphism. In particular this proves invariance
under actual scheme isomorphisms without assuming a toric presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace Unimodular.NefBig

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]

/-- Compose a genuine integral closed curve with a closed immersion over k. -/
def integralCurveComp (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsClosedImmersion f] (C : IntegralCurve k X) : IntegralCurve k Y where
  carrier := C.carrier
  ι := C.ι ≫ f
  isClosedImmersion := inferInstance
  isIntegral := inferInstance
  isProper := by
    simpa only [Category.assoc, comp_over] using C.isProper
  dim_eq_one := C.dim_eq_one

/-- Ordinary residue-weighted curve nefness pulls back along any closed
immersion over the original field. -/
theorem isNef_pullback_closedImmersion
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] [IsClosedImmersion f]
    (L : InvertibleSheaf Y)
    (hL : AlgebraicGeometry.IsNef (baseField := k) L.obj) :
    AlgebraicGeometry.IsNef (baseField := k)
      ((InvertibleSheaf.pullback f).obj L).obj := by
  intro C
  letI : SheafOfModules.isInvertible Y L.obj := L.property
  letI : SheafOfModules.isInvertible X ((Scheme.Modules.pullback f).obj L.obj) :=
    SheafOfModules.isInvertible_pullback f L.obj
  let D := integralCurveComp k f C
  have h := hL D
  let E : (Scheme.Modules.pullback C.ι).obj ((Scheme.Modules.pullback f).obj L.obj) ≅
      (Scheme.Modules.pullback (C.ι ≫ f)).obj L.obj :=
    (Scheme.Modules.pullbackComp C.ι f).app L.obj
  have hdegree := C.lineBundleDegree_eq_of_iso E
  change 0 ≤ C.lineBundleDegree
    ((Scheme.Modules.pullback C.ι).obj ((Scheme.Modules.pullback f).obj L.obj))
  rw [hdegree]
  simpa only [IntegralCurve.lineBundleDegree, IntegralCurve.over,
    D, integralCurveComp, Category.assoc, comp_over] using h

/-- Scheme isomorphism invariance of the same ordinary nefness predicate. -/
theorem isNef_pullback_schemeIso_iff
    (e : X ≅ Y) [e.hom.IsOver (Spec (CommRingCat.of k))]
    (L : InvertibleSheaf Y) :
    AlgebraicGeometry.IsNef (baseField := k)
        ((InvertibleSheaf.pullback e.hom).obj L).obj ↔
      AlgebraicGeometry.IsNef (baseField := k) L.obj := by
  constructor
  · intro h
    have h' := isNef_pullback_closedImmersion k e.inv
      ((InvertibleSheaf.pullback e.hom).obj L) h
    let E : ((InvertibleSheaf.pullback e.inv).obj
        ((InvertibleSheaf.pullback e.hom).obj L)).obj ≅ L.obj :=
      ((Scheme.Modules.pullbackComp e.inv e.hom) ≪≫
        Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
          Scheme.Modules.pullbackId Y).app L.obj
    exact AlgebraicGeometry.IsNef.of_iso E h'
  · exact isNef_pullback_closedImmersion k e.hom L

end Unimodular.NefBig

#print axioms Unimodular.NefBig.isNef_pullback_closedImmersion
#print axioms Unimodular.NefBig.isNef_pullback_schemeIso_iff
