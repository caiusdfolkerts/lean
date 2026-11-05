module

public import Continuation.Geometry.OpenImmersionTensor

/-!
# The intrinsic canonical sheaf under an actual scheme isomorphism

The canonical object is the existing top exterior power of the universal
Kähler sheaf. The comparison below uses its proved open-immersion pullback
isomorphism, and derives the dual comparison from ordinary tensor evaluation.
No canonical-bundle comparison is assumed as extra input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry

section Dual

variable {X Y : Scheme.{u}}

local instance canonicalTransportSourceMonoidal : MonoidalCategory X.Modules :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf
local instance canonicalTransportSourceSymmetric : SymmetricCategory X.Modules :=
  TauCeti.SheafOfModules.symmetricCategory X.sheaf
local instance canonicalTransportTargetMonoidal : MonoidalCategory Y.Modules :=
  TauCeti.SheafOfModules.monoidalCategory Y.sheaf
local instance canonicalTransportTargetSymmetric : SymmetricCategory Y.Modules :=
  TauCeti.SheafOfModules.symmetricCategory Y.sheaf

/-- Pullback preserves the actual internal-Hom dual of an invertible sheaf. -/
def ordinaryPullbackDualIso (f : X ⟶ Y) [IsOpenImmersion f] (L : InvertibleSheaf Y) :
    (Scheme.Modules.pullback f).obj (InvertibleSheaf.dual L).obj ≅
      (InvertibleSheaf.dual ((InvertibleSheaf.pullback f).obj L)).obj := by
  let K := (InvertibleSheaf.pullback f).obj L
  let D := InvertibleSheaf.dual L
  let ev : L.obj ⊗ D.obj ≅ SheafOfModules.unit Y.ringCatSheaf := by
    simpa only [D, InvertibleSheaf.dual_obj] using
      (Scheme.Modules.isoOfSheafIso Y (L.evaluationDualIsoSheaf))
  let evPullback :
      (Scheme.Modules.pullback f).obj L.obj ⊗
        (Scheme.Modules.pullback f).obj D.obj ≅
          SheafOfModules.unit X.ringCatSheaf :=
    (asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L.obj D.obj)).symm ≪≫
      (Scheme.Modules.pullback f).mapIso ev ≪≫
        Scheme.Modules.pullbackObjUnitIso f
  apply tensorInverseIsoDual K
  exact (SheafOfModules.tensorUnderlyingIso K.obj
      ((Scheme.Modules.pullback f).obj D.obj)).symm ≪≫ evPullback

end Dual

section TopDifferentials

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] [IsOpenImmersion f]
  (n : ℕ)
  (hK : SheafOfModules.isInvertible Y (topDifferentialSheaf k Y n))

/-- The intrinsic anticanonical object, transported to the source's actual
top Kähler sheaf. This holds for every exterior degree, including zero. -/
def intrinsicAnticanonicalPullbackIso :
    (Scheme.Modules.pullback f).obj (topDifferentialSheaf k Y n).dual ≅
      (topDifferentialSheaf k X n).dual := by
  let K : InvertibleSheaf Y := ⟨topDifferentialSheaf k Y n, hK⟩
  let K' := (InvertibleSheaf.pullback f).obj K
  let sourceIso : (Scheme.Modules.pullback f).obj K.dual.obj ≅
      (Scheme.Modules.pullback f).obj (topDifferentialSheaf k Y n).dual :=
    (Scheme.Modules.pullback f).mapIso
      (Scheme.Modules.isoOfSheafIso Y (eqToIso (InvertibleSheaf.dual_obj K)))
  exact sourceIso.symm ≪≫ ordinaryPullbackDualIso f K ≪≫
    Scheme.Modules.isoOfSheafIso X
      (eqToIso (InvertibleSheaf.dual_obj K') ≪≫
        SheafOfModules.dualIso (R := X.sheaf)
          (topDifferentialSheafPullbackIso f n k))

end TopDifferentials

section Fan

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  (f : X ⟶ F.fanScheme k) [f.IsOver (Spec (CommRingCat.of k))]
  [IsOpenImmersion f]

/-- The fan anticanonical bundle is pulled to the intrinsic anticanonical
sheaf on the actual source scheme, with no supplied bundle identification. -/
def fanAnticanonicalPullbackIso :
    (Scheme.Modules.pullback f).obj (anticanonicalLineBundle F k).obj ≅
      (topDifferentialSheaf k X n).dual := by
  let sourceIso : (anticanonicalLineBundle F k).obj ≅
      (topDifferentialSheaf k (F.fanScheme k) n).dual := by
    exact Scheme.Modules.isoOfSheafIso _
      (eqToIso (InvertibleSheaf.dual_obj (canonicalLineBundle F k)))
  exact (Scheme.Modules.pullback f).mapIso sourceIso ≪≫
    intrinsicAnticanonicalPullbackIso k f n (canonicalLineBundle F k).property

end Fan

end Unimodular.NefBig

#print axioms Unimodular.NefBig.ordinaryPullbackDualIso
#print axioms Unimodular.NefBig.intrinsicAnticanonicalPullbackIso
#print axioms Unimodular.NefBig.fanAnticanonicalPullbackIso
