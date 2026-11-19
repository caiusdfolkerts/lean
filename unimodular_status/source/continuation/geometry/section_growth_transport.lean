module

public import Continuation.Geometry.OpenImmersionTensor
public import Continuation.Divisor.InvariantCurves

/-!
# Actual tensor-power sections under a scheme isomorphism

The existing Cartier section comparison is proved using genuine local-ring
and function-field maps. An actual fractional presentation of each invertible
module therefore gives its global-section equivalence. Ordinary monoidal
pullback identifies all tensor powers, including degree zero. Bigness then
transports its original section-growth function and actual Krull dimension.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry PaperVerification.ToricSchemes
open scoped BaseSections

section TensorPullback

variable {X Y : Scheme.{u}}

local instance sectionGrowthSourceMonoidal : MonoidalCategory X.Modules :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf
local instance sectionGrowthTargetMonoidal : MonoidalCategory Y.Modules :=
  TauCeti.SheafOfModules.monoidalCategory Y.sheaf

/-- Ordinary pullback commutes with the actual sheafified tensor product. -/
def pullbackTensorSheafIso (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorSheaf M N) ≅
      tensorSheaf ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  (Scheme.Modules.pullback f).mapIso (SheafOfModules.tensorUnderlyingIso (R := Y.sheaf) M N).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N) ≪≫
      SheafOfModules.tensorUnderlyingIso (R := X.sheaf) _ _

/-- Pullback commutes with every ordinary tensor power. -/
def pullbackTensorSheafPowerIso (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    ∀ m : ℕ, (Scheme.Modules.pullback f).obj (tensorSheafPower M m) ≅
      tensorSheafPower ((Scheme.Modules.pullback f).obj M) m
  | 0 => Scheme.Modules.pullbackObjUnitIso f
  | m + 1 => pullbackTensorSheafIso f (tensorSheafPower M m) M ≪≫
      tensorSheafIso (pullbackTensorSheafPowerIso f M m) (Iso.refl _)

end TensorPullback

section GlobalSections

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
  (e : Y ≅ X) [e.hom.IsOver (Spec (CommRingCat.of k))]

/-- Global sections of the original invertible module and its literal
pullback are linearly equivalent over the original field. -/
def invertibleGlobalSectionsSchemeIso (M : X.Modules)
    [hM : SheafOfModules.isInvertible X M] :
    Γ(M, ⊤) ≃ₗ[k] Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) := by
  let D := invertibleFractionalPresentation M
    ((isInvertibleModule_iff_standard M).mpr hM)
  change Γ(D.sheaf, ⊤) ≃ₗ[k] Γ((Scheme.Modules.pullback e.hom).obj D.sheaf, ⊤)
  exact (D.schemeIsoGlobalSections k e).trans
    (BaseSections.globalSectionsIso k (D.dominantPullbackSheafIso e.hom).symm)

/-- Every tensor power remains an actual ordinary invertible module. -/
theorem tensorSheafPower_isInvertible (L : InvertibleSheaf X) (m : ℕ) :
    SheafOfModules.isInvertible X (tensorSheafPower L.obj m) := by
  let D := invertibleFractionalPresentation L.obj
    ((isInvertibleModule_iff_standard L.obj).mpr L.property)
  change SheafOfModules.isInvertible X (tensorSheafPower D.sheaf m)
  exact (SheafOfModules.isInvertible X).prop_of_iso (D.tensorSheafNsmulIso m).symm
    ((isInvertibleModule_iff_standard _).mp (D.nsmul m).locallyFree)

/-- All ordinary tensor-power section spaces, with no omitted degree. -/
def tensorPowerGlobalSectionsSchemeIso (L : InvertibleSheaf X) (m : ℕ) :
    Γ(tensorSheafPower L.obj m, ⊤) ≃ₗ[k]
      Γ(tensorSheafPower ((InvertibleSheaf.pullback e.hom).obj L).obj m, ⊤) := by
  letI := tensorSheafPower_isInvertible L m
  exact (invertibleGlobalSectionsSchemeIso k e (tensorSheafPower L.obj m)).trans
    (BaseSections.globalSectionsIso k (pullbackTensorSheafPowerIso e.hom L.obj m))

/-- Bigness is invariant under an actual scheme isomorphism over the field.
The proof transports finite-dimensionality in every degree and the same
positive asymptotic volume in the actual scheme dimension. -/
theorem isBig_pullback_schemeIso_iff (L : InvertibleSheaf X) :
    IsBig k ((InvertibleSheaf.pullback e.hom).obj L).obj ↔ IsBig k L.obj := by
  let E (m : ℕ) := tensorPowerGlobalSectionsSchemeIso k e L m
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  have hsections :
      (fun m => Module.finrank k Γ(tensorSheafPower L.obj m, ⊤)) =
        (fun m => Module.finrank k
          Γ(tensorSheafPower ((InvertibleSheaf.pullback e.hom).obj L).obj m, ⊤)) := by
    funext m
    exact (E m).finrank_eq
  constructor
  · rintro ⟨n, hn, hfinite, hvolume⟩
    refine ⟨n, hdim.symm.trans hn, ?_, ?_⟩
    · intro m
      letI := hfinite m
      exact (E m).symm.finiteDimensional
    · rw [hsections]
      exact hvolume
  · rintro ⟨n, hn, hfinite, hvolume⟩
    refine ⟨n, hdim.trans hn, ?_, ?_⟩
    · intro m
      letI := hfinite m
      exact (E m).finiteDimensional
    · rw [← hsections]
      exact hvolume

end GlobalSections

end Unimodular.NefBig

#print axioms Unimodular.NefBig.invertibleGlobalSectionsSchemeIso
#print axioms Unimodular.NefBig.tensorPowerGlobalSectionsSchemeIso
#print axioms Unimodular.NefBig.isBig_pullback_schemeIso_iff
