module

public import ToricPower.CartierOpenPushforward
public import ToricPower.AffineInvertibleHomColimits
public import ToricPower.QuasicoherentTensorColimits
public import ToricPower.SchemePushforwardBaseSections

/-! # Unrestricted affine coefficients of the reconstruction target

Tensoring with an actual invertible sheaf is an equivalence in QCoh.
Its sections after an affine open direct image preserve all small
colimits: the original Cartier projection isomorphism expresses them
as affine sections of the corresponding tensor product on the source.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X]

/-- The actual invertible tensor functor, on arbitrary quasicoherent
coefficients, has an actual Cartier inverse. -/
theorem reconstructionTensorLeft_isEquivalence (L : QCoh X)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj] :
    (tensorLeft L).IsEquivalence := by
  obtain ⟨D, ⟨e⟩⟩ := CartierDivisor.exists_nonempty_iso_sheaf
    (⟨L.obj, inferInstance⟩ : TauCeti.AlgebraicGeometry.InvertibleSheaf X)
  let L' : QCoh X := ⟨D.sheaf, inferInstance⟩
  let e' : L ≅ L' := ObjectProperty.isoMk _ e
  letI : (tensorLeft L').IsEquivalence :=
    (quasicoherentCartierTensorEquivalence D).isEquivalence_functor
  exact Functor.isEquivalence_of_iso ((tensoringLeft (QCoh X)).mapIso e').symm

variable {U : Scheme.{u}} [U.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of k))]

/-- The literal direct-image section comparison at one open, natural
in the entire coefficient sheaf. -/
def reconstructionPushforwardSectionsIso (V : X.Opens) :
    Scheme.Modules.pushforward j ⋙ FiniteCover.schemeBaseSections k X V ≅
      FiniteCover.schemeBaseSections k U (j ⁻¹ᵁ V) :=
  NatIso.ofComponents (fun M => (pushforwardBaseSectionsLinearEquiv k j M V).toModuleIso)
    (by intro M N f; ext x; rfl)

/-- The original projection isomorphism computes the tensor target on
every affine test open and every actual coefficient sheaf. -/
def reconstructionCartierTargetSectionsIso (D : CartierDivisor X) (V : X.Opens) :
    quasicoherentAffinePushforward j ⋙
        tensorLeft (⟨D.sheaf, inferInstance⟩ : QCoh X) ⋙
        quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X V ≅
      tensorLeft ((quasicoherentRestriction j).obj
        (⟨D.sheaf, inferInstance⟩ : QCoh X)) ⋙
        quasicoherentInclusion U ⋙ FiniteCover.schemeBaseSections k U (j ⁻¹ᵁ V) :=
  Functor.isoWhiskerLeft (quasicoherentInclusion U)
    (Functor.isoWhiskerRight (cartierOpenPushforwardIso j D)
        (FiniteCover.schemeBaseSections k X V) ≪≫
      Functor.isoWhiskerLeft (tensorLeft (D.sheaf.restrict j))
        (reconstructionPushforwardSectionsIso k X j V))

/-- Arbitrary small colimits are retained by the actual tensor target
on every affine test open. -/
theorem reconstructionAffineTarget_preservesColimits
    (L : QCoh X) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj]
    (V : X.Opens) (affine : IsAffineOpen V) :
    PreservesColimitsOfSize.{u,u}
      (quasicoherentAffinePushforward j ⋙ tensorLeft L ⋙
        quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X V) := by
  obtain ⟨D, ⟨e⟩⟩ := CartierDivisor.exists_nonempty_iso_sheaf
    (⟨L.obj, inferInstance⟩ : TauCeti.AlgebraicGeometry.InvertibleSheaf X)
  let L' : QCoh X := ⟨D.sheaf, inferInstance⟩
  let e' : L ≅ L' := ObjectProperty.isoMk _ e
  letI := affineBaseSections_preservesColimits k U (j ⁻¹ᵁ V) (affine.preimage j)
  let comparison :
      quasicoherentAffinePushforward j ⋙ tensorLeft L ⋙
          quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X V ≅
        tensorLeft ((quasicoherentRestriction j).obj L') ⋙
          quasicoherentInclusion U ⋙ FiniteCover.schemeBaseSections k U (j ⁻¹ᵁ V) :=
    Functor.isoWhiskerLeft (quasicoherentAffinePushforward j)
      (Functor.isoWhiskerRight ((tensoringLeft (QCoh X)).mapIso e')
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X V)) ≪≫
      reconstructionCartierTargetSectionsIso k X j D V
  exact preservesColimits_of_natIso comparison.symm

end ToricPower

end
