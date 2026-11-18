module

public import ToricPower.ReconstructionCompletionAffineComparison
public import ToricPower.ReconstructionCompletionFactors
public import ToricPower.SignedShiftFunctor

/-! # The cellular top comparison on every affine coresolution

The finite total is factored through an already triangulated derived
functor.  Its original top comparison descends through the homotopy
quotient, and the finite cone filtration extends the affine calculation
to every unbounded input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  {C B : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* B] [Abelian B] [HasFiniteBiproducts B] [HasDerivedCategory B]
  (H : QCoh X ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]
  (T : QCoh X ⥤ B) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ FunctorTotal.singleCoefficient T n)
  (L : DerivedCategory C ⥤ DerivedCategory B)
  [L.CommShift ℤ] [L.IsTriangulated]
  (factors : DerivedCategory.Q ⋙ L ≅
    FunctorTotal.functor Φ width ⋙ DerivedCategory.Q)

local instance finiteAffineShiftCommShift (m : ℤ) :
    (shiftFunctor (DerivedCategory B) m).CommShift ℤ :=
  signedShiftFunctorCommShift (DerivedCategory B) m

local instance finiteAffineShiftTriangulated (m : ℤ) :
    (shiftFunctor (DerivedCategory B) m).IsTriangulated :=
  signedShiftFunctor_isTriangulated (DerivedCategory B) m

include L factors

/-- Only the actual local comparison on affine direct-image complexes
is needed; the full coresolution is handled by its finite cone closure. -/
theorem affineCoresolution_reconstructionComparison_quasiIso
    (localQuasiIso : ∀ (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ),
      QuasiIso ((FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ).app
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J)))
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    QuasiIso ((FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ).app
      ((affineConeCoresolution V l).obj K)) := by
  let F := H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L
  let G := T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
    shiftFunctor (DerivedCategory B) (-(n : ℤ))
  let eF := homotopyCompositeFactors H L
    (FunctorTotal.functor Φ width ⋙ DerivedCategory.Q) factors
  let eG := homotopyCompositeFactors T
    (shiftFunctor (DerivedCategory B) (-(n : ℤ)))
    (shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q)
    (DerivedCategory.Q.commShiftIso (-(n : ℤ))).symm
  let a := FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ
  let α : HomotopyCategory.quotient (QCoh X) (.up ℤ) ⋙ F ⟶
      HomotopyCategory.quotient (QCoh X) (.up ℤ) ⋙ G :=
    eF.hom ≫ Functor.whiskerRight a DerivedCategory.Q ≫ eG.inv
  have h := affineCoresolution_complexComparison_isIso V F G α
    (fun i J => by
      letI := localQuasiIso i J
      change IsIso (eF.hom.app _ ≫ DerivedCategory.Q.map (a.app _) ≫ eG.inv.app _)
      infer_instance) l K
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mp
  simpa only [α, NatTrans.comp_app, Functor.whiskerRight_app,
    isIso_comp_left_iff, isIso_comp_right_iff] using h

end ToricPower

end
