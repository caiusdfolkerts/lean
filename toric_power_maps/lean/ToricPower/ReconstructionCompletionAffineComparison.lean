module

public import ToricPower.AffineCoresolutionClosure
public import ToricPower.HomologicalComparisonClosure
public import ToricPower.ReconstructionCompletionHomotopyComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Comparison maps on the finite affine cone coresolution

A comparison between triangulated functors is invertible on the entire
coresolution when it is invertible on all affine direct-image complexes.
The proof uses the genuine finite cone filtration, so its input may be
unbounded and its terms need not themselves be affine direct images.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  {B : Type w} [Category.{z} B] [Abelian B] [HasDerivedCategory B]
  (F G : HomotopyCategory (QCoh X) (.up ℤ) ⥤ DerivedCategory B)
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]

/-- The finite cone filtration extends an actual natural comparison
from arbitrary affine direct-image complexes to the coresolution. -/
theorem affineCoresolution_homotopyComparison_isIso (a : F ⟶ G)
    (localIso : ∀ (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ),
      IsIso (a.app ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J))))
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    IsIso (a.app ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
      ((affineConeCoresolution V l).obj K))) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let Hq := DerivedCategory.homologyFunctor B q
  let α := Functor.whiskerRight a Hq
  let P := homologicalComparisonLocus (F ⋙ Hq) (G ⋙ Hq) α
  have hlocal (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ) :
      P (Q.obj (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex
        (.up ℤ)).obj J)) := by
    let T := (quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)
    intro n
    let e := Q.mapIso ((T.commShiftIso n).app J) ≪≫
      (Q.commShiftIso n).app (T.obj J)
    apply (NatTrans.isIso_app_iff_of_iso α e).mp
    haveI := localIso i (J⟦n⟧)
    change IsIso (Hq.map (a.app (Q.obj (T.obj (J⟦n⟧)))))
    infer_instance
  have hR := affineConeCoresolution_mem V P hlocal l K
  exact (NatTrans.isIso_app_iff_of_iso α
    ((shiftFunctorZero (HomotopyCategory (QCoh X) (.up ℤ)) ℤ).app
      (Q.obj ((affineConeCoresolution V l).obj K)))).mp (hR 0)

/-- A comparison supplied on ordinary complexes has exactly the same
components after descent to the homotopy category. -/
theorem affineCoresolution_complexComparison_isIso
    (a : HomotopyCategory.quotient (QCoh X) (.up ℤ) ⋙ F ⟶
      HomotopyCategory.quotient (QCoh X) (.up ℤ) ⋙ G)
    (localIso : ∀ (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ),
      IsIso (a.app
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J)))
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    IsIso (a.app ((affineConeCoresolution V l).obj K)) := by
  let α := homotopyComparisonOfComplex F G a
  have h := affineCoresolution_homotopyComparison_isIso V F G α
    (fun i J => by simpa only [α, homotopyComparisonOfComplex_app] using localIso i J) l K
  simpa only [α, homotopyComparisonOfComplex_app] using h

end ToricPower

end
