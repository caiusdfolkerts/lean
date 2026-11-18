module

public import ToricPower.AffineConeCoresolution

/-! # The actual affine coaugmentation after localization -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ToricPower

universe u v w

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  [HasDerivedCategory.{w} (QCoh X)]
  (l : List I) (coversList : ∀ i, i ∈ l) (covers : IsOpenCover V)

/-- The natural isomorphism is the localization of the original
coaugmentation on every unbounded complex. -/
def affineConeLocalizationIso :
    DerivedCategory.Q ≅ affineConeCoresolution V l ⋙ DerivedCategory.Q := by
  let C := affineConeCoresolution V l
  let a := affineConeCoaugmentation V l
  let component (K : CochainComplex (QCoh X) ℤ) :
      DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj (C.obj K) := by
    letI := affineConeCoaugmentation_quasiIso V l coversList covers K
    exact asIso (DerivedCategory.Q.map (a.app K))
  exact NatIso.ofComponents component (by
    intro K M f
    change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (a.app M) =
      DerivedCategory.Q.map (a.app K) ≫ DerivedCategory.Q.map (C.map f)
    simpa only [Functor.map_comp, Functor.id_map] using
      congrArg DerivedCategory.Q.map (a.naturality f))

end ToricPower

end
