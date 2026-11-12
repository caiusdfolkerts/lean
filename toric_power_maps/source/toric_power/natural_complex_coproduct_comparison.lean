module

public import ToricPower.ExactComplexCoproducts

/-! # Natural quasi-isomorphisms on unrestricted coproducts

The conclusion concerns the given natural transformation at the actual
coproduct object. It follows from the canonical coproduct comparisons
and exactness of coproducts of full coefficient complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace ToricPower

universe u v w u' v'
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [HasCoproducts.{w} B]
  {I : Type w} [HasColimitsOfShape (Discrete I) A]
  [HasExactColimitsOfShape (Discrete I) A]
  {ι : Type*} {shape : ComplexShape ι}
  {F G : B ⥤ HomologicalComplex A shape} (τ : F ⟶ G) (family : I → B)
  [PreservesColimit (Discrete.functor family) F]
  [PreservesColimit (Discrete.functor family) G]

theorem naturalComparison_coproduct_square :
    sigmaComparison F family ≫ τ.app (∐ family) =
      Limits.Sigma.map (fun i => τ.app (family i)) ≫ sigmaComparison G family := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc,ι_comp_sigmaComparison,τ.naturality]
  rw [← Category.assoc,Sigma.ι_map,Category.assoc,ι_comp_sigmaComparison]

theorem naturalComparison_coproduct_quasiIso
    [∀ i, QuasiIso (τ.app (family i))] : QuasiIso (τ.app (∐ family)) := by
  let α : Discrete.functor (fun i => F.obj (family i)) ⟶
      Discrete.functor (fun i => G.obj (family i)) :=
    Discrete.natTrans (fun i : Discrete I => τ.app (family i.as))
  letI (j : Discrete I) : QuasiIso (α.app j) :=
    inferInstanceAs (QuasiIso (τ.app (family j.as)))
  haveI : QuasiIso (Limits.Sigma.map (fun i => τ.app (family i))) :=
    complex_colimitMap_quasiIso
      (F := Discrete.functor (fun i => F.obj (family i)))
      (G := Discrete.functor (fun i => G.obj (family i)))
      α
  have equality : τ.app (∐ family) = inv (sigmaComparison F family) ≫
      Limits.Sigma.map (fun i => τ.app (family i)) ≫ sigmaComparison G family := by
    calc
      τ.app (∐ family) = inv (sigmaComparison F family) ≫
          (sigmaComparison F family ≫ τ.app (∐ family)) := by simp
      _ = _ := by rw [naturalComparison_coproduct_square]
  rw [equality]
  infer_instance

end ToricPower

end
