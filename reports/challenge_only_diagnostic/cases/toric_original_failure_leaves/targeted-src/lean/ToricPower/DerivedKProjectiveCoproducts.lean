module

public import ToricPower.HomotopyCategoryCoproducts
public import ToricPower.CoproductLocalFullTransfer
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Derived coproducts represented by K-projective complexes

The ordinary localization induces Hom bijections out of K-projective
complexes. An actual coproduct of such complexes is K-projective, so its
image is a genuine coproduct in the full unbounded derived category.
If every derived object admits such a representative, this constructs
all derived coproducts of the indicated size.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.CoproductComplex

universe u v w wD
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{w} A]
  [HasDerivedCategory.{wD} A] {I : Type w}

def derivedCofan (K : I → CochainComplex A ℤ) :
    Cofan (fun i => DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj (K i))) :=
  imageCofan DerivedCategory.Qh (homotopyCofan K)

def derivedIsColimit (K : I → CochainComplex A ℤ) [∀ i, (K i).IsKProjective] :
    IsColimit (derivedCofan K) := by
  letI : CochainComplex.IsKProjective (obj K) := isKProjective K
  exact isColimitImageCofan DerivedCategory.Qh (homotopyCofan K) (homotopyIsColimit K)
    (fun Y => CochainComplex.IsKProjective.Qh_map_bijective (obj K) Y)
    (fun i Y => CochainComplex.IsKProjective.Qh_map_bijective (K i) Y)

/-- Having genuine K-projective representatives is enough to construct
all coproducts in the actual unbounded derived category. -/
theorem derived_hasCoproducts
    (representatives : ∀ X : DerivedCategory A,
      ∃ (K : CochainComplex A ℤ), K.IsKProjective ∧
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≅ X)) :
    HasCoproducts.{w} (DerivedCategory A) := by
  have familyCoproduct (I : Type w) (family : I → DerivedCategory A) : HasCoproduct family := by
    choose K projective iso using fun i : I => representatives (family i)
    letI : ∀ i, (K i).IsKProjective := projective
    let e i := Classical.choice (iso i)
    letI : HasCoproduct (fun i => DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj (K i))) :=
      ⟨⟨derivedCofan K, derivedIsColimit K⟩⟩
    exact hasCoproduct_of_equiv_of_iso
      (fun i => DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj (K i)))
      family (Equiv.refl I) (fun i => (e i).symm)
  intro I
  refine ⟨fun F => ?_⟩
  letI := familyCoproduct I (fun i => F.obj ⟨i⟩)
  let e : Discrete.functor (fun i : I => F.obj ⟨i⟩) ≅ F :=
    Discrete.natIso (fun _ => Iso.refl _)
  exact hasColimit_of_iso e.symm

/-- K-projective representatives also prove that the actual derived Hom
sets have the original coefficient Hom universe, even when the chosen
localization was constructed in a larger universe. -/
theorem derived_locallySmall
    (representatives : ∀ X : DerivedCategory A,
      ∃ (K : CochainComplex A ℤ), K.IsKProjective ∧
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≅ X)) :
    LocallySmall.{v} (DerivedCategory A) where
  hom_small X Y := by
    obtain ⟨K, projective, ⟨e⟩⟩ := representatives X
    letI := projective
    let L := (DerivedCategory.Qh (C := A)).objPreimage Y
    let d : DerivedCategory.Qh.obj L ≅ Y := DerivedCategory.Qh.objObjPreimageIso Y
    exact small_of_surjective
      ((Iso.homCongr e d).surjective.comp
        (CochainComplex.IsKProjective.Qh_map_bijective K L).surjective)

end ToricPower.CoproductComplex

end

