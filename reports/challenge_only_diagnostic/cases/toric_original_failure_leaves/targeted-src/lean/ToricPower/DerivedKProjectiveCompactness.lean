module

public import ToricPower.CoproductCompactFunctor
public import ToricPower.HomotopyQuotientCoproducts
public import ToricPower.DerivedKProjectiveCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Compact K-projective complexes in the actual derived category

Maps from a K-projective complex lift to homotopy classes. Arbitrary
derived targets admit genuine K-projective representatives; their
actual coproduct is represented by the degreewise coproduct complex.
This transfers the finite-support factorization condition to the full
unbounded derived category, without an assumed localization theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.CompactExtraction

universe u v w wD
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{w} A]
  [HasDerivedCategory.{wD} A]

theorem homotopy_coproductCompact (P : CochainComplex A ℤ)
    (compact : CoproductCompact.{max u v,v,w} P) :
    letI := CoproductComplex.homotopy_hasCoproducts (A := A) (shape := .up ℤ)
    CoproductCompact.{max u v,v,w}
      ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  letI := CoproductComplex.homotopy_hasCoproducts (A := A) (shape := .up ℤ)
  exact coproductCompact_image (HomotopyCategory.quotient A (.up ℤ))
    (fun _ K => CoproductComplex.quotient_preservesCoproduct K) compact
    (fun _ => Functor.map_surjective _)

theorem Qh_preservesCoproduct_of_kProjective
    {I : Type w} (family : I → HomotopyCategory A (.up ℤ))
    (projective : ∀ i, CochainComplex.IsKProjective (family i).as) :
    PreservesColimit (Discrete.functor family) (DerivedCategory.Qh (C := A)) := by
  letI : ∀ i, CochainComplex.IsKProjective (family i).as := projective
  apply preservesColimit_of_preserves_colimit_cocone
    (CoproductComplex.homotopyIsColimit (fun i => (family i).as))
  exact (isColimitMapCoconeCofanMkEquiv DerivedCategory.Qh family
    (fun i => (HomotopyCategory.quotient A (.up ℤ)).map
      (CoproductComplex.ι (fun j => (family j).as) i))).symm
      (CoproductComplex.derivedIsColimit (fun i => (family i).as))

theorem derived_coproductCompact_of_kProjective
    (representatives : ∀ X : DerivedCategory A,
      ∃ K : CochainComplex A ℤ, K.IsKProjective ∧
        Nonempty (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≅ X))
    (P : CochainComplex A ℤ) [P.IsKProjective]
    (compact : CoproductCompact.{max u v,v,w} P) :
    letI := CoproductComplex.derived_hasCoproducts representatives
    CoproductCompact.{max u v,wD,w} (DerivedCategory.Q.obj P) := by
  letI := CoproductComplex.homotopy_hasCoproducts (A := A) (shape := .up ℤ)
  letI := CoproductComplex.derived_hasCoproducts representatives
  apply coproductCompact_of_iso ((DerivedCategory.quotientCompQhIso A).app P)
  apply coproductCompact_image_of_representatives DerivedCategory.Qh
    (fun K : HomotopyCategory A (.up ℤ) => CochainComplex.IsKProjective K.as)
  · intro Y
    obtain ⟨K, projective, e⟩ := representatives Y
    exact ⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, projective, e⟩
  · intro I family members
    exact Qh_preservesCoproduct_of_kProjective family members
  · exact homotopy_coproductCompact P compact
  · intro Y
    exact (CochainComplex.IsKProjective.Qh_map_bijective P Y).surjective

end ToricPower.CompactExtraction

end
