module

public import ToricPower.DerivedKProjectiveCompactness
public import ToricPower.ExactComplexCoproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Localization preserves actual coproducts under exactness

K-projective representatives give actual derived coproducts. Exact
coefficient coproducts make the coproduct of arbitrary quasi-isomorphisms
a quasi-isomorphism. Comparison with K-projective representatives then
shows that the original localization preserves every actual coproduct
of arbitrary unbounded complexes.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

section Comparison

universe u v u' v' w z
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : Type w} [Category.{z} J]
  [HasColimitsOfShape J C] [HasColimitsOfShape J D]
  (F : C ⥤ D) {K L : J ⥤ C} (α : K ⟶ L)

/-- Naturality of the canonical colimit comparison, without any
preservation assumption. -/
theorem colimitPost_naturality :
    colim.map (Functor.whiskerRight α F) ≫ colimit.post L F =
      colimit.post K F ≫ F.map (colim.map α) := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, Functor.whiskerRight_app,
    colimit.ι_post, colimit.ι_post_assoc, ← Functor.map_comp, colimit.ι_map]

theorem preservesColimit_of_inverted_comparison
    [PreservesColimit K F] [IsIso (Functor.whiskerRight α F)]
    [IsIso (F.map (colim.map α))] : PreservesColimit L F := by
  have equation : colimit.post L F =
      inv (colim.map (Functor.whiskerRight α F)) ≫ colimit.post K F ≫
        F.map (colim.map α) := by
    rw [← colimitPost_naturality F α]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  haveI : IsIso (colimit.post L F) := by
    rw [equation]
    infer_instance
  exact preservesColimit_of_isIso_post F L

end Comparison

namespace CoproductComplex

universe u v w wD
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{w} A]
  [HasDerivedCategory.{wD} A]

/-- The lift is an actual chain map; the source alone is K-projective. -/
theorem derivedQ_map_surjective_of_kProjective
    (K L : CochainComplex A ℤ) [K.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient A (.up ℤ)).obj L)).surjective
      (((DerivedCategory.quotientCompQhIso A).app K).hom ≫ f ≫
        ((DerivedCategory.quotientCompQhIso A).app L).inv)
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g', ?_⟩
  calc
    DerivedCategory.Q.map g' =
        ((DerivedCategory.quotientCompQhIso A).app K).inv ≫
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g') ≫
            ((DerivedCategory.quotientCompQhIso A).app L).hom) := by
      change DerivedCategory.Q.map g' =
        (DerivedCategory.quotientCompQhIso A).inv.app K ≫
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g') ≫
            (DerivedCategory.quotientCompQhIso A).hom.app L)
      rw [DerivedCategory.quotientCompQhIso_hom_naturality]
      simp only [Iso.inv_hom_id_app_assoc]
    _ = f := by rw [hg]; simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]

theorem derivedQ_preservesCoproduct_of_kProjective
    {I : Type w} (K : I → CochainComplex A ℤ) [∀ i, (K i).IsKProjective] :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A)) := by
  letI := homotopy_hasCoproducts (A := A) (shape := .up ℤ)
  letI := quotient_preservesCoproduct K
  letI : PreservesColimit
      (Discrete.functor (fun i => (HomotopyCategory.quotient A (.up ℤ)).obj (K i)))
      (DerivedCategory.Qh (C := A)) :=
    CompactExtraction.Qh_preservesCoproduct_of_kProjective _ (fun i => by
      rw [HomotopyCategory.quotient_obj_as]
      infer_instance)
  let comparison :
      Discrete.functor (fun i => (HomotopyCategory.quotient A (.up ℤ)).obj (K i)) ≅
        Discrete.functor K ⋙ HomotopyCategory.quotient A (.up ℤ) :=
    Discrete.natIso (fun _ => Iso.refl _)
  letI : PreservesColimit (Discrete.functor K ⋙ HomotopyCategory.quotient A (.up ℤ))
      (DerivedCategory.Qh (C := A)) :=
    preservesColimit_of_iso_diagram _ comparison
  letI : PreservesColimit (Discrete.functor K)
      (HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh) := inferInstance
  exact preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A)

variable (representatives : ∀ X : DerivedCategory A,
  ∃ K : CochainComplex A ℤ, K.IsKProjective ∧
    Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≅ X))

include representatives in
/-- Every original complex admits an actual quasi-isomorphism from an
actual K-projective complex, not just a replacement object name. -/
theorem exists_kProjective_quasiIso (L : CochainComplex A ℤ) :
    ∃ (K : CochainComplex A ℤ) (_ : K.IsKProjective) (f : K ⟶ L), QuasiIso f := by
  obtain ⟨K, projective, ⟨e⟩⟩ := representatives (DerivedCategory.Q.obj L)
  letI := projective
  let iso : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L :=
    ((DerivedCategory.quotientCompQhIso A).app K).symm ≪≫ e
  obtain ⟨f, hf⟩ := derivedQ_map_surjective_of_kProjective K L iso.hom
  refine ⟨K, projective, f, ?_⟩
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso A f).mp
  rw [hf]
  infer_instance

include representatives in
/-- Exact coproducts and K-projective representatives imply preservation
by the actual localization on all unbounded complexes. -/
theorem derivedQ_preservesCoproducts (I : Type w)
    [HasExactColimitsOfShape (Discrete I) A] :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  letI := derived_hasCoproducts representatives
  suffices all : ∀ family : I → CochainComplex A ℤ,
      PreservesColimit (Discrete.functor family) (DerivedCategory.Q (C := A)) from
    by
      letI := all
      exact preservesColimitsOfShape_of_discrete DerivedCategory.Q
  intro family
  choose K projective maps quasi using fun i : I =>
    exists_kProjective_quasiIso representatives (family i)
  letI (i : I) := projective i
  letI (i : I) := quasi i
  let α : Discrete.functor K ⟶ Discrete.functor family :=
    Discrete.natTrans (fun i => maps i.as)
  letI := derivedQ_preservesCoproduct_of_kProjective K
  haveI : ∀ i, QuasiIso (α.app i) := fun i => quasi i.as
  haveI : QuasiIso (colim.map α) := complex_colimitMap_quasiIso α
  haveI : ∀ i, IsIso ((Functor.whiskerRight α DerivedCategory.Q).app i) := fun i => by
    change IsIso (DerivedCategory.Q.map (maps i.as))
    infer_instance
  haveI : IsIso (Functor.whiskerRight α DerivedCategory.Q) :=
    NatIso.isIso_of_isIso_app _
  exact preservesColimit_of_inverted_comparison DerivedCategory.Q α

end CoproductComplex
end ToricPower
end
