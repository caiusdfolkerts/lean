module

public import PaperVerification.ToricCartierTensor
public import PaperVerification.ToricCartierBaseSections

@[expose] public section

/-!
# Actual section multiplication under arbitrary line-bundle isomorphisms

The tensor sheaf is the genuine sheafification of sectionwise tensor
products. Naturality of its sheafification unit proves compatibility on
pure sections. Consequently arbitrary isomorphisms of the two line
bundles induce a commuting square for their actual section multiplication,
without any compatibility assumption on fractional embeddings.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

theorem tensorSheafIso_pure_sections {M M' N N' : X.Modules}
    (F : M ≅ M') (G : N ≅ N') (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) :
    (tensorSheafIso F G).hom.app U
      ((tensorSheafUnit M N).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      (tensorSheafUnit M' N').app (op U)
        (F.hom.app U s ⊗ₜ[Γ(X,U)] G.hom.app U t) := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let h := ((SheafOfModules.forget _).map F.hom) ⊗ₘ
    ((SheafOfModules.forget _).map G.hom)
  have he := congrArg (fun a=>a.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (adj.unit.naturality h)
  exact he.symm

variable [IsIntegral X]

namespace CartierData

variable (D D' E E' : CartierData X)

theorem tensorSheafAddIso_pure_sections (U : X.Opens)
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.tensorSheafAddIso E).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        D.sectionProduct E U s t := by
  change (D.localCocycle.tensorSheafMulIso E.localCocycle).hom.app U
    ((tensorSheafIso D.presentationIso E.presentationIso).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t))) = _
  rw [tensorSheafIso_pure_sections,RationalCartierCocycle.tensorSheafMulIso_pure_sections]
  rfl

def addSheafIso (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf) :
    (D.add E).sheaf ≅ (D'.add E').sheaf :=
  (D.tensorSheafAddIso E).symm ≪≫ tensorSheafIso F G ≪≫ D'.tensorSheafAddIso E'

theorem addSheafIso_sectionProduct
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)
    (U : X.Opens) (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.addSheafIso D' E E' F G).hom.app U (D.sectionProduct E U s t) =
      D'.sectionProduct E' U (F.hom.app U s) (G.hom.app U t) := by
  rw [← D.tensorSheafAddIso_pure_sections E U s t]
  change (D'.tensorSheafAddIso E').hom.app U
    ((tensorSheafIso F G).hom.app U
      ((D.tensorSheafAddIso E).inv.app U
        ((D.tensorSheafAddIso E).hom.app U
          ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))))) = _
  have he : (D.tensorSheafAddIso E).inv.app U
      ((D.tensorSheafAddIso E).hom.app U
        ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))) =
      (tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t) := by
    exact congrArg (fun h=>h.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t)))
      (D.tensorSheafAddIso E).hom_inv_id
  rw [he,tensorSheafIso_pure_sections,tensorSheafAddIso_pure_sections]

end CartierData

namespace BaseSections

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]

def globalSectionsIso {M N : X.Modules} (F : M ≅ N) : Γ(M,⊤) ≃ₗ[k] Γ(N,⊤) := by
  let e : Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso F)).toLinearEquiv
  exact e.restrictScalars k

@[simp] theorem globalSectionsIso_apply {M N : X.Modules} (F : M ≅ N) (s : Γ(M,⊤)) :
    globalSectionsIso k F s=F.hom.app ⊤ s := rfl

end BaseSections

namespace CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (D D' E E' : CartierData X)
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)

theorem sectionMultiplicationOver_sheafIso :
    (BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)).toLinearMap.comp
      (D.sectionMultiplicationOver k E) =
    (D'.sectionMultiplicationOver k E').comp
      (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
        (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
      (D.sectionProduct E ⊤ s t) =
    D'.sectionProduct E' ⊤ (BaseSections.globalSectionsIso k F s)
      (BaseSections.globalSectionsIso k G t)
  exact D.addSheafIso_sectionProduct D' E E' F G ⊤ s t

include F G in
/-- Surjectivity of the actual tensor multiplication is an invariant of
the actual line bundles, independently of fractional presentations. -/
theorem sectionMultiplicationOver_surjective_iff_sheafIso :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (D'.sectionMultiplicationOver k E') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      D'.sectionMultiplicationOver k E' (es z) :=
    congrArg (fun h=>h z) (D.sectionMultiplicationOver_sheafIso k D' E E' F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_sheafIso
