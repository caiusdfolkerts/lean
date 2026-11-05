module

public import PaperVerification.ToricSectionTensorNaturality

@[expose] public section

/-!
# The ordinary tensor multiplication of sections of arbitrary module sheaves

This map is defined before choosing any fractional Cartier presentation.
It sends a pure tensor of global sections to the corresponding section of
the actual tensor sheaf. The base scalars come from the structural morphism.
For Cartier sheaves it is identified with the rational-product construction.
Actual sheaf isomorphisms preserve its surjectivity.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

def moduleSectionProductOver (M N : X.Modules) :
    Γ(M,⊤) →ₗ[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) := by
  letI : Module Γ(X,⊤) Γ(tensorSheaf M N,⊤) :=
    ModuleCat.isModule ((tensorSheaf M N).val.obj (op ⊤))
  let unitMap : Γ(M,⊤) ⊗[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    ((tensorSheafUnit M N).app (op ⊤)).hom
  let product : Γ(M,⊤) →ₗ[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    (TensorProduct.mk Γ(X,⊤) Γ(M,⊤) Γ(N,⊤)).compr₂
      (R := Γ(X,⊤)) (A := Γ(X,⊤)) unitMap
  exact product.restrictScalars₁₂ k k

/-- The usual base-linear multiplication into the genuine tensor sheaf. -/
def moduleSectionMultiplicationOver (M N : X.Modules) :
    Γ(M,⊤) ⊗[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) :=
  TensorProduct.lift (moduleSectionProductOver k M N)

@[simp] theorem moduleSectionMultiplicationOver_tmul (M N : X.Modules)
    (s : Γ(M,⊤)) (t : Γ(N,⊤)) :
    moduleSectionMultiplicationOver k M N (s⊗ₜ[k]t) =
      (tensorSheafUnit M N).app (op ⊤) (s⊗ₜ[Γ(X,⊤)]t) := rfl

theorem moduleSectionMultiplicationOver_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    (BaseSections.globalSectionsIso k (tensorSheafIso F G)).toLinearMap.comp
        (moduleSectionMultiplicationOver k M N) =
      (moduleSectionMultiplicationOver k M' N').comp
        (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
          (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change (tensorSheafIso F G).hom.app ⊤
      ((tensorSheafUnit M N).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    (tensorSheafUnit M' N').app (op ⊤)
      (F.hom.app ⊤ s ⊗ₜ[Γ(X,⊤)] G.hom.app ⊤ t)
  exact tensorSheafIso_pure_sections F G ⊤ s t

/-- This is an invariant of the actual module sheaves, independently
of frames, divisors, fans, or rational embeddings. -/
theorem moduleSectionMultiplicationOver_surjective_iff_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    Function.Surjective (moduleSectionMultiplicationOver k M N) ↔
      Function.Surjective (moduleSectionMultiplicationOver k M' N') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (tensorSheafIso F G)
  have he (z) : et (moduleSectionMultiplicationOver k M N z) =
      moduleSectionMultiplicationOver k M' N' (es z) :=
    congrArg (fun h=>h z) (moduleSectionMultiplicationOver_sheafIso k F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

namespace CartierData

variable [IsIntegral X] (D E : CartierData X)

/-- Multiplication in the function field is precisely the ordinary
tensor-sheaf section map, followed by the actual O(D)⊗O(E)≅O(D+E). -/
theorem sectionMultiplicationOver_eq_moduleSectionMultiplicationOver :
    (BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)).toLinearMap.comp
      (moduleSectionMultiplicationOver k D.sheaf E.sheaf) =
        D.sectionMultiplicationOver k E := by
  apply TensorProduct.ext'
  intro s t
  change (D.tensorSheafAddIso E).hom.app ⊤
      ((tensorSheafUnit D.sheaf E.sheaf).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    D.sectionProduct E ⊤ s t
  exact D.tensorSheafAddIso_pure_sections E ⊤ s t

theorem sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (moduleSectionMultiplicationOver k D.sheaf E.sheaf) := by
  let et := BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)
  have he (z) : et (moduleSectionMultiplicationOver k D.sheaf E.sheaf z) =
      D.sectionMultiplicationOver k E z :=
    congrArg (fun h=>h z)
      (D.sectionMultiplicationOver_eq_moduleSectionMultiplicationOver k E)
  constructor
  · intro h t
    obtain ⟨z,hz⟩ := h (et t)
    exact ⟨z,et.injective (by rw [he,hz])⟩
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨z,(he z).symm.trans (by rw [hz,ht])⟩

/-- Any actual presentation of a canonical line bundle can be removed
from the final multiplication statement. -/
theorem moduleSectionMultiplicationOver_adjoint_of_cartier
    (K : CartierData X) (ω : X.Modules) (F : K.sheaf≅ω)
    (h : Function.Surjective (D.sectionMultiplicationOver k (E.add K))) :
    Function.Surjective
      (moduleSectionMultiplicationOver k D.sheaf (tensorSheaf E.sheaf ω)) := by
  let G : (E.add K).sheaf≅tensorSheaf E.sheaf ω :=
    (E.tensorSheafAddIso K).symm ≪≫ tensorSheafIso (Iso.refl E.sheaf) F
  exact (moduleSectionMultiplicationOver_surjective_iff_sheafIso k
    (Iso.refl D.sheaf) G).mp
      ((D.sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver k
        (E.add K)).mp h)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.moduleSectionMultiplicationOver_surjective_iff_sheafIso
#print axioms PaperVerification.ToricSchemes.CartierData.moduleSectionMultiplicationOver_adjoint_of_cartier
