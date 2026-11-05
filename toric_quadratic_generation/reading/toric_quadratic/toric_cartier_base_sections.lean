module

public import PaperVerification.ToricCartierProducts
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

/-!
# Actual base-field section multiplication

The scalar map comes from the given structural morphism X→Spec k, followed
by the actual structure-sheaf restriction. Consequently the multiplication
map here is the tensor map over the base field, without assuming Γ(X,O_X)=k.
The rational-value square is proved on pure tensors and hence on the whole
tensor product.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

namespace BaseSections

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]

/-- The scalar map is induced by the actual structural morphism. -/
def scalarMap (U : X.Opens) : k →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (((X ↘ Spec (CommRingCat.of k)).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

scoped instance sectionsAlgebra (U : X.Opens) : Algebra k Γ(X,U) :=
  (scalarMap k X U).toAlgebra

scoped instance sectionsModule (M : X.Modules) (U : X.Opens) : Module k Γ(M,U) :=
  Module.compHom Γ(M,U) (scalarMap k X U)

scoped instance sectionsScalarTower (M : X.Modules) (U : X.Opens) :
    IsScalarTower k Γ(X,U) Γ(M,U) :=
  IsScalarTower.of_compHom k Γ(X,U) Γ(M,U)

variable [IsIntegral X]

scoped instance functionFieldAlgebra : Algebra k X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (scalarMap k X ⊤)).toAlgebra

scoped instance functionFieldScalarTower : IsScalarTower k Γ(X,⊤) X.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

end BaseSections

open scoped BaseSections

namespace CartierData

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (D E : CartierData X)

/-- Actual rational values of global sections as a base-linear map. -/
def globalSectionValue : Γ(D.sheaf,⊤) →ₗ[k] X.functionField :=
  (D.sectionValue ⊤).restrictScalars k

theorem globalSectionValue_injective : Function.Injective (D.globalSectionValue k) :=
  D.sectionValue_injective ⊤

/-- Multiplication of actual sections as a bilinear map over the base. -/
def sectionProductOver :
    Γ(D.sheaf,⊤) →ₗ[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  (D.sectionProduct E ⊤).restrictScalars₁₂ k k

/-- The section multiplication map in the manuscript, with its tensor
product over the actual base field (indeed over any commutative base ring). -/
def sectionMultiplicationOver :
    Γ(D.sheaf,⊤) ⊗[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  TensorProduct.lift (D.sectionProductOver k E)

@[simp] theorem sectionMultiplicationOver_value_tmul
    (s : Γ(D.sheaf,⊤)) (t : Γ(E.sheaf,⊤)) :
    (D.add E).globalSectionValue k (D.sectionMultiplicationOver k E (s ⊗ₜ[k] t)) =
      D.globalSectionValue k s * E.globalSectionValue k t :=
  D.sectionProduct_value E ⊤ s t

/-- The actual section tensor map becomes literal multiplication in K(X)
under the actual injective rational-value maps. -/
theorem globalSectionValue_comp_sectionMultiplicationOver :
    ((D.add E).globalSectionValue k).comp (D.sectionMultiplicationOver k E) =
      (LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k)) := by
  apply TensorProduct.ext'
  intro s t
  exact D.sectionMultiplicationOver_value_tmul k E s t

/-- Surjectivity may be checked in the actual function field because the
target section map is proved injective. -/
theorem sectionMultiplicationOver_surjective_iff_range :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      ((LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k))).range =
      ((D.add E).globalSectionValue k).range := by
  rw [← D.globalSectionValue_comp_sectionMultiplicationOver k E]
  constructor
  · intro hs
    ext r
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨D.sectionMultiplicationOver k E s,rfl⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨s,rfl⟩ := hs t
      exact ⟨s,rfl⟩
  · intro hr t
    have ht : (D.add E).globalSectionValue k t ∈
        (((D.add E).globalSectionValue k).comp
          (D.sectionMultiplicationOver k E)).range := by
      rw [hr]
      exact ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := ht
    exact ⟨s,(D.add E).globalSectionValue_injective k hs⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.globalSectionValue_comp_sectionMultiplicationOver
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_range
