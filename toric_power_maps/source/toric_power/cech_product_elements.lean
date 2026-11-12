module

public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Elements of an actual product of abelian groups

This small generic API is extracted from CechComparisonFoundations so the
pure incidence and topology proofs do not import the scheme/sheaf theory.
The construction and proof bodies are retained verbatim in their own namespace.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CechProductElements

def productElementsEquiv {Tuple : Type u} (coefficient : Tuple → AddCommGrpCat.{u}) :
    (∏ᶜ coefficient : AddCommGrpCat.{u}) ≃+ (∀ index, coefficient index) :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor coefficient))
    (AddCommGrpCat.HasLimit.productLimitCone coefficient).isLimit).addCommGroupIsoToAddEquiv

theorem productElementsEquiv_apply {Tuple : Type u} (coefficient : Tuple → AddCommGrpCat.{u})
    (element : (∏ᶜ coefficient : AddCommGrpCat.{u})) (index : Tuple) :
    productElementsEquiv coefficient element index = Limits.Pi.π coefficient index element := by
  have projection := IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (Discrete.functor coefficient))
    (AddCommGrpCat.HasLimit.productLimitCone coefficient).isLimit (Discrete.mk index)
  exact (ConcreteCategory.congr_hom projection element).symm

theorem productElementsEquiv_map {Tuple : Type u} {first second : Tuple → AddCommGrpCat.{u}}
    (coefficient_map : ∀ index, first index ⟶ second index)
    (element : (∏ᶜ first : AddCommGrpCat.{u})) (index : Tuple) :
    productElementsEquiv second (Limits.Pi.map coefficient_map element) index =
      coefficient_map index (productElementsEquiv first element index) := by
  rw [productElementsEquiv_apply, productElementsEquiv_apply]
  exact ConcreteCategory.congr_hom (Limits.Pi.map_π coefficient_map index) element

end ToricPower.CechProductElements
