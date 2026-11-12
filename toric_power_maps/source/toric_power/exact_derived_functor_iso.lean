module

public import ToricPower.CategoricalFoundations

/-!
# Natural isomorphisms of exact derived functors

An isomorphism of exact additive functors acts termwise on complexes and
then descends through the actual localization at quasi-isomorphisms.
The two inverse identities follow from functoriality of that localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The actual natural isomorphism on the full unbounded derived categories. -/
def exactDerivedFunctorIso (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory where
  hom := e.hom.mapDerivedCategory
  inv := e.inv.mapDerivedCategory
  hom_inv_id := by
    rw [← NatTrans.mapDerivedCategory_comp, e.hom_inv_id,
      NatTrans.mapDerivedCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapDerivedCategory_comp, e.inv_hom_id,
      NatTrans.mapDerivedCategory_id]

end ToricPower

end
