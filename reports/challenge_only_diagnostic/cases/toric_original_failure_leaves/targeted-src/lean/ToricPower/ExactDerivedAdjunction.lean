module

public import ToricPower.ComplexAdjunction
public import ToricPower.CategoricalFoundations
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Exact adjunctions on unbounded derived categories

Both ordinary functors are required to be exact. Their termwise functors
therefore preserve quasi-isomorphisms, and the actual complex adjunction
descends through the two derived localizations. No injective resolution,
boundedness condition, or derived full-faithfulness assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasDerivedCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The adjunction of the actual unbounded derived functors of two
exact adjoint functors. -/
def exactDerivedAdjunction (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (complexAdjunction adj (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

/-- An isomorphism counit remains an isomorphism after actual derived
localization. Thus this construction retains full faithfulness of the
right adjoint when the ordinary adjunction has that property. -/
theorem exactDerivedAdjunction_counit_isIso (adj : F ⊣ G) [IsIso adj.counit] :
    IsIso (exactDerivedAdjunction adj).counit := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let η := (exactDerivedAdjunction adj).counit
  let L := Localization.whiskeringLeftFunctor' (DerivedCategory.Q (C := B))
    (HomologicalComplex.quasiIso B (.up ℤ)) (DerivedCategory B)
  letI : IsIso (L.map η) := by
    haveI (K : CochainComplex B ℤ) : IsIso ((L.map η).app K) := by
      change IsIso ((exactDerivedAdjunction adj).counit.app (DerivedCategory.Q.obj K))
      unfold exactDerivedAdjunction
      rw [Adjunction.localization_counit_app]
      letI : IsIso ((complexAdjunction adj (.up ℤ)).counit.app K) := by
        haveI (n : ℤ) : IsIso (((complexAdjunction adj (.up ℤ)).counit.app K).f n) :=
          inferInstanceAs (IsIso (adj.counit.app (K.X n)))
        exact HomologicalComplex.Hom.isIso_of_components _
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso η L

/-- Full faithfulness of an exact right adjoint passes to the unbounded
derived functor by the checked localized adjunction. -/
def exactDerivedRightFullyFaithful (adj : F ⊣ G) [G.Full] [G.Faithful] :
    G.mapDerivedCategory.FullyFaithful := by
  letI := exactDerivedAdjunction_counit_isIso adj
  exact (exactDerivedAdjunction adj).fullyFaithfulROfIsIsoCounit

end ToricPower

end
