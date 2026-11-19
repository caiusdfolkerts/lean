module

public import ToricPower.LinearVectorCopower
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-! # Linear Hom coordinates of a finite scalar copower

The equivalence is derived from the genuine copower universal property.
Its finite-function coordinates evaluate the original scalar basis
vectors; there is no dual-reflexivity assumption on the target module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B] [HasCoproducts.{u} B]

def vectorCopowerHomLinearEquiv (P : B) (M : ModuleCat.{u} k) (E : B) :
    (vectorCopower k P M ⟶ E) ≃ₗ[k] (M ⟶ ModuleCat.of k (P ⟶ E)) :=
  { vectorCopowerHomEquiv k P M E with
    map_add' f g := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change vectorCopowerInclusion k P M x ≫ (f+g) =
        (vectorCopowerInclusion k P M x ≫ f)+(vectorCopowerInclusion k P M x ≫ g)
      rw [Preadditive.comp_add]
    map_smul' r f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change vectorCopowerInclusion k P M x ≫ (r • f) =
        r • (vectorCopowerInclusion k P M x ≫ f)
      rw [Linear.comp_smul] }

variable (P E : B) (I : Type u) [Finite I]

def vectorCopowerFiniteFunctionsHomEquiv :
    (vectorCopower k P (ModuleCat.of k (I → k)) ⟶ E) ≃ₗ[k] (I → (P ⟶ E)) := by
  letI : Fintype I := Fintype.ofFinite _
  exact ((vectorCopowerHomLinearEquiv k P (ModuleCat.of k (I → k)) E).trans
    ModuleCat.homLinearEquiv).trans ((Pi.basisFun k I).constr k).symm

variable [DecidableEq I]

theorem vectorCopowerFiniteFunctionsHomEquiv_apply
    (f : vectorCopower k P (ModuleCat.of k (I → k)) ⟶ E) (i : I) :
    vectorCopowerFiniteFunctionsHomEquiv k P E I f i =
      vectorCopowerInclusion k P (ModuleCat.of k (I → k)) (Pi.single i 1) ≫ f := by
  letI : Fintype I := Fintype.ofFinite _
  change ((Pi.basisFun k I).constr k).symm _ i = _
  rw [Module.Basis.constr_symm_apply,Pi.basisFun_apply]
  rfl

end ToricPower.Cellular

end

