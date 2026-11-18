module

public import ToricPower.SerrePairingRetract
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite direct sums of Serre pairings

The finite-product duality used here is the literal linear equivalence
LinearMap.lsum. No finiteness is imposed on any individual Hom space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace ToricPower.SerrePairing

universe v u w t
variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {I : Type t} [Fintype I] [DecidableEq I]
variable (family : I → C) [HasBiproduct family]

def homToBiproduct (E : C) :
    (E ⟶ ⨁ family) ≃ₗ[k] ∀ i, E ⟶ family i where
  toFun f i := f ≫ biproduct.π family i
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext
    intro i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' a f := by
    funext i
    simp

variable (T : C ⥤ C) [T.Additive]

def mappedBiproductHom (E : C) :
    (T.obj (⨁ family) ⟶ E) ≃ₗ[k] ∀ i, T.obj (family i) ⟶ E where
  toFun f i := T.map (biproduct.ι family i) ≫ f
  invFun f := ∑ i, T.map (biproduct.π family i) ≫ f i
  left_inv f := by
    calc
      (∑ i, T.map (biproduct.π family i) ≫
          (T.map (biproduct.ι family i) ≫ f)) =
          (∑ i, T.map (biproduct.π family i ≫ biproduct.ι family i)) ≫ f := by
        simp only [Preadditive.sum_comp, CategoryTheory.Functor.map_comp, Category.assoc]
      _ = T.map (∑ i, biproduct.π family i ≫ biproduct.ι family i) ≫ f := by
        rw [CategoryTheory.Functor.map_sum]
      _ = f := by
        rw [biproduct.total, CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv f := by
    funext i
    simp only [Preadditive.comp_sum, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ different
      simp [biproduct.ι_π, Ne.symm different]
    · simp
  map_add' f g := by
    funext i
    simp
  map_smul' a f := by
    funext i
    simp

def biproductEquiv (pairing : ∀ i, CodomainPairing k T (family i)) (E : C) :
    (E ⟶ ⨁ family) ≃ₗ[k] Module.Dual k (T.obj (⨁ family) ⟶ E) :=
  (homToBiproduct k family E).trans
    ((LinearEquiv.piCongrRight fun i => (pairing i).equiv E).trans
      ((LinearMap.lsum k (fun i => T.obj (family i) ⟶ E) k).trans
        (mappedBiproductHom k family T E).dualMap))

theorem biproductEquiv_apply
    (pairing : ∀ i, CodomainPairing k T (family i))
    (E : C) (f : E ⟶ ⨁ family) (g : T.obj (⨁ family) ⟶ E) :
    biproductEquiv k family T pairing E f g =
      ∑ i, (pairing i).equiv E (f ≫ biproduct.π family i)
        (T.map (biproduct.ι family i) ≫ g) := by
  simp [biproductEquiv, homToBiproduct, mappedBiproductHom, LinearMap.lsum_apply]

def biproductPairing (pairing : ∀ i, CodomainPairing k T (family i)) :
    CodomainPairing k T (⨁ family) where
  equiv := biproductEquiv k family T pairing
  naturality {E E'} a f g := by
    rw [biproductEquiv_apply, biproductEquiv_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Category.assoc, (pairing i).naturality, Category.assoc]

/-- Compatibility for every block of an actual matrix implies
compatibility for the entire finite-biproduct morphism. -/
theorem biproductPairing_compatible
    {J : Type t} [Fintype J] [DecidableEq J]
    (otherFamily : J → C) [HasBiproduct otherFamily]
    (pairing : ∀ i, CodomainPairing k T (family i))
    (otherPairing : ∀ j, CodomainPairing k T (otherFamily j))
    (a : (⨁ family) ⟶ ⨁ otherFamily)
    (blocks : ∀ i j, Compatible k (pairing i) (otherPairing j)
      (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j)) :
    Compatible k (biproductPairing k family T pairing)
      (biproductPairing k otherFamily T otherPairing) a := by
  intro E f g
  change biproductEquiv k otherFamily T otherPairing E (f ≫ a) g =
    biproductEquiv k family T pairing E f (T.map a ≫ g)
  rw [biproductEquiv_apply, biproductEquiv_apply]
  have decompose (j : J) :
      (f ≫ a) ≫ biproduct.π otherFamily j =
        ∑ i, (f ≫ biproduct.π family i) ≫
          (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) := by
    have total := congrArg (fun h => (f ≫ h) ≫ a ≫ biproduct.π otherFamily j)
      (biproduct.total (f := family))
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc, Category.comp_id] using total.symm
  have sumBlocks (i : I) :
      (∑ j, T.map (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) ≫
        (T.map (biproduct.ι otherFamily j) ≫ g)) =
        T.map (biproduct.ι family i) ≫ (T.map a ≫ g) := by
    have total : (∑ j, (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) ≫
        biproduct.ι otherFamily j) = biproduct.ι family i ≫ a := by
      simpa only [Preadditive.comp_sum, Category.assoc, Category.comp_id] using
        congrArg (fun h => (biproduct.ι family i ≫ a) ≫ h)
          (biproduct.total (f := otherFamily))
    calc
      _ = T.map (∑ j, (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) ≫
          biproduct.ι otherFamily j) ≫ g := by
        simp only [CategoryTheory.Functor.map_sum, Preadditive.sum_comp,
          CategoryTheory.Functor.map_comp, Category.assoc]
      _ = _ := by rw [total, CategoryTheory.Functor.map_comp, Category.assoc]
  calc
    _ = ∑ j, ∑ i, (otherPairing j).equiv E
        ((f ≫ biproduct.π family i) ≫
          (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j))
        (T.map (biproduct.ι otherFamily j) ≫ g) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [decompose]
      simp only [map_sum, LinearMap.sum_apply]
    _ = ∑ j, ∑ i, (pairing i).equiv E (f ≫ biproduct.π family i)
        (T.map (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) ≫
          (T.map (biproduct.ι otherFamily j) ≫ g)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact blocks i j E _ _
    _ = ∑ i, ∑ j, (pairing i).equiv E (f ≫ biproduct.π family i)
        (T.map (biproduct.ι family i ≫ a ≫ biproduct.π otherFamily j) ≫
          (T.map (biproduct.ι otherFamily j) ≫ g)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← map_sum, sumBlocks]

end ToricPower.SerrePairing

end

