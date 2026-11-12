module

public import ToricPower.InternalDualComplex
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual internal duals of finite biproducts

The comparison is built from the actual duals of the inclusions and
projections. Its matrix formula is the literal transposition of entries.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped BigOperators

namespace ToricPower

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {I J : Type w} [Fintype I] [Fintype J] (L : I → C) (M : J → C)

/-- The comparison uses the dual of each original inclusion. -/
def internalDualBiproductIso :
    (internalDual C).obj (op (⨁ L)) ≅
      ⨁ (fun i => (internalDual C).obj (op (L i))) where
  hom := biproduct.lift (fun i => (internalDual C).map (biproduct.ι L i).op)
  inv := biproduct.desc (fun i => (internalDual C).map (biproduct.π L i).op)
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [← Functor.map_comp, ← op_comp, ← Functor.map_sum, ← op_sum,
      biproduct.total, op_id, Functor.map_id]
    exact (internalDual C).map_id _
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ← Functor.map_comp, ← op_comp]
    by_cases equal : i = j
    · subst j; simp
    · simp [equal, Ne.symm equal]
      exact (internalDual C).map_zero _ _

@[reassoc (attr := simp)]
theorem internalDualBiproductIso_hom_π (i : I) :
    (internalDualBiproductIso L).hom ≫
        biproduct.π (fun j => (internalDual C).obj (op (L j))) i =
      (internalDual C).map (biproduct.ι L i).op :=
  biproduct.lift_π _ _

@[reassoc (attr := simp)]
theorem internalDualBiproductIso_ι_inv (i : I) :
    biproduct.ι (fun j => (internalDual C).obj (op (L j))) i ≫
        (internalDualBiproductIso L).inv =
      (internalDual C).map (biproduct.π L i).op :=
  biproduct.ι_desc _ _

/-- Every actual opposite matrix entry is retained. -/
theorem internalDualBiproductIso_matrix (f : (⨁ L) ⟶ ⨁ M) (i : I) (j : J) :
    biproduct.ι (fun j => (internalDual C).obj (op (M j))) j ≫
        (internalDualBiproductIso M).inv ≫ (internalDual C).map f.op ≫
        (internalDualBiproductIso L).hom ≫
        biproduct.π (fun i => (internalDual C).obj (op (L i))) i =
      (internalDual C).map (biproduct.ι L i ≫ f ≫ biproduct.π M j).op := by
  rw [internalDualBiproductIso_ι_inv_assoc, internalDualBiproductIso_hom_π]
  simp only [op_comp, Functor.map_comp, Category.assoc]

end ToricPower
