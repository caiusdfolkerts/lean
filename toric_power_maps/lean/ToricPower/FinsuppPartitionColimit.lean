module

public import ToricPower.ModuleDirectSumColimit
public import ToricPower.HomologicalComplexColimitLinear
public import ToricPower.ExactComplexCoproducts
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# A free module partitioned into its complete family of fibers

The comparison retains each original finite-support generator. Applying
the genuine single-degree functor gives the categorical coproduct of
the full family of single-degree fiber complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable (k : Type) [Field k] {I J : Type} (L : I → Type) (e : J ≃ Σ i, L i)

def freePartitionFamily : Discrete I ⥤ ModuleCat k :=
  Discrete.functor (fun i => ModuleCat.of k (L i →₀ k))

def freePartitionInclusion (i : I) :
    ModuleCat.of k (L i →₀ k) ⟶ ModuleCat.of k (J →₀ k) :=
  ModuleCat.ofHom (Finsupp.lmapDomain k k (fun x : L i => e.symm ⟨i,x⟩))

def freePartitionLinearEquiv : (J →₀ k) ≃ₗ[k] Π₀ i, L i →₀ k :=
  (Finsupp.mapDomain.linearEquiv k k e).trans (sigmaFinsuppLequivDFinsupp k)

theorem freePartitionLinearEquiv_inclusion (i : I) :
    freePartitionInclusion k L e i ≫ (freePartitionLinearEquiv k L e).toModuleIso.hom =
      ModuleCat.ofHom (X := L i →₀ k)
        (Y := Π₀ j, L j →₀ k)
        (DFinsupp.lsingle (R := k) (M := fun j => L j →₀ k) i) := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change sigmaFinsuppLequivDFinsupp k
    (Finsupp.mapDomain e (Finsupp.mapDomain (fun y : L i => e.symm ⟨i,y⟩)
      (Finsupp.single x a))) = DFinsupp.single i (Finsupp.single x a)
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Equiv.apply_symm_apply]
  exact sigmaFinsuppEquivDFinsupp_single (⟨i,x⟩ : Σ j, L j) a

def freePartitionColimitIso : ModuleCat.of k (J →₀ k) ≅ colimit (freePartitionFamily k L) :=
  (freePartitionLinearEquiv k L e).toModuleIso ≪≫
    ModuleDirectSum.sumColimitIso k (freePartitionFamily k L)

@[reassoc]
theorem freePartitionColimitIso_inclusion (i : I) :
    freePartitionInclusion k L e i ≫ (freePartitionColimitIso k L e).hom =
      colimit.ι (freePartitionFamily k L) ⟨i⟩ := by
  rw [freePartitionColimitIso, Iso.trans_hom, ← Category.assoc,
    freePartitionLinearEquiv_inclusion]
  exact ModuleDirectSum.sumColimitIso_inclusion k (freePartitionFamily k L) i

variable (n : ℕ)

local notation "singleTop" => HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℕ) n

def freePartitionSingleFamilyIso :
    freePartitionFamily k L ⋙ singleTop ≅
      Discrete.functor (fun i => (singleTop).obj (ModuleCat.of k (L i →₀ k))) :=
  Discrete.natIso (fun _ => Iso.refl _)

def freePartitionSingleColimitIso :
    (singleTop).obj (ModuleCat.of k (J →₀ k)) ≅
      colimit (Discrete.functor (fun i => (singleTop).obj (ModuleCat.of k (L i →₀ k)))) :=
  (singleTop).mapIso (freePartitionColimitIso k L e) ≪≫
    preservesColimitIso singleTop (freePartitionFamily k L) ≪≫
      HasColimit.isoOfNatIso (freePartitionSingleFamilyIso k L n)

@[reassoc]
theorem freePartitionSingleColimitIso_inclusion (i : I) :
    colimit.ι (Discrete.functor (fun i => (singleTop).obj (ModuleCat.of k (L i →₀ k)))) ⟨i⟩ ≫
        (freePartitionSingleColimitIso k L e n).inv =
      (singleTop).map (freePartitionInclusion k L e i) := by
  apply (cancel_mono ((singleTop).map (freePartitionColimitIso k L e).hom)).mp
  simp only [freePartitionSingleColimitIso, Iso.trans_inv, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  rw [HasColimit.ι_isoOfNatIso_inv_assoc]
  simp only [freePartitionSingleFamilyIso, Discrete.natIso_inv_app, Iso.refl_inv,
    Category.id_comp]
  erw [Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [ι_preservesColimitIso_inv, freePartitionColimitIso_inclusion]

end ToricPower.IntegralArrangement

end
