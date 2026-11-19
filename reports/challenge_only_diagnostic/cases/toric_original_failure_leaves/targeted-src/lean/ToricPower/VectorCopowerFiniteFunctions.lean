module

public import ToricPower.VectorCopowerFree
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Canonical function coordinates of finite scalar copowers

The coefficient module consists of functions on a finite type. Its
copower has one literal label coordinate for each index. The comparison
is constructed from the actual copower universal property, and the
evaluation formula retains both the scalar and label maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.Cellular

variable (k : Type) [Field k] (P : ModuleCat.{0} k)
  (I : Type) [Finite I]

def vectorCopowerFiniteFunctionsIso :
    vectorCopower k P (ModuleCat.of k (I → k)) ≅ ModuleCat.of k (I → P) :=
  (vectorCopowerFunctor k P).mapIso
      (Finsupp.linearEquivFunOnFinite k k I).symm.toModuleIso ≪≫
    vectorCopowerFreeBiproductIso k P I ≪≫
    ModuleCat.biproductIsoPi (fun _ : I => P)

theorem vectorCopowerFiniteFunctionsIso_generator (i : I) :
    vectorCopowerInclusion k P (ModuleCat.of k (I → k)) (Pi.single i 1) ≫
        (vectorCopowerFiniteFunctionsIso k P I).hom =
      biproduct.ι (fun _ : I => P) i ≫
        (ModuleCat.biproductIsoPi (fun _ : I => P)).hom := by
  unfold vectorCopowerFiniteFunctionsIso
  simp only [Iso.trans_hom,Category.assoc,Functor.mapIso_hom]
  rw [← Category.assoc,vectorCopowerInclusion_map]
  change vectorCopowerInclusion k P ((ModuleCat.free k).obj I)
      ((Finsupp.linearEquivFunOnFinite k k I).symm (Pi.single i 1)) ≫ _ = _
  rw [Finsupp.linearEquivFunOnFinite_symm_single]
  exact vectorCopowerFreeBiproductIso_generator_assoc k P I i _

theorem vectorCopowerFiniteFunctionsIso_generator_apply
    (i j : I) (v : P) :
    (vectorCopowerFiniteFunctionsIso k P I).hom
        (vectorCopowerInclusion k P (ModuleCat.of k (I → k)) (Pi.single i 1) v) j =
      if i = j then v else 0 := by
  have generator := ConcreteCategory.congr_hom
    (vectorCopowerFiniteFunctionsIso_generator k P I i) v
  change (vectorCopowerFiniteFunctionsIso k P I).hom
      (vectorCopowerInclusion k P (ModuleCat.of k (I → k)) (Pi.single i 1) v) =
    (ModuleCat.biproductIsoPi (fun _ : I => P)).hom
      (biproduct.ι (fun _ : I => P) i v) at generator
  rw [generator]
  have projection : (ModuleCat.biproductIsoPi (fun _ : I => P)).hom ≫
      ModuleCat.ofHom (LinearMap.proj j : (I → P) →ₗ[k] P) =
        biproduct.π (fun _ : I => P) j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π,Iso.hom_inv_id_assoc]
  have value := ConcreteCategory.congr_hom projection
    (biproduct.ι (fun _ : I => P) i v)
  change (ModuleCat.biproductIsoPi (fun _ : I => P)).hom
      (biproduct.ι (fun _ : I => P) i v) j =
    biproduct.π (fun _ : I => P) j (biproduct.ι (fun _ : I => P) i v) at value
  rw [value,← ModuleCat.comp_apply]
  by_cases equal : i = j
  · subst j
    rw [biproduct.ι_π_self,ModuleCat.id_apply,if_pos rfl]
  · rw [biproduct.ι_π_ne _ equal,if_neg equal]
    rfl

/-- Every vector inclusion has its literal scalar-multiplication
formula in all function coordinates. -/
theorem vectorCopowerFiniteFunctionsIso_inclusion
    (x : I → k) (v : P) (j : I) :
    (vectorCopowerFiniteFunctionsIso k P I).hom
        (vectorCopowerInclusion k P (ModuleCat.of k (I → k)) x v) j =
      x j • v := by
  letI : Fintype I := Fintype.ofFinite I
  have expansion := pi_eq_sum_univ' x
  conv_lhs => rw [expansion]
  simp only [map_sum,map_smul,ModuleCat.hom_sum,ModuleCat.hom_smul,
    LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply]
  change (∑ i : I, x i • ((vectorCopowerFiniteFunctionsIso k P I).hom
    (vectorCopowerInclusion k P (ModuleCat.of k (I → k)) (Pi.single i 1) v)) j) = _
  calc
    _ = ∑ i : I, x i • (if i = j then v else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun y : P => x i • y)
        (vectorCopowerFiniteFunctionsIso_generator_apply k P I i j v)
    _ = x j • v := by simp

end ToricPower.Cellular

end
