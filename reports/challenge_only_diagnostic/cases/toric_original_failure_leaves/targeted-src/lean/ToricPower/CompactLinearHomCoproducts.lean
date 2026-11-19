module

public import ToricPower.CompactHomCoproduct
public import ToricPower.FiniteDiagramCoproductCompact
public import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Actual coproduct preservation of scalar-linear Hom

The full finite-support Hom isomorphism identifies the canonical
categorical coproduct comparison itself. Consequently the scalar-linear
Hom functor of a compact source preserves arbitrary coproducts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.CompactExtraction

universe u v
variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasCoproducts.{v} C]
  (P : C) (compact : CoproductCompact.{u,v,v} P)
  {I : Type v} (family : I → C)

def linearHomCoproductIso :
    (∐ fun i => ModuleCat.of R (P ⟶ family i)) ≅ ModuleCat.of R (P ⟶ ∐ family) :=
  ModuleCat.coprodIsoDirectSum (fun i => ModuleCat.of R (P ⟶ family i)) ≪≫
    (homCoproductLinearEquiv R P family compact).toModuleIso

@[reassoc]
theorem linearHomCoproductIso_inclusion (i : I) :
    Sigma.ι (fun i => ModuleCat.of R (P ⟶ family i)) i ≫
      (linearHomCoproductIso R P compact family).hom =
        ModuleCat.ofHom (Linear.rightComp R P (Sigma.ι family i)) := by
  rw [linearHomCoproductIso,Iso.trans_hom,← Category.assoc,
    ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact homCoproductSum_single R P family i f

theorem linearHomCoproductIso_comparison :
    sigmaComparison ((linearCoyoneda R C).obj (op P)) family =
      (linearHomCoproductIso R P compact family).hom := by
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison]
  change ModuleCat.ofHom (Linear.rightComp R P (Sigma.ι family i)) =
    Sigma.ι (fun i => ModuleCat.of R (P ⟶ family i)) i ≫
      (linearHomCoproductIso R P compact family).hom
  exact (linearHomCoproductIso_inclusion R P compact family i).symm

include compact in
theorem linearHom_preservesCoproduct :
    PreservesColimit (Discrete.functor family) ((linearCoyoneda R C).obj (op P)) := by
  haveI : IsIso (sigmaComparison ((linearCoyoneda R C).obj (op P)) family) := by
    rw [linearHomCoproductIso_comparison R P compact family]
    infer_instance
  exact PreservesCoproduct.of_iso_comparison _ _

end ToricPower.CompactExtraction

end
