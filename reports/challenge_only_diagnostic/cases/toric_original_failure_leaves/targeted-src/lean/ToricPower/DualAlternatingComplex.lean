module

public import ToricPower.AdditiveAlternatingCoface
public import Mathlib.Algebra.Homology.Opposite

/-! # Exact duality of the full alternating face and coface complexes -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : Cᵒᵖ ⥤ D) [F.Additive] (X : SimplicialObject C)

/-- The degree identities retain all signs when an actual simplicial
chain complex is dualized by any additive contravariant functor. -/
def dualAlternatingIso :
    (F.mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj X).op ≅
      AlgebraicTopology.AlternatingCofaceMapComplex.obj (X.rightOp ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun p q related => by
      change p+1 = q at related
      subst q
      simp [AlgebraicTopology.AlternatingFaceMapComplex.obj,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD,
        ChainComplex.of_d,CochainComplex.of_d,op_sum,op_zsmul,F.map_sum,F.map_zsmul]
      rfl)

variable {E : Type*} [Category* E] [Preadditive E]
  (G : D ⥤ E) [G.Additive] (Y : CosimplicialObject E)
  (e : X.rightOp ⋙ F ⋙ G ≅ Y)

/-- The entire scalar comparison is factored before specializing its
functors, avoiding repeated reduction of large coefficient records. -/
def dualAlternatingComparisonIso :
    (G.mapHomologicalComplex (.up ℕ)).obj
      ((F.mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj X).op) ≅
      AlgebraicTopology.AlternatingCofaceMapComplex.obj Y :=
  (G.mapHomologicalComplex (.up ℕ)).mapIso (dualAlternatingIso F X) ≪≫
    (additiveAlternatingCofaceIso G (X.rightOp ⋙ F)).symm ≪≫
      (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso e

theorem dualAlternatingComparisonIso_hom_f (q : ℕ) :
    (dualAlternatingComparisonIso F X G Y e).hom.f q = e.hom.app ⦋q⦌ := by
  simp only [dualAlternatingComparisonIso,Iso.trans_hom,HomologicalComplex.comp_f,
    Functor.mapIso_hom,Functor.mapHomologicalComplex_map_f]
  change G.map (𝟙 _) ≫ 𝟙 _ ≫ e.hom.app ⦋q⦌ = _
  rw [G.map_id,Category.id_comp,Category.id_comp]

end ToricPower

end
