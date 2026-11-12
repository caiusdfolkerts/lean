module

public import ToricPower.NegativeFunctorTotalMap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z r t

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  {D : Type r} [Category.{t} D] [Preadditive D] [HasFiniteBiproducts D]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive]
  (H : B ⥤ D) [H.Additive]

abbrev postcompose : A ⥤ ChainComplex D ℕ :=
  Φ ⋙ H.mapHomologicalComplex (.down ℕ)

def postcomposeDegreeIso (width : ℕ) (K : CochainComplex A ℤ) (a : ℤ) :
    H.obj ((total Φ width K).X a) ≅ (total (postcompose Φ H) width K).X a :=
  H.mapBiproduct (fun q : Fin width => (row Φ K q).X a)

theorem postcompose_offEntry {width : ℕ} (K : CochainComplex A ℤ)
    (a : ℤ) (p q : Fin width) :
    H.map (offEntry Φ K a p q) = offEntry (postcompose Φ H) K a p q := by
  classical
  unfold offEntry
  split_ifs
  · simp only [transportedHorizontal,postcompose,Functor.comp_obj,
      Functor.map_comp,eqToHom_map]
    rfl
  · exact H.map_zero _ _

theorem postcompose_d_entry {width : ℕ} (K : CochainComplex A ℤ)
    (a : ℤ) (p q : Fin width) :
    H.map (biproduct.ι (fun p => (row Φ K p).X a) p ≫
      (total Φ width K).d a (a+1) ≫
        biproduct.π (fun q => (row Φ K q).X (a+1)) q) =
    biproduct.ι (fun p => (row (postcompose Φ H) K p).X a) p ≫
      (total (postcompose Φ H) width K).d a (a+1) ≫
        biproduct.π (fun q => (row (postcompose Φ H) K q).X (a+1)) q := by
  classical
  change H.map (biproduct.ι _ p ≫
      CochainComplex.of.d (FiniteTotal.term (row Φ K))
        (FiniteTotal.differential (row Φ K) (off Φ K)) a (a+1) ≫ biproduct.π _ q) =
    biproduct.ι _ p ≫
      CochainComplex.of.d (FiniteTotal.term (row (postcompose Φ H) K))
        (FiniteTotal.differential (row (postcompose Φ H) K)
          (off (postcompose Φ H) K)) a (a+1) ≫ biproduct.π _ q
  simp only [CochainComplex.of_d,FiniteTotal.differential,FiniteTotal.diagonal,off,
    comp_add,add_comp,Category.assoc,biproduct.map_π,biproduct.ι_matrix_assoc,
    biproduct.lift_π,Functor.map_add,postcompose_offEntry]
  congr 1
  by_cases same : p=q
  · subst q
    simp only [← Category.assoc,biproduct.ι_π_self,Category.id_comp]
    change H.map ((chainDegree p : ℤ).negOnePow • (Φ.map (K.d _ _)).f _) =
      (chainDegree p : ℤ).negOnePow • H.map ((Φ.map (K.d _ _)).f _)
    exact H.map_units_smul _ _
  · simp only [← Category.assoc,biproduct.ι_π_ne _ same,zero_comp,Functor.map_zero]

theorem postcomposeDegreeIso_d (width : ℕ) (K : CochainComplex A ℤ) (a : ℤ) :
    H.map ((total Φ width K).d a (a+1)) ≫ (postcomposeDegreeIso Φ H width K (a+1)).hom =
      (postcomposeDegreeIso Φ H width K a).hom ≫
        (total (postcompose Φ H) width K).d a (a+1) := by
  apply (cancel_epi (postcomposeDegreeIso Φ H width K a).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro p
  apply biproduct.hom_ext
  intro q
  simp only [postcomposeDegreeIso,Functor.mapBiproduct_inv,Functor.mapBiproduct_hom,
    Category.assoc,biproduct.ι_desc_assoc]
  erw [biproduct.lift_π]
  simpa only [Functor.map_comp] using postcompose_d_entry Φ H K a p q

def postcomposeIso (width : ℕ) (K : CochainComplex A ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj (total Φ width K) ≅
      total (postcompose Φ H) width K :=
  HomologicalComplex.Hom.isoOfComponents (postcomposeDegreeIso Φ H width K)
    (fun a b relation => by
      obtain rfl : a+1=b := relation
      exact (postcomposeDegreeIso_d Φ H width K a).symm)

end ToricPower.NegativeFunctorTotal

end

