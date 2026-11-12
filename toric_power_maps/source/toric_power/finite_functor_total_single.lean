module

public import ToricPower.FiniteFunctorTotalMap
public import ToricPower.FiniteTotalSingleRow
public import Mathlib.Algebra.Homology.Single

/-!
# Totalizing a genuine single-degree coefficient functor

The finite total of `single_n ∘ H` is canonically `H(K)[-n]`, with
its actual shifted differential and the original biproduct projection.
The calculation keeps arbitrary unbounded coefficient complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasZeroObject B] [HasFiniteBiproducts B]
  (H : A ⥤ B) [H.Additive] (n : ℕ)

abbrev singleCoefficient : A ⥤ CochainComplex B ℕ :=
  H ⋙ HomologicalComplex.single B (.up ℕ) n

theorem singleCoefficient_off_zero {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ) :
    off (singleCoefficient H n) K (width := width) a = 0 := by
  classical
  apply biproduct.hom_ext'
  intro p
  apply biproduct.hom_ext
  intro q
  simp only [off,Category.assoc,biproduct.ι_matrix_assoc,biproduct.lift_π,comp_zero,zero_comp]
  unfold offEntry
  split_ifs
  · simp only [transportedHorizontal,singleCoefficient,Functor.comp_obj,single_obj_d,zero_comp]
  · rfl

def singleDegreeIso : degree (singleCoefficient H n) n ≅ H :=
  isoWhiskerLeft H (HomologicalComplex.singleCompEvalIsoSelf B (.up ℕ) n) ≪≫
    Functor.rightUnitor H

/-- The genuine termwise and shifted identification of the surviving
row. -/
def singleRowIso (K : CochainComplex A ℤ) {width : ℕ} (retained : n < width) :
    row (singleCoefficient H n) K (⟨n,retained⟩ : Fin width) ≅
      (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(n : ℤ))).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj K) :=
  (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(n : ℤ))).mapIso
    ((NatIso.mapHomologicalComplex (singleDegreeIso H n) (.up ℤ)).app K)

/-- The actual entire single-degree total, with no boundedness
condition on `K`. -/
def singleTotalIso (K : CochainComplex A ℤ) {width : ℕ} (retained : n < width) :
    total (singleCoefficient H n) width K ≅
      (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(n : ℤ))).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj K) :=
  FiniteTotal.singleRowIso (row (singleCoefficient H n) K)
    (off (singleCoefficient H n) K) (off_coherent (singleCoefficient H n) K)
    (singleCoefficient_off_zero H n K) ⟨n,retained⟩ (by
      intro q different a
      change IsZero (((HomologicalComplex.single B (.up ℕ) n).obj
        (H.obj (K.X (a + -(q.val : ℤ))))).X q.val)
      apply HomologicalComplex.isZero_single_obj_X
      intro same
      exact different (Fin.ext same)) ≪≫
    singleRowIso H n K retained

/-- The original projection followed by the usual single-term frame
is the component of the canonical total isomorphism. -/
theorem singleTotalIso_hom_f (K : CochainComplex A ℤ) {width : ℕ}
    (retained : n < width) (a : ℤ) :
    (singleTotalIso H n K retained).hom.f a =
      biproduct.π (fun q : Fin width => (row (singleCoefficient H n) K q).X a)
        ⟨n,retained⟩ ≫
      (HomologicalComplex.singleObjXSelf (.up ℕ) n
        (H.obj (K.X (a + -(n : ℤ))))).hom := by
  change biproduct.π (fun q : Fin width => (row (singleCoefficient H n) K q).X a)
    ⟨n,retained⟩ ≫ (singleDegreeIso H n).hom.app (K.X (a + -(n : ℤ))) = _
  simp only [singleDegreeIso,Iso.trans_hom,NatTrans.comp_app,
    isoWhiskerLeft_hom,whiskerLeft_app,HomologicalComplex.singleCompEvalIsoSelf,
    NatIso.ofComponents_hom_app,Functor.rightUnitor_hom_app,Category.comp_id]
  exact congrArg
    (fun f => biproduct.π (fun q : Fin width => (row (singleCoefficient H n) K q).X a)
      ⟨n,retained⟩ ≫ f)
    (Category.comp_id (HomologicalComplex.singleObjXSelf (.up ℕ) n
      (H.obj (K.X (a + -(n : ℤ))))).hom)

/-- This isomorphism is natural in the actual unbounded coefficient
complex, hence can be used before and after localization. -/
def singleTotalNatIso {width : ℕ} (retained : n < width) :
    functor (singleCoefficient H n) width ≅
      H.mapHomologicalComplex (.up ℤ) ⋙
        CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) :=
  NatIso.ofComponents (fun K => singleTotalIso H n K retained) (by
    intro K L f
    apply HomologicalComplex.Hom.ext
    funext a
    simp only [HomologicalComplex.comp_f,singleTotalIso_hom_f,Functor.comp_map]
    change (map (singleCoefficient H n) width f).f a ≫
        (biproduct.π (fun q : Fin width => (row (singleCoefficient H n) L q).X a)
          ⟨n,retained⟩ ≫ _) = _
    rw [map_f,← Category.assoc,biproduct.map_π,Category.assoc]
    change _ ≫ (((HomologicalComplex.single B (.up ℕ) n).map
      (H.map (f.f (a + -(n : ℤ))))).f n ≫ _) = _
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl)

end ToricPower.FunctorTotal

end
