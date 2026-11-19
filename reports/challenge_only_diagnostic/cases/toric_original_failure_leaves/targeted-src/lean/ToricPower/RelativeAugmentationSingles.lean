module

public import ToricPower.RelativeHomComplexAcyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Exact coefficient rows and the augmentation on single targets

For a complex concentrated in nonpositive degrees, exactness of its
augmented contravariant coefficient row says precisely that its actual
augmentation induces bijections of homotopy classes into every single
complex. All maps in this statement are the literal precomposition maps.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A factorization through the following differential is a literal
null homotopy of a map to a single complex. -/
theorem toSingle_homotopy_zero_of_factor
    {K : CochainComplex C ℤ} {Y : C} {q : ℤ}
    (f : K ⟶ (CochainComplex.singleFunctor C q).obj Y)
    (g : K.X (q+1) ⟶ Y)
    (hg : K.d q (q+1) ≫ g = f.f q ≫
      (singleObjXSelf (.up ℤ) q Y).hom) : Nonempty (Homotopy f 0) := by
  refine ⟨(Cochain.equivHomotopy f 0).symm
    ⟨Cochain.toSingleMk g (show (q+1)+(-1)=q by omega), ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero,
    Cochain.δ_toSingleMk g (show (q+1)+(-1)=q by omega) 0 q (by omega),
    Int.negOnePow_zero, one_smul, hg]
  apply (Cochain.toSingleEquiv (show q+0=q by omega)).injective
  simp only [Cochain.toSingleEquiv_toSingleMk]
  change (Cochain.ofHom f).v q q (add_zero q) ≫ _ = _
  rw [Cochain.ofHom_v]

/-- Below degree zero, exactness of the actual dual row; at degree zero,
the actual augmentation is its kernel. -/
def AugmentationHomExact (K : CochainComplex C ℤ) (Z Y : C)
    (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj Z) : Prop :=
  (∀ (q : ℤ), q < 0 → ∀ (u : K.X q ⟶ Y), K.d (q-1) q ≫ u = 0 →
    ∃ g : K.X (q+1) ⟶ Y, K.d q (q+1) ≫ g = u) ∧
  (∀ (u : K.X 0 ⟶ Y), K.d (-1) 0 ≫ u = 0 →
    ∃ g : Z ⟶ Y, ε.f 0 ≫ (singleObjXSelf (.up ℤ) 0 Z).hom ≫ g = u)

/-- The source augmentation induces a bijection on the actual homotopy
classes with every shifted single target. -/
theorem augmentation_single_precomp_bijective
    (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (Z Y : C)
    (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj Z) [Epi (ε.f 0)]
    (hex : AugmentationHomExact K Z Y ε) (q : ℤ) :
    Function.Bijective (fun f :
      (HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj Z) ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C q).obj Y) =>
      (HomotopyCategory.quotient C (.up ℤ)).map ε ≫ f) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  by_cases hq : q = 0
  · subst q
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := Q.map_surjective a
      obtain ⟨b, rfl⟩ := Q.map_surjective b
      have h : Nonempty (Homotopy (ε ≫ a) (ε ≫ b)) := by
        refine ⟨HomotopyCategory.homotopyOfEq (ε ≫ a) (ε ≫ b) ?_⟩
        simpa only [CategoryTheory.Functor.map_comp] using hab
      have eq := h.some.comm 0
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
        HomologicalComplex.single_obj_d, comp_zero,
        (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt (K.d 0 1) 0,
        zero_comp, add_zero, zero_add] at eq
      have ab : a = b := by
        apply HomologicalComplex.to_single_hom_ext
        apply (cancel_epi (ε.f 0)).mp
        exact eq
      exact congrArg Q.map ab
    · intro f
      obtain ⟨f, rfl⟩ := Q.map_surjective f
      have closed : K.d (-1) 0 ≫
          (f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 Y).hom) = 0 := by
        rw [← Category.assoc, ← f.comm, HomologicalComplex.single_obj_d,
          comp_zero, zero_comp]
      obtain ⟨g, hg⟩ := hex.2 _ closed
      refine ⟨Q.map ((CochainComplex.singleFunctor C 0).map g), ?_⟩
      change Q.map ε ≫ Q.map ((CochainComplex.singleFunctor C 0).map g) = Q.map f
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
      apply HomologicalComplex.to_single_hom_ext
      apply (cancel_mono (singleObjXSelf (.up ℤ) 0 Y).hom).mp
      rw [HomologicalComplex.comp_f, Category.assoc]
      change ε.f 0 ≫ ((HomologicalComplex.single C (.up ℤ) 0).map g).f 0 ≫
        (singleObjXSelf (.up ℤ) 0 Y).hom = _
      rw [HomologicalComplex.single_map_f_self]
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hg
  · have source_zero (f : Q.obj ((CochainComplex.singleFunctor C 0).obj Z) ⟶
        Q.obj ((CochainComplex.singleFunctor C q).obj Y)) : f = 0 := by
      obtain ⟨f, rfl⟩ := Q.map_surjective f
      have hf : f = 0 := by
        apply HomologicalComplex.to_single_hom_ext
        exact (isZero_single_obj_X (.up ℤ) 0 Z q hq).eq_of_src _ _
      simp only [hf, CategoryTheory.Functor.map_zero]
    have target_zero (f : Q.obj K ⟶
        Q.obj ((CochainComplex.singleFunctor C q).obj Y)) : f = 0 := by
      obtain ⟨f, rfl⟩ := Q.map_surjective f
      apply (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
      by_cases hneg : q < 0
      · have closed : K.d (q-1) q ≫
            (f.f q ≫ (singleObjXSelf (.up ℤ) q Y).hom) = 0 := by
          rw [← Category.assoc, ← f.comm, HomologicalComplex.single_obj_d,
            comp_zero, zero_comp]
        obtain ⟨g, hg⟩ := hex.1 q hneg _ closed
        exact toSingle_homotopy_zero_of_factor f g hg
      · apply Nonempty.intro
        apply Homotopy.ofEq
        apply HomologicalComplex.to_single_hom_ext
        exact (K.isZero_of_isStrictlyLE 0 q (by omega)).eq_of_src _ _
    constructor
    · intro a b _
      exact (source_zero a).trans (source_zero b).symm
    · intro f
      refine ⟨0, ?_⟩
      change Q.map ε ≫ 0 = f
      rw [comp_zero, target_zero f]

end ToricPower
