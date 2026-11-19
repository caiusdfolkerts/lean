module

public import ToricPower.ProjectiveSectionSingleNaturality
public import ToricPower.LinearHomToSingleExtension
public import ToricPower.RelativeBoundedSourceHomotopy

/-! # Recognizing the actual scalar section comparison

A quasi-isomorphism from a single coefficient to the actual projective
section complex forces the original ordinary section map to be an
isomorphism and all positive coefficient rows to be exact. Degree zero
uses only the actual cokernel property of the projective augmentation.
These implications allow the bounded-source assembly theorem to apply
to arbitrary unbounded targets.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]
  {Z : C} (P : ProjectiveResolution Z) (Y : C)

theorem projectiveAugmentation_zero_factor
    (f : (projectiveCochain P).X 0 ⟶ Y)
    (closed : (projectiveCochain P).d (-1) 0 ≫ f = 0) :
    ∃ g : Z ⟶ Y, (projectiveCochainAugmentation P).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 Z).hom ≫ g = f := by
  let e₀ := P.complex.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl)
  let e₁ := P.complex.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f 1 = (-1 : ℤ) by rfl)
  have hf : P.complex.d 1 0 ≫ e₀.inv ≫ f = 0 := by
    change (P.complex.extend ComplexShape.embeddingDownNat).d (-1) 0 ≫ f = 0 at closed
    rw [P.complex.extend_d_eq ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 1 = (-1 : ℤ) by rfl)
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl)] at closed
    have h := congrArg (fun z => e₁.inv ≫ z) closed
    simpa only [e₀,e₁,Category.assoc,Iso.inv_hom_id_assoc,comp_zero] using h
  obtain ⟨g,hg⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork
    (e₀.inv ≫ f) hf
  change ((ChainComplex.single₀ C).obj Z).X 0 ⟶ Y at g
  change P.π.f 0 ≫ g = e₀.inv ≫ f at hg
  refine ⟨(singleObjXSelf (.down ℕ) 0 Z).inv ≫ g,?_⟩
  rw [← Category.assoc,projectiveCochainAugmentation_zero]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,hg]
  exact e₀.hom_inv_id_assoc f

/-- The degree-zero augmentation property is unconditional, including
for coefficient objects which have nonzero higher Ext groups. -/
theorem projectiveAugmentation_zero_precomp_bijective :
    Function.Bijective (fun f :
      (HomotopyCategory.singleFunctor C 0).obj Z ⟶
        (HomotopyCategory.singleFunctor C 0).obj Y =>
      (HomotopyCategory.quotient C (.up ℤ)).map (projectiveCochainAugmentation P) ≫ f) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let ε := projectiveCochainAugmentation P
  constructor
  · intro a b equal
    obtain ⟨a,rfl⟩ := Q.map_surjective a
    obtain ⟨b,rfl⟩ := Q.map_surjective b
    have h : Nonempty (Homotopy (ε ≫ a) (ε ≫ b)) := by
      refine ⟨HomotopyCategory.homotopyOfEq (ε ≫ a) (ε ≫ b) ?_⟩
      simpa only [CategoryTheory.Functor.map_comp] using equal
    have equation := h.some.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      HomologicalComplex.single_obj_d,comp_zero,
      ((projectiveCochain P).isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt
        ((projectiveCochain P).d 0 1) 0,
      zero_comp,add_zero,zero_add] at equation
    have same : a = b := by
      apply HomologicalComplex.to_single_hom_ext
      apply (cancel_epi (ε.f 0)).mp
      exact equation
    exact congrArg Q.map same
  · intro f
    obtain ⟨f,rfl⟩ := Q.map_surjective f
    have closed : (projectiveCochain P).d (-1) 0 ≫
        (f.f 0 ≫ (singleObjXSelf (.up ℤ) 0 Y).hom) = 0 := by
      rw [← Category.assoc,← f.comm,HomologicalComplex.single_obj_d,comp_zero,zero_comp]
    obtain ⟨g,hg⟩ := projectiveAugmentation_zero_factor P Y _ closed
    refine ⟨Q.map ((CochainComplex.singleFunctor C 0).map g),?_⟩
    change Q.map ε ≫ Q.map ((CochainComplex.singleFunctor C 0).map g) = Q.map f
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono (singleObjXSelf (.up ℤ) 0 Y).hom).mp
    rw [HomologicalComplex.comp_f,Category.assoc]
    change ε.f 0 ≫ ((HomologicalComplex.single C (.up ℤ) 0).map g).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 Y).hom = _
    rw [HomologicalComplex.single_map_f_self]
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hg

variable (R : Type r) [CommRing R] [Linear R C]

omit P Y in
theorem linearHomPrecomp_quasiIsoAt_of_homotopy_bijective
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (X : CochainComplex C ℤ) (n : ℤ)
    (h : Function.Bijective (fun g :
      (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj (X⟦n⟧) =>
      (HomotopyCategory.quotient C (.up ℤ)).map f ≫ g)) :
    QuasiIsoAt (linearHomComplexPrecomp R f X) n := by
  rw [quasiIsoAt_iff]
  apply (linearHomComplexPrecompHomologyData R f X n).quasiIso_iff.mpr
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (homClassPrecomp R f X n)
  constructor
  · intro a b equal
    apply (CohomologyClass.homAddEquiv (K := L) (L := X) (n := n)).injective
    apply h.injective
    change (HomotopyCategory.quotient C (.up ℤ)).map f ≫ CohomologyClass.toHom a =
      (HomotopyCategory.quotient C (.up ℤ)).map f ≫ CohomologyClass.toHom b
    rw [← homClassPrecomp_toHom R f X n a,← homClassPrecomp_toHom R f X n b,equal]
  · intro a
    obtain ⟨b,hb⟩ := h.surjective (CohomologyClass.toHom a)
    obtain ⟨z,rfl⟩ := (CohomologyClass.homAddEquiv (K := L) (L := X) (n := n)).surjective b
    refine ⟨z,(CohomologyClass.homAddEquiv (K := K) (L := X) (n := n)).injective ?_⟩
    exact (homClassPrecomp_toHom R f X n z).trans hb

theorem projectiveAugmentation_precomp_quasiIsoAt_zero :
    QuasiIsoAt (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      ((CochainComplex.singleFunctor C 0).obj Y)) 0 := by
  apply linearHomPrecomp_quasiIsoAt_of_homotopy_bijective R
  exact precomp_bijective_targetIso _
    ((HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app
        ((CochainComplex.singleFunctor C 0).obj Y)).symm)
    (projectiveAugmentation_zero_precomp_bijective P Y)

end ToricPower

end
