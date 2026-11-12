module

public import ToricPower.RelativeAugmentationSingles
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Relative exactness of an actual augmentation cone

Bijections on all single-target homotopy classes imply exactness of the
ordinary Hom rows of the literal mapping cone. Together with the
bounded-below construction, this proves acyclic assembly without a
spectral-sequence convergence assumption or an unbounded resolution.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

namespace ToricPower

universe u v u' v'

section Categorical
variable {A : Type u} [Category.{v} A]
  {B : Type u'} [Category.{v'} B]

/-- Precomposition bijectivity is invariant under an actual target isomorphism. -/
theorem precomp_bijective_targetIso {X X' Y Y' : A} (f : X ⟶ X')
    (e : Y ≅ Y') (h : Function.Bijective (fun g : X' ⟶ Y => f ≫ g)) :
    Function.Bijective (fun g : X' ⟶ Y' => f ≫ g) := by
  constructor
  · intro a b hab
    apply (cancel_mono e.inv).mp
    apply h.injective
    simpa only [Category.assoc] using congrArg (fun z => z ≫ e.inv) hab
  · intro a
    obtain ⟨b, hb⟩ := h.surjective (a ≫ e.inv)
    refine ⟨b ≫ e.hom, ?_⟩
    change f ≫ b ≫ e.hom = a
    change f ≫ b = a ≫ e.inv at hb
    rw [← Category.assoc, hb, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- An adjunction transports the actual precomposition map and its
surjectivity, including its naturality square. -/
theorem precomp_surjective_adjoint {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {X X' : A} (f : X ⟶ X') (Y : B)
    (h : Function.Surjective (fun g : X' ⟶ G.obj Y => f ≫ g)) :
    Function.Surjective (fun g : F.obj X' ⟶ Y => F.map f ≫ g) := by
  intro a
  obtain ⟨b, hb⟩ := h (adj.homEquiv X Y a)
  refine ⟨(adj.homEquiv X' Y).symm b, ?_⟩
  apply (adj.homEquiv X Y).injective
  rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact hb

end Categorical

section Triangulated
variable {A : Type u} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasShift A ℤ]
  [∀ n : ℤ, CategoryTheory.Functor.Additive (CategoryTheory.shiftFunctor A n)] [Pretriangulated A]

/-- The exact Hom sequence of a distinguished triangle detects all maps
from its third term from two actual precomposition conditions. -/
theorem triangle_hom_eq_zero_of_precomp
    (T : Triangle A) (hT : T ∈ distTriang A) (Y : A)
    (hi : Function.Injective (fun g : T.obj₂ ⟶ Y => T.mor₁ ≫ g))
    (hs : Function.Surjective (fun g : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y => T.mor₁⟦(1 : ℤ)⟧' ≫ g))
    (f : T.obj₃ ⟶ Y) : f = 0 := by
  have hf : T.mor₂ ≫ f = 0 := by
    apply hi
    change T.mor₁ ≫ T.mor₂ ≫ f = T.mor₁ ≫ 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp, comp_zero]
  obtain ⟨b, hb⟩ := T.yoneda_exact₃ hT f hf
  obtain ⟨c, hc⟩ := hs b
  change T.mor₁⟦(1 : ℤ)⟧' ≫ c = b at hc
  rw [hb, ← hc, ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

end Triangulated

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual mapping cone has exact coefficient rows whenever its
first arrow is a homotopy equivalence against every single target. -/
theorem rightHomExact_cone_of_single_precomp
    {K L : CochainComplex C ℤ} (ε : K ⟶ L) (Y : C)
    (h : ∀ q : ℤ, Function.Bijective (fun g :
      (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
        (HomotopyCategory.singleFunctor C q).obj Y =>
      (HomotopyCategory.quotient C (.up ℤ)).map ε ≫ g)) :
    RightHomExact (mappingCone ε) Y := by
  apply rightHomExact_of_single_homotopy
  intro q f
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).mp
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let e := ((HomotopyCategory.singleFunctors C).shiftIso (-1) (q+1) q (by omega)).app Y
  have hs := precomp_surjective_adjoint
    (shiftEquiv (HomotopyCategory C (.up ℤ)) (1 : ℤ)).toAdjunction (Q.map ε)
    ((HomotopyCategory.singleFunctor C q).obj Y)
    (precomp_bijective_targetIso (Q.map ε) e.symm (h (q+1))).surjective
  exact triangle_hom_eq_zero_of_precomp (mappingCone.triangleh ε)
    (HomotopyCategory.mappingCone_triangleh_distinguished ε)
    ((HomotopyCategory.singleFunctor C q).obj Y) (h q).injective hs (Q.map f)

/-- Exact augmented rows assemble to an acyclic full signed Hom
complex of the literal augmentation cone. -/
theorem augmentation_cone_linearHom_acyclic
    (R : Type*) [CommRing R] [Linear R C]
    (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (Z : C)
    (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj Z) [Epi (ε.f 0)]
    (L : CochainComplex C ℤ) (d : ℤ) [L.IsStrictlyGE d]
    (h : ∀ q, AugmentationHomExact K Z (L.X q) ε) :
    (CochainComplex.linearHomComplex R (mappingCone ε) L).Acyclic := by
  apply linearHomComplex_acyclic_of_rightHomExact R _ L d
  intro q
  exact rightHomExact_cone_of_single_precomp ε (L.X q)
    (augmentation_single_precomp_bijective K Z (L.X q) ε (h q))

end ToricPower
