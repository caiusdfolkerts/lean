module

public import ToricPower.CoproductProjectorMap
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.LinearAlgebra.DFinsupp

/-! # The literal scalar-linear Hom comparison for a compact source

The comparison sums the actual coproduct inclusions. Compactness gives
surjectivity through the canonical finite-support projector; actual
coordinate projections give injectivity. No dimension or reflexivity
assumption is made on any target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

namespace ToricPower.CompactExtraction

universe u v w r
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Actual coproduct coordinate projection in any preadditive category. -/
def coproductCoordinate {I : Type w} (family : I → C) (i : I) :
    (∐ family) ⟶ family i :=
  Sigma.desc (fun j => if h : j = i then eqToHom (congrArg family h) else 0)

@[simp, reassoc]
theorem coproduct_ι_coordinate_same {I : Type w} (family : I → C) (i : I) :
    Sigma.ι family i ≫ coproductCoordinate family i = 𝟙 (family i) := by
  simp [coproductCoordinate,Sigma.ι_comp_desc]

@[simp, reassoc]
theorem coproduct_ι_coordinate_ne {I : Type w} (family : I → C) {i j : I}
    (different : i ≠ j) : Sigma.ι family i ≫ coproductCoordinate family j = 0 := by
  simp [coproductCoordinate,Sigma.ι_comp_desc,different]

theorem coproduct_ι_coordinate_inclusion {I : Type w} (family : I → C) (i j : I) :
    Sigma.ι family j ≫ coproductCoordinate family i ≫ Sigma.ι family i =
      if j = i then Sigma.ι family j else 0 := by
  by_cases same : j = i
  · subst j
    rw [← Category.assoc,coproduct_ι_coordinate_same,Category.id_comp]
    simp
  · simp [coproduct_ι_coordinate_ne_assoc family same,same]

/-- The canonical finite projector is the sum of its genuine coordinate
projections followed by the original coproduct inclusions. -/
theorem finiteCoproductProjector_eq_sum {I : Type w} (family : I → C) (s : Finset I) :
    finiteCoproductProjector family s =
      ∑ i ∈ s, coproductCoordinate family i ≫ Sigma.ι family i := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_sum]
  simp only [coproduct_ι_coordinate_inclusion]
  by_cases member : j ∈ s
  · rw [ι_finiteCoproductProjector family s member]
    simp [Finset.sum_ite_eq,member]
  · rw [ι_finiteCoproductProjector_of_not_mem family s member]
    simp [Finset.sum_ite_eq,member]

variable (R : Type r) [CommRing R] [Linear R C]
  (P : C) {I : Type w} (family : I → C)

/-- The actual sum of a finitely supported family of Hom coefficients. -/
def homCoproductSum : (Π₀ i : I, P ⟶ family i) →ₗ[R] (P ⟶ ∐ family) :=
  DFinsupp.lsum R (fun i => Linear.rightComp R P (Sigma.ι family i))

@[simp]
theorem homCoproductSum_single (i : I) (f : P ⟶ family i) :
    homCoproductSum R P family (DFinsupp.single i f) = f ≫ Sigma.ι family i :=
  DFinsupp.lsum_single (S := R) _ _ _

theorem homCoproductSum_projection (i : I) (f : Π₀ j : I, P ⟶ family j) :
    homCoproductSum R P family f ≫ coproductCoordinate family i = f i := by
  have h : (Linear.rightComp R P (coproductCoordinate family i)).comp
      (homCoproductSum R P family) = DFinsupp.lapply i := by
    apply DFinsupp.lhom_ext
    intro j a
    change homCoproductSum R P family (DFinsupp.single j a) ≫
      coproductCoordinate family i = _
    rw [homCoproductSum_single]
    by_cases same : j = i
    · subst j
      rw [Category.assoc,coproduct_ι_coordinate_same,Category.comp_id,
        DFinsupp.lapply_apply,DFinsupp.single_eq_same]
    · rw [Category.assoc,coproduct_ι_coordinate_ne family same,comp_zero,
        DFinsupp.lapply_apply,DFinsupp.single_eq_of_ne (Ne.symm same)]
  exact DFunLike.congr_fun h f

theorem homCoproductSum_injective : Function.Injective (homCoproductSum R P family) := by
  intro f g h
  apply DFinsupp.ext
  intro i
  rw [← homCoproductSum_projection R P family i f,
    ← homCoproductSum_projection R P family i g,h]

/-- The target modules may be arbitrary: only the source is compact. -/
theorem homCoproductSum_surjective (compact : CoproductCompact.{u,v,w} P) :
    Function.Surjective (homCoproductSum R P family) := by
  intro f
  obtain ⟨s,supported⟩ := (coproductCompact_iff_projector.mp compact) I family f
  refine ⟨∑ i ∈ s, DFinsupp.single i (f ≫ coproductCoordinate family i),?_⟩
  rw [map_sum]
  simp only [homCoproductSum_single,Category.assoc]
  rw [← Preadditive.comp_sum,← finiteCoproductProjector_eq_sum,supported]

/-- The actual scalar-linear isomorphism from all finitely supported
Hom coefficients to maps into the entire coproduct. -/
def homCoproductLinearEquiv (compact : CoproductCompact.{u,v,w} P) :
    (Π₀ i : I, P ⟶ family i) ≃ₗ[R] (P ⟶ ∐ family) :=
  LinearEquiv.ofBijective (homCoproductSum R P family)
    ⟨homCoproductSum_injective R P family,homCoproductSum_surjective R P family compact⟩

/-- Precomposition is retained literally in the full character sum. -/
theorem homCoproductSum_precomp {Q : C} (a : Q ⟶ P)
    (f : Π₀ i : I, P ⟶ family i) :
    a ≫ homCoproductSum R P family f =
      homCoproductSum R Q family
        (DFinsupp.mapRange.linearMap (fun i => Linear.leftComp R (family i) a) f) := by
  have h : (Linear.leftComp R (∐ family) a).comp (homCoproductSum R P family) =
      (homCoproductSum R Q family).comp
        (DFinsupp.mapRange.linearMap (fun i => Linear.leftComp R (family i) a)) := by
    apply DFinsupp.lhom_ext
    intro i g
    change a ≫ homCoproductSum R P family (DFinsupp.single i g) =
      homCoproductSum R Q family
        (DFinsupp.mapRange.linearMap (fun i => Linear.leftComp R (family i) a)
          (DFinsupp.single i g))
    rw [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single,
      homCoproductSum_single,homCoproductSum_single]
    exact (Category.assoc a g (Sigma.ι family i)).symm
  exact DFunLike.congr_fun h f

/-- Every map of the complete target family is retained literally. -/
theorem homCoproductSum_postcomp (other : I → C) (a : ∀ i, family i ⟶ other i)
    (f : Π₀ i : I, P ⟶ family i) :
    homCoproductSum R P family f ≫ Limits.Sigma.map a =
      homCoproductSum R P other
        (DFinsupp.mapRange.linearMap (fun i => Linear.rightComp R P (a i)) f) := by
  have h : (Linear.rightComp R P (Limits.Sigma.map a)).comp (homCoproductSum R P family) =
      (homCoproductSum R P other).comp
        (DFinsupp.mapRange.linearMap (fun i => Linear.rightComp R P (a i))) := by
    apply DFinsupp.lhom_ext
    intro i g
    change homCoproductSum R P family (DFinsupp.single i g) ≫ Limits.Sigma.map a =
      homCoproductSum R P other
        (DFinsupp.mapRange.linearMap (fun i => Linear.rightComp R P (a i))
          (DFinsupp.single i g))
    rw [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single,
      homCoproductSum_single,homCoproductSum_single,Category.assoc,Sigma.ι_map]
    change g ≫ a i ≫ Sigma.ι other i = (g ≫ a i) ≫ Sigma.ι other i
    exact (Category.assoc _ _ _).symm
  exact DFunLike.congr_fun h f

end ToricPower.CompactExtraction

end
