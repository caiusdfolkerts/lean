module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Restricting a Serre pairing to retracts

The dual remains on the Hom space with compact source. The other object
may have arbitrary dimension. Naturality for the chosen idempotent is
the exact condition needed to restrict the pairing.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe v u w
variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

def precompLinear {X Y Z : C} (a : X ⟶ Y) :
    (Y ⟶ Z) →ₗ[k] (X ⟶ Z) where
  toFun f := a ≫ f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def postcompLinear {X Y Z : C} (b : Y ⟶ Z) :
    (X ⟶ Y) →ₗ[k] (X ⟶ Z) where
  toFun f := f ≫ b
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

structure CodomainPairing (T : C ⥤ C) (J : C) where
  equiv : ∀ E : C, (E ⟶ J) ≃ₗ[k] Module.Dual k (T.obj J ⟶ E)
  naturality : ∀ {E E' : C} (a : E ⟶ E') (f : E' ⟶ J) (g : T.obj J ⟶ E),
    equiv E (a ≫ f) g = equiv E' f (g ≫ a)

def Compatible {T : C ⥤ C} {J K : C}
    (left : CodomainPairing k T J) (right : CodomainPairing k T K)
    (a : J ⟶ K) : Prop :=
  ∀ (E : C) (f : E ⟶ J) (g : T.obj K ⟶ E),
    right.equiv E (f ≫ a) g = left.equiv E f (T.map a ≫ g)

variable {k}
variable {T : C ⥤ C} {F J : C}
variable (pairing : CodomainPairing k T J)
variable (i : F ⟶ J) (p : J ⟶ F) (split : i ≫ p = 𝟙 F)
variable (compatible : Compatible k pairing pairing (p ≫ i))

def retractEquiv (E : C) :
    (E ⟶ F) ≃ₗ[k] Module.Dual k (T.obj F ⟶ E) where
  toLinearMap :=
    (precompLinear k (T.map p)).dualMap.comp
      ((pairing.equiv E).toLinearMap.comp (postcompLinear k i))
  invFun φ :=
    (pairing.equiv E).symm ((precompLinear k (T.map i)).dualMap φ) ≫ p
  left_inv f := by
    have equation :
        (precompLinear k (T.map i)).dualMap
          ((precompLinear k (T.map p)).dualMap
            (pairing.equiv E (f ≫ i))) =
        pairing.equiv E (f ≫ i) := by
      apply LinearMap.ext
      intro g
      change pairing.equiv E (f ≫ i) (T.map p ≫ (T.map i ≫ g)) =
        pairing.equiv E (f ≫ i) g
      calc
        pairing.equiv E (f ≫ i) (T.map p ≫ (T.map i ≫ g)) =
            pairing.equiv E (f ≫ i) (T.map (p ≫ i) ≫ g) := by
          rw [CategoryTheory.Functor.map_comp, Category.assoc]
        _ = pairing.equiv E ((f ≫ i) ≫ (p ≫ i)) g :=
          (compatible E (f ≫ i) g).symm
        _ = pairing.equiv E (f ≫ i) g := by
          have retractEquation : (f ≫ i) ≫ (p ≫ i) = f ≫ i := by
            calc
              (f ≫ i) ≫ (p ≫ i) = f ≫ ((i ≫ p) ≫ i) := by
                simp only [Category.assoc]
              _ = f ≫ i := by rw [split, Category.id_comp]
          rw [retractEquation]
    change (pairing.equiv E).symm
      ((precompLinear k (T.map i)).dualMap
        ((precompLinear k (T.map p)).dualMap
          (pairing.equiv E (f ≫ i)))) ≫ p = f
    rw [equation, LinearEquiv.symm_apply_apply, Category.assoc, split, Category.comp_id]
  right_inv φ := by
    have mappedSplit : T.map i ≫ T.map p = 𝟙 (T.obj F) := by
      rw [← CategoryTheory.Functor.map_comp, split, CategoryTheory.Functor.map_id]
    let h := (pairing.equiv E).symm ((precompLinear k (T.map i)).dualMap φ)
    apply LinearMap.ext
    intro g
    change pairing.equiv E ((h ≫ p) ≫ i) (T.map p ≫ g) = φ g
    calc
      pairing.equiv E ((h ≫ p) ≫ i) (T.map p ≫ g) =
          pairing.equiv E (h ≫ (p ≫ i)) (T.map p ≫ g) := by
        rw [Category.assoc]
      _ = pairing.equiv E h (T.map (p ≫ i) ≫ (T.map p ≫ g)) :=
        compatible E h (T.map p ≫ g)
      _ = pairing.equiv E h (T.map p ≫ g) := by
        have retractEquation : T.map i ≫ (T.map p ≫ g) = g := by
          rw [← Category.assoc, mappedSplit, Category.id_comp]
        rw [CategoryTheory.Functor.map_comp, Category.assoc, retractEquation]
      _ = φ (T.map i ≫ (T.map p ≫ g)) := by
        change pairing.equiv E
          ((pairing.equiv E).symm ((precompLinear k (T.map i)).dualMap φ))
          (T.map p ≫ g) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      _ = φ g := by
        rw [← Category.assoc, mappedSplit, Category.id_comp]

@[simp]
theorem retractEquiv_apply (E : C) (f : E ⟶ F) (g : T.obj F ⟶ E) :
    retractEquiv pairing i p split compatible E f g =
      pairing.equiv E (f ≫ i) (T.map p ≫ g) := rfl

def retract : CodomainPairing k T F where
  equiv := retractEquiv pairing i p split compatible
  naturality {E E'} a f g := by
    change pairing.equiv E ((a ≫ f) ≫ i) (T.map p ≫ g) =
      pairing.equiv E' (f ≫ i) (T.map p ≫ (g ≫ a))
    rw [Category.assoc, pairing.naturality]
    rw [Category.assoc]

theorem retract_compatible
    {G K : C} (other : CodomainPairing k T K)
    (j : G ⟶ K) (q : K ⟶ G) (otherSplit : j ≫ q = 𝟙 G)
    (otherCompatible : Compatible k other other (q ≫ j))
    (a : F ⟶ G)
    (matrixCompatible : Compatible k pairing other (p ≫ a ≫ j)) :
    Compatible k (retract pairing i p split compatible)
      (retract other j q otherSplit otherCompatible) a := by
  intro E f g
  change other.equiv E ((f ≫ a) ≫ j) (T.map q ≫ g) =
    pairing.equiv E (f ≫ i) (T.map p ≫ (T.map a ≫ g))
  calc
    other.equiv E ((f ≫ a) ≫ j) (T.map q ≫ g) =
        other.equiv E ((f ≫ i) ≫ (p ≫ a ≫ j)) (T.map q ≫ g) := by
      have retractEquation : (f ≫ i) ≫ (p ≫ a ≫ j) = (f ≫ a) ≫ j := by
        calc
          (f ≫ i) ≫ (p ≫ a ≫ j) = f ≫ ((i ≫ p) ≫ (a ≫ j)) := by
            simp only [Category.assoc]
          _ = (f ≫ a) ≫ j := by
            rw [split, Category.id_comp, Category.assoc]
      rw [retractEquation]
    _ = pairing.equiv E (f ≫ i) (T.map (p ≫ a ≫ j) ≫ (T.map q ≫ g)) :=
      matrixCompatible E (f ≫ i) (T.map q ≫ g)
    _ = pairing.equiv E (f ≫ i) (T.map p ≫ (T.map a ≫ g)) := by
      have mappedOtherSplit : T.map j ≫ T.map q = 𝟙 (T.obj G) := by
        rw [← CategoryTheory.Functor.map_comp, otherSplit, CategoryTheory.Functor.map_id]
      have retractEquation : T.map j ≫ (T.map q ≫ g) = g := by
        rw [← Category.assoc, mappedOtherSplit, Category.id_comp]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [retractEquation]

end ToricPower.SerrePairing

end

