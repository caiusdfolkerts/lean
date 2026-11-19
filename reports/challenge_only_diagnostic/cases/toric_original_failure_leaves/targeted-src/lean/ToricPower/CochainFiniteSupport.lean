module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Finite support in actual Hom cochains

If either complex is zero outside a finite set, the corresponding
product defining a Hom cochain reduces to a finite product. The other
complex may be completely unbounded. Objects outside the chosen set
are required only to be zero objects, rather than definitionally zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v r t
variable (R : Type r) [CommRing R]

def piRestrictZeroOutside {I : Type t} (M : I → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (support : Finset I) (outside : ∀ i, i ∉ support → Subsingleton (M i)) :
    (∀ i, M i) ≃ₗ[R] ∀ i : support, M i := by
  classical
  exact
    { toFun := fun f i => f i
      invFun := fun f i => if h : i ∈ support then f ⟨i, h⟩ else 0
      left_inv := by
        intro f
        funext i
        by_cases h : i ∈ support
        · simp only [dif_pos h]
        · simp only [dif_neg h]
          exact (outside i h).elim _ _
      right_inv := by
        intro f
        funext i
        simp only [dif_pos i.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear R A]

def cochainTargetValues (E J : CochainComplex A ℤ) (n : ℤ) :
    Cochain E J n ≃ₗ[R] ∀ q : ℤ, E.X (q - n) ⟶ J.X q where
  toFun f q := f.v (q - n) q (by omega)
  invFun f := Cochain.mk fun p q h =>
    eqToHom (congrArg E.X (show p = q - n by omega)) ≫ f q
  left_inv f := by
    apply Cochain.ext
    intro p q h
    have equal : p = q - n := by omega
    subst p
    simp only [Cochain.mk_v, eqToHom_refl, Category.id_comp]
  right_inv f := by
    funext q
    simp only [Cochain.mk_v, eqToHom_refl, Category.id_comp]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def cochainSourceValues (J E : CochainComplex A ℤ) (n : ℤ) :
    Cochain J E n ≃ₗ[R] ∀ q : ℤ, J.X q ⟶ E.X (q + n) where
  toFun f q := f.v q (q + n) rfl
  invFun f := Cochain.mk fun p q h => f p ≫ eqToHom (congrArg E.X h)
  left_inv f := by
    apply Cochain.ext
    intro p q h
    subst q
    simp only [Cochain.mk_v, eqToHom_refl, Category.comp_id]
  right_inv f := by
    funext q
    simp only [Cochain.mk_v, eqToHom_refl, Category.comp_id]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def cochainFiniteTargetValues (E J : CochainComplex A ℤ) (n : ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q)) :
    Cochain E J n ≃ₗ[R] ∀ q : support, E.X (q.val - n) ⟶ J.X q :=
  (cochainTargetValues R E J n).trans
    (piRestrictZeroOutside R _ support
      (fun q h => ⟨fun _ _ => (outside q h).eq_of_tgt _ _⟩))

def cochainFiniteSourceValues (J E : CochainComplex A ℤ) (n : ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q)) :
    Cochain J E n ≃ₗ[R] ∀ q : support, J.X q ⟶ E.X (q.val + n) :=
  (cochainSourceValues R J E n).trans
    (piRestrictZeroOutside R _ support
      (fun q h => ⟨fun _ _ => (outside q h).eq_of_src _ _⟩))

theorem cochainFiniteTargetValues_apply (E J : CochainComplex A ℤ) (n : ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (f : Cochain E J n) (q : support) :
    cochainFiniteTargetValues R E J n support outside f q =
      f.v (q.val - n) q.val (by omega) := rfl

theorem cochainFiniteSourceValues_apply (J E : CochainComplex A ℤ) (n : ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (f : Cochain J E n) (q : support) :
    cochainFiniteSourceValues R J E n support outside f q =
      f.v q.val (q.val + n) rfl := rfl

end ToricPower.SerrePairing

end
