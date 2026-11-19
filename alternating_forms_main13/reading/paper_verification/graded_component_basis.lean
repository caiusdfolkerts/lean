module

public import TauCeti.Algebra.Module.GradedModule.Polynomial
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.Tactic.Abel

/-!
# Homogeneous component bases and polynomial towers

A homogeneous basis restricts to a basis of each actual graded component.
A basis over `K[X]` gives the expected coefficient-field basis of all its
polynomial towers, retaining every degree and every tower exponent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Module Polynomial

namespace PaperVerification.GradedComponentBasis

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {D : Type} [DecidableEq D]

def projection (G : TauCeti.InternalGrading K V D) (p : D) : V →ₗ[K] V where
  toFun x := (DirectSum.decompose G.piece x p : V)
  map_add' x y := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  map_smul' c x := by
    simp only [DirectSum.decompose_smul, DirectSum.smul_apply,
      Submodule.coe_smul, RingHom.id_apply]

theorem projection_of_mem (G : TauCeti.InternalGrading K V D) (p : D)
    (x : V) (hx : x ∈ G.piece p) : projection G p x = x :=
  DirectSum.decompose_of_mem_same G.piece hx

theorem projection_of_mem_ne (G : TauCeti.InternalGrading K V D) (p q : D)
    (x : V) (hx : x ∈ G.piece q) (hqp : q ≠ p) : projection G p x = 0 :=
  DirectSum.decompose_of_mem_ne G.piece hx hqp

theorem span_homogeneous_basis_piece
    (G : TauCeti.InternalGrading K V D) (B : Basis I K V) (degree : I → D)
    (hhom : ∀ i, B i ∈ G.piece (degree i)) (p : D) :
    Submodule.span K (Set.range (fun i : {i // degree i = p} => B i)) =
      G.piece p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change B i.val ∈ G.piece p
    simpa only [i.property] using hhom i.val
  · intro x hx
    let S := Submodule.span K (Set.range (fun i : {i // degree i = p} => B i))
    have hprojection : ∀ y ∈ Submodule.span K (Set.range B), projection G p y ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        by_cases hi : degree i = p
        · have hmem : B i ∈ G.piece p := by simpa only [hi] using hhom i
          rw [projection_of_mem G p _ hmem]
          exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
        · rw [projection_of_mem_ne G p _ _ (hhom i) hi]
          exact S.zero_mem
      | zero => simpa only [map_zero] using S.zero_mem
      | add y z hy hz ihy ihz =>
        simpa only [map_add] using S.add_mem ihy ihz
      | smul c y hy ih =>
        simpa only [map_smul] using S.smul_mem c ih
    have hp := hprojection x (B.mem_span x)
    rwa [projection_of_mem G p x hx] at hp

def componentBasis (G : TauCeti.InternalGrading K V D) (B : Basis I K V)
    (degree : I → D) (hhom : ∀ i, B i ∈ G.piece (degree i)) (p : D) :
    Basis {i // degree i = p} K (G.piece p) :=
  (Basis.span (B.linearIndependent.comp
    (fun i : {i // degree i = p} => (i : I)) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (span_homogeneous_basis_piece G B degree hhom p))

theorem finrank_piece (G : TauCeti.InternalGrading K V D) (B : Basis I K V)
    (degree : I → D) (hhom : ∀ i, B i ∈ G.piece (degree i)) (p : D) :
    Module.finrank K (G.piece p) = Nat.card {i // degree i = p} :=
  Module.finrank_eq_nat_card_basis (componentBasis G B degree hhom p)

section PolynomialTowers

variable [Module K[X] V] [IsScalarTower K K[X] V]

def towerBasis (B : Basis I K[X] V) : Basis (ℕ × I) K V :=
  (Polynomial.basisMonomials K).smulTower B

theorem towerBasis_apply (B : Basis I K[X] V) (a : ℕ × I) :
    towerBasis B a = (X ^ a.1 : K[X]) • B a.2 := by
  rw [towerBasis, Basis.smulTower_apply, Polynomial.coe_basisMonomials]
  change (Polynomial.monomial a.1 (1 : K)) • B a.2 = _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul]

theorem towerBasis_homogeneous
    (G : TauCeti.InternalGrading K V) (B : Basis I K[X] V)
    (degree : I → ℤ) (d : ℕ)
    (hhom : ∀ i, B i ∈ G.piece (degree i))
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : V⦄, x ∈ G.piece p →
      (X : K[X]) • x ∈ G.piece (p - d)) (a : ℕ × I) :
    towerBasis B a ∈ G.piece (degree a.2 - (a.1 : ℤ) * d) := by
  rw [towerBasis_apply]
  rcases a with ⟨j, i⟩
  induction j with
  | zero => simpa only [pow_zero, one_smul, Nat.cast_zero, zero_mul, sub_zero] using hhom i
  | succ j ih =>
    rw [pow_succ', mul_smul]
    convert hX ih using 1 <;>
      simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] <;> abel

theorem finrank_tower_piece
    (G : TauCeti.InternalGrading K V) (B : Basis I K[X] V)
    (degree : I → ℤ) (d : ℕ)
    (hhom : ∀ i, B i ∈ G.piece (degree i))
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : V⦄, x ∈ G.piece p →
      (X : K[X]) • x ∈ G.piece (p - d)) (p : ℤ) :
    Module.finrank K (G.piece p) =
      Nat.card {a : ℕ × I // degree a.2 - (a.1 : ℤ) * d = p} :=
  finrank_piece G (towerBasis B) _ (towerBasis_homogeneous G B degree d hhom hX) p

end PolynomialTowers
end PaperVerification.GradedComponentBasis
