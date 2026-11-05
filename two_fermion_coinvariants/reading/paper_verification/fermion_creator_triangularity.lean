module

public import PaperVerification.FermionCreators
public import PaperVerification.FermionTriangularExterior

/-!
# The suffix creators have the claimed triangular coefficients

This file connects the generic exterior-minor calculation to the actual
suffix polynomials and the two creator families. The diagonal factors are
`βᵢ aᵢ ∏_{j>i}(φᵢ-φⱼ)` and `bᵢ ∏_{j>i}(φᵢ-φⱼ)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- Numerical ordering places all theta modes before all xi modes. -/
def modeRank : Fin n ⊕ Fin n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val

theorem modeRank_injective : Function.Injective (modeRank (n := n)) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Fin.ext h)
      | inr j => simp only [modeRank] at h; omega
  | inr i =>
      cases j with
      | inl j => simp only [modeRank] at h; omega
      | inr j =>
          apply congrArg Sum.inr
          apply Fin.ext
          simpa only [modeRank, Nat.add_left_cancel_iff] using h

local instance FermionCreatorTriangularity_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

variable (b : Module.Basis (Fin n ⊕ Fin n) R V) (φ β a c : Fin n → R)

def prefixCreatorVector : Fin n ⊕ Fin n → V
  | .inl j => thetaCreatorVector b φ β a (suffixPolynomial φ j)
  | .inr j => xiCreatorVector b φ c (suffixPolynomial φ j)

/-- A single linear transformation packages all suffix creator vectors. -/
def prefixCreatorMap : V →ₗ[R] V := b.constr R (prefixCreatorVector b φ β a c)

@[simp]
theorem prefixCreatorMap_basis (j : Fin n ⊕ Fin n) :
    prefixCreatorMap b φ β a c (b j) = prefixCreatorVector b φ β a c j :=
  b.constr_basis R _ j

/-- The ordinary diagonal coefficient attached to each exterior mark. -/
def prefixCreatorDiagonal : Fin n ⊕ Fin n → R
  | .inl j => β j * a j * ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (φ j - φ i)
  | .inr j => c j * ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (φ j - φ i)

theorem prefixCreatorMap_diagonal (j : Fin n ⊕ Fin n) :
    b.repr (prefixCreatorMap b φ β a c (b j)) j = prefixCreatorDiagonal φ β a c j := by
  rw [prefixCreatorMap_basis]
  cases j with
  | inl j =>
      change b.coord (.inl j) (thetaCreatorVector b φ β a (suffixPolynomial φ j)) = _
      rw [coord_thetaCreatorVector_left, suffixPolynomial_eval_at]
      rfl
  | inr j =>
      change b.coord (.inr j) (xiCreatorVector b φ c (suffixPolynomial φ j)) = _
      rw [coord_xiCreatorVector_right, suffixPolynomial_eval_at]
      rfl

/-- Suffix evaluation enforces literal support at indices no greater than the
index at which a mark is being created. -/
theorem prefixCreatorMap_triangular (i j : Fin n ⊕ Fin n)
    (hij : modeRank j < modeRank i) :
    b.repr (prefixCreatorMap b φ β a c (b j)) i = 0 := by
  rw [prefixCreatorMap_basis]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change b.coord (.inl i) (thetaCreatorVector b φ β a (suffixPolynomial φ j)) = 0
          rw [coord_thetaCreatorVector_left,
            suffixPolynomial_eval_above φ j i (by exact hij), mul_zero]
      | inr j =>
          exact coord_xiCreatorVector_left b φ c (suffixPolynomial φ j) i
  | inr i =>
      cases j with
      | inl j =>
          exact coord_thetaCreatorVector_right b φ β a (suffixPolynomial φ j) i
      | inr j =>
          change b.coord (.inr i) (xiCreatorVector b φ c (suffixPolynomial φ j)) = 0
          rw [coord_xiCreatorVector_right,
            suffixPolynomial_eval_above φ j i (by simpa only [Fin.lt_iff_val_lt_val, modeRank, Nat.add_lt_add_iff_left] using hij),
            mul_zero]

/-- The creator wedge indexed by `t`, represented in the actual exterior power. -/
def prefixCreatorWedge (k : ℕ) (t : Set.powersetCard (Fin n ⊕ Fin n) k) : ⋀[R]^k V :=
  exteriorPower.map k (prefixCreatorMap b φ β a c) (b.exteriorPower k t)

/-- A created wedge has no other coefficient at the same or a larger rank sum. -/
theorem prefixCreatorWedge_coordinate_zero
    (k : ℕ) (s t : Set.powersetCard (Fin n ⊕ Fin n) k) (hst : s ≠ t)
    (hweight : exteriorIndexWeight modeRank t ≤ exteriorIndexWeight modeRank s) :
    (b.exteriorPower k).repr (prefixCreatorWedge b φ β a c k t) s = 0 :=
  exterior_map_coordinate_zero b (prefixCreatorMap b φ β a c) modeRank modeRank_injective
    (prefixCreatorMap_triangular b φ β a c) k s t hst hweight

/-- Formula (15), before splitting the product into its two color supports. -/
theorem prefixCreatorWedge_coordinate_self
    (k : ℕ) (t : Set.powersetCard (Fin n ⊕ Fin n) k) :
    (b.exteriorPower k).repr (prefixCreatorWedge b φ β a c k t) t =
      ∏ i : Fin k, prefixCreatorDiagonal φ β a c
        (Set.powersetCard.ofFinEmbEquiv.symm t i) := by
  rw [prefixCreatorWedge, exterior_map_coordinate_self b _ modeRank modeRank_injective
    (prefixCreatorMap_triangular b φ β a c)]
  apply Finset.prod_congr rfl
  intro i _
  exact prefixCreatorMap_diagonal b φ β a c _

/-- An ordered product of suffix-created generators is harmonic. -/
theorem prefixCreator_product_isHarmonic
    (h : ∀ k, moment φ (fun i ↦ β i * a i * c i) k = 0)
    (L : List (Fin n ⊕ Fin n)) :
    IsHarmonic b φ β a c
      ((L.map fun j ↦ ExteriorAlgebra.ι R (prefixCreatorVector b φ β a c j)).prod) := by
  induction L with
  | nil => exact isHarmonic_one b φ β a c
  | cons j L ih =>
      cases j with
      | inl j =>
          exact thetaCreator_preserves_harmonics b φ β a c h (suffixPolynomial φ j) _ ih
      | inr j =>
          exact xiCreator_preserves_harmonics b φ β a c h (suffixPolynomial φ j) _ ih

/-- The literal exterior-power creator vectors satisfy every harmonic equation. -/
theorem prefixCreatorWedge_isHarmonic
    (h : ∀ k, moment φ (fun i ↦ β i * a i * c i) k = 0)
    (k : ℕ) (t : Set.powersetCard (Fin n ⊕ Fin n) k) :
    IsHarmonic b φ β a c (prefixCreatorWedge b φ β a c k t : ExteriorAlgebra R V) := by
  have hproduct := prefixCreator_product_isHarmonic b φ β a c h
    (List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm t))
  simpa only [prefixCreatorWedge, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family_apply_coe,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    List.map_ofFn, Function.comp_def, prefixCreatorMap_basis] using hproduct

end PaperVerification.Fermion.Exterior
