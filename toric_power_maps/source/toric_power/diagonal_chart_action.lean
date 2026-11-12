module

public import ToricPower.DiagonalCellWeights
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Tactic.Abel

/-! # The actual affine-chart monomial action on diagonal cells

Multiplication by the monomial pair `(a,b)` changes total character `u`
to `u+a+b` and translates the actual cell by `a`. The two semigroup
conditions are precisely the regularity inequalities on the two affine
charts. The coordinate hyperplanes used to refine the arrangement impose
no extra section condition.

Candidate until ordinary checking of the complete source closure.
-/

@[expose] public noncomputable section

open Set
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

@[simp]
theorem rayPairing_zero (i : Fin s) : rayPairing A 0 i = 0 := by
  simp [rayPairing]

@[simp]
theorem rayPairing_add (a b : Fin n → ℤ) (i : Fin s) :
    rayPairing A (a+b) i = rayPairing A a i + rayPairing A b i := by
  simp [rayPairing, mul_add, Finset.sum_add_distrib]

/-- The actual character semigroup defined by a set of ray inequalities. -/
def rayCharacterMonoid (S : Set (Fin s)) : AddSubmonoid (Fin n → ℤ) where
  carrier := {a | ∀ i ∈ S, 0 ≤ rayPairing A a i}
  zero_mem' := by simp
  add_mem' ha hb i hi := by
    rw [rayPairing_add]
    exact add_nonneg (ha i hi) (hb i hi)

/-- A basis index is an actual character and a cell of its literal strip. -/
abbrev DiagonalChartCell (S T : Set (Fin s)) (d : ℕ) :=
  Σ u : Fin n → ℤ, {c : Cell (augmentedForms A) d // stripCellAllowed A S T u c}

theorem diagonalChartCell_ext {S T : Set (Fin s)} {d : ℕ}
    {x y : DiagonalChartCell A S T d} (weight : x.1 = y.1)
    (cell : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨u, c, hc⟩
  rcases y with ⟨v, b, hb⟩
  dsimp only at weight cell
  subst v
  subst b
  rfl

theorem stripCellAllowed_monomial_translate (S T : Set (Fin s))
    (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)
    (u : Fin n → ℤ) {d : ℕ} (c : Cell (augmentedForms A) d)
    (hc : stripCellAllowed A S T u c) :
    stripCellAllowed A S T (u+a.val+b.val) (translateCell A a.val c) := by
  apply (stripCellAllowed_translate_iff A S T _ a.val c).mpr
  constructor
  · intro i hi
    exact (hc.1 i hi).trans (a.property i hi)
  · intro i hi
    have hb := b.property i hi
    have hh := hc.2 i hi
    rw [rayPairing_sub, rayPairing_add, rayPairing_add]
    omega

/-- Multiplication by a regular monomial pair on the two affine factors. -/
def diagonalChartTranslate (S T : Set (Fin s))
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) {d : ℕ}
    (x : DiagonalChartCell A S T d) : DiagonalChartCell A S T d :=
  ⟨x.1+p.1.val+p.2.val, translateCell A p.1.val x.2.val,
    stripCellAllowed_monomial_translate A S T p.1 p.2 x.1 x.2.val x.2.property⟩

@[simp]
theorem diagonalChartTranslate_zero (S T : Set (Fin s)) {d : ℕ}
    (x : DiagonalChartCell A S T d) : diagonalChartTranslate A S T 0 x = x := by
  apply diagonalChartCell_ext A
  · change x.1 + (0 : Fin n → ℤ) + 0 = x.1
    simp
  · change translateCell A 0 x.2.val = x.2.val
    exact translateCell_zero A x.2.val

theorem diagonalChartTranslate_add (S T : Set (Fin s))
    (p q : rayCharacterMonoid A S × rayCharacterMonoid A T) {d : ℕ}
    (x : DiagonalChartCell A S T d) :
    diagonalChartTranslate A S T (p+q) x =
      diagonalChartTranslate A S T p (diagonalChartTranslate A S T q x) := by
  have hu : x.1 + (p.1.val+q.1.val) + (p.2.val+q.2.val) =
      x.1+q.1.val+q.2.val+p.1.val+p.2.val := by
    abel
  apply diagonalChartCell_ext A
  · exact hu
  · change translateCell A (p.1.val+q.1.val) x.2.val =
      translateCell A p.1.val (translateCell A q.1.val x.2.val)
    rw [translateCell_add, add_comm]

/-- In the monomial indexing of the line-bundle factors, this action has
exactly the exponents `(a+c,b+d)` from multiplication of monomials. -/
theorem diagonalMonomialAllowed_multiply (S T : Set (Fin s))
    (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)
    (u : Fin n → ℤ) {d : ℕ}
    (c : NormalizedCell A d) (v : Fin n → ℤ)
    (hv : diagonalMonomialAllowed A S T u (c,v)) :
    diagonalMonomialAllowed A S T (u+a.val+b.val) (c,v+a.val) := by
  dsimp only [diagonalMonomialAllowed] at hv ⊢
  constructor
  · intro i hi
    have ha := a.property i hi
    have hh := hv.1 i hi
    rw [rayPairing_add]
    omega
  · intro i hi
    have hb := b.property i hi
    have hh := hv.2 i hi
    rw [rayPairing_sub, rayPairing_add, rayPairing_add, rayPairing_add]
    rw [rayPairing_sub] at hh
    omega

end ToricPower.IntegralArrangement
