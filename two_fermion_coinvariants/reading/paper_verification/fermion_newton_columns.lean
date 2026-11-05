module

public import PaperVerification.FermionNewtonDeletion
public import PaperVerification.FermionNewtonContraction
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The literal Newton columns and their polynomial contractions

The active interval is defined by the first strict multiplicity increase,
exactly as in equation (7). The columns live in the fraction field of the
actual polynomial ring. Their weighted sums are proved to be the explicit
polynomials obtained by monic division, rather than supplied as separate
contraction data. This module does not assume the Newton determinant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def earlierPositive (σ : Fin n → ℤ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j < i ∧ σ j = 1

def earlierNegative (σ : Fin n → ℤ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j < i ∧ σ j = -1

/-- The interval `[i,b_i)`, expressed without an artificial sentinel index. -/
def activeInterval (δ : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k ↦ i ≤ k ∧ ∀ j, i < j → j ≤ k → δ j ≤ δ i

@[simp] theorem mem_earlierPositive (σ : Fin n → ℤ) (i j : Fin n) :
    j ∈ earlierPositive σ i ↔ j < i ∧ σ j = 1 := by
  simp [earlierPositive]

@[simp] theorem mem_earlierNegative (σ : Fin n → ℤ) (i j : Fin n) :
    j ∈ earlierNegative σ i ↔ j < i ∧ σ j = -1 := by
  simp [earlierNegative]

@[simp] theorem earlierPositive_zero (σ : Fin (n + 1) → ℤ) : earlierPositive σ 0 = ∅ := by
  ext j
  simp [earlierPositive]

@[simp] theorem earlierNegative_zero (σ : Fin (n + 1) → ℤ) : earlierNegative σ 0 = ∅ := by
  ext j
  simp [earlierNegative]

@[simp] theorem mem_activeInterval (δ : Fin n → ℕ) (i k : Fin n) :
    k ∈ activeInterval δ i ↔ i ≤ k ∧ ∀ j, i < j → j ≤ k → δ j ≤ δ i := by
  simp [activeInterval]

theorem self_mem_activeInterval (δ : Fin n → ℕ) (i : Fin n) :
    i ∈ activeInterval δ i := by
  refine (mem_activeInterval δ i i).mpr ⟨le_rfl, ?_⟩
  intro j hij hji
  exact False.elim ((not_lt_of_ge hji) hij)

theorem activeInterval_nonempty (δ : Fin n → ℕ) (i : Fin n) :
    (activeInterval δ i).Nonempty := ⟨i, self_mem_activeInterval δ i⟩

theorem activeInterval_multiplicity_le (δ : Fin n → ℕ) (i k : Fin n)
    (hk : k ∈ activeInterval δ i) : δ k ≤ δ i := by
  rcases (mem_activeInterval δ i k).mp hk with ⟨hik, hδ⟩
  rcases eq_or_lt_of_le hik with h | h
  · subst k; exact le_rfl
  · exact hδ k h le_rfl

theorem activeInterval_disjoint_earlierNegative
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) :
    Disjoint (activeInterval δ i) (earlierNegative σ i) := by
  apply Finset.disjoint_left.mpr
  intro k hk hn
  exact (not_lt_of_ge ((mem_activeInterval δ i k).mp hk).1)
    ((mem_earlierNegative σ i k).mp hn).1

/-- The compatibility condition prevents a positive edge from leaving an
active interval, the exact combinatorial fact used in the tangency proof. -/
theorem activeInterval_closed_positive
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (h : Compatible δ σ)
    (i a b : Fin n) (ha : a ∈ activeInterval δ i) (hab : a < b)
    (hσ : σ a = 1) : b ∈ activeInterval δ i := by
  rcases (mem_activeInterval δ i a).mp ha with ⟨hia, hδ⟩
  refine (mem_activeInterval δ i b).mpr ⟨hia.trans (le_of_lt hab), ?_⟩
  intro j hij hjb
  by_cases hja : j ≤ a
  · exact hδ j hij hja
  · exact (h.1 a j (lt_of_not_ge hja) hσ).trans
      (activeInterval_multiplicity_le δ i a ha)

theorem earlierNegative_multiplicity_le
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (h : Compatible δ σ)
    (i k : Fin n) (hk : k ∈ earlierNegative σ i) : δ k ≤ δ i := by
  rcases (mem_earlierNegative σ i k).mp hk with ⟨hki, hσ⟩
  exact h.2 k i hki hσ

def columnNumerator (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) :
    Polynomial (P (F := F) (n := n)) :=
  Polynomial.X ^ δ i * ∏ j ∈ earlierPositive σ i,
    (Polynomial.X - Polynomial.C (MvPolynomial.X j))

def columnDenominator (σ : Fin n → ℤ) (i : Fin n) :
    Polynomial (P (F := F) (n := n)) :=
  ∏ j ∈ earlierNegative σ i, (Polynomial.X - Polynomial.C (MvPolynomial.X j))

def columnPolynomialPart (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) :
    Polynomial (P (F := F) (n := n)) := columnNumerator δ σ i /ₘ columnDenominator σ i

def columnContraction (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (i : Fin n) : P (F := F) (n := n) :=
  ∑ k ∈ activeInterval δ i,
    MvPolynomial.C (β k) * (columnPolynomialPart δ σ i).eval (MvPolynomial.X k)

theorem columnNumerator_monic (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) :
    (columnNumerator (F := F) δ σ i).Monic := by
  apply (Polynomial.monic_X.pow (δ i)).mul
  exact Polynomial.monic_prod_of_monic _ _ fun j hj ↦ Polynomial.monic_X_sub_C _

theorem columnDenominator_monic (σ : Fin n → ℤ) (i : Fin n) :
    (columnDenominator (F := F) σ i).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ fun j hj ↦ Polynomial.monic_X_sub_C _

theorem columnNumerator_natDegree (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) :
    (columnNumerator (F := F) δ σ i).natDegree = δ i + (earlierPositive σ i).card := by
  rw [columnNumerator, Polynomial.natDegree_mul
    (Polynomial.monic_X.pow (δ i)).ne_zero
    (Polynomial.monic_prod_of_monic _ _ fun j hj ↦ Polynomial.monic_X_sub_C _).ne_zero]
  rw [Polynomial.natDegree_prod_of_monic _ _ fun j hj ↦ Polynomial.monic_X_sub_C _]
  simp only [Polynomial.natDegree_X_pow,
    Polynomial.natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem columnDenominator_natDegree (σ : Fin n → ℤ) (i : Fin n) :
    (columnDenominator (F := F) σ i).natDegree = (earlierNegative σ i).card := by
  unfold columnDenominator
  rw [Polynomial.natDegree_prod_of_monic _ _ fun j hj ↦ Polynomial.monic_X_sub_C _]
  simp

/-- A zero height yields the literal constant polynomial one, including
profiles with both positive and negative earlier signs. -/
theorem columnPolynomialPart_eq_one_of_zero_height
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hzero : δ i + (earlierPositive σ i).card = (earlierNegative σ i).card) :
    columnPolynomialPart (F := F) δ σ i = 1 := by
  have hdegree : (columnDenominator (F := F) σ i).degree ≤
      (columnNumerator (F := F) δ σ i).degree := by
    rw [Polynomial.degree_eq_natDegree (columnDenominator_monic σ i).ne_zero,
      Polynomial.degree_eq_natDegree (columnNumerator_monic δ σ i).ne_zero,
      columnNumerator_natDegree, columnDenominator_natDegree, hzero]
  have hmonic : (columnPolynomialPart (F := F) δ σ i).Monic := by
    change (columnNumerator δ σ i /ₘ columnDenominator σ i).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_divByMonic_of_monic (columnDenominator_monic σ i) hdegree]
    exact (columnNumerator_monic δ σ i)
  apply hmonic.natDegree_eq_zero.mp
  rw [columnPolynomialPart, Polynomial.natDegree_divByMonic _ (columnDenominator_monic σ i),
    columnNumerator_natDegree, columnDenominator_natDegree, hzero, Nat.sub_self]

theorem columnContraction_zero_height
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hzero : δ i + (earlierPositive σ i).card = (earlierNegative σ i).card) :
    columnContraction β δ σ i = MvPolynomial.C (∑ k ∈ activeInterval δ i, β k) := by
  simp only [columnContraction, columnPolynomialPart_eq_one_of_zero_height δ σ i hzero,
    Polynomial.eval_one, mul_one, map_sum]

theorem columnContraction_isUnit_of_zero_height
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ k ∈ U, β k))
    (hzero : δ i + (earlierPositive σ i).card = (earlierNegative σ i).card) :
    IsUnit (columnContraction β δ σ i) := by
  rw [columnContraction_zero_height β δ σ i hzero]
  exact (hβ _ (activeInterval_nonempty δ i)).map MvPolynomial.C

abbrev RationalFunctions := FractionRing (P (F := F) (n := n))

def rationalNode (i : Fin n) : RationalFunctions (F := F) (n := n) :=
  algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (MvPolynomial.X i)

theorem rationalNode_injective : Function.Injective (rationalNode (F := F) (n := n)) := by
  intro i j h
  apply MvPolynomial.X_injective (R := F)
  exact IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) h

/-- Equation (7), with its exact interval and its forced negative residues. -/
def newtonColumn (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (i k : Fin n) : RationalFunctions (F := F) (n := n) :=
  rationalColumn
    ((columnNumerator (F := F) δ σ i).map
      (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))))
    (earlierNegative σ i) (activeInterval δ i) rationalNode
    (fun j ↦ algebraMap F (RationalFunctions (F := F) (n := n)) (β j)) k

theorem map_columnDenominator (σ : Fin n → ℤ) (i : Fin n) :
    (columnDenominator (F := F) σ i).map
        (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))) =
      Lagrange.nodal (earlierNegative σ i) (rationalNode (F := F)) := by
  simp only [columnDenominator, Lagrange.nodal, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, rationalNode]

/-- The weighted contraction of the literal rational column is exactly the
literal polynomial constructed above. -/
theorem newtonColumn_weighted_sum
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hβ : ∀ j, β j ≠ 0) :
    (∑ k, algebraMap F (RationalFunctions (F := F) (n := n)) (β k) * newtonColumn β δ σ i k) =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (columnContraction β δ σ i) := by
  have hcross : ∀ k ∈ activeInterval δ i, ∀ j ∈ earlierNegative σ i,
      rationalNode (F := F) k ≠ rationalNode j := by
    intro k hk j hj heq
    have he := rationalNode_injective heq
    subst j
    exact Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) hk hj
  have hunit : ∀ j ∈ earlierNegative σ i,
      algebraMap F (RationalFunctions (F := F) (n := n)) (β j) ≠ 0 := by
    intro j hj
    exact (map_ne_zero (algebraMap F (RationalFunctions (F := F) (n := n)))).mpr (hβ j)
  rw [show (∑ k, algebraMap F (RationalFunctions (F := F) (n := n)) (β k) * newtonColumn β δ σ i k) =
      ∑ k, algebraMap F (RationalFunctions (F := F) (n := n)) (β k) *
        rationalColumn _ (earlierNegative σ i) (activeInterval δ i) rationalNode
          (fun j ↦ algebraMap F (RationalFunctions (F := F) (n := n)) (β j)) k by rfl]
  rw [rationalColumn_weighted_sum _ _ _ _ _
    (activeInterval_disjoint_earlierNegative δ σ i) rationalNode_injective.injOn hcross hunit,
    ← map_columnDenominator, ← Polynomial.map_divByMonic _ (columnDenominator_monic σ i)]
  simp only [columnContraction, map_sum, map_mul, columnPolynomialPart,
    rationalNode, Polynomial.eval_map_apply,
    ← MvPolynomial.algebraMap_eq,
    IsScalarTower.algebraMap_apply F (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))]

end PaperVerification.Fermion.Newton
