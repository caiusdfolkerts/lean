import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Weight
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
/-! # Finite exponent families and their genuine monomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Exponent (V : Type*) := V →₀ ℕ
abbrev Family (V : Type*) := Finset (Exponent V)

def Equigenerated (B : Family V) (d : ℕ) : Prop := ∀ a ∈ B, a.degree = d

def Antichain (B : Family V) : Prop := ∀ a ∈ B, ∀ b ∈ B, a ≤ b → a = b

def Contains (B : Family V) (a : Exponent V) : Prop := ∃ b ∈ B, b ≤ a

def exchange (a : Exponent V) (i j : V) : Exponent V :=
  a - Finsupp.single i 1 + Finsupp.single j 1

def ExchangeAxiom (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ i, b i < a i →
    ∃ j, a j < b j ∧ exchange a i j ∈ B

def IsPolymatroidal (B : Family V) : Prop :=
  (∃ d, Equigenerated B d) ∧ ExchangeAxiom B

def monomialIdeal (k : Type*) [CommSemiring k] (B : Family V) :
    Ideal (MvPolynomial V k) :=
  Ideal.span ((fun a : Exponent V => MvPolynomial.monomial a (1 : k)) '' (B : Set (Exponent V)))

theorem mem_monomialIdeal_iff {k : Type*} [CommSemiring k] (B : Family V)
    (f : MvPolynomial V k) :
    f ∈ monomialIdeal k B ↔ ∀ a ∈ f.support, Contains B a := by
  exact MvPolynomial.mem_ideal_span_monomial_image

theorem monomial_mem_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    (B : Family V) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ monomialIdeal k B ↔ Contains B a := by
  rw [mem_monomialIdeal_iff]
  simp

theorem degree_mono {a b : Exponent V} (h : a ≤ b) : a.degree ≤ b.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum (fun i _ => h i)

theorem eq_of_le_of_degree_eq {a b : Exponent V} (h : a ≤ b)
    (hd : a.degree = b.degree) : a = b := by
  ext i
  have hs : ∑ j, a j = ∑ j, b j := by
    simpa only [Finsupp.degree_eq_sum] using hd
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => h j)).mp hs i (Finset.mem_univ i)

theorem Equigenerated.antichain {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    Antichain B := by
  intro a ha b hb hab
  exact eq_of_le_of_degree_eq hab ((hB a ha).trans (hB b hb).symm)

theorem Equigenerated.mem_iff_contains {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) {a : Exponent V} (ha : a.degree = d) :
    a ∈ B ↔ Contains B a := by
  constructor
  · intro h
    exact ⟨a, h, le_rfl⟩
  · rintro ⟨b, hb, hba⟩
    exact eq_of_le_of_degree_eq hba ((hB b hb).trans ha.symm) ▸ hb

@[simp] theorem exchange_apply (a : Exponent V) (i j h : V) :
    exchange a i j h = a h - (if h = i then 1 else 0) + (if h = j then 1 else 0) := by
  simp [exchange, Finsupp.single_apply, eq_comm]

theorem exchange_degree (a : Exponent V) (i j : V) (hi : 0 < a i) :
    (exchange a i j).degree = a.degree := by
  have hle : Finsupp.single i 1 ≤ a := by
    intro h
    by_cases hh : h = i
    · subst h
      simpa using (show 1 ≤ a i by omega)
    · simp [Finsupp.single_apply, hh, Ne.symm hh]
  have he : exchange a i j + Finsupp.single i 1 = a + Finsupp.single j 1 := by
    unfold exchange
    rw [add_right_comm, tsub_add_cancel_of_le hle]
  have hd := congrArg Finsupp.degree he
  simp only [map_add, Finsupp.degree_single] at hd
  omega

theorem exchange_ne {a : Exponent V} {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    exchange a i j ≠ a := by
  intro h
  have he := congrArg (fun b : Exponent V => b i) h
  simp [hij] at he
  omega

theorem exchange_inverse {a : Exponent V} {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    exchange (exchange a i j) j i = a := by
  ext h
  simp only [exchange_apply]
  by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all <;> omega

theorem exists_surplus {a b : Exponent V} (hdeg : a.degree = b.degree)
    {i : V} (hi : b i < a i) : ∃ j, a j < b j := by
  by_contra h
  push_neg at h
  have hab : b ≤ a := h
  have heq := eq_of_le_of_degree_eq hab hdeg.symm
  rw [heq] at hi
  exact (lt_irrefl _ hi)

def subsetSum (a : Exponent V) (U : Finset V) : ℕ := ∑ i ∈ U, a i

@[simp] theorem subsetSum_empty (a : Exponent V) : subsetSum a ∅ = 0 := by
  simp [subsetSum]

@[simp] theorem subsetSum_univ (a : Exponent V) : subsetSum a Finset.univ = a.degree := by
  simp [subsetSum, Finsupp.degree_eq_sum]

theorem subsetSum_mono (a : Exponent V) {U W : Finset V} (h : U ⊆ W) :
    subsetSum a U ≤ subsetSum a W :=
  Finset.sum_le_sum_of_subset h

theorem subsetSum_union_inter (a : Exponent V) (U W : Finset V) :
    subsetSum a U + subsetSum a W = subsetSum a (U ∪ W) + subsetSum a (U ∩ W) := by
  exact (Finset.sum_union_inter (s₁ := U) (s₂ := W) (f := fun i => a i)).symm

end CommAlg.Polymatroid
end
