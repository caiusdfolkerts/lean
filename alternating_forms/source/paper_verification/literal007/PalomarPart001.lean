module

public import paper_verification.literal007.PalomarPart000
import all paper_verification.literal007.PalomarPart000
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import paper_verification.literal006
public import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import paper_verification.literal002
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import paper_verification.literal003
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import paper_verification.literal005
public import paper_verification.literal001
import Lean.Elab.Tactic.Omega
public import paper_verification.literal000
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import paper_verification.literal004
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.FieldSimp
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Sort

set_option Elab.async false

section TAF_LiteralSource_0452
/- Original module: TauCeti.Data.Finsupp.Multiset -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Multisets of exponent vectors

Mathlib's `Finsupp.toMultiset` sends an exponent vector `e : α →₀ ℕ` to the multiset in which
each `a` occurs `e a` times. Its cardinality is the total degree of `e`. This file also computes it
on exponent vectors built from unit steps `Finsupp.single a 1`: adding one unit step conses its
index, and a sum of unit steps along a finite family is the multiset of values of the family.

## Main results

* `Finsupp.card_toMultiset_eq_degree`: `card (toMultiset e) = e.degree`.
* `Finsupp.toMultiset_add_single_one`: `toMultiset (e + single a 1) = a ::ₘ toMultiset e`.
* `Finsupp.toMultiset_sum_single_one`: `toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p`.

The same unit steps summed along a list, with coefficients in any additive commutative monoid
with one, count the occurrences of each letter; in characteristic zero these counts determine a
constant list.

* `List.sum_map_single_one_apply`: `(l.map fun k ↦ single k 1).sum a = l.count a`.
* `List.eq_replicate_of_sum_map_single_one_eq`: a list whose letter counts are those of `m`
  copies of `i` is `m` copies of `i`.
-/

public section

namespace Finsupp

/-- The number of letters of the monomial with exponent vector `d` is its total degree. This is
not a `simp` lemma: `Finsupp.card_toMultiset` already rewrites the left-hand side to
`d.sum fun _ => id`, so tagging it would leave it out of simp-normal form. -/
theorem card_toMultiset_eq_degree {α : Type*} (d : α →₀ ℕ) :
    Multiset.card d.toMultiset = d.degree := by
  rw [card_toMultiset, degree_apply]
  rfl

/-- Adding one unit step at `a` to an exponent vector conses `a` onto its multiset. -/
theorem toMultiset_add_single_one {α : Type*} (e : α →₀ ℕ) (a : α) :
    toMultiset (e + single a 1) = a ::ₘ toMultiset e := by
  simp [toMultiset_add, add_comm]

/-- The multiset of a sum of unit steps along a family `p` indexed by a finset `s` is the
multiset of the values of `p` on `s`. -/
theorem toMultiset_sum_single_one {α ι : Type*} (s : Finset ι) (p : ι → α) :
    toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p := by
  simpa [toMultiset_sum, one_nsmul, Finset.sum_map_val] using
    Multiset.sum_map_singleton (s.val.map p)

end Finsupp

namespace List

variable {α R : Type*} [AddCommMonoidWithOne R]

/-- Summing the unit steps `single k 1` along a list counts the occurrences of each letter. -/
theorem sum_map_single_one_apply [DecidableEq α] (l : List α) (a : α) :
    (l.map fun k => Finsupp.single k (1 : R)).sum a = l.count a := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [map_cons, sum_cons, Finsupp.add_apply, ih, count_cons, Finsupp.single_apply]
    split_ifs <;> simp_all [add_comm]

/-- In characteristic zero, a list whose sum of unit steps is `m` times the unit step at `i` is
the list of `m` copies of `i`. -/
theorem eq_replicate_of_sum_map_single_one_eq [CharZero R] {l : List α} {i : α} {m : ℕ}
    (hl : (l.map fun k => Finsupp.single k (1 : R)).sum = Finsupp.single i (m : R)) :
    l = replicate m i := by
  classical
  have hcount : ∀ j, (l.count j : R) = Finsupp.single i (m : R) j := fun j => by
    rw [← hl, sum_map_single_one_apply]
  have hall : ∀ j ∈ l, j = i := by
    intro j hj
    by_contra hji
    have := hcount j
    rw [Finsupp.single_eq_of_ne hji, Nat.cast_eq_zero] at this
    exact (count_pos_iff.2 hj).ne' this
  have hi := hcount i
  rw [Finsupp.single_eq_same, Nat.cast_inj, count_eq_length.2 fun j hj => (hall j hj).symm] at hi
  exact eq_replicate_iff.2 ⟨hi, hall⟩

end List
end
end TAF_LiteralSource_0452

section TAF_LiteralSource_0453
/- Original module: TauCeti.Data.Finsupp.Order -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Decompositions of finitely supported functions on linear orders

A finitely supported function splits into its coordinates below a chosen index, its value at
that index, and its coordinates above it.

A natural-valued finitely supported function with an index below `l` in its support splits as
`single i 1 + g`, where `i < l` and every index in the support of `g` is at least `i`.
This decomposition supports induction on ordered monomials by removing one occurrence of
their least variable.
-/

public section

namespace Finsupp

variable {ι : Type*} [LinearOrder ι]

/-- A finitely supported function splits into its values before `i`, at `i`, and after `i`. -/
theorem filter_lt_add_single_add_filter_gt {M : Type*} [AddZeroClass M] (f : ι →₀ M) (i : ι) :
    f.filter (· < i) + single i (f i) + f.filter (i < ·) = f := by
  ext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne]
  · simp
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne']

/-- If the support of `f` is not bounded below by `l`, split off one occurrence of its least
index `i < l`. Every index in the remaining support is at least `i`. -/
theorem exists_eq_single_add_of_not_forall_le (f : ι →₀ ℕ) {l : ι}
    (h : ¬ ∀ i ∈ f.support, l ≤ i) :
    ∃ (i : ι) (g : ι →₀ ℕ), i < l ∧ (∀ j ∈ g.support, i ≤ j) ∧ f = single i 1 + g := by
  simp only [not_forall, not_le] at h
  obtain ⟨j, hj, hjl⟩ := h
  have hne : f.support.Nonempty := ⟨j, hj⟩
  let i := f.support.min' hne
  have hi : i ∈ f.support := f.support.min'_mem hne
  refine ⟨i, f - single i 1, (f.support.min'_le j hj).trans_lt hjl, fun k hk ↦ ?_, ?_⟩
  · exact f.support.min'_le k (support_tsub hk)
  · simpa only [add_comm] using (sub_add_single_one_cancel (mem_support_iff.1 hi)).symm

end Finsupp
end
end TAF_LiteralSource_0453

section TAF_LiteralSource_0454
/- Original module: TauCeti.Data.Finsupp.Weight -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Weights of finitely supported functions

If every variable occurring in a monomial `f : σ →₀ ℕ` has weight at most `c`, then the weight
of `f` is at most `degree f • c`. With `c = -1` over `ℤ`, this says that a monomial all of whose
variables have negative weight has weight at most minus its total degree, which is how
negatively graded variables bound the degree of elements of powers of the ideal of the
variables.

The weight of a multiset multiplicity function is the sum of the weights of its entries.

Weights also respect scaling of the weight vector and decompose into contributions before, at,
and after a chosen coordinate in a linear order. These identities support comparisons between
lexicographic order and weighted degree.

On a product `ι × κ` of blocks indexed by `ι`, the weight given by the indicator of block `b`
sums the coefficients in that block. For natural-valued exponents, this is the degree in block `b`.
More generally, for a block map `b : σ → τ`, the indicator weight of the fibre over `h` is the value
at `h` of the pushforward `Finsupp.mapDomain b`.

## Main results

* `Finsupp.weight_toFinsupp`: multiset multiplicities recover the sum of entry weights.
* `Finsupp.prod_pow_eq_pow_degree`: `∏ a ^ tᵢ = a ^ degree t`.
* `Finsupp.degree_optionElim`: extending by `y` at `none` adds `y` to the degree.
* `Finsupp.prod_pow_optionElim`, `Finsupp.sum_nsmul_optionElim`: extending by `n` at `none`
  splits off the factor `c none ^ n` from the weighted product `∏ c i ^ (f.optionElim n) i`, and
  the summand `n • c none` from the weighted sum.
* `Finsupp.pow_degree_le_pow_degree_optionElim`: `a ^ degree f ≤ b ^ degree (f.optionElim m)`
  for `0 ≤ a ≤ b` and `1 ≤ b`.
* `Finsupp.weight_le_degree_nsmul`: if `w s ≤ c` for all `s`, then `weight w f ≤ degree f • c`.
* `Finsupp.weight_le_degree_nsmul_of_mem_support`: the same bound, assuming `w s ≤ c` only for
  the variables `s` occurring in `f`.
* `Finsupp.weight_le_degree_nsmul_of_monotone`: for monotone weights `w`, if every variable
  occurring in `f` is at most `i`, then `weight w f ≤ degree f • w i`.
* `Finsupp.weight_filter_lt_add_smul_add_weight_filter_gt`: split a weight at a coordinate.
* `Finsupp.weight_smul_left`: scaling the weight vector scales the weight.
* `Finsupp.weight_ite_fst_eq_sum`: the indicator weight of a block sums its coefficients; for
  natural-valued exponents, this is the degree in that block.
* `Finsupp.weight_ite_eq_mapDomain_apply`: the indicator weight of a fibre of `b : σ → τ` is the
  corresponding value of `Finsupp.mapDomain b`.
* `Finsupp.weight_ite_sumElim_eq_add_mapDomain_apply`: for the block map `Sum.elim id b` on
  `τ ⊕ σ`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`.
* `Finsupp.natCast_weight_eq_of_support_subset`: on monomials supported in a finite set `s`, the
  weight `weight w` agrees with any additive functional on `s → ℤ` taking the value `w i` on the
  `i`-th coordinate vector.
* `Finsupp.finite_degree_eq`, `Finsupp.finite_degree_le`: in finitely many variables there are
  finitely many exponent vectors of each degree, and of degree at most `n`.
* `Finsupp.fintypeDegreeEq`: for a fintype of variables with decidable equality, the exponent
  vectors of degree `n` form a fintype, enumerated by `Finset.finsuppAntidiag`.
-/

public section

namespace Finsupp

/-- The weight of the multiplicity function of a multiset is the sum of its entry weights. -/
@[simp]
theorem weight_toFinsupp {σ M : Type*} [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (s : Multiset σ) :
    weight w s.toFinsupp = (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, map_add, weight_single]
    simpa using congrArg (w i + ·) ih

/-- A product of powers of one fixed element `a`, with exponents given by `t`, is `a` raised to
the degree of `t`. -/
theorem prod_pow_eq_pow_degree {σ M : Type*} [CommMonoid M] (t : σ →₀ ℕ) (a : M) :
    (t.prod fun _ n ↦ a ^ n) = a ^ t.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, degree_apply]

/-- Extending `f` to `Option σ` by the value `y` at `none` adds `y` to the degree. -/
@[simp]
theorem degree_optionElim {σ R : Type*} [AddCommMonoid R] (f : σ →₀ R) (y : R) :
    (f.optionElim y).degree = y + f.degree := by
  have h (g : Option σ →₀ R) : g.degree = g.sum fun _ e ↦ e := degree_apply g
  rw [h, sum_option_index _ _ (fun _ ↦ rfl) fun _ _ _ ↦ rfl, optionElim_apply_none,
    some_optionElim, degree_apply, Finsupp.sum]

/-- The weighted product of `f.optionElim n` splits off the factor `c none ^ n`. This is the
form of Mathlib's `Finsupp.prod_option_index` used to separate one variable from the monomial
weights of multivariate series. -/
@[to_additive /-- The weighted sum of `f.optionElim n` splits off the summand `n • c none`. -/]
theorem prod_pow_optionElim {α N : Type*} [CommMonoid N] (c : Option α → N) (n : ℕ)
    (f : α →₀ ℕ) :
    (f.optionElim n).prod (c · ^ ·) = c none ^ n * f.prod (fun i k ↦ c (Option.some i) ^ k) := by
  rw [prod_option_index _ _ (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _,
    optionElim_apply_none, some_optionElim]

/-- A power `a ^ degree f` is bounded by the power `b ^ degree (f.optionElim m)` of a larger
base `b ≥ 1`, for any value `m` at `none`. -/
theorem pow_degree_le_pow_degree_optionElim {σ R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 ≤ b) (f : σ →₀ ℕ) (m : ℕ) :
    a ^ f.degree ≤ b ^ (f.optionElim m).degree := by
  rw [degree_optionElim, pow_add]
  exact (pow_le_pow_left₀ ha hab _).trans (le_mul_of_one_le_left (pow_nonneg (ha.trans hab) _)
    (one_le_pow₀ hb))

end Finsupp

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- If every variable occurring in `f` has weight at most `c`, then the weight of `f` is at most
its degree times `c`. -/
theorem weight_le_degree_nsmul_of_mem_support (f : σ →₀ ℕ) {w : σ → M} {c : M}
    (hw : ∀ s ∈ f.support, w s ≤ c) : weight w f ≤ degree f • c := by
  rw [weight_apply, degree_apply, Finsupp.sum, ← Finset.sum_nsmul_assoc]
  gcongr with s hs
  exact hw s hs

/-- If every variable has weight at most `c`, then the weight of `f` is at most its degree times
`c`. -/
theorem weight_le_degree_nsmul (f : σ →₀ ℕ) {w : σ → M} {c : M} (hw : ∀ s, w s ≤ c) :
    weight w f ≤ degree f • c :=
  weight_le_degree_nsmul_of_mem_support f fun s _ ↦ hw s

/-- If the weights `w` are monotone and every variable occurring in `f` is at most `i`, then the
weight of `f` is at most its degree times `w i`. -/
theorem weight_le_degree_nsmul_of_monotone [Preorder σ] (f : σ →₀ ℕ) {w : σ → M}
    (hw : Monotone w) {i : σ} (hf : ∀ s ∈ f.support, s ≤ i) : weight w f ≤ degree f • w i :=
  weight_le_degree_nsmul_of_mem_support f fun s hs ↦ hw (hf s hs)

end Finsupp

namespace Finsupp

variable {σ M : Type*}

/-- The `c`-weight of a finitely supported function `w` splits into the weights before `i`, at
`i`, and after `i`. -/
theorem weight_filter_lt_add_smul_add_weight_filter_gt [LinearOrder σ] {R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (c : σ → M) (w : σ →₀ R) (i : σ) :
    weight c (w.filter (· < i)) + w i • c i + weight c (w.filter (i < ·)) = weight c w := by
  conv_rhs => rw [← filter_lt_add_single_add_filter_gt w i]
  rw [map_add, map_add, weight_single]

/-- Scaling the weight vector scales the weight. -/
theorem weight_smul_left {R S : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DistribSMul S M] [SMulCommClass R S M] (s : S) (c : σ → M) (w : σ →₀ R) :
    weight (s • c) w = s • weight c w := by
  simp only [weight_apply, smul_sum, Pi.smul_apply]
  exact sum_congr fun _ _ ↦ smul_comm _ s _

end Finsupp

namespace Finsupp

/-- The indicator weight of block `b` of a finitely supported function on `ι × κ` is the sum of
its coefficients in block `b`. -/
theorem weight_ite_fst_eq_sum {ι κ R : Type*} [Fintype κ] [DecidableEq ι] [Semiring R]
    (e : ι × κ →₀ R) (b : ι) :
    weight (fun p : ι × κ ↦ if p.1 = b then (1 : R) else 0) e = ∑ l, e (b, l) := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, Finsupp.add_apply, Finset.sum_add_distrib]
  | single p n =>
    obtain ⟨h, l⟩ := p
    by_cases hb : h = b
    · subst hb
      classical
      simp [Finsupp.weight_single, Finsupp.single_apply]
    · simp [Finsupp.weight_single, hb]

end Finsupp

namespace Finsupp

/-- The indicator weight of the fibre of `b` over `h` is the value at `h` of the pushforward of
`e` along `b`, that is, the sum of the coefficients of `e` at the indices lying over `h`. -/
theorem weight_ite_eq_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (e : σ →₀ R) (h : τ) :
    weight (fun j ↦ if b j = h then (1 : R) else 0) e = e.mapDomain b h := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, mapDomain_add, Finsupp.add_apply]
  | single j n => by_cases hj : b j = h <;> simp [weight_single, mapDomain_single, hj]

end Finsupp

namespace Finsupp

/-- On `τ ⊕ σ`, with the block map `Sum.elim id b` that puts the coordinate `.inl h` into block
`h`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`. -/
theorem weight_ite_sumElim_eq_add_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (a : τ →₀ R) (e : σ →₀ R) (h : τ) :
    weight (fun v ↦ if Sum.elim id b v = h then (1 : R) else 0) (a.sumElim e) =
      a h + e.mapDomain b h := by
  rw [weight_ite_eq_mapDomain_apply, sumElim_eq_add, mapDomain_add, ← mapDomain_comp,
    ← mapDomain_comp]
  simp

end Finsupp

namespace Finsupp

/-- If an additive functional `μ` on the integer vectors indexed by a finite set `s` takes the
value `w i` on the `i`-th coordinate vector, then `μ` agrees with the weight `weight w` on every
monomial supported in `s`. -/
theorem natCast_weight_eq_of_support_subset {σ : Type*} [DecidableEq σ] {s : Finset σ}
    (μ : (s → ℤ) →+ ℤ) {w : σ → ℕ} (hμ : ∀ i : s, μ (Pi.single i 1) = w i) {a : σ →₀ ℕ}
    (ha : a.support ⊆ s) : (weight w a : ℤ) = μ fun i ↦ (a i : ℤ) := by
  rw [weight_apply, Finsupp.sum_of_support_subset a ha _ (by simp), Nat.cast_sum,
    ← Finset.sum_coe_sort s]
  conv_rhs => rw [← Finset.univ_sum_single fun i : s ↦ (a i : ℤ)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (Pi.single i (a i : ℤ) : s → ℤ) = a i • Pi.single i 1 := by
    rw [← Pi.single_smul', Nat.smul_one_eq_cast]
  rw [hc, map_nsmul, hμ]
  simp

end Finsupp

namespace Finsupp

/-- In finitely many variables there are finitely many exponent vectors of each degree. -/
instance finite_degree_eq {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree = n} :=
  (finite_of_degree_eq n).to_subtype

/-- In finitely many variables there are finitely many exponent vectors of degree at most `n`. -/
instance finite_degree_le {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree ≤ n} :=
  (finite_of_degree_le n).to_subtype

/-- For a fintype of variables with decidable equality, the exponent vectors of degree `n` form a
fintype, enumerated by `Finset.finsuppAntidiag`. -/
instance fintypeDegreeEq {σ : Type*} [Fintype σ] [DecidableEq σ] (n : ℕ) :
    Fintype {s : σ →₀ ℕ // s.degree = n} :=
  Fintype.ofFinset (p := {s : σ →₀ ℕ | s.degree = n}) ((Finset.univ : Finset σ).finsuppAntidiag n)
    fun s ↦ by simp [Finset.mem_finsuppAntidiag, degree_eq_sum]

end Finsupp
end
end TAF_LiteralSource_0454

section TAF_LiteralSource_0455
/- Original module: TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The submodules of polynomials of bounded total degree

Mathlib's `MvPolynomial.restrictTotalDegree σ R m` is the submodule of polynomials of total degree
at most `m`. This file records that these submodules increase with `m`, that a monomial of degree
at most `m` lies in the `m`-th one, and that the `m`-th one is spanned by those monomials, so that
a linear statement about polynomials of bounded degree reduces to monomials. These monomials form
a basis whose coordinates are the coefficients, giving finite coordinates on tuples of
bounded-degree polynomials; evaluating such tuples is faithful over an infinite integral domain,
by Mathlib's `MvPolynomial.funext`. Raising the degree bound leaves the evaluation unchanged and
zero-pads the coordinates. As a spanning family, the monomials may be
replaced by products `∏ᵢ Sₖᵢ(Xᵢ)` of the members of a polynomial sequence `S` in the separate
variables, for instance the integer-valued binomial polynomials.

## Main results

* `MvPolynomial.restrictTotalDegree_mono`: the submodules increase with the degree bound.
* `MvPolynomial.monomial_mem_restrictTotalDegree`: a monomial of degree at most `m` has total
  degree at most `m`.
* `MvPolynomial.restrictTotalDegree_eq_span`: the monomials of degree at most `m` span the
  polynomials of total degree at most `m`.
* `MvPolynomial.basisRestrictTotalDegree`: the monomial basis of the polynomials of total degree
  at most `m`, whose coordinates are the coefficients.
* `MvPolynomial.boundedCoefficientEquiv`: monomial coefficients as finite coordinates on tuples of
  bounded-degree polynomials.
* `MvPolynomial.boundedEvaluation`, `MvPolynomial.boundedEvaluation_injective`: evaluation of such
  tuples as vector-valued functions is linear, and injective over an infinite integral domain.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp`: raising the degree bound extends the
  finite coefficient coordinates by zero.
* `MvPolynomial.span_prod_aeval_X_le`: products of a triangular family of one-variable polynomials
  in the separate variables lie in the span of the products of the original family.
* `Polynomial.Sequence.span_prod_aeval_X_eq_restrictTotalDegree`: the products `∏ᵢ Sₖᵢ(Xᵢ)` of
  a polynomial sequence with unit leading coefficients span the polynomials of bounded degree.
* `Module.Basis.apply_mem_of_monomial_degree_le`: a bilinear map takes values in a submodule on
  bounded-degree polynomials if it does so on basis vectors and bounded-degree monomials.
* `Module.Basis.constr_X_mul_mem_restrictTotalDegree`: multiplication by a linear form raises
  total degree by at most one.
-/

public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

variable (σ R) in
/-- The polynomials of total degree at most `m` increase with `m`. -/
theorem restrictTotalDegree_mono : Monotone (restrictTotalDegree σ R) :=
  fun _ _ h p hp ↦
    (mem_restrictTotalDegree σ _ p).2 (((mem_restrictTotalDegree σ _ p).1 hp).trans h)

/-- A monomial whose exponent has degree at most `m` has total degree at most `m`. -/
theorem monomial_mem_restrictTotalDegree {s : σ →₀ ℕ} {m : ℕ} (h : s.degree ≤ m) (r : R) :
    monomial s r ∈ restrictTotalDegree σ R m :=
  (mem_restrictTotalDegree σ m _).2 <| (totalDegree_monomial_le s r).trans <| by
    simpa [Finsupp.sum, Finsupp.degree_apply] using h

variable (σ R) in
/-- The polynomials of total degree at most `m` are those supported on exponents of degree at
most `m`. -/
theorem restrictTotalDegree_eq_restrictSupport (m : ℕ) :
    restrictTotalDegree σ R m = restrictSupport R {s : σ →₀ ℕ | s.degree ≤ m} := by
  have hs : {s : σ →₀ ℕ | (s.sum fun _ e ↦ e) ≤ m} = {s | s.degree ≤ m} := by
    ext s
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [restrictTotalDegree, hs]

variable (σ R) in
/-- The polynomials of total degree at most `m` are spanned by the monomials of degree at most
`m`. -/
theorem restrictTotalDegree_eq_span (m : ℕ) :
    restrictTotalDegree σ R m =
      Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ m}) := by
  rw [restrictTotalDegree_eq_restrictSupport, restrictSupport_eq_span]

variable (σ R) in
/-- The monomial basis of the polynomials of total degree at most `m`, indexed by exponents of
degree at most `m`. -/
noncomputable def basisRestrictTotalDegree (m : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree ≤ m} R (restrictTotalDegree σ R m) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm)

/-- The coordinate of a bounded-degree polynomial in the monomial basis is its coefficient. -/
@[simp]
theorem basisRestrictTotalDegree_repr_apply (m : ℕ) (p : restrictTotalDegree σ R m)
    (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m).repr p s = (p : MvPolynomial σ R).coeff s := (rfl)

/-- A monomial basis vector of the bounded-degree polynomials is the corresponding monomial. -/
@[simp]
theorem coe_basisRestrictTotalDegree (m : ℕ) (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m s : MvPolynomial σ R) = monomial s.1 1 := by
  classical
  have h : basisRestrictTotalDegree σ R m s =
      ⟨monomial s.1 1, monomial_mem_restrictTotalDegree s.2 1⟩ := by
    refine (basisRestrictTotalDegree σ R m).repr.injective (Finsupp.ext fun t ↦ ?_)
    simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  rw [h]

section Coordinates

variable {J : Type*}

variable (σ R J) in
/-- Monomial coefficients identify `J`-indexed tuples of polynomials of total degree at most `d`
with functions on the pairs of an index and an exponent of degree at most `d`. For finitely many
variables and indices this index type is finite, so these are finite coordinates. -/
noncomputable def boundedCoefficientEquiv [Finite σ] (d : ℕ) :
    (J → restrictTotalDegree σ R d) ≃ₗ[R] (J × {s : σ →₀ ℕ // s.degree ≤ d} → R) :=
  (LinearEquiv.piCongrRight fun _ => (basisRestrictTotalDegree σ R d).equivFun).trans
    (LinearEquiv.curry R R J {s : σ →₀ ℕ // s.degree ≤ d}).symm

/-- A finite coefficient coordinate is the corresponding monomial coefficient of an entry. -/
@[simp] theorem boundedCoefficientEquiv_apply [Finite σ] {d : ℕ}
    (v : J → restrictTotalDegree σ R d) (i : J × {s : σ →₀ ℕ // s.degree ≤ d}) :
    boundedCoefficientEquiv σ R J d v i = (v i.1 : MvPolynomial σ R).coeff i.2 := by
  simp [boundedCoefficientEquiv, Function.uncurry]

/-- The tuple with prescribed finite coefficient coordinates has those monomial coefficients. -/
@[simp] theorem coeff_boundedCoefficientEquiv_symm_apply [Finite σ] {d : ℕ}
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R) (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (((boundedCoefficientEquiv σ R J d).symm a j : restrictTotalDegree σ R d) :
      MvPolynomial σ R).coeff s = a (j, s) := by
  have h := boundedCoefficientEquiv_apply ((boundedCoefficientEquiv σ R J d).symm a) (j, s)
  rwa [LinearEquiv.apply_symm_apply, eq_comm] at h

variable (σ R J) in
/-- Evaluation of a tuple of bounded-degree polynomials as a vector-valued function on points.
It is linear in the tuple. -/
noncomputable def boundedEvaluation (d : ℕ) :
    (J → restrictTotalDegree σ R d) →ₗ[R] (σ → R) → J → R where
  toFun v x j := eval x (v j : MvPolynomial σ R)
  map_add' v w := by
    funext x j
    simp
  map_smul' a v := by
    funext x j
    simp

/-- Coordinate evaluation of a tuple of bounded-degree polynomials. -/
@[simp] theorem boundedEvaluation_apply {d : ℕ} (v : J → restrictTotalDegree σ R d)
    (x : σ → R) (j : J) :
    boundedEvaluation σ R J d v x j = eval x (v j : MvPolynomial σ R) := (rfl)

/-- Over an infinite integral domain, bounded-degree polynomial tuples are determined by the
functions they define: the evaluation map is faithful. -/
theorem boundedEvaluation_injective {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (d : ℕ) : Function.Injective (boundedEvaluation σ R J d) := fun _ _ h =>
  _root_.funext fun j => Subtype.ext <| MvPolynomial.funext fun x => congrFun (congrFun h x) j

/-- Raising the degree bound from `d` to `d'` does not change the function defined by a tuple of
bounded-degree polynomials. -/
@[simp] theorem boundedEvaluation_inclusion_comp {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedEvaluation σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      boundedEvaluation σ R J d v := (rfl)

/-- Raising the degree bound from `d` to `d'` zero-pads the finite coefficient coordinates: they
are extended by zero along the inclusion of index types, so the new coordinates at exponents of
degree above `d` vanish. -/
theorem boundedCoefficientEquiv_inclusion_comp [Finite σ] {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedCoefficientEquiv σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
            fun _ hs => hs.trans h))
        (boundedCoefficientEquiv σ R J d v) := by
  have hinj : Function.Injective (Prod.map (id : J → J)
      (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
        fun _ hs => hs.trans h)) :=
    Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective
  ext ⟨j, s, hs'⟩
  by_cases hs : s.degree ≤ d
  · convert (hinj.extend_apply (boundedCoefficientEquiv σ R J d v)
      (0 : J × {s : σ →₀ ℕ // s.degree ≤ d'} → R) (j, ⟨s, hs⟩)).symm using 1
    · simp
    · -- The index `(j, ⟨s, hs'⟩)` is the image of `(j, ⟨s, hs⟩)` by definition.
      rw [Function.ExtendByZero.linearMap_apply]
      rfl
  · rw [Function.ExtendByZero.linearMap_apply, Function.extend_apply' _ _ _ ?_, Pi.zero_apply,
      boundedCoefficientEquiv_apply, Function.comp_apply, Submodule.coe_inclusion]
    · refine coeff_eq_zero_of_totalDegree_lt ?_
      rw [← Finsupp.degree_apply]
      exact ((mem_restrictTotalDegree σ d _).1 (v j).2).trans_lt (not_le.1 hs)
    · rintro ⟨⟨j', s', hs''⟩, he⟩
      exact hs (by cases he; exact hs'')

end Coordinates

open Polynomial in
/-- If each `q k` with `k ≤ m` is a combination of the `p j` with `j ≤ k`, then the products
`∏ᵢ q_{τ i}(Xᵢ)` with `τ.degree ≤ m` lie in the span of the products `∏ᵢ p_{τ i}(Xᵢ)` with
`τ.degree ≤ m`. -/
theorem span_prod_aeval_X_le {σ R : Type*} [Fintype σ] [CommSemiring R] {p q : ℕ → R[X]} {m : ℕ}
    (h : ∀ k ≤ m, q k ∈ Submodule.span R (p '' Set.Iic k)) :
    Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i))) ''
        {τ | τ.degree ≤ m}) ≤
      Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (p (τ i))) ''
        {τ | τ.degree ≤ m}) := by
  classical
  rw [Submodule.span_le]
  rintro _ ⟨τ, hτ, rfl⟩
  -- Each factor lies in the span of the `p j (Xᵢ)` with `j ≤ τ i`.
  have hmem (i : σ) : Polynomial.aeval (X (R := R) i) (q (τ i)) ∈
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (h _ ((Finsupp.le_degree i τ).trans hτ))
  have hprod : ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i)) ∈ ∏ i,
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    induction (Finset.univ : Finset σ) using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact Submodule.one_le.1 le_rfl
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Submodule.mul_mem_mul (hmem i) ih
  rw [Submodule.prod_span] at hprod
  refine Submodule.span_mono ?_ hprod
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hx
  simp only [Finset.mem_univ, forall_const, Set.image_image] at hg
  choose j hj hgj using fun i ↦ @hg i
  refine ⟨Finsupp.equivFunOnFinite.symm j, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_le_sum fun i _ ↦ Set.mem_Iic.1 (hj i)).trans
      ((Finsupp.degree_eq_sum τ).symm.le.trans hτ)
  · simp [← hgj]

end MvPolynomial

namespace Polynomial.Sequence

open Submodule

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- **Change of basis to products of a polynomial sequence.** If the leading coefficients of
`S₀, …, Sₘ` are units, then the products `∏ᵢ S_{τ i}(Xᵢ)` over the exponents `τ` of degree at
most `m` span the polynomials of total degree at most `m`, exactly as the monomials `X^τ` do. -/
theorem span_prod_aeval_X_eq_restrictTotalDegree (S : Sequence R) {m : ℕ}
    (hS : ∀ k ≤ m, IsUnit (S k).leadingCoeff) :
    span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) (S (τ i))) ''
        {τ | τ.degree ≤ m}) = MvPolynomial.restrictTotalDegree σ R m := by
  classical
  have hmon : MvPolynomial.restrictTotalDegree σ R m =
      span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) ((X : R[X]) ^ (τ i))) ''
        {τ | τ.degree ≤ m}) := by
    rw [MvPolynomial.restrictTotalDegree_eq_span]
    congr! with τ
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  rw [hmon]
  refine le_antisymm (MvPolynomial.span_prod_aeval_X_le fun k _ ↦ ?_)
    (MvPolynomial.span_prod_aeval_X_le fun k hk ↦ ?_)
  · have : S k ∈ degreeLE R k := mem_degreeLE.2 (S.degree_eq k).le
    rwa [degreeLE_eq_span_X_pow, Finset.coe_image, Finset.coe_range,
      Set.Iio_add_one_eq_Iic] at this
  · rw [S.span_degreeLE fun i hi ↦ hS i (hi.trans hk), mem_degreeLE]
    exact degree_X_pow_le k

end Polynomial.Sequence

namespace Module.Basis

open MvPolynomial

section Bilinear

variable {σ κ R L M : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]
  [AddCommMonoid M] [Module R M]

/-- A bilinear map out of a module and a polynomial algebra takes values in a submodule on
polynomials of total degree at most `d` if it does so on basis vectors and monomials of degree at
most `d`. -/
theorem apply_mem_of_monomial_degree_le (b : Basis κ R L)
    (Φ : L →ₗ[R] MvPolynomial σ R →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : κ) (s : σ →₀ ℕ), s.degree ≤ d → Φ (b l) (monomial s 1) ∈ N)
    (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h l s hs
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

end Bilinear

variable {ι R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- Multiplying by the linear form attached to `x` in the basis `b` raises total degree by at
most one. -/
theorem constr_X_mul_mem_restrictTotalDegree (b : Basis ι R L) {d : ℕ} (x : L)
    {p : MvPolynomial ι R} (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  refine b.apply_mem_of_monomial_degree_le
    ((LinearMap.mul R _).comp (b.constr R X)) _ d (fun l σ hσ ↦ ?_) x hp
  have hm : (monomial (Finsupp.single l 1 + σ) 1 : MvPolynomial ι R) ∈
      restrictTotalDegree ι R (d + 1) :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  simpa [monomial_single_add] using hm

end Module.Basis
end
end TAF_LiteralSource_0455

section TAF_LiteralSource_0456
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.PolynomialRep -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The PBW representation of a Lie algebra on a polynomial algebra

Let `L` be a Lie algebra over a commutative ring `R`, free with a basis `b` indexed by a linearly
ordered type `ι`, and let `S = R[zᵢ | i ∈ ι]` be the polynomial algebra on the same index set.
This file constructs the representation of `L` on `S` that proves the linear-independence half
of the Poincaré--Birkhoff--Witt theorem: a Lie algebra homomorphism

`b.pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R S`

such that

* `bᵢ` acts on a monomial `z^σ` all of whose variables are at least `i` by multiplication by
  `zᵢ`;
* every `x : L` acts on a polynomial of total degree at most `d` as multiplication by the linear
  form `zₓ = ∑ᵢ (b.repr x i) zᵢ`, up to an error of total degree at most `d`.

Given a word `x₁ ⋯ xₙ` in `L`, the induced action of `U(L)` therefore sends `1` to `zₓ₁ ⋯ zₓₙ`
up to lower-degree terms, and sends an ordered monomial `bᵢ₁ ⋯ bᵢₙ` (`i₁ ≤ ⋯ ≤ iₙ`) to the monomial
`zᵢ₁ ⋯ zᵢₙ` exactly. This is what separates the graded pieces of the PBW filtration from each
other.

## The construction

The action of `bₗ` on a monomial `z^σ` is defined by induction on the degree of `σ`. If every
variable of `σ` is at least `l`, it is multiplication by `zₗ`. Otherwise `σ = eμ + τ` where `μ` is
the least variable of `σ` and `μ < l`, and the value is forced by the commutator relation that the
representation must satisfy:

`bₗ · z^σ = zμ zₗ z^τ + bμ · (bₗ · z^τ - zₗ z^τ) + ⁅bₗ, bμ⁆ · z^τ`,

where all actions on the right are on polynomials of degree less than that of `σ`. The induction
is carried out by iterating a single step on bilinear maps `L → S → S`; the iterates agree on
polynomials of degree at most `n` from the `n`-th one onwards, and their limit is the action.
Verifying that the result is a Lie algebra homomorphism is again an induction on degree, whose
only nontrivial case uses the Jacobi identity. The recursive construction and its degree estimates
use only a module with a bracket; the Lie identities enter when proving the representation law.

## Main definitions and results

* `Module.Basis.pbwPolynomialRep`: the representation.
* `Module.Basis.pbwPolynomialRep_basis_monomial_of_le`: the action of `bₗ` on a monomial in
  variables at least `l` is multiplication by `zₗ`.
* `Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`: up to terms of total degree at
  most `d`, the action on a polynomial of total degree at most `d` is multiplication by the
  corresponding linear form.
* `Module.Basis.pbwPolynomialRep_mem_restrictTotalDegree`: the action raises total degree by at
  most one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4,
  Lemma A, whose proof this file follows.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

open MvPolynomial

universe u v w

namespace Module.Basis

variable {R : Type u} {L : Type v} {ι : Type w}

local notation "S" => MvPolynomial ι R

local notation "S≤" => MvPolynomial.restrictTotalDegree ι R

attribute [local instance 100] LieRing.ofAssociativeRing

namespace PBWPolynomialRep

/-! ### Monomial bookkeeping -/

-- Keep the split-off variable first so Mathlib normalizes its monomial directly.
attribute [local simp] monomial_single_add

/-! ### Multiplication by the linear form -/

section Semiring

variable [CommSemiring R] [AddCommMonoid L] [Module R L] (b : Basis ι R L)

/-- Multiplication by the linear form `zₓ = b.constr R X x`. -/
private noncomputable def naive : L →ₗ[R] S →ₗ[R] S :=
  (LinearMap.mul R S).comp (b.constr R X)

private theorem naive_apply (x : L) (p : S) : naive b x p = b.constr R X x * p :=
  rfl

end Semiring

section DegreeBound

variable [CommRing R] [AddCommGroup L] [Module R L] (b : Basis ι R L)

/-- The degree estimate `g x p - zₓ p ∈ S≤ d` for `p ∈ S≤ d`, in every degree. -/
private def DegreeBound (g : L →ₗ[R] S →ₗ[R] S) : Prop :=
  ∀ (d : ℕ) (x : L) (p : S), p ∈ (S≤ d) → g x p - b.constr R X x * p ∈ S≤ d

private theorem DegreeBound.mem {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ} (x : L)
    {p : S} (hp : p ∈ S≤ d) : g x p ∈ S≤ (d + 1) := by
  have := Submodule.add_mem _ (restrictTotalDegree_mono ι R (Nat.le_succ d) (hg d x p hp))
    (b.constr_X_mul_mem_restrictTotalDegree x hp)
  rwa [sub_add_cancel] at this

end DegreeBound

variable [CommRing R] [LinearOrder ι]

/-! ### The inductive step -/

section Construction

variable [AddCommGroup L] [Module R L] (b : Basis ι R L) [Bracket L L]

/-- One step of the inductive construction: from an action `g`, valid in degrees below that of
`σ`, define the action of `bₗ` on `z^σ`. -/
private noncomputable def step (g : L →ₗ[R] S →ₗ[R] S) : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦
    if h : ∀ i ∈ σ.support, l ≤ i then X l * monomial σ 1
    else
      let μ := σ.support.min' (by
        push Not at h
        obtain ⟨i, hi, -⟩ := h
        exact ⟨i, hi⟩)
      let τ := σ - Finsupp.single μ 1
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1)

private theorem step_of_le (g : L →ₗ[R] S →ₗ[R] S) {l : ι} {σ : ι →₀ ℕ}
    (h : ∀ i ∈ σ.support, l ≤ i) : step b g (b l) (monomial σ 1) = X l * monomial σ 1 := by
  have hσ : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis, dite_eq_left_of_eq_true (eq_true h), hσ]

private theorem step_of_lt (g : L →ₗ[R] S →ₗ[R] S) {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    step b g (b l) (monomial (Finsupp.single μ 1 + τ) 1) =
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : μ ∈ (Finsupp.single μ 1 + τ).support := by simp
  have h : ¬ ∀ i ∈ (Finsupp.single μ 1 + τ).support, l ≤ i :=
    fun h ↦ (h μ hμ).not_gt hμl
  have hσ : (monomial (Finsupp.single μ 1 + τ) 1 : S) =
      basisMonomials ι R (Finsupp.single μ 1 + τ) := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis,
    dite_eq_right_of_eq_false (eq_false h)]
  have hmin : (Finsupp.single μ 1 + τ).support.min' ⟨μ, hμ⟩ = μ :=
    le_antisymm (Finset.min'_le _ _ hμ)
      (Finset.le_min' _ _ _ (by simpa [Finsupp.support_add_eq_union] using hμτ))
  simp only [hmin, add_tsub_cancel_left]

private theorem degreeBound_step {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) :
    DegreeBound b (step b g) := by
  intro d x p hp
  refine b.apply_mem_of_monomial_degree_le (step b g - naive b) _ d (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, naive_apply, Basis.constr_basis]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := σ.exists_eq_single_add_of_not_forall_le h
  have hτ : τ.degree + 1 ≤ d := by simpa [Nat.one_add] using hσ
  have hX : X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) - X l * (X μ * monomial τ 1) =
      g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) + g ⁅b l, b μ⁆ (monomial τ 1) := by
    ring
  rw [step_of_lt b g hμl hμτ]
  simp only [monomial_single_add, pow_one]
  rw [hX]
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  refine restrictTotalDegree_mono ι R hτ
    (Submodule.add_mem _ (DegreeBound.mem b hg _ ?_) (DegreeBound.mem b hg _ hτmem))
  have := hg _ (b l) _ hτmem
  rwa [Basis.constr_basis] at this

/-- `step` only looks one degree down: actions agreeing in degree at most `d` give the same next
step in degree at most `d + 1`. -/
private theorem step_congr {g g' : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ}
    (hgg' : ∀ (x : L) (p : S), p ∈ (S≤ d) → g x p = g' x p) (x : L) {p : S}
    (hp : p ∈ S≤ (d + 1)) : step b g x p = step b g' x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine b.apply_mem_of_monomial_degree_le (step b g - step b g') ⊥ (d + 1)
    (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, step_of_le b g' h]
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := σ.exists_eq_single_add_of_not_forall_le h
  have hτmem : (monomial τ 1 : S) ∈ S≤ d :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  have hq : g (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ d := by
    have := hg d (b l) _ hτmem
    rwa [Basis.constr_basis] at this
  rw [step_of_lt b g hμl hμτ, step_of_lt b g' hμl hμτ, hgg' _ _ hq, hgg' _ _ hτmem,
    hgg' _ _ hτmem]

/-- The iterates of `step`, starting from multiplication by the linear form. -/
private noncomputable def approx : ℕ → L →ₗ[R] S →ₗ[R] S
  | 0 => naive b
  | n + 1 => step b (approx n)

private theorem degreeBound_approx (n : ℕ) : DegreeBound b (approx b n) := by
  induction n with
  | zero =>
      intro d x p _
      rw [approx, naive_apply, sub_self]
      exact Submodule.zero_mem _
  | succ n ih => exact degreeBound_step b ih

private theorem approx_succ_eq (n : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + 1) x p = approx b n x p := by
  induction n generalizing x p with
  | zero =>
      rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
      refine b.apply_mem_of_monomial_degree_le (approx b 1 - approx b 0) ⊥ 0
        (fun l σ hσ ↦ ?_) x hp
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
      have hσ : σ = 0 := (Finsupp.degree_eq_zero_iff σ).1 (Nat.le_zero.1 hσ)
      subst hσ
      rw [approx, approx, step_of_le b _ (by simp), naive_apply, Basis.constr_basis]
  | succ n ih => exact step_congr b (degreeBound_approx b (n + 1)) ih x hp

private theorem approx_add_eq (n k : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + k) x p = approx b n x p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← add_assoc,
        approx_succ_eq b _ x (restrictTotalDegree_mono ι R (Nat.le_add_right n k) hp), ih]

/-! ### The limit action -/

/-- The limit of the iterates: on monomials of degree `n`, the `n`-th iterate. -/
private noncomputable def act : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦ approx b σ.degree (b l) (monomial σ 1)

private theorem act_eq_approx {d n : ℕ} (hdn : d ≤ n) (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p = approx b n x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine b.apply_mem_of_monomial_degree_le (act b - approx b n) ⊥ d (fun l σ hσ ↦ ?_) x hp
  have hσb : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero, act,
    Basis.constr_basis, hσb, Basis.constr_basis, ← hσb]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hσ.trans hdn)
  exact (approx_add_eq b _ k _ (monomial_mem_restrictTotalDegree le_rfl 1)).symm

private theorem act_sub_mem {d : ℕ} (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p - b.constr R X x * p ∈ S≤ d := by
  rw [act_eq_approx b le_rfl x hp]
  exact degreeBound_approx b d d x p hp

private theorem degreeBound_act : DegreeBound b (act b) :=
  fun _ x _ hp ↦ act_sub_mem b x hp

private theorem act_of_le {l : ι} {σ : ι →₀ ℕ} (h : ∀ i ∈ σ.support, l ≤ i) :
    act b (b l) (monomial σ 1) = X l * monomial σ 1 := by
  rw [act_eq_approx b (Nat.le_succ _) _ (monomial_mem_restrictTotalDegree le_rfl 1), approx,
    step_of_le b _ h]

private theorem act_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l) (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (monomial (Finsupp.single μ 1 + τ) 1) =
      X μ * X l * monomial τ 1 + act b (b μ) (act b (b l) (monomial τ 1) - X l * monomial τ 1) +
        act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  have hq : approx b τ.degree (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ τ.degree := by
    have := degreeBound_approx b τ.degree τ.degree (b l) _ hτmem
    rwa [Basis.constr_basis] at this
  rw [act_eq_approx b le_rfl _
      (monomial_mem_restrictTotalDegree (s := Finsupp.single μ 1 + τ) le_rfl 1), map_add,
    Finsupp.degree_single, add_comm 1 τ.degree, approx, step_of_lt b _ hμl hμτ,
    act_eq_approx b le_rfl _ hτmem,
    act_eq_approx b le_rfl _ hτmem, act_eq_approx b le_rfl _ hq]

/-- The defining case of the commutator relation: `μ < l` and `μ` is at most every variable
of `τ`. -/
private theorem act_comm_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (act b (b μ) (monomial τ 1)) =
      act b (b μ) (act b (b l) (monomial τ 1)) + act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : act b (b μ) (X l * monomial τ 1) = X μ * X l * monomial τ 1 := by
    have h := act_of_le b (l := μ) (σ := Finsupp.single l 1 + τ)
      (by simpa [Finsupp.support_add_eq_union] using And.intro hμl.le hμτ)
    simpa [mul_assoc] using h
  have h := act_of_lt b hμl hμτ
  simp only [monomial_single_add, pow_one] at h
  rw [act_of_le b hμτ, h, map_sub, hμ]
  abel

/-! ### The commutator relation -/

/-- The commutator relation for the action, in total degree at most `d`. -/
private def CommRel (d : ℕ) : Prop :=
  ∀ (x y : L) (p : S), p ∈ (S≤ d) → act b x (act b y p) = act b y (act b x p) + act b ⁅x, y⁆ p

/-- The expansion of `bₗ bₘ z^τ` when the least variable `ν` of `τ` is less than both `l` and `m`,
assuming the commutator relation one degree down. -/
private theorem act_act_eq_of_lt {l m ν : ι} {Ψ : ι →₀ ℕ} (hνl : ν < l) (hνm : ν < m)
    (hνΨ : ∀ i ∈ Ψ.support, ν ≤ i) (ih : CommRel b Ψ.degree) :
    act b (b l) (act b (b m) (monomial (Finsupp.single ν 1 + Ψ) 1)) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) +
        act b ⁅b m, b ν⁆ (act b (b l) (monomial Ψ 1)) +
        act b ⁅b l, ⁅b m, b ν⁆⁆ (monomial Ψ 1) := by
  have hΨ : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  -- `bₘ z^Ψ` is the monomial `zₘ z^Ψ` up to an error `w` of degree at most that of `Ψ`.
  set w := act b (b m) (monomial Ψ 1) - monomial (Finsupp.single m 1 + Ψ) 1 with hw
  have hwmem : w ∈ S≤ Ψ.degree := by
    rw [hw]
    simpa [Basis.constr_basis] using act_sub_mem b (b m) hΨ
  have hνΨm : ∀ i ∈ (Finsupp.single m 1 + Ψ).support, ν ≤ i :=
    by simpa [Finsupp.support_add_eq_union] using And.intro hνm.le hνΨ
  have hsplit : act b (b m) (monomial Ψ 1) = monomial (Finsupp.single m 1 + Ψ) 1 + w := by
    rw [hw, add_sub_cancel]
  -- The commutator relation for `bₗ` and `bν` on `bₘ z^Ψ`.
  have hlν : act b (b l) (act b (b ν) (act b (b m) (monomial Ψ 1))) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) := by
    rw [hsplit]
    simp only [map_add]
    rw [act_comm_of_lt b hνl hνΨm, ih _ _ _ hwmem]
    abel
  simp only [monomial_single_add, pow_one]
  rw [← act_of_le b hνΨ,
    ih (b m) (b ν) _ hΨ, map_add, hlν, ih (b l) ⁅b m, b ν⁆ _ hΨ]
  abel

end Construction

variable [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

/-- The defect `x ↦ y ↦ [act x, act y] - act ⁅x, y⁆`, as a bilinear map. -/
private noncomputable def defect : L →ₗ[R] L →ₗ[R] Module.End R S :=
  LinearMap.mk₂ R (fun x y ↦ act b x * act b y - act b y * act b x - act b ⁅x, y⁆)
    (fun x₁ x₂ y ↦ by simp only [map_add, add_lie, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, smul_lie, smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun x y₁ y₂ ↦ by simp only [map_add, lie_add, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, lie_smul, smul_mul_assoc, mul_smul_comm, smul_sub])

private theorem commRel_of_basis {d : ℕ}
    (h : ∀ (l m : ι) (τ : ι →₀ ℕ), τ.degree ≤ d →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1)) :
    CommRel b d := by
  have key : ∀ (l : ι) (y : L) (p : S), p ∈ (S≤ d) → defect b (b l) y p = 0 := by
    intro l y p hp
    rw [← Submodule.mem_bot R]
    refine b.apply_mem_of_monomial_degree_le (defect b (b l)) ⊥ d
      (fun m τ hτ ↦ ?_) y hp
    simp [defect, h l m τ hτ]
  intro x y p hp
  have hx : ((defect b).flip y).flip p = 0 := b.ext fun l ↦ by simpa using key l y p hp
  have := LinearMap.congr_fun hx x
  simp only [defect, LinearMap.flip_apply, LinearMap.mk₂_apply, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← sub_eq_zero, ← this]
  abel

/-- The commutator relation in total degree at most `d`, by strong induction on `d`. -/
private theorem commRel (d : ℕ) : CommRel b d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  refine commRel_of_basis b fun l m τ hτ ↦ ?_
  -- the hard case: the least variable `ν` of `τ` is less than both `l` and `m`
  have hard : ∀ {l m : ι}, (¬ ∀ i ∈ τ.support, m ≤ i) → m < l →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1) := by
    intro l m hm hml
    obtain ⟨ν, Ψ, hνm, hνΨ, rfl⟩ := τ.exists_eq_single_add_of_not_forall_le hm
    have hΨ : Ψ.degree < d := by simp at hτ; omega
    have hνl := hνm.trans hml
    have ihΨ := ih _ hΨ
    have hΨmem : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
    -- Expand both `bₗ bₘ z^τ` and `bₘ bₗ z^τ`; the cross terms `⁅bₗ, bν⁆ bₘ z^Ψ` and
    -- `⁅bₘ, bν⁆ bₗ z^Ψ` cancel. Writing `z^τ = bν z^Ψ`, the commutator relation one degree down
    -- turns the right-hand side into `bν ⁅bₗ, bₘ⁆ z^Ψ + ⁅⁅bₗ, bₘ⁆, bν⁆ z^Ψ`, and the Jacobi
    -- identity matches the remaining double brackets.
    rw [act_act_eq_of_lt b hνl hνm hνΨ ihΨ, act_act_eq_of_lt b hνm hνl hνΨ ihΨ,
      monomial_single_add, pow_one, ← act_of_le b hνΨ,
      ihΨ ⁅b l, b m⁆ (b ν) _ hΨmem,
      ihΨ (b l) (b m) _ hΨmem, map_add, leibniz_lie (b l) (b m) (b ν), map_add,
      LinearMap.add_apply]
    abel
  rcases lt_trichotomy m l with hml | rfl | hlm
  · by_cases hm : ∀ i ∈ τ.support, m ≤ i
    · exact act_comm_of_lt b hml hm
    · exact hard hm hml
  · rw [lie_self, map_zero, LinearMap.zero_apply, add_zero]
  · by_cases hl : ∀ i ∈ τ.support, l ≤ i
    · rw [act_comm_of_lt b hlm hl, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel
    · rw [hard hl hlm, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel

end PBWPolynomialRep

open PBWPolynomialRep

variable [CommRing R] [LinearOrder ι] [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

/-- **The PBW representation.** For a Lie algebra `L` with a basis `b` indexed by a linearly
ordered type `ι`, the representation of `L` on the polynomial algebra `R[zᵢ | i ∈ ι]` in which
`bₗ` acts on a monomial in variables at least `l` by multiplication by `zₗ`
(`Module.Basis.pbwPolynomialRep_basis_monomial_of_le`), and every element acts as multiplication
by its linear form up to lower-degree terms
(`Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`). -/
noncomputable def pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R (MvPolynomial ι R) where
  toLinearMap := act b
  map_lie' {x y} := by
    refine LinearMap.ext fun p ↦ ?_
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LieRing.of_associative_ring_bracket,
      LinearMap.sub_apply, Module.End.mul_apply,
      commRel b p.totalDegree x y p ((mem_restrictTotalDegree ι _ p).2 le_rfl)]
    abel

/-- A basis vector `bₗ` acts on a monomial with any coefficient, all of whose variables are at
least `l`, as multiplication by the variable `zₗ`. -/
@[simp↓]
theorem pbwPolynomialRep_basis_monomial_of_le {l : ι} {σ : ι →₀ ℕ} (r : R)
    (h : ∀ i ∈ σ.support, l ≤ i) :
    b.pbwPolynomialRep (b l) (monomial σ r) = X l * monomial σ r := by
  have hr : (monomial σ r : S) = r • monomial σ 1 := by simp [smul_monomial]
  have h1 : b.pbwPolynomialRep (b l) (monomial σ 1) = X l * monomial σ 1 :=
    act_of_le b h
  rw [hr, map_smul, h1, mul_smul_comm]

/-- On polynomials of total degree at most `d`, the action of `x` is multiplication by the linear
form `zₓ = b.constr R X x`, up to an error of total degree at most `d`. -/
theorem pbwPolynomialRep_sub_mul_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p - b.constr R X x * p ∈ restrictTotalDegree ι R d :=
  act_sub_mem b x hp

/-- The action raises total degree by at most one. -/
theorem pbwPolynomialRep_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p ∈ restrictTotalDegree ι R (d + 1) :=
  DegreeBound.mem b (degreeBound_act b) x hp

end Module.Basis
end
end TAF_LiteralSource_0456

section TAF_LiteralSource_0457
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic results on universal enveloping algebras

This file records general results about universal enveloping algebras that do not depend on
additional structures such as filtrations, bialgebras, or antipodes.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`: a universal enveloping algebra is
  generated, as an algebra, by its canonical Lie generators.
* `TauCeti.UniversalEnvelopingAlgebra.induction_ι`: the induction principle on the canonical Lie
  generators that the previous statement supplies.
* `TauCeti.UniversalEnvelopingAlgebra.instFiniteType`: a universal enveloping algebra is an algebra
  of finite type over the base ring as soon as the Lie algebra is finite as a module.
* `TauCeti.UniversalEnvelopingAlgebra.representation`: the algebra homomorphism `U(L) → End M`
  attached to a Lie module `M`, in particular the adjoint action of `U(L)` on `L` at `M = L`.
* `TauCeti.UniversalEnvelopingAlgebra.representation_lie_of_mem_center`: a central element of
  `U(L)` acts on a Lie module by a map commuting with the Lie action.
* `TauCeti.UniversalEnvelopingAlgebra.mem_center_iff_forall_lie_ι`: centrality in `U(L)` is
  detected on the canonical Lie generators alone.
* `TauCeti.UniversalEnvelopingAlgebra.ad_ι_pow_apply_ι`: iterating the commutator with a Lie
  generator reproduces, on the Lie generators, the iterated adjoint action of `L`.
* `TauCeti.UniversalEnvelopingAlgebra.lie_map_ι`: an algebra representation maps the bracket of
  canonical Lie generators to the bracket of their images.
* `TauCeti.UniversalEnvelopingAlgebra.lie_map_ι_eq_smul`: a Lie-bracket eigenvector remains one
  under an algebra representation.
* `TauCeti.UniversalEnvelopingAlgebra.mul_sub_mul_eq_map_ι_lie`: the image of a Lie bracket
  under an algebra homomorphism is the ring commutator of the images.
* `TauCeti.UniversalEnvelopingAlgebra.commute_of_lie_eq_zero`: images of Lie-commuting elements
  commute.
* `TauCeti.UniversalEnvelopingAlgebra.zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq`: a scaled
  Lie-bracket relation gives the corresponding scaled ring-commutator relation.
* `TauCeti.UniversalEnvelopingAlgebra.mul_eq_mul_add_zsmul_of_lie_eq`: an integral Lie-bracket
  structure constant gives the corresponding ring-commutator relation.
-/

public section

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The enveloping algebra is generated by the canonical Lie generators.** This is the `U(L)`
analogue of `TensorAlgebra.adjoin_range_ι`, obtained by pushing that statement along the surjective
quotient map `UniversalEnvelopingAlgebra.mkAlgHom R L`. -/
theorem adjoin_range_ι :
    _root_.Algebra.adjoin R (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R)) =
      (⊤ : Subalgebra R U) := by
  have hcomp : (⇑(_root_.UniversalEnvelopingAlgebra.ι R) : L → U) =
      ⇑(_root_.UniversalEnvelopingAlgebra.mkAlgHom R L) ∘ ⇑(TensorAlgebra.ι R) :=
    funext fun x => _root_.UniversalEnvelopingAlgebra.ι_apply R x
  rw [hcomp, Set.range_comp, ← AlgHom.map_adjoin, TensorAlgebra.adjoin_range_ι,
    _root_.Algebra.map_top]
  -- `mkAlgHom R L` is by definition the quotient map `RingCon.mkₐ R (ringCon R L)`.
  exact (AlgHom.range_eq_top _).2 (RingCon.mkₐ_surjective _)

/-- **Induction on the canonical Lie generators.** A property of elements of `U(L)` that holds for
the canonical Lie generators and the scalars, and is stable under sums and products, holds
everywhere, since those generate `U(L)` as an `R`-algebra. -/
@[elab_as_elim]
theorem induction_ι {p : U → Prop}
    (ι : ∀ x : L, p (_root_.UniversalEnvelopingAlgebra.ι R x))
    (algebraMap : ∀ r : R, p (_root_.Algebra.algebraMap R U r))
    (add : ∀ a b, p a → p b → p (a + b)) (mul : ∀ a b, p a → p b → p (a * b)) (u : U) : p u := by
  have hu : u ∈ _root_.Algebra.adjoin R (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R)) := by
    rw [adjoin_range_ι R L]; exact _root_.Algebra.mem_top
  induction hu using _root_.Algebra.adjoin_induction with
  | mem u hu => obtain ⟨x, rfl⟩ := hu; exact ι x
  | algebraMap r => exact algebraMap r
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

variable {R L} in
/-- **The enveloping algebra of a Lie algebra which is finite as a module is an `R`-algebra of
finite type**: a finite spanning set of `L` generates `U(L)` as an algebra, the canonical Lie
generators of `U(L)` generating it
(`TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`). -/
instance instFiniteType [Module.Finite R L] : Algebra.FiniteType R U := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := L)
  -- the span of the image of a spanning set of `L` is the whole of the image of `L`
  have hrange : ((Submodule.span R
      (⇑((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U) ''
        (S : Set L)) : Submodule R U) : Set U) =
      Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R (L := L)) := by
    rw [← Submodule.map_span, hS, ← LinearMap.range_eq_map, LinearMap.coe_range,
      LieHom.coe_toLinearMap]
  exact ⟨S.image ⇑((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U), by
    rw [Finset.coe_image, ← _root_.Algebra.adjoin_span, hrange, adjoin_range_ι R L]⟩

variable (M : Type w) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The representation of a universal enveloping algebra on a Lie module**: the algebra
homomorphism obtained from `LieModule.toEnd` by the universal property of `U(L)`. At `M = L` this
is the adjoint action, since `LieAlgebra.ad R L` is `LieModule.toEnd R L L`. -/
noncomputable def representation : U →ₐ[R] Module.End R M :=
  _root_.UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)

-- Neither this lemma nor its pointwise form below is a `simp` lemma: `simp` unfolds `ι` through
-- Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so a left-hand side mentioning `ι` is not in
-- simp-normal form. This is why Mathlib's own `lift_ι_apply` is not a `simp` lemma either;
-- `representation_ι'` is the corresponding simp-normal form.
/-- The representation acts on a canonical Lie generator by the Lie action. -/
theorem representation_ι (x : L) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) = LieModule.toEnd R L M x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The representation on the Lie algebra itself acts on a canonical generator by the adjoint
action. -/
theorem representation_ι_ad (x : L) :
    representation R L L (_root_.UniversalEnvelopingAlgebra.ι R x) = LieAlgebra.ad R L x :=
  representation_ι R L L x

/-- The `simp`-normal form of `TauCeti.UniversalEnvelopingAlgebra.representation_ι`, stated for
the canonical generators as `simp` writes them. -/
@[simp]
theorem representation_ι' (x : L) :
    representation R L M
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      LieModule.toEnd R L M x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply' R _ x

/-- The pointwise form of `TauCeti.UniversalEnvelopingAlgebra.representation_ι`: a Lie generator
acts by the Lie bracket. -/
theorem representation_ι_apply (x : L) (m : M) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  rw [representation_ι, LieModule.toEnd_apply_apply]

/-- **A central element of `U(L)` acts on a Lie module by a map commuting with the Lie action.**
Equivalently, `TauCeti.UniversalEnvelopingAlgebra.representation R L M u` is `L`-equivariant, that
is, a homomorphism of Lie modules. Centrality is used only against the canonical Lie generators,
which is what the Lie action is read off. -/
theorem representation_lie_of_mem_center {u : U} (hu : u ∈ Subalgebra.center R U) (x : L) (m : M) :
    representation R L M u ⁅x, m⁆ = ⁅x, representation R L M u m⁆ := by
  have h := congrArg (representation R L M)
    (Subalgebra.mem_center_iff.mp hu (_root_.UniversalEnvelopingAlgebra.ι R x))
  rw [map_mul, map_mul, representation_ι] at h
  have h₁ := congrArg (fun g : Module.End R M ↦ g m) h
  simpa only [Module.End.mul_apply, LieModule.toEnd_apply_apply] using h₁.symm

variable {R L}
variable {B : Type w} [Ring B] [Algebra R B]

/-- An algebra representation of the universal enveloping algebra maps the Lie bracket to the
commutator in its target algebra. -/
theorem lie_map_ι (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) (x y : L) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι R x), ρ (_root_.UniversalEnvelopingAlgebra.ι R y)⁆ =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) := by
  have hlie := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) x y
  rw [LieRing.of_associative_ring_bracket] at hlie
  rw [LieRing.of_associative_ring_bracket, hlie, map_sub, map_mul, map_mul]

/-- A Lie-bracket eigenvector remains one under an algebra representation of the universal
enveloping algebra. -/
theorem lie_map_ι_eq_smul (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {x y : L} {a : R}
    (hxy : ⁅x, y⁆ = a • y) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι R x), ρ (_root_.UniversalEnvelopingAlgebra.ι R y)⁆ =
      a • ρ (_root_.UniversalEnvelopingAlgebra.ι R y) := by
  rw [lie_map_ι ρ, hxy, map_smul, map_smul]

/-- The image of a Lie bracket under an algebra homomorphism from a universal enveloping algebra
is the ring commutator of the images. -/
theorem mul_sub_mul_eq_map_ι_lie
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) (a b : L) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι R a) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R b) -
        ρ (_root_.UniversalEnvelopingAlgebra.ι R b) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R a) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R ⁅a, b⁆) := by
  rw [LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) a b,
    LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul]

/-- Images of Lie-commuting elements commute under every algebra homomorphism from the universal
enveloping algebra. -/
theorem commute_of_lie_eq_zero
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b : L} (hab : ⁅a, b⁆ = 0) :
    Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι R a))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) := by
  have h := mul_sub_mul_eq_map_ι_lie ρ a b
  rw [hab, map_zero, map_zero] at h
  exact sub_eq_zero.mp h

/-- A scaled Lie-bracket relation becomes the corresponding scaled ring-commutator relation under
every algebra homomorphism from the universal enveloping algebra. -/
theorem zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b b' : L} {p q r : ℤ} {n : ℕ}
    (hab : (p * q) • ⁅a, b⁆ = ((n : ℤ) * r) • b') :
    (p • ρ (_root_.UniversalEnvelopingAlgebra.ι R a)) *
        (q • ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) =
      (q • ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) *
          (p • ρ (_root_.UniversalEnvelopingAlgebra.ι R a)) +
        n • (r • ρ (_root_.UniversalEnvelopingAlgebra.ι R b')) := by
  have hbracket := congrArg ((p * q) • ·) (mul_sub_mul_eq_map_ι_lie ρ a b)
  rw [← map_zsmul, ← map_zsmul, hab, map_zsmul, map_zsmul] at hbracket
  rw [← sub_eq_iff_eq_add']
  have hcoeff : n • (r • ρ (_root_.UniversalEnvelopingAlgebra.ι R b')) =
      ((n : ℤ) * r) • ρ (_root_.UniversalEnvelopingAlgebra.ι R b') := by
    rw [← natCast_zsmul, ← mul_zsmul]
  rw [hcoeff]
  simpa only [smul_sub, mul_smul_comm, smul_mul_assoc, mul_zsmul, smul_comm p q] using
    hbracket

/-- A bracket relation with an integral structure constant becomes the corresponding commutator
relation under every algebra homomorphism from the universal enveloping algebra. -/
theorem mul_eq_mul_add_zsmul_of_lie_eq
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b b' : L} {c : ℤ}
    (hab : ⁅a, b⁆ = c • b') :
    ρ (_root_.UniversalEnvelopingAlgebra.ι R a) *
        ρ (_root_.UniversalEnvelopingAlgebra.ι R b) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R b) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R a) +
        c • ρ (_root_.UniversalEnvelopingAlgebra.ι R b') := by
  simpa using
    (zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := 1) (r := c) (n := 1) (by simpa using hab))


section Center

variable (R L)

/-- **Centrality in `U(L)` is detected on the canonical Lie generators.**  An element of `U(L)`
is central exactly when it brackets to zero against every canonical Lie generator, because those
generators generate `U(L)` as an algebra and the elements commuting with a fixed element form a
subalgebra. -/
theorem mem_center_iff_forall_lie_ι {u : U} :
    u ∈ Subalgebra.center R U ↔
      ∀ x : L, ⁅u, _root_.UniversalEnvelopingAlgebra.ι R x⁆ = 0 := by
  refine ⟨fun hu x => ?_, fun h => ?_⟩
  · rw [LieRing.of_associative_ring_bracket,
      ← Subalgebra.mem_center_iff.mp hu (_root_.UniversalEnvelopingAlgebra.ι R x), sub_self]
  · -- The centralizer of `u` is a subalgebra containing every Lie generator, hence everything.
    have hgen : (⊤ : Subalgebra R U) ≤ Subalgebra.centralizer R {u} := by
      rw [← adjoin_range_ι R L]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      refine (Subalgebra.mem_centralizer_iff R).mpr fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hx := h x
      rw [LieRing.of_associative_ring_bracket] at hx
      exact sub_eq_zero.mp hx
    exact Subalgebra.mem_center_iff.mpr fun b =>
      ((Subalgebra.mem_centralizer_iff R).mp (hgen (Set.mem_univ b)) u rfl).symm

variable {R L}

/-- **The iterated commutator with a Lie generator, read on the Lie generators.**  Bracketing
`n` times with `ι x` inside `U(L)` sends `ι y` to the image of the `n`-fold adjoint action of `x`
on `y`; that is, `ι` intertwines `LieAlgebra.ad R L x` with the inner derivation of `U(L)`
attached to `ι x`. -/
theorem ad_ι_pow_apply_ι (x y : L) (n : ℕ) :
    (LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n)
        (_root_.UniversalEnvelopingAlgebra.ι R y) =
      _root_.UniversalEnvelopingAlgebra.ι R ((LieAlgebra.ad R L x ^ n) y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply,
      ← LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R), ih, pow_succ,
      Module.End.mul_apply, LieAlgebra.ad_apply]

end Center

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0457

section TAF_LiteralSource_0458
/- Original module: TauCeti.Algebra.WordFiltration.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The word filtration generated by a linear map

Let `A` be an associative algebra and let `f : M →ₗ[R] A` be a linear family of elements of `A`.
This file defines `TauCeti.Algebra.wordFiltration f k`, the submodule spanned by products of at most
`k` elements in the range of `f`. This is the canonical increasing filtration on any algebra
generated by a linear family.

The construction is factored out of the Clifford and universal-enveloping-algebra filtrations. In
both cases the defining relations can lower word length, so the quotient is filtered rather than
graded by length. The generic construction records the properties independent of those relations:
monotonicity, multiplicativity, the first two steps, comparison with powers of the range of `f`,
and exhaustivity onto the subalgebra generated by `f`.

## Main definitions and results

* `TauCeti.Algebra.wordFiltration`: powers of the scalar-and-generator submodule.
* `TauCeti.Algebra.wordFiltration.previousRestricted`: the preceding step inside the current step.
* `TauCeti.Algebra.wordFiltration_eq_pow`: its defining equation as that power.
* `TauCeti.Algebra.wordFiltration_mul`: multiplication adds filtration degrees.
* `TauCeti.Algebra.span_prod_map_eq_wordFiltration`: words in a spanning family span each
  filtration step.
* `TauCeti.Algebra.span_prod_map_eq_range_pow`: words of length exactly `n` span the `n`-th power
  of the generator range.
* `TauCeti.Algebra.map_wordFiltration_le`: algebra maps sending generators into degree one preserve
  every filtration step.
* `TauCeti.Algebra.map_wordFiltration_eq`: an algebra map carrying the scalar-and-generator
  submodule exactly onto another does the same in every filtration degree.
* `TauCeti.Algebra.map_wordFiltration_eq_of_surjective`: a compatible algebra map carries every
  filtration step onto the corresponding target step when the map between generators is
  surjective.
* `TauCeti.Algebra.wordFiltration_eq_iSup_pow`: comparison with powers of `LinearMap.range f`.
* `TauCeti.Algebra.iSup_wordFiltration_eq_adjoin`: the filtration exhausts precisely the subalgebra
  generated by `f`.
* `TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top` and
  `TauCeti.Algebra.exists_mem_notMem_wordFiltrationPrevious`: elementwise consequences of
  exhaustivity, the second producing the leading degree of a nonzero element.
* `TauCeti.Algebra.wordFiltration.instGradedMonoid` and
  `TauCeti.Algebra.wordFiltration.instIsRingFiltration`: the bundled multiplicativity and
  filtration instances.
-/

public section

universe u v w

namespace TauCeti.Algebra

variable {R : Type u} {M : Type v} {A : Type w}
variable [CommSemiring R] [Semiring A] [_root_.Algebra R A] [AddCommMonoid M] [Module R M]

/-- The degree filtration generated by a linear map `f : M →ₗ[R] A`.

The `k`-th step is the `k`-th submodule power of the scalars together with the range of `f`. It is
equivalently the `R`-span of products of at most `k` elements in the range of `f`, including the
empty product; see `wordFiltration_le_iff`. -/
def wordFiltration (f : M →ₗ[R] A) (k : ℕ) : Submodule R A :=
  (1 ⊔ LinearMap.range f) ^ k

/-- The defining equation of the word filtration: degree `k` is the `k`-th submodule power of the
scalars together with the range of `f`. -/
theorem wordFiltration_eq_pow (f : M →ₗ[R] A) (k : ℕ) :
    wordFiltration f k = (1 ⊔ LinearMap.range f) ^ k :=
  (rfl)

/-- The step preceding degree `k`, with bottom in degree zero. -/
def wordFiltrationPrevious (f : M →ₗ[R] A) : ℕ → Submodule R A
  | 0 => ⊥
  | k + 1 => wordFiltration f k

/-- The preceding word filtration is trivial in degree zero. -/
@[simp]
theorem wordFiltrationPrevious_zero (f : M →ₗ[R] A) : wordFiltrationPrevious f 0 = ⊥ :=
  (rfl)

/-- In successor degree, the preceding word filtration is the previous filtration step. -/
@[simp]
theorem wordFiltrationPrevious_succ (f : M →ₗ[R] A) (k : ℕ) :
    wordFiltrationPrevious f (k + 1) = wordFiltration f k :=
  (rfl)

variable (f : M →ₗ[R] A)

/-- A word of length `n` lies in the `n`-th power of the range of the generators. -/
theorem prod_map_mem_range_pow (l : List M) :
    (l.map f).prod ∈ LinearMap.range f ^ l.length := by
  induction l with
  | nil => exact Submodule.one_le.1 le_rfl
  | cons m l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self f m) ih

open Pointwise in
/-- Words of length exactly `n` in a spanning family span the `n`-th power of the generator
range. -/
theorem span_prod_map_eq_range_pow_of_span {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (n : ℕ) :
    Submodule.span R {a | ∃ l : List ι, l.length = n ∧
      (l.map fun i ↦ f (e i)).prod = a} = LinearMap.range f ^ n := by
  have hrange : LinearMap.range f = Submodule.span R (Set.range fun i ↦ f (e i)) := by
    rw [LinearMap.range_eq_map, ← he, Submodule.map_span]
    congr 2
    ext a
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, ⟨i, rfl⟩, rfl⟩
  rw [hrange, Submodule.span_pow]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_pow]
  constructor
  · rintro ⟨l, rfl, rfl⟩
    exact ⟨fun i ↦ ⟨f (e l[(i : ℕ)]), Set.mem_range_self _⟩, congrArg List.prod
      (List.ofFn_getElem_eq_map l fun i ↦ f (e i))⟩
  · rintro ⟨g, rfl⟩
    choose i hi using fun j ↦ (Set.mem_range.mp (g j).2)
    exact ⟨List.ofFn i, List.length_ofFn, by
      rw [List.map_ofFn]
      simp [Function.comp_def, hi]⟩

/-- Words of length exactly `n` span the `n`-th power of the generator range. -/
theorem span_prod_map_eq_range_pow (n : ℕ) :
    Submodule.span R {a | ∃ l : List M, l.length = n ∧ (l.map f).prod = a} =
      LinearMap.range f ^ n := by
  have hid : Submodule.span R (Set.range (id : M → M)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  simpa only [id_eq] using span_prod_map_eq_range_pow_of_span f id hid n

/-- A word of length at most `k` belongs to the `k`-th word-filtration step. -/
theorem prod_map_mem_wordFiltration {k : ℕ} {l : List M} (hl : l.length ≤ k) :
    (l.map f).prod ∈ wordFiltration f k := by
  rw [wordFiltration]
  have hpow : LinearMap.range f ^ l.length ≤ (1 ⊔ LinearMap.range f) ^ k :=
    (pow_le_pow_left' le_sup_right l.length).trans (pow_le_pow_right' le_sup_left hl)
  exact hpow (prod_map_mem_range_pow f l)

/-- A submodule contains the `k`-th filtration step exactly when it contains every word of length
at most `k`. -/
theorem wordFiltration_le_iff {k : ℕ} {p : Submodule R A} :
    wordFiltration f k ≤ p ↔ ∀ l : List M, l.length ≤ k → (l.map f).prod ∈ p := by
  constructor
  · intro h l hl
    exact h (prod_map_mem_wordFiltration f hl)
  · intro h
    induction k generalizing p with
    | zero =>
        rw [wordFiltration, pow_zero]
        exact Submodule.one_le.2 (by simpa using h [] le_rfl)
    | succ k ih =>
        rw [wordFiltration, pow_succ', Submodule.sup_mul, Submodule.one_mul]
        refine sup_le (ih fun l hl => h l (hl.trans (Nat.le_succ k))) ?_
        rw [Submodule.mul_le]
        rintro _ ⟨m, rfl⟩ y hy
        apply ih (p := p.comap (LinearMap.mulLeft R (f m))) _ hy
        intro l hl
        rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
        rw [← List.prod_cons, ← List.map_cons]
        exact h (m :: l) (by simpa using Nat.succ_le_succ hl)

/-- Products of at most `k` images of a spanning family span the `k`-th word-filtration step. -/
theorem span_prod_map_eq_wordFiltration {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (k : ℕ) :
    Submodule.span R {a | ∃ word : List ι, word.length ≤ k ∧
      (word.map fun i ↦ f (e i)).prod = a} = wordFiltration f k := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro a ⟨word, hword, rfl⟩
    have h := prod_map_mem_wordFiltration f (l := word.map e) (by simpa using hword)
    simpa only [List.map_map, Function.comp_def, SetLike.mem_coe] using h
  · rw [wordFiltration_le_iff]
    intro word hword
    induction word generalizing k with
    | nil => exact Submodule.subset_span ⟨[], Nat.zero_le k, by simp⟩
    | cons x word ih =>
        cases k with
        | zero => simp at hword
        | succ k =>
            have htail : word.length ≤ k := by simpa using hword
            have ih := ih k htail
            have hx : x ∈ Submodule.span R (Set.range e) := by rw [he]; exact Submodule.mem_top
            refine Submodule.span_induction (p := fun y _ ↦
              f y * (word.map f).prod ∈ Submodule.span R
                {a | ∃ familyWord : List ι, familyWord.length ≤ k + 1 ∧
                  (familyWord.map fun i ↦ f (e i)).prod = a}) ?_ ?_ ?_ ?_ hx
            · intro y hy
              obtain ⟨i, rfl⟩ := hy
              have hcomap : (word.map f).prod ∈
                  (Submodule.span R {a | ∃ familyWord : List ι, familyWord.length ≤ k + 1 ∧
                    (familyWord.map fun i ↦ f (e i)).prod = a}).comap
                      (LinearMap.mulLeft R (f (e i))) := by
                refine (Submodule.span_le.mpr ?_) ih
                rintro a ⟨tail, htail, rfl⟩
                exact Submodule.subset_span
                  ⟨i :: tail, by simpa using Nat.succ_le_succ htail, by simp⟩
              simpa only [LinearMap.mulLeft_apply] using Submodule.mem_comap.mp hcomap
            · simp
            · intro y z _ _ hy hz
              simpa only [map_add, add_mul] using Submodule.add_mem _ hy hz
            · intro r y _ hy
              simpa only [map_smul, smul_mul_assoc] using Submodule.smul_mem _ r hy

section Map

variable {N : Type*} {B : Type*}
variable [Semiring B] [_root_.Algebra R B] [AddCommMonoid N] [Module R N]

/-- An algebra homomorphism that sends each source generator into target filtration degree one
preserves word-filtration degree. -/
theorem map_wordFiltration_le (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap ≤ wordFiltration f' k := by
  rw [wordFiltration_eq_pow, wordFiltration_eq_pow, Submodule.map_pow, Submodule.map_sup,
    Submodule.map_one]
  apply pow_le_pow_left'
  refine sup_le le_sup_left ?_
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  simpa only [wordFiltration, pow_one, AlgHom.toLinearMap_apply] using h m

/-- The membership form of `map_wordFiltration_le`: an algebra homomorphism that sends source
generators into target filtration degree one preserves every filtration step. -/
theorem map_mem_wordFiltration (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) {k : ℕ} {x : A}
    (hx : x ∈ wordFiltration f k) : g x ∈ wordFiltration f' k :=
  map_wordFiltration_le f g f' h k ⟨x, hx, rfl⟩

/-- An algebra homomorphism that maps one scalar-and-generator submodule exactly onto another
maps every corresponding word-filtration step exactly onto the other. -/
theorem map_wordFiltration_eq (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : (1 ⊔ LinearMap.range f).map g.toLinearMap = 1 ⊔ LinearMap.range f') (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap = wordFiltration f' k := by
  rw [wordFiltration_eq_pow, wordFiltration_eq_pow, Submodule.map_pow, h]

/-- A compatible algebra homomorphism maps every word-filtration step onto the corresponding
target step when its map on the generating modules is surjective. -/
theorem map_wordFiltration_eq_of_surjective (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : g.toLinearMap.comp f = f'.comp q) (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap = wordFiltration f' k := by
  apply map_wordFiltration_eq f g f' _ k
  rw [Submodule.map_sup, Submodule.map_one, ← LinearMap.range_comp, h,
    LinearMap.range_comp, LinearMap.range_eq_top_of_surjective q hq, Submodule.map_top]

end Map

/-- The word filtration is increasing. -/
theorem wordFiltration_mono : Monotone (wordFiltration f) := fun _ _ hij =>
  pow_le_pow_right' le_sup_left hij

/-- The zeroth word-filtration step consists of the scalars. -/
@[simp]
theorem wordFiltration_zero : wordFiltration f 0 = 1 := by
  simp [wordFiltration]

/-- The empty word puts `1` in every filtration step. -/
theorem one_mem_wordFiltration (k : ℕ) : (1 : A) ∈ wordFiltration f k := by
  simpa using prod_map_mem_wordFiltration f (l := []) (Nat.zero_le k)

/-- Every scalar belongs to every filtration step. -/
theorem algebraMap_mem_wordFiltration (r : R) (k : ℕ) :
    algebraMap R A r ∈ wordFiltration f k := by
  rw [_root_.Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (one_mem_wordFiltration f k)

/-- Each generator belongs to the first filtration step. -/
theorem apply_mem_wordFiltration_one (m : M) : f m ∈ wordFiltration f 1 := by
  simpa using prod_map_mem_wordFiltration f (l := [m]) le_rfl

/-- The range of the generating linear map lies in the first filtration step. -/
theorem range_le_wordFiltration_one : LinearMap.range f ≤ wordFiltration f 1 := by
  rintro _ ⟨m, rfl⟩
  exact apply_mem_wordFiltration_one f m

/-- Multiplication adds word-filtration degrees. In fact the product of the two filtration steps
equals the step in the sum degree. -/
theorem wordFiltration_mul (i j : ℕ) :
    wordFiltration f i * wordFiltration f j = wordFiltration f (i + j) := by
  rw [wordFiltration, wordFiltration, wordFiltration, pow_add]

/-- The elementwise multiplicativity of the word filtration. -/
theorem mul_mem_wordFiltration {i j : ℕ} {x y : A} (hx : x ∈ wordFiltration f i)
    (hy : y ∈ wordFiltration f j) : x * y ∈ wordFiltration f (i + j) := by
  rw [← wordFiltration_mul f i j]
  exact Submodule.mul_mem_mul hx hy

/-- Multiplying an element of degree strictly below `i` by an element of degree at most `j`
produces an element of degree strictly below `i + j`. -/
theorem mul_mem_wordFiltrationPrevious_left {i j : ℕ} {x y : A}
    (hx : x ∈ wordFiltrationPrevious f i) (hy : y ∈ wordFiltration f j) :
    x * y ∈ wordFiltrationPrevious f (i + j) := by
  cases i with
  | zero =>
      simp only [wordFiltrationPrevious_zero, Submodule.mem_bot] at hx
      subst x
      simp
  | succ i =>
      rw [wordFiltrationPrevious_succ] at hx
      rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc,
        wordFiltrationPrevious_succ]
      exact mul_mem_wordFiltration f hx hy

/-- Multiplying an element of degree at most `i` by an element of degree strictly below `j`
produces an element of degree strictly below `i + j`. -/
theorem mul_mem_wordFiltrationPrevious_right {i j : ℕ} {x y : A}
    (hx : x ∈ wordFiltration f i) (hy : y ∈ wordFiltrationPrevious f j) :
    x * y ∈ wordFiltrationPrevious f (i + j) := by
  cases j with
  | zero =>
      simp only [wordFiltrationPrevious_zero, Submodule.mem_bot] at hy
      subst y
      simp
  | succ j =>
      rw [wordFiltrationPrevious_succ] at hy
      rw [← Nat.add_assoc, wordFiltrationPrevious_succ]
      exact mul_mem_wordFiltration f hx hy

/-- The `n`-th power of the generator range lies in filtration degree `n`. -/
theorem range_pow_le_wordFiltration (n : ℕ) : LinearMap.range f ^ n ≤ wordFiltration f n :=
  pow_le_pow_left' le_sup_right n

/-- The `k`-th word-filtration step is the supremum of the powers of the generator range of degree
at most `k`. -/
theorem wordFiltration_eq_iSup_pow (k : ℕ) :
    wordFiltration f k = ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range f ^ (i : ℕ) := by
  refine le_antisymm ((wordFiltration_le_iff f).2 fun l hl => ?_) (iSup_le fun i => ?_)
  · exact Submodule.mem_iSup_of_mem ⟨l.length, hl⟩ (prod_map_mem_range_pow f l)
  · exact (range_pow_le_wordFiltration f i).trans (wordFiltration_mono f i.2)

/-- The successor filtration step adjoins words of exactly the new degree. -/
theorem wordFiltration_succ_eq_sup (k : ℕ) :
    wordFiltration f (k + 1) = wordFiltration f k ⊔ LinearMap.range f ^ (k + 1) := by
  refine le_antisymm ((wordFiltration_le_iff f).2 fun l hl => ?_)
    (sup_le (wordFiltration_mono f (Nat.le_succ k)) (range_pow_le_wordFiltration f (k + 1)))
  rcases eq_or_lt_of_le hl with h | h
  · exact Submodule.mem_sup_right (h ▸ prod_map_mem_range_pow f l)
  · exact Submodule.mem_sup_left (prod_map_mem_wordFiltration f (Nat.lt_succ_iff.1 h))

/-- The first filtration step consists of the scalars and the generator range. -/
@[simp]
theorem wordFiltration_one : wordFiltration f 1 = 1 ⊔ LinearMap.range f := by
  simp [wordFiltration]

/-- Powers of a filtration step multiply its degree. -/
theorem wordFiltration_pow (i n : ℕ) : wordFiltration f i ^ n = wordFiltration f (i * n) := by
  rw [wordFiltration, wordFiltration, pow_mul]

/-- The word filtration exhausts exactly the subalgebra generated by the range of `f`. -/
theorem iSup_wordFiltration_eq_adjoin :
    ⨆ k, wordFiltration f k = (_root_.Algebra.adjoin R (Set.range f)).toSubmodule := by
  refine le_antisymm (iSup_le fun _ => (wordFiltration_le_iff f).2 ?_) ?_
  · intro l hl
    clear hl
    induction l with
    | nil => simp
    | cons m l ih =>
      rw [List.map_cons, List.prod_cons]
      exact (_root_.Algebra.adjoin R (Set.range f)).mul_mem
        (_root_.Algebra.subset_adjoin (Set.mem_range_self m)) ih
  · rintro x hx
    refine _root_.Algebra.adjoin_induction (p := fun x _ => x ∈ ⨆ k, wordFiltration f k)
      (fun _ hx => ?_) (fun r => ?_) (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy)
      (fun _ _ _ _ hx hy => ?_) hx
    · obtain ⟨m, rfl⟩ := hx
      exact Submodule.mem_iSup_of_mem 1 (apply_mem_wordFiltration_one f m)
    · exact Submodule.mem_iSup_of_mem 0 (algebraMap_mem_wordFiltration f r 0)
    · rw [Submodule.mem_iSup_of_directed _ (wordFiltration_mono f).directed_le] at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      exact Submodule.mem_iSup_of_mem (i + j) (mul_mem_wordFiltration f hi hj)

/-- **An exhaustive word filtration covers the algebra elementwise**: if the filtration steps
supremum to `⊤`, every element lies in one of them. -/
theorem exists_mem_wordFiltration_of_iSup_eq_top (h : ⨆ k, wordFiltration f k = ⊤) (a : A) :
    ∃ k, a ∈ wordFiltration f k := by
  have hmem : a ∈ ⨆ k, wordFiltration f k := by
    rw [h]
    exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (wordFiltration_mono f).directed_le] at hmem

/-- **A nonzero element of an exhaustive word filtration has a leading degree**: a degree it
belongs to but whose preceding step it misses. -/
theorem exists_mem_notMem_wordFiltrationPrevious {a : A} (ha : a ≠ 0)
    (hex : ∃ k, a ∈ wordFiltration f k) :
    ∃ k, a ∈ wordFiltration f k ∧ a ∉ wordFiltrationPrevious f k := by
  classical
  obtain ⟨k, hk, hmin⟩ :
      ∃ k, a ∈ wordFiltration f k ∧ ∀ m, m < k → a ∉ wordFiltration f m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨k, hk, ?_⟩
  cases k with
  | zero => simpa using ha
  | succ m =>
      rw [wordFiltrationPrevious_succ]
      exact hmin m (Nat.lt_succ_self m)

namespace wordFiltration

/-- The preceding word-filtration step, viewed as a submodule of the current step. -/
abbrev previousRestricted (k : ℕ) :
    Submodule R (wordFiltration f k) :=
  (wordFiltrationPrevious f k).submoduleOf (wordFiltration f k)

/-- Membership in the restricted preceding step is ambient membership in the preceding step. -/
@[simp]
theorem mem_previousRestricted_iff (k : ℕ)
    (x : wordFiltration f k) :
    x ∈ previousRestricted f k ↔ (x : A) ∈ wordFiltrationPrevious f k :=
  Iff.rfl

/-- The restricted preceding word filtration is trivial in degree zero. -/
@[simp]
theorem previousRestricted_zero : previousRestricted f 0 = ⊥ := by
  ext x
  simp

/-- In successor degree, the restricted preceding word filtration is the previous step viewed
inside the current step. -/
@[simp]
theorem previousRestricted_succ (k : ℕ) :
    previousRestricted f (k + 1) =
      Submodule.comap (wordFiltration f (k + 1)).subtype (wordFiltration f k) := by
  simp only [previousRestricted, wordFiltrationPrevious_succ, Submodule.submoduleOf]

/-- Casting a filtered element between equal degrees does not change its value in the ambient
algebra. -/
@[simp]
theorem wordFiltration_coe_cast {i j : ℕ}
    (h : i = j) (x : wordFiltration f i) :
    ((cast (congrArg (fun k => ↥(wordFiltration f k)) h) x : wordFiltration f j) :
      A) = x := by
  subst j
  rfl

/-- Word filtrations are multiplicative families of submodules. -/
instance instGradedMonoid : SetLike.GradedMonoid (wordFiltration f) where
  one_mem := by simpa using one_mem_wordFiltration f 0
  mul_mem := fun {i j} {x y} hx hy =>
    mul_mem_wordFiltration (i := i) (j := j) (x := x) (y := y) f hx hy

/-- The word filtration, with the preceding step at each degree, is a ring filtration. -/
instance instIsRingFiltration :
    IsRingFiltration (wordFiltration f) (wordFiltrationPrevious f) where
  mono := wordFiltration_mono f
  is_le := by
    intro i j hij
    cases j with
    | zero => simp at hij
    | succ j =>
        exact wordFiltration_mono f (Nat.le_of_lt_succ hij)
  is_sup := by
    intro B j hB
    cases j with
    | zero => exact bot_le
    | succ j => exact hB j (Nat.lt_succ_self j)

end wordFiltration

end TauCeti.Algebra
end
end TAF_LiteralSource_0458

section TAF_LiteralSource_0459
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The PBW filtration of a universal enveloping algebra

This file constructs the Poincaré--Birkhoff--Witt filtration: the increasing filtration of
`UniversalEnvelopingAlgebra R L` by word length in the image of the canonical Lie map
`UniversalEnvelopingAlgebra.ι R`.

The defining relation

```text
ι(x) * ι(y) = ι(y) * ι(x) + ι([x,y])
```

replaces a degree-two commutator by a degree-one term. Thus word length gives a filtration, not a
grading. In the associated graded this degree drop makes the leading symbols commute; the comparison
with `SymmetricAlgebra R L` is not treated here.

Nothing in the construction is special to the enveloping algebra: `pbwFiltration` and
`pbwFiltrationPrevious` are `TauCeti.Algebra.wordFiltration` and
`TauCeti.Algebra.wordFiltrationPrevious` of `TauCeti/Algebra/WordFiltration/Basic.lean`,
specialized to `UniversalEnvelopingAlgebra.ι R`, exactly as `CliffordAlgebra.filtration` is that
same construction for `CliffordAlgebra.ι`. What is special to `U(L)` is the exhaustivity, which
comes from the tensor-algebra presentation.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration`: words of length at most `k` in the range of
  `UniversalEnvelopingAlgebra.ι R`.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_eq_pow`: its defining equation as the power of
  the scalar-and-generator submodule.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_mul`: multiplication adds degrees.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_zero` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_one`: the scalar and generator steps.
* `TauCeti.UniversalEnvelopingAlgebra.adjoin_image_ι_eq_top`: the image of any Lie generating set
  generates `U(L)` as an `R`-algebra.
* `TauCeti.UniversalEnvelopingAlgebra.iSup_pbwFiltration_eq_top`: the filtration is exhaustive.
* `TauCeti.UniversalEnvelopingAlgebra.exists_mem_pbwFiltration`: exhaustivity read elementwise.
* `TauCeti.UniversalEnvelopingAlgebra.instIsRingFiltration`: the bundled `IsRingFiltration`
  structure on `pbwFiltration`, with `pbwFiltrationPrevious` as its preceding-step family.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The PBW filtration on `U(L)`: its `k`-th step is spanned by products of at most `k` canonical
Lie generators.

This is `TauCeti.Algebra.wordFiltration` specialized to `UniversalEnvelopingAlgebra.ι R`; the
shared API is in `TauCeti/Algebra/WordFiltration/Basic.lean`. -/
def pbwFiltration (k : ℕ) : Submodule R U :=
  TauCeti.Algebra.wordFiltration (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k

/-- The PBW filtration is the word filtration generated by the canonical Lie map. -/
theorem pbwFiltration_def (k : ℕ) :
    pbwFiltration R L k =
      TauCeti.Algebra.wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k := (rfl)

/-- PBW filtration degree `k` is the `k`-th power of the scalars and canonical Lie generators. -/
theorem pbwFiltration_eq_pow (k : ℕ) :
    pbwFiltration R L k =
      (1 ⊔ LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap) ^ k :=
  TauCeti.Algebra.wordFiltration_eq_pow _ k

/-- The step preceding degree `k` in the PBW filtration, that is
`TauCeti.Algebra.wordFiltrationPrevious` specialized to `UniversalEnvelopingAlgebra.ι R`, with
bottom in degree zero. -/
def pbwFiltrationPrevious : ℕ → Submodule R U :=
  TauCeti.Algebra.wordFiltrationPrevious (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap

/-- The preceding PBW filtration is the preceding word filtration of the canonical Lie map. -/
theorem pbwFiltrationPrevious_def (k : ℕ) :
    pbwFiltrationPrevious R L k =
      TauCeti.Algebra.wordFiltrationPrevious
        (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k := (rfl)

/-- The preceding PBW filtration is trivial in degree zero. -/
@[simp]
theorem pbwFiltrationPrevious_zero : pbwFiltrationPrevious R L 0 = ⊥ :=
  TauCeti.Algebra.wordFiltrationPrevious_zero _

/-- In successor degree, the preceding PBW filtration is the previous filtration step. -/
@[simp]
theorem pbwFiltrationPrevious_succ (k : ℕ) :
    pbwFiltrationPrevious R L (k + 1) = pbwFiltration R L k :=
  TauCeti.Algebra.wordFiltrationPrevious_succ _ k

/-- A word of at most `k` canonical Lie generators lies in PBW filtration degree `k`. -/
theorem prod_map_ι_mem_pbwFiltration {k : ℕ} {l : List L} (hl : l.length ≤ k) :
    (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈ pbwFiltration R L k := by
  -- The generic lemma is about the underlying linear map, so name the coercion explicitly.
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.prod_map_mem_wordFiltration _ hl

/-- A submodule contains the `k`-th PBW filtration step exactly when it contains every word of
length at most `k` in the canonical Lie generators. -/
theorem pbwFiltration_le_iff {k : ℕ} {p : Submodule R U} :
    pbwFiltration R L k ≤ p ↔
      ∀ l : List L, l.length ≤ k → (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈ p := by
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.wordFiltration_le_iff _

/-- The PBW filtration is increasing. -/
theorem pbwFiltration_mono : Monotone (pbwFiltration R L) :=
  TauCeti.Algebra.wordFiltration_mono _

/-- PBW filtration degree zero consists of scalars. -/
@[simp]
theorem pbwFiltration_zero : pbwFiltration R L 0 = 1 :=
  TauCeti.Algebra.wordFiltration_zero _

/-- The empty word puts `1` in every PBW filtration step. -/
theorem one_mem_pbwFiltration (k : ℕ) : (1 : U) ∈ pbwFiltration R L k :=
  TauCeti.Algebra.one_mem_wordFiltration _ k

/-- Scalars belong to every PBW filtration step. -/
theorem algebraMap_mem_pbwFiltration (r : R) (k : ℕ) :
    algebraMap R U r ∈ pbwFiltration R L k :=
  TauCeti.Algebra.algebraMap_mem_wordFiltration _ r k

/-- A canonical Lie generator has PBW filtration degree at most one. -/
theorem ι_mem_pbwFiltration_one (x : L) :
    _root_.UniversalEnvelopingAlgebra.ι R x ∈ pbwFiltration R L 1 := by
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.apply_mem_wordFiltration_one _ x

/-- The range of the canonical Lie map lies in the first PBW filtration step. -/
theorem ι_range_le_pbwFiltration_one :
    LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ≤ pbwFiltration R L 1 :=
  TauCeti.Algebra.range_le_wordFiltration_one _

/-- Multiplication adds PBW filtration degrees. -/
theorem pbwFiltration_mul (i j : ℕ) :
    pbwFiltration R L i * pbwFiltration R L j = pbwFiltration R L (i + j) :=
  TauCeti.Algebra.wordFiltration_mul _ i j

/-- The elementwise multiplicativity of the PBW filtration. -/
theorem mul_mem_pbwFiltration {i j : ℕ} {x y : U} (hx : x ∈ pbwFiltration R L i)
    (hy : y ∈ pbwFiltration R L j) : x * y ∈ pbwFiltration R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltration _ hx hy

/-- Multiplication preserves a strict degree drop in the left factor of the PBW filtration. -/
theorem mul_mem_pbwFiltrationPrevious_left {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltrationPrevious R L i) (hy : y ∈ pbwFiltration R L j) :
    x * y ∈ pbwFiltrationPrevious R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_left _ hx hy

/-- Multiplication preserves a strict degree drop in the right factor of the PBW filtration. -/
theorem mul_mem_pbwFiltrationPrevious_right {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltration R L i) (hy : y ∈ pbwFiltrationPrevious R L j) :
    x * y ∈ pbwFiltrationPrevious R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_right _ hx hy

/-- Iterating `pbwFiltration_mul`: the `n`-th submodule power of the `i`-th step is the `i * n`-th
step. -/
theorem pbwFiltration_pow (i n : ℕ) :
    pbwFiltration R L i ^ n = pbwFiltration R L (i * n) :=
  TauCeti.Algebra.wordFiltration_pow _ i n

/-- The `k`-th PBW filtration step is the supremum of the powers of the canonical generator range
of degree at most `k`. -/
theorem pbwFiltration_eq_iSup_pow (k : ℕ) :
    pbwFiltration R L k =
      ⨆ i : {i : ℕ // i ≤ k},
        LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ^ (i : ℕ) :=
  TauCeti.Algebra.wordFiltration_eq_iSup_pow _ k

/-- The successor PBW step adjoins words of exactly the new degree. -/
theorem pbwFiltration_succ_eq_sup (k : ℕ) :
    pbwFiltration R L (k + 1) =
      pbwFiltration R L k ⊔
        LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ^ (k + 1) :=
  TauCeti.Algebra.wordFiltration_succ_eq_sup _ k

/-- PBW filtration degree one consists of the scalars and the canonical Lie generators. -/
@[simp]
theorem pbwFiltration_one :
    pbwFiltration R L 1 = 1 ⊔ LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap :=
  TauCeti.Algebra.wordFiltration_one _

/-- **A Lie generating set generates the enveloping algebra.** If `S` generates `L` as a Lie
algebra, then the image of `S` under the canonical map generates `U(L)` as an `R`-algebra.

Only the associative subalgebra generated by the image is involved, so no linear independence or
finiteness of `S` is needed. -/
theorem adjoin_image_ι_eq_top {S : Set L} (hS : LieSubalgebra.lieSpan R L S = ⊤) :
    _root_.Algebra.adjoin R (⇑(_root_.UniversalEnvelopingAlgebra.ι R) '' S) =
      (⊤ : Subalgebra R U) := by
  have hle : LieSubalgebra.lieSpan R L S ≤
      (lieSubalgebraOfSubalgebra R U (_root_.Algebra.adjoin R
        (⇑(_root_.UniversalEnvelopingAlgebra.ι R) '' S))).comap
          (_root_.UniversalEnvelopingAlgebra.ι R) :=
    LieSubalgebra.lieSpan_le.2 fun y hy =>
      (LieSubalgebra.mem_comap _ _).2 (_root_.Algebra.subset_adjoin ⟨y, hy, rfl⟩)
  rw [hS] at hle
  rw [eq_top_iff, ← adjoin_range_ι R L]
  refine _root_.Algebra.adjoin_le ?_
  rintro _ ⟨x, rfl⟩
  exact (LieSubalgebra.mem_comap _ _).1 (hle (LieSubalgebra.mem_top x))

/-- **The PBW filtration is exhaustive.** The canonical generators generate `U(L)` as an algebra,
so every element is a combination of words of some finite length. -/
theorem iSup_pbwFiltration_eq_top : ⨆ k, pbwFiltration R L k = ⊤ := by
  have h : ⨆ k, pbwFiltration R L k =
      (_root_.Algebra.adjoin R
        (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap)).toSubmodule :=
    TauCeti.Algebra.iSup_wordFiltration_eq_adjoin _
  rw [h, LieHom.coe_toLinearMap, adjoin_range_ι, _root_.Algebra.top_toSubmodule]

/-- **Every element of the enveloping algebra lies in some PBW filtration step**, the elementwise
form of `TauCeti.UniversalEnvelopingAlgebra.iSup_pbwFiltration_eq_top`. -/
theorem exists_mem_pbwFiltration (a : U) : ∃ k, a ∈ pbwFiltration R L k :=
  TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top _ (iSup_pbwFiltration_eq_top R L) a

/-- The PBW filtration carries Mathlib's bundled ring-filtration structure. -/
instance instIsRingFiltration :
    IsRingFiltration (pbwFiltration R L) (pbwFiltrationPrevious R L) :=
  TauCeti.Algebra.wordFiltration.instIsRingFiltration _

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0459

section TAF_LiteralSource_0460
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Functoriality of universal enveloping algebras

A homomorphism of Lie algebras induces an algebra homomorphism of their universal enveloping
algebras. This file constructs that map directly from Mathlib's universal property and proves its
characteristic equation on the canonical Lie generators, its identity and composition laws, and
its behaviour on split monomorphisms and split epimorphisms. A Lie algebra equivalence consequently
induces an algebra equivalence of universal enveloping algebras.

The split-morphism results avoid any freeness or Poincare--Birkhoff--Witt hypothesis: a chosen
one-sided inverse of a Lie homomorphism lifts to the same one-sided inverse on enveloping algebras.
In particular, the equivalence construction is available over an arbitrary commutative ring. No
Poincare--Birkhoff--Witt theorem or injectivity of the canonical Lie map is asserted here.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.map`: the algebra homomorphism induced by a Lie algebra
  homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.mapEquiv`: the algebra equivalence induced by a Lie algebra
  equivalence.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_ι`: the induced map agrees with the original Lie
  homomorphism on the canonical generators.
* `TauCeti.UniversalEnvelopingAlgebra.map_id` and
  `TauCeti.UniversalEnvelopingAlgebra.map_comp`: enveloping-algebra maps are functorial.
* `TauCeti.UniversalEnvelopingAlgebra.map_surjective_of_surjective`: surjective Lie maps induce
  surjective enveloping-algebra maps.
* `TauCeti.UniversalEnvelopingAlgebra.map_injective_of_leftInverse` and
  `TauCeti.UniversalEnvelopingAlgebra.map_surjective_of_rightInverse`: split morphisms remain split
  after passing to enveloping algebras.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The algebra homomorphism of universal enveloping algebras induced by a Lie algebra
homomorphism.

It is the unique algebra homomorphism sending the canonical generator `ι R x` to `ι R (f x)`;
`map_ι` is the corresponding computation rule and `map_unique` is the universal property in that
form. -/
noncomputable def map (f : LieHom R L M) :
    _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  _root_.UniversalEnvelopingAlgebra.lift R
    ((_root_.UniversalEnvelopingAlgebra.ι R).comp f)

/-- An enveloping-algebra map acts on the canonical Lie generators by the original Lie
homomorphism. -/
-- `simp`-normal form is `map_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem map_ι (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x) := by
  rw [map, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact LieHom.comp_apply _ _ _

/-- The `simp`-normal form of `map_ι`, stated for the canonical generators as `simp` writes them:
`ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem map_ι' (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (f x)) := by
  simpa using map_ι R f x

/-- An algebra homomorphism out of an enveloping algebra is the map induced by `f` exactly when
it sends every canonical generator to the image prescribed by `f`. -/
theorem map_unique (f : LieHom R L M)
    (g : _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M) :
    (∀ x, g (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x)) ↔ g = map R f := by
  rw [map]
  refine Iff.trans ?_
    (_root_.UniversalEnvelopingAlgebra.lift_unique R
      ((_root_.UniversalEnvelopingAlgebra.ι R).comp f) g)
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- The identity Lie homomorphism induces the identity algebra homomorphism. -/
@[simp]
theorem map_id :
    map R (LieHom.id : LieHom R L L) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.id_apply, AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.id_apply]

/-- Composition of Lie homomorphisms becomes composition of the induced algebra homomorphisms. -/
@[simp]
theorem map_comp (f : LieHom R L M) (g : LieHom R M N) :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply]

/-- For Lie subalgebras `A ≤ B` of `L`, mapping `U(A)` into `U(B)` and then into `U(L)` is the map
induced by the inclusion of `A` in `L`. -/
@[simp]
theorem map_incl_comp_map_inclusion {A B : LieSubalgebra R L} (h : A ≤ B) :
    (map R B.incl).comp (map R (LieSubalgebra.inclusion h)) = map R A.incl := by
  rw [← map_comp]
  -- `B.incl ∘ inclusion h` and `A.incl` are both the coercion `A → L`
  rfl

/-- A left inverse of Lie homomorphisms induces a left inverse of the corresponding
enveloping-algebra maps. -/
theorem map_leftInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : g.comp f = LieHom.id) : Function.LeftInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R g).comp (map R f) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A right inverse of Lie homomorphisms induces a right inverse of the corresponding
enveloping-algebra maps. -/
theorem map_rightInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : f.comp g = LieHom.id) : Function.RightInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R f).comp (map R g) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R M) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A split monomorphism of Lie algebras induces an injective homomorphism of enveloping
algebras. -/
theorem map_injective_of_leftInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : g.comp f = LieHom.id) : Function.Injective (map R f) :=
  (map_leftInverse R h).injective

/-- A surjective Lie homomorphism induces a surjective homomorphism of universal enveloping
algebras. -/
theorem map_surjective_of_surjective (f : LieHom R L M) (hf : Function.Surjective f) :
    Function.Surjective (map R f) := by
  intro y
  induction y using induction_ι R M with
  | ι y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨_root_.UniversalEnvelopingAlgebra.ι R x, map_ι R f x⟩
  | algebraMap r =>
      exact ⟨algebraMap R (_root_.UniversalEnvelopingAlgebra R L) r, (map R f).commutes r⟩
  | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, map_add (map R f) x y⟩
  | mul a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x * y, map_mul (map R f) x y⟩

/-- A split epimorphism of Lie algebras induces a surjective homomorphism of enveloping
algebras. -/
theorem map_surjective_of_rightInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : f.comp g = LieHom.id) : Function.Surjective (map R f) :=
  map_surjective_of_surjective R f fun y ↦
    ⟨g y, by
      simpa only [LieHom.comp_apply, LieHom.id_apply] using
        DFunLike.congr_fun h y⟩

/-- A Lie algebra equivalence induces an algebra equivalence of universal enveloping algebras. -/
noncomputable def mapEquiv (e : LieEquiv R L M) :
    _root_.UniversalEnvelopingAlgebra R L ≃ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  AlgEquiv.ofAlgHom (map R e.toLieHom) (map R e.symm.toLieHom)
    (by
      rw [← map_comp]
      have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.apply_symm_apply
      rw [h, map_id])
    (by
      rw [← map_comp]
      have h : e.symm.toLieHom.comp e.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.symm_apply_apply
      rw [h, map_id])

/-- The algebra homomorphism underlying `mapEquiv` is the map induced by the underlying Lie
homomorphism. -/
@[simp]
theorem mapEquiv_toAlgHom (e : LieEquiv R L M) :
    (mapEquiv R e).toAlgHom = map R e.toLieHom :=
  by rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The algebra equivalence induced by a Lie equivalence acts on canonical generators by that Lie
equivalence. -/
-- `simp`-normal form is `mapEquiv_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem mapEquiv_ι (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (e x) := by
  rw [← AlgEquiv.toAlgHom_apply, mapEquiv_toAlgHom, map_ι, LieEquiv.coe_coe]

/-- The `simp`-normal form of `mapEquiv_ι`, stated for the canonical generators as `simp` writes
them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem mapEquiv_ι' (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (e x)) := by
  simpa using mapEquiv_ι R e x

/-- Passing the inverse Lie equivalence to enveloping algebras gives the inverse algebra
equivalence. -/
@[simp]
theorem mapEquiv_symm (e : LieEquiv R L M) :
    (mapEquiv R e).symm = mapEquiv R e.symm :=
  by
    apply AlgEquiv.ext
    intro a
    rw [mapEquiv, AlgEquiv.ofAlgHom_symm]
    simp only [AlgEquiv.ofAlgHom_apply, mapEquiv, LieEquiv.symm_symm]

/-- The identity Lie equivalence induces the identity algebra equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv R (LieEquiv.refl : LieEquiv R L L) = AlgEquiv.refl :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have hrefl : (LieEquiv.refl : LieEquiv R L L).toLieHom = LieHom.id := by
      apply LieHom.ext
      intro x
      rfl
    rw [hrefl, map_id, AlgEquiv.refl_toAlgHom]

/-- Composition of Lie equivalences becomes composition of the induced algebra equivalences. -/
@[simp]
theorem mapEquiv_trans (e : LieEquiv R L M) (d : LieEquiv R M N) :
    (mapEquiv R e).trans (mapEquiv R d) = mapEquiv R (e.trans d) :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have htrans : ((mapEquiv R e).trans (mapEquiv R d)).toAlgHom =
        (mapEquiv R d).toAlgHom.comp (mapEquiv R e).toAlgHom := by
      apply AlgHom.ext
      intro a
      simp only [AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply, AlgHom.comp_apply]
    rw [htrans, mapEquiv_toAlgHom, mapEquiv_toAlgHom]
    have hLie : (e.trans d).toLieHom = d.toLieHom.comp e.toLieHom := by
      apply LieHom.ext
      intro x
      simp only [LieEquiv.trans_apply, LieHom.comp_apply, LieEquiv.coe_coe]
    rw [hLie, map_comp]

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0460

section TAF_LiteralSource_0461
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Permuting PBW words modulo lower filtration

This file proves the first consequence of the defining relation of a universal enveloping algebra
for its associated graded. If two words in the canonical generators differ only by a permutation,
then their difference has filtration degree strictly below their common word length. In particular,
the leading term of a word is unchanged when the word is sorted.

An adjacent exchange is the mathematical heart of the proof:

```text
ι(x) * ι(y) - ι(y) * ι(x) = ι([x,y]).
```

The left side has word length two while the right side has word length one. Multiplying by the
unchanged suffix preserves this one-degree drop. Induction on `List.Perm` then gives the result for
an arbitrary permutation.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial`: the product of a word in a chosen family of
  Lie-algebra elements.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwMonomial`: induced maps act factorwise on PBW
  monomials.
* `TauCeti.UniversalEnvelopingAlgebra.prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm`:
  permuted words in canonical generators differ by a lower-filtration term.
* `pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm`:
  the same statement for words in an indexed family.
* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`:
  every word has the same leading term as its ordered version.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Exchanging the two leading generators of a word lowers the PBW filtration degree of the
difference by one. -/
private theorem prod_map_ι_sub_swap_mem_pbwFiltrationPrevious (x y : L) (l : List L) :
    ((x :: y :: l).map ⇑ι).prod - ((y :: x :: l).map ⇑ι).prod ∈
      pbwFiltrationPrevious R L (x :: y :: l).length := by
  simp only [List.length_cons, pbwFiltrationPrevious_succ, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← mul_assoc, ← sub_mul,
    ← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]
  simpa only [Nat.add_comm] using
    mul_mem_pbwFiltration (R := R) (L := L) (ι_mem_pbwFiltration_one R L ⁅x, y⁆)
      (prod_map_ι_mem_pbwFiltration R L le_rfl)

/-- **Permuting a word does not change its leading PBW term.** The products of two permuted lists
of canonical generators differ by an element of degree strictly below their common length. -/
theorem prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm {l₁ l₂ : List L}
    (h : l₁.Perm l₂) :
    (l₁.map ⇑ι).prod - (l₂.map ⇑ι).prod ∈ pbwFiltrationPrevious R L l₁.length := by
  induction h with
  | nil => simp
  | cons x h ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [← mul_sub]
      simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
        mul_mem_pbwFiltrationPrevious_right (R := R) (L := L)
          (ι_mem_pbwFiltration_one R L x) ih
  | swap x y l => exact prod_map_ι_sub_swap_mem_pbwFiltrationPrevious R L y x l
  | trans h₁ _ ih₁ ih₂ =>
      rw [← h₁.length_eq] at ih₂
      simpa only [sub_add_sub_cancel] using
        (pbwFiltrationPrevious R L _).add_mem ih₁ ih₂

variable {ιIndex : Type w}

/-- The PBW monomial attached to a word of indices in a family `e : ιIndex → L`. No ordering or
linear-independence hypothesis on the family is needed. -/
def pbwMonomial (e : ιIndex → L) (word : List ιIndex) :
    _root_.UniversalEnvelopingAlgebra R L :=
  ((word.map e).map ⇑ι).prod

@[simp]
theorem pbwMonomial_nil (e : ιIndex → L) : pbwMonomial R L e [] = 1 := by
  simp [pbwMonomial]

@[simp]
theorem pbwMonomial_cons (e : ιIndex → L) (i : ιIndex) (word : List ιIndex) :
    pbwMonomial R L e (i :: word) = ι (e i) * pbwMonomial R L e word := by
  simp [pbwMonomial]

/-- A PBW monomial is the product of the corresponding canonical Lie generators. -/
theorem pbwMonomial_def (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word = ((word.map e).map ⇑ι).prod := by
  induction word with
  | nil => exact pbwMonomial_nil R L e
  | cons i word ih => simp only [pbwMonomial_cons, List.map_cons, List.prod_cons, ih]

section Map

variable (S : Type u) [CommRing S]
variable {A : Type v} {B : Type x}
variable [LieRing A] [LieAlgebra S A]
variable [LieRing B] [LieAlgebra S B]

/-- An induced enveloping-algebra map applies the Lie homomorphism to every factor of a PBW
monomial. -/
@[simp]
theorem map_pbwMonomial (f : LieHom S A B) (e : ιIndex → A) (word : List ιIndex) :
    map S f (pbwMonomial S A e word) = pbwMonomial S B (fun i ↦ f (e i)) word := by
  rw [pbwMonomial_def, pbwMonomial_def, map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  exact map_ι S f (e i)

end Map

@[simp]
theorem pbwMonomial_append (e : ιIndex → L) (word₁ word₂ : List ιIndex) :
    pbwMonomial R L e (word₁ ++ word₂) =
      pbwMonomial R L e word₁ * pbwMonomial R L e word₂ := by
  simp [pbwMonomial]

/-- A PBW monomial belongs to the filtration step given by the length of its word. -/
theorem pbwMonomial_mem_pbwFiltration (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word ∈ pbwFiltration R L word.length := by
  rw [pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_mem_pbwFiltration R L (l := word.map e) (by simp)

/-- Permuted words in any indexed family give PBW monomials with the same leading term. -/
theorem pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm
    (e : ιIndex → L) {word₁ word₂ : List ιIndex} (h : word₁.Perm word₂) :
    pbwMonomial R L e word₁ - pbwMonomial R L e word₂ ∈
      pbwFiltrationPrevious R L word₁.length := by
  rw [pbwMonomial_def, pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L (h.map e)

/-- Sorting the indices of a PBW monomial by a decidable relation preserves its leading term. This
is the form used to span the associated graded by ordered monomials. -/
theorem pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
    (r : ιIndex → ιIndex → Prop) [DecidableRel r] (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word - pbwMonomial R L e (word.insertionSort r) ∈
      pbwFiltrationPrevious R L word.length :=
  pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm R L e
    (List.perm_insertionSort r word).symm

/-- Relabelling the indices of an exponent vector along an order embedding relabels its ordered
PBW monomial. -/
theorem pbwMonomial_sort_toMultiset_mapDomain {ι₁ ι₂ : Type*} [LinearOrder ι₁]
    [LinearOrder ι₂] (g : ι₁ ↪o ι₂) (e : ι₂ → L) (n : ι₁ →₀ ℕ) :
    pbwMonomial R L e ((n.mapDomain g).toMultiset.sort (· ≤ ·)) =
      pbwMonomial R L (e ∘ g) (n.toMultiset.sort (· ≤ ·)) := by
  rw [← Finsupp.toMultiset_map, ← Multiset.map_sort g n.toMultiset (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ ↦ g.le_iff_le.symm)]
  simp only [pbwMonomial_def, List.map_map, Function.comp_def]

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0461

section TAF_LiteralSource_0462
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Evaluation -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Evaluation of the PBW polynomial representation

The polynomial representation attached to an ordered basis of a Lie algebra gives a linear map
from its enveloping algebra to polynomials by applying an operator to `1`. An ordered word of
basis vectors evaluates to the monomial with exactly those multiplicities. This normalization
identifies the ordered PBW basis with the usual polynomial monomials as modules.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace Module.Basis

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Apply the PBW polynomial representation of the enveloping algebra to the constant `1`. -/
noncomputable def pbwEval : _root_.UniversalEnvelopingAlgebra R L →ₗ[R] MvPolynomial ι R :=
  LinearMap.applyₗ (1 : MvPolynomial ι R) ∘ₗ
    (_root_.UniversalEnvelopingAlgebra.lift R b.pbwPolynomialRep).toLinearMap

@[simp]
theorem pbwEval_one : b.pbwEval 1 = 1 := by
  simp [pbwEval]

/-- Left multiplication by a generator becomes its action on polynomials. -/
theorem pbwEval_ι_mul (x : L) (a : _root_.UniversalEnvelopingAlgebra R L) :
    b.pbwEval (_root_.UniversalEnvelopingAlgebra.ι R x * a) =
      b.pbwPolynomialRep x (b.pbwEval a) := by
  simp [pbwEval]

/-- An ordered word evaluates to the polynomial monomial with the same multiplicities. -/
theorem pbwEval_pbwMonomial {word : List ι} (hword : word.Pairwise (· ≤ ·)) :
    b.pbwEval (pbwMonomial R L b word) = monomial (Multiset.toFinsupp (word : Multiset ι)) 1 := by
  induction word with
  | nil => simp [Multiset.toFinsupp_zero]
  | cons i word ih =>
      obtain ⟨hle, htail⟩ := List.pairwise_cons.1 hword
      rw [pbwMonomial_cons, pbwEval_ι_mul, ih htail,
        pbwPolynomialRep_basis_monomial_of_le b 1 (fun j hj ↦ hle j (by simpa using hj))]
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton, X, monomial_mul_monomial, one_mul]

end Module.Basis
end
end TAF_LiteralSource_0462

section TAF_LiteralSource_0463
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Ordered monomials span the PBW filtration

Let `e : ι → L` be a linearly ordered spanning family of a Lie algebra. This file proves that the
degree-`k` Poincaré--Birkhoff--Witt filtration of `UniversalEnvelopingAlgebra R L` is spanned by the
monomials

```text
ι(e(i₁)) ⋯ ι(e(iₙ)),    i₁ ≤ ⋯ ≤ iₙ,    n ≤ k.
```

There are two steps. First, `span_prod_map_eq_wordFiltration` expands arbitrary Lie-algebra words in
the spanning family. Second, sorting a word in that family changes it only by a term in the
preceding filtration step, by
`pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`. Induction on the filtration degree then
absorbs this error into shorter ordered monomials.

For an arbitrary Lie homomorphism, the induced enveloping-algebra map sends the ordered monomials
in a family, and their span, exactly onto those for the image family.

This is the spanning half of the PBW basis theorem; linear independence of the ordered monomials is
not proved here.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.orderedPBWMonomials`: the ordered monomials of length at
  most a specified degree.
* `TauCeti.UniversalEnvelopingAlgebra.map_span_orderedPBWMonomials`: induced maps carry their
  spans onto the spans of the corresponding image-family monomials.
* `TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`: these monomials
  span exactly the corresponding PBW filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.span_iUnion_orderedPBWMonomials_eq_top`: all ordered monomials
  span the universal enveloping algebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section OrderedWords

variable {ι : Type w} [LE ι] (e : ι → L)

/-- Ordered PBW monomials in a family indexed by an ordered type, of word length at most `k`. -/
def orderedPBWMonomials (k : ℕ) : Set U :=
  {a | ∃ word : List ι,
    word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a}

/-- Membership in `orderedPBWMonomials`, in terms of an ordered word of family indices. -/
@[simp]
theorem mem_orderedPBWMonomials_iff {k : ℕ} {a : U} :
    a ∈ orderedPBWMonomials R L e k ↔
      ∃ word : List ι,
        word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a :=
  Iff.rfl

/-- An ordered family word of length at most `k` gives an ordered PBW monomial of degree at most
`k`. -/
theorem pbwMonomial_mem_orderedPBWMonomials {k : ℕ} {word : List ι}
    (hsorted : word.Pairwise (· ≤ ·)) (hword : word.length ≤ k) :
    pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
  ⟨word, hsorted, hword, rfl⟩

/-- Increasing the degree bound enlarges the set of ordered PBW monomials. -/
theorem orderedPBWMonomials_mono : Monotone (orderedPBWMonomials R L e) := by
  intro i j hij a
  rintro ⟨word, hsorted, hlength, rfl⟩
  exact ⟨word, hsorted, hlength.trans hij, rfl⟩

/-- Every ordered PBW monomial of degree at most `k` lies in the `k`-th PBW filtration step. -/
theorem orderedPBWMonomials_subset_pbwFiltration (k : ℕ) :
    orderedPBWMonomials R L e k ⊆ pbwFiltration R L k := by
  rintro a ⟨word, -, hword, rfl⟩
  exact (pbwFiltration_mono R L hword) (pbwMonomial_mem_pbwFiltration R L e word)

/-- The only ordered PBW monomial of degree zero is the empty monomial `1`. -/
@[simp]
theorem orderedPBWMonomials_zero : orderedPBWMonomials R L e 0 = {1} := by
  ext a
  constructor
  · rintro ⟨word, -, hword, rfl⟩
    rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hword), pbwMonomial_nil]
    exact Set.mem_singleton 1
  · rintro rfl
    exact ⟨[], List.Pairwise.nil, le_rfl, pbwMonomial_nil R L e⟩

end OrderedWords

section Map

variable {M : Type x} [LieRing M] [LieAlgebra R M]
variable {ι : Type w} [LE ι]

/-- An induced enveloping-algebra map sends the ordered monomials in a family exactly to the
ordered monomials in its image family. This statement does not require the Lie map or the family
to be surjective. -/
@[simp]
theorem image_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    map R f '' orderedPBWMonomials R L e k =
      orderedPBWMonomials R M (fun i ↦ f (e i)) k := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [mem_orderedPBWMonomials_iff] at hb ⊢
    obtain ⟨word, hordered, hlength, rfl⟩ := hb
    exact ⟨word, hordered, hlength, (map_pbwMonomial R f e word).symm⟩
  · rw [mem_orderedPBWMonomials_iff]
    rintro ⟨word, hordered, hlength, rfl⟩
    have hsource : pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
      (mem_orderedPBWMonomials_iff R L e).2 ⟨word, hordered, hlength, rfl⟩
    exact ⟨pbwMonomial R L e word, hsource, map_pbwMonomial R f e word⟩

/-- The induced enveloping-algebra map carries the span of the ordered monomials in a family
onto the span of the corresponding ordered monomials in its image family. -/
@[simp]
theorem map_span_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    (Submodule.span R (orderedPBWMonomials R L e k)).map (map R f).toLinearMap =
      Submodule.span R (orderedPBWMonomials R M (fun i ↦ f (e i)) k) := by
  rw [Submodule.map_span, AlgHom.coe_toLinearMap, image_orderedPBWMonomials R L f e k]

end Map

section Spanning

variable {ι : Type w} [LinearOrder ι] (e : ι → L)

/-- **Ordered PBW monomials span the PBW filtration.** For a linearly ordered spanning family `e`
in `L`, the monomials in nondecreasing family elements of length at most `k` span precisely
filtration degree `k` of `UniversalEnvelopingAlgebra R L`.

This is the spanning half of PBW. The reverse information needed for a basis is linear independence,
which comes from identifying the associated graded algebra with `SymmetricAlgebra R L`. -/
theorem span_orderedPBWMonomials_eq_pbwFiltration
    (he : Submodule.span R (Set.range e) = ⊤) (k : ℕ) :
    Submodule.span R (orderedPBWMonomials R L e k) = pbwFiltration R L k := by
  refine le_antisymm (Submodule.span_le.mpr
    (orderedPBWMonomials_subset_pbwFiltration R L e k)) ?_
  induction k with
  | zero =>
      rw [pbwFiltration_zero, orderedPBWMonomials_zero, Submodule.one_le]
      exact Submodule.subset_span (Set.mem_singleton 1)
  | succ k ih =>
      -- Expand arbitrary generator words in the spanning family, then sort the resulting words.
      have hfiltration : TauCeti.Algebra.wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (k + 1) =
          pbwFiltration R L (k + 1) := by
        rw [TauCeti.Algebra.wordFiltration_eq_pow, pbwFiltration_eq_pow]
      rw [← hfiltration, ← TauCeti.Algebra.span_prod_map_eq_wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap e he (k + 1),
        Submodule.span_le]
      rintro a ⟨word, hword, rfl⟩
      have hp :
          (word.map fun i ↦
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (e i)).prod =
            pbwMonomial R L e word := by
        rw [pbwMonomial_def]
        simp only [List.map_map, Function.comp_def, LieHom.coe_toLinearMap]
      rw [hp]
      let sorted := word.insertionSort (· ≤ ·)
      have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
      have hlength : sorted.length ≤ k + 1 := by
        simpa [sorted] using hword
      have hsorted_mem : pbwMonomial R L e sorted ∈
          Submodule.span R (orderedPBWMonomials R L e (k + 1)) :=
        Submodule.subset_span
          (pbwMonomial_mem_orderedPBWMonomials R L e hsorted hlength)
      cases word with
      | nil =>
          simpa [sorted] using hsorted_mem
      | cons head tail =>
          have htail : tail.length ≤ k := by simpa using hword
          have hdiff :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                pbwFiltration R L tail.length := by
            have h := pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
              R L (· ≤ ·) e (head :: tail)
            rw [List.length_cons, pbwFiltrationPrevious_succ] at h
            exact h
          have hdiff' :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                Submodule.span R (orderedPBWMonomials R L e (k + 1)) := by
            have hdiffk := pbwFiltration_mono R L htail hdiff
            exact Submodule.span_mono (orderedPBWMonomials_mono R L e (Nat.le_succ k))
              (ih hdiffk)
          rw [← sub_add_cancel (pbwMonomial R L e (head :: tail))
            (pbwMonomial R L e sorted)]
          exact Submodule.add_mem _ hdiff' hsorted_mem

/-- The ordered PBW monomials in a linearly ordered spanning family span the whole universal
enveloping algebra. -/
theorem span_iUnion_orderedPBWMonomials_eq_top
    (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R (⋃ k, orderedPBWMonomials R L e k) = ⊤ := by
  rw [Submodule.span_iUnion]
  simp_rw [span_orderedPBWMonomials_eq_pbwFiltration R L e he]
  exact iSup_pbwFiltration_eq_top R L

end Spanning

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0463

