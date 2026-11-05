module
public import FourPapers.Homological.Complete
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Relation
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Deterministically consolidated Characterizations proof sources.
The exact source-block correspondence is audit/mathematical_assembly.json.
Generation alone is not a successful Lean check. -/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Source: Characterizations.ExchangeGraph -/
section CheckedCharacterizationsSource0

/-! # Unit-exchange paths in coordinate boxes

All vertices are actual nonnegative integer exponent vectors. A box path is
the ordinary finite reflexive-transitive closure of unit exchanges inside the
specified family and coordinate box.
-/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def UnitStep (a b : Exponent V) : Prop :=
  ∃ i j, i ≠ j ∧ 0 < a i ∧ b = exchange a i j

theorem UnitStep.symm {a b : Exponent V} (h : UnitStep a b) : UnitStep b a := by
  obtain ⟨i, j, hij, hi, rfl⟩ := h
  refine ⟨j, i, hij.symm, ?_, (exchange_inverse hij hi).symm⟩
  simp only [exchange_apply, if_neg hij.symm, ite_true]
  omega

def BoxStep (B : Family V) (C a b : Exponent V) : Prop :=
  a ∈ B ∧ b ∈ B ∧ a ≤ C ∧ b ≤ C ∧ UnitStep a b

def BoxConnected (B : Family V) : Prop :=
  ∀ C a, a ∈ B → a ≤ C → ∀ b, b ∈ B → b ≤ C →
    Relation.ReflTransGen (BoxStep B C) a b

def l1Distance (a b : Exponent V) : ℕ := (a - b).degree + (b - a).degree

def DonorGood (B : Family V) (C : Exponent V) (j : V) (a : Exponent V) : Prop :=
  ∃ i, i ≠ j ∧ 0 < a j ∧ exchange a j i ∈ B ∧ exchange a j i ≤ C

theorem step_preserves_top_coordinate {B : Family V} {C a b : Exponent V} {j : V}
    (hab : BoxStep B C a b) (haj : a j = C j) (hbad : ¬ DonorGood B C j a) :
    b j = C j := by
  obtain ⟨ha, hb, haC, hbC, p, q, hpq, hp, rfl⟩ := hab
  have hpj : p ≠ j := by
    intro he
    subst p
    exact hbad ⟨q, hpq.symm, hp, hb, hbC⟩
  have hqj : q ≠ j := by
    intro he
    subst q
    have hh := hbC j
    simp only [exchange_apply, if_neg hpj.symm, ite_true] at hh
    omega
  simpa only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, Nat.sub_zero,
    Nat.add_zero] using haj

theorem first_good_boundary {B : Family V} {C a b : Exponent V} {j : V}
    (hpath : Relation.ReflTransGen (BoxStep B C) a b)
    (haj : a j = C j) (hbad : ¬ DonorGood B C j a) (hbj : b j < C j) :
    ∃ c c', BoxStep B C c c' ∧ c j = C j ∧
      ¬ DonorGood B C j c ∧ DonorGood B C j c' := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | @head a c hac hcb ih =>
    by_cases hc : DonorGood B C j c
    · exact ⟨a, c, hac, haj, hbad, hc⟩
    · exact ih (step_preserves_top_coordinate hac haj hbad) hc

theorem two_exchanges_cancel (c : Exponent V) {p q j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j) (hp : 0 < c p) :
    exchange (exchange c p q) j p = exchange c j q := by
  ext x
  simp only [exchange_apply]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
    simp_all <;> omega

theorem two_exchanges_distance (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) (hp : 0 < c p) (hj : 0 < c j) :
    l1Distance c (exchange (exchange c p q) j i) = 4 := by
  have hsub : c - exchange (exchange c p q) j i =
      Finsupp.single p 1 + Finsupp.single j 1 := by
    ext x
    simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega
  have hsub' : exchange (exchange c p q) j i - c =
      Finsupp.single q 1 + Finsupp.single i 1 := by
    ext x
    simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega
  simp [l1Distance, hsub, hsub']

theorem exchange_le_of_two_exchanges {C c : Exponent V} {p q i j : V}
    (hc : c ≤ C) (hu : exchange (exchange c p q) j i ≤ C)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) :
    exchange c j i ≤ C ∧ exchange c j q ≤ C := by
  constructor <;> intro x
  all_goals
    have hcx := hc x
    have hux := hu x
    simp only [exchange_apply] at hux ⊢
    by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm] <;> omega

/-- The exact configuration found at the first vertex where the prescribed
donor can be decreased. The two receiving coordinates may initially coincide. -/
theorem failed_exchange_configuration {B : Family V} (hconn : BoxConnected B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧
      ∃ p q i j : V, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ i ≠ p ∧ i ≠ j ∧
        0 < c p ∧ 0 < c j ∧ u = exchange (exchange c p q) j i ∧
        exchange c j i ∉ B ∧ exchange c j q ∉ B := by
  classical
  simp only [ExchangeAxiom, not_forall] at hfail
  obtain ⟨b, hb, a, ha, j, haj, hnone⟩ := hfail
  simp only [not_exists, not_and] at hnone
  let C := a ⊔ b
  have hbj : b j = C j := by simp only [C, Finsupp.sup_apply]; omega
  have hajC : a j < C j := by rw [← hbj]; exact haj
  have hbad : ¬ DonorGood B C j b := by
    rintro ⟨i, hij, hj, hex, heC⟩
    have hi := heC i
    simp only [exchange_apply, if_neg hij, ite_true, C, Finsupp.sup_apply] at hi
    exact hnone i (by omega) hex
  obtain ⟨c, c', hstep, hcj, hbadc, hgood⟩ :=
    first_good_boundary (hconn C b hb le_sup_right a ha le_sup_left) hbj hbad hajC
  obtain ⟨hc, hc', hcC, hc'C, p, q, hpq, hp, he⟩ := hstep
  subst c'
  have hpj : p ≠ j := by
    intro he
    subst p
    exact hbadc ⟨q, hpq.symm, hp, hc', hc'C⟩
  have hqj : q ≠ j := by
    intro he
    subst q
    have hh := hc'C j
    simp only [exchange_apply, if_neg hpj.symm, ite_true] at hh
    omega
  obtain ⟨i, hij, hj', hu, huC⟩ := hgood
  have hj : 0 < c j := by
    simpa only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm,
      Nat.sub_zero, Nat.add_zero] using hj'
  have hip : i ≠ p := by
    intro he
    subst i
    rw [two_exchanges_cancel c hpq hpj hqj hp] at hu huC
    exact hbadc ⟨q, hqj, hj, hu, huC⟩
  obtain ⟨hiC, hqC⟩ := exchange_le_of_two_exchanges hcC huC hpq hpj hqj hip hij
  exact ⟨c, exchange (exchange c p q) j i, hc, hu, p, q, i, j,
    hpq, hpj, hqj, hip, hij, hp, hj, rfl,
    fun h => hbadc ⟨i, hij, hj, h, hiC⟩,
    fun h => hbadc ⟨q, hqj, hj, h, hqC⟩⟩

/-- Lemma 3.2: failure of exchange is witnessed at ℓ₁-distance exactly four. -/
theorem failed_exchange_distance_four {B : Family V} (hconn : BoxConnected B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧ l1Distance c u = 4 ∧
      ∃ j, u j < c j ∧ ∀ i, c i < u i → exchange c j i ∉ B := by
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij,
    hp, hj, rfl, hni, hnq⟩ := failed_exchange_configuration hconn hfail
  refine ⟨c, _, hc, hu, two_exchanges_distance c hpq hpj hqj hip hij hp hj, j, ?_, ?_⟩
  · simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm,
      if_neg hij.symm, ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  · intro x hx
    by_cases hxi : x = i
    · simpa [hxi] using hni
    by_cases hxq : x = q
    · simpa [hxq] using hnq
    simp only [exchange_apply, if_neg hxi, if_neg hxq, Nat.add_zero] at hx
    split_ifs at hx <;> omega

end Characterizations

end
end CheckedCharacterizationsSource0

/-! ## Source: Characterizations.Quotients -/
section CheckedCharacterizationsSource1

/-! # Literal colon ideals and the combinatorial variable-witness condition -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev GeneratorOrder (V : Type*) := Exponent V → Exponent V → Prop

def preceding (B : Family V) (r : GeneratorOrder V) (b : Exponent V) : Family V :=
  B.filter (fun a => r a b)

@[simp] theorem mem_preceding (B : Family V) (r : GeneratorOrder V) (a b : Exponent V) :
    a ∈ preceding B r b ↔ a ∈ B ∧ r a b := by simp [preceding]

def QuotientWitness (B : Family V) (r : GeneratorOrder V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, r a b →
    ∃ w ∈ B, r w b ∧ ∃ i, w - b = Finsupp.single i 1 ∧ b i < a i

def HasLinearQuotients (k : Type*) [CommSemiring k]
    (B : Family V) (r : GeneratorOrder V) : Prop :=
  ∀ b ∈ B, ∃ D : Finset V,
    (monomialIdeal k (preceding B r b)).colon {MvPolynomial.monomial b (1 : k)} =
      variableIdeal (k := k) D

theorem sub_single_le_add {w b : Exponent V} {i : V}
    (h : w - b = Finsupp.single i 1) : w ≤ b + Finsupp.single i 1 := by
  intro x
  have hx := congrArg (fun a : Exponent V => a x) h
  simp only [Finsupp.tsub_apply, Finsupp.add_apply] at hx ⊢
  omega

theorem sub_single_receiver {w b : Exponent V} {i : V}
    (h : w - b = Finsupp.single i 1) : w i = b i + 1 := by
  have hx := congrArg (fun a : Exponent V => a i) h
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hx
  omega

theorem sub_single_of_le_add {w b : Exponent V} {i : V}
    (hle : w ≤ b + Finsupp.single i 1) (hn : ¬ w ≤ b) :
    w - b = Finsupp.single i 1 := by
  have hi : b i < w i := by
    by_contra hi
    apply hn
    intro x
    by_cases hx : x = i
    · subst x; omega
    · have hh := hle x
      simpa [Finsupp.single_apply, hx, Ne.symm hx] using hh
  ext x
  have hh := hle x
  by_cases hx : x = i
  · subst x
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.add_apply] at hh ⊢
    omega
  · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply,
      if_neg hx, if_neg (Ne.symm hx), Nat.add_zero] at hh ⊢
    omega

theorem witness_of_linearQuotients {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (hL : HasLinearQuotients k B r) : QuotientWitness B r := by
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro a ha b hb hab
  obtain ⟨D, hD⟩ := hL b hb
  have hratio : MvPolynomial.monomial (a - b) (1 : k) ∈
      (monomialIdeal k (preceding B r b)).colon {MvPolynomial.monomial b 1} := by
    rw [mem_monomialIdeal_colon_iff]
    intro x hx
    have he : x = a - b := by simpa [eq_comm] using hx
    subst x
    exact ⟨a, (mem_preceding _ _ _ _).mpr ⟨ha, hab⟩, by
      intro i
      simp only [Finsupp.tsub_apply, Finsupp.add_apply]
      omega⟩
  rw [hD, mem_variableIdeal_iff] at hratio
  obtain ⟨i, hiD, hi⟩ := hratio (a - b) (by simp)
  have hvar : MvPolynomial.X i ∈ variableIdeal (k := k) D :=
    Ideal.subset_span ⟨i, hiD, rfl⟩
  rw [← hD, mem_monomialIdeal_colon_iff] at hvar
  obtain ⟨w, hw, hwb⟩ := hvar (Finsupp.single i 1) (by simp [MvPolynomial.X])
  obtain ⟨hwB, hwr⟩ := (mem_preceding _ _ _ _).mp hw
  have hnot : ¬ w ≤ b := by
    intro hle
    have he := hB w hwB b hb hle
    exact hirr b (he ▸ hwr)
  refine ⟨w, hwB, hwr, i, sub_single_of_le_add (by simpa [add_comm] using hwb) hnot, ?_⟩
  simp only [Finsupp.tsub_apply] at hi
  omega

def witnessVariables (B : Family V) (r : GeneratorOrder V) (b : Exponent V) : Finset V :=
  univ.filter (fun i => ∃ w ∈ B, r w b ∧ w - b = Finsupp.single i 1)

theorem linearQuotients_of_witness {k : Type*} [CommSemiring k]
    {B : Family V} {r : GeneratorOrder V} (hW : QuotientWitness B r) :
    HasLinearQuotients k B r := by
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro b hb
  refine ⟨witnessVariables B r b, ?_⟩
  ext f
  rw [mem_monomialIdeal_colon_iff, mem_variableIdeal_iff]
  have he (a : Exponent V) : Contains (preceding B r b) (a + b) ↔
      ∃ i ∈ witnessVariables B r b, 0 < a i := by
    constructor
    · rintro ⟨c, hc, hca⟩
      obtain ⟨hcB, hcr⟩ := (mem_preceding _ _ _ _).mp hc
      obtain ⟨w, hw, hwr, i, hwb, hi⟩ := hW c hcB b hb hcr
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, w, hw, hwr, hwb⟩, ?_⟩
      have hh := hca i
      simp only [Finsupp.add_apply] at hh
      omega
    · rintro ⟨i, hi, hai⟩
      obtain ⟨w, hw, hwr, hwb⟩ := (mem_filter.mp hi).2
      refine ⟨w, (mem_preceding _ _ _ _).mpr ⟨hw, hwr⟩, ?_⟩
      have hle := sub_single_le_add hwb
      intro x
      have hh := hle x
      by_cases hx : x = i
      · subst x
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hh ⊢
        omega
      · simp [Finsupp.single_apply, hx, Ne.symm hx] at hh
        simp only [Finsupp.add_apply]
        omega
  simp_rw [he]

theorem linearQuotients_iff_witness {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a) :
    HasLinearQuotients k B r ↔ QuotientWitness B r :=
  ⟨witness_of_linearQuotients hB hirr, linearQuotients_of_witness⟩

theorem witness_is_exchange {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {w b : Exponent V} (hw : w ∈ B) (hb : b ∈ B) {i : V}
    (h : w - b = Finsupp.single i 1) :
    ∃ j, i ≠ j ∧ 0 < b j ∧ w = exchange b j i := by
  have hi := sub_single_receiver h
  obtain ⟨j, hj⟩ := exists_surplus ((hB w hw).trans (hB b hb).symm) (show b i < w i by omega)
  have hij : i ≠ j := by intro he; subst j; omega
  have hle : w ≤ exchange b j i := by
    have hwb := sub_single_le_add h
    intro x
    have hh := hwb x
    by_cases hxi : x = i
    · subst x
      simp only [exchange_apply, if_neg hij, ite_true, Nat.sub_zero]
      omega
    by_cases hxj : x = j
    · subst x
      simp only [exchange_apply, ite_true, if_neg hij.symm, Nat.add_zero]
      omega
    · simpa [exchange_apply, hxi, hxj, Finsupp.single_apply,
        Ne.symm hxi] using hh
  exact ⟨j, hij, by omega, eq_of_le_of_degree_eq hle
    ((hB w hw).trans ((exchange_degree b j i (by omega)).trans (hB b hb)).symm)⟩

end Characterizations

end
end CheckedCharacterizationsSource1

/-! ## Source: Characterizations.WitnessPaths -/
section CheckedCharacterizationsSource2

/-! # Linear-quotient witnesses connect every coordinate box -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem preceding_card_lt {B : Family V} {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {a b : Exponent V} (ha : a ∈ B) (hab : r a b) :
    (preceding B r a).card < (preceding B r b).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxB, hxa⟩ := (mem_preceding _ _ _ _).mp hx
    exact (mem_preceding _ _ _ _).mpr ⟨hxB, htrans hxa hab⟩
  · intro he
    have haa : a ∈ preceding B r a := he ▸ (mem_preceding _ _ _ _).mpr ⟨ha, hab⟩
    exact hirr a ((mem_preceding _ _ _ _).mp haa).2

theorem witness_le_sup {a b w : Exponent V} {i : V}
    (hwb : w - b = Finsupp.single i 1) (hai : b i < a i) : w ≤ a ⊔ b := by
  have hh := sub_single_le_add hwb
  intro x
  have hx := hh x
  by_cases hxi : x = i
  · subst x
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.sup_apply] at hx ⊢
    omega
  · simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg hxi,
      if_neg (Ne.symm hxi), Nat.add_zero, Finsupp.sup_apply] at hx ⊢
    omega

/-- A direct finite descent proof. It uses the literal colon witness and so
works without assuming the desired exchange axiom. -/
theorem boxConnected_of_witness {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hW : QuotientWitness B r) : BoxConnected B := by
  intro C a ha haC b hb hbC
  generalize hm : (preceding B r a).card + (preceding B r b).card = m
  induction m using Nat.strong_induction_on generalizing a b with
  | h m ih =>
    by_cases he : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    rcases htotal a b he with hab | hba
    · obtain ⟨w, hw, hwb, i, hwi, hai⟩ := hW a ha b hb hab
      have hwC : w ≤ C := (witness_le_sup hwi hai).trans (sup_le haC hbC)
      obtain ⟨j, hij, hbj, hew⟩ := witness_is_exchange hB hw hb hwi
      have hlt := preceding_card_lt hirr htrans hw hwb
      have hpath := ih ((preceding B r a).card + (preceding B r w).card)
        (by omega) a ha haC w hw hwC rfl
      exact hpath.tail ⟨hw, hb, hwC, hbC, (show UnitStep b w from
        ⟨j, i, hij.symm, hbj, hew⟩).symm⟩
    · obtain ⟨w, hw, hwa, i, hwi, hbi⟩ := hW b hb a ha hba
      have hwC : w ≤ C := (witness_le_sup hwi hbi).trans (sup_le hbC haC)
      obtain ⟨j, hij, haj, hew⟩ := witness_is_exchange hB hw ha hwi
      have hlt := preceding_card_lt hirr htrans hw hwa
      have hpath := ih ((preceding B r w).card + (preceding B r b).card)
        (by omega) w hw hwC b hb hbC rfl
      exact hpath.head ⟨ha, hw, haC, hwC, j, i, hij.symm, haj, hew⟩

theorem boxConnected_of_linearQuotients {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a) (hL : HasLinearQuotients k B r) :
    BoxConnected B :=
  boxConnected_of_witness hB hirr htrans htotal
    (witness_of_linearQuotients hB.antichain hirr hL)

end Characterizations

end
end CheckedCharacterizationsSource2

/-! ## Source: Characterizations.FourObstruction -/
section CheckedCharacterizationsSource3

/-! # The four-coordinate exchange obstruction -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def SingletonExchange (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ i,
    (∀ h, b h < a h ↔ h = i) → ∀ j, a j < b j → exchange b j i ∈ B

theorem exchange_mem_donor_pos {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {c : Exponent V} (hc : c ∈ B) {i j : V} (hex : exchange c i j ∈ B) : 0 < c i := by
  by_contra hi
  have hz : c i = 0 := by omega
  have hsub : c - Finsupp.single i 1 = c := by
    ext x
    by_cases hx : x = i
    · subst x; simp [hz]
    · simp [Finsupp.single_apply, hx, Ne.symm hx]
  have hd := hB (exchange c i j) hex
  simp only [exchange, hsub, map_add, Finsupp.degree_single, hB c hc] at hd
  omega

theorem two_exchanges_unique_receiver (c : Exponent V) {p i j : V}
    (hpi : p ≠ i) (hpj : p ≠ j) (hij : i ≠ j) (h : V) :
    c h < exchange (exchange c p i) j i h ↔ h = i := by
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhi : h = i <;> by_cases hhj : h = j <;>
    simp_all [eq_comm] <;> omega

theorem two_exchanges_against_receiver_swap (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) (hiq : i ≠ q) (hq : 0 < c q) (h : V) :
    exchange c q i h < exchange (exchange c p q) j i h ↔ h = q := by
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhq : h = q <;>
    by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all [eq_comm] <;> omega

theorem two_exchanges_commute (c : Exponent V) {p q i j : V}
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hip : i ≠ p) (hij : i ≠ j) :
    exchange (exchange c p q) j i = exchange (exchange c p i) j q := by
  ext h
  simp only [exchange_apply]
  by_cases hhp : h = p <;> by_cases hhq : h = q <;>
    by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all [eq_comm] <;> omega

/-- Lemma 3.5, with all nonnegativity obligations explicit and discharged.
The two additional missing swaps are actual exponent-vector nonmembership. -/
theorem four_coordinate_obstruction {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hconn : BoxConnected B) (hsingle : SingletonExchange B)
    (hfail : ¬ ExchangeAxiom B) :
    ∃ c u : Exponent V, c ∈ B ∧ u ∈ B ∧
      ∃ p q i j : V, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ i ≠ p ∧ i ≠ j ∧ i ≠ q ∧
        0 < c p ∧ 0 < c j ∧ u = exchange (exchange c p q) j i ∧
        exchange c j i ∉ B ∧ exchange c j q ∉ B ∧
        exchange c q i ∉ B ∧ exchange c i q ∉ B := by
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hp, hj, he, hni, hnq⟩ :=
    failed_exchange_configuration hconn hfail
  subst u
  have hjdrop : exchange (exchange c p q) j i j < c j := by
    simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
      ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  have hiq : i ≠ q := by
    intro he
    subst q
    exact hni (hsingle _ hu c hc i (two_exchanges_unique_receiver c hpq hpj hij) j hjdrop)
  have hnoSwap (p q i j : V) (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
      (hip : i ≠ p) (hij : i ≠ j) (hiq : i ≠ q) (hj : 0 < c j)
      (hu : exchange (exchange c p q) j i ∈ B)
      (hni : exchange c j i ∉ B) : exchange c q i ∉ B := by
    intro hv
    have hq := exchange_mem_donor_pos hB hc hv
    have hdrop : exchange (exchange c p q) j i j < exchange c q i j := by
      simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
        ite_true, Nat.sub_zero, Nat.add_zero]
      omega
    have hh := hsingle _ hu _ hv q
      (two_exchanges_against_receiver_swap c hpq hpj hqj hip hij hiq hq) j hdrop
    rw [two_exchanges_cancel c hiq.symm hqj hij hq] at hh
    exact hni hh
  have hqi := hnoSwap p q i j hpq hpj hqj hip hij hiq hj hu hni
  have hiq' := hnoSwap p i q j hip.symm hpj hij hpq.symm hqj hiq.symm hj
    (by rwa [← two_exchanges_commute c hpq hpj hqj hip hij]) hnq
  exact ⟨c, _, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, rfl, hni, hnq, hqi, hiq'⟩

end Characterizations

end
end CheckedCharacterizationsSource3

/-! ## Source: Characterizations.VariableOrders -/
section CheckedCharacterizationsSource4

/-! # Variable permutations and pure reverse lexicographic tests -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev VariableOrder (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

def variableLinearOrder (o : VariableOrder V) : LinearOrder V :=
  LinearOrder.lift' o o.injective

def variableRevlex (o : VariableOrder V) (a b : Exponent V) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, o i < o j → a j = b j

theorem variableRevlex_irrefl (o : VariableOrder V) (a : Exponent V) :
    ¬ variableRevlex o a a := by rintro ⟨i, hi, _⟩; exact (lt_irrefl _ hi)

theorem variableRevlex_trans (o : VariableOrder V) {a b c : Exponent V}
    (hab : variableRevlex o a b) (hbc : variableRevlex o b c) : variableRevlex o a c := by
  letI := variableLinearOrder o
  exact revlexBefore_trans hab hbc

theorem variableRevlex_total (o : VariableOrder V) (a b : Exponent V) (hab : a ≠ b) :
    variableRevlex o a b ∨ variableRevlex o b a := by
  letI := variableLinearOrder o
  exact revlexBefore_total hab

theorem variableRevlex_exchange (o : VariableOrder V) (b : Exponent V) {i j : V}
    (hji : o j < o i) (hi : 0 < b i) : variableRevlex o (exchange b i j) b := by
  letI := variableLinearOrder o
  exact exchange_revlexBefore b hji hi

theorem variableRevlex_exchange_iff (o : VariableOrder V) (b : Exponent V) {i j : V}
    (hij : i ≠ j) (hi : 0 < b i) :
    variableRevlex o (exchange b i j) b ↔ o j < o i := by
  refine ⟨?_, fun h => variableRevlex_exchange o b h hi⟩
  rintro ⟨x, hx, he⟩
  have hxi : x = i := by
    by_contra hxi
    simp only [exchange_apply, if_neg hxi, Nat.sub_zero] at hx
    split_ifs at hx <;> omega
  subst x
  by_contra hji
  have hlt : o i < o j := lt_of_le_of_ne (le_of_not_gt hji) (fun h => hij (o.injective h))
  have hh := he j hlt
  simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero] at hh
  omega

theorem polymatroidal_variable_linearQuotients {k : Type*} [CommSemiring k]
    {B : Family V} (hB : ExchangeAxiom B) (o : VariableOrder V) :
    HasLinearQuotients k B (variableRevlex o) := by
  letI := variableLinearOrder o
  intro b hb
  exact ⟨revlexColonVariables B b, revlex_colon_eq_variableIdeal hB hb⟩

def FinalPair (o : VariableOrder V) (i j : V) : Prop :=
  o i < o j ∧ ∀ h, h ≠ i → h ≠ j → o h < o i

def FinalTriple (o : VariableOrder V) (i q j : V) : Prop :=
  o i < o j ∧ o q < o j ∧
    ∀ h, h ≠ i → h ≠ q → h ≠ j → o h < o i ∧ o h < o q

def CoversFinalPairs (F : Set (VariableOrder V)) : Prop :=
  ∀ i j, i ≠ j → ∃ o ∈ F, FinalPair o i j

def CoversFinalTriples (F : Set (VariableOrder V)) : Prop :=
  ∀ i q j, i ≠ q → i ≠ j → q ≠ j → ∃ o ∈ F, FinalTriple o i q j

theorem FinalPair.no_after {o : VariableOrder V} {i j : V} (hF : FinalPair o i j) (h : V) :
    ¬ o j < o h := by
  intro hlt
  by_cases hhi : h = i
  · subst h; exact (not_lt_of_gt hF.1) hlt
  by_cases hhj : h = j
  · subst h; exact (lt_irrefl _ hlt)
  exact (lt_irrefl _ (hlt.trans ((hF.2 h hhi hhj).trans hF.1)))

theorem FinalTriple.no_after {o : VariableOrder V} {i q j : V}
    (hF : FinalTriple o i q j) (h : V) : ¬ o j < o h := by
  intro hlt
  by_cases hhi : h = i
  · subst h; exact (not_lt_of_gt hF.1) hlt
  by_cases hhq : h = q
  · subst h; exact (not_lt_of_gt hF.2.1) hlt
  by_cases hhj : h = j
  · subst h; exact (lt_irrefl _ hlt)
  exact (lt_irrefl _ (hlt.trans (((hF.2.2 h hhi hhq hhj).1).trans hF.1)))

/-- Lemma 3.4: final-pair orders force every prescribed single-receiver exchange. -/
theorem singletonExchange_of_finalPairs {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (F : Set (VariableOrder V))
    (hF : CoversFinalPairs F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : SingletonExchange B := by
  intro a ha b hb i hi j hj
  have hij : i ≠ j := by
    intro he
    subst j
    have hh := (hi i).mpr rfl
    omega
  obtain ⟨o, ho, hp⟩ := hF i j hij
  have hab : variableRevlex o a b :=
    ⟨j, hj, fun x hx => False.elim (hp.no_after x hx)⟩
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ :=
    witness_of_linearQuotients hB.antichain (variableRevlex_irrefl o) (hL o ho) a ha b hb hab
  have hzi : z = i := (hi z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange hB hw hb hwz
  have horder : o i < o t :=
    (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    exact (not_lt_of_gt (hp.2 t hit.symm htj)) horder
  simpa [hew, htj] using hw

/-- Theorem 3.6: the exact final-pair and final-triple patterns suffice. -/
theorem exchange_of_order_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (F : Set (VariableOrder V))
    (hne : F.Nonempty) (hpairs : CoversFinalPairs F) (htriples : CoversFinalTriples F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : ExchangeAxiom B := by
  obtain ⟨o₀, ho₀⟩ := hne
  have hconn := boxConnected_of_linearQuotients hB (variableRevlex_irrefl o₀)
    (fun {_ _ _} => variableRevlex_trans o₀) (variableRevlex_total o₀) (hL o₀ ho₀)
  have hsingle := singletonExchange_of_finalPairs hB F hpairs hL
  by_contra hfail
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, he, hni, hnq, hnqi, hniq⟩ := four_coordinate_obstruction hB hconn hsingle hfail
  subst u
  obtain ⟨o, ho, hfinal⟩ := htriples i q j hiq hij hqj
  have huc : variableRevlex o (exchange (exchange c p q) j i) c := by
    refine ⟨j, ?_, fun x hx => False.elim (hfinal.no_after x hx)⟩
    simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
      ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  obtain ⟨w, hw, hwc, z, hwz, hcz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) _ hu c hc huc
  have hziq : z = i ∨ z = q := by
    by_contra hz
    push_neg at hz
    simp only [exchange_apply, if_neg hz.1, if_neg hz.2, Nat.add_zero] at hcz
    split_ifs at hcz <;> omega
  obtain ⟨t, hzt, ht, hew⟩ := witness_is_exchange hB hw hc hwz
  have horder : o z < o t :=
    (variableRevlex_exchange_iff o c hzt.symm ht).mp (hew ▸ hwc)
  rcases hziq with rfl | rfl
  · by_cases htj : t = j
    · exact hni (by simpa [hew, htj] using hw)
    by_cases htq : t = q
    · exact hnqi (by simpa [hew, htq] using hw)
    exact (not_lt_of_gt (hfinal.2.2 t hzt.symm htq htj).1) horder
  · by_cases htj : t = j
    · exact hnq (by simpa [hew, htj] using hw)
    by_cases hti : t = i
    · exact hniq (by simpa [hew, hti] using hw)
    exact (not_lt_of_gt (hfinal.2.2 t hti hzt.symm htj).2) horder

end Characterizations

end
end CheckedCharacterizationsSource4

/-! ## Source: Characterizations.OrderExistence -/
section CheckedCharacterizationsSource5

/-! # Actual variable permutations with specified final patterns -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_order_refining (f : V → ℕ) :
    ∃ o : VariableOrder V, ∀ a b, f a < f b → o a < o b := by
  let e := Fintype.equivFin V
  let key : V → Lex (ℕ × Fin (Fintype.card V)) := fun a => toLex (f a, e a)
  have hk : Function.Injective key := by
    intro a b h
    exact e.injective (congrArg (fun z => (ofLex z).2) h)
  letI : LinearOrder V := LinearOrder.lift' key hk
  let o : V ≃o Fin (Fintype.card V) := (Fintype.orderIsoFinOfCardEq V rfl).symm
  refine ⟨o.toEquiv, ?_⟩
  intro a b hab
  apply o.strictMono
  change key a < key b
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

theorem exists_finalPair (i j : V) (hij : i ≠ j) :
    ∃ o : VariableOrder V, FinalPair o i j := by
  let f : V → ℕ := fun h => if h = j then 2 else if h = i then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  refine ⟨o, ho i j (by simp [f, hij]), ?_⟩
  intro h hhi hhj
  apply ho
  simp [f, hhi, hhj, hij]

theorem exists_finalTriple (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    ∃ o : VariableOrder V, FinalTriple o i q j := by
  let f : V → ℕ := fun h => if h = j then 2 else if h = i ∨ h = q then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  refine ⟨o, ho i j (by simp [f, hij]), ho q j (by simp [f, hqj]), ?_⟩
  intro h hhi hhq hhj
  constructor <;> apply ho <;> simp [f, hhi, hhq, hhj, hij, hqj]

/-- The complete universal reverse-lexicographic characterization, stated
with actual polynomial colon ideals over every nontrivial coefficient semiring. -/
theorem polymatroidal_iff_universal_revlex {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    IsPolymatroidal B ↔ ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) := by
  constructor
  · intro h o
    exact polymatroidal_variable_linearQuotients h.2 o
  · intro h
    refine ⟨⟨d, hB⟩, ?_⟩
    apply exchange_of_order_coverage (k := k) hB Set.univ
      ⟨Fintype.equivFin V, Set.mem_univ _⟩
    · intro i j hij
      obtain ⟨o, ho⟩ := exists_finalPair i j hij
      exact ⟨o, Set.mem_univ _, ho⟩
    · intro i q j hiq hij hqj
      obtain ⟨o, ho⟩ := exists_finalTriple i q j hiq hij hqj
      exact ⟨o, Set.mem_univ _, ho⟩
    · intro o ho
      exact h o

end Characterizations

end
end CheckedCharacterizationsSource5

/-! ## Source: Characterizations.PureDegree -/
section CheckedCharacterizationsSource6

/-! # Universal pure reverse lexicographic quotients force one degree -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def boxFamily (B : Family V) (C : Exponent V) : Family V := B.filter (· ≤ C)

@[simp] theorem mem_boxFamily (B : Family V) (C a : Exponent V) :
    a ∈ boxFamily B C ↔ a ∈ B ∧ a ≤ C := by simp [boxFamily]

theorem antichain_boxFamily {B : Family V} (hB : Antichain B) (C : Exponent V) :
    Antichain (boxFamily B C) := fun a ha b hb hab =>
  hB a ((mem_boxFamily _ _ _).mp ha).1 b ((mem_boxFamily _ _ _).mp hb).1 hab

theorem witness_boxFamily {B : Family V} {r : GeneratorOrder V}
    (hW : QuotientWitness B r) (C : Exponent V) : QuotientWitness (boxFamily B C) r := by
  intro a ha b hb hab
  obtain ⟨haB, haC⟩ := (mem_boxFamily _ _ _).mp ha
  obtain ⟨hbB, hbC⟩ := (mem_boxFamily _ _ _).mp hb
  obtain ⟨w, hw, hwr, i, hwi, hai⟩ := hW a haB b hbB hab
  exact ⟨w, (mem_boxFamily _ _ _).mpr ⟨hw, (witness_le_sup hwi hai).trans
    (sup_le haC hbC)⟩, hwr, i, hwi, hai⟩

/-- Lemma 3.8, expressed with ordinary polynomial colon ideals. -/
theorem linearQuotients_boxFamily {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (hL : HasLinearQuotients k B r) (C : Exponent V) :
    HasLinearQuotients k (boxFamily B C) r :=
  linearQuotients_of_witness (witness_boxFamily (witness_of_linearQuotients hB hirr hL) C)

theorem witness_degree_le {B : Family V} (hB : Antichain B)
    {w b : Exponent V} (hw : w ∈ B) (hb : b ∈ B) {i : V}
    (h : w - b = Finsupp.single i 1) : w.degree ≤ b.degree := by
  have hle := sub_single_le_add h
  have hd := degree_mono hle
  simp only [map_add, Finsupp.degree_single] at hd
  by_contra hbad
  have heq : w.degree = (b + Finsupp.single i 1).degree := by
    simp only [map_add, Finsupp.degree_single]
    omega
  have hwEq := eq_of_le_of_degree_eq hle heq
  have hbEq := hB b hb w hw (hwEq ▸ le_add_right le_rfl)
  have hwi := sub_single_receiver h
  rw [hbEq] at hwi
  omega

/-- Lemma 3.7: the first generator has the least total degree. -/
theorem first_generator_minimum_degree {B : Family V} (hB : Antichain B)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a) (hW : QuotientWitness B r)
    (a : Exponent V) (ha : a ∈ B) (hfirst : ∀ b ∈ B, ¬ r b a) :
    ∀ b ∈ B, a.degree ≤ b.degree := by
  intro b hb
  generalize hm : (preceding B r b).card = m
  induction m using Nat.strong_induction_on generalizing b with
  | h m ih =>
    by_cases he : a = b
    · subst b; exact le_rfl
    have hab : r a b := (htotal a b he).resolve_right (hfirst b hb)
    obtain ⟨w, hw, hwr, i, hwi, _⟩ := hW a ha b hb hab
    have hlt := preceding_card_lt hirr htrans hw hwr
    exact (ih _ (by omega) w hw rfl).trans (witness_degree_le hB hw hb hwi)

theorem exists_first_generator {B : Family V} (hne : B.Nonempty)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c) :
    ∃ a ∈ B, ∀ b ∈ B, ¬ r b a := by
  obtain ⟨a, ha, hmin⟩ := B.exists_min_image (fun b => (preceding B r b).card) hne
  refine ⟨a, ha, ?_⟩
  intro b hb hba
  exact (not_lt_of_ge (hmin b hb)) (preceding_card_lt hirr htrans hb hba)

def LastVariable (o : VariableOrder V) (i : V) : Prop := ∀ j, j ≠ i → o j < o i

theorem exists_lastVariable (i : V) : ∃ o : VariableOrder V, LastVariable o i := by
  obtain ⟨o, ho⟩ := exists_order_refining (fun j : V => if j = i then 1 else 0)
  exact ⟨o, fun j hji => ho j i (by simp [hji])⟩

/-- Lemma 3.9. The selected last-variable orders need not be the same orders
for different variables, and no degree hypothesis is assumed. -/
theorem equigenerated_of_lastVariable_tests {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hne : B.Nonempty) (hB : Antichain B)
    (hL : ∀ i : V, ∃ o : VariableOrder V, LastVariable o i ∧
      HasLinearQuotients k B (variableRevlex o)) : ∃ d, Equigenerated B d := by
  obtain ⟨a₀, ha₀, hmin⟩ := B.exists_min_image Finsupp.degree hne
  let d := a₀.degree
  refine ⟨d, ?_⟩
  intro b hb
  have hdb : d ≤ b.degree := hmin b hb
  by_contra hbd
  have hbd' : d < b.degree := by omega
  let D := B.filter (fun a => a.degree = d)
  have hD : D.Nonempty := ⟨a₀, mem_filter.mpr ⟨ha₀, rfl⟩⟩
  obtain ⟨a, haD, hdelta⟩ := D.exists_min_image (fun a => (a - b).degree) hD
  obtain ⟨ha, had⟩ := mem_filter.mp haD
  have hnot : ¬ a ≤ b := by
    intro hab
    have he := hB a ha b hb hab
    have hh := congrArg Finsupp.degree he
    omega
  obtain ⟨i, hi⟩ : ∃ i, b i < a i := by
    change ¬ ∀ i, a i ≤ b i at hnot
    simpa only [not_forall, not_le] using hnot
  let C := a ⊔ b
  have haC : a ∈ boxFamily B C := (mem_boxFamily _ _ _).mpr ⟨ha, le_sup_left⟩
  have hbC : b ∈ boxFamily B C := (mem_boxFamily _ _ _).mpr ⟨hb, le_sup_right⟩
  have hfix {a' : Exponent V} (ha' : a' ∈ boxFamily B C) (hd' : a'.degree = d) : a' i = a i := by
    obtain ⟨ha'B, ha'C⟩ := (mem_boxFamily _ _ _).mp ha'
    have hle : a' - b ≤ a - b := by
      intro x
      have hh := ha'C x
      simp only [C, Finsupp.sup_apply, Finsupp.tsub_apply] at hh ⊢
      omega
    have hdeg : (a' - b).degree = (a - b).degree :=
      le_antisymm (degree_mono hle) (hdelta a' (mem_filter.mpr ⟨ha'B, hd'⟩))
    have he := congrArg (fun c : Exponent V => c i) (eq_of_le_of_degree_eq hle hdeg)
    simp only [Finsupp.tsub_apply] at he
    omega
  obtain ⟨o, holast, hoL⟩ := hL i
  have hW := witness_boxFamily (witness_of_linearQuotients hB (variableRevlex_irrefl o) hoL) C
  obtain ⟨w, hw, hfirst⟩ := exists_first_generator ⟨a, haC⟩ (variableRevlex_irrefl o)
    (fun {_ _ _} => variableRevlex_trans o)
  have hwd : w.degree = d := by
    have hlo := hmin w ((mem_boxFamily _ _ _).mp hw).1
    have hhi := first_generator_minimum_degree (antichain_boxFamily hB C)
      (variableRevlex_irrefl o) (fun {_ _ _} => variableRevlex_trans o)
      (variableRevlex_total o) hW w hw hfirst a haC
    omega
  apply hfirst b hbC
  refine ⟨i, ?_, ?_⟩
  · rw [hfix hw hwd]
    exact hi
  · intro j hij
    by_cases hji : j = i
    · subst j; exact (lt_irrefl _ hij).elim
    · exact (not_lt_of_gt (holast j hji) hij).elim

/-- Corollary 3.10: universal pure reverse-lexicographic quotients characterize
polymatroidality without any equigeneration assumption. -/
theorem polymatroidal_iff_universal_pure_revlex {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) :
    IsPolymatroidal B ↔ ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) := by
  constructor
  · intro h o
    exact polymatroidal_variable_linearQuotients h.2 o
  · intro h
    by_cases hne : B.Nonempty
    · obtain ⟨d, hd⟩ := equigenerated_of_lastVariable_tests (k := k) hne hB (fun i => by
        obtain ⟨o, ho⟩ := exists_lastVariable i
        exact ⟨o, ho, h o⟩)
      exact (polymatroidal_iff_universal_revlex hd).mpr h
    · have hzero : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst B
      exact ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩

end Characterizations

end
end CheckedCharacterizationsSource6

/-! ## Source: Characterizations.BoundedFamilies -/
section CheckedCharacterizationsSource7

/-! # Capped Veronese families and deletion of one generator -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def boundedFamily (d : ℕ) (W : Finset V) : Family V :=
  (Finsupp.finite_of_degree_eq (σ := V) d).toFinset.filter (fun a => ∀ i ∈ W, a i ≤ 1)

@[simp] theorem mem_boundedFamily (d : ℕ) (W : Finset V) (a : Exponent V) :
    a ∈ boundedFamily d W ↔ a.degree = d ∧ ∀ i ∈ W, a i ≤ 1 := by
  simp [boundedFamily]

def deletedBounded (d : ℕ) (W : Finset V) (h : Exponent V) : Family V :=
  (boundedFamily d W).erase h

@[simp] theorem mem_deletedBounded (d : ℕ) (W : Finset V) (h a : Exponent V) :
    a ∈ deletedBounded d W h ↔ a ≠ h ∧ a.degree = d ∧ ∀ i ∈ W, a i ≤ 1 := by
  simp [deletedBounded]

theorem boundedFamily_equigenerated (d : ℕ) (W : Finset V) :
    Equigenerated (boundedFamily d W) d := fun a ha => ((mem_boundedFamily _ _ _).mp ha).1

theorem deletedBounded_equigenerated (d : ℕ) (W : Finset V) (h : Exponent V) :
    Equigenerated (deletedBounded d W h) d := fun a ha => ((mem_deletedBounded _ _ _ _).mp ha).2.1

theorem boundedFamily_exchange {d : ℕ} {W : Finset V} {a b : Exponent V}
    (ha : a ∈ boundedFamily d W) (hb : b ∈ boundedFamily d W)
    {p q : V} (hp : a p < b p) (hq : b q < a q) :
    exchange b p q ∈ boundedFamily d W := by
  obtain ⟨had, hac⟩ := (mem_boundedFamily _ _ _).mp ha
  obtain ⟨hbd, hbc⟩ := (mem_boundedFamily _ _ _).mp hb
  have hpq : p ≠ q := by intro h; subst q; omega
  apply (mem_boundedFamily _ _ _).mpr
  refine ⟨(exchange_degree b p q (by omega)).trans hbd, ?_⟩
  intro x hx
  have hbx := hbc x hx
  by_cases hxq : x = q
  · subst x
    have haq := hac q hx
    simp only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero]
    omega
  · simp only [exchange_apply, if_neg hxq, Nat.add_zero]
    split_ifs <;> omega

theorem exchange_sub_self (b : Exponent V) {p q : V} (hpq : p ≠ q) :
    exchange b p q - b = Finsupp.single q 1 := by
  ext x
  simp only [Finsupp.tsub_apply, exchange_apply, Finsupp.single_apply]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> simp_all [eq_comm] <;> omega

theorem exchange_receiver_injective (b : Exponent V) (p : V) :
    Function.Injective (exchange b p) := by
  intro i j he
  by_contra hij
  have hh := congrArg (fun a : Exponent V => a i) he
  simp only [exchange_apply, ite_true, if_neg hij] at hh
  omega

theorem exchange_eq_of_unique_receiver {a b : Exponent V} {p q : V}
    (hdeg : a.degree = b.degree) (hp : a p < b p)
    (hq : a q = b q + 1) (hunique : ∀ i, b i < a i → i = q) :
    a = exchange b p q := by
  have hpq : p ≠ q := by intro he; subst q; omega
  apply eq_of_le_of_degree_eq
  · intro x
    by_cases hxp : x = p
    · subst x
      simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero]
      omega
    by_cases hxq : x = q
    · subst x
      simp only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero]
      exact hq.le
    have hx : a x ≤ b x := by
      by_contra hx
      exact hxq (hunique x (by omega))
    simpa [exchange_apply, hxp, hxq] using hx
  · exact hdeg.trans (exchange_degree b p q (by omega)).symm

/-- Any failed prescribed exchange after one deletion has one receiving
coordinate, and both donor and receiver lie outside the saturated caps. -/
theorem deletedBounded_failed_exchange {d : ℕ} {W : Finset V} {h a b : Exponent V}
    (hsat : ∀ i ∈ W, h i = 1)
    (ha : a ∈ deletedBounded d W h) (hb : b ∈ deletedBounded d W h)
    {p : V} (hp : a p < b p)
    (hbad : ∀ q, b q < a q → exchange b p q ∉ deletedBounded d W h) :
    ∃ q, (∀ i, b i < a i ↔ i = q) ∧ p ≠ q ∧ p ∉ W ∧ q ∉ W ∧
      0 < h q ∧ exchange b p q = h ∧ b = exchange h q p := by
  obtain ⟨han, had, hac⟩ := (mem_deletedBounded _ _ _ _).mp ha
  obtain ⟨hbn, hbd, hbc⟩ := (mem_deletedBounded _ _ _ _).mp hb
  obtain ⟨q, hq⟩ := exists_surplus (hbd.trans had.symm) hp
  have hpq : p ≠ q := by intro he; subst q; omega
  have heq (i : V) (hi : b i < a i) : exchange b p i = h := by
    have hfull := boundedFamily_exchange ((mem_boundedFamily _ _ _).mpr ⟨had, hac⟩)
      ((mem_boundedFamily _ _ _).mpr ⟨hbd, hbc⟩) hp hi
    by_contra he
    exact hbad i hi (mem_erase.mpr ⟨he, hfull⟩)
  have huniq (i : V) (hi : b i < a i) : i = q :=
    exchange_receiver_injective b p ((heq i hi).trans (heq q hq).symm)
  have hpW : p ∉ W := by
    intro hpW
    have hh := congrArg (fun a : Exponent V => a p) (heq q hq)
    have hbp := hbc p hpW
    simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero, hsat p hpW] at hh
    omega
  have hhq : h q = b q + 1 := by
    have hh := congrArg (fun a : Exponent V => a q) (heq q hq)
    simpa only [exchange_apply, if_neg hpq.symm, ite_true, Nat.sub_zero] using hh.symm
  have hqW : q ∉ W := by
    intro hqW
    have haq := hac q hqW
    have he : a q = b q + 1 := by omega
    exact han ((exchange_eq_of_unique_receiver (had.trans hbd.symm) hp he huniq).trans (heq q hq))
  refine ⟨q, fun i => ⟨huniq i, fun he => he ▸ hq⟩, hpq, hpW, hqW,
    by omega, heq q hq, ?_⟩
  rw [← heq q hq, exchange_inverse hpq (by omega)]

/-- Lemma 4.6 in a slightly stronger form: the removed exponent can be
arbitrary off the capped coordinates. -/
theorem deletedBounded_linearQuotients_last {k : Type*} [CommSemiring k]
    (d : ℕ) (W : Finset V) (h : Exponent V) (hsat : ∀ i ∈ W, h i = 1)
    (o : VariableOrder V) (w : V) (hw : w ∈ W) (hlast : LastVariable o w) :
    HasLinearQuotients k (deletedBounded d W h) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨han, had, hac⟩ := (mem_deletedBounded _ _ _ _).mp ha
  obtain ⟨hbn, hbd, hbc⟩ := (mem_deletedBounded _ _ _ _).mp hb
  obtain ⟨p, hp, hafter⟩ := hab
  obtain ⟨q, hq⟩ := exists_surplus (hbd.trans had.symm) hp
  have hpq : p ≠ q := by intro he; subst q; omega
  have hqp : o q < o p := by
    rcases lt_trichotomy (o q) (o p) with h | h | h
    · exact h
    · exact (hpq (o.injective h).symm).elim
    · have hh := hafter q h
      omega
  have hfull := boundedFamily_exchange ((mem_boundedFamily _ _ _).mpr ⟨had, hac⟩)
    ((mem_boundedFamily _ _ _).mpr ⟨hbd, hbc⟩) hp hq
  by_cases he : exchange b p q = h
  · have hpw : p ≠ w := by
      intro hpw
      subst p
      have hh := congrArg (fun a : Exponent V => a w) he
      have hbw := hbc w hw
      simp only [exchange_apply, ite_true, if_neg hpq, Nat.add_zero, hsat w hw] at hh
      omega
    have hqw : q ≠ w := by
      intro hqw
      subst q
      exact (not_lt_of_gt (hlast p hpw)) hqp
    have hbw : b w = 1 := by
      have hh := congrArg (fun a : Exponent V => a w) he
      simpa only [exchange_apply, if_neg hpw.symm, if_neg hqw.symm,
        Nat.sub_zero, Nat.add_zero, hsat w hw] using hh
    have hnew : exchange b w q ∈ boundedFamily d W := by
      apply (mem_boundedFamily _ _ _).mpr
      refine ⟨(exchange_degree b w q (by omega)).trans hbd, ?_⟩
      intro x hx
      have hbx := hbc x hx
      by_cases hxq : x = q
      · subst x
        have haq := hac q hx
        simp only [exchange_apply, if_neg hqw, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hxq, Nat.add_zero]
        split_ifs <;> omega
    have hne : exchange b w q ≠ h := by
      intro hew
      have hh := congrArg (fun a : Exponent V => a w) hew
      simp [hbw, hqw.symm, hsat w hw] at hh
    exact ⟨exchange b w q, mem_erase.mpr ⟨hne, hnew⟩,
      variableRevlex_exchange o b (hlast q hqw) (by omega), q,
      exchange_sub_self b hqw.symm, hq⟩
  · exact ⟨exchange b p q, mem_erase.mpr ⟨he, hfull⟩,
      variableRevlex_exchange o b hqp (by omega), q, exchange_sub_self b hpq, hq⟩

end Characterizations

end
end CheckedCharacterizationsSource7

/-! ## Source: Characterizations.Localization -/
section CheckedCharacterizationsSource8

/-! # Literal monomial localization in the retained-variable polynomial ring -/

noncomputable section

namespace Characterizations

open CommAlg.Polymatroid
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def restrictExponent (U : Finset V) (a : Exponent V) : Exponent U :=
  a.subtypeDomain (· ∈ U)

@[simp] theorem restrictExponent_apply (U : Finset V) (a : Exponent V) (i : U) :
    restrictExponent U a i = a i := rfl

def extendExponent (U : Finset V) (a : Exponent U) : Exponent V := a.extendDomain

@[simp] theorem extendExponent_apply (U : Finset V) (a : Exponent U) (i : V) :
    extendExponent U a i = if hi : i ∈ U then a ⟨i, hi⟩ else 0 := by
  simp [extendExponent, Finsupp.extendDomain_apply]

@[simp] theorem restrict_extend (U : Finset V) (a : Exponent U) :
    restrictExponent U (extendExponent U a) = a := by
  ext i
  simp

@[simp] theorem extend_restrict (U : Finset V) (a : Exponent V) :
    extendExponent U (restrictExponent U a) = project U a := by
  ext i
  by_cases hi : i ∈ U <;> simp [hi]

theorem extendExponent_le_iff (U : Finset V) (a b : Exponent U) :
    extendExponent U a ≤ extendExponent U b ↔ a ≤ b := by
  constructor
  · intro h i
    simpa using h i
  · intro h i
    by_cases hi : i ∈ U
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi]

def extendExponentEmbedding (U : Finset V) : Exponent U ↪o Exponent V :=
  OrderEmbedding.ofMapLEIff (extendExponent U) (extendExponent_le_iff U)

theorem restrictExponent_degree (U : Finset V) (a : Exponent V) :
    (restrictExponent U a).degree = subsetSum a U := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.sum_coe_sort U (fun i => a i)

theorem extendExponent_degree (U : Finset V) (a : Exponent U) :
    (extendExponent U a).degree = a.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [extendExponent_apply]
  rw [← Finset.sum_attach_eq_sum_dite U (fun i => a i)]
  rfl

def localFamily (B : Family V) (U : Finset V) : Family U :=
  minimalFamily (B.image (restrictExponent U))

theorem localFamily_antichain (B : Family V) (U : Finset V) : Antichain (localFamily B U) :=
  minimalFamily_antichain _

theorem localFamily_nonempty {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    (localFamily B U).Nonempty := minimalFamily_nonempty (hB.image _)

theorem contains_localFamily (B : Family V) (U : Finset V) (a : Exponent U) :
    Contains (localFamily B U) a ↔ ∃ b ∈ B, restrictExponent U b ≤ a := by
  rw [localFamily, contains_minimalFamily]
  simp [Contains]

theorem contains_localize_iff (B : Family V) (U : Finset V) (a : Exponent V) :
    Contains (localize B U) a ↔ Contains (localFamily B U) (restrictExponent U a) := by
  rw [contains_localize, contains_localFamily]
  constructor
  · rintro ⟨b, hb, hba⟩
    refine ⟨b, hb, ?_⟩
    intro i
    simpa using hba i
  · rintro ⟨b, hb, hba⟩
    refine ⟨b, hb, ?_⟩
    intro i
    by_cases hi : i ∈ U
    · simpa [hi] using hba ⟨i, hi⟩
    · simp [hi]

theorem minimalFamily_image_orderEmbedding {W : Type*} [Fintype W] [DecidableEq W]
    (f : Exponent V ↪o Exponent W) (B : Family V) :
    minimalFamily (B.image f) = (minimalFamily B).image f := by
  ext a
  simp only [mem_minimalFamily, Finset.mem_image]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hmin⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    intro c hc hcb
    exact f.injective (hmin (f c) ⟨c, hc, rfl⟩ (f.monotone hcb))
  · rintro ⟨b, ⟨hb, hmin⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    rintro _ ⟨c, hc, rfl⟩ hcb
    exact congrArg f (hmin c hc (f.le_iff_le.mp hcb))

theorem localize_eq_extend_localFamily (B : Family V) (U : Finset V) :
    localize B U = (localFamily B U).image (extendExponent U) := by
  have h := minimalFamily_image_orderEmbedding (extendExponentEmbedding U)
    (B.image (restrictExponent U))
  simpa only [Finset.image_image, Function.comp_def, extendExponentEmbedding,
    OrderEmbedding.coe_ofMapLEIff, extend_restrict, localize, localFamily] using h

theorem locallyEquigenerated_iff (B : Family V) :
    LocallyEquigenerated B ↔ ∀ U, ∃ d, Equigenerated (localFamily B U) d := by
  constructor
  · intro h U
    obtain ⟨d, hd⟩ := h U
    refine ⟨d, ?_⟩
    intro a ha
    have he : extendExponent U a ∈ localize B U := by
      rw [localize_eq_extend_localFamily]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    simpa [extendExponent_degree] using hd _ he
  · intro h U
    obtain ⟨d, hd⟩ := h U
    refine ⟨d, ?_⟩
    intro a ha
    rw [localize_eq_extend_localFamily] at ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa [extendExponent_degree] using hd _ hb

variable (k : Type*) [CommSemiring k]

def localizationMap (U : Finset V) : MvPolynomial V k →ₐ[k] MvPolynomial U k :=
  MvPolynomial.aeval (fun i => if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ else 1)

@[simp] theorem localizationMap_X (U : Finset V) (i : V) :
    localizationMap k U (MvPolynomial.X i) =
      if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ else 1 := by simp [localizationMap]

theorem localizationMap_monomial (U : Finset V) (a : Exponent V) (c : k) :
    localizationMap k U (MvPolynomial.monomial a c) =
      MvPolynomial.monomial (restrictExponent U a) c := by
  classical
  rw [localizationMap, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [restrictExponent_apply]
  have he : (fun i : V => (if hi : i ∈ U then (MvPolynomial.X ⟨i, hi⟩ : MvPolynomial U k)
      else 1) ^ a i) = (fun i => if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ ^ a i else 1) := by
    funext i
    by_cases hi : i ∈ U <;> simp [hi]
  rw [he, ← Finset.prod_attach_eq_prod_dite U (fun i => MvPolynomial.X i ^ a i)]
  rfl

def monomialLocalization (I : Ideal (MvPolynomial V k)) (U : Finset V) :
    Ideal (MvPolynomial U k) := Ideal.map (localizationMap k U).toRingHom I

theorem monomialLocalization_eq (B : Family V) (U : Finset V) :
    monomialLocalization k (monomialIdeal k B) U = monomialIdeal k (localFamily B U) := by
  rw [monomialLocalization, localFamily, monomialIdeal_minimalFamily]
  simp only [monomialIdeal, Ideal.map_span, Set.image_image, Finset.coe_image]
  congr 1
  ext p
  simp only [Set.mem_image, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, localizationMap_monomial]

end Characterizations

end
end CheckedCharacterizationsSource8

/-! ## Source: Characterizations.Resolution.HomogeneousFree -/
section CheckedCharacterizationsSource9

/-! # Homogeneous maps and lifts between genuine finite free polynomial modules -/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqHomogeneousFree (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
namespace Characterizations.Resolution
open Classical Finset MvPolynomial
universe u v w
variable {V k : Type u} {J : Type v} {L : Type w} [CommRing k] [Fintype J] [Fintype L]

abbrev Polynomial := MvPolynomial V k
abbrev Free (J : Type v) := J → Polynomial (V := V) (k := k)

def IsHomogeneousVector (x : Free (V := V) (k := k) J) (d : ℕ) : Prop :=
  ∀ j, (x j).IsHomogeneous d

def component (d : ℕ) (x : Free (V := V) (k := k) J) : Free (V := V) (k := k) J :=
  fun j => homogeneousComponent d (x j)

lemma component_homogeneous (d : ℕ) (x : Free (V := V) (k := k) J) :
    IsHomogeneousVector (component d x) d :=
  fun j => homogeneousComponent_isHomogeneous d (x j)

lemma component_eq_self {x : Free (V := V) (k := k) J} {d : ℕ}
    (hx : IsHomogeneousVector x d) : component d x = x := by
  funext j
  exact homogeneousComponent_eq_self (hx j)

lemma component_mul_of_homogeneous {a : Polynomial (V := V) (k := k)} {r : ℕ}
    (ha : a.IsHomogeneous r) (b : Polynomial (V := V) (k := k)) (t : ℕ) :
    homogeneousComponent (r + t) (a * b) = a * homogeneousComponent t b := by
  induction b using MvPolynomial.induction_on' with
  | monomial e c =>
    have hb : (monomial e c : Polynomial (V := V) (k := k)).IsHomogeneous e.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (ha.mul hb), homogeneousComponent_of_mem hb]
    by_cases he : t = e.degree <;> simp [he]
  | add p q hp hq => simp [mul_add, map_add, hp, hq]

/-- All entries of the matrix of the actual polynomial-linear map have degree `r`. -/
def IsHomogeneousMap (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) (r : ℕ) : Prop :=
  ∀ a b, (f (Pi.single b 1) a).IsHomogeneous r

lemma linearMap_apply_eq_sum (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) (x : Free (V := V) (k := k) J) (a : L) :
    f x a = ∑ b, x b * f (Pi.single b 1) a := by
  have hx : x = ∑ b, x b • Pi.single b (1 : Polynomial (V := V) (k := k)) := by
    funext b
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

lemma homogeneousMap_component (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) {r : ℕ} (hf : IsHomogeneousMap f r)
    (x : Free (V := V) (k := k) J) (t : ℕ) :
    component (r + t) (f x) = f (component t x) := by
  funext a
  rw [component, linearMap_apply_eq_sum, map_sum, linearMap_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mul_comm (x b), component_mul_of_homogeneous (hf a b), mul_comm]
  rfl

lemma homogeneousMap_apply (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) {r t : ℕ} (hf : IsHomogeneousMap f r)
    {x : Free (V := V) (k := k) J} (hx : IsHomogeneousVector x t) :
    IsHomogeneousVector (f x) (r + t) := by
  have he : component (r + t) (f x) = f x := by
    rw [homogeneousMap_component f hf, component_eq_self hx]
  rw [← he]
  exact component_homogeneous _ _

/-- Exactness supplies a homogeneous preimage of the required degree, with no
assumption that a chosen ungraded lift happened to preserve degrees. -/
lemma exists_homogeneous_lift
    (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)] Free (V := V) (k := k) L)
    {r t : ℕ} (hf : IsHomogeneousMap f r)
    {y : Free (V := V) (k := k) L} (hy : IsHomogeneousVector y (r + t))
    (hmem : y ∈ LinearMap.range f) :
    ∃ x, IsHomogeneousVector x t ∧ f x = y := by
  obtain ⟨x, rfl⟩ := hmem
  refine ⟨component t x, component_homogeneous _ _, ?_⟩
  rw [← homogeneousMap_component f hf, component_eq_self hy]

end Characterizations.Resolution

end
end CheckedCharacterizationsSource9

/-! ## Source: Characterizations.Resolution.Basic -/
section CheckedCharacterizationsSource10

/-! # Actual linear free resolutions

The definition records a genuine exact augmented complex of finite free polynomial
modules. The grading condition is that every matrix entry of a differential is a
linear form, while the augmentation has degree `d`. It contains no homology or
Betti-vanishing assertion.
-/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqBasic (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical CategoryTheory CategoryTheory.Limits HomologicalComplex
open Resolution
universe u
variable {V k : Type u} [CommRing k]

structure LinearResolution (I : Ideal (MvPolynomial V k)) (d : ℕ) where
  Index : ℕ → Type
  finite : ∀ n, Fintype (Index n)
  differential : ∀ n, (Index (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (Index n → MvPolynomial V k)
  augmentation : (Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k] MvPolynomial V k
  augmentation_range : LinearMap.range augmentation = I
  exact_zero : LinearMap.range (differential 0) = LinearMap.ker augmentation
  exact_succ : ∀ n, LinearMap.range (differential (n + 1)) = LinearMap.ker (differential n)
  linear : ∀ n, letI := finite n; letI := finite (n + 1)
    IsHomogeneousMap (differential n) 1
  augmentation_homogeneous : ∀ b, (augmentation (Pi.single b 1)).IsHomogeneous d

attribute [instance] LinearResolution.finite

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)

lemma differential_comp (n : ℕ) :
    P.differential n ∘ₗ P.differential (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  change P.differential n (P.differential (n + 1) x) = 0
  apply LinearMap.mem_ker.mp
  rw [← P.exact_succ n]
  exact LinearMap.mem_range_self _ x

lemma augmentation_comp : P.augmentation ∘ₗ P.differential 0 = 0 := by
  apply LinearMap.ext
  intro x
  change P.augmentation (P.differential 0 x) = 0
  apply LinearMap.mem_ker.mp
  rw [← P.exact_zero]
  exact LinearMap.mem_range_self _ x

/-- The actual complex of finite free polynomial modules. -/
def complex : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (P.Index n → MvPolynomial V k))
    (fun n => ModuleCat.ofHom (P.differential n))
    (fun n => ModuleCat.hom_ext (P.differential_comp n))

@[simp] lemma complex_d (n : ℕ) : P.complex.d (n + 1) n = ModuleCat.ofHom (P.differential n) := by
  exact ChainComplex.of_d (fun j => ModuleCat.of (MvPolynomial V k) (P.Index j → MvPolynomial V k))
    (fun j => ModuleCat.ofHom (P.differential j)) n

/-- The augmentation takes values in the original ideal itself. -/
def augmentationToIdeal : (P.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k] I :=
  P.augmentation.codRestrict I (fun x => by
    exact Eq.mp (congrArg (fun J : Submodule (MvPolynomial V k) (MvPolynomial V k) =>
      P.augmentation x ∈ J) P.augmentation_range) (LinearMap.mem_range_self _ x))

lemma augmentationToIdeal_surjective : Function.Surjective P.augmentationToIdeal := by
  intro y
  have hy : y.val ∈ LinearMap.range P.augmentation := by
    rw [P.augmentation_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

lemma augmentationToIdeal_ker : LinearMap.ker P.augmentationToIdeal = LinearMap.ker P.augmentation := by
  ext x
  simp [augmentationToIdeal, LinearMap.mem_ker, Subtype.ext_iff]

lemma complex_exactAt_succ (n : ℕ) : P.complex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (ModuleCat.Hom.hom (P.complex.d ((n + 1) + 1) (n + 1))) =
    LinearMap.ker (ModuleCat.Hom.hom (P.complex.d (n + 1) n))
  rw [P.complex_d, P.complex_d]
  exact P.exact_succ n

/-- The conventional categorical projective resolution obtained from the concrete data. -/
def toProjectiveResolution : ProjectiveResolution (ModuleCat.of (MvPolynomial V k) I) where
  complex := P.complex
  projective n := by
    change Projective (ModuleCat.of (MvPolynomial V k) (P.Index n → MvPolynomial V k))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv P.complex _).symm
    ⟨ModuleCat.ofHom P.augmentationToIdeal, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun P.augmentation_comp x⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, ?_⟩
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range (ModuleCat.Hom.hom (P.complex.d 1 0)) = LinearMap.ker P.augmentationToIdeal
          rw [P.augmentationToIdeal_ker]
          rw [P.complex_d]
          exact P.exact_zero
        · exact (ModuleCat.epi_iff_surjective _).mpr P.augmentationToIdeal_surjective
      · exact P.complex.shape 0 0 (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact P.complex_exactAt_succ n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end LinearResolution

/-- Existence of an exact finite-free resolution with shifts `d + i`. -/
def HasLinearResolution (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ d, Nonempty (LinearResolution I d)

end Characterizations

end
end CheckedCharacterizationsSource10

/-! ## Source: Characterizations.Resolution.Lift -/
section CheckedCharacterizationsSource11

/-! # Homogeneous comparison maps for free resolutions -/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqLift (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]
variable {I J : Ideal (MvPolynomial V k)} {d : ℕ}

namespace LinearResolution

lemma augmentation_component (P : LinearResolution I d)
    (x : P.Index 0 → MvPolynomial V k) (t : ℕ) :
    homogeneousComponent (d + t) (P.augmentation x) = P.augmentation (component t x) := by
  let f : (P.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
      (Unit → MvPolynomial V k) := LinearMap.pi (fun _ => P.augmentation)
  have hf : IsHomogeneousMap f d := fun _ b => P.augmentation_homogeneous b
  exact congrFun (homogeneousMap_component f hf x t) ()

lemma homogeneous_augmentation_lift (P : LinearResolution I d)
    {y : MvPolynomial V k} (hy : y.IsHomogeneous (d + 1)) (hI : y ∈ I) :
    ∃ x, IsHomogeneousVector x 1 ∧ P.augmentation x = y := by
  have hmem : y ∈ LinearMap.range P.augmentation := by simpa only [P.augmentation_range] using hI
  obtain ⟨x, rfl⟩ := hmem
  refine ⟨component 1 x, component_homogeneous _ _, ?_⟩
  rw [← P.augmentation_component, homogeneousComponent_eq_self hy]

variable (Q : LinearResolution J 1) (P : LinearResolution I d)
    (g : MvPolynomial V k) (hg : g.IsHomogeneous d)
    (hmul : ∀ z ∈ J, g * z ∈ I)

def liftZeroImage (b : Q.Index 0) : P.Index 0 → MvPolynomial V k :=
  Classical.choose (P.homogeneous_augmentation_lift
    (hg.mul (Q.augmentation_homogeneous b))
    (hmul _ (by simpa only [← Q.augmentation_range] using
      LinearMap.mem_range_self Q.augmentation (Pi.single b 1))))

lemma liftZeroImage_spec (b : Q.Index 0) :
    IsHomogeneousVector (liftZeroImage Q P g hg hmul b) 1 ∧
      P.augmentation (liftZeroImage Q P g hg hmul b) = g * Q.augmentation (Pi.single b 1) :=
  by
    exact Classical.choose_spec (P.homogeneous_augmentation_lift
    (hg.mul (Q.augmentation_homogeneous b))
    (hmul _ (by simpa only [← Q.augmentation_range] using
      LinearMap.mem_range_self Q.augmentation (Pi.single b 1))))

def liftZero : (Q.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (P.Index 0 → MvPolynomial V k) :=
  (Pi.basisFun (MvPolynomial V k) (Q.Index 0)).constr (MvPolynomial V k)
    (liftZeroImage Q P g hg hmul)

lemma liftZero_apply_single (b : Q.Index 0) :
    liftZero Q P g hg hmul (Pi.single b 1) = liftZeroImage Q P g hg hmul b := by
  exact Module.Basis.constr_basis _ _ _ b

lemma liftZero_homogeneous : IsHomogeneousMap (liftZero Q P g hg hmul) 1 := by
  intro a b
  rw [liftZero_apply_single]
  exact (liftZeroImage_spec Q P g hg hmul b).1 a

lemma liftZero_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (liftZero Q P g hg hmul x) = g * Q.augmentation x := by
  have h : P.augmentation ∘ₗ liftZero Q P g hg hmul =
      (LinearMap.mulLeft (MvPolynomial V k) g) ∘ₗ Q.augmentation := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index 0)).ext
    intro b
    change P.augmentation (liftZero Q P g hg hmul (Pi.single b 1)) =
      g * Q.augmentation (Pi.single b 1)
    rw [liftZero_apply_single]
    exact (liftZeroImage_spec Q P g hg hmul b).2
  exact LinearMap.congr_fun h x

/-- One adjacent pair of genuine homogeneous comparison maps. -/
structure LiftPair (n : ℕ) where
  low : (Q.Index n → MvPolynomial V k) →ₗ[MvPolynomial V k] (P.Index n → MvPolynomial V k)
  high : (Q.Index (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (P.Index (n + 1) → MvPolynomial V k)
  low_homogeneous : IsHomogeneousMap low 1
  high_homogeneous : IsHomogeneousMap high 1
  comm : P.differential n ∘ₗ high = low ∘ₗ Q.differential n

def liftOneImage (b : Q.Index 1) : P.Index 1 → MvPolynomial V k :=
  Classical.choose (exists_homogeneous_lift (P.differential 0) (P.linear 0)
    (homogeneousMap_apply (liftZero Q P g hg hmul) (liftZero_homogeneous Q P g hg hmul)
      (Q.linear 0 · b)) (by
        rw [P.exact_zero]
        apply LinearMap.mem_ker.mpr
        rw [liftZero_aug]
        have hz := LinearMap.congr_fun Q.augmentation_comp (Pi.single b 1)
        change Q.augmentation (Q.differential 0 (Pi.single b 1)) = 0 at hz
        rw [hz, mul_zero]))

lemma liftOneImage_spec (b : Q.Index 1) :
    IsHomogeneousVector (liftOneImage Q P g hg hmul b) 1 ∧
      P.differential 0 (liftOneImage Q P g hg hmul b) =
        liftZero Q P g hg hmul (Q.differential 0 (Pi.single b 1)) := by
  exact Classical.choose_spec (exists_homogeneous_lift (P.differential 0) (P.linear 0)
    (homogeneousMap_apply (liftZero Q P g hg hmul) (liftZero_homogeneous Q P g hg hmul)
      (Q.linear 0 · b)) (by
        rw [P.exact_zero]
        apply LinearMap.mem_ker.mpr
        rw [liftZero_aug]
        have hz := LinearMap.congr_fun Q.augmentation_comp (Pi.single b 1)
        change Q.augmentation (Q.differential 0 (Pi.single b 1)) = 0 at hz
        rw [hz, mul_zero]))

def initialLiftPair : LiftPair Q P 0 where
  low := liftZero Q P g hg hmul
  high := (Pi.basisFun (MvPolynomial V k) (Q.Index 1)).constr (MvPolynomial V k)
    (liftOneImage Q P g hg hmul)
  low_homogeneous := liftZero_homogeneous Q P g hg hmul
  high_homogeneous := by
    intro a b
    change (((Pi.basisFun (MvPolynomial V k) (Q.Index 1)).constr (MvPolynomial V k)
      (liftOneImage Q P g hg hmul)) ((Pi.basisFun _ _) b) a).IsHomogeneous 1
    rw [Module.Basis.constr_basis]
    exact (liftOneImage_spec Q P g hg hmul b).1 a
  comm := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index 1)).ext
    intro b
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact (liftOneImage_spec Q P g hg hmul b).2

def nextLiftImage {n : ℕ} (A : LiftPair Q P n) (b : Q.Index (n + 2)) :
    P.Index (n + 2) → MvPolynomial V k :=
  Classical.choose (exists_homogeneous_lift (P.differential (n + 1)) (P.linear (n + 1))
    (homogeneousMap_apply A.high A.high_homogeneous (Q.linear (n + 1) · b)) (by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      change (P.differential n ∘ₗ A.high) (Q.differential (n + 1) (Pi.single b 1)) = 0
      rw [A.comm]
      change A.low ((Q.differential n ∘ₗ Q.differential (n + 1)) (Pi.single b 1)) = 0
      rw [Q.differential_comp]
      simp))

lemma nextLiftImage_spec {n : ℕ} (A : LiftPair Q P n) (b : Q.Index (n + 2)) :
    IsHomogeneousVector (nextLiftImage Q P A b) 1 ∧
      P.differential (n + 1) (nextLiftImage Q P A b) =
        A.high (Q.differential (n + 1) (Pi.single b 1)) := by
  exact Classical.choose_spec (exists_homogeneous_lift (P.differential (n + 1)) (P.linear (n + 1))
    (homogeneousMap_apply A.high A.high_homogeneous (Q.linear (n + 1) · b)) (by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      change (P.differential n ∘ₗ A.high) (Q.differential (n + 1) (Pi.single b 1)) = 0
      rw [A.comm]
      change A.low ((Q.differential n ∘ₗ Q.differential (n + 1)) (Pi.single b 1)) = 0
      rw [Q.differential_comp]
      simp))

def nextLiftPair {n : ℕ} (A : LiftPair Q P n) : LiftPair Q P (n + 1) where
  low := A.high
  high := (Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).constr (MvPolynomial V k)
    (nextLiftImage Q P A)
  low_homogeneous := A.high_homogeneous
  high_homogeneous := by
    intro a b
    change (((Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).constr (MvPolynomial V k)
      (nextLiftImage Q P A)) ((Pi.basisFun _ _) b) a).IsHomogeneous 1
    rw [Module.Basis.constr_basis]
    exact (nextLiftImage_spec Q P A b).1 a
  comm := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).ext
    intro b
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact (nextLiftImage_spec Q P A b).2

def liftPairs : ∀ n, LiftPair Q P n
  | 0 => initialLiftPair Q P g hg hmul
  | n + 1 => nextLiftPair Q P (liftPairs n)

/-- A homogeneous lift of multiplication by `g`, obtained from actual exactness. -/
def multiplicationLift (n : ℕ) :
    (Q.Index n → MvPolynomial V k) →ₗ[MvPolynomial V k] (P.Index n → MvPolynomial V k) :=
  (liftPairs Q P g hg hmul n).low

lemma multiplicationLift_homogeneous (n : ℕ) :
    IsHomogeneousMap (multiplicationLift Q P g hg hmul n) 1 :=
  (liftPairs Q P g hg hmul n).low_homogeneous

lemma multiplicationLift_comm (n : ℕ) :
    P.differential n ∘ₗ multiplicationLift Q P g hg hmul (n + 1) =
      multiplicationLift Q P g hg hmul n ∘ₗ Q.differential n :=
  (liftPairs Q P g hg hmul n).comm

lemma multiplicationLift_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (multiplicationLift Q P g hg hmul 0 x) = g * Q.augmentation x :=
  liftZero_aug Q P g hg hmul x

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource11

/-! ## Source: Characterizations.Resolution.Cone -/
section CheckedCharacterizationsSource12

/-! # The actual graded mapping cone for adjoining one generator -/

noncomputable section
@[reducible] local instance (priority := 2000) classicalBasisDecidableEqCone (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]
variable {I C : Ideal (MvPolynomial V k)} {d : ℕ}
namespace LinearResolution

abbrev leftProjection (A B : Type*) : (A ⊕ B → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (A → MvPolynomial V k) := LinearMap.pi (fun a => LinearMap.proj (Sum.inl a))
abbrev rightProjection (A B : Type*) : (A ⊕ B → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (B → MvPolynomial V k) := LinearMap.pi (fun b => LinearMap.proj (Sum.inr b))

@[simp] lemma leftProjection_apply (A B : Type*) (x : A ⊕ B → MvPolynomial V k) :
    leftProjection A B x = (fun a => x (Sum.inl a)) := rfl
@[simp] lemma rightProjection_apply (A B : Type*) (x : A ⊕ B → MvPolynomial V k) :
    rightProjection A B x = (fun b => x (Sum.inr b)) := rfl

abbrev joinMaps {A B L : Type*}
    (f : (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (A → MvPolynomial V k))
    (g : (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (B → MvPolynomial V k)) :
    (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (A ⊕ B → MvPolynomial V k) :=
  LinearMap.pi (Sum.elim (fun a => (LinearMap.proj a).comp f) (fun b => (LinearMap.proj b).comp g))

@[simp] lemma left_single_inl {A B : Type*} [Fintype A] [Fintype B] (a : A) :
    (fun i : A => (Pi.single (Sum.inl a) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inl i)) = Pi.single a 1 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma left_single_inr {A B : Type*} [Fintype A] [Fintype B] (b : B) :
    (fun i : A => (Pi.single (Sum.inr b) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inl i)) = 0 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma right_single_inl {A B : Type*} [Fintype A] [Fintype B] (a : A) :
    (fun i : B => (Pi.single (Sum.inl a) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inr i)) = 0 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma right_single_inr {A B : Type*} [Fintype A] [Fintype B] (b : B) :
    (fun i : B => (Pi.single (Sum.inr b) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inr i)) = Pi.single b 1 := by
  funext i
  simp [Pi.single_apply]

variable (P : LinearResolution I d) (Q : LinearResolution C 1)
    (g : MvPolynomial V k) (hg : g.IsHomogeneous d)
    (hcolon : C = I.colon {g})

include hcolon in
lemma mul_mem (z : MvPolynomial V k) (hz : z ∈ C) : g * z ∈ I := by
  rw [hcolon, Submodule.mem_colon_singleton] at hz
  simpa [smul_eq_mul, mul_comm] using hz

def theta (n : ℕ) := Q.multiplicationLift P g hg (mul_mem g hcolon) n

lemma theta_comm (n : ℕ) (x : Q.Index (n + 1) → MvPolynomial V k) :
    P.differential n (theta P Q g hg hcolon (n + 1) x) =
      theta P Q g hg hcolon n (Q.differential n x) :=
  LinearMap.congr_fun (Q.multiplicationLift_comm P g hg (mul_mem g hcolon) n) x

lemma theta_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (theta P Q g hg hcolon 0 x) = g * Q.augmentation x :=
  Q.multiplicationLift_aug P g hg (mul_mem g hcolon) x

abbrev coneRight : ℕ → Type
  | 0 => PUnit
  | n + 1 => Q.Index n

abbrev coneIndex (n : ℕ) : Type := P.Index n ⊕ coneRight Q n

instance coneIndex_fintype (n : ℕ) : Fintype (coneIndex P Q n) := by
  cases n <;> dsimp [coneIndex, coneRight] <;> infer_instance

def coneAugmentation : (coneIndex P Q 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
    MvPolynomial V k :=
  P.augmentation.comp (leftProjection _ _) +
    (LinearMap.mulLeft (MvPolynomial V k) g).comp (LinearMap.proj (Sum.inr PUnit.unit))

def coneDifferential : ∀ n,
    (coneIndex P Q (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
      (coneIndex P Q n → MvPolynomial V k)
  | 0 => joinMaps
      ((P.differential 0).comp (leftProjection _ _) +
        (theta P Q g hg hcolon 0).comp (rightProjection _ _))
      (LinearMap.pi (fun _ : PUnit => -(Q.augmentation.comp (rightProjection _ _))))
  | n + 1 => joinMaps
      ((P.differential (n + 1)).comp (leftProjection _ _) +
        (theta P Q g hg hcolon (n + 1)).comp (rightProjection _ _))
      (-((Q.differential n).comp (rightProjection _ _)))

lemma coneDifferential_left (n : ℕ)
    (x : coneIndex P Q (n + 1) → MvPolynomial V k) (a : P.Index n) :
    coneDifferential P Q g hg hcolon n x (Sum.inl a) =
      P.differential n (fun a => x (Sum.inl a)) a +
        theta P Q g hg hcolon n (fun b => x (Sum.inr b)) a := by
  cases n <;> rfl

lemma coneDifferential_right_zero
    (x : coneIndex P Q 1 → MvPolynomial V k) :
    coneDifferential P Q g hg hcolon 0 x (Sum.inr PUnit.unit) =
      -Q.augmentation (fun b => x (Sum.inr b)) := rfl

lemma coneDifferential_right_succ (n : ℕ)
    (x : coneIndex P Q (n + 2) → MvPolynomial V k) (b : Q.Index n) :
    coneDifferential P Q g hg hcolon (n + 1) x (Sum.inr b) =
      -Q.differential n (fun b => x (Sum.inr b)) b := rfl

lemma coneAugmentation_apply (x : coneIndex P Q 0 → MvPolynomial V k) :
    coneAugmentation P Q g x = P.augmentation (fun a => x (Sum.inl a)) + g * x (Sum.inr PUnit.unit) := rfl

lemma coneAugmentation_range : LinearMap.range (coneAugmentation P Q g) = I ⊔ Ideal.span {g} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [coneAugmentation_apply]
    apply add_mem
    · exact (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) (show P.augmentation _ ∈ I by
        simpa only [P.augmentation_range] using LinearMap.mem_range_self P.augmentation (fun a => x (Sum.inl a)))
    · exact (show Ideal.span {g} ≤ I ⊔ Ideal.span {g} from le_sup_right) (Ideal.mem_span_singleton'.mpr ⟨x (Sum.inr PUnit.unit), mul_comm _ _⟩)
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha' : a ∈ LinearMap.range P.augmentation := by simpa only [P.augmentation_range] using ha
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨Sum.elim x (fun _ => c), ?_⟩
    change P.augmentation x + g * c = P.augmentation x + c * g
    ring

lemma coneExact_zero : LinearMap.range (coneDifferential P Q g hg hcolon 0) =
    LinearMap.ker (coneAugmentation P Q g) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [coneAugmentation_apply]
    change P.augmentation (P.differential 0 _ + theta P Q g hg hcolon 0 _) + _ = 0
    rw [map_add, theta_aug]
    have hz := LinearMap.congr_fun P.augmentation_comp (fun a => y (Sum.inl a))
    change P.augmentation (P.differential 0 _) = 0 at hz
    simp only [leftProjection_apply, rightProjection_apply]
    rw [hz, coneDifferential_right_zero]
    ring
  · intro hx
    have he := LinearMap.mem_ker.mp hx
    rw [coneAugmentation_apply] at he
    let a : P.Index 0 → MvPolynomial V k := fun i => x (Sum.inl i)
    let c := x (Sum.inr PUnit.unit)
    have hgc : g * c ∈ I := by
      have hp : P.augmentation a ∈ I := by
        simpa only [P.augmentation_range] using LinearMap.mem_range_self P.augmentation a
      have hneg : g * c = -P.augmentation a := by change P.augmentation a + g * c = 0 at he; linear_combination he
      rw [hneg]
      exact I.neg_mem hp
    have hc : c ∈ C := by
      rw [hcolon, Submodule.mem_colon_singleton]
      simpa [smul_eq_mul, mul_comm] using hgc
    have hc' : c ∈ LinearMap.range Q.augmentation := by simpa only [Q.augmentation_range] using hc
    obtain ⟨q, hq⟩ := hc'
    have hp : a + theta P Q g hg hcolon 0 q ∈ LinearMap.ker P.augmentation := by
      apply LinearMap.mem_ker.mpr
      rw [map_add, theta_aug, hq]
      exact he
    rw [← P.exact_zero] at hp
    obtain ⟨p, hp⟩ := hp
    refine ⟨Sum.elim p (-q), ?_⟩
    funext i
    cases i with
    | inl i =>
      rw [coneDifferential_left]
      change (P.differential 0 p + theta P Q g hg hcolon 0 (-q)) i = a i
      rw [hp, map_neg]
      simp
    | inr i =>
      cases i
      rw [coneDifferential_right_zero]
      change -Q.augmentation (-q) = c
      rw [map_neg, neg_neg, hq]

lemma coneDifferential_comp (n : ℕ) :
    coneDifferential P Q g hg hcolon n ∘ₗ coneDifferential P Q g hg hcolon (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  cases n with
  | zero =>
    cases i with
    | inl i =>
      simp only [LinearMap.comp_apply, coneDifferential_left, coneDifferential_right_succ]
      change (P.differential 0 (P.differential 1 _ + theta P Q g hg hcolon 1 _) +
        theta P Q g hg hcolon 0 (-Q.differential 0 _)) i = 0
      rw [map_add, theta_comm, map_neg]
      have hz := LinearMap.congr_fun (P.differential_comp 0) (fun a => x (Sum.inl a))
      change P.differential 0 (P.differential 1 _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp
    | inr i =>
      cases i
      rw [LinearMap.comp_apply, coneDifferential_right_zero]
      change -Q.augmentation (-Q.differential 0 _) = 0
      rw [map_neg, neg_neg]
      exact LinearMap.congr_fun Q.augmentation_comp _
  | succ n =>
    cases i with
    | inl i =>
      simp only [LinearMap.comp_apply, coneDifferential_left, coneDifferential_right_succ]
      change (P.differential (n + 1) (P.differential (n + 2) _ + theta P Q g hg hcolon (n + 2) _) +
        theta P Q g hg hcolon (n + 1) (-Q.differential (n + 1) _)) i = 0
      rw [map_add, theta_comm, map_neg]
      have hz := LinearMap.congr_fun (P.differential_comp (n + 1)) (fun a => x (Sum.inl a))
      change P.differential (n + 1) (P.differential (n + 2) _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp
    | inr i =>
      rw [LinearMap.comp_apply, coneDifferential_right_succ]
      change -Q.differential n (-Q.differential (n + 1) _) i = 0
      rw [map_neg]
      have hz := LinearMap.congr_fun (Q.differential_comp n) (fun b => x (Sum.inr b))
      change Q.differential n (Q.differential (n + 1) _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp

lemma coneExact_succ (n : ℕ) :
    LinearMap.range (coneDifferential P Q g hg hcolon (n + 1)) =
      LinearMap.ker (coneDifferential P Q g hg hcolon n) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (coneDifferential_comp P Q g hg hcolon n)
  · intro x hx
    let a : P.Index (n + 1) → MvPolynomial V k := fun i => x (Sum.inl i)
    let b : Q.Index n → MvPolynomial V k := fun j => x (Sum.inr j)
    have hx0 := LinearMap.mem_ker.mp hx
    have hleft : P.differential n a + theta P Q g hg hcolon n b = 0 := by
      funext i
      have h := congrFun hx0 (Sum.inl i)
      rw [coneDifferential_left P Q g hg hcolon n] at h
      change P.differential n a i + theta P Q g hg hcolon n b i = 0 at h
      exact h
    have hb : b ∈ LinearMap.range (Q.differential n) := by
      cases n with
      | zero =>
        rw [Q.exact_zero]
        apply LinearMap.mem_ker.mpr
        have h := congrFun hx0 (Sum.inr PUnit.unit)
        change -Q.augmentation b = 0 at h
        exact neg_eq_zero.mp h
      | succ n =>
        rw [Q.exact_succ n]
        apply LinearMap.mem_ker.mpr
        funext j
        have h := congrFun hx0 (Sum.inr j)
        change -Q.differential n b j = 0 at h
        exact neg_eq_zero.mp h
    obtain ⟨q, hq⟩ := hb
    have hp : a + theta P Q g hg hcolon (n + 1) q ∈ LinearMap.range (P.differential (n + 1)) := by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      rw [map_add, theta_comm, hq]
      exact hleft
    obtain ⟨p, hp⟩ := hp
    refine ⟨Sum.elim p (-q), ?_⟩
    funext i
    cases i with
    | inl i =>
      rw [coneDifferential_left]
      change (P.differential (n + 1) p + theta P Q g hg hcolon (n + 1) (-q)) i = a i
      rw [hp, map_neg]
      simp
    | inr i =>
      rw [coneDifferential_right_succ]
      change -Q.differential n (-q) i = b i
      rw [map_neg, hq]
      simp

/-- Adjoining one degree-`d` generator with a linearly resolved colon ideal
produces a genuine `d`-linear free resolution of the enlarged ideal. -/
def adjoin : LinearResolution (I ⊔ Ideal.span {g}) d where
  Index := coneIndex P Q
  finite := coneIndex_fintype P Q
  differential := coneDifferential P Q g hg hcolon
  augmentation := coneAugmentation P Q g
  augmentation_range := coneAugmentation_range P Q g
  exact_zero := coneExact_zero P Q g hg hcolon
  exact_succ := coneExact_succ P Q g hg hcolon
  linear := by
    intro n
    intro a b
    cases n with
    | zero =>
      cases a with
      | inl a =>
        rw [coneDifferential_left]
        cases b with
        | inl b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using P.linear 0 a b
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using Q.multiplicationLift_homogeneous P g hg (mul_mem g hcolon) 0 a b
      | inr a =>
        cases a
        rw [coneDifferential_right_zero]
        cases b with
        | inl b => simp only [left_single_inr, right_single_inl, map_zero, Pi.zero_apply, neg_zero]; exact isHomogeneous_zero _ _ _
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using (Q.augmentation_homogeneous b).neg
    | succ n =>
      cases a with
      | inl a =>
        rw [coneDifferential_left]
        cases b with
        | inl b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using P.linear (n + 1) a b
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using Q.multiplicationLift_homogeneous P g hg (mul_mem g hcolon) (n + 1) a b
      | inr a =>
        rw [coneDifferential_right_succ]
        cases b with
        | inl b => simp only [left_single_inr, right_single_inl, map_zero, Pi.zero_apply, neg_zero]; exact isHomogeneous_zero _ _ _
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using (Q.linear n a b).neg
  augmentation_homogeneous := by
    intro b
    rw [coneAugmentation_apply]
    cases b with
    | inl b =>
      rw [left_single_inl]
      simpa only [Pi.single_apply, Sum.inr_ne_inl, ite_false, mul_zero, add_zero] using
        P.augmentation_homogeneous b
    | inr b =>
      rw [left_single_inr, map_zero, zero_add]
      cases b
      simpa only [Pi.single_eq_same, mul_one] using hg

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource12

/-! ## Source: Characterizations.Resolution.VariableIdeal -/
section CheckedCharacterizationsSource13

/-! # A genuine linear free resolution of an ideal generated by variables -/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqVariableIdeal (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
namespace Characterizations
open Classical Resolution CategoryTheory CommAlg.Koszul MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

lemma exact_transport {M₀ M₁ M₂ N₀ N₁ N₂ : Type u}
    [AddCommGroup M₀] [Module (MvPolynomial V k) M₀]
    [AddCommGroup M₁] [Module (MvPolynomial V k) M₁]
    [AddCommGroup M₂] [Module (MvPolynomial V k) M₂]
    [AddCommGroup N₀] [Module (MvPolynomial V k) N₀]
    [AddCommGroup N₁] [Module (MvPolynomial V k) N₁]
    [AddCommGroup N₂] [Module (MvPolynomial V k) N₂]
    (f : M₂ →ₗ[MvPolynomial V k] M₁) (g : M₁ →ₗ[MvPolynomial V k] M₀)
    (h : LinearMap.range f = LinearMap.ker g)
    (e₀ : M₀ ≃ₗ[MvPolynomial V k] N₀) (e₁ : M₁ ≃ₗ[MvPolynomial V k] N₁)
    (e₂ : M₂ ≃ₗ[MvPolynomial V k] N₂) :
    LinearMap.range (e₁.toLinearMap ∘ₗ f ∘ₗ e₂.symm.toLinearMap) =
      LinearMap.ker (e₀.toLinearMap ∘ₗ g ∘ₗ e₁.symm.toLinearMap) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hm : f (e₂.symm x) ∈ LinearMap.ker g := h ▸ LinearMap.mem_range_self _ _
    rw [LinearMap.mem_ker.mp hm, map_zero]
  · intro hy
    have hh : e₁.symm y ∈ LinearMap.ker g := by
      apply LinearMap.mem_ker.mpr
      apply e₀.injective
      simpa using LinearMap.mem_ker.mp hy
    rw [← h] at hh
    obtain ⟨x, hx⟩ := hh
    refine ⟨e₂ x, ?_⟩
    simp [hx]

namespace VariableResolution
variable (l : List (MvPolynomial V k))

abbrev Index (i : ℕ) := Set.powersetCard (Fin l.length) i

def coordinates (i : ℕ) : (⋀[MvPolynomial V k]^i (Fin l.length → MvPolynomial V k)) ≃ₗ[MvPolynomial V k]
    (Index l i → MvPolynomial V k) :=
  ((Pi.basisFun (MvPolynomial V k) (Fin l.length)).exteriorPower i).equivFun

lemma coordinates_symm_single (i : ℕ) (b : Index l i) :
    (coordinates l i).symm (Pi.single b 1) =
      ((Pi.basisFun (MvPolynomial V k) (Fin l.length)).exteriorPower i) b := by
  apply (coordinates l i).injective
  ext a
  simp [coordinates, Pi.single_apply, eq_comm]

def differential (i : ℕ) :
    (Index l (i + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k] (Index l i → MvPolynomial V k) :=
  (coordinates l i).toLinearMap ∘ₗ
    koszulComplex.d (Fintype.linearCombination (MvPolynomial V k) l.get) i ∘ₗ
      (coordinates l (i + 1)).symm.toLinearMap

def augmentation : (Index l 1 → MvPolynomial V k) →ₗ[MvPolynomial V k] MvPolynomial V k :=
  (exteriorPower.zeroEquiv (MvPolynomial V k) (Fin l.length → MvPolynomial V k)).toLinearMap ∘ₗ
    koszulComplex.d (Fintype.linearCombination (MvPolynomial V k) l.get) 0 ∘ₗ
      (coordinates l 1).symm.toLinearMap

lemma augmentation_range : LinearMap.range (augmentation l) = Ideal.ofList l := by
  rw [augmentation, ← LinearMap.comp_assoc,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    koszulComplex.equiv_comp_koszulComplex.d_zero_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  simpa using Fintype.range_linearCombination (MvPolynomial V k) l.get

lemma exact_d (hreg : RingTheory.Sequence.IsRegular (MvPolynomial V k) l) (i : ℕ) :
    LinearMap.range (koszulComplex.d (Fintype.linearCombination (MvPolynomial V k) l.get) (i + 1)) =
      LinearMap.ker (koszulComplex.d (Fintype.linearCombination (MvPolynomial V k) l.get) i) := by
  have h := koszulComplex.exactAt_of_isRegular l hreg (i + 1) (Nat.succ_ne_zero i)
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  simpa [koszulComplex.ofList, koszulComplex.d_eq_d, Nat.add_assoc] using h

lemma phi_basis (j : Fin l.length) :
    Fintype.linearCombination (MvPolynomial V k) l.get
      ((Pi.basisFun (MvPolynomial V k) (Fin l.length)) j) = l.get j := by
  simp [Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply]

lemma differential_homogeneous
    (hl : ∀ x ∈ l, (x : MvPolynomial V k).IsHomogeneous 1) (i : ℕ) :
    IsHomogeneousMap (differential l i) 1 := by
  intro a b
  simp only [differential, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coordinates_symm_single, differential_eq_contraction,
    Module.Basis.koszulDifferential_eq_sum (Pi.basisFun (MvPolynomial V k) (Fin l.length))]
  simp only [phi_basis, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  apply (homogeneousSubmodule V k 1).sum_mem
  intro j hj
  by_cases hjb : j ∈ b.val
  · rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem _ hjb,
      map_zsmul_unit]
    change (l.get j * (TauCeti.ExteriorAlgebra.basisEraseSign j b.val •
      (coordinates l i) ((Pi.basisFun (MvPolynomial V k) (Fin l.length)).exteriorPower i _) a)).IsHomogeneous 1
    rw [show ∀ t, (coordinates l i)
      ((Pi.basisFun (MvPolynomial V k) (Fin l.length)).exteriorPower i t) a =
      if t = a then 1 else 0 from fun t => Module.Basis.equivFun_self _ _ _]
    split_ifs
    · have hh := (homogeneousSubmodule V k 1).toAddSubgroup.zsmul_mem (hl (l.get j) (List.get_mem l j))
        (TauCeti.ExteriorAlgebra.basisEraseSign j b.val : ℤ)
      simpa only [Submodule.mem_toAddSubgroup, mem_homogeneousSubmodule, Units.smul_def, zsmul_eq_mul, mul_comm, mul_one, one_mul] using hh
    · simp [isHomogeneous_zero]
  · rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem _ hjb]
    simp [isHomogeneous_zero]

lemma augmentation_homogeneous
    (hl : ∀ x ∈ l, (x : MvPolynomial V k).IsHomogeneous 1) (b : Index l 1) :
    (augmentation l (Pi.single b 1)).IsHomogeneous 1 := by
  simp only [augmentation, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coordinates_symm_single, differential_eq_contraction,
    Module.Basis.koszulDifferential_eq_sum (Pi.basisFun (MvPolynomial V k) (Fin l.length))]
  simp only [phi_basis, map_sum, map_smul]
  apply (homogeneousSubmodule V k 1).sum_mem
  intro j hj
  by_cases hjb : j ∈ b.val
  · rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem _ hjb,
      map_zsmul_unit]
    have he : ∀ t, exteriorPower.zeroEquiv (MvPolynomial V k) (Fin l.length → MvPolynomial V k)
        ((Pi.basisFun (MvPolynomial V k) (Fin l.length)).exteriorPower 0 t) = 1 := by
      intro t
      rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.zeroEquiv_ιMulti]
    rw [he]
    have hh := (homogeneousSubmodule V k 1).toAddSubgroup.zsmul_mem (hl (l.get j) (List.get_mem l j))
      (TauCeti.ExteriorAlgebra.basisEraseSign j b.val : ℤ)
    simpa only [Submodule.mem_toAddSubgroup, mem_homogeneousSubmodule, Units.smul_def, smul_eq_mul, zsmul_eq_mul, mul_comm, mul_one, one_mul] using hh
  · rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem _ hjb]
    simp [isHomogeneous_zero]

/-- The positive truncation of the genuine Koszul complex, in its finite exterior basis. -/
def ofRegularLinearForms (hreg : RingTheory.Sequence.IsRegular (MvPolynomial V k) l)
    (hl : ∀ x ∈ l, (x : MvPolynomial V k).IsHomogeneous 1) :
    LinearResolution (Ideal.ofList l) 1 where
  Index n := Index l (n + 1)
  finite n := inferInstance
  differential n := differential l (n + 1)
  augmentation := augmentation l
  augmentation_range := augmentation_range l
  exact_zero := exact_transport _ _ (exact_d l hreg 0)
    (exteriorPower.zeroEquiv _ _) (coordinates l 1) (coordinates l 2)
  exact_succ n := exact_transport _ _ (exact_d l hreg (n + 1))
    (coordinates l (n + 1)) (coordinates l (n + 2)) (coordinates l (n + 3))
  linear n := differential_homogeneous l hl (n + 1)
  augmentation_homogeneous := augmentation_homogeneous l hl

end VariableResolution

variable [Nontrivial k]

/-- Every actual ideal generated by a subset of the polynomial variables has a
one-linear finite-free resolution, supplied by its regular Koszul complex. -/
def variableIdealLinearResolution (A : Finset V) :
    LinearResolution (CommAlg.Polymatroid.variableIdeal (k := k) A) 1 := by
  let l := A.toList.map (MvPolynomial.X : V → MvPolynomial V k)
  have hreg := CommAlg.Koszul.variables_regular (k := k) A.toList A.nodup_toList
  have he : Ideal.ofList l = CommAlg.Polymatroid.variableIdeal (k := k) A := by
    apply congrArg Ideal.span
    ext x
    simp [l, CommAlg.Polymatroid.variableIdeal]
  rw [← he]
  apply VariableResolution.ofRegularLinearForms l hreg
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact isHomogeneous_X _ _

end Characterizations

end
end CheckedCharacterizationsSource13

/-! ## Source: Characterizations.Resolution.LinearQuotients -/
section CheckedCharacterizationsSource14

/-! # Linear quotients construct actual linear free resolutions -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The zero module is resolved by the zero complex, for every proposed shift. -/
def zeroLinearResolution (d : ℕ) : LinearResolution (⊥ : Ideal (MvPolynomial V k)) d where
  Index _ := Empty
  finite _ := inferInstance
  differential _ := 0
  augmentation := 0
  augmentation_range := LinearMap.range_zero
  exact_zero := by simp only [LinearMap.range_zero, LinearMap.ker_zero]; exact Subsingleton.elim _ _
  exact_succ _ := by simp only [LinearMap.range_zero, LinearMap.ker_zero]; exact Subsingleton.elim _ _
  linear _ a := Empty.elim a
  augmentation_homogeneous b := Empty.elim b

private theorem exists_greatest (r : GeneratorOrder V)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (C : Family V) (hC : C.Nonempty) :
    ∃ b ∈ C, ∀ a ∈ C, a = b ∨ r a b := by
  induction C using Finset.induction_on with
  | empty => simp at hC
  | @insert b C hb ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨c, hc, hmax⟩ := ih hne
      by_cases hbc : b = c
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl hbc
        · exact hmax a ha
      rcases htotal b c hbc with hbc | hcb
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inr hbc
        · exact hmax a ha
      · refine ⟨b, mem_insert_self _ _, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl rfl
        · rcases hmax a ha with rfl | hac
          · exact Or.inr hcb
          · exact Or.inr (htrans hac hcb)
    · have he := not_nonempty_iff_eq_empty.mp hne
      subst C
      exact ⟨b, by simp, fun a ha => Or.inl (by simpa using ha)⟩

private theorem initialSegment_linearResolution (B : Family V) (d : ℕ)
    (hB : Equigenerated B d) (r : GeneratorOrder V)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hL : HasLinearQuotients k B r) (C : Family V) (hCB : C ⊆ B)
    (hdown : ∀ a ∈ C, ∀ b ∈ B, r b a → b ∈ C) :
    Nonempty (LinearResolution (monomialIdeal k C) d) := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨b, hb, hmax⟩ := exists_greatest r htrans htotal C hne
      let D := C.erase b
      have hDB : D ⊆ B := (erase_subset _ _).trans hCB
      have hDdown : ∀ a ∈ D, ∀ c ∈ B, r c a → c ∈ D := by
        intro a ha c hc hca
        obtain ⟨hab, haC⟩ := mem_erase.mp ha
        apply mem_erase.mpr
        refine ⟨?_, hdown a haC c hc hca⟩
        intro hcb
        subst c
        rcases hmax a haC with he | habefore
        · exact hab he
        · exact hirr a (htrans habefore hca)
      obtain ⟨P⟩ := ih D (erase_ssubset hb) hDB hDdown
      have hDeq : D = preceding B r b := by
        ext a
        constructor
        · intro ha
          obtain ⟨hab, haC⟩ := mem_erase.mp ha
          exact (mem_preceding _ _ _ _).mpr ⟨hCB haC, (hmax a haC).resolve_left hab⟩
        · intro ha
          obtain ⟨haB, hab⟩ := (mem_preceding _ _ _ _).mp ha
          exact mem_erase.mpr ⟨fun he => hirr b (he ▸ hab), hdown b hb a haB hab⟩
      obtain ⟨A, hcolon⟩ := hL b (hCB hb)
      have hcol : variableIdeal (k := k) A =
          (monomialIdeal k D).colon {MvPolynomial.monomial b 1} := by
        rw [hDeq]
        exact hcolon.symm
      have hg : (MvPolynomial.monomial b (1 : k)).IsHomogeneous d :=
        MvPolynomial.isHomogeneous_monomial _ (hB b (hCB hb))
      have he : monomialIdeal k C = monomialIdeal k D ⊔ Ideal.span {MvPolynomial.monomial b (1 : k)} := by
        rw [← insert_erase hb]
        simp only [monomialIdeal, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
        exact sup_comm _ _
      rw [he]
      exact ⟨P.adjoin (variableIdealLinearResolution (k := k) A)
        (MvPolynomial.monomial b 1) hg hcol⟩
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst C
      have he0 : monomialIdeal k (∅ : Family V) = ⊥ := by simp [monomialIdeal]
      rw [he0]
      exact ⟨zeroLinearResolution d⟩

/-- Lemma 2.1 with its conventional conclusion: an actual exact complex of finite
free modules, generated in degrees `d+i`, resolves the given ideal. -/
theorem linearResolution_of_linearQuotients (B : Family V) (d : ℕ)
    (hB : Equigenerated B d) (r : GeneratorOrder V)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hL : HasLinearQuotients k B r) :
    Nonempty (LinearResolution (monomialIdeal k B) d) :=
  initialSegment_linearResolution B d hB r hirr htrans htotal hL B le_rfl
    (fun _ _ _ hb _ => hb)

theorem linearResolution_of_polymatroidal {B : Family V} (hB : IsPolymatroidal B) :
    HasLinearResolution (monomialIdeal k B) := by
  obtain ⟨d, hd⟩ := hB.1
  let o : VariableOrder V := Fintype.equivFin V
  refine ⟨d, linearResolution_of_linearQuotients B d hd (variableRevlex o)
    (variableRevlex_irrefl o) (fun h₁ h₂ => variableRevlex_trans o h₁ h₂)
    (variableRevlex_total o) ?_⟩
  exact polymatroidal_variable_linearQuotients hB.2 o

end Characterizations

end
end CheckedCharacterizationsSource14

/-! ## Source: Characterizations.Isolators.Projection -/
section CheckedCharacterizationsSource15

/-! # Exact minimal generators in localized deleted bounded families -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicatorExponent (T : Finset V) : Exponent V := ∑ i ∈ T, Finsupp.single i 1
@[simp] lemma indicatorExponent_apply (T : Finset V) (i : V) :
    indicatorExponent T i = if i ∈ T then 1 else 0 := by
  simp [indicatorExponent, Finsupp.single_apply]
@[simp] lemma indicatorExponent_degree (T : Finset V) : (indicatorExponent T).degree = T.card := by
  simp [indicatorExponent, map_sum]

def retainedCaps (T R : Finset V) : Finset R := univ.filter (fun i => i.val ∈ T)
@[simp] lemma mem_retainedCaps (T R : Finset V) (i : R) : i ∈ retainedCaps T R ↔ i.val ∈ T := by
  simp [retainedCaps]

lemma degree_split (R : Finset V) (a : Exponent V) :
    (restrictExponent R a).degree + subsetSum a Rᶜ = a.degree := by
  rw [restrictExponent_degree]
  have h := subsetSum_union_inter a R Rᶜ
  simpa using h

lemma degree_split_saturated (T R : Finset V) (h : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hcover : Rᶜ ⊆ T) :
    (restrictExponent R h).degree + Rᶜ.card = h.degree := by
  have he : subsetSum h Rᶜ = Rᶜ.card := by
    unfold subsetSum
    calc
      _ = ∑ i ∈ Rᶜ, (1 : ℕ) := sum_congr rfl (fun i hi => hsat i (hcover hi))
      _ = _ := by simp
  rw [← he]
  exact degree_split R h

lemma minimalFamily_eq_of_divisors {W : Type*} [Fintype W] [DecidableEq W]
    (A D : Family W) (hD : Antichain D) (hDA : D ⊆ A)
    (hdiv : ∀ a ∈ A, ∃ b ∈ D, b ≤ a) : minimalFamily A = D := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := hdiv a (minimalFamily_subset A ha)
    have he := (mem_minimalFamily.mp ha).2 b (hDA hb) hba
    exact he ▸ hb
  · intro ha
    apply mem_minimalFamily.mpr
    refine ⟨hDA ha, ?_⟩
    intro b hb hba
    obtain ⟨c, hc, hcb⟩ := hdiv b hb
    have he := hD c hc a ha (hcb.trans hba)
    exact le_antisymm hba (he ▸ hcb)

/-- An extra exponent cannot leave the removed monomial as the only divisor:
its support supplies a different donor, and saturation excludes capped receivers. -/
lemma deletedBounded_below (T : Finset V) (h x : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hsupp : 2 ≤ h.support.card)
    (hdeg : h.degree ≤ x.degree) (hcap : ∀ i ∈ T, x i ≤ 1) (hne : x ≠ h) :
    Contains (deletedBounded h.degree T h) x := by
  obtain ⟨b, hbx, hbd⟩ := Finsupp.exists_le_degree_eq x h.degree hdeg
  by_cases hbh : b = h
  · subst b
    have hex : ∃ j, h j < x j := by
      by_contra hn
      push_neg at hn
      exact hne (le_antisymm hn hbx)
    obtain ⟨j, hj⟩ := hex
    obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (show 1 < h.support.card by omega) j
    have hip : 0 < h i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hjT : j ∉ T := by
      intro hjT
      have hc := hcap j hjT
      rw [hsat j hjT] at hj
      omega
    refine ⟨exchange h i j, (mem_deletedBounded _ _ _ _).mpr
      ⟨exchange_ne hij hip, exchange_degree h i j hip, ?_⟩, ?_⟩
    · intro v hv
      have hvj : v ≠ j := fun he => hjT (he ▸ hv)
      simp only [exchange_apply, if_neg hvj, Nat.add_zero, hsat v hv]
      omega
    · intro v
      have hv := hbx v
      by_cases hvj : v = j
      · subst v
        simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hvj, Nat.add_zero]
        split_ifs <;> omega
  · exact ⟨b, (mem_deletedBounded _ _ _ _).mpr
      ⟨hbh, hbd, fun i hi => (hbx i).trans (hcap i hi)⟩, hbx⟩

lemma restrict_lift (R : Finset V) (b : Exponent R) :
    restrictExponent R (extendExponent R b + indicatorExponent Rᶜ) = b := by
  ext i
  simp [extendExponent_apply, i.property]

/-- Exact minimal projected generators. The only hypotheses are saturated caps,
all omitted coordinates capped, and at least two retained support coordinates. -/
theorem localFamily_deletedBounded (T R : Finset V) (h : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hcover : Rᶜ ⊆ T)
    (hsupp : 2 ≤ (restrictExponent R h).support.card) :
    localFamily (deletedBounded h.degree T h) R =
      deletedBounded (restrictExponent R h).degree (retainedCaps T R) (restrictExponent R h) := by
  let D := deletedBounded (restrictExponent R h).degree (retainedCaps T R) (restrictExponent R h)
  have hsatR : ∀ i ∈ retainedCaps T R, restrictExponent R h i = 1 := by
    intro i hi
    exact hsat i.val ((mem_retainedCaps _ _ _).mp hi)
  have hdegree := degree_split_saturated T R h hsat hcover
  apply minimalFamily_eq_of_divisors _ D (deletedBounded_equigenerated _ _ _).antichain
  · intro b hb
    obtain ⟨hbne, hbdeg, hbcap⟩ := (mem_deletedBounded _ _ _ _).mp hb
    let x := extendExponent R b + indicatorExponent Rᶜ
    have hxres : restrictExponent R x = b := restrict_lift R b
    refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
    · intro he
      exact hbne (hxres.symm.trans (congrArg (restrictExponent R) he))
    · rw [show x.degree = b.degree + Rᶜ.card by simp [x, map_add, extendExponent_degree]]
      rw [hbdeg, hdegree]
    · intro i hi
      by_cases hiR : i ∈ R
      · have hc := hbcap ⟨i, hiR⟩ (by simp [hi])
        simpa [x, extendExponent_apply, hiR] using hc
      · simp [x, extendExponent_apply, hiR]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hxne, hxdeg, hxcap⟩ := (mem_deletedBounded _ _ _ _).mp hx
    apply deletedBounded_below (retainedCaps T R) (restrictExponent R h) (restrictExponent R x) hsatR hsupp
    · have hsplit := degree_split R x
      have hsum : subsetSum x Rᶜ ≤ Rᶜ.card := by
        calc
          _ ≤ ∑ i ∈ Rᶜ, 1 := sum_le_sum (fun i hi => hxcap i (hcover hi))
          _ = _ := by simp
      omega
    · intro i hi
      exact hxcap i.val ((mem_retainedCaps _ _ _).mp hi)
    · intro he
      apply hxne
      apply eq_of_le_of_degree_eq ?_ hxdeg
      intro i
      by_cases hiR : i ∈ R
      · exact le_of_eq (congrArg (fun a : Exponent R => a ⟨i, hiR⟩) he)
      · have hiT := hcover (mem_compl.mpr hiR)
        rw [hsat i hiT]
        exact hxcap i hiT

end Characterizations.Isolators

end
end CheckedCharacterizationsSource15

/-! ## Source: Characterizations.Strands.DeletedGenerators -/
section CheckedCharacterizationsSource16

/-! # The actual ideal obtained by deleting one Veronese generator -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def deletedVeronese (a : Exponent V) : Family V := deletedBounded a.degree ∅ a

@[simp] theorem mem_deletedVeronese (a b : Exponent V) :
    b ∈ deletedVeronese a ↔ b ≠ a ∧ b.degree = a.degree := by
  simp [deletedVeronese]

theorem deletedVeronese_equigenerated (a : Exponent V) :
    Equigenerated (deletedVeronese a) a.degree :=
  fun b hb => (mem_deletedVeronese a b).mp hb |>.2

theorem deletedVeronese_contains (a b : Exponent V) (ha : 2 ≤ a.support.card) :
    Contains (deletedVeronese a) b ↔ a.degree ≤ b.degree ∧ b ≠ a := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    obtain ⟨hca, hcd⟩ := (mem_deletedVeronese a c).mp hc
    refine ⟨hcd ▸ degree_mono hcb, ?_⟩
    intro he
    subst b
    exact hca (eq_of_le_of_degree_eq hcb hcd)
  · rintro ⟨hdeg, hba⟩
    obtain ⟨c, hcb, hcd⟩ := Finsupp.exists_le_degree_eq b a.degree hdeg
    by_cases hca : c = a
    · subst c
      have hex : ∃ j, a j < b j := by
        by_contra h
        push_neg at h
        exact hba (le_antisymm h hcb)
      obtain ⟨j, hj⟩ := hex
      obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (show 1 < a.support.card by omega) j
      have hipos : 0 < a i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      refine ⟨exchange a i j, (mem_deletedVeronese a _).mpr
        ⟨exchange_ne hij hipos, exchange_degree a i j hipos⟩, ?_⟩
      intro x
      have hx := hcb x
      by_cases hxj : x = j
      · subst x
        simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hxj, Nat.add_zero]
        split_ifs <;> omega
    · exact ⟨c, (mem_deletedVeronese a c).mpr ⟨hca, hcd⟩, hcb⟩

theorem deletedVeronese_degree_pos (a : Exponent V) (ha : 2 ≤ a.support.card) :
    0 < a.degree := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < a.support.card by omega)
  have h := Finset.single_le_sum (f := fun i => a i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi' := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  rw [Finsupp.degree_eq_sum]
  omega

end Characterizations

end
end CheckedCharacterizationsSource16

/-! ## Source: Characterizations.Isolators.Pure -/
section CheckedCharacterizationsSource17

/-! # The exact family isolating one nonlinear localization -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma singleton_polymatroidal (a : Exponent V) : IsPolymatroidal ({a} : Family V) := by
  refine ⟨⟨a.degree, fun b hb => by simpa using congrArg Finsupp.degree (mem_singleton.mp hb)⟩, ?_⟩
  intro b hb c hc i hi
  have hb' := mem_singleton.mp hb
  have hc' := mem_singleton.mp hc
  subst b; subst c
  exact False.elim (lt_irrefl _ hi)

lemma purePower_mem (T : Finset V) (h : Exponent V) (hsupp : 2 ≤ h.support.card)
    (i : V) (hi : i ∉ T) : Finsupp.single i h.degree ∈ deletedBounded h.degree T h := by
  apply (mem_deletedBounded _ _ _ _).mpr
  refine ⟨?_, Finsupp.degree_single _ _, ?_⟩
  · obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (show 1 < h.support.card by omega) i
    intro he
    have hh := congrArg (fun a : Exponent V => a j) he
    have hjp : h j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simp [Finsupp.single_apply, hji, hji.symm] at hh
    exact hjp hh.symm
  · intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp [Finsupp.single_apply, hji, hji.symm]

lemma localFamily_eq_zero_of_purePower (T R : Finset V) (h : Exponent V)
    (hsupp : 2 ≤ h.support.card) (i : V) (hiT : i ∉ T) (hiR : i ∉ R) :
    localFamily (deletedBounded h.degree T h) R = {0} := by
  apply minimalFamily_eq_of_divisors _ {0}
    (singleton_polymatroidal (0 : Exponent R)).1.choose_spec.antichain
  · intro a ha
    have he : a = 0 := mem_singleton.mp ha
    subst a
    refine mem_image.mpr ⟨Finsupp.single i h.degree, purePower_mem T h hsupp i hiT, ?_⟩
    ext j
    have hji : j.val ≠ i := fun he => hiR (he ▸ j.property)
    simp [restrictExponent_apply, Finsupp.single_apply, hji, hji.symm]
  · intro a ha
    exact ⟨0, mem_singleton_self _, bot_le⟩

lemma deletedBounded_linearResolution {k : Type u} [CommRing k] [Nontrivial k]
    (d : ℕ) (T : Finset V) (h : Exponent V) (hsat : ∀ i ∈ T, h i = 1)
    (hT : T.Nonempty) : Nonempty (LinearResolution (monomialIdeal k (deletedBounded d T h)) d) := by
  obtain ⟨w, hw⟩ := hT
  obtain ⟨o, ho⟩ := exists_lastVariable w
  exact linearResolution_of_linearQuotients _ d (deletedBounded_equigenerated d T h)
    (variableRevlex o) (variableRevlex_irrefl o) (fun {_ _ _} => variableRevlex_trans o)
    (variableRevlex_total o) (deletedBounded_linearQuotients_last d T h hsat o w hw ho)

def removedExponent (U : Finset V) (q : Exponent V) := q + indicatorExponent Uᶜ

def pureIsolator (U : Finset V) (q : Exponent V) : Family V :=
  deletedBounded (removedExponent U q).degree Uᶜ (removedExponent U q)

lemma removedExponent_saturated (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    ∀ i ∈ Uᶜ, removedExponent U q i = 1 := by
  intro i hi
  have hqi : q i = 0 := Finsupp.notMem_support_iff.mp (fun h => (mem_compl.mp hi) (hq h))
  simp [removedExponent, hqi, hi]

lemma support_restrict_removed (U R : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hUR : U ⊆ R) (hsupp : 2 ≤ q.support.card) :
    2 ≤ (restrictExponent R (removedExponent U q)).support.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < q.support.card by omega)
  let a' : R := ⟨a, hUR (hq ha)⟩
  let b' : R := ⟨b, hUR (hq hb)⟩
  have ha' : a' ∈ (restrictExponent R (removedExponent U q)).support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < q a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)
    simp only [restrictExponent_apply, removedExponent, Finsupp.add_apply, a']
    omega
  have hb' : b' ∈ (restrictExponent R (removedExponent U q)).support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < q b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hb)
    simp only [restrictExponent_apply, removedExponent, Finsupp.add_apply, b']
    omega
  have hab' : a' ≠ b' := fun he => hab (congrArg Subtype.val he)
  exact (Finset.one_lt_card.mpr ⟨a', ha', b', hb', hab'⟩)

lemma removed_support (U : Finset V) (q : Exponent V) (hsupp : 2 ≤ q.support.card) :
    2 ≤ (removedExponent U q).support.card := by
  apply hsupp.trans
  apply card_le_card
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  have hp : 0 < q i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  simp only [removedExponent, Finsupp.add_apply]
  omega

lemma pureIsolator_degree (U : Finset V) (q : Exponent V) :
    Equigenerated (pureIsolator U q) (q.degree + Uᶜ.card) := by
  simpa [pureIsolator, removedExponent, map_add] using
    deletedBounded_equigenerated (removedExponent U q).degree Uᶜ (removedExponent U q)

lemma pureIsolator_nonempty (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) : (pureIsolator U q).Nonempty := by
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < q.support.card by omega)
  exact ⟨_, purePower_mem Uᶜ _ (removed_support U q hsupp) i (by simpa using hq hi)⟩

/-- Every localization omitting an uncapped variable is literally the unit family. -/
theorem pureIsolator_local_omit (U R : Finset V) (q : Exponent V)
    (hsupp : 2 ≤ q.support.card) (hUR : ¬ U ⊆ R) :
    localFamily (pureIsolator U q) R = {0} := by
  obtain ⟨i, hiU, hiR⟩ := not_subset.mp hUR
  exact localFamily_eq_zero_of_purePower Uᶜ R _ (removed_support U q hsupp) i (by simpa using hiU) hiR

/-- At every retained superset the displayed deleted capped family is exact. -/
theorem pureIsolator_local_contain (U R : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (hUR : U ⊆ R) :
    localFamily (pureIsolator U q) R =
      deletedBounded (restrictExponent R (removedExponent U q)).degree
        (retainedCaps Uᶜ R) (restrictExponent R (removedExponent U q)) := by
  apply localFamily_deletedBounded Uᶜ R _ (removedExponent_saturated U q hq)
    (compl_subset_compl.mpr hUR) (support_restrict_removed U R q hq hUR hsupp)

lemma pureIsolator_local_at (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    localFamily (pureIsolator U q) U = deletedVeronese (restrictExponent U q) := by
  rw [pureIsolator_local_contain U U q hq hsupp le_rfl]
  have he : restrictExponent U (removedExponent U q) = restrictExponent U q := by
    ext i
    simp [removedExponent, i.property]
  have hc : retainedCaps Uᶜ U = ∅ := by ext i; simp [i.property]
  rw [he, hc]
  rfl

/-- All localizations of the pure isolator have one generator degree. -/
theorem pureIsolator_locallyEquigenerated (U : Finset V) (q : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) : LocallyEquigenerated (pureIsolator U q) := by
  rw [locallyEquigenerated_iff]
  intro R
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    exact ⟨_, deletedBounded_equigenerated _ _ _⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    exact (singleton_polymatroidal (0 : Exponent R)).1

/-- Every localization other than the designated one has an actual linear free resolution. -/
theorem pureIsolator_local_linear {k : Type u} [CommRing k] [Nontrivial k]
    (U R : Finset V) (q : Exponent V) (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card)
    (hRU : R ≠ U) : HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U q) R)) := by
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    refine ⟨_, deletedBounded_linearResolution _ _ _ ?_ ?_⟩
    · intro i hi
      exact removedExponent_saturated U q hq i.val ((mem_retainedCaps _ _ _).mp hi)
    · have hex : ∃ i ∈ R, i ∉ U := by
        by_contra hn
        push_neg at hn
        exact hRU (le_antisymm hn hUR)
      obtain ⟨i, hiR, hiU⟩ := hex
      exact ⟨⟨i, hiR⟩, by simp [hiU]⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal (0 : Exponent R))

end Characterizations.Isolators

end
end CheckedCharacterizationsSource17

/-! ## Source: Characterizations.Resolution.Degree -/
section CheckedCharacterizationsSource18

/-! The generator degree of an actual homogeneous free resolution. -/
noncomputable section
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

namespace Resolution
lemma component_mul_below {a : MvPolynomial V k} {d e : ℕ}
    (ha : a.IsHomogeneous d) (b : MvPolynomial V k) (he : e < d) :
    homogeneousComponent e (a * b) = 0 := by
  induction b using MvPolynomial.induction_on' with
  | monomial f c =>
      have hf : (monomial f c : MvPolynomial V k).IsHomogeneous f.degree :=
        isHomogeneous_monomial c rfl
      rw [homogeneousComponent_of_mem (ha.mul hf)]
      simp only [show e ≠ d + f.degree by omega, ↓reduceIte]
  | add b c hb hc => simp [mul_add, map_add, hb, hc]
end Resolution

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

lemma augmentation_component_below (x : P.Index 0 → MvPolynomial V k)
    {e : ℕ} (he : e < d) : homogeneousComponent e (P.augmentation x) = 0 := by
  have hx : x = ∑ j, x j • Pi.single j (1 : MvPolynomial V k) := by
    funext j
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_smul, smul_eq_mul, mul_comm]
  exact component_mul_below (P.augmentation_homogeneous j) (x j) he

lemma degree_le_of_homogeneous_mem {y : MvPolynomial V k} {e : ℕ}
    (hy : y.IsHomogeneous e) (hy0 : y ≠ 0) (hyI : y ∈ I) : d ≤ e := by
  by_contra h
  have he : e < d := by omega
  have hr : y ∈ LinearMap.range P.augmentation := by rw [P.augmentation_range]; exact hyI
  obtain ⟨x, hx⟩ := hr
  have hh := P.augmentation_component_below x he
  rw [hx, homogeneousComponent_eq_self hy] at hh
  exact hy0 hh

variable [Nontrivial k]

omit P in
lemma equigenerated_of_monomial (B : Family V) (hB : Antichain B)
    (P : LinearResolution (monomialIdeal k B) d) : Equigenerated B d := by
  have hlo : ∀ a ∈ B, d ≤ a.degree := by
    intro a ha
    apply P.degree_le_of_homogeneous_mem (isHomogeneous_monomial (1 : k) rfl)
      (by simp) ((monomial_mem_iff B a).mpr ⟨a, ha, le_rfl⟩)
  let C := B.filter (fun a => a.degree = d)
  have hgen : ∀ j, P.augmentation (Pi.single j 1) ∈ monomialIdeal k C := by
    intro j
    apply (mem_monomialIdeal_iff C _).mpr
    intro a ha
    have hmem : P.augmentation (Pi.single j 1) ∈ monomialIdeal k B := by
      simpa only [P.augmentation_range] using
        LinearMap.mem_range_self P.augmentation (Pi.single j 1)
    obtain ⟨b, hb, hba⟩ := (mem_monomialIdeal_iff B _).mp hmem a ha
    have had : a.degree = d := by
      simpa only [← Finsupp.degree_apply] using
        ((P.augmentation_homogeneous j).degree_eq_sum_deg_support ha).symm
    have hbd : b.degree = d := le_antisymm ((degree_mono hba).trans_eq had) (hlo b hb)
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hbd⟩, hba⟩
  have hsub : monomialIdeal k B ≤ monomialIdeal k C := by
    rw [← P.augmentation_range]
    rintro y ⟨x, rfl⟩
    have hx : x = ∑ j, x j • Pi.single j (1 : MvPolynomial V k) := by
      funext j
      simp [Pi.single_apply]
    rw [hx, map_sum]
    exact (monomialIdeal k C).sum_mem (fun j _ => by
      rw [map_smul]
      exact (monomialIdeal k C).smul_mem _ (hgen j))
  intro a ha
  have ham : monomial a (1 : k) ∈ monomialIdeal k C :=
    hsub ((monomial_mem_iff B a).mpr ⟨a, ha, le_rfl⟩)
  obtain ⟨b, hb, hba⟩ := (monomial_mem_iff C a).mp ham
  obtain ⟨hbB, hbd⟩ := Finset.mem_filter.mp hb
  exact (hB b hbB a ha hba) ▸ hbd

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource18

/-! ## Source: Characterizations.Isolators.Mixed -/
section CheckedCharacterizationsSource19

/-! # The lower-degree isolator with exactly one mixed-degree localization -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def mixedCore (a : V) : Family V :=
  (univ.erase a).image (fun j => Finsupp.single j 1) ∪ {Finsupp.single a 2}

@[simp] lemma mem_mixedCore (a : V) (b : Exponent V) :
    b ∈ mixedCore a ↔ (∃ j, j ≠ a ∧ b = Finsupp.single j 1) ∨ b = Finsupp.single a 2 := by
  simp [mixedCore, eq_comm, or_comm]

lemma mixedCore_antichain (a : V) : Antichain (mixedCore a) := by
  intro b hb c hc hbc
  rcases (mem_mixedCore a b).mp hb with ⟨j, hja, rfl⟩ | rfl <;>
    rcases (mem_mixedCore a c).mp hc with ⟨i, hia, rfl⟩ | rfl
  · by_cases hji : j = i
    · exact congrArg (fun j => Finsupp.single j 1) hji
    · have hh := hbc j
      simp [Finsupp.single_apply, hji, Ne.symm hji] at hh
  · have hh := hbc j
    simp [Finsupp.single_apply, hja, hja.symm] at hh
  · have hh := hbc a
    simp [Finsupp.single_apply, hia, hia.symm] at hh
  · rfl

lemma mixedCore_contains (a : V) (b : Exponent V) :
    Contains (mixedCore a) b ↔ b ≠ 0 ∧ b ≠ Finsupp.single a 1 := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    rcases (mem_mixedCore a c).mp hc with ⟨j, hja, rfl⟩ | rfl
    · constructor
      · intro he; subst b; have hh := hcb j; simp at hh
      · intro he; subst b; have hh := hcb j; simp [Finsupp.single_apply, hja, hja.symm] at hh
    · constructor
      · intro he; subst b; have hh := hcb a; simp at hh
      · intro he; subst b; have hh := hcb a; simp at hh
  · rintro ⟨hb0, hba⟩
    by_cases hex : ∃ j, j ≠ a ∧ 0 < b j
    · obtain ⟨j, hja, hj⟩ := hex
      refine ⟨Finsupp.single j 1, (mem_mixedCore _ _).mpr (Or.inl ⟨j, hja, rfl⟩), ?_⟩
      intro i
      by_cases hij : i = j
      · subst i; simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hj
      · simp [Finsupp.single_apply, hij, Ne.symm hij]
    · have hz : ∀ j, j ≠ a → b j = 0 := by
        intro j hj
        by_contra hn
        exact hex ⟨j, hj, Nat.pos_of_ne_zero hn⟩
      have he : b = Finsupp.single a (b a) := by
        ext j
        by_cases hj : j = a
        · subst j; simp
        · rw [hz j hj, Finsupp.single_eq_of_ne hj]
      have htwo : 2 ≤ b a := by
        have h0 : b a ≠ 0 := by intro h; exact hb0 (by simpa [h] using he)
        have h1 : b a ≠ 1 := by intro h; exact hba (by simpa [h] using he)
        omega
      refine ⟨Finsupp.single a 2, (mem_mixedCore _ _).mpr (Or.inr rfl), ?_⟩
      rw [he]
      exact Finsupp.single_le_single.mpr htwo

lemma mixedCore_not_equigenerated (a b : V) (hab : a ≠ b) :
    ¬ ∃ d, Equigenerated (mixedCore a) d := by
  rintro ⟨d, hd⟩
  have h1 := hd (Finsupp.single b 1) ((mem_mixedCore _ _).mpr (Or.inl ⟨b, hab.symm, rfl⟩))
  have h2 := hd (Finsupp.single a 2) ((mem_mixedCore _ _).mpr (Or.inr rfl))
  simp only [Finsupp.degree_single] at h1 h2
  omega

lemma support_card_two_of_coordinates (h : Exponent V) (a b : V)
    (hab : a ≠ b) (ha : 0 < h a) (hb : 0 < h b) : 2 ≤ h.support.card := by
  exact Finset.one_lt_card.mpr ⟨a, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt ha),
    b, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hb), hab⟩

lemma mixed_removed_support (U : Finset V) (a : V) (ha : a ∈ U) (hT : Uᶜ.Nonempty) :
    2 ≤ (removedExponent U (Finsupp.single a 1)).support.card := by
  obtain ⟨v, hv⟩ := hT
  have hav : a ≠ v := fun he => (mem_compl.mp hv) (he ▸ ha)
  apply support_card_two_of_coordinates _ a v hav
  · simp [removedExponent, ha]
  · simp [removedExponent, Finsupp.single_apply, hav, hav.symm, hv]

/-- The mixed core occurs literally in the retained-variable polynomial ring. -/
theorem mixedIsolator_local_at (U : Finset V) (a : V) (ha : a ∈ U)
    (hT : Uᶜ.Nonempty) :
    localFamily (pureIsolator U (Finsupp.single a 1)) U = mixedCore (⟨a, ha⟩ : U) := by
  let a' : U := ⟨a, ha⟩
  let h := removedExponent U (Finsupp.single a 1)
  have hsat : ∀ i ∈ Uᶜ, h i = 1 := removedExponent_saturated U (Finsupp.single a 1) (by simpa)
  have hres : restrictExponent U h = Finsupp.single a' 1 := by
    ext i
    simp [h, removedExponent, a', Finsupp.single_apply, Subtype.ext_iff, i.property]
  have hdeg : h.degree = 1 + Uᶜ.card := by simp [h, removedExponent, map_add]
  change minimalFamily ((deletedBounded h.degree Uᶜ h).image (restrictExponent U)) = mixedCore a'
  apply minimalFamily_eq_of_divisors _ _ (mixedCore_antichain a')
  · intro b hb
    rcases (mem_mixedCore a' b).mp hb with ⟨j, hja, rfl⟩ | rfl
    · let x := extendExponent U (Finsupp.single j 1) + indicatorExponent Uᶜ
      have hxres : restrictExponent U x = Finsupp.single j 1 := restrict_lift _ _
      refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
      · intro he
        have hh := hxres.symm.trans ((congrArg (restrictExponent U) he).trans hres)
        exact hja (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) hh)
      · simp [x, map_add, extendExponent_degree, hdeg]
      · intro i hi
        have hiU : i ∉ U := mem_compl.mp hi
        simp [x, extendExponent_apply, hiU, hi]
    · obtain ⟨v, hv⟩ := hT
      let x := extendExponent U (Finsupp.single a' 2) + indicatorExponent (Uᶜ.erase v)
      have hxres : restrictExponent U x = Finsupp.single a' 2 := by
        ext i
        simp [x, extendExponent_apply, i.property]
      refine mem_image.mpr ⟨x, (mem_deletedBounded _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hxres⟩
      · intro he
        have hh := congrArg (fun z : Exponent U => z a') (hxres.symm.trans ((congrArg (restrictExponent U) he).trans hres))
        simp at hh
      · have hc : 0 < Uᶜ.card := card_pos.mpr ⟨v, hv⟩
        simp only [x, map_add, extendExponent_degree, Finsupp.degree_single, indicatorExponent_degree,
          card_erase_of_mem hv, hdeg]
        omega
      · intro i hi
        have hiU : i ∉ U := mem_compl.mp hi
        simp only [x, Finsupp.add_apply, extendExponent_apply, dif_neg hiU, zero_add,
          indicatorExponent_apply]
        split_ifs <;> omega
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    obtain ⟨hxne, hxdeg, hxcap⟩ := (mem_deletedBounded _ _ _ _).mp hx
    apply (mixedCore_contains _ _).mpr
    have hsplit := degree_split U x
    have hsum : subsetSum x Uᶜ ≤ Uᶜ.card := by
      calc
        _ ≤ ∑ i ∈ Uᶜ, 1 := sum_le_sum (fun i hi => hxcap i hi)
        _ = _ := by simp
    constructor
    · intro he
      have he' := congrArg Finsupp.degree he
      simp only [map_zero] at he'
      omega
    · intro he
      apply hxne
      apply eq_of_le_of_degree_eq ?_ hxdeg
      intro i
      by_cases hiU : i ∈ U
      · have hh := congrArg (fun z : Exponent U => z ⟨i, hiU⟩) (he.trans hres.symm)
        exact hh.le
      · rw [hsat i (mem_compl.mpr hiU)]
        exact hxcap i (mem_compl.mpr hiU)

lemma mixedIsolator_local_linear {k : Type u} [CommRing k] [Nontrivial k]
    (U R : Finset V) (a : V) (ha : a ∈ U) (hT : Uᶜ.Nonempty) (hRU : R ≠ U) :
    HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U (Finsupp.single a 1)) R)) := by
  let h := removedExponent U (Finsupp.single a 1)
  by_cases hUR : U ⊆ R
  · obtain ⟨v, hvR, hvU⟩ : ∃ v ∈ R, v ∉ U := by
      by_contra hn
      push_neg at hn
      exact hRU (le_antisymm hn hUR)
    let a' : R := ⟨a, hUR ha⟩
    let v' : R := ⟨v, hvR⟩
    have hav : a ≠ v := fun he => hvU (he ▸ ha)
    have hsupp : 2 ≤ (restrictExponent R h).support.card := by
      apply support_card_two_of_coordinates _ a' v' (fun he => hav (congrArg Subtype.val he))
      · simp [h, removedExponent, a', ha]
      · simp [h, removedExponent, v', Finsupp.single_apply, hav, hav.symm, hvU]
    have hsat := removedExponent_saturated U (Finsupp.single a 1) (by simpa)
    rw [show pureIsolator U (Finsupp.single a 1) = deletedBounded h.degree Uᶜ h from rfl,
      localFamily_deletedBounded Uᶜ R h hsat (compl_subset_compl.mpr hUR) hsupp]
    refine ⟨_, deletedBounded_linearResolution _ _ _ ?_ ⟨v', by simp [v', hvU]⟩⟩
    intro i hi
    exact hsat i.val ((mem_retainedCaps _ _ _).mp hi)
  · obtain ⟨i, hiU, hiR⟩ := not_subset.mp hUR
    rw [show localFamily (pureIsolator U (Finsupp.single a 1)) R = {0} from
      localFamily_eq_zero_of_purePower Uᶜ R h (mixed_removed_support U a ha hT) i (by simpa using hiU) hiR]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal (0 : Exponent R))

end Characterizations.Isolators

end
end CheckedCharacterizationsSource19

/-! ## Source: Characterizations.PairIsolator -/
section CheckedCharacterizationsSource20

/-! # The exact final-pair obstruction (Lemma 5.1) -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def onesOn (S : Finset V) : Exponent V := ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem onesOn_apply (S : Finset V) (i : V) :
    onesOn S i = if i ∈ S then 1 else 0 := by
  simp [onesOn, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp] theorem onesOn_degree (S : Finset V) : (onesOn S).degree = S.card := by
  simp [onesOn, map_sum]

def pairCap (i j : V) : Finset V := univ \ {i, j}
def pairHole (j : V) : Exponent V := onesOn (univ.erase j)
def pairFamily (i j : V) : Family V :=
  deletedBounded (Fintype.card V - 1) (pairCap i j) (pairHole j)

@[simp] theorem mem_pairCap (i j x : V) : x ∈ pairCap i j ↔ x ≠ i ∧ x ≠ j := by
  simp [pairCap, and_comm]

@[simp] theorem pairHole_apply (j x : V) : pairHole j x = if x = j then 0 else 1 := by
  simp [pairHole, eq_comm]

@[simp] theorem pairHole_degree (j : V) : (pairHole j).degree = Fintype.card V - 1 := by
  simp [pairHole]

theorem pairFamily_equigenerated (i j : V) :
    Equigenerated (pairFamily i j) (Fintype.card V - 1) :=
  deletedBounded_equigenerated _ _ _

theorem pairFamily_sat (i j : V) (x : V) (hx : x ∈ pairCap i j) : pairHole j x = 1 := by
  simp [((mem_pairCap _ _ _).mp hx).2]

theorem pairFamily_last_failure {i j : V} (hij : i ≠ j) {a b : Exponent V}
    (ha : a ∈ pairFamily i j) (hb : b ∈ pairFamily i j) {p : V} (hp : a p < b p)
    (hbad : ∀ q, b q < a q → exchange b p q ∉ pairFamily i j) :
    p = j ∧ (∀ x, b x < a x ↔ x = i) ∧ b = pairHole i := by
  obtain ⟨q, huniq, hpq, hpW, hqW, hhq, he, hbEq⟩ :=
    deletedBounded_failed_exchange (pairFamily_sat i j) ha hb hp hbad
  have hqij : q = i ∨ q = j := by
    by_contra hn
    exact hqW ((mem_pairCap _ _ _).mpr ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩)
  have hqj : q ≠ j := by intro he; subst q; simp at hhq
  have hqi : q = i := hqij.resolve_right hqj
  subst q
  have hpij : p = i ∨ p = j := by
    by_contra hn
    exact hpW ((mem_pairCap _ _ _).mpr ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩)
  have hpj : p = j := hpij.resolve_left hpq
  subst p
  refine ⟨rfl, huniq, hbEq.trans ?_⟩
  ext x
  simp only [exchange_apply, pairHole_apply]
  by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp [hxi, hxj, hij] <;> omega

theorem pairFamily_linearQuotients_of_not_final {k : Type*} [CommSemiring k]
    {i j : V} (hij : i ≠ j) (o : VariableOrder V) (hnot : ¬ FinalPair o i j) :
    HasLinearQuotients k (pairFamily i j) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨p, hp, he⟩ := hab
  by_cases hex : ∃ q, b q < a q ∧ exchange b p q ∈ pairFamily i j
  · obtain ⟨q, hq, hmem⟩ := hex
    have hpq : p ≠ q := by intro h; subst q; omega
    have hqp : o q < o p := by
      rcases lt_trichotomy (o q) (o p) with h | h | h
      · exact h
      · exact (hpq (o.injective h).symm).elim
      · have hh := he q h; omega
    exact ⟨_, hmem, variableRevlex_exchange o b hqp (by omega), q,
      exchange_sub_self b hpq, hq⟩
  · have hbad : ∀ q, b q < a q → exchange b p q ∉ pairFamily i j := by
      simpa only [not_exists, not_and] using hex
    obtain ⟨hpj, huniq, hbEq⟩ := pairFamily_last_failure hij ha hb hp hbad
    subst p
    have hai : b i < a i := (huniq i).mpr rfl
    have hijOrder : o i < o j := by
      rcases lt_trichotomy (o i) (o j) with h | h | h
      · exact h
      · exact (hij (o.injective h)).elim
      · have hh := he i h; omega
    have ht : ∃ t, t ≠ i ∧ t ≠ j ∧ o i < o t := by
      by_contra ht
      apply hnot
      refine ⟨hijOrder, ?_⟩
      intro t hti htj
      have hn : ¬ o i < o t := fun h => ht ⟨t, hti, htj, h⟩
      exact lt_of_le_of_ne (le_of_not_gt hn) (fun h => hti (o.injective h))
    obtain ⟨t, hti, htj, hit⟩ := ht
    have hbt : b t = 1 := by simp [hbEq, hti]
    have hmem : exchange b t i ∈ pairFamily i j := by
      apply (mem_deletedBounded _ _ _ _).mpr
      refine ⟨?_, (exchange_degree b t i (by omega)).trans
        (pairFamily_equigenerated i j b hb), ?_⟩
      · intro hh
        have hhj := congrArg (fun a : Exponent V => a j) hh
        simp [exchange_apply, hbEq, htj.symm, hij.symm] at hhj
      · intro x hx
        obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp hx
        simp only [exchange_apply, if_neg hxi, Nat.add_zero]
        have hbx : b x = 1 := by simp [hbEq, hxi]
        rw [hbx]
        split_ifs <;> omega
    exact ⟨_, hmem, variableRevlex_exchange o b hit (by omega), i,
      exchange_sub_self b hti, hai⟩

theorem pairFamily_counter_generators {i j v : V} (hij : i ≠ j)
    (hv : v ∈ pairCap i j) :
    pairHole i ∈ pairFamily i j ∧ exchange (pairHole j) v i ∈ pairFamily i j := by
  obtain ⟨hvi, hvj⟩ := (mem_pairCap _ _ _).mp hv
  constructor
  · apply (mem_deletedBounded _ _ _ _).mpr
    refine ⟨?_, pairHole_degree i, ?_⟩
    · intro he
      have hi := congrArg (fun a : Exponent V => a i) he
      simp [hij] at hi
    · intro x hx
      simp only [pairHole_apply]
      split_ifs <;> omega
  · apply (mem_deletedBounded _ _ _ _).mpr
    refine ⟨exchange_ne hvi (by simp [hvj]),
      (exchange_degree _ v i (by simp [hvj])).trans (pairHole_degree j), ?_⟩
    intro x hx
    obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp hx
    simp only [exchange_apply, if_neg hxi, Nat.add_zero, pairHole_apply, if_neg hxj]
    split_ifs <;> omega

theorem pairFamily_not_linearQuotients_final {k : Type*} [CommSemiring k] [Nontrivial k]
    {i j : V} (hij : i ≠ j) (hcard : 3 ≤ Fintype.card V)
    (o : VariableOrder V) (hfinal : FinalPair o i j) :
    ¬ HasLinearQuotients k (pairFamily i j) (variableRevlex o) := by
  intro hL
  have hWcard : (pairCap i j).card = Fintype.card V - 2 := by
    rw [pairCap, card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨v, hv⟩ : (pairCap i j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hvi, hvj⟩ := (mem_pairCap _ _ _).mp hv
  obtain ⟨hb, ha⟩ := pairFamily_counter_generators hij hv
  let a := exchange (pairHole j) v i
  let b := pairHole i
  have hdef (x : V) : b x < a x ↔ x = i := by
    simp only [a, b, exchange_apply, pairHole_apply]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> by_cases hxv : x = v <;>
      simp_all [eq_comm] <;> omega
  have hab : variableRevlex o a b := by
    refine ⟨j, ?_, fun x hx => (hfinal.no_after x hx).elim⟩
    simp [a, b, exchange_apply, hvj.symm, hij.symm]
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ := witness_of_linearQuotients
    (pairFamily_equigenerated i j).antichain (variableRevlex_irrefl o) hL a ha b hb hab
  have hzi : z = i := (hdef z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange (pairFamily_equigenerated i j) hw hb hwz
  have horder := (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    exact (not_lt_of_gt (hfinal.2 t hit.symm htj)) horder
  have hwh : w = pairHole j := by
    rw [hew, htj]
    ext x
    simp only [b, exchange_apply, pairHole_apply]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all [eq_comm]
  exact ((mem_deletedBounded _ _ _ _).mp hw).1 hwh

/-- Exact failure signature of Lemma 5.1. -/
theorem pairFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {i j : V} (hij : i ≠ j) (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    HasLinearQuotients k (pairFamily i j) (variableRevlex o) ↔ ¬ FinalPair o i j := by
  exact ⟨fun h hf => pairFamily_not_linearQuotients_final hij hcard o hf h,
    pairFamily_linearQuotients_of_not_final hij o⟩

theorem pairFamily_not_polymatroidal {i j : V} (hij : i ≠ j)
    (hcard : 3 ≤ Fintype.card V) : ¬ IsPolymatroidal (pairFamily i j) := by
  intro h
  obtain ⟨o, ho⟩ := exists_finalPair i j hij
  exact pairFamily_not_linearQuotients_final (k := ℚ) hij hcard o ho
    (polymatroidal_variable_linearQuotients h.2 o)

end Characterizations

end
end CheckedCharacterizationsSource20

/-! ## Source: Characterizations.TripleIsolator -/
section CheckedCharacterizationsSource21

/-! # The exact pointed-triple obstruction (Lemma 5.2) -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def tripleCap (i q z : V) : Finset V := univ \ {i, q, z}
def tripleCondition (i q z : V) (a : Exponent V) : Prop :=
  0 < a z ∨ (0 < a i ∧ 0 < a q)
def tripleFamily (i q z : V) : Family V :=
  (boundedFamily (Fintype.card V - 2) (tripleCap i q z)).filter (tripleCondition i q z)
def tripleBase (i q : V) : Exponent V := onesOn (univ \ {i, q})

@[simp] theorem mem_tripleCap (i q z x : V) :
    x ∈ tripleCap i q z ↔ x ≠ i ∧ x ≠ q ∧ x ≠ z := by simp [tripleCap]
@[simp] theorem mem_tripleFamily (i q z : V) (a : Exponent V) :
    a ∈ tripleFamily i q z ↔ a ∈ boundedFamily (Fintype.card V - 2) (tripleCap i q z) ∧
      tripleCondition i q z a := by simp [tripleFamily]
@[simp] theorem tripleBase_apply (i q x : V) :
    tripleBase i q x = if x = i ∨ x = q then 0 else 1 := by
  by_cases hxi : x = i <;> by_cases hxq : x = q <;> simp [tripleBase, hxi, hxq]
@[simp] theorem tripleBase_degree {i q : V} (hiq : i ≠ q) :
    (tripleBase i q).degree = Fintype.card V - 2 := by
  rw [tripleBase, onesOn_degree, card_sdiff_of_subset (subset_univ _)]
  simp [hiq]

theorem tripleFamily_equigenerated (i q z : V) :
    Equigenerated (tripleFamily i q z) (Fintype.card V - 2) :=
  fun _ ha => ((mem_boundedFamily _ _ _).mp ((mem_tripleFamily _ _ _ _).mp ha).1).1

theorem condition_receive_z (i q z p : V) (b : Exponent V) :
    tripleCondition i q z (exchange b p z) := by
  left
  simp only [exchange_apply, ite_true]
  omega

theorem condition_keep_z {i q z p r : V} {b : Exponent V}
    (hz : 0 < b z) (hpz : p ≠ z) : tripleCondition i q z (exchange b p r) := by
  left
  simp only [exchange_apply, if_neg hpz.symm, Nat.sub_zero]
  omega

theorem condition_large_z {i q z p r : V} {b : Exponent V}
    (hz : 2 ≤ b z) : tripleCondition i q z (exchange b p r) := by
  left
  simp only [exchange_apply]
  split_ifs <;> omega

theorem condition_keep_both {i q z p r : V} {b : Exponent V}
    (hi : 0 < b i) (hq : 0 < b q)
    (hpi : p ≠ i ∨ 2 ≤ b i) (hpq : p ≠ q ∨ 2 ≤ b q) :
    tripleCondition i q z (exchange b p r) := by
  right
  simp only [exchange_apply]
  constructor
  · rcases hpi with h | h
    · rw [if_neg h.symm]; omega
    · split_ifs <;> omega
  · rcases hpq with h | h
    · rw [if_neg h.symm]; omega
    · split_ifs <;> omega

/-- The non-convex condition has only one type of prescribed-exchange failure. -/
theorem condition_failed_exchange {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    {a b : Exponent V} (ha : tripleCondition i q z a) (hb : tripleCondition i q z b)
    {p : V} (hp : a p < b p) (hr : ∃ r, b r < a r)
    (hbad : ∀ r, b r < a r → ¬ tripleCondition i q z (exchange b p r)) :
    p = z ∧ b z = 1 ∧ b i = 0 ∧ b q = 0 ∧ 0 < a i ∧ 0 < a q := by
  obtain ⟨r, hr⟩ := hr
  have hbz : 0 < b z := by
    by_contra hn
    have hbz : b z = 0 := by omega
    obtain ⟨hbi, hbq⟩ : 0 < b i ∧ 0 < b q := by simpa [tripleCondition, hbz] using hb
    have hpiq : p = i ∨ p = q := by
      by_contra hn
      have hpi : p ≠ i := fun h => hn (Or.inl h)
      have hpq : p ≠ q := fun h => hn (Or.inr h)
      exact hbad r hr (condition_keep_both hbi hbq (Or.inl hpi) (Or.inl hpq))
    rcases hpiq with hpi | hpq
    · subst p
      have hbi1 : b i = 1 := by
        by_contra hn
        exact hbad r hr (condition_keep_both hbi hbq (Or.inr (by omega)) (Or.inl hiq))
      have hai : a i = 0 := by omega
      have haz : 0 < a z := by simpa [tripleCondition, hai] using ha
      exact hbad z (by omega) (condition_receive_z i q z i b)
    · subst p
      have hbq1 : b q = 1 := by
        by_contra hn
        exact hbad r hr (condition_keep_both hbi hbq (Or.inl hiq.symm) (Or.inr (by omega)))
      have haq : a q = 0 := by omega
      have haz : 0 < a z := by simpa [tripleCondition, haq] using ha
      exact hbad z (by omega) (condition_receive_z i q z q b)
  have hpz : p = z := by
    by_contra hn
    exact hbad r hr (condition_keep_z hbz hn)
  subst p
  have hbz1 : b z = 1 := by
    by_contra hn
    exact hbad r hr (condition_large_z (by omega))
  have haz : a z = 0 := by omega
  obtain ⟨hai, haq⟩ : 0 < a i ∧ 0 < a q := by simpa [tripleCondition, haz] using ha
  have hbi : b i = 0 := by
    by_contra hn
    by_cases hq : 0 < b q
    · exact hbad r hr (condition_keep_both (by omega) hq (Or.inl hiz.symm) (Or.inl hqz.symm))
    · apply hbad q (by omega)
      right
      constructor
      · simp [exchange_apply, hiz, hiq] <;> omega
      · simp [exchange_apply, hqz] <;> omega
  have hbq : b q = 0 := by
    by_contra hn
    apply hbad i (by omega)
    right
    constructor
    · simp [exchange_apply, hiz] <;> omega
    · simp [exchange_apply, hqz, hiq.symm] <;> omega
  exact ⟨rfl, hbz1, hbi, hbq, hai, haq⟩

theorem tripleFamily_failed_exchange {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    {a b : Exponent V} (ha : a ∈ tripleFamily i q z) (hb : b ∈ tripleFamily i q z)
    {p : V} (hp : a p < b p)
    (hbad : ∀ r, b r < a r → exchange b p r ∉ tripleFamily i q z) :
    p = z ∧ b = tripleBase i q ∧ (∀ x, b x < a x ↔ x = i ∨ x = q) := by
  obtain ⟨hab, hac⟩ := (mem_tripleFamily _ _ _ _).mp ha
  obtain ⟨hbb, hbc⟩ := (mem_tripleFamily _ _ _ _).mp hb
  obtain ⟨had, hacap⟩ := (mem_boundedFamily _ _ _).mp hab
  obtain ⟨hbd, hbcap⟩ := (mem_boundedFamily _ _ _).mp hbb
  have hbadc r (hr : b r < a r) : ¬ tripleCondition i q z (exchange b p r) := by
    intro hc
    exact hbad r hr ((mem_tripleFamily _ _ _ _).mpr ⟨boundedFamily_exchange hab hbb hp hr, hc⟩)
  obtain ⟨hpz, hbz, hbi, hbq, hai, haq⟩ := condition_failed_exchange hiq hiz hqz hac hbc hp
    (exists_surplus (hbd.trans had.symm) hp) hbadc
  have hbeq : b = tripleBase i q := by
    apply eq_of_le_of_degree_eq
    · intro x
      by_cases hxi : x = i
      · subst x; simp [hbi]
      by_cases hxq : x = q
      · subst x; simp [hbq]
      by_cases hxz : x = z
      · subst x; simp [tripleBase_apply, hiz.symm, hqz.symm, hbz]
      · simpa [tripleBase_apply, hxi, hxq] using hbcap x ((mem_tripleCap _ _ _ _).mpr ⟨hxi, hxq, hxz⟩)
    · exact hbd.trans (tripleBase_degree hiq).symm
  refine ⟨hpz, hbeq, fun x => ?_⟩
  constructor
  · intro hx
    by_contra hn
    have hxi : x ≠ i := fun h => hn (Or.inl h)
    have hxq : x ≠ q := fun h => hn (Or.inr h)
    by_cases hxz : x = z
    · subst x; subst p; omega
    · have hh := hacap x ((mem_tripleCap _ _ _ _).mpr ⟨hxi, hxq, hxz⟩)
      have hbxx : b x = 1 := by simp [hbeq, hxi, hxq]
      omega
  · rintro (rfl | rfl) <;> omega


theorem tripleBase_mem {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z) :
    tripleBase i q ∈ tripleFamily i q z := by
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨tripleBase_degree hiq, ?_⟩, Or.inl ?_⟩
  · intro x hx
    simp only [tripleBase_apply]
    split_ifs <;> omega
  · simp [hiz.symm, hqz.symm]

theorem tripleBase_exchange_cap {i q z t r : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (ht : t ∈ tripleCap i q z) (hr : r = i ∨ r = q) :
    exchange (tripleBase i q) t r ∈ tripleFamily i q z := by
  obtain ⟨hti, htq, htz⟩ := (mem_tripleCap _ _ _ _).mp ht
  have hbt : tripleBase i q t = 1 := by simp [hti, htq]
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨(exchange_degree _ _ _ (by omega)).trans
    (tripleBase_degree hiq), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨hxi, hxq, hxz⟩ := (mem_tripleCap _ _ _ _).mp hx
    have hxr : x ≠ r := by rcases hr with rfl | rfl <;> assumption
    simp only [exchange_apply, if_neg hxr, Nat.add_zero]
    have hbx : tripleBase i q x = 1 := by simp [hxi, hxq]
    rw [hbx]
    split_ifs <;> omega
  · exact condition_keep_z (by simp [hiz.symm, hqz.symm]) htz

theorem tripleFamily_linearQuotients_of_not_final {k : Type*} [CommSemiring k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (o : VariableOrder V) (hnot : ¬ FinalTriple o i q z) :
    HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨p, hp, hafter⟩ := hab
  by_cases hex : ∃ r, b r < a r ∧ exchange b p r ∈ tripleFamily i q z
  · obtain ⟨r, hr, hm⟩ := hex
    have hpr : p ≠ r := by intro h; subst r; omega
    have hrp : o r < o p := by
      rcases lt_trichotomy (o r) (o p) with h | h | h
      · exact h
      · exact (hpr (o.injective h).symm).elim
      · have hh := hafter r h; omega
    exact ⟨_, hm, variableRevlex_exchange o b hrp (by omega), r, exchange_sub_self b hpr, hr⟩
  · have hbad : ∀ r, b r < a r → exchange b p r ∉ tripleFamily i q z := by
      simpa only [not_exists, not_and] using hex
    obtain ⟨hpz, hbeq, hdef⟩ := tripleFamily_failed_exchange hiq hiz hqz ha hb hp hbad
    subst p
    have hir : b i < a i := (hdef i).mpr (Or.inl rfl)
    have hqr : b q < a q := (hdef q).mpr (Or.inr rfl)
    have hizord : o i < o z := by
      rcases lt_trichotomy (o i) (o z) with h | h | h
      · exact h
      · exact (hiz (o.injective h)).elim
      · have hh := hafter i h; omega
    have hqzord : o q < o z := by
      rcases lt_trichotomy (o q) (o z) with h | h | h
      · exact h
      · exact (hqz (o.injective h)).elim
      · have hh := hafter q h; omega
    have ht : ∃ t ∈ tripleCap i q z, o i < o t ∨ o q < o t := by
      by_contra hn
      apply hnot
      refine ⟨hizord, hqzord, ?_⟩
      intro t hti htq htz
      have htC : t ∈ tripleCap i q z := (mem_tripleCap _ _ _ _).mpr ⟨hti, htq, htz⟩
      constructor
      · exact lt_of_le_of_ne (le_of_not_gt (fun h => hn ⟨t, htC, Or.inl h⟩))
          (fun h => hti (o.injective h))
      · exact lt_of_le_of_ne (le_of_not_gt (fun h => hn ⟨t, htC, Or.inr h⟩))
          (fun h => htq (o.injective h))
    obtain ⟨t, ht, htr⟩ := ht
    obtain ⟨hti, htq, htz⟩ := (mem_tripleCap _ _ _ _).mp ht
    have hbt : b t = 1 := by simp [hbeq, hti, htq]
    rcases htr with hit | hqt
    · exact ⟨_, hbeq ▸ tripleBase_exchange_cap hiq hiz hqz ht (Or.inl rfl),
        variableRevlex_exchange o b hit (by omega), i, exchange_sub_self b hti, hir⟩
    · exact ⟨_, hbeq ▸ tripleBase_exchange_cap hiq hiz hqz ht (Or.inr rfl),
        variableRevlex_exchange o b hqt (by omega), q, exchange_sub_self b htq, hqr⟩

theorem tripleFamily_counter_target {i q z v : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hv : v ∈ tripleCap i q z) : tripleBase z v ∈ tripleFamily i q z := by
  obtain ⟨hvi, hvq, hvz⟩ := (mem_tripleCap _ _ _ _).mp hv
  apply (mem_tripleFamily _ _ _ _).mpr
  refine ⟨(mem_boundedFamily _ _ _).mpr ⟨tripleBase_degree hvz.symm, ?_⟩, Or.inr ?_⟩
  · intro x hx
    simp only [tripleBase_apply]
    split_ifs <;> omega
  · simp [hiz, hqz, hvi.symm, hvq.symm]

theorem tripleFamily_not_linearQuotients_final {k : Type*} [CommSemiring k] [Nontrivial k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) (o : VariableOrder V) (hfinal : FinalTriple o i q z) :
    ¬ HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) := by
  intro hL
  have hCcard : (tripleCap i q z).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hiz, hqz]
  obtain ⟨v, hv⟩ : (tripleCap i q z).Nonempty := card_pos.mp (by omega)
  obtain ⟨hvi, hvq, hvz⟩ := (mem_tripleCap _ _ _ _).mp hv
  let a := tripleBase z v
  let b := tripleBase i q
  have ha : a ∈ tripleFamily i q z := tripleFamily_counter_target hiq hiz hqz hv
  have hb : b ∈ tripleFamily i q z := tripleBase_mem hiq hiz hqz
  have hdef (x : V) : b x < a x ↔ x = i ∨ x = q := by
    simp only [a, b, tripleBase_apply]
    by_cases hxi : x = i <;> by_cases hxq : x = q <;>
      by_cases hxz : x = z <;> by_cases hxv : x = v <;> simp_all [eq_comm]
  have hab : variableRevlex o a b := by
    refine ⟨z, ?_, fun x hx => (hfinal.no_after x hx).elim⟩
    simp [a, b, hiz.symm, hqz.symm]
  obtain ⟨w, hw, hwb, r, hwr, har⟩ := witness_of_linearQuotients
    (tripleFamily_equigenerated i q z).antichain (variableRevlex_irrefl o) hL a ha b hb hab
  obtain ⟨t, hrt, ht, hew⟩ := witness_is_exchange (tripleFamily_equigenerated i q z) hw hb hwr
  have hr : r = i ∨ r = q := (hdef r).mp har
  have horder := (variableRevlex_exchange_iff o b hrt.symm ht).mp (hew ▸ hwb)
  have hti : t ≠ i := by intro he; subst t; simp [b] at ht
  have htq : t ≠ q := by intro he; subst t; simp [b] at ht
  have htz : t = z := by
    by_contra hn
    have hbefore := hfinal.2.2 t hti htq hn
    rcases hr with rfl | rfl
    · exact (not_lt_of_gt hbefore.1) horder
    · exact (not_lt_of_gt hbefore.2) horder
  have hc := ((mem_tripleFamily _ _ _ _).mp hw).2
  rw [hew, htz] at hc
  rcases hr with rfl | rfl
  · simpa [tripleCondition, b, exchange_apply, hiz, hqz, hiq, hiq.symm,
      hiz.symm, hqz.symm] using hc
  · simpa [tripleCondition, b, exchange_apply, hiz, hqz, hiq, hiq.symm,
      hiz.symm, hqz.symm] using hc

/-- Exact failure signature of Lemma 5.2. -/
theorem tripleFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) (o : VariableOrder V) :
    HasLinearQuotients k (tripleFamily i q z) (variableRevlex o) ↔ ¬ FinalTriple o i q z :=
  ⟨fun h hf => tripleFamily_not_linearQuotients_final hiq hiz hqz hcard o hf h,
    tripleFamily_linearQuotients_of_not_final hiq hiz hqz o⟩

theorem tripleFamily_not_polymatroidal {i q z : V} (hiq : i ≠ q) (hiz : i ≠ z) (hqz : q ≠ z)
    (hcard : 4 ≤ Fintype.card V) : ¬ IsPolymatroidal (tripleFamily i q z) := by
  intro h
  obtain ⟨o, ho⟩ := exists_finalTriple i q z hiq hiz hqz
  exact tripleFamily_not_linearQuotients_final (k := ℚ) hiq hiz hqz hcard o ho
    (polymatroidal_variable_linearQuotients h.2 o)

end Characterizations

end
end CheckedCharacterizationsSource21

/-! ## Source: Characterizations.ExactCoverage -/
section CheckedCharacterizationsSource22

/-! # The exact universal coverage characterization in Theorem 5.3 -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def UniversalOrderTests (k : Type*) [CommSemiring k] (F : Set (VariableOrder V)) : Prop :=
  ∀ (B : Family V) (d : ℕ), Equigenerated B d →
    (∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) → IsPolymatroidal B

theorem exists_distinct_of_card_two (hcard : 2 ≤ Fintype.card V) : ∃ i j : V, i ≠ j := by
  let e := (Fintype.equivFin V).symm
  refine ⟨e ⟨0, by omega⟩, e ⟨1, by omega⟩, ?_⟩
  intro h
  have he := e.injective h
  exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val he)

/-- Both final-pattern conditions are necessary and sufficient, with the
quantification over every generator degree in the definition. -/
theorem universalOrderTests_iff_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (F : Set (VariableOrder V)) :
    UniversalOrderTests k F ↔ CoversFinalPairs F ∧ CoversFinalTriples F := by
  constructor
  · intro htest
    constructor
    · intro i j hij
      by_contra hn
      apply pairFamily_not_polymatroidal hij (by omega)
      apply htest _ _ (pairFamily_equigenerated i j)
      intro o ho
      exact pairFamily_linearQuotients_of_not_final hij o (fun hf => hn ⟨o, ho, hf⟩)
    · intro i q j hiq hij hqj
      by_contra hn
      apply tripleFamily_not_polymatroidal hiq hij hqj hcard
      apply htest _ _ (tripleFamily_equigenerated i q j)
      intro o ho
      exact tripleFamily_linearQuotients_of_not_final hiq hij hqj o (fun hf => hn ⟨o, ho, hf⟩)
  · rintro ⟨hpairs, htriples⟩ B d hB hL
    obtain ⟨i, j, hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
    obtain ⟨o, ho, _⟩ := hpairs i j hij
    exact ⟨⟨d, hB⟩, exchange_of_order_coverage (k := k) hB F ⟨o, ho⟩ hpairs htriples hL⟩

end Characterizations

end
end CheckedCharacterizationsSource22

/-! ## Source: Characterizations.DegreeCoverage -/
section CheckedCharacterizationsSource23

/-! # The full degree-sensitive sufficient coverage theorem -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def OrderPattern (o : VariableOrder V) (C : Finset V) (i q j : V) : Prop :=
  o i < o j ∧ o q < o j ∧ ∀ t ∈ C, o t < o i ∧ o t < o q

def CoversPatterns (s : ℕ) (F : Set (VariableOrder V)) : Prop :=
  ∀ i q j, i ≠ q → i ≠ j → q ≠ j → ∀ C : Finset V,
    C ⊆ tripleCap i q j → C.card = s → ∃ o ∈ F, OrderPattern o C i q j

theorem card_positive_except_le_degree {a : Exponent V} {S : Finset V} {j : V}
    (hjS : j ∉ S) (hj : 0 < a j) (hS : ∀ x ∈ S, 0 < a x) : S.card + 1 ≤ a.degree := by
  have hones : onesOn (insert j S) ≤ a := by
    intro x
    by_cases hx : x ∈ insert j S
    · have hh : 0 < a x := by
        rcases mem_insert.mp hx with rfl | hx
        · exact hj
        · exact hS x hx
      simpa [hx] using (show 1 ≤ a x by omega)
    · simp [hx]
  have hh := degree_mono hones
  simpa [hjS] using hh

theorem singletonExchange_of_degree_patterns {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hd : d ≤ Fintype.card V - 2) (F : Set (VariableOrder V))
    (hF : CoversPatterns (d - 1) F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : SingletonExchange B := by
  intro a ha b hb i huniq j hj
  have hi : b i < a i := (huniq i).mpr rfl
  have hij : i ≠ j := by intro he; subst j; omega
  let C₀ := (pairCap i j).filter (fun x => 0 < b x)
  have hC₀pair : C₀ ⊆ pairCap i j := filter_subset _ _
  have hC₀card : C₀.card ≤ d - 1 := by
    have hh := card_positive_except_le_degree (a := b) (S := C₀) (j := j)
      (by simp [C₀]) (by omega) (fun x hx => (mem_filter.mp hx).2)
    rw [hB b hb] at hh
    omega
  have hpaircard : (pairCap i j).card = Fintype.card V - 2 := by
    rw [pairCap, card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨C, hC₀C, hCpair, hCcard⟩ := exists_subsuperset_card_eq hC₀pair hC₀card
    (show d - 1 ≤ (pairCap i j).card by omega)
  have hCproper : C.card < (pairCap i j).card := by
    have hdpos : 0 < d := by
      have hh := card_positive_except_le_degree (a := b) (S := ∅) (j := j)
        (by simp) (by omega) (by simp)
      rw [hB b hb] at hh
      simp only [card_empty, zero_add] at hh
      omega
    omega
  obtain ⟨q, hqpair, hqC⟩ := exists_mem_notMem_of_card_lt_card hCproper
  obtain ⟨hqi, hqj⟩ := (mem_pairCap _ _ _).mp hqpair
  have hCcap : C ⊆ tripleCap i q j := by
    intro x hx
    obtain ⟨hxi, hxj⟩ := (mem_pairCap _ _ _).mp (hCpair hx)
    exact (mem_tripleCap _ _ _ _).mpr ⟨hxi, fun he => hqC (he ▸ hx), hxj⟩
  obtain ⟨o, ho, hpattern⟩ := hF i q j hqi.symm hij hqj C hCcap hCcard
  have hbzero (x : V) (hxi : x ≠ i) (hxj : x ≠ j) (hxC : x ∉ C) : b x = 0 := by
    by_contra hn
    apply hxC
    apply hC₀C
    exact mem_filter.mpr ⟨(mem_pairCap _ _ _).mpr ⟨hxi, hxj⟩, by omega⟩
  have hab : variableRevlex o a b := by
    refine ⟨j, hj, ?_⟩
    intro x hx
    have hxi : x ≠ i := by intro he; subst x; exact (not_lt_of_gt hpattern.1) hx
    have hxj : x ≠ j := by intro he; subst x; exact (lt_irrefl _ hx)
    have hxC : x ∉ C := by
      intro hxC
      exact (lt_irrefl _ (hx.trans ((hpattern.2.2 x hxC).1.trans hpattern.1)))
    have hbx := hbzero x hxi hxj hxC
    have hax : a x ≤ b x := by
      by_contra hn
      exact hxi ((huniq x).mp (by omega))
    omega
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) a ha b hb hab
  have hzi : z = i := (huniq z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange hB hw hb hwz
  have horder := (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    have htC : t ∈ C := hC₀C (mem_filter.mpr ⟨(mem_pairCap _ _ _).mpr ⟨hit.symm, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).1) horder
  simpa [hew, htj] using hw


theorem exists_three_distinct (hcard : 3 ≤ Fintype.card V) :
    ∃ i q j : V, i ≠ q ∧ i ≠ j ∧ q ≠ j := by
  let e := (Fintype.equivFin V).symm
  refine ⟨e ⟨0, by omega⟩, e ⟨1, by omega⟩, e ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;>
    intro h <;> have he := congrArg Fin.val (e.injective h) <;> simp at he

theorem CoversPatterns.nonempty {s : ℕ} {F : Set (VariableOrder V)}
    (hF : CoversPatterns s F) (hcard : 3 ≤ Fintype.card V) (hs : s ≤ Fintype.card V - 3) :
    F.Nonempty := by
  obtain ⟨i, q, j, hiq, hij, hqj⟩ := exists_three_distinct hcard
  have hcapcard : (tripleCap i q j).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hij, hqj]
  obtain ⟨C, hC, hc⟩ := exists_subset_card_eq (show s ≤ (tripleCap i q j).card by omega)
  obtain ⟨o, ho, _⟩ := hF i q j hiq hij hqj C hC hc
  exact ⟨o, ho⟩

/-- Theorem 5.4, the full sufficient direction for all degrees and variable
numbers in its main range. No condition is imposed on unused variables. -/
theorem exchange_of_degree_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hcard : 4 ≤ Fintype.card V)
    (F : Set (VariableOrder V)) (hpatterns : CoversPatterns (min (d - 1) (Fintype.card V - 3)) F)
    (hpairs : Fintype.card V - 1 ≤ d → CoversFinalPairs F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : ExchangeAxiom B := by
  obtain ⟨o₀, ho₀⟩ := hpatterns.nonempty (by omega) (Nat.min_le_right _ _)
  have hconn := boxConnected_of_linearQuotients hB (variableRevlex_irrefl o₀)
    (fun {_ _ _} => variableRevlex_trans o₀) (variableRevlex_total o₀) (hL o₀ ho₀)
  have hsingle : SingletonExchange B := by
    by_cases hd : Fintype.card V - 1 ≤ d
    · exact singletonExchange_of_finalPairs hB F (hpairs hd) hL
    · have hd' : d ≤ Fintype.card V - 2 := by omega
      have hmin : min (d - 1) (Fintype.card V - 3) = d - 1 := by omega
      exact singletonExchange_of_degree_patterns hB hd' F (hmin ▸ hpatterns) hL
  by_contra hfail
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, he, hni, hnq, hnqi, hniq⟩ := four_coordinate_obstruction hB hconn hsingle hfail
  let C₀ := (tripleCap i q j).filter (fun x => 0 < c x)
  have hC₀cap : C₀ ⊆ tripleCap i q j := filter_subset _ _
  have hcapcard : (tripleCap i q j).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hiq, hij, hqj]
  have hC₀d : C₀.card ≤ d - 1 := by
    have hh := card_positive_except_le_degree (a := c) (S := C₀) (j := j)
      (by simp [C₀]) hj (fun x hx => (mem_filter.mp hx).2)
    rw [hB c hc] at hh
    omega
  have hC₀card : C₀.card ≤ min (d - 1) (Fintype.card V - 3) :=
    le_min hC₀d (by have hh := card_le_card hC₀cap; omega)
  obtain ⟨C, hC₀C, hCcap, hCcard⟩ := exists_subsuperset_card_eq hC₀cap hC₀card
    (show min (d - 1) (Fintype.card V - 3) ≤ (tripleCap i q j).card by omega)
  obtain ⟨o, ho, hpattern⟩ := hpatterns i q j hiq hij hqj C hCcap hCcard
  have hpC : p ∈ C := hC₀C (mem_filter.mpr
    ⟨(mem_tripleCap _ _ _ _).mpr ⟨hip.symm, hpq, hpj⟩, hp⟩)
  have hpord : o p < o j := (hpattern.2.2 p hpC).1.trans hpattern.1
  subst u
  have huc : variableRevlex o (exchange (exchange c p q) j i) c := by
    refine ⟨j, ?_, ?_⟩
    · simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
        ite_true, Nat.sub_zero, Nat.add_zero]
      omega
    · intro x hx
      have hxp : x ≠ p := by intro he; subst x; exact (not_lt_of_gt hpord) hx
      have hxq : x ≠ q := by intro he; subst x; exact (not_lt_of_gt hpattern.2.1) hx
      have hxi : x ≠ i := by intro he; subst x; exact (not_lt_of_gt hpattern.1) hx
      have hxj : x ≠ j := by intro he; subst x; exact (lt_irrefl _ hx)
      simp [hxp, hxq, hxi, hxj]
  obtain ⟨w, hw, hwc, z, hwz, hcz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) _ hu c hc huc
  have hziq : z = i ∨ z = q := by
    by_contra hz
    push_neg at hz
    simp only [exchange_apply, if_neg hz.1, if_neg hz.2, Nat.add_zero] at hcz
    split_ifs at hcz <;> omega
  obtain ⟨t, hzt, ht, hew⟩ := witness_is_exchange hB hw hc hwz
  have horder : o z < o t :=
    (variableRevlex_exchange_iff o c hzt.symm ht).mp (hew ▸ hwc)
  rcases hziq with rfl | rfl
  · by_cases htj : t = j
    · exact hni (by simpa [hew, htj] using hw)
    by_cases htq : t = q
    · exact hnqi (by simpa [hew, htq] using hw)
    have htC : t ∈ C := hC₀C (mem_filter.mpr
      ⟨(mem_tripleCap _ _ _ _).mpr ⟨hzt.symm, htq, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).1) horder
  · by_cases htj : t = j
    · exact hnq (by simpa [hew, htj] using hw)
    by_cases hti : t = i
    · exact hniq (by simpa [hew, hti] using hw)
    have htC : t ∈ C := hC₀C (mem_filter.mpr
      ⟨(mem_tripleCap _ _ _ _).mpr ⟨hti, hzt.symm, htj⟩, ht⟩)
    exact (not_lt_of_gt (hpattern.2.2 t htC).2) horder

end Characterizations

end
end CheckedCharacterizationsSource23

/-! ## Source: Characterizations.Transport -/
section CheckedCharacterizationsSource24

/-! # Common monomial factors and unused variables preserve quotient tests -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def translatedFamily (c : Exponent V) (B : Family V) : Family V := B.image (fun a => a + c)
def embeddedFamily (e : W ↪ V) (B : Family W) : Family V := B.image (Finsupp.embDomain e)

theorem translatedFamily_equigenerated {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (c : Exponent V) : Equigenerated (translatedFamily c B) (d + c.degree) := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  simp [hB b hb]

theorem variableRevlex_add_iff (o : VariableOrder V) (a b c : Exponent V) :
    variableRevlex o (a + c) (b + c) ↔ variableRevlex o a b := by
  simp [variableRevlex, Finsupp.add_apply]

theorem translatedFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (c : Exponent V) (o : VariableOrder V) :
    HasLinearQuotients k (translatedFamily c B) (variableRevlex o) ↔
      HasLinearQuotients k B (variableRevlex o) := by
  rw [linearQuotients_iff_witness (translatedFamily_equigenerated hB c).antichain (variableRevlex_irrefl o),
    linearQuotients_iff_witness hB.antichain (variableRevlex_irrefl o)]
  constructor
  · intro h a ha b hb hab
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h (a+c) (mem_image.mpr ⟨a, ha, rfl⟩)
      (b+c) (mem_image.mpr ⟨b, hb, rfl⟩) ((variableRevlex_add_iff o a b c).mpr hab)
    obtain ⟨w, hw₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp hw
    refine ⟨w, hw₀, (variableRevlex_add_iff o w b c).mp hwb, i, ?_, ?_⟩
    · simpa only [add_tsub_add_eq_tsub_right] using hwi
    · simpa using hai
  · intro h a ha b hb hab
    obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp ha
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp hb
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h a ha₀ b hb₀ ((variableRevlex_add_iff o a b c).mp hab)
    refine ⟨w+c, mem_image.mpr ⟨w, hw, rfl⟩, (variableRevlex_add_iff o w b c).mpr hwb,
      i, ?_, ?_⟩
    · simpa only [add_tsub_add_eq_tsub_right] using hwi
    · simpa using hai

theorem translatedFamily_polymatroidal_iff {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (c : Exponent V) :
    IsPolymatroidal (translatedFamily c B) ↔ IsPolymatroidal B := by
  rw [polymatroidal_iff_universal_revlex (k := ℚ) (translatedFamily_equigenerated hB c),
    polymatroidal_iff_universal_revlex (k := ℚ) hB]
  simp only [translatedFamily_linearQuotients_iff hB c]

theorem embeddedFamily_equigenerated {B : Family W} {d : ℕ} (hB : Equigenerated B d)
    (e : W ↪ V) : Equigenerated (embeddedFamily e B) d := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  simpa [Finsupp.embDomain_eq_mapDomain] using hB b hb

theorem embDomain_exchange (e : W ↪ V) (a : Exponent W) (i j : W) :
    Finsupp.embDomain e (exchange a i j) = exchange (Finsupp.embDomain e a) (e i) (e j) := by
  simp [exchange, Finsupp.embDomain_add, Finsupp.embDomain_tsub, Finsupp.embDomain_single]

theorem embDomain_positive_range (e : W ↪ V) (a : Exponent W) {j : V}
    (hj : 0 < Finsupp.embDomain e a j) : ∃ x, e x = j := by
  by_contra hn
  simp [Finsupp.embDomain_apply, hn] at hj

theorem embeddedFamily_polymatroidal_implies {B : Family W} {d : ℕ}
    (hB : Equigenerated B d) (e : W ↪ V) (h : IsPolymatroidal (embeddedFamily e B)) :
    IsPolymatroidal B := by
  refine ⟨⟨d, hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj, hw⟩ := h.2 (Finsupp.embDomain e a) (mem_image.mpr ⟨a, ha, rfl⟩)
    (Finsupp.embDomain e b) (mem_image.mpr ⟨b, hb, rfl⟩) (e i) (by simpa using hi)
  obtain ⟨j, rfl⟩ := embDomain_positive_range e b (lt_of_le_of_lt (Nat.zero_le _) hj)
  obtain ⟨w, hw, he⟩ := mem_image.mp hw
  have hew : w = exchange a i j := Finsupp.embDomain_injective e
    (he.trans (embDomain_exchange e a i j).symm)
  exact ⟨j, by simpa using hj, hew ▸ hw⟩

/-- Restriction of a variable permutation to the active variables, retaining
exactly their relative order. -/
def restrictedOrder (o : VariableOrder V) (e : W ↪ V) : VariableOrder W := by
  letI : LinearOrder W := LinearOrder.lift' (o ∘ e) (o.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq W rfl).symm.toEquiv

theorem restrictedOrder_lt_iff (o : VariableOrder V) (e : W ↪ V) (a b : W) :
    restrictedOrder o e a < restrictedOrder o e b ↔ o (e a) < o (e b) := by
  letI : LinearOrder W := LinearOrder.lift' (o ∘ e) (o.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq W rfl).symm.lt_iff_lt

theorem embedded_revlex_iff (o : VariableOrder V) (e : W ↪ V) (a b : Exponent W) :
    variableRevlex o (Finsupp.embDomain e a) (Finsupp.embDomain e b) ↔
      variableRevlex (restrictedOrder o e) a b := by
  constructor
  · rintro ⟨i, hi, hafter⟩
    obtain ⟨i, rfl⟩ := embDomain_positive_range e b (lt_of_le_of_lt (Nat.zero_le _) hi)
    refine ⟨i, by simpa using hi, ?_⟩
    intro j hij
    simpa using hafter (e j) ((restrictedOrder_lt_iff o e i j).mp hij)
  · rintro ⟨i, hi, hafter⟩
    refine ⟨e i, by simpa using hi, ?_⟩
    intro j hij
    by_cases hj : ∃ x, e x = j
    · obtain ⟨j, rfl⟩ := hj
      simpa using hafter j ((restrictedOrder_lt_iff o e i j).mpr hij)
    · simp [Finsupp.embDomain_apply, hj]

theorem embeddedFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family W} {d : ℕ} (hB : Equigenerated B d) (e : W ↪ V) (o : VariableOrder V) :
    HasLinearQuotients k (embeddedFamily e B) (variableRevlex o) ↔
      HasLinearQuotients k B (variableRevlex (restrictedOrder o e)) := by
  rw [linearQuotients_iff_witness (embeddedFamily_equigenerated hB e).antichain (variableRevlex_irrefl o),
    linearQuotients_iff_witness hB.antichain (variableRevlex_irrefl _)]
  constructor
  · intro h a ha b hb hab
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h (Finsupp.embDomain e a) (mem_image.mpr ⟨a, ha, rfl⟩)
      (Finsupp.embDomain e b) (mem_image.mpr ⟨b, hb, rfl⟩) ((embedded_revlex_iff o e a b).mpr hab)
    obtain ⟨w, hw₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp hw
    obtain ⟨i, rfl⟩ := embDomain_positive_range e a (lt_of_le_of_lt (Nat.zero_le _) hai)
    refine ⟨w, hw₀, (embedded_revlex_iff o e w b).mp hwb, i, ?_, by simpa using hai⟩
    apply Finsupp.embDomain_injective e
    simpa only [Finsupp.embDomain_tsub, Finsupp.embDomain_single] using hwi
  · intro h a ha b hb hab
    obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp ha
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp hb
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h a ha₀ b hb₀ ((embedded_revlex_iff o e a b).mp hab)
    refine ⟨Finsupp.embDomain e w, mem_image.mpr ⟨w, hw, rfl⟩,
      (embedded_revlex_iff o e w b).mpr hwb, e i, ?_, by simpa using hai⟩
    simpa only [Finsupp.embDomain_tsub, Finsupp.embDomain_single] using
      congrArg (Finsupp.embDomain e) hwi

end Characterizations

end
end CheckedCharacterizationsSource24

/-! ## Source: Characterizations.Strands.SimplexHomology -/
section CheckedCharacterizationsSource25

/-! # Explicit contraction and the one-dimensional boundary-simplex class -/
noncomputable section
set_option maxHeartbeats 800000
namespace Characterizations.Strands
open Classical Finset CommAlg.Simplicial CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

lemma creation_mem_degree {K : Finset V → Prop} (e : V) (i : ℕ)
    (h : ∀ s, K s → s.card = i → e ∉ s → K (insert e s))
    {z : Ambient V k} (hz : z ∈ Chains K i) : creation e z ∈ Chains K (i+1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hc⟩, rfl⟩ := ha
    rw [creation_basis]
    split_ifs with he
    · exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (basis_mem (h s hs hc he) (by simp [he, hc]))
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i+1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma exactIn_of_degree_extension {K : Finset V → Prop} (e : V) (i : ℕ)
    (h : ∀ s, K s → s.card = i → e ∉ s → K (insert e s)) :
    ExactIn (k := k) K i := by
  intro z hz hc
  exact ⟨creation e z, creation_mem_degree e i h hz, by
    simp only [boundary_creation, hc, map_zero, sub_zero]⟩

def simplexBoundary (T : Finset V) (s : Finset V) : Prop := s ⊂ T

lemma simplexBoundary_downward (T : Finset V) : Downward (simplexBoundary T) := by
  intro s t hts hs
  exact Finset.ssubset_of_subset_of_ssubset hts hs

lemma boundary_basis_mem (T : Finset V) (i : ℕ) (hcard : T.card = i+1) :
    boundary (basis (k := k) T) ∈ Chains (simplexBoundary T) i := by
  rw [boundary_eq_sum]
  apply Submodule.sum_mem
  intro e he
  rw [contraction_basis]
  split_ifs with heT
  · apply Submodule.smul_mem
    exact basis_mem (Finset.erase_ssubset heT)
      (by simpa [hcard] using Finset.card_erase_of_mem heT)
  · exact Submodule.zero_mem _

lemma boundary_basis_ne_zero [Nontrivial k] {T : Finset V} (hT : T.Nonempty) :
    boundary (basis (k := k) T) ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  intro hzero
  have h := boundary_creation e (basis (k := k) T)
  rw [creation_basis, if_pos he, map_zero, hzero, map_zero, sub_zero] at h
  exact Module.Basis.ne_zero basis T h.symm

lemma simplexBoundary_nonzero [Nontrivial k] (T : Finset V) (i : ℕ)
    (hcard : T.card = i+1) : NonzeroHomology (k := k) (simplexBoundary T) i := by
  refine ⟨boundary (basis T), boundary_basis_mem T i hcard, boundary_boundary _, ?_⟩
  intro y hy he
  have hbot : Chains (k := k) (simplexBoundary T) (i+1) = ⊥ :=
    chains_eq_bot_of_no_face (fun s hs hc => by
      have hlt := Finset.card_lt_card hs
      omega)
  rw [hbot, Submodule.mem_bot] at hy
  subst y
  exact boundary_basis_ne_zero (k := k) (T := T)
    (Finset.card_pos.mp (by omega)) (by simpa using he.symm)

lemma simplex_top_chains (T : Finset V) :
    Chains (k := k) (fun s => s ⊆ T) T.card = Submodule.span k {basis T} := by
  apply le_antisymm
  · rw [Chains, Submodule.span_le]
    rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
    have he : s = T := Finset.eq_of_subset_of_card_le hs hc.ge
    subst s
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact basis_mem (Finset.Subset.refl T) rfl

lemma simplexBoundary_cycle_span (T : Finset V) (i : ℕ) (hcard : T.card = i+1)
    {z : Ambient V k} (hz : z ∈ Chains (simplexBoundary T) i) (hc : boundary z = 0) :
    z ∈ Submodule.span k {boundary (basis T)} := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hz' : z ∈ Chains (fun s => s ⊆ T) i :=
    chains_mono (fun s hs => hs.subset) _ hz
  have hy := creation_mem_of_cone (k := k) e
    (K := fun s => s ⊆ T) (fun s hs => Finset.insert_subset he hs) hz'
  rw [← hcard, simplex_top_chains] at hy
  obtain ⟨c, hcy⟩ := Submodule.mem_span_singleton.mp hy
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  have hh := congrArg boundary hcy
  simpa only [map_smul, boundary_creation, hc, map_zero, sub_zero] using hh

end Ring

lemma homology_finrank_eq_one [Field k] {K : Finset V → Prop} (hK : Downward K)
    (i : ℕ) (v : Ambient V k) (hv : v ≠ 0)
    (hspan : ∀ z : Ambient V k, z ∈ Chains K i → boundary z = 0 →
      z ∈ Submodule.span k {v}) (hnonzero : NonzeroHomology (k := k) K i) :
    Module.finrank k ((chainComplex (k := k) hK).homology i) = 1 := by
  let C := chainComplex (k := k) hK
  let f₀ : C.cycles i →ₗ[k] Ambient V k :=
    (Chains (k := k) K i).subtype.comp (C.iCycles i).hom
  have hfmem (z : C.cycles i) : f₀ z ∈ Submodule.span k {v} := by
    apply hspan _ ((C.iCycles i z).property)
    cases i with
    | zero => exact boundary_zero_degree_zero (C.iCycles 0 z).property
    | succ j =>
      have h : (C.d (j+1) j).hom ((C.iCycles (j+1)).hom z) = 0 :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (C.iCycles_d (j+1) j)) z
      rw [show C.d (j+1) j = ModuleCat.ofHom (chainDifferential hK j) from
        chainComplex_d hK j] at h
      change (chainDifferential hK j) ((C.iCycles (j+1)).hom z) = 0 at h
      exact congrArg (fun q : Chains (k := k) K j => q.val) h
  let f : C.cycles i →ₗ[k] Submodule.span k {v} := f₀.codRestrict _ hfmem
  have hfi : Function.Injective f := by
    intro x y he
    apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
    have he' : f₀ x = f₀ y := congrArg (fun z : Submodule.span k {v} => z.val) he
    exact Subtype.ext he'
  letI : FiniteDimensional k (C.cycles i) := FiniteDimensional.of_injective f hfi
  have hs : Function.Surjective (C.homologyπ i).hom :=
    (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance
  letI : FiniteDimensional k (C.homology i) :=
    FiniteDimensional.of_surjective (C.homologyπ i).hom hs
  have hle : Module.finrank k (C.homology i) ≤ 1 := by
    calc
      _ ≤ Module.finrank k (C.cycles i) := LinearMap.finrank_le_finrank_of_surjective hs
      _ ≤ Module.finrank k (Submodule.span k {v}) := LinearMap.finrank_le_finrank_of_injective hfi
      _ = 1 := finrank_span_singleton hv
  have hn : ¬ Subsingleton (C.homology i) := by
    intro hn
    have hz := (ModuleCat.isZero_iff_subsingleton (M := C.homology i)).mpr hn
    exact ((homology_nonzero_iff hK i).mpr hnonzero) hz
  have hne : Module.finrank k (C.homology i) ≠ 0 :=
    fun h => hn ((Module.finrank_zero_iff (R := k) (M := C.homology i)).mp h)
  change Module.finrank k (C.homology i) = 1
  omega

lemma simplexBoundary_homology_finrank [Field k] (T : Finset V) (i : ℕ)
    (hcard : T.card = i+1) :
    Module.finrank k ((chainComplex (k := k) (simplexBoundary_downward T)).homology i) = 1 :=
  homology_finrank_eq_one (simplexBoundary_downward T) i (boundary (basis T))
    (boundary_basis_ne_zero (k := k) (T := T) (Finset.card_pos.mp (by omega)))
    (fun _ hz hc => simplexBoundary_cycle_span T i hcard hz hc)
    (simplexBoundary_nonzero T i hcard)

end Characterizations.Strands

end
end CheckedCharacterizationsSource25

/-! ## Source: Characterizations.Strands.BettiTransport -/
section CheckedCharacterizationsSource26

/-! # Numerical transport to the genuine derived-Tor components -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
open CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma chainComplex_congr {K L : Finset V → Prop} (hK : Downward K) (hL : Downward L)
    (h : K = L) : chainComplex (k := k) hK = chainComplex hL := by
  subst L
  rfl

lemma bettiNumber_eq_face_homology_finrank (B : Family V) (a : Exponent V) (i : ℕ) :
    bettiNumber (k := k) B a i =
      Module.finrank k ((chainComplex (k := k) (koszulFaces_downward B a)).homology i) := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (homogeneousFacesIso (k := k) B a)
  exact (e ≪≫ gradedTorIso (k := k) B a i).toLinearEquiv.finrank_eq.symm

lemma bettiNumber_eq_one_of_boundary (B : Family V) (a : Exponent V)
    (T : Finset V) (i : ℕ) (hcard : T.card = i+1)
    (hfaces : koszulFaces B a = simplexBoundary T) :
    bettiNumber (k := k) B a i = 1 := by
  rw [bettiNumber_eq_face_homology_finrank]
  rw [chainComplex_congr (koszulFaces_downward B a) (simplexBoundary_downward T) hfaces]
  exact simplexBoundary_homology_finrank T i hcard

lemma bettiNumber_eq_zero_of_exact (B : Family V) (a : Exponent V) (i : ℕ)
    (h : ExactIn (k := k) (koszulFaces B a) i) : bettiNumber (k := k) B a i = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [bettiNumber_pos_iff_faces, nonzeroHomology_iff_not_exactIn]
  exact not_not.mpr h

lemma bettiNumber_congr_faces (B C : Family V) (a b : Exponent V) (i : ℕ)
    (h : koszulFaces B a = koszulFaces C b) :
    bettiNumber (k := k) B a i = bettiNumber (k := k) C b i := by
  rw [bettiNumber_eq_face_homology_finrank, bettiNumber_eq_face_homology_finrank,
    chainComplex_congr (koszulFaces_downward B a) (koszulFaces_downward C b) h]

lemma bettiNumber_congr_contains (B C : Family V) (a : Exponent V) (i : ℕ)
    (h : ∀ b, Contains B b ↔ Contains C b) :
    bettiNumber (k := k) B a i = bettiNumber (k := k) C a i := by
  apply bettiNumber_congr_faces
  funext s
  exact propext (and_congr_right (fun _ => h _))

end Characterizations.Strands

end
end CheckedCharacterizationsSource26

/-! ## Source: Characterizations.Isolators.Shift -/
section CheckedCharacterizationsSource27

/-! # Common monomial factors: actual ideals, localization, and derived Betti numbers -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma translatedFamily_antichain {B : Family V} (hB : Antichain B) (c : Exponent V) :
    Antichain (translatedFamily c B) := by
  rintro a ha b hb hab
  obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp ha
  obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
  exact congrArg (· + c) (hB a ha₀ b hb₀ (add_le_add_iff_right c |>.mp hab))

lemma translatedFamily_nonempty {B : Family V} (hB : B.Nonempty) (c : Exponent V) :
    (translatedFamily c B).Nonempty := hB.image _

lemma localFamily_translated (B : Family V) (c : Exponent V) (R : Finset V) :
    localFamily (translatedFamily c B) R =
      translatedFamily (restrictExponent R c) (localFamily B R) := by
  let f : Exponent R ↪o Exponent R := OrderEmbedding.ofMapLEIff
    (fun b => b + restrictExponent R c) (fun _ _ => add_le_add_iff_right _)
  have hh := minimalFamily_image_orderEmbedding f (B.image (restrictExponent R))
  have hadd : ∀ b, restrictExponent R (b+c) = restrictExponent R b + restrictExponent R c := by
    intro b; ext i; rfl
  simpa only [localFamily, translatedFamily, Finset.image_image, Function.comp_def,
    hadd, f, OrderEmbedding.coe_ofMapLEIff] using hh

lemma monomialIdeal_translated (k : Type*) [CommSemiring k] (B : Family V) (c : Exponent V) :
    monomialIdeal k (translatedFamily c B) =
      monomialIdeal k B * Ideal.span {MvPolynomial.monomial c (1 : k)} := by
  have hs : monomialIdeal k ({c} : Family V) = Ideal.span {MvPolynomial.monomial c (1 : k)} := by
    unfold monomialIdeal
    congr 1
    ext p
    simp
  rw [← hs, monomialIdeal_mul]
  congr 1
  ext a
  simp [translatedFamily]

lemma translatedFamily_locallyEquigenerated {B : Family V}
    (hB : LocallyEquigenerated B) (c : Exponent V) :
    LocallyEquigenerated (translatedFamily c B) := by
  apply (locallyEquigenerated_iff _).mpr
  intro R
  obtain ⟨d, hd⟩ := (locallyEquigenerated_iff _).mp hB R
  rw [localFamily_translated]
  exact ⟨_, translatedFamily_equigenerated hd _⟩

lemma translated_deletedBounded_linearResolution {k : Type u} [CommRing k] [Nontrivial k]
    (d : ℕ) (T : Finset V) (h c : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hT : T.Nonempty) :
    Nonempty (LinearResolution
      (monomialIdeal k (translatedFamily c (deletedBounded d T h))) (d+c.degree)) := by
  obtain ⟨w, hw⟩ := hT
  obtain ⟨o, ho⟩ := exists_lastVariable w
  apply linearResolution_of_linearQuotients _ _
    (translatedFamily_equigenerated (deletedBounded_equigenerated d T h) c)
    (variableRevlex o) (variableRevlex_irrefl o) (fun hab hbc => variableRevlex_trans o hab hbc)
    (variableRevlex_total o)
  exact (translatedFamily_linearQuotients_iff (deletedBounded_equigenerated d T h) c o).mpr
    (deletedBounded_linearQuotients_last d T h hsat o w hw ho)

section Betti
variable [LinearOrder V]
variable {k : Type u} [Field k]

lemma koszulFaces_translated (B : Family V) (a c : Exponent V) :
    koszulFaces (translatedFamily c B) (a+c) = koszulFaces B a := by
  funext s
  apply propext
  constructor
  · rintro ⟨hf, b, hb, hba⟩
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
    have hf' : faceExponent s ≤ a := by
      intro i
      have h1 := hf i
      have h2 := hba i
      simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h1 h2
      omega
    refine ⟨hf', b, hb₀, ?_⟩
    intro i
    have h1 := hf' i
    have h2 := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
    omega
  · rintro ⟨hf, b, hb, hba⟩
    refine ⟨hf.trans (by intro j; exact Nat.le_add_right _ _), b+c, mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro i
    have h1 := hf i
    have h2 := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
    omega

lemma koszulFaces_translated_outside (B : Family V) (a c : Exponent V) (hc : ¬ c ≤ a) :
    koszulFaces (translatedFamily c B) a = fun _ => False := by
  funext s
  apply propext
  constructor
  · rintro ⟨hf, b, hb, hba⟩
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
    apply hc
    intro i
    have hh := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hh
    omega
  · exact False.elim

lemma gradedBetti_translated (B : Family V) (a c : Exponent V) (i : ℕ) :
    GradedBettiNonzero (k := k) (translatedFamily c B) (a+c) i ↔
      GradedBettiNonzero (k := k) B a i := by
  rw [gradedBettiNonzero_iff_faces, gradedBettiNonzero_iff_faces, koszulFaces_translated]

lemma bettiNumber_translated (B : Family V) (a c : Exponent V) (i : ℕ) :
    bettiNumber (k := k) (translatedFamily c B) (a+c) i = bettiNumber (k := k) B a i := by
  rw [Strands.bettiNumber_eq_face_homology_finrank, Strands.bettiNumber_eq_face_homology_finrank]
  rw [Strands.chainComplex_congr _ _ (koszulFaces_translated B a c)]

lemma bettiNumber_translated_outside (B : Family V) (a c : Exponent V) (i : ℕ)
    (hc : ¬ c ≤ a) : bettiNumber (k := k) (translatedFamily c B) a i = 0 := by
  apply Strands.bettiNumber_eq_zero_of_exact
  apply exactIn_of_no_face
  intro s hs
  rw [koszulFaces_translated_outside B a c hc] at hs
  exact hs.elim

end Betti
end Characterizations.Isolators

end
end CheckedCharacterizationsSource27

/-! ## Source: Characterizations.Resolution.KoszulRows -/
section CheckedCharacterizationsSource28

/-! Genuine coefficient Koszul rows, their naturality and exactness on free coefficients. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
namespace Characterizations.Resolution
open Classical CategoryTheory CategoryTheory.Limits MvPolynomial CommAlg.Koszul
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev KoszulRows (M : Type u) [Zero M] (i : ℕ) :=
  Set.powersetCard V i →₀ M

abbrev rowDifferential (M : Type u) [AddCommGroup M] [Module (MvPolynomial V k) M] (i : ℕ) :
    KoszulRows (V := V) M (i + 1) →ₗ[MvPolynomial V k] KoszulRows (V := V) M i :=
  coordinateDifferential (X : V → MvPolynomial V k) (ModuleCat.of (MvPolynomial V k) M) i

abbrev mapRows {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) :
    KoszulRows (V := V) M i →ₗ[MvPolynomial V k] KoszulRows (V := V) N i :=
  Finsupp.mapRange.linearMap f

@[simp] lemma mapRows_apply {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (z : KoszulRows (V := V) M i) (s) :
    mapRows f i z s = f (z s) := rfl

@[simp] lemma mapRows_single {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (s : Set.powersetCard V i) (m : M) :
    mapRows f i (Finsupp.single s m) = Finsupp.single s (f m) := by
  exact Finsupp.mapRange_single (hf := f.map_zero)

lemma rowDifferential_natural {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (z : KoszulRows (V := V) M (i + 1)) :
    rowDifferential (V := V) (k := k) N i (mapRows f (i + 1) z) = mapRows f i (rowDifferential (V := V) (k := k) M i z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single s m =>
      rw [mapRows_single, coordinateDifferential_single, coordinateDifferential_single, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mapRows_single]
      congr 1
      simp only [map_smul, map_zsmul_unit]

lemma rowDifferential_square {M : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    (i : ℕ) (z : KoszulRows (V := V) M (i + 2)) :
    rowDifferential (V := V) (k := k) M i (rowDifferential (V := V) (k := k) M (i + 1) z) = 0 :=
  LinearMap.congr_fun (coordinateDifferential_comp X (ModuleCat.of (MvPolynomial V k) M) i) z

variable {J : Type}

def HomogeneousRows (i t : ℕ) (z : KoszulRows (V := V) (J → MvPolynomial V k) i) : Prop :=
  ∀ s j, (z s j).IsHomogeneous t

lemma homogeneousRows_zero (i t : ℕ) :
    HomogeneousRows (V := V) (k := k) (J := J) i t 0 := fun _ _ => (homogeneousSubmodule V k t).zero_mem

lemma homogeneousRows_differential {i t : ℕ}
    {z : KoszulRows (V := V) (J → MvPolynomial V k) (i + 1)}
    (hz : HomogeneousRows (i + 1) t z) :
    HomogeneousRows i (t + 1) (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i z) := by
  intro a b
  have hre : z = ∑ s ∈ z.support, Finsupp.single s (z s) := by
    exact (Finsupp.sum_single z).symm
  rw [hre, map_sum]
  simp only [Finsupp.finsetSum_apply, Finset.sum_apply]
  apply IsHomogeneous.sum
  intro s hs
  rw [coordinateDifferential_single]
  simp only [Finsupp.finsetSum_apply, Finset.sum_apply]
  apply IsHomogeneous.sum
  intro j hj
  by_cases he : eraseIndex s j = a
  · simp only [Finsupp.single_apply, he, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    have hsign : ((TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) • z s b).IsHomogeneous t := by
      rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) with h | h
      · rw [h]
        simpa only [one_smul] using hz s b
      · rw [h]
        simpa only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul] using (hz s b).neg
    simpa [Nat.add_comm] using (isHomogeneous_X (R := k) j.val).mul hsign
  · simp only [Finsupp.single_apply, he, ↓reduceIte, Pi.zero_apply]
    exact (homogeneousSubmodule V k _).zero_mem

variable [Nontrivial k] [Fintype J]

/-- Exactness here is transported from the actual regular Koszul complex tensored
with the actual finite free coefficient module. -/
lemma freeRows_exact (i : ℕ)
    (z : KoszulRows (V := V) (J → MvPolynomial V k) (i + 1))
    (hz : rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i z = 0) :
    ∃ w, rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1) w = z := by
  let M := ModuleCat.of (MvPolynomial V k) (J → MvPolynomial V k)
  have hK : (koszulComplex (Fintype.linearCombination (MvPolynomial V k) X)).ExactAt (i + 1) :=
    (koszulComplex.exactAt_of_isRegular (finiteVariableList (V := V) (k := k))
      finite_variables_regular (i + 1) (by omega)).of_iso finiteVariableKoszulIso
  have hF : (familyCoefficientComplex (X : V → MvPolynomial V k) M).ExactAt (i + 1) := by
    change ((koszulComplex (Fintype.linearCombination (MvPolynomial V k) X)).sc (i + 1)).map
      (CategoryTheory.MonoidalCategory.tensorRight M) |>.Exact
    exact Module.Flat.rTensor_shortComplex_exact M _ hK
  have hC := hF.of_iso (coordinateComplexIso X M)
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at hC
  change LinearMap.range (ModuleCat.Hom.hom ((coordinateComplex X M).d (i + 2) (i + 1))) =
    LinearMap.ker (ModuleCat.Hom.hom ((coordinateComplex X M).d (i + 1) i)) at hC
  rw [coordinateComplex_d, coordinateComplex_d] at hC
  change LinearMap.range (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1)) =
    LinearMap.ker (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i) at hC
  have hm : z ∈ LinearMap.range (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1)) := by
    rw [hC]
    exact hz
  exact hm

lemma homogeneous_mem_variables {f : MvPolynomial V k} {t : ℕ}
    (hf : f.IsHomogeneous t) (ht : 0 < t) : f ∈ idealOfVars V k := by
  rw [idealOfVars_eq_restrictSupportIdeal]
  intro a ha
  have he : a.degree = t := by
    simpa only [← Finsupp.degree_apply] using (hf.degree_eq_sum_deg_support ha).symm
  change 1 ≤ a.degree
  omega

lemma rowDifferential_singleton (i : V) (m : J → MvPolynomial V k) :
    rowDifferential (V := V) (k := k) (J → MvPolynomial V k) 0
      (Finsupp.single (⟨{i}, by simp⟩ : Set.powersetCard V 1) m) =
      Finsupp.single (⟨∅, by simp⟩ : Set.powersetCard V 0) ((X i : MvPolynomial V k) • m) := by
  rw [coordinateDifferential_single]
  have hsub : ∀ j : {j // j ∈ ({i} : Finset V)}, j.val = i := fun j => Finset.mem_singleton.mp j.property
  have he : ∀ j : {j // j ∈ ({i} : Finset V)},
      eraseIndex (⟨{i}, by simp⟩ : Set.powersetCard V 1) j = ⟨∅, by simp⟩ := by
    intro j
    apply Subtype.ext
    simp [eraseIndex, hsub j]
  simp only [he, hsub]
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt]
  have hf : ({i} : Finset V).filter (fun j => j < i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
    have he := Finset.mem_singleton.mp hj
    exact (lt_irrefl i) (he ▸ hlt)
  simp only [hf, Finset.card_empty, pow_zero, one_smul]
  simp

/-- Positive homogeneous polynomial coefficients vanish in zeroth free Koszul homology. -/
lemma freeRows_zero_boundary {t : ℕ} (ht : 0 < t)
    (z : KoszulRows (V := V) (J → MvPolynomial V k) 0)
    (hz : HomogeneousRows 0 t z) :
    ∃ w, rowDifferential (V := V) (k := k) (J → MvPolynomial V k) 0 w = z := by
  let e : Set.powersetCard V 0 := ⟨∅, by simp⟩
  have hex : ∀ j : J, ∃ c : V → MvPolynomial V k, ∑ v, c v * X v = z e j := by
    intro j
    exact Ideal.mem_span_range_iff_exists_fun.mp (homogeneous_mem_variables (hz e j) ht)
  choose c hc using hex
  refine ⟨∑ v : V, Finsupp.single (⟨{v}, by simp⟩ : Set.powersetCard V 1) (fun j => c j v), ?_⟩
  rw [map_sum]
  simp_rw [rowDifferential_singleton]
  apply Finsupp.ext
  intro s
  funext j
  have hs : s = e := Subtype.ext (Finset.card_eq_zero.mp s.property)
  subst s
  simp only [e, Finsupp.finsetSum_apply, Finsupp.single_eq_same, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using hc j

end Characterizations.Resolution

end
end CheckedCharacterizationsSource28

/-! ## Source: Characterizations.Resolution.KoszulStaircase -/
section CheckedCharacterizationsSource29

/-! A graded double-complex staircase, proved by actual element lifting. -/
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

namespace Resolution

lemma mapRows_comp {M N Q : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    [AddCommGroup Q] [Module (MvPolynomial V k) Q]
    (f : M →ₗ[MvPolynomial V k] N) (g : N →ₗ[MvPolynomial V k] Q)
    (i : ℕ) (z : KoszulRows (V := V) M i) :
    mapRows g i (mapRows f i z) = mapRows (g ∘ₗ f) i z := by
  apply Finsupp.ext
  intro s
  rfl

lemma homogeneousRows_lift {J L : Type} [Fintype J] [Fintype L]
    (f : (J → MvPolynomial V k) →ₗ[MvPolynomial V k] (L → MvPolynomial V k))
    (hf : IsHomogeneousMap f 1) {i t : ℕ}
    (z : KoszulRows (V := V) (L → MvPolynomial V k) i)
    (hz : HomogeneousRows i (t + 1) z)
    (hmem : ∀ s, z s ∈ LinearMap.range f) :
    ∃ w : KoszulRows (V := V) (J → MvPolynomial V k) i,
      HomogeneousRows i t w ∧ mapRows f i w = z := by
  have hh : ∀ s, ∃ x, IsHomogeneousVector x t ∧ f x = z s := by
    intro s
    apply exists_homogeneous_lift f hf ?_ (hmem s)
    intro j
    simpa only [Nat.add_comm] using hz s j
  choose w hw he using hh
  refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_⟩
  · intro s j
    exact hw s j
  · apply Finsupp.ext
    intro s
    exact he s

end Resolution

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

lemma row_differential_comp (n i : ℕ)
    (z : KoszulRows (V := V) (P.Index (n + 2) → MvPolynomial V k) i) :
    mapRows (P.differential n) i (mapRows (P.differential (n + 1)) i z) = 0 := by
  rw [mapRows_comp, P.differential_comp]
  ext s
  rfl

/-- The diagonal chase uses homogeneous lifts of the exact vertical complex and
actual positive-degree Koszul exactness in the horizontal direction. -/
lemma koszul_staircase (t : ℕ) (ht : 0 < t) : ∀ (i n : ℕ)
    (z : KoszulRows (V := V) (P.Index n → MvPolynomial V k) (i + 1)),
    HomogeneousRows (i + 1) t z →
    (∃ y : KoszulRows (V := V) (P.Index (n + 1) → MvPolynomial V k) i,
      HomogeneousRows i t y ∧ mapRows (P.differential n) i y =
        rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) i z) →
    ∃ (u : KoszulRows (V := V) (P.Index n → MvPolynomial V k) (i + 2))
      (v : KoszulRows (V := V) (P.Index (n + 1) → MvPolynomial V k) (i + 1)),
      z = rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1) u +
        mapRows (P.differential n) (i + 1) v := by
  intro i
  induction i with
  | zero =>
      intro n z hz hLift
      obtain ⟨y, hy, he⟩ := hLift
      obtain ⟨v, hv⟩ := freeRows_zero_boundary ht y hy
      have hcycle : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) 0
          (z - mapRows (P.differential n) 1 v) = 0 := by
        rw [map_sub, rowDifferential_natural, hv, he, sub_self]
      obtain ⟨u, hu⟩ := freeRows_exact 0 _ hcycle
      refine ⟨u, v, ?_⟩
      rw [hu]
      exact (sub_add_cancel _ _).symm
  | succ i ih =>
      intro n z hz hLift
      obtain ⟨y, hy, he⟩ := hLift
      have hcycle : mapRows (P.differential n) i
          (rowDifferential (V := V) (k := k) (P.Index (n + 1) → MvPolynomial V k) i y) = 0 := by
        rw [← rowDifferential_natural, he, rowDifferential_square]
      have hmem : ∀ s, (rowDifferential (V := V) (k := k) (P.Index (n + 1) → MvPolynomial V k) i y) s ∈
          LinearMap.range (P.differential (n + 1)) := by
        intro s
        rw [P.exact_succ n]
        exact congrArg (fun z => z s) hcycle
      obtain ⟨w, hw, hwe⟩ := homogeneousRows_lift (P.differential (n + 1))
        (P.linear (n + 1)) _ (homogeneousRows_differential hy) hmem
      obtain ⟨u, v, huv⟩ := ih (n + 1) y hy ⟨w, hw, hwe⟩
      have hd : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1) z =
          rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1)
            (mapRows (P.differential n) (i + 2) u) := by
        rw [← he, huv, map_add, P.row_differential_comp, add_zero, rowDifferential_natural]
      have hcycle' : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1)
          (z - mapRows (P.differential n) (i + 2) u) = 0 := by rw [map_sub, hd, sub_self]
      obtain ⟨w', hw'⟩ := freeRows_exact (i + 1) _ hcycle'
      refine ⟨w', u, ?_⟩
      rw [hw']
      exact (sub_add_cancel _ _).symm

lemma augmentation_rows_lift (i t : ℕ)
    (z : KoszulRows (V := V) (MvPolynomial V k) i)
    (hz : ∀ s, (z s).IsHomogeneous (d + t)) (hmem : ∀ s, z s ∈ I) :
    ∃ w : KoszulRows (V := V) (P.Index 0 → MvPolynomial V k) i,
      HomogeneousRows i t w ∧ mapRows P.augmentation i w = z := by
  have hh : ∀ s, ∃ x, IsHomogeneousVector x t ∧ P.augmentation x = z s := by
    intro s
    have hs : z s ∈ LinearMap.range P.augmentation := by rw [P.augmentation_range]; exact hmem s
    obtain ⟨x, hx⟩ := hs
    refine ⟨component t x, component_homogeneous _ _, ?_⟩
    rw [← P.augmentation_component, hx, homogeneousComponent_eq_self (hz s)]
  choose w hw he using hh
  refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_⟩
  · intro s j
    exact hw s j
  · apply Finsupp.ext
    intro s
    exact he s

lemma augmentationToIdeal_rows_comp (i : ℕ)
    (z : KoszulRows (V := V) (P.Index 1 → MvPolynomial V k) i) :
    mapRows P.augmentationToIdeal i (mapRows (P.differential 0) i z) = 0 := by
  apply Finsupp.ext
  intro s
  apply Subtype.ext
  exact LinearMap.congr_fun P.augmentation_comp (z s)

/-- Genuine coefficient Koszul cycles with coefficient degree strictly above the
linear generator degree are actual boundaries. -/
lemma idealRows_boundary_above (t : ℕ) (ht : 0 < t) (i : ℕ)
    (z : KoszulRows (V := V) I i) (hz : ∀ s, (z s).val.IsHomogeneous (d + t))
    (hcycle : ∀ j (he : i = j + 1), rowDifferential (V := V) (k := k) I j (he ▸ z) = 0) :
    ∃ w : KoszulRows (V := V) I (i + 1), rowDifferential (V := V) (k := k) I i w = z := by
  let incl : I →ₗ[MvPolynomial V k] MvPolynomial V k := I.subtype
  let zs := mapRows incl i z
  obtain ⟨x, hx, hxe⟩ := P.augmentation_rows_lift i t zs hz (fun s => (z s).property)
  have haug : mapRows P.augmentationToIdeal i x = z := by
    apply Finsupp.ext
    intro s
    apply Subtype.ext
    exact congrArg (fun w => w s) hxe
  cases i with
  | zero =>
      obtain ⟨u, hu⟩ := freeRows_zero_boundary ht x hx
      refine ⟨mapRows P.augmentationToIdeal 1 u, ?_⟩
      rw [rowDifferential_natural, hu, haug]
  | succ i =>
      have hz0 : rowDifferential (V := V) (k := k) I i z = 0 := hcycle i rfl
      have hcyclex : mapRows P.augmentation i
          (rowDifferential (V := V) (k := k) (P.Index 0 → MvPolynomial V k) i x) = 0 := by
        rw [← rowDifferential_natural, hxe]
        change rowDifferential (V := V) (k := k) (MvPolynomial V k) i (mapRows incl (i + 1) z) = 0
        rw [rowDifferential_natural, hz0, map_zero]
      have hmem : ∀ s, (rowDifferential (V := V) (k := k) (P.Index 0 → MvPolynomial V k) i x) s ∈
          LinearMap.range (P.differential 0) := by
        intro s
        rw [P.exact_zero]
        exact congrArg (fun w => w s) hcyclex
      obtain ⟨y, hy, hye⟩ := homogeneousRows_lift (P.differential 0) (P.linear 0) _
        (homogeneousRows_differential hx) hmem
      obtain ⟨u, v, huv⟩ := P.koszul_staircase t ht i 0 x hx ⟨y, hy, hye⟩
      refine ⟨mapRows P.augmentationToIdeal (i + 2) u, ?_⟩
      rw [rowDifferential_natural, ← haug, huv, map_add, P.augmentationToIdeal_rows_comp, add_zero]

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource29

/-! ## Source: Characterizations.Strands.DeletedFaces -/
section CheckedCharacterizationsSource30

/-! # Complete multigraded face calculation for a deleted Veronese generator -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

lemma degree_sub_faceExponent {a : Exponent V} {s : Finset V} (hs : faceExponent s ≤ a) :
    (a - faceExponent s).degree + s.card = a.degree := by
  simpa only [subsetSum_univ, Finset.inter_univ] using subsetSum_sub_faceExponent hs Finset.univ

lemma deleted_faces_iff (a b : Exponent V) (ha : 2 ≤ a.support.card) (s : Finset V) :
    koszulFaces (deletedVeronese a) b s ↔
      s ⊆ b.support ∧ a.degree + s.card ≤ b.degree ∧ b - faceExponent s ≠ a := by
  rw [koszulFaces, deletedVeronese_contains a _ ha]
  constructor
  · rintro ⟨hdiv, hdeg, hne⟩
    exact ⟨(faceExponent_le_iff_subset_support s b).mp hdiv,
      by have h := degree_sub_faceExponent hdiv; omega, hne⟩
  · rintro ⟨hs, hdeg, hne⟩
    have hdiv := (faceExponent_le_iff_subset_support s b).mpr hs
    exact ⟨hdiv, by have h := degree_sub_faceExponent hdiv; omega, hne⟩

lemma deleted_faces_extension_low (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (e : V) (he : e ∈ b.support) (i : ℕ) (hdeg : a.degree + i + 1 < b.degree) :
    ∀ s, koszulFaces (deletedVeronese a) b s → s.card = i → e ∉ s →
      koszulFaces (deletedVeronese a) b (insert e s) := by
  intro s hs hc hes
  obtain ⟨hsub, hbound, hne⟩ := (deleted_faces_iff a b ha s).mp hs
  apply (deleted_faces_iff a b ha _).mpr
  have hsub' := Finset.insert_subset he hsub
  have hcard : (insert e s).card = i+1 := by simp [hes, hc]
  refine ⟨hsub', by omega, ?_⟩
  intro hbad
  have hh := degree_sub_faceExponent ((faceExponent_le_iff_subset_support _ b).mpr hsub')
  rw [hbad, hcard] at hh
  omega

lemma deleted_faces_eq_boundary (a : Exponent V) (ha : 2 ≤ a.support.card)
    (T : Finset V) (hT : a.support ⊆ T) :
    koszulFaces (deletedVeronese a) (a + faceExponent T) = simplexBoundary T := by
  have hsupp : (a + faceExponent T).support = T := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, faceExponent_apply]
    by_cases hj : j ∈ T
    · simp [hj]
    · have ha0 : a j = 0 := Finsupp.notMem_support_iff.mp (fun hh => hj (hT hh))
      simp [hj, ha0]
  have hdeg : (a + faceExponent T).degree = a.degree + T.card := by
    rw [map_add]
    have hd := degree_sub_faceExponent (a := faceExponent T) (le_refl _)
    simpa using hd.symm
  funext s
  apply propext
  rw [deleted_faces_iff a _ ha s, hsupp, hdeg]
  constructor
  · rintro ⟨hs, hc, hne⟩
    exact ⟨hs, fun hTs => hne (by rw [Finset.Subset.antisymm hs hTs]; simp)⟩
  · intro hs
    refine ⟨hs.subset, by have h := Finset.card_le_card hs.subset; omega, ?_⟩
    intro he
    have hdiv : faceExponent s ≤ a + faceExponent T :=
      (faceExponent_mono hs.subset).trans (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    have hh := degree_sub_faceExponent hdiv
    rw [he, hdeg] at hh
    have hlt := Finset.card_lt_card hs
    omega

section Ring
variable [CommRing k]

lemma faceExponent_injective : Function.Injective (faceExponent (V := V)) := by
  intro s t he
  ext j
  have h := congrArg (fun a : Exponent V => a j) he
  simp only [faceExponent_apply] at h
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

lemma deleted_faces_exact_critical (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : b.degree = a.degree + i + 1)
    (hn : ¬ ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  have hb : b.support.Nonempty := by
    by_contra hb
    have he : b = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hb)
    subst b
    simp at hdeg
  have hex : ∃ e ∈ b.support, ∀ T : Finset V, b = a + faceExponent T → e ∉ T := by
    by_cases hT : ∃ T : Finset V, b = a + faceExponent T
    · obtain ⟨T, hT⟩ := hT
      have hcard : T.card = i+1 := by
        have hh := degree_sub_faceExponent (a := faceExponent T) (le_refl _)
        have he := congrArg Finsupp.degree hT
        simp only [map_add, tsub_self, map_zero, zero_add] at hh he
        omega
      have hsub : ¬a.support ⊆ T := fun h => hn ⟨T, h, hcard, hT⟩
      obtain ⟨e, hea, heT⟩ := Finset.not_subset.mp hsub
      have heb : e ∈ b.support := by
        rw [hT, Finsupp.mem_support_iff, Finsupp.add_apply]
        have hepos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hea)
        omega
      refine ⟨e, heb, ?_⟩
      intro T' hT'
      have heq := faceExponent_injective (add_left_cancel (hT.symm.trans hT'))
      simpa only [← heq] using heT
    · obtain ⟨e, he⟩ := hb
      exact ⟨e, he, fun T heq => (hT ⟨T, heq⟩).elim⟩
  obtain ⟨e, he, heT⟩ := hex
  apply exactIn_of_degree_extension e i
  intro s hs hc hes
  obtain ⟨hsub, hbound, hne⟩ := (deleted_faces_iff a b ha s).mp hs
  apply (deleted_faces_iff a b ha _).mpr
  have hsub' := Finset.insert_subset he hsub
  have hcard : (insert e s).card = i+1 := by simp [hes, hc]
  refine ⟨hsub', by omega, ?_⟩
  intro heq
  have hdiv := (faceExponent_le_iff_subset_support _ b).mpr hsub'
  have hb' : b = a + faceExponent (insert e s) := by
    rw [← heq]
    exact (tsub_add_cancel_of_le hdiv).symm
  exact heT (insert e s) hb' (Finset.mem_insert_self e s)

lemma deleted_faces_exact_of_large_degree (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : a.degree + i + 1 < b.degree) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  have hb : b.support.Nonempty := by
    by_contra hb
    have he : b = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hb)
    subst b
    simp at hdeg
  obtain ⟨e, he⟩ := hb
  exact exactIn_of_degree_extension e i (deleted_faces_extension_low a b ha e he i hdeg)

lemma deleted_faces_exact_of_small_degree (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : b.degree < a.degree + i) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  apply exactIn_of_no_face
  intro s hs hc
  have hh := ((deleted_faces_iff a b ha s).mp hs).2.1
  omega

lemma deleted_faces_nonzero_iff_off_linear [Nontrivial k] (a b : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    NonzeroHomology (k := k) (koszulFaces (deletedVeronese a) b) i ↔
      ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T := by
  constructor
  · intro h
    by_contra hn
    have hnot := (nonzeroHomology_iff_not_exactIn _ _).mp h
    by_cases hsmall : b.degree < a.degree+i
    · exact hnot (deleted_faces_exact_of_small_degree a b ha i hsmall)
    by_cases hlarge : a.degree+i+1 < b.degree
    · exact hnot (deleted_faces_exact_of_large_degree a b ha i hlarge)
    exact hnot (deleted_faces_exact_critical a b ha i (by omega) hn)
  · rintro ⟨T, hT, hc, rfl⟩
    rw [deleted_faces_eq_boundary a ha T hT]
    exact simplexBoundary_nonzero T i hc

end Ring
end Characterizations.Strands

end
end CheckedCharacterizationsSource30

/-! ## Source: Characterizations.Strands.DeletedBetti -/
section CheckedCharacterizationsSource31

/-! # Proposition 4.3: all nonlinear multigraded and total Betti numbers -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def exceptionalFaces (a : Exponent V) (i : ℕ) : Finset (Finset V) :=
  ((Finset.univ : Finset V).powersetCard (i+1)).filter (a.support ⊆ ·)

def exceptionalDegrees (a : Exponent V) (i : ℕ) : Finset (Exponent V) :=
  (exceptionalFaces a i).image (fun T => a + faceExponent T)

@[simp] lemma mem_exceptionalFaces (a : Exponent V) (i : ℕ) (T : Finset V) :
    T ∈ exceptionalFaces a i ↔ a.support ⊆ T ∧ T.card = i+1 := by
  simp [exceptionalFaces, and_comm]

@[simp] lemma mem_exceptionalDegrees (a b : Exponent V) (i : ℕ) :
    b ∈ exceptionalDegrees a i ↔
      ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T := by
  simp only [exceptionalDegrees, Finset.mem_image, mem_exceptionalFaces]
  constructor
  · rintro ⟨T, ⟨hT, hc⟩, he⟩; exact ⟨T, hT, hc, he.symm⟩
  · rintro ⟨T, hT, hc, he⟩; exact ⟨T, ⟨hT, hc⟩, he.symm⟩

lemma degree_faceExponent (T : Finset V) : (faceExponent T).degree = T.card := by
  have h := degree_sub_faceExponent (a := faceExponent T) (s := T) (le_refl _)
  simpa using h.symm

lemma exceptionalDegrees_degree {a b : Exponent V} {i : ℕ}
    (h : b ∈ exceptionalDegrees a i) : b.degree = a.degree+i+1 := by
  obtain ⟨T, hT, hc, rfl⟩ := (mem_exceptionalDegrees a b i).mp h
  rw [map_add, degree_faceExponent, hc]
  omega

lemma deletedVeronese_betti_off_linear (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    bettiNumber (k := k) (deletedVeronese a) b i =
      if b ∈ exceptionalDegrees a i then 1 else 0 := by
  split_ifs with hb
  · obtain ⟨T, hT, hc, rfl⟩ := (mem_exceptionalDegrees a b i).mp hb
    exact bettiNumber_eq_one_of_boundary _ _ T i hc (deleted_faces_eq_boundary a ha T hT)
  · apply Nat.eq_zero_of_not_pos
    rw [bettiNumber_pos_iff_faces, deleted_faces_nonzero_iff_off_linear a b ha i hoff,
      ← mem_exceptionalDegrees]
    exact hb

lemma deletedVeronese_first_nonlinear (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ i < a.support.card - 1, ∀ b, b.degree ≠ a.degree+i →
      bettiNumber (k := k) (deletedVeronese a) b i = 0) ∧
    bettiNumber (k := k) (deletedVeronese a) (a + faceExponent a.support)
      (a.support.card - 1) = 1 := by
  constructor
  · intro i hi b hoff
    rw [deletedVeronese_betti_off_linear a b ha i hoff, if_neg]
    intro hb
    obtain ⟨T, hT, hc, _⟩ := (mem_exceptionalDegrees a b i).mp hb
    have hh := Finset.card_le_card hT
    omega
  · exact bettiNumber_eq_one_of_boundary _ _ a.support _ (by omega)
      (deleted_faces_eq_boundary a ha a.support (Finset.Subset.refl _))

/-- Total-degree Betti number, the sum of the genuine finite multigraded dimensions. -/
def totalBettiNumber (B : Family V) (i j : ℕ) : ℕ :=
  ∑ b ∈ (Finsupp.finite_of_degree_eq (σ := V) j).toFinset, bettiNumber (k := k) B b i

lemma exceptionalDegrees_card (a : Exponent V) (i : ℕ) :
    (exceptionalDegrees a i).card =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V - a.support.card) (i+1-a.support.card) else 0 := by
  rw [exceptionalDegrees, Finset.card_image_of_injective]
  · by_cases h : a.support.card ≤ i+1
    · rw [if_pos h]
      exact (Finset.card_filter_powersetCard_subset a.support Finset.univ (i+1)
        (Finset.subset_univ _) h).trans (by simp)
    · rw [if_neg h]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hs, hc⟩ := (mem_exceptionalFaces a i T).mp hT
      exact h (hc ▸ Finset.card_le_card hs)
  · intro T U he
    exact faceExponent_injective (add_left_cancel he)

lemma deletedVeronese_total_nonlinear (a : Exponent V) (ha : 2 ≤ a.support.card) (i : ℕ) :
    totalBettiNumber (k := k) (deletedVeronese a) i (a.degree+i+1) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V - a.support.card) (i+1-a.support.card) else 0 := by
  rw [totalBettiNumber]
  trans (exceptionalDegrees a i).card
  · have he : ∀ b ∈ (Finsupp.finite_of_degree_eq (σ := V) (a.degree+i+1)).toFinset,
        bettiNumber (k := k) (deletedVeronese a) b i =
          if b ∈ exceptionalDegrees a i then 1 else 0 := by
      intro b hb
      have hd : b.degree = a.degree+i+1 := by simpa using hb
      exact deletedVeronese_betti_off_linear a b ha i (by omega)
    rw [Finset.sum_congr rfl he, Finset.sum_boole]
    simp only [Nat.cast_id]
    apply congrArg Finset.card
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using exceptionalDegrees_degree h, h⟩⟩
  · exact exceptionalDegrees_card a i

lemma deletedVeronese_total_other (a : Exponent V) (ha : 2 ≤ a.support.card) (i j : ℕ)
    (hlin : j ≠ a.degree+i) (hnonlin : j ≠ a.degree+i+1) :
    totalBettiNumber (k := k) (deletedVeronese a) i j = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  have hd : b.degree = j := by simpa using hb
  rw [deletedVeronese_betti_off_linear a b ha i (hd ▸ hlin), if_neg]
  intro he
  exact hnonlin (hd.symm.trans (exceptionalDegrees_degree he))

end Characterizations.Strands

end
end CheckedCharacterizationsSource31

/-! ## Source: Characterizations.Resolution.Betti -/
section CheckedCharacterizationsSource32

/-! # An actual linear free resolution forces genuine graded Tor concentration -/
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

namespace Resolution
lemma homogeneousPiece_coeff_homogeneous (B : Family V) (a : Exponent V) (i e : ℕ)
    (hdegree : a.degree = e+i) {z : KoszulRows (V := V) (monomialIdeal k B) i}
    (hz : z ∈ homogeneousPiece (k := k) B a i) :
    ∀ s, (z s).val.IsHomogeneous e := by
  change z ∈ Submodule.span k (monomialCoefficientBasis (k := k) B i ''
    {t | monomialDegree t = a}) at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨s, b⟩, hb, rfl⟩ := hx
    have hbd : b.val.degree = e := by
      have hd := congrArg Finsupp.degree hb
      change (b.val + faceExponent s.val).degree = a.degree at hd
      rw [map_add, Strands.degree_faceExponent, s.property, hdegree] at hd
      omega
    intro q
    rw [monomialCoefficientBasis_apply]
    by_cases hqs : s = q
    · subst q
      simp only [Finsupp.single_eq_same, monomialBasis_val]
      exact isHomogeneous_monomial (1 : k) hbd
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hqs), ZeroMemClass.coe_zero]
      exact (homogeneousSubmodule V k e).zero_mem
  | zero => intro s; exact (homogeneousSubmodule V k e).zero_mem
  | add x y hx hy ihx ihy => intro s; exact (ihx s).add (ihy s)
  | smul c x hx ih => intro s; exact (homogeneousSubmodule V k e).smul_mem c (ih s)
end Resolution

namespace LinearResolution

lemma homogeneous_exact_above (B : Family V) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i t : ℕ)
    (ht : 0 < t) (hdegree : a.degree = d+t+i) :
    (homogeneousComplex (k := k) B a).ExactAt i := by
  have hfill (z : homogeneousPiece (k := k) B a i)
      (hz : ∀ j (he : i = j+1), homogeneousDifferential (k := k) B a j (he ▸ z) = 0) :
      ∃ w : homogeneousPiece (k := k) B a (i+1), homogeneousDifferential B a i w = z := by
    have hh := Resolution.homogeneousPiece_coeff_homogeneous B a i (d+t) hdegree z.property
    have hcycle : ∀ j (he : i = j+1),
        rowDifferential (V := V) (k := k) (monomialIdeal k B) j (he ▸ z.val) = 0 := by
      intro j he
      subst i
      exact congrArg Subtype.val (hz j rfl)
    obtain ⟨w, hw⟩ := P.idealRows_boundary_above t ht i z.val hh hcycle
    refine ⟨⟨homogeneousProjection B a (i+1) w, homogeneousProjection_mem B a (i+1) w⟩, ?_⟩
    apply Subtype.ext
    change monomialDifferential (k := k) B i (homogeneousProjection B a (i+1) w) = z.val
    have hp := LinearMap.congr_fun (homogeneousProjection_differential B a i) w
    simp only [LinearMap.comp_apply] at hp
    rw [← hp]
    change homogeneousProjection B a i
      (rowDifferential (V := V) (k := k) (monomialIdeal k B) i w) = z.val
    rw [hw]
    exact CommAlg.Grading.projection_eq_self z.property
  cases i with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    rw [homogeneousComplex_d, (homogeneousComplex (k := k) B a).shape 0 0 (by simp)]
    change ∀ z : homogeneousPiece (k := k) B a 0, (0 : homogeneousPiece (k := k) B a 0) = 0 →
      ∃ w : homogeneousPiece (k := k) B a 1, homogeneousDifferential B a 0 w = z
    intro z _
    exact hfill z (fun j he => by omega)
  | succ j =>
    rw [HomologicalComplex.exactAt_iff' _ (j+2) (j+1) j (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    simp only [homogeneousComplex_d]
    change ∀ z : homogeneousPiece (k := k) B a (j+1), homogeneousDifferential B a j z = 0 →
      ∃ w : homogeneousPiece (k := k) B a (j+2), homogeneousDifferential B a (j+1) w = z
    intro z hz
    apply hfill z
    intro l he
    have heq : l = j := by omega
    subst l
    exact hz

lemma gradedBetti_degree (B : Family V) (hanti : Antichain B) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) : a.degree = d+i := by
  have hdeg := LinearResolution.equigenerated_of_monomial B hanti P
  have hlow : d+i ≤ a.degree := by
    by_contra hlow
    have hn := (gradedBettiNonzero_iff_faces B a i).mp h
    apply ((CommAlg.Simplicial.nonzeroHomology_iff_not_exactIn _ _).mp hn)
    apply CommAlg.Simplicial.exactIn_of_no_face
    intro s hs hcard
    obtain ⟨b, hb, hba⟩ := hs.2
    have hd := Strands.degree_sub_faceExponent hs.1
    have hbd := degree_mono hba
    rw [hdeg b hb] at hbd
    omega
  by_contra heq
  let t := a.degree-(d+i)
  have ht : 0 < t := by dsimp [t]; omega
  have hsum : a.degree = d+t+i := by dsimp [t]; omega
  have hx := homogeneous_exact_above B P a i t ht hsum
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hx
  apply h
  exact (gradedTorIso (k := k) B a i).isZero_iff.mp hz

lemma bettiNumber_eq_zero_off_linear (B : Family V) (hanti : Antichain B) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i : ℕ)
    (hoff : a.degree ≠ d+i) : bettiNumber (k := k) B a i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hoff (gradedBetti_degree B hanti P a i ((bettiNumber_pos_iff B a i).mp hp))

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource32

/-! ## Source: Characterizations.Isolators.Sharp -/
section CheckedCharacterizationsSource33

/-! # Exact sharpness: a prescribed first nonlinear derived-Tor position -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- All earlier homological positions are linear, and the displayed position has
an actual nonzero derived-Tor component in a strictly larger total degree. -/
def FirstNonlinear (B : Family V) (d r : ℕ) : Prop :=
  (∀ i < r, ∀ b, b.degree ≠ d+i → bettiNumber (k := k) B b i = 0) ∧
  ∃ b, d+r < b.degree ∧ 0 < bettiNumber (k := k) B b r

lemma firstNonlinear_not_linear {B : Family V} {d r : ℕ}
    (hBne : B.Nonempty) (hdeg : Equigenerated B d) (hfirst : FirstNonlinear (k := k) B d r) :
    ¬ HasLinearResolution (monomialIdeal k B) := by
  rintro ⟨e, ⟨P⟩⟩
  have he := LinearResolution.equigenerated_of_monomial B hdeg.antichain P
  obtain ⟨b, hb⟩ := hBne
  have hed : e = d := (he b hb).symm.trans (hdeg b hb)
  subst e
  obtain ⟨a, ha, hp⟩ := hfirst.2
  have hz := LinearResolution.bettiNumber_eq_zero_off_linear B hdeg.antichain P a r (Nat.ne_of_gt ha)
  omega

lemma deletedVeronese_shift_first (a c : Exponent V) (ha : 2 ≤ a.support.card) :
    FirstNonlinear (k := k) (translatedFamily c (deletedVeronese a))
      (a.degree+c.degree) (a.support.card-1) := by
  obtain ⟨hzero, hone⟩ := Strands.deletedVeronese_first_nonlinear (k := k) a ha
  constructor
  · intro i hi b hoff
    by_cases hc : c ≤ b
    · have he : b = (b-c)+c := (tsub_add_cancel_of_le hc).symm
      rw [he, bettiNumber_translated]
      apply hzero i hi (b-c)
      intro hd
      apply hoff
      rw [he, map_add, hd]
      omega
    · exact bettiNumber_translated_outside _ _ _ _ hc
  · refine ⟨(a+faceExponent a.support)+c, ?_, ?_⟩
    · rw [map_add, map_add, Strands.degree_faceExponent]
      omega
    · rw [bettiNumber_translated, hone]
      exact Nat.zero_lt_one

lemma restrict_support_card (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    (restrictExponent U q).support.card = q.support.card := by
  rw [restrictExponent, Finsupp.support_subtypeDomain, Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr hq]

lemma restrict_degree_eq (U : Finset V) (q : Exponent V) (hq : q.support ⊆ U) :
    (restrictExponent U q).degree = q.degree := by
  rw [restrictExponent_degree, Finsupp.degree_eq_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hiU
  exact Finsupp.notMem_support_iff.mp (fun h => hiU (hq h))

lemma shiftedPure_local_linear (U R : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (hRU : R ≠ U) :
    HasLinearResolution (monomialIdeal k (localFamily (translatedFamily c (pureIsolator U q)) R)) := by
  rw [localFamily_translated]
  by_cases hUR : U ⊆ R
  · rw [pureIsolator_local_contain U R q hq hsupp hUR]
    refine ⟨_, translated_deletedBounded_linearResolution _ _ _ _ ?_ ?_⟩
    · intro i hi
      exact removedExponent_saturated U q hq i.val ((mem_retainedCaps _ _ _).mp hi)
    · have hex : ∃ i ∈ R, i ∉ U := by
        by_contra hn
        push_neg at hn
        exact hRU (le_antisymm hn hUR)
      obtain ⟨i, hiR, hiU⟩ := hex
      exact ⟨⟨i, hiR⟩, by simp [hiU]⟩
  · rw [pureIsolator_local_omit U R q hsupp hUR]
    have he : translatedFamily (restrictExponent R c) ({0} : Family R) = {restrictExponent R c} := by
      simp [translatedFamily]
    rw [he]
    exact linearResolution_of_polymatroidal (singleton_polymatroidal _)

lemma shiftedPure_first (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    FirstNonlinear (k := k) (localFamily (translatedFamily c (pureIsolator U q)) U)
      (q.degree+(restrictExponent U c).degree) (q.support.card-1) := by
  rw [localFamily_translated, pureIsolator_local_at U q hq hsupp]
  have hcard := restrict_support_card U q hq
  have hd := restrict_degree_eq U q hq
  have H := deletedVeronese_shift_first (k := k)
    (restrictExponent U q) (restrictExponent U c) (by omega)
  rw [hcard, hd] at H
  convert H using 1
  congr <;> exact Subsingleton.elim _ _

lemma shiftedPure_local_at_degree (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) :
    Equigenerated (localFamily (translatedFamily c (pureIsolator U q)) U)
      (q.degree+(restrictExponent U c).degree) := by
  rw [localFamily_translated, pureIsolator_local_at U q hq hsupp]
  simpa only [restrict_degree_eq U q hq] using translatedFamily_equigenerated
    (deletedVeronese_equigenerated (restrictExponent U q)) (restrictExponent U c)

lemma shiftedPure_unique_bad (U : Finset V) (q c : Exponent V)
    (hq : q.support ⊆ U) (hsupp : 2 ≤ q.support.card) (R : Finset V) :
    HasLinearResolution (monomialIdeal k (localFamily (translatedFamily c (pureIsolator U q)) R))
      ↔ R ≠ U := by
  constructor
  · intro h he
    subst R
    exact firstNonlinear_not_linear
      (localFamily_nonempty (translatedFamily_nonempty (pureIsolator_nonempty U q hq hsupp) c) U)
      (shiftedPure_local_at_degree U q c hq hsupp) (shiftedPure_first U q c hq hsupp) h
  · exact shiftedPure_local_linear U R q c hq hsupp

lemma mixedIsolator_unique_bad (U : Finset V) (a b : V) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) (hT : Uᶜ.Nonempty) (R : Finset V) :
    HasLinearResolution (monomialIdeal k (localFamily (pureIsolator U (Finsupp.single a 1)) R))
      ↔ R ≠ U := by
  constructor
  · rintro ⟨d, ⟨P⟩⟩ he
    subst R
    rw [mixedIsolator_local_at U a ha hT] at P
    exact mixedCore_not_equigenerated (⟨a, ha⟩ : U) ⟨b, hb⟩
      (fun he => hab (congrArg Subtype.val he))
      ⟨d, LinearResolution.equigenerated_of_monomial _ (mixedCore_antichain _) P⟩
  · exact mixedIsolator_local_linear U R a ha hT

end Characterizations.Isolators

end
end CheckedCharacterizationsSource33

/-! ## Source: Characterizations.Isolators.Main -/
section CheckedCharacterizationsSource34

/-! # Propositions 4.7 and 4.10 in the actual localized polynomial rings -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

@[simp] lemma indicatorExponent_support (A : Finset V) : (indicatorExponent A).support = A := by
  ext i
  simp [Finsupp.mem_support_iff, indicatorExponent_apply]

/-- Proposition 4.10: exact degree, all local generation tests, the unique bad
localization, and the sharp first nonlinear position in genuine derived Tor. -/
theorem exists_sharp_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ) (hd : 2 ≤ d)
    (hk : Uᶜ.card ≤ d-2) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) ∧
      Equigenerated (localFamily B U) (d-Uᶜ.card) ∧
      FirstNonlinear (k := k) (localFamily B U) (d-Uᶜ.card)
        (min (d-1-Uᶜ.card) (U.card-1)) := by
  let e := min (d-Uᶜ.card) U.card
  have he2 : 2 ≤ e := le_min (by omega) hm
  have heU : e ≤ U.card := min_le_right _ _
  have hed : e+Uᶜ.card ≤ d := by have := min_le_left (d-Uᶜ.card) U.card; dsimp [e]; omega
  obtain ⟨A, hAU, hAe⟩ := Finset.exists_subset_card_eq heU
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  let q := indicatorExponent A
  let c : Exponent V := Finsupp.single a (d-(e+Uᶜ.card))
  let B := translatedFamily c (pureIsolator U q)
  have hq : q.support ⊆ U := by simpa [q] using hAU
  have hqs : q.support.card = e := by simpa [q] using hAe
  have hqd : q.degree = e := by simpa [q] using hAe
  have hcd : c.degree = d-(e+Uᶜ.card) := Finsupp.degree_single _ _
  have hcU : c.support ⊆ U := by
    intro i hi
    have hai : a = i := by
      by_contra hn
      have hz : c i = 0 := by simp [c, Finsupp.single_apply, hn, Ne.symm hn]
      exact Finsupp.mem_support_iff.mp hi hz
    simpa [← hai] using ha
  have hlocaldeg : q.degree+(restrictExponent U c).degree = d-Uᶜ.card := by
    rw [hqd, restrict_degree_eq U c hcU, hcd]
    omega
  have hposition : q.support.card-1 = min (d-1-Uᶜ.card) (U.card-1) := by
    rw [hqs]
    dsimp [e]
    by_cases h : d-Uᶜ.card ≤ U.card
    · rw [min_eq_left h, min_eq_left (by omega)]
      omega
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
  refine ⟨B, translatedFamily_nonempty (pureIsolator_nonempty U q hq (by omega)) c,
    ?_, translatedFamily_locallyEquigenerated (pureIsolator_locallyEquigenerated U q hq (by omega)) c,
    ?_, ?_, ?_⟩
  · have hh := translatedFamily_equigenerated (pureIsolator_degree U q) c
    have heq : q.degree+Uᶜ.card+c.degree = d := by rw [hqd, hcd]; omega
    simpa only [heq] using hh
  · intro R
    rw [monomialLocalization_eq]
    exact shiftedPure_unique_bad U q c hq (by omega) R
  · simpa only [hlocaldeg] using shiftedPure_local_at_degree U q c hq (by omega)
  · simpa only [hlocaldeg, hposition] using shiftedPure_first (k := k) U q c hq (by omega)

/-- Proposition 4.7(i), including U=E: the smallest exhibited pure degree is k+2. -/
theorem exists_pure_isolator (U : Finset V) (hm : 2 ≤ U.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card+2) ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  obtain ⟨B, hB, hd, hl, hu, _⟩ := exists_sharp_isolator (k := k) U hm (Uᶜ.card+2) (by omega) (by omega)
  exact ⟨B, hB, hd, hl, hu⟩

/-- Proposition 4.7(ii): one mixed-degree localization, all other localizations
having actual linear free resolutions, at the smaller degree k+1. -/
theorem exists_mixed_isolator (U : Finset V) (hm : 2 ≤ U.card) (hk : 1 ≤ Uᶜ.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card+1) ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
  have hT : Uᶜ.Nonempty := Finset.card_pos.mp (by omega)
  let B := pureIsolator U (Finsupp.single a 1)
  have hne : B.Nonempty := by
    exact ⟨_, purePower_mem Uᶜ _ (mixed_removed_support U a ha hT) a (by simpa using ha)⟩
  refine ⟨B, hne, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using pureIsolator_degree U (Finsupp.single a 1)
  · rw [show localFamily B U = mixedCore (⟨a, ha⟩ : U) from mixedIsolator_local_at U a ha hT]
    exact mixedCore_not_equigenerated (⟨a, ha⟩ : U) ⟨b, hb⟩
      (fun he => hab (congrArg Subtype.val he))
  · intro R
    rw [monomialLocalization_eq]
    exact mixedIsolator_unique_bad U a b ha hb hab hT R

/-- The outer-band generation test of Proposition 4.10 is individually necessary. -/
theorem exists_outer_band_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ)
    (hd : 2 ≤ d) (hk : Uᶜ.card = d-1) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  have hpos : 1 ≤ Uᶜ.card := by omega
  obtain ⟨B, hB, he, hbad, hgood⟩ := exists_mixed_isolator (k := k) U hm hpos
  have hdeg : Uᶜ.card+1 = d := by omega
  exact ⟨B, hB, hdeg ▸ he, hbad, hgood⟩

end Characterizations.Isolators

end
end CheckedCharacterizationsSource34

/-! ## Source: Characterizations.Projection -/
section CheckedCharacterizationsSource35

/-! # Monomial localization preserves the full exchange axiom

The minimal projected generators are precisely the projections of the bases
minimizing the total exponent on the retained coordinates. This proves the
localization theorem simultaneously for every retained subset.
-/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem minimum_layer_dominates {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) {a : Exponent V} (ha : a ∈ B) :
    ∃ b ∈ B, subsetSum b U = lowerRank B U ∧ restrictExponent U b ≤ restrictExponent U a := by
  classical
  let L := B.filter (fun b => subsetSum b U = lowerRank B U)
  have hL : L.Nonempty := by
    obtain ⟨b, hb, he⟩ := lowerRank_attained ⟨a, ha⟩ U
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, he⟩⟩
  obtain ⟨b, hbL, hmin⟩ := L.exists_min_image (fun b => ∑ i ∈ U, (b i - a i)) hL
  obtain ⟨hb, hbmin⟩ := Finset.mem_filter.mp hbL
  refine ⟨b, hb, hbmin, ?_⟩
  intro i
  by_contra hn
  have hi : a i < b i := Nat.lt_of_not_ge hn
  obtain ⟨j, hj, hc⟩ := hB.2 b hb a ha i hi
  have hij : i.val ≠ j := by intro h; subst j; omega
  have hsum := subsetSum_exchange b i j (by omega) U
  have hlo := lowerRank_le hc U
  have hjU : j ∈ U := by
    by_contra hjU
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hcmin : subsetSum (exchange b i j) U = lowerRank B U := by
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hbetter : (∑ q ∈ U, (exchange b i j q - a q)) < ∑ q ∈ U, (b q - a q) := by
    apply Finset.sum_lt_sum
    · intro q hq
      by_cases hqi : q = i.val
      · subst q
        simp only [exchange_apply, ↓reduceIte, hij]
        omega
      · by_cases hqj : q = j
        · subst q
          simp only [exchange_apply, hqi, ↓reduceIte]
          omega
        · simp [hqi, hqj]
    · refine ⟨i.val, i.property, ?_⟩
      simp only [exchange_apply, ↓reduceIte, hij]
      omega
  have hbad := hmin (exchange b i j) (Finset.mem_filter.mpr ⟨hc, hcmin⟩)
  omega

theorem localFamily_eq_minimum_layer {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) :
    localFamily B U = (B.filter (fun a => subsetSum a U = lowerRank B U)).image
      (restrictExponent U) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨ha, hminimal⟩ :=
      (mem_minimalFamily.mp ha : a ∈ B.image (restrictExponent U) ∧ _)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c, hc, hcmin, hcb⟩ := minimum_layer_dominates hB U hb
    have he := hminimal (restrictExponent U c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩) hcb
    exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hcmin⟩, he⟩
  · rintro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hbmin⟩ := Finset.mem_filter.mp hb
    apply mem_minimalFamily.mpr
    refine ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro c hc hcb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    apply eq_of_le_of_degree_eq hcb
    apply Nat.le_antisymm (degree_mono hcb)
    rw [restrictExponent_degree, restrictExponent_degree, hbmin]
    exact lowerRank_le hz U

theorem localFamily_equigenerated {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) : Equigenerated (localFamily B U) (lowerRank B U) := by
  intro a ha
  rw [localFamily_eq_minimum_layer hB] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [restrictExponent_degree]
  exact (Finset.mem_filter.mp hb).2

theorem restrict_exchange (U : Finset V) (a : Exponent V) (i j : U) :
    restrictExponent U (exchange a i j) = exchange (restrictExponent U a) i j := by
  ext q
  simp only [restrictExponent_apply, exchange_apply]
  have hqi : q.val = i.val ↔ q = i := Subtype.ext_iff.symm
  have hqj : q.val = j.val ↔ q = j := Subtype.ext_iff.symm
  simp only [hqi, hqj]

/-- Proposition 2.8, with actual minimal generators in the retained-variable ring. -/
theorem localFamily_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) : IsPolymatroidal (localFamily B U) := by
  classical
  refine ⟨⟨lowerRank B U, localFamily_equigenerated hB U⟩, ?_⟩
  intro a ha b hb i hi
  rw [localFamily_eq_minimum_layer hB] at ha hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hx, hxmin⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hymin⟩ := Finset.mem_filter.mp hy
  obtain ⟨j, hj, hz⟩ := hB.2 x hx y hy i hi
  have hsum := subsetSum_exchange x i j (by exact Nat.zero_lt_of_lt hi) U
  have hlo := lowerRank_le hz U
  have hjU : j ∈ U := by
    by_contra hjU
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hzmin : subsetSum (exchange x i j) U = lowerRank B U := by
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  refine ⟨⟨j, hjU⟩, hj, ?_⟩
  rw [← restrict_exchange, localFamily_eq_minimum_layer hB]
  exact Finset.mem_image.mpr ⟨exchange x i j, Finset.mem_filter.mpr ⟨hz, hzmin⟩, rfl⟩

theorem polymatroidal_locallyEquigenerated {B : Family V} (hB : IsPolymatroidal B) :
    LocallyEquigenerated B :=
  (locallyEquigenerated_iff B).mpr (fun U => ⟨lowerRank B U, localFamily_equigenerated hB U⟩)

end Characterizations

end
end CheckedCharacterizationsSource35

/-! ## Source: Characterizations.Resolution.Localizations -/
section CheckedCharacterizationsSource36

/-! # Actual linear resolutions after monomial localization -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The forward implication in Theorem 1.1(A), in the actual polynomial ring on
exactly the retained variables. The conclusion is an exact finite-free complex,
with linear differential matrices, resolving the literal localized ideal. -/
theorem polymatroidal_local_linearResolutions {B : Family V}
    (hB : IsPolymatroidal B) (U : Finset V) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal (localFamily_polymatroidal hB U)

end Characterizations

end
end CheckedCharacterizationsSource36

/-! ## Source: Characterizations.Resolution.KoszulSocleCycle -/
section CheckedCharacterizationsSource37

/-! The actual top Koszul socle cycle and its non-boundary property. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
namespace Characterizations.Resolution
open Classical MvPolynomial CommAlg.Koszul
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

lemma mapRows_injective {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (hf : Function.Injective f) (i : ℕ) :
    Function.Injective (mapRows f i) := by
  intro z w he
  apply Finsupp.ext
  intro s
  exact hf (congrArg (fun z => z s) he)

lemma polynomialRows_homogeneous_differential {i t : ℕ}
    (z : KoszulRows (V := V) (MvPolynomial V k) (i + 1))
    (hz : ∀ s, (z s).IsHomogeneous t) :
    ∀ s, (rowDifferential (V := V) (k := k) (MvPolynomial V k) i z s).IsHomogeneous (t + 1) := by
  let f : MvPolynomial V k →ₗ[MvPolynomial V k] (Unit → MvPolynomial V k) :=
    LinearMap.pi (fun _ => LinearMap.id)
  have hh : HomogeneousRows (i + 1) t (mapRows f (i + 1) z) := fun s _ => hz s
  have h := homogeneousRows_differential hh
  rw [rowDifferential_natural] at h
  exact fun s => h s ()

lemma polynomialRows_exact (i : ℕ)
    (z : KoszulRows (V := V) (MvPolynomial V k) (i + 1))
    (hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) i z = 0) :
    ∃ w, rowDifferential (V := V) (k := k) (MvPolynomial V k) (i + 1) w = z := by
  let f : MvPolynomial V k →ₗ[MvPolynomial V k] (Unit → MvPolynomial V k) :=
    LinearMap.pi (fun _ => LinearMap.id)
  let g : (Unit → MvPolynomial V k) →ₗ[MvPolynomial V k] MvPolynomial V k :=
    LinearMap.proj ()
  have hcycle : rowDifferential (V := V) (k := k) (Unit → MvPolynomial V k) i
      (mapRows f (i + 1) z) = 0 := by rw [rowDifferential_natural, hz, map_zero]
  obtain ⟨w, hw⟩ := freeRows_exact i _ hcycle
  refine ⟨mapRows g (i + 2) w, ?_⟩
  rw [rowDifferential_natural, hw]
  apply Finsupp.ext
  intro s
  rfl

lemma polynomialRows_top_injective (m : ℕ) (hcard : Fintype.card V = m + 1)
    (z : KoszulRows (V := V) (MvPolynomial V k) (m + 1))
    (hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) m z = 0) : z = 0 := by
  obtain ⟨w, hw⟩ := polynomialRows_exact m z hz
  haveI : IsEmpty (Set.powersetCard V (m + 2)) := ⟨fun s => by
    have hs := Finset.card_le_univ s.val
    rw [s.property, hcard] at hs
    omega⟩
  have hw0 : w = 0 := Subsingleton.elim _ _
  simpa only [hw0, map_zero] using hw.symm

variable (I : Ideal (MvPolynomial V k))

def socleBoundary {i : ℕ} (s : Set.powersetCard V (i + 1)) (y : MvPolynomial V k)
    (hy : ∀ j : s.val, X j.val * y ∈ I) : KoszulRows (V := V) I i :=
  ∑ j : s.val, Finsupp.single (eraseIndex s j)
    (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • ⟨X j.val * y, hy j⟩)

lemma socleBoundary_inclusion {i : ℕ} (s : Set.powersetCard V (i + 1)) (y : MvPolynomial V k)
    (hy : ∀ j : s.val, X j.val * y ∈ I) :
    mapRows I.subtype i (socleBoundary I s y hy) =
      rowDifferential (V := V) (k := k) (MvPolynomial V k) i (Finsupp.single s y) := by
  rw [socleBoundary, map_sum, coordinateDifferential_single]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mapRows_single]
  congr 1
  change TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • ((X j.val : MvPolynomial V k) • y) =
    (X j.val : MvPolynomial V k) • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • y)
  exact smul_comm _ _ _

lemma socleBoundary_homogeneous {i e : ℕ} (s : Set.powersetCard V (i + 1))
    (y : MvPolynomial V k) (hy : ∀ j : s.val, X j.val * y ∈ I)
    (hdegree : y.IsHomogeneous e) : ∀ a, ((socleBoundary I s y hy) a).val.IsHomogeneous (e + 1) := by
  have hz : ∀ a, (Finsupp.single s y a).IsHomogeneous e := by
    intro a
    by_cases he : s = a
    · simpa only [Finsupp.single_apply, he, ↓reduceIte] using hdegree
    · simp only [Finsupp.single_apply, he, ↓reduceIte]
      exact (homogeneousSubmodule V k e).zero_mem
  have hh := polynomialRows_homogeneous_differential (Finsupp.single s y) hz
  rw [← socleBoundary_inclusion I s y hy] at hh
  exact hh

lemma socleBoundary_cycle {i : ℕ} (s : Set.powersetCard V (i + 1))
    (y : MvPolynomial V k) (hy : ∀ j : s.val, X j.val * y ∈ I) :
    ∀ j (he : i = j + 1), rowDifferential (V := V) (k := k) I j
      (he ▸ socleBoundary I s y hy) = 0 := by
  intro j he
  subst i
  apply mapRows_injective I.subtype Subtype.val_injective j
  rw [map_zero, ← rowDifferential_natural, socleBoundary_inclusion, rowDifferential_square]

/-- The top socle boundary cannot be a boundary inside the ideal: an incoming
chain would have to have the missing socle element as its top coefficient. -/
lemma socleBoundary_not_boundary (m : ℕ) (hcard : Fintype.card V = m + 1)
    (y : MvPolynomial V k) (hy : ∀ j : V, X j * y ∈ I) (hout : y ∉ I) :
    ¬ ∃ w : KoszulRows (V := V) I (m + 1),
      rowDifferential (V := V) (k := k) I m w =
        socleBoundary I (⟨Finset.univ, hcard⟩ : Set.powersetCard V (m + 1)) y
          (fun j => hy j.val) := by
  rintro ⟨w, hw⟩
  let s : Set.powersetCard V (m + 1) := ⟨Finset.univ, hcard⟩
  have hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) m
      (mapRows I.subtype (m + 1) w - Finsupp.single s y) = 0 := by
    rw [map_sub, rowDifferential_natural, hw, socleBoundary_inclusion, sub_self]
  have he := polynomialRows_top_injective m hcard _ hz
  have hrow : mapRows I.subtype (m + 1) w = Finsupp.single s y := sub_eq_zero.mp he
  have hs := congrArg (fun z => z s) hrow
  simp only [mapRows_apply, Submodule.subtype_apply, Finsupp.single_eq_same] at hs
  exact hout (hs ▸ (w s).property)

end Characterizations.Resolution

end
end CheckedCharacterizationsSource37

/-! ## Source: Characterizations.Socles -/
section CheckedCharacterizationsSource38

/-! # Actual quotient socles and the local-socle characterization

The socle is the subspace of the actual quotient ring annihilated by every
variable. Concentration means that every such class has a homogeneous
representative of the specified degree. The equivalence with the monomial
test is proved, rather than used as a definition of the socle.
-/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid MvPolynomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {k : Type*} [CommRing k] [Nontrivial k]

def quotientSocle (I : Ideal (MvPolynomial V k)) : Set (MvPolynomial V k ⧸ I) :=
  {q | ∀ i : V, Ideal.Quotient.mk I (X i) * q = 0}

def SocleConcentrated (I : Ideal (MvPolynomial V k)) (d : ℕ) : Prop :=
  ∀ q ∈ quotientSocle I, ∃ f : MvPolynomial V k,
    f.IsHomogeneous d ∧ Ideal.Quotient.mk I f = q

theorem monomial_quotientSocle_iff (B : Family V) (a : Exponent V) :
    Ideal.Quotient.mk (monomialIdeal k B) (monomial a (1 : k)) ∈
      quotientSocle (monomialIdeal k B) ↔
      ∀ i : V, Contains B (a + Finsupp.single i 1) := by
  simp only [quotientSocle, Set.mem_setOf_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have he : ∀ i : V, (X i : MvPolynomial V k) * monomial a 1 =
      monomial (a + Finsupp.single i 1) 1 := by
    intro i
    rw [X, monomial_mul]
    simp [add_comm]
  simp only [he, monomial_mem_iff]

/-- A complete bridge from the actual quotient socle to monomial degrees. -/
theorem socleConcentrated_iff (B : Family V) (d : ℕ) :
    SocleConcentrated (monomialIdeal k B) d ↔
      ∀ a : Exponent V, ¬ Contains B a →
        (∀ i : V, Contains B (a + Finsupp.single i 1)) → a.degree = d := by
  classical
  constructor
  · intro h a ha hsoc
    obtain ⟨f, hf, heq⟩ := h _ ((monomial_quotientSocle_iff B a).mpr hsoc)
    have hmem := Ideal.Quotient.eq.mp heq
    have ha0 : (f - monomial a 1).coeff a = 0 := by
      by_contra hn
      exact ha ((mem_monomialIdeal_iff B _).mp hmem a (mem_support_iff.mpr hn))
    have hfa : f.coeff a ≠ 0 := by
      simp only [coeff_sub, coeff_monomial, ↓reduceIte] at ha0
      intro hz
      rw [hz] at ha0
      simpa using ha0
    simpa only [← Finsupp.degree_apply] using
      (hf.degree_eq_sum_deg_support (mem_support_iff.mpr hfa)).symm
  · intro h q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hvar : ∀ i : V, X i * f ∈ monomialIdeal k B := by
      intro i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by
        rw [map_mul]
        exact hq i)
    have hdegree : ∀ a ∈ f.support, ¬ Contains B a → a.degree = d := by
      intro a ha hout
      apply h a hout
      intro i
      apply (mem_monomialIdeal_iff B _).mp (hvar i)
      rw [add_comm a]
      exact mem_support_iff.mpr (by simpa using mem_support_iff.mp ha)
    refine ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f, ?_⟩
    apply Ideal.Quotient.eq.mpr
    apply (mem_monomialIdeal_iff B _).mpr
    intro a ha
    by_contra hout
    have hn := mem_support_iff.mp ha
    have hfa : f.coeff a ≠ 0 := by
      intro hz
      simp [coeff_sub, coeff_homogeneousComponent, hz] at hn
    have hd := hdegree a (mem_support_iff.mpr hfa) hout
    simp [coeff_sub, coeff_homogeneousComponent, hd] at hn

theorem polymatroidal_monomial_socle_degree {B : Family V} (hBne : B.Nonempty)
    (hB : IsPolymatroidal B) {d : ℕ} (hdeg : Equigenerated B d)
    {a : Exponent V} (hout : ¬ Contains B a)
    (hsoc : ∀ i : V, Contains B (a + Finsupp.single i 1)) : a.degree + 1 = d := by
  classical
  have hrep := contains_iff_canonical_lower B hBne d hdeg hB
  have hbad : ¬ LowerFeasible (lowerRank B) a := fun h => hout ((hrep a).mpr h)
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hUtop : U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have h := (hrep _).mp (hsoc i) U
    have he : subsetSum (a + Finsupp.single i 1) U = subsetSum a U := by
      simp [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply, hi]
    rw [he] at h
    omega
  have htop : lowerRank B Finset.univ = d := by
    obtain ⟨b, hb, he⟩ := lowerRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg b hb] using he.symm
  rw [hUtop, subsetSum_univ, htop] at hU
  have hne : Nonempty V := by
    by_contra hn
    haveI : IsEmpty V := not_nonempty_iff.mp hn
    have he : (Finset.univ : Finset V) = ∅ := Finset.univ_eq_empty
    rw [he, lowerRank_empty] at htop
    omega
  let i : V := Classical.choice hne
  obtain ⟨b, hb, hba⟩ := hsoc i
  have hlo := degree_mono hba
  simp only [map_add, Finsupp.degree_single, hdeg b hb] at hlo
  omega

theorem polymatroidal_socleConcentrated {B : Family V} (hBne : B.Nonempty)
    (hB : IsPolymatroidal B) {d : ℕ} (hdeg : Equigenerated B d) :
    SocleConcentrated (monomialIdeal k B) (d - 1) := by
  rw [socleConcentrated_iff]
  intro a ha hs
  have h := polymatroidal_monomial_socle_degree hBne hB hdeg ha hs
  omega

end Characterizations

end
end CheckedCharacterizationsSource38

/-! ## Source: Characterizations.Resolution.Socle -/
section CheckedCharacterizationsSource39

/-! The socle-degree theorem derived from a genuine exact linear free resolution. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

/-- Lemma2.2 in its full homogeneous form. The cycle is the actual top Koszul
boundary inside the ideal, and the staircase proves that its degree is forced. -/
theorem homogeneous_socle_degree [Nonempty V] {y : MvPolynomial V k} {e : ℕ}
    (hy : y.IsHomogeneous e) (hout : y ∉ I)
    (hmul : ∀ i : V, X i * y ∈ I) : e + 1 = d := by
  have hy0 : y ≠ 0 := fun h => hout (h ▸ I.zero_mem)
  let i₀ : V := Classical.choice inferInstance
  have hx0 : X i₀ * y ≠ 0 := by
    intro hz
    apply hy0
    apply (MvPolynomial.X_mul_cancel_left_iff (i := i₀)).mp
    simpa only [mul_zero] using hz
  have hlo : d ≤ e + 1 := P.degree_le_of_homogeneous_mem
    (by simpa only [Nat.add_comm] using (isHomogeneous_X (R := k) i₀).mul hy) hx0 (hmul i₀)
  by_contra hne
  have hlt : d < e + 1 := lt_of_le_of_ne hlo (Ne.symm hne)
  let t := e + 1 - d
  have ht : 0 < t := Nat.sub_pos_of_lt hlt
  have hdegree : d + t = e + 1 := Nat.add_sub_of_le hlo
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  let s : Set.powersetCard V (m + 1) := ⟨Finset.univ, hm⟩
  let z := socleBoundary I s y (fun j => hmul j.val)
  have hz : ∀ a, (z a).val.IsHomogeneous (d + t) := by
    rw [hdegree]
    exact socleBoundary_homogeneous I s y (fun j => hmul j.val) hy
  have hc := socleBoundary_cycle I s y (fun j => hmul j.val)
  have hb := P.idealRows_boundary_above t ht m z hz hc
  exact socleBoundary_not_boundary I m hm y hmul hout hb

omit P in
theorem monomial_socle_degree [Nonempty V] (B : Family V)
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V)
    (hout : ¬ Contains B a) (hmul : ∀ i : V, Contains B (a + Finsupp.single i 1)) :
    a.degree + 1 = d := by
  apply P.homogeneous_socle_degree (isHomogeneous_monomial (1 : k) rfl)
  · exact fun h => hout ((monomial_mem_iff B a).mp h)
  · intro i
    have he : (X i : MvPolynomial V k) * monomial a 1 = monomial (a + Finsupp.single i 1) 1 := by
      rw [X, monomial_mul]
      simp [add_comm]
    rw [he]
    exact (monomial_mem_iff B _).mpr (hmul i)

omit P in
/-- Every actual quotient-socle class has a homogeneous representative of degree d−1.
The zero-variable case is included for every nonzero monomial ideal. -/
theorem socleConcentrated (B : Family V) (hB : B.Nonempty)
    (P : LinearResolution (monomialIdeal k B) d) :
    SocleConcentrated (monomialIdeal k B) (d - 1) := by
  rw [socleConcentrated_iff]
  intro a ha hs
  cases isEmpty_or_nonempty V with
  | inl h =>
      letI := h
      obtain ⟨b, hb⟩ := hB
      have he : b = a := Subsingleton.elim _ _
      exact False.elim (ha ⟨b, hb, he.le⟩)
  | inr h =>
      letI := h
      have he := P.monomial_socle_degree B a ha hs
      omega

end LinearResolution
end Characterizations

end
end CheckedCharacterizationsSource39

/-! ## Source: Characterizations.SocleCharacterization -/
section CheckedCharacterizationsSource40

/-! The full local-socle characterization, in the actual retained-variable quotient rings. -/
noncomputable section
namespace Characterizations
open CommAlg.Polymatroid MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem localFamily_degree_of_locallyEquigenerated {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) (U : Finset V) :
    Equigenerated (localFamily B U) (lowerRank B U) := by
  intro a ha
  have he : extendExponent U a ∈ localize B U := by
    rw [localize_eq_extend_localFamily]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  simpa only [extendExponent_degree] using localize_degree hB hl he

theorem restrict_add_single (U : Finset V) (a : Exponent V) (i : U) :
    restrictExponent U (a + Finsupp.single i.val 1) =
      restrictExponent U a + Finsupp.single i 1 := by
  ext j
  simp only [restrictExponent_apply, Finsupp.add_apply, Finsupp.single_apply]
  have he : i.val = j.val ↔ i = j := Subtype.ext_iff.symm
  simp only [he]

theorem restrict_degree_of_supported {U : Finset V} {a : Exponent V}
    (ha : project U a = a) : (restrictExponent U a).degree = a.degree := by
  rw [← extendExponent_degree U, extend_restrict, ha]

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- Corollary 2.7, with ordinary polynomial quotient socles, including zero
socles and every nonzero monomial ideal. The field hypothesis can be weakened
to an arbitrary nontrivial commutative coefficient ring. -/
theorem polymatroidal_iff_local_socles {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∀ U : Finset V, monomialIdeal k (localFamily B U) ≠ ⊤ →
        SocleConcentrated (monomialIdeal k (localFamily B U)) (lowerRank B U - 1) := by
  constructor
  · intro hp
    refine ⟨polymatroidal_locallyEquigenerated hp, ?_⟩
    intro U _
    exact polymatroidal_socleConcentrated (localFamily_nonempty hB U)
      (localFamily_polymatroidal hp U) (localFamily_equigenerated hp U)
  · rintro ⟨hl, hsoc⟩
    apply polymatroidal_of_local_socles hB hanti hl
    intro U a ha hout hmul
    have hout' : ¬ Contains (localFamily B U) (restrictExponent U a) :=
      fun h => hout ((contains_localize_iff B U a).mpr h)
    have hmul' : ∀ i : U, Contains (localFamily B U)
        (restrictExponent U a + Finsupp.single i 1) := by
      intro i
      rw [← restrict_add_single]
      exact (contains_localize_iff B U _).mp (hmul i i.property)
    have hproper : monomialIdeal k (localFamily B U) ≠ ⊤ := by
      intro he
      apply hout'
      apply (monomial_mem_iff (k := k) _ _).mp
      rw [he]
      trivial
    have hd := (socleConcentrated_iff (localFamily B U) (lowerRank B U - 1)).mp
      (hsoc U hproper) _ hout' hmul'
    have hpos : 0 < lowerRank B U := by
      by_contra hn
      have hr : lowerRank B U = 0 := Nat.eq_zero_of_not_pos hn
      obtain ⟨b, hb⟩ := localFamily_nonempty hB U
      have hb0 : b = 0 := (Finsupp.degree_eq_zero_iff b).mp
        ((localFamily_degree_of_locallyEquigenerated hB hl U b hb).trans hr)
      exact hout' ⟨b, hb, by simp [hb0]⟩
    rw [restrict_degree_of_supported ha] at hd
    omega

end Characterizations

end
end CheckedCharacterizationsSource40

/-! ## Source: Characterizations.MainLocalization -/
section CheckedCharacterizationsSource41

/-! # Theorem 1.1(A): actual local linear resolutions characterize polymatroids -/
noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [Field k]

theorem polymatroidal_iff_local_linearResolutions {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ ∀ U : Finset V,
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  constructor
  · exact fun hp U => polymatroidal_local_linearResolutions hp U
  · intro h
    classical
    have hres : ∀ U, HasLinearResolution (monomialIdeal k (localFamily B U)) := by
      intro U
      simpa only [monomialLocalization_eq] using h U
    have hl : LocallyEquigenerated B := by
      rw [locallyEquigenerated_iff]
      intro U
      obtain ⟨d, ⟨P⟩⟩ := hres U
      exact ⟨d, P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U)⟩
    apply (polymatroidal_iff_local_socles k hB hanti).mpr
    refine ⟨hl, ?_⟩
    intro U _
    letI : LinearOrder U := LinearOrder.lift' (Fintype.equivFin U) (Fintype.equivFin U).injective
    obtain ⟨d, ⟨P⟩⟩ := hres U
    obtain ⟨a, ha⟩ := localFamily_nonempty hB U
    have hd : d = lowerRank B U :=
      (P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U) a ha).symm.trans
        (localFamily_degree_of_locallyEquigenerated hB hl U a ha)
    simpa only [hd] using P.socleConcentrated (localFamily B U) (localFamily_nonempty hB U)

theorem local_linearResolutions_field_independent {k' : Type u} [Field k']
    {B : Family V} (hB : B.Nonempty) (hanti : Antichain B) :
    (∀ U : Finset V, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) ↔
    (∀ U : Finset V, HasLinearResolution (monomialLocalization k' (monomialIdeal k' B) U)) :=
  (polymatroidal_iff_local_linearResolutions (k := k) hB hanti).symm.trans
    (polymatroidal_iff_local_linearResolutions (k := k') hB hanti)

end Characterizations

end
end CheckedCharacterizationsSource41

/-! ## Source: Characterizations.Isolators.Coverage -/
section CheckedCharacterizationsSource42

/-! # Necessary localization tests and their exact cardinalities -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- A fixed family of actual localization tests is sufficient in degree d. -/
def LocalizationTestSufficient (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, B.Nonempty → Equigenerated B d →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

/-- The same test with prior equigeneration at every localization. -/
def PureLocalizationTestSufficient (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, B.Nonempty → Equigenerated B d → LocallyEquigenerated B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

/-- A fixed localization test with no a priori bound on the generator degrees. -/
def UnboundedLocalizationTestSufficient (Γ : Finset (Finset V)) : Prop :=
  ∀ B : Family V, B.Nonempty → Antichain B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def localizationBand (t : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun U => 2 ≤ U.card ∧ Uᶜ.card ≤ t)

@[simp] lemma mem_localizationBand (t : ℕ) (U : Finset V) :
    U ∈ localizationBand (V := V) t ↔ 2 ≤ U.card ∧ Uᶜ.card ≤ t := by
  simp [localizationBand]

/-- Every test in the ordinary band is individually necessary (Theorem 4.5). -/
theorem localizationTestSufficient_necessary (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d)
    (hΓ : LocalizationTestSufficient (k := k) Γ d) : localizationBand (V := V) (d-1) ⊆ Γ := by
  intro U hU
  obtain ⟨hm, hk⟩ := (mem_localizationBand _ _).mp hU
  by_contra hnot
  have hex : ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
    by_cases hk' : Uᶜ.card ≤ d-2
    · obtain ⟨B, hB, he, _, hres, _⟩ := exists_sharp_isolator (k := k) U hm d hd hk'
      exact ⟨B, hB, he, hres⟩
    · have he : Uᶜ.card = d-1 := by omega
      obtain ⟨B, hB, hdeg, _, hres⟩ := exists_outer_band_isolator (k := k) U hm d hd he
      exact ⟨B, hB, hdeg, hres⟩
  obtain ⟨B, hB, hdeg, hres⟩ := hex
  have hp := hΓ B hB hdeg (fun R hR => (hres R).mpr (fun he => hnot (he ▸ hR)))
  exact (hres U).mp (polymatroidal_local_linearResolutions hp U) rfl

/-- Every test in the narrower pure band is individually necessary (Theorem 4.5). -/
theorem pureLocalizationTestSufficient_necessary (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d)
    (hΓ : PureLocalizationTestSufficient (k := k) Γ d) : localizationBand (V := V) (d-2) ⊆ Γ := by
  intro U hU
  obtain ⟨hm, hk⟩ := (mem_localizationBand _ _).mp hU
  by_contra hnot
  obtain ⟨B, hB, hdeg, hl, hres, _⟩ := exists_sharp_isolator (k := k) U hm d hd hk
  have hp := hΓ B hB hdeg hl (fun R hR => (hres R).mpr (fun he => hnot (he ▸ hR)))
  exact (hres U).mp (polymatroidal_local_linearResolutions hp U) rfl

/-- Corollary 4.8: every coordinate prime on at least two variables is necessary. -/
theorem unboundedLocalizationTestSufficient_necessary (Γ : Finset (Finset V))
    (hΓ : UnboundedLocalizationTestSufficient (k := k) Γ) :
    ∀ U : Finset V, 2 ≤ U.card → U ∈ Γ := by
  intro U hm
  by_contra hnot
  obtain ⟨B, hB, hdeg, _, hres⟩ := exists_pure_isolator (k := k) U hm
  have hp := hΓ B hB hdeg.antichain (fun R hR => (hres R).mpr (fun he => hnot (he ▸ hR)))
  exact (hres U).mp (polymatroidal_local_linearResolutions hp U) rfl

/-- A monomial ideal on at most one retained variable is principal, hence linear. -/
lemma local_linearResolution_of_card_le_one {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (hcard : U.card ≤ 1) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  letI : Subsingleton U := Finset.card_le_one_iff_subsingleton_coe.mp hcard
  obtain ⟨a, ha⟩ := localFamily_nonempty hB U
  have he : localFamily B U = {a} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ha, ?_⟩
    intro b hb
    by_cases hba : b ≤ a
    · exact localFamily_antichain B U b hb a ha hba
    · have hab : a ≤ b := by
        have hn : ∃ i, ¬ b i ≤ a i := not_forall.mp hba
        obtain ⟨i, hi⟩ := hn
        intro j
        have hji : j = i := Subsingleton.elim _ _
        subst j
        omega
      exact (localFamily_antichain B U a ha b hb hab).symm
  rw [monomialLocalization_eq, he]
  exact linearResolution_of_polymatroidal (singleton_polymatroidal a)

/-- Complete form of Corollary 4.8: the fixed tests work in every degree exactly
when they contain all coordinate primes generated by at least two variables. -/
theorem unboundedLocalizationTestSufficient_iff (Γ : Finset (Finset V)) :
    UnboundedLocalizationTestSufficient (k := k) Γ ↔
      ∀ U : Finset V, 2 ≤ U.card → U ∈ Γ := by
  constructor
  · exact unboundedLocalizationTestSufficient_necessary Γ
  · intro hΓ B hB hanti hres
    apply (polymatroidal_iff_local_linearResolutions (k := k) hB hanti).mpr
    intro U
    by_cases hU : 2 ≤ U.card
    · exact hres U (hΓ U hU)
    · exact local_linearResolution_of_card_le_one hB U (by omega)

/-- Exact count of the codimension band in Theorem 4.5. -/
theorem localizationBand_card (t : ℕ) (hn : 2 ≤ Fintype.card V) :
    (localizationBand (V := V) t).card =
      ∑ j ∈ Finset.range (min t (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j := by
  let r := min t (Fintype.card V-2)
  let C := (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ r)
  have himage : (localizationBand (V := V) t).image (fun U => Uᶜ) = C := by
    ext A
    simp only [Finset.mem_image, mem_localizationBand, C, mem_filter, mem_powerset]
    constructor
    · rintro ⟨U, ⟨hm, ht⟩, rfl⟩
      refine ⟨subset_univ _, le_min ht ?_⟩
      have hc := Finset.card_add_card_compl U
      try simp only [card_univ] at hc
      omega
    · rintro ⟨_, hA⟩
      have ht : A.card ≤ t := hA.trans (min_le_left _ _)
      have hn' : A.card ≤ Fintype.card V-2 := hA.trans (min_le_right _ _)
      have hc := Finset.card_add_card_compl A
      try simp only [card_univ] at hc
      refine ⟨Aᶜ, ⟨by omega, by simpa using ht⟩, compl_compl A⟩
  have hcard : (localizationBand (V := V) t).card = C.card := by
    rw [← himage, Finset.card_image_of_injective]
    exact fun U W h => compl_injective h
  rw [hcard]
  have hf : C.card = ∑ j ∈ Finset.range (r+1), (C.filter (fun A => A.card = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun A hA => mem_range.mpr (by
      have hh := (mem_filter.mp hA).2; omega))
  rw [hf]
  apply sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using (Nat.lt_succ_iff.mp (mem_range.mp hj))
  have he : C.filter (fun A => A.card = j) = (Finset.univ : Finset V).powersetCard j := by
    ext A
    simp only [C, mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨⟨hA, _⟩, he⟩; exact ⟨hA, he⟩
    · rintro ⟨hA, he⟩; exact ⟨⟨hA, he ▸ hjr⟩, he⟩
  rw [he, card_powersetCard, card_univ]

/-- The exact unbounded number of nontrivial coordinate primes. -/
theorem allLocalizationTests_card :
    (Finset.univ.filter (fun U : Finset V => 2 ≤ U.card)).card =
      2 ^ Fintype.card V - Fintype.card V - 1 := by
  let S : Finset (Finset V) := insert ∅ ((Finset.univ : Finset V).image (fun i => {i}))
  have hS : S.card = Fintype.card V+1 := by
    dsimp only [S]
    rw [card_insert_of_notMem, card_image_of_injective]
    · simp
    · intro i j he; exact singleton_injective he
    · simp
  have he : Finset.univ.filter (fun U : Finset V => 2 ≤ U.card) = Sᶜ := by
    ext U
    simp only [mem_filter, mem_univ, true_and, mem_compl, S, mem_insert, mem_image]
    constructor
    · intro hu hsmall
      rcases hsmall with rfl | ⟨i, _, rfl⟩ <;> simp at hu
    · intro hu
      by_contra hn
      have hc : U.card ≤ 1 := by omega
      by_cases hzero : U = ∅
      · exact hu (Or.inl hzero)
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
        have he : U = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hi, fun j hj => (Finset.card_le_one.mp hc) j hj i hi⟩
        exact hu (Or.inr ⟨i, he.symm⟩)
  rw [he, Finset.card_compl, hS]
  simp only [Fintype.card_finset, Nat.sub_add_eq]

/-- The exact minimum in Corollary 4.8 is attained and is a lower bound for every
fixed localization-testing family. -/
theorem unboundedLocalization_minimum :
    (∃ Γ : Finset (Finset V), UnboundedLocalizationTestSufficient (k := k) Γ ∧
      Γ.card = 2 ^ Fintype.card V - Fintype.card V - 1) ∧
    (∀ Γ : Finset (Finset V), UnboundedLocalizationTestSufficient (k := k) Γ →
      2 ^ Fintype.card V - Fintype.card V - 1 ≤ Γ.card) := by
  constructor
  · refine ⟨Finset.univ.filter (fun U : Finset V => 2 ≤ U.card), ?_, allLocalizationTests_card⟩
    apply (unboundedLocalizationTestSufficient_iff _).mpr
    intro U hU
    simpa using hU
  · intro Γ hΓ
    rw [← allLocalizationTests_card (V := V)]
    apply Finset.card_le_card
    intro U hU
    exact (unboundedLocalizationTestSufficient_iff Γ).mp hΓ U (by simpa using hU)

end Characterizations.Isolators

end
end CheckedCharacterizationsSource42

/-! ## Source: Characterizations.GreedyChain -/
section CheckedCharacterizationsSource43

/-! # Actual generators attaining every minimum along a nested chain -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every minimal projected generator lifts to a minimal generator at every
larger retained set. This statement does not assume exchange. -/
theorem localize_nested_lift (B : Family V) {U W : Finset V} (hWU : W ⊆ U)
    {b : Exponent V} (hb : b ∈ localize B W) :
    ∃ c ∈ localize B U, project W c = b := by
  obtain ⟨a, ha, hab⟩ := localize_member hb
  obtain ⟨c, hc, hca⟩ := localize_below (U := U) ha
  refine ⟨c, hc, ?_⟩
  have hcb : project W c ≤ b := by
    have h := project_mono W hca
    rwa [project_project hWU, hab] at h
  have hcW : project W c ∈ B.image (project W) := by
    obtain ⟨z, hz, rfl⟩ := localize_member hc
    exact Finset.mem_image.mpr ⟨z, hz, (project_project hWU z).symm⟩
  exact (mem_minimalFamily.mp hb).2 _ hcW hcb

theorem localize_univ_of_antichain {B : Family V} (hB : Antichain B) :
    localize B Finset.univ = B := by
  have he : project (Finset.univ : Finset V) = id := funext project_univ
  simpa [localize, he] using minimalFamily_eq hB

/-- Simultaneous attainment along an arbitrary increasing chain, by a literal
minimal generator of the localization at its last term. -/
theorem localize_chain_minimum {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) (U : ℕ → Finset V) (hU : Monotone U) (n : ℕ) :
    ∃ b ∈ localize B (U n), ∀ j ≤ n, subsetSum b (U j) = lowerRank B (U j) := by
  induction n with
  | zero =>
    obtain ⟨b, hb⟩ := localize_nonempty hB (U 0)
    refine ⟨b, hb, ?_⟩
    intro j hj
    have he : j = 0 := by omega
    subst j
    rw [← degree_project, localize_supported hb]
    exact localize_degree hB hl hb
  | succ n ih =>
    obtain ⟨b, hb, hmin⟩ := ih
    obtain ⟨c, hc, he⟩ := localize_nested_lift B (hU (Nat.le_succ n)) hb
    refine ⟨c, hc, ?_⟩
    intro j hj
    by_cases hlast : j = n + 1
    · subst j
      rw [← degree_project, localize_supported hc]
      exact localize_degree hB hl hc
    · have hjn : j ≤ n := by omega
      rw [← subsetSum_project (hU hjn) c, he]
      exact hmin j hjn

/-- The greedy-chain assertion in the proof of Theorem 2.11. -/
theorem generator_chain_minimum {B : Family V} (hB : B.Nonempty) (ha : Antichain B)
    (hl : LocallyEquigenerated B) (U : ℕ → Finset V) (hU : Monotone U)
    (n : ℕ) (hn : U n = Finset.univ) :
    ∃ b ∈ B, ∀ j ≤ n, subsetSum b (U j) = lowerRank B (U j) := by
  obtain ⟨b, hb, hmin⟩ := localize_chain_minimum hB hl U hU n
  rw [hn, localize_univ_of_antichain ha] at hb
  exact ⟨b, hb, hmin⟩

end Characterizations

end
end CheckedCharacterizationsSource43

/-! ## Source: Characterizations.RealHull -/
section CheckedCharacterizationsSource44

/-! # The exact real convex hull forced by local equigeneration -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def realExponent (a : Exponent V) : V → ℝ := fun i => a i

def realSubsetSum (x : V → ℝ) (U : Finset V) : ℝ := ∑ i ∈ U, x i

@[simp] theorem realSubsetSum_exponent (a : Exponent V) (U : Finset V) :
    realSubsetSum (realExponent a) U = (subsetSum a U : ℝ) := by
  simp [realSubsetSum, realExponent, subsetSum]

def lowerRankPolytope (B : Family V) (d : ℕ) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ realSubsetSum x univ = d ∧
    ∀ U, (lowerRank B U : ℝ) ≤ realSubsetSum x U}

theorem lowerRankPolytope_convex (B : Family V) (d : ℕ) :
    Convex ℝ (lowerRankPolytope B d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) = (d : ℝ)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    change a * realSubsetSum x univ + b * realSubsetSum y univ = _
    rw [hx.2.1, hy.2.1, ← add_mul, hab, one_mul]
  · intro U
    change (lowerRank B U : ℝ) ≤ ∑ i ∈ U, (a * x i + b * y i)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2.2 U) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2.2 U) hb
    have he : a * (lowerRank B U : ℝ) + b * (lowerRank B U : ℝ) = lowerRank B U := by
      rw [← add_mul, hab, one_mul]
    exact he ▸ add_le_add h1 h2

theorem exponent_mem_lowerRankPolytope {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) {a : Exponent V} (ha : a ∈ B) :
    realExponent a ∈ lowerRankPolytope B d := by
  refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_⟩
  · rw [realSubsetSum_exponent, subsetSum_univ, hd a ha]
  · intro U
    rw [realSubsetSum_exponent]
    exact_mod_cast lowerRank_le ha U

def orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) : Finset V :=
  univ.filter (fun v => (e.symm v).val < j)

theorem orderPrefix_mono {n : ℕ} (e : Fin n ≃ V) : Monotone (orderPrefix e) := by
  intro j k hjk v hv
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hv).2 hjk⟩

@[simp] theorem orderPrefix_full {n : ℕ} (e : Fin n ≃ V) : orderPrefix e n = univ := by
  ext v
  simp [orderPrefix, (e.symm v).isLt]

def orderedSequence {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (e ⟨j, h⟩) else 0

theorem sum_orderPrefix {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) (hj : j ≤ n) :
    realSubsetSum x (orderPrefix e j) = ∑ i ∈ range j, orderedSequence e x i := by
  classical
  apply sum_bij (fun v _ => (e.symm v).val)
  · intro v hv
    exact mem_range.mpr (mem_filter.mp hv).2
  · intro v hv w hw he
    exact e.symm.injective (Fin.ext he)
  · intro i hi
    have hin : i < n := (mem_range.mp hi).trans_le hj
    refine ⟨e ⟨i, hin⟩, ?_, ?_⟩
    · simp [orderPrefix, mem_range.mp hi]
    · simp
  · intro v hv
    simp [orderedSequence, (e.symm v).isLt]

theorem sum_ordered_product {n : ℕ} (e : Fin n ≃ V) (x w : V → ℝ) :
    (∑ i ∈ range n, orderedSequence e x i * orderedSequence e w i) =
      ∑ v, x v * w v := by
  have he : ∀ i, orderedSequence e x i * orderedSequence e w i =
      orderedSequence e (fun v => x v * w v) i := by
    intro i
    by_cases hi : i < n <;> simp [orderedSequence, hi]
  simp_rw [he]
  rw [← sum_orderPrefix e _ n le_rfl, orderPrefix_full]
  rfl

theorem weighted_le_of_prefix {n : ℕ} (e : Fin n ≃ V) (x y w : V → ℝ)
    (hw : Antitone (fun i => w (e i)))
    (hp : ∀ j ≤ n, realSubsetSum x (orderPrefix e j) ≤ realSubsetSum y (orderPrefix e j))
    (ht : realSubsetSum x univ = realSubsetSum y univ) :
    (∑ v, x v * w v) ≤ ∑ v, y v * w v := by
  let f : ℕ → ℝ := fun i => orderedSequence e y i - orderedSequence e x i
  let g : ℕ → ℝ := orderedSequence e w
  have hsum : ∀ j ≤ n, 0 ≤ ∑ i ∈ range j, f i := by
    intro j hj
    have h := hp j hj
    rw [sum_orderPrefix e x j hj, sum_orderPrefix e y j hj] at h
    simpa only [f, sum_sub_distrib, sub_nonneg] using h
  have htotal : ∑ i ∈ range n, f i = 0 := by
    rw [show f = (fun i => orderedSequence e y i - orderedSequence e x i) from rfl,
      sum_sub_distrib, ← sum_orderPrefix e y n le_rfl,
      ← sum_orderPrefix e x n le_rfl, orderPrefix_full, ht, sub_self]
  have hnonneg : 0 ≤ ∑ i ∈ range n, f i * g i := by
    simp_rw [← smul_eq_mul]
    rw [sum_range_by_parts', smul_eq_mul, htotal, zero_mul, zero_sub]
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro i hi
    have hin : i < n - 1 := mem_range.mp hi
    have h1 := hsum (i + 1) (by omega)
    have h2 : g (i + 1) - g i ≤ 0 := by
      have hi0 : i < n := by omega
      have hi1 : i + 1 < n := by omega
      have hw' := hw (show (⟨i, hi0⟩ : Fin n) ≤ ⟨i+1, hi1⟩ by
        change i ≤ i + 1
        omega)
      simpa [g, orderedSequence, hi0, hi1, sub_nonpos] using hw'
    simpa only [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos h1 h2
  simp only [f, g, sub_mul, sum_sub_distrib, sub_nonneg] at hnonneg
  rwa [sum_ordered_product, sum_ordered_product] at hnonneg

theorem exists_antitone_enumeration (w : V → ℝ) :
    ∃ e : Fin (Fintype.card V) ≃ V, Antitone (fun i => w (e i)) := by
  let f : Fin (Fintype.card V) → OrderDual ℝ := fun i => w ((Fintype.equivFin V).symm i)
  let e := (Tuple.sort f).trans (Fintype.equivFin V).symm
  exact ⟨e, Tuple.monotone_sort f⟩

theorem generator_minimizes_every_functional {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (w : V → ℝ) :
    ∃ b ∈ B, ∀ x ∈ lowerRankPolytope B d,
      (∑ v, realExponent b v * w v) ≤ ∑ v, x v * w v := by
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  obtain ⟨b, hb, hmin⟩ := generator_chain_minimum hB hanti hl
    (orderPrefix e) (orderPrefix_mono e) (Fintype.card V) (orderPrefix_full e)
  refine ⟨b, hb, ?_⟩
  intro x hx
  apply weighted_le_of_prefix e (realExponent b) x w he
  · intro j hj
    rw [realSubsetSum_exponent, hmin j hj]
    exact hx.2.2 _
  · rw [realSubsetSum_exponent, subsetSum_univ, hd b hb, hx.2.1]

theorem linearFunctional_eq_weighted_sum (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have he : x = ∑ v, x v • Pi.single v (1 : ℝ) := by
    funext v
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp

/-- Equation (2.3) of Theorem 2.11: equality of actual real convex sets. -/
theorem convexHull_generators_eq_lowerRankPolytope {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    convexHull ℝ (realExponent '' (B : Set (Exponent V))) = lowerRankPolytope B d := by
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (lowerRankPolytope_convex B d)
    rintro x ⟨a, ha, rfl⟩
    exact exponent_mem_lowerRankPolytope hd ha
  · intro x hx
    by_contra hout
    have hfin : (realExponent '' (B : Set (Exponent V))).Finite := B.finite_toSet.image _
    obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) (hfin.isClosed_convexHull ℝ) hout
    obtain ⟨b, hb, hmin⟩ := generator_minimizes_every_functional hB hanti hl hd
      (fun v => f (Pi.single v 1))
    have hm := hmin x hx
    rw [← linearFunctional_eq_weighted_sum, ← linearFunctional_eq_weighted_sum] at hm
    have hc := hcf (realExponent b) (subset_convexHull ℝ _ ⟨b, hb, rfl⟩)
    linarith

end Characterizations

end
end CheckedCharacterizationsSource44

/-! ## Source: Characterizations.LowerBases -/
section CheckedCharacterizationsSource45

/-! # The full integer base family of a locally equigenerated monomial ideal -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def lowerBaseFamily (r : Finset V → ℕ) (d : ℕ) : Family V :=
  (Finset.Iic (constExponent d)).filter (fun a => a.degree = d ∧ LowerFeasible r a)

@[simp] theorem mem_lowerBaseFamily (r : Finset V → ℕ) (d : ℕ) (a : Exponent V) :
    a ∈ lowerBaseFamily r d ↔ a.degree = d ∧ LowerFeasible r a := by
  classical
  simp only [lowerBaseFamily, Finset.mem_filter, Finset.mem_Iic]
  exact ⟨And.right, fun h => ⟨fun i => (coordinate_le_degree a i).trans h.1.le, h⟩⟩

theorem lowerBaseFamily_equigenerated (r : Finset V → ℕ) (d : ℕ) :
    Equigenerated (lowerBaseFamily r d) d := fun a ha => ((mem_lowerBaseFamily r d a).mp ha).1

theorem contains_lowerBaseFamily_iff {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d)
    (a : Exponent V) : Contains (lowerBaseFamily r d) a ↔ LowerFeasible r a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (((mem_lowerBaseFamily r d b).mp hb).2 U).trans
      (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    obtain ⟨b, hba, hd, hb⟩ := exists_lower_base_below hr hr0 hrd hrle ha
    exact ⟨b, (mem_lowerBaseFamily r d b).mpr ⟨hd, hb⟩, hba⟩

theorem lowerBaseFamily_polymatroidal {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d) :
    IsPolymatroidal (lowerBaseFamily r d) :=
  polymatroidal_of_lower_inequalities (lowerBaseFamily_equigenerated r d) hr
    (contains_lowerBaseFamily_iff hr hr0 hrd hrle)

theorem lowerRank_univ_of_equigenerated {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) : lowerRank B Finset.univ = d := by
  obtain ⟨a, ha, he⟩ := lowerRank_attained hB Finset.univ
  simpa only [subsetSum_univ, hd a ha] using he.symm

theorem lowerRank_le_degree {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V) : lowerRank B U ≤ d := by
  rw [← lowerRank_univ_of_equigenerated hB hd]
  exact lowerRank_mono hB (Finset.subset_univ U)

theorem subset_lowerBaseFamily {B : Family V} {d : ℕ} (hd : Equigenerated B d) :
    B ⊆ lowerBaseFamily (lowerRank B) d := by
  intro a ha
  exact (mem_lowerBaseFamily _ _ _).mpr ⟨hd a ha, fun U => lowerRank_le ha U⟩

theorem canonicalLowerBases_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) :=
  lowerBaseFamily_polymatroidal (lowerRank_supermodular hB hl) (lowerRank_empty B)
    (lowerRank_univ_of_equigenerated hB hd) (lowerRank_le_degree hB hd)

theorem contains_canonicalLowerBases_iff {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (a : Exponent V) :
    Contains (lowerBaseFamily (lowerRank B) d) a ↔ LowerFeasible (lowerRank B) a :=
  contains_lowerBaseFamily_iff (lowerRank_supermodular hB hl) (lowerRank_empty B)
    (lowerRank_univ_of_equigenerated hB hd) (lowerRank_le_degree hB hd) a

end Characterizations

end
end CheckedCharacterizationsSource45

/-! ## Source: Characterizations.RankIncrements -/
section CheckedCharacterizationsSource46

/-! # Rank increments on intervals of coordinate localizations -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem equigenerated_localize_degree {B : Family V} (hB : B.Nonempty)
    {U : Finset V} {d : ℕ} (hd : Equigenerated (localize B U) d)
    {b : Exponent V} (hb : b ∈ localize B U) : b.degree = lowerRank B U := by
  obtain ⟨a, ha, hmin⟩ := lowerRank_attained (localize_nonempty hB U) U
  rw [lowerRank_localize hB le_rfl] at hmin
  have haD : a.degree = subsetSum a U := by rw [← degree_project, localize_supported ha]
  exact (hd b hb).trans ((hd a ha).symm.trans (haD.trans hmin))

theorem lowerRank_supermodular_at_union {B : Family V} (hB : B.Nonempty)
    (A C : Finset V) (he : ∃ d, Equigenerated (localize B (A ∪ C)) d) :
    lowerRank B A + lowerRank B C ≤ lowerRank B (A ∪ C) + lowerRank B (A ∩ C) := by
  obtain ⟨d, hd⟩ := he
  obtain ⟨b, hb, hmin⟩ := lowerRank_attained (localize_nonempty hB (A ∪ C)) (A ∩ C)
  rw [lowerRank_localize hB (Finset.inter_subset_left.trans Finset.subset_union_left)] at hmin
  have hsum : subsetSum b (A ∪ C) = lowerRank B (A ∪ C) := by
    rw [← degree_project, localize_supported hb]
    exact equigenerated_localize_degree hB hd hb
  calc
    lowerRank B A + lowerRank B C ≤ subsetSum b A + subsetSum b C :=
      Nat.add_le_add (localize_sum_ge Finset.subset_union_left hb)
        (localize_sum_ge Finset.subset_union_right hb)
    _ = subsetSum b (A ∪ C) + subsetSum b (A ∩ C) := subsetSum_union_inter b A C
    _ = _ := by rw [hsum, hmin]

def SupermodularAbove (r : Finset V → ℕ) (U : Finset V) : Prop :=
  ∀ A C, U ⊆ A → U ⊆ C → r A + r C ≤ r (A ∪ C) + r (A ∩ C)

theorem lowerRank_supermodular_above {B : Family V} (hB : B.Nonempty) (U : Finset V)
    (he : ∀ W, U ⊂ W → ∃ d, Equigenerated (localize B W) d) :
    SupermodularAbove (lowerRank B) U := by
  intro A C hUA hUC
  by_cases h : A ∪ C = U
  · have hA : A = U := Finset.Subset.antisymm (h ▸ Finset.subset_union_left) hUA
    have hC : C = U := Finset.Subset.antisymm (h ▸ Finset.subset_union_right) hUC
    simp [hA, hC]
  · exact lowerRank_supermodular_at_union hB A C
      (he _ ((hUA.trans Finset.subset_union_left).ssubset_of_ne (Ne.symm h)))

theorem supermodular_rank_increments {r : Finset V → ℕ} {U : Finset V}
    (hr : SupermodularAbove r U) (hinc : ∀ i ∉ U, r U + 1 ≤ r (insert i U))
    (C : Finset V) (hC : Disjoint U C) : r U + C.card ≤ r (U ∪ C) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert i C hi ih =>
    have hdis : Disjoint U C := hC.mono_right (Finset.subset_insert _ _)
    have hiU : i ∉ U := fun h => (Finset.disjoint_left.mp hC) h (Finset.mem_insert_self _ _)
    have hih := ih hdis
    have hs := hr (U ∪ C) (insert i U) Finset.subset_union_left (Finset.subset_insert _ _)
    have hun : (U ∪ C) ∪ insert i U = insert i (U ∪ C) := by ext x; simp; tauto
    have hin : (U ∪ C) ∩ insert i U = U := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨hxU | hxC, hxi | hxU'⟩
        · exact hxU
        · exact hxU
        · subst x; exact (hi hxC).elim
        · exact hxU'
      · intro hx; exact ⟨Or.inl hx, Or.inr hx⟩
    rw [hun, hin] at hs
    have hs1 := hinc i hiU
    rw [Finset.card_insert_of_notMem hi, Finset.union_insert]
    omega

theorem supermodular_rank_codimension_bound {r : Finset V → ℕ} {U : Finset V}
    (hr : SupermodularAbove r U) (hinc : ∀ i ∉ U, r U + 1 ≤ r (insert i U)) :
    r U + (Fintype.card V - U.card) ≤ r Finset.univ := by
  simpa only [Finset.card_compl, Finset.card_univ, Finset.union_compl] using
    supermodular_rank_increments hr hinc Uᶜ disjoint_compl_right

/-- A zero rank increment at an equigenerated larger localization forces the
whole ambient exponent family to be unchanged; the added variables do not occur. -/
theorem localize_eq_of_rank_eq {B : Family V} (hB : B.Nonempty)
    {U W : Finset V} (hUW : U ⊆ W)
    (he : ∃ d, Equigenerated (localize B W) d) (hr : lowerRank B U = lowerRank B W) :
    localize B W = localize B U := by
  obtain ⟨d, hd⟩ := he
  have hsupp : ∀ b ∈ localize B W, project U b = b := by
    intro b hb
    apply eq_of_le_of_degree_eq (project_le U b)
    rw [degree_project]
    apply le_antisymm
    · simpa only [degree_project] using degree_mono (project_le U b)
    · rw [equigenerated_localize_degree hB hd hb, ← hr]
      exact localize_sum_ge hUW hb
  apply family_eq_of_contains_iff (localize_antichain B W) (localize_antichain B U)
  intro a
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, hcb⟩ := localize_member hb
    apply (contains_localize B U a).mpr
    refine ⟨c, hc, ?_⟩
    have hproj : project U c = b := by
      rw [← project_project hUW c, hcb, hsupp b hb]
    rwa [hproj]
  · intro ha
    obtain ⟨c, hc, hca⟩ := (contains_localize B U a).mp ha
    obtain ⟨b, hb, hbc⟩ := localize_below (U := W) hc
    refine ⟨b, hb, ?_⟩
    have hp := project_mono U hbc
    rw [hsupp b hb, project_project hUW] at hp
    exact hp.trans hca

end Characterizations

end
end CheckedCharacterizationsSource46

/-! ## Source: Characterizations.AmbientLocalization -/
section CheckedCharacterizationsSource47

/-! # Retained-variable and ambient descriptions of monomial localization agree -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem embeddedFamily_polymatroidal {B : Family W} (hp : IsPolymatroidal B) (e : W ↪ V) :
    IsPolymatroidal (embeddedFamily e B) := by
  obtain ⟨d, hd⟩ := hp.1
  apply (polymatroidal_iff_universal_revlex (k := ℚ) (embeddedFamily_equigenerated hd e)).mpr
  intro o
  exact (embeddedFamily_linearQuotients_iff hd e o).mpr
    (polymatroidal_variable_linearQuotients hp.2 (restrictedOrder o e))

theorem localize_eq_embeddedFamily (B : Family V) (U : Finset V) :
    localize B U = embeddedFamily (Function.Embedding.subtype (· ∈ U)) (localFamily B U) := by
  rw [localize_eq_extend_localFamily]
  unfold embeddedFamily
  congr 1
  funext a
  exact Finsupp.extendDomain_eq_embDomain_subtype a

theorem localize_polymatroidal_of_localFamily {B : Family V} (U : Finset V)
    (h : IsPolymatroidal (localFamily B U)) : IsPolymatroidal (localize B U) := by
  rw [localize_eq_embeddedFamily]
  exact embeddedFamily_polymatroidal h _

theorem localize_polymatroidal {B : Family V} (hp : IsPolymatroidal B) (U : Finset V) :
    IsPolymatroidal (localize B U) :=
  localize_polymatroidal_of_localFamily U (localFamily_polymatroidal hp U)

theorem localFamily_polymatroidal_iff (B : Family V) (U : Finset V) :
    IsPolymatroidal (localFamily B U) ↔ IsPolymatroidal (localize B U) := by
  refine ⟨localize_polymatroidal_of_localFamily U, ?_⟩
  intro h
  obtain ⟨d, hd⟩ := h.1
  have heq : Equigenerated (localFamily B U) d := by
    intro a ha
    have hh : extendExponent U a ∈ localize B U := by
      rw [localize_eq_extend_localFamily]
      exact mem_image.mpr ⟨a, ha, rfl⟩
    simpa only [extendExponent_degree] using hd _ hh
  rw [localize_eq_embeddedFamily] at h
  exact embeddedFamily_polymatroidal_implies heq _ h

end Characterizations

end
end CheckedCharacterizationsSource47

/-! ## Source: Characterizations.GenerationCoverage -/
section CheckedCharacterizationsSource48

/-! # The sharp codimension range needed to force local equigeneration -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem localize_equigenerated_of_rank_zero {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (hr : lowerRank B U = 0) : Equigenerated (localize B U) 0 := by
  obtain ⟨a,ha,hmin⟩ := lowerRank_attained hB U
  have hpa : project U a = 0 := (Finsupp.degree_eq_zero_iff _).mp
    ((degree_project U a).trans (hmin.trans hr))
  obtain ⟨b,hb,hba⟩ := localize_below (U := U) ha
  have hb0 : b = 0 := le_antisymm (hpa ▸ hba) zero_le
  intro c hc
  have hbc := localize_antichain B U b hb c hc (by rw [hb0]; exact zero_le)
  rw [← hbc, hb0]
  simp

theorem localize_equigenerated_of_card_le_one {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (hcard : U.card ≤ 1) : ∃ d, Equigenerated (localize B U) d := by
  obtain ⟨a,ha⟩ := localize_nonempty hB U
  refine ⟨a.degree,?_⟩
  intro b hb
  have hsame : a = b := by
    by_cases hU : U.Nonempty
    · obtain ⟨i,hi⟩ := hU
      have hsingle : U = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj => by
        by_contra hji
        have htwo : ({i,j} : Finset V) ⊆ U :=
          Finset.insert_subset_iff.mpr ⟨hi,Finset.singleton_subset_iff.mpr hj⟩
        have hc := Finset.card_le_card htwo
        simp [Ne.symm hji] at hc
        omega⟩
      have hcomp (c e : Exponent V) (hc : c ∈ localize B U) (he : e ∈ localize B U)
          (hce : c i ≤ e i) : c ≤ e := by
        intro j
        by_cases hji : j = i
        · simpa [hji] using hce
        · have hcj := congrArg (fun f : Exponent V => f j) (localize_supported hc)
          have hjU : j ∉ U := by simpa [hsingle] using hji
          simp only [project_apply, if_neg hjU] at hcj
          rw [← hcj]
          exact Nat.zero_le _
      rcases le_total (a i) (b i) with h | h
      · exact localize_antichain B U a ha b hb (hcomp a b ha hb h)
      · exact (localize_antichain B U b hb a ha (hcomp b a hb ha h)).symm
    · have hU0 := Finset.not_nonempty_iff_eq_empty.mp hU
      have ha0 := localize_supported ha
      have hb0 := localize_supported hb
      simp only [hU0, project_empty] at ha0 hb0
      exact ha0.symm.trans hb0
  exact congrArg Finsupp.degree hsame.symm

theorem maximal_nonequigenerated_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ ∃ e, Equigenerated (localize B U) e)
    (hmax : ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hbad (localize_equigenerated_of_card_le_one hB U (by omega))
  have hpos : 1 ≤ lowerRank B U := by
    by_contra h
    exact hbad ⟨0,localize_equigenerated_of_rank_zero hB U (by omega)⟩
  have hinc : ∀ i ∉ U, lowerRank B U+1 ≤ lowerRank B (insert i U) := by
    intro i hi
    have hsub : U ⊂ insert i U := Finset.ssubset_insert hi
    have he := hmax _ hsub
    have hm := lowerRank_mono hB (Finset.subset_insert i U)
    by_contra h
    have hr : lowerRank B U = lowerRank B (insert i U) := by omega
    have hf := localize_eq_of_rank_eq hB (Finset.subset_insert i U) he hr
    rw [hf] at he
    exact hbad he
  have hbound := supermodular_rank_codimension_bound (lowerRank_supermodular_above hB U hmax) hinc
  rw [lowerRank_univ_of_equigenerated hB hd] at hbound
  exact ⟨hcard,hpos,hbound⟩

theorem locallyEquigenerated_of_band_tests {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (htest : ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      ∃ e, Equigenerated (localize B U) e) : LocallyEquigenerated B := by
  by_contra hn
  unfold LocallyEquigenerated at hn
  obtain ⟨U,hU⟩ := not_forall.mp hn
  let bad : Finset (Finset V) := Finset.univ.filter
    (fun W => ¬∃ e, Equigenerated (localize B W) e)
  have hb : bad.Nonempty := ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
  obtain ⟨W,hW,hmax⟩ := bad.exists_maximal hb
  have hbad := (Finset.mem_filter.mp hW).2
  have hs : ∀ T, W ⊂ T → ∃ e, Equigenerated (localize B T) e := by
    intro T hWT
    by_contra hT
    have hTW := hmax (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩) hWT.subset
    exact hWT.not_superset hTW
  obtain ⟨hc,hp,hcost⟩ := maximal_nonequigenerated_rank_cost hB hd W hbad hs
  exact hbad (htest W hc (by omega))

end Characterizations

end
end CheckedCharacterizationsSource48

/-! ## Source: Characterizations.Strands.OrderEmbedding -/
section CheckedCharacterizationsSource49

/-! # Signed simplicial chain transport along an order embedding -/
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical Finset CommAlg.Simplicial CommAlg.Koszul CategoryTheory
universe u
variable {W V k : Type u} [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Field k]

def ambientMap (f : W ↪o V) : Ambient W k →ₗ[k] Ambient V k :=
  basis.constr k (fun s => basis (s.map f.toEmbedding))

@[simp] lemma ambientMap_basis (f : W ↪o V) (s : Finset W) :
    ambientMap (k := k) f (basis s) = basis (s.map f.toEmbedding) :=
  Module.Basis.constr_basis _ _ _ _

lemma eraseSign_map (f : W ↪o V) (s : Finset W) (e : W) :
    TauCeti.ExteriorAlgebra.basisEraseSign (f e) (s.map f.toEmbedding) =
      TauCeti.ExteriorAlgebra.basisEraseSign e s := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    Finset.filter_map]
  simp only [Finset.card_map]
  change (-1 : ℤˣ) ^ (s.filter (fun j => f j < f e)).card = _
  simp only [f.lt_iff_lt]

lemma boundary_basis_finset (s : Finset V) :
    boundary (basis (k := k) s) =
      ∑ e ∈ s, TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (s.erase e) := by
  rw [boundary_eq_sum]
  trans ∑ e ∈ s, contraction (k := k) e (basis s)
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e he hnot
    simp [contraction_basis, hnot]
  · apply Finset.sum_congr rfl
    intro e he
    simp only [contraction_basis, if_pos he]

lemma ambientMap_boundary (f : W ↪o V) :
    ambientMap (k := k) f ∘ₗ boundary = boundary ∘ₗ ambientMap f := by
  apply basis.ext
  intro s
  simp only [LinearMap.comp_apply, boundary_basis_finset, map_sum, map_zsmul_unit,
    ambientMap_basis, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  change TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (map f.toEmbedding (s.erase e)) =
    TauCeti.ExteriorAlgebra.basisEraseSign (f e) (map f.toEmbedding s) •
      basis ((map f.toEmbedding s).erase (f e))
  rw [eraseSign_map]
  exact congrArg (fun t : Finset V =>
    TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (k := k) t)
    (Finset.map_erase f.toEmbedding s e)

abbrev ChainIndex (K : Finset W → Prop) (i : ℕ) := {s : Finset W // K s ∧ s.card=i}

def chainBasis (K : Finset W → Prop) (i : ℕ) :
    Module.Basis (ChainIndex K i) k (Chains (k := k) K i) :=
  CommAlg.Grading.restrictedBasis basis (fun s => K s ∧ s.card=i)

@[simp] lemma chainBasis_val (K : Finset W → Prop) (i : ℕ) (s : ChainIndex K i) :
    (chainBasis (k := k) K i s).val = basis s.val :=
  CommAlg.Grading.restrictedBasis_val _ _ _

def faceIndexMap (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    ChainIndex K i → ChainIndex L i := fun s =>
  ⟨s.val.map f.toEmbedding, (h _).mpr ⟨s.val, s.property.1, rfl⟩,
    (Finset.card_map _).trans s.property.2⟩

def faceIndexEquiv (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    ChainIndex K i ≃ ChainIndex L i := Equiv.ofBijective (faceIndexMap f K L h i) (by
  constructor
  · intro s t he
    apply Subtype.ext
    exact Finset.map_injective f.toEmbedding (congrArg Subtype.val he)
  · intro s
    obtain ⟨t, ht, he⟩ := (h s.val).mp s.property.1
    refine ⟨⟨t, ht, ?_⟩, Subtype.ext he.symm⟩
    simpa only [he, Finset.card_map] using s.property.2)

def chainEquiv (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    Chains (k := k) K i ≃ₗ[k] Chains (k := k) L i :=
  (chainBasis K i).equiv (chainBasis L i) (faceIndexEquiv f K L h i)

lemma chainEquiv_val (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ)
    (z : Chains (k := k) K i) : (chainEquiv f K L h i z).val = ambientMap f z.val := by
  have he : (Chains (k := k) L i).subtype ∘ₗ (chainEquiv f K L h i).toLinearMap =
      ambientMap f ∘ₗ (Chains (k := k) K i).subtype := by
    apply (chainBasis (k := k) K i).ext
    intro s
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, chainEquiv,
      Module.Basis.equiv_apply]
    change ((chainBasis (k := k) L i) (faceIndexEquiv f K L h i s)).val =
      ambientMap f ((chainBasis (k := k) K i) s).val
    rw [chainBasis_val, chainBasis_val, ambientMap_basis]
    rfl
  exact LinearMap.congr_fun he z

def embeddedChainIso (f : W ↪o V) {K : Finset W → Prop} {L : Finset V → Prop}
    (hK : Downward K) (hL : Downward L)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) :
    chainComplex (k := k) hK ≅ chainComplex hL :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (chainEquiv f K L h i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j+1 := hij.symm
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change Chains (k := k) K (j+1) at z
      apply Subtype.ext
      change (chainDifferential hL j (chainEquiv f K L h (j+1) z)).val =
        (chainEquiv f K L h j (chainDifferential hK j z)).val
      simp only [chainEquiv_val, chainDifferential_val]
      exact (LinearMap.congr_fun (ambientMap_boundary f) z.val).symm)

lemma embedded_homology_finrank (f : W ↪o V) {K : Finset W → Prop} {L : Finset V → Prop}
    (hK : Downward K) (hL : Downward L)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    Module.finrank k ((chainComplex (k := k) hK).homology i) =
      Module.finrank k ((chainComplex (k := k) hL).homology i) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (embeddedChainIso f hK hL h)).toLinearEquiv.finrank_eq

end Characterizations.Strands

end
end CheckedCharacterizationsSource49

/-! ## Source: Characterizations.Strands.Restriction -/
section CheckedCharacterizationsSource50

/-! # Exact fine Betti transport under deletion of unused coordinates -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def subsetOrderEmbedding (U : Finset V) : U ↪o V :=
  OrderEmbedding.ofMapLEIff Subtype.val (by intros; rfl)

lemma extend_faceExponent (U : Finset V) (s : Finset U) :
    extendExponent U (faceExponent s) = faceExponent (s.map (subsetOrderEmbedding U).toEmbedding) := by
  ext j
  by_cases hj : j ∈ U
  · simp only [extendExponent_apply, dif_pos hj, faceExponent_apply, Finset.mem_map]
    have he : (∃ a, a ∈ s ∧ (subsetOrderEmbedding U).toEmbedding a = j) ↔
        (⟨j, hj⟩ : U) ∈ s := by
      constructor
      · rintro ⟨a, ha, he⟩
        have he' : a = ⟨j, hj⟩ := Subtype.ext he
        simpa only [he'] using ha
      · intro h; exact ⟨⟨j, hj⟩, h, rfl⟩
    simp only [he]
    split_ifs <;> first | rfl | contradiction
  · simp only [extendExponent_apply, dif_neg hj, faceExponent_apply]
    rw [if_neg]
    intro hm
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hm
    exact hj (he ▸ a.property)

lemma extend_sub (U : Finset V) (a b : Exponent U) :
    extendExponent U (a-b) = extendExponent U a - extendExponent U b := by
  ext j
  by_cases hj : j ∈ U <;> simp [extendExponent_apply, hj]

lemma extend_support_subset (U : Finset V) (a : Exponent U) :
    (extendExponent U a).support ⊆ U := by
  intro j hj
  by_contra hjU
  have h := Finsupp.mem_support_iff.mp hj
  exact h (by simp [hjU])

lemma koszulFaces_extend_image (U : Finset V) (B : Family V) (C : Family U)
    (hcontains : ∀ a, Contains B (extendExponent U a) ↔ Contains C a) (a : Exponent U) :
    ∀ s, koszulFaces B (extendExponent U a) s ↔
      ∃ t, koszulFaces C a t ∧ s=t.map (subsetOrderEmbedding U).toEmbedding := by
  have mapped (t : Finset U) :
      koszulFaces B (extendExponent U a) (t.map (subsetOrderEmbedding U).toEmbedding) ↔
        koszulFaces C a t := by
    unfold koszulFaces
    rw [← extend_faceExponent, extendExponent_le_iff, ← extend_sub, hcontains]
  intro s
  constructor
  · intro hs
    have hsub : s ⊆ U := ((faceExponent_le_iff_subset_support s _).mp hs.1).trans
      (extend_support_subset U a)
    let t := s.subtype (· ∈ U)
    have he : t.map (subsetOrderEmbedding U).toEmbedding = s :=
      Finset.subtype_map_of_mem (fun j hj => hsub hj)
    refine ⟨t, (mapped t).mp (by simpa only [he] using hs), he.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact (mapped t).mpr ht

theorem betti_restriction_transport (U : Finset V) (B : Family V) (C : Family U)
    (hcontains : ∀ a, Contains B (extendExponent U a) ↔ Contains C a) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) B (extendExponent U a) i = bettiNumber (k := k) C a i := by
  rw [bettiNumber_eq_face_homology_finrank, bettiNumber_eq_face_homology_finrank]
  exact (embedded_homology_finrank (subsetOrderEmbedding U) (koszulFaces_downward C a)
    (koszulFaces_downward B _) (koszulFaces_extend_image U B C hcontains a) i).symm

/-- Set the omitted variables to zero; generators involving them disappear. -/
def restrictionFamily (B : Family V) (U : Finset V) : Family U :=
  (B.filter (fun b => b.support ⊆ U)).image (restrictExponent U)

lemma contains_restrictionFamily (B : Family V) (U : Finset V) (a : Exponent U) :
    Contains B (extendExponent U a) ↔ Contains (restrictionFamily B U) a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hs : b.support ⊆ U := by
      intro j hj
      by_contra hjU
      have h := hba j
      have hp := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      simp only [extendExponent_apply, dif_neg hjU] at h
      omega
    refine ⟨restrictExponent U b, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, rfl⟩, ?_⟩
    intro j
    simpa using hba j
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hcB, hcU⟩ := Finset.mem_filter.mp hc
    refine ⟨c, hcB, ?_⟩
    intro j
    by_cases hj : j ∈ U
    · simpa [hj] using hba ⟨j, hj⟩
    · have hz : c j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hcU h))
      simp [hj, hz]

theorem betti_restriction (B : Family V) (U : Finset V) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) B (extendExponent U a) i =
      bettiNumber (k := k) (restrictionFamily B U) a i :=
  betti_restriction_transport U B _ (contains_restrictionFamily B U) a i

lemma contains_extendedFamily (U : Finset V) (B : Family U) (a : Exponent U) :
    Contains (B.image (extendExponent U)) (extendExponent U a) ↔ Contains B a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨c, hc, (extendExponent_le_iff U c a).mp hba⟩
  · rintro ⟨b, hb, hba⟩
    exact ⟨extendExponent U b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      (extendExponent_le_iff U b a).mpr hba⟩

theorem betti_extension (U : Finset V) (B : Family U) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) (B.image (extendExponent U)) (extendExponent U a) i =
      bettiNumber (k := k) B a i :=
  betti_restriction_transport U _ B (contains_extendedFamily U B) a i

lemma ambient_restriction_faces (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) :
    koszulFaces (B.filter (fun b => b.support ⊆ U)) a = koszulFaces B a := by
  funext s
  apply propext
  constructor
  · rintro ⟨hdiv, b, hb, hba⟩
    exact ⟨hdiv, b, (Finset.mem_filter.mp hb).1, hba⟩
  · rintro ⟨hdiv, b, hb, hba⟩
    refine ⟨hdiv, b, Finset.mem_filter.mpr ⟨hb, ?_⟩, hba⟩
    intro j hj
    apply ha
    have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
    have hbj : b j ≤ a j := (hba.trans tsub_le_self) j
    exact Finsupp.mem_support_iff.mpr (by omega)

theorem betti_ambient_restriction (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) (i : ℕ) :
    bettiNumber (k := k) (B.filter (fun b => b.support ⊆ U)) a i =
      bettiNumber (k := k) B a i :=
  bettiNumber_congr_faces _ _ _ _ _ (ambient_restriction_faces B U a ha)

end Characterizations.Strands

end
end CheckedCharacterizationsSource50

/-! ## Source: Characterizations.TriangleCore -/
section CheckedCharacterizationsSource51

/-! # Rank-maximal nonlinear localizations and the triangular range

Every Betti number used here is a component of the genuine derived Tor module.
Supported ambient degrees are identified with degrees over the polynomial ring
on the retained variables by the checked Koszul chain isomorphism.
-/

noncomputable section
set_option maxHeartbeats 900000
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem localFamily_equigenerated_iff {B : Family V} {U : Finset V} {e : ℕ} :
    Equigenerated (localFamily B U) e ↔ Equigenerated (localize B U) e := by
  rw [localize_eq_extend_localFamily]
  constructor
  · intro h a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    simpa only [extendExponent_degree] using h b hb
  · intro h a ha
    have hh := h (extendExponent U a) (mem_image.mpr ⟨a,ha,rfl⟩)
    simpa only [extendExponent_degree] using hh

theorem betti_localize_supported (B : Family V) (U : Finset V)
    (a : Exponent V) (ha : a.support ⊆ U) (i : ℕ) :
    bettiNumber (k := k) (localize B U) a i =
      bettiNumber (k := k) (localFamily B U) (restrictExponent U a) i := by
  have he : extendExponent U (restrictExponent U a) = a := by
    rw [extend_restrict]
    ext j
    by_cases hj : j ∈ U
    · simp [hj]
    · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (ha h))
      simp [hj,hz]
  rw [← he,localize_eq_extend_localFamily,Strands.betti_extension,restrict_extend]

theorem restrictExponent_degree_supported (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) : (restrictExponent U a).degree = a.degree := by
  rw [restrictExponent_degree,← degree_project]
  congr 1
  ext j
  by_cases hj : j ∈ U
  · simp [hj]
  · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (ha h))
    simp [hj,hz]

/-- Linearity through a homological position, expressed using actual Tor
components in the naturally identified supported ambient multidegrees. -/
def LocalLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent V, a.support ⊆ U → ∀ i : ℕ, i ≤ t →
    a.degree ≠ e+i → bettiNumber (k := k) (localize B U) a i = 0

def TriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localize B U) e ∧
      (0 < e → LocalLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

theorem localLinearThrough_of_linearResolution {B : Family V} (hB : B.Nonempty)
    (U : Finset V) {e : ℕ} (he : Equigenerated (localize B U) e)
    (hL : HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (t : ℕ) : LocalLinearThrough (k := k) B U e t := by
  rw [monomialLocalization_eq] at hL
  obtain ⟨f,⟨P⟩⟩ := hL
  have hf := P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U)
  have he' := localFamily_equigenerated_iff.mpr he
  obtain ⟨b,hb⟩ := localFamily_nonempty hB U
  have hef : e = f := (he' b hb).symm.trans (hf b hb)
  subst f
  intro a ha i hi hoff
  rw [betti_localize_supported B U a ha i]
  exact P.bettiNumber_eq_zero_off_linear (localFamily B U) (localFamily_antichain B U)
    (restrictExponent U a) i (by rwa [restrictExponent_degree_supported U a ha])

theorem triangularTests_of_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (d : ℕ) : TriangularTests (k := k) B d := by
  intro U _ _
  have hp := localize_polymatroidal hB U
  obtain ⟨e,⟨P⟩⟩ := linearResolution_of_polymatroidal (k := k) hp
  have he := P.equigenerated_of_monomial (localize B U) (localize_antichain B U)
  refine ⟨e,he,?_⟩
  intro _ a _ i _ hoff
  exact P.bettiNumber_eq_zero_off_linear (localize B U) (localize_antichain B U) a i hoff

theorem locallyEquigenerated_of_triangularTests {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (ht : TriangularTests (k := k) B d) :
    LocallyEquigenerated B :=
  locallyEquigenerated_of_band_tests hB hd (fun U hc hk =>
    let ⟨e,he,_⟩ := ht U hc hk
    ⟨e,he⟩)

/-- Enlarge a nonlinear localization without changing its generators or its
Tor component until every restored variable costs one unit of generator degree. -/
theorem maximize_low_nonlinear_localization {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B)
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) :
    ∃ W : Finset V, U ⊆ W ∧ lowerRank B W = e ∧
      Equigenerated (localize B W) e ∧ 2 ≤ W.card ∧ 2 ≤ e ∧
      e+(Fintype.card V-W.card) ≤ d ∧
      i ≤ min (e-1) (min (d-1-(Fintype.card V-W.card)) (W.card-1)) ∧
      a.support ⊆ W ∧ bettiNumber (k := k) (localize B W) a i ≠ 0 := by
  let candidates : Finset (Finset V) := univ.filter (fun W => U ⊆ W ∧ lowerRank B W = e)
  have hne : candidates.Nonempty := ⟨U,mem_filter.mpr ⟨mem_univ _,le_rfl,hr⟩⟩
  obtain ⟨W,hW,hmax⟩ := candidates.exists_maximal hne
  obtain ⟨hUW,hrW⟩ := (mem_filter.mp hW).2
  have hsame : localize B W = localize B U :=
    localize_eq_of_rank_eq hB hUW (hl W) (hr.trans hrW.symm)
  have hinc : ∀ j ∉ W, lowerRank B W+1 ≤ lowerRank B (insert j W) := by
    intro j hj
    have hmono := lowerRank_mono hB (subset_insert j W)
    by_contra hn
    have hreq : lowerRank B (insert j W) = e := by omega
    have hmem : insert j W ∈ candidates :=
      mem_filter.mpr ⟨mem_univ _,hUW.trans (subset_insert j W),hreq⟩
    have hsub := hmax hmem (subset_insert j W)
    exact hj (hsub (mem_insert_self j W))
  have hsm : SupermodularAbove (lowerRank B) W :=
    fun A C _ _ => lowerRank_supermodular hB hl A C
  have hcost := supermodular_rank_codimension_bound hsm hinc
  rw [hrW,lowerRank_univ_of_equigenerated hB hd] at hcost
  have hcards := card_le_card hUW
  refine ⟨W,hUW,hrW,hsame ▸ he,by omega,by omega,hcost,?_,ha.trans hUW,?_⟩
  · exact le_min hie (le_min (by omega) (by omega))
  · rwa [hsame]

theorem triangularTests_exclude_low_nonlinear {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (ht : TriangularTests (k := k) B d)
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) : False := by
  have hl := locallyEquigenerated_of_triangularTests hB hd ht
  obtain ⟨W,hUW,hrW,heW,hcW,he2,hcost,hiW,haW,hbettiW⟩ :=
    maximize_low_nonlinear_localization hB hd hl U e i a he hr hc hi hie hic ha hdeg hbetti
  obtain ⟨f,hf,hlinear⟩ := ht W hcW (by omega)
  obtain ⟨b,hb⟩ := localize_nonempty hB W
  have hef : e = f := (heW b hb).symm.trans (hf b hb)
  subst f
  exact hbettiW (hlinear (by omega) a haW i hiW (by omega))

theorem linearBand_excludes_low_nonlinear {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B)
    (ht : ∀ W : Finset V, 2 ≤ W.card → Fintype.card V-W.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) W))
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) : False := by
  obtain ⟨W,hUW,hrW,heW,hcW,he2,hcost,hiW,haW,hbettiW⟩ :=
    maximize_low_nonlinear_localization hB hd hl U e i a he hr hc hi hie hic ha hdeg hbetti
  have hL := ht W hcW (by omega)
  exact hbettiW (localLinearThrough_of_linearResolution hB W heW hL i a haW i le_rfl (by omega))

theorem locallyEquigenerated_of_linearBand {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (ht : ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    LocallyEquigenerated B := by
  apply locallyEquigenerated_of_band_tests hB hd
  intro U hc hk
  have hL := ht U hc hk
  rw [monomialLocalization_eq] at hL
  obtain ⟨e,⟨P⟩⟩ := hL
  exact ⟨e,localFamily_equigenerated_iff.mp
    (P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U))⟩

end Characterizations

end
end CheckedCharacterizationsSource51

/-! ## Source: Characterizations.MixedMinors -/
section CheckedCharacterizationsSource52

/-! # Coordinate restrictions and mixed monomial minors

Restriction retains exactly those minimal exponent vectors supported on the
retained coordinates.  Localization then sets the other variables equal to
one and removes divisibility redundancies.  The identities below are proved
for these literal operations on generators.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def restriction (B : Family V) (A : Finset V) : Family V :=
  B.filter (fun a => project A a = a)

@[simp] theorem mem_restriction {B : Family V} {A : Finset V} {a : Exponent V} :
    a ∈ restriction B A ↔ a ∈ B ∧ project A a = a := by
  simp [restriction]

theorem restriction_subset (B : Family V) (A : Finset V) : restriction B A ⊆ B :=
  fun _ h => (mem_restriction.mp h).1

theorem restriction_antichain {B : Family V} (hB : Antichain B) (A : Finset V) :
    Antichain (restriction B A) := by
  intro a ha b hb hab
  exact hB a (restriction_subset B A ha) b (restriction_subset B A hb) hab

theorem restriction_equigenerated {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (A : Finset V) : Equigenerated (restriction B A) d :=
  fun a ha => hB a (restriction_subset B A ha)

theorem project_inter (A U : Finset V) (a : Exponent V) :
    project U (project A a) = project (A ∩ U) a := by
  ext i
  by_cases hiA : i ∈ A <;> by_cases hiU : i ∈ U <;> simp [hiA,hiU]

theorem supported_of_le {A : Finset V} {a b : Exponent V}
    (hb : project A b = b) (hab : a ≤ b) : project A a = a := by
  ext i
  by_cases hi : i ∈ A
  · simp [hi]
  · have hbi := congrArg (fun c : Exponent V => c i) hb
    have habi := hab i
    simp only [project_apply,if_neg hi] at hbi ⊢
    omega

theorem contains_restriction (B : Family V) (A : Finset V) (a : Exponent V) :
    Contains (restriction B A) a ↔ Contains B (project A a) := by
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨hb,hbs⟩ := mem_restriction.mp hb
    refine ⟨b,hb,?_⟩
    have hh := project_mono A hba
    simpa only [hbs] using hh
  · rintro ⟨b,hb,hba⟩
    exact ⟨b,mem_restriction.mpr ⟨hb,supported_of_le (project_project le_rfl a) hba⟩,
      hba.trans (project_le A a)⟩

theorem antichain_eq_of_contains_iff {B C : Family V} (hB : Antichain B)
    (hC : Antichain C) (h : ∀ a, Contains B a ↔ Contains C a) : B = C := by
  have hsub {D E : Family V} (hD : Antichain D)
      (hh : ∀ a, Contains D a ↔ Contains E a) : D ⊆ E := by
    intro a ha
    obtain ⟨b,hb,hba⟩ := (hh a).mp ⟨a,ha,le_rfl⟩
    obtain ⟨c,hc,hcb⟩ := (hh b).mpr ⟨b,hb,le_rfl⟩
    have hca : c = a := hD c hc a ha (hcb.trans hba)
    have hbe : b = a := le_antisymm hba (hca ▸ hcb)
    exact hbe ▸ hb
  exact subset_antisymm (hsub hB h) (hsub hC (fun a => (h a).symm))

theorem localize_localize (B : Family V) (A U : Finset V) :
    localize (localize B A) U = localize B (A ∩ U) := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _) (localize_antichain _ _)
  intro a
  simp only [contains_localize]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨c,hc,rfl⟩ := localize_member hb
    exact ⟨c,hc,by simpa only [project_inter] using hba⟩
  · rintro ⟨c,hc,hca⟩
    obtain ⟨b,hb,hbc⟩ := localize_below (U := A) hc
    refine ⟨b,hb,?_⟩
    exact (project_mono U hbc).trans (by simpa only [project_inter] using hca)

theorem restriction_restriction (B : Family V) (A U : Finset V) :
    restriction (restriction B A) U = restriction B (A ∩ U) := by
  ext a
  simp only [mem_restriction]
  constructor
  · rintro ⟨⟨ha,hA⟩,hU⟩
    exact ⟨ha,by rw [← project_inter,hA,hU]⟩
  · rintro ⟨ha,hAU⟩
    have hA : project A a = a := by
      rw [← hAU,project_inter,inter_eq_left.mpr inter_subset_left]
    have hU : project U a = a := by
      rw [← hAU,project_inter,inter_eq_left.mpr inter_subset_right]
    exact ⟨⟨ha,hA⟩,hU⟩

/-- The mixed-minor identity (4.2), including removal of redundant projected
monomials on both sides. -/
theorem localize_restriction (B : Family V) {A U : Finset V} (hUA : U ⊆ A) :
    localize (restriction B A) U = restriction (localize B (U ∪ Aᶜ)) U := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _)
    (restriction_antichain (localize_antichain _ _) _)
  intro a
  rw [contains_localize,contains_restriction,contains_localize]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨hb,hbs⟩ := mem_restriction.mp hb
    refine ⟨b,hb,?_⟩
    intro i
    have hbi := congrArg (fun c : Exponent V => c i) hbs
    have hi := hba i
    by_cases hiU : i ∈ U
    · simpa [hiU] using hi
    · by_cases hiA : i ∈ A
      · simp [hiU,hiA]
      · have hz : b i = 0 := by simpa only [project_apply,if_neg hiA] using hbi.symm
        simp [hiU,hiA,hz]
  · rintro ⟨b,hb,hba⟩
    have hbs : project A b = b := by
      ext i
      by_cases hiA : i ∈ A
      · simp [hiA]
      · have hiU : i ∉ U := fun h => hiA (hUA h)
        have hi := hba i
        simp only [project_apply,mem_union,mem_compl,hiU,hiA,
          not_false_eq_true,or_true,if_true,if_false] at hi
        simp only [project_apply,if_neg hiA]
        omega
    refine ⟨b,mem_restriction.mpr ⟨hb,hbs⟩,?_⟩
    intro i
    by_cases hiU : i ∈ U
    · have hi := hba i
      simpa only [project_apply,if_pos hiU,mem_union,hiU,true_or,if_true] using hi
    · simp [hiU]

def mixedMinor (B : Family V) (A U : Finset V) : Family V :=
  localize (restriction B A) U

theorem localize_restriction_inter (B : Family V) (A U : Finset V) :
    localize (restriction B A) U = localize (restriction B A) (A ∩ U) := by
  apply antichain_eq_of_contains_iff (localize_antichain _ _) (localize_antichain _ _)
  intro a
  simp only [contains_localize]
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  have hbs := (mem_restriction.mp hb).2
  have he : project U b = project (A ∩ U) b := by rw [← project_inter,hbs]
  rw [he]

theorem restriction_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A : Finset V) : LocallyEquigenerated (restriction B A) := by
  intro U
  rw [localize_restriction_inter,localize_restriction B inter_subset_left]
  obtain ⟨d,hd⟩ := hl ((A ∩ U) ∪ Aᶜ)
  exact ⟨d,restriction_equigenerated hd _⟩

theorem localize_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A : Finset V) : LocallyEquigenerated (localize B A) := by
  intro U
  rw [localize_localize]
  exact hl (A ∩ U)

theorem mixedMinor_locallyEquigenerated {B : Family V} (hl : LocallyEquigenerated B)
    (A U : Finset V) : LocallyEquigenerated (mixedMinor B A U) :=
  localize_locallyEquigenerated (restriction_locallyEquigenerated hl A) U

theorem restriction_lowerRank {B : Family V} (hl : LocallyEquigenerated B)
    {A W : Finset V} (hK : (restriction B A).Nonempty) (hWA : W ⊆ A) :
    lowerRank (restriction B A) W = lowerRank B (W ∪ Aᶜ) := by
  have hB : B.Nonempty := hK.mono (restriction_subset B A)
  obtain ⟨b,hb⟩ := localize_nonempty hK W
  have hleft := localize_degree hK (restriction_locallyEquigenerated hl A) hb
  have hrightmem : b ∈ localize B (W ∪ Aᶜ) := by
    rw [localize_restriction B hWA] at hb
    exact restriction_subset _ _ hb
  exact hleft.symm.trans (localize_degree hB hl hrightmem)

theorem localize_nonempty_iff (B : Family V) (U : Finset V) :
    (localize B U).Nonempty ↔ B.Nonempty := by
  refine ⟨?_,fun h => localize_nonempty h U⟩
  rintro ⟨b,hb⟩
  obtain ⟨a,ha,_⟩ := localize_member hb
  exact ⟨a,ha⟩

theorem mixedMinor_lowerRank {B : Family V} (hl : LocallyEquigenerated B)
    {A U W : Finset V} (hM : (mixedMinor B A U).Nonempty)
    (hUA : U ⊆ A) (hWU : W ⊆ U) :
    lowerRank (mixedMinor B A U) W = lowerRank B (W ∪ Aᶜ) := by
  have hK : (restriction B A).Nonempty := (localize_nonempty_iff _ _).mp hM
  rw [mixedMinor,lowerRank_localize hK hWU]
  exact restriction_lowerRank hl hK (hWU.trans hUA)

theorem localize_mixedMinor (B : Family V) (A U W : Finset V) :
    localize (mixedMinor B A U) W = mixedMinor B A (U ∩ W) := by
  exact localize_localize _ _ _

/-- A further coordinate restriction of a mixed minor is again a mixed
minor of the original family.  The newly discarded coordinates are exactly
those in `U \ W`; the previously localized coordinates remain localized. -/
theorem restriction_mixedMinor (B : Family V) {A U W : Finset V}
    (hUA : U ⊆ A) (hWU : W ⊆ U) :
    restriction (mixedMinor B A U) W = mixedMinor B (A ∩ (W ∪ Uᶜ)) W := by
  have hWsub : W ⊆ A ∩ (W ∪ Uᶜ) := by
    intro i hi
    exact mem_inter.mpr ⟨hUA (hWU hi),mem_union_left _ hi⟩
  have he : W ∪ (A ∩ (W ∪ Uᶜ))ᶜ = U ∪ Aᶜ := by
    ext i
    have h1 := @hUA i
    have h2 := @hWU i
    simp only [mem_union,mem_inter,mem_compl]
    tauto
  rw [mixedMinor,localize_restriction B hUA,restriction_restriction,
    inter_eq_right.mpr hWU,mixedMinor,localize_restriction B hWsub,he]

theorem restriction_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (A : Finset V) : IsPolymatroidal (restriction B A) := by
  obtain ⟨d,hd⟩ := hB.1
  refine ⟨⟨d,restriction_equigenerated hd A⟩,?_⟩
  intro a ha b hb i hi
  obtain ⟨ha,haA⟩ := mem_restriction.mp ha
  obtain ⟨hb,hbA⟩ := mem_restriction.mp hb
  obtain ⟨j,hj,he⟩ := hB.2 a ha b hb i hi
  refine ⟨j,hj,mem_restriction.mpr ⟨he,?_⟩⟩
  ext x
  by_cases hx : x ∈ A
  · simp [hx]
  · have hax := congrArg (fun c : Exponent V => c x) haA
    have hbx := congrArg (fun c : Exponent V => c x) hbA
    have hxi : x ≠ i := by
      intro hh
      subst x
      simp only [project_apply,if_neg hx] at hax hbx
      omega
    have hxj : x ≠ j := by
      intro hh
      subst x
      simp only [project_apply,if_neg hx] at hax hbx
      omega
    simp only [project_apply,if_neg hx,exchange_apply,
      Finsupp.single_apply,if_neg hxi,if_neg hxj]
    simp only [project_apply,if_neg hx] at hax
    omega

theorem mixedMinor_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (A U : Finset V) : IsPolymatroidal (mixedMinor B A U) :=
  localize_polymatroidal (restriction_polymatroidal hB A) U

end Characterizations

end
end CheckedCharacterizationsSource52

/-! ## Source: Characterizations.RationalConvex -/
section CheckedCharacterizationsSource53

/-! # Rational coefficients for rational points in finite real convex hulls -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset Matrix
open scoped BigOperators

theorem rational_solution_of_injective_matrix
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix J I ℚ) (hinj : Function.Injective A.mulVec)
    (b : J → ℚ) (y : I → ℝ)
    (hy : A.map (Rat.castHom ℝ) *ᵥ y = fun j => (b j : ℝ)) :
    ∃ x : I → ℚ, ∀ i, (x i : ℝ) = y i := by
  have hker : LinearMap.ker A.toLin' = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨L, hL⟩ := A.toLin'.exists_leftInverse_of_injective hker
  let M := LinearMap.toMatrix' L
  have hMA : M * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hL
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id, M] using h
  have hreal : M.map (Rat.castHom ℝ) * A.map (Rat.castHom ℝ) = 1 := by
    rw [← Matrix.map_mul, hMA]
    exact Matrix.map_one _ (by simp) (by simp)
  refine ⟨M *ᵥ b, ?_⟩
  intro i
  change (Rat.castHom ℝ) ((M *ᵥ b) i) = y i
  rw [RingHom.map_mulVec (Rat.castHom ℝ)]
  change (M.map (Rat.castHom ℝ) *ᵥ (fun j => (b j : ℝ))) i = y i
  rw [← hy, Matrix.mulVec_mulVec, hreal, Matrix.one_mulVec]

variable {V : Type u} {I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def affineMatrix (p : I → V → ℚ) : Matrix (Option V) I ℚ :=
  fun j i => j.elim 1 (p i)

theorem affineMatrix_injective (p : I → V → ℚ)
    (hp : AffineIndependent ℝ (fun i v => (p i v : ℝ))) :
    Function.Injective (affineMatrix p).mulVec := by
  intro x y hxy
  let w : I → ℝ := fun i => (x i : ℝ) - y i
  have hs : ∑ i, w i = 0 := by
    have h := congrFun hxy none
    simp only [Matrix.mulVec, dotProduct, affineMatrix, Option.elim_none, one_mul] at h
    have hr : (∑ i, (x i : ℝ)) = ∑ i, (y i : ℝ) := by exact_mod_cast h
    simpa only [w, sum_sub_distrib, sub_eq_zero] using hr
  have hv : ∑ i, w i • (fun v => (p i v : ℝ)) = (0 : V → ℝ) := by
    funext v
    have h := congrFun hxy (some v)
    simp only [Matrix.mulVec, dotProduct, affineMatrix, Option.elim_some] at h
    have hr : (∑ i, (p i v : ℝ) * x i) = ∑ i, (p i v : ℝ) * y i := by exact_mod_cast h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      w, sub_mul, sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using hr
  have hzero := (affineIndependent_iff_of_fintype ℝ _).mp hp w hs (by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w _ hs 0,
      Finset.weightedVSubOfPoint_apply]
    simpa only [vsub_eq_sub, sub_zero] using hv)
  funext i
  have h := hzero i
  change (x i : ℝ) - y i = 0 at h
  exact_mod_cast sub_eq_zero.mp h

/-- Real barycentric coordinates on a rational affine-independent family are
rational whenever the represented point is rational. -/
theorem rational_barycentric_weights (p : I → V → ℚ) (b : V → ℚ)
    (hp : AffineIndependent ℝ (fun i v => (p i v : ℝ))) (w : I → ℝ)
    (hs : ∑ i, w i = 1) (hb : ∀ v, ∑ i, w i * (p i v : ℝ) = b v) :
    ∃ q : I → ℚ, ∀ i, (q i : ℝ) = w i := by
  apply rational_solution_of_injective_matrix (affineMatrix p) (affineMatrix_injective p hp)
    (fun j : Option V => j.elim 1 b) w
  funext j
  cases j with
  | none => simpa [Matrix.mulVec, dotProduct, affineMatrix] using hs
  | some v => simpa [Matrix.mulVec, dotProduct, affineMatrix, mul_comm] using hb v

/-- Every integral point in the real convex hull of a finite integral family
has a finite rational convex combination of actual members of that family. -/
theorem rational_combination_of_mem_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ (J : Type u) (_ : Fintype J) (p : J → Exponent V) (q : J → ℚ),
      (∀ j, p j ∈ B) ∧ (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧
        ∀ v, ∑ j, q j * (p j v : ℚ) = a v := by
  classical
  let T := Caratheodory.minCardFinsetOfMemConvexHull ha
  have hTsub := Caratheodory.minCardFinsetOfMemConvexHull_subseteq ha
  have hTI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull ha
  have hTa := Caratheodory.mem_minCardFinsetOfMemConvexHull ha
  change AffineIndependent ℝ (fun j : T => j.val) at hTI
  change realExponent a ∈ convexHull ℝ (T : Set (V → ℝ)) at hTa
  have hpre : ∀ j : T, ∃ b ∈ B, realExponent b = j.val := by
    intro j
    exact hTsub j.property
  choose p hp hpeq using hpre
  rw [Finset.convexHull_eq] at hTa
  obtain ⟨w, hw, hsum, hcomb⟩ := hTa
  let α : T → ℝ := fun j => w j.val
  have hsum' : ∑ j : T, α j = 1 := by
    simpa only [α, Finset.sum_coe_sort] using hsum
  have hpI : AffineIndependent ℝ (fun j : T => fun v => ((p j v : ℚ) : ℝ)) := by
    have he : (fun j : T => fun v => ((p j v : ℚ) : ℝ)) = fun j : T => j.val := by
      funext j v
      simpa [realExponent] using congrFun (hpeq j) v
    rw [he]
    exact hTI
  have hcomb' : ∀ v, ∑ j : T, α j * ((p j v : ℚ) : ℝ) = ((a v : ℚ) : ℝ) := by
    intro v
    have hh := congrFun hcomb v
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at hh
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id_eq, realExponent] at hh
    have he : (∑ j : T, α j * ((p j v : ℚ) : ℝ)) = ∑ z ∈ T, w z * z v := by
      calc
        _ = ∑ j : T, w j.val * j.val v := by
          apply Finset.sum_congr rfl
          intro j _
          have hj := congrFun (hpeq j) v
          simp only [realExponent] at hj
          simpa [α] using congrArg (fun r : ℝ => w j.val * r) hj
        _ = _ := Finset.sum_coe_sort T (fun z => w z * z v)
    rw [he]
    simpa using hh
  obtain ⟨q, hq⟩ := rational_barycentric_weights
    (fun j : T => fun v => (p j v : ℚ)) (fun v => (a v : ℚ)) hpI α hsum' hcomb'
  refine ⟨↥T, inferInstance, p, q, hp, ?_, ?_, ?_⟩
  · intro j
    have h : 0 ≤ (q j : ℝ) := by rw [hq]; exact hw j.val j.property
    exact_mod_cast h
  · have h : (∑ j, (q j : ℝ)) = 1 := by simpa only [hq] using hsum'
    exact_mod_cast h
  · intro v
    have h : (∑ j, (q j : ℝ) * ((p j v : ℚ) : ℝ)) = ((a v : ℚ) : ℝ) := by
      simpa only [hq] using hcomb' v
    exact_mod_cast h

end Characterizations

end
end CheckedCharacterizationsSource53

/-! ## Source: Characterizations.ClearDenominators -/
section CheckedCharacterizationsSource54

/-! # Exact denominator clearing for nonnegative rational convex combinations -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset
open scoped BigOperators

theorem nonnegative_rational_common_denominator {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : I → ℕ, ∀ i, (m i : ℚ) = (N : ℚ) * q i := by
  classical
  let N : ℕ := ∏ i, (q i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
  let m : I → ℕ := fun i => (q i).num.toNat * (N / (q i).den)
  refine ⟨N, hN, m, ?_⟩
  intro i
  have hdiv : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have he : (q i).den * (N / (q i).den) = N := Nat.mul_div_cancel' hdiv
  have hnum : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
  have hval : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
    (div_eq_iff (show ((q i).den : ℚ) ≠ 0 by exact_mod_cast (q i).den_ne_zero)).mp
      (q i).num_div_den
  have he' : ((q i).den : ℚ) * (N / (q i).den : ℕ) = N := by exact_mod_cast he
  change ((q i).num.toNat * (N / (q i).den) : ℕ) = (N : ℚ) * q i
  rw [Nat.cast_mul, hnum, hval, mul_assoc, he', mul_comm]

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem scaled_sum_of_mem_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ (N : ℕ) (_ : 0 < N) (J : Type u) (_ : Fintype J)
      (p : J → Exponent V) (m : J → ℕ),
      (∀ j, p j ∈ B) ∧ (∑ j, m j = N) ∧ N • a = ∑ j, m j • p j := by
  classical
  obtain ⟨J, hJ, p, q, hp, hq, hsum, hcomb⟩ := rational_combination_of_mem_convexHull B a ha
  letI : Fintype J := hJ
  obtain ⟨N, hN, m, hm⟩ := nonnegative_rational_common_denominator q hq
  have hsum' : ∑ j, m j = N := by
    have h : (∑ j, (m j : ℚ)) = N := by
      simp_rw [hm]
      rw [← Finset.mul_sum, hsum, mul_one]
    exact_mod_cast h
  refine ⟨N, hN, J, hJ, p, m, hp, hsum', ?_⟩
  ext v
  have h : (N : ℚ) * (a v : ℚ) = ∑ j, (m j : ℚ) * (p j v : ℚ) := by
    simp_rw [hm, mul_assoc]
    rw [← Finset.mul_sum, hcomb]
  have hn : N * a v = ∑ j, m j * p j v := by exact_mod_cast h
  simpa only [Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul] using hn

end Characterizations

end
end CheckedCharacterizationsSource54

/-! ## Source: Characterizations.IntegralBridge -/
section CheckedCharacterizationsSource55

/-! # From actual Rees-algebra integrality to ideal integrality

This supplies addition and multiplication closure for the monomials proved
integral by a power-membership witness. The final conclusion is the ordinary
monic ideal-integrality equation, not a substitute definition.
-/

noncomputable section
namespace Characterizations
open Polynomial CommAlg
open scoped BigOperators
variable {R : Type*} [CommRing R]

def reesIntegralIdeal (I : Ideal R) : Ideal R where
  carrier := {x | IsIntegral (reesAlgebra I) (C x * X : R[X])}
  zero_mem' := by simpa using (isIntegral_zero : IsIntegral (reesAlgebra I) (0 : R[X]))
  add_mem' hx hy := by simpa [map_add, add_mul] using hx.add hy
  smul_mem' r x hx := by
    have hr : IsIntegral (reesAlgebra I) (C r : R[X]) := by
      exact isIntegral_algebraMap (R := reesAlgebra I) (A := R[X])
        (x := algebraMap R (reesAlgebra I) r)
    simpa [smul_eq_mul, map_mul, mul_assoc] using hr.mul hx

theorem mem_reesIntegralIdeal_of_pow_mem {I : Ideal R} {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n ∈ I ^ n) : x ∈ reesIntegralIdeal I := by
  have hmem : (C x * X : R[X]) ^ n ∈ reesAlgebra I := by
    simpa [← Polynomial.C_mul_X_pow_eq_monomial, mul_pow] using
      (reesAlgebra.monomial_mem.mpr hx : Polynomial.monomial n (x ^ n) ∈ reesAlgebra I)
  have hi : IsIntegral (reesAlgebra I) ((C x * X : R[X]) ^ n) :=
    isIntegral_algebraMap (R := reesAlgebra I) (A := R[X]) (x := ⟨_, hmem⟩)
  exact IsIntegral.of_pow hn hi

theorem adjoin_C_mul_X_eq_rees (I : Ideal R) :
    Algebra.adjoin R {C r * X | r ∈ I} = reesAlgebra I := by
  rw [← adjoin_monomial_eq_reesAlgebra I]
  congr 1
  ext p
  simp only [Submodule.mem_map, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp [← Polynomial.C_mul_X_pow_eq_monomial]⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp [← Polynomial.C_mul_X_pow_eq_monomial]⟩

theorem integralOverIdeal_of_mem_reesIntegralIdeal [Nontrivial R] {I : Ideal R} {x : R}
    (hx : x ∈ reesIntegralIdeal I) : IntegralOverIdeal I x := by
  have hi : IsIntegral (Algebra.adjoin R {C r * X | r ∈ I}) (C x * X : R[X]) := by
    rw [adjoin_C_mul_X_eq_rees]
    exact hx
  have hAlg : Polynomial.algebra R R = Algebra.id R[X] := by
    apply Algebra.algebra_ext
    intro p
    simp [Polynomial.algebra]
  have ht := Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    (R := R) (S := R) (I := I) (x := x)
  rw [hAlg] at ht
  obtain ⟨p, hp, he, hc⟩ := ht hi
  refine ⟨p.natDegree, Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp he,
    fun i => p.coeff i, fun i _ => hc i, ?_⟩
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ] at he
  simpa only [smul_eq_mul, hp.coeff_natDegree, one_mul, add_comm] using he

theorem integralOverIdeal_of_pow_mem [Nontrivial R] {I : Ideal R} {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n ∈ I ^ n) : IntegralOverIdeal I x :=
  integralOverIdeal_of_mem_reesIntegralIdeal (mem_reesIntegralIdeal_of_pow_mem hn hx)

/-- Ideal-span induction transfers finitely many monomial power witnesses to
every polynomial in the generated ideal, with a genuine integral equation. -/
theorem integralOverIdeal_of_span_generators [Nontrivial R] {I : Ideal R} (S : Set R)
    (hS : ∀ x ∈ S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I ^ n)
    {x : R} (hx : x ∈ Ideal.span S) : IntegralOverIdeal I x := by
  apply integralOverIdeal_of_mem_reesIntegralIdeal
  apply (Ideal.span_le.mpr (fun y hy => ?_) : Ideal.span S ≤ reesIntegralIdeal I) hx
  obtain ⟨n, hn, hp⟩ := hS y hy
  exact mem_reesIntegralIdeal_of_pow_mem hn hp

end Characterizations

end
end CheckedCharacterizationsSource55

/-! ## Source: Characterizations.MonomialIntegrality -/
section CheckedCharacterizationsSource56

/-! # Integral equations for every lattice point of a monomial Newton polytope -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset MvPolynomial
open scoped BigOperators
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k]

theorem monomial_power_mem_of_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ N : ℕ, 0 < N ∧ (monomial a (1 : k)) ^ N ∈ (monomialIdeal k B) ^ N := by
  classical
  obtain ⟨N, hN, J, hJ, p, m, hp, hsum, he⟩ := scaled_sum_of_mem_convexHull B a ha
  letI : Fintype J := hJ
  refine ⟨N, hN, ?_⟩
  have hprod : (∏ j, (monomial (p j) (1 : k)) ^ m j) ∈
      ∏ j, (monomialIdeal k B) ^ m j := by
    apply Ideal.prod_mem_prod
    intro j _
    apply Ideal.pow_mem_pow
    exact Ideal.subset_span (Set.mem_image_of_mem _ (hp j))
  have hpow : (∏ j, (monomialIdeal k B) ^ m j) = (monomialIdeal k B) ^ N := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [hpow] at hprod
  have hmon : (monomial a (1 : k)) ^ N = ∏ j, (monomial (p j) (1 : k)) ^ m j := by
    simp only [MvPolynomial.monomial_pow, one_pow]
    rw [he]
    simpa using (MvPolynomial.monomial_sum_one (s := Finset.univ)
      (f := fun j => m j • p j) (R := k))
  rw [hmon]
  exact hprod

theorem monomial_integral_of_convexHull [Nontrivial k] (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    CommAlg.IntegralOverIdeal (monomialIdeal k B) (monomial a (1 : k)) := by
  obtain ⟨N, hN, h⟩ := monomial_power_mem_of_convexHull k B a ha
  exact integralOverIdeal_of_pow_mem hN h

end Characterizations

end
end CheckedCharacterizationsSource56

/-! ## Source: Characterizations.SubsetWeights -/
section CheckedCharacterizationsSource57

/-! # Literal subset-degree valuations and integral closure -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def subsetWeight (U : Finset V) : V → ℤ := fun v => if v ∈ U then 1 else 0

theorem weight_subsetWeight (U : Finset V) (a : Exponent V) :
    Finsupp.weight (subsetWeight U) a = (subsetSum a U : ℤ) := by
  rw [Finsupp.weight_eq_sum]
  simp only [subsetWeight, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  simp [subsetSum]

variable {k : Type*} [CommRing k]

theorem subsetWeight_nonnegative (U : Finset V) (f : MvPolynomial V k) :
    Weight.Bound (subsetWeight U) 0 f := by
  intro a _
  rw [weight_subsetWeight]
  positivity

theorem subsetWeight_bound_of_mem (B : Family V) {f : MvPolynomial V k}
    (hf : f ∈ monomialIdeal k B) (U : Finset V) :
    Weight.Bound (subsetWeight U) (lowerRank B U : ℤ) f := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := (mem_monomialIdeal_iff B f).mp hf a (Finsupp.mem_support_iff.mpr ha)
  rw [weight_subsetWeight]
  exact_mod_cast (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))

theorem subsetWeight_bound_of_integral [IsDomain k] (B : Family V) {f : MvPolynomial V k}
    (hf : IntegralOverIdeal (monomialIdeal k B) f) (U : Finset V) :
    Weight.Bound (subsetWeight U) (lowerRank B U : ℤ) f :=
  Weight.bound_of_integral (RingHom.id _) (subsetWeight U) (subsetWeight_nonnegative U)
    (monomialIdeal k B) (lowerRank B U : ℤ)
    (fun _ h => subsetWeight_bound_of_mem B h U) hf

theorem integral_mem_canonicalLowerBases [IsDomain k] {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) {f : MvPolynomial V k}
    (hf : IntegralOverIdeal (monomialIdeal k B) f) :
    f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d) := by
  apply (mem_monomialIdeal_iff _ f).mpr
  intro a ha
  apply (contains_canonicalLowerBases_iff hB hl hd a).mpr
  intro U
  have h := subsetWeight_bound_of_integral B hf U a (Finsupp.mem_support_iff.mp ha)
  rw [weight_subsetWeight] at h
  exact_mod_cast h

theorem polymatroidal_integrallyClosed [IsDomain k] {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) : IsIntegrallyClosedIdeal (monomialIdeal k B) := by
  obtain ⟨d, hd⟩ := hp.1
  intro f hf
  apply (mem_monomialIdeal_iff _ f).mpr
  intro a ha
  apply (contains_iff_canonical_lower B hB d hd hp a).mpr
  intro U
  have h := subsetWeight_bound_of_integral B hf U a (Finsupp.mem_support_iff.mp ha)
  rw [weight_subsetWeight] at h
  exact_mod_cast h

end Characterizations

end
end CheckedCharacterizationsSource57

/-! ## Source: Characterizations.IntegralClosure -/
section CheckedCharacterizationsSource58

/-! # Theorem 2.11: exact integral closure and the integral-closure characterization -/

noncomputable section
namespace Characterizations
universe u
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem canonicalLowerBase_mem_convexHull {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank B) d) :
    realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V))) := by
  rw [convexHull_generators_eq_lowerRankPolytope hB hanti hl hd]
  obtain ⟨hdeg, hlo⟩ := (mem_lowerBaseFamily _ _ a).mp ha
  refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_⟩
  · rw [realSubsetSum_exponent, subsetSum_univ, hdeg]
  · intro U
    rw [realSubsetSum_exponent]
    exact_mod_cast hlo U

variable {k : Type*} [CommRing k] [IsDomain k]

theorem mem_canonicalLowerBases_integral {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {f : MvPolynomial V k} (hf : f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d)) :
    IntegralOverIdeal (monomialIdeal k B) f := by
  apply integralOverIdeal_of_span_generators
    ((fun a : Exponent V => monomial a (1 : k)) ''
      (lowerBaseFamily (lowerRank B) d : Set (Exponent V))) ?_ hf
  rintro y ⟨a, ha, rfl⟩
  exact monomial_power_mem_of_convexHull k B a
    (canonicalLowerBase_mem_convexHull hB hanti hl hd ha)

/-- Every polynomial is integral over the original ideal exactly when it lies
in the full integer-base ideal. Both directions use ordinary monic equations. -/
theorem integralOverIdeal_iff_mem_canonicalLowerBases {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (f : MvPolynomial V k) :
    IntegralOverIdeal (monomialIdeal k B) f ↔
      f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d) :=
  ⟨integral_mem_canonicalLowerBases hB hl hd,
    mem_canonicalLowerBases_integral hB hanti hl hd⟩

theorem integralClosure_set_eq {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    {f : MvPolynomial V k | IntegralOverIdeal (monomialIdeal k B) f} =
      (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k)) := by
  ext f
  exact integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd f

/-- The full characterization, without assuming equigeneration separately. -/
theorem polymatroidal_iff_integrallyClosed_localEquigenerated {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ IsIntegrallyClosedIdeal (monomialIdeal k B) ∧
      LocallyEquigenerated B := by
  constructor
  · intro hp
    exact ⟨polymatroidal_integrallyClosed hB hp, polymatroidal_locallyEquigenerated hp⟩
  · rintro ⟨hc, hl⟩
    obtain ⟨d, hd⟩ := hl Finset.univ
    rw [localize_univ_of_antichain hanti] at hd
    have hcontains : ∀ a, Contains B a ↔ Contains (lowerBaseFamily (lowerRank B) d) a := by
      intro a
      rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k)]
      constructor
      · intro ha
        exact (integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd _).mp
          (integralOverIdeal_of_mem ha)
      · intro ha
        exact hc _ ((integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd _).mpr ha)
    have he := family_eq_of_contains_iff hanti
      (lowerBaseFamily_equigenerated (lowerRank B) d).antichain hcontains
    rw [he]
    exact canonicalLowerBases_polymatroidal hB hl hd

end Characterizations

end
end CheckedCharacterizationsSource58

/-! ## Source: Characterizations.FiniteHoles -/
section CheckedCharacterizationsSource59

/-! # Finite holes in a minimal coordinate obstruction -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetSum_project_inter (U W : Finset V) (a : Exponent V) :
    subsetSum (project U a) W = subsetSum a (W ∩ U) := by
  simp only [subsetSum, project_apply]
  rw [Finset.sum_ite_mem]

theorem lowerRank_localize_inter {B : Family V} (hB : B.Nonempty) (U W : Finset V) :
    lowerRank (localize B U) W = lowerRank B (W ∩ U) := by
  have hsame : lowerRank (localize B U) W = lowerRank (localize B U) (W ∩ U) := by
    have hs : ∀ b ∈ localize B U, subsetSum b W = subsetSum b (W ∩ U) := by
      intro b hb
      calc
        subsetSum b W = subsetSum (project U b) W := by rw [localize_supported hb]
        _ = _ := subsetSum_project_inter U W b
    apply le_antisymm
    · obtain ⟨b, hb, he⟩ := lowerRank_attained (localize_nonempty hB U) (W ∩ U)
      calc
        lowerRank (localize B U) W ≤ subsetSum b W := lowerRank_le hb W
        _ = lowerRank (localize B U) (W ∩ U) := (hs b hb).trans he
    · obtain ⟨b, hb, he⟩ := lowerRank_attained (localize_nonempty hB U) W
      calc
        lowerRank (localize B U) (W ∩ U) ≤ subsetSum b (W ∩ U) := lowerRank_le hb _
        _ = lowerRank (localize B U) W := (hs b hb).symm.trans he
  rw [hsame, lowerRank_localize hB Finset.inter_subset_right]

theorem lowerFeasible_project_mem {B : Family V} (hB : B.Nonempty) {a : Exponent V}
    (ha : LowerFeasible (lowerRank B) a) (U : Finset V)
    (hp : IsPolymatroidal (localize B U)) : Contains (localize B U) (project U a) := by
  obtain ⟨d, hd⟩ := hp.1
  apply (contains_iff_canonical_lower _ (localize_nonempty hB U) d hd hp _).mpr
  intro W
  rw [lowerRank_localize_inter hB U W, subsetSum_project_inter U W a]
  exact ha (W ∩ U)

theorem hole_coordinate_lt_degree {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    {a : Exponent V} (ha : LowerFeasible (lowerRank B) a) (hout : ¬ Contains B a)
    (i : V) : a i < d := by
  by_contra hn
  have hdi : d ≤ a i := by omega
  let U : Finset V := Finset.univ.erase i
  have hU : U ⊂ Finset.univ := Finset.erase_ssubset (Finset.mem_univ i)
  obtain ⟨b, hb, hba⟩ := (contains_localize B U _).mp
    (lowerFeasible_project_mem hB ha U (hloc U hU))
  apply hout
  refine ⟨b, hb, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact (coordinate_le_degree b i).trans ((hd b hb).le.trans hdi)
  · have hjU : j ∈ U := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    simpa only [project_apply, if_pos hjU] using hba j

def holeSet (B : Family V) : Set (Exponent V) :=
  {a | LowerFeasible (lowerRank B) a ∧ ¬ Contains B a}

theorem holeSet_finite {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    (holeSet B).Finite := by
  apply (Set.finite_Iic (constExponent d)).subset
  intro a ha i
  exact (hole_coordinate_lt_degree hB hd hloc ha.1 ha.2 i).le

theorem exists_top_hole {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hh : (holeSet B).Nonempty) :
    ∃ a ∈ holeSet B, (∀ b ∈ holeSet B, b.degree ≤ a.degree) ∧ d ≤ a.degree ∧
      ∀ i, Contains B (a + Finsupp.single i 1) := by
  obtain ⟨a, ha, hmax⟩ := (holeSet_finite hB hd hloc).exists_maximalFor
    (fun a : Exponent V => a.degree) _ hh
  have hbound : ∀ b ∈ holeSet B, b.degree ≤ a.degree := by
    intro b hb
    by_contra hn
    have hab : a.degree ≤ b.degree := by omega
    exact (not_le_of_gt (by omega : a.degree < b.degree)) (hmax hb hab)
  refine ⟨a, ha, hbound, ?_, ?_⟩
  · have h := ha.1 Finset.univ
    rw [lowerRank_univ_of_equigenerated hB hd, subsetSum_univ] at h
    exact h
  · intro i
    by_contra hout
    have hlo : LowerFeasible (lowerRank B) (a + Finsupp.single i 1) := by
      intro U
      exact (ha.1 U).trans (Finset.sum_le_sum (fun j _ => by simp only [Finsupp.add_apply]; omega))
    have h := hbound _ ⟨hlo, hout⟩
    simp only [map_add, Finsupp.degree_single] at h
    omega

end Characterizations

end
end CheckedCharacterizationsSource59

/-! ## Source: Characterizations.PatternIsolator -/
section CheckedCharacterizationsSource60

/-! # Exact degree-padded isolators on arbitrary active variable sets -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def patternActive (C : Finset V) (i q j : V) : Finset V := insert i (insert q (insert j C))

theorem patternActive_card {C : Finset V} {i q j : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    (patternActive C i q j).card = C.card + 3 := by
  have hiC : i ∉ C := fun hi => by simpa using hC hi
  have hqC : q ∉ C := fun hq => by simpa using hC hq
  have hjC : j ∉ C := fun hj => by simpa using hC hj
  simp [patternActive, hiC, hqC, hjC, hiq, hij, hqj]

theorem exists_pattern_isolator {k : Type*} [CommSemiring k] [Nontrivial k]
    (C : Finset V) (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j)
    (hC : C ⊆ tripleCap i q j) (hCne : C.Nonempty) (d : ℕ) (hd : C.card + 1 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) ↔ ¬ OrderPattern o C i q j := by
  let T := patternActive C i q j
  let e : T ↪ V := Function.Embedding.subtype _
  let I : T := ⟨i, by simp [T, patternActive]⟩
  let Q : T := ⟨q, by simp [T, patternActive]⟩
  let J : T := ⟨j, by simp [T, patternActive]⟩
  have hIQ : I ≠ Q := fun h => hiq (congrArg Subtype.val h)
  have hIJ : I ≠ J := fun h => hij (congrArg Subtype.val h)
  have hQJ : Q ≠ J := fun h => hqj (congrArg Subtype.val h)
  have hTcard : Fintype.card T = C.card + 3 := by
    rw [Fintype.card_coe]
    exact patternActive_card hiq hij hqj hC
  have hfour : 4 ≤ Fintype.card T := by have hh := card_pos.mpr hCne; omega
  have hdegree : Fintype.card T - 2 = C.card + 1 := by omega
  let B₀ := tripleFamily I Q J
  let B₁ := embeddedFamily e B₀
  let c : Exponent V := Finsupp.single i (d - (C.card + 1))
  let B := translatedFamily c B₁
  have hB₀ : Equigenerated B₀ (C.card + 1) := hdegree ▸ tripleFamily_equigenerated I Q J
  have hB₁ : Equigenerated B₁ (C.card + 1) := embeddedFamily_equigenerated hB₀ e
  have hcdegree : c.degree = d - (C.card + 1) := by simp only [c, Finsupp.degree_single]
  refine ⟨B, ?_, ?_, ?_⟩
  · have hh := translatedFamily_equigenerated hB₁ c
    have he : C.card + 1 + c.degree = d := by omega
    exact he ▸ hh
  · intro hp
    have hp₁ : IsPolymatroidal B₁ := (translatedFamily_polymatroidal_iff hB₁ c).mp hp
    have hp₀ : IsPolymatroidal B₀ := embeddedFamily_polymatroidal_implies hB₀ e hp₁
    exact tripleFamily_not_polymatroidal hIQ hIJ hQJ hfour hp₀
  · intro o
    rw [translatedFamily_linearQuotients_iff hB₁ c o,
      embeddedFamily_linearQuotients_iff hB₀ e o,
      tripleFamily_linearQuotients_iff hIQ hIJ hQJ hfour]
    apply not_congr
    simp only [FinalTriple, OrderPattern, restrictedOrder_lt_iff]
    change (o i < o j ∧ o q < o j ∧
      ∀ x : T, x ≠ I → x ≠ Q → x ≠ J → o x.val < o i ∧ o x.val < o q) ↔ _
    constructor
    · rintro ⟨hijO, hqjO, hrest⟩
      refine ⟨hijO, hqjO, ?_⟩
      intro x hx
      have hxT : x ∈ T := by simp [T, patternActive, hx]
      have hxneq := (mem_tripleCap _ _ _ _).mp (hC hx)
      exact hrest ⟨x, hxT⟩ (fun he => hxneq.1 (congrArg Subtype.val he))
        (fun he => hxneq.2.1 (congrArg Subtype.val he))
        (fun he => hxneq.2.2 (congrArg Subtype.val he))
    · rintro ⟨hijO, hqjO, hrest⟩
      refine ⟨hijO, hqjO, ?_⟩
      intro x hxi hxq hxj
      have hxi' : x.val ≠ i := fun he => hxi (Subtype.ext he)
      have hxq' : x.val ≠ q := fun he => hxq (Subtype.ext he)
      have hxj' : x.val ≠ j := fun he => hxj (Subtype.ext he)
      have hxC : x.val ∈ C := by
        have hxT := x.property
        simpa [T, patternActive, hxi', hxq', hxj'] using hxT
      exact hrest x.val hxC

def DegreeOrderTests (k : Type*) [CommSemiring k] (d : ℕ) (F : Set (VariableOrder V)) : Prop :=
  ∀ B : Family V, Equigenerated B d →
    (∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) → IsPolymatroidal B

/-- Theorem 5.4, the full necessary-and-sufficient pattern characterization. -/
theorem degreeOrderTests_iff_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (F : Set (VariableOrder V)) :
    DegreeOrderTests k d F ↔
      CoversPatterns (min (d - 1) (Fintype.card V - 3)) F ∧
      (Fintype.card V - 1 ≤ d → CoversFinalPairs F) := by
  constructor
  · intro htest
    constructor
    · intro i q j hiq hij hqj C hC hc
      by_contra hn
      have hCne : C.Nonempty := card_pos.mp (by omega)
      obtain ⟨B, hB, hnot, hfail⟩ := exists_pattern_isolator (k := k) C i q j hiq hij hqj hC hCne d (by omega)
      apply hnot
      apply htest B hB
      intro o ho
      exact (hfail o).mpr (fun hp => hn ⟨o, ho, hp⟩)
    · intro hdlarge i j hij
      by_contra hn
      let c : Exponent V := Finsupp.single i (d - (Fintype.card V - 1))
      let B := translatedFamily c (pairFamily i j)
      have hB : Equigenerated B d := by
        have hh := translatedFamily_equigenerated (pairFamily_equigenerated i j) c
        have he : (Fintype.card V - 1) + c.degree = d := by simp only [c, Finsupp.degree_single]; omega
        exact he ▸ hh
      have hp := htest B hB (fun o ho =>
        (translatedFamily_linearQuotients_iff (pairFamily_equigenerated i j) c o).mpr
          (pairFamily_linearQuotients_of_not_final hij o (fun hf => hn ⟨o, ho, hf⟩)))
      exact pairFamily_not_polymatroidal hij (by omega)
        ((translatedFamily_polymatroidal_iff (pairFamily_equigenerated i j) c).mp hp)
  · rintro ⟨hpatterns, hpairs⟩ B hB hL
    exact ⟨⟨d, hB⟩, exchange_of_degree_coverage (k := k) hB hcard F hpatterns hpairs hL⟩

end Characterizations

end
end CheckedCharacterizationsSource60

/-! ## Source: Characterizations.Tournament -/
section CheckedCharacterizationsSource61

/-! # A tournament with a predecessor at every vertex -/

noncomputable section
namespace Characterizations
open Classical Finset

def cyclicTournament {n : ℕ} (a b : Fin n) : Prop :=
  (a.val = n - 1 ∧ b.val = 0) ∨ (a.val < b.val ∧ ¬ (a.val = 0 ∧ b.val = n - 1))

theorem cyclicTournament_asymm {n : ℕ} (hn : 3 ≤ n) (a b : Fin n)
    (hab : cyclicTournament a b) : ¬ cyclicTournament b a := by
  simp only [cyclicTournament] at *
  omega

theorem cyclicTournament_total {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    cyclicTournament a b ∨ cyclicTournament b a := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp only [cyclicTournament]
  omega

theorem cyclicTournament_incoming {n : ℕ} (hn : 3 ≤ n) (b : Fin n) :
    ∃ a, cyclicTournament a b := by
  by_cases hb : b.val = 0
  · refine ⟨⟨n-1, by omega⟩, Or.inl ⟨rfl, hb⟩⟩
  by_cases hlast : b.val = n-1
  · refine ⟨⟨1, by omega⟩, Or.inr ?_⟩
    simp only
    omega
  · refine ⟨⟨0, by omega⟩, Or.inr ?_⟩
    simp only
    omega

theorem exists_incoming_tournament (W : Type*) [Fintype W] (hcard : 3 ≤ Fintype.card W) :
    ∃ R : W → W → Prop,
      (∀ a b, R a b → ¬ R b a) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧ (∀ b, ∃ a, R a b) := by
  let e := Fintype.equivFin W
  refine ⟨fun a b => cyclicTournament (e a) (e b), ?_, ?_, ?_⟩
  · exact fun a b => cyclicTournament_asymm hcard (e a) (e b)
  · exact fun a b h => cyclicTournament_total hcard (e a) (e b) (fun he => h (e.injective he))
  · intro b
    obtain ⟨a, ha⟩ := cyclicTournament_incoming hcard (e b)
    exact ⟨e.symm a, by simpa using ha⟩

end Characterizations

end
end CheckedCharacterizationsSource61

/-! ## Source: Characterizations.TripleCount -/
section CheckedCharacterizationsSource62

/-! # Exact counting of pointed final triples -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def PointedTriple (V : Type*) [Fintype V] [DecidableEq V] :=
  Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}

instance : Fintype (PointedTriple V) := inferInstanceAs
  (Fintype (Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}))

theorem card_pointedTriple : Fintype.card (PointedTriple V) =
    Fintype.card V * (Fintype.card V - 1).choose 2 := by
  change Fintype.card (Σ j : V, {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2}) = _
  rw [Fintype.card_sigma]
  have hj (j : V) : Fintype.card {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2} =
      (Fintype.card V - 1).choose 2 := by
    let e : {A : Finset V // A ⊆ univ.erase j ∧ A.card = 2} ≃
        ↥((univ.erase j).powersetCard 2) := Equiv.subtypeEquivRight (fun A => by simp)
    rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard]
    simp
  simp_rw [hj]
  simp

def CoversPoint (o : VariableOrder V) (P : PointedTriple V) : Prop :=
  ∃ i q : V, i ≠ q ∧ P.2.val = {i,q} ∧ FinalTriple o i q P.1

theorem coversPoint_of_triples {F : Set (VariableOrder V)} (hF : CoversFinalTriples F)
    (P : PointedTriple V) : ∃ o ∈ F, CoversPoint o P := by
  obtain ⟨i, q, hiq, hA⟩ := card_eq_two.mp P.2.property.2
  have hiP : i ∈ P.2.val := by simp [hA]
  have hqP : q ∈ P.2.val := by simp [hA]
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 hiP)).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 hqP)).1
  obtain ⟨o, ho, hf⟩ := hF i q P.1 hiq hij hqj
  exact ⟨o, ho, i, q, hiq, hA, hf⟩

theorem finalTriple_pair_unique {o : VariableOrder V} {i q a b j : V}
    (hiq : i ≠ q) (hab : a ≠ b) (hij : i ≠ j) (hqj : q ≠ j)
    (haj : a ≠ j) (hbj : b ≠ j) (h₁ : FinalTriple o i q j) (h₂ : FinalTriple o a b j) :
    ({i,q} : Finset V) = {a,b} := by
  have hi : i ∈ ({a,b} : Finset V) := by
    by_contra hn
    have hia : i ≠ a := by simpa using (not_or.mp (by simpa using hn)).1
    have hib : i ≠ b := by simpa using (not_or.mp (by simpa using hn)).2
    have hlow := h₂.2.2 i hia hib hij
    by_cases haq : a = q
    · have hbq : b ≠ q := by intro he; exact hab (haq.trans he.symm)
      exact (lt_irrefl _ (hlow.2.trans (h₁.2.2 b hib.symm hbq hbj).1))
    · exact (lt_irrefl _ (hlow.1.trans (h₁.2.2 a hia.symm haq haj).1))
  have hq : q ∈ ({a,b} : Finset V) := by
    by_contra hn
    have hqa : q ≠ a := by simpa using (not_or.mp (by simpa using hn)).1
    have hqb : q ≠ b := by simpa using (not_or.mp (by simpa using hn)).2
    have hlow := h₂.2.2 q hqa hqb hqj
    by_cases hai : a = i
    · have hbi : b ≠ i := by intro he; exact hab (hai.trans he.symm)
      exact (lt_irrefl _ (hlow.2.trans (h₁.2.2 b hbi hqb.symm hbj).2))
    · exact (lt_irrefl _ (hlow.1.trans (h₁.2.2 a hai hqa.symm haj).2))
  exact eq_of_subset_of_card_le (by simp [insert_subset_iff, hi, hq]) (by simp [hiq, hab])

theorem coversPoint_unique {o : VariableOrder V} {P Q : PointedTriple V}
    (hP : CoversPoint o P) (hQ : CoversPoint o Q) : P = Q := by
  obtain ⟨i, q, hiq, hA, h₁⟩ := hP
  obtain ⟨a, b, hab, hB, h₂⟩ := hQ
  have hj : P.1 = Q.1 := by
    apply o.injective
    apply le_antisymm
    · exact le_of_not_gt (h₂.no_after P.1)
    · exact le_of_not_gt (h₁.no_after Q.1)
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have haj : a ≠ Q.1 := (mem_erase.mp (Q.2.property.1 (by simp [hB]))).1
  have hbj : b ≠ Q.1 := (mem_erase.mp (Q.2.property.1 (by simp [hB]))).1
  have hsets : P.2.val = Q.2.val := by
    rw [hA, hB]
    exact finalTriple_pair_unique hiq hab hij hqj (hj ▸ haj) (hj ▸ hbj) h₁ (hj ▸ h₂)
  cases P with | mk p A =>
    cases Q with | mk q B =>
      dsimp at hj hsets
      subst q
      congr
      exact Subtype.ext hsets

/-- Every order realizes exactly one pointed final triple; hence coverage
requires at least `n * choose (n-1) 2` orders. -/
theorem triple_coverage_card_lower_bound (F : Finset (VariableOrder V))
    (hF : CoversFinalTriples (F : Set (VariableOrder V))) :
    Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card := by
  choose f hf hcover using coversPoint_of_triples hF
  let g : PointedTriple V → F := fun P => ⟨f P, hf P⟩
  have hginj : Function.Injective g := by
    intro P Q h
    have he : f P = f Q := congrArg Subtype.val h
    exact coversPoint_unique (he ▸ hcover P) (hcover Q)
  have hh := Fintype.card_le_of_injective g hginj
  simpa [card_pointedTriple] using hh

theorem universalOrderTests_card_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (F : Finset (VariableOrder V))
    (hF : UniversalOrderTests k (F : Set (VariableOrder V))) :
    Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card :=
  triple_coverage_card_lower_bound F ((universalOrderTests_iff_coverage hcard _).mp hF).2

end Characterizations

end
end CheckedCharacterizationsSource62

/-! ## Source: Characterizations.OptimalOrders -/
section CheckedCharacterizationsSource63

/-! # A minimum family of universal variable-order tests -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Except (j : V) := {v : V // v ≠ j}

theorem card_except (j : V) : Fintype.card (Except j) = Fintype.card V - 1 := by
  simpa using Fintype.card_subtype_compl (fun v : V => v = j)

theorem exists_finalTriple_and_pair (i q j : V) (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    ∃ o : VariableOrder V, FinalTriple o i q j ∧ FinalPair o q j := by
  let f : V → ℕ := fun x => if x = j then 3 else if x = q then 2 else if x = i then 1 else 0
  obtain ⟨o, ho⟩ := exists_order_refining f
  have hijO : o i < o j := ho i j (by simp [f, hij, hiq])
  have hqjO : o q < o j := ho q j (by simp [f, hqj])
  refine ⟨o, ⟨hijO, hqjO, ?_⟩, ⟨hqjO, ?_⟩⟩
  · intro t hti htq htj
    exact ⟨ho t i (by simp [f, hti, htq, htj, hiq, hij]),
      ho t q (by simp [f, hti, htq, htj, hqj])⟩
  · intro t htq htj
    apply ho
    simp only [f, if_neg htj, if_neg htq, if_neg hqj, ite_true]
    split_ifs <;> omega

theorem FinalTriple.swap {o : VariableOrder V} {i q j : V} (h : FinalTriple o i q j) :
    FinalTriple o q i j := ⟨h.2.1, h.1, fun x hxq hxi hxj => (h.2.2 x hxi hxq hxj).symm⟩

theorem FinalTriple.of_pair_eq {o : VariableOrder V} {i q a b j : V}
    (h : FinalTriple o a b j) (hiq : i ≠ q) (hab : a ≠ b)
    (he : ({i,q} : Finset V) = {a,b}) : FinalTriple o i q j := by
  have hi : i = a ∨ i = b := by
    have hh : i ∈ ({i,q} : Finset V) := by simp
    rw [he] at hh
    simpa using hh
  have hq : q = a ∨ q = b := by
    have hh : q ∈ ({i,q} : Finset V) := by simp
    rw [he] at hh
    simpa using hh
  rcases hi with rfl | rfl
  · have hqb : q = b := hq.resolve_left hiq.symm
    simpa [hqb] using h
  · have hqa : q = a := hq.resolve_right hiq.symm
    simpa [hqa] using h.swap

structure OrderedPoint (R : ∀ j : V, Except j → Except j → Prop) (P : PointedTriple V) where
  left : Except P.1
  right : Except P.1
  edge : R P.1 left right
  pair_eq : P.2.val = {left.val, right.val}
  order : VariableOrder V
  triple : FinalTriple order left.val right.val P.1
  finalPair : FinalPair order right.val P.1

theorem exists_orderedPoint (R : ∀ j : V, Except j → Except j → Prop)
    (hR : ∀ j a b, a ≠ b → R j a b ∨ R j b a) (P : PointedTriple V) :
    Nonempty (OrderedPoint R P) := by
  obtain ⟨i, q, hiq, hA⟩ := card_eq_two.mp P.2.property.2
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  let I : Except P.1 := ⟨i,hij⟩
  let Q : Except P.1 := ⟨q,hqj⟩
  rcases hR P.1 I Q (fun h => hiq (congrArg Subtype.val h)) with h | h
  · obtain ⟨o, ht, hp⟩ := exists_finalTriple_and_pair i q P.1 hiq hij hqj
    exact ⟨⟨I,Q,h,hA,o,ht,hp⟩⟩
  · obtain ⟨o, ht, hp⟩ := exists_finalTriple_and_pair q i P.1 hiq.symm hqj hij
    exact ⟨⟨Q,I,h,by simpa [pair_comm] using hA,o,ht,hp⟩⟩

/-- Exactly one order for every pointed final triple suffices, with the
orientations chosen so that every final pair is also covered. -/
theorem exists_optimal_order_family (hcard : 4 ≤ Fintype.card V) :
    ∃ F : Finset (VariableOrder V), CoversFinalPairs (F : Set (VariableOrder V)) ∧
      CoversFinalTriples (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V - 1).choose 2 := by
  have hT (j : V) : ∃ R : Except j → Except j → Prop,
      (∀ a b, R a b → ¬ R b a) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧ (∀ b, ∃ a, R a b) :=
    exists_incoming_tournament (Except j) (by rw [card_except]; omega)
  choose R hRasym hRtotal hRincoming using hT
  let chosen (P : PointedTriple V) : OrderedPoint R P := (exists_orderedPoint R hRtotal P).some
  let F : Finset (VariableOrder V) := univ.image (fun P : PointedTriple V => (chosen P).order)
  have hmem (P : PointedTriple V) : (chosen P).order ∈ F := mem_image.mpr ⟨P, mem_univ _, rfl⟩
  have hchosen_ne (P : PointedTriple V) : (chosen P).left ≠ (chosen P).right := by
    intro he
    have hh := (chosen P).edge
    have hh' : R P.1 (chosen P).right (chosen P).left := he ▸ hh
    exact hRasym P.1 _ _ hh hh'
  have htriples : CoversFinalTriples (F : Set (VariableOrder V)) := by
    intro i q j hiq hij hqj
    let P : PointedTriple V := ⟨j, ⟨{i,q}, by simp [insert_subset_iff, hij, hqj], by simp [hiq]⟩⟩
    refine ⟨(chosen P).order, hmem P, ?_⟩
    exact (chosen P).triple.of_pair_eq hiq
      (fun he => hchosen_ne P (Subtype.ext he)) (chosen P).pair_eq
  have hpairs : CoversFinalPairs (F : Set (VariableOrder V)) := by
    intro b j hbj
    let B : Except j := ⟨b,hbj⟩
    obtain ⟨A, hAB⟩ := hRincoming j B
    have hABne : A ≠ B := by
      intro he
      exact hRasym j _ _ hAB (he ▸ hAB)
    have hab : A.val ≠ b := fun he => hABne (Subtype.ext he)
    let P : PointedTriple V := ⟨j, ⟨{A.val,b},
      by simp [insert_subset_iff, A.property, hbj], by simp [hab]⟩⟩
    have hright : (chosen P).right.val = b := by
      have hrmem : (chosen P).right.val ∈ ({A.val,b} : Finset V) := by
        change (chosen P).right.val ∈ P.2.val
        rw [(chosen P).pair_eq]
        simp
      rcases (by simpa using hrmem : (chosen P).right.val = A.val ∨ (chosen P).right.val = b) with hr | hr
      · have hlmem : (chosen P).left.val ∈ ({A.val,b} : Finset V) := by
          change (chosen P).left.val ∈ P.2.val
          rw [(chosen P).pair_eq]
          simp
        have hlb : (chosen P).left.val = b := by
          rcases (by simpa using hlmem : (chosen P).left.val = A.val ∨ (chosen P).left.val = b) with hl | hl
          · exact (hchosen_ne P (Subtype.ext (hl.trans hr.symm))).elim
          · exact hl
        have hlB : (chosen P).left = B := Subtype.ext hlb
        have hrA : (chosen P).right = A := Subtype.ext hr
        have hBA : R j B A := by simpa only [hlB, hrA] using (chosen P).edge
        exact (hRasym j A B hAB hBA).elim
      · exact hr
    exact ⟨(chosen P).order, hmem P, by simpa only [hright] using (chosen P).finalPair⟩
  refine ⟨F, hpairs, htriples, le_antisymm ?_ (triple_coverage_card_lower_bound F htriples)⟩
  have hh := card_image_le (s := (univ : Finset (PointedTriple V))) (f := fun P => (chosen P).order)
  simpa [F, card_pointedTriple] using hh

/-- The minimum number in Theorem 5.3, expressed as an attained bound. -/
theorem exact_universal_test_number {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) :
    (∃ F : Finset (VariableOrder V), UniversalOrderTests k (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V - 1).choose 2) ∧
    (∀ F : Finset (VariableOrder V), UniversalOrderTests k (F : Set (VariableOrder V)) →
      Fintype.card V * (Fintype.card V - 1).choose 2 ≤ F.card) := by
  constructor
  · obtain ⟨F, hp, ht, hc⟩ := exists_optimal_order_family (V := V) hcard
    exact ⟨F, (universalOrderTests_iff_coverage hcard _).mpr ⟨hp, ht⟩, hc⟩
  · exact fun F hF => universalOrderTests_card_lower_bound hcard F hF

end Characterizations

end
end CheckedCharacterizationsSource63

/-! ## Source: Characterizations.SmallCases -/
section CheckedCharacterizationsSource64

/-! # The small-variable and small-degree cases of the sharp test theorem -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem equigenerated_polymatroidal_of_card_le_one {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hcard
  have he : i = j := Subsingleton.elim _ _
  subst j
  omega

theorem positive_coordinate_single_of_degree_one {a : Exponent V} {i : V}
    (ha : a.degree = 1) (hi : 0 < a i) : a = Finsupp.single i 1 := by
  apply (eq_of_le_of_degree_eq (a := Finsupp.single i 1) (b := a) ?_ (by simpa using ha.symm)).symm
  intro x
  by_cases hx : x = i
  · subst x; simp; omega
  · simp [Finsupp.single_apply, hx, Ne.symm hx]

theorem equigenerated_polymatroidal_of_degree_le_one {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hd : d ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  have hpos : 0 < d := by
    have hh := card_positive_except_le_degree (a := a) (S := ∅) (j := i) (by simp) (by omega) (by simp)
    rw [hB a ha] at hh
    simp only [card_empty, zero_add] at hh
    omega
  have hd1 : d = 1 := by omega
  have hai := positive_coordinate_single_of_degree_one ((hB a ha).trans hd1) (by omega : 0 < a i)
  have hbj := positive_coordinate_single_of_degree_one ((hB b hb).trans hd1) (by omega : 0 < b j)
  refine ⟨j,hj,?_⟩
  have he : exchange a i j = b := by simp [exchange, hai, hbj]
  exact he ▸ hb

theorem card_two_exhaust {i j : V} (hcard : Fintype.card V ≤ 2) (hij : i ≠ j) (x : V) :
    x = i ∨ x = j := by
  have he : (univ : Finset V) = {i,j} :=
    (eq_of_subset_of_card_le (subset_univ _) (by simp [hij]; omega)).symm
  have hx := mem_univ x
  rw [he] at hx
  simpa using hx

theorem exchange_of_boxConnected_card_two {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 2) (hconn : BoxConnected B) : ExchangeAxiom B := by
  intro a ha b hb i hi
  obtain ⟨j,hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  have hij : i ≠ j := by intro he; subst j; omega
  have hpath := hconn (a ⊔ b) a ha le_sup_left b hb le_sup_right
  rcases hpath.cases_head with he | ⟨c,hstep,_⟩
  · have hh := congrArg (fun x : Exponent V => x i) he
    omega
  obtain ⟨_,hc,_,hcbox,p,q,hpq,hp,hec⟩ := hstep
  have hpi : p = i := by
    rcases card_two_exhaust hcard hij p with hpI | hpJ
    · exact hpI
    · have hqi : q = i := (card_two_exhaust hcard hij q).resolve_right (fun hqJ => hpq (hpJ.trans hqJ.symm))
      have hcI := hcbox i
      rw [hec] at hcI
      simp only [exchange_apply, Finsupp.sup_apply] at hcI
      rw [hpJ, hqi] at hcI
      simp only [if_neg hij, ite_true, Nat.sub_zero] at hcI
      omega
  have hqj : q = j := (card_two_exhaust hcard hij q).resolve_left (fun hqI => hpq (hpi.trans hqI.symm))
  exact ⟨j,hj,by simpa [hec,hpi,hqj] using hc⟩

theorem one_order_suffices_card_two {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 2)
    (o : VariableOrder V) (hL : HasLinearQuotients k B (variableRevlex o)) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, exchange_of_boxConnected_card_two hB hcard ?_⟩
  exact boxConnected_of_linearQuotients hB (variableRevlex_irrefl o)
    (fun {_ _ _} => variableRevlex_trans o) (variableRevlex_total o) hL

theorem nonempty_order_family_card_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V ≤ 2) (F : Set (VariableOrder V)) (hne : F.Nonempty) :
    UniversalOrderTests k F := by
  intro B d hB hL
  obtain ⟨o,ho⟩ := hne
  exact one_order_suffices_card_two hB hcard o (hL o ho)

def purePairFamily (d : ℕ) (i j : V) : Family V := {Finsupp.single i d, Finsupp.single j d}

theorem purePair_equigenerated (d : ℕ) (i j : V) : Equigenerated (purePairFamily d i j) d := by
  intro a ha
  rcases (by simpa [purePairFamily] using ha : a = Finsupp.single i d ∨ a = Finsupp.single j d) with rfl | rfl <;> simp

theorem purePair_not_polymatroidal {d : ℕ} (hd : 2 ≤ d) {i j : V} (hij : i ≠ j) :
    ¬ IsPolymatroidal (purePairFamily d i j) := by
  intro h
  have ha : Finsupp.single i d ∈ purePairFamily d i j := by simp [purePairFamily]
  have hb : Finsupp.single j d ∈ purePairFamily d i j := by simp [purePairFamily]
  obtain ⟨q,hq,he⟩ := h.2 _ ha _ hb i (by simp [Finsupp.single_apply, hij, hij.symm]; omega)
  have hqj : q = j := by
    by_contra hn
    simp [Finsupp.single_apply, Ne.symm hn] at hq
  subst q
  rcases (by simpa [purePairFamily] using he :
    exchange (Finsupp.single i d) i j = Finsupp.single i d ∨
    exchange (Finsupp.single i d) i j = Finsupp.single j d) with he | he
  · have hh := congrArg (fun a : Exponent V => a j) he
    simp [exchange_apply, Finsupp.single_apply, hij, hij.symm] at hh
  · have hh := congrArg (fun a : Exponent V => a i) he
    simp [exchange_apply, Finsupp.single_apply, hij, hij.symm] at hh
    omega

end Characterizations

end
end CheckedCharacterizationsSource64

/-! ## Source: Characterizations.SupportedFamilies -/
section CheckedCharacterizationsSource65

/-! # Exact support identities for coordinate minors -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem project_eq_self_iff_support_subset (a : Exponent V) (U : Finset V) :
    project U a = a ↔ a.support ⊆ U := by
  constructor
  · intro h i hi
    by_contra hn
    have he := congrArg (fun b : Exponent V => b i) h
    simp only [project_apply, if_neg hn] at he
    exact (Finsupp.mem_support_iff.mp hi) he.symm
  · intro h
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have haz : a i = 0 := Finsupp.notMem_support_iff.mp (fun hc => hi (h hc))
      simp [hi,haz]

theorem supported_of_subsetSum_compl_zero {a : Exponent V} {U : Finset V}
    (h : subsetSum a Uᶜ = 0) : project U a = a := by
  apply (project_eq_self_iff_support_subset a U).mpr
  intro i hi
  by_contra hiU
  have hle : a i ≤ subsetSum a Uᶜ := Finset.single_le_sum
    (fun j _ => Nat.zero_le (a j)) (Finset.mem_compl.mpr hiU)
  exact (Finsupp.mem_support_iff.mp hi) (by omega)

theorem subsetSum_supported_inter {a : Exponent V} {U : Finset V}
    (h : project U a = a) (W : Finset V) : subsetSum a W = subsetSum a (W ∩ U) := by
  calc
    subsetSum a W = subsetSum (project U a) W := by rw [h]
    _ = _ := subsetSum_project_inter U W a

theorem lowerRank_supported_inter {B : Family V} (hB : B.Nonempty) (U : Finset V)
    (hs : ∀ a ∈ B, project U a = a) (W : Finset V) :
    lowerRank B W = lowerRank B (W ∩ U) := by
  apply le_antisymm
  · obtain ⟨a,ha,he⟩ := lowerRank_attained hB (W ∩ U)
    exact (lowerRank_le ha W).trans_eq ((subsetSum_supported_inter (hs a ha) W).trans he)
  · obtain ⟨a,ha,he⟩ := lowerRank_attained hB W
    exact (lowerRank_le ha (W ∩ U)).trans_eq ((subsetSum_supported_inter (hs a ha) W).symm.trans he)

theorem lowerRank_on_support {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a) :
    lowerRank B U = d := by
  obtain ⟨a,ha,he⟩ := lowerRank_attained hB U
  calc
    lowerRank B U = subsetSum a U := he.symm
    _ = a.degree := by rw [← degree_project, hs a ha]
    _ = d := hd a ha

theorem lowerBase_supported {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a)
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank B) d) : project U a = a := by
  obtain ⟨had,hlo⟩ := (mem_lowerBaseFamily _ _ _).mp ha
  apply eq_of_le_of_degree_eq (project_le U a)
  apply le_antisymm (degree_mono (project_le U a))
  rw [degree_project, had, ← lowerRank_on_support hB hd U hs]
  exact hlo U

theorem supported_equigenerated_polymatroidal_card_le_one {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a)
    (hc : U.card ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hd⟩,?_⟩
  intro a ha b hb i hi
  obtain ⟨j,hj⟩ := exists_surplus ((hd a ha).trans (hd b hb).symm) hi
  have hiU : i ∈ U := (project_eq_self_iff_support_subset a U).mp (hs a ha)
    (Finsupp.mem_support_iff.mpr (by omega))
  have hjU : j ∈ U := (project_eq_self_iff_support_subset b U).mp (hs b hb)
    (Finsupp.mem_support_iff.mpr (by omega))
  have hij : i ≠ j := by intro he; subst j; omega
  have hp : ({i,j} : Finset V) ⊆ U :=
    Finset.insert_subset_iff.mpr ⟨hiU,Finset.singleton_subset_iff.mpr hjU⟩
  have hcard := Finset.card_le_card hp
  simp only [Finset.card_pair hij] at hcard
  omega

end Characterizations

end
end CheckedCharacterizationsSource65

/-! ## Source: Characterizations.MinimalMixedMinor -/
section CheckedCharacterizationsSource66

/-! # A smallest non-polymatroidal mixed coordinate minor -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restriction_univ (B : Family V) : restriction B Finset.univ = B := by
  ext a
  simp

theorem mixedMinor_univ {B : Family V} (hB : Antichain B) :
    mixedMinor B Finset.univ Finset.univ = B := by
  rw [mixedMinor,restriction_univ,localize_univ_of_antichain hB]

theorem exists_minimal_bad_mixedMinor {B : Family V} (hB : B.Nonempty) (hanti : Antichain B)
    (hn : ¬ IsPolymatroidal B) :
    ∃ A U : Finset V, U ⊆ A ∧ (mixedMinor B A U).Nonempty ∧
      ¬ IsPolymatroidal (mixedMinor B A U) ∧
      (∀ W : Finset V, W ⊂ U → IsPolymatroidal (localize (mixedMinor B A U) W)) ∧
      (∀ W : Finset V, W ⊂ U → (restriction (mixedMinor B A U) W).Nonempty →
        IsPolymatroidal (restriction (mixedMinor B A U) W)) := by
  let bad : Finset (Finset V × Finset V) := Finset.univ.filter (fun p =>
    p.2 ⊆ p.1 ∧ (mixedMinor B p.1 p.2).Nonempty ∧ ¬IsPolymatroidal (mixedMinor B p.1 p.2))
  have hb : bad.Nonempty := by
    refine ⟨(Finset.univ,Finset.univ),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,?_⟩⟩
    · exact le_rfl
    · simpa only [mixedMinor_univ hanti] using hB
    · simpa only [mixedMinor_univ hanti] using hn
  obtain ⟨⟨A,U⟩,hp,hmin⟩ := bad.exists_minimalFor (fun p => p.2.card) hb
  obtain ⟨hUA,hL,hbad⟩ := (Finset.mem_filter.mp hp).2
  refine ⟨A,U,hUA,hL,hbad,?_,?_⟩
  · intro W hWU
    by_contra hnW
    have he : localize (mixedMinor B A U) W = mixedMinor B A W := by
      rw [localize_mixedMinor,Finset.inter_eq_right.mpr hWU.subset]
    have hnew : (A,W) ∈ bad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWU.subset.trans hUA,?_,?_⟩
      · rw [← he]
        exact localize_nonempty hL W
      · rwa [← he]
    have hc := hmin hnew (Finset.card_le_card hWU.subset)
    change U.card ≤ W.card at hc
    have hc' := Finset.card_lt_card hWU
    omega
  · intro W hWU hR
    by_contra hnW
    have hWA : W ⊆ A ∩ (W ∪ Uᶜ) := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨hUA (hWU.subset hi),Finset.mem_union_left _ hi⟩
    have he := restriction_mixedMinor B hUA hWU.subset
    have hnew : (A ∩ (W ∪ Uᶜ),W) ∈ bad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWA,?_,?_⟩
      · rwa [← he]
      · rwa [← he]
    have hc := hmin hnew (Finset.card_le_card hWU.subset)
    change U.card ≤ W.card at hc
    have hc' := Finset.card_lt_card hWU
    omega

/-- A missing integral generator in a restriction-minimal obstruction uses
every retained variable. This is the degree-versus-dimension step in 4.2. -/
theorem missing_base_full_support {L : Family V} (hL : L.Nonempty)
    (hl : LocallyEquigenerated L) {e : ℕ} (he : Equigenerated L e) (U : Finset V)
    (hs : ∀ b ∈ L, project U b = b)
    (hrest : ∀ W : Finset V, W ⊂ U → (restriction L W).Nonempty →
      IsPolymatroidal (restriction L W))
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank L) e) (hout : ¬Contains L a) :
    a.support = U := by
  have haU := lowerBase_supported hL he U hs ha
  have hsub := (project_eq_self_iff_support_subset a U).mp haU
  by_contra hne
  have hproper : a.support ⊂ U := hsub.ssubset_of_ne hne
  have haA : project a.support a = a := (project_eq_self_iff_support_subset _ _).mpr le_rfl
  have hlo := ((mem_lowerBaseFamily _ _ _).mp ha).2
  have hsumzero : subsetSum a a.supportᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact Finsupp.notMem_support_iff.mp (Finset.mem_compl.mp hi)
  have hrzero : lowerRank L a.supportᶜ = 0 := Nat.eq_zero_of_le_zero (hsumzero ▸ hlo a.supportᶜ)
  obtain ⟨b,hb,hmin⟩ := lowerRank_attained hL a.supportᶜ
  have hbA : project a.support b = b := supported_of_subsetSum_compl_zero (hmin.trans hrzero)
  have hK : (restriction L a.support).Nonempty := ⟨b,mem_restriction.mpr ⟨hb,hbA⟩⟩
  have hpK := hrest a.support hproper hK
  have hdegK := restriction_equigenerated he a.support
  have hfeas : LowerFeasible (lowerRank (restriction L a.support)) a := by
    intro W
    rw [lowerRank_supported_inter hK a.support (fun c hc => (mem_restriction.mp hc).2),
      restriction_lowerRank hl hK Finset.inter_subset_right]
    have hh := hlo ((W ∩ a.support) ∪ a.supportᶜ)
    have hsum : subsetSum a ((W ∩ a.support) ∪ a.supportᶜ) = subsetSum a W := by
      rw [subsetSum_supported_inter haA]
      have hset : ((W ∩ a.support) ∪ a.supportᶜ) ∩ a.support = W ∩ a.support := by
        ext i
        simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_compl]
        tauto
      rw [hset,← subsetSum_supported_inter haA W]
    rwa [hsum] at hh
  have hcontains := (contains_iff_canonical_lower _ hK e hdegK hpK a).mpr hfeas
  obtain ⟨c,hc,hca⟩ := hcontains
  exact hout ⟨c,restriction_subset L a.support hc,hca⟩

theorem degree_ge_support_card (a : Exponent V) : a.support.card ≤ a.degree := by
  calc
    a.support.card = ∑ i ∈ a.support, 1 := by simp
    _ ≤ subsetSum a a.support := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ ≤ a.degree := by
      simpa only [degree_project] using degree_mono (project_le a.support a)

end Characterizations

end
end CheckedCharacterizationsSource66

/-! ## Source: Characterizations.Strands.SocleTor -/
section CheckedCharacterizationsSource67

/-! # A monomial socle element produces the actual top derived-Tor class -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

lemma socle_faces_eq_boundary (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent Finset.univ) = simplexBoundary (Finset.univ : Finset V) := by
  funext s
  apply propext
  constructor
  · rintro ⟨hs, hmem⟩
    refine ⟨Finset.subset_univ s, ?_⟩
    intro hsub
    have he : s = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ s) hsub
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent Finset.univ :=
      (faceExponent_mono (Finset.subset_univ s)).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply,
      Finset.mem_univ, ite_true, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs]
    · by_cases hxs : x ∈ s <;> simp [hxj, Ne.symm hxj, hxs] <;> omega

lemma socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    bettiNumber (k := k) B (a + faceExponent Finset.univ) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ Finset.univ i (by simpa using hcard)
    (socle_faces_eq_boundary B a hout hmul)

lemma socle_gradedBettiNonzero [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    GradedBettiNonzero (k := k) B (a + faceExponent Finset.univ) i := by
  rw [← bettiNumber_pos_iff, socle_bettiNumber_eq_one B a hout hmul i hcard]
  exact Nat.zero_lt_one

lemma relative_socle_faces_eq_boundary (B : Family V) (a : Exponent V) (U : Finset V)
    (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent U) = simplexBoundary U := by
  have hsupp' : (a + faceExponent U).support = U := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, faceExponent_apply]
    by_cases hj : j ∈ U
    · simp [hj]
    · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hsupp h))
      simp [hj, hz]
  funext s
  apply propext
  constructor
  · rintro ⟨hdiv, hmem⟩
    have hs : s ⊆ U := by
      simpa only [hsupp'] using (faceExponent_le_iff_subset_support s _).mp hdiv
    refine ⟨hs, ?_⟩
    intro hUs
    have he : s = U := Finset.Subset.antisymm hs hUs
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent U :=
      (faceExponent_mono hs.subset).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j hj
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs, hj]
    · by_cases hxs : x ∈ s
      · have hxU := hs.subset hxs
        simp [hxj, Ne.symm hxj, hxs, hxU]
      · simp [hxj, Ne.symm hxj, hxs]

lemma relative_socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (U : Finset V) (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) (i : ℕ)
    (hcard : U.card = i+1) : bettiNumber (k := k) B (a+faceExponent U) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ U i hcard
    (relative_socle_faces_eq_boundary B a U hsupp hout hmul)

end Characterizations.Strands

end
end CheckedCharacterizationsSource67

/-! ## Source: Characterizations.MinimalMixedObstruction -/
section CheckedCharacterizationsSource68

/-! # Every failure has a genuine nonlinear Tor class in the degree-bounded range -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem betti_restriction_sameambient (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : project U a = a) (i : ℕ) :
    bettiNumber (k := k) (restriction B U) a i = bettiNumber (k := k) B a i := by
  have hfaces : koszulFaces (restriction B U) a = koszulFaces B a := by
    funext s
    apply propext
    change (faceExponent s ≤ a ∧ Contains (restriction B U) (a-faceExponent s)) ↔ _
    rw [contains_restriction]
    have hs := supported_of_le ha (tsub_le_self : a-faceExponent s ≤ a)
    rw [hs]
    rfl
  rw [Strands.bettiNumber_eq_face_homology_finrank,Strands.bettiNumber_eq_face_homology_finrank,
    Strands.chainComplex_congr (koszulFaces_downward _ _) (koszulFaces_downward _ _) hfaces]

theorem relative_socle_above_missing_base {L : Family V} (hL : L.Nonempty)
    (U : Finset V) (hs : ∀ c ∈ L, project U c = c)
    (hloc : ∀ W : Finset V, W ⊂ U → IsPolymatroidal (localize L W))
    {a : Exponent V} (ha : LowerFeasible (lowerRank L) a)
    (has : project U a = a) (hout : ¬Contains L a) :
    ∃ b, a ≤ b ∧ project U b = b ∧ ¬Contains L b ∧
      ∀ i ∈ U, Contains L (b+Finsupp.single i 1) := by
  apply exists_socle_above L U a has hout
  intro i hi
  have hgood := lowerFeasible_project_mem hL ha (U.erase i)
    (hloc _ (Finset.erase_ssubset hi))
  obtain ⟨c,hc,hca⟩ := (contains_localize L (U.erase i) _).mp hgood
  refine ⟨c i,c,hc,?_⟩
  intro j
  by_cases hji : j = i
  · subst j; simp
  · by_cases hjU : j ∈ U
    · have hjE : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hji,hjU⟩
      have hh := hca j
      simpa only [project_apply,if_pos hjE,Finsupp.add_apply,Finsupp.single_apply,
        if_neg (Ne.symm hji),add_zero] using hh
    · have hz := congrArg (fun x : Exponent V => x j) (hs c hc)
      simp only [project_apply,if_neg hjU] at hz
      rw [← hz]
      exact Nat.zero_le _

/-- The obstruction underlying Theorems4.2 and4.9. All Betti numbers are the
actual numerical dimensions of the derived Tor components in the ambient ring;
the exhibited degree is supported on the retained localization coordinates. -/
theorem exists_low_nonlinear_localization {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) (hn : ¬IsPolymatroidal B) :
    ∃ (U : Finset V) (e i : ℕ) (a : Exponent V),
      Equigenerated (localize B U) e ∧ lowerRank B U = e ∧ 2 ≤ U.card ∧
      1 ≤ i ∧ i ≤ e-1 ∧ i ≤ U.card-1 ∧ a.support ⊆ U ∧
      e+i < a.degree ∧ bettiNumber (k := k) (localize B U) a i ≠ 0 := by
  obtain ⟨A,U,hUA,hL,hnL,hloc,hrest⟩ := exists_minimal_bad_mixedMinor hB hanti hn
  let L := mixedMinor B A U
  have hantiL : Antichain L := localize_antichain _ _
  have hlL : LocallyEquigenerated L := mixedMinor_locallyEquigenerated hl A U
  obtain ⟨e,he⟩ := hlL Finset.univ
  rw [localize_univ_of_antichain hantiL] at he
  have hs : ∀ c ∈ L, project U c = c := fun c hc => localize_supported hc
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hnL (supported_equigenerated_polymatroidal_card_le_one he U hs (by omega))
  have hnot : ¬ lowerBaseFamily (lowerRank L) e ⊆ L := by
    intro h
    have hEq : L = lowerBaseFamily (lowerRank L) e :=
      Finset.Subset.antisymm (subset_lowerBaseFamily he) h
    apply hnL
    change IsPolymatroidal L
    rw [hEq]
    exact canonicalLowerBases_polymatroidal hL hlL he
  obtain ⟨a,haJ,haL⟩ := Finset.not_subset.mp hnot
  obtain ⟨hade,hafeas⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  have hout : ¬Contains L a := fun h => haL ((he.mem_iff_contains hade).mpr h)
  have hsupp : a.support = U := missing_base_full_support hL hlL he U hs hrest haJ hout
  have hUe : U.card ≤ e := by simpa only [hsupp,hade] using degree_ge_support_card a
  have has : project U a = a := lowerBase_supported hL he U hs haJ
  obtain ⟨b,hab,hbs,hbout,hmul⟩ := relative_socle_above_missing_base hL U hs hloc hafeas has hout
  let α := b+faceExponent U
  have hα : project U α = α := by
    dsimp [α]
    rw [project_add,hbs]
    congr 1
    ext j
    simp only [project_apply,faceExponent_apply]
    split_ifs <;> rfl
  have hβ : bettiNumber (k := k) L α (U.card-1) = 1 :=
    Strands.relative_socle_bettiNumber_eq_one L b U
      ((project_eq_self_iff_support_subset b U).mp hbs) hbout hmul _ (by omega)
  have hαdegree : e+(U.card-1) < α.degree := by
    have hdeg := degree_mono hab
    rw [hade] at hdeg
    dsimp [α]
    rw [map_add,Strands.degree_faceExponent]
    omega
  let T := U ∪ Aᶜ
  have hUT : U ⊆ T := Finset.subset_union_left
  have hTdegree : lowerRank B T = e := by
    have h := mixedMinor_lowerRank hl hL hUA (Finset.Subset.refl U)
    rw [lowerRank_on_support hL he U hs] at h
    exact h.symm
  have hTgen : Equigenerated (localize B T) e := by
    intro c hc
    exact (localize_degree hB hl hc).trans hTdegree
  have hLeq : L = restriction (localize B T) U := localize_restriction B hUA
  have hβT : bettiNumber (k := k) (localize B T) α (U.card-1) = 1 := by
    rw [hLeq,betti_restriction_sameambient _ U α hα] at hβ
    exact hβ
  refine ⟨T,e,U.card-1,α,hTgen,hTdegree,?_,by omega,by omega,?_,?_,hαdegree,?_⟩
  · exact hcard.trans (Finset.card_le_card hUT)
  · have h := Finset.card_le_card hUT
    omega
  · exact ((project_eq_self_iff_support_subset α U).mp hα).trans hUT
  · rw [hβT]
    exact one_ne_zero

end Characterizations

end
end CheckedCharacterizationsSource68

/-! ## Source: Characterizations.Triangular -/
section CheckedCharacterizationsSource69

/-! # The degree-bounded and triangular localization characterizations

Theorems 4.2, 4.5 (sufficiency), and 4.9, with the exact polynomial rings on
the retained variables and genuine derived-Tor Betti components.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def RetainedLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent U, ∀ i : ℕ, i ≤ t →
    a.degree ≠ e+i → bettiNumber (k := k) (localFamily B U) a i = 0

theorem localLinearThrough_iff_retained (B : Family V) (U : Finset V) (e t : ℕ) :
    LocalLinearThrough (k := k) B U e t ↔ RetainedLinearThrough (k := k) B U e t := by
  constructor
  · intro h a i hi hoff
    have hs := Strands.extend_support_subset U a
    have hh := h (extendExponent U a) hs i hi (by simpa only [extendExponent_degree] using hoff)
    rw [betti_localize_supported B U _ hs i,restrict_extend] at hh
    exact hh
  · intro h a ha i hi hoff
    rw [betti_localize_supported B U a ha i]
    exact h (restrictExponent U a) i hi (by rwa [restrictExponent_degree_supported U a ha])

/-- The literal local-ring statement of the triangular tests. -/
def RetainedTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

theorem triangularTests_iff_retained (B : Family V) (d : ℕ) :
    TriangularTests (k := k) B d ↔ RetainedTriangularTests (k := k) B d := by
  simp only [TriangularTests,RetainedTriangularTests,
    localFamily_equigenerated_iff,localLinearThrough_iff_retained]

/-- Theorem 4.9 in the ambient supported-degree description. -/
theorem polymatroidal_iff_triangular_ambient {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TriangularTests (k := k) B d := by
  refine ⟨fun hp => triangularTests_of_polymatroidal hp d,?_⟩
  intro ht
  by_contra hn
  have hl := locallyEquigenerated_of_triangularTests hB hd ht
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact triangularTests_exclude_low_nonlinear hB hd ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.9, with every Betti component computed over `k[U]`. -/
theorem polymatroidal_iff_triangular {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ RetainedTriangularTests (k := k) B d :=
  (polymatroidal_iff_triangular_ambient hB hd hd2).trans (triangularTests_iff_retained B d)

/-- Theorem 4.5 with prior local equigeneration: codimension at most d−2
suffices, and the conclusion is the full exchange axiom. -/
theorem polymatroidal_iff_pure_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact linearBand_excludes_low_nonlinear hB hd hl ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.5 without prior local equigeneration: codimension at most d−1
forces both purity and the complete polymatroid exchange property. -/
theorem polymatroidal_iff_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  have hl := locallyEquigenerated_of_linearBand hB hd ht
  exact (polymatroidal_iff_pure_localization_band hB hd hd2 hl).mpr
    (fun U hc hk => ht U hc (by omega))

def DegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (e-1))

def DegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

theorem degreeBoundedTests_of_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) : DegreeBoundedTests (k := k) B := by
  intro U
  have he := localFamily_equigenerated hp U
  refine ⟨lowerRank B U,he,?_⟩
  intro _
  apply (localLinearThrough_iff_retained B U _ _).mp
  exact localLinearThrough_of_linearResolution hB U
    (localFamily_equigenerated_iff.mp he) (polymatroidal_local_linearResolutions hp U) _

theorem degreeDimensionBoundedTests_of_degreeBoundedTests {B : Family V}
    (ht : DegreeBoundedTests (k := k) B) : DegreeDimensionBoundedTests (k := k) B := by
  intro U
  obtain ⟨e,he,hlinear⟩ := ht U
  exact ⟨e,he,fun hp a i hi hoff => hlinear hp a i (hi.trans (min_le_left _ _)) hoff⟩

/-- Theorem 4.2, including the smaller equivalent depth
`min {e_U−1, |U|−1}`. No original equigeneration hypothesis is added. -/
theorem polymatroidal_iff_degree_dimension_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeDimensionBoundedTests (k := k) B := by
  refine ⟨fun hp => degreeDimensionBoundedTests_of_degreeBoundedTests
    (degreeBoundedTests_of_polymatroidal hB hp),?_⟩
  intro ht
  have hl : LocallyEquigenerated B := by
    intro U
    obtain ⟨e,he,_⟩ := ht U
    exact ⟨e,localFamily_equigenerated_iff.mp he⟩
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hanti hl hn
  obtain ⟨f,hf,hlinear⟩ := ht U
  have hf' := localFamily_equigenerated_iff.mp hf
  obtain ⟨b,hb⟩ := localize_nonempty hB U
  have hef : e = f := (he b hb).symm.trans (hf' b hb)
  subst f
  have hvan := (localLinearThrough_iff_retained B U e _).mpr (hlinear (by omega))
  exact hbetti (hvan a ha i (le_min hie hic) (by omega))

/-- Theorem 4.2 with exactly the displayed degree cutoff `e_U−1`. -/
theorem polymatroidal_iff_degree_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeBoundedTests (k := k) B :=
  ⟨degreeBoundedTests_of_polymatroidal hB,fun ht =>
    (polymatroidal_iff_degree_dimension_tests hB hanti).mpr
      (degreeDimensionBoundedTests_of_degreeBoundedTests ht)⟩

end Characterizations

end
end CheckedCharacterizationsSource69

/-! ## Source: Characterizations.Isolators.Optimality -/
section CheckedCharacterizationsSource70

/-! # Exact optimal localization families and the smallest isolator degrees -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Full fixed-family equivalence in Theorem 4.5, without prior local purity. -/
theorem localizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-1) ⊆ Γ := by
  constructor
  · exact localizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg htest
    apply (polymatroidal_iff_localization_band (k := k) hB hdeg hd).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- Full fixed-family equivalence in Theorem 4.5 with prior local purity. -/
theorem pureLocalizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-2) ⊆ Γ := by
  constructor
  · exact pureLocalizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg hl htest
    apply (polymatroidal_iff_pure_localization_band (k := k) hB hdeg hd hl).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- The exact ordinary-band minimum is attained and bounds every valid testing family. -/
theorem localizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-1), (localizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-1) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-1) hn]
    exact Finset.card_le_card ((localizationTestSufficient_iff Γ d hd).mp hΓ)

/-- The exact narrower-band minimum under prior local equigeneration. -/
theorem pureLocalizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-2), (pureLocalizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-2) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-2) hn]
    exact Finset.card_le_card ((pureLocalizationTestSufficient_iff Γ d hd).mp hΓ)

/-- Any equigenerated ideal with a unique bad localization has degree at least
codimension plus one, and never degree zero or one. -/
theorem unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    2 ≤ d ∧ Uᶜ.card+1 ≤ d := by
  have hd2 : 2 ≤ d := by
    by_contra hn
    exact hbad (polymatroidal_local_linearResolutions
      (equigenerated_polymatroidal_of_degree_le_one hd (by omega)) U)
  refine ⟨hd2, ?_⟩
  by_contra hcost
  have hp : IsPolymatroidal B := (polymatroidal_iff_localization_band (k := k) hB hd hd2).mpr (by
    intro R hm hk
    apply hgood R
    intro he
    subst R
    have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
    omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

/-- Proposition 4.7's sharper optimality when all localizations are equigenerated. -/
theorem pure_unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    Uᶜ.card+2 ≤ d := by
  have hd2 := (unique_bad_degree_lower_bound hB hd U hbad hgood).1
  by_contra hcost
  have hp : IsPolymatroidal B :=
    (polymatroidal_iff_pure_localization_band (k := k) hB hd hd2 hl).mpr (by
      intro R hm hk
      apply hgood R
      intro he
      subst R
      have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
      omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

end Characterizations.Isolators

end
end CheckedCharacterizationsSource70

/-! ## Source: Characterizations.MonomialNormalForm -/
section CheckedCharacterizationsSource71

/-! # Every monomial ideal has its unique finite minimal monomial presentation

The input notion allows an arbitrary, possibly infinite, set of exponents. The
finite-antichain presentation is proved using Hilbert's basis theorem, not included
as an assumption in the notion of monomial ideal.
-/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations
open Classical Finset CommAlg CommAlg.Polymatroid MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The ordinary meaning of a monomial ideal, permitting an arbitrary exponent set. -/
def IsMonomialIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ A : Set (Exponent V), I = Ideal.span ((fun a => monomial a (1 : k)) '' A)

lemma monomialIdeal_isMonomial (B : Family V) : IsMonomialIdeal (monomialIdeal k B) :=
  ⟨(B : Set (Exponent V)), rfl⟩

/-- Arbitrary monomial spans have finite monomial generators. -/
lemma IsMonomialIdeal.exists_finite {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, I = monomialIdeal k B := by
  obtain ⟨A, rfl⟩ := hI
  let f : Exponent V → MvPolynomial V k := fun a => monomial a (1 : k)
  have hfg : (Ideal.span (f '' A)).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨Q, hQA, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (f '' A)).mp hfg
  have hq : ∀ q : Q, ∃ a ∈ A, f a = q.val := fun q => hQA q.property
  let b : Q → Exponent V := fun q => (hq q).choose
  have hbA : ∀ q, b q ∈ A := fun q => (hq q).choose_spec.1
  have hbeq : ∀ q, f (b q) = q.val := fun q => (hq q).choose_spec.2
  let B : Family V := Finset.univ.image b
  refine ⟨B, ?_⟩
  have hset : f '' (B : Set (Exponent V)) = (Q : Set (MvPolynomial V k)) := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
      rw [hbeq]
      exact q.property
    · intro hp
      refine ⟨b ⟨p, hp⟩, Finset.mem_image.mpr ⟨⟨p, hp⟩, mem_univ _, rfl⟩, hbeq _⟩
  change Ideal.span (f '' A) = Ideal.span (f '' (B : Set (Exponent V)))
  rw [hset]
  exact hspan

/-- Every monomial ideal has a finite antichain of actual monomial generators. -/
lemma IsMonomialIdeal.exists_antichain {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, Antichain B ∧ I = monomialIdeal k B := by
  obtain ⟨B, hB⟩ := hI.exists_finite
  exact ⟨minimalFamily B, minimalFamily_antichain B,
    hB.trans (monomialIdeal_minimalFamily k B).symm⟩

lemma antichain_generators_unique {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (hI : monomialIdeal k B = monomialIdeal k C) : B = C := by
  apply family_eq_of_contains_iff hB hC
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), hI]

/-- The unique finite family of minimal monomial exponents of a literal ideal. -/
def monomialGenerators (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) : Family V :=
  hI.exists_antichain.choose

lemma monomialGenerators_antichain (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    Antichain (monomialGenerators I hI) := hI.exists_antichain.choose_spec.1

lemma monomialGenerators_ideal (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    monomialIdeal k (monomialGenerators I hI) = I := hI.exists_antichain.choose_spec.2.symm

lemma monomialGenerators_eq {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {B : Family V} (hB : Antichain B) (he : I = monomialIdeal k B) :
    monomialGenerators I hI = B :=
  antichain_generators_unique (monomialGenerators_antichain I hI) hB
    ((monomialGenerators_ideal I hI).trans he)

lemma monomialGenerators_nonempty {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hne : I ≠ ⊥) : (monomialGenerators I hI).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  apply hne
  rw [← monomialGenerators_ideal I hI, he]
  simp [monomialIdeal]

/-- The chosen presentation is exactly the divisibility-minimal monomials in I. -/
lemma mem_monomialGenerators_iff (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I)
    (a : Exponent V) :
    a ∈ monomialGenerators I hI ↔ monomial a (1 : k) ∈ I ∧
      ∀ b : Exponent V, b ≤ a → monomial b (1 : k) ∈ I → b = a := by
  have hanti := monomialGenerators_antichain I hI
  have hm : ∀ b : Exponent V, monomial b (1 : k) ∈ I ↔ Contains (monomialGenerators I hI) b := by
    intro b
    simpa only [monomialGenerators_ideal I hI] using
      (monomial_mem_iff (k := k) (monomialGenerators I hI) b)
  simp only [hm]
  constructor
  · intro ha
    refine ⟨⟨a, ha, le_rfl⟩, ?_⟩
    rintro b hba ⟨c, hc, hcb⟩
    have hca := hanti c hc a ha (hcb.trans hba)
    exact le_antisymm hba (hca ▸ hcb)
  · rintro ⟨⟨b, hb, hba⟩, hmin⟩
    have he := hmin b hba ⟨b, hb, le_rfl⟩
    exact he ▸ hb

lemma isPolymatroidalIdeal_iff_generators {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsPolymatroidal (monomialGenerators I hI) := by
  constructor
  · rintro ⟨B, hp, he⟩
    rw [monomialGenerators_eq hI hp.1.choose_spec.antichain he]
    exact hp
  · intro hp
    exact ⟨monomialGenerators I hI, hp, (monomialGenerators_ideal I hI).symm⟩

/-- Theorem 1.1(A), now quantified over an arbitrary literal monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_local_linear {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔
      ∀ U : Finset V, HasLinearResolution (monomialLocalization k I U) := by
  by_cases hzero : I = ⊥
  · subst I
    constructor
    · intro _ U
      rw [monomialLocalization, Ideal.map_bot]
      exact ⟨0, ⟨zeroLinearResolution 0⟩⟩
    · intro _
      exact isPolymatroidalIdeal_bot
  · rw [isPolymatroidalIdeal_iff_generators hI,
      polymatroidal_iff_local_linearResolutions (k := k) (monomialGenerators_nonempty hI hzero)
        (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI]

/-- Theorem 1.1(B) / Corollary 3.10 on the actual minimal generators of an
arbitrary literal monomial ideal, without an equigeneration assumption. -/
theorem monomialIdeal_polymatroidal_iff_universal_quotients {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ ∀ o : VariableOrder V,
      HasLinearQuotients k (monomialGenerators I hI) (variableRevlex o) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  exact polymatroidal_iff_universal_pure_revlex (monomialGenerators_antichain I hI)

/-- Theorem 2.11 / Corollary 2.12's integrality form for literal monomial ideals. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d, Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  rw [isPolymatroidalIdeal_iff_generators hI,
    polymatroidal_iff_integrallyClosed_localEquigenerated (k := k) (monomialGenerators_nonempty hI hne)
      (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI, locallyEquigenerated_iff]

/-- The complete integral-closure ideal in Theorem 2.11, for an arbitrary literal I. -/
theorem monomialIdeal_integralClosure {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) {d : ℕ}
    (hd : Equigenerated (monomialGenerators I hI) d) :
    {f : MvPolynomial V k | IntegralOverIdeal I f} =
      (monomialIdeal k (lowerBaseFamily (lowerRank (monomialGenerators I hI)) d) : Set (MvPolynomial V k)) := by
  simpa only [monomialGenerators_ideal I hI] using integralClosure_set_eq
    (k := k) (monomialGenerators_nonempty hI hne) (monomialGenerators_antichain I hI) hl hd

end Characterizations

end
end CheckedCharacterizationsSource71

/-! ## Source: Characterizations.AllCases -/
section CheckedCharacterizationsSource72

/-! Theorem 4.5 and its universal testing predicates, including the zero ideal. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem empty_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0,?_⟩,?_⟩
  · intro a ha; simp at ha
  · intro a ha; simp at ha

theorem polymatroidal_iff_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_localization_band hB hd hd2
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

theorem polymatroidal_iff_pure_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_pure_localization_band hB hd hd2 hl
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

/-- Literal-ideal Theorem 4.5, with no nonzero hypothesis. The degree refers
to the actual minimal monomial generators characterized in MonomialNormalForm. -/
theorem monomialIdeal_polymatroidal_iff_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_localization_band_all (k:=k) hd hd2)

theorem monomialIdeal_polymatroidal_iff_pure_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_pure_localization_band_all (k:=k) hd hd2 hl)

namespace Isolators

def LocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def PureLocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d → LocallyEquigenerated B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def UnboundedLocalizationTestSufficientAll (Γ : Finset (Finset V)) : Prop :=
  ∀ B : Family V, Antichain B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

theorem localizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ LocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd ht; exact h B hd ht
  · intro h B hd ht
    by_cases hB : B.Nonempty
    · exact h B hB hd ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem pureLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ PureLocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd hl ht; exact h B hd hl ht
  · intro h B hd hl ht
    by_cases hB : B.Nonempty
    · exact h B hB hd hl ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem unboundedLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) :
    UnboundedLocalizationTestSufficientAll (k:=k) Γ ↔ UnboundedLocalizationTestSufficient (k:=k) Γ := by
  constructor
  · intro h B _ ha ht; exact h B ha ht
  · intro h B ha ht
    by_cases hB : B.Nonempty
    · exact h B hB ha ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem localizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-1) ⊆ Γ :=
  (localizationTestSufficientAll_iff Γ d).trans (localizationTestSufficient_iff Γ d hd)

theorem pureLocalizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-2) ⊆ Γ :=
  (pureLocalizationTestSufficientAll_iff Γ d).trans (pureLocalizationTestSufficient_iff Γ d hd)

end Isolators
end Characterizations

end
end CheckedCharacterizationsSource72

/-! ## Source: Characterizations.FiniteUniform -/
section CheckedCharacterizationsSource73

/-! # Exact finite uniform probabilities and equally sized fibers -/

noncomputable section
namespace Characterizations
open Classical Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

def finiteFraction (P : X → Prop) : ℝ := (Nat.card {x // P x} : ℝ) / Nat.card X

def preimageSigmaEquiv (f : X → Y) (P : Y → Prop) :
    {x // P (f x)} ≃ Σ y : {y // P y}, {x // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by rw [y.2.property]; exact y.1.property⟩
  left_inv _ := rfl
  right_inv y := by rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩; dsimp at hx; subst y; rfl

theorem card_preimage_of_constant_fiber (f : X → Y) (P : Y → Prop) (c : ℕ)
    (hc : ∀ y, Nat.card {x // f x = y} = c) :
    Nat.card {x // P (f x)} = Nat.card {y // P y} * c := by
  rw [Nat.card_congr (preimageSigmaEquiv f P), Nat.card_sigma]
  simp_rw [hc]
  simp [Nat.card_eq_fintype_card]

theorem fraction_preimage_of_constant_fiber [Nonempty X] (f : X → Y) (P : Y → Prop)
    (c : ℕ) (hc : ∀ y, Nat.card {x // f x = y} = c) :
    finiteFraction (fun x => P (f x)) = finiteFraction P := by
  have hX : Nat.card X = Nat.card Y * c := by
    simpa using card_preimage_of_constant_fiber f (fun _ => True) c hc
  have hcpos : 0 < c := by
    have hh : 0 < Nat.card X := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    nlinarith
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcpos)
  unfold finiteFraction
  rw [card_preimage_of_constant_fiber f P c hc, hX]
  push_cast
  rw [mul_div_mul_right _ _ hcR]

theorem variableOrder_eq_of_lt_iff {V : Type*} [Fintype V]
    (o₁ o₂ : VariableOrder V)
    (h : ∀ a b, o₁ a < o₁ b ↔ o₂ a < o₂ b) : o₁ = o₂ := by
  have hs : StrictMono (fun x => o₂ (o₁.symm x)) := by
    intro a b hab
    exact (h _ _).mp (by simpa using hab)
  apply Equiv.ext
  intro x
  have hh := hs.apply_eq (x := o₁ x)
  simpa using hh.symm

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restrictedOrder_comp_subtype (T : Finset V) (o : VariableOrder V)
    (π : Equiv.Perm T) :
    restrictedOrder ((Equiv.Perm.ofSubtype π).trans o) (Function.Embedding.subtype (· ∈ T)) =
      π.trans (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) := by
  apply variableOrder_eq_of_lt_iff
  intro a b
  rw [restrictedOrder_lt_iff]
  simp only [Equiv.trans_apply, Function.Embedding.subtype_apply, Equiv.Perm.ofSubtype_apply_coe]
  exact (restrictedOrder_lt_iff o (Function.Embedding.subtype (· ∈ T)) (π a) (π b)).symm

def restrictionFiberEquiv (T : Finset V) (r₁ r₂ : VariableOrder T) :
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₁} ≃
    {o : VariableOrder V // restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₂} := by
  let π := r₂.trans r₁.symm
  let σ : Equiv.Perm V := Equiv.Perm.ofSubtype π
  refine {
    toFun := fun o => ⟨σ.trans o.val, ?_⟩
    invFun := fun o => ⟨σ.symm.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · have hσ : σ.symm = Equiv.Perm.ofSubtype π.symm :=
      (map_inv (Equiv.Perm.ofSubtype) π).symm
    rw [hσ, restrictedOrder_comp_subtype, o.property]
    ext a
    simp [π]
  · intro o
    apply Subtype.ext
    ext a
    simp
  · intro o
    apply Subtype.ext
    ext a
    simp

theorem restriction_uniform (T : Finset V) (P : VariableOrder T → Prop) :
    finiteFraction (fun o : VariableOrder V => P (restrictedOrder o (Function.Embedding.subtype (· ∈ T)))) =
      finiteFraction P := by
  classical
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let r₀ : VariableOrder T := Fintype.equivFin T
  let c := Nat.card {o : VariableOrder V //
    restrictedOrder o (Function.Embedding.subtype (· ∈ T)) = r₀}
  apply fraction_preimage_of_constant_fiber _ P c
  intro r
  exact Nat.card_congr (restrictionFiberEquiv T r r₀)

end Characterizations

end
end CheckedCharacterizationsSource73

/-! ## Source: Characterizations.PointUniformity -/
section CheckedCharacterizationsSource74

/-! # Uniform distribution of pointed final triples -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def PointedTriple.map (σ : Equiv.Perm V) (P : PointedTriple V) : PointedTriple V :=
  ⟨σ P.1, ⟨P.2.val.map σ.toEmbedding, by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp (P.2.property.1 hy)).1 (σ.injective he), mem_univ _⟩,
    by simpa using P.2.property.2⟩⟩

theorem CoversPoint.map {o : VariableOrder V} {P : PointedTriple V}
    (h : CoversPoint o P) (σ : Equiv.Perm V) :
    CoversPoint (σ.symm.trans o) (P.map σ) := by
  obtain ⟨i,q,hiq,hA,hf⟩ := h
  refine ⟨σ i,σ q,fun he => hiq (σ.injective he),?_,?_,?_,?_⟩
  · simp [PointedTriple.map,hA]
  · simpa [PointedTriple.map] using hf.1
  · simpa [PointedTriple.map] using hf.2.1
  · intro x hxi hxq hxj
    have hxi' : σ.symm x ≠ i := fun he => hxi (by simpa using congrArg σ he)
    have hxq' : σ.symm x ≠ q := fun he => hxq (by simpa using congrArg σ he)
    have hxj' : σ.symm x ≠ P.1 := fun he => hxj (by simpa [PointedTriple.map] using congrArg σ he)
    simpa using hf.2.2 (σ.symm x) hxi' hxq' hxj'

theorem exists_order_covering_point (P : PointedTriple V) :
    ∃ o : VariableOrder V, CoversPoint o P := by
  obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.property.2
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  obtain ⟨o,ho⟩ := exists_finalTriple i q P.1 hiq hij hqj
  exact ⟨o,i,q,hiq,hA,ho⟩

def pointFiberEquiv (P Q : PointedTriple V) :
    {o : VariableOrder V // CoversPoint o P} ≃ {o : VariableOrder V // CoversPoint o Q} := by
  let oP := (exists_order_covering_point P).choose
  have hP : CoversPoint oP P := (exists_order_covering_point P).choose_spec
  let oQ := (exists_order_covering_point Q).choose
  have hQ : CoversPoint oQ Q := (exists_order_covering_point Q).choose_spec
  let σ : Equiv.Perm V := oP.trans oQ.symm
  have hmap : P.map σ = Q := by
    apply coversPoint_unique _ hQ
    have hh := hP.map σ
    have he : σ.symm.trans oP = oQ := by ext x; simp [σ]
    simpa only [he] using hh
  have hmapinv : Q.map σ.symm = P := by
    apply coversPoint_unique _ hP
    have hh := hQ.map σ.symm
    have he : σ.trans oQ = oP := by ext x; simp [σ]
    simpa only [Equiv.symm_symm,he] using hh
  refine {
    toFun := fun o => ⟨σ.symm.trans o.val, hmap ▸ o.property.map σ⟩
    invFun := fun o => ⟨σ.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [Equiv.symm_symm] using (hmapinv ▸ o.property.map σ.symm)
  · intro o; apply Subtype.ext; ext x; simp
  · intro o; apply Subtype.ext; ext x; simp

theorem exists_point_covered (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    ∃ P : PointedTriple V, CoversPoint o P := by
  let i := o.symm ⟨Fintype.card V-3,by omega⟩
  let q := o.symm ⟨Fintype.card V-2,by omega⟩
  let j := o.symm ⟨Fintype.card V-1,by omega⟩
  have hi : (o i).val = Fintype.card V-3 := by simp [i]
  have hq : (o q).val = Fintype.card V-2 := by simp [q]
  have hj : (o j).val = Fintype.card V-1 := by simp [j]
  have hiq : i ≠ q := by intro he; rw [he] at hi; omega
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  have hqj : q ≠ j := by intro he; rw [he] at hq; omega
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩
  refine ⟨P,i,q,hiq,rfl,?_,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · change (o q).val < (o j).val
    omega
  · intro x hxi hxq hxj
    have hn1 : (o x).val ≠ (o i).val := fun he => hxi (o.injective (Fin.ext he))
    have hn2 : (o x).val ≠ (o q).val := fun he => hxq (o.injective (Fin.ext he))
    have hn3 : (o x).val ≠ (o j).val := fun he => hxj (o.injective (Fin.ext he))
    have hxlt := (o x).isLt
    change (o x).val < (o i).val ∧ (o x).val < (o q).val
    omega

def finalPoint (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) : PointedTriple V :=
  (exists_point_covered hcard o).choose

theorem finalPoint_spec (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    CoversPoint o (finalPoint hcard o) := (exists_point_covered hcard o).choose_spec

theorem finalPoint_eq_iff (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) (P : PointedTriple V) :
    finalPoint hcard o = P ↔ CoversPoint o P :=
  ⟨fun h => h ▸ finalPoint_spec hcard o, fun h => coversPoint_unique (finalPoint_spec hcard o) h⟩

theorem pointedTriple_probability (hcard : 3 ≤ Fintype.card V) (P : PointedTriple V) :
    finiteFraction (fun o : VariableOrder V => CoversPoint o P) =
      1 / (Fintype.card V * (Fintype.card V - 1).choose 2 : ℕ) := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let c := Nat.card {o : VariableOrder V // CoversPoint o P}
  have hc (Q : PointedTriple V) : Nat.card {o : VariableOrder V // finalPoint hcard o = Q} = c := by
    calc
      _ = Nat.card {o : VariableOrder V // CoversPoint o Q} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun o => finalPoint_eq_iff hcard o Q))
      _ = c := Nat.card_congr (pointFiberEquiv Q P)
  have hh := fraction_preimage_of_constant_fiber (finalPoint hcard) (fun Q => Q = P) c hc
  have he : (fun o : VariableOrder V => finalPoint hcard o = P) = (fun o => CoversPoint o P) :=
    funext (fun o => propext (finalPoint_eq_iff hcard o P))
  rw [he] at hh
  simpa [finiteFraction,Nat.card_eq_fintype_card,card_pointedTriple] using hh

end Characterizations

end
end CheckedCharacterizationsSource74

/-! ## Source: Characterizations.PatternProbability -/
section CheckedCharacterizationsSource75

/-! # The exact rejection mass of an active order pattern -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteFraction_congr {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x ↔ Q x) : finiteFraction P = finiteFraction Q :=
  congrArg finiteFraction (funext (fun x => propext (h x)))

theorem finiteFraction_mono {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x → Q x) : finiteFraction P ≤ finiteFraction Q := by
  have hc : Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
    Nat.card_le_card_of_injective (fun x => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
      (fun _ _ he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)

theorem finiteFraction_true {X : Type*} [Fintype X] [Nonempty X] :
    finiteFraction (fun _ : X => True) = 1 := by
  unfold finiteFraction
  simp [Nat.card_eq_fintype_card,Fintype.card_pos.ne']

theorem finiteFraction_le_one {X : Type*} [Fintype X] [Nonempty X] (P : X → Prop) :
    finiteFraction P ≤ 1 := by
  rw [← finiteFraction_true (X := X)]
  exact finiteFraction_mono (fun _ _ => trivial)

theorem coversPoint_pair_iff {o : VariableOrder V} {i q j : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    CoversPoint o (⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩ : PointedTriple V) ↔
      FinalTriple o i q j := by
  constructor
  · rintro ⟨a,b,hab,hA,hf⟩
    exact hf.of_pair_eq hiq hab hA
  · intro hf
    exact ⟨i,q,hiq,rfl,hf⟩

theorem restricted_finalTriple_iff (T : Finset V) (o : VariableOrder V) (i q j : T) :
    FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) i q j ↔
      OrderPattern o (T \ {i.val,q.val,j.val}) i.val q.val j.val := by
  simp only [FinalTriple,OrderPattern,restrictedOrder_lt_iff]
  constructor
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hx
    obtain ⟨hxT,hxn⟩ := mem_sdiff.mp hx
    have hxi : x ≠ i.val := fun he => hxn (by simp [he])
    have hxq : x ≠ q.val := fun he => hxn (by simp [he])
    have hxj : x ≠ j.val := fun he => hxn (by simp [he])
    exact hr ⟨x,hxT⟩ (fun he => hxi (congrArg Subtype.val he))
      (fun he => hxq (congrArg Subtype.val he)) (fun he => hxj (congrArg Subtype.val he))
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hxi hxq hxj
    apply hr x.val
    exact mem_sdiff.mpr ⟨x.property,by
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hxi (Subtype.ext he),fun he => hxq (Subtype.ext he),fun he => hxj (Subtype.ext he)⟩⟩

theorem restricted_point_probability (T : Finset V) (hT : 3 ≤ T.card) (P : PointedTriple T) :
    finiteFraction (fun o : VariableOrder V => CoversPoint
      (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) =
      1 / (T.card * (T.card-1).choose 2 : ℕ) := by
  calc
    _ = finiteFraction (fun r : VariableOrder T => CoversPoint r P) := restriction_uniform T _
    _ = _ := by
      have hh := pointedTriple_probability (V := T) (by simpa using hT) P
      simpa only [Fintype.card_coe] using hh

theorem orderPattern_probability (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      1 / ((C.card+3) * (C.card+2).choose 2 : ℕ) := by
  let T := patternActive C i q j
  let I : T := ⟨i,by simp [T,patternActive]⟩
  let Q : T := ⟨q,by simp [T,patternActive]⟩
  let J : T := ⟨j,by simp [T,patternActive]⟩
  have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
  have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
  have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
  let P : PointedTriple T := ⟨J,⟨{I,Q},by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩
  have hTC : T \ {i,q,j} = C := by
    ext x
    have hiC : i ∉ C := fun h => by simpa using hC h
    have hqC : q ∉ C := fun h => by simpa using hC h
    have hjC : j ∉ C := fun h => by simpa using hC h
    by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
      simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
  have he (o : VariableOrder V) :
      CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P ↔ OrderPattern o C i q j := by
    rw [coversPoint_pair_iff hIQ hIJ hQJ, restricted_finalTriple_iff]
    simpa only [I,Q,J,hTC]
  have hcard : Fintype.card T = C.card+3 := by
    rw [Fintype.card_coe]
    exact patternActive_card hiq hij hqj hC
  calc
    _ = finiteFraction (fun o : VariableOrder V => CoversPoint
        (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) := finiteFraction_congr (fun o => (he o).symm)
    _ = _ := by
      have hTc : T.card = C.card+3 := by simpa only [Fintype.card_coe] using hcard
      rw [restricted_point_probability T (by omega) P,hTc]
      simp

/-- The fraction in the paper's displayed rational form. -/
theorem orderPattern_probability_formula (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      2 / (((C.card:ℝ)+1) * ((C.card:ℝ)+2) * ((C.card:ℝ)+3)) := by
  rw [orderPattern_probability C i q j hiq hij hqj hC]
  have hn := Nat.add_one_mul_choose_eq (C.card+1) 1
  have hn' : ((C.card+2).choose 2 : ℝ)*2 = ((C.card:ℝ)+1)*((C.card:ℝ)+2) := by
    have hh : (C.card+2).choose 2 * 2 = (C.card+1)*(C.card+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (C.card+2).choose 2 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ C.card+2))
  push_cast
  field_simp
  nlinarith

end Characterizations

end
end CheckedCharacterizationsSource75

/-! ## Source: Characterizations.FiniteCover -/
section CheckedCharacterizationsSource76

/-! # A kernel-checked probabilistic covering bound for finite tests -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {X I : Type*} [Fintype X] [Fintype I]

theorem finiteFraction_not [Nonempty X] (P : X → Prop) :
    finiteFraction (fun x => ¬P x) = 1 - finiteFraction P := by
  classical
  have hle := Fintype.card_subtype_le P
  have hpos : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  unfold finiteFraction
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  rw [Nat.cast_sub hle]
  field_simp

theorem finiteFraction_exists_le_sum (R : I → X → Prop) :
    finiteFraction (fun x => ∃ i,R i x) ≤ ∑ i, finiteFraction (R i) := by
  classical
  let f : {x // ∃ i,R i x} → Σ i : I, {x // R i x} :=
    fun x => ⟨x.property.choose,⟨x.val,x.property.choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : Σ i : I, {x // R i x} => z.2.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hc
  unfold finiteFraction
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

def allTrialEquiv (M : ℕ) (P : X → Prop) :
    {f : Fin M → X // ∀ j,P (f j)} ≃ (Fin M → {x // P x}) where
  toFun f j := ⟨f.val j,f.property j⟩
  invFun f := ⟨fun j => (f j).val,fun j => (f j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteFraction_all_trials (M : ℕ) (P : X → Prop) :
    finiteFraction (fun f : Fin M → X => ∀ j,P (f j)) = (finiteFraction P)^M := by
  unfold finiteFraction
  rw [Nat.card_congr (allTrialEquiv M P),Nat.card_fun,Nat.card_fun]
  simp only [Nat.card_fin,Nat.cast_pow,div_pow]

theorem finiteFraction_nonneg (P : X → Prop) : 0 ≤ finiteFraction P := by
  unfold finiteFraction
  positivity

theorem exists_outside_of_fraction_lt_one [Nonempty X] (P : X → Prop)
    (h : finiteFraction P < 1) : ∃ x, ¬P x := by
  by_contra hn
  have hP : ∀ x,P x := by simpa using hn
  have he : finiteFraction P = 1 := by
    rw [finiteFraction_congr (fun x => iff_true_intro (hP x)),finiteFraction_true]
  linarith

/-- Independent draws miss at most the sum of the exact individual missing
probabilities. This is a finite counting proof of the union bound. -/
theorem independent_miss_fraction_bound [Nonempty X] (R : I → X → Prop)
    (p : ℝ) (hp : 0 ≤ p) (hR : ∀ i, finiteFraction (R i) = p) (M : ℕ) :
    finiteFraction (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j)) ≤
      (Fintype.card I : ℝ) * Real.exp (-p * M) := by
  have hsum := finiteFraction_exists_le_sum (fun i (f : Fin M → X) => ∀ j,¬R i (f j))
  have hsingle (i : I) : finiteFraction (fun f : Fin M → X => ∀ j,¬R i (f j)) = (1-p)^M := by
    rw [finiteFraction_all_trials M (fun x => ¬R i x),finiteFraction_not (R i),hR i]
  simp only [hsingle,sum_const,card_univ,nsmul_eq_mul] at hsum
  apply hsum.trans
  by_cases hI : Nonempty I
  · letI := hI
    have hple : p ≤ 1 := by
      obtain ⟨i⟩ := hI
      simpa [hR i] using finiteFraction_le_one (R i)
    have hexp : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-p) hexp M
    have he : Real.exp (-p)^M = Real.exp (-p * M) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he] at hpow
    exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    simp

/-- A finite family meeting all tests, with the exact logarithmic size bound. -/
theorem finite_probabilistic_cover [Nonempty X] [Nonempty I]
    (R : I → X → Prop) (p : ℝ) (hp : 0 < p)
    (hR : ∀ i, finiteFraction (R i) = p) :
    ∃ F : Finset X, F.card ≤ ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊ ∧
      ∀ i, ∃ x ∈ F,R i x := by
  classical
  let M : ℕ := ⌈p⁻¹ * (Real.log (Fintype.card I) + 1)⌉₊
  have hM : p⁻¹ * (Real.log (Fintype.card I) + 1) ≤ (M : ℝ) := Nat.le_ceil _
  have hQ : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpM : Real.log (Fintype.card I) + 1 ≤ p * M := by
    have hh := mul_le_mul_of_nonneg_left hM hp.le
    simpa [← mul_assoc,mul_inv_cancel₀ hp.ne'] using hh
  have hbound : (Fintype.card I : ℝ) * Real.exp (-p*M) < 1 := by
    calc
      _ = Real.exp (Real.log (Fintype.card I) - p*M) := by
        rw [Real.exp_sub,Real.exp_log hQ]
        simp [Real.exp_neg,div_eq_mul_inv]
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ < 1 := by simpa using (Real.exp_lt_exp.mpr (show (-1:ℝ)<0 by norm_num))
  obtain ⟨f,hf⟩ := exists_outside_of_fraction_lt_one
    (fun f : Fin M → X => ∃ i,∀ j,¬R i (f j))
    ((independent_miss_fraction_bound R p hp.le hR M).trans_lt hbound)
  refine ⟨univ.image f,?_,?_⟩
  · exact (card_image_le).trans (by simp [M])
  · intro i
    have hi : ∃ j,R i (f j) := by
      by_contra hn
      exact hf ⟨i,by simpa using hn⟩
    obtain ⟨j,hj⟩ := hi
    exact ⟨f j,mem_image.mpr ⟨j,mem_univ _,rfl⟩,hj⟩

end Characterizations

end
end CheckedCharacterizationsSource76

/-! ## Source: Characterizations.PatternSpace -/
section CheckedCharacterizationsSource77

/-! # The finite space of all required degree-sensitive patterns -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev DegreePattern (V : Type*) [Fintype V] [DecidableEq V] (s : ℕ) :=
  Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val

def RealizesPattern {s : ℕ} (o : VariableOrder V) (P : DegreePattern V s) : Prop :=
  CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2

theorem card_degreePattern (s : ℕ) : Nat.card (DegreePattern V s) =
    (Fintype.card V).choose (s+3) * ((s+3)*(s+2).choose 2) := by
  change Nat.card (Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val) = _
  rw [Nat.card_sigma]
  have hP (T : {T : Finset V // T.card = s+3}) :
      Nat.card (PointedTriple T.val) = (s+3)*(s+2).choose 2 := by
    rw [Nat.card_eq_fintype_card,card_pointedTriple,Fintype.card_coe,T.property]
    simp
  simp_rw [hP]
  simp [Fintype.card_finset_len]

theorem pointedTriple_count_formula (n : ℕ) (hn : 1 ≤ n) :
    n*(n-1).choose 2 = 3*n.choose 3 := by
  have hh := Nat.add_one_mul_choose_eq (n-1) 2
  have he : n-1+1 = n := by omega
  simpa [he,mul_comm] using hh

theorem card_degreePattern_paper (s : ℕ) (hn : 1 ≤ Fintype.card V) :
    Nat.card (DegreePattern V s) =
      Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose s := by
  have hsmall : (s+3)*(s+2).choose 2 = 3*(s+3).choose 3 := by
    simpa using pointedTriple_count_formula (s+3) (by omega)
  rw [card_degreePattern,hsmall,pointedTriple_count_formula (Fintype.card V) hn]
  have hh := Nat.choose_mul (n := Fintype.card V) (k := s+3) (s := 3) (by omega)
  have he : s+3-3 = s := by omega
  rw [he] at hh
  nlinarith

theorem degreePattern_nonempty (s : ℕ) (hs : s+3 ≤ Fintype.card V) :
    Nonempty (DegreePattern V s) := by
  obtain ⟨T,hTsub,hTc⟩ := exists_subset_card_eq (show s+3 ≤ (univ : Finset V).card by simpa using hs)
  have hcard : 3 ≤ Fintype.card T := by rw [Fintype.card_coe,hTc]; omega
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct hcard
  exact ⟨⟨⟨T,hTc⟩,⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩⟩

theorem realizesPattern_probability {s : ℕ} (P : DegreePattern V s) :
    finiteFraction (fun o : VariableOrder V => RealizesPattern o P) =
      1 / ((s+3)*(s+2).choose 2 : ℕ) := by
  change finiteFraction (fun o : VariableOrder V => CoversPoint
    (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2) = _
  have hh := restricted_point_probability P.1.val (by rw [P.1.property]; omega) P.2
  simpa only [P.1.property,show s+3-1=s+2 by omega] using hh

theorem coversPatterns_iff_degreePattern {s : ℕ} (F : Set (VariableOrder V)) :
    CoversPatterns s F ↔ ∀ P : DegreePattern V s, ∃ o ∈ F,RealizesPattern o P := by
  constructor
  · intro hF P
    obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.2.property.2
    let j := P.2.1
    have hij : i ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hqj : q ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hiq' : i.val ≠ q.val := fun he => hiq (Subtype.ext he)
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hqj' : q.val ≠ j.val := fun he => hqj (Subtype.ext he)
    let C := P.1.val \ {i.val,q.val,j.val}
    have hCcap : C ⊆ tripleCap i.val q.val j.val := by
      intro x hx
      have hh := (mem_sdiff.mp hx).2
      simpa [tripleCap] using hh
    have hCcard : C.card = s := by
      have hsubset : ({i.val,q.val,j.val} : Finset V) ⊆ P.1.val := by
        simp [insert_subset_iff,i.property,q.property,j.property]
      dsimp only [C]
      rw [card_sdiff_of_subset hsubset,P.1.property]
      simp [hiq',hij',hqj']
    obtain ⟨o,ho,hp⟩ := hF i.val q.val j.val hiq' hij' hqj' C hCcap hCcard
    refine ⟨o,ho,i,q,hiq,hA,?_⟩
    exact (restricted_finalTriple_iff P.1.val o i q j).mpr hp
  · intro hF i q j hiq hij hqj C hC hCc
    let T := patternActive C i q j
    have hTc : T.card = s+3 := by rw [patternActive_card hiq hij hqj hC,hCc]
    let I : T := ⟨i,by simp [T,patternActive]⟩
    let Q : T := ⟨q,by simp [T,patternActive]⟩
    let J : T := ⟨j,by simp [T,patternActive]⟩
    have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
    have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
    have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
    let P : DegreePattern V s := ⟨⟨T,hTc⟩,⟨J,⟨{I,Q},
      by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hF P
    have hf : FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) I Q J :=
      (coversPoint_pair_iff hIQ hIJ hQJ).mp hp
    have hpat := (restricted_finalTriple_iff T o I Q J).mp hf
    have hTC : T \ {i,q,j} = C := by
      ext x
      have hiC : i ∉ C := fun h => by simpa using hC h
      have hqC : q ∉ C := fun h => by simpa using hC h
      have hjC : j ∉ C := fun h => by simpa using hC h
      by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
        simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
    exact ⟨o,ho,by simpa only [I,Q,J,hTC] using hpat⟩

end Characterizations

end
end CheckedCharacterizationsSource77

/-! ## Source: Characterizations.SignatureBound -/
section CheckedCharacterizationsSource78

/-! # The sharp Boolean-antichain constraint on any degree-sensitive test family -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem relative_triples_of_patterns {s : ℕ} {F : Set (VariableOrder V)}
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s F) (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ o ∈ F, o x < o y ∧ o y < o z := by
  have hthree : ({x,y,z} : Finset V).card = 3 := by simp [hxy,hxz,hyz]
  obtain ⟨q, _, hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x,y,z} : Finset V).card < (univ : Finset V).card by simp; omega)
  have hqx : q ≠ x := fun h => hq (by simp [h])
  have hqy : q ≠ y := fun h => hq (by simp [h])
  have hqz : q ≠ z := fun h => hq (by simp [h])
  have hxcap : x ∈ tripleCap y q z := (mem_tripleCap _ _ _ _).mpr ⟨hxy,hqx.symm,hxz⟩
  have hcapcard : (tripleCap y q z).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hqy.symm, hyz, hqz]
  obtain ⟨C,hxC,hCcap,hCc⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hxcap)
    (show ({x} : Finset V).card ≤ s by simpa using hs)
    (show s ≤ (tripleCap y q z).card by omega)
  obtain ⟨o,ho,hp⟩ := hF y q z hqy.symm hyz hqz C hCcap hCc
  exact ⟨o,ho,(hp.2.2 x (hxC (by simp))).1,hp.1⟩

/-- Corollary 5.5, inequality (5.3), for every finite family satisfying the
full degree-sensitive test criterion. -/
theorem pattern_signature_bound {s : ℕ} (F : Finset (VariableOrder V))
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  obtain ⟨x,y,hxy⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let signature (x : Except y) : Finset F := univ.filter (fun o => o.val x.val < o.val y)
  have hnot (x z : Except y) (hxz : x ≠ z) : ¬ signature x ⊆ signature z := by
    intro hsub
    obtain ⟨o,ho,hxyO,hyzO⟩ := relative_triples_of_patterns hcard hs hsn hF x.val y z.val
      x.property (fun he => hxz (Subtype.ext he)) z.property.symm
    have hxmem : (⟨o,ho⟩ : F) ∈ signature x := by simp [signature,hxyO]
    have hzmem := hsub hxmem
    have hzyO : o z.val < o y := by simpa [signature] using hzmem
    exact (lt_irrefl _ (hyzO.trans hzyO))
  have hinj : Function.Injective signature := by
    intro x z he
    by_contra hn
    exact hnot x z hn (by rw [he])
  let A : Finset (Finset F) := univ.image signature
  have hA : IsAntichain (· ⊆ ·) (A : Set (Finset F)) := by
    intro a ha b hb hab hsub
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    have hxz : x ≠ z := fun he => hab (congrArg signature he)
    exact hnot x z hxz hsub
  have hAc : A.card = Fintype.card V - 1 := by
    dsimp only [A]
    rw [card_image_of_injective _ hinj, card_univ, card_except]
  have hh := hA.sperner
  simpa [hAc] using hh

theorem degree_test_signature_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  exact pattern_signature_bound F hcard (by omega) (Nat.min_le_right _ _)
    ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1

end Characterizations

end
end CheckedCharacterizationsSource78

/-! ## Source: Characterizations.SmallTestNumbers -/
section CheckedCharacterizationsSource79

/-! # The exact zero-, one-, and six-test small cases -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem variableOrder_card : Fintype.card (VariableOrder V) = (Fintype.card V).factorial :=
  Fintype.card_equiv (Fintype.equivFin V)

theorem finalPair_card_three_values (hcard : Fintype.card V = 3)
    {o : VariableOrder V} {i j : V} (hij : i ≠ j) (h : FinalPair o i j) :
    (o i).val = 1 ∧ (o j).val = 2 ∧ ∀ x, x ≠ i → x ≠ j → (o x).val = 0 := by
  obtain ⟨q,_,hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({i,j} : Finset V).card < (univ : Finset V).card by simp [hij,hcard])
  have hqi : q ≠ i := fun he => hq (by simp [he])
  have hqj : q ≠ j := fun he => hq (by simp [he])
  have hlt1 := h.1
  have hlt0 := h.2 q hqi hqj
  have hiBound := (o i).isLt
  have hjBound := (o j).isLt
  have hqBound := (o q).isLt
  change (o i).val < (o j).val at hlt1
  change (o q).val < (o i).val at hlt0
  refine ⟨by omega, by omega, ?_⟩
  intro x hxi hxj
  have hh := h.2 x hxi hxj
  change (o x).val < (o i).val at hh
  omega

theorem finalPair_unique_card_three (hcard : Fintype.card V = 3)
    {o o' : VariableOrder V} {i j : V} (hij : i ≠ j)
    (h : FinalPair o i j) (h' : FinalPair o' i j) : o = o' := by
  obtain ⟨hi,hj,hrest⟩ := finalPair_card_three_values hcard hij h
  obtain ⟨hi',hj',hrest'⟩ := finalPair_card_three_values hcard hij h'
  ext x
  by_cases hxi : x = i
  · subst x; omega
  by_cases hxj : x = j
  · subst x; omega
  rw [hrest x hxi hxj,hrest' x hxi hxj]

theorem order_has_finalPair_card_three (hcard : Fintype.card V = 3) (o : VariableOrder V) :
    ∃ i j : V, i ≠ j ∧ FinalPair o i j := by
  let i := o.symm ⟨1,by omega⟩
  let j := o.symm ⟨2,by omega⟩
  have hi : (o i).val = 1 := by simp [i]
  have hj : (o j).val = 2 := by simp [j]
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  refine ⟨i,j,hij,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · intro x hxi hxj
    have hni : (o x).val ≠ 1 := fun he => hxi (o.injective (Fin.ext (he.trans hi.symm)))
    have hnj : (o x).val ≠ 2 := fun he => hxj (o.injective (Fin.ext (he.trans hj.symm)))
    have hb := (o x).isLt
    change (o x).val < (o i).val
    omega

theorem degree_tests_card_three_iff_univ {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V)) :
    DegreeOrderTests k d (F : Set (VariableOrder V)) ↔ F = univ := by
  constructor
  · intro htest
    apply eq_univ_of_forall
    intro o
    by_contra hn
    obtain ⟨i,j,hij,hfinal⟩ := order_has_finalPair_card_three hcard o
    let c : Exponent V := Finsupp.single i (d-2)
    have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
    have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
    have hgen : Equigenerated (translatedFamily c (pairFamily i j)) d := by
      have hh := translatedFamily_equigenerated hbase c
      have he : 2+c.degree = d := by omega
      exact he ▸ hh
    have hp := htest _ hgen (fun o' ho' =>
      (translatedFamily_linearQuotients_iff hbase c o').mpr
        (pairFamily_linearQuotients_of_not_final hij o' (fun hf =>
          hn ((finalPair_unique_card_three hcard hij hf hfinal) ▸ ho'))))
    exact pairFamily_not_polymatroidal hij (by omega)
      ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · rintro rfl B hB hL
    exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ o))

theorem degree_test_number_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) (F : Finset (VariableOrder V))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) : F.card = 6 := by
  rw [(degree_tests_card_three_iff_univ hcard d hd F).mp hF,card_univ,variableOrder_card,hcard]
  norm_num

theorem empty_tests_of_small_degree {k : Type*} [CommSemiring k]
    (d : ℕ) (hd : d ≤ 1) : DegreeOrderTests k d (∅ : Set (VariableOrder V)) := by
  intro B hB _
  exact equigenerated_polymatroidal_of_degree_le_one hB hd

theorem empty_tests_of_small_dimension {k : Type*} [CommSemiring k]
    (hcard : Fintype.card V ≤ 1) : UniversalOrderTests k (∅ : Set (VariableOrder V)) := by
  intro B d hB _
  exact equigenerated_polymatroidal_of_card_le_one hB hcard

theorem degree_tests_card_two_iff_nonempty {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) (F : Set (VariableOrder V)) :
    DegreeOrderTests k d F ↔ F.Nonempty := by
  constructor
  · intro htest
    by_contra hn
    obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (by omega : 2 ≤ Fintype.card V)
    apply purePair_not_polymatroidal hd hij
    exact htest _ (purePair_equigenerated d i j) (fun o ho => False.elim (hn ⟨o,ho⟩))
  · intro hne B hB hL
    obtain ⟨o,ho⟩ := hne
    exact one_order_suffices_card_two hB (by omega) o (hL o ho)

end Characterizations

end
end CheckedCharacterizationsSource79

/-! ## Source: Characterizations.HighDegreeNumbers -/
section CheckedCharacterizationsSource80

/-! # The exact test number once the degree reaches n-2 -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coversPatterns_top_iff (F : Set (VariableOrder V)) :
    CoversPatterns (Fintype.card V-3) F ↔ CoversFinalTriples F := by
  constructor
  · intro hF i q j hiq hij hqj
    have hc : (tripleCap i q j).card = Fintype.card V-3 := by
      rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
      simp [hiq,hij,hqj]
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj (tripleCap i q j) le_rfl hc
    exact ⟨o,ho,hp.1,hp.2.1,fun x hxi hxq hxj => hp.2.2 x
      ((mem_tripleCap _ _ _ _).mpr ⟨hxi,hxq,hxj⟩)⟩
  · intro hF i q j hiq hij hqj C hC hc
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj
    refine ⟨o,ho,hp.1,hp.2.1,?_⟩
    intro x hx
    obtain ⟨hxi,hxq,hxj⟩ := (mem_tripleCap _ _ _ _).mp (hC hx)
    exact hp.2.2 x hxi hxq hxj

theorem exact_high_degree_test_number {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (d : ℕ) (hd : Fintype.card V-2 ≤ d) :
    (∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V-1).choose 2) ∧
    (∀ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) →
      Fintype.card V * (Fintype.card V-1).choose 2 ≤ F.card) := by
  constructor
  · obtain ⟨F,hF,hc⟩ := (exact_universal_test_number (k := k) (V := V) hcard).1
    exact ⟨F,fun B hB hL => hF B d hB hL,hc⟩
  · intro F hF
    have hp := ((degreeOrderTests_iff_coverage d (by omega) hcard _).mp hF).1
    have he : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
    rw [he] at hp
    exact triple_coverage_card_lower_bound F ((coversPatterns_top_iff _).mp hp)

end Characterizations

end
end CheckedCharacterizationsSource80

/-! ## Source: Characterizations.CountingBounds -/
section CheckedCharacterizationsSource81

/-! # The numerical upper and lower bounds of Corollary 5.5 -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def testProbability (d : ℕ) : ℝ := 2 / ((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2))

theorem inverse_point_count_eq_probability (s : ℕ) :
    (1 / ((s+3)*(s+2).choose 2 : ℕ) : ℝ) = testProbability (s+1) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold testProbability
  push_cast
  field_simp
  nlinarith

theorem exists_degree_test_family_logarithmic {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2) :
    ∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card ≤ ⌈(testProbability d)⁻¹ *
        (Real.log (Fintype.card V * (Fintype.card V-1).choose 2 *
          (Fintype.card V-3).choose (d-1)) + 1)⌉₊ := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  letI : Nonempty (DegreePattern V (d-1)) := degreePattern_nonempty (d-1) (by omega)
  have hp : 0 < testProbability d := by unfold testProbability; positivity
  have hR (P : DegreePattern V (d-1)) :
      finiteFraction (fun o : VariableOrder V => RealizesPattern o P) = testProbability d := by
    rw [realizesPattern_probability,inverse_point_count_eq_probability]
    congr 1
    omega
  obtain ⟨F,hsize,hcover⟩ := finite_probabilistic_cover
    (fun (P : DegreePattern V (d-1)) (o : VariableOrder V) => RealizesPattern o P)
    (testProbability d) hp hR
  have hpat : CoversPatterns (d-1) (F : Set (VariableOrder V)) :=
    (coversPatterns_iff_degreePattern _).mpr hcover
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  refine ⟨F,(degreeOrderTests_iff_coverage d hd hcard _).mpr ⟨by rw [hmin]; exact hpat,?_⟩,?_⟩
  · intro hn
    omega
  · have hcount : Fintype.card (DegreePattern V (d-1)) =
        Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose (d-1) := by
      simpa only [Nat.card_eq_fintype_card] using card_degreePattern_paper (V := V) (d-1) (by omega)
    simpa only [hcount,Nat.cast_mul] using hsize

theorem degree_test_number_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    3 * (d+2).choose 3 ≤ F.card := by
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq (show d+2 ≤ (univ : Finset V).card by simp; omega)
  let e : T ↪ V := Function.Embedding.subtype _
  let F' : Finset (VariableOrder T) := F.image (fun o => restrictedOrder o e)
  have hpatterns := ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  rw [hmin] at hpatterns
  have hcover := (coversPatterns_iff_degreePattern _).mp hpatterns
  have htriples : CoversFinalTriples (F' : Set (VariableOrder T)) := by
    intro i q j hiq hij hqj
    have hTcard : T.card = (d-1)+3 := by omega
    let P : DegreePattern V (d-1) := ⟨⟨T,hTcard⟩,⟨j,⟨{i,q},
      by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hcover P
    refine ⟨restrictedOrder o e,mem_image.mpr ⟨o,ho,rfl⟩,?_⟩
    exact (coversPoint_pair_iff hiq hij hqj).mp hp
  have hh := triple_coverage_card_lower_bound F' htriples
  rw [Fintype.card_coe,hTc,pointedTriple_count_formula (d+2) (by omega)] at hh
  exact hh.trans (card_image_le)

end Characterizations

end
end CheckedCharacterizationsSource81

/-! ## Source: Characterizations.TestNumbers -/
section CheckedCharacterizationsSource82

/-! # The literal minimum numbers N(n) and N(n,d) -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid

variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem exists_degree_test_size (n d : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def orderTestNumber (n d : ℕ) : ℕ := Nat.find (exists_degree_test_size k n d)

theorem orderTestNumber_attained (n d : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)),
      DegreeOrderTests k d (F : Set (VariableOrder (Fin n))) ∧ F.card = orderTestNumber k n d :=
  Nat.find_spec (exists_degree_test_size k n d)

theorem orderTestNumber_le_card {n d : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : DegreeOrderTests k d (F : Set (VariableOrder (Fin n)))) : orderTestNumber k n d ≤ F.card :=
  Nat.find_min' (exists_degree_test_size k n d) ⟨F,hF,rfl⟩

theorem exists_universal_test_size (n : ℕ) :
    ∃ m, ∃ F : Finset (VariableOrder (Fin n)),
      UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧ F.card = m := by
  refine ⟨Fintype.card (VariableOrder (Fin n)),univ,?_,card_univ⟩
  intro B d hB hL
  exact (polymatroidal_iff_universal_revlex hB).mpr (fun o => hL o (mem_univ _))

def universalTestNumber (n : ℕ) : ℕ := Nat.find (exists_universal_test_size k n)

theorem universalTestNumber_attained (n : ℕ) :
    ∃ F : Finset (VariableOrder (Fin n)), UniversalOrderTests k (F : Set (VariableOrder (Fin n))) ∧
      F.card = universalTestNumber k n := Nat.find_spec (exists_universal_test_size k n)

theorem universalTestNumber_le_card {n : ℕ} (F : Finset (VariableOrder (Fin n)))
    (hF : UniversalOrderTests k (F : Set (VariableOrder (Fin n)))) : universalTestNumber k n ≤ F.card :=
  Nat.find_min' (exists_universal_test_size k n) ⟨F,hF,rfl⟩

theorem universalTestNumber_ge_four {n : ℕ} (hn : 4 ≤ n) :
    universalTestNumber k n = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k n
  have hlo := universalOrderTests_card_lower_bound (V := Fin n) (by simpa) F hF
  obtain ⟨G,hG,hGc⟩ := (exact_universal_test_number (k := k) (V := Fin n) (by simpa using hn)).1
  have hhi := universalTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem universalTestNumber_one : universalTestNumber k 1 = 0 := by
  have h := universalTestNumber_le_card k (∅ : Finset (VariableOrder (Fin 1)))
    (by simpa using (empty_tests_of_small_dimension (k := k) (V := Fin 1) (by simp)))
  simpa using h

theorem universalTestNumber_two : universalTestNumber k 2 = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have hhi := universalTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2)))
    (nonempty_order_family_card_two (by simp) _ ⟨o,by simp⟩)
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 2
  have hne := (degree_tests_card_two_iff_nonempty (k := k) (V := Fin 2) (by simp) 2 (by omega) _).mp
    (fun B hB hL => hF B 2 hB hL)
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem universalTestNumber_three : universalTestNumber k 3 = 6 := by
  obtain ⟨F,hF,hc⟩ := universalTestNumber_attained k 3
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) 2 (by omega) F
    (fun B hB hL => hF B 2 hB hL)
  omega

theorem orderTestNumber_small_degree {n d : ℕ} (hd : d ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (by simpa using (empty_tests_of_small_degree (k := k) (V := Fin n) d hd))
  simpa using hh

theorem orderTestNumber_small_dimension {n d : ℕ} (hn : n ≤ 1) : orderTestNumber k n d = 0 := by
  have hh := orderTestNumber_le_card k (d := d) (∅ : Finset (VariableOrder (Fin n)))
    (fun B hB _ => equigenerated_polymatroidal_of_card_le_one hB (by simpa using hn))
  simpa using hh

theorem orderTestNumber_two {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 2 d = 1 := by
  let o : VariableOrder (Fin 2) := Fintype.equivFin _
  have htest : DegreeOrderTests k d (({o} : Finset (VariableOrder (Fin 2))) : Set _) :=
    (degree_tests_card_two_iff_nonempty (by simp) d hd _).mpr ⟨o,by simp⟩
  have hhi := orderTestNumber_le_card k ({o} : Finset (VariableOrder (Fin 2))) htest
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 2 d
  have hne := (degree_tests_card_two_iff_nonempty (by simp) d hd _).mp hF
  have hpos : 0 < F.card := card_pos.mpr hne
  simp only [card_singleton] at hhi
  omega

theorem orderTestNumber_three {d : ℕ} (hd : 2 ≤ d) : orderTestNumber k 3 d = 6 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k 3 d
  have hh := degree_test_number_three (k := k) (V := Fin 3) (by simp) d hd F hF
  omega

theorem orderTestNumber_high_degree {n d : ℕ} (hn : 4 ≤ n) (hd : n-2 ≤ d) :
    orderTestNumber k n d = 3*n.choose 3 := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  have hlo := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).2 F hF
  obtain ⟨G,hG,hGc⟩ := (exact_high_degree_test_number (k := k) (V := Fin n) (by simpa using hn) d (by simpa using hd)).1
  have hhi := orderTestNumber_le_card k G hG
  have hformula := pointedTriple_count_formula n (by omega)
  simp only [Fintype.card_fin] at hlo hGc
  omega

theorem orderTestNumber_logarithmic_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    orderTestNumber k n d ≤ ⌈(testProbability d)⁻¹ *
      (Real.log (n * (n-1).choose 2 * (n-3).choose (d-1)) + 1)⌉₊ := by
  obtain ⟨F,hF,hc⟩ := exists_degree_test_family_logarithmic (k := k) (V := Fin n) d hd
    (by simpa using hn) (by simpa using hdn)
  exact (orderTestNumber_le_card k F hF).trans (by simpa using hc)

theorem orderTestNumber_counting_lower {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n-2) :
    3*(d+2).choose 3 ≤ orderTestNumber k n d := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  rw [←hc]
  exact degree_test_number_lower_bound d hd (by simpa using hn) (by simpa using hdn) F hF

theorem orderTestNumber_signature_bound {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    n-1 ≤ (orderTestNumber k n d).choose (orderTestNumber k n d / 2) := by
  obtain ⟨F,hF,hc⟩ := orderTestNumber_attained k n d
  simpa [hc] using degree_test_signature_bound d hd (V := Fin n) (by simpa using hn) F hF

end Characterizations

end
end CheckedCharacterizationsSource82

/-! ## Source: Characterizations.AsymptoticTests -/
section CheckedCharacterizationsSource83

/-! # The fixed-degree logarithmic asymptotic in Corollary 5.5 -/

noncomputable section
namespace Characterizations
open Classical Finset Filter Asymptotics
variable (k : Type*) [CommSemiring k] [Nontrivial k]

theorem pattern_count_le_power {n d : ℕ} (hd : 1 ≤ d) :
    n * (n-1).choose 2 * (n-3).choose (d-1) ≤ n^(d+2) := by
  calc
    _ ≤ n * n^2 * n^(d-1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left n ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2))
      · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) (d-1))
    _ = _ := by
      have hfirst : n*n^2=n^3 := by ring
      rw [hfirst,←pow_add]
      congr 1
      omega

theorem testNumber_log_upper {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) (hdn : d+2 ≤ n) :
    (orderTestNumber k n d : ℝ) ≤
      ((testProbability d)⁻¹ * (d+2) + ((testProbability d)⁻¹+1)/Real.log 2) * Real.log n := by
  let Q := n * (n-1).choose 2 * (n-3).choose (d-1)
  let p := testProbability d
  have hp : 0 < p := by dsimp [p,testProbability]; positivity
  have hQ : 0 < Q := by
    apply Nat.mul_pos
    · exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    · exact Nat.choose_pos (by omega)
  have hQpow : (Q:ℝ) ≤ (n:ℝ)^(d+2) := by exact_mod_cast pattern_count_le_power (n := n) (by omega : 1 ≤ d)
  have hlogQ : Real.log Q ≤ (d+2:ℝ)*Real.log n := by
    have hh := Real.log_le_log (show (0:ℝ)<Q by exact_mod_cast hQ) hQpow
    rw [Real.log_pow] at hh
    simpa using hh
  have hA : 0 ≤ p⁻¹ * (Real.log Q+1) := mul_nonneg (inv_nonneg.mpr hp.le)
    (by linarith [Real.log_natCast_nonneg Q])
  have hceil := Nat.ceil_lt_add_one hA
  have hN : (orderTestNumber k n d : ℝ) ≤ ⌈p⁻¹*(Real.log Q+1)⌉₊ := by
    exact_mod_cast orderTestNumber_logarithmic_upper k hn hd (by omega)
  have hN' : (orderTestNumber k n d : ℝ) ≤ p⁻¹*(Real.log Q+1)+1 := hN.trans hceil.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ n by omega))
  have hbonus := mul_le_mul_of_nonneg_left hlogn
    (div_nonneg (by positivity : 0 ≤ p⁻¹+1) hlog2.le)
  rw [div_mul_cancel₀ _ hlog2.ne'] at hbonus
  have hmain := mul_le_mul_of_nonneg_left hlogQ (inv_nonneg.mpr hp.le)
  change (orderTestNumber k n d : ℝ) ≤ (p⁻¹*(d+2) + (p⁻¹+1)/Real.log 2)*Real.log n
  nlinarith

theorem log_le_testNumber {n d : ℕ} (hn : 4 ≤ n) (hd : 2 ≤ d) :
    Real.log n ≤ (2*Real.log 2)*(orderTestNumber k n d : ℝ) := by
  have hsig := orderTestNumber_signature_bound k hn hd
  have hpow : n-1 ≤ 2^(orderTestNumber k n d) :=
    hsig.trans (Nat.choose_le_two_pow _ _)
  have hn1 : (0:ℝ) < (n-1:ℕ) := by exact_mod_cast (show 0<n-1 by omega)
  have hlog := Real.log_le_log hn1 (show ((n-1:ℕ):ℝ) ≤ (2:ℝ)^(orderTestNumber k n d) by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hsquare : (n:ℝ) ≤ (((n-1:ℕ):ℝ))^2 := by
    have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlogn := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega)) hsquare
  rw [Real.log_pow] at hlogn
  norm_num at hlogn
  nlinarith

/-- For every fixed degree d≥2, the exact minimum number of tests has order
Θ(log n), with ordinary real natural logarithm and n tending to infinity. -/
theorem orderTestNumber_isTheta_log (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (orderTestNumber k n d : ℝ)) =Θ[atTop] (fun n : ℕ => Real.log n) := by
  constructor
  · apply IsBigO.of_bound ((testProbability d)⁻¹*(d+2) + ((testProbability d)⁻¹+1)/Real.log 2)
    filter_upwards [eventually_ge_atTop (max 4 (d+2))] with n hn
    have hh := testNumber_log_upper k (n := n) (d := d) (by omega) hd (by omega)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh
  · apply IsBigO.of_bound (2*Real.log 2)
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hh := log_le_testNumber k hn hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ (orderTestNumber k n d : ℝ) by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg n)] using hh

end Characterizations

end
end CheckedCharacterizationsSource83

/-! ## Source: Characterizations.PrimePowers -/
section CheckedCharacterizationsSource84

/-! # Ordinary coordinate-prime powers, and the exact intersection formula -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k]

def coordinatePrime (U : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (MvPolynomial.X '' (U : Set V))

theorem coordinatePrime_weight (U : Finset V) {f : MvPolynomial V k}
    (hf : f ∈ coordinatePrime k U) : Weight.Bound (subsetWeight U) 1 f := by
  intro a ha
  obtain ⟨i, hi, hpos⟩ := MvPolynomial.mem_ideal_span_X_image.mp hf a
    (Finsupp.mem_support_iff.mpr ha)
  rw [weight_subsetWeight]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hpos).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi)

theorem monomial_mem_coordinatePrime_pow (U : Finset V) (n : ℕ) (a : Exponent V)
    (ha : n ≤ subsetSum a U) : monomial a (1 : k) ∈ (coordinatePrime k U) ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨i, hi, hai⟩ := Finset.sum_pos_iff.mp
      (show 0 < ∑ j ∈ U, a j from lt_of_lt_of_le (Nat.zero_lt_succ n) ha)
    have hs := subsetSum_sub_single hai U
    rw [if_pos hi] at hs
    have hrest : n ≤ subsetSum (a - Finsupp.single i 1) U := by omega
    have hfactor : monomial a (1 : k) =
        monomial (a - Finsupp.single i 1) 1 * X i := by
      have he : a - Finsupp.single i 1 + Finsupp.single i 1 = a :=
        tsub_add_cancel_of_le (single_one_le hai)
      have hm := MvPolynomial.monomial_add_single (s := a - Finsupp.single i 1)
        (n := i) (e := 1) (a := (1 : k))
      rw [he, pow_one] at hm
      exact hm
    rw [hfactor, pow_succ]
    exact Ideal.mul_mem_mul (ih _ hrest)
      (Ideal.subset_span (Set.mem_image_of_mem _ hi))

theorem mem_coordinatePrime_pow_iff (U : Finset V) (n : ℕ) (f : MvPolynomial V k) :
    f ∈ (coordinatePrime k U) ^ n ↔ ∀ a ∈ f.support, n ≤ subsetSum a U := by
  constructor
  · intro hf a ha
    have h := Weight.bound_of_mem_pow (RingHom.id _) (subsetWeight U)
      (subsetWeight_nonnegative U) (coordinatePrime k U) 1
      (fun _ h => coordinatePrime_weight k U h) n hf a (Finsupp.mem_support_iff.mp ha)
    rw [weight_subsetWeight] at h
    simpa using h
  · intro hf
    rw [← f.support_sum_monomial_coeff]
    apply Ideal.sum_mem
    intro a ha
    have h := (coordinatePrime k U ^ n).mul_mem_left (C (f.coeff a))
      (monomial_mem_coordinatePrime_pow k U n a (hf a ha))
    simpa only [C_mul_monomial, mul_one] using h

theorem mem_coordinatePrime_pow_iff_weight (U : Finset V) (n : ℕ) (f : MvPolynomial V k) :
    f ∈ (coordinatePrime k U) ^ n ↔ Weight.Bound (subsetWeight U) (n : ℤ) f := by
  rw [mem_coordinatePrime_pow_iff]
  constructor
  · intro h a ha
    rw [weight_subsetWeight]
    exact_mod_cast h a (Finsupp.mem_support_iff.mpr ha)
  · intro h a ha
    have hh := h a (Finsupp.mem_support_iff.mp ha)
    rw [weight_subsetWeight] at hh
    exact_mod_cast hh

theorem canonicalLowerBases_eq_primePower_intersection {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    monomialIdeal k (lowerBaseFamily (lowerRank B) d) =
      ⨅ U : Finset V, (coordinatePrime k U) ^ lowerRank B U := by
  ext f
  rw [mem_monomialIdeal_iff, Ideal.mem_iInf]
  simp only [mem_coordinatePrime_pow_iff, contains_canonicalLowerBases_iff hB hl hd,
    LowerFeasible]
  exact ⟨fun h U a ha => h a ha U, fun h a ha U => h U a ha⟩

variable [IsDomain k]

theorem coordinatePrime_pow_integrallyClosed (U : Finset V) (n : ℕ) :
    IsIntegrallyClosedIdeal ((coordinatePrime k U) ^ n) := by
  intro f hf
  apply (mem_coordinatePrime_pow_iff_weight k U n f).mpr
  exact Weight.bound_of_integral (RingHom.id _) (subsetWeight U)
    (subsetWeight_nonnegative U) ((coordinatePrime k U) ^ n) n
    (fun g hg => (mem_coordinatePrime_pow_iff_weight k U n g).mp hg) hf

theorem primePower_intersection_integrallyClosed (e : Finset V → ℕ) :
    IsIntegrallyClosedIdeal (⨅ U : Finset V, (coordinatePrime k U) ^ e U) := by
  apply Weight.integrallyClosed_of_weight_bounds (RingHom.id _) subsetWeight
    (fun U => (e U : ℤ)) (fun U => subsetWeight_nonnegative U)
  intro f
  simp only [Ideal.mem_iInf, mem_coordinatePrime_pow_iff_weight, RingHom.id_apply]

/-- Equation (2.4), with ordinary powers of literal ideals generated by the
variables in each subset, and the usual ideal-integral-closure predicate. -/
theorem integralClosure_eq_primePower_intersection {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (f : MvPolynomial V k) :
    IntegralOverIdeal (monomialIdeal k B) f ↔
      f ∈ ⨅ U : Finset V, (coordinatePrime k U) ^ lowerRank B U := by
  rw [integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd,
    canonicalLowerBases_eq_primePower_intersection k hB hl hd]

/-- Corollary 2.12: intersection type plus local equigeneration is equivalent
to polymatroidality. Missing factors are represented by exponent zero. -/
theorem polymatroidal_iff_intersectionType_localEquigenerated {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∃ e : Finset V → ℕ, monomialIdeal k B =
        ⨅ U : Finset V, (coordinatePrime k U) ^ e U := by
  constructor
  · intro hp
    have hl := polymatroidal_locallyEquigenerated hp
    obtain ⟨d, hd⟩ := hp.1
    refine ⟨hl, lowerRank B, ?_⟩
    have he : B = lowerBaseFamily (lowerRank B) d :=
      family_eq_of_contains_iff hanti (lowerBaseFamily_equigenerated _ _).antichain
        (fun a => (contains_iff_canonical_lower B hB d hd hp a).trans
          (contains_canonicalLowerBases_iff hB hl hd a).symm)
    conv_lhs => rw [he]
    exact canonicalLowerBases_eq_primePower_intersection k hB hl hd
  · rintro ⟨hl, e, he⟩
    apply (polymatroidal_iff_integrallyClosed_localEquigenerated (k := k) hB hanti).mpr
    refine ⟨?_, hl⟩
    rw [he]
    exact primePower_intersection_integrallyClosed k e

end Characterizations

end
end CheckedCharacterizationsSource84

/-! ## Source: Characterizations.CoordinatePrime -/
section CheckedCharacterizationsSource85

/-! # The coordinate ideals in the intersection formula are actually prime -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k] [IsDomain k]

theorem coordinatePrime_isPrime (U : Finset V) : (coordinatePrime k U).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro ht
    have h : (1 : MvPolynomial V k) ∈ coordinatePrime k U := by rw [ht]; trivial
    have hb := coordinatePrime_weight k U h (0 : Exponent V) (by simp)
    simp [weight_subsetWeight, subsetSum] at hb
  · intro f g hfg
    by_contra hn
    push_neg at hn
    have hzero (p : MvPolynomial V k) (hp : p ∉ coordinatePrime k U) :
        ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight (subsetWeight U) a = 0 := by
      have hn : p ≠ 0 := fun he => hp (he ▸ (coordinatePrime k U).zero_mem)
      obtain ⟨m, hm, a, ha, he⟩ := Weight.exists_minimum (subsetWeight U) hn
      have hm0 : 0 ≤ m := he ▸ subsetWeight_nonnegative U p a ha
      have hm1 : m < 1 := by
        by_contra h
        apply hp
        have hb : Weight.Bound (subsetWeight U) (1 : ℤ) p := hm.mono (by omega)
        simpa only [pow_one] using (mem_coordinatePrime_pow_iff_weight k U 1 p).mpr hb
      exact ⟨a, ha, by omega⟩
    obtain ⟨a, ha, he⟩ := Weight.minimum_mul (subsetWeight_nonnegative U f)
      (subsetWeight_nonnegative U g) (hzero f hn.1) (hzero g hn.2)
    have hb := coordinatePrime_weight k U hfg a ha
    omega

end Characterizations

end
end CheckedCharacterizationsSource85

/-! ## Source: Characterizations.DependencyInterfaces -/
section CheckedCharacterizationsSource86

/-!
# Arbitrary polynomial generators in the exact Rees generation bound

This supplemental interface identifies generation by all homogeneous polynomial
elements through a given Rees degree with generation by the corresponding
monomials. Consequently the exact bound of Homological Shifts, Theorem 4.4,
is the least bound even when arbitrary polynomial generators are allowed.
The underlying ideal is the genuine homological-shift ideal in Mathlib's
ordinary Rees algebra; its coefficients need not themselves be monomials.
-/

noncomputable section

namespace Characterizations.DependencyInterfaces

open Classical Finset CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All homogeneous polynomial elements of the positive-power homological-shift
module whose Rees degree is at most `q`. -/
def boundedHomologicalPolynomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s f, s ≤ q ∧ f ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s f}

theorem boundedHomologicalMonomials_subset_polynomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    boundedHomologicalPowerMonomials I hI i q ⊆
      boundedHomologicalPolynomials I hI i q := by
  rintro p ⟨s, a, ha, hs, he⟩
  exact ⟨s, MvPolynomial.monomial a 1, hs, ha, he⟩

theorem boundedHomologicalPolynomial_span_eq_monomials_rank
    (ρ : RankFunction V) (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials (rankIdeal k ρ) hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q) := by
  apply le_antisymm
  · rw [boundedHomologicalPowerMonomials_rank]
    apply Ideal.span_le.mpr
    rintro p ⟨s, f, hs, hf, he⟩
    rw [homologicalPowerPiece_rank] at hf
    have hfPow := powerShiftPiece_le_pow (k := k) ρ i s hf
    have hp : p = liftReesCoefficient ρ s f hfPow := Subtype.ext he
    rw [hp]
    by_cases hs0 : s = 0
    · have hf0 : f = 0 := by simpa only [hs0, powerShiftPiece_zero, Ideal.mem_bot] using hf
      have hz : liftReesCoefficient ρ s f hfPow = 0 := by
        apply Subtype.ext
        simp [liftReesCoefficient, hf0]
      rw [hz]
      exact Ideal.zero_mem _
    · apply liftReesCoefficient_mem_of_bases ρ i (by omega) _ _ f hf
      intro a ha haPow
      have hmem : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
        rw [powerShiftPiece_pos ρ i (by omega), rankShiftIdeal_eq_monomialIdeal,
          monomial_mem_iff]
        exact ⟨a, ha, le_rfl⟩
      exact Ideal.subset_span ⟨s, a, hmem, hs, rfl⟩
  · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)

/-- Arbitrary polynomial homogeneous generators give exactly the same bounded
span as all bounded monomials. This includes the zero and unit ideals. -/
theorem boundedHomologicalPolynomial_span_eq_monomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials I hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials I hI i q) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, he⟩
  · subst I
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro p ⟨s, f, hs, hf, he⟩
      have hf0 : f = 0 := by
        by_cases hs0 : s = 0
        · simpa [homologicalPowerPiece, hs0] using hf
        · simpa [homologicalPowerPiece, hs0, Ideal.bot_pow hs0] using hf
      have hp : p = 0 := by
        apply Subtype.ext
        simpa [hf0] using he
      rw [hp]
      exact Ideal.zero_mem _
    · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)
  · subst I
    exact boundedHomologicalPolynomial_span_eq_monomials_rank ρ hI i q

/-- The exact least Rees generation bound permits arbitrary polynomial
homogeneous generators and arbitrary polynomial coefficients in the Rees ring. -/
theorem homologicalPower_polynomial_generation_bound_iff
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (ρ : RankFunction V) (he : I = rankIdeal k ρ) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPolynomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  rw [boundedHomologicalPolynomial_span_eq_monomials]
  exact homologicalPower_generation_bound_iff I hI ρ he hρ i hi0 hi q

end Characterizations.DependencyInterfaces

end
end CheckedCharacterizationsSource86

/-! ## Source: Characterizations.Thickening -/
section CheckedCharacterizationsSource87

/-! # Multiplication by every power of the homogeneous maximal ideal -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeFamily (q : ℕ) : Family V := (Finsupp.finite_of_degree_eq (σ := V) q).toFinset

@[simp] theorem mem_degreeFamily (q : ℕ) (a : Exponent V) : a ∈ degreeFamily q ↔ a.degree = q := by
  simp [degreeFamily]

def thickening (B : Family V) (q : ℕ) : Family V :=
  (B.product (degreeFamily q)).image (fun bc => bc.1 + bc.2)

theorem thickening_equigenerated {B : Family V} {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    Equigenerated (thickening B q) (d + q) := by
  intro a ha
  obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  simp only [map_add, hd b hb, (mem_degreeFamily q c).mp hc]

theorem contains_thickening_iff {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) (a : Exponent V) :
    Contains (thickening B q) a ↔ Contains B a ∧ d + q ≤ a.degree := by
  constructor
  · rintro ⟨w, hw, hwa⟩
    obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp hw
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    refine ⟨⟨b,hb,(le_add_right le_rfl).trans hwa⟩, ?_⟩
    have h := degree_mono hwa
    simpa only [map_add, hd b hb, (mem_degreeFamily q c).mp hc] using h
  · rintro ⟨⟨b,hb,hba⟩, hdeg⟩
    have hdiff : q ≤ (a-b).degree := by
      have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hba)
      simp only [map_add, hd b hb] at h
      omega
    obtain ⟨c,hc,hcd⟩ := Finsupp.exists_le_degree_eq (a-b) q hdiff
    refine ⟨b+c, mem_image.mpr ⟨(b,c), mem_product.mpr ⟨hb,(mem_degreeFamily q c).mpr hcd⟩,rfl⟩, ?_⟩
    calc
      b+c ≤ b+(a-b) := add_le_add le_rfl hc
      _ = a := by rw [add_comm, tsub_add_cancel_of_le hba]

theorem thickening_mono {B C : Family V} (h : B ⊆ C) (q : ℕ) :
    thickening B q ⊆ thickening C q := by
  intro a ha
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨(b,c),mem_product.mpr ⟨h (mem_product.mp hbc).1,(mem_product.mp hbc).2⟩,rfl⟩

theorem thickening_nonempty [Nonempty V] {B : Family V} (hB : B.Nonempty) (q : ℕ) :
    (thickening B q).Nonempty := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨i⟩ := ‹Nonempty V›
  exact ⟨b+Finsupp.single i q,mem_image.mpr ⟨(b,Finsupp.single i q),
    mem_product.mpr ⟨hb,by simp⟩,rfl⟩⟩

def raisedTopRank (r : Finset V → ℕ) (q : ℕ) (U : Finset V) : ℕ :=
  if U = Finset.univ then r U + q else r U

theorem raisedTopRank_supermodular {r : Finset V → ℕ} (hr : Supermodular r) (q : ℕ) :
    Supermodular (raisedTopRank r q) := by
  intro A C
  by_cases hA : A = Finset.univ
  · subst A
    have hu : (Finset.univ : Finset V) ∪ C = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_left
    rw [hu]
    simp
  by_cases hC : C = Finset.univ
  · subst C
    have hu : A ∪ (Finset.univ : Finset V) = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) Finset.subset_union_right
    rw [hu]
    simp [add_comm]
  have h := hr A C
  have hle (U : Finset V) : r U ≤ raisedTopRank r q U := by
    unfold raisedTopRank; split_ifs <;> omega
  have hU := hle (A ∪ C)
  have hI := hle (A ∩ C)
  simp only [raisedTopRank, if_neg hA, if_neg hC]
  change r A + r C ≤ raisedTopRank r q (A ∪ C) + raisedTopRank r q (A ∩ C)
  omega

theorem raisedTopRank_feasible_iff {r : Finset V → ℕ} (q : ℕ) (a : Exponent V) :
    LowerFeasible (raisedTopRank r q) a ↔ LowerFeasible r a ∧ r Finset.univ + q ≤ a.degree := by
  constructor
  · intro h
    refine ⟨fun U => ?_, ?_⟩
    · have hh := h U
      unfold raisedTopRank at hh
      split_ifs at hh <;> omega
    · simpa [raisedTopRank] using h Finset.univ
  · rintro ⟨h,hdeg⟩ U
    by_cases hU : U = Finset.univ
    · subst U; simpa [raisedTopRank] using hdeg
    · simpa only [raisedTopRank, if_neg hU] using h U

theorem thickening_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) (q : ℕ) : IsPolymatroidal (thickening B q) := by
  obtain ⟨d,hd⟩ := hp.1
  have hr := lowerRank_supermodular hB (polymatroidal_locallyEquigenerated hp)
  apply polymatroidal_of_lower_inequalities (thickening_equigenerated hd q)
    (raisedTopRank_supermodular hr q)
  intro a
  rw [contains_thickening_iff hd, contains_iff_canonical_lower B hB d hd hp,
    raisedTopRank_feasible_iff, lowerRank_univ_of_equigenerated hB hd]

variable (k : Type*) [CommRing k]

theorem degreeFamily_ideal_eq_maximal_pow (q : ℕ) :
    monomialIdeal k (degreeFamily (V := V) q) = (coordinatePrime k Finset.univ) ^ q := by
  ext f
  rw [mem_monomialIdeal_iff, mem_coordinatePrime_pow_iff]
  apply forall₂_congr
  intro a ha
  simp only [subsetSum_univ]
  constructor
  · rintro ⟨b,hb,hba⟩
    exact ((mem_degreeFamily q b).mp hb).symm.le.trans (degree_mono hba)
  · intro h
    obtain ⟨b,hba,hbd⟩ := Finsupp.exists_le_degree_eq a q h
    exact ⟨b,(mem_degreeFamily q b).mpr hbd,hba⟩

theorem thickening_ideal_eq (B : Family V) (q : ℕ) :
    monomialIdeal k (thickening B q) = (coordinatePrime k Finset.univ) ^ q * monomialIdeal k B := by
  rw [← degreeFamily_ideal_eq_maximal_pow, mul_comm, monomialIdeal_mul]
  rfl

end Characterizations

end
end CheckedCharacterizationsSource87

/-! ## Source: Characterizations.ThickeningClosure -/
section CheckedCharacterizationsSource88

/-! # Exact closure and sharp power threshold for minimal local obstructions -/
noncomputable section
namespace Characterizations
universe u
open Classical CommAlg CommAlg.Polymatroid Finset
open scoped Pointwise
variable {V : Type u} [Fintype V] [DecidableEq V]

@[simp] theorem realExponent_add (a b : Exponent V) :
    realExponent (a+b) = realExponent a + realExponent b := by
  ext i
  simp [realExponent]

theorem realImage_thickening (B : Family V) (q : ℕ) :
    realExponent '' (thickening B q : Set (Exponent V)) =
      (realExponent '' (B : Set (Exponent V))) +
        (realExponent '' (degreeFamily (V := V) q : Set (Exponent V))) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    exact Set.mem_add.mpr ⟨realExponent b,Set.mem_image_of_mem _ hb,
      realExponent c,Set.mem_image_of_mem _ hc,(realExponent_add b c).symm⟩
  · intro hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Set.mem_add.mp hx
    obtain ⟨b,hb,rfl⟩ := hy
    obtain ⟨c,hc,rfl⟩ := hz
    exact ⟨b+c,mem_image.mpr ⟨(b,c),mem_product.mpr ⟨hb,hc⟩,rfl⟩,realExponent_add b c⟩

theorem closed_thickening_generator_mem_convexHull {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) {a : Exponent V} (ha : a ∈ thickening (lowerBaseFamily (lowerRank B) d) q) :
    realExponent a ∈ convexHull ℝ (realExponent '' (thickening B q : Set (Exponent V))) := by
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  rw [realExponent_add, realImage_thickening, convexHull_add]
  exact Set.add_mem_add (canonicalLowerBase_mem_convexHull hB hanti hl hd hb)
    (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hc))

theorem thickening_polymatroidal_iff_closed [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔
      thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q := by
  constructor
  · intro hp
    apply Finset.Subset.antisymm (thickening_mono (subset_lowerBaseFamily hd) q)
    intro a ha
    have hi := monomial_integral_of_convexHull ℚ (thickening B q) a
      (closed_thickening_generator_mem_convexHull hB hanti hl hd q ha)
    have hm := polymatroidal_integrallyClosed (thickening_nonempty hB q) hp _ hi
    have hcontains := (monomial_mem_iff (k := ℚ) _ _).mp hm
    have hdeg := thickening_equigenerated (lowerBaseFamily_equigenerated (lowerRank B) d) q a ha
    exact ((thickening_equigenerated hd q).mem_iff_contains hdeg).mpr hcontains
  · intro he
    rw [he]
    exact thickening_polymatroidal (hB.mono (subset_lowerBaseFamily hd))
      (canonicalLowerBases_polymatroidal hB hl hd) q

theorem thickening_eq_closed_iff_hole_bound {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q ↔
      ∀ a ∈ holeSet B, a.degree < d+q := by
  constructor
  · intro he a ha
    by_contra hn
    have hc : Contains (thickening (lowerBaseFamily (lowerRank B) d) q) a :=
      (contains_thickening_iff (lowerBaseFamily_equigenerated _ _) q a).mpr
        ⟨(contains_canonicalLowerBases_iff hB hl hd a).mpr ha.1,by omega⟩
    rw [← he] at hc
    exact ha.2 ((contains_thickening_iff hd q a).mp hc).1
  · intro h
    apply family_eq_of_contains_iff (thickening_equigenerated hd q).antichain
      (thickening_equigenerated (lowerBaseFamily_equigenerated _ _) q).antichain
    intro a
    rw [contains_thickening_iff hd, contains_thickening_iff (lowerBaseFamily_equigenerated _ _),
      contains_canonicalLowerBases_iff hB hl hd]
    constructor
    · rintro ⟨⟨b,hb,hba⟩,hdeg⟩
      exact ⟨fun U => (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i)),hdeg⟩
    · rintro ⟨ha,hdeg⟩
      refine ⟨?_,hdeg⟩
      by_contra hout
      exact (not_lt_of_ge hdeg) (h a ⟨ha,hout⟩)

theorem thickening_polymatroidal_iff_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔ a.degree < d+q := by
  rw [thickening_polymatroidal_iff_closed hB hanti hl hd,
    thickening_eq_closed_iff_hole_bound hB hl hd]
  exact ⟨fun h => h a ha,fun h b hb => (hmax b hb).trans_lt h⟩

theorem least_polymatroidal_thickening [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hda : d ≤ a.degree) :
    IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (a.degree+1-d) := by
  constructor
  · exact (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax _).mpr (by omega)
  · intro q hq
    have h := (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax q).mp hq
    omega

end Characterizations

end
end CheckedCharacterizationsSource88

/-! ## Source: Characterizations.Strands.FiniteHoles -/
section CheckedCharacterizationsSource89

/-! # Exact regularity bounds from a finite collection of missing monomials -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma chains_le_of_faces_at_degree {K L : Finset V → Prop} (i : ℕ)
    (h : ∀ s, K s → s.card = i → L s) : Chains (k := k) K i ≤ Chains L i := by
  apply Submodule.span_mono
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact ⟨s, ⟨h s hs hc, hc⟩, rfl⟩

lemma polymatroidal_faces_exact_off_linear (B : Family V) (hB : B.Nonempty)
    (d : ℕ) (hdeg : Equigenerated B d) (hpoly : IsPolymatroidal B)
    (a : Exponent V) (i : ℕ) (hoff : a.degree ≠ d+i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  by_contra hex
  have hn := (nonzeroHomology_iff_not_exactIn _ _).mpr hex
  let g := canonicalRank B hB d hdeg hpoly
  have hr : rankBases g = B := rankBases_canonical B hB d hdeg hpoly
  have hn' : NonzeroHomology (k := k) (koszulFaces (rankBases g) a) i := by
    simpa only [hr] using hn
  have hm := (koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i).mp hn'
  have hd := ((mem_rankShiftFamily_iff g i a).mp hm).1
  have hg : g Finset.univ = d := by
    change upperRank B Finset.univ = d
    obtain ⟨b, hb, he⟩ := upperRank_attained hB Finset.univ
    simpa only [subsetSum_univ, hdeg b hb] using he.symm
  exact hoff (by simpa only [hg] using hd)

lemma exactIn_of_finite_holes (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (a : Exponent V) (i : ℕ) (hlarge : t+i+1 < a.degree)
    (hC : ExactIn (k := k) (koszulFaces C a) i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  intro z hz hc
  have hzC : z ∈ Chains (koszulFaces C a) i :=
    chains_mono (fun s hs => ⟨hs.1, hincl _ hs.2⟩) i hz
  obtain ⟨y, hy, he⟩ := hC z hzC hc
  refine ⟨y, ?_, he⟩
  apply chains_le_of_faces_at_degree (i+1) (K := koszulFaces C a) _ hy
  intro s hs hcard
  refine ⟨hs.1, ?_⟩
  by_contra hnot
  have hb := hholes (a-faceExponent s) hs.2 hnot
  have hd := degree_sub_faceExponent hs.1
  omega

lemma finite_holes_betti_degree_bound (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (hC : C.Nonempty) (d : ℕ) (hdeg : Equigenerated C d)
    (hpoly : IsPolymatroidal C) (hd : d ≤ t+1)
    (a : Exponent V) (i : ℕ) (hbeta : bettiNumber (k := k) B a i ≠ 0) :
    a.degree ≤ t+i+1 := by
  by_contra hle
  have hl : t+i+1 < a.degree := by omega
  have hnonzero := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero hbeta)
  have hnot := (nonzeroHomology_iff_not_exactIn _ _).mp hnonzero
  apply hnot (exactIn_of_finite_holes B C hincl t hholes a i hl _)
  exact polymatroidal_faces_exact_off_linear C hC d hdeg hpoly a i (by omega)

end Characterizations.Strands

end
end CheckedCharacterizationsSource89

/-! ## Source: Characterizations.Regularity -/
section CheckedCharacterizationsSource90

/-! # Genuine Tor regularity of a minimal local obstruction -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The maximum defining Castelnuovo–Mumford regularity: all actual derived-Tor
degrees are bounded by r+i, and that bound occurs. -/
def IsTorRegularity (B : Family V) (r : ℕ) : Prop :=
  (∀ i a, bettiNumber (k := k) B a i ≠ 0 → a.degree ≤ r+i) ∧
    ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧ a.degree = r+i

theorem torRegularity_unique {B : Family V} {r s : ℕ}
    (hr : IsTorRegularity (k := k) B r) (hs : IsTorRegularity (k := k) B s) : r = s := by
  obtain ⟨i,a,ha,hda⟩ := hr.2
  obtain ⟨j,b,hb,hdb⟩ := hs.2
  have h₁ := hs.1 i a ha
  have h₂ := hr.1 j b hb
  omega

theorem totalBettiNumber_pos_iff (B : Family V) (i j : ℕ) :
    0 < Strands.totalBettiNumber (k := k) B i j ↔
      ∃ a, a.degree = j ∧ 0 < bettiNumber (k := k) B a i := by
  rw [Strands.totalBettiNumber, Finset.sum_pos_iff]
  simp

/-- The multigraded maximum agrees exactly with the usual total-degree formula. -/
theorem torRegularity_iff_total (B : Family V) (r : ℕ) :
    IsTorRegularity (k := k) B r ↔
      (∀ i j, 0 < Strands.totalBettiNumber (k := k) B i j → j ≤ r+i) ∧
        ∃ i j, 0 < Strands.totalBettiNumber (k := k) B i j ∧ j = r+i := by
  constructor
  · rintro ⟨hu,⟨i,a,ha,hda⟩⟩
    refine ⟨?_,i,a.degree,(totalBettiNumber_pos_iff B i _).mpr
      ⟨a,rfl,Nat.pos_of_ne_zero ha⟩,hda⟩
    intro i j hij
    obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
    exact had ▸ hu i a (Nat.ne_of_gt ha)
  · rintro ⟨hu,⟨i,j,hij,hj⟩⟩
    refine ⟨?_,?_⟩
    · intro i a ha
      exact hu i a.degree ((totalBettiNumber_pos_iff B i _).mpr ⟨a,rfl,Nat.pos_of_ne_zero ha⟩)
    · obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
      exact ⟨i,a,Nat.ne_of_gt ha,had.trans hj⟩

theorem generator_bettiNumber_pos {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ B) : 0 < bettiNumber (k := k) B a 0 := by
  rw [bettiNumber_pos_iff_faces]
  apply nonzeroHomology_zero_of_only_empty
  · exact ⟨by simp,by simpa using (show Contains B a from ⟨a,ha,le_rfl⟩)⟩
  · intro s hs
    obtain ⟨b,hb,hba⟩ := hs.2
    have hdeg := degree_mono hba
    have he := Strands.degree_sub_faceExponent hs.1
    rw [hd b hb] at hdeg
    rw [hd a ha] at he
    exact Finset.card_eq_zero.mp (by omega)

theorem polymatroidal_torRegularity {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hp : IsPolymatroidal B) :
    IsTorRegularity (k := k) B d := by
  constructor
  · intro i a ha
    have he : a.degree = d+i := by
      by_contra hn
      have hex := Strands.polymatroidal_faces_exact_off_linear (k := k) B hB d hd hp a i hn
      have hh := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero ha)
      exact ((nonzeroHomology_iff_not_exactIn _ _).mp hh) hex
    exact he.le
  · obtain ⟨a,ha⟩ := hB
    exact ⟨0,a,Nat.ne_of_gt (generator_bettiNumber_pos hd ha),by simpa using hd a ha⟩

theorem torRegularity_of_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hmul : ∀ j, Contains B (a+Finsupp.single j 1)) :
    IsTorRegularity (k := k) B (a.degree+1) := by
  have hda : d ≤ a.degree := by
    have h := ha.1 Finset.univ
    simpa only [lowerRank_univ_of_equigenerated hB hd, subsetSum_univ] using h
  constructor
  · intro i b hb
    have h := Strands.finite_holes_betti_degree_bound (k := k) B
      (lowerBaseFamily (lowerRank B) d) (fun c hc =>
        (contains_canonicalLowerBases_iff hB hl hd c).mpr
          (fun U => by
            obtain ⟨z,hz,hzc⟩ := hc
            exact (lowerRank_le hz U).trans (Finset.sum_le_sum (fun j _ => hzc j))))
      a.degree (fun c hc hout => hmax c
        ⟨(contains_canonicalLowerBases_iff hB hl hd c).mp hc,hout⟩)
      (hB.mono (subset_lowerBaseFamily hd)) d (lowerBaseFamily_equigenerated _ _)
      (canonicalLowerBases_polymatroidal hB hl hd) (by omega) b i hb
    omega
  · have hc : Fintype.card V = (Fintype.card V-1)+1 := by
      have hpos := Fintype.card_pos (α := V)
      omega
    refine ⟨Fintype.card V-1,a+faceExponent Finset.univ,?_,?_⟩
    · rw [Strands.socle_bettiNumber_eq_one B a ha.2 hmul _ hc]
      exact one_ne_zero
    · rw [map_add, Strands.degree_faceExponent, Finset.card_univ]
      omega

theorem locallyEquigenerated_of_proper_polymatroidal {B : Family V} {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    LocallyEquigenerated B := by
  intro U
  by_cases hU : U = Finset.univ
  · subst U
    rw [localize_univ_of_antichain hd.antichain]
    exact ⟨d,hd⟩
  · exact (hloc U ((Finset.subset_univ U).ssubset_of_ne hU)).1

theorem holeSet_nonempty_of_nonclosed {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    (holeSet B).Nonempty := by
  have hnot : ¬ lowerBaseFamily (lowerRank B) d ⊆ B := fun h =>
    hne (Finset.Subset.antisymm (subset_lowerBaseFamily hd) h)
  obtain ⟨a,haJ,haB⟩ := Finset.not_subset.mp hnot
  obtain ⟨had,hlo⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  exact ⟨a,hlo,fun h => haB ((hd.mem_iff_contains had).mpr h)⟩

/-- Proposition 4.1: the exact maximum hole degree, actual Tor regularity, and
the least maximal-ideal power that becomes polymatroidal. -/
theorem minimal_local_obstruction {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    ∃ t : ℕ, (∃ a ∈ holeSet B, a.degree = t) ∧
      (∀ b ∈ holeSet B, b.degree ≤ t) ∧ d ≤ t ∧
      IsTorRegularity (k := k) B (t+1) ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (t+1-d) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  obtain ⟨a,ha,hmax,hda,hmul⟩ := exists_top_hole hB hd hloc (holeSet_nonempty_of_nonclosed hd hne)
  haveI : Nonempty V := by
    by_contra hn
    haveI : IsEmpty V := not_nonempty_iff.mp hn
    obtain ⟨b,hb⟩ := hB
    exact ha.2 ⟨b,hb,(Subsingleton.elim b a).le⟩
  exact ⟨a.degree,⟨a,ha,rfl⟩,hmax,hda,torRegularity_of_top_hole hB hl hd ha hmax hmul,
    least_polymatroidal_thickening hB hd.antichain hl hd ha hmax hda⟩

end Characterizations

end
end CheckedCharacterizationsSource90

/-! ## Source: Characterizations.TotalTests -/
section CheckedCharacterizationsSource91

/-! # Total-degree Tor formulations of the homological tests

The total-degree piece is the sum, inside genuine derived Tor, of its actual
multigraded submodules of that total degree.  Vanishing is proved equivalent
both to fine-degree vanishing and to the finite sum of Betti dimensions.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def totalDegreeTor (B : Family V) (i j : ℕ) :=
  ⨆ (a : Exponent V) (_ : a.degree = j), gradedTor (k := k) B a i

theorem totalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j = ⊥ ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  simp only [totalDegreeTor,iSup_eq_bot,bettiNumber,Submodule.finrank_eq_zero]

theorem iSup_totalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, totalDegreeTor (k := k) B i j) = ⊤ := by
  rw [← iSup_gradedTor B i]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro a
    apply iSup_le
    intro _
    exact le_iSup (fun a => gradedTor (k := k) B a i) a
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.degree (le_iSup_of_le a (le_iSup_of_le rfl le_rfl))

theorem totalBettiNumber_eq_zero_iff (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  constructor
  · intro hz a ha
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hh := (totalBettiNumber_pos_iff B i j).mpr ⟨a,ha,hp⟩
    omega
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hp
    obtain ⟨a,ha,hpa⟩ := (totalBettiNumber_pos_iff B i j).mp hp
    have hz := h a ha
    omega

theorem totalBettiNumber_zero_iff_totalDegreeTor (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  (totalBettiNumber_eq_zero_iff B i j).trans (totalDegreeTor_eq_bot_iff B i j).symm

theorem retainedLinearThrough_iff_totalBetti (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔
      ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
        Strands.totalBettiNumber (k := k) (localFamily B U) i j = 0 := by
  constructor
  · intro h i hi j hj
    apply (totalBettiNumber_eq_zero_iff _ _ _).mpr
    intro a ha
    exact h a i hi (by rwa [ha])
  · intro h a i hi hoff
    exact (totalBettiNumber_eq_zero_iff _ _ _).mp (h i hi a.degree hoff) a rfl

def RetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    totalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem retainedLinearThrough_iff_totalTor (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔ RetainedTorLinearThrough (k := k) B U e t := by
  rw [retainedLinearThrough_iff_totalBetti]
  simp only [RetainedTorLinearThrough,totalBettiNumber_zero_iff_totalDegreeTor]

def TotalTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedTorLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

def TotalDegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (e-1))

def TotalDegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

/-- Theorem4.9 as literal vanishing of total-degree submodules of genuine
derived Tor over the retained-variable polynomial rings. -/
theorem polymatroidal_iff_triangular_totalTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TotalTriangularTests (k := k) B d := by
  rw [polymatroidal_iff_triangular (k := k) hB hd hd2]
  simp only [RetainedTriangularTests,TotalTriangularTests,retainedLinearThrough_iff_totalTor]

/-- The displayed Tor-vanishing statement of Theorem4.2. -/
theorem polymatroidal_iff_degree_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_tests (k := k) hB hanti]
  simp only [DegreeBoundedTests,TotalDegreeBoundedTests,retainedLinearThrough_iff_totalTor]

/-- The equivalent smaller cutoff from Theorem4.2, with actual total Tor. -/
theorem polymatroidal_iff_degree_dimension_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeDimensionBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_dimension_tests (k := k) hB hanti]
  simp only [DegreeDimensionBoundedTests,TotalDegreeDimensionBoundedTests,
    retainedLinearThrough_iff_totalTor]

end Characterizations

end
end CheckedCharacterizationsSource91

/-! ## Source: Characterizations.Strands.TotalDimension -/
section CheckedCharacterizationsSource92

/-! # Total Betti sums are dimensions of the actual total-degree derived-Tor submodules -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {k : Type u} [Field k]

lemma finrank_finset_sup_of_independent {ι M : Type*} [AddCommGroup M] [Module k M]
    (P : ι → Submodule k M) [∀ a, FiniteDimensional k (P a)]
    (h : iSupIndep P) (s : Finset ι) :
    Module.finrank k ↥(s.sup P) = ∑ a ∈ s, Module.finrank k (P a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hd : Disjoint (P a) (s.sup P) := by
      rw [Finset.sup_eq_iSup]
      exact h.disjoint_biSup (y := (s : Set ι)) ha
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (P a) (s.sup P)
    rw [hd.eq_bot, finrank_bot, add_zero, ih] at hh
    exact hh

variable {V : Type u} [Fintype V] [LinearOrder V]

theorem totalDegreeTor_eq_finset_sup (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j =
      ((Finsupp.finite_of_degree_eq (σ := V) j).toFinset).sup
        (fun a => gradedTor (k := k) B a i) := by
  rw [Finset.sup_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact le_iSup_of_le a (le_iSup_of_le (by simpa using ha) le_rfl)

theorem totalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (totalDegreeTor (k := k) B i j) := by
  rw [totalDegreeTor_eq_finset_sup]
  infer_instance

/-- The usual total-degree numerical Betti number, with its dimension meaning
proved from the independent internal multigrading of genuine derived Tor. -/
theorem finrank_totalDegreeTor (B : Family V) (i j : ℕ) :
    Module.finrank k (totalDegreeTor (k := k) B i j) =
      totalBettiNumber (k := k) B i j := by
  rw [totalDegreeTor_eq_finset_sup]
  exact finrank_finset_sup_of_independent (fun a => gradedTor (k := k) B a i)
    (gradedTor_independent B i) _

end Characterizations.Strands

end
end CheckedCharacterizationsSource92

/-! ## Source: Characterizations.Strands.DeletedGeneratorTheorem -/
section CheckedCharacterizationsSource93

/-! # The complete deleted-generator proposition, including its localized ideals -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem deletedVeronese_proper_localization (a : Exponent V) (ha : 2 ≤ a.support.card)
    (U : Finset V) (hU : U ⊂ Finset.univ) :
    monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_of_ssubset hU
  rw [monomialLocalization_eq]
  have he : localFamily (deletedVeronese a) U = {0} :=
    Isolators.localFamily_eq_zero_of_purePower ∅ U a ha j (Finset.notMem_empty _) hj
  rw [he, Ideal.eq_top_iff_one]
  have h : MvPolynomial.monomial (0 : Exponent U) (1 : k) ∈
      monomialIdeal k ({0} : Family U) := (monomial_mem_iff _ _).mpr
        ⟨0, Finset.mem_singleton_self _, le_rfl⟩
  simpa using h

/-- Proposition 4.3: every proper localization is the unit ideal, every
nonlinear fine Betti entry is exactly zero or one as stated, and the total
nonlinear strand has the exact binomial coefficient (including out-of-range zero). -/
theorem deleted_generator_nonlinear_strand (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ U : Finset V, U ⊂ Finset.univ →
      monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤) ∧
    (∀ i b, b.degree ≠ a.degree+i →
      bettiNumber (k := k) (deletedVeronese a) b i =
        if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
          then 1 else 0) ∧
    (∀ i, totalBettiNumber (k := k) (deletedVeronese a) i (a.degree+i+1) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0) ∧
    (∀ i j, j ≠ a.degree+i → j ≠ a.degree+i+1 →
      totalBettiNumber (k := k) (deletedVeronese a) i j = 0) := by
  refine ⟨deletedVeronese_proper_localization a ha, ?_,
    deletedVeronese_total_nonlinear a ha, deletedVeronese_total_other a ha⟩
  intro i b hb
  simpa only [mem_exceptionalDegrees] using deletedVeronese_betti_off_linear a b ha i hb

theorem deletedVeronese_full_support (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (hfull : a.support = Finset.univ) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    bettiNumber (k := k) (deletedVeronese a) b i =
      if i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ then 1 else 0 := by
  rw [deletedVeronese_betti_off_linear a b ha i hoff]
  have he : b ∈ exceptionalDegrees a i ↔
      i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ := by
    rw [mem_exceptionalDegrees]
    constructor
    · rintro ⟨T, hT, hc, he⟩
      have hTu : T = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) (hfull ▸ hT)
      subst T
      exact ⟨by simpa using hc.symm, he⟩
    · rintro ⟨hc, he⟩
      exact ⟨Finset.univ, Finset.subset_univ _, by simpa using hc.symm, he⟩
  simp only [he]

end Characterizations.Strands

end
end CheckedCharacterizationsSource93

/-! ## Source: Characterizations.DerivedTorOrder -/
section CheckedCharacterizationsSource94

/-! # The manuscript's `Tor(I,k)` and its genuine homogeneous submodules

The existing Koszul construction resolves the residue module in the first tensor
factor. Tensor braiding identifies that derived functor with Mathlib's `Tor(I,k)`,
which resolves the same residue module in the second factor. This does not use or
assume a balance theorem between two different projective resolutions.
-/
noncomputable section
namespace Characterizations
open CategoryTheory CategoryTheory.MonoidalCategory CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

def tensorBraidingDerivedIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (((tensoringRight _).obj M).leftDerived i) ≅
      (((tensoringLeft _).obj M).leftDerived i) where
  hom := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).inv i
  inv := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight M).hom i
  hom_inv_id := by
    rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id, NatTrans.leftDerived_id]

/-- The exact chain isomorphism inducing the change of tensor order. -/
def tensorBraidingChainIso (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ) :
    (((tensoringRight _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ≅
      (((tensoringLeft _).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M).symm
    (ComplexShape.down ℕ)).app P

/-- In each chain degree the map merely switches the two tensor factors;
in particular both their polynomial and exterior degrees are retained. -/
@[simp] theorem tensorBraidingChainIso_tmul
    (M : ModuleCat.{u} (MvPolynomial V k))
    (P : ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ)
    (j : ℕ) (x : P.X j) (m : M) :
    (tensorBraidingChainIso M P).hom.f j (x ⊗ₜ[MvPolynomial V k] m) =
      m ⊗ₜ[MvPolynomial V k] x := rfl

/-- Compatibility with the actual homology map of the displayed chain braiding. -/
theorem tensorBraidingDerivedIso_eq_homology
    {X : ModuleCat.{u} (MvPolynomial V k)} (P : ProjectiveResolution X)
    (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    (tensorBraidingDerivedIso M i).hom.app X =
      (P.isoLeftDerivedObj ((tensoringRight _).obj M) i).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
          (tensorBraidingChainIso M P.complex).hom ≫
        (P.isoLeftDerivedObj ((tensoringLeft _).obj M) i).inv :=
  P.leftDerived_app_eq (BraidedCategory.tensorLeftIsoTensorRight M).inv i

/-- The manuscript's derived Tor with the actual coefficient ring carrying
the polynomial action by evaluation at zero. -/
def paperTor (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :=
  ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).obj
    (residueCoefficientModule (V := V) (k := k))

/-- Canonical agreement with the exact argument ordering `Tor_i(M,k)`. -/
def polynomialTorOrderIso (M : ModuleCat.{u} (MvPolynomial V k)) (i : ℕ) :
    finitePolynomialTor i M ≅ paperTor M i :=
  (tensorBraidingDerivedIso M i).app
      (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) ≪≫
    ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).mapIso residueCoefficientIso

def coefficientTorOrderIso (B : Family V) (i : ℕ) :=
  (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapIso
    (polynomialTorOrderIso (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i)

end Ring

section Field
variable [Field k]

/-- The fine-degree piece transported through the canonical derived tensor braiding. -/
def paperGradedTor (B : Family V) (a : Exponent V) (i : ℕ) :=
  (gradedTor (k := k) B a i).map (coefficientTorOrderIso (k := k) B i).hom.hom

/-- The total-degree piece inside Mathlib's literal `Tor_i(I,k)`. -/
def paperTotalDegreeTor (B : Family V) (i j : ℕ) :=
  (totalDegreeTor (k := k) B i j).map (coefficientTorOrderIso (k := k) B i).hom.hom

theorem paperTotalDegreeTor_eq_sum (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j =
      ⨆ (a : Exponent V) (_ : a.degree = j), paperGradedTor (k := k) B a i := by
  simp only [paperTotalDegreeTor, totalDegreeTor, Submodule.map_iSup, paperGradedTor]

theorem paperGradedTor_finrank (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.finrank k (paperGradedTor (k := k) B a i) = bettiNumber (k := k) B a i :=
  (coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _

theorem paperGradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (paperGradedTor (k := k) B a i) := by
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (gradedTor (k := k) B a i)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_finrank (B : Family V) (i j : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) B i j) =
      Strands.totalBettiNumber (k := k) B i j := by
  exact ((coefficientTorOrderIso (k := k) B i).toLinearEquiv.finrank_map_eq _).trans
    (Strands.finrank_totalDegreeTor B i j)

theorem paperTotalDegreeTor_finite (B : Family V) (i j : ℕ) :
    FiniteDimensional k (paperTotalDegreeTor (k := k) B i j) := by
  letI := Strands.totalDegreeTor_finite (k := k) B i j
  let e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv.submoduleMap
    (totalDegreeTor (k := k) B i j)
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

theorem paperTotalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    paperTotalDegreeTor (k := k) B i j = ⊥ ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  Submodule.map_eq_bot_iff (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)

/-- No part of `Tor(I,k)` is lost by the transported total grading. -/
theorem iSup_paperTotalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, paperTotalDegreeTor (k := k) B i j) = ⊤ := by
  simp only [paperTotalDegreeTor, ← Submodule.map_iSup, iSup_totalDegreeTor]
  exact (Submodule.map_eq_top_iff
    (e := (coefficientTorOrderIso (k := k) B i).toLinearEquiv)).mpr rfl

/-- The paper's initial-segment condition with its literal derived tensor order. -/
def PaperRetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    paperTotalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem paperRetainedTorLinearThrough_iff (B : Family V) (U : Finset V) (e t : ℕ) :
    PaperRetainedTorLinearThrough (k := k) B U e t ↔
      RetainedTorLinearThrough (k := k) B U e t := by
  simp only [PaperRetainedTorLinearThrough, RetainedTorLinearThrough,
    paperTotalDegreeTor_eq_bot_iff]

/-- Theorem 4.2 with actual `Tor_i(I_U,k)` over `k[U]`. -/
theorem polymatroidal_iff_degree_tests_paperTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (e-1)) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_tests_totalTor hB hanti

/-- The equivalent degree-and-dimension cutoff in Theorem 4.2. -/
theorem polymatroidal_iff_degree_dimension_tests_paperTor {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) : IsPolymatroidal B ↔
    ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → PaperRetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_degree_dimension_tests_totalTor hB hanti

/-- Theorem 4.9 in exactly the manuscript's derived tensor order. -/
theorem polymatroidal_iff_triangular_paperTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) : IsPolymatroidal B ↔
    ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      ∃ e, Equigenerated (localFamily B U) e ∧
        (0 < e → PaperRetainedTorLinearThrough (k := k) B U e
          (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1)))) := by
  simp only [paperRetainedTorLinearThrough_iff]
  exact polymatroidal_iff_triangular_totalTor hB hd hd2

/-- Proposition 4.3's total nonlinear strand as a dimension inside `Tor_i(I,k)`. -/
theorem deleted_generator_paperTor_finrank (a : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) :
    Module.finrank k (paperTotalDegreeTor (k := k) (deletedVeronese a) i (a.degree+i+1)) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0 := by
  rw [paperTotalDegreeTor_finrank]
  exact Strands.deletedVeronese_total_nonlinear a ha i

/-- Proposition 4.3's complete nonlinear fine strand inside literal `Tor_i(I,k)`. -/
theorem deleted_generator_paperGradedTor_finrank (a b : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    Module.finrank k (paperGradedTor (k := k) (deletedVeronese a) b i) =
      if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
        then 1 else 0 := by
  rw [paperGradedTor_finrank]
  exact (Strands.deleted_generator_nonlinear_strand (k := k) a ha).2.1 i b hoff

end Field
end Characterizations

end
end CheckedCharacterizationsSource94

/-! ## Source: Characterizations.GradedRevlex -/
section CheckedCharacterizationsSource95

/-! # Graded reverse lexicographic order as a genuine Mathlib monomial order -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def GradedReverse (V : Type*) := Exponent V

instance : AddCommMonoid (GradedReverse V) := inferInstanceAs (AddCommMonoid (Exponent V))

def gradedReverseEquiv : Exponent V ≃+ GradedReverse V := AddEquiv.refl _

def gradedReverseUnderlying (a : GradedReverse V) : Exponent V := a

section Ordered
variable [LinearOrder V]

def gradedReverseKey (a : GradedReverse V) : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) :=
  toLex ((gradedReverseUnderlying a).degree, OrderDual.toDual (toColex (gradedReverseUnderlying a)))

theorem gradedReverseKey_injective : Function.Injective (gradedReverseKey (V := V)) := by
  intro a b he
  exact congrArg (fun x : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) =>
    (ofColex (OrderDual.ofDual ((ofLex x).2)) : Exponent V)) he

instance : LinearOrder (GradedReverse V) :=
  LinearOrder.lift' gradedReverseKey gradedReverseKey_injective

theorem gradedReverse_lt_iff (a b : GradedReverse V) :
    a < b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) < toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a < gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]

theorem gradedReverse_le_iff (a b : GradedReverse V) :
    a ≤ b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) ≤ toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a ≤ gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual]

instance : IsOrderedAddMonoid (GradedReverse V) where
  add_le_add_left a b h c := by
    rw [gradedReverse_le_iff] at h ⊢
    change (gradedReverseUnderlying a + gradedReverseUnderlying c).degree < (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∨
      ((gradedReverseUnderlying a + gradedReverseUnderlying c).degree = (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∧
        toColex (gradedReverseUnderlying b + gradedReverseUnderlying c) ≤ toColex (gradedReverseUnderlying a + gradedReverseUnderlying c))
    simpa only [map_add, toColex_add, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

theorem gradedReverse_degree_mono :
    Monotone (fun a : GradedReverse V => (gradedReverseUnderlying a).degree) := by
  intro a b h
  rcases (gradedReverse_le_iff a b).mp h with h | h
  · exact h.le
  · exact h.1.le

instance : WellFoundedLT (GradedReverse V) := by
  apply WellFounded.wellFoundedLT_iff_exists_minimal.mpr
  intro S hS
  obtain ⟨a, ha⟩ := hS
  let T : Set (GradedReverse V) :=
    {b | b ∈ S ∧ (gradedReverseUnderlying b).degree ≤ (gradedReverseUnderlying a).degree}
  have hfin : T.Finite := by
    change {b : Exponent V | b ∈ S ∧ b.degree ≤ (gradedReverseUnderlying a).degree}.Finite
    apply (Set.finite_Iic (constExponent (gradedReverseUnderlying a).degree)).subset
    intro b hb i
    exact (coordinate_le_degree b i).trans hb.2
  obtain ⟨b, hb, hmin⟩ := hfin.exists_minimal ⟨a, ha, le_rfl⟩
  refine ⟨b, hb.1, ?_⟩
  intro c hc hcb
  exact hmin ⟨hc, (gradedReverse_degree_mono hcb).trans hb.2⟩ hcb

def gradedRevlexMonomialOrder : MonomialOrder V where
  syn := GradedReverse V
  toSyn := gradedReverseEquiv
  toSyn_monotone a b hab := by
    apply (gradedReverse_le_iff _ _).mpr
    have hd := degree_mono hab
    rcases hd.lt_or_eq with hlt | he
    · exact Or.inl hlt
    · have hab' := eq_of_le_of_degree_eq hab he
      exact Or.inr ⟨he, by rw [hab']⟩

end Ordered

def variableGradedRevlexOrder (o : VariableOrder V) : MonomialOrder V :=
  letI := variableLinearOrder o
  gradedRevlexMonomialOrder

theorem variableGradedRevlexOrder_decreasing_iff (o : VariableOrder V)
    (a b : Exponent V) (hd : a.degree = b.degree) :
    (variableGradedRevlexOrder o).toSyn b < (variableGradedRevlexOrder o).toSyn a ↔
      variableRevlex o a b := by
  letI := variableLinearOrder o
  change gradedReverseEquiv b < gradedReverseEquiv a ↔ _
  rw [gradedReverse_lt_iff]
  change (b.degree < a.degree ∨ b.degree = a.degree ∧ toColex a < toColex b) ↔ _
  simp only [hd, lt_self_iff_false, true_and, false_or, Finsupp.Colex.lt_iff]
  exact ⟨fun ⟨i, he, hi⟩ => ⟨i, hi, he⟩, fun ⟨i, hi, he⟩ => ⟨i, he, hi⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource95

/-! ## Source: Characterizations.Strands.FiniteLength -/
section CheckedCharacterizationsSource96

/-! # Actual ideal quotients with finitely many missing monomials have finite length -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The actual module quotient J/(I∩J), written without choosing a complement. -/
abbrev idealDifferenceQuotient (B C : Family V) :=
  (monomialIdeal k C) ⧸ Submodule.comap (monomialIdeal k C).subtype (monomialIdeal k B)

theorem idealDifferenceQuotient_finite (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    Module.Finite k (idealDifferenceQuotient (k := k) B C) := by
  let J := monomialIdeal k C
  let N : Submodule (MvPolynomial V k) J := Submodule.comap J.subtype (monomialIdeal k B)
  let Q := J ⧸ N
  let H := {a : Exponent V // Contains C a ∧ ¬Contains B a}
  letI : Fintype H := hholes.fintype
  let q : J →ₗ[k] Q := N.mkQ.restrictScalars k
  let hvec : H → Q := fun a => q (monomialBasis C ⟨a.val, a.property.1⟩)
  let f : (H →₀ k) →ₗ[k] Q := Finsupp.linearCombination k hvec
  have hbas (a : {a : Exponent V // Contains C a}) :
      q (monomialBasis C a) ∈ LinearMap.range f := by
    by_cases ha : Contains B a.val
    · have hz : q (monomialBasis C a) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        change (monomialBasis C a).val ∈ monomialIdeal k B
        rw [monomialBasis_val, monomial_mem_iff]
        exact ha
      rw [hz]
      exact Submodule.zero_mem _
    · let a' : H := ⟨a.val, a.property, ha⟩
      refine ⟨Finsupp.single a' 1, ?_⟩
      simp only [f, Finsupp.linearCombination_single, one_smul]
      rfl
  have hspan (x : J) : q x ∈ LinearMap.range f := by
    have hx : x ∈ Submodule.span k (Set.range (monomialBasis (k := k) C)) := by
      rw [(monomialBasis (k := k) C).span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hbas a
    | zero => simpa using (Submodule.zero_mem (LinearMap.range f))
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih => simpa using Submodule.smul_mem _ c ih
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := N.mkQ_surjective z
    obtain ⟨y, hy⟩ := hspan x
    exact ⟨y, hy.trans hx⟩
  exact Module.Finite.of_surjective f hf

theorem idealDifferenceQuotient_finiteLength (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    IsFiniteLength (MvPolynomial V k) (idealDifferenceQuotient (k := k) B C) := by
  letI := idealDifferenceQuotient_finite (k := k) B C hholes
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

end Characterizations.Strands

end
end CheckedCharacterizationsSource96

/-! ## Source: Characterizations.MinimalLocal -/
section CheckedCharacterizationsSource97

/-! # Proposition 4.1 with the actual integral closure and actual finite-length quotient -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem thickening_zero (B : Family V) : thickening B 0 = B := by
  ext a
  constructor
  · intro ha
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
    have hc0 : c = 0 := (Finsupp.degree_eq_zero_iff c).mp ((mem_degreeFamily 0 c).mp hc)
    simpa only [hc0,add_zero] using hb
  · intro ha
    exact Finset.mem_image.mpr ⟨(a,0),Finset.mem_product.mpr ⟨ha,by simp⟩,by simp⟩

theorem minimal_local_closure_finiteLength {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) ∧
      monomialIdeal k B ≤ monomialIdeal k (lowerBaseFamily (lowerRank B) d) ∧
      ({f : MvPolynomial V k | IntegralOverIdeal (monomialIdeal k B) f} =
        (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k))) ∧
      IsFiniteLength (MvPolynomial V k)
        (Strands.idealDifferenceQuotient (k := k) B (lowerBaseFamily (lowerRank B) d)) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  refine ⟨canonicalLowerBases_polymatroidal hB hl hd,?_,
    integralClosure_set_eq hB hd.antichain hl hd,?_⟩
  · apply Ideal.span_mono
    rintro f ⟨a,ha,rfl⟩
    exact ⟨a,subset_lowerBaseFamily hd ha,rfl⟩
  · apply Strands.idealDifferenceQuotient_finiteLength
    have he : {a : Exponent V | Contains (lowerBaseFamily (lowerRank B) d) a ∧ ¬Contains B a} =
        holeSet B := by
      ext a
      simp only [Set.mem_setOf_eq,contains_canonicalLowerBases_iff hB hl hd,holeSet]
    rw [he]
    exact holeSet_finite hB hd hloc

/-- The "in particular" statement in4.1, including the integrally closed case
where the least power and regularity difference are both zero. -/
theorem least_polymatroidal_power_eq_regularity_difference {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r-d) := by
  by_cases hclosed : B = lowerBaseFamily (lowerRank B) d
  · have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
    have hp : IsPolymatroidal B := by
      conv_rhs => rw [hclosed]
      exact canonicalLowerBases_polymatroidal hB hl hd
    refine ⟨d,polymatroidal_torRegularity hB hd hp,?_⟩
    simp only [Nat.sub_self]
    exact ⟨by simpa only [Set.mem_setOf_eq,thickening_zero] using hp,fun _ _ => Nat.zero_le _⟩
  · obtain ⟨t,ht,hmax,hdt,hreg,hq⟩ := minimal_local_obstruction (k := k) hB hd hloc hclosed
    exact ⟨t+1,hreg,hq⟩

end Characterizations

end
end CheckedCharacterizationsSource97

/-! ## Source: Characterizations.Resolution.Specialize -/
section CheckedCharacterizationsSource98

/-! Exact specialization of actual finite free matrices along a regular quotient. -/

noncomputable section
namespace Characterizations.Resolution
open Classical Finset
universe u v w z
variable {R S : Type u} [CommRing R] [CommRing S]
  {J : Type v} {L : Type w} {M : Type z}
  [Fintype J] [Fintype L] [Fintype M]

lemma free_apply_eq_sum (f : (J → R) →ₗ[R] (L → R)) (x : J → R) (a : L) :
    f x a = ∑ b, x b * f (Pi.single b 1) a := by
  have hx : x = ∑ b, x b • Pi.single b (1 : R) := by
    funext b
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

def specialize (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) :
    (J → S) →ₗ[S] (L → S) where
  toFun x a := ∑ b, x b * φ (f (Pi.single b 1) a)
  map_add' x y := by ext a; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext a; simp [mul_assoc, Finset.mul_sum]

lemma specialize_apply (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (x : J → S) (a : L) : specialize φ f x a =
      ∑ b, x b * φ (f (Pi.single b 1) a) := rfl

@[simp] lemma specialize_single (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (b : J) (a : L) : specialize φ f (Pi.single b 1) a = φ (f (Pi.single b 1) a) := by
  simp [specialize, Pi.single_apply]

lemma specialize_map (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) (x : J → R) :
    specialize φ f (fun j => φ (x j)) = fun a => φ (f x a) := by
  ext a
  rw [specialize_apply, free_apply_eq_sum]
  simp

lemma specialize_exact (φ : R →+* S) (hφ : Function.Surjective φ) (t : R)
    (ht : φ t = 0) (hker : ∀ a, φ a = 0 → ∃ b, a = t * b)
    (f : (J → R) →ₗ[R] (L → R)) (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g)
    (hsat : ∀ y : M → R, t • y ∈ LinearMap.range g → y ∈ LinearMap.range g) :
    LinearMap.range (specialize φ f) = LinearMap.ker (specialize φ g) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : J → R, (fun j => φ (y j)) = x := by
      choose y hy using fun j => hφ (x j)
      exact ⟨y, funext hy⟩
    rw [← hy, specialize_map, LinearMap.mem_ker, specialize_map]
    have hf : g (f y) = 0 := LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f y)
    ext a
    simp [hf]
  · intro hz
    obtain ⟨x, hx⟩ : ∃ x : L → R, (fun j => φ (x j)) = z := by
      choose x hx using fun j => hφ (z j)
      exact ⟨x, funext hx⟩
    have hg : ∀ a, φ (g x a) = 0 := by
      have h := LinearMap.mem_ker.mp hz
      rw [← hx, specialize_map] at h
      exact congrFun h
    choose y hy using fun a => hker (g x a) (hg a)
    have hgy : g x = t • y := by ext a; exact hy a
    obtain ⟨w, hw⟩ := hsat y ⟨x, hgy⟩
    have hcycle : x - t • w ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hw, hgy, sub_self]
    obtain ⟨q, hq⟩ := hex.symm ▸ hcycle
    refine ⟨fun j => φ (q j), ?_⟩
    rw [specialize_map, hq]
    ext a
    simpa [ht] using congrFun hx a

lemma saturated_range_of_exact (f : (J → R) →ₗ[R] (L → R))
    (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g) (t : R)
    (ht : Function.Injective (fun a : R => t * a)) :
    ∀ y : L → R, t • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  intro y hy
  rw [hex, LinearMap.mem_ker] at hy ⊢
  rw [map_smul] at hy
  ext a
  apply ht
  simpa using congrFun hy a

def scalarFree (f : (J → R) →ₗ[R] R) : (J → R) →ₗ[R] (Unit → R) :=
  LinearMap.pi (fun _ => f)

@[simp] lemma scalarFree_apply (f : (J → R) →ₗ[R] R) (x : J → R) (a : Unit) :
    scalarFree f x a = f x := rfl

@[simp] lemma scalarFree_ker (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (scalarFree f) = LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, scalarFree_apply, Pi.zero_apply, implies_true]
  exact ⟨fun h => h (), fun h _ => h⟩

def specializeScalar (φ : R →+* S) (f : (J → R) →ₗ[R] R) : (J → S) →ₗ[S] S :=
  (LinearMap.proj ()).comp (specialize φ (scalarFree f))

@[simp] lemma specializeScalar_single (φ : R →+* S) (f : (J → R) →ₗ[R] R) (b : J) :
    specializeScalar φ f (Pi.single b 1) = φ (f (Pi.single b 1)) := by
  exact specialize_single φ (scalarFree f) b ()

lemma specializeScalar_map (φ : R →+* S) (f : (J → R) →ₗ[R] R) (x : J → R) :
    specializeScalar φ f (fun j => φ (x j)) = φ (f x) :=
  congrFun (specialize_map φ (scalarFree f) x) ()

lemma specializeScalar_ker (φ : R →+* S) (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (specialize φ (scalarFree f)) =
      LinearMap.ker (specializeScalar φ f) := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  exact ⟨fun h => h (), fun h a => by cases a; exact h⟩

lemma specializeScalar_range (φ : R →+* S) (hφ : Function.Surjective φ)
    (f : (J → R) →ₗ[R] R) (I : Ideal R) (hf : LinearMap.range f = I) :
    LinearMap.range (specializeScalar φ f) = Ideal.map φ I := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,hz⟩ : ∃ z : J → R, (fun j => φ (z j)) = x := by
      choose z hz using fun j => hφ (x j)
      exact ⟨z,funext hz⟩
    rw [← hz,specializeScalar_map]
    exact Ideal.mem_map_of_mem φ (hf ▸ LinearMap.mem_range_self f z)
  · intro hy
    obtain ⟨z,hz,hzy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hy
    obtain ⟨x,hx⟩ := hf.symm ▸ hz
    refine ⟨fun j => φ (x j),?_⟩
    rw [specializeScalar_map,hx,hzy]

end Characterizations.Resolution

end
end CheckedCharacterizationsSource98

/-! ## Source: Characterizations.Resolution.DeleteVariable -/
section CheckedCharacterizationsSource99

/-! Removing a polynomial variable from a genuine linear free resolution. -/
noncomputable section
namespace Characterizations.Resolution
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [CommRing k]

lemma killCompl_homogeneous {W : Type u} (f : W → V) (hf : Function.Injective f)
    {p : MvPolynomial V k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (MvPolynomial.killCompl hf p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain f) ≠ 0 := by
    simpa only [MvPolynomial.coeff_killCompl] using ha
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain]
    using hp hcoeff

lemma killCompl_kernel_of_range {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (p : MvPolynomial V k) (hp : MvPolynomial.killCompl hf p = 0) :
    ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range f := by
      intro i hi
      apply (hrange i).mpr
      intro he
      subst i
      exact (Finsupp.mem_support_iff.mp hi) ha
    let b := a.comapDomain f hf.injOn
    have hb : b.mapDomain f = a := a.mapDomain_comapDomain f hf hs
    have hc := congrArg (fun q : MvPolynomial W k => q.coeff b) hp
    simpa [MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

abbrev Deleted (j : V) := {i : V // i ≠ j}

def deleteVariable (j : V) : MvPolynomial V k →ₐ[k] MvPolynomial (Deleted j) k :=
  MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective

lemma deleteVariable_surjective (j : V) : Function.Surjective (deleteVariable (k:=k) j) := by
  intro p
  exact ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.killCompl_rename_app _ _⟩

@[simp] lemma deleteVariable_X (j : V) : deleteVariable (k:=k) j (X j) = 0 := by
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
    Subtype.val_injective 1 (a := j)
  · simp
  · rintro ⟨i,hi⟩
    exact i.property hi

lemma deleteVariable_homogeneous (j : V) {p : MvPolynomial V k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (deleteVariable j p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain Subtype.val) ≠ 0 := by
    simpa only [deleteVariable, MvPolynomial.coeff_killCompl] using ha
  have h := hp hcoeff
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

lemma deleteVariable_kernel (j : V) (p : MvPolynomial V k)
    (hp : deleteVariable j p = 0) : ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range (Subtype.val : Deleted j → V) := by
      intro i hi
      have hne : i ≠ j := by
        intro he
        subst i
        exact (Finsupp.mem_support_iff.mp hi) ha
      exact ⟨⟨i,hne⟩,rfl⟩
    let b := a.comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective.injOn
    have hb : b.mapDomain Subtype.val = a :=
      a.mapDomain_comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective hs
    have hc := congrArg (fun q : MvPolynomial (Deleted j) k => q.coeff b) hp
    simpa [deleteVariable, MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

lemma monomialIdeal_variable_saturated [Fintype V] [DecidableEq V]
    (B : Family V) (j : V) (hs : ∀ a ∈ B, a j = 0)
    (p : MvPolynomial V k) (hp : X j * p ∈ monomialIdeal k B) :
    p ∈ monomialIdeal k B := by
  rw [mem_monomialIdeal_iff] at hp ⊢
  intro a ha
  have hsum : a + Finsupp.single j 1 ∈ (X j * p).support := by
    rw [MvPolynomial.mem_support_iff, add_comm a, MvPolynomial.coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp ha
  obtain ⟨b,hb,hba⟩ := hp _ hsum
  refine ⟨b,hb,fun i => ?_⟩
  by_cases hi : i = j
  · subst i
    rw [hs b hb]
    exact Nat.zero_le _
  · simpa [Finsupp.single_apply, hi] using hba i

end Characterizations.Resolution

end
end CheckedCharacterizationsSource99

/-! ## Source: Characterizations.Resolution.Descent -/
section CheckedCharacterizationsSource100

/-! Genuine linear free resolutions descend along a variable regular on the ideal quotient. -/
noncomputable section
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)

private lemma augmentation_variable_saturated (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    ∀ y : Unit → MvPolynomial V k,
      (X j : MvPolynomial V k) • y ∈ LinearMap.range (scalarFree P.augmentation) →
        y ∈ LinearMap.range (scalarFree P.augmentation) := by
  intro y hy
  obtain ⟨x,hx⟩ := hy
  have hmul : X j * y () ∈ I := by
    have hm : P.augmentation x ∈ I := (P.augmentationToIdeal x).property
    have he := congrFun hx ()
    change P.augmentation x = X j * y () at he
    rwa [← he]
  have hyI : y () ∈ LinearMap.range P.augmentation := by
    rw [P.augmentation_range]
    exact hI (y ()) hmul
  obtain ⟨z,hz⟩ := hyI
  refine ⟨z,?_⟩
  funext a
  cases a
  exact hz

/-- Evaluation at zero in one variable preserves exactness whenever that
variable is regular on the quotient by the resolved ideal. The resulting
object is again a literal exact complex of finite free modules. -/
def specializeQuotient {W : Type u}
    (φ : MvPolynomial V k →ₐ[k] MvPolynomial W k)
    (hφ : Function.Surjective φ) (j : V) (ht : φ (X j) = 0)
    (hker : ∀ p, φ p = 0 → ∃ q, p = X j * q)
    (hhom : ∀ {p : MvPolynomial V k} {d}, p.IsHomogeneous d → (φ p).IsHomogeneous d)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map φ.toRingHom I) d where
  Index := P.Index
  finite := P.finite
  differential n := specialize φ.toRingHom (P.differential n)
  augmentation := specializeScalar φ.toRingHom P.augmentation
  augmentation_range := specializeScalar_range _ hφ
    P.augmentation I P.augmentation_range
  exact_zero := by
    have h := specialize_exact φ.toRingHom hφ (X j) ht
      hker (P.differential 0) (scalarFree P.augmentation)
      (by simpa only [scalarFree_ker] using P.exact_zero)
      (P.augmentation_variable_saturated j hI)
    exact h.trans (specializeScalar_ker _ P.augmentation)
  exact_succ n := by
    apply specialize_exact φ.toRingHom hφ (X j) ht hker _ _ (P.exact_succ n)
    cases n with
    | zero =>
      exact saturated_range_of_exact (P.differential 0) (scalarFree P.augmentation)
        (by simpa only [scalarFree_ker] using P.exact_zero) (X j)
        (MvPolynomial.isRegular_X.left)
    | succ n =>
      exact saturated_range_of_exact (P.differential (n+1)) (P.differential n)
        (P.exact_succ n) (X j) (MvPolynomial.isRegular_X.left)
  linear n := by
    intro a b
    rw [specialize_single]
    exact hhom (P.linear n a b)
  augmentation_homogeneous b := by
    rw [specializeScalar_single]
    exact hhom (P.augmentation_homogeneous b)

def deleteVariable (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) d :=
  P.specializeQuotient (Resolution.deleteVariable j) (deleteVariable_surjective j)
    j (deleteVariable_X j) (deleteVariable_kernel j)
    (deleteVariable_homogeneous j) hI

def descendAlong {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (MvPolynomial.killCompl hf).toRingHom I) d := by
  apply P.specializeQuotient (MvPolynomial.killCompl hf)
    (fun p => ⟨MvPolynomial.rename f p,MvPolynomial.killCompl_rename_app hf p⟩)
    j ?_ (killCompl_kernel_of_range f hf j hrange) (killCompl_homogeneous f hf) hI
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf 1 (a:=j)
  · simp
  · simpa only [hrange, ne_eq, not_not] using (rfl : j = j)

end LinearResolution

theorem HasLinearResolution.deleteVariable
    {I : Ideal (MvPolynomial V k)} (h : HasLinearResolution I) (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    HasLinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) := by
  obtain ⟨d,⟨P⟩⟩ := h
  exact ⟨d,⟨P.deleteVariable j hI⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource100

/-! ## Source: Characterizations.Resolution.LocalizationDescentData -/
section CheckedCharacterizationsSource101

/-! Exact retained-variable data for localization descent. -/

noncomputable section

namespace Characterizations.Resolution

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {U W : Finset V}

def retainedInclusion (hUW : U ⊆ W) : U → W := fun i => ⟨i.val, hUW i.property⟩

theorem retainedInclusion_injective (hUW : U ⊆ W) :
    Function.Injective (retainedInclusion hUW) := by
  intro i j h
  exact Subtype.ext (congrArg (fun x : W => x.val) h)

theorem extendExponent_mapDomain_retained (hUW : U ⊆ W) (a : Exponent U) :
    extendExponent W (a.mapDomain (retainedInclusion hUW)) = extendExponent U a := by
  simp only [extendExponent, Finsupp.extendDomain_eq_embDomain_subtype,
    Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- Equality of the ambient localized families is precisely extension of the
smaller retained-variable family by zero in the newly retained variables. -/
theorem localFamily_eq_image_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    localFamily B W = (localFamily B U).image
      (fun a => a.mapDomain (retainedInclusion hUW)) := by
  apply Finset.image_injective (show Function.Injective (extendExponent W) from
    (extendExponentEmbedding W).injective)
  calc
    (localFamily B W).image (extendExponent W) = localize B W :=
      (localize_eq_extend_localFamily B W).symm
    _ = localize B U := he
    _ = ((localFamily B U).image (fun a => a.mapDomain (retainedInclusion hUW))).image
        (extendExponent W) := by
      rw [localize_eq_extend_localFamily, Finset.image_image]
      simp only [Function.comp_def, extendExponent_mapDomain_retained]

theorem localFamily_zero_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) (j : W) (hj : j.val ∉ U)
    (a : Exponent W) (ha : a ∈ localFamily B W) : a j = 0 := by
  rw [localFamily_eq_image_of_localize_eq B hUW he] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact hj (congrArg Subtype.val hi ▸ i.property)

variable {k : Type*} [CommSemiring k]

/-- Setting all newly retained variables to zero gives exactly the ideal in
the smaller retained-variable polynomial ring. -/
theorem killCompl_localFamily_ideal (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    Ideal.map (MvPolynomial.killCompl (retainedInclusion_injective hUW)).toRingHom
      (monomialIdeal k (localFamily B W)) = monomialIdeal k (localFamily B U) := by
  have hmon (a : Exponent U) :
      MvPolynomial.killCompl (retainedInclusion_injective hUW)
        (MvPolynomial.monomial (a.mapDomain (retainedInclusion hUW)) (1 : k)) =
          MvPolynomial.monomial a 1 := by
    rw [← MvPolynomial.rename_monomial]
    exact MvPolynomial.killCompl_rename_app _ _
  rw [localFamily_eq_image_of_localize_eq B hUW he]
  simp only [monomialIdeal, Ideal.map_span, Finset.coe_image, Set.image_image]
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_image, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hmon]

end Characterizations.Resolution

end
end CheckedCharacterizationsSource101

/-! ## Source: Characterizations.Resolution.LocalizationDescent -/
section CheckedCharacterizationsSource102

/-! Descent from a restored variable when the actual generator family is unchanged. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid Resolution
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

theorem local_linearResolution_of_insert_family_eq (B : Family V) (U : Finset V)
    (i : V) (hi : i ∉ U)
    (he : localize B (insert i U) = localize B U)
    (hL : HasLinearResolution (monomialLocalization k (monomialIdeal k B) (insert i U))) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  let hUW : U ⊆ insert i U := Finset.subset_insert i U
  let j : (insert i U : Finset V) := ⟨i,Finset.mem_insert_self _ _⟩
  let f : U → (insert i U : Finset V) := retainedInclusion hUW
  have hf : Function.Injective f := retainedInclusion_injective hUW
  have hrange : ∀ w, w ∈ Set.range f ↔ w ≠ j := by
    intro w
    constructor
    · rintro ⟨u,rfl⟩ heq
      have hv := congrArg Subtype.val heq
      change u.val = i at hv
      exact hi (hv ▸ u.property)
    · intro hne
      have hw : w.val ∈ U := by
        rcases Finset.mem_insert.mp w.property with hw | hw
        · exact False.elim (hne (Subtype.ext hw))
        · exact hw
      exact ⟨⟨w.val,hw⟩,Subtype.ext rfl⟩
  rw [monomialLocalization_eq] at hL
  obtain ⟨d,⟨P⟩⟩ := hL
  have hs : ∀ a ∈ localFamily B (insert i U), a j = 0 := by
    exact localFamily_zero_of_localize_eq B hUW he j hi
  have hI := monomialIdeal_variable_saturated (k:=k) (localFamily B (insert i U)) j hs
  rw [monomialLocalization_eq, ← killCompl_localFamily_ideal (k:=k) B hUW he]
  exact ⟨d,⟨P.descendAlong f hf j hrange hI⟩⟩

end Characterizations

end
end CheckedCharacterizationsSource102

/-! ## Source: Characterizations.ObstructionDegree -/
section CheckedCharacterizationsSource103

/-! # The full degree cost of a maximal obstruction (Lemma 4.4)

Linearity is the existence of an actual exact finite-free linear resolution.
Polynomial-extension descent is established by coefficient specialization.
-/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem nonlinear_localization_rank_pos {B : Family V} (hB : B.Nonempty)
    (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    1 ≤ lowerRank B U := by
  by_contra hn
  have he := localize_equigenerated_of_rank_zero hB U (by omega)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

theorem nonlinear_equigenerated_localization_rank_ge_two {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (he : ∃ e, Equigenerated (localize B U) e)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    2 ≤ lowerRank B U := by
  by_contra hn
  obtain ⟨e,he⟩ := he
  obtain ⟨a,ha⟩ := localize_nonempty hB U
  have hr : e = lowerRank B U :=
    (he a ha).symm.trans (equigenerated_localize_degree hB he ha)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

/-- Lemma 4.4 for an inclusion-maximal localization lacking a genuine linear
free resolution. No prior equigeneration of all localizations is assumed. -/
theorem maximal_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hbad (Isolators.local_linearResolution_of_card_le_one hB U (by omega))
  have hequi : ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e := by
    intro W hW
    have hL := hmax W hW
    rw [monomialLocalization_eq] at hL
    obtain ⟨e,⟨P⟩⟩ := hL
    exact ⟨e,localFamily_equigenerated_iff.mp
      (P.equigenerated_of_monomial (localFamily B W) (localFamily_antichain B W))⟩
  have hinc : ∀ i ∉ U, lowerRank B U+1 ≤ lowerRank B (insert i U) := by
    intro i hi
    have hsub : U ⊂ insert i U := Finset.ssubset_insert hi
    have hm := lowerRank_mono hB (Finset.subset_insert i U)
    by_contra hn
    have hr : lowerRank B U = lowerRank B (insert i U) := by omega
    have hf := localize_eq_of_rank_eq hB (Finset.subset_insert i U) (hequi _ hsub) hr
    exact hbad (local_linearResolution_of_insert_family_eq B U i hi hf (hmax _ hsub))
  have hbound := supermodular_rank_codimension_bound
    (lowerRank_supermodular_above hB U hequi) hinc
  rw [lowerRank_univ_of_equigenerated hB hd] at hbound
  exact ⟨hcard,nonlinear_localization_rank_pos hB U hbad,hbound⟩

/-- Both alternatives in the literal statement of Lemma 4.4. -/
theorem maximal_obstruction_degree_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hmax :
      ((¬ ∃ e, Equigenerated (localize B U) e) ∧
        ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e) ∨
      ((¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) ∧
        ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W))) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  rcases hmax with ⟨hbad,hm⟩ | ⟨hbad,hm⟩
  · exact maximal_nonequigenerated_rank_cost hB hd U hbad hm
  · exact maximal_nonlinear_rank_cost hB hd U hbad hm

/-- The final assertion of Lemma 4.4 under prior local equigeneration. -/
theorem maximal_pure_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 2 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  obtain ⟨hc,_,hdim⟩ := maximal_nonlinear_rank_cost hB hd U hbad hmax
  exact ⟨hc,nonlinear_equigenerated_localization_rank_ge_two hB U (hl U) hbad,hdim⟩

end Characterizations

end
end CheckedCharacterizationsSource103

/-! ## Source: Characterizations.PairMass -/
section CheckedCharacterizationsSource104

/-! # A pointed triple injects into any prescribed final pair event -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triple_to_pair_card_le {i q j k : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j)
    (hki : k ≠ i) (hkq : k ≠ q) (hkj : k ≠ j) :
    Nat.card {o : VariableOrder V // FinalTriple o i q j} ≤
      Nat.card {o : VariableOrder V // FinalPair o i j} := by
  let σ : Equiv.Perm V := (Equiv.swap q k).trans (Equiv.swap i q)
  have hσi : σ i = q := by simp [σ,Equiv.swap_apply_def,hiq,hiq.symm,hki.symm]
  have hσq : σ q = k := by simp [σ,Equiv.swap_apply_def,hki,hkq]
  have hσk : σ k = i := by simp [σ,Equiv.swap_apply_def,hkq.symm]
  have hσj : σ j = j := by simp [σ,Equiv.swap_apply_def,hij.symm,hqj.symm,hkj.symm]
  have hσx (x : V) (hxi : x ≠ i) (hxq : x ≠ q) (hxk : x ≠ k) : σ x = x := by
    simp [σ,Equiv.swap_apply_def,hxi,hxq,hxk,Ne.symm hxi,Ne.symm hxq,Ne.symm hxk]
  let f (o : VariableOrder V) : VariableOrder V := if o q < o i then o else σ.trans o
  have hf (o : VariableOrder V) (ho : FinalTriple o i q j) : FinalPair (f o) i j := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi]
      refine ⟨ho.1,?_⟩
      intro x hxi hxj
      by_cases hxq : x = q
      · simpa [hxq] using hqi
      · exact (ho.2.2 x hxi hxq hxj).1
    · have hiqO : o i < o q := lt_of_le_of_ne (le_of_not_gt hqi)
        (fun he => hiq (o.injective he))
      simp only [f,if_neg hqi]
      refine ⟨?_,?_⟩
      · simpa only [Equiv.trans_apply,hσi,hσj] using ho.2.1
      · intro x hxi hxj
        by_cases hxq : x = q
        · subst x
          simpa only [Equiv.trans_apply,hσq,hσi] using (ho.2.2 k hki hkq hkj).2
        by_cases hxk : x = k
        · subst x
          simpa only [Equiv.trans_apply,hσk,hσi] using hiqO
        · simpa only [Equiv.trans_apply,hσi,hσx x hxi hxq hxk] using (ho.2.2 x hxi hxq hxj).2
  have hsignal (o : VariableOrder V) (ho : FinalTriple o i q j) :
      (f o) q < (f o) k ↔ ¬ o q < o i := by
    by_cases hqi : o q < o i
    · simp only [f,if_pos hqi,hqi,not_true_eq_false,iff_false]
      exact not_lt_of_gt (ho.2.2 k hki hkq hkj).2
    · simp only [f,if_neg hqi,Equiv.trans_apply,hσq,hσk,hqi,not_false_eq_true,iff_true]
      exact (ho.2.2 k hki hkq hkj).1
  let g : {o : VariableOrder V // FinalTriple o i q j} → {o : VariableOrder V // FinalPair o i j} :=
    fun o => ⟨f o.val,hf o.val o.property⟩
  apply Nat.card_le_card_of_injective g
  intro o o' he
  have heq : f o.val = f o'.val := congrArg Subtype.val he
  have hcond : (o.val q < o.val i) ↔ (o'.val q < o'.val i) := by
    have hs : (¬o.val q < o.val i) ↔ ¬o'.val q < o'.val i := by
      rw [← hsignal o.val o.property,← hsignal o'.val o'.property,heq]
    tauto
  apply Subtype.ext
  by_cases h : o.val q < o.val i
  · simpa only [f,if_pos h,if_pos (hcond.mp h)] using heq
  · have h' : ¬o'.val q < o'.val i := fun h' => h (hcond.mpr h')
    simp only [f,if_neg h,if_neg h'] at heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun e : VariableOrder V => e (σ.symm x)) heq
    simpa using hx

theorem finalPair_probability_lower_bound (hcard : 4 ≤ Fintype.card V) {i j : V} (hij : i ≠ j) :
    1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) ≤
      finiteFraction (fun o : VariableOrder V => FinalPair o i j) := by
  have hpaircard : (pairCap i j).card = Fintype.card V-2 := by
    rw [pairCap,card_sdiff_of_subset (subset_univ _)]
    simp [hij]
  obtain ⟨q,hq⟩ : (pairCap i j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hqi,hqj⟩ := (mem_pairCap _ _ _).mp hq
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hqi.symm,hij,hqj]
  obtain ⟨k,hk⟩ : (tripleCap i q j).Nonempty := card_pos.mp (by omega)
  obtain ⟨hki,hkq,hkj⟩ := (mem_tripleCap _ _ _ _).mp hk
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hqi.symm]⟩⟩
  have hprob : finiteFraction (fun o : VariableOrder V => FinalTriple o i q j) =
      1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
    rw [← pointedTriple_probability (by omega) P]
    exact finiteFraction_congr (fun o => (coversPoint_pair_iff hqi.symm hij hqj).symm)
  rw [←hprob]
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast triple_to_pair_card_le hqi.symm hij hqj hki hkq hkj)
    (Nat.cast_nonneg _)

end Characterizations

end
end CheckedCharacterizationsSource104

/-! ## Source: Characterizations.PaperEndpoints -/
section CheckedCharacterizationsSource105

/-!
# The integral-closedness characterization, including the zero ideal

The polytope in Theorem 2.11 requires a nonempty generator family, since its
lower rank is a minimum.  The characterization in (2.5) itself also holds at
zero.  This interface states that equivalence for every literal monomial ideal.
It adds no hypothesis and uses the ordinary monic-equation definition of
integral closedness already used by the nonzero theorem.
-/

noncomputable section

namespace Characterizations

open CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Equation (2.5), for an arbitrary monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed_all
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d,
        Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  by_cases hzero : I = ⊥
  · subst I
    have hp : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) :=
      isPolymatroidalIdeal_bot
    have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
    constructor
    · intro _
      exact ⟨integrallyClosed_bot, fun U => (localFamily_polymatroidal hgenerators U).1⟩
    · intro _
      exact hp
  · exact monomialIdeal_polymatroidal_iff_integrallyClosed hI hzero

/-- Corollary 2.10 for an arbitrary literal monomial ideal, including zero.
The same minimal monomial exponent family is interpreted over any coefficient field. -/
theorem monomialIdeal_local_linearResolutions_field_independent_all
    {k' : Type u} [Field k']
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hlinear : ∀ U : Finset V,
      HasLinearResolution (monomialLocalization k I U)) :
    ∀ U : Finset V,
      HasLinearResolution
        (monomialLocalization k' (monomialIdeal k' (monomialGenerators I hI)) U) := by
  have hp := (monomialIdeal_polymatroidal_iff_local_linear hI).mpr hlinear
  have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
  exact fun U => polymatroidal_local_linearResolutions (k := k') hgenerators U

end Characterizations

end
end CheckedCharacterizationsSource105

/-! ## Source: Characterizations.Presentation.Strands -/
section CheckedCharacterizationsSource106

/-! # The actual multigraded strands of the canonical monomial presentation -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

abbrev Generators (B : Family V) := {b // b ∈ B}
abbrev Free (B : Family V) := Generators B → MvPolynomial V k

/-- The canonical augmentation of the actual free polynomial module. -/
def augmentation (B : Family V) : Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b : Generators B => monomial b.val 1)

@[simp] theorem augmentation_apply (B : Family V) (x : Free (k := k) B) :
    augmentation B x = ∑ b, x b * monomial b.val 1 := by
  simp [augmentation, Fintype.linearCombination_apply, smul_eq_mul]

/-- The coefficient of the generator-labelled basis monomial of multidegree `C`. -/
def strandCoefficient (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) : k := if b.val ≤ C then (x b).coeff (C - b.val) else 0

/-- Projection of a genuine polynomial vector onto one multidegree, with the
basis vector labelled `b` carrying its natural degree `b`. -/
def strand (B : Family V) (C : Exponent V) (x : Free (k := k) B) : Free (k := k) B :=
  fun b => monomial (C - b.val) (strandCoefficient B C x b)

@[simp] theorem strandCoefficient_add (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x + y) = strandCoefficient B C x + strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_sub (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x - y) = strandCoefficient B C x - strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_zero (B : Family V) (C : Exponent V) :
    strandCoefficient B C (0 : Free (k := k) B) = 0 := by
  funext b
  simp [strandCoefficient]

@[simp] theorem strandCoefficient_smul (B : Family V) (C : Exponent V) (c : k)
    (x : Free (k := k) B) : strandCoefficient B C (c • x) = c • strandCoefficient B C x := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

lemma augmentation_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    (augmentation B x).coeff C = ∑ b, strandCoefficient B C x b := by
  simp [augmentation_apply, coeff_mul_monomial', strandCoefficient]

lemma strandCoefficient_sum_zero {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    ∑ b, strandCoefficient B C x b = 0 := by
  rw [← augmentation_coeff, LinearMap.mem_ker.mp hx]
  simp

lemma strand_augmentation (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    augmentation B (strand B C x) = monomial C (∑ b, strandCoefficient B C x b) := by
  rw [augmentation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : b.val ≤ C
  · simp [strand, strandCoefficient, h, monomial_mul_monomial, tsub_add_cancel_of_le h]
  · simp [strand, strandCoefficient, h]

lemma strand_mem_ker {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    strand B C x ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [strand_augmentation, strandCoefficient_sum_zero hx]
  simp

/-- The finite set of multidegrees occurring in an actual polynomial vector. -/
def support (B : Family V) (x : Free (k := k) B) : Finset (Exponent V) :=
  univ.biUnion (fun b => (x b).support.image (fun a => a + b.val))

lemma degree_mem_support {B : Family V} (x : Free (k := k) B) (b : Generators B)
    (a : Exponent V) (ha : (x b).coeff a ≠ 0) : a + b.val ∈ support B x := by
  exact mem_biUnion.mpr ⟨b, mem_univ _, mem_image.mpr ⟨a, mem_support_iff.mpr ha, rfl⟩⟩

lemma strand_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) (a : Exponent V) :
    (strand B C x b).coeff a = if C = a + b.val then (x b).coeff a else 0 := by
  by_cases h : b.val ≤ C
  · have he : C - b.val = a ↔ C = a + b.val := by
      constructor
      · intro he
        rw [← he, tsub_add_cancel_of_le h]
      · intro he
        rw [he, add_tsub_cancel_right]
    by_cases hC : C = a + b.val
    · subst C; simp [strand, strandCoefficient, add_tsub_cancel_right]
    · simp [strand, strandCoefficient, h, coeff_monomial, he, hC]
  · have he : C ≠ a + b.val := by
      intro he
      exact h (he ▸ le_add_left le_rfl)
    simp [strand, strandCoefficient, h, he]

/-- Finite multigraded decomposition in the original free module. -/
lemma sum_strand (B : Family V) (x : Free (k := k) B) :
    ∑ C ∈ support B x, strand B C x = x := by
  funext b
  apply MvPolynomial.ext
  intro a
  simp only [Finset.sum_apply, coeff_sum, strand_coeff]
  by_cases h : a + b.val ∈ support B x
  · simp [h]
  · have hz : (x b).coeff a = 0 := by
      by_contra hn
      exact h (degree_mem_support x b a hn)
    simp [h, hz]

/-- A genuine binomial syzygy between two canonical generators, at their lcm. -/
def pairSyzygy (B : Family V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial ((a.val ⊔ b.val) - a.val) 1) -
    Pi.single b (monomial ((a.val ⊔ b.val) - b.val) 1)

lemma augmentation_single (B : Family V) (b : Generators B) (p : MvPolynomial V k) :
    augmentation B (Pi.single b p) = p * monomial b.val 1 := by
  simp [augmentation_apply, Pi.single_apply]

lemma pairSyzygy_mem_ker (B : Family V) (a b : Generators B) :
    pairSyzygy (k := k) B a b ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [pairSyzygy, map_sub, augmentation_single, augmentation_single,
    monomial_mul_monomial, monomial_mul_monomial,
    tsub_add_cancel_of_le le_sup_left, tsub_add_cancel_of_le le_sup_right, sub_self]

/-- The conventional algebraic definition: the first syzygy module of the
canonical minimal generator presentation is generated by linear forms. -/
def HasLinearPresentation (B : Family V) : Prop :=
  LinearMap.ker (augmentation (k := k) B) ≤
    Submodule.span (MvPolynomial V k)
      {x | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1}

end Characterizations.Presentation

end
end CheckedCharacterizationsSource106

/-! ## Source: Characterizations.Presentation.Edges -/
section CheckedCharacterizationsSource107

/-! # Linear binomial syzygies are exactly unit-exchange relations -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

lemma sup_exchange (a : Exponent V) {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    a ⊔ exchange a i j = a + Finsupp.single j 1 := by
  ext v
  simp only [Finsupp.sup_apply, exchange_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

lemma sup_sub_of_step {a b : Exponent V} (h : UnitStep a b) :
    ∃ i j, (a ⊔ b) - a = Finsupp.single j 1 ∧
      (a ⊔ b) - b = Finsupp.single i 1 := by
  obtain ⟨i, j, hij, hi, rfl⟩ := h
  refine ⟨i, j, ?_, ?_⟩
  · rw [sup_exchange a hij hi, add_tsub_cancel_left]
  · rw [sup_exchange a hij hi]
    ext v
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, exchange_apply]
    by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

lemma pairSyzygy_linear (B : Family V) (a b : Generators B) (h : UnitStep a.val b.val) :
    Resolution.IsHomogeneousVector (pairSyzygy (k := k) B a b) 1 := by
  obtain ⟨i, j, ha, hb⟩ := sup_sub_of_step h
  intro c
  simp only [pairSyzygy, Pi.sub_apply, ha, hb]
  apply MvPolynomial.IsHomogeneous.sub
  · by_cases he : c = a
    · subst c; simpa [Pi.single_apply, MvPolynomial.X] using (isHomogeneous_X (R := k) j)
    · simp [Pi.single_apply, he, Ne.symm he, isHomogeneous_zero]
  · by_cases he : c = b
    · subst c; simpa [Pi.single_apply, MvPolynomial.X] using (isHomogeneous_X (R := k) i)
    · simp [Pi.single_apply, he, Ne.symm he, isHomogeneous_zero]

/-- The polynomial submodule generated by actual linear binomial syzygies. -/
def edgeSpan (B : Family V) : Submodule (MvPolynomial V k) (Free (k := k) B) :=
  Submodule.span _ {x | ∃ a b : Generators B, UnitStep a.val b.val ∧ x = pairSyzygy B a b}

lemma pairSyzygy_mem_edgeSpan (B : Family V) (a b : Generators B) (h : UnitStep a.val b.val) :
    pairSyzygy (k := k) B a b ∈ edgeSpan B :=
  Submodule.subset_span ⟨a, b, h, rfl⟩

lemma edgeSpan_le_ker (B : Family V) : edgeSpan (k := k) B ≤ LinearMap.ker (augmentation B) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, h, rfl⟩
  exact pairSyzygy_mem_ker B a b

lemma edgeSpan_le_linearSpan (B : Family V) :
    edgeSpan (k := k) B ≤ Submodule.span (MvPolynomial V k)
      {x | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1} := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, h, rfl⟩
  exact Submodule.subset_span ⟨pairSyzygy_mem_ker B a b, pairSyzygy_linear B a b h⟩

/-- A pair relation at any common multiple is a monomial multiple of its lcm relation. -/
lemma scaled_pairSyzygy (B : Family V) (C : Exponent V) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) :
    (monomial (C - (a.val ⊔ b.val)) (1 : k)) • pairSyzygy (k := k) B a b =
      Pi.single a (monomial (C - a.val) (1 : k)) - Pi.single b (monomial (C - b.val) (1 : k)) := by
  have hsup : a.val ⊔ b.val ≤ C := sup_le ha hb
  have h₁ : C - (a.val ⊔ b.val) + ((a.val ⊔ b.val) - a.val) = C - a.val := by
    ext v
    have hs := hsup v
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.sup_apply] at hs ⊢
    omega
  have h₂ : C - (a.val ⊔ b.val) + ((a.val ⊔ b.val) - b.val) = C - b.val := by
    ext v
    have hs := hsup v
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.sup_apply] at hs ⊢
    omega
  funext v
  simp only [pairSyzygy, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub]
  by_cases hva : v = a <;> by_cases hvb : v = b <;>
    simp_all [Pi.single_apply, eq_comm, monomial_mul_monomial, h₁, h₂]

lemma step_of_common_degree_one {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (C : Exponent V) (hC : C.degree = d + 1) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) (hab : a ≠ b) : UnitStep a.val b.val := by
  have hdeg (x : Generators B) (hx : x.val ≤ C) : (C - x.val).degree = 1 := by
    have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hx)
    rw [map_add, hB x.val x.property, hC] at he
    omega
  obtain ⟨j, hj⟩ : ∃ j, Finsupp.single j 1 = C - a.val := by
    apply Set.mem_range.mp
    rw [Finsupp.range_single_one]
    exact hdeg a ha
  obtain ⟨i, hi⟩ : ∃ i, Finsupp.single i 1 = C - b.val := by
    apply Set.mem_range.mp
    rw [Finsupp.range_single_one]
    exact hdeg b hb
  have he : a.val + Finsupp.single j 1 = b.val + Finsupp.single i 1 := by
    rw [hj, hi, add_tsub_cancel_of_le ha, add_tsub_cancel_of_le hb]
  have hij : i ≠ j := by
    intro hij
    apply hab
    apply Subtype.ext
    rw [hij] at he
    exact add_right_cancel he
  have hai : 0 < a.val i := by
    have hh := congrArg (fun t : Exponent V => t i) he
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply,
      if_neg hij, if_neg hij.symm] at hh
    omega
  refine ⟨i, j, hij, hai, ?_⟩
  ext v
  have hh := congrArg (fun t : Exponent V => t v) he
  simp only [Finsupp.add_apply, Finsupp.single_apply, exchange_apply] at hh ⊢
  by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp_all [eq_comm] <;> omega

end Characterizations.Presentation

end
end CheckedCharacterizationsSource107

/-! ## Source: Characterizations.Presentation.Paths -/
section CheckedCharacterizationsSource108

/-! # Exchange paths span the actual polynomial syzygies -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

def pairAt (B : Family V) (C : Exponent V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial (C - a.val) 1) - Pi.single b (monomial (C - b.val) 1)

@[simp] lemma pairAt_self (B : Family V) (C : Exponent V) (a : Generators B) :
    pairAt (k := k) B C a a = 0 := sub_self _

lemma pairAt_add (B : Family V) (C : Exponent V) (a b c : Generators B) :
    pairAt (k := k) B C a b + pairAt B C b c = pairAt B C a c := by
  exact sub_add_sub_cancel _ _ _

lemma pairAt_mem_of_step (B : Family V) (C : Exponent V) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) (h : UnitStep a.val b.val) :
    pairAt (k := k) B C a b ∈ edgeSpan B := by
  rw [pairAt, ← scaled_pairSyzygy B C a b ha hb]
  exact (edgeSpan B).smul_mem _ (pairSyzygy_mem_edgeSpan B a b h)

lemma pairAt_mem_of_path (B : Family V) (C : Exponent V) {a b : Exponent V}
    (hp : Relation.ReflTransGen (BoxStep B C) a b) (ha : a ∈ B) (hb : b ∈ B) :
    pairAt (k := k) B C ⟨a, ha⟩ ⟨b, hb⟩ ∈ edgeSpan B := by
  induction hp with
  | refl => simp
  | @tail b c hp hbc ih =>
    have h₁ := ih hbc.1
    have h₂ := pairAt_mem_of_step (k := k) B C ⟨b, hbc.1⟩ ⟨c, hb⟩ hbc.2.2.1 hbc.2.2.2.1 hbc.2.2.2.2
    simpa only [pairAt_add] using (edgeSpan B).add_mem h₁ h₂

lemma strand_eq_sum_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B)) (a : Generators B) :
    (∑ b, (MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) • pairAt B C b a) = strand B C x := by
  have hs : (∑ b, MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) = 0 := by
    rw [← map_sum, strandCoefficient_sum_zero hx, map_zero]
  simp only [pairAt, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [hs, zero_smul, sub_zero]
  funext c
  simp [Pi.single_apply, strand, C_mul_monomial]

lemma strand_mem_of_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B))
    (hp : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → pairAt (k := k) B C a b ∈ edgeSpan B) :
    strand B C x ∈ edgeSpan B := by
  by_cases hne : ∃ a : Generators B, a.val ≤ C
  · obtain ⟨a, ha⟩ := hne
    rw [← strand_eq_sum_pairs C x hx a]
    apply (edgeSpan B).sum_mem
    intro b hb
    by_cases hbc : b.val ≤ C
    · exact (edgeSpan B).smul_mem _ (hp b a hbc ha)
    · simp [strandCoefficient, hbc]
  · have he : strand B C x = 0 := by
      funext b
      have hb : ¬ b.val ≤ C := fun h => hne ⟨b, h⟩
      simp [strand, strandCoefficient, hb]
    rw [he]
    exact (edgeSpan B).zero_mem

lemma ker_le_edgeSpan_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B := by
  intro x hx
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  exact pairAt_mem_of_path B C (hB C a.val a.property ha b.val b.property hb) a.property b.property

/-- Every actual homogeneous linear syzygy is spanned by the binomial
unit-exchange syzygies, without any connectivity assumption. -/
lemma linear_relation_mem_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (x : Free (k := k) B) (hx : x ∈ LinearMap.ker (augmentation B))
    (hlin : Resolution.IsHomogeneousVector x 1) : x ∈ edgeSpan B := by
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  have hdeg : C.degree = d + 1 := by
    obtain ⟨b, hb, hC⟩ := mem_biUnion.mp hC
    obtain ⟨e, he, rfl⟩ := mem_image.mp hC
    have he' : e.degree = 1 := by
      by_contra hn
      exact (mem_support_iff.mp he) ((hlin b).coeff_eq_zero hn)
    rw [map_add, he', hB b.val b.property, Nat.add_comm]
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  by_cases hab : a = b
  · subst b; simp
  · exact pairAt_mem_of_step B C a b ha hb (step_of_common_degree_one hB C hdeg a b ha hb hab)

lemma linearSpan_eq_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    Submodule.span (MvPolynomial V k)
      {x : Free (k := k) B | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1} =
      edgeSpan B := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact linear_relation_mem_edgeSpan hB x hx.1 hx.2
  · exact edgeSpan_le_linearSpan B

lemma linearPresentation_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    HasLinearPresentation (k := k) B :=
  (ker_le_edgeSpan_of_boxConnected hB).trans (edgeSpan_le_linearSpan B)

end Characterizations.Presentation

end
end CheckedCharacterizationsSource108

/-! ## Source: Characterizations.Presentation.Connectivity -/
section CheckedCharacterizationsSource109

/-! # A disconnected box detects a genuine nonlinear first syzygy -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- Restrict the actual canonical augmentation to a specified generator subset. -/
def selectedAugmentation (B : Family V) (U : Finset (Generators B)) :
    Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b => if b ∈ U then monomial b.val 1 else 0)

lemma selectedAugmentation_single (B : Family V) (U : Finset (Generators B))
    (b : Generators B) (p : MvPolynomial V k) :
    selectedAugmentation B U (Pi.single b p) = if b ∈ U then p * monomial b.val 1 else 0 := by
  simp [selectedAugmentation, Fintype.linearCombination_apply, Pi.single_apply, smul_eq_mul,
    mul_ite]

lemma selectedAugmentation_pair (B : Family V) (U : Finset (Generators B))
    (a b : Generators B) :
    selectedAugmentation (k := k) B U (pairSyzygy B a b) =
      (if a ∈ U then monomial (a.val ⊔ b.val) 1 else 0) -
        (if b ∈ U then monomial (a.val ⊔ b.val) 1 else 0) := by
  rw [pairSyzygy, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le le_sup_left,
    tsub_add_cancel_of_le le_sup_right]

lemma selectedAugmentation_pairAt (B : Family V) (U : Finset (Generators B))
    (C : Exponent V) (a b : Generators B) (ha : a.val ≤ C) (hb : b.val ≤ C) :
    selectedAugmentation (k := k) B U (pairAt B C a b) =
      (if a ∈ U then monomial C 1 else 0) - (if b ∈ U then monomial C 1 else 0) := by
  rw [pairAt, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le ha,
    tsub_add_cancel_of_le hb]

lemma selectedAugmentation_edge_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (a b : Generators B) (hab : UnitStep a.val b.val) (p : MvPolynomial V k) :
    (selectedAugmentation (k := k) B U (p • pairSyzygy (k := k) B a b)).coeff C = 0 := by
  rw [map_smul, selectedAugmentation_pair]
  by_cases hsup : a.val ⊔ b.val ≤ C
  · have he := hU a b (le_sup_left.trans hsup) (le_sup_right.trans hsup) hab
    by_cases ha : a ∈ U
    · simp [ha, he.mp ha]
    · have hb : b ∉ U := fun hb => ha (he.mpr hb)
      simp [ha, hb]
  · simp only [smul_eq_mul, mul_sub]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
      simp [ha, hb, coeff_mul_monomial', hsup]

lemma selectedAugmentation_edgeSpan_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (x : Free (k := k) B) (hx : x ∈ edgeSpan B) :
    (selectedAugmentation B U x).coeff C = 0 := by
  suffices hh : ∀ p : MvPolynomial V k, (selectedAugmentation B U (p • x)).coeff C = 0 by
    simpa using hh 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact selectedAugmentation_edge_coeff_zero B U C hU a b hab
  | zero => intro p; simp
  | add x y hx hy ihx ihy =>
    intro p
    simp only [smul_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihx, ihy, add_zero]
  | smul r x hx ih =>
    intro p
    rw [smul_smul]
    exact ih (p * r)

/-- A disconnected box produces an actual syzygy outside the submodule generated
by all linear binomial relations. This holds in every nontrivial coefficient ring. -/
lemma boxConnected_of_ker_le_edgeSpan [Nontrivial k] {B : Family V}
    (hker : LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B) : BoxConnected B := by
  intro C a ha haC b hb hbC
  by_contra hpath
  let U : Finset (Generators B) := univ.filter (fun c => Relation.ReflTransGen (BoxStep B C) a c.val)
  have hU : ∀ x y : Generators B, x.val ≤ C → y.val ≤ C → UnitStep x.val y.val → (x ∈ U ↔ y ∈ U) := by
    intro x y hx hy hxy
    simp only [U, mem_filter, mem_univ, true_and]
    constructor
    · intro hp
      exact hp.tail ⟨x.property, y.property, hx, hy, hxy⟩
    · intro hp
      exact hp.tail ⟨y.property, x.property, hy, hx, hxy.symm⟩
  let a' : Generators B := ⟨a, ha⟩
  let b' : Generators B := ⟨b, hb⟩
  have haU : a' ∈ U := by simp [U, a', Relation.ReflTransGen.refl]
  have hbU : b' ∉ U := by simpa [U, b'] using hpath
  have hz : pairAt (k := k) B C a' b' ∈ LinearMap.ker (augmentation B) := by
    rw [pairAt, ← scaled_pairSyzygy B C a' b' haC hbC]
    exact (LinearMap.ker (augmentation B)).smul_mem _ (pairSyzygy_mem_ker B a' b')
  have hh := selectedAugmentation_edgeSpan_coeff_zero B U C hU _ (hker hz)
  rw [selectedAugmentation_pairAt B U C a' b' haC hbC] at hh
  simpa [haU, hbU] using hh

/-- Lemma 3.1: the conventional linear first-syzygy condition is equivalent to
connectivity of every nonempty coordinate box, over every field (indeed, ring). -/
theorem linearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : HasLinearPresentation (k := k) B ↔ BoxConnected B := by
  constructor
  · intro h
    apply boxConnected_of_ker_le_edgeSpan (k := k)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  · exact linearPresentation_of_boxConnected

end Characterizations.Presentation

end
end CheckedCharacterizationsSource109

/-! ## Source: Characterizations.Presentation.Finite -/
section CheckedCharacterizationsSource110

/-! # Conventional finite free presentations and the local exchange criterion -/
noncomputable section
@[reducible] local instance (priority := 2000) presentationDecEq (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- An actual finite free presentation of the original monomial ideal, with all
first differential entries linear. The canonical free generators have the common
degree of the monomial generating family. -/
structure FiniteLinearPresentation (B : Family V) where
  rank : ℕ
  differential : (Fin rank → MvPolynomial V k) →ₗ[MvPolynomial V k] Free (k := k) B
  exact : LinearMap.range differential = LinearMap.ker (augmentation B)
  linear : Resolution.IsHomogeneousMap differential 1

lemma augmentation_range (B : Family V) :
    LinearMap.range (augmentation (k := k) B) = monomialIdeal k B := by
  rw [augmentation, Fintype.range_linearCombination, monomialIdeal]
  apply congrArg (Submodule.span (MvPolynomial V k))
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

lemma FiniteLinearPresentation.hasLinearPresentation {B : Family V}
    (P : FiniteLinearPresentation (k := k) B) : HasLinearPresentation (k := k) B := by
  intro x hx
  rw [← P.exact] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y = ∑ j, y j • Pi.single j (1 : MvPolynomial V k) := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  constructor
  · rw [← P.exact]
    exact LinearMap.mem_range_self _ _
  · exact fun b => P.linear b j

abbrev Edges (B : Family V) :=
  {ab : Generators B × Generators B // UnitStep ab.1.val ab.2.val}

def edgeColumn (B : Family V) (j : Fin (Fintype.card (Edges B))) : Free (k := k) B :=
  let ab := (Fintype.equivFin (Edges B)).symm j
  pairSyzygy B ab.val.1 ab.val.2

lemma edgeColumn_range (B : Family V) :
    Set.range (edgeColumn (k := k) B) =
      {x | ∃ a b : Generators B, UnitStep a.val b.val ∧ x = pairSyzygy B a b} := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact ⟨ab.val.1, ab.val.2, ab.property, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨(Fintype.equivFin (Edges B)) ⟨(a, b), hab⟩, ?_⟩
    simp [edgeColumn]

/-- The first free module has one basis vector for each ordered unit-exchange
edge. Exactness follows from the proved algebraic syzygy criterion. -/
def finiteLinearPresentationOfCondition {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (h : HasLinearPresentation (k := k) B) :
    FiniteLinearPresentation (k := k) B where
  rank := Fintype.card (Edges B)
  differential := Fintype.linearCombination _ (edgeColumn B)
  exact := by
    rw [Fintype.range_linearCombination, edgeColumn_range]
    change edgeSpan B = LinearMap.ker (augmentation B)
    apply le_antisymm (edgeSpan_le_ker B)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  linear := by
    intro b j
    have he : Fintype.linearCombination (MvPolynomial V k) (edgeColumn (k := k) B) (Pi.single j 1) = edgeColumn (k := k) B j := by
      simp [Fintype.linearCombination_apply, Pi.single_apply]
    rw [he]
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact pairSyzygy_linear B ab.val.1 ab.val.2 ab.property b

/-- The syzygy-generation definition is equivalent to a literal finite free
presentation with linear entries. -/
theorem nonempty_finiteLinearPresentation_iff {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ HasLinearPresentation (k := k) B :=
  ⟨fun ⟨P⟩ => P.hasLinearPresentation, fun h => ⟨finiteLinearPresentationOfCondition hB h⟩⟩

/-- Lemma 3.1, stated directly with the actual finite free presentation. -/
theorem finiteLinearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ BoxConnected B :=
  (nonempty_finiteLinearPresentation_iff hB).trans (linearPresentation_iff_boxConnected hB)

/-- Exchange restricted exactly to pairs at the paper's distance four. -/
def DistanceFourExchange (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, l1Distance a b = 4 → ∀ i, b i < a i →
    ∃ j, a j < b j ∧ exchange a i j ∈ B

/-- Theorem 3.3, with a genuine finite linear presentation and the full prescribed
donor exchange condition. -/
theorem polymatroidal_iff_linearPresentation_distanceFour [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    IsPolymatroidal B ↔ Nonempty (FiniteLinearPresentation (k := k) B) ∧ DistanceFourExchange B := by
  constructor
  · intro h
    constructor
    · apply (finiteLinearPresentation_iff_boxConnected hB).mpr
      let o : VariableOrder V := Fintype.equivFin V
      exact boxConnected_of_linearQuotients hB (variableRevlex_irrefl o)
        (variableRevlex_trans o) (variableRevlex_total o)
        (polymatroidal_variable_linearQuotients (k := k) h.2 o)
    · intro a ha b hb _ i hi
      exact h.2 a ha b hb i hi
  · rintro ⟨hp, he⟩
    refine ⟨⟨d, hB⟩, ?_⟩
    by_contra hn
    obtain ⟨a, b, ha, hb, hd, i, hi, hbad⟩ :=
      failed_exchange_distance_four ((finiteLinearPresentation_iff_boxConnected hB).mp hp) hn
    obtain ⟨j, hj, hjB⟩ := he a ha b hb hd i hi
    exact hbad j hj hjB

end Characterizations.Presentation

end
end CheckedCharacterizationsSource110

/-! ## Source: Characterizations.Rejection -/
section CheckedCharacterizationsSource111

/-! # The sharp rejection fraction, including independent repeated tests -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def rejectionFraction (k : Type*) [CommSemiring k] (B : Family V) : ℝ :=
  finiteFraction (fun o : VariableOrder V => ¬ HasLinearQuotients k B (variableRevlex o))

def patternMass (s : ℕ) : ℝ := 1 / ((s+3)*(s+2).choose 2 : ℕ)

/-- Theorem 5.6: every nonpolymatroidal generator family has at least the
probability of one full active order pattern. -/
theorem rejection_fraction_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    patternMass (min (d-1) (Fintype.card V-3)) ≤ rejectionFraction k B := by
  let G : Set (VariableOrder V) := {o | HasLinearQuotients k B (variableRevlex o)}
  by_cases hpatterns : CoversPatterns (min (d-1) (Fintype.card V-3)) G
  · have hnpairs : ¬ (Fintype.card V-1 ≤ d → CoversFinalPairs G) := by
      intro hpairs
      exact hnot ⟨⟨d,hB⟩,exchange_of_degree_coverage (k := k) hB hcard G hpatterns hpairs (fun _ h => h)⟩
    simp only [CoversFinalPairs,not_forall] at hnpairs
    obtain ⟨hdlarge,i,j,hij,hbad⟩ := hnpairs
    have hmass : patternMass (min (d-1) (Fintype.card V-3)) =
        1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
      have h1 : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
      have h2 : Fintype.card V-3+3 = Fintype.card V := by omega
      have h3 : Fintype.card V-3+2 = Fintype.card V-1 := by omega
      simp only [patternMass,h1,h2,h3]
    rw [hmass]
    apply (finalPair_probability_lower_bound hcard hij).trans
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩
  · simp only [CoversPatterns,not_forall] at hpatterns
    obtain ⟨i,q,j,hiq,hij,hqj,C,hC,hCc,hbad⟩ := hpatterns
    have hm : patternMass (min (d-1) (Fintype.card V-3)) =
        finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) := by
      rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]
      rfl
    rw [hm]
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩

/-- The lower bound is attained by an actual capped monomial ideal, extended
by unused variables and multiplied by a common monomial when necessary. -/
theorem exists_sharp_rejection_family {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      rejectionFraction k B = patternMass (min (d-1) (Fintype.card V-3)) := by
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct (V := V) (by omega)
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hiq,hij,hqj]
  obtain ⟨C,hC,hCc⟩ := exists_subset_card_eq
    (show min (d-1) (Fintype.card V-3) ≤ (tripleCap i q j).card by omega)
  have hCne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨B,hB,hnot,hiff⟩ := exists_pattern_isolator (k := k) C i q j hiq hij hqj hC hCne d (by omega)
  refine ⟨B,hB,hnot,?_⟩
  calc
    rejectionFraction k B = finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) :=
      finiteFraction_congr (fun o => by rw [hiff o]; simp)
    _ = _ := by rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]; rfl

theorem patternMass_formula (s : ℕ) :
    patternMass s = 2 / (((s:ℝ)+1)*((s:ℝ)+2)*((s:ℝ)+3)) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold patternMass
  push_cast
  field_simp
  nlinarith

theorem rejection_fraction_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    let t := min d (Fintype.card V-2)
    2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) ≤ rejectionFraction k B := by
  have hh := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [patternMass_formula] at hh
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simpa only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num] using hh

/-- The sharp examples attain exactly the rational expression printed in
Theorem 5.6, for every allowed degree and number of variables. -/
theorem exists_sharp_rejection_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      let t := min d (Fintype.card V-2)
      rejectionFraction k B = 2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) := by
  obtain ⟨B,hB,hnot,heq⟩ := exists_sharp_rejection_family (k := k) d hd hcard
  refine ⟨B,hB,hnot,?_⟩
  rw [heq,patternMass_formula]
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simp only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num]

theorem independent_tests_miss_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) (M : ℕ) :
    finiteFraction (fun f : Fin M → VariableOrder V =>
      ∀ j, HasLinearQuotients k B (variableRevlex (f j))) ≤
      (1-patternMass (min (d-1) (Fintype.card V-3)))^M := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let P := fun o : VariableOrder V => HasLinearQuotients k B (variableRevlex o)
  have hrej : rejectionFraction k B = 1-finiteFraction P := finiteFraction_not P
  have hbound := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [hrej] at hbound
  rw [finiteFraction_all_trials M P]
  exact pow_le_pow_left₀ (finiteFraction_nonneg P) (by linarith) M

end Characterizations

end
end CheckedCharacterizationsSource111

/-! ## Source: Characterizations.SmallRejection -/
section CheckedCharacterizationsSource112

/-! # Sharp rejection probabilities in two and three variables -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rejection_fraction_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : (1:ℝ)/6 ≤ rejectionFraction k B := by
  have hbad : ∃ o : VariableOrder V,¬HasLinearQuotients k B (variableRevlex o) := by
    by_contra hn
    apply hnot
    exact (polymatroidal_iff_universal_revlex hB).mpr (by simpa using hn)
  haveI : Nonempty {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} :=
    ⟨⟨hbad.choose,hbad.choose_spec⟩⟩
  have hc : 1 ≤ Nat.card {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hord : Nat.card (VariableOrder V) = 6 := by
    rw [Nat.card_eq_fintype_card,variableOrder_card,hcard]
    norm_num
  unfold rejectionFraction finiteFraction
  rw [hord]
  norm_num only [Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num)

theorem exists_sharp_rejection_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = (1:ℝ)/6 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let c : Exponent V := Finsupp.single i (d-2)
  let B := translatedFamily c (pairFamily i j)
  have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
  have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
  have hgen : Equigenerated B d := by
    have hh := translatedFamily_equigenerated hbase c
    have he : 2+c.degree = d := by omega
    exact he ▸ hh
  obtain ⟨o₀,h₀⟩ := exists_finalPair i j hij
  have hiff (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) ↔ o = o₀ := by
    rw [translatedFamily_linearQuotients_iff hbase c o,pairFamily_linearQuotients_iff hij (by omega) o]
    simp only [not_not]
    exact ⟨fun hf => finalPair_unique_card_three hcard hij hf h₀,fun he => he ▸ h₀⟩
  refine ⟨B,hgen,?_,?_⟩
  · intro hp
    exact pairFamily_not_polymatroidal hij (by omega) ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
    rw [finiteFraction_congr hiff]
    norm_num [finiteFraction,Nat.card_eq_fintype_card,variableOrder_card,hcard]

theorem rejection_fraction_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V ≤ 2) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : rejectionFraction k B = 1 := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  have hbad (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) :=
    fun hL => hnot (one_order_suffices_card_two hB hcard o hL)
  change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
  rw [finiteFraction_congr (fun o => iff_true_intro (hbad o)),finiteFraction_true]

theorem exists_sharp_rejection_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = 1 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  refine ⟨purePairFamily d i j,purePair_equigenerated d i j,purePair_not_polymatroidal hd hij,?_⟩
  exact rejection_fraction_two (by omega) (purePair_equigenerated d i j) (purePair_not_polymatroidal hd hij)

end Characterizations

end
end CheckedCharacterizationsSource112

/-! ## Source: Characterizations.TermOrders.MatroidMatching -/
section CheckedCharacterizationsSource113

/-! # One-sided matching of two actual matroid bases

The Hall condition follows from the fundamental circuits and the rank inequality.
Every matched exchange is feasible at the same original base.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma matroid_basis_matching (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α)) :
    ∃ f : A ≃ B, ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α) := by
  let t : A → Finset B := fun x => univ.filter (fun y => y.val ∈ M.fundCircuit x.val (B : Set α))
  have hhall : ∀ S : Finset A, S.card ≤ (S.biUnion t).card := by
    intro S
    let T : Finset α := S.image Subtype.val
    let N : Finset α := (S.biUnion t).image Subtype.val
    have hTA : (T : Set α) ⊆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hNB : (N : Set α) ⊆ B := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact y.property
    have hTN : (T : Set α) ⊆ M.closure (N : Set α) := by
      intro x hx
      obtain ⟨x, hxS, rfl⟩ := mem_image.mp hx
      by_cases hxB : x.val ∈ B
      · apply M.subset_closure _ (hNB.trans hB.subset_ground)
        exact mem_image.mpr ⟨⟨x.val, hxB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, M.mem_fundCircuit _ _⟩⟩, rfl⟩
      · have hC := hB.fundCircuit_isCircuit (hA.subset_ground x.property) hxB
        apply M.closure_subset_closure (show M.fundCircuit x.val (B : Set α) \ {x.val} ⊆ (N : Set α) from ?_)
          (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit _ _))
        intro y hy
        have hyB : y ∈ B := by
          rcases M.fundCircuit_subset_insert x.val (B : Set α) hy.1 with h | h
          · exact False.elim (hy.2 h)
          · exact h
        exact mem_image.mpr ⟨⟨y, hyB⟩, mem_biUnion.mpr ⟨x, hxS,
          mem_filter.mpr ⟨mem_univ _, hy.1⟩⟩, rfl⟩
    have hcard : T.card ≤ N.card := by
      have hh := (hA.indep.subset hTA).encard_le_eRk_of_subset hTN
      rw [M.eRk_closure_eq] at hh
      have hh' := hh.trans (M.eRk_le_encard (N : Set α))
      exact_mod_cast hh'
    simpa only [T, N, card_image_of_injective _ Subtype.coe_injective] using hcard
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hcard : Fintype.card A = Fintype.card B := by
    have h := hA.encard_eq_encard_of_isBase hB
    simpa only [Fintype.card_coe, Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj] using h
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩), ?_⟩
  intro x
  exact (mem_filter.mp (hft x)).2

lemma matroid_matching_fixes_common (M : Matroid α) (A B : Finset α)
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∈ B) : (f x).val = x.val := by
  have h := hf x
  rw [M.fundCircuit_eq_of_mem hx] at h
  exact h

lemma matroid_matching_exchange (M : Matroid α) (A B : Finset α)
    (hA : M.IsBase (A : Set α)) (hB : M.IsBase (B : Set α))
    (f : A ≃ B) (hf : ∀ x : A, (f x).val ∈ M.fundCircuit x.val (B : Set α))
    (x : A) (hx : x.val ∉ B) :
    (f x).val ∉ A ∧ M.IsBase (insert x.val ((B : Set α) \ {(f x).val})) := by
  have hfxA : (f x).val ∉ A := by
    intro hyA
    let y : A := ⟨(f x).val, hyA⟩
    have hy : (f y).val = y.val := matroid_matching_fixes_common M A B f hf y (f x).property
    have he : f y = f x := Subtype.ext hy
    have he' := f.injective he
    exact hx ((congrArg Subtype.val he') ▸ (show y.val ∈ B from (f x).property))
  refine ⟨hfxA, hB.exchange_isBase_of_indep hx ?_⟩
  have hI := (hB.indep.mem_fundCircuit_iff (by rw [hB.closure_eq]; exact hA.subset_ground x.property) hx).mp (hf x)
  have hne : x.val ≠ (f x).val := fun h => hx (h ▸ (f x).property)
  simpa only [Set.insert_sdiff_singleton_comm hne] using hI

end Characterizations.TermOrders

end
end CheckedCharacterizationsSource113

/-! ## Source: Characterizations.TermOrders.Arbitrary -/
section CheckedCharacterizationsSource114

/-! # Linear quotients in every genuine monomial term order

The matching is on actual clone-matroid bases. Common clones are fixed; every
other matched pair gives an exchange feasible at the original base. Additivity
of the given Mathlib monomial order forces one matched exchange to move earlier.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Decreasing order under the actual well-founded multiplicative monomial order. -/
def termBefore (m : MonomialOrder V) (a b : Exponent V) : Prop := m.toSyn b < m.toSyn a

lemma termBefore_irrefl (m : MonomialOrder V) (a : Exponent V) : ¬ termBefore m a a := lt_irrefl _
lemma termBefore_trans (m : MonomialOrder V) {a b c : Exponent V}
    (hab : termBefore m a b) (hbc : termBefore m b c) : termBefore m a c := hbc.trans hab
lemma termBefore_total (m : MonomialOrder V) (a b : Exponent V) (hab : a ≠ b) :
    termBefore m a b ∨ termBefore m b a := by
  exact lt_or_gt_of_ne (fun h => hab (m.toSyn.injective h)) |>.symm

private lemma clone_sum (m : MonomialOrder V) (d : ℕ) (A : Finset (Clone V d)) :
    (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn (cloneCount A) := by
  simp only [cloneCount, map_sum]
  exact Finset.sum_attach A (fun x => m.toSyn (Finsupp.single x.1 1))

lemma termOrder_exchange {B : Family V} (hB : IsPolymatroidal B)
    (m : MonomialOrder V) {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B)
    (hab : termBefore m a b) :
    ∃ i j, b i < a i ∧ a j < b j ∧ exchange b j i ∈ B ∧ termBefore m (exchange b j i) b := by
  obtain ⟨d, hdeg⟩ := hB.1
  let A := canonicalClones d a
  let D := canonicalClones d b
  let M := cloneMatroid B ⟨a, ha⟩ d hdeg hB
  have hAc : cloneCount A = a := cloneCount_canonical d a (fun i =>
    (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))
  have hDc : cloneCount D = b := cloneCount_canonical d b (fun i =>
    (coordinate_le_degree b i).trans (by rw [hdeg b hb]; omega))
  have hA : M.IsBase (A : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (A : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hAc]
  have hD : M.IsBase (D : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (D : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hDc]
  obtain ⟨f, hf⟩ := matroid_basis_matching M A D hA hD
  have hsumA : (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn a := by
    rw [clone_sum, hAc]
  have hsumD : (∑ x : A, m.toSyn (Finsupp.single (f x).val.1 1)) = m.toSyn b := by
    rw [f.sum_comp (fun y : D => m.toSyn (Finsupp.single y.val.1 1)), clone_sum, hDc]
  have hsome : ∃ x : A, m.toSyn (Finsupp.single (f x).val.1 1) < m.toSyn (Finsupp.single x.val.1 1) := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset A)) => hn x)
    rw [hsumA, hsumD] at hh
    exact (not_le_of_gt hab) hh
  obtain ⟨x, hx⟩ := hsome
  have hxD : x.val ∉ D := by
    intro h
    have he := matroid_matching_fixes_common M A D f hf x h
    rw [he] at hx
    exact (lt_irrefl _ hx)
  obtain ⟨hfA, hbase⟩ := matroid_matching_exchange M A D hA hD f hf x hxD
  have hi : b x.val.1 < a x.val.1 := by
    have h₁ : x.val.2.val < a x.val.1 := by exact (mem_filter.mp x.property).2
    have h₂ : ¬ x.val.2.val < b x.val.1 := by simpa [D, canonicalClones] using hxD
    omega
  have hj : a (f x).val.1 < b (f x).val.1 := by
    have h₁ : (f x).val.2.val < b (f x).val.1 := by exact (mem_filter.mp (f x).property).2
    have h₂ : ¬ (f x).val.2.val < a (f x).val.1 := by simpa [A, canonicalClones] using hfA
    omega
  have hw : exchange b (f x).val.1 x.val.1 ∈ B := by
    change cloneCount (clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val}))) ∈ B at hbase
    have he : clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val})) =
        insert x.val (D.erase (f x).val) := by
      ext z
      simp [and_comm]
    rw [he, cloneCount_exchange (f x).property hxD, hDc] at hbase
    exact hbase
  have hpos : 0 < b (f x).val.1 := Nat.zero_lt_of_lt hj
  have hle : Finsupp.single (f x).val.1 1 ≤ b := by
    intro v
    by_cases he : v = (f x).val.1
    · subst v; simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hpos
    · simp [Finsupp.single_apply, he, Ne.symm he]
  refine ⟨x.val.1, (f x).val.1, hi, hj, hw, ?_⟩
  change m.toSyn b < m.toSyn (exchange b (f x).val.1 x.val.1)
  calc
    m.toSyn b = m.toSyn (b - Finsupp.single (f x).val.1 1) +
        m.toSyn (Finsupp.single (f x).val.1 1) := by rw [← map_add, tsub_add_cancel_of_le hle]
    _ < m.toSyn (b - Finsupp.single (f x).val.1 1) + m.toSyn (Finsupp.single x.val.1 1) :=
      add_lt_add_of_le_of_lt le_rfl hx
    _ = m.toSyn (exchange b (f x).val.1 x.val.1) := by rw [← map_add]; rfl

/-- Theorem 3.12, for every actual admissible monomial term order, with literal
polynomial colon ideals and no replacement by a variable-permutation order. -/
theorem polymatroidal_termOrder_linearQuotients {k : Type*} [CommSemiring k]
    {B : Family V} (hB : IsPolymatroidal B) (m : MonomialOrder V) :
    HasLinearQuotients k B (termBefore m) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨i, j, hi, hj, hw, hwb⟩ := termOrder_exchange hB m ha hb hab
  have hji : j ≠ i := by intro he; subst j; omega
  exact ⟨exchange b j i, hw, hwb, i, Characterizations.exchange_sub_self b hji, hi⟩

end Characterizations.TermOrders

end
end CheckedCharacterizationsSource114

/-! ## Source: Characterizations.TermOrders.Characterization -/
section CheckedCharacterizationsSource115

/-! # The full arbitrary-term-order characterization -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid TermOrders
universe u
variable {V : Type u} {k : Type*} [Fintype V] [DecidableEq V] [CommSemiring k] [Nontrivial k]

theorem polymatroidal_iff_all_termOrder_linearQuotients {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : IsPolymatroidal B ↔
      ∀ m : MonomialOrder.{u,u} V, HasLinearQuotients k B (termBefore m) := by
  constructor
  · exact fun hp m => polymatroidal_termOrder_linearQuotients hp m
  · intro h
    apply (polymatroidal_iff_universal_revlex (k := k) hB).mpr
    intro o
    have hw := witness_of_linearQuotients hB.antichain
      (termBefore_irrefl (variableGradedRevlexOrder o)) (h (variableGradedRevlexOrder o))
    apply linearQuotients_of_witness
    intro a ha b hb hab
    have hdab : a.degree = b.degree := (hB a ha).trans (hB b hb).symm
    obtain ⟨w, hwB, hwb, i, hwi, hi⟩ := hw a ha b hb
      ((variableGradedRevlexOrder_decreasing_iff o a b hdab).mpr hab)
    exact ⟨w, hwB, (variableGradedRevlexOrder_decreasing_iff o w b
      ((hB w hwB).trans (hB b hb).symm)).mp hwb, i, hwi, hi⟩

end Characterizations

end
end CheckedCharacterizationsSource115

/-! ## Source: Characterizations.UniversalLocalization -/
section CheckedCharacterizationsSource116

/-! # Universal pure reverse-lexicographic quotients survive localization -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Corollary 3.11. `localFamily` is the actual minimal generator family of
`Ideal.map (localizationHom U) (monomialIdeal k B)`, as established in
`Localization.monomialIdeal_localFamily`. -/
theorem universal_pure_revlex_localization {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B)
    (h : ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o))
    (U : Finset V) (o : VariableOrder U) :
    HasLinearQuotients k (localFamily B U) (variableRevlex o) := by
  have hp := (polymatroidal_iff_universal_pure_revlex hB).mpr h
  exact polymatroidal_variable_linearQuotients (localFamily_polymatroidal hp U).2 o

end Characterizations

end
end CheckedCharacterizationsSource116

/-! ## Source: Characterizations.ZeroRegularity -/
section CheckedCharacterizationsSource117

/-!
# The zero-ideal obstruction to an unrestricted regularity formula

The paper admits the zero ideal among polymatroidal ideals. Its Tor support is
empty, so the maximum defining regularity is not attained at any natural number.
Nevertheless every maximal-ideal power times zero is polymatroidal, and the least
such exponent is zero. This is an explicit boundary-case obstruction to reading
Proposition 4.1's regularity conclusion without a nonzero-ideal restriction.
-/

noncomputable section

namespace Characterizations

open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem zero_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0, ?_⟩, ?_⟩ <;> simp [Equigenerated, ExchangeAxiom]

theorem empty_family_equigenerated_two : Equigenerated (∅ : Family V) 2 := by
  simp [Equigenerated]

theorem empty_family_betti_zero (a : Exponent V) (i : ℕ) :
    bettiNumber (k := k) (∅ : Family V) a i = 0 := by
  by_contra h
  exact gradedBettiNonzero_empty a i
    ((bettiNumber_pos_iff _ _ _).mp (Nat.pos_of_ne_zero h))

/-- The actual zero ideal has no attained natural-number Tor regularity. -/
theorem zero_ideal_no_torRegularity :
    ¬ ∃ r : ℕ, IsTorRegularity (k := k) (∅ : Family V) r := by
  rintro ⟨r, _, i, a, ha, _⟩
  exact ha (empty_family_betti_zero a i)

theorem empty_localize_polymatroidal (U : Finset V) :
    IsPolymatroidal (localize (∅ : Family V) U) := by
  simpa [localize, minimalFamily] using (zero_family_polymatroidal (V := V))

theorem empty_thickening_polymatroidal (q : ℕ) :
    IsPolymatroidal (thickening (∅ : Family V) q) := by
  simpa [thickening] using (zero_family_polymatroidal (V := V))

theorem zero_ideal_least_polymatroidal_power :
    IsLeast {q : ℕ | IsPolymatroidal (thickening (∅ : Family V) q)} 0 :=
  ⟨empty_thickening_polymatroidal 0, fun _ _ => Nat.zero_le _⟩

theorem zero_ideal_integralClosure :
    {f : MvPolynomial V k | IntegralOverIdeal (⊥ : Ideal (MvPolynomial V k)) f} =
      (⊥ : Ideal (MvPolynomial V k)) := by
  ext f
  exact ⟨fun h => integrallyClosed_bot f h, fun h => integralOverIdeal_of_mem h⟩

theorem zero_ideal_closure_quotient_finiteLength :
    IsFiniteLength (MvPolynomial V k)
      (Strands.idealDifferenceQuotient (k := k) (∅ : Family V) ∅) := by
  apply Strands.idealDifferenceQuotient_finiteLength
  have he : {a : Exponent V | Contains (∅ : Family V) a ∧ ¬Contains ∅ a} = ∅ := by
    ext a
    simp
  rw [he]
  exact Set.finite_empty

/-- Multiplication by an actual maximal-ideal power cannot alter zero. -/
theorem zero_ideal_all_actual_powers_polymatroidal (q : ℕ) :
    IsPolymatroidalIdeal
      ((Ideal.span (Set.range (MvPolynomial.X : V → MvPolynomial V k))) ^ q * ⊥) := by
  simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))

/-- Formal negation of the unrestricted attained-regularity version of the
"in particular" conclusion of Proposition 4.1. The counterexample is the
empty minimal generating family, representing the actual zero ideal. -/
theorem unrestricted_proposition41_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
          IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r - 2)) := by
  intro h
  obtain ⟨r, hr, _⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  exact zero_ideal_no_torRegularity ⟨r, hr⟩

/-- The actual nonzero Tor degrees `j-i`, embedded in the integers with a
bottom element representing negative infinity. -/
def torRegularityDegrees (B : Family V) : Set (WithBot ℤ) :=
  {x | ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧
    x = (((a.degree : ℤ) - i : ℤ) : WithBot ℤ)}

theorem zero_ideal_regularityDegrees_empty :
    torRegularityDegrees (k := k) (∅ : Family V) = ∅ := by
  ext x
  simp [torRegularityDegrees, empty_family_betti_zero]

/-- Under the standard extended convention, regularity of zero is negative
infinity, the least upper bound of its empty actual Tor-degree support. -/
theorem zero_ideal_extended_regularity :
    IsLUB (torRegularityDegrees (k := k) (∅ : Family V)) ⊥ := by
  rw [zero_ideal_regularityDegrees_empty]
  exact isLUB_empty

/-- Subtracting the chosen generating degree two from negative infinity
still does not give the actual least polymatroidal power, which is zero.
Addition of the embedded integer `-2` is the usual finite degree shift. -/
theorem zero_ideal_extended_regularity_difference_ne_least :
    (0 : WithBot ℤ) ≠ (⊥ : WithBot ℤ) + ((-2 : ℤ) : WithBot ℤ) := by
  simp

/-- The unrestricted formula is false even when regularity is interpreted
as an extended least upper bound, with `reg(0) = -∞`. -/
theorem unrestricted_proposition41_extended_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : WithBot ℤ, IsLUB (torRegularityDegrees (k := k) B) r ∧
          ∃ q : ℕ, IsLeast {n : ℕ | IsPolymatroidal (thickening B n)} q ∧
            ((q : ℤ) : WithBot ℤ) = r + ((-2 : ℤ) : WithBot ℤ)) := by
  intro h
  obtain ⟨r, hr, q, _, he⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  have hr0 : r = ⊥ := hr.unique zero_ideal_extended_regularity
  simpa [hr0] using he

end Characterizations

end
end CheckedCharacterizationsSource117
