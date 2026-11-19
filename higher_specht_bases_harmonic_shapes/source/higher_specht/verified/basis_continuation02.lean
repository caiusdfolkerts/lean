module

public import higher_specht.verified.basis_continuation01
public import tau_ceti.representation_theory.symmetric.specht.decomposition
public import Mathlib.RingTheory.Flat.Domain
public import tau_ceti.representation_theory.symmetric.specht.standard_basis
public import Mathlib.Data.Fin.Tuple.Sort

/- Generated ordinary proof stage. See audit/staged_specht_basis32/BasisContinuation02/manifest.json. -/

@[expose] public section

section CanonicalSource32
/- Source: HigherSpecht/StaircaseIndependence.lean -/



/-!
# Griffin staircase monomials: independence in every characteristic

An injective filling decreasing up each column describes a shuffle of the
descending column staircases.  Its actual column Vandermonde product is
lexicographically monic.  Contraction supplies the triangular witnesses for
every exponent below the staircase.  This proves monomial independence over
arbitrary nontrivial commutative rings; spanning is a separate Gröbner step.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped MonomialOrder

namespace HigherSpecht

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} {μ : YoungDiagram}

def ColumnDescending (U : ↥μ.cells ↪ Fin n) : Prop :=
  ∀ j, StrictAnti (columnEmbedding U j)

theorem lex_degree_X_sub_X {i j : Fin n} (hij : i < j) :
    MonomialOrder.lex.degree (MvPolynomial.X i - MvPolynomial.X j : PolynomialRing n R) =
      Finsupp.single i 1 := by
  have hlt : MonomialOrder.lex.degree (MvPolynomial.X j : PolynomialRing n R) ≺[MonomialOrder.lex]
      MonomialOrder.lex.degree (MvPolynomial.X i : PolynomialRing n R) := by
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
    exact Finsupp.Lex.single_lt_iff.mpr hij
  rw [MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_X]

theorem lex_monic_X_sub_X {i j : Fin n} (hij : i < j) :
    MonomialOrder.lex.Monic (MvPolynomial.X i - MvPolynomial.X j : PolynomialRing n R) := by
  have hlt : MonomialOrder.lex.degree (MvPolynomial.X j : PolynomialRing n R) ≺[MonomialOrder.lex]
      MonomialOrder.lex.degree (MvPolynomial.X i : PolynomialRing n R) := by
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
    exact Finsupp.Lex.single_lt_iff.mpr hij
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff_sub_of_lt hlt,
    MonomialOrder.leadingCoeff_X]

theorem columnAlternant_eq_vandermonde (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    columnAlternant (R := R) U j = ∏ r : Fin (μ.colLen j),
      ∏ t ∈ Finset.Ioi r,
        (MvPolynomial.X (columnEmbedding U j t) - MvPolynomial.X (columnEmbedding U j r)) := by
  rw [columnAlternant, TauCeti.alternant_fin_val_eq_vandermonde]
  simp only [map_prod, map_sub, MvPolynomial.rename_X]

def columnLeader (U : ↥μ.cells ↪ Fin n) (j : ℕ) : Fin n →₀ ℕ :=
  ∑ r : Fin (μ.colLen j), ∑ t ∈ Finset.Ioi r, Finsupp.single (columnEmbedding U j t) 1

theorem columnLeader_eq_rowSum (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    columnLeader U j = ∑ r : Fin (μ.colLen j), Finsupp.single (columnEmbedding U j r) r.val := by
  classical
  unfold columnLeader
  calc
    (∑ r : Fin (μ.colLen j), ∑ t ∈ Finset.Ioi r,
        Finsupp.single (columnEmbedding U j t) 1) =
        ∑ r : Fin (μ.colLen j), ∑ t : Fin (μ.colLen j),
          if r < t then Finsupp.single (columnEmbedding U j t) 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_filter]
      congr 1
      ext t
      simp
    _ = ∑ t : Fin (μ.colLen j), ∑ r : Fin (μ.colLen j),
        if r < t then Finsupp.single (columnEmbedding U j t) 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      have hset : (Finset.univ.filter fun r : Fin (μ.colLen j) => r < t) = Finset.Iio t := by
        ext r
        simp
      rw [hset, Finset.sum_const, Fin.card_Iio]
      simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem columnAlternant_monic (U : ↥μ.cells ↪ Fin n) (hU : ColumnDescending U) (j : ℕ) :
    MonomialOrder.lex.Monic (columnAlternant (R := R) U j) := by
  rw [columnAlternant_eq_vandermonde]
  apply MonomialOrder.Monic.prod
  intro r hr
  apply MonomialOrder.Monic.prod
  intro t ht
  exact lex_monic_X_sub_X (hU j (Finset.mem_Ioi.mp ht))

theorem columnAlternant_degree (U : ↥μ.cells ↪ Fin n) (hU : ColumnDescending U) (j : ℕ) :
    MonomialOrder.lex.degree (columnAlternant (R := R) U j) = columnLeader U j := by
  rw [columnAlternant_eq_vandermonde]
  rw [MonomialOrder.degree_prod_of_regular]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [MonomialOrder.degree_prod_of_regular]
    · apply Finset.sum_congr rfl
      intro t ht
      exact lex_degree_X_sub_X (hU j (Finset.mem_Ioi.mp ht))
    · intro t ht
      rw [(lex_monic_X_sub_X (R := R) (hU j (Finset.mem_Ioi.mp ht))).leadingCoeff_eq_one]
      exact isRegular_one
  · intro r hr
    have hmonic : MonomialOrder.lex.Monic
        (∏ t ∈ Finset.Ioi r,
          (MvPolynomial.X (columnEmbedding U j t) - MvPolynomial.X (columnEmbedding U j r) :
            PolynomialRing n R)) :=
      MonomialOrder.Monic.prod fun t ht => lex_monic_X_sub_X (hU j (Finset.mem_Ioi.mp ht))
    rw [hmonic.leadingCoeff_eq_one]
    exact isRegular_one

def outsideLeader (U : ↥μ.cells ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  ∑ i ∈ (fillingLabels U)ᶜ, Finsupp.single i (s - 1)

def staircaseVector (U : ↥μ.cells ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  (∑ j ∈ Finset.range n, columnLeader U j) + outsideLeader U s

theorem outsidePower_monic (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    MonomialOrder.lex.Monic (outsidePower (R := R) U s) := by
  exact MonomialOrder.Monic.prod fun i hi => MonomialOrder.monic_X.pow

theorem outsidePower_degree (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    MonomialOrder.lex.degree (outsidePower (R := R) U s) = outsideLeader U s := by
  rw [outsidePower, MonomialOrder.degree_prod_of_regular]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero]
    · rw [MonomialOrder.degree_X]
      simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one, Nat.cast_id]
    · rw [MonomialOrder.leadingCoeff_X, one_pow]
      exact one_ne_zero
  · intro i hi
    rw [(MonomialOrder.monic_X.pow (m := MonomialOrder.lex) (n := s - 1)).leadingCoeff_eq_one]
    exact isRegular_one

theorem columnWitness_monic (U : ↥μ.cells ↪ Fin n) (hU : ColumnDescending U) (s : ℕ) :
    MonomialOrder.lex.Monic (columnWitness (R := R) U s) :=
  (MonomialOrder.Monic.prod fun j hj => columnAlternant_monic U hU j).mul (outsidePower_monic U s)

theorem columnWitness_degree (U : ↥μ.cells ↪ Fin n) (hU : ColumnDescending U) (s : ℕ) :
    MonomialOrder.lex.degree (columnWitness (R := R) U s) = staircaseVector U s := by
  rw [columnWitness, MonomialOrder.degree_mul_of_isRegular_left]
  · rw [MonomialOrder.degree_prod_of_regular]
    · simp_rw [columnAlternant_degree U hU, outsidePower_degree]
      rfl
    · intro j hj
      rw [(columnAlternant_monic (R := R) U hU j).leadingCoeff_eq_one]
      exact isRegular_one
  · rw [(MonomialOrder.Monic.prod fun j hj => columnAlternant_monic (R := R) U hU j).leadingCoeff_eq_one]
    exact isRegular_one
  · exact (outsidePower_monic (R := R) U s).ne_zero

/-- The actual downward closure of the shuffled column staircases, with
the outside entries equal to s−1.  The row-sum identity above supplies the
descending sequence h−1,…,0 in each ordered column. -/
def GriffinStaircaseExponents (n : ℕ) (μ : YoungDiagram) (s : ℕ) : Set (Fin n →₀ ℕ) :=
  {c | ∃ U : ↥μ.cells ↪ Fin n, ColumnDescending U ∧ c ≤ staircaseVector U s}

/-- This is the independence half of Griffin's standard-monomial theorem,
with no characteristic restriction and no unproved dimension input. -/
theorem griffin_staircase_monomials_linearIndependent (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    LinearIndependent R (fun c : GriffinStaircaseExponents n μ s =>
      Ideal.Quotient.mk (griffinIdeal R n μ s) (MvPolynomial.monomial c.val 1)) := by
  apply linearIndependent_quotient_monomials_of_monic_harmonics MonomialOrder.lex
  rintro c ⟨U, hU, hc⟩
  let w := columnWitness (R := R) U s
  have hw : MonomialOrder.lex.Monic w := columnWitness_monic U hU s
  have hdeg : MonomialOrder.lex.degree w = staircaseVector U s := columnWitness_degree U hU s
  have hc' : c ≤ MonomialOrder.lex.degree w := by rwa [hdeg]
  have hsub : MonomialOrder.lex.degree w - c ≤ MonomialOrder.lex.degree w := tsub_le_self
  refine ⟨contractMonomial (MonomialOrder.lex.degree w - c) w,
    contractMonomial_mem_dividedHarmonics (columnWitness_mem_griffinHarmonics U hs hheight) _,
    ?_, monic_contractMonomial MonomialOrder.lex hw _ hsub⟩
  rw [degree_contractMonomial MonomialOrder.lex hw.ne_zero _ hsub,
    tsub_tsub_cancel_of_le hc']

def UntruncatedStaircaseExponents (n : ℕ) (μ : YoungDiagram) : Set (Fin n →₀ ℕ) :=
  {c | ∃ s : ℕ, c ∈ GriffinStaircaseExponents n μ s}

theorem untruncated_staircase_monomials_linearIndependent :
    LinearIndependent R (fun c : UntruncatedStaircaseExponents n μ =>
      Ideal.Quotient.mk (untruncatedIdeal R n μ) (MvPolynomial.monomial c.val 1)) := by
  apply linearIndependent_quotient_monomials_of_monic_harmonics MonomialOrder.lex
  rintro c ⟨s, U, hU, hc⟩
  let w := columnWitness (R := R) U s
  have hw : MonomialOrder.lex.Monic w := columnWitness_monic U hU s
  have hdeg : MonomialOrder.lex.degree w = staircaseVector U s := columnWitness_degree U hU s
  have hc' : c ≤ MonomialOrder.lex.degree w := by rwa [hdeg]
  have hsub : MonomialOrder.lex.degree w - c ≤ MonomialOrder.lex.degree w := tsub_le_self
  refine ⟨contractMonomial (MonomialOrder.lex.degree w - c) w,
    contractMonomial_mem_dividedHarmonics (columnWitness_mem_untruncatedHarmonics U s) _,
    ?_, monic_contractMonomial MonomialOrder.lex hw _ hsub⟩
  rw [degree_contractMonomial MonomialOrder.lex hw.ne_zero _ hsub,
    tsub_tsub_cancel_of_le hc']

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/StaircaseOperations.lean -/



/-!
# Prefix operations on the actual staircase shuffles

The smallest variable can be placed either outside the diagram or at the
top of a corner column.  These operations suffice to prove coverage by the
recursive reductions: a non-staircase exponent remains non-staircase after
every admissible prefix placement.  No unproved enumeration or dimension
formula is used here.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {n : ℕ} {μ : YoungDiagram}

theorem cell_column_lt_ambient (U : ↥μ.cells ↪ Fin n) (c : ↥μ.cells) : c.val.2 < n := by
  have hcard := Fintype.card_le_of_injective U U.injective
  have hcard' : μ.card ≤ n := by simpa only [Fintype.card_coe, Fintype.card_fin,
    YoungDiagram.card] using hcard
  have hc := YoungDiagram.mem_iff_lt_rowLen.mp c.property
  have hrow := μ.rowLen_anti 0 c.val.1 (Nat.zero_le _)
  exact hc.trans_le (hrow.trans ((rowLen_zero_le_card μ).trans hcard'))

theorem columnLeader_apply_cell (U : ↥μ.cells ↪ Fin n) (c : ↥μ.cells) (j : ℕ) :
    columnLeader U j (U c) = if j = c.val.2 then c.val.1 else 0 := by
  classical
  rw [columnLeader_eq_rowSum, Finsupp.finsetSum_apply]
  by_cases hj : j = c.val.2
  · subst j
    rw [if_pos rfl]
    let r : Fin (μ.colLen c.val.2) := ⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp c.property⟩
    rw [Finset.sum_eq_single r]
    · have hr : columnEmbedding U c.val.2 r = U c := by
        apply congrArg U
        exact Subtype.ext rfl
      rw [hr, Finsupp.single_eq_same]
    · intro t ht htr
      have hne : columnEmbedding U c.val.2 t ≠ U c := by
        intro he
        have hrow := congrArg (fun d : ↥μ.cells => d.val.1) (U.injective he)
        exact htr (Fin.ext hrow)
      exact Finsupp.single_eq_of_ne hne.symm
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro t ht
    have hne : columnEmbedding U j t ≠ U c := by
      intro he
      exact hj (congrArg (fun d : ↥μ.cells => d.val.2) (U.injective he))
    exact Finsupp.single_eq_of_ne hne.symm

theorem columnLeader_apply_outside (U : ↥μ.cells ↪ Fin n) {i : Fin n}
    (hi : i ∉ Set.range U) (j : ℕ) : columnLeader U j i = 0 := by
  rw [columnLeader_eq_rowSum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  apply Finsupp.single_eq_of_ne
  intro he
  exact hi ⟨⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩, he.symm⟩

theorem mem_fillingLabels_iff (U : ↥μ.cells ↪ Fin n) (i : Fin n) :
    i ∈ fillingLabels U ↔ i ∈ Set.range U := by
  simp [fillingLabels]

theorem outsideLeader_apply (U : ↥μ.cells ↪ Fin n) (s : ℕ) (i : Fin n) :
    outsideLeader U s i = if i ∈ Set.range U then 0 else s - 1 := by
  classical
  rw [outsideLeader, Finsupp.finsetSum_apply]
  by_cases hi : i ∈ Set.range U
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finsupp.single_eq_of_ne
    intro he
    subst j
    exact (Finset.mem_compl.mp hj) ((mem_fillingLabels_iff U i).mpr hi)
  · rw [if_neg hi, Finset.sum_eq_single i]
    · exact Finsupp.single_eq_same
    · intro j hj hji
      exact Finsupp.single_eq_of_ne hji.symm
    · intro h
      exact (h (Finset.mem_compl.mpr (by rwa [mem_fillingLabels_iff]))).elim

theorem staircaseVector_apply_cell (U : ↥μ.cells ↪ Fin n) (s : ℕ) (c : ↥μ.cells) :
    staircaseVector U s (U c) = c.val.1 := by
  rw [staircaseVector, Finsupp.add_apply, Finsupp.finsetSum_apply]
  simp_rw [columnLeader_apply_cell]
  rw [Finset.sum_eq_single c.val.2]
  · rw [if_pos rfl, outsideLeader_apply, if_pos ⟨c, rfl⟩, add_zero]
  · intro j hj hjc
    simp only [hjc, if_false]
  · exact fun h => (h (Finset.mem_range.mpr (cell_column_lt_ambient U c))).elim

theorem staircaseVector_apply_outside (U : ↥μ.cells ↪ Fin n) (s : ℕ) {i : Fin n}
    (hi : i ∉ Set.range U) : staircaseVector U s i = s - 1 := by
  rw [staircaseVector, Finsupp.add_apply, Finsupp.finsetSum_apply]
  simp only [columnLeader_apply_outside U hi, Finset.sum_const_zero,
    outsideLeader_apply, if_neg hi, zero_add]

/-- A shuffle of descending column staircases, with no bound on the
positions left outside the diagram. -/
def ShuffleBound (n : ℕ) (μ : YoungDiagram) (a : Fin n →₀ ℕ) : Prop :=
  ∃ U : ↥μ.cells ↪ Fin n, ColumnDescending U ∧ ∀ c : ↥μ.cells, a (U c) ≤ c.val.1

theorem mem_untruncatedStaircaseExponents_iff (a : Fin n →₀ ℕ) :
    a ∈ UntruncatedStaircaseExponents n μ ↔ ShuffleBound n μ a := by
  constructor
  · rintro ⟨s, U, hU, ha⟩
    exact ⟨U, hU, fun c => by simpa only [staircaseVector_apply_cell] using ha (U c)⟩
  · rintro ⟨U, hU, ha⟩
    refine ⟨a.degree + 1, U, hU, ?_⟩
    intro i
    by_cases hi : i ∈ Set.range U
    · obtain ⟨c, rfl⟩ := hi
      rw [staircaseVector_apply_cell]
      exact ha c
    · rw [staircaseVector_apply_outside U _ hi, Nat.add_sub_cancel]
      exact Finsupp.le_degree i a

theorem mem_griffinStaircaseExponents_iff (a : Fin n →₀ ℕ) {s : ℕ}
    (hs : 0 < s) (hheight : μ.colLen 0 ≤ s) :
    a ∈ GriffinStaircaseExponents n μ s ↔ ShuffleBound n μ a ∧ ∀ i, a i < s := by
  constructor
  · rintro ⟨U, hU, ha⟩
    refine ⟨⟨U, hU, fun c => by simpa only [staircaseVector_apply_cell] using ha (U c)⟩, ?_⟩
    intro i
    by_cases hi : i ∈ Set.range U
    · obtain ⟨c, rfl⟩ := hi
      have hc := ha (U c)
      rw [staircaseVector_apply_cell] at hc
      have hrow : c.val.1 < μ.colLen c.val.2 :=
        YoungDiagram.mem_iff_lt_colLen.mp c.property
      have hcol := μ.colLen_anti 0 c.val.2 (Nat.zero_le _)
      exact hc.trans_lt (hrow.trans_le (hcol.trans hheight))
    · have hh := ha i
      rw [staircaseVector_apply_outside U s hi] at hh
      omega
  · rintro ⟨⟨U, hU, ha⟩, hb⟩
    refine ⟨U, hU, ?_⟩
    intro i
    by_cases hi : i ∈ Set.range U
    · obtain ⟨c, rfl⟩ := hi
      rw [staircaseVector_apply_cell]
      exact ha c
    · rw [staircaseVector_apply_outside U s hi]
      exact Nat.le_sub_one_of_lt (hb i)

theorem shuffleBound_false_of_card_gt {a : Fin n →₀ ℕ} (hn : n < μ.card) :
    ¬ ShuffleBound n μ a := by
  rintro ⟨U, hU, ha⟩
  have hcard := Fintype.card_le_of_injective U U.injective
  have hle : μ.card ≤ n := by
    simpa only [Fintype.card_coe, Fintype.card_fin, YoungDiagram.card] using hcard
  omega

def tailExponent (a : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => a i.succ

@[simp] theorem tailExponent_apply (a : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    tailExponent a i = a i.succ := rfl

def shiftFilling (U : ↥μ.cells ↪ Fin n) : ↥μ.cells ↪ Fin (n + 1) := U.trans (Fin.succEmb n)

theorem columnDescending_shift (U : ↥μ.cells ↪ Fin n) (hU : ColumnDescending U) :
    ColumnDescending (shiftFilling U) := by
  intro j r t hrt
  exact Fin.succ_lt_succ_iff.mpr (hU j hrt)

theorem shuffleBound_cons_outside (a : Fin (n + 1) →₀ ℕ)
    (ha : ShuffleBound n μ (tailExponent a)) : ShuffleBound (n + 1) μ a := by
  obtain ⟨U, hU, hb⟩ := ha
  exact ⟨shiftFilling U, columnDescending_shift U hU, hb⟩

def extendCornerFilling {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (U : ↥(μ.erase c).cells ↪ Fin n) : ↥μ.cells ↪ Fin (n + 1) where
  toFun x := if h : x.val = c then 0 else
    (U ⟨x.val, hc.mem_erase_iff.mpr ⟨x.property, h⟩⟩).succ
  inj' x y hxy := by
    classical
    dsimp only at hxy
    split_ifs at hxy with hx hy hy
    · exact Subtype.ext (hx.trans hy.symm)
    · exact (Fin.succ_ne_zero _ hxy.symm).elim
    · exact (Fin.succ_ne_zero _ hxy).elim
    · have h := U.injective (Fin.succ_injective _ hxy)
      exact Subtype.ext (congrArg (fun z : ↥(μ.erase c).cells => z.val) h)

theorem columnDescending_extendCorner {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (U : ↥(μ.erase c).cells ↪ Fin n) (hU : ColumnDescending U) :
    ColumnDescending (extendCornerFilling hc U) := by
  intro j r t hrt
  change (if ht : (t.val, j) = c then 0 else _) < (if hr : (r.val, j) = c then 0 else _)
  by_cases ht : (t.val, j) = c
  · rw [dif_pos ht]
    have hr : (r.val, j) ≠ c := by
      intro hr
      have := congrArg Prod.fst (hr.trans ht.symm)
      exact hrt.ne (Fin.ext this)
    rw [dif_neg hr]
    exact Fin.succ_pos _
  · have hr : (r.val, j) ≠ c := by
      intro hr
      have hcmax := hc.eq_of_le (YoungDiagram.mem_iff_lt_colLen.mpr t.isLt)
        (by rw [← hr]; exact ⟨hrt.le, le_rfl⟩)
      exact ht hcmax
    rw [dif_neg ht, dif_neg hr]
    apply Fin.succ_lt_succ_iff.mpr
    let r' : Fin ((μ.erase c).colLen j) := ⟨r.val,
      YoungDiagram.mem_iff_lt_colLen.mp (hc.mem_erase_iff.mpr
        ⟨YoungDiagram.mem_iff_lt_colLen.mpr r.isLt, hr⟩)⟩
    let t' : Fin ((μ.erase c).colLen j) := ⟨t.val,
      YoungDiagram.mem_iff_lt_colLen.mp (hc.mem_erase_iff.mpr
        ⟨YoungDiagram.mem_iff_lt_colLen.mpr t.isLt, ht⟩)⟩
    exact hU j (show r' < t' from hrt)

theorem shuffleBound_cons_corner {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (a : Fin (n + 1) →₀ ℕ) (hzero : a 0 ≤ c.1)
    (ha : ShuffleBound n (μ.erase c) (tailExponent a)) : ShuffleBound (n + 1) μ a := by
  obtain ⟨U, hU, hb⟩ := ha
  refine ⟨extendCornerFilling hc U, columnDescending_extendCorner hc U hU, ?_⟩
  intro x
  change a (if h : x.val = c then 0 else _) ≤ x.val.1
  split_ifs with hx
  · simpa only [hx] using hzero
  · exact hb ⟨x.val, hc.mem_erase_iff.mpr ⟨x.property, hx⟩⟩

/-- The rightmost column reaching a given row ends in a genuine corner.
Its next-column height is at most that row, which is exactly Yu's required
leading exponent bound. -/
theorem exists_corner_at_cut (μ : YoungDiagram) {a : ℕ} (ha : a < μ.colLen 0) :
    ∃ c : ℕ × ℕ, YoungDiagram.IsCorner μ c ∧ a ≤ c.1 ∧ μ.colLen (c.2 + 1) ≤ a := by
  have hrow : 0 < μ.rowLen a := YoungDiagram.mem_iff_lt_rowLen.mp
    (YoungDiagram.mem_iff_lt_colLen.mpr ha)
  let j := μ.rowLen a - 1
  have hmem : (a, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by dsimp [j]; omega)
  have hh : a < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hmem
  let c := (μ.colLen j - 1, j)
  have hnext : μ.colLen (j + 1) ≤ a := by
    by_contra h
    have hm : (a, j + 1) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have he := YoungDiagram.mem_iff_lt_rowLen.mp hm
    dsimp [j] at he
    omega
  refine ⟨c, ?_, by dsimp [c]; omega, hnext⟩
  refine (YoungDiagram.isCorner_def μ c).mpr ⟨?_, ?_, ?_⟩
  · apply YoungDiagram.mem_iff_lt_colLen.mpr
    omega
  · intro hm
    have he := YoungDiagram.mem_iff_lt_colLen.mp hm
    dsimp [c] at he
    omega
  · intro hm
    have he := YoungDiagram.mem_iff_lt_colLen.mp hm
    dsimp [c] at he
    omega

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/MinimumLexReduction.lean -/



/-!
# Homogeneous monic reductions with a minimum lexicographic term

Yu's homogeneous reverse-lexicographic reductions can be used without
installing a new global monomial order.  On each fixed total degree there
are finitely many exponents.  A relation with coefficient one at its least
lexicographic exponent replaces that monomial by strictly larger exponents,
so reverse induction proves spanning.  The argument is valid integrally.
-/

noncomputable section

open Finset MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

structure MinimumLexMonic (f : PolynomialRing n R) (a : Fin n →₀ ℕ) : Prop where
  homogeneous : f.IsHomogeneous a.degree
  coefficient : f.coeff a = 1
  minimum : ∀ b, f.coeff b ≠ 0 → b ≠ a → toLex a < toLex b

theorem minimumLexMonic_monomial (a : Fin n →₀ ℕ) :
    MinimumLexMonic (MvPolynomial.monomial a (1 : R)) a := by
  refine ⟨MvPolynomial.isHomogeneous_monomial 1 rfl, by simp, ?_⟩
  intro b hb hba
  simp [MvPolynomial.coeff_monomial, hba.symm] at hb

theorem lex_cons_lt_cons_of_head {a b : ℕ} (hab : a < b)
    (u v : Fin n →₀ ℕ) : toLex (u.cons a) < toLex (v.cons b) := by
  refine ⟨0, ?_, ?_⟩
  · intro i hi
    exact (Fin.not_lt_zero i hi).elim
  · exact hab

theorem lex_cons_lt_cons_of_tail (a : ℕ) {u v : Fin n →₀ ℕ}
    (huv : toLex u < toLex v) : toLex (u.cons a) < toLex (v.cons a) := by
  obtain ⟨i, hi, huv⟩ := huv
  refine ⟨i.succ, ?_, huv⟩
  intro j hj
  cases j using Fin.cases with
  | zero => rfl
  | succ j => exact hi j (Fin.succ_lt_succ_iff.mp hj)

theorem finSuccEquiv_rename_succ (f : PolynomialRing n R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.finSuccEquiv_apply]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ, hf]

theorem coeff_lift_of_head_le (a : ℕ) (f : PolynomialRing n R)
    (F Q : PolynomialRing (n + 1) R)
    (hF : F = MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ f +
      MvPolynomial.X 0 ^ (a + 1) * Q)
    (b : Fin (n + 1) →₀ ℕ) (hb : b 0 ≤ a) :
    F.coeff b = if b 0 = a then f.coeff b.tail else 0 := by
  have h := MvPolynomial.finSuccEquiv_coeff_coeff b.tail F (b 0)
  rw [Finsupp.cons_tail] at h
  rw [← h, hF, map_add, map_mul, map_mul, map_pow, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_rename_succ,
    Polynomial.coeff_add]
  rw [mul_comm (Polynomial.X ^ a) (Polynomial.C f), Polynomial.coeff_C_mul_X_pow]
  rw [mul_comm (Polynomial.X ^ (a + 1)), Polynomial.coeff_mul_X_pow']
  simp only [show ¬ a + 1 ≤ b 0 by omega, if_false, add_zero]
  by_cases he : b 0 = a <;> simp [he]

theorem minimumLexMonic_homogeneous_lift (a : ℕ) {f : PolynomialRing n R}
    {b : Fin n →₀ ℕ} (hf : MinimumLexMonic f b)
    (F Q : PolynomialRing (n + 1) R)
    (hF : F = MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ f +
      MvPolynomial.X 0 ^ (a + 1) * Q) :
    MinimumLexMonic (MvPolynomial.homogeneousComponent (b.cons a).degree F) (b.cons a) := by
  refine ⟨MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
  · rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
      coeff_lift_of_head_le a f F Q hF _ (by simp)]
    simp only [Finsupp.cons_zero, Finsupp.tail_cons, if_pos rfl, hf.coefficient, ite_true]
  · intro beta hbeta hne
    have hdegree : beta.degree = (b.cons a).degree := by
      by_contra hd
      rw [MvPolynomial.coeff_homogeneousComponent, if_neg hd] at hbeta
      exact hbeta rfl
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdegree] at hbeta
    by_cases hhead : beta 0 ≤ a
    · have heq : beta 0 = a := by
        by_contra hn
        rw [coeff_lift_of_head_le a f F Q hF beta hhead, if_neg hn] at hbeta
        exact hbeta rfl
      rw [coeff_lift_of_head_le a f F Q hF beta hhead, if_pos heq] at hbeta
      have htail : beta.tail ≠ b := by
        intro ht
        apply hne
        rw [← Finsupp.cons_tail beta, heq, ht]
      rw [← Finsupp.cons_tail beta, heq]
      exact lex_cons_lt_cons_of_tail a (hf.minimum _ hbeta htail)
    · rw [← Finsupp.cons_tail beta]
      exact lex_cons_lt_cons_of_head (lt_of_not_ge hhead) b beta.tail

/-- A homogeneous reduction with least term x^a can be used in a
well-founded reverse induction inside its finite homogeneous component. -/
theorem monomials_span_of_minimumLex_reductions [Nontrivial R]
    (I : Ideal (PolynomialRing n R)) (C : Set (Fin n →₀ ℕ))
    (hred : ∀ a ∉ C, ∃ f ∈ I, MinimumLexMonic f a) :
    Submodule.span R (Set.range fun a : C =>
      Ideal.Quotient.mk I (MvPolynomial.monomial a.val 1)) = ⊤ := by
  classical
  let V := Submodule.span R (Set.range fun a : C =>
    Ideal.Quotient.mk I (MvPolynomial.monomial a.val 1))
  have hmono (a : Fin n →₀ ℕ) : Ideal.Quotient.mk I (MvPolynomial.monomial a 1) ∈ V := by
    let S : Set (Lex (Fin n →₀ ℕ)) := {b | (ofLex b).degree = a.degree}
    have hS : S.Finite := by
      have hfin := (Finsupp.finite_of_degree_eq (σ := Fin n) a.degree).image toLex
      convert hfin using 1
      ext b
      simp [S]
    have hWF : S.WellFoundedOn (· > ·) := hS.wellFoundedOn
    apply hWF.induction (x := toLex a)
      (P := fun b => Ideal.Quotient.mk I (MvPolynomial.monomial (ofLex b) 1) ∈ V) rfl
    intro b hb ih
    by_cases hbc : ofLex b ∈ C
    · exact Submodule.subset_span ⟨⟨ofLex b, hbc⟩, rfl⟩
    · obtain ⟨f, hfI, hf⟩ := hred (ofLex b) hbc
      have hsum : Ideal.Quotient.mk I
          (∑ c ∈ f.support.erase (ofLex b), MvPolynomial.monomial c (f.coeff c)) ∈ V := by
        rw [map_sum]
        apply Submodule.sum_mem
        intro c hc
        have hcne := (Finset.mem_erase.mp hc).1
        have hcs := (Finset.mem_erase.mp hc).2
        have hc0 := MvPolynomial.mem_support_iff.mp hcs
        have hdeg : c.degree = (ofLex b).degree := by
          by_contra h
          exact hc0 (hf.homogeneous.coeff_eq_zero h)
        have hih := ih (toLex c) (by exact hdeg.trans hb)
          (hf.minimum c hc0 hcne)
        have hterm : MvPolynomial.monomial c (f.coeff c) =
            f.coeff c • MvPolynomial.monomial c (1 : R) := by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hterm]
        change (Ideal.Quotient.mkₐ R I) (f.coeff c • MvPolynomial.monomial c (1 : R)) ∈ V
        rw [map_smul]
        exact V.smul_mem _ hih
      have hfrepr : f = MvPolynomial.monomial (ofLex b) 1 +
          ∑ c ∈ f.support.erase (ofLex b), MvPolynomial.monomial c (f.coeff c) := by
        have hmem : ofLex b ∈ f.support := MvPolynomial.mem_support_iff.mpr
          (by rw [hf.coefficient]; exact one_ne_zero)
        conv_lhs => rw [MvPolynomial.as_sum f]
        rw [← Finset.add_sum_erase f.support _ hmem, hf.coefficient]
      have heq : Ideal.Quotient.mk I (MvPolynomial.monomial (ofLex b) 1) =
          -Ideal.Quotient.mk I (∑ c ∈ f.support.erase (ofLex b),
            MvPolynomial.monomial c (f.coeff c)) := by
        have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hfI
        rw [hfrepr, map_add] at hz
        exact eq_neg_of_add_eq_zero_left hz
      rw [heq]
      exact V.neg_mem hsum
  apply top_unique
  intro q hq
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [MvPolynomial.as_sum f, map_sum]
  apply V.sum_mem
  intro a ha
  have heq : MvPolynomial.monomial a (f.coeff a) = f.coeff a • MvPolynomial.monomial a (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [heq]
  change (Ideal.Quotient.mkₐ R I) (f.coeff a • MvPolynomial.monomial a (1 : R)) ∈ V
  rw [map_smul]
  exact V.smul_mem _ (hmono a)

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource35
/- Source: HigherSpecht/YuIdealLift.lean -/



/-!
# Lifting arbitrary ideal elements in the integral recursion

Each elementary generator has the explicitly verified lift from
`GroebnerLifts`.  Ideal induction extends it to every element, with its
congruence modulo the next power of the first variable kept in the theorem.
Taking the required homogeneous component then preserves both membership
and the specified minimum lexicographic term.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

theorem elementaryOn_isHomogeneous (Y : Finset (Fin n)) (d : ℕ) :
    (elementaryOn (R := R) Y d).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro A hA
  have hcard := (Finset.mem_powersetCard.mp hA).2
  have h := MvPolynomial.IsHomogeneous.prod A (fun i => (MvPolynomial.X i : PolynomialRing n R))
    (fun _ => 1) (fun i hi => MvPolynomial.isHomogeneous_X R i)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id, hcard] using h

attribute [local instance] MvPolynomial.gradedAlgebra

theorem extendedElementaryIdeal_isHomogeneous (μ : YoungDiagram) :
    (extendedElementaryIdeal R n μ).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R) := by
  apply Ideal.homogeneous_span
  rintro p ⟨Y, d, hd, hth, rfl⟩
  exact ⟨d, elementaryOn_isHomogeneous Y d⟩

def yuChildShape (μ : YoungDiagram) (c : Option (ℕ × ℕ)) : YoungDiagram :=
  match c with | none => μ | some cell => μ.erase cell

def yuLeadingPower (μ : YoungDiagram) (c : Option (ℕ × ℕ)) : ℕ :=
  match c with | none => μ.colLen 0 | some cell => μ.colLen (cell.2 + 1)

theorem rename_elementaryOn_embedding {m : ℕ} (e : Fin n ↪ Fin m)
    (Y : Finset (Fin n)) (d : ℕ) :
    MvPolynomial.rename e (elementaryOn (R := R) Y d) = elementaryOn (Y.map e) d := by
  classical
  simp only [elementaryOn, map_sum, map_prod, MvPolynomial.rename_X,
    Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.prod_map]

theorem yu_generator_lift_congruence (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (Y : Finset (Fin n)) (d : ℕ) :
    ∃ Q : PolynomialRing (n + 1) R,
      yuGeneratorLift μ c (Y.map (Fin.succEmb n)) 0 d =
        MvPolynomial.X 0 ^ yuLeadingPower μ c * MvPolynomial.rename Fin.succ (elementaryOn Y d) +
        MvPolynomial.X 0 ^ (yuLeadingPower μ c + 1) * Q := by
  have hzero : (0 : Fin (n + 1)) ∉ Y.map (Fin.succEmb n) := by simp
  have hrename : MvPolynomial.rename Fin.succ (elementaryOn (R := R) Y d) =
      elementaryOn (Y.map (Fin.succEmb n)) d :=
    rename_elementaryOn_embedding (Fin.succEmb n) Y d
  rw [hrename]
  cases c with
  | none => exact ⟨0, by simp [yuGeneratorLift, yuLeadingPower]⟩
  | some cell =>
    by_cases hcut : n - (Y.map (Fin.succEmb n)).card ≤ cell.2
    · cases d with
      | zero => exact ⟨0, by simp [yuGeneratorLift, yuLeadingPower, hcut]⟩
      | succ d =>
        refine ⟨elementaryOn (Y.map (Fin.succEmb n)) d, ?_⟩
        simp only [yuGeneratorLift, yuLeadingPower, if_pos hcut]
        rw [elementaryOn_insert_succ _ hzero, pow_succ]
        ring
    · exact ⟨0, by
        simp only [yuGeneratorLift, yuLeadingPower, if_neg hcut, mul_zero, add_zero]⟩

theorem yu_ideal_element_lift (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (hc : ∀ cell, c = some cell → YoungDiagram.IsCorner μ cell)
    {f : PolynomialRing n R} (hf : f ∈ extendedElementaryIdeal R n (yuChildShape μ c)) :
    ∃ F Q : PolynomialRing (n + 1) R,
      F ∈ extendedElementaryIdeal R (n + 1) μ ∧
      F = MvPolynomial.X 0 ^ yuLeadingPower μ c * MvPolynomial.rename Fin.succ f +
        MvPolynomial.X 0 ^ (yuLeadingPower μ c + 1) * Q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Y, d, hd, hth, rfl⟩ := hf
    obtain ⟨Q, hQ⟩ := yu_generator_lift_congruence (R := R) μ c Y d
    refine ⟨yuGeneratorLift μ c (Y.map (Fin.succEmb n)) 0 d, Q, ?_, hQ⟩
    apply yu_generator_lift_mem μ c hc _ (by simp) d
    cases c <;> simpa only [Finset.card_map, yuChildShape] using hth
  | zero => exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨F, Q, hFI, hF⟩ := ihf
    obtain ⟨G, S, hGI, hG⟩ := ihg
    refine ⟨F + G, Q + S, Ideal.add_mem _ hFI hGI, ?_⟩
    rw [hF, hG, map_add]
    ring
  | smul g f hf ihf =>
    simp only [smul_eq_mul]
    obtain ⟨F, Q, hFI, hF⟩ := ihf
    refine ⟨MvPolynomial.rename Fin.succ g * F, MvPolynomial.rename Fin.succ g * Q,
      Ideal.mul_mem_left _ _ hFI, ?_⟩
    rw [hF, map_mul]
    ring

theorem yu_ideal_element_lift_higher (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (hc : ∀ cell, c = some cell → YoungDiagram.IsCorner μ cell)
    {f : PolynomialRing n R} (hf : f ∈ extendedElementaryIdeal R n (yuChildShape μ c))
    (a : ℕ) (ha : yuLeadingPower μ c ≤ a) :
    ∃ F Q : PolynomialRing (n + 1) R,
      F ∈ extendedElementaryIdeal R (n + 1) μ ∧
      F = MvPolynomial.X 0 ^ a * MvPolynomial.rename Fin.succ f +
        MvPolynomial.X 0 ^ (a + 1) * Q := by
  obtain ⟨F, Q, hFI, hF⟩ := yu_ideal_element_lift μ c hc hf
  refine ⟨MvPolynomial.X 0 ^ (a - yuLeadingPower μ c) * F, Q,
    Ideal.mul_mem_left _ _ hFI, ?_⟩
  rw [hF, mul_add, ← mul_assoc, ← pow_add, Nat.sub_add_cancel ha]
  rw [← mul_assoc, ← pow_add]
  rw [show a - yuLeadingPower μ c + (yuLeadingPower μ c + 1) = a + 1 by omega]

theorem yu_minimumLex_reduction_lift (μ : YoungDiagram) (c : Option (ℕ × ℕ))
    (hc : ∀ cell, c = some cell → YoungDiagram.IsCorner μ cell)
    {f : PolynomialRing n R} (hf : f ∈ extendedElementaryIdeal R n (yuChildShape μ c))
    {b : Fin n →₀ ℕ} (hmin : MinimumLexMonic f b)
    (a : ℕ) (ha : yuLeadingPower μ c ≤ a) :
    ∃ F ∈ extendedElementaryIdeal R (n + 1) μ, MinimumLexMonic F (b.cons a) := by
  obtain ⟨F, Q, hFI, hF⟩ := yu_ideal_element_lift_higher μ c hc hf a ha
  refine ⟨MvPolynomial.homogeneousComponent (b.cons a).degree F, ?_,
    minimumLexMonic_homogeneous_lift a hmin F Q hF⟩
  exact MvPolynomial.homogeneousComponent_mem_of_mem
    (extendedElementaryIdeal_isHomogeneous μ) hFI _

/-- Every exponent outside the actual shuffle set has a monic homogeneous
reduction with that exponent as its least lexicographic term.  This is the
coverage step of the integral Gröbner argument, proved by induction on the
number of variables and actual corner/outside prefix operations. -/
theorem exists_minimumLex_reduction_of_not_shuffle
    (n : ℕ) (μ : YoungDiagram) (a : Fin n →₀ ℕ) (ha : ¬ ShuffleBound n μ a) :
    ∃ f ∈ extendedElementaryIdeal R n μ, MinimumLexMonic f a := by
  induction n generalizing μ with
  | zero =>
    have hcard : 0 < μ.card := by
      by_contra h
      have hzero : μ.cells = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
      letI : IsEmpty ↥μ.cells := Finset.isEmpty_coe_sort.mpr hzero
      let U : ↥μ.cells ↪ Fin 0 := ⟨isEmptyElim, fun x => isEmptyElim x⟩
      apply ha
      refine ⟨U, ?_, fun c => isEmptyElim c⟩
      intro j r t hrt
      exact isEmptyElim (⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩ : ↥μ.cells)
    refine ⟨MvPolynomial.monomial a 1, ?_, minimumLexMonic_monomial a⟩
    rw [extendedElementaryIdeal_eq_top_of_card_gt μ hcard]
    simp
  | succ n ih =>
    by_cases hfirst : a 0 < μ.colLen 0
    · obtain ⟨c, hc, hrow, hnext⟩ := exists_corner_at_cut μ hfirst
      have htail : ¬ ShuffleBound n (μ.erase c) (tailExponent a) :=
        fun ht => ha (shuffleBound_cons_corner hc a hrow ht)
      obtain ⟨f, hf, hmin⟩ := ih (μ.erase c) (tailExponent a) htail
      have hf' : f ∈ extendedElementaryIdeal R n (yuChildShape μ (some c)) := hf
      obtain ⟨F, hFI, hF⟩ := yu_minimumLex_reduction_lift μ (some c)
        (by intro cell he; cases Option.some.inj he; exact hc) hf' hmin (a 0) hnext
      refine ⟨F, hFI, ?_⟩
      have heq : (tailExponent a).cons (a 0) = a := Finsupp.cons_tail a
      rwa [heq] at hF
    · have htail : ¬ ShuffleBound n μ (tailExponent a) :=
        fun ht => ha (shuffleBound_cons_outside a ht)
      obtain ⟨f, hf, hmin⟩ := ih μ (tailExponent a) htail
      obtain ⟨F, hFI, hF⟩ := yu_minimumLex_reduction_lift μ none
        (by simp) hf hmin (a 0) (le_of_not_gt hfirst)
      refine ⟨F, hFI, ?_⟩
      have heq : (tailExponent a).cons (a 0) = a := Finsupp.cons_tail a
      rwa [heq] at hF

end HigherSpecht
end
end CanonicalSource35

section CanonicalSource36
/- Source: HigherSpecht/PolynomialDegrees.lean -/



/-!
# Exact homogeneous degrees of the prescribed polynomial families

The cocharge polynomial has degree `cc(S)` and the elementary multiplier
has degree the number of boxes of its actual indexing partition.  Thus all
later degreewise arguments use the manuscript's grading, with no formal
degree attached independently of the polynomial representatives.
-/

noncomputable section

open Finset TauCeti MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem degree_transportedCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (T : YoungTableau μ) : (transportedCocharge S T).degree = cochargeDegree S := by
  rw [Finsupp.degree_eq_sum]
  let e : Equiv.Perm (Fin μ.card) := T.symm.trans S.toTableau
  simpa only [transportedCocharge, Finsupp.equivFunOnFinite_symm_apply_apply,
    cochargeFilling, cochargeDegree, e, Equiv.trans_apply,
    StandardYoungTableau.toTableau_apply] using Equiv.sum_comp e (cochargeLabel S)

theorem rowSymmetrize_isHomogeneous {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    {f : PolynomialRing n R} (hf : f.IsHomogeneous d) :
    (rowSymmetrize G f).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  exact hf.rename_isHomogeneous

theorem columnAlternate_isHomogeneous {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    {f : PolynomialRing n R} (hf : f.IsHomogeneous d) :
    (columnAlternate G f).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  exact (MvPolynomial.homogeneousSubmodule (Fin n) R d).smul_mem _ hf.rename_isHomogeneous

theorem youngApply_isHomogeneous {μ : YoungDiagram} (T : YoungTableau μ)
    {f : PolynomialRing μ.card R} {d : ℕ} (hf : f.IsHomogeneous d) :
    (youngApply T f).IsHomogeneous d :=
  columnAlternate_isHomogeneous _ (rowSymmetrize_isHomogeneous _ hf)

theorem higherSpechtPolynomial_isHomogeneous {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) :
    (higherSpechtPolynomial (R := R) S T).IsHomogeneous (cochargeDegree S) := by
  apply youngApply_isHomogeneous
  exact MvPolynomial.isHomogeneous_monomial 1 (degree_transportedCocharge S T.toTableau)

theorem pairPolynomial_isHomogeneous {n : ℕ} (P : StandardPair n) :
    (pairPolynomial (R := R) P).IsHomogeneous (cochargeDegree P.left) :=
  (higherSpechtPolynomial_isHomogeneous P.left P.right).rename_isHomogeneous

theorem partition_weighted_differences (eta : YoungDiagram) (m : ℕ) :
    (∑ j ∈ Finset.range m, (j + 1) * (eta.rowLen j - eta.rowLen (j + 1))) +
      m * eta.rowLen m = ∑ j ∈ Finset.range m, eta.rowLen j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hle := eta.rowLen_anti m (m + 1) (Nat.le_succ m)
    have hsub := Nat.sub_add_cancel hle
    nlinarith

theorem partition_weighted_differences_eq_card (eta : YoungDiagram) {m : ℕ}
    (heta : eta.colLen 0 ≤ m) :
    (∑ j ∈ Finset.range m, (j + 1) * (eta.rowLen j - eta.rowLen (j + 1))) = eta.card := by
  have h := partition_weighted_differences eta m
  rw [YoungDiagram.rowLen_eq_zero_of_colLen_le heta, mul_zero, add_zero] at h
  exact h.trans (YoungDiagram.card_eq_sum_range_rowLen eta heta).symm

theorem elementaryMultiplier_isHomogeneous (n m : ℕ) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ m) :
    (elementaryMultiplier (R := R) n m eta.rowLen).IsHomogeneous eta.card := by
  rw [← partition_weighted_differences_eq_card eta heta]
  apply MvPolynomial.IsHomogeneous.prod
  intro j hj
  exact (elementaryOn_isHomogeneous (Finset.univ : Finset (Fin n)) (j + 1)).pow _

theorem griffinPolynomial_isHomogeneous {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) :
    (griffinPolynomial (R := R) i).IsHomogeneous (cochargeDegree i.pair.left + i.multiplier.card) :=
  (pairPolynomial_isHomogeneous i.pair).mul
    (elementaryMultiplier_isHomogeneous n (n - lam.card) i.multiplier i.multiplier_length)

end HigherSpecht
end
end CanonicalSource36

section CanonicalSource37
/- Source: HigherSpecht/StandardMonomialBasis.lean -/



/-!
# The full integral staircase-monomial basis

The proof combines two separately established facts: monomial independence
from genuine divided-power column witnesses, and spanning from the integral
minimum-lexicographic reductions.  All shapes, all ambient dimensions, and
all positive exponent bounds in the manuscript's range are retained.  This
is the supporting standard-monomial theorem, not the higher Specht basis
theorem: the latter still requires its exact tableau-index correspondence.
-/

noncomputable section

open Finset MvPolynomial TauCeti Module

namespace HigherSpecht

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} {μ : YoungDiagram}

theorem untruncated_staircase_monomials_span (hn : μ.card ≤ n) :
    Submodule.span R (Set.range fun a : UntruncatedStaircaseExponents n μ =>
      Ideal.Quotient.mk (untruncatedIdeal R n μ) (MvPolynomial.monomial a.val 1)) = ⊤ := by
  apply monomials_span_of_minimumLex_reductions
  intro a ha
  have hshuffle : ¬ ShuffleBound n μ a := fun h => ha
    ((mem_untruncatedStaircaseExponents_iff a).mpr h)
  obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle (R := R) n μ a hshuffle
  exact ⟨f, by rwa [extendedElementaryIdeal_eq_untruncated μ hn] at hf, hmin⟩

def untruncatedStandardMonomialBasis (hn : μ.card ≤ n) :
    Basis (UntruncatedStaircaseExponents n μ) R (UntruncatedRing R n μ) :=
  Basis.mk untruncated_staircase_monomials_linearIndependent
    (le_of_eq (untruncated_staircase_monomials_span (R := R) hn).symm)

@[simp] theorem untruncatedStandardMonomialBasis_apply (hn : μ.card ≤ n)
    (a : UntruncatedStaircaseExponents n μ) :
    untruncatedStandardMonomialBasis (R := R) hn a =
      Ideal.Quotient.mk (untruncatedIdeal R n μ) (MvPolynomial.monomial a.val 1) :=
  Basis.mk_apply _ _ _

theorem monomial_mem_griffin_of_large_coordinate (s : ℕ) (a : Fin n →₀ ℕ)
    (i : Fin n) (hi : s ≤ a i) :
    MvPolynomial.monomial a (1 : R) ∈ griffinIdeal R n μ s := by
  have hpow : (MvPolynomial.X i : PolynomialRing n R) ^ s ∈ griffinIdeal R n μ s :=
    (show powerIdeal R n s ≤ griffinIdeal R n μ s from le_sup_right)
      (Ideal.subset_span ⟨i, rfl⟩)
  have hs : Finsupp.single i s ≤ a := Finsupp.single_le_iff.mpr hi
  have heq : (MvPolynomial.X i : PolynomialRing n R) ^ s *
      MvPolynomial.monomial (a - Finsupp.single i s) 1 = MvPolynomial.monomial a 1 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      add_tsub_cancel_of_le hs, mul_one]
  rw [← heq]
  exact Ideal.mul_mem_right _ _ hpow

theorem griffin_staircase_monomials_span (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    Submodule.span R (Set.range fun a : GriffinStaircaseExponents n μ s =>
      Ideal.Quotient.mk (griffinIdeal R n μ s) (MvPolynomial.monomial a.val 1)) = ⊤ := by
  apply monomials_span_of_minimumLex_reductions
  intro a ha
  by_cases hb : ∀ i, a i < s
  · have hshuffle : ¬ ShuffleBound n μ a := fun h => ha
      ((mem_griffinStaircaseExponents_iff a hs hheight).mpr ⟨h, hb⟩)
    obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle (R := R) n μ a hshuffle
    rw [extendedElementaryIdeal_eq_untruncated μ hn] at hf
    exact ⟨f, (show untruncatedIdeal R n μ ≤ griffinIdeal R n μ s from le_sup_left) hf, hmin⟩
  · push_neg at hb
    obtain ⟨i, hi⟩ := hb
    exact ⟨MvPolynomial.monomial a 1, monomial_mem_griffin_of_large_coordinate s a i hi,
      minimumLexMonic_monomial a⟩

def griffinStandardMonomialBasis (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    Basis (GriffinStaircaseExponents n μ s) R (GriffinRing R n μ s) :=
  Basis.mk (griffin_staircase_monomials_linearIndependent s hs hheight)
    (le_of_eq (griffin_staircase_monomials_span (R := R) hn s hs hheight).symm)

@[simp] theorem griffinStandardMonomialBasis_apply (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) (a : GriffinStaircaseExponents n μ s) :
    griffinStandardMonomialBasis (R := R) hn s hs hheight a =
      Ideal.Quotient.mk (griffinIdeal R n μ s) (MvPolynomial.monomial a.val 1) :=
  Basis.mk_apply _ _ _

/-- Lemma 6.4, as an explicit free abelian basis of the untruncated quotient. -/
theorem lemma_6_4_untruncated_integral (hn : μ.card ≤ n) :
    ∃ B : Basis (UntruncatedStaircaseExponents n μ) ℤ (UntruncatedRing ℤ n μ),
      ∀ a, B a = Ideal.Quotient.mk (untruncatedIdeal ℤ n μ) (MvPolynomial.monomial a.val 1) :=
  ⟨untruncatedStandardMonomialBasis hn, untruncatedStandardMonomialBasis_apply hn⟩

/-- Lemma 6.4, with the complete finite exponent bound and no characteristic
restriction; the polynomial representatives themselves are specified. -/
theorem lemma_6_4_griffin_integral (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    ∃ B : Basis (GriffinStaircaseExponents n μ s) ℤ (GriffinRing ℤ n μ s),
      ∀ a, B a = Ideal.Quotient.mk (griffinIdeal ℤ n μ s) (MvPolynomial.monomial a.val 1) :=
  ⟨griffinStandardMonomialBasis hn s hs hheight, griffinStandardMonomialBasis_apply hn s hs hheight⟩

theorem finite_griffinStaircaseExponents (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) : (GriffinStaircaseExponents n μ s).Finite := by
  apply (Finsupp.finite_of_degree_le (σ := Fin n) (n * (s - 1))).subset
  intro a ha
  have hb := ((mem_griffinStaircaseExponents_iff a hs hheight).mp ha).2
  change a.degree ≤ n * (s - 1)
  rw [Finsupp.degree_eq_sum]
  calc
    (∑ i : Fin n, a i) ≤ ∑ i : Fin n, (s - 1) :=
      Finset.sum_le_sum fun i hi => Nat.le_sub_one_of_lt (hb i)
    _ = n * (s - 1) := by simp

theorem finrank_griffin_eq_staircase_card (K : Type*) [Field K]
    (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : μ.colLen 0 ≤ s) :
    Module.finrank K (GriffinRing K n μ s) = Nat.card (GriffinStaircaseExponents n μ s) := by
  letI : Fintype (GriffinStaircaseExponents n μ s) :=
    (finite_griffinStaircaseExponents (n := n) s hs hheight).fintype
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (griffinStandardMonomialBasis hn s hs hheight)

theorem finrank_griffin_independent_of_field (K L : Type*) [Field K] [Field L]
    (hn : μ.card ≤ n) (s : ℕ) (hs : 0 < s) (hheight : μ.colLen 0 ≤ s) :
    Module.finrank K (GriffinRing K n μ s) = Module.finrank L (GriffinRing L n μ s) := by
  rw [finrank_griffin_eq_staircase_card K hn s hs hheight,
    finrank_griffin_eq_staircase_card L hn s hs hheight]

end HigherSpecht
end
end CanonicalSource37

section CanonicalSource38
/- Source: HigherSpecht/EligibleIndexCount.lean -/



/-!
# Exact finite index sets for the outstanding Griffin count

The cardinalities below are cardinalities of genuine finite sets. In particular,
`Nat.card` is not used on an unproved finite index type. The RSK equivalence is
transported with all eligibility and rectangle conditions intact; it does not
assert that those conditions are equivalent to the staircase condition.

`GriffinDegreeCount` records the remaining Chou--Hanada counting statement.
The definitions and finite equivalences in this file do not prove that statement.
-/

noncomputable section
open Finset TauCeti
open scoped Classical

namespace HigherSpecht

abbrev RectanglePartition (m w : ℕ) :=
  {eta : YoungDiagram // eta.colLen 0 ≤ m ∧ eta.rowLen 0 ≤ w}

def rectanglePartitionCode {m w : ℕ} (eta : RectanglePartition m w) :
    Finset (Fin m × Fin w) :=
  Finset.univ.filter fun c => (c.1.val, c.2.val) ∈ eta.val

theorem rectanglePartitionCode_injective (m w : ℕ) :
    Function.Injective (rectanglePartitionCode (m := m) (w := w)) := by
  intro eta theta hcode
  apply Subtype.ext
  ext c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells]
  have hbound (z : RectanglePartition m w) (hz : c ∈ z.val) : c.1 < m ∧ c.2 < w := by
    refine ⟨?_, ?_⟩
    · exact (YoungDiagram.mem_iff_lt_colLen.mp hz).trans_le
        ((z.val.colLen_anti 0 c.2 (Nat.zero_le _)).trans z.property.1)
    · exact (YoungDiagram.mem_iff_lt_rowLen.mp hz).trans_le
        ((z.val.rowLen_anti 0 c.1 (Nat.zero_le _)).trans z.property.2)
  by_cases hc : c.1 < m ∧ c.2 < w
  · have h : (⟨c.1, hc.1⟩, ⟨c.2, hc.2⟩) ∈ rectanglePartitionCode eta ↔
        (⟨c.1, hc.1⟩, ⟨c.2, hc.2⟩) ∈ rectanglePartitionCode theta := by rw [hcode]
    simpa only [rectanglePartitionCode, Finset.mem_filter, Finset.mem_univ, true_and] using h
  · exact iff_of_false (fun h => hc (hbound eta h)) (fun h => hc (hbound theta h))

instance finiteRectanglePartition (m w : ℕ) : Finite (RectanglePartition m w) :=
  Finite.of_injective rectanglePartitionCode (rectanglePartitionCode_injective m w)

noncomputable instance fintypeRectanglePartition (m w : ℕ) :
    Fintype (RectanglePartition m w) := Fintype.ofFinite _

def griffinIndexFiniteCode {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} {s : ℕ}
    (i : GriffinIndex n lam hk s) : StandardPair n × RectanglePartition (n - lam.card) s :=
  ⟨i.pair, i.multiplier, i.multiplier_length,
    i.multiplier_width.trans (Nat.sub_le _ _) |>.trans (Nat.sub_le _ _)⟩

theorem griffinIndexFiniteCode_injective (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    Function.Injective (griffinIndexFiniteCode (n := n) (lam := lam) (hk := hk) (s := s)) := by
  intro i j h
  have hp : i.pair = j.pair := congrArg Prod.fst h
  have he : i.multiplier = j.multiplier := congrArg (fun x => x.2.val) h
  cases i
  cases j
  cases hp
  cases he
  rfl

instance finiteGriffinIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) :
    Finite (GriffinIndex n lam hk s) :=
  Finite.of_injective griffinIndexFiniteCode (griffinIndexFiniteCode_injective n lam hk s)

noncomputable instance fintypeGriffinIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) : Fintype (GriffinIndex n lam hk s) := Fintype.ofFinite _

def griffinIndexDegree {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} {s : ℕ}
    (i : GriffinIndex n lam hk s) : ℕ := cochargeDegree i.pair.left + i.multiplier.card

abbrev GriffinDegreeFiber (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s d : ℕ) :=
  {i : GriffinIndex n lam hk s // griffinIndexDegree i = d}

abbrev StaircaseDegreeFiber (n : ℕ) (lam : YoungDiagram) (s d : ℕ) :=
  {a : Fin n →₀ ℕ // a ∈ GriffinStaircaseExponents n lam s ∧ a.degree = d}

instance finiteStaircaseDegreeFiber (n : ℕ) (lam : YoungDiagram) (s d : ℕ) :
    Finite (StaircaseDegreeFiber n lam s d) := by
  have hfinite : {a : Fin n →₀ ℕ | a ∈ GriffinStaircaseExponents n lam s ∧
      a.degree = d}.Finite :=
    (Finsupp.finite_of_degree_le (σ := Fin n) d).subset (fun a ha => ha.2.le)
  exact hfinite.to_subtype

/-- A proposition describing the exact degreewise count still to be proved.
All types on both sides have finite instances independently of this predicate. -/
def GriffinDegreeCount : Prop :=
  ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s d : ℕ),
    0 < lam.card → lam.colLen 0 ≤ s →
      Nat.card (GriffinDegreeFiber n lam hk s d) = Nat.card (StaircaseDegreeFiber n lam s d)

structure EligiblePermutationIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) where
  permutation : Equiv.Perm (Fin n)
  multiplier : YoungDiagram
  eligible : prefixEligible lam hk (rskPair n permutation)
  descents_lt : descentNumber (rskPair n permutation).left < s
  multiplier_length : multiplier.colLen 0 ≤ n - lam.card
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber (rskPair n permutation).left - 1

def griffinIndexRSKEquiv (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) :
    GriffinIndex n lam hk s ≃ EligiblePermutationIndex n lam hk s where
  toFun i :=
    { permutation := (rskPair n).symm i.pair
      multiplier := i.multiplier
      eligible := by simpa only [Equiv.apply_symm_apply] using i.eligible
      descents_lt := by
        exact (congrArg (fun P : StandardPair n => descentNumber P.left < s)
          ((rskPair n).apply_symm_apply i.pair)).mpr i.descents_lt
      multiplier_length := i.multiplier_length
      multiplier_width := by
        exact (congrArg (fun P : StandardPair n =>
          i.multiplier.rowLen 0 ≤ s - descentNumber P.left - 1)
          ((rskPair n).apply_symm_apply i.pair)).mpr i.multiplier_width }
  invFun i :=
    { pair := rskPair n i.permutation
      multiplier := i.multiplier
      eligible := i.eligible
      descents_lt := i.descents_lt
      multiplier_length := i.multiplier_length
      multiplier_width := i.multiplier_width }
  left_inv i := by
    cases i
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    cases i
    simp only [Equiv.symm_apply_apply]

def eligiblePermutationDegree {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n} {s : ℕ}
    (i : EligiblePermutationIndex n lam hk s) : ℕ :=
  cochargeDegree (rskPair n i.permutation).left + i.multiplier.card

@[simp] theorem griffinIndexRSKEquiv_degree (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (i : GriffinIndex n lam hk s) :
    eligiblePermutationDegree (griffinIndexRSKEquiv n lam hk s i) = griffinIndexDegree i := by
  change cochargeDegree (rskPair n ((rskPair n).symm i.pair)).left + i.multiplier.card =
    cochargeDegree i.pair.left + i.multiplier.card
  exact congrArg (fun P : StandardPair n => cochargeDegree P.left + i.multiplier.card)
    ((rskPair n).apply_symm_apply i.pair)

def griffinDegreeRSKEquiv (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s d : ℕ) :
    GriffinDegreeFiber n lam hk s d ≃
      {i : EligiblePermutationIndex n lam hk s // eligiblePermutationDegree i = d} :=
  (griffinIndexRSKEquiv n lam hk s).subtypeEquiv fun i => by
    rw [griffinIndexRSKEquiv_degree]

theorem card_griffinDegreeFiber_eq_permutation (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s d : ℕ) :
    Nat.card (GriffinDegreeFiber n lam hk s d) =
      Nat.card {i : EligiblePermutationIndex n lam hk s // eligiblePermutationDegree i = d} :=
  Nat.card_congr (griffinDegreeRSKEquiv n lam hk s d)

end HigherSpecht
end
end CanonicalSource38

section CanonicalSource39
/- Source: HigherSpecht/HarmonicGeneration.lean -/



/-!
# The exact divided-power inverse systems

The elementary reductions and the monic column witnesses determine the whole
inverse system, over every nontrivial commutative coefficient ring.  A leading
term of a harmonic polynomial must be a staircase: a minimum-lex relation at
any other exponent would pair nontrivially with it.  Subtracting the matching
monic contracted column witness then decreases the leading exponent.

This supplies the full inverse-system generation statement without a field
dimension argument or an assumed description of the annihilator.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped MonomialOrder

namespace HigherSpecht

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} {μ : YoungDiagram}

theorem coeff_zero_dividedAction (f w : PolynomialRing n R) :
    (dividedAction f w).coeff 0 = ∑ a ∈ f.support, f.coeff a * w.coeff a := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, LinearMap.sum_apply, MvPolynomial.coeff_sum,
    dividedAction_monomial, LinearMap.smul_apply, MvPolynomial.coeff_smul,
    coeff_contractMonomial, zero_add, smul_eq_mul]

theorem harmonic_leader_mem_of_minimumLex_reductions
    (I : Ideal (PolynomialRing n R)) (C : Set (Fin n →₀ ℕ))
    (hred : ∀ a ∉ C, ∃ f ∈ I, MinimumLexMonic f a)
    {w : PolynomialRing n R} (hw : w ∈ dividedHarmonics I) (hw0 : w ≠ 0) :
    MonomialOrder.lex.degree w ∈ C := by
  classical
  by_contra hC
  obtain ⟨f, hfI, hf⟩ := hred (MonomialOrder.lex.degree w) hC
  have hz := congrArg (fun p : PolynomialRing n R => p.coeff 0) (hw f hfI)
  rw [coeff_zero_dividedAction, MvPolynomial.coeff_zero] at hz
  have hsingle : (∑ a ∈ f.support, f.coeff a * w.coeff a) =
      w.coeff (MonomialOrder.lex.degree w) := by
    rw [Finset.sum_eq_single (MonomialOrder.lex.degree w)]
    · rw [hf.coefficient, one_mul]
    · intro a ha hne
      have hlt := hf.minimum a (MvPolynomial.mem_support_iff.mp ha) hne
      rw [MonomialOrder.lex.coeff_eq_zero_of_lt (f := w) hlt, mul_zero]
    · intro hn
      exact (hn (MvPolynomial.mem_support_iff.mpr
        (by rw [hf.coefficient]; exact one_ne_zero))).elim
  rw [hsingle] at hz
  exact (MonomialOrder.lex.coeff_degree_ne_zero_iff.mpr hw0) hz

/-- Exact generation from genuine monic harmonic leaders and actual ideal
relations.  Neither an annihilator equality nor a dimension equality is a
hypothesis. -/
theorem dividedHarmonics_eq_of_minimumLex_reductions
    (I : Ideal (PolynomialRing n R)) (C : Set (Fin n →₀ ℕ))
    (hred : ∀ a ∉ C, ∃ f ∈ I, MinimumLexMonic f a)
    (V : Submodule R (PolynomialRing n R)) (hV : V ≤ dividedHarmonics I)
    (hleaders : ∀ a ∈ C, ∃ w ∈ V,
      MonomialOrder.lex.degree w = a ∧ MonomialOrder.lex.Monic w) :
    dividedHarmonics I = V := by
  apply le_antisymm
  · intro w hw
    induction hd : toLex (MonomialOrder.lex.degree w) using WellFoundedLT.induction
      generalizing w with
    | ind d ih =>
      subst hd
      by_cases hw0 : w = 0
      · simpa only [hw0] using V.zero_mem
      have hc := harmonic_leader_mem_of_minimumLex_reductions I C hred hw hw0
      obtain ⟨u, huV, huDegree, huMonic⟩ := hleaders _ hc
      let g := w - MonomialOrder.lex.leadingCoeff w • u
      have hgH : g ∈ dividedHarmonics I :=
        (dividedHarmonics I).sub_mem hw ((dividedHarmonics I).smul_mem _ (hV huV))
      have hcoeff : g.coeff (MonomialOrder.lex.degree w) = 0 := by
        dsimp only [g]
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, ← huDegree]
        change w.coeff (MonomialOrder.lex.degree u) -
          MonomialOrder.lex.leadingCoeff w * MonomialOrder.lex.leadingCoeff u = 0
        rw [huMonic.leadingCoeff_eq_one, mul_one, huDegree]
        exact sub_self _
      have hgV : g ∈ V := by
        by_cases hg0 : g = 0
        · simpa only [hg0] using V.zero_mem
        have hle : toLex (MonomialOrder.lex.degree g) ≤ toLex (MonomialOrder.lex.degree w) := by
          apply MonomialOrder.lex.degree_sub_le.trans
          apply max_le le_rfl
          exact MonomialOrder.lex.degree_smul_le.trans (le_of_eq (congrArg toLex huDegree))
        have hne : toLex (MonomialOrder.lex.degree g) ≠ toLex (MonomialOrder.lex.degree w) := by
          intro he
          have he' : MonomialOrder.lex.degree g = MonomialOrder.lex.degree w := congrArg ofLex he
          have hnonzero := MonomialOrder.lex.coeff_degree_ne_zero_iff.mpr hg0
          rw [he'] at hnonzero
          exact hnonzero hcoeff
        exact ih _ (lt_of_le_of_ne hle hne) hgH rfl
      have h := V.add_mem hgV (V.smul_mem (MonomialOrder.lex.leadingCoeff w) huV)
      simpa only [g, sub_add_cancel] using h
  · exact hV

def columnContractionSpan (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Submodule R (PolynomialRing n R) :=
  Submodule.span R {w | ∃ (U : ↥μ.cells ↪ Fin n) (d : Fin n →₀ ℕ),
    w = contractMonomial d (columnWitness U s)}

theorem columnContractionSpan_le_griffinHarmonics (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    columnContractionSpan R n μ s ≤ dividedHarmonics (griffinIdeal R n μ s) := by
  apply Submodule.span_le.mpr
  rintro w ⟨U, d, rfl⟩
  exact contractMonomial_mem_dividedHarmonics (columnWitness_mem_griffinHarmonics U hs hheight) d

theorem griffinHarmonics_eq_columnContractionSpan (hn : μ.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : μ.colLen 0 ≤ s) :
    dividedHarmonics (griffinIdeal R n μ s) = columnContractionSpan R n μ s := by
  apply dividedHarmonics_eq_of_minimumLex_reductions (griffinIdeal R n μ s)
    (GriffinStaircaseExponents n μ s)
  · intro a ha
    by_cases hb : ∀ i, a i < s
    · have hshuffle : ¬ ShuffleBound n μ a := fun h => ha
        ((mem_griffinStaircaseExponents_iff a hs hheight).mpr ⟨h, hb⟩)
      obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle (R := R) n μ a hshuffle
      rw [extendedElementaryIdeal_eq_untruncated μ hn] at hf
      exact ⟨f, Ideal.mem_sup_left hf, hmin⟩
    · push_neg at hb
      obtain ⟨i, hi⟩ := hb
      exact ⟨MvPolynomial.monomial a 1, monomial_mem_griffin_of_large_coordinate s a i hi,
        minimumLexMonic_monomial a⟩
  · exact columnContractionSpan_le_griffinHarmonics s hs hheight
  · rintro a ⟨U, hU, ha⟩
    let w := columnWitness (R := R) U s
    have hw : MonomialOrder.lex.Monic w := columnWitness_monic U hU s
    have hdeg : MonomialOrder.lex.degree w = staircaseVector U s := columnWitness_degree U hU s
    have ha' : a ≤ MonomialOrder.lex.degree w := by rwa [hdeg]
    have hsub : MonomialOrder.lex.degree w - a ≤ MonomialOrder.lex.degree w := tsub_le_self
    refine ⟨contractMonomial (MonomialOrder.lex.degree w - a) w,
      Submodule.subset_span ⟨U, _, rfl⟩, ?_,
      monic_contractMonomial MonomialOrder.lex hw _ hsub⟩
    rw [degree_contractMonomial MonomialOrder.lex hw.ne_zero _ hsub,
      tsub_tsub_cancel_of_le ha']

def untruncatedColumnContractionSpan (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Submodule R (PolynomialRing n R) :=
  Submodule.span R {w | ∃ (s : ℕ) (U : ↥μ.cells ↪ Fin n) (d : Fin n →₀ ℕ),
    w = contractMonomial d (columnWitness U s)}

theorem untruncatedHarmonics_eq_columnContractionSpan (hn : μ.card ≤ n) :
    dividedHarmonics (untruncatedIdeal R n μ) = untruncatedColumnContractionSpan R n μ := by
  apply dividedHarmonics_eq_of_minimumLex_reductions (untruncatedIdeal R n μ)
    (UntruncatedStaircaseExponents n μ)
  · intro a ha
    have hshuffle : ¬ ShuffleBound n μ a := fun h => ha
      ((mem_untruncatedStaircaseExponents_iff a).mpr h)
    obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle (R := R) n μ a hshuffle
    exact ⟨f, by rwa [extendedElementaryIdeal_eq_untruncated μ hn] at hf, hmin⟩
  · apply Submodule.span_le.mpr
    rintro w ⟨s, U, d, rfl⟩
    exact contractMonomial_mem_dividedHarmonics (columnWitness_mem_untruncatedHarmonics U s) d
  · rintro a ⟨s, U, hU, ha⟩
    let w := columnWitness (R := R) U s
    have hw : MonomialOrder.lex.Monic w := columnWitness_monic U hU s
    have hdeg : MonomialOrder.lex.degree w = staircaseVector U s := columnWitness_degree U hU s
    have ha' : a ≤ MonomialOrder.lex.degree w := by rwa [hdeg]
    have hsub : MonomialOrder.lex.degree w - a ≤ MonomialOrder.lex.degree w := tsub_le_self
    refine ⟨contractMonomial (MonomialOrder.lex.degree w - a) w,
      Submodule.subset_span ⟨s, U, _, rfl⟩, ?_,
      monic_contractMonomial MonomialOrder.lex hw _ hsub⟩
    rw [degree_contractMonomial MonomialOrder.lex hw.ne_zero _ hsub,
      tsub_tsub_cancel_of_le ha']

end HigherSpecht
end
end CanonicalSource39

section CanonicalSource40
/- Source: HigherSpecht/DominanceIdeals.lean -/



/-!
# Dominance and the exact elementary ideals

Row-prefix dominance implies the required reverse inequality for conjugate
tails.  The proof also allows different cardinalities, as needed by the
simultaneous untruncated construction.  Each elementary generator is then
transported with its original numerical threshold.
-/

noncomputable section

open Finset TauCeti MvPolynomial

namespace HigherSpecht

private theorem sum_excess_add_mul_takeWhile {l : List ℕ} (hl : l.SortedGE) (k : ℕ) :
    (l.map fun x => x - k).sum + k * (l.takeWhile fun x => decide (k < x)).length =
      (l.takeWhile fun x => decide (k < x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hlsorted : l.SortedGE := hl.pairwise.tail.sortedGE
    by_cases ha : k < a
    · rw [List.takeWhile_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have htail := ih hlsorted
      rw [Nat.mul_succ]
      omega
    · have hale : a ≤ k := Nat.le_of_not_gt ha
      have htail : ∀ x ∈ l, x ≤ k := by
        intro x hx
        exact (hl.pairwise.rel_head_tail (by simpa using hx)).trans hale
      have hsum : (l.map fun x => x - k).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact Nat.sub_eq_zero_of_le (htail x hx)
      rw [List.takeWhile_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.sum_cons, List.sum_nil, List.length_nil,
        mul_zero, add_zero, Nat.sub_eq_zero_of_le hale]
      simpa only [zero_add] using hsum

private theorem sum_take_le_mul_add_excess (l : List ℕ) (k r : ℕ) :
    (l.take r).sum ≤ k * r + (l.map fun x => x - k).sum := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
    cases l with
    | nil => simp
    | cons a l =>
      simp only [List.take_succ_cons, List.sum_cons, List.map_cons, Nat.mul_succ]
      have htail := ih l
      omega

private theorem sum_excess_le_of_prefix_le {l u : List ℕ} (hl : l.SortedGE)
    (hprefix : ∀ r, (l.take r).sum ≤ (u.take r).sum) (k : ℕ) :
    (l.map fun x => x - k).sum ≤ (u.map fun x => x - k).sum := by
  let r := (l.takeWhile fun x => decide (k < x)).length
  have htake : l.take r = l.takeWhile fun x => decide (k < x) := by
    dsimp only [r]
    calc
      l.take (l.takeWhile fun x => decide (k < x)).length =
          ((l.takeWhile fun x => decide (k < x)) ++
            l.dropWhile fun x => decide (k < x)).take
              (l.takeWhile fun x => decide (k < x)).length := by
        rw [List.takeWhile_append_dropWhile]
      _ = _ := List.take_left
  have he := sum_excess_add_mul_takeWhile hl k
  have hp := hprefix r
  have hu := sum_take_le_mul_add_excess u k r
  rw [htake] at hp
  dsimp only [r] at hp hu
  omega

theorem columnTail_eq_rowLens_excess (μ : YoungDiagram) (h : ℕ) :
    columnTail μ h = (μ.rowLens.map fun r => r - h).sum := by
  rw [columnTail, YoungDiagram.card_filter_cells μ (fun c => h ≤ c.2) le_rfl]
  have hcount (i : ℕ) : ((Finset.range (μ.rowLen i)).filter fun j => h ≤ j).card =
      μ.rowLen i - h := by
    have heq : (Finset.range (μ.rowLen i)).filter (fun j => h ≤ j) = Finset.Ico h (μ.rowLen i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      tauto
    rw [heq, Nat.card_Ico]
  simp_rw [hcount]
  simpa only [Multiset.map_coe, Multiset.sum_coe] using
    (YoungDiagram.sum_map_coe_rowLens μ (fun r => r - h)).symm

theorem columnTail_le_of_dominates {μ ν : YoungDiagram} (h : Dominates ν μ) (k : ℕ) :
    columnTail μ k ≤ columnTail ν k := by
  rw [columnTail_eq_rowLens_excess, columnTail_eq_rowLens_excess]
  apply sum_excess_le_of_prefix_le μ.rowLens_sorted
  intro r
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  exact h r

variable {R : Type*} [CommRing R] {n s : ℕ} {μ ν : YoungDiagram}

theorem untruncatedIdeal_le_of_dominates (hμ : μ.card ≤ n) (hν : ν.card ≤ n)
    (h : Dominates ν μ) : untruncatedIdeal R n μ ≤ untruncatedIdeal R n ν := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hcard, hthreshold, rfl⟩
  apply elementaryOn_mem_untruncatedIdeal Y hd hcard
  have ht := columnTail_le_of_dominates h (n - Y.card)
  rw [columnTail_eq_conjugateTail μ hμ, columnTail_eq_conjugateTail ν hν] at ht
  omega

theorem griffinIdeal_le_of_dominates (hμ : μ.card ≤ n) (hν : ν.card ≤ n)
    (h : Dominates ν μ) : griffinIdeal R n μ s ≤ griffinIdeal R n ν s :=
  sup_le_sup (untruncatedIdeal_le_of_dominates hμ hν h) le_rfl

theorem columnWitness_mem_dominated_untruncatedHarmonics
    (U : ↥ν.cells ↪ Fin n) (hμ : μ.card ≤ n) (h : Dominates ν μ) (s : ℕ) :
    columnWitness (R := R) U s ∈ dividedHarmonics (untruncatedIdeal R n μ) := by
  have hν : ν.card ≤ n := by
    simpa only [Fintype.card_coe, Fintype.card_fin, YoungDiagram.card] using
      Fintype.card_le_of_injective U U.injective
  exact dividedHarmonics_antitone (untruncatedIdeal_le_of_dominates hμ hν h)
    (columnWitness_mem_untruncatedHarmonics U s)

end HigherSpecht
end
end CanonicalSource40

section CanonicalSource41
/- Source: HigherSpecht/EligibleIndexCountRecursion.lean -/



/-!
# The exact greedy staircase recursion

The converse direction of the greedy prefix recursion is obtained from two
independent polynomial facts: every staircase exponent is a monic harmonic
leader, and every forbidden child exponent has an actual integral Yu lift.
A minimum-lex relation cannot pair trivially with its matching harmonic leader.
This proves the disjoint recurrence, not only the easy child-to-parent inclusion.
No dimension formula or eligible-index count is used in this argument.
-/

noncomputable section
open Finset MvPolynomial TauCeti
open scoped Classical MonomialOrder

namespace HigherSpecht

variable {n : ℕ} {μ ν : YoungDiagram}

theorem exists_monic_harmonic_leader_of_shuffle {a : Fin n →₀ ℕ}
    (ha : ShuffleBound n μ a) :
    ∃ w : PolynomialRing n ℚ,
      w ∈ dividedHarmonics (extendedElementaryIdeal ℚ n μ) ∧
      MonomialOrder.lex.degree w = a ∧ MonomialOrder.lex.Monic w := by
  obtain ⟨s, U, hU, hbound⟩ := (mem_untruncatedStaircaseExponents_iff a).mpr ha
  have hcard : μ.card ≤ n := by
    simpa only [Fintype.card_coe, Fintype.card_fin, _root_.YoungDiagram.card] using
      Fintype.card_le_of_injective U U.injective
  let W : PolynomialRing n ℚ := columnWitness U s
  have hW : MonomialOrder.lex.Monic W := columnWitness_monic U hU s
  have hdegree : MonomialOrder.lex.degree W = staircaseVector U s := columnWitness_degree U hU s
  have hale : a ≤ MonomialOrder.lex.degree W := by rwa [hdegree]
  have hsub : MonomialOrder.lex.degree W - a ≤ MonomialOrder.lex.degree W := tsub_le_self
  refine ⟨contractMonomial (MonomialOrder.lex.degree W - a) W, ?_, ?_,
    monic_contractMonomial MonomialOrder.lex hW _ hsub⟩
  · rw [extendedElementaryIdeal_eq_untruncated μ hcard]
    exact contractMonomial_mem_dividedHarmonics (columnWitness_mem_untruncatedHarmonics U s) _
  · rw [degree_contractMonomial MonomialOrder.lex hW.ne_zero _ hsub,
      tsub_tsub_cancel_of_le hale]

theorem no_minimumLex_reduction_of_shuffle {a : Fin n →₀ ℕ}
    (ha : ShuffleBound n μ a) {f : PolynomialRing n ℚ}
    (hf : f ∈ extendedElementaryIdeal ℚ n μ) : ¬ MinimumLexMonic f a := by
  intro hmin
  obtain ⟨w, hw, hdeg, hmonic⟩ := exists_monic_harmonic_leader_of_shuffle ha
  let C : Set (Fin n →₀ ℕ) := {b | b ≠ a}
  have hred : ∀ b ∉ C, ∃ g ∈ extendedElementaryIdeal ℚ n μ, MinimumLexMonic g b := by
    intro b hb
    have hba : b = a := by simpa only [C, Set.mem_setOf_eq, not_not] using hb
    subst b
    exact ⟨f, hf, hmin⟩
  have h := harmonic_leader_mem_of_minimumLex_reductions
    (extendedElementaryIdeal ℚ n μ) C hred hw hmonic.ne_zero
  exact h hdeg

theorem shuffleBound_iff_no_minimumLex_reduction (a : Fin n →₀ ℕ) :
    ShuffleBound n μ a ↔
      ¬ ∃ f : PolynomialRing n ℚ, f ∈ extendedElementaryIdeal ℚ n μ ∧ MinimumLexMonic f a := by
  constructor
  · intro ha
    rintro ⟨f, hf, hmin⟩
    exact no_minimumLex_reduction_of_shuffle ha hf hmin
  · intro h
    by_contra ha
    exact h (exists_minimumLex_reduction_of_not_shuffle n μ a ha)

theorem shuffleBound_tail_corner {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (a : Fin (n + 1) →₀ ℕ) (hnext : μ.colLen (c.2 + 1) ≤ a 0)
    (ha : ShuffleBound (n + 1) μ a) : ShuffleBound n (μ.erase c) (tailExponent a) := by
  by_contra htail
  obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle
    (R := ℚ) n (μ.erase c) (tailExponent a) htail
  obtain ⟨F, hF, hFmin⟩ := yu_minimumLex_reduction_lift μ (some c)
    (by intro cell he; cases Option.some.inj he; exact hc) hf hmin (a 0) hnext
  have heq : (tailExponent a).cons (a 0) = a := Finsupp.cons_tail a
  rw [heq] at hFmin
  exact no_minimumLex_reduction_of_shuffle ha hF hFmin

theorem shuffleBound_tail_outside (a : Fin (n + 1) →₀ ℕ)
    (hfirst : μ.colLen 0 ≤ a 0) (ha : ShuffleBound (n + 1) μ a) :
    ShuffleBound n μ (tailExponent a) := by
  by_contra htail
  obtain ⟨f, hf, hmin⟩ := exists_minimumLex_reduction_of_not_shuffle
    (R := ℚ) n μ (tailExponent a) htail
  obtain ⟨F, hF, hFmin⟩ := yu_minimumLex_reduction_lift μ none (by simp)
    hf hmin (a 0) hfirst
  have heq : (tailExponent a).cons (a 0) = a := Finsupp.cons_tail a
  rw [heq] at hFmin
  exact no_minimumLex_reduction_of_shuffle ha hF hFmin

theorem shuffleBound_corner_iff {c : ℕ × ℕ} (hc : YoungDiagram.IsCorner μ c)
    (a : Fin (n + 1) →₀ ℕ) (hrow : a 0 ≤ c.1) (hnext : μ.colLen (c.2 + 1) ≤ a 0) :
    ShuffleBound (n + 1) μ a ↔ ShuffleBound n (μ.erase c) (tailExponent a) :=
  ⟨shuffleBound_tail_corner hc a hnext, shuffleBound_cons_corner hc a hrow⟩

theorem shuffleBound_outside_iff (a : Fin (n + 1) →₀ ℕ) (hfirst : μ.colLen 0 ≤ a 0) :
    ShuffleBound (n + 1) μ a ↔ ShuffleBound n μ (tailExponent a) :=
  ⟨shuffleBound_tail_outside a hfirst, shuffleBound_cons_outside a⟩

def greedyCutCorner (μ : YoungDiagram) (j : ℕ) (hj : j < μ.colLen 0) : ℕ × ℕ :=
  Classical.choose (exists_corner_at_cut μ hj)

theorem greedyCutCorner_spec (μ : YoungDiagram) (j : ℕ) (hj : j < μ.colLen 0) :
    YoungDiagram.IsCorner μ (greedyCutCorner μ j hj) ∧
      j ≤ (greedyCutCorner μ j hj).1 ∧ μ.colLen ((greedyCutCorner μ j hj).2 + 1) ≤ j :=
  Classical.choose_spec (exists_corner_at_cut μ hj)

def staircaseChildShape (μ : YoungDiagram) (j : ℕ) : YoungDiagram :=
  if hj : j < μ.colLen 0 then μ.erase (greedyCutCorner μ j hj) else μ

theorem staircaseChildShape_le (μ : YoungDiagram) (j : ℕ) : staircaseChildShape μ j ≤ μ := by
  unfold staircaseChildShape
  split_ifs
  · exact YoungDiagram.erase_le _ _
  · exact le_rfl

theorem staircaseChildShape_height_le (μ : YoungDiagram) (j : ℕ) :
    (staircaseChildShape μ j).colLen 0 ≤ μ.colLen 0 :=
  YoungDiagram.colLen_le_of_le (staircaseChildShape_le μ j) 0

/-- Exact disjoint-prefix recurrence, including the case where the child
diagram has more cells than the number of remaining variables. -/
theorem shuffleBound_child_iff (a : Fin (n + 1) →₀ ℕ) :
    ShuffleBound (n + 1) μ a ↔ ShuffleBound n (staircaseChildShape μ (a 0)) (tailExponent a) := by
  unfold staircaseChildShape
  split_ifs with h
  · obtain ⟨hc, hrow, hnext⟩ := greedyCutCorner_spec μ (a 0) h
    exact shuffleBound_corner_iff hc a hrow hnext
  · exact shuffleBound_outside_iff a (Nat.le_of_not_gt h)

theorem griffinStaircase_child_iff (a : Fin (n + 1) →₀ ℕ) {s : ℕ}
    (hs : 0 < s) (hheight : μ.colLen 0 ≤ s) :
    a ∈ GriffinStaircaseExponents (n + 1) μ s ↔
      a 0 < s ∧ tailExponent a ∈ GriffinStaircaseExponents n (staircaseChildShape μ (a 0)) s := by
  rw [mem_griffinStaircaseExponents_iff a hs hheight, shuffleBound_child_iff,
    mem_griffinStaircaseExponents_iff _ hs ((staircaseChildShape_height_le μ (a 0)).trans hheight)]
  constructor
  · rintro ⟨hshuffle, hbound⟩
    exact ⟨hbound 0, hshuffle, fun i => hbound i.succ⟩
  · rintro ⟨hzero, hshuffle, htail⟩
    refine ⟨hshuffle, ?_⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hzero
    | succ j => exact htail j

@[simp] theorem tailExponent_cons (j : ℕ) (a : Fin n →₀ ℕ) :
    tailExponent (a.cons j) = a := by
  ext i
  rfl

def griffinStaircaseChildEquiv (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    GriffinStaircaseExponents (n + 1) μ s ≃
      Σ j : Fin s, GriffinStaircaseExponents n (staircaseChildShape μ j.val) s where
  toFun a :=
    ⟨⟨a.val 0, ((griffinStaircase_child_iff a.val hs hheight).mp a.property).1⟩,
      tailExponent a.val, ((griffinStaircase_child_iff a.val hs hheight).mp a.property).2⟩
  invFun b :=
    ⟨b.2.val.cons b.1.val, (griffinStaircase_child_iff _ hs hheight).mpr
      ⟨b.1.isLt, by simpa only [Finsupp.cons_zero, tailExponent_cons] using b.2.property⟩⟩
  left_inv a := Subtype.ext (Finsupp.cons_tail a.val)
  right_inv b := by
    rcases b with ⟨j, a⟩
    simp only [Finsupp.cons_zero]
    congr 1
    exact Subtype.ext (tailExponent_cons j.val a.val)

theorem card_griffinStaircase_recursion (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    Nat.card (GriffinStaircaseExponents (n + 1) μ s) =
      ∑ j : Fin s, Nat.card (GriffinStaircaseExponents n (staircaseChildShape μ j.val) s) := by
  letI := (finite_griffinStaircaseExponents (n := n + 1) (μ := μ) s hs hheight).fintype
  letI (j : Fin s) := (finite_griffinStaircaseExponents (n := n)
    (μ := staircaseChildShape μ j.val) s hs
      ((staircaseChildShape_height_le μ j.val).trans hheight)).fintype
  rw [Nat.card_congr (griffinStaircaseChildEquiv μ s hs hheight)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

theorem degree_cons_exponent (j : ℕ) (a : Fin n →₀ ℕ) :
    (a.cons j).degree = j + a.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.degree_eq_sum]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ]

theorem degree_eq_head_add_tail (a : Fin (n + 1) →₀ ℕ) :
    a.degree = a 0 + (tailExponent a).degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.degree_eq_sum]
  rfl

def staircaseDegreeChildEquiv (μ : YoungDiagram) (s d : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    StaircaseDegreeFiber (n + 1) μ s d ≃
      Σ j : Fin s, {a : Fin n →₀ ℕ //
        a ∈ GriffinStaircaseExponents n (staircaseChildShape μ j.val) s ∧
          j.val + a.degree = d} where
  toFun a :=
    ⟨⟨a.val 0, ((griffinStaircase_child_iff a.val hs hheight).mp a.property.1).1⟩,
      tailExponent a.val,
      ((griffinStaircase_child_iff a.val hs hheight).mp a.property.1).2,
      (degree_eq_head_add_tail a.val).symm.trans a.property.2⟩
  invFun b :=
    ⟨b.2.val.cons b.1.val,
      (griffinStaircase_child_iff _ hs hheight).mpr
        ⟨b.1.isLt, by simpa only [Finsupp.cons_zero, tailExponent_cons] using b.2.property.1⟩,
      (degree_cons_exponent b.1.val b.2.val).trans b.2.property.2⟩
  left_inv a := Subtype.ext (Finsupp.cons_tail a.val)
  right_inv b := by
    rcases b with ⟨j, a⟩
    simp only [Finsupp.cons_zero]
    congr 1
    exact Subtype.ext (tailExponent_cons j.val a.val)

/-- The full degree-preserving staircase recursion. Its right side is zero
when the first exponent exceeds the total degree, rather than using truncated
subtraction to add nonexistent degree-zero terms. -/
theorem card_staircaseDegree_recursion (μ : YoungDiagram) (s d : ℕ) (hs : 0 < s)
    (hheight : μ.colLen 0 ≤ s) :
    Nat.card (StaircaseDegreeFiber (n + 1) μ s d) =
      ∑ j : Fin s, if j.val ≤ d then
        Nat.card (StaircaseDegreeFiber n (staircaseChildShape μ j.val) s (d - j.val)) else 0 := by
  let A (j : Fin s) := {a : Fin n →₀ ℕ //
    a ∈ GriffinStaircaseExponents n (staircaseChildShape μ j.val) s ∧ j.val + a.degree = d}
  letI (j : Fin s) : Finite (A j) := by
    have hfinite : {a : Fin n →₀ ℕ |
        a ∈ GriffinStaircaseExponents n (staircaseChildShape μ j.val) s ∧
          j.val + a.degree = d}.Finite :=
      (Finsupp.finite_of_degree_le (σ := Fin n) d).subset (fun a ha => by
        change a.degree ≤ d
        have hd : j.val + a.degree = d := ha.2
        omega)
    exact hfinite.to_subtype
  rw [Nat.card_congr (staircaseDegreeChildEquiv μ s d hs hheight), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  change Nat.card (A j) = _
  by_cases h : j.val ≤ d
  · rw [if_pos h]
    apply Nat.card_congr
    exact (Equiv.refl (Fin n →₀ ℕ)).subtypeEquiv fun a => by
      change (_ ∧ j.val + a.degree = d) ↔ (_ ∧ a.degree = d - j.val)
      constructor <;> rintro ⟨ha, hd⟩ <;> exact ⟨ha, by omega⟩
  · rw [if_neg h]
    haveI : IsEmpty (A j) := ⟨fun a => h (by have := a.property.2; omega)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end HigherSpecht
end
end CanonicalSource41

section CanonicalSource42
/- Source: HigherSpecht/EligibleIndexCountEmpty.lean -/



/-!
# The literal empty-partition Griffin index count

The monotone boost in stable standardization is converted into a genuine Young
diagram by reversing its parts. RSK then gives exactly the manuscript's pair
of standard tableaux and its rectangle bound. This proves the unrestricted
`s^n` count used in Section 5; it does not prove the count for a nonempty λ.
-/

noncomputable section
open TauCeti Finset
open scoped Classical

namespace HigherSpecht

def partitionOfBoost {n : ℕ} (b : Fin n → ℕ) (hb : Monotone b) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn fun i => b i.rev)
    (List.sortedGE_ofFn_iff.mpr fun i j hij => hb (Fin.rev_le_rev.mpr hij))

theorem partitionOfBoost_height {n : ℕ} (b : Fin n → ℕ) (hb : Monotone b) :
    (partitionOfBoost b hb).colLen 0 ≤ n := by
  by_contra h
  have hc : (n, 0) ∈ partitionOfBoost b hb := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge h)
  rw [partitionOfBoost, YoungDiagram.mem_ofRowLens] at hc
  obtain ⟨hn, _⟩ := hc
  have hnn : n < n := by simpa only [List.length_ofFn] using hn
  exact (Nat.lt_irrefl n) hnn

theorem partitionOfBoost_rowLen {n : ℕ} (b : Fin n → ℕ) (hb : Monotone b) (i : Fin n) :
    (partitionOfBoost b hb).rowLen i.val = b i.rev := by
  have h := YoungDiagram.rowLen_ofRowLens
    (w := List.ofFn fun i : Fin n => b i.rev)
    (hw := List.sortedGE_ofFn_iff.mpr fun i j hij => hb (Fin.rev_le_rev.mpr hij))
    ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  simpa only [partitionOfBoost, Fin.getElem_fin, List.getElem_ofFn] using h

theorem boostLabel_partitionOfBoost {n : ℕ} (b : Fin n → ℕ) (hb : Monotone b) (i : Fin n) :
    boostLabel (partitionOfBoost b hb) n i = b i := by
  have he : n - 1 - i.val = i.rev.val := by rw [Fin.val_rev]; omega
  rw [boostLabel, he, partitionOfBoost_rowLen, Fin.rev_rev]

theorem partitionOfBoost_boostLabel (eta : YoungDiagram) (n : ℕ)
    (heta : eta.colLen 0 ≤ n) :
    partitionOfBoost (boostLabel eta n) (boostLabel_mono eta n) = eta := by
  have hrow (j : ℕ) :
      (partitionOfBoost (boostLabel eta n) (boostLabel_mono eta n)).rowLen j = eta.rowLen j := by
    by_cases hj : j < n
    · rw [partitionOfBoost_rowLen _ _ ⟨j, hj⟩]
      dsimp only [boostLabel]
      congr 1
      change n - 1 - (n - (j + 1)) = j
      omega
    · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le
        ((partitionOfBoost_height _ _).trans (le_of_not_gt hj)),
        YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans (le_of_not_gt hj))]
  exact YoungDiagram.rowLen_injective (funext hrow)

theorem partitionOfBoost_card {n : ℕ} (b : Fin n → ℕ) (hb : Monotone b) :
    (partitionOfBoost b hb).card = ∑ i, b i := by
  rw [YoungDiagram.card_eq_sum_range_rowLen _ (partitionOfBoost_height b hb),
    ← Fin.sum_univ_eq_sum_range]
  simp only [partitionOfBoost_rowLen]
  exact Equiv.sum_comp Fin.revPerm b

def permutationDescentNumber {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  wordCochargeLabel (permutationValueWord σ) (n - 1)

structure PermutationRectangleIndex (n s : ℕ) where
  permutation : Equiv.Perm (Fin n)
  multiplier : YoungDiagram
  height : multiplier.colLen 0 ≤ n
  descents_lt : permutationDescentNumber permutation < s
  width : multiplier.rowLen 0 ≤ s - permutationDescentNumber permutation - 1

def codeToRectangle {n s : ℕ} (hs : 0 < s) (c : BoundedCochargeCode n s) :
    PermutationRectangleIndex n s where
  permutation := c.permutation
  multiplier := partitionOfBoost c.boost c.boost_mono
  height := partitionOfBoost_height _ _
  descents_lt := by
    cases n with
    | zero => simpa only [permutationDescentNumber, Nat.zero_sub,
        wordCochargeLabel_zero] using hs
    | succ n =>
        have h := c.bound (Fin.last n)
        change wordCochargeLabel (permutationValueWord c.permutation) n +
          c.boost (Fin.last n) < s at h
        change wordCochargeLabel (permutationValueWord c.permutation) n < s
        omega
  width := by
    cases n with
    | zero =>
        rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (partitionOfBoost_height _ _)]
        exact Nat.zero_le _
    | succ n =>
        have h := c.bound (Fin.last n)
        have hrow := partitionOfBoost_rowLen c.boost c.boost_mono (0 : Fin (n + 1))
        simp only [Fin.val_zero, Fin.rev_zero] at hrow
        rw [hrow]
        dsimp only [permutationCocharge, permutationDescentNumber] at h ⊢
        simp only [Fin.val_last, Nat.add_sub_cancel] at h ⊢
        omega

def rectangleToCode {n s : ℕ} (c : PermutationRectangleIndex n s) :
    BoundedCochargeCode n s where
  permutation := c.permutation
  boost := boostLabel c.multiplier n
  boost_mono := boostLabel_mono _ _
  bound i := by
    have hcc : permutationCocharge c.permutation i ≤ permutationDescentNumber c.permutation :=
      wordCochargeLabel_mono _ (by have := i.isLt; omega)
    have hb := c.multiplier.rowLen_anti 0 (n - 1 - i.val) (Nat.zero_le _)
    have hd := c.descents_lt
    have hw := c.width
    change permutationCocharge c.permutation i + c.multiplier.rowLen (n - 1 - i.val) < s
    omega

def codeRectangleEquiv (n s : ℕ) (hs : 0 < s) :
    BoundedCochargeCode n s ≃ PermutationRectangleIndex n s where
  toFun := codeToRectangle hs
  invFun := rectangleToCode
  left_inv c := by
    have hb : boostLabel (partitionOfBoost c.boost c.boost_mono) n = c.boost := by
      funext i
      exact boostLabel_partitionOfBoost _ _ i
    cases c
    simp only [codeToRectangle, rectangleToCode, hb]
  right_inv c := by
    have he := partitionOfBoost_boostLabel c.multiplier n c.height
    cases c
    simp only [codeToRectangle, rectangleToCode, he]

theorem prefixEligible_bot {n : ℕ} (P : StandardPair n) :
    prefixEligible ⊥ (by simp [YoungDiagram.card]) P := by
  obtain ⟨nu, hnu⟩ := exists_catTableauOutput
    (prefixTableau P.left (⊥ : YoungDiagram).card (by simp [YoungDiagram.card]))
  refine ⟨nu, hnu, ?_⟩
  intro r
  simp only [YoungDiagram.rowLen_bot, Finset.sum_const_zero]
  exact Nat.zero_le _

def rectangleGriffinEmptyEquiv (n s : ℕ) :
    PermutationRectangleIndex n s ≃ GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s where
  toFun c :=
    { pair := rskPair n c.permutation
      multiplier := c.multiplier
      eligible := prefixEligible_bot _
      descents_lt := by
        rw [rskPair_left_descentNumber]
        exact c.descents_lt
      multiplier_length := by simpa [YoungDiagram.card] using c.height
      multiplier_width := by
        rw [rskPair_left_descentNumber]
        exact c.width }
  invFun c :=
    { permutation := (rskPair n).symm c.pair
      multiplier := c.multiplier
      height := by simpa [YoungDiagram.card] using c.multiplier_length
      descents_lt := by
        have h := rskPair_left_descentNumber ((rskPair n).symm c.pair)
        have hp := congrArg (fun P : StandardPair n => descentNumber P.left)
          ((rskPair n).apply_symm_apply c.pair)
        have hdes : descentNumber c.pair.left =
            permutationDescentNumber ((rskPair n).symm c.pair) := hp.symm.trans h
        exact (congrArg (fun d : ℕ => d < s) hdes).mp c.descents_lt
      width := by
        have h := rskPair_left_descentNumber ((rskPair n).symm c.pair)
        have hp := congrArg (fun P : StandardPair n => descentNumber P.left)
          ((rskPair n).apply_symm_apply c.pair)
        have hdes : descentNumber c.pair.left =
            permutationDescentNumber ((rskPair n).symm c.pair) := hp.symm.trans h
        exact (congrArg (fun d : ℕ => c.multiplier.rowLen 0 ≤ s - d - 1)
          hdes).mp c.multiplier_width }
  left_inv c := by cases c; simp only [Equiv.symm_apply_apply]
  right_inv c := by cases c; simp only [Equiv.apply_symm_apply]

def boundedWordGriffinEmptyEquiv (n s : ℕ) (hs : 0 < s) :
    (Fin n → Fin s) ≃ GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s :=
  (boundedWordCochargeEquiv n s).trans
    ((codeRectangleEquiv n s hs).trans (rectangleGriffinEmptyEquiv n s))

/-- The complete actual empty-partition index count in Section 5. No
catabolizability count for a nonempty partition is inferred from it. -/
theorem card_griffinIndex_empty (n s : ℕ) (hs : 0 < s) :
    Nat.card (GriffinIndex n ⊥ (by simp [YoungDiagram.card]) s) = s ^ n := by
  rw [← Nat.card_congr (boundedWordGriffinEmptyEquiv n s hs), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_fin]

end HigherSpecht
end
end CanonicalSource42

section CanonicalSource43
/- Source: HigherSpecht/MultiplicitySpaces.lean -/



/-!
# Independent vectors in a genuine Young-symmetrizer image

This is the finite-dimensional multiplicity-space step of Lemma 3.3.  The
evaluation map is the previously verified symmetric-group decomposition, not
an assumed independence of the generated copies.  Tensor-product independence
then gives all vectors in each copy simultaneously.  Homogeneous pieces of the
polynomial representation are finite-dimensional, which is the application
needed by the manuscript.
-/

noncomputable section

open Module TauCeti
open scoped TensorProduct DirectSum

namespace HigherSpecht

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

abbrev YoungIdeal (mu : n.Partition) :=
  (Ideal.span {mu.youngSymmetrizer K} : Ideal (MonoidAlgebra K (Equiv.Perm (Fin n))))

abbrev YoungImage (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :=
  LinearMap.range (rho.asAlgebraHom (mu.youngSymmetrizer K))

def youngComponentEvaluation (rho : Representation K (Equiv.Perm (Fin n)) M)
    (mu : n.Partition) : (YoungIdeal (K := K) mu ⊗[K] YoungImage rho mu) →ₗ[K] M :=
  rho.youngSymmetrizerEval ∘ₗ DirectSum.lof K (n.Partition)
    (fun nu => YoungIdeal (K := K) nu ⊗[K] YoungImage rho nu) mu

@[simp] theorem youngComponentEvaluation_tmul
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition)
    (a : YoungIdeal (K := K) mu) (v : YoungImage rho mu) :
    youngComponentEvaluation rho mu (a ⊗ₜ[K] v) =
      rho.asAlgebraHom (a : MonoidAlgebra K (Equiv.Perm (Fin n))) v := by
  exact rho.youngSymmetrizerEval_lof_tmul mu a v

theorem youngComponentEvaluation_injective
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :
    Function.Injective (youngComponentEvaluation rho mu) := by
  intro x y hxy
  have h := rho.youngSymmetrizerEval_bijective.1 hxy
  have hmu := congrArg (fun z => z mu) h
  simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hmu

/-- Transport tensor-product independence through an injective linear map.
The pointwise equality identifies the resulting family without simplifying
representation-specific submodule or scalar-action structures. -/
private theorem linearIndependent_tmul_image
    {P Q V : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup V] [Module K V]
    {A I : Type*} (a : A → P) (v : I → Q)
    (f : (P ⊗[K] Q) →ₗ[K] V) (hf : Function.Injective f)
    (ha : LinearIndependent K a) (hv : LinearIndependent K v)
    (b : A × I → V) (hb : ∀ z, f (a z.1 ⊗ₜ[K] v z.2) = b z) :
    LinearIndependent K b := by
  have ht : LinearIndependent K (fun z : A × I => a z.1 ⊗ₜ[K] v z.2) :=
    LinearIndependent.tmul_of_isDomain (R := K) (M := P) (N := Q)
      (ι := A) (κ := I) (v := a) (w := v) ha hv
  have hm : LinearIndependent K (fun z : A × I => f (a z.1 ⊗ₜ[K] v z.2)) :=
    LinearIndependent.map' (R := K) (M := P ⊗[K] Q) (M' := V)
      (ι := A × I) (v := fun z : A × I => a z.1 ⊗ₜ[K] v z.2)
      ht f (LinearMap.ker_eq_bot.mpr hf)
  exact Eq.mp (congrArg (fun w : A × I → V => LinearIndependent K w) (funext hb)) hm

set_option maxHeartbeats 800000 in
/-- All basis vectors in all copies belonging to independent multiplicity
vectors are independent. This is the actual injectivity assertion underlying
the direct-sum conclusion of Lemma 3.3. -/
theorem lemma_3_3_independent_copies
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition)
    {A I : Type*} (a : A → YoungIdeal (K := K) mu) (v : I → YoungImage rho mu)
    (ha : LinearIndependent K a) (hv : LinearIndependent K v) :
    LinearIndependent K (fun z : A × I =>
      rho.asAlgebraHom (a z.1 : MonoidAlgebra K (Equiv.Perm (Fin n))) (v z.2)) := by
  exact linearIndependent_tmul_image (K := K)
    (P := YoungIdeal (K := K) mu) (Q := YoungImage rho mu) (V := M)
    a v (youngComponentEvaluation rho mu)
    (youngComponentEvaluation_injective rho mu) ha hv
    (fun z : A × I =>
      rho.asAlgebraHom (a z.1 : MonoidAlgebra K (Equiv.Perm (Fin n))) (v z.2 : M))
    (fun z => youngComponentEvaluation_tmul rho mu (a z.1) (v z.2))

/-- The injective map on the entire tensor product identifies its image with
the sum of the generated copies, independently of a chosen basis.  The explicit
subtype bundles a linear map together with its injectivity proof. -/
def youngComponentEmbedding
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :
    {f : (YoungIdeal (K := K) mu ⊗[K] YoungImage rho mu) →ₗ[K] M // Function.Injective f} :=
  ⟨youngComponentEvaluation rho mu, youngComponentEvaluation_injective rho mu⟩

@[simp] theorem youngComponentEmbedding_val
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :
    (youngComponentEmbedding rho mu).val = youngComponentEvaluation rho mu := rfl

theorem youngComponentEmbedding_injective
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :
    Function.Injective (youngComponentEmbedding rho mu).val :=
  (youngComponentEmbedding rho mu).property

end HigherSpecht
end
end CanonicalSource43

section CanonicalSource44
/- Source: HigherSpecht/IntertwinerCopies.lean -/



/-!
# Promoting actual equivariant maps to independent complete copies

Evaluation at any one source vector detects independence of intertwining maps.
The previously verified Young-symmetrizer decomposition then makes their full
images independent, including across distinct shapes.  This avoids identifying
the paper's column-after-row operator with the library's opposite product.
-/

noncomputable section

open Module TauCeti
open scoped TensorProduct DirectSum

namespace HigherSpecht

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

abbrev YoungIdealRepresentation (mu : n.Partition) :=
  Representation.ofModule' (k := K) (G := Equiv.Perm (Fin n)) (YoungIdeal (K := K) mu)

def youngQuasiScalar (mu : n.Partition) : K :=
  algebraMap ℚ K ((n.factorial : ℚ) / finrank ℚ (spechtModule mu))

 theorem youngQuasiScalar_ne_zero (mu : n.Partition) : youngQuasiScalar (K := K) mu ≠ 0 := by
  rw [youngQuasiScalar, map_ne_zero]
  exact div_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    (Nat.cast_ne_zero.mpr (finrank_spechtModule_pos mu).ne')

def youngHomImageEquiv (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition) :
    (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho ≃ₗ[K] YoungImage rho mu :=
  Representation.spanSingletonHomEquivRange rho
    (isUnit_iff_ne_zero.mpr (youngQuasiScalar_ne_zero (K := K) mu)) (mu.youngSymmetrizer_mul_self K)

def intertwinerEvaluation {V : Type*} [AddCommGroup V] [Module K V]
    (rhoV : Representation K (Equiv.Perm (Fin n)) V)
    (rho : Representation K (Equiv.Perm (Fin n)) M) (v : V) :
    rhoV.IntertwiningMap rho →ₗ[K] M where
  toFun f := f v
  map_add' f g := rfl
  map_smul' c f := rfl

 theorem youngIdeal_action_generator (mu : n.Partition) (a : YoungIdeal (K := K) mu) :
    (YoungIdealRepresentation (K := K) mu).asAlgebraHom
        (a : MonoidAlgebra K (Equiv.Perm (Fin n)))
        (TauCeti.spanSingletonGenerator (mu.youngSymmetrizer K)) =
      youngQuasiScalar (K := K) mu • a := by
  rw [TauCeti.Representation.asAlgebraHom_ofModule'_apply]
  apply Subtype.ext
  obtain ⟨r, rfl⟩ := TauCeti.exists_smul_spanSingletonGenerator a
  simp only [Submodule.coe_smul, smul_eq_mul, TauCeti.coe_spanSingletonGenerator,
    Submodule.coe_smul_of_tower]
  rw [mul_assoc, mu.youngSymmetrizer_mul_self K]
  simp only [youngQuasiScalar, Algebra.mul_smul_comm, smul_mul_assoc]

 theorem youngImage_action_intertwiner
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition)
    (f : (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho)
    (a : YoungIdeal (K := K) mu) :
    rho.asAlgebraHom (a : MonoidAlgebra K (Equiv.Perm (Fin n)))
        (youngHomImageEquiv rho mu f : M) = youngQuasiScalar (K := K) mu • f a := by
  have hEval : (youngHomImageEquiv rho mu f : M) =
      f (TauCeti.spanSingletonGenerator (mu.youngSymmetrizer K)) :=
    Representation.coe_spanSingletonHomEquivRange_apply rho
      (isUnit_iff_ne_zero.mpr (youngQuasiScalar_ne_zero (K := K) mu))
      (mu.youngSymmetrizer_mul_self K) f
  rw [hEval, ← f.apply_asAlgebraHom, youngIdeal_action_generator, map_smul]

/-- One shape, with a freely chosen test vector in its actual source ideal. -/
 theorem independent_intertwiner_copies
    (rho : Representation K (Equiv.Perm (Fin n)) M) (mu : n.Partition)
    {A I : Type*} (a : A → YoungIdeal (K := K) mu)
    (f : I → (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho)
    (v0 : YoungIdeal (K := K) mu) (ha : LinearIndependent K a)
    (hf : LinearIndependent K (fun i => f i v0)) :
    LinearIndependent K (fun z : A × I => f z.2 (a z.1)) := by
  have hfmap : LinearIndependent K f :=
    LinearIndependent.of_comp (intertwinerEvaluation _ rho v0) hf
  have hv := hfmap.map' (youngHomImageEquiv rho mu).toLinearMap
    (LinearMap.ker_eq_bot.mpr (youngHomImageEquiv rho mu).injective)
  have hscaled := lemma_3_3_independent_copies rho mu a (fun i => youngHomImageEquiv rho mu (f i)) ha hv
  simp only [youngImage_action_intertwiner] at hscaled
  let u : Kˣ := Units.mk0 (youngQuasiScalar (K := K) mu) (youngQuasiScalar_ne_zero (K := K) mu)
  exact (LinearIndependent.units_smul_iff (fun z : A × I => f z.2 (a z.1)) (fun _ => u)).mp hscaled

/-- Independent tensor families remain independent after an injective map
from their direct sum, including independent rescaling in each summand.
All direct-sum and tensor reasoning takes place over abstract modules. -/
private theorem linearIndependent_directSum_tmul_image
    {J : Type*} [DecidableEq J] {P Q : J → Type*} {V : Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module K (Q j)]
    [AddCommGroup V] [Module K V] {A I : J → Type*}
    (a : ∀ j, A j → P j) (v : ∀ j, I j → Q j)
    (ha : ∀ j, LinearIndependent K (a j)) (hv : ∀ j, LinearIndependent K (v j))
    (F : (⨁ j, P j ⊗[K] Q j) →ₗ[K] V) (hF : Function.Injective F)
    (b : (Σ j, A j × I j) → V) (u : J → Kˣ)
    (hb : ∀ z, F (DirectSum.lof K J (fun j => P j ⊗[K] Q j) z.1
      (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2)) = u z.1 • b z) :
    LinearIndependent K b := by
  have ht (j : J) : LinearIndependent K (fun z : A j × I j => a j z.1 ⊗ₜ[K] v j z.2) :=
    LinearIndependent.tmul_of_isDomain (R := K) (M := P j) (N := Q j)
      (ι := A j) (κ := I j) (v := a j) (w := v j) (ha j) (hv j)
  have hs : LinearIndependent K (fun z : Σ j, A j × I j =>
      (DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2) : ⨁ j, P j ⊗[K] Q j)) :=
    DFinsupp.linearIndependent_single (R := K) (M := fun j => P j ⊗[K] Q j)
      (φ := fun j => A j × I j) (fun j (z : A j × I j) => a j z.1 ⊗ₜ[K] v j z.2) ht
  have hm : LinearIndependent K (fun z : Σ j, A j × I j =>
      F (DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))) :=
    LinearIndependent.map' (R := K) (M := ⨁ j, P j ⊗[K] Q j) (M' := V)
      (ι := Σ j, A j × I j)
      (v := fun z : Σ j, A j × I j =>
        DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))
      hs F (LinearMap.ker_eq_bot.mpr hF)
  have heq : (fun z : Σ j, A j × I j =>
      F (DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))) =
      (fun z : Σ j, A j × I j => u z.1 • b z) := by
    funext z
    exact (congrArg F (DirectSum.single_eq_lof (R := K) z.1
      (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))).trans (hb z)
  have hscaled : LinearIndependent K (fun z : Σ j, A j × I j => u z.1 • b z) :=
    Eq.mp (congrArg (fun w : (Σ j, A j × I j) → V => LinearIndependent K w) heq) hm
  exact (LinearIndependent.units_smul_iff (R := K) (M := V) b (fun z => u z.1)).mp hscaled

set_option maxHeartbeats 800000 in
/-- Distinct partitions occupy distinct summands of the actual decomposition.
Thus complete-copy independence is simultaneous across all shapes. -/
 theorem independent_intertwiner_copies_all_shapes
    (rho : Representation K (Equiv.Perm (Fin n)) M)
    {A I : n.Partition → Type*}
    (a : ∀ mu, A mu → YoungIdeal (K := K) mu)
    (f : ∀ mu, I mu → (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho)
    (v0 : ∀ mu, YoungIdeal (K := K) mu)
    (ha : ∀ mu, LinearIndependent K (a mu))
    (hf : ∀ mu, LinearIndependent K (fun i => f mu i (v0 mu))) :
    LinearIndependent K (fun z : Σ mu, A mu × I mu => f z.1 z.2.2 (a z.1 z.2.1)) := by
  classical
  let v : ∀ mu, I mu → YoungImage rho mu := fun mu i => youngHomImageEquiv rho mu (f mu i)
  have hv (mu : n.Partition) : LinearIndependent K (v mu) := by
    have hmap : LinearIndependent K (f mu) :=
      LinearIndependent.of_comp (R := K)
        (M := (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho) (M' := M)
        (v := f mu) (intertwinerEvaluation _ rho (v0 mu)) (hf mu)
    exact LinearIndependent.map' (R := K)
      (M := (YoungIdealRepresentation (K := K) mu).IntertwiningMap rho)
      (M' := YoungImage rho mu) (v := f mu) hmap
      (youngHomImageEquiv rho mu).toLinearMap
      (LinearMap.ker_eq_bot.mpr (youngHomImageEquiv rho mu).injective)
  let u : n.Partition → Kˣ := fun mu =>
    Units.mk0 (youngQuasiScalar (K := K) mu) (youngQuasiScalar_ne_zero (K := K) mu)
  refine linearIndependent_directSum_tmul_image (K := K) (J := n.Partition)
    (P := fun mu => YoungIdeal (K := K) mu) (Q := fun mu => YoungImage rho mu) (V := M)
    a v ha hv rho.youngSymmetrizerEval rho.youngSymmetrizerEval_bijective.1
    (fun z : Σ mu, A mu × I mu => f z.1 z.2.2 (a z.1 z.2.1)) u ?_
  intro z
  exact (rho.youngSymmetrizerEval_lof_tmul z.1 (a z.1 z.2.1) (v z.1 z.2.2)).trans
    (youngImage_action_intertwiner rho z.1 (f z.1 z.2.2) (a z.1 z.2.1))

end HigherSpecht
end
end CanonicalSource44

section CanonicalSource45
/- Source: HigherSpecht/FinitePairing.lean -/



/-!
# Finite triangular coefficient pairings

This is the linear-algebra conclusion used after the manuscript's coefficient
inequalities have been established.  Its hypotheses are explicit auxiliary
pairing conditions; it does not assert that higher Specht polynomials satisfy
them without their separate combinatorial proof.
-/

noncomputable section

open Matrix

namespace HigherSpecht

variable {R V ι : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup V] [Module R V] [Fintype ι] [LinearOrder ι]

def pairingMap (L : ι → Module.Dual R V) : V →ₗ[R] (ι → R) :=
  LinearMap.pi L

@[simp] theorem pairingMap_apply (L : ι → Module.Dual R V) (v : V) (i : ι) :
    pairingMap L v i = L i v := rfl

theorem linearIndependent_of_triangular_pairing
    (L : ι → Module.Dual R V) (v : ι → V)
    (hzero : ∀ i j, j < i → L i (v j) = 0)
    (hdiag : ∀ i, L i (v i) ≠ 0) : LinearIndependent R v := by
  let A : Matrix ι ι R := fun i j => L i (v j)
  have hA : A.IsUpperTriangular := hzero
  have hdet : A.det ≠ 0 := hA.det_ne_zero_iff.mpr hdiag
  have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  exact LinearIndependent.of_comp (pairingMap L) hcols

/-- Quotient independence follows once each coefficient functional kills the
actual submodule of relations. -/
theorem linearIndependent_quotient_of_triangular_pairing
    (N : Submodule R V) (L : ι → Module.Dual R V) (v : ι → V)
    (hkill : ∀ i, N ≤ LinearMap.ker (L i))
    (hzero : ∀ i j, j < i → L i (v j) = 0)
    (hdiag : ∀ i, L i (v i) ≠ 0) :
    LinearIndependent R (fun i => N.mkQ (v i)) := by
  let Lq : ι → Module.Dual R (V ⧸ N) := fun i => N.liftQ (L i) (hkill i)
  apply linearIndependent_of_triangular_pairing Lq
  · intro i j hij
    exact hzero i j hij
  · intro i
    exact hdiag i

omit [Fintype ι] [LinearOrder ι] in
/-- Ties in a numerical key cause no difficulty when distinct tied vectors
have zero cross-pairings.  This avoids imposing an arbitrary mathematical
injectivity assumption on the norm/prefix key. -/
theorem linearIndependent_of_pairing_key {κ : Type*} [LinearOrder κ]
    (key : ι → κ) (L : ι → Module.Dual R V) (v : ι → V)
    (hzero : ∀ i j, i ≠ j → key j ≤ key i → L i (v j) = 0)
    (hdiag : ∀ i, L i (v i) ≠ 0) : LinearIndependent R v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  by_contra hci
  let support := s.filter fun j => c j ≠ 0
  have hsupport : support.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hj, hmax⟩ := support.exists_max_image key hsupport
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hp := congrArg (L j) hsum
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hp
  have hone : (∑ l ∈ s, c l * L j (v l)) = c j * L j (v j) := by
    apply Finset.sum_eq_single j
    · intro l hls hlj
      by_cases hcl : c l = 0
      · simp [hcl]
      · rw [hzero j l hlj.symm (hmax l (Finset.mem_filter.mpr ⟨hls, hcl⟩)), mul_zero]
    · exact fun h => (h hjs).elim
  rw [hone] at hp
  exact (mul_ne_zero hcj (hdiag j)) hp

end HigherSpecht
end
end CanonicalSource45

section CanonicalSource46
/- Source: HigherSpecht/TriangularCriterion.lean -/



/-!
# The integral triangular coefficient criterion

This file proves the coefficient-functional conclusion of Lemma 3.1 from
its polynomial support and insertion-witness hypotheses.  The functional is
identified with the actual divided-power contraction, and the diagonal is
the coefficient times the exact number of permutations fixing both the
rejection counts and the original columns.  It is an auxiliary theorem;
applications must construct the witness and verify the support hypotheses.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Function Equiv

namespace HigherSpecht

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def intExponent (a : ι →₀ ℕ) : ι → ℤ := fun i => a i

theorem intExponent_injective : Function.Injective (intExponent : (ι →₀ ℕ) → ι → ℤ) := by
  intro a b h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

def permutedExponent (a : ι →₀ ℕ) (σ : Equiv.Perm ι) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => a (σ i)

@[simp] theorem permutedExponent_apply (a : ι →₀ ℕ) (σ : Equiv.Perm ι) (i : ι) :
    permutedExponent a σ i = a (σ i) := rfl

@[simp] theorem permutedExponent_one (a : ι →₀ ℕ) : permutedExponent a 1 = a := by
  ext i
  rfl

@[simp] theorem intExponent_permuted (a : ι →₀ ℕ) (σ : Equiv.Perm ι) :
    intExponent (permutedExponent a σ) = intExponent a ∘ σ := rfl

theorem intExponent_sub {a r : ι →₀ ℕ} (hr : r ≤ a) :
    intExponent (a - r) = fun i => intExponent a i - intExponent r i := by
  funext i
  simp only [intExponent, Finsupp.tsub_apply, Nat.cast_sub (hr i)]

def coefficientSign (σ : Equiv.Perm ι) : R := ((Equiv.Perm.sign σ : ℤ) : R)

@[simp] theorem coefficientSign_mul_self (σ : Equiv.Perm ι) :
    coefficientSign (R := R) σ * coefficientSign σ = 1 := by
  unfold coefficientSign
  rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

@[simp] theorem coefficientSign_one : coefficientSign (R := R) (1 : Equiv.Perm ι) = 1 := by
  simp [coefficientSign]

/-- The actual alternating divided-power witness.  Inverse permutations
would give the same sum, so composing exponent functions on the right is
equivalent to the manuscript's permutation action. -/
def coefficientWitness (G : Subgroup (Equiv.Perm ι)) (a : ι →₀ ℕ) : MvPolynomial ι R :=
  ∑ τ : G, MvPolynomial.monomial (permutedExponent a τ.val) (coefficientSign τ.val)

def witnessCoefficient (G : Subgroup (Equiv.Perm ι)) (a r : ι →₀ ℕ) :
    Module.Dual R (MvPolynomial ι R) :=
  contractionCoefficient (coefficientWitness G a) r

theorem witnessCoefficient_apply (G : Subgroup (Equiv.Perm ι)) (a r : ι →₀ ℕ)
    (P : MvPolynomial ι R) :
    witnessCoefficient G a r P = ∑ τ : G,
      if r ≤ permutedExponent a τ.val then
        coefficientSign τ.val * P.coeff (permutedExponent a τ.val - r) else 0 := by
  rw [witnessCoefficient, coefficientWitness, contractionCoefficient_signed_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro τ hτ
  split_ifs <;> rfl

/-- Polynomial-side conditions with the column-weight key.  At a fixed
degree, this weight is the sum of the negatives of all column-prefix sums,
up to a constant; the prefix inequalities imply these exact conditions. -/
structure TriangularSupport (c : ι → ℤ) (b : ι →₀ ℕ)
    (P : MvPolynomial ι R) : Prop where
  norm : ∀ beta, P.coeff beta ≠ 0 → squareNorm (intExponent beta) ≤ squareNorm (intExponent b)
  weight : ∀ beta, P.coeff beta ≠ 0 →
    squareNorm (intExponent beta) = squareNorm (intExponent b) →
      columnWeight c (intExponent beta) ≤ columnWeight c (intExponent b)
  orbit : ∀ beta, P.coeff beta ≠ 0 →
    squareNorm (intExponent beta) = squareNorm (intExponent b) →
    columnWeight c (intExponent beta) = columnWeight c (intExponent b) →
      ∃ ρ : Equiv.Perm ι, c ∘ ρ = c ∧ intExponent beta = intExponent b ∘ ρ

variable {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq κ] [DecidableEq ν]

/-- All off-diagonal entries below the norm/column-weight key vanish.
Distinct tied fillings are handled by the same argument. -/
theorem witnessCoefficient_eq_zero_of_key
    {u : ι → κ} {v : ι → ν} {a r b d : ι →₀ ℕ} {c row : ι → ℤ}
    (hw : RearrangementWitness u v (intExponent a) (intExponent r) (intExponent b) c)
    (G : Subgroup (Equiv.Perm ι)) (hG : ∀ τ : G, ∀ i, u (τ.val i) = u i)
    (P : MvPolynomial ι R) (hP : TriangularSupport c d P)
    (hkey : normWeightKey c (intExponent d) ≤ normWeightKey c (intExponent b))
    (hbd : b ≠ d)
    (hrow : ∀ j, Function.Injective (fun i : {i // c i = j} => row i))
    (hb : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => intExponent b i))
    (hd : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => intExponent d i)) :
    witnessCoefficient G a r P = 0 := by
  rw [witnessCoefficient_apply]
  apply Finset.sum_eq_zero
  intro τ hτ
  split_ifs with hr
  · have hz : P.coeff (permutedExponent a τ.val - r) = 0 := by
      by_contra hn
      have hi : intExponent b = intExponent d := contribution_same_filling hw τ.val (hG τ)
        ((intExponent_sub hr).trans rfl) (hP.norm _ hn) (hP.weight _ hn)
        (hP.orbit _ hn) hkey row hrow hb hd
      exact hbd (intExponent_injective hi)
    rw [hz, mul_zero]
  · rfl

/-- The finite set whose cardinality appears on the diagonal.  This is
literally the intersection of the witness group with the two stabilizers. -/
def fixedWitnessPermutations (G : Subgroup (Equiv.Perm ι)) (r : ι →₀ ℕ) (c : ι → ℤ) :
    Finset G := Finset.univ.filter fun τ => intExponent r ∘ τ.val = intExponent r ∧ c ∘ τ.val = c

theorem mem_fixedWitnessPermutations (G : Subgroup (Equiv.Perm ι))
    (r : ι →₀ ℕ) (c : ι → ℤ) (τ : G) :
    τ ∈ fixedWitnessPermutations G r c ↔
      intExponent r ∘ τ.val = intExponent r ∧ c ∘ τ.val = c := by
  simp [fixedWitnessPermutations]

theorem fixedWitnessPermutations_nonempty (G : Subgroup (Equiv.Perm ι))
    (r : ι →₀ ℕ) (c : ι → ℤ) : (fixedWitnessPermutations G r c).Nonempty := by
  refine ⟨1, ?_⟩
  simp [mem_fixedWitnessPermutations, Function.comp_def]

/-- The exact integral diagonal in Lemma 3.1.  Alternation is imposed on
the original column group, not on the witness group. -/
theorem witnessCoefficient_diagonal
    {u : ι → κ} {v : ι → ν} {a r b : ι →₀ ℕ} {c : ι → ℤ}
    (hw : RearrangementWitness u v (intExponent a) (intExponent r) (intExponent b) c)
    (G : Subgroup (Equiv.Perm ι)) (hG : ∀ τ : G, ∀ i, u (τ.val i) = u i)
    (P : MvPolynomial ι R) (hP : TriangularSupport c b P)
    (hAlt : ∀ τ : Equiv.Perm ι, c ∘ τ = c →
      P.coeff (permutedExponent b τ) = coefficientSign τ * P.coeff b) :
    witnessCoefficient G a r P =
      P.coeff b * ((fixedWitnessPermutations G r c).card : R) := by
  rw [witnessCoefficient_apply]
  have hterm (τ : G) :
      (if r ≤ permutedExponent a τ.val then
        coefficientSign τ.val * P.coeff (permutedExponent a τ.val - r) else 0) =
      if τ ∈ fixedWitnessPermutations G r c then P.coeff b else 0 := by
    by_cases ht : τ ∈ fixedWitnessPermutations G r c
    · obtain ⟨hr, hc⟩ := (mem_fixedWitnessPermutations G r c τ).mp ht
      have ha (i : ι) : a (τ.val i) = b (τ.val i) + r i := by
        have hsub := hw.subtraction (τ.val i)
        have hri := congrFun hr i
        dsimp [intExponent, Function.comp_apply] at hsub hri
        omega
      have hra : r ≤ permutedExponent a τ.val := fun i => by
        simp only [permutedExponent_apply, ha]
        omega
      have hdif : permutedExponent a τ.val - r = permutedExponent b τ.val := by
        ext i
        simp only [Finsupp.tsub_apply, permutedExponent_apply, ha, Nat.add_sub_cancel]
      rw [if_pos hra, if_pos ht, hdif, hAlt τ.val hc, ← mul_assoc,
        coefficientSign_mul_self, one_mul]
    · rw [if_neg ht]
      split_ifs with hra
      · have hz : P.coeff (permutedExponent a τ.val - r) = 0 := by
          by_contra hn
          have hbeta : intExponent (permutedExponent a τ.val - r) =
              fun i => intExponent a (τ.val i) - intExponent r i :=
            (intExponent_sub hra).trans rfl
          have hnorm : squareNorm (intExponent b) =
              squareNorm (fun i => intExponent a (τ.val i) - intExponent r i) := by
            apply le_antisymm (hw.norm_le τ.val (hG τ))
            simpa only [← hbeta] using hP.norm _ hn
          have hweight : columnWeight c (intExponent b) =
              columnWeight c (fun i => intExponent a (τ.val i) - intExponent r i) := by
            apply le_antisymm (hw.weight_le_of_norm_eq τ.val (hG τ) hnorm)
            exact hbeta ▸ hP.weight _ hn (hbeta ▸ hnorm.symm)
          exact ht ((mem_fixedWitnessPermutations G r c τ).mpr
            ⟨hw.rejection_fixed_of_norm_eq τ.val (hG τ) hnorm,
              hw.columns_fixed_of_norm_weight_eq τ.val (hG τ) hnorm hweight⟩)
        rw [hz, mul_zero]
      · rfl
  simp_rw [hterm]
  rw [← Finset.sum_filter,
    Finset.filter_mem_eq_of_subset (Finset.subset_univ (fixedWitnessPermutations G r c))]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

end HigherSpecht
end
end CanonicalSource46

section CanonicalSource47
/- Source: HigherSpecht/WitnessTransport.lean -/



/-!
# Relabeling and finite-range versions of coefficient witnesses

Only attained column names enter a finite rearrangement.  These wrappers
therefore allow natural-number column indices without imposing an artificial
finite type on all possible row or column names.
-/

noncomputable section

open Equiv Function MvPolynomial

namespace HigherSpecht

variable {ι ξ κ ν : Type*} [Fintype ι] [Fintype ξ]

theorem RearrangementWitness.precompEquiv {u : ι → κ} {v : ι → ν}
    {a r b c : ι → ℤ} (h : RearrangementWitness u v a r b c) (e : ξ ≃ ι) :
    RearrangementWitness (u ∘ e) (v ∘ e) (a ∘ e) (r ∘ e) (b ∘ e) (c ∘ e) := by
  constructor
  · intro i
    exact h.subtraction (e i)
  · intro j i l hil
    have he := h.columnDistinct j
      (a₁ := ⟨e i.val, i.property⟩) (a₂ := ⟨e l.val, l.property⟩) hil
    exact Subtype.ext (e.injective (congrArg Subtype.val he))
  · intro j
    exact (h.columnMonovary j).comp_right
      (fun i : {i : ξ // (u ∘ e) i = j} =>
        (⟨e i.val, i.property⟩ : {i // u i = j}))
  · intro i j
    exact h.refinement (e i) (e j)
  · intro j
    exact (h.tiedMonovary j).comp_right
      (fun i : {i : ξ // (v ∘ e) i = j} =>
        (⟨e i.val, i.property⟩ : {i // v i = j}))

def rangeColor (u : ι → κ) (i : ι) : Set.range u := ⟨u i, ⟨i, rfl⟩⟩

theorem RearrangementWitness.rangeColors {u : ι → κ} {v : ι → ν}
    {a r b c : ι → ℤ} (h : RearrangementWitness u v a r b c) :
    RearrangementWitness (rangeColor u) (rangeColor v) a r b c := by
  constructor
  · exact h.subtraction
  · intro j i l hil
    have he := h.columnDistinct j.val
      (a₁ := ⟨i.val, congrArg Subtype.val i.property⟩)
      (a₂ := ⟨l.val, congrArg Subtype.val l.property⟩) hil
    exact Subtype.ext (congrArg (fun z : {i : ι // u i = j.val} => z.val) he)
  · intro j
    exact (h.columnMonovary j.val).comp_right
      (fun i : {i : ι // rangeColor u i = j} =>
        (⟨i.val, congrArg (fun z : Set.range u => z.val) i.property⟩ : {i // u i = j.val}))
  · intro i j
    constructor
    · intro he
      obtain ⟨hu, hr⟩ := (h.refinement i j).mp (congrArg Subtype.val he)
      exact ⟨Subtype.ext hu, hr⟩
    · rintro ⟨hu, hr⟩
      exact Subtype.ext ((h.refinement i j).mpr ⟨congrArg Subtype.val hu, hr⟩)
  · intro j
    exact (h.tiedMonovary j.val).comp_right
      (fun i : {i : ι // rangeColor v i = j} =>
        (⟨i.val, congrArg (fun z : Set.range v => z.val) i.property⟩ : {i // v i = j.val}))

variable {R : Type*} [CommRing R] [DecidableEq ι]

theorem witnessCoefficient_eq_zero_of_key_finiteRange
    {u : ι → κ} {v : ι → ν} {a r b d : ι →₀ ℕ} {c row : ι → ℤ}
    (hw : RearrangementWitness u v (intExponent a) (intExponent r) (intExponent b) c)
    (G : Subgroup (Equiv.Perm ι)) (hG : ∀ τ : G, ∀ i, u (τ.val i) = u i)
    (P : MvPolynomial ι R) (hP : TriangularSupport c d P)
    (hkey : normWeightKey c (intExponent d) ≤ normWeightKey c (intExponent b))
    (hbd : b ≠ d)
    (hrow : ∀ j, Function.Injective (fun i : {i // c i = j} => row i))
    (hb : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => intExponent b i))
    (hd : ∀ j, Monovary (fun i : {i // c i = j} => row i)
      (fun i : {i // c i = j} => intExponent d i)) :
    witnessCoefficient G a r P = 0 := by
  classical
  letI : Fintype (Set.range u) := (Set.finite_range u).fintype
  letI : Fintype (Set.range v) := (Set.finite_range v).fintype
  exact witnessCoefficient_eq_zero_of_key hw.rangeColors G
    (fun τ i => Subtype.ext (hG τ i)) P hP hkey hbd hrow hb hd

theorem witnessCoefficient_diagonal_finiteRange
    {u : ι → κ} {v : ι → ν} {a r b : ι →₀ ℕ} {c : ι → ℤ}
    (hw : RearrangementWitness u v (intExponent a) (intExponent r) (intExponent b) c)
    (G : Subgroup (Equiv.Perm ι)) (hG : ∀ τ : G, ∀ i, u (τ.val i) = u i)
    (P : MvPolynomial ι R) (hP : TriangularSupport c b P)
    (hAlt : ∀ τ : Equiv.Perm ι, c ∘ τ = c →
      P.coeff (permutedExponent b τ) = coefficientSign τ * P.coeff b) :
    witnessCoefficient G a r P =
      P.coeff b * ((fixedWitnessPermutations G r c).card : R) := by
  classical
  letI : Fintype (Set.range u) := (Set.finite_range u).fintype
  letI : Fintype (Set.range v) := (Set.finite_range v).fintype
  exact witnessCoefficient_diagonal hw.rangeColors G
    (fun τ i => Subtype.ext (hG τ i)) P hP hAlt

/-- The literal permutations preserving every fiber of the given column map. -/
def colorPermutationGroup (c : ι → κ) : Subgroup (Equiv.Perm ι) where
  carrier := {σ | ∀ i, c (σ i) = c i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro σ τ hσ hτ i
    exact (hσ (τ i)).trans (hτ i)
  inv_mem' := by
    intro σ hσ i
    exact (hσ (σ.symm i)).symm.trans (congrArg c (σ.apply_symm_apply i))

@[simp] theorem mem_colorPermutationGroup (c : ι → κ) (σ : Equiv.Perm ι) :
    σ ∈ colorPermutationGroup c ↔ ∀ i, c (σ i) = c i := Iff.rfl

end HigherSpecht
end
end CanonicalSource47

section CanonicalSource48
/- Source: HigherSpecht/YoungPolynomialSupport.lean -/



/-!
# Polynomial hypotheses for the actual higher Specht polynomials

The double sum below is exactly the manuscript's column-after-row operator.
Every monomial has the same squared norm as the cocharge filling.  The row
rearrangement proves the weighted-prefix bound, its equality identifies the
column orbit, and the distinguished coefficient counts the row stabilizer.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Function Equiv TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem permutedExponent_eq_mapDomain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι →₀ ℕ) (σ : Equiv.Perm ι) :
    permutedExponent b σ = b.mapDomain σ.symm := by
  ext i
  rw [permutedExponent_apply]
  have h := Finsupp.mapDomain_apply_of_injective σ.symm.injective b (σ i)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem rename_monomial_permuted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι →₀ ℕ) (σ : Equiv.Perm ι) (a : R) :
    MvPolynomial.rename σ (MvPolynomial.monomial b a) =
      MvPolynomial.monomial (permutedExponent b σ.symm) a := by
  rw [MvPolynomial.rename_monomial, permutedExponent_eq_mapDomain, Equiv.symm_symm]

theorem coefficientSign_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ τ : Equiv.Perm ι) :
    coefficientSign (R := R) (σ * τ) = coefficientSign σ * coefficientSign τ := by
  simp [coefficientSign, Equiv.Perm.sign_mul, Units.val_mul]

theorem rename_columnAlternate {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (τ : G) (P : PolynomialRing n R) :
    MvPolynomial.rename τ.val (columnAlternate G P) =
      coefficientSign (R := R) τ.val • columnAlternate G P := by
  have heq := Equiv.sum_comp (Equiv.mulLeft τ)
    (fun σ : G => coefficientSign (R := R) σ.val • MvPolynomial.rename σ.val P)
  change (∑ σ : G, coefficientSign (R := R) (τ.val * σ.val) •
      MvPolynomial.rename (τ.val * σ.val) P) = columnAlternate G P at heq
  conv_rhs => rw [← heq, Finset.smul_sum]
  simp only [columnAlternate, map_sum, map_smul, MvPolynomial.rename_rename,
    coefficientSign_mul, smul_smul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← mul_assoc, coefficientSign_mul_self, one_mul]
  rfl

theorem youngApply_columnAlternating {μ : YoungDiagram} (T : YoungTableau μ)
    (P : PolynomialRing μ.card R) (τ : colSubgroup T) :
    MvPolynomial.rename τ.val (youngApply T P) = coefficientSign (R := R) τ.val • youngApply T P :=
  rename_columnAlternate (colSubgroup T) τ (rowSymmetrize (rowSubgroup T) P)

theorem coeff_rename_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι R) (σ : Equiv.Perm ι) (b : ι →₀ ℕ) :
    (MvPolynomial.rename σ P).coeff b = P.coeff (permutedExponent b σ) := by
  rw [permutedExponent_eq_mapDomain]
  have h := MvPolynomial.coeff_rename_mapDomain σ σ.injective P (b.mapDomain σ.symm)
  simpa only [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id] using h

theorem youngApply_coeff_columnPermuted {μ : YoungDiagram} (T : YoungTableau μ)
    (P : PolynomialRing μ.card R) (τ : Equiv.Perm (Fin μ.card))
    (hτ : ∀ i, colIndex T (τ i) = colIndex T i) (b : Fin μ.card →₀ ℕ) :
    (youngApply T P).coeff (permutedExponent b τ) =
      coefficientSign τ * (youngApply T P).coeff b := by
  rw [← coeff_rename_perm, youngApply_columnAlternating T P
    (⟨τ, mem_colSubgroup.mpr hτ⟩ : colSubgroup T), MvPolynomial.coeff_smul, smul_eq_mul]

def youngExponent {μ : YoungDiagram} (T : YoungTableau μ) (b : Fin μ.card →₀ ℕ)
    (σ : colSubgroup T) (ρ : rowSubgroup T) : Fin μ.card →₀ ℕ :=
  permutedExponent (permutedExponent b ρ.val.symm) σ.val.symm

theorem youngApply_monomial_eq_sum {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ) :
    youngApply (R := R) T (MvPolynomial.monomial b 1) =
      ∑ σ : colSubgroup T, ∑ ρ : rowSubgroup T,
        MvPolynomial.monomial (youngExponent T b σ ρ) (coefficientSign σ.val) := by
  simp only [youngApply, columnAlternate, rowSymmetrize, map_sum, Finset.smul_sum,
    rename_monomial_permuted, youngExponent, MvPolynomial.smul_monomial, smul_eq_mul, mul_one,
    coefficientSign]

theorem youngApply_coeff_eq_sum {μ : YoungDiagram} (T : YoungTableau μ)
    (b beta : Fin μ.card →₀ ℕ) :
    (youngApply (R := R) T (MvPolynomial.monomial b 1)).coeff beta =
      ∑ σ : colSubgroup T, ∑ ρ : rowSubgroup T,
        if youngExponent T b σ ρ = beta then coefficientSign σ.val else 0 := by
  rw [youngApply_monomial_eq_sum]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem youngApply_coeff_ne_zero {μ : YoungDiagram} (T : YoungTableau μ)
    (b beta : Fin μ.card →₀ ℕ)
    (h : (youngApply (R := R) T (MvPolynomial.monomial b 1)).coeff beta ≠ 0) :
    ∃ (σ : colSubgroup T) (ρ : rowSubgroup T), youngExponent T b σ ρ = beta := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  rw [youngApply_coeff_eq_sum]
  simp only [hn, if_false, Finset.sum_const_zero]

theorem youngExponent_squareNorm {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ) (σ : colSubgroup T) (ρ : rowSubgroup T) :
    squareNorm (intExponent (youngExponent T b σ ρ)) = squareNorm (intExponent b) := by
  simp only [youngExponent, intExponent_permuted, squareNorm_comp_perm]

theorem youngExponent_weight_le {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i))
    (σ : colSubgroup T) (ρ : rowSubgroup T) :
    columnWeight (fun i => colIndex T i) (intExponent (youngExponent T b σ ρ)) ≤
      columnWeight (fun i => colIndex T i) (intExponent b) := by
  apply rowColumn_weight_le (rowIndex T) (fun i => colIndex T i) (intExponent b) hb
    ρ.val.symm σ.val.symm
  · exact mem_rowSubgroup.mp ((rowSubgroup T).inv_mem ρ.property)
  · funext i
    exact congrArg (fun k : ℕ => (k : ℤ))
      (mem_colSubgroup.mp ((colSubgroup T).inv_mem σ.property) i)

theorem youngExponent_weight_eq_imp_columnOrbit {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i))
    (σ : colSubgroup T) (ρ : rowSubgroup T)
    (heq : columnWeight (fun i => colIndex T i) (intExponent (youngExponent T b σ ρ)) =
      columnWeight (fun i => colIndex T i) (intExponent b)) :
    youngExponent T b σ ρ = permutedExponent b σ.val.symm := by
  apply intExponent_injective
  exact rowColumn_weight_eq_imp_columnOrbit (rowIndex T) (fun i => colIndex T i)
    (intExponent b) (colIndex_injective_on_row T) hb ρ.val.symm σ.val.symm
    (mem_rowSubgroup.mp ((rowSubgroup T).inv_mem ρ.property))
    (by
      funext i
      exact congrArg (fun k : ℕ => (k : ℤ))
        (mem_colSubgroup.mp ((colSubgroup T).inv_mem σ.property) i)) heq

/-- These are the actual support properties, derived from the literal Young
operator; there is no assumption about its polynomial support. -/
theorem youngApply_triangularSupport {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i)) :
    TriangularSupport (fun i => colIndex T i) b
      (youngApply (R := R) T (MvPolynomial.monomial b 1)) := by
  constructor
  · intro beta hbeta
    obtain ⟨σ, ρ, rfl⟩ := youngApply_coeff_ne_zero T b beta hbeta
    exact (youngExponent_squareNorm T b σ ρ).le
  · intro beta hbeta hnorm
    obtain ⟨σ, ρ, rfl⟩ := youngApply_coeff_ne_zero T b beta hbeta
    exact youngExponent_weight_le T b hb σ ρ
  · intro beta hbeta hnorm hweight
    obtain ⟨σ, ρ, rfl⟩ := youngApply_coeff_ne_zero T b beta hbeta
    refine ⟨σ.val.symm, ?_, ?_⟩
    · funext i
      exact congrArg (fun k : ℕ => (k : ℤ))
        (mem_colSubgroup.mp ((colSubgroup T).inv_mem σ.property) i)
    · rw [youngExponent_weight_eq_imp_columnOrbit T b hb σ ρ hweight]
      rfl

theorem higherSpecht_triangularSupport {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) :
    TriangularSupport (fun i => colIndex T.toTableau i) (transportedCocharge S T.toTableau)
      (higherSpechtPolynomial (R := R) S T) :=
  youngApply_triangularSupport T.toTableau (transportedCocharge S T.toTableau)
    (transportedCocharge_rowMonovary S T.toTableau)

theorem youngExponent_eq_base_iff {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i))
    (hc : ∀ j, Function.Injective (fun i : {i // colIndex T i = j} => b i))
    (σ : colSubgroup T) (ρ : rowSubgroup T) :
    youngExponent T b σ ρ = b ↔ σ = 1 ∧ permutedExponent b ρ.val.symm = b := by
  constructor
  · intro heq
    have hcol : permutedExponent b σ.val.symm = b :=
      (youngExponent_weight_eq_imp_columnOrbit T b hb σ ρ (by rw [heq])).symm.trans heq
    have hσ : σ = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have hfix : σ.val.symm i = i := by
        apply_fun (fun d : Fin μ.card →₀ ℕ => d i) at hcol
        have hz := hc (colIndex T i)
          (a₁ := ⟨σ.val.symm i, mem_colSubgroup.mp ((colSubgroup T).inv_mem σ.property) i⟩)
          (a₂ := ⟨i, rfl⟩) hcol
        exact congrArg Subtype.val hz
      have h := congrArg σ.val hfix
      simpa only [Equiv.apply_symm_apply, Subgroup.coe_one, Equiv.Perm.one_apply] using h.symm
    refine ⟨hσ, ?_⟩
    simpa only [hσ, youngExponent, Subgroup.coe_one, ← Equiv.Perm.inv_def, inv_one,
      permutedExponent_one] using heq
  · rintro ⟨rfl, hρ⟩
    simpa only [youngExponent, Subgroup.coe_one, ← Equiv.Perm.inv_def, inv_one,
      permutedExponent_one] using hρ

def rowFillingStabilizers {μ : YoungDiagram} (T : YoungTableau μ) (b : Fin μ.card →₀ ℕ) :
    Finset (rowSubgroup T) := Finset.univ.filter fun ρ => permutedExponent b ρ.val.symm = b

theorem youngApply_distinguishedCoefficient {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i))
    (hc : ∀ j, Function.Injective (fun i : {i // colIndex T i = j} => b i)) :
    (youngApply (R := R) T (MvPolynomial.monomial b 1)).coeff b =
      ((rowFillingStabilizers T b).card : R) := by
  rw [youngApply_coeff_eq_sum]
  simp_rw [youngExponent_eq_base_iff T b hb hc]
  rw [Finset.sum_eq_single (1 : colSubgroup T)]
  · simp only [true_and, coefficientSign_one, Subgroup.coe_one]
    rw [← Finset.sum_filter]
    simp [rowFillingStabilizers]
  · intro σ hσ hne
    simp only [hne, false_and, if_false, Finset.sum_const_zero]
  · simp

theorem rowFillingStabilizers_nonempty {μ : YoungDiagram} (T : YoungTableau μ)
    (b : Fin μ.card →₀ ℕ) : (rowFillingStabilizers T b).Nonempty := by
  refine ⟨1, ?_⟩
  simp only [rowFillingStabilizers, Finset.mem_filter, Finset.mem_univ, true_and,
    Subgroup.coe_one, ← Equiv.Perm.inv_def, inv_one, permutedExponent_one]

theorem higherSpecht_distinguishedCoefficient {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) :
    (higherSpechtPolynomial (R := R) S T).coeff (transportedCocharge S T.toTableau) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge S T.toTableau)).card : R) :=
  youngApply_distinguishedCoefficient T.toTableau (transportedCocharge S T.toTableau)
    (transportedCocharge_rowMonovary S T.toTableau)
    (transportedCocharge_columnDistinct S T.toTableau)

end HigherSpecht
end
end CanonicalSource48

section CanonicalSource49
/- Source: HigherSpecht/FactorialTransport.lean -/



/-!
# Ordinary differentiation and divided contraction

Over a characteristic-zero field, the diagonal linear equivalence
`x^[a] ↦ x^a / ∏ a_i!` carries contraction to the actual Mathlib partial
derivatives.  The resulting coefficient identity supplies the factorial factor
in Lemma 3.1 without extending ordinary differentiation to small characteristic.
-/

noncomputable section

open MvPolynomial Finset

namespace HigherSpecht

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]

def exponentFactorial (a : σ →₀ ℕ) : ℕ := ∏ i, (a i).factorial

theorem exponentFactorial_pos (a : σ →₀ ℕ) : 0 < exponentFactorial a :=
  Finset.prod_pos fun i hi => Nat.factorial_pos _

theorem exponentFactorial_ne_zero (a : σ →₀ ℕ) :
    (exponentFactorial a : K) ≠ 0 := by
  exact_mod_cast (exponentFactorial_pos a).ne'

theorem exponentFactorial_add_single (a : σ →₀ ℕ) (i : σ) :
    exponentFactorial (a + Finsupp.single i 1) = (a i + 1) * exponentFactorial a := by
  have hprod : (∏ j : σ, ((a + Finsupp.single i 1 : σ →₀ ℕ) j).factorial) =
      (∏ j : σ, (if j = i then a i + 1 else 1)) * ∏ j : σ, (a j).factorial := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [Nat.factorial_succ]
    · simp [Finsupp.single_apply, hji, Ne.symm hji]
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true, exponentFactorial] using hprod

def factorialNormalize : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (MvPolynomial.basisMonomials σ K).constr K fun a =>
    MvPolynomial.monomial a (exponentFactorial a : K)⁻¹

def factorialDenormalize : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (MvPolynomial.basisMonomials σ K).constr K fun a =>
    MvPolynomial.monomial a (exponentFactorial a : K)

@[simp] theorem factorialNormalize_monomial_one (a : σ →₀ ℕ) :
    factorialNormalize (MvPolynomial.monomial a (1 : K)) =
      MvPolynomial.monomial a (exponentFactorial a : K)⁻¹ :=
  (MvPolynomial.basisMonomials σ K).constr_basis K _ a

@[simp] theorem factorialDenormalize_monomial_one (a : σ →₀ ℕ) :
    factorialDenormalize (MvPolynomial.monomial a (1 : K)) =
      MvPolynomial.monomial a (exponentFactorial a : K) :=
  (MvPolynomial.basisMonomials σ K).constr_basis K _ a

theorem factorialNormalize_monomial (a : σ →₀ ℕ) (c : K) :
    factorialNormalize (MvPolynomial.monomial a c) =
      MvPolynomial.monomial a (c / exponentFactorial a) := by
  have h : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, factorialNormalize_monomial_one]
  rw [MvPolynomial.smul_monomial, smul_eq_mul, div_eq_mul_inv]

theorem factorialDenormalize_monomial (a : σ →₀ ℕ) (c : K) :
    factorialDenormalize (MvPolynomial.monomial a c) =
      MvPolynomial.monomial a (c * exponentFactorial a) := by
  have h : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, factorialDenormalize_monomial_one]
  rw [MvPolynomial.smul_monomial, smul_eq_mul]

@[simp] theorem coeff_factorialNormalize (p : MvPolynomial σ K) (a : σ →₀ ℕ) :
    (factorialNormalize p).coeff a = p.coeff a / exponentFactorial a := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_div]
  | monomial b c =>
    rw [factorialNormalize_monomial]
    by_cases hab : b = a <;> simp [coeff_monomial, hab]

@[simp] theorem coeff_factorialDenormalize (p : MvPolynomial σ K) (a : σ →₀ ℕ) :
    (factorialDenormalize p).coeff a = p.coeff a * exponentFactorial a := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial b c =>
    rw [factorialDenormalize_monomial]
    by_cases hab : b = a <;> simp [coeff_monomial, hab]

def factorialTransport : MvPolynomial σ K ≃ₗ[K] MvPolynomial σ K where
  toLinearMap := factorialNormalize
  invFun := factorialDenormalize
  left_inv p := by
    change factorialDenormalize (factorialNormalize p) = p
    apply MvPolynomial.ext
    intro a
    rw [coeff_factorialDenormalize, coeff_factorialNormalize]
    exact div_mul_cancel₀ _ (exponentFactorial_ne_zero (K := K) a)
  right_inv p := by
    change factorialNormalize (factorialDenormalize p) = p
    apply MvPolynomial.ext
    intro a
    rw [coeff_factorialNormalize, coeff_factorialDenormalize]
    exact mul_div_cancel_right₀ _ (exponentFactorial_ne_zero (K := K) a)

theorem factorialNormalize_contract_X (i : σ) (p : MvPolynomial σ K) :
    factorialNormalize (contractMonomial (Finsupp.single i 1) p) =
      MvPolynomial.pderiv i (factorialNormalize p) := by
  ext a
  rw [coeff_factorialNormalize, coeff_contractMonomial, MvPolynomial.coeff_pderiv,
    coeff_factorialNormalize, exponentFactorial_add_single]
  push_cast
  have ha := exponentFactorial_ne_zero (K := K) a
  have hi : (a i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (a i)
  field_simp

/-- The ordinary polynomial differential operator, obtained by a conjugation
whose values on variables are proved to be the actual partial derivatives. -/
def ordinaryAction : MvPolynomial σ K →ₐ[K] Module.End K (MvPolynomial σ K) :=
  ((factorialTransport (σ := σ) (K := K)).conjAlgEquiv K).toAlgHom.comp dividedAction

theorem ordinaryAction_factorialTransport (f p : MvPolynomial σ K) :
    ordinaryAction f (factorialTransport p) = factorialTransport (dividedAction f p) := by
  simp [ordinaryAction, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

theorem ordinaryAction_X (i : σ) :
    ordinaryAction (MvPolynomial.X i : MvPolynomial σ K) =
      (MvPolynomial.pderiv i).toLinearMap := by
  apply LinearMap.ext
  intro p
  obtain ⟨q, rfl⟩ := (factorialTransport (σ := σ) (K := K)).surjective p
  rw [ordinaryAction_factorialTransport, dividedAction_X]
  exact factorialNormalize_contract_X i q

/-- This checks the mathematical meaning of the action independently of its
construction: it is the unique algebra homomorphism sending each variable to
the corresponding ordinary partial derivative. -/
theorem ordinaryAction_unique
    (A : MvPolynomial σ K →ₐ[K] Module.End K (MvPolynomial σ K))
    (hA : ∀ i, A (MvPolynomial.X i) = (MvPolynomial.pderiv i).toLinearMap) :
    A = ordinaryAction := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [hA, ordinaryAction_X]

theorem factorialNormalize_sum_of_common_factorial {ι : Type*} (s : Finset ι)
    (a : ι → σ →₀ ℕ) (c : ι → K) (N : ℕ)
    (hN : ∀ i ∈ s, exponentFactorial (a i) = N) :
    factorialNormalize (∑ i ∈ s, MvPolynomial.monomial (a i) (c i)) =
      (N : K)⁻¹ • ∑ i ∈ s, MvPolynomial.monomial (a i) (c i) := by
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [factorialNormalize_monomial, hN i hi]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Exact ordinary-apolar / integral-coefficient conversion for any finite
monomial witness whose exponents have a common factorial product. -/
theorem ordinary_coefficient_eq_factorial_mul_contraction {ι : Type*}
    (s : Finset ι) (a : ι → σ →₀ ℕ) (c : ι → K) (N : ℕ) (hNpos : 0 < N)
    (hN : ∀ i ∈ s, exponentFactorial (a i) = N)
    (f : MvPolynomial σ K) (r : σ →₀ ℕ) :
    (ordinaryAction f (∑ i ∈ s, MvPolynomial.monomial (a i) (c i))).coeff r =
      ((N : K) / exponentFactorial r) *
        contractionCoefficient (∑ i ∈ s, MvPolynomial.monomial (a i) (c i)) r f := by
  let w : MvPolynomial σ K := ∑ i ∈ s, MvPolynomial.monomial (a i) (c i)
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hNpos.ne'
  have h := ordinaryAction_factorialTransport f w
  change ordinaryAction f (factorialNormalize w) = factorialNormalize (dividedAction f w) at h
  rw [factorialNormalize_sum_of_common_factorial s a c N hN, map_smul] at h
  have hc := congrArg (fun p : MvPolynomial σ K => p.coeff r) h
  simp only [MvPolynomial.coeff_smul, coeff_factorialNormalize, smul_eq_mul] at hc
  change (ordinaryAction f w).coeff r =
    ((N : K) / exponentFactorial r) * (dividedAction f w).coeff r
  calc
    (ordinaryAction f w).coeff r =
        (N : K) * ((N : K)⁻¹ * (ordinaryAction f w).coeff r) := by simp [hN0]
    _ = (N : K) * ((dividedAction f w).coeff r / exponentFactorial r) := by rw [hc]
    _ = _ := by ring

end HigherSpecht
end
end CanonicalSource49

section CanonicalSource50
/- Source: HigherSpecht/HigherSpechtPairing.lean -/



/-!
# The actual higher Specht triangular pairing

The witness, its exponents and its rejection vector are extracted from the
terminating column-reading insertion.  All polynomial support and diagonal
conditions are derived for the literal unnormalized higher Specht polynomial.
The final statements below are the coefficient and ordinary-apolar versions
of Theorem 3.2; no catabolism-shape identification is used in this theorem.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Function Equiv TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {μ : YoungDiagram}

def scanLabelEquiv (T : YoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  (columnScanEquiv μ).trans T

@[simp] theorem columnScanEquiv_scanLabelEquiv_symm (T : YoungTableau μ)
    (i : Fin μ.card) : columnScanEquiv μ ((scanLabelEquiv T).symm i) = T.symm i := by
  change columnScanEquiv μ ((columnScanEquiv μ).symm (T.symm i)) = _
  exact Equiv.apply_symm_apply _ _

def insertionFilling (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    ↥(columnInsertion S).state.shape.cells ≃ Fin μ.card :=
  (columnInsertion S).filling.trans (scanLabelEquiv T)

def insertionRow (S : StandardYoungTableau μ) (T : YoungTableau μ) (i : Fin μ.card) : ℕ :=
  (columnInsertion S).row ((scanLabelEquiv T).symm i)

def insertionColumn (S : StandardYoungTableau μ) (T : YoungTableau μ) (i : Fin μ.card) : ℕ :=
  (columnInsertion S).column ((scanLabelEquiv T).symm i)

def insertionRejections (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (i : Fin μ.card) : ℕ :=
  (columnInsertion S).rejection ((scanLabelEquiv T).symm i)

def insertionAlpha (S : StandardYoungTableau μ) (T : YoungTableau μ) : Fin μ.card →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (insertionRow S T)

def insertionRejectionExponent (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Fin μ.card →₀ ℕ := Finsupp.equivFunOnFinite.symm (insertionRejections S T)

def insertionColumnGroup (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Subgroup (Equiv.Perm (Fin μ.card)) := colorPermutationGroup (insertionColumn S T)

theorem insertion_row_eq_input_add_rejections (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (i : Fin μ.card) :
    insertionRow S T i = transportedCocharge S T i + insertionRejections S T i := by
  simpa only [insertionRow, insertionRejections, columnScanCocharge,
    columnScanEquiv_scanLabelEquiv_symm, transportedCocharge,
    Finsupp.equivFunOnFinite_symm_apply_apply] using
    (columnInsertion S).row_eq_input_add_rejection ((scanLabelEquiv T).symm i)

theorem insertion_rearrangementWitness (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    RearrangementWitness (insertionColumn S T)
      (fun i => (insertionColumn S T i, insertionRejections S T i))
      (intExponent (insertionAlpha S T))
      (intExponent (insertionRejectionExponent S T))
      (intExponent (transportedCocharge S T)) (fun i => (colIndex T i : ℤ)) := by
  have h := (columnInsertion_rearrangementWitness S).precompEquiv (scanLabelEquiv T).symm
  have hcolumn : insertionColumn S T =
      fun i => (columnInsertion S).column ((scanLabelEquiv T).symm i) := rfl
  have halpha : intExponent (insertionAlpha S T) =
      fun i => ((columnInsertion S).row ((scanLabelEquiv T).symm i) : ℤ) := by
    funext i
    simp only [intExponent, insertionAlpha, Finsupp.equivFunOnFinite_symm_apply_apply,
      insertionRow]
  have hrejection : intExponent (insertionRejectionExponent S T) =
      fun i => ((columnInsertion S).rejection ((scanLabelEquiv T).symm i) : ℤ) := by
    funext i
    simp only [intExponent, insertionRejectionExponent,
      Finsupp.equivFunOnFinite_symm_apply_apply, insertionRejections]
  have hcocharge : intExponent (transportedCocharge S T) =
      fun i => (cochargeFilling S (T.symm i) : ℤ) := by
    funext i
    simp only [intExponent, transportedCocharge, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [hcolumn, halpha, hrejection, hcocharge]
  simpa only [Function.comp_def, insertionColumn, insertionRejections,
    columnScanCocharge, columnScanEquiv_scanLabelEquiv_symm, colIndex_def] using h

def higherSpechtWitness {R : Type*} [CommRing R]
    (S : StandardYoungTableau μ) (T : YoungTableau μ) : PolynomialRing μ.card R :=
  coefficientWitness (insertionColumnGroup S T) (insertionAlpha S T)

def higherSpechtCoefficientFunctional {R : Type*} [CommRing R]
    (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Module.Dual R (PolynomialRing μ.card R) :=
  witnessCoefficient (insertionColumnGroup S T) (insertionAlpha S T)
    (insertionRejectionExponent S T)

def higherSpechtPairingKey (S : StandardYoungTableau μ) (T : YoungTableau μ) : ℤ ×ₗ ℤ :=
  normWeightKey (fun i => colIndex T i) (intExponent (transportedCocharge S T))

def insertionFixedPermutations (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Finset (insertionColumnGroup S T) :=
  fixedWitnessPermutations (insertionColumnGroup S T) (insertionRejectionExponent S T)
    (fun i => colIndex T i)

theorem rowIndex_injective_on_intColumn (T : YoungTableau μ) (j : ℤ) :
    Function.Injective (fun i : {i // (colIndex T i : ℤ) = j} => (rowIndex T i : ℤ)) := by
  intro i l hil
  change (rowIndex T i : ℤ) = (rowIndex T l : ℤ) at hil
  apply Subtype.ext
  apply rowIndex_colIndex_injective T
  exact Prod.ext (Int.ofNat_inj.mp hil)
    (Int.ofNat_inj.mp (i.property.trans l.property.symm))

theorem transportedCocharge_intColumnMonovary (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (j : ℤ) :
    Monovary (fun i : {i // (colIndex T i : ℤ) = j} => (rowIndex T i : ℤ))
      (fun i : {i // (colIndex T i : ℤ) = j} => intExponent (transportedCocharge S T) i) := by
  apply Monovary.symm
  intro i l hil
  change (rowIndex T i : ℤ) < (rowIndex T l : ℤ) at hil
  have hrow : rowIndex T i < rowIndex T l := Int.ofNat_lt.mp hil
  have hcol : colIndex T i = colIndex T l :=
    Int.ofNat_inj.mp (i.property.trans l.property.symm)
  have hc : (T.symm i).val.2 = (T.symm l).val.2 := by
    simpa only [← colIndex_def] using hcol
  have hr : (T.symm i).val.1 < (T.symm l).val.1 := by
    simpa only [← rowIndex_def] using hrow
  change (cochargeFilling S (T.symm i) : ℤ) ≤ (cochargeFilling S (T.symm l) : ℤ)
  exact Int.ofNat_le.mpr (cochargeFilling_col_strict S hc hr).le

theorem transportedCocharge_injective (T : YoungTableau μ) :
    Function.Injective (fun S : StandardYoungTableau μ => transportedCocharge S T) := by
  intro S S' heq
  apply cochargeFilling_injective μ
  funext c
  have h := congrArg (fun b : Fin μ.card →₀ ℕ => b (T c)) heq
  simpa only [transportedCocharge, Finsupp.equivFunOnFinite_symm_apply_apply,
    Equiv.symm_apply_apply] using h

/-- The exact vanishing below the norm/column-weight ordering, including
distinct tableaux with equal keys. -/
theorem higherSpecht_coefficient_pairing_offDiagonal {R : Type*} [CommRing R]
    (S S' T : StandardYoungTableau μ) (hne : S ≠ S')
    (hkey : higherSpechtPairingKey S' T.toTableau ≤ higherSpechtPairingKey S T.toTableau) :
    higherSpechtCoefficientFunctional (R := R) S T.toTableau
      (higherSpechtPolynomial S' T) = 0 := by
  apply witnessCoefficient_eq_zero_of_key_finiteRange
    (row := fun i => (rowIndex T.toTableau i : ℤ))
    (insertion_rearrangementWitness S T.toTableau)
    (insertionColumnGroup S T.toTableau)
    (fun τ i => τ.property i) (higherSpechtPolynomial S' T)
    (higherSpecht_triangularSupport S' T) hkey
    (fun h => hne (transportedCocharge_injective T.toTableau h))
    (rowIndex_injective_on_intColumn T.toTableau)
    (transportedCocharge_intColumnMonovary S T.toTableau)
    (transportedCocharge_intColumnMonovary S' T.toTableau)

/-- The integral coefficient diagonal is exactly the two finite stabilizer
cardinalities, rather than merely an unspecified nonzero constant. -/
theorem higherSpecht_coefficient_pairing_diagonal {R : Type*} [CommRing R]
    (S T : StandardYoungTableau μ) :
    higherSpechtCoefficientFunctional (R := R) S T.toTableau
      (higherSpechtPolynomial S T) =
        ((rowFillingStabilizers T.toTableau (transportedCocharge S T.toTableau)).card : R) *
          ((insertionFixedPermutations S T.toTableau).card : R) := by
  change witnessCoefficient _ _ _ _ = _
  rw [witnessCoefficient_diagonal_finiteRange
    (insertion_rearrangementWitness S T.toTableau)
    (insertionColumnGroup S T.toTableau) (fun τ i => τ.property i)
    (higherSpechtPolynomial (R := R) S T) (higherSpecht_triangularSupport S T)
    (fun τ hτ => youngApply_coeff_columnPermuted T.toTableau _ τ
      (fun i => Int.ofNat_inj.mp (congrFun hτ i)) _)]
  rw [higherSpecht_distinguishedCoefficient]
  rfl

theorem higherSpecht_coefficient_pairing_diagonal_ne_zero
    {K : Type*} [Field K] [CharZero K] (S T : StandardYoungTableau μ) :
    higherSpechtCoefficientFunctional (R := K) S T.toTableau
      (higherSpechtPolynomial S T) ≠ 0 := by
  rw [higherSpecht_coefficient_pairing_diagonal]
  apply mul_ne_zero
  · exact_mod_cast (Finset.card_pos.mpr (rowFillingStabilizers_nonempty
      T.toTableau (transportedCocharge S T.toTableau))).ne'
  · exact_mod_cast (Finset.card_pos.mpr (fixedWitnessPermutations_nonempty
      (insertionColumnGroup S T.toTableau) (insertionRejectionExponent S T.toTableau)
      (fun i => (colIndex T.toTableau i : ℤ)))).ne'

theorem exponentFactorial_permuted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι →₀ ℕ) (σ : Equiv.Perm ι) :
    exponentFactorial (permutedExponent a σ) = exponentFactorial a :=
  Equiv.prod_comp σ (fun i => (a i).factorial)

theorem ordinaryAction_coefficientWitness {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (G : Subgroup (Equiv.Perm ι))
    (a r : ι →₀ ℕ) (P : MvPolynomial ι K) :
    (ordinaryAction P (coefficientWitness G a)).coeff r =
      ((exponentFactorial a : K) / exponentFactorial r) * witnessCoefficient G a r P := by
  exact ordinary_coefficient_eq_factorial_mul_contraction Finset.univ
    (fun τ : G => permutedExponent a τ.val) (fun τ => coefficientSign τ.val)
    (exponentFactorial a) (exponentFactorial_pos a)
    (fun τ hτ => exponentFactorial_permuted a τ.val) P r

def higherSpechtApolarFunctional {K : Type*} [Field K] [CharZero K]
    (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Module.Dual K (PolynomialRing μ.card K) :=
  ((exponentFactorial (insertionAlpha S T) : K) /
    exponentFactorial (insertionRejectionExponent S T)) •
      higherSpechtCoefficientFunctional S T

/-- Independent correspondence check: this functional is exactly the
specified coefficient of the actual ordinary differential operator. -/
theorem higherSpechtApolarFunctional_apply {K : Type*} [Field K] [CharZero K]
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (P : PolynomialRing μ.card K) :
    higherSpechtApolarFunctional S T P =
      (ordinaryAction P (higherSpechtWitness S T)).coeff (insertionRejectionExponent S T) :=
  (ordinaryAction_coefficientWitness _ _ _ _).symm

theorem theorem_3_2_offDiagonal {K : Type*} [Field K] [CharZero K]
    (S S' T : StandardYoungTableau μ) (hne : S ≠ S')
    (hkey : higherSpechtPairingKey S' T.toTableau ≤ higherSpechtPairingKey S T.toTableau) :
    higherSpechtApolarFunctional (K := K) S T.toTableau
      (higherSpechtPolynomial S' T) = 0 := by
  change (_ : K) * higherSpechtCoefficientFunctional (R := K) S T.toTableau _ = 0
  rw [higherSpecht_coefficient_pairing_offDiagonal S S' T hne hkey, mul_zero]

theorem theorem_3_2_diagonal {K : Type*} [Field K] [CharZero K]
    (S T : StandardYoungTableau μ) :
    higherSpechtApolarFunctional (K := K) S T.toTableau (higherSpechtPolynomial S T) =
      ((rowFillingStabilizers T.toTableau (transportedCocharge S T.toTableau)).card : K) *
      ((insertionFixedPermutations S T.toTableau).card : K) *
      ((exponentFactorial (insertionAlpha S T.toTableau) : K) /
        exponentFactorial (insertionRejectionExponent S T.toTableau)) := by
  change (_ : K) * higherSpechtCoefficientFunctional (R := K) S T.toTableau _ = _
  rw [higherSpecht_coefficient_pairing_diagonal]
  ring

theorem theorem_3_2_diagonal_pos (S T : StandardYoungTableau μ) :
    0 < higherSpechtApolarFunctional (K := ℚ) S T.toTableau (higherSpechtPolynomial S T) := by
  rw [theorem_3_2_diagonal]
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast Finset.card_pos.mpr
        (rowFillingStabilizers_nonempty T.toTableau (transportedCocharge S T.toTableau))
    · exact_mod_cast Finset.card_pos.mpr
        (fixedWitnessPermutations_nonempty (insertionColumnGroup S T.toTableau)
          (insertionRejectionExponent S T.toTableau) (fun i => (colIndex T.toTableau i : ℤ)))
  · exact div_pos (by exact_mod_cast exponentFactorial_pos (insertionAlpha S T.toTableau))
      (by exact_mod_cast exponentFactorial_pos (insertionRejectionExponent S T.toTableau))

theorem higherSpecht_fixedTableau_linearIndependent {K : Type*} [Field K] [CharZero K]
    (T : StandardYoungTableau μ) :
    LinearIndependent K (fun S : StandardYoungTableau μ => higherSpechtPolynomial (R := K) S T) := by
  apply linearIndependent_of_pairing_key (fun S => higherSpechtPairingKey S T.toTableau)
    (fun S => higherSpechtCoefficientFunctional S T.toTableau)
  · intro S S' hne hkey
    exact higherSpecht_coefficient_pairing_offDiagonal S S' T hne hkey
  · intro S
    exact higherSpecht_coefficient_pairing_diagonal_ne_zero S T

end HigherSpecht
end
end CanonicalSource50

section CanonicalSource51
/- Source: HigherSpecht/PermutationAction.lean -/



/-!
# The actual symmetric-group action on the defining quotients

Variable permutation preserves every defining elementary or power generator.
The quotient actions below are consequently genuine representations.  The same
proof works for sums and intersections, and coefficient extension carries the
literal integral ideals to the same ideals over the target ring.
-/

noncomputable section

open MvPolynomial Finset

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem rename_elementaryOn (e : Equiv.Perm (Fin n)) (Y : Finset (Fin n)) (d : ℕ) :
    MvPolynomial.rename e (elementaryOn (R := R) Y d) =
      elementaryOn (Y.map e.toEmbedding) d := by
  classical
  simp only [elementaryOn, map_sum, map_prod, rename_X,
    Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.prod_map,
    Equiv.coe_toEmbedding]

def PermutationStable (I : Ideal (PolynomialRing n R)) : Prop :=
  ∀ (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R),
    p ∈ I → MvPolynomial.rename e p ∈ I

theorem permutationStable_untruncatedIdeal (μ : YoungDiagram) :
    PermutationStable (untruncatedIdeal R n μ) := by
  intro e p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨Y, d, hd, hcard, ht, rfl⟩ := hp
    rw [rename_elementaryOn]
    apply elementaryOn_mem_untruncatedIdeal _ hd
    · simpa only [Finset.card_map] using hcard
    · simpa only [Finset.card_map] using ht
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using Ideal.add_mem _ ihp ihq
  | smul p q hq ihq => simpa only [smul_eq_mul, map_mul] using Ideal.mul_mem_left _ _ ihq

theorem permutationStable_powerIdeal (s : ℕ) : PermutationStable (powerIdeal R n s) := by
  intro e p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    simp only [map_pow, rename_X]
    exact Ideal.subset_span ⟨e i, rfl⟩
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using Ideal.add_mem _ ihp ihq
  | smul p q hq ihq => simpa only [smul_eq_mul, map_mul] using Ideal.mul_mem_left _ _ ihq

theorem PermutationStable.sup {I J : Ideal (PolynomialRing n R)}
    (hI : PermutationStable I) (hJ : PermutationStable J) : PermutationStable (I ⊔ J) := by
  intro e p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact Ideal.add_mem _ (Submodule.mem_sup_left (hI e a ha))
    (Submodule.mem_sup_right (hJ e b hb))

theorem PermutationStable.inf {I J : Ideal (PolynomialRing n R)}
    (hI : PermutationStable I) (hJ : PermutationStable J) : PermutationStable (I ⊓ J) := by
  intro e p hp
  exact ⟨hI e p hp.1, hJ e p hp.2⟩

theorem permutationStable_griffinIdeal (μ : YoungDiagram) (s : ℕ) :
    PermutationStable (griffinIdeal R n μ s) :=
  (permutationStable_untruncatedIdeal μ).sup (permutationStable_powerIdeal s)

theorem PermutationStable.rename_mem_iff {I : Ideal (PolynomialRing n R)}
    (hI : PermutationStable I) (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R) :
    MvPolynomial.rename e p ∈ I ↔ p ∈ I := by
  constructor
  · intro hp
    have h := hI e.symm _ hp
    simpa only [rename_rename, Equiv.symm_comp_self, rename_id_apply] using h
  · exact hI e p

def polynomialRepresentation (R : Type*) [CommRing R] (n : ℕ) :
    Representation R (Equiv.Perm (Fin n)) (PolynomialRing n R) where
  toFun e := (MvPolynomial.rename e).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    exact MvPolynomial.rename_id_apply p
  map_mul' e f := by
    apply LinearMap.ext
    intro p
    exact (MvPolynomial.rename_rename f e p).symm

@[simp] theorem polynomialRepresentation_apply (e : Equiv.Perm (Fin n))
    (p : PolynomialRing n R) : polynomialRepresentation R n e p = MvPolynomial.rename e p := rfl

def idealSubrepresentation (I : Ideal (PolynomialRing n R)) (hI : PermutationStable I) :
    Subrepresentation (polynomialRepresentation R n) where
  toSubmodule := I.restrictScalars R
  apply_mem_toSubmodule e p hp := hI e p hp

def quotientRepresentation (I : Ideal (PolynomialRing n R)) (hI : PermutationStable I) :
    Representation R (Equiv.Perm (Fin n)) (PolynomialRing n R ⧸ I) :=
  (idealSubrepresentation I hI).quotient

@[simp] theorem quotientRepresentation_mk (I : Ideal (PolynomialRing n R))
    (hI : PermutationStable I) (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R) :
    quotientRepresentation I hI e (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I (MvPolynomial.rename e p) := rfl

def springerRepresentation (R : Type*) [CommRing R] (μ : YoungDiagram) :
    Representation R (Equiv.Perm (Fin μ.card)) (SpringerRing R μ) :=
  quotientRepresentation (springerIdeal R μ) (permutationStable_untruncatedIdeal μ)

def griffinRepresentation (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Representation R (Equiv.Perm (Fin n)) (GriffinRing R n μ s) :=
  quotientRepresentation (griffinIdeal R n μ s) (permutationStable_griffinIdeal μ s)

def untruncatedRepresentation (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Representation R (Equiv.Perm (Fin n)) (UntruncatedRing R n μ) :=
  quotientRepresentation (untruncatedIdeal R n μ) (permutationStable_untruncatedIdeal μ)

/-- Coefficient extension preserves the exact elementary generating set. -/
theorem map_untruncatedIdeal (f : R →+* S) (n : ℕ) (μ : YoungDiagram) :
    Ideal.map (MvPolynomial.map f) (untruncatedIdeal R n μ) = untruncatedIdeal S n μ := by
  rw [untruncatedIdeal, untruncatedIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨Y, d, hd, hcard, ht, rfl⟩, rfl⟩
    exact ⟨Y, d, hd, hcard, ht, map_elementaryOn f Y d⟩
  · rintro ⟨Y, d, hd, hcard, ht, rfl⟩
    exact ⟨elementaryOn (R := R) Y d, ⟨Y, d, hd, hcard, ht, rfl⟩,
      map_elementaryOn f Y d⟩

theorem map_powerIdeal (f : R →+* S) (n s : ℕ) :
    Ideal.map (MvPolynomial.map f) (powerIdeal R n s) = powerIdeal S n s := by
  rw [powerIdeal, powerIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(X i : PolynomialRing n R) ^ s, ⟨i, rfl⟩, by simp⟩

theorem map_griffinIdeal (f : R →+* S) (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Ideal.map (MvPolynomial.map f) (griffinIdeal R n μ s) = griffinIdeal S n μ s := by
  rw [griffinIdeal, griffinIdeal, Ideal.map_sup, map_untruncatedIdeal, map_powerIdeal]

end HigherSpecht
end
end CanonicalSource51

section CanonicalSource52
/- Source: HigherSpecht/TabloidPolynomialMap.lean -/



/-!
# The literal higher Specht family as an equivariant image

A tabloid is sent to the sum of the cocharge monomials of its row-equivalent
tableaux.  Consequently a polytabloid is sent to the manuscript's exact
column-after-row polynomial, with no factorial normalization.  Its nonzero
distinguished coefficient proves that the restriction to the ordinary Specht
module is injective.  This identifies a complete fixed-S family, rather than
only one polynomial in that family.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Equiv Function TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {mu : YoungDiagram}

def tableauRelabelEquiv (sigma : Equiv.Perm (Fin mu.card)) :
    YoungTableau mu ≃ YoungTableau mu where
  toFun := relabel sigma
  invFun := relabel sigma⁻¹
  left_inv T := by simp only [relabel_relabel, inv_mul_cancel, relabel_one]
  right_inv T := by simp only [relabel_relabel, mul_inv_cancel, relabel_one]

theorem relabel_left_injective (T : YoungTableau mu) :
    Function.Injective (fun sigma : Equiv.Perm (Fin mu.card) => relabel sigma T) := by
  intro sigma tau h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun U : YoungTableau mu => U (T.symm i)) h
  simpa only [relabel_apply, Equiv.apply_symm_apply] using hi

def tableauRowOrbitEquiv (T : YoungTableau mu) :
    rowSubgroup T ≃ {U : YoungTableau mu // tabloid U = tabloid T} :=
  Equiv.ofBijective
    (fun sigma => ⟨relabel sigma.val T, (tabloid_relabel _ _).trans
      (smul_tabloid_eq_self_iff.mpr sigma.property)⟩)
    ⟨by
      intro sigma tau h
      exact Subtype.ext (relabel_left_injective T (congrArg Subtype.val h)),
    by
      intro U
      let sigma := relabelPerm T U.val
      have hs : sigma ∈ rowSubgroup T := by
        apply smul_tabloid_eq_self_iff.mp
        rw [← tabloid_relabel, relabel_relabelPerm]
        exact U.property
      exact ⟨⟨sigma, hs⟩, Subtype.ext (relabel_relabelPerm T U.val)⟩⟩

def tableauCochargeMonomial (S : StandardYoungTableau mu) (T : YoungTableau mu) :
    PolynomialRing mu.card ℚ := MvPolynomial.monomial (transportedCocharge S T) 1

theorem rename_tableauCochargeMonomial (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (sigma : Equiv.Perm (Fin mu.card)) :
    MvPolynomial.rename sigma (tableauCochargeMonomial S T) =
      tableauCochargeMonomial S (relabel sigma T) := by
  rw [tableauCochargeMonomial, rename_monomial_permuted, tableauCochargeMonomial]
  apply congrArg (fun a : Fin mu.card →₀ ℕ => MvPolynomial.monomial a (1 : ℚ))
  apply Finsupp.ext
  intro i
  simp only [permutedExponent_apply, transportedCocharge,
    Finsupp.equivFunOnFinite_symm_apply_apply, relabel_symm_apply, Equiv.Perm.inv_def]

abbrev TableauTabloid (mu : YoungDiagram) :=
  Equiv.Perm (Fin mu.card) ⧸ youngSubgroup (shapePartition mu)

def tabloidPolynomial (S : StandardYoungTableau mu) (q : TableauTabloid mu) :
    PolynomialRing mu.card ℚ :=
  ∑ T : YoungTableau mu, if tabloid T = q then tableauCochargeMonomial S T else 0

theorem tabloidPolynomial_tabloid (S : StandardYoungTableau mu) (T : YoungTableau mu) :
    tabloidPolynomial S (tabloid T) =
      rowSymmetrize (rowSubgroup T) (tableauCochargeMonomial S T) := by
  rw [tabloidPolynomial, ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun U : YoungTableau mu => tabloid U = tabloid T)
    _ (by intro U; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (tableauCochargeMonomial S)]
  rw [← Equiv.sum_comp (tableauRowOrbitEquiv T)
    (fun U : {U : YoungTableau mu // tabloid U = tabloid T} => tableauCochargeMonomial S U.val)]
  unfold rowSymmetrize
  apply Finset.sum_congr rfl
  intro sigma hsigma
  exact (rename_tableauCochargeMonomial S T sigma.val).symm

theorem tabloidPolynomial_smul (S : StandardYoungTableau mu)
    (q : TableauTabloid mu) (sigma : Equiv.Perm (Fin mu.card)) :
    tabloidPolynomial S (sigma • q) = MvPolynomial.rename sigma (tabloidPolynomial S q) := by
  rw [tabloidPolynomial, tabloidPolynomial, map_sum]
  rw [← Equiv.sum_comp (tableauRelabelEquiv sigma)
    (fun T : YoungTableau mu => if tabloid T = sigma • q then tableauCochargeMonomial S T else 0)]
  apply Finset.sum_congr rfl
  intro T hT
  change (if tabloid (relabel sigma T) = sigma • q then
    tableauCochargeMonomial S (relabel sigma T) else 0) = _
  rw [tabloid_relabel]
  by_cases hq : tabloid T = q
  · simp only [hq, if_true, rename_tableauCochargeMonomial]
  · have hq' : sigma • tabloid T ≠ sigma • q := by
      intro h
      apply hq
      exact (MulAction.injective sigma) h
    simp only [if_neg hq, if_neg hq', map_zero]

def tabloidPolynomialLinear (S : StandardYoungTableau mu) :
    (permutationModule (shapePartition mu)).V →ₗ[ℚ] PolynomialRing mu.card ℚ :=
  Finsupp.linearCombination ℚ (tabloidPolynomial S) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem tabloidPolynomialLinear_single (S : StandardYoungTableau mu)
    (q : TableauTabloid mu) (a : ℚ) :
    tabloidPolynomialLinear S (MonoidAlgebra.single q a) = a • tabloidPolynomial S q := by
  change Finsupp.linearCombination ℚ (tabloidPolynomial S) (Finsupp.single q a) = _
  exact Finsupp.linearCombination_single ℚ a q

/-- The reduced-carrier form lets `simp` match the representation's underlying
monoid algebra, as in `coe_standardPolytabloidBasis`. -/
@[simp] theorem tabloidPolynomialLinear_single_dsimp (S : StandardYoungTableau mu)
    (q : TableauTabloid mu) (a : ℚ) :
    (dsimp% only (tabloidPolynomialLinear S (MonoidAlgebra.single q a))) =
      a • tabloidPolynomial S q :=
  tabloidPolynomialLinear_single S q a

def tabloidPolynomialIntertwiner (S : StandardYoungTableau mu) :
    (permutationModule (shapePartition mu)).ρ.IntertwiningMap
      (polynomialRepresentation ℚ mu.card) where
  toLinearMap := tabloidPolynomialLinear S
  isIntertwining' sigma := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single, tabloidPolynomialLinear_single_dsimp,
      polynomialRepresentation_apply, map_smul, tabloidPolynomial_smul]

theorem tabloidPolynomialLinear_polytabloid (S : StandardYoungTableau mu)
    (T : YoungTableau mu) :
    tabloidPolynomialLinear S (polytabloid T) =
      youngApply T (tableauCochargeMonomial S T) := by
  rw [polytabloid_eq_sum, map_sum]
  simp only [map_smul, tabloidPolynomialLinear_single_dsimp, one_smul, tabloidPolynomial_smul,
    tabloidPolynomial_tabloid]
  rfl

def higherSpechtIntertwiner (S : StandardYoungTableau mu) :
    (spechtSubrepresentation mu).toRepresentation.IntertwiningMap
      (polynomialRepresentation ℚ mu.card) :=
  (tabloidPolynomialIntertwiner S).comp (spechtSubrepresentation mu).subtype

theorem higherSpechtIntertwiner_standardBasis (S T : StandardYoungTableau mu) :
    higherSpechtIntertwiner S (standardPolytabloidBasis mu T) =
      higherSpechtPolynomial S T := by
  simp only [higherSpechtIntertwiner, Representation.IntertwiningMap.comp_apply,
    Subrepresentation.coe_subtype, tabloidPolynomialIntertwiner,
    Representation.IntertwiningMap.coe_mk]
  change tabloidPolynomialLinear S ((standardPolytabloidBasis mu T :
    (spechtSubrepresentation mu).toSubmodule) : (permutationModule (shapePartition mu)).V) = _
  rw [coe_standardPolytabloidBasis, tabloidPolynomialLinear_polytabloid]
  rfl

theorem higherSpechtPolynomial_ne_zero (S T : StandardYoungTableau mu) :
    higherSpechtPolynomial (R := ℚ) S T ≠ 0 := by
  intro hz
  have hc := higherSpecht_distinguishedCoefficient (R := ℚ) S T
  simp only [hz, MvPolynomial.coeff_zero, Finsupp.zero_apply] at hc
  have hp : (0 : ℚ) < (rowFillingStabilizers T.toTableau
      (transportedCocharge S T.toTableau)).card := by
    exact_mod_cast Finset.card_pos.mpr (rowFillingStabilizers_nonempty
      T.toTableau (transportedCocharge S T.toTableau))
  linarith

theorem higherSpechtIntertwiner_ne_zero (S : StandardYoungTableau mu) :
    higherSpechtIntertwiner S ≠ 0 := by
  intro hz
  have h := DFunLike.congr_fun hz (standardPolytabloidBasis mu S)
  rw [higherSpechtIntertwiner_standardBasis] at h
  exact higherSpechtPolynomial_ne_zero S S h

theorem higherSpechtIntertwiner_injective (S : StandardYoungTableau mu) :
    Function.Injective (higherSpechtIntertwiner S) := by
  letI : (spechtSubrepresentation mu).toRepresentation.IsIrreducible :=
    isIrreducible_spechtSubrepresentation mu
  exact (Representation.IsIrreducible.injective_or_eq_zero (higherSpechtIntertwiner S)).resolve_right
    (higherSpechtIntertwiner_ne_zero S)

/-- The entire fixed-S polynomial family is independent, through its literal
ordinary Specht-module map. This statement makes no quotient eligibility
claim and does not substitute for the all-S quotient-basis theorem. -/
theorem higherSpecht_fixedLeft_linearIndependent (S : StandardYoungTableau mu) :
    LinearIndependent ℚ (fun T : StandardYoungTableau mu => higherSpechtPolynomial (R := ℚ) S T) := by
  have h := (standardPolytabloidBasis mu).linearIndependent.map'
    (higherSpechtIntertwiner S).toLinearMap
    (LinearMap.ker_eq_bot.mpr (higherSpechtIntertwiner_injective S))
  have hfamily :
      (fun T : StandardYoungTableau mu =>
        (higherSpechtIntertwiner S).toLinearMap (standardPolytabloidBasis mu T)) =
      (fun T : StandardYoungTableau mu => higherSpechtPolynomial (R := ℚ) S T) := by
    funext T
    rw [Representation.IntertwiningMap.toLinearMap_apply]
    exact higherSpechtIntertwiner_standardBasis S T
  rw [← hfamily]
  exact h

end HigherSpecht
end
end CanonicalSource52

section CanonicalSource53
/- Source: HigherSpecht/CanonicalSpechtCopies.lean -/



/-!
# The actual partition-indexed Young ideal and ordinary Specht module

The group-algebra transport is the exact `Fin` relabeling used by the library's
partition-indexed representation.  Its inverse carries the principal ideal to
the tableau-indexed principal ideal.  Composing with the verified comparison
map identifies its complete standard basis, without changing the order of the
paper's row and column operators.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau Module

namespace HigherSpecht

 theorem youngSymmetrizerOver_rat {mu : YoungDiagram} (T : YoungTableau mu) :
    youngSymmetrizerOver ℚ T = youngSymmetrizer T := by
  ext g
  simp only [youngSymmetrizerOver_coeff, Algebra.algebraMap_self, RingHom.id_apply]

def partitionLabelAlgebraEquiv {n : ℕ} (part : n.Partition) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin (YoungDiagram.ofPartition part).card)) ≃ₐ[ℚ]
      MonoidAlgebra ℚ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.domCongr ℚ ℚ (finCongr (YoungDiagram.card_ofPartition part)).permCongrHom

 theorem partitionLabelAlgebraEquiv_generator {n : ℕ} (part : n.Partition) :
    partitionLabelAlgebraEquiv part
      (youngSymmetrizer (StandardYoungTableau.rowSuperstandard
        (YoungDiagram.ofPartition part)).toTableau) = part.youngSymmetrizer ℚ := by
  rw [Nat.Partition.youngSymmetrizer_def, youngSymmetrizerOver_rat]
  rfl

def canonicalYoungIdealLinearEquiv {n : ℕ} (part : n.Partition) :
    YoungIdeal (K := ℚ) part ≃ₗ[ℚ]
      spechtIdeal (StandardYoungTableau.rowSuperstandard
        (YoungDiagram.ofPartition part)).toTableau where
  toFun x := ⟨(partitionLabelAlgebraEquiv part).symm x, by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    apply (mem_spechtIdeal_iff _ _).mpr
    refine ⟨(partitionLabelAlgebraEquiv part).symm a, ?_⟩
    rw [← ha, map_mul, ← partitionLabelAlgebraEquiv_generator,
      AlgEquiv.symm_apply_apply]⟩
  invFun y := ⟨partitionLabelAlgebraEquiv part y, by
    obtain ⟨a, ha⟩ := (mem_spechtIdeal_iff
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)).toTableau
      (y : MonoidAlgebra ℚ (Equiv.Perm (Fin (YoungDiagram.ofPartition part).card)))).mp y.property
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨partitionLabelAlgebraEquiv part a, ?_⟩
    rw [← ha, map_mul, partitionLabelAlgebraEquiv_generator]⟩
  left_inv x := by apply Subtype.ext; exact AlgEquiv.apply_symm_apply _ _
  right_inv y := by apply Subtype.ext; exact AlgEquiv.symm_apply_apply _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

 theorem canonicalYoungIdealLinearEquiv_action {n : ℕ} (part : n.Partition)
    (g : Equiv.Perm (Fin n)) (x : YoungIdeal (K := ℚ) part) :
    canonicalYoungIdealLinearEquiv part (YoungIdealRepresentation part g x) =
      (spechtIdealRep (StandardYoungTableau.rowSuperstandard
        (YoungDiagram.ofPartition part)).toTableau).ρ
        ((finCongr (YoungDiagram.card_ofPartition part)).permCongrHom.symm g)
        (canonicalYoungIdealLinearEquiv part x) := by
  apply Subtype.ext
  rw [spechtIdealRep_ρ_apply_coe]
  change (partitionLabelAlgebraEquiv part).symm
      ((YoungIdealRepresentation part g x : YoungIdeal (K := ℚ) part).val) =
    MonoidAlgebra.single
      ((finCongr (YoungDiagram.card_ofPartition part)).permCongrHom.symm g) 1 *
        (partitionLabelAlgebraEquiv part).symm x.val
  rw [YoungIdealRepresentation, TauCeti.Representation.ofModule'_apply,
    Submodule.coe_smul, smul_eq_mul, map_mul]
  congr 1
  apply (partitionLabelAlgebraEquiv part).injective
  simp only [AlgEquiv.apply_symm_apply, partitionLabelAlgebraEquiv,
    MonoidAlgebra.domCongr_single, MulEquiv.apply_symm_apply]

def canonicalYoungIdealSpechtEquiv {n : ℕ} (part : n.Partition) :
    (YoungIdealRepresentation (K := ℚ) part).Equiv (spechtModule part).ρ := by
  let T := (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)).toTableau
  let E := spechtIdealEquivSpechtSubrepresentation T
  refine Representation.Equiv.mk
    ((canonicalYoungIdealLinearEquiv part).trans E.toLinearEquiv) ?_
  intro g
  apply LinearMap.ext
  intro x
  have h := E.toIntertwiningMap.isIntertwining'
    ((finCongr (YoungDiagram.card_ofPartition part)).permCongrHom.symm g)
  have hx := DFunLike.congr_fun h (canonicalYoungIdealLinearEquiv part x)
  simp only [LinearMap.comp_apply] at hx
  rw [← canonicalYoungIdealLinearEquiv_action] at hx
  simp only [Equiv.permCongrHom_symm, finCongr_symm] at hx
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_trans,
    LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap,
    Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toLinearMap,
    Representation.Equiv.coe_toIntertwiningMap,
    spechtModule, FDRep.of_ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, finCongr, E, T] using hx

/-- A full standard basis inside the actual ideal used by the decomposition. -/
def canonicalYoungIdealBasis {n : ℕ} (part : n.Partition) :
    Basis (StandardYoungTableau (YoungDiagram.ofPartition part)) ℚ
      (YoungIdeal (K := ℚ) part) :=
  (spechtModuleStandardBasis part).map (canonicalYoungIdealSpechtEquiv part).toLinearEquiv.symm

@[simp] theorem canonicalYoungIdealSpechtEquiv_basis {n : ℕ} (part : n.Partition)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    canonicalYoungIdealSpechtEquiv part (canonicalYoungIdealBasis part T) =
      spechtModuleStandardBasis part T := by
  simp only [canonicalYoungIdealBasis, Basis.map_apply,
    Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_symm,
    Representation.Equiv.apply_symm_apply]

end HigherSpecht
end
end CanonicalSource53

section CanonicalSource54
/- Source: HigherSpecht/PrefixCocharge.lean -/



/-!
# The unboosted prefix and its actual column-insertion filling

Restriction keeps the literal cells and the same initial labels.  Its cocharge
is therefore the restriction of the original cocharge, rather than an
independently chosen filling.  The output labels are then embedded into the
ambient tableau without changing their original column numbers.
-/

noncomputable section

open Finset TauCeti TauCeti.YoungTableau Function

namespace HigherSpecht

variable {μ : YoungDiagram}

def prefixCellsEmbedding (S : StandardYoungTableau μ) (k : ℕ) :
    ↥(prefixShape S k).cells ↪ ↥μ.cells where
  toFun c := ⟨c.val, prefixShape_le S k c.property⟩
  inj' c d h := Subtype.ext (congrArg (fun z : ↥μ.cells => z.val) h)

@[simp] theorem prefixCellsEmbedding_apply (S : StandardYoungTableau μ) (k : ℕ)
    (c : ↥(prefixShape S k).cells) :
    prefixCellsEmbedding S k c = ⟨c.val, prefixShape_le S k c.property⟩ := rfl

@[simp] theorem prefixCellsEmbedding_val (S : StandardYoungTableau μ) (k : ℕ)
    (c : ↥(prefixShape S k).cells) : (prefixCellsEmbedding S k c).val = c.val := rfl

 theorem prefixTableau_symm_val (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (i : Fin (prefixShape S k).card) :
    prefixCellsEmbedding S k ((prefixTableau S k hk).toTableau.symm i) =
      S.toTableau.symm ⟨i.val, by
        have hi : i.val < k := by simpa only [prefixShape_card S k hk] using i.isLt
        exact hi.trans_le hk⟩ := by
  apply S.toTableau.injective
  apply Fin.ext
  simpa only [prefixCellsEmbedding_apply,
    StandardYoungTableau.toTableau_apply, standardTableau_apply_symm,
    Equiv.apply_symm_apply] using
    (prefixTableau_apply_val S k hk ((prefixTableau S k hk).toTableau.symm i)).symm

 theorem tableauRows_prefix (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    {i : ℕ} (hi : i < k) :
    tableauRows (prefixTableau S k hk) i = tableauRows S i := by
  have hip : i < (prefixShape S k).card := by simpa only [prefixShape_card S k hk] using hi
  simp only [tableauRows, dif_pos hip, dif_pos (hi.trans_le hk), rowIndex_def]
  exact congrArg (fun c : ↥μ.cells => c.val.1)
    (prefixTableau_symm_val S k hk ⟨i, hip⟩)

 theorem cochargeLabel_prefix (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (i : Fin (prefixShape S k).card) :
    cochargeLabel (prefixTableau S k hk) i =
      cochargeLabel S ⟨i.val, by
        have hi : i.val < k := by simpa only [prefixShape_card S k hk] using i.isLt
        exact hi.trans_le hk⟩ := by
  unfold cochargeLabel ascentCount
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have hik : i.val < k := by simpa only [prefixShape_card S k hk] using i.isLt
  rw [tableauRows_prefix S k hk (by omega), tableauRows_prefix S k hk (by omega)]

 theorem cochargeFilling_prefix (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (c : ↥(prefixShape S k).cells) :
    cochargeFilling (prefixTableau S k hk) c = cochargeFilling S (prefixCellsEmbedding S k c) := by
  rw [cochargeFilling, cochargeLabel_prefix]
  congr 1

 theorem boostedFilling_prefix (S : StandardYoungTableau μ) (eta : YoungDiagram)
    (k : ℕ) (hk : k ≤ μ.card) (hlen : eta.colLen 0 ≤ μ.card - k)
    (c : ↥(prefixShape S k).cells) :
    boostedFilling S eta (prefixCellsEmbedding S k c) =
      cochargeFilling (prefixTableau S k hk) c := by
  rw [cochargeFilling_prefix]
  exact boostedLabel_eq_on_prefix S eta hk hlen _
    (((mem_prefixShape S k c.val).mp c.property).choose_spec)

/-- Original column-scan positions of the restricted tableau, with ambient
variable labels supplied by `T`. -/
def prefixScanEmbedding (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) : Fin (prefixShape S k).card ↪ Fin μ.card :=
  (columnScanEquiv (prefixShape S k)).toEmbedding.trans
    ((prefixCellsEmbedding S k).trans T.toEmbedding)

 theorem prefixScanEmbedding_column_antitone (S : StandardYoungTableau μ)
    (T : YoungTableau μ) (k : ℕ) :
    Antitone (fun i => colIndex T (prefixScanEmbedding S T k i)) := by
  simpa only [prefixScanEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    colIndex_apply, prefixCellsEmbedding_val] using
    columnScan_column_antitone (prefixShape S k)

/-- The actual partial filling used in Section 4.2. -/
def prefixInsertionFilling (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) :
    ↥(columnInsertion (prefixTableau S k hk)).state.shape.cells ↪ Fin μ.card :=
  (columnInsertion (prefixTableau S k hk)).filling.toEmbedding.trans
    (prefixScanEmbedding S T k)

 theorem prefixInsertionFilling_range (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) :
    Set.range (prefixInsertionFilling S T k hk) =
      {i | (S (T.symm i)).val < k} := by
  ext i
  constructor
  · rintro ⟨c, rfl⟩
    simp only [prefixInsertionFilling, Function.Embedding.trans_apply, prefixScanEmbedding,
      Equiv.coe_toEmbedding, Set.mem_setOf_eq, Equiv.symm_apply_apply]
    exact ((mem_prefixShape S k _).mp
      (columnScanEquiv (prefixShape S k) ((columnInsertion (prefixTableau S k hk)).filling c)).property).choose_spec
  · intro hi
    let c : ↥(prefixShape S k).cells :=
      ⟨(T.symm i).val, (mem_prefixShape S k _).mpr ⟨(T.symm i).property, hi⟩⟩
    refine ⟨(columnInsertion (prefixTableau S k hk)).filling.symm
      ((columnScanEquiv (prefixShape S k)).symm c), ?_⟩
    simp only [prefixInsertionFilling, prefixScanEmbedding, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.apply_symm_apply, prefixCellsEmbedding]
    exact T.apply_symm_apply i

 theorem prefixInsertionFilling_card (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) :
    (columnInsertion (prefixTableau S k hk)).state.shape.card = k := by
  simpa only [prefixShape_card S k hk] using
    catTableauOutput_card (prefixTableau S k hk)
      (columnInsertion_catTableauOutput (prefixTableau S k hk))

 theorem prefixInsertionFilling_dominates (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (lam : YoungDiagram)
    (he : CatDominates (prefixTableau S k hk) lam) :
    Dominates (columnInsertion (prefixTableau S k hk)).state.shape lam :=
  (columnInsertion_dominates_iff (prefixTableau S k hk) lam).mpr he

end HigherSpecht
end
end CanonicalSource54

section CanonicalSource55
/- Source: HigherSpecht/WitnessVandermonde.lean -/



/-!
# The alternating witness is the actual column Vandermonde product

A matrix whose off-column blocks are zero supplies the correspondence.
Its Leibniz sum is the alternating column-group sum, whereas its block
determinants are precisely the embedded column alternants.  This avoids
any choice of signs or an unproved factorization convention.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Equiv Function TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem coefficientWitness_eq_columnAlternate {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n →₀ ℕ) :
    coefficientWitness (R := R) G a =
      columnAlternate G (MvPolynomial.monomial a 1) := by
  rw [columnAlternate]
  simp only [rename_monomial_permuted, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have h := Equiv.sum_comp (Equiv.inv G)
    (fun τ : G => MvPolynomial.monomial (permutedExponent a τ.val)
      (coefficientSign (R := R) τ.val))
  simpa only [coefficientWitness, coefficientSign, Equiv.inv_apply, Subgroup.coe_inv,
    Equiv.Perm.sign_inv, ← Equiv.Perm.inv_def] using h.symm

def coloredPowerMatrix {n : ℕ} (c : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    Matrix (Fin n) (Fin n) (PolynomialRing n R) :=
  fun i j => if c i = c j then MvPolynomial.X i ^ a j else 0

theorem det_coloredPowerMatrix {n : ℕ} (c : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    (coloredPowerMatrix (R := R) c a).det = coefficientWitness (colorPermutationGroup c) a := by
  rw [coefficientWitness_eq_columnAlternate, columnAlternate, Matrix.det_apply]
  have hterm (σ : Equiv.Perm (Fin n)) :
      Equiv.Perm.sign σ • ∏ i, coloredPowerMatrix (R := R) c a (σ i) i =
        if σ ∈ colorPermutationGroup c then
          coefficientSign (R := R) σ • MvPolynomial.rename σ (MvPolynomial.monomial a 1) else 0 := by
    by_cases hσ : σ ∈ colorPermutationGroup c
    · rw [if_pos hσ]
      have hp : (∏ i, coloredPowerMatrix (R := R) c a (σ i) i) =
          MvPolynomial.rename σ (MvPolynomial.monomial a 1) := by
        rw [show a = Finsupp.equivFunOnFinite.symm (fun i => a i) by ext i; rfl,
          monomial_equivFun_eq_prod]
        simp only [map_prod, map_pow, rename_X]
        apply Finset.prod_congr rfl
        intro i hi
        simp only [coloredPowerMatrix, Finsupp.equivFunOnFinite_symm_apply_apply, hσ i, if_true]
      rw [hp]
      simp only [coefficientSign, Units.smul_def, Int.cast_smul_eq_zsmul]
    · rw [if_neg hσ]
      obtain ⟨i, hi⟩ := not_forall.mp hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coloredPowerMatrix, hi]), smul_zero]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ ∈ colorPermutationGroup c)
    (fun _ => by simp) _

theorem coloredPowerMatrix_blockTriangular {n : ℕ} (c : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    Matrix.BlockTriangular (coloredPowerMatrix (R := R) c a) c := by
  intro i j hij
  exact if_neg hij.ne'

variable {n : ℕ} {μ : YoungDiagram}

def fullFillingRow (U : ↥μ.cells ≃ Fin n) (i : Fin n) : ℕ := (U.symm i).val.1

def fullFillingColumn (U : ↥μ.cells ≃ Fin n) (i : Fin n) : ℕ := (U.symm i).val.2

def fullFillingExponent (U : ↥μ.cells ≃ Fin n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fullFillingRow U)

def fullColumnFiberEquiv (U : ↥μ.cells ≃ Fin n) (j : ℕ) :
    Fin (μ.colLen j) ≃ {i : Fin n // fullFillingColumn U i = j} where
  toFun i := ⟨columnEmbedding U.toEmbedding j i, by
    simp only [columnEmbedding, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding,
      fullFillingColumn, Equiv.symm_apply_apply]⟩
  invFun i := ⟨(U.symm i.val).val.1, by
    have hc := (U.symm i.val).property
    change ((U.symm i.val).val.1, (U.symm i.val).val.2) ∈ μ at hc
    rw [show (U.symm i.val).val.2 = j from i.property] at hc
    exact YoungDiagram.mem_iff_lt_colLen.mp hc⟩
  left_inv i := by
    simp only [columnEmbedding, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding,
      Equiv.symm_apply_apply]
  right_inv i := by
    apply Subtype.ext
    apply U.symm.injective
    simp only [columnEmbedding, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding,
      Equiv.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext rfl i.property.symm

theorem coloredPowerMatrix_columnBlock_det (U : ↥μ.cells ≃ Fin n) (j : ℕ) :
    ((coloredPowerMatrix (R := R) (fullFillingColumn U) (fullFillingExponent U)).toSquareBlock
      (fullFillingColumn U) j).det = columnAlternant U.toEmbedding j := by
  rw [columnAlternant, TauCeti.alternant_def, AlgHom.map_det]
  rw [← Matrix.det_reindex_self (fullColumnFiberEquiv U j).symm]
  apply congrArg Matrix.det
  rw [Matrix.reindex_apply]
  apply Matrix.ext
  intro i l
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
    Matrix.of, Matrix.of_apply, Equiv.refl_apply, Equiv.coe_fn_mk,
    coloredPowerMatrix, fullColumnFiberEquiv, fullFillingColumn,
    fullFillingExponent, Finsupp.equivFunOnFinite_symm_apply_apply, fullFillingRow,
    columnEmbedding, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply, if_true, AlgHom.mapMatrix_apply, Matrix.map_apply,
    map_pow, rename_X]
  let cell : Fin (μ.colLen j) → ↥μ.cells := fun r =>
    ⟨(r.val, j), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩
  change
    (if (U.symm (U (cell i))).val.2 = (U.symm (U (cell l))).val.2 then
      (MvPolynomial.X (U (cell i)) : PolynomialRing n R) ^
        (U.symm (U (cell l))).val.1 else 0) =
      MvPolynomial.rename (fun r => U (cell r))
        ((MvPolynomial.X i : PolynomialRing (μ.colLen j) R) ^ l.val)
  simp only [Equiv.symm_apply_apply, cell, if_true, map_pow, rename_X]

theorem image_fullFillingColumn (U : ↥μ.cells ≃ Fin n) :
    Finset.univ.image (fullFillingColumn U) = Finset.range (μ.rowLen 0) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    have hc := μ.up_left_mem (Nat.zero_le _) le_rfl (U.symm i).property
    exact YoungDiagram.mem_iff_lt_rowLen.mp hc
  · intro hj
    let c : ↥μ.cells := ⟨(0, j), YoungDiagram.mem_iff_lt_rowLen.mpr hj⟩
    exact ⟨U c, by simp only [fullFillingColumn, Equiv.symm_apply_apply, c]⟩

theorem fullFilling_width_le (U : ↥μ.cells ≃ Fin n) : μ.rowLen 0 ≤ n := by
  have hn : μ.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr U
  rw [← hn, YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem columnAlternant_eq_one_of_width_le (U : ↥μ.cells ↪ Fin n) {j : ℕ}
    (hj : μ.rowLen 0 ≤ j) : columnAlternant (R := R) U j = 1 := by
  have hz : μ.colLen j = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hm : (0, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hp
    have hl := YoungDiagram.mem_iff_lt_rowLen.mp hm
    omega
  haveI : IsEmpty (Fin (μ.colLen j)) := by rw [hz]; infer_instance
  rw [columnAlternant, TauCeti.alternant_def, Matrix.det_isEmpty, map_one]

theorem fillingLabels_equiv (U : ↥μ.cells ≃ Fin n) : fillingLabels U.toEmbedding = Finset.univ := by
  ext i
  simp only [fillingLabels, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨fun _ => trivial, fun _ => U.surjective i⟩

theorem outsidePower_equiv (U : ↥μ.cells ≃ Fin n) (s : ℕ) :
    outsidePower (R := R) U.toEmbedding s = 1 := by
  simp only [outsidePower, fillingLabels_equiv, Finset.compl_univ, Finset.prod_empty]

/-- Exact sign-preserving identification of the alternating group sum with
the manuscript's product of column Vandermonde polynomials. -/
theorem coefficientWitness_fullFilling_eq_columnWitness (U : ↥μ.cells ≃ Fin n) (s : ℕ) :
    coefficientWitness (R := R) (colorPermutationGroup (fullFillingColumn U))
      (fullFillingExponent U) = columnWitness U.toEmbedding s := by
  rw [← det_coloredPowerMatrix, (coloredPowerMatrix_blockTriangular _ _).det,
    image_fullFillingColumn]
  simp_rw [coloredPowerMatrix_columnBlock_det]
  rw [columnWitness, outsidePower_equiv, mul_one]
  apply Finset.prod_subset (Finset.range_mono (fullFilling_width_le U))
  intro j hj hn
  exact columnAlternant_eq_one_of_width_le U.toEmbedding (by
    simpa only [Finset.mem_range, not_lt] using hn)

theorem higherSpechtWitness_eq_columnWitness (S : StandardYoungTableau μ)
    (T : YoungTableau μ) :
    higherSpechtWitness (R := R) S T = columnWitness (insertionFilling S T).toEmbedding 1 := by
  exact coefficientWitness_fullFilling_eq_columnWitness (insertionFilling S T) 1

/-- The actual pairing witness satisfies every generator relation of its
actual insertion shape; this contains no assumption about a spanning system. -/
theorem higherSpechtWitness_mem_harmonics (S : StandardYoungTableau μ)
    (T : YoungTableau μ) :
    higherSpechtWitness (R := R) S T ∈
      dividedHarmonics (untruncatedIdeal R μ.card (columnInsertion S).state.shape) := by
  rw [higherSpechtWitness_eq_columnWitness]
  exact columnWitness_mem_untruncatedHarmonics (insertionFilling S T).toEmbedding 1

end HigherSpecht
end
end CanonicalSource55

section CanonicalSource56
/- Source: HigherSpecht/EmbeddedWitness.lean -/



/-!
# Extending a column witness by fixed outside labels

The exterior variables are singleton permutation blocks.  The actual alternating
sum factors as the renamed interior witness times its exterior monomial, and the
finite rearrangement inequalities extend without any condition on the ordering
of different singleton blocks.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset Equiv Function MvPolynomial

namespace HigherSpecht

variable {ι ξ κ ν : Type*} [Fintype ι] [Fintype ξ]

 theorem RearrangementWitness.sumSingletons {u : ι → κ} {v : ι → ν}
    {a r b c : ι → ℤ} (h : RearrangementWitness u v a r b c)
    (A B C : ξ → ℤ) :
    RearrangementWitness (Sum.elim (Sum.inl ∘ u) Sum.inr)
      (Sum.elim (Sum.inl ∘ v) Sum.inr)
      (Sum.elim a A) (Sum.elim r (fun i => A i - B i))
      (Sum.elim b B) (Sum.elim c C) := by
  constructor
  · intro i
    cases i with
    | inl i => exact h.subtraction i
    | inr i => simp
  · intro j i l hil
    rcases i with ⟨i, hi⟩
    rcases l with ⟨l, hl⟩
    cases j <;> cases i <;> cases l <;> simp only [Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hi hl hil
    · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val
        (h.columnDistinct _ (a₁ := ⟨_, hi⟩) (a₂ := ⟨_, hl⟩) hil)))
    all_goals first | contradiction | exact Subtype.ext (congrArg Sum.inr (hi.trans hl.symm))
  · intro j i l hil
    rcases i with ⟨i, hi⟩
    rcases l with ⟨l, hl⟩
    cases j <;> cases i <;> cases l <;> simp only [Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hi hl hil ⊢
    · exact (h.columnMonovary _) (i := ⟨_, hi⟩) (j := ⟨_, hl⟩) hil
    all_goals first | contradiction | simp only [hi.trans hl.symm, le_refl]
  · intro i j
    cases i <;> cases j <;> simp only [Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and]
    · exact h.refinement _ _
    · constructor
      · intro hij
        exact ⟨hij, congrArg (fun i : ξ => A i - B i) hij⟩
      · exact And.left
  · intro j i l hil
    rcases i with ⟨i, hi⟩
    rcases l with ⟨l, hl⟩
    cases j <;> cases i <;> cases l <;> simp only [Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hi hl hil ⊢
    · exact (h.tiedMonovary _) (i := ⟨_, hi⟩) (j := ⟨_, hl⟩) hil
    all_goals first | contradiction | simp only [hi.trans hl.symm, le_refl]

/-- The actual interior labels and their exterior complement form a disjoint
sum equivalence with the ambient variables. -/
def embeddingSumEquiv (e : ι ↪ ξ) : ι ⊕ {j : ξ // j ∉ Set.range e} ≃ ξ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range e))

@[simp] theorem embeddingSumEquiv_inl (e : ι ↪ ξ) (i : ι) :
    embeddingSumEquiv e (Sum.inl i) = e i := rfl

@[simp] theorem embeddingSumEquiv_inr (e : ι ↪ ξ) (i : {j : ξ // j ∉ Set.range e}) :
    embeddingSumEquiv e (Sum.inr i) = i.val := rfl

def extendByEmbedding (e : ι ↪ ξ) (f : ι → ℤ) (g : ξ → ℤ) : ξ → ℤ :=
  Sum.elim f (fun j => g j.val) ∘ (embeddingSumEquiv e).symm

 theorem extendByEmbedding_apply (e : ι ↪ ξ) (f : ι → ℤ) (g : ξ → ℤ) (i : ι) :
    extendByEmbedding e f g (e i) = f i := by
  change Sum.elim f _ ((embeddingSumEquiv e).symm (embeddingSumEquiv e (Sum.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

 theorem extendByEmbedding_apply_outside (e : ι ↪ ξ) (f : ι → ℤ) (g : ξ → ℤ)
    (j : ξ) (hj : j ∉ Set.range e) : extendByEmbedding e f g j = g j := by
  change Sum.elim f _ ((embeddingSumEquiv e).symm (embeddingSumEquiv e (Sum.inr ⟨j, hj⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

def embeddedColumn (e : ι ↪ ξ) (u : ι → κ) : ξ → κ ⊕ {j : ξ // j ∉ Set.range e} :=
  Sum.elim (Sum.inl ∘ u) Sum.inr ∘ (embeddingSumEquiv e).symm

 theorem RearrangementWitness.extendEmbedding {u : ι → κ} {v : ι → ν}
    {a r b c : ι → ℤ} (h : RearrangementWitness u v a r b c)
    (e : ι ↪ ξ) (A B C : ξ → ℤ) :
    RearrangementWitness (embeddedColumn e u) (embeddedColumn e v)
      (extendByEmbedding e a A) (extendByEmbedding e r (fun i => A i - B i))
      (extendByEmbedding e b B) (extendByEmbedding e c C) :=
  (h.sumSingletons
    (fun j : {j : ξ // j ∉ Set.range e} => A j.val)
    (fun j : {j : ξ // j ∉ Set.range e} => B j.val)
    (fun j : {j : ξ // j ∉ Set.range e} => C j.val)).precompEquiv
      (embeddingSumEquiv e).symm

variable [DecidableEq ι] [DecidableEq ξ]

def embeddedPermutationGroup (e : ι ↪ ξ) (G : Subgroup (Equiv.Perm ι)) :
    Subgroup (Equiv.Perm ξ) := G.map (Equiv.Perm.viaEmbeddingHom e)

 theorem embeddedPermutationGroup_preserves {e : ι ↪ ξ} {u : ι → κ}
    {G : Subgroup (Equiv.Perm ι)} (hG : ∀ σ : G, ∀ i, u (σ.val i) = u i)
    (τ : embeddedPermutationGroup e G) (j : ξ) :
    embeddedColumn e u (τ.val j) = embeddedColumn e u j := by
  obtain ⟨σ, hσ, hτ⟩ := τ.property
  have ht : τ.val = σ.viaEmbedding e := hτ.symm
  rw [ht]
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [Equiv.Perm.viaEmbedding_apply]
    change Sum.elim _ _ ((embeddingSumEquiv e).symm (embeddingSumEquiv e (Sum.inl (σ i)))) =
      Sum.elim _ _ ((embeddingSumEquiv e).symm (embeddingSumEquiv e (Sum.inl i)))
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Function.comp_apply, hG ⟨σ, hσ⟩ i]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hj]

 theorem permutedExponent_embedded (e : ι ↪ ξ) (a : ι →₀ ℕ) (q : ξ →₀ ℕ)
    (hq : ∀ i, q (e i) = 0) (σ : Equiv.Perm ι) :
    permutedExponent (a.mapDomain e + q) (σ.viaEmbedding e) =
      (permutedExponent a σ).mapDomain e + q := by
  ext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp only [permutedExponent_apply, Finsupp.add_apply, Equiv.Perm.viaEmbedding_apply,
      Finsupp.mapDomain_apply_of_injective e.injective, hq, add_zero]
  · simp only [permutedExponent_apply, Finsupp.add_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hj,
      Finsupp.mapDomain_of_notMem_range _ _ hj, zero_add]

variable {R : Type*} [CommRing R]

 theorem coefficientWitness_embedded (e : ι ↪ ξ) (G : Subgroup (Equiv.Perm ι))
    (a : ι →₀ ℕ) (q : ξ →₀ ℕ) (hq : ∀ i, q (e i) = 0) :
    coefficientWitness (R := R) (embeddedPermutationGroup e G) (a.mapDomain e + q) =
      MvPolynomial.rename e (coefficientWitness G a) * MvPolynomial.monomial q 1 := by
  unfold embeddedPermutationGroup
  let E := G.equivMapOfInjective (Equiv.Perm.viaEmbeddingHom e)
    (Equiv.Perm.viaEmbeddingHom_injective e)
  rw [coefficientWitness]
  conv_lhs =>
    rw [← E.toEquiv.sum_comp (fun τ : G.map (Equiv.Perm.viaEmbeddingHom e) =>
      MvPolynomial.monomial (permutedExponent (a.mapDomain e + q) τ.val)
        (coefficientSign (R := R) τ.val))]
  simp only [coefficientWitness, map_sum, Finset.sum_mul, rename_monomial,
    MvPolynomial.monomial_mul, mul_one]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hE : (E.toEquiv σ : Equiv.Perm ξ) =
      (Equiv.Perm.viaEmbeddingHom e) σ.val := by
    exact Subgroup.coe_equivMapOfInjective_apply G (Equiv.Perm.viaEmbeddingHom e)
      (Equiv.Perm.viaEmbeddingHom_injective e) σ
  rw [hE, Equiv.Perm.viaEmbeddingHom_apply, permutedExponent_embedded e a q hq]
  congr 1
  unfold coefficientSign Equiv.Perm.viaEmbedding
  rw [Equiv.Perm.sign_extendDomain]

end HigherSpecht
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/FactorialWitnesses.lean -/



/-!
# Equivalence of the integral and ordinary column witnesses

The divided-power witness and the ordinary product of column Vandermondes have
the same displayed coefficients.  Every term has the same product of exponent
factorials.  The normalization below proves their precise scalar relationship,
so the characteristic-zero ordinary-differential form of Lemma 2.1 follows from
the integral contraction identity without changing its witness polynomial.
-/

noncomputable section

open MvPolynomial Finset TauCeti

namespace HigherSpecht

variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
  [Field K] [CharZero K]

theorem exponentFactorial_mapDomain (e : σ ↪ τ) (a : σ →₀ ℕ) :
    exponentFactorial (a.mapDomain e) = exponentFactorial a := by
  classical
  unfold exponentFactorial
  calc
    (∏ j : τ, ((a.mapDomain e) j).factorial) =
        ∏ j ∈ (Finset.univ.map e), ((a.mapDomain e) j).factorial := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro j hj hjnot
      have hr : j ∉ Set.range e := by simpa using hjnot
      rw [Finsupp.mapDomain_of_notMem_range _ _ hr]
      rfl
    _ = ∏ i : σ, (a i).factorial := by
      rw [Finset.prod_map]
      simp only [Finsupp.mapDomain_apply_of_injective e.injective]

theorem factorialNormalize_rename_embedding (e : σ ↪ τ) (p : MvPolynomial σ K) :
    factorialNormalize (MvPolynomial.rename e p) =
      MvPolynomial.rename e (factorialNormalize p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial a c =>
    rw [rename_monomial, factorialNormalize_monomial,
      factorialNormalize_monomial, rename_monomial, exponentFactorial_mapDomain]

theorem exponentFactorial_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    exponentFactorial (Finsupp.sumElim a b) = exponentFactorial a * exponentFactorial b := by
  simp only [exponentFactorial, Fintype.prod_sum_type, Finsupp.sumElim_inl,
    Finsupp.sumElim_inr]

theorem factorialNormalize_tensor (p : MvPolynomial σ K) (q : MvPolynomial τ K) :
    factorialNormalize (tensorPolynomial p q) =
      tensorPolynomial (factorialNormalize p) (factorialNormalize q) := by
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp' => simp [hp, hp']
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq' => simp [hq, hq']
    | monomial b e =>
      rw [tensorPolynomial_monomial, factorialNormalize_monomial,
        factorialNormalize_monomial, factorialNormalize_monomial,
        tensorPolynomial_monomial, exponentFactorial_sumElim, Nat.cast_mul]
      congr 1
      exact (div_mul_div_comm c _ e _).symm

/-- Factorial normalization is multiplicative precisely for the disjoint
variable products used here. -/
theorem factorialNormalize_mul_disjoint (p q : MvPolynomial σ K)
    (hpq : Disjoint p.vars q.vars) :
    factorialNormalize (p * q) = factorialNormalize p * factorialNormalize q := by
  classical
  let C : Set σ := ↑p.vars
  obtain ⟨p', hp'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (Subtype.val : C → σ) Subtype.val_injective (by simpa [C])
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q
    (Subtype.val : {i : σ // i ∉ C} → σ) Subtype.val_injective (by
      intro i hi
      exact ⟨⟨i, fun hip => Finset.disjoint_left.mp hpq hip hi⟩, rfl⟩)
  let E := Equiv.sumCompl (fun i : σ => i ∈ C)
  have h := congrArg (MvPolynomial.rename E)
    (factorialNormalize_tensor (K := K) p' q')
  have hE : factorialNormalize (MvPolynomial.rename E (tensorPolynomial p' q')) =
      MvPolynomial.rename E (factorialNormalize (tensorPolynomial p' q')) := by
    simpa only [Equiv.coe_toEmbedding] using
      factorialNormalize_rename_embedding E.toEmbedding (tensorPolynomial p' q')
  have hpN : factorialNormalize (MvPolynomial.rename (Subtype.val : C → σ) p') =
      MvPolynomial.rename (Subtype.val : C → σ) (factorialNormalize p') := by
    simpa only [Function.Embedding.coeFn_mk] using
      factorialNormalize_rename_embedding
        (⟨Subtype.val, Subtype.val_injective⟩ : C ↪ σ) p'
  have hqN : factorialNormalize
      (MvPolynomial.rename (Subtype.val : {i : σ // i ∉ C} → σ) q') =
      MvPolynomial.rename (Subtype.val : {i : σ // i ∉ C} → σ)
        (factorialNormalize q') := by
    simpa only [Function.Embedding.coeFn_mk] using
      factorialNormalize_rename_embedding
        (⟨Subtype.val, Subtype.val_injective⟩ : {i : σ // i ∉ C} ↪ σ) q'
  rw [← hE] at h
  simpa only [tensorPolynomial, map_mul, rename_rename, Function.comp_def, E,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
    ← hpN, ← hqN, hp', hq'] using h

theorem factorialNormalize_prod_disjoint {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => (f i).vars)) :
    factorialNormalize (∏ i ∈ s, f i) = ∏ i ∈ s, factorialNormalize (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    change factorialNormalize (monomial 0 1) = 1
    rw [factorialNormalize_monomial]
    simp [exponentFactorial]
  | @insert a s ha ih =>
    have hds : (s : Set ι).PairwiseDisjoint (fun i => (f i).vars) :=
      hdisj.subset (by intro i hi; exact Finset.mem_insert_of_mem hi)
    have hda : Disjoint (f a).vars (∏ i ∈ s, f i).vars := by
      apply Finset.disjoint_left.mpr
      intro j hja hjp
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hjp)
      exact Finset.disjoint_left.mp
        (hdisj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
          (by intro h; subst i; exact ha hi)) hja hji
    rw [Finset.prod_insert ha, factorialNormalize_mul_disjoint _ _ hda,
      ih hds, Finset.prod_insert ha]

theorem factorialNormalize_fullAlternation (p : MvPolynomial σ K) :
    factorialNormalize (fullAlternation p) = fullAlternation (factorialNormalize p) := by
  rw [fullAlternation_apply, map_sum, fullAlternation_apply]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_smul]
  have heq : factorialNormalize (MvPolynomial.rename e p) =
      MvPolynomial.rename e (factorialNormalize p) := by
    simpa only [Equiv.coe_toEmbedding] using
      factorialNormalize_rename_embedding e.toEmbedding p
  rw [heq]

theorem factorialNormalize_alternant (a : σ →₀ ℕ) :
    factorialNormalize (TauCeti.alternant σ K a) =
      (exponentFactorial a : K)⁻¹ • TauCeti.alternant σ K a := by
  rw [← fullAlternation_monomial, factorialNormalize_fullAlternation,
    factorialNormalize_monomial_one]
  have hm : monomial a (exponentFactorial a : K)⁻¹ =
      (exponentFactorial a : K)⁻¹ • (monomial a 1 : MvPolynomial σ K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, fullAlternation_monomial]

theorem exponentFactorial_single (i : σ) (s : ℕ) :
    exponentFactorial (Finsupp.single i s) = s.factorial := by
  classical
  unfold exponentFactorial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Finsupp.single_apply, hji]
  · simp

theorem factorialNormalize_X_pow (i : σ) (s : ℕ) :
    factorialNormalize ((X i : MvPolynomial σ K) ^ s) =
      (s.factorial : K)⁻¹ • (X i) ^ s := by
  rw [MvPolynomial.X_pow_eq_monomial, factorialNormalize_monomial,
    exponentFactorial_single]
  simp only [MvPolynomial.X_pow_eq_monomial, one_div, MvPolynomial.smul_monomial,
    smul_eq_mul, mul_one]

variable {n : ℕ} {μ : YoungDiagram}

def columnWitnessFactorial (U : ↥μ.cells ↪ Fin n) (s : ℕ) : ℕ :=
  (∏ j ∈ Finset.range n, exponentFactorial (staircaseExponent (μ.colLen j))) *
    ∏ i ∈ (fillingLabels U)ᶜ, (s - 1).factorial

theorem columnWitnessFactorial_pos (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    0 < columnWitnessFactorial U s := by
  apply Nat.mul_pos
  · exact Finset.prod_pos fun _ _ => exponentFactorial_pos _
  · exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem factorialNormalize_columnAlternant (U : ↥μ.cells ↪ Fin n) (j : ℕ) :
    factorialNormalize (columnAlternant (R := K) U j) =
      (exponentFactorial (staircaseExponent (μ.colLen j)) : K)⁻¹ • columnAlternant U j := by
  rw [columnAlternant, factorialNormalize_rename_embedding]
  rw [show (fun i : Fin (μ.colLen j) => i.val) = staircaseExponent (μ.colLen j) from rfl]
  rw [factorialNormalize_alternant, map_smul]

theorem factorialNormalize_columnWitness (U : ↥μ.cells ↪ Fin n) (s : ℕ) :
    factorialNormalize (columnWitness (R := K) U s) =
      (columnWitnessFactorial U s : K)⁻¹ • columnWitness U s := by
  classical
  have hcols : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
      (fun j => (columnAlternant (R := K) U j).vars) := by
    intro j hj l hl hne
    exact (columnLabels_pairwiseDisjoint U (Set.mem_univ j) (Set.mem_univ l) hne).mono
      (vars_columnAlternant_subset U j) (vars_columnAlternant_subset U l)
  have houtside : (↑(fillingLabels U)ᶜ : Set (Fin n)).PairwiseDisjoint
      (fun i => (((X i : PolynomialRing n K) ^ (s - 1)).vars)) := by
    intro i hi j hj hij
    apply (Finset.disjoint_singleton.mpr hij).mono
    · exact (MvPolynomial.vars_pow _ _).trans (by simp)
    · exact (MvPolynomial.vars_pow _ _).trans (by simp)
  have hdisj : Disjoint (∏ j ∈ Finset.range n, columnAlternant (R := K) U j).vars
      (outsidePower (R := K) U s).vars := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hi)
    exact Finset.mem_compl.mp (vars_outsidePower_subset U s ho)
      (columnLabels_subset_fillingLabels U j (vars_columnAlternant_subset U j hij))
  rw [columnWitness, factorialNormalize_mul_disjoint _ _ hdisj,
    factorialNormalize_prod_disjoint _ _ hcols]
  have hout : factorialNormalize (outsidePower (R := K) U s) =
      (∏ i ∈ (fillingLabels U)ᶜ, ((s - 1).factorial : K)⁻¹) • outsidePower U s := by
    rw [outsidePower, factorialNormalize_prod_disjoint _ _ houtside]
    simp_rw [factorialNormalize_X_pow]
    rw [Finset.prod_smul]
  rw [hout]
  simp_rw [factorialNormalize_columnAlternant]
  rw [Finset.prod_smul, smul_mul_smul_comm]
  congr 1
  simp [columnWitnessFactorial, Nat.cast_mul, Nat.cast_prod, mul_inv,
    Finset.prod_inv_distrib, mul_comm]

/-- Integral contraction and the ordinary differential operator annihilate
exactly the same specified column witness in characteristic zero. -/
theorem ordinaryAction_columnWitness_eq_zero_of_divided
    (U : ↥μ.cells ↪ Fin n) (s : ℕ) (f : PolynomialRing n K)
    (hf : dividedAction f (columnWitness U s) = 0) :
    ordinaryAction f (columnWitness U s) = 0 := by
  have h := ordinaryAction_factorialTransport f (columnWitness (R := K) U s)
  change ordinaryAction f (factorialNormalize (columnWitness U s)) =
    factorialNormalize (dividedAction f (columnWitness U s)) at h
  rw [factorialNormalize_columnWitness, map_smul, hf, map_zero] at h
  have hN : (columnWitnessFactorial U s : K) ≠ 0 := by
    exact_mod_cast (columnWitnessFactorial_pos U s).ne'
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hN)

/-- The ordinary elementary-operator statement of manuscript Lemma 2.1. -/
theorem ordinary_elementary_contract_columnWitness (U : ↥μ.cells ↪ Fin n) (s : ℕ)
    (Y : Finset (Fin n)) {d : ℕ} (hd : 0 < d)
    (hthreshold : (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ)) :
    ordinaryAction (elementaryOn (R := K) Y d) (columnWitness U s) = 0 :=
  ordinaryAction_columnWitness_eq_zero_of_divided U s _
    (elementary_contract_columnWitness U s Y hd hthreshold)

/-- The ordinary power-operator statement of manuscript Lemma 2.1. -/
theorem ordinary_power_contract_columnWitness (U : ↥μ.cells ↪ Fin n) {s : ℕ}
    (hs0 : 0 < s) (hs : μ.colLen 0 ≤ s) (i : Fin n) :
    ordinaryAction ((X i : PolynomialRing n K) ^ s) (columnWitness U s) = 0 :=
  ordinaryAction_columnWitness_eq_zero_of_divided U s _
    (power_contract_columnWitness U hs0 hs i)

end HigherSpecht
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/PartialColumnWitness.lean -/



/-!
# Exact partial column witness and exterior powers

The ambient alternating sum is the literal product of column Vandermondes
with the exterior exponent `s-1`.  The subgroup is the image of the interior
column group under extension by the identity, so outside labels are fixed.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset Equiv Function MvPolynomial TauCeti

namespace HigherSpecht

variable {k n : ℕ} {μ : YoungDiagram} {R : Type*} [CommRing R]

def exteriorExponent (e : Fin k ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => if i ∈ Set.range e then 0 else s - 1

@[simp] theorem exteriorExponent_inside (e : Fin k ↪ Fin n) (s : ℕ) (i : Fin k) :
    exteriorExponent e s (e i) = 0 := by
  simp [exteriorExponent, Set.mem_range_self]

 theorem exteriorExponent_outside (e : Fin k ↪ Fin n) (s : ℕ) (i : Fin n)
    (hi : i ∉ Set.range e) : exteriorExponent e s i = s - 1 := by
  simp only [exteriorExponent, Finsupp.equivFunOnFinite_symm_apply_apply, if_neg hi]

 theorem fillingLabels_comp_equiv (U : ↥μ.cells ≃ Fin k) (e : Fin k ↪ Fin n) :
    fillingLabels (U.toEmbedding.trans e) = Finset.univ.map e := by
  ext i
  simp only [fillingLabels, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨U c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨U.symm c, by rw [Equiv.apply_symm_apply]⟩

 theorem monomial_exteriorExponent (U : ↥μ.cells ≃ Fin k) (e : Fin k ↪ Fin n) (s : ℕ) :
    MvPolynomial.monomial (exteriorExponent e s) (1 : R) =
      outsidePower (U.toEmbedding.trans e) s := by
  rw [exteriorExponent, monomial_equivFun_eq_prod, outsidePower, fillingLabels_comp_equiv]
  calc
    (∏ i : Fin n, (MvPolynomial.X i : PolynomialRing n R) ^
        (if i ∈ Set.range e then 0 else s - 1)) =
        ∏ i ∈ (Finset.univ.map e)ᶜ, (MvPolynomial.X i : PolynomialRing n R) ^
          (if i ∈ Set.range e then 0 else s - 1) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i hi hin
      have hmem : i ∈ Set.range e := by
        simpa only [Finset.mem_compl, not_not, Finset.mem_map, Finset.mem_univ,
          true_and, Set.mem_range] using hin
      simp only [if_pos hmem, pow_zero]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hnot : i ∉ Set.range e := by simpa only [Finset.mem_compl, Finset.mem_map,
        Finset.mem_univ, true_and, Set.mem_range] using hi
      rw [if_neg hnot]

 theorem rename_columnAlternant (e : Fin k ↪ Fin n) (U : ↥μ.cells ↪ Fin k) (j : ℕ) :
    MvPolynomial.rename e (columnAlternant (R := R) U j) =
      columnAlternant (U.trans e) j := by
  rw [columnAlternant, columnAlternant, rename_rename]
  rfl

 theorem rename_fullColumnWitness_mul_exterior (U : ↥μ.cells ≃ Fin k)
    (e : Fin k ↪ Fin n) (s : ℕ) :
    MvPolynomial.rename e (columnWitness (R := R) U.toEmbedding 1) *
        MvPolynomial.monomial (exteriorExponent e s) 1 =
      columnWitness (U.toEmbedding.trans e) s := by
  have hkn : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  rw [columnWitness, outsidePower_equiv, mul_one, map_prod, monomial_exteriorExponent,
    columnWitness]
  simp_rw [rename_columnAlternant]
  congr 1
  apply Finset.prod_subset (Finset.range_mono hkn)
  intro j hj hjnot
  exact columnAlternant_eq_one_of_width_le (U.toEmbedding.trans e)
    ((fullFilling_width_le U).trans (by simpa only [Finset.mem_range, not_lt] using hjnot))

 theorem coefficientWitness_partialFilling (U : ↥μ.cells ≃ Fin k)
    (e : Fin k ↪ Fin n) (s : ℕ) :
    coefficientWitness (R := R)
        (embeddedPermutationGroup e (colorPermutationGroup (fullFillingColumn U)))
        ((fullFillingExponent U).mapDomain e + exteriorExponent e s) =
      columnWitness (U.toEmbedding.trans e) s := by
  rw [coefficientWitness_embedded e _ _ _ (exteriorExponent_inside e s),
    coefficientWitness_fullFilling_eq_columnWitness U 1]
  exact rename_fullColumnWitness_mul_exterior U e s

def embeddedWitnessAlpha (e : Fin k ↪ Fin n) (a : Fin k →₀ ℕ) (s : ℕ) : Fin n →₀ ℕ :=
  a.mapDomain e + exteriorExponent e s

@[simp] theorem embeddedWitnessAlpha_inside (e : Fin k ↪ Fin n)
    (a : Fin k →₀ ℕ) (s : ℕ) (i : Fin k) :
    embeddedWitnessAlpha e a s (e i) = a i := by
  simp only [embeddedWitnessAlpha, Finsupp.add_apply,
    Finsupp.mapDomain_apply_of_injective e.injective, exteriorExponent_inside, add_zero]

 theorem embeddedWitnessAlpha_outside (e : Fin k ↪ Fin n)
    (a : Fin k →₀ ℕ) (s : ℕ) (i : Fin n) (hi : i ∉ Set.range e) :
    embeddedWitnessAlpha e a s i = s - 1 := by
  simp only [embeddedWitnessAlpha, Finsupp.add_apply,
    Finsupp.mapDomain_of_notMem_range _ _ hi, exteriorExponent_outside e s i hi, zero_add]

 theorem embeddedWitness_geometry {κ ν : Type*}
    {u : Fin k → κ} {v : Fin k → ν} {a r b : Fin k →₀ ℕ} {c : Fin k → ℤ}
    (h : RearrangementWitness u v (intExponent a) (intExponent r) (intExponent b) c)
    (e : Fin k ↪ Fin n) (s : ℕ) (B : Fin n →₀ ℕ) (C : Fin n → ℤ)
    (hB : ∀ i, B (e i) = b i) (hC : ∀ i, C (e i) = c i)
    (hbound : ∀ i, i ∉ Set.range e → B i ≤ s - 1) :
    RearrangementWitness (embeddedColumn e u) (embeddedColumn e v)
      (intExponent (embeddedWitnessAlpha e a s))
      (intExponent (embeddedWitnessAlpha e a s - B)) (intExponent B) C := by
  have hle : B ≤ embeddedWitnessAlpha e a s := by
    intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [hB, embeddedWitnessAlpha_inside]
      have hs := h.subtraction j
      dsimp [intExponent] at hs
      omega
    · rw [embeddedWitnessAlpha_outside e a s i hi]
      exact hbound i hi
  have heqA : extendByEmbedding e (intExponent a) (fun _ => (s - 1 : ℕ)) =
      intExponent (embeddedWitnessAlpha e a s) := by
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      simp only [extendByEmbedding_apply, intExponent, embeddedWitnessAlpha_inside]
    · rw [extendByEmbedding_apply_outside e _ _ i hi, intExponent,
        embeddedWitnessAlpha_outside e a s i hi]
  have heqB : extendByEmbedding e (intExponent b) (intExponent B) = intExponent B := by
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [extendByEmbedding_apply]
      exact congrArg Int.ofNat (hB j).symm
    · exact extendByEmbedding_apply_outside e _ _ i hi
  have heqC : extendByEmbedding e c C = C := by
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [extendByEmbedding_apply, hC]
    · exact extendByEmbedding_apply_outside e _ _ i hi
  have heqR : extendByEmbedding e (intExponent r)
      (fun i => ((s - 1 : ℕ) : ℤ) - intExponent B i) =
        intExponent (embeddedWitnessAlpha e a s - B) := by
    funext i
    rw [intExponent_sub hle]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      simp only [extendByEmbedding_apply, intExponent, embeddedWitnessAlpha_inside, hB]
      have hs := h.subtraction j
      dsimp [intExponent] at hs
      omega
    · simp only [extendByEmbedding_apply_outside e _ _ i hi, intExponent,
        embeddedWitnessAlpha_outside e a s i hi]
  simpa only [heqA, heqR, heqB, heqC] using
    h.extendEmbedding e (fun _ => ((s - 1 : ℕ) : ℤ)) (intExponent B) C

end HigherSpecht
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/ColumnPrefixes.lean -/



/-!
# The manuscript's exact column-prefix ordering

The weighted column sum is useful for detecting equality, but the manuscript
orders tableaux by the entire prefix vector.  This file proves each prefix
inequality, and uses the literal lexicographic key `(N,-P₁,...,-Pₙ)` in the
off-diagonal pairing statement.  The finite key includes every possible
column; all subsequent prefixes are the common total degree.
-/

noncomputable section

open Finset Function Equiv MvPolynomial TauCeti TauCeti.YoungTableau

namespace HigherSpecht

variable {ι κ ν : Type*} [Fintype ι]

def columnPrefix (c : ι → ℕ) (b : ι → ℤ) (k : ℕ) : ℤ :=
  ∑ i, if c i < k then b i else 0

def prefixStep (k : ℕ) (z : ℤ) : ℤ := if z < (k : ℤ) then -1 else 0

theorem prefixStep_monotone (k : ℕ) : Monotone (prefixStep k) := by
  intro x y hxy
  unfold prefixStep
  split_ifs <;> omega

theorem columnWeight_prefixStep (c : ι → ℕ) (b : ι → ℤ) (k : ℕ) :
    columnWeight (fun i => prefixStep k (c i)) b = -columnPrefix c b k := by
  simp only [columnWeight, columnPrefix, prefixStep, Int.ofNat_lt,
    ite_mul, neg_one_mul, zero_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem RearrangementWitness.mapColumnWeight
    {u : ι → κ} {v : ι → ν} {a r b c : ι → ℤ}
    (h : RearrangementWitness u v a r b c) (w : ℤ → ℤ) (hw : Monotone w) :
    RearrangementWitness u v a r b (w ∘ c) := by
  refine ⟨h.subtraction, h.columnDistinct, h.columnMonovary, h.refinement, ?_⟩
  intro j i l hil
  apply h.tiedMonovary j
  have hc : c l.val < c i.val := by
    by_contra hn
    have hm := hw (le_of_not_gt hn)
    dsimp only [Function.comp_apply] at hil
    linarith
  linarith

theorem RearrangementWitness.prefix_le_of_norm_eq
    {u : ι → κ} {v : ι → ν} {a r b : ι → ℤ} {c : ι → ℕ}
    (h : RearrangementWitness u v a r b (fun i => (c i : ℤ)))
    (σ : Equiv.Perm ι) (hu : ∀ i, u (σ i) = u i)
    (heq : squareNorm b = squareNorm (fun i => a (σ i) - r i)) (k : ℕ) :
    columnPrefix c (fun i => a (σ i) - r i) k ≤ columnPrefix c b k := by
  classical
  letI : Fintype (Set.range u) := (Set.finite_range u).fintype
  letI : Fintype (Set.range v) := (Set.finite_range v).fintype
  have hw := (h.rangeColors.mapColumnWeight (prefixStep k) (prefixStep_monotone k)).weight_le_of_norm_eq
    σ (fun i => Subtype.ext (hu i)) heq
  change columnWeight (fun i => prefixStep k (c i)) b ≤
    columnWeight (fun i => prefixStep k (c i)) (fun i => a (σ i) - r i) at hw
  rw [columnWeight_prefixStep, columnWeight_prefixStep] at hw
  linarith

theorem columnPrefix_comp_perm (c : ι → ℕ) (b : ι → ℤ) (σ : Equiv.Perm ι)
    (hc : ∀ i, c (σ i) = c i) (k : ℕ) :
    columnPrefix c (b ∘ σ) k = columnPrefix c b k := by
  have heq : (fun i => if c i < k then b (σ i) else 0) =
      (fun i => if c i < k then b i else 0) ∘ σ := by
    funext i
    simp only [Function.comp_apply, hc]
  unfold columnPrefix
  simp only [Function.comp_apply]
  rw [heq]
  exact Equiv.sum_comp σ (fun i : ι => if c i < k then b i else (0 : ℤ))

theorem columnPrefix_rowPermutation_le (row : ι → κ) (c : ι → ℕ) (b : ι → ℤ)
    (h : ∀ j, Monovary (fun i : {i // row i = j} => (c i : ℤ))
      (fun i : {i // row i = j} => b i))
    (ρ : Equiv.Perm ι) (hr : ∀ i, row (ρ i) = row i) (k : ℕ) :
    columnPrefix c b k ≤ columnPrefix c (b ∘ ρ) k := by
  have hs : ∀ j, Monovary (fun i : {i // row i = j} => prefixStep k (c i))
      (fun i : {i // row i = j} => b i) := by
    intro j i l hil
    exact prefixStep_monotone k (h j hil)
  have hw := columnWeight_rowPermutation_le row (fun i => prefixStep k (c i)) b hs ρ hr
  rw [columnWeight_prefixStep, columnWeight_prefixStep] at hw
  linarith

theorem youngExponent_prefix_le {μ : YoungDiagram}
    (T : YoungTableau μ) (b : Fin μ.card →₀ ℕ)
    (hb : ∀ j, Monovary (fun i : {i // rowIndex T i = j} => (colIndex T i : ℤ))
      (fun i : {i // rowIndex T i = j} => intExponent b i))
    (σ : colSubgroup T) (ρ : rowSubgroup T) (k : ℕ) :
    columnPrefix (colIndex T) (intExponent b) k ≤
      columnPrefix (colIndex T) (intExponent (youngExponent T b σ ρ)) k := by
  change columnPrefix _ _ _ ≤ columnPrefix _ ((intExponent b ∘ ρ.val.symm) ∘ σ.val.symm) _
  rw [columnPrefix_comp_perm _ _ σ.val.symm
    (mem_colSubgroup.mp ((colSubgroup T).inv_mem σ.property))]
  exact columnPrefix_rowPermutation_le (rowIndex T) (colIndex T) (intExponent b) hb
    ρ.val.symm (mem_rowSubgroup.mp ((rowSubgroup T).inv_mem ρ.property)) k

theorem higherSpecht_supported_prefix_le {R : Type*} [CommRing R] {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) (beta : Fin μ.card →₀ ℕ)
    (hbeta : (higherSpechtPolynomial (R := R) S T).coeff beta ≠ 0) (k : ℕ) :
    columnPrefix (colIndex T.toTableau) (intExponent (transportedCocharge S T.toTableau)) k ≤
      columnPrefix (colIndex T.toTableau) (intExponent beta) k := by
  obtain ⟨σ, ρ, rfl⟩ := youngApply_coeff_ne_zero T.toTableau _ beta hbeta
  exact youngExponent_prefix_le T.toTableau _ (transportedCocharge_rowMonovary S T.toTableau)
    σ ρ k

theorem sum_prefixIndicators (c n : ℕ) :
    (∑ k ∈ Finset.range n, if c < k + 1 then (1 : ℤ) else 0) = (n - c : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      split_ifs <;> omega

theorem sum_columnPrefixes (c : ι → ℕ) (b : ι → ℤ) (n : ℕ)
    (hc : ∀ i, c i ≤ n) :
    (∑ k ∈ Finset.range n, columnPrefix c b (k + 1)) =
      (n : ℤ) * (∑ i, b i) - columnWeight (fun i => c i) b := by
  unfold columnPrefix columnWeight
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ k ∈ Finset.range n, if c i < k + 1 then b i else 0) =
        (∑ k ∈ Finset.range n, if c i < k + 1 then (1 : ℤ) else 0) * b i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> simp
    _ = (n : ℤ) * b i - (c i : ℤ) * b i := by
      rw [sum_prefixIndicators, Nat.cast_sub (hc i)]
      ring

theorem columnWeight_eq_of_prefix_eq (c : ι → ℕ) (b d : ι → ℤ) (n : ℕ)
    (hc : ∀ i, c i < n)
    (hprefix : ∀ k : Fin n, columnPrefix c b (k.val + 1) = columnPrefix c d (k.val + 1)) :
    columnWeight (fun i => c i) b = columnWeight (fun i => c i) d := by
  by_cases hn : n = 0
  · subst n
    haveI : IsEmpty ι := ⟨fun i => (Nat.not_lt_zero _ (hc i)).elim⟩
    simp only [columnWeight, Finset.univ_eq_empty, Finset.sum_empty]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hlast := hprefix ⟨n - 1, by omega⟩
    have hnm : n - 1 + 1 = n := by omega
    simp only [hnm, columnPrefix, if_pos (hc _)] at hlast
    have hsum : (∑ k ∈ Finset.range n, columnPrefix c b (k + 1)) =
        ∑ k ∈ Finset.range n, columnPrefix c d (k + 1) :=
      Finset.sum_congr rfl (fun k hk => hprefix ⟨k, Finset.mem_range.mp hk⟩)
    rw [sum_columnPrefixes c b n (fun i => (hc i).le),
      sum_columnPrefixes c d n (fun i => (hc i).le), hlast] at hsum
    linarith

def normPrefixKey (c : ι → ℕ) (n : ℕ) (b : ι → ℤ) : Lex (Fin (n + 1) → ℤ) :=
  toLex (Fin.cases (squareNorm b) (fun k : Fin n => -columnPrefix c b (k.val + 1)))

theorem norm_le_of_prefixKey_le (c : ι → ℕ) (n : ℕ) (b d : ι → ℤ)
    (h : normPrefixKey c n b ≤ normPrefixKey c n d) : squareNorm b ≤ squareNorm d := by
  rcases lt_or_eq_of_le h with h | h
  · obtain ⟨i, hbefore, hi⟩ := h
    by_cases hi0 : i = 0
    · subst i
      exact hi.le
    · have h0 := hbefore 0 (Fin.pos_iff_ne_zero.mpr hi0)
      exact h0.le
  · exact (congrArg (fun z : Lex (Fin (n + 1) → ℤ) => z 0) h).le

theorem prefix_eq_of_prefixKey_le_of_bounds (c : ι → ℕ) (n : ℕ) (b d : ι → ℤ)
    (hkey : normPrefixKey c n d ≤ normPrefixKey c n b)
    (hnorm : squareNorm b = squareNorm d)
    (hprefix : ∀ k : Fin n, columnPrefix c d (k.val + 1) ≤ columnPrefix c b (k.val + 1)) :
    ∀ k : Fin n, columnPrefix c b (k.val + 1) = columnPrefix c d (k.val + 1) := by
  have hrev : normPrefixKey c n b ≤ normPrefixKey c n d := by
    apply Pi.toLex_monotone
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hnorm.le
    · exact neg_le_neg (hprefix k)
  have heq := le_antisymm hrev hkey
  intro k
  exact neg_injective (congrArg (fun z : Lex (Fin (n + 1) → ℤ) => z k.succ) heq)

/-- This key is literally the norm followed by the negatives of all initial
column sums, in their stated order. -/
def higherSpechtPrefixKey {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (T : YoungTableau μ) : Lex (Fin (μ.card + 1) → ℤ) :=
  normPrefixKey (colIndex T) μ.card (intExponent (transportedCocharge S T))

/-- Theorem 3.2 in the manuscript's exact lexicographic order.  The proof
first derives every prefix bound from the actual coefficient equation, and
only then invokes the already established equality detector. -/
theorem theorem_3_2_prefix_offDiagonal {K : Type*} [Field K] [CharZero K]
    {μ : YoungDiagram} (S S' T : StandardYoungTableau μ) (hne : S ≠ S')
    (hkey : higherSpechtPrefixKey S' T.toTableau ≤ higherSpechtPrefixKey S T.toTableau) :
    higherSpechtApolarFunctional (K := K) S T.toTableau (higherSpechtPolynomial S' T) = 0 := by
  change _ * higherSpechtCoefficientFunctional (R := K) S T.toTableau _ = 0
  suffices hz : higherSpechtCoefficientFunctional (R := K) S T.toTableau
      (higherSpechtPolynomial S' T) = 0 by rw [hz, mul_zero]
  rw [higherSpechtCoefficientFunctional, witnessCoefficient_apply]
  apply Finset.sum_eq_zero
  intro τ hτ
  split_ifs with hr
  · suffices hz : (higherSpechtPolynomial (R := K) S' T).coeff
        (permutedExponent (insertionAlpha S T.toTableau) τ.val -
          insertionRejectionExponent S T.toTableau) = 0 by rw [hz, mul_zero]
    by_contra hn
    let b := intExponent (transportedCocharge S T.toTableau)
    let d := intExponent (transportedCocharge S' T.toTableau)
    let beta := intExponent (permutedExponent (insertionAlpha S T.toTableau) τ.val -
      insertionRejectionExponent S T.toTableau)
    have hw := insertion_rearrangementWitness S T.toTableau
    letI : Fintype (Set.range (insertionColumn S T.toTableau)) :=
      (Set.finite_range _).fintype
    letI : Fintype (Set.range (fun i =>
        (insertionColumn S T.toTableau i, insertionRejections S T.toTableau i))) :=
      (Set.finite_range _).fintype
    have hbeta : beta = fun i => intExponent (insertionAlpha S T.toTableau) (τ.val i) -
        intExponent (insertionRejectionExponent S T.toTableau) i := intExponent_sub hr
    have hnb : squareNorm b ≤ squareNorm beta := by
      rw [hbeta]
      exact hw.rangeColors.norm_le τ.val (fun i => Subtype.ext (τ.property i))
    have hnd : squareNorm beta ≤ squareNorm d := (higherSpecht_triangularSupport S' T).norm _ hn
    have hdb : squareNorm d ≤ squareNorm b := norm_le_of_prefixKey_le _ _ d b hkey
    have hnbe : squareNorm b = squareNorm beta := le_antisymm hnb (hnd.trans hdb)
    have hnbd : squareNorm b = squareNorm d := le_antisymm (hnb.trans hnd) hdb
    have hp (k : ℕ) : columnPrefix (colIndex T.toTableau) d k ≤
        columnPrefix (colIndex T.toTableau) b k := by
      refine (higherSpecht_supported_prefix_le S' T _ hn k).trans ?_
      change columnPrefix (colIndex T.toTableau) beta k ≤
        columnPrefix (colIndex T.toTableau) b k
      rw [hbeta] at hnbe ⊢
      exact hw.prefix_le_of_norm_eq τ.val (fun i => τ.property i) hnbe k
    have heq := prefix_eq_of_prefixKey_le_of_bounds (colIndex T.toTableau) μ.card b d
      hkey hnbd (fun k => hp (k.val + 1))
    have hcw : columnWeight (fun i => colIndex T.toTableau i) b =
        columnWeight (fun i => colIndex T.toTableau i) d := by
      apply columnWeight_eq_of_prefix_eq _ b d μ.card _ heq
      intro i
      rw [colIndex_def]
      have hl := YoungDiagram.mem_iff_lt_rowLen.mp (T.toTableau.symm i).property
      apply hl.trans_le
      rw [μ.rowLen_eq_card]
      change (μ.cells.filter fun c => c.1 = (T.toTableau.symm i).val.1).card ≤ μ.cells.card
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hweighted : higherSpechtPairingKey S' T.toTableau ≤
        higherSpechtPairingKey S T.toTableau := by
      apply Prod.Lex.toLex_le_toLex'.mpr
      exact ⟨hnbd.ge, fun _ => hcw.ge⟩
    -- The weighted criterion proves each summand vanishes, not merely their sum.
    have hsame := contribution_same_filling hw.rangeColors τ.val
      (fun i => Subtype.ext (τ.property i)) hbeta hnd
      ((higherSpecht_triangularSupport S' T).weight _ hn)
      ((higherSpecht_triangularSupport S' T).orbit _ hn) hweighted
      (fun i => (rowIndex T.toTableau i : ℤ))
      (rowIndex_injective_on_intColumn T.toTableau)
      (transportedCocharge_intColumnMonovary S T.toTableau)
      (transportedCocharge_intColumnMonovary S' T.toTableau)
    exact hne (transportedCocharge_injective T.toTableau (intExponent_injective hsame))
  · rfl

end HigherSpecht
end
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/ElementaryNormBounds.lean -/



/-!
# The exact norm extremum for a product of elementary factors

An exponent of an elementary product is a sum of zero-one subset vectors.
Its squared norm is the sum of all pairwise intersection cardinalities.
Combining the intersection bound with the largest-subset rearrangement
gives the norm extremum and its equality conditions, including the actual
nesting of all subsets in an extremal term.
-/

noncomputable section

open Finset Equiv Function

namespace HigherSpecht

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]

def subsetMultiplicity (A : F → Finset ι) (i : ι) : ℤ :=
  ∑ f, if i ∈ A f then 1 else 0

theorem subsetMultiplicity_dot (A : F → Finset ι) (a : ι → ℤ) :
    (∑ i, a i * subsetMultiplicity A i) = ∑ f, ∑ i ∈ A f, a i := by
  simp only [subsetMultiplicity, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

theorem subsetMultiplicity_squareNorm (A : F → Finset ι) :
    squareNorm (subsetMultiplicity A) =
      ∑ f, ∑ g, ((A f ∩ A g).card : ℤ) := by
  unfold squareNorm
  simp only [pow_two]
  rw [subsetMultiplicity_dot]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [subsetMultiplicity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem card_inter_le_min_card (A B : Finset ι) : (A ∩ B).card ≤ min A.card B.card :=
  le_min (Finset.card_le_card Finset.inter_subset_left)
    (Finset.card_le_card Finset.inter_subset_right)

theorem card_inter_eq_min_card_iff_nested (A B : Finset ι) :
    (A ∩ B).card = min A.card B.card ↔ A ⊆ B ∨ B ⊆ A := by
  constructor
  · intro h
    rcases le_total A.card B.card with hcard | hcard
    · rw [min_eq_left hcard] at h
      have heq : A ∩ B = A := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left h.ge
      left
      rw [← heq]
      exact Finset.inter_subset_right
    · rw [min_eq_right hcard] at h
      have heq : A ∩ B = B := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right h.ge
      right
      rw [← heq]
      exact Finset.inter_subset_left
  · rintro (h | h)
    · rw [Finset.inter_eq_left.mpr h, min_eq_left (Finset.card_le_card h)]
    · rw [Finset.inter_eq_right.mpr h, min_eq_right (Finset.card_le_card h)]

theorem subsetMultiplicity_norm_le_nested (A B : F → Finset ι)
    (hcard : ∀ f, (A f).card = (B f).card)
    (hnested : ∀ f g, B f ⊆ B g ∨ B g ⊆ B f) :
    squareNorm (subsetMultiplicity A) ≤ squareNorm (subsetMultiplicity B) := by
  rw [subsetMultiplicity_squareNorm, subsetMultiplicity_squareNorm]
  apply Finset.sum_le_sum
  intro f hf
  apply Finset.sum_le_sum
  intro g hg
  apply Int.ofNat_le.mpr
  rw [(card_inter_eq_min_card_iff_nested (B f) (B g)).mpr (hnested f g)]
  simpa only [hcard] using card_inter_le_min_card (A f) (A g)

theorem nested_of_subsetMultiplicity_norm_eq (A B : F → Finset ι)
    (hcard : ∀ f, (A f).card = (B f).card)
    (hnested : ∀ f g, B f ⊆ B g ∨ B g ⊆ B f)
    (heq : squareNorm (subsetMultiplicity A) = squareNorm (subsetMultiplicity B)) :
    ∀ f g, A f ⊆ A g ∨ A g ⊆ A f := by
  rw [subsetMultiplicity_squareNorm, subsetMultiplicity_squareNorm] at heq
  have hle (f g : F) : ((A f ∩ A g).card : ℤ) ≤ (B f ∩ B g).card := by
    apply Int.ofNat_le.mpr
    rw [(card_inter_eq_min_card_iff_nested (B f) (B g)).mpr (hnested f g)]
    simpa only [hcard] using card_inter_le_min_card (A f) (A g)
  have hout := Finset.sum_eq_sum_iff_of_le
    (fun f (_ : f ∈ (Finset.univ : Finset F)) => Finset.sum_le_sum
      (fun g (_ : g ∈ (Finset.univ : Finset F)) => hle f g)) |>.mp heq
  intro f g
  have hin := (Finset.sum_eq_sum_iff_of_le
    (fun g (_ : g ∈ (Finset.univ : Finset F)) => hle f g)).mp (hout f (mem_univ f))
  apply (card_inter_eq_min_card_iff_nested (A f) (A g)).mp
  have hnat : (A f ∩ A g).card = (B f ∩ B g).card := by
    exact_mod_cast hin g (mem_univ g)
  rw [hnat, (card_inter_eq_min_card_iff_nested (B f) (B g)).mpr (hnested f g), hcard, hcard]

theorem sum_subset_le_largest_of_card_eq (A B : Finset ι) (a : ι → ℤ)
    (hcard : A.card = B.card)
    (hmax : ∀ i ∈ B, ∀ j ∉ B, a j ≤ a i) :
    (∑ i ∈ A, a i) ≤ ∑ i ∈ B, a i := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq B A hcard.symm
  have h := sum_permuted_le_sum_of_largest B a hmax σ
  have hmap : (∑ i ∈ B, a (σ i)) = ∑ i ∈ A, a i := by
    simpa only [Finset.sum_map, Equiv.coe_toEmbedding] using
      congrArg (fun s : Finset ι => ∑ i ∈ s, a i) hσ
  exact hmap ▸ h

theorem subsetMultiplicity_dot_le_largest (A B : F → Finset ι) (a : ι → ℤ)
    (hcard : ∀ f, (A f).card = (B f).card)
    (hmax : ∀ f, ∀ i ∈ B f, ∀ j ∉ B f, a j ≤ a i) (σ : Equiv.Perm ι) :
    (∑ i, a (σ i) * subsetMultiplicity A i) ≤ ∑ i, a i * subsetMultiplicity B i := by
  rw [subsetMultiplicity_dot, subsetMultiplicity_dot]
  apply Finset.sum_le_sum
  intro f hf
  have h := sum_subset_le_largest_of_card_eq ((A f).map σ.toEmbedding) (B f) a
    (by simpa only [Finset.card_map] using hcard f) (hmax f)
  simpa only [Finset.sum_map, Equiv.coe_toEmbedding] using h

theorem squareNorm_add (a b : ι → ℤ) :
    squareNorm (fun i => a i + b i) = squareNorm a + squareNorm b + 2 * ∑ i, a i * b i := by
  unfold squareNorm
  calc
    (∑ i, (a i + b i) ^ 2) = ∑ i, (a i ^ 2 + b i ^ 2 + 2 * (a i * b i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The complete norm inequality for every literal subset choice in every
elementary factor, and every permutation of the base filling. -/
theorem elementaryProduct_norm_le (A B : F → Finset ι) (a : ι → ℤ)
    (hcard : ∀ f, (A f).card = (B f).card)
    (hnested : ∀ f g, B f ⊆ B g ∨ B g ⊆ B f)
    (hmax : ∀ f, ∀ i ∈ B f, ∀ j ∉ B f, a j ≤ a i) (σ : Equiv.Perm ι) :
    squareNorm (fun i => a (σ i) + subsetMultiplicity A i) ≤
      squareNorm (fun i => a i + subsetMultiplicity B i) := by
  have hN := subsetMultiplicity_norm_le_nested A B hcard hnested
  have hdot := subsetMultiplicity_dot_le_largest A B a hcard hmax σ
  rw [squareNorm_add, squareNorm_add, squareNorm_permuted]
  linarith

/-- Equality forces actual nested subsets and a largest-entry choice in
every factor separately; no cancellation between their deficits is possible. -/
theorem elementaryProduct_norm_eq_forces_nested_and_largest
    (A B : F → Finset ι) (a : ι → ℤ)
    (hcard : ∀ f, (A f).card = (B f).card)
    (hnested : ∀ f g, B f ⊆ B g ∨ B g ⊆ B f)
    (hmax : ∀ f, ∀ i ∈ B f, ∀ j ∉ B f, a j ≤ a i) (σ : Equiv.Perm ι)
    (heq : squareNorm (fun i => a (σ i) + subsetMultiplicity A i) =
      squareNorm (fun i => a i + subsetMultiplicity B i)) :
    (∀ f g, A f ⊆ A g ∨ A g ⊆ A f) ∧
      (∀ f, (∑ i ∈ A f, a (σ i)) = ∑ i ∈ B f, a i) := by
  have hN := subsetMultiplicity_norm_le_nested A B hcard hnested
  have hdot := subsetMultiplicity_dot_le_largest A B a hcard hmax σ
  rw [squareNorm_add, squareNorm_add, squareNorm_permuted] at heq
  have hNeq : squareNorm (subsetMultiplicity A) = squareNorm (subsetMultiplicity B) := by linarith
  have hdotEq : (∑ i, a (σ i) * subsetMultiplicity A i) =
      ∑ i, a i * subsetMultiplicity B i := by linarith
  refine ⟨nested_of_subsetMultiplicity_norm_eq A B hcard hnested hNeq, ?_⟩
  rw [subsetMultiplicity_dot, subsetMultiplicity_dot] at hdotEq
  have hEach (f : F) : (∑ i ∈ A f, a (σ i)) ≤ ∑ i ∈ B f, a i := by
    have h := sum_subset_le_largest_of_card_eq ((A f).map σ.toEmbedding) (B f) a
      (by simpa only [Finset.card_map] using hcard f) (hmax f)
    simpa only [Finset.sum_map, Equiv.coe_toEmbedding] using h
  exact fun f => (Finset.sum_eq_sum_iff_of_le
    (fun f (_ : f ∈ (Finset.univ : Finset F)) => hEach f)).mp hdotEq f (mem_univ f)

end HigherSpecht
end
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/ElementaryChoices.lean -/



/-!
# Literal subset choices in the elementary multiplier

This expands the actual elementary product into its subset choices and
identifies the nested largest-coordinate choice with the multiplier
partition's reversed parts.  The expansion is integral and works even when
different choices cancel after changing the coefficient ring.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial Equiv Function TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]

def elementaryChoiceSet (k : F → ℕ) : Finset (F → Finset ι) :=
  Fintype.piFinset fun f => (Finset.univ : Finset ι).powersetCard (k f)

def elementaryChoiceExponent (A : F → Finset ι) : ι →₀ ℕ := ∑ f, subsetExponent (A f)

theorem mem_elementaryChoiceSet (k : F → ℕ) (A : F → Finset ι) :
    A ∈ elementaryChoiceSet k ↔ ∀ f, (A f).card = k f := by
  simp only [elementaryChoiceSet, Fintype.mem_piFinset, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

theorem intExponent_elementaryChoiceExponent (A : F → Finset ι) :
    intExponent (elementaryChoiceExponent A) = subsetMultiplicity A := by
  funext i
  simp only [intExponent, elementaryChoiceExponent, Finsupp.finsetSum_apply,
    subsetExponent_apply, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    subsetMultiplicity]

theorem elementary_product_eq_sum_choices (k : F → ℕ) :
    (∏ f, MvPolynomial.esymm ι R (k f)) =
      ∑ A ∈ elementaryChoiceSet k, MvPolynomial.monomial (elementaryChoiceExponent A) 1 := by
  simp only [MvPolynomial.esymm, prod_X_eq_monomial_subset]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [elementaryChoiceExponent, ← MvPolynomial.monomial_sum_one]

theorem elementary_product_coeff_ne_zero (k : F → ℕ) (beta : ι →₀ ℕ)
    (h : (∏ f, MvPolynomial.esymm ι R (k f)).coeff beta ≠ 0) :
    ∃ A : F → Finset ι, (∀ f, (A f).card = k f) ∧ elementaryChoiceExponent A = beta := by
  rw [elementary_product_eq_sum_choices, MvPolynomial.coeff_sum] at h
  obtain ⟨A, hA, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨A, (mem_elementaryChoiceSet k A).mp hA, ?_⟩
  by_contra hn
  exact hcoeff (by simp only [MvPolynomial.coeff_monomial, if_neg hn])

def upperTail (n k : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => n - k ≤ i.val

@[simp] theorem mem_upperTail {n k : ℕ} (i : Fin n) :
    i ∈ upperTail n k ↔ n - k ≤ i.val := by simp only [upperTail, Finset.mem_filter, mem_univ, true_and]

theorem upperTail_card {n k : ℕ} (hk : k ≤ n) : (upperTail n k).card = k := by
  by_cases hk0 : k = 0
  · subst k
    have he : upperTail n 0 = ∅ := by ext i; simp [mem_upperTail, i.isLt.not_ge]
    simp [he]
  · have hn : n - k < n := by omega
    let i : Fin n := ⟨n - k, hn⟩
    have he : upperTail n k = Finset.Ici i := by
      ext j
      simp only [mem_upperTail, Finset.mem_Ici, Fin.le_def, i]
    rw [he, Fin.card_Ici]
    dsimp only [i]
    omega

theorem upperTail_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) : upperTail n k ⊆ upperTail n l := by
  intro i hi
  simp only [mem_upperTail] at hi ⊢
  omega

theorem upperTail_nested (n k l : ℕ) : upperTail n k ⊆ upperTail n l ∨
    upperTail n l ⊆ upperTail n k := by
  rcases le_total k l with h | h
  · exact Or.inl (upperTail_mono n h)
  · exact Or.inr (upperTail_mono n h)

theorem upperTail_largest {n k : ℕ} (a : Fin n → ℤ) (ha : Monotone a) :
    ∀ i ∈ upperTail n k, ∀ j ∉ upperTail n k, a j ≤ a i := by
  intro i hi j hj
  simp only [mem_upperTail] at hi hj
  apply ha
  change j.val ≤ i.val
  omega

abbrev ElementaryFactorIndex (m : ℕ) (eta : YoungDiagram) :=
  Σ j : Fin m, Fin (eta.rowLen j.val - eta.rowLen (j.val + 1))

def elementaryFactorSize {m : ℕ} {eta : YoungDiagram} (f : ElementaryFactorIndex m eta) : ℕ :=
  f.1.val + 1

theorem elementaryMultiplier_eq_factorProduct (n m : ℕ) (eta : YoungDiagram) :
    elementaryMultiplier (R := R) n m eta.rowLen =
      ∏ f : ElementaryFactorIndex m eta, MvPolynomial.esymm (Fin n) R (elementaryFactorSize f) := by
  rw [Fintype.prod_sigma]
  simp only [elementaryFactorSize, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

theorem partition_reverse_differences_Ico (eta : YoungDiagram) {l m : ℕ} (hlm : l ≤ m) :
    (∑ j ∈ Finset.Ico l m, ((eta.rowLen j - eta.rowLen (j + 1) : ℕ) : ℤ)) =
      (eta.rowLen l : ℤ) - eta.rowLen m := by
  simp_rw [Nat.cast_sub (eta.rowLen_anti _ _ (Nat.le_succ _))]
  have h := Finset.sum_Ico_sub (f := fun j => -(eta.rowLen j : ℤ)) hlm
  simpa only [neg_sub_neg] using h

theorem subsetMultiplicity_upperTails {n m : ℕ} (hmn : m ≤ n) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ m) (i : Fin n) :
    subsetMultiplicity (fun f : ElementaryFactorIndex m eta => upperTail n (elementaryFactorSize f)) i =
      (boostLabel eta n i : ℤ) := by
  unfold subsetMultiplicity
  rw [Fintype.sum_sigma]
  change (∑ j : Fin m, ∑ _ : Fin (eta.rowLen j.val - eta.rowLen (j.val + 1)),
    if i ∈ upperTail n (j.val + 1) then (1 : ℤ) else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (eta.rowLen j - eta.rowLen (j + 1)) •
      (if i ∈ upperTail n (j + 1) then (1 : ℤ) else 0)) m]
  let l := n - 1 - i.val
  have hmem (j : ℕ) (hj : j < m) : i ∈ upperTail n (j + 1) ↔ l ≤ j := by
    rw [mem_upperTail]
    dsimp only [l]
    have := i.isLt
    omega
  have hsum : (∑ j ∈ Finset.range m,
      (eta.rowLen j - eta.rowLen (j + 1) : ℕ) •
        (if i ∈ upperTail n (j + 1) then (1 : ℤ) else 0)) =
        ∑ j ∈ Finset.Ico l m, ((eta.rowLen j - eta.rowLen (j + 1) : ℕ) : ℤ) := by
    calc
      _ = ∑ j ∈ Finset.range m,
          if l ≤ j then ((eta.rowLen j - eta.rowLen (j + 1) : ℕ) : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [hmem j (Finset.mem_range.mp hj)]
        split_ifs <;> simp
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        exact and_comm
  change (∑ j ∈ Finset.range m,
    (eta.rowLen j - eta.rowLen (j + 1) : ℕ) •
      (if i ∈ upperTail n (j + 1) then (1 : ℤ) else 0)) = _
  rw [hsum]
  by_cases hlm : l ≤ m
  · rw [partition_reverse_differences_Ico eta hlm,
      YoungDiagram.rowLen_eq_zero_of_colLen_le heta, Nat.cast_zero, sub_zero]
    rfl
  · rw [Finset.Ico_eq_empty_of_le (le_of_not_ge hlm), Finset.sum_empty,
      boostLabel, YoungDiagram.rowLen_eq_zero_of_colLen_le (heta.trans (le_of_not_ge hlm)), Nat.cast_zero]

/-- The first half of Lemma 4.2 for a literal monomial of the elementary
multiplier and an arbitrary permutation of an increasing base sequence. -/
theorem elementaryMultiplier_supported_norm_bound {n m : ℕ} (hmn : m ≤ n)
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) (a : Fin n → ℤ) (ha : Monotone a)
    (σ : Equiv.Perm (Fin n)) (delta : Fin n →₀ ℕ)
    (hdelta : (elementaryMultiplier (R := R) n m eta.rowLen).coeff delta ≠ 0) :
    squareNorm (fun i => a (σ i) + (delta i : ℤ)) ≤
      squareNorm (fun i => a i + (boostLabel eta n i : ℤ)) := by
  rw [elementaryMultiplier_eq_factorProduct] at hdelta
  obtain ⟨A, hA, rfl⟩ := elementary_product_coeff_ne_zero elementaryFactorSize delta hdelta
  let B := fun f : ElementaryFactorIndex m eta => upperTail n (elementaryFactorSize f)
  have hcard (f : ElementaryFactorIndex m eta) : (A f).card = (B f).card := by
    rw [hA, upperTail_card (by have := f.1.isLt; dsimp [elementaryFactorSize]; omega)]
  have h := elementaryProduct_norm_le A B a hcard
    (fun f g => upperTail_nested _ _ _) (fun f => upperTail_largest a ha) σ
  simpa only [← intExponent_elementaryChoiceExponent, intExponent,
    B, subsetMultiplicity_upperTails hmn eta heta] using h

end HigherSpecht
end
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/ElementaryExtremalContent.lean -/



/-!
# Content and alignment in the extremal elementary layer

Equality in the norm bound gives nested subset choices.  Membership in any
one of those subsets strictly separates their total multiplicities.  Sorting
the resulting exponent therefore sorts both its base and its boost; each
subset becomes the unique terminal segment of its cardinality.  This proves
the exact content assertion without assuming a majorization theorem.
-/

noncomputable section

open Finset Equiv Function

namespace HigherSpecht

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]

theorem largest_of_subset_sum_max (A B : Finset ι) (a : ι → ℤ)
    (hcard : A.card = B.card) (hB : ∀ i ∈ B, ∀ j ∉ B, a j ≤ a i)
    (σ : Equiv.Perm ι) (heq : (∑ i ∈ A, a (σ i)) = ∑ i ∈ B, a i) :
    ∀ i ∈ A, ∀ j ∉ A, a (σ j) ≤ a (σ i) := by
  intro i hi j hj
  let A' := insert j (A.erase i)
  have hj' : j ∉ A.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcard' : A'.card = B.card := by
    dsimp only [A']
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
    have hp := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hle := sum_subset_le_largest_of_card_eq (A'.map σ.toEmbedding) B a
    (by simpa only [Finset.card_map] using hcard') hB
  simp only [Finset.sum_map, Equiv.coe_toEmbedding] at hle
  dsimp only [A'] at hle
  rw [Finset.sum_insert hj'] at hle
  have hsum := Finset.sum_erase_add A (fun x => a (σ x)) hi
  linarith

theorem subsetMultiplicity_alignment (A : F → Finset ι) (a : ι → ℤ)
    (hA : ∀ f, ∀ i ∈ A f, ∀ j ∉ A f, a j ≤ a i) :
    ∀ i j, a i < a j → subsetMultiplicity A i ≤ subsetMultiplicity A j := by
  intro i j hij
  apply Finset.sum_le_sum
  intro f hf
  by_cases hi : i ∈ A f
  · have hj : j ∈ A f := by
      by_contra hn
      exact (not_le_of_gt hij) (hA f i hi j hn)
    simp only [if_pos hi, if_pos hj, le_refl]
  · simp only [if_neg hi]
    split_ifs <;> norm_num

theorem subsetMultiplicity_strict_across_nested_cut (A : F → Finset ι)
    (hnested : ∀ f g, A f ⊆ A g ∨ A g ⊆ A f)
    (f : F) {i j : ι} (hi : i ∈ A f) (hj : j ∉ A f) :
    subsetMultiplicity A j < subsetMultiplicity A i := by
  apply Finset.sum_lt_sum
  · intro g hg
    by_cases hjg : j ∈ A g
    · have hig : i ∈ A g := by
        rcases hnested f g with h | h
        · exact h hi
        · exact (hj (h hjg)).elim
      simp only [if_pos hjg, if_pos hig, le_refl]
    · simp only [if_neg hjg]
      split_ifs <;> norm_num
  · exact ⟨f, mem_univ f, by simp only [if_neg hj, if_pos hi]; norm_num⟩

theorem monotone_components_of_aligned_sum {n : ℕ} (a d : Fin n → ℤ)
    (halign : ∀ i j, a i < a j → d i ≤ d j) (τ : Equiv.Perm (Fin n))
    (hβ : Monotone ((fun i => a i + d i) ∘ τ)) :
    Monotone (a ∘ τ) ∧ Monotone (d ∘ τ) := by
  constructor
  · intro i j hij
    have hsum := hβ hij
    by_contra hn
    have ha : a (τ j) < a (τ i) := lt_of_not_ge hn
    have hd := halign (τ j) (τ i) ha
    dsimp only [Function.comp_apply] at hsum
    linarith
  · intro i j hij
    have hsum := hβ hij
    by_contra hn
    have hd : d (τ j) < d (τ i) := lt_of_not_ge hn
    have ha : a (τ j) ≤ a (τ i) := by
      by_contra hn
      have h := halign (τ i) (τ j) (lt_of_not_ge hn)
      linarith
    dsimp only [Function.comp_apply] at hsum
    linarith

theorem upper_set_eq_upperTail {n : ℕ} (A : Finset (Fin n))
    (hup : ∀ i ∈ A, ∀ j, i ≤ j → j ∈ A) : A = upperTail n A.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have hsub : Finset.Ici i ⊆ A := fun j hj => hup i hi j (Finset.mem_Ici.mp hj)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Ici] at hcard
    rw [mem_upperTail]
    have := i.isLt
    omega
  · rw [upperTail_card (by simpa only [Fintype.card_fin] using Finset.card_le_univ A)]

theorem nested_subset_sorted_eq_upperTail {n : ℕ} (A : F → Finset (Fin n))
    (hnested : ∀ f g, A f ⊆ A g ∨ A g ⊆ A f)
    (τ : Equiv.Perm (Fin n)) (hd : Monotone (subsetMultiplicity A ∘ τ)) (f : F) :
    (A f).map τ.symm.toEmbedding = upperTail n (A f).card := by
  have hmem (i : Fin n) : i ∈ (A f).map τ.symm.toEmbedding ↔ τ i ∈ A f := by
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa only [Equiv.apply_symm_apply] using hj
    · intro hi
      exact ⟨τ i, hi, Equiv.symm_apply_apply τ i⟩
  have hup : ∀ i ∈ (A f).map τ.symm.toEmbedding, ∀ j, i ≤ j →
      j ∈ (A f).map τ.symm.toEmbedding := by
    intro i hi j hij
    apply (hmem j).mpr
    by_contra hj
    have hlt := subsetMultiplicity_strict_across_nested_cut A hnested f ((hmem i).mp hi) hj
    exact (not_lt_of_ge (hd hij)) hlt
  simpa only [Finset.card_map] using upper_set_eq_upperTail ((A f).map τ.symm.toEmbedding) hup

theorem nested_multiplicity_sorted_eq {n : ℕ} (A : F → Finset (Fin n))
    (hnested : ∀ f g, A f ⊆ A g ∨ A g ⊆ A f)
    (τ : Equiv.Perm (Fin n)) (hd : Monotone (subsetMultiplicity A ∘ τ)) :
    subsetMultiplicity A ∘ τ =
      subsetMultiplicity (fun f => upperTail n (A f).card) := by
  funext i
  unfold subsetMultiplicity
  dsimp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro f hf
  have hmem : i ∈ (A f).map τ.symm.toEmbedding ↔ τ i ∈ A f := by
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa only [Equiv.apply_symm_apply] using hj
    · intro hi
      exact ⟨τ i, hi, Equiv.symm_apply_apply τ i⟩
  have htail : i ∈ upperTail n (A f).card ↔ τ i ∈ A f := by
    rw [← nested_subset_sorted_eq_upperTail A hnested τ hd f]
    exact hmem
  simp only [htail]

/-- The complete content conclusion for an extremal subset choice.  The
displayed permutation is the actual sorting permutation of the resulting
exponent, and no equality of multisets is assumed. -/
theorem elementaryProduct_extremal_components {n : ℕ} (A : F → Finset (Fin n))
    (a : Fin n → ℤ) (ha : Monotone a) (σ : Equiv.Perm (Fin n))
    (heq : squareNorm (fun i => a (σ i) + subsetMultiplicity A i) =
      squareNorm (fun i => a i + subsetMultiplicity
        (fun f => upperTail n (A f).card) i)) :
    ∃ τ : Equiv.Perm (Fin n), (a ∘ σ) ∘ τ = a ∧
      subsetMultiplicity A ∘ τ = subsetMultiplicity (fun f => upperTail n (A f).card) := by
  let B := fun f => upperTail n (A f).card
  have hcard (f : F) : (A f).card = (B f).card := by
    rw [upperTail_card (by simpa only [Fintype.card_fin] using Finset.card_le_univ (A f))]
  have hnestedB (f g : F) : B f ⊆ B g ∨ B g ⊆ B f := upperTail_nested _ _ _
  have hmax (f : F) : ∀ i ∈ B f, ∀ j ∉ B f, a j ≤ a i := upperTail_largest a ha
  obtain ⟨hnested, hEach⟩ := elementaryProduct_norm_eq_forces_nested_and_largest
    A B a hcard hnestedB hmax σ heq
  have hmaxA (f : F) : ∀ i ∈ A f, ∀ j ∉ A f, a (σ j) ≤ a (σ i) :=
    largest_of_subset_sum_max (A f) (B f) a (hcard f) (hmax f) σ (hEach f)
  let τ := Tuple.sort (fun i => a (σ i) + subsetMultiplicity A i)
  have hβ : Monotone ((fun i => a (σ i) + subsetMultiplicity A i) ∘ τ) := Tuple.monotone_sort _
  have hc := monotone_components_of_aligned_sum (a ∘ σ) (subsetMultiplicity A)
    (subsetMultiplicity_alignment A (a ∘ σ) hmaxA) τ hβ
  have haeq : (a ∘ σ) ∘ τ = a := by
    have h := Tuple.unique_monotone (f := a) (σ := σ * τ) (τ := 1) hc.1 ha
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Function.comp_def] using h
  have hdeq := nested_multiplicity_sorted_eq A hnested τ hc.2
  exact ⟨τ, haeq, hdeq⟩

theorem elementaryProduct_extremal_content {n : ℕ} (A : F → Finset (Fin n))
    (a : Fin n → ℤ) (ha : Monotone a) (σ : Equiv.Perm (Fin n))
    (heq : squareNorm (fun i => a (σ i) + subsetMultiplicity A i) =
      squareNorm (fun i => a i + subsetMultiplicity
        (fun f => upperTail n (A f).card) i)) :
    ∃ τ : Equiv.Perm (Fin n),
      (fun i => a (σ i) + subsetMultiplicity A i) ∘ τ =
        fun i => a i + subsetMultiplicity (fun f => upperTail n (A f).card) i := by
  obtain ⟨τ, haeq, hdeq⟩ := elementaryProduct_extremal_components A a ha σ heq
  refine ⟨τ, ?_⟩
  funext i
  exact congrArg₂ (· + ·) (congrFun haeq i) (congrFun hdeq i)

theorem elementaryMultiplier_extremal_components {R : Type*} [CommRing R]
    {n m : ℕ} (hmn : m ≤ n) (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m)
    (a : Fin n → ℤ) (ha : Monotone a) (sigma : Equiv.Perm (Fin n))
    (delta : Fin n →₀ ℕ)
    (hdelta : (elementaryMultiplier (R := R) n m eta.rowLen).coeff delta ≠ 0)
    (heq : squareNorm (fun i => a (sigma i) + (delta i : ℤ)) =
      squareNorm (fun i => a i + (boostLabel eta n i : ℤ))) :
    ∃ tau : Equiv.Perm (Fin n), (a ∘ sigma) ∘ tau = a ∧
      (fun i => (delta i : ℤ)) ∘ tau = fun i => (boostLabel eta n i : ℤ) := by
  rw [elementaryMultiplier_eq_factorProduct] at hdelta
  obtain ⟨A, hA, rfl⟩ := elementary_product_coeff_ne_zero elementaryFactorSize delta hdelta
  have ht : subsetMultiplicity (fun f => upperTail n (A f).card) =
      fun i => (boostLabel eta n i : ℤ) := by
    funext i
    simpa only [hA] using subsetMultiplicity_upperTails hmn eta heta i
  have he : squareNorm (fun i => a (sigma i) + subsetMultiplicity A i) =
      squareNorm (fun i => a i + subsetMultiplicity (fun f => upperTail n (A f).card) i) := by
    rw [ht]
    simpa only [← intExponent_elementaryChoiceExponent, intExponent] using heq
  obtain ⟨tau, hbase, hboost⟩ := elementaryProduct_extremal_components A a ha sigma he
  refine ⟨tau, hbase, ?_⟩
  rw [ht] at hboost
  change intExponent (elementaryChoiceExponent A) ∘ tau = _
  rw [intExponent_elementaryChoiceExponent]
  exact hboost

end HigherSpecht
end
end CanonicalSource62

section CanonicalSource63
/- Source: HigherSpecht/BoostedRearrangement.lean -/



/-!
# Prefix minimization in an extremal boosted layer

Norm equality separates an exponent into its original cocharge value and its
boost.  A row permutation first sorts the total values.  Strict separation of
different cocharge levels then sorts those levels too, so they return to their
original row positions.  The remaining permutation acts only inside a fixed
cocharge level.  Two finite rearrangements give every prefix inequality and
the exact weighted-equality case.
-/

noncomputable section

open Finset Equiv Function

namespace HigherSpecht

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem columnWeight_swap (c b : ι → ℤ) {i j : ι} (hij : i ≠ j) :
    columnWeight c (b ∘ Equiv.swap i j) = columnWeight c b +
      (c i - c j) * (b j - b i) := by
  have hp (x : ι) : c x * b (Equiv.swap i j x) = c x * b x +
      (if x = i then c i * (b j - b i) else 0) +
      (if x = j then c j * (b i - b j) else 0) := by
    by_cases hxi : x = i
    · subst x
      simp only [Equiv.swap_apply_left, if_true, if_neg hij]
      ring
    · by_cases hxj : x = j
      · subst x
        simp only [Equiv.swap_apply_right, if_true, if_neg hij.symm]
        ring
      · simp only [Equiv.swap_apply_of_ne_of_ne hxi hxj, if_neg hxi, if_neg hxj, add_zero]
  unfold columnWeight
  simp only [Function.comp_apply, hp, Finset.sum_add_distrib,
    Finset.sum_ite_eq', mem_univ, if_true]
  ring

theorem exists_fiber_sort (row : ι → κ) (c b : ι → ℤ) :
    ∃ omega : Equiv.Perm ι, (∀ i, row (omega i) = row i) ∧
      ∀ j, Monovary (fun i : {i // row i = j} => c i)
        (fun i : {i // row i = j} => b (omega i)) := by
  classical
  obtain ⟨omega, homega, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (colorPermutationGroup row))
    (fun omega => columnWeight c (b ∘ omega.val)) ⟨1, mem_univ 1⟩
  refine ⟨omega.val, omega.property, ?_⟩
  intro j i l hil
  by_contra hn
  have hci : c l.val < c i.val := lt_of_not_ge hn
  have hne : i.val ≠ l.val := by
    intro h
    exact (ne_of_lt hci) (congrArg c h).symm
  have hs : Equiv.swap i.val l.val ∈ colorPermutationGroup row := by
    intro x
    by_cases hxi : x = i.val
    · subst x
      simpa only [Equiv.swap_apply_left] using l.property.trans i.property.symm
    · by_cases hxl : x = l.val
      · subst x
        simpa only [Equiv.swap_apply_right] using i.property.trans l.property.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxl]
  let tau : colorPermutationGroup row := omega * ⟨Equiv.swap i.val l.val, hs⟩
  have hle := hmax tau (mem_univ tau)
  change columnWeight c ((b ∘ omega.val) ∘ Equiv.swap i.val l.val) ≤
    columnWeight c (b ∘ omega.val) at hle
  rw [columnWeight_swap c (b ∘ omega.val) hne] at hle
  have hp : 0 < (c i.val - c l.val) *
      (b (omega.val l.val) - b (omega.val i.val)) := mul_pos (sub_pos.mpr hci) (sub_pos.mpr hil)
  dsimp only [Function.comp_apply] at hle
  linarith

theorem eq_of_fiberOrbit_of_sorted (row : ι → κ) (c : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    {a b : ι → ℤ}
    (ha : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => a i))
    (hb : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => b i))
    (sigma : Equiv.Perm ι) (hsigma : ∀ i, row (sigma i) = row i)
    (heq : a ∘ sigma = b) : a = b := by
  classical
  letI : Fintype (Set.range row) := (Set.finite_range row).fintype
  apply eq_of_columnOrbit_of_sorted (rangeColor row) c _ _ _ sigma _ heq
  · intro j i l hil
    have h := hc j.val (a₁ := ⟨i.val, congrArg Subtype.val i.property⟩)
      (a₂ := ⟨l.val, congrArg Subtype.val l.property⟩) hil
    exact Subtype.ext (congrArg (fun x : {i // row i = j.val} => x.val) h)
  · intro j
    exact (ha j.val).comp_right
      (fun i : {i // rangeColor row i = j} => ⟨i.val, congrArg Subtype.val i.property⟩)
  · intro j
    exact (hb j.val).comp_right
      (fun i : {i // rangeColor row i = j} => ⟨i.val, congrArg Subtype.val i.property⟩)
  · intro i
    exact Subtype.ext (hsigma i)

/-- Both constituent permutations are constructed from the actual extremal
content data. The intermediate sorted exponent is explicitly retained for
the equality argument. -/
theorem boosted_fiber_sort (row : ι → κ) (c a b gamma : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    (ha : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => a i))
    (hbands : ∀ i j, a i < a j → b i < b j)
    (pi rho : Equiv.Perm ι) (hrho : ∀ i, row (rho i) = row i)
    (hgamma : gamma = b ∘ pi) (hbase : a ∘ pi = a ∘ rho) :
    ∃ omega : Equiv.Perm ι, (∀ i, row (omega i) = row i) ∧
      (∀ j, Monovary (fun i : {i // row i = j} => c i)
        (fun i : {i // row i = j} => gamma (omega i))) ∧
      ∀ i, a (pi (omega i)) = a i := by
  obtain ⟨omega, homega, hsort⟩ := exists_fiber_sort row c gamma
  refine ⟨omega, homega, hsort, ?_⟩
  have hsorta : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => a (pi (omega i))) := by
    intro j
    apply Monovary.symm
    intro i l hil
    by_contra hn
    have hab := hbands (pi (omega l.val)) (pi (omega i.val)) (lt_of_not_ge hn)
    have hgb := (hsort j).symm hil
    rw [hgamma] at hgb
    dsimp only [Function.comp_apply] at hgb
    exact (not_lt_of_ge hgb) hab
  have heq : a = (a ∘ pi) ∘ omega :=
    eq_of_fiberOrbit_of_sorted row c hc ha hsorta (rho * omega)
      (fun i => (hrho (omega i)).trans (homega i)) (by
        funext i
        exact (congrFun hbase (omega i)).symm)
  intro i
  exact (congrFun heq i).symm

theorem boosted_monotone_columnWeight_le (row : ι → κ) (c a b gamma : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    (ha : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => a i))
    (hbands : ∀ i j, a i < a j → b i < b j)
    (hb : ∀ j, Monovary (fun i : {i // a i = j} => c i)
      (fun i : {i // a i = j} => b i))
    (pi rho : Equiv.Perm ι) (hrho : ∀ i, row (rho i) = row i)
    (hgamma : gamma = b ∘ pi) (hbase : a ∘ pi = a ∘ rho)
    (w : ℤ → ℤ) (hw : Monotone w) :
    columnWeight (w ∘ c) gamma ≤ columnWeight (w ∘ c) b := by
  obtain ⟨omega, homega, hsort, hfix⟩ :=
    boosted_fiber_sort row c a b gamma hc ha hbands pi rho hrho hgamma hbase
  have hsortw : ∀ j, Monovary (fun i : {i // row i = j} => w (c i))
      (fun i : {i // row i = j} => gamma (omega i)) := by
    intro j i l hil
    exact hw (hsort j hil)
  have hbw : ∀ j, Monovary (fun i : {i // a i = j} => w (c i))
      (fun i : {i // a i = j} => b i) := by
    intro j i l hil
    exact hw (hb j hil)
  have h1 := columnWeight_rowPermutation_le row (w ∘ c) (gamma ∘ omega)
    hsortw omega.symm (fun i => (homega (omega.symm i)).symm.trans
      (congrArg row (Equiv.apply_symm_apply omega i)))
  have h2 := columnWeight_rowPermutation_le a (w ∘ c) b hbw (pi * omega) hfix
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h1
  have h2' : columnWeight (w ∘ c) (gamma ∘ omega) ≤ columnWeight (w ∘ c) b := by
    simpa only [hgamma, Function.comp_def, Equiv.Perm.mul_apply] using h2
  exact h1.trans h2'

theorem boosted_columnWeight_eq_iff (row : ι → κ) (c a b gamma : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => c i))
    (hca : ∀ j, Function.Injective (fun i : {i // a i = j} => c i))
    (ha : ∀ j, Monovary (fun i : {i // row i = j} => c i)
      (fun i : {i // row i = j} => a i))
    (hbands : ∀ i j, a i < a j → b i < b j)
    (hb : ∀ j, Monovary (fun i : {i // a i = j} => c i)
      (fun i : {i // a i = j} => b i))
    (pi rho : Equiv.Perm ι) (hrho : ∀ i, row (rho i) = row i)
    (hgamma : gamma = b ∘ pi) (hbase : a ∘ pi = a ∘ rho) :
    columnWeight c gamma = columnWeight c b ↔ gamma = b := by
  constructor
  · intro heq
    obtain ⟨omega, homega, hsort, hfix⟩ :=
      boosted_fiber_sort row c a b gamma hc ha hbands pi rho hrho hgamma hbase
    have h1 := columnWeight_rowPermutation_le row c (gamma ∘ omega)
      hsort omega.symm (fun i => (homega (omega.symm i)).symm.trans
        (congrArg row (Equiv.apply_symm_apply omega i)))
    have h2 := columnWeight_rowPermutation_le a c b hb (pi * omega) hfix
    have h2' : columnWeight c (gamma ∘ omega) ≤ columnWeight c b := by
      simpa only [hgamma, Function.comp_def, Equiv.Perm.mul_apply] using h2
    simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h1
    have hfirst : columnWeight c ((gamma ∘ omega) ∘ omega.symm) =
        columnWeight c (gamma ∘ omega) := by
      simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
      exact le_antisymm h1 (h2'.trans_eq heq.symm)
    have hg := (columnWeight_rowPermutation_eq_iff row c (gamma ∘ omega) hc hsort
      omega.symm (fun i => (homega (omega.symm i)).symm.trans
        (congrArg row (Equiv.apply_symm_apply omega i)))).mp hfirst
    have hsecond : columnWeight c (b ∘ (pi * omega)) = columnWeight c b := by
      have hs : columnWeight c (gamma ∘ omega) = columnWeight c b :=
        le_antisymm h2' (heq.symm.trans_le h1)
      simpa only [hgamma, Function.comp_def, Equiv.Perm.mul_apply] using hs
    have hbfix := (columnWeight_rowPermutation_eq_iff a c b hca hb (pi * omega) hfix).mp hsecond
    calc
      gamma = gamma ∘ omega := by
        simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hg
      _ = b ∘ (pi * omega) := by
        simp only [hgamma, Function.comp_def, Equiv.Perm.mul_apply]
      _ = b := hbfix
  · rintro rfl
    rfl

theorem boosted_prefix_le (row : ι → κ) (c : ι → ℕ) (a b gamma : ι → ℤ)
    (hc : ∀ j, Function.Injective (fun i : {i // row i = j} => (c i : ℤ)))
    (ha : ∀ j, Monovary (fun i : {i // row i = j} => (c i : ℤ))
      (fun i : {i // row i = j} => a i))
    (hbands : ∀ i j, a i < a j → b i < b j)
    (hb : ∀ j, Monovary (fun i : {i // a i = j} => (c i : ℤ))
      (fun i : {i // a i = j} => b i))
    (pi rho : Equiv.Perm ι) (hrho : ∀ i, row (rho i) = row i)
    (hgamma : gamma = b ∘ pi) (hbase : a ∘ pi = a ∘ rho) (k : ℕ) :
    columnPrefix c b k ≤ columnPrefix c gamma k := by
  have h := boosted_monotone_columnWeight_le row (fun i => (c i : ℤ)) a b gamma hc ha hbands hb
    pi rho hrho hgamma hbase (prefixStep k) (prefixStep_monotone k)
  change columnWeight (fun i => prefixStep k (c i)) gamma ≤
    columnWeight (fun i => prefixStep k (c i)) b at h
  rw [columnWeight_prefixStep, columnWeight_prefixStep] at h
  linarith

end HigherSpecht
end
end CanonicalSource63
