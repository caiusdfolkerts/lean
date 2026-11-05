import CommAlg.Polymatroid.RankShiftFormula
import CommAlg.Polymatroid.IdealProducts

/-! # Multiplication of rank-shift ideals, including all inactive coordinates

These are genuine ideal inclusions. The proof uses the exact partition
membership inequalities and is transported to homological shifts by the
separate graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.lower_add (f g : RankFunction V) (U : Finset V) :
    (f.add g).lower U = f.lower U + g.lower U := by
  have hf := f.lower_add_compl U
  have hg := g.lower_add_compl U
  have hfg := (f.add g).lower_add_compl U
  change (f.add g).lower U + (f Uᶜ + g Uᶜ) = f univ + g univ at hfg
  omega

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_add_mem_rankShiftIdeal (f g : RankFunction V) (i : ℕ)
    (b a : Exponent V) (hb : LowerFeasible f.lower b)
    (ha : MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i) :
    MvPolynomial.monomial (b + a) (1 : k) ∈ rankShiftIdeal k (f.add g) i := by
  obtain ⟨haDeg, haLower, haPart⟩ := (monomial_mem_rankShiftIdeal_partition_iff g i a).mp ha
  apply (monomial_mem_rankShiftIdeal_partition_iff (f.add g) i (b + a)).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hbDeg := hb univ
    simp only [RankFunction.lower_univ, subsetSum_univ] at hbDeg
    change (f univ + g univ) + i ≤ (b + a).degree
    rw [map_add]
    omega
  · intro U
    rw [RankFunction.lower_add, subsetSum_add]
    exact Nat.add_le_add (hb U) (haLower U)
  · intro A hA P
    have hpa := haPart A hA P
    have hbf := hb Aᶜ
    have hfcomp := f.lower_add_compl Aᶜ
    simp only [compl_compl] at hfcomp
    have hfpart := f.le_sum_partition P
    change (f univ + g univ) + i + P.parts.card ≤
      subsetSum (b + a) Aᶜ + A.card + ∑ C ∈ P.parts, (f C + g C)
    rw [subsetSum_add, Finset.sum_add_distrib]
    omega

/-- Lemma 3.4 for the exact formula ideals, with no positivity or activity
restriction on either rank. -/
theorem rankIdeal_mul_rankShiftIdeal_le (f g : RankFunction V) (i : ℕ) :
    rankIdeal k f * rankShiftIdeal k g i ≤ rankShiftIdeal k (f.add g) i := by
  rw [rankIdeal, rankShiftIdeal_eq_monomialIdeal, monomialIdeal_mul]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨⟨b, c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb, hc⟩ := mem_product.mp hbc
  have hb' : LowerFeasible f.lower b :=
    (contains_rankBases_iff f b).mp ⟨b, hb, le_rfl⟩
  have hc' : MvPolynomial.monomial c (1 : k) ∈ rankShiftIdeal k g i := by
    rw [rankShiftIdeal_eq_monomialIdeal]
    exact Ideal.subset_span ⟨c, hc, rfl⟩
  exact monomial_add_mem_rankShiftIdeal f g i b c hb' hc'

end Ideals

end CommAlg.Polymatroid
