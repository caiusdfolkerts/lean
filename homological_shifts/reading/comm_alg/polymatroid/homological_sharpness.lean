import CommAlg.Polymatroid.IdealBridge
import CommAlg.Polymatroid.UniformSharpness

/-! # The sharp uniform-Veronese example in every positive degree

The ideal is the squarefree Veronese ideal in `i+1` variables. Its exact
generators are identified, and every homological shift assertion uses
the genuine derived-Tor definition on actual powers of that ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def squarefreeVeroneseIdeal (k : Type u) [CommRing k] (V : Type u)
    [Fintype V] [LinearOrder V] (d : ℕ) : Ideal (MvPolynomial V k) :=
  rankIdeal k (uniformRank V d)

theorem squarefreeVeronese_polymatroidal (d : ℕ) :
    IsPolymatroidalIdeal (squarefreeVeroneseIdeal k V d) :=
  isPolymatroidalIdeal_rankIdeal _

/-- The generating monomials are exactly the squarefree monomials of
degree `d`, whenever `d` is at most the number of variables. -/
theorem squarefreeVeronese_generators (d : ℕ) (hd : d ≤ Fintype.card V) (a : Exponent V) :
    a ∈ rankBases (uniformRank V d) ↔ a.degree = d ∧ ∀ j, a j ≤ 1 := by
  have he : uniformPowerRank V d 1 = uniformRank V d := by
    apply RankFunction.ext_fun
    intro A
    simp
  rw [← he, mem_rankBases, isRankBase_uniformPower_iff d 1 hd]
  simp

theorem squarefreeVeronese_power_rank (d s : ℕ) :
    squarefreeVeroneseIdeal k V d ^ s = rankIdeal k (uniformPowerRank V d s) :=
  (rankIdeal_scale k (uniformRank V d) s).symm

/-- Proposition 4.2, vanishing at every positive power strictly below `i`. -/
theorem squarefreeVeronese_shift_below {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ s)
      ((squarefreeVeronese_polymatroidal i).pow s) i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i s)
    (squarefreeVeronese_power_rank i s) i]
  have he : universalHomologicalRank (uniformPowerRank V i s) i =
      homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  have hlt := uniform_homologicalRank_lt hi hs hsi hcard
  simp only [rankShiftIdeal, he, if_neg (Nat.ne_of_lt hlt)]

theorem monomial_constExponent_eq_prod_pow (i : ℕ) :
    MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) =
      (∏ j : V, MvPolynomial.X j) ^ i := by
  rw [← Finset.prod_pow]
  rw [MvPolynomial.prod_X_pow]
  have he : (constExponent i : Exponent V) = Finsupp.indicator univ (fun _ _ => i) := by
    ext j
    simp
  exact congrArg (fun a : Exponent V => MvPolynomial.monomial a (1 : k)) he

/-- Proposition 4.2, the exact principal ideal at the sharp threshold. -/
theorem squarefreeVeronese_shift_at_threshold {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i i)
    (squarefreeVeronese_power_rank i i) i]
  have he : universalHomologicalRank (uniformPowerRank V i i) i =
      homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  rw [rankShiftIdeal, he, if_pos (uniform_homologicalRank_top hi hcard), rankIdeal,
    uniform_threshold_rankBases hi hcard, monomialIdeal]
  simp only [Finset.coe_singleton, Set.image_singleton, monomial_constExponent_eq_prod_pow]

theorem squarefreeVeronese_shift_at_threshold_ne_bot {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i ≠ ⊥ := by
  rw [squarefreeVeronese_shift_at_threshold hi hcard,
    ← monomial_constExponent_eq_prod_pow]
  intro he
  have hm : MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) ∈
      Ideal.span {MvPolynomial.monomial (constExponent i : Exponent V) (1 : k)} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [he, Ideal.mem_bot] at hm
  simpa using hm

end CommAlg.Polymatroid
