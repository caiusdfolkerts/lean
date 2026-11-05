import CommAlg.Polymatroid.RankIdeal

/-! # Finite integer base families and their actual polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsRankBase (g : RankFunction V) (a : Exponent V) : Prop :=
  a.degree = g Finset.univ ∧ UpperFeasible g a

def constExponent (n : ℕ) : Exponent V := Finsupp.equivFunOnFinite.symm (fun _ => n)

@[simp] theorem constExponent_apply (n : ℕ) (i : V) : constExponent n i = n := rfl

def rankBases (g : RankFunction V) : Family V :=
  (Finset.Iic (constExponent (g Finset.univ))).filter (IsRankBase g)

@[simp] theorem mem_rankBases (g : RankFunction V) (a : Exponent V) :
    a ∈ rankBases g ↔ IsRankBase g a := by
  simp only [rankBases, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (coordinate_le_degree a i).trans h.1.le

theorem subsetSum_add (a b : Exponent V) (U : Finset V) :
    subsetSum (a + b) U = subsetSum a U + subsetSum b U := by
  simp [subsetSum, Finset.sum_add_distrib]

theorem rankBases_equigenerated (g : RankFunction V) :
    Equigenerated (rankBases g) (g Finset.univ) := by
  intro a ha
  exact ((mem_rankBases g a).mp ha).1

theorem rankBases_nonempty (g : RankFunction V) : (rankBases g).Nonempty := by
  have hf : LowerFeasible g.lower (constExponent (g Finset.univ)) := by
    intro U
    by_cases hU : U.Nonempty
    · obtain ⟨i, hi⟩ := hU
      exact (g.lower_le U).trans (by
        simpa only [subsetSum, constExponent_apply] using
          Finset.single_le_sum (f := fun _ : V => g Finset.univ)
            (fun j _ => Nat.zero_le _) hi)
    · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [he]
  obtain ⟨a, _, hadeg, ha⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
    g.lower_univ g.lower_le hf
  exact ⟨a, (mem_rankBases g a).mpr
    ⟨hadeg, (upperFeasible_iff_lowerFeasible g hadeg).mpr ha⟩⟩

theorem rankBases_polymatroidal (g : RankFunction V) : IsPolymatroidal (rankBases g) := by
  refine ⟨⟨g Finset.univ, rankBases_equigenerated g⟩, ?_⟩
  intro a ha b hb i hi
  have ha := (mem_rankBases g a).mp ha
  have hb := (mem_rankBases g b).mp hb
  have hla := (upperFeasible_iff_lowerFeasible g ha.1).mp ha.2
  have hlb := (upperFeasible_iff_lowerFeasible g hb.1).mp hb.2
  obtain ⟨j, hj, hex⟩ := feasible_exchange g.lower_supermodular hla hlb
    (ha.1.trans hb.1.symm) hi
  have hd := (exchange_degree a i j (by omega)).trans ha.1
  exact ⟨j, hj, (mem_rankBases g _).mpr
    ⟨hd, (upperFeasible_iff_lowerFeasible g hd).mpr hex⟩⟩

theorem contains_rankBases_iff (g : RankFunction V) (a : Exponent V) :
    Contains (rankBases g) a ↔ LowerFeasible g.lower a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    have hb := (mem_rankBases g b).mp hb
    exact ((upperFeasible_iff_lowerFeasible g hb.1).mp hb.2 U).trans
      (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    obtain ⟨b, hba, hbdeg, hb⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
      g.lower_univ g.lower_le ha
    exact ⟨b, (mem_rankBases g b).mpr
      ⟨hbdeg, (upperFeasible_iff_lowerFeasible g hbdeg).mpr hb⟩, hba⟩

theorem rankBases_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) :
    rankBases (canonicalRank B hBne d hdeg hB) = B := by
  have htop : upperRank B Finset.univ = d := by
    obtain ⟨a, ha, he⟩ := upperRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg a ha] using he.symm
  ext a
  rw [mem_rankBases, mem_iff_canonical_rank B hBne d hdeg hB]
  change (a.degree = upperRank B Finset.univ ∧ _) ↔ _
  rw [htop]
  rfl

def rankIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) : Ideal (MvPolynomial V k) :=
  monomialIdeal k (rankBases g)

theorem monomial_mem_rankIdeal_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (g : RankFunction V) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g ↔ LowerFeasible g.lower a := by
  rw [rankIdeal, monomial_mem_iff, contains_rankBases_iff]

end CommAlg.Polymatroid
