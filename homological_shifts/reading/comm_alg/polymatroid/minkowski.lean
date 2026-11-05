import CommAlg.Polymatroid.RankBases
import CommAlg.Polymatroid.IntegerSandwich

/-! # Integral Minkowski decomposition of polymatroid bases -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rank_base_decompose (g h : RankFunction V) {a : Exponent V}
    (ha : IsRankBase (g.add h) a) :
    ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  let p : Finset V → ℤ := fun U => (subsetSum a U : ℤ) - h U
  let q : Finset V → ℤ := fun U => g U
  have hp0 : p ∅ = 0 := by simp [p]
  have hq0 : q ∅ = 0 := by simp [q]
  have hp : ∀ U W, p U + p W ≤ p (U ∪ W) + p (U ∩ W) := by
    intro U W
    have hs : (h (U ∪ W) : ℤ) + h (U ∩ W) ≤ h U + h W := by
      exact_mod_cast h.submodular U W
    have hm : (subsetSum a (U ∪ W) : ℤ) + subsetSum a (U ∩ W) =
        subsetSum a U + subsetSum a W := by
      exact_mod_cast (subsetSum_union_inter a U W).symm
    dsimp [p]
    omega
  have hq : ∀ U W, q (U ∪ W) + q (U ∩ W) ≤ q U + q W := by
    intro U W
    dsimp [q]
    exact_mod_cast g.submodular U W
  have hpq : ∀ U, p U ≤ q U := by
    intro U
    have hU : subsetSum a U ≤ g U + h U := ha.2 U
    have hz : (subsetSum a U : ℤ) ≤ g U + h U := by exact_mod_cast hU
    dsimp [p, q]
    omega
  obtain ⟨bZ, hbZ⟩ := integer_sandwich p q hp0 hq0 hp hq hpq
  have hadeg : a.degree = g Finset.univ + h Finset.univ := ha.1
  have hbtotal : (∑ i, bZ i) = (g Finset.univ : ℤ) := by
    have hb := hbZ Finset.univ
    dsimp [p, q] at hb
    rw [subsetSum_univ, hadeg] at hb
    push_cast at hb
    omega
  have hb0 : ∀ i, 0 ≤ bZ i := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).2
    have hg : (g (Finset.univ.erase i) : ℤ) ≤ g Finset.univ := by
      exact_mod_cast g.monotone (Finset.erase_subset _ _)
    change (∑ j ∈ Finset.univ.erase i, bZ j) ≤ (g (Finset.univ.erase i) : ℤ) at hb
    omega
  have hbaZ : ∀ i, bZ i ≤ (a i : ℤ) := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).1
    have hh : (h (Finset.univ.erase i) : ℤ) ≤ h Finset.univ := by
      exact_mod_cast h.monotone (Finset.erase_subset _ _)
    have haSum : (subsetSum a (Finset.univ.erase i) : ℤ) + a i = a.degree := by
      exact_mod_cast (show subsetSum a (Finset.univ.erase i) + a i = a.degree by
        simpa only [subsetSum, Finsupp.degree_eq_sum] using
          Finset.sum_erase_add Finset.univ a (Finset.mem_univ i))
    have hdegree : (a.degree : ℤ) = g Finset.univ + h Finset.univ := by exact_mod_cast hadeg
    dsimp [p] at hb
    omega
  let b : Exponent V := Finsupp.equivFunOnFinite.symm (fun i => (bZ i).toNat)
  have hbcast : ∀ i, (b i : ℤ) = bZ i := fun i => Int.toNat_of_nonneg (hb0 i)
  have hbsum : ∀ U, (subsetSum b U : ℤ) = ∑ i ∈ U, bZ i := by
    intro U
    simp only [subsetSum, Nat.cast_sum, hbcast]
  have hbdeg : b.degree = g Finset.univ := by
    have ht := hbsum Finset.univ
    rw [subsetSum_univ, hbtotal] at ht
    exact_mod_cast ht
  have hble : b ≤ a := by
    intro i
    have ht := hbaZ i
    rw [← hbcast i] at ht
    exact_mod_cast ht
  have hbupper : UpperFeasible g b := by
    intro U
    have ht := (hbZ U).2
    change (∑ i ∈ U, bZ i) ≤ (g U : ℤ) at ht
    rw [← hbsum U] at ht
    exact_mod_cast ht
  let c := a - b
  have hcb : c + b = a := tsub_add_cancel_of_le hble
  have hcdeg : c.degree = h Finset.univ := by
    have ht := congrArg Finsupp.degree hcb
    rw [map_add, hbdeg, hadeg] at ht
    omega
  have hcupper : UpperFeasible h c := by
    intro U
    have ht := (hbZ U).1
    have hs := congrArg (fun z : Exponent V => subsetSum z U) hcb
    rw [subsetSum_add] at hs
    have hsZ : (subsetSum c U : ℤ) + subsetSum b U = subsetSum a U := by exact_mod_cast hs
    dsimp [p] at ht
    rw [← hbsum U] at ht
    have hcZ : (subsetSum c U : ℤ) ≤ h U := by omega
    exact_mod_cast hcZ
  exact ⟨b, c, ⟨hbdeg, hbupper⟩, ⟨hcdeg, hcupper⟩, by simpa only [add_comm] using hcb.symm⟩

theorem rank_base_add {g h : RankFunction V} {b c : Exponent V}
    (hb : IsRankBase g b) (hc : IsRankBase h c) : IsRankBase (g.add h) (b + c) := by
  constructor
  · change (b + c).degree = g Finset.univ + h Finset.univ
    rw [map_add, hb.1, hc.1]
  · intro U
    change subsetSum (b + c) U ≤ g U + h U
    rw [subsetSum_add]
    exact Nat.add_le_add (hb.2 U) (hc.2 U)

theorem rank_base_minkowski (g h : RankFunction V) (a : Exponent V) :
    IsRankBase (g.add h) a ↔
      ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  refine ⟨rank_base_decompose g h, ?_⟩
  rintro ⟨b, c, hb, hc, rfl⟩
  exact rank_base_add hb hc

theorem rankBases_add (g h : RankFunction V) :
    rankBases (g.add h) = ((rankBases g).product (rankBases h)).image (fun bc => bc.1 + bc.2) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, c, hb, hc, he⟩ := rank_base_decompose g h ((mem_rankBases _ _).mp ha)
    exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr
      ⟨(mem_rankBases _ _).mpr hb, (mem_rankBases _ _).mpr hc⟩, he.symm⟩
  · intro ha
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    exact (mem_rankBases _ _).mpr (rank_base_add ((mem_rankBases _ _).mp hb)
      ((mem_rankBases _ _).mp hc))

end CommAlg.Polymatroid
