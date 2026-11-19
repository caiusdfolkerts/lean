module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

/-!
# Convex open sets with countably many points removed

This is the small-domain version of Mathlib's two-segment proof of path
connectedness of a countable complement. The intermediate point is chosen
close to the midpoint, so both segments remain in the prescribed convex set.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Metric
open scoped Convex Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joinedIn_convex_sdiff_countable {U S : Set E}
    (hU : Convex ℝ U) (hopen : IsOpen U) (hS : S.Countable)
    (hdim : 1 < Module.rank ℝ E) {a b : E}
    (ha : a ∈ U \ S) (hb : b ∈ U \ S) : JoinedIn (U \ S) a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by dsimp [c,x]; module
  have Ib : c + x = b := by dsimp [c,x]; module
  have hc : c ∈ U := by
    convert hU ha.1 hb.1 (a := (2 : ℝ)⁻¹) (b := (2 : ℝ)⁻¹)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> dsimp [c] <;> module
  have hx : x ≠ 0 := by simpa [x] using sub_ne_zero.mpr hab.symm
  obtain ⟨y,hy⟩ := exists_linearIndependent_pair_of_one_lt_rank hdim hx
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.mpr
    have N : {c + x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty,Ib] using hb.2
    rw [inter_assoc,inter_comm S,inter_assoc,inter_self,← inter_assoc,
      ← subset_empty_iff,← N]
    exact inter_subset_inter_left _
      (segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm c).subset
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.mpr
    have N : {c - x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty,Ia] using ha.2
    rw [inter_assoc,inter_comm S,inter_assoc,inter_self,← inter_assoc,
      ← subset_empty_iff,← N]
    apply inter_subset_inter_left
    apply Eq.subset
    rw [sub_eq_add_neg _ x]
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert hy.units_smul ![-1,1] using 1
    simp [← List.ofFn_inj]
  have hsmall : {t : ℝ | c + t • y ∈ U} ∈ 𝓝 (0 : ℝ) := by
    have hf : Continuous (fun t : ℝ => c + t • y) := by fun_prop
    exact hf.continuousAt (hopen.mem_nhds (by simpa using hc))
  obtain ⟨t,ht,hzU⟩ := ((A.union B).dense_compl ℝ).inter_nhds_nonempty hsmall
  let z := c + t • y
  simp only [compl_union,mem_inter_iff,mem_compl_iff,mem_setOf_eq,
    not_nonempty_iff_eq_empty] at ht
  have JA : JoinedIn (U \ S) a z := by
    apply JoinedIn.of_segment_subset
    intro p hp
    refine ⟨hU.segment_subset ha.1 hzU hp,?_⟩
    have hdis : [a -[ℝ] z] ∩ S = ∅ := by simpa only [Ia,z] using ht.2
    intro hpS
    exact Set.notMem_empty p (hdis ▸ ⟨hp,hpS⟩)
  have JB : JoinedIn (U \ S) b z := by
    apply JoinedIn.of_segment_subset
    intro p hp
    refine ⟨hU.segment_subset hb.1 hzU hp,?_⟩
    have hdis : [b -[ℝ] z] ∩ S = ∅ := by simpa only [Ib,z] using ht.1
    intro hpS
    exact Set.notMem_empty p (hdis ▸ ⟨hp,hpS⟩)
  exact JA.trans JB.symm

theorem isPreconnected_convex_sdiff_countable {U S : Set E}
    (hU : Convex ℝ U) (hopen : IsOpen U) (hS : S.Countable)
    (hdim : 1 < Module.rank ℝ E) : IsPreconnected (U \ S) := by
  rcases (U \ S).eq_empty_or_nonempty with h | ⟨a,ha⟩
  · rw [h]
    exact isPreconnected_empty
  · exact (show IsPathConnected (U \ S) from
      ⟨a,ha,fun b hb => joinedIn_convex_sdiff_countable hU hopen hS hdim ha hb⟩).isConnected.isPreconnected

end NormalProjective.Planar
