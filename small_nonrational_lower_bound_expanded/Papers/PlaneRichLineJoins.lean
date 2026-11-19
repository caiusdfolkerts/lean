module
public import Papers.PlaneDependentTriples

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace Papers.RationalityTen.PlaneRationalization

open SmallTripleCores

theorem DefiningPair.join_support {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v) :
    lineSupport S p (B.join p) = T := by
  let l := richLineCovector hp ⟨T,hT⟩
  have hl : l ≠ 0 := richLineCovector_ne_zero hp ⟨T,hT⟩
  have ha : B.left ∈ S := richLine_subset hT (Finset.mem_of_mem_erase B.left_mem)
  have hb : B.right ∈ S := richLine_subset hT (Finset.mem_of_mem_erase B.right_mem)
  have hab := hp.2 B.left ha B.right hb B.ne
  have hn : B.join p ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hab
  have hdep : ¬ LinearIndependent ℝ ![l,B.join p] := by
    intro h
    apply independent_incidence_pair_impossible l (B.join p) (p B.left) (p B.right) h hab
    · exact (richLines_realization hp).incident ⟨T,hT⟩ B.left
        (Finset.mem_of_mem_erase B.left_mem)
    · exact (richLines_realization hp).incident ⟨T,hT⟩ B.right
        (Finset.mem_of_mem_erase B.right_mem)
    · rw [DefiningPair.join,dotProduct_comm]
      exact dot_self_cross _ _
    · rw [DefiningPair.join,dotProduct_comm]
      exact dot_cross_self _ _
  rw [LinearIndependent.pair_iff' hl] at hdep
  push_neg at hdep
  obtain ⟨c,hc⟩ := hdep
  have hc0 : c ≠ 0 := by
    intro hc0
    exact hn (by simpa [hc0] using hc.symm)
  rw [← hc,lineSupport_smul l hc0]
  exact richLineCovector_support hp ⟨T,hT⟩

theorem DefiningPair.distinct_joins_independent
    {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T U : Triple}
    (hT : T ∈ richLines S p) (hU : U ∈ richLines S p)
    {v : Fin 8} (B : DefiningPair T v) (C : DefiningPair U v) (hTU : T ≠ U) :
    LinearIndependent ℝ ![B.join p,C.join p] := by
  have hps : IndependentProjectivePoints (S.erase v) p :=
    ⟨fun i hi => hp.1 i (Finset.mem_of_mem_erase hi),
      fun i hi j hj hij => hp.2 i (Finset.mem_of_mem_erase hi)
        j (Finset.mem_of_mem_erase hj) hij⟩
  by_contra h
  rw [LinearIndependent.pair_iff' (B.join_ne_zero hT hps)] at h
  push_neg at h
  obtain ⟨c,hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro hc0
    exact C.join_ne_zero hU hps (by simpa [hc0] using hc.symm)
  apply hTU
  rw [← B.join_support hp hT,← C.join_support hp hU,← hc,lineSupport_smul _ hc0]

theorem DefiningPair.continuous_join {T : Triple} {v : Fin 8} (B : DefiningPair T v) :
    Continuous B.join := by
  change Continuous (fun q : Fin 8→V => crossProduct (q B.left) (q B.right))
  simpa only [Function.comp_def] using
    (continuous_cross.comp ((continuous_apply B.left : Continuous
      (fun q : Fin 8→V => q B.left)).prodMk (continuous_apply B.right)))

theorem DefiningPair.rational_join {T : Triple} {v : Fin 8} (B : DefiningPair T v)
    {q : Fin 8 → V} (hq : RatConfiguration q) : RatVector (B.join q) :=
  (hq B.left).cross (hq B.right)

end Papers.RationalityTen.PlaneRationalization
