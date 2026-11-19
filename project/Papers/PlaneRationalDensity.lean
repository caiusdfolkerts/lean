module
public import Papers.PlaneRichLineJoins
public import Mathlib.Order.Filter.Finite

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace Papers.RationalityTen.PlaneRationalization

open SmallTripleCores

structure ReinsertChart (S : Finset (Fin 8)) (p : Fin 8 → V) (v : Fin 8)
    (B : ∀ T, T ∈ throughPoint S p v → DefiningPair T v) where
  value : ((Fin 8 → V) × V) → V
  continuousAt_base : ContinuousAt value (p,p v)
  value_base : value (p,p v) = p v
  rational_value : ∀ q w, RatConfiguration q → RatVector w → RatVector (value (q,w))
  incident_value : ∀ q w, IndependentProjectivePoints (S.erase v) q →
    ∀ T (hT : T ∈ throughPoint S p v), dotProduct ((B T hT).join q) (value (q,w)) = 0

set_option maxHeartbeats 1000000 in
/-- A concrete rational projection chart for zero, one, or two original rich lines. -/
theorem exists_reinsertChart
    {S : Finset (Fin 8)} {p : Fin 8 → V} {v : Fin 8}
    (hp : IndependentProjectivePoints S p) (hv : v ∈ S)
    (hdegree : degree (richLines S p) v ≤ 2)
    (B : ∀ T, T ∈ throughPoint S p v → DefiningPair T v) :
    Nonempty (ReinsertChart S p v B) := by
  classical
  let C := throughPoint S p v
  have hcard : C.card ≤ 2 := hdegree
  have hps : IndependentProjectivePoints (S.erase v) p :=
    ⟨fun i hi => hp.1 i (Finset.mem_of_mem_erase hi),
      fun i hi j hj hij => hp.2 i (Finset.mem_of_mem_erase hi)
        j (Finset.mem_of_mem_erase hj) hij⟩
  by_cases hC0 : C = ∅
  · refine ⟨{
      value := Prod.snd
      continuousAt_base := continuousAt_snd
      value_base := rfl
      rational_value := fun _ _ _ hw => hw
      incident_value := ?_ }⟩
    intro q w hq T hT
    have : T ∈ C := hT
    simpa [hC0] using this
  by_cases hC1 : C.card = 1
  · obtain ⟨T,hT⟩ := Finset.card_eq_one.mp hC1
    have hTC : T ∈ C := by rw [hT]; simp
    have hTrich : T ∈ richLines S p := (Finset.mem_filter.mp hTC).1
    have hvT : v ∈ T := (Finset.mem_filter.mp hTC).2
    let b := B T hTC
    refine ⟨{
      value := fun z => projectOne (b.join z.1) z.2
      continuousAt_base := ?_
      value_base := ?_
      rational_value := ?_
      incident_value := ?_ }⟩
    · have hc : ContinuousAt (fun z : (Fin 8→V)×V => (b.join z.1,z.2)) (p,p v) :=
        ((b.continuous_join.comp continuous_fst).prodMk continuous_snd).continuousAt
      exact (continuousAt_projectOne (b.join p) (p v)
        (b.join_ne_zero hTrich hps)).comp_of_eq hc rfl
    · exact projectOne_fixed _ _ (b.join_incident hp hTrich hvT)
    · intro q w hq hw
      exact (b.rational_join hq).projectOne hw
    · intro q w hq U hU
      have hUT : U = T := by
        have : U ∈ C := hU
        simpa [hT] using this
      subst U
      exact projectOne_incident _ _ (b.join_ne_zero hTrich hq)
  have hC2 : C.card = 2 := by
    have hpos : C.card ≠ 0 := by
      intro hz
      exact hC0 (Finset.card_eq_zero.mp hz)
    omega
  obtain ⟨T,U,hTU,hC⟩ := Finset.card_eq_two.mp hC2
  have hTC : T ∈ C := by rw [hC]; simp
  have hUC : U ∈ C := by rw [hC]; simp
  have hTrich : T ∈ richLines S p := (Finset.mem_filter.mp hTC).1
  have hUrich : U ∈ richLines S p := (Finset.mem_filter.mp hUC).1
  have hvT : v ∈ T := (Finset.mem_filter.mp hTC).2
  have hvU : v ∈ U := (Finset.mem_filter.mp hUC).2
  let b := B T hTC
  let c := B U hUC
  have hbc := b.distinct_joins_independent hp hTrich hUrich c hTU
  refine ⟨{
    value := fun z => projectTwo (b.join z.1) (c.join z.1) z.2
    continuousAt_base := ?_
    value_base := ?_
    rational_value := ?_
    incident_value := ?_ }⟩
  · have hc : ContinuousAt (fun z : (Fin 8→V)×V => ((b.join z.1,c.join z.1),z.2)) (p,p v) :=
      (((b.continuous_join.comp continuous_fst).prodMk
        (c.continuous_join.comp continuous_fst)).prodMk continuous_snd).continuousAt
    exact (continuousAt_projectTwo (b.join p) (c.join p) (p v) hbc).comp_of_eq hc rfl
  · exact projectTwo_fixed _ _ _ hbc
      (b.join_incident hp hTrich hvT) (c.join_incident hp hUrich hvU)
  · intro q w hq hw
    exact (b.rational_join hq).projectTwo (c.rational_join hq) hw
  · intro q w hq W hW
    have hW' : W = T ∨ W = U := by
      have : W ∈ C := hW
      simpa [hC] using this
    rcases hW' with rfl | rfl
    · exact projectTwo_left_incident _ _ _
    · exact projectTwo_right_incident _ _ _

theorem eventually_independentProjectivePoints
    {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) :
    ∀ᶠ q in 𝓝 p, IndependentProjectivePoints S q := by
  have hn : ∀ i : Fin 8, ∀ᶠ q in 𝓝 p, i ∈ S → q i ≠ 0 := by
    intro i
    by_cases hi : i ∈ S
    · exact ((continuous_apply i).continuousAt.eventually_ne (hp.1 i hi)).mono
        fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hi h).elim
  have hpair : ∀ i j : Fin 8, ∀ᶠ q in 𝓝 p,
      i ∈ S → j ∈ S → i ≠ j → LinearIndependent ℝ ![q i,q j] := by
    intro i j
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · by_cases hij : i ≠ j
        · have hc : Continuous (fun q : Fin 8 → V => crossProduct (q i) (q j)) := by
            simpa only [Function.comp_def] using
              (continuous_cross.comp ((continuous_apply i : Continuous
                (fun q : Fin 8→V => q i)).prodMk (continuous_apply j)))
          exact (hc.continuousAt.eventually_ne
            (crossProduct_ne_zero_iff_linearIndependent.mpr (hp.2 i hi j hj hij))).mono
              fun q h _ _ _ => crossProduct_ne_zero_iff_linearIndependent.mp h
        · exact Eventually.of_forall fun _ _ _ h => (hij h).elim
      · exact Eventually.of_forall fun _ _ h _ => (hj h).elim
    · exact Eventually.of_forall fun _ h _ _ => (hi h).elim
  filter_upwards [eventually_all.mpr hn,
    eventually_all.mpr (fun i => eventually_all.mpr (hpair i))] with q hqn hqp
  exact ⟨hqn,fun i hi j hj hij => hqp i j hi hj hij⟩

def RationalZeroConfigurations (S : Finset (Fin 8)) (p : Fin 8 → V) :
    Set (Fin 8 → V) :=
  {q | RatConfiguration q ∧ TripleZeros S p q ∧ IndependentProjectivePoints S q}

/-- Rational point configurations preserving all original dependent triples
are dense at every configuration of at most eight distinct projective points.
Pair independence and nonzero representatives are retained as well. -/
theorem rational_zero_configurations_dense
    (S : Finset (Fin 8)) (p : Fin 8 → V)
    (hp : IndependentProjectivePoints S p) :
    p ∈ closure (RationalZeroConfigurations S p) := by
  classical
  induction S using Finset.strongInductionOn generalizing p with
  | _ S ih =>
    by_cases hS : S = ∅
    · subst S
      simpa [RationalZeroConfigurations,TripleZeros,IndependentProjectivePoints]
        using ratConfiguration_dense p
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨v,hv,hdegree⟩ := exists_point_on_at_most_two_rich_lines hSne hp
    have hps : IndependentProjectivePoints (S.erase v) p :=
      ⟨fun i hi => hp.1 i (Finset.mem_of_mem_erase hi),
        fun i hi j hj hij => hp.2 i (Finset.mem_of_mem_erase hi)
          j (Finset.mem_of_mem_erase hj) hij⟩
    have hrec := ih (S.erase v) (Finset.erase_ssubset hv) p hps
    have hB : ∀ T (hT : T ∈ throughPoint S p v), Nonempty (DefiningPair T v) := by
      intro T hT
      exact exists_definingPair hp (Finset.mem_filter.mp hT).1 v
    let B : ∀ T, T ∈ throughPoint S p v → DefiningPair T v :=
      fun T hT => Classical.choice (hB T hT)
    obtain ⟨R⟩ := exists_reinsertChart hp hv hdegree B
    let F : ((Fin 8 → V) × V) → (Fin 8 → V) :=
      fun z => Function.update z.1 v (R.value z)
    have hFc : ContinuousAt F (p,p v) := by
      apply continuousAt_pi.mpr
      intro i
      by_cases hiv : i = v
      · subst i
        simpa [F] using R.continuousAt_base
      · simpa only [F,Function.update_of_ne hiv,Function.comp_def] using
          ((continuous_apply i).comp continuous_fst).continuousAt
    have hFbase : F (p,p v) = p := by
      simp [F,R.value_base]
    have hprod : (p,p v) ∈ closure
        (RationalZeroConfigurations (S.erase v) p ×ˢ {w : V | RatVector w}) := by
      rw [closure_prod_eq]
      exact ⟨hrec,ratVector_dense (p v)⟩
    have himage : p ∈ closure
        (F '' (RationalZeroConfigurations (S.erase v) p ×ˢ {w : V | RatVector w})) := by
      simpa only [hFbase] using mem_closure_image hFc hprod
    have hsub : F '' (RationalZeroConfigurations (S.erase v) p ×ˢ
        {w : V | RatVector w}) ⊆ {q | RatConfiguration q ∧ TripleZeros S p q} := by
      rintro _ ⟨⟨q,w⟩,⟨hq,hw⟩,rfl⟩
      refine ⟨?_,tripleZeros_update hp hv hq.2.2 hq.2.1 B (R.value (q,w))
        (R.incident_value q w hq.2.2)⟩
      intro i
      by_cases hiv : i = v
      · subst i
        simpa [F] using R.rational_value q w hq.1 hw
      · simpa [F,Function.update_of_ne hiv] using hq.1 i
    have hcl := closure_mono hsub himage
    have hcl' := mem_closure_inter_of_eventually hcl
      (eventually_independentProjectivePoints hp)
    have hsubset : {q | RatConfiguration q ∧ TripleZeros S p q} ∩
        {q | IndependentProjectivePoints S q} ⊆ RationalZeroConfigurations S p := by
      intro q hq
      exact ⟨hq.1.1,hq.1.2,hq.2⟩
    exact closure_mono hsubset hcl'

end Papers.RationalityTen.PlaneRationalization
