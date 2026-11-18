module

public import Papers.GraphicalZonotopes.SaturatedBookPartitionCount
public import Papers.GraphicalZonotopes.BookCircuitAssembly

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def activeNatPair (hs : 5≤s) (i j : ℕ) (hij : i<j) (hj : j<s)
    (hne : ¬(i=0 ∧ j=1)) : ActivePair (show 2≤s by omega) :=
  ⟨natPair i j hij hj,by
    intro h
    exact hne ((pair_eq_reference (show 2≤s by omega) _).mp h)⟩

theorem groupPair_03_12 (hs : 5≤s) :
    groupPair hs (activeNatPair hs 0 3 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 2 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 2<s-1 by omega)]

theorem groupPair_04_13 (hs : 5≤s) :
    groupPair hs (activeNatPair hs 0 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 3 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 3<s-1 by omega)]

theorem groupPair_14_23 (hs : 5≤s) :
    groupPair hs (activeNatPair hs 1 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 2 3 (by omega) (by omega) (by omega)) := by
  by_cases hs6 : 6≤s
  · simp [groupPair,activeNatPair,natPair,orderedPair,hs6,(show 4<s-1 by omega)]
  · have hs5 : s=5 := by omega
    subst s
    simp [groupPair,activeNatPair,natPair,orderedPair]

theorem groupPair_step (hs : 5≤s) (j : ℕ) (hj : 5≤j) (hjs : j<s) :
    groupPair hs (activeNatPair hs 0 j (by omega) hjs (by omega))=
    groupPair hs (activeNatPair hs 1 (j-1) (by omega) (by omega) (by omega)) := by
  have he : 1+(j-1)=j := by omega
  simp [groupPair,activeNatPair,natPair,orderedPair,he,(show j≠1 by omega),
    (show j-1<s-1 by omega)]

/-- The matching partition retains exactly the endpoint comparisons needed
for full arithmetic-progression rigidity; all other pair pieces may be split. -/
theorem grouped_endpoint_rigidity (hs : 5≤s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0)
    (hgroup : ∀ e f : ActivePair (show 2≤s by omega),groupPair hs e=groupPair hs f →
      d e.1.1.1.1+d e.1.1.1.2=d f.1.1.1.1+d f.1.1.1.2) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j<s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have h03 : D 0+D 3=D 1+D 2 := by
    have h := hgroup _ _ (groupPair_03_12 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0<s by omega),(show 1<s by omega),
      (show 2<s by omega),(show 3<s by omega)] using h
  have h04 : D 0+D 4=D 1+D 3 := by
    have h := hgroup _ _ (groupPair_04_13 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0<s by omega),(show 1<s by omega),
      (show 3<s by omega),(show 4<s by omega)] using h
  have h14 : D 1+D 4=D 2+D 3 := by
    have h := hgroup _ _ (groupPair_14_23 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 1<s by omega),(show 2<s by omega),
      (show 3<s by omega),(show 4<s by omega)] using h
  have hstep : ∀ j,5≤j → j<s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    have h := hgroup _ _ (groupPair_step hs j hj hjs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0<s by omega),(show 1<s by omega),
      hjs,(show j-1<s by omega)] using h
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0<s by omega)] using h0) h03 h04 h14 hstep
  intro a
  have ha := h a.val a.isLt
  rw [hD a] at ha
  simpa [D,(show 1<s by omega)] using ha

def groupIndex (hs : 5≤s) (e : ActivePair (show 2≤s by omega)) : ↥(retainedPairs s) :=
  ⟨groupPair hs e,mem_retainedPairs.mpr (groupPair_retained hs e)⟩

theorem mem_group_iff (hs : 5≤s) (e : ActivePair (show 2≤s by omega))
    (r : ↥(retainedPairs s)) : e.1∈group hs r ↔ r=groupIndex hs e := by
  rw [mem_group]
  constructor
  · rintro ⟨hn,hg⟩
    exact Subtype.ext hg.symm
  · rintro rfl
    exact ⟨e.2,rfl⟩

theorem sum_group_indicator (hs : 5≤s) (w : ↥(retainedPairs s) → ℝ)
    (e : ActivePair (show 2≤s by omega)) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e.1)=w (groupIndex hs e) := by
  simp only [pairIndicator,mem_group_iff,mul_ite,mul_one,mul_zero,
    sum_ite_eq',mem_univ,ite_true]

theorem sum_group_indicator_reference (hs : 5≤s) (w : ↥(retainedPairs s) → ℝ) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) (referencePair (show 2≤s by omega)))=0 := by
  simp only [pairIndicator,group_reference_not_mem,ite_false,mul_zero,sum_const_zero]

/-- Every zero full-block relation has the prescribed positive scales. -/
theorem full_block_unique (hs : 5≤s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (w : ↥(retainedPairs s) → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d-∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r))=0) :
    (∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩) ∧
    (∀ r : ↥(retainedPairs s),w r=((pairSum r.1 : ℝ)-1)*d ⟨1,by omega⟩) := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff univ (referencePair (show 2≤s by omega)) _).mp hz
  have hrow : ∀ e : HubPair s,d e.1.1.1+d e.1.1.2-
      ∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e=c := by
    intro e
    simpa only [Pi.sub_apply,endpointCoefficients,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hc e
  have hc1 : c=d ⟨1,by omega⟩ := by
    have h := hrow (referencePair (show 2≤s by omega))
    rw [sum_group_indicator_reference] at h
    change d ⟨0,by omega⟩+d ⟨1,by omega⟩-0=c at h
    simpa only [h0,zero_add,sub_zero] using h.symm
  have hactive : ∀ e : ActivePair (show 2≤s by omega),
      d e.1.1.1.1+d e.1.1.1.2-w (groupIndex hs e)=c := by
    intro e
    simpa only [sum_group_indicator] using hrow e.1
  have hd := grouped_endpoint_rigidity hs d h0 (by
    intro e f hef
    have hidx : groupIndex hs e=groupIndex hs f := Subtype.ext hef
    have he := hactive e
    have hf := hactive f
    rw [hidx] at he
    linarith)
  refine ⟨hd,?_⟩
  intro r
  have hr := mem_retainedPairs.mp r.2
  let e : ActivePair (show 2≤s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
  have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
  have h := hactive e
  rw [hidx,hc1] at h
  change d r.1.1.1.1+d r.1.1.1.2-w r=d ⟨1,by omega⟩ at h
  simp only [pairSum,Nat.cast_add]
  nlinarith [hd r.1.1.1.1,hd r.1.1.1.2]

end GraphicalZonotopes.BooleanModule.Saturated
