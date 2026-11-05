module

public import Papers.GraphicalZonotopes.MatchingPureModules
public import Papers.GraphicalZonotopes.BookQuadrilateralPattern
public import Papers.GraphicalZonotopes.PairColumnRefinement

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

abbrev HubPair (s : ℕ) := PairIn (univ : Finset (Fin s))

def natPair {s : ℕ} (i j : ℕ) (hij : i<j) (hj : j<s) : HubPair s :=
  orderedPair univ ⟨i,lt_trans hij hj⟩ ⟨j,hj⟩ hij (mem_univ _) (mem_univ _)

def pairSum {s : ℕ} (e : HubPair s) : ℕ := e.1.1.1.val+e.1.1.2.val

def Retained {s : ℕ} (e : HubPair s) : Prop :=
  ¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
  ¬(e.1.1.1.val=1 ∧ e.1.1.2.val<s-1) ∧
  ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)

instance {s : ℕ} (e : HubPair s) : Decidable (Retained e) := inferInstanceAs
  (Decidable (¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
    ¬(e.1.1.1.val=1 ∧ e.1.1.2.val<s-1) ∧
    ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)))

def retainedPairs (s : ℕ) : Finset (HubPair s) := univ.filter Retained

@[simp] theorem mem_retainedPairs {s : ℕ} {e : HubPair s} :
    e∈retainedPairs s ↔ Retained e := by simp [retainedPairs]

def referencePair {s : ℕ} (hs : 2≤s) : HubPair s := natPair 0 1 (by omega) (by omega)

theorem pair_eq_reference {s : ℕ} (hs : 2≤s) (e : HubPair s) :
    e=referencePair hs ↔ e.1.1.1.val=0 ∧ e.1.1.2.val=1 := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl⟩
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))

abbrev ActivePair {s : ℕ} (hs : 2≤s) := {e : HubPair s // e≠referencePair hs}

def groupPair {s : ℕ} (hs : 5≤s) (e : ActivePair (show 2≤s by omega)) : HubPair s :=
  if h : e.1.1.1.1.val=1 ∧ e.1.1.1.2.val<s-1 then
    natPair 0 (1+e.1.1.1.2.val) (by omega) (by omega)
  else if h : e.1.1.1.1.val=2 ∧ e.1.1.1.2.val=3 then
    if hs6 : 6≤s then natPair 0 5 (by omega) (by omega)
    else natPair 1 4 (by omega) (by omega)
  else e.1

theorem groupPair_retained {s : ℕ} (hs : 5≤s)
    (e : ActivePair (show 2≤s by omega)) : Retained (groupPair hs e) := by
  have huv : e.1.1.1.1.val<e.1.1.1.2.val := e.1.1.2.1
  have hne : ¬(e.1.1.1.1.val=0 ∧ e.1.1.1.2.val=1) := by
    intro h
    exact e.2 ((pair_eq_reference (show 2≤s by omega) e.1).mpr h)
  unfold groupPair
  split_ifs with h1 h2 h6
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · exact ⟨hne,h1,h2⟩

theorem groupPair_sum {s : ℕ} (hs : 5≤s)
    (e : ActivePair (show 2≤s by omega)) : pairSum (groupPair hs e)=pairSum e.1 := by
  unfold groupPair
  split_ifs with h1 h2 h6 <;> simp only [pairSum,natPair,orderedPair] <;> omega

theorem retained_not_reference {s : ℕ} (hs : 2≤s) {e : HubPair s}
    (he : Retained e) : e≠referencePair hs := by
  intro h
  exact he.1 ((pair_eq_reference hs e).mp h)

theorem groupPair_of_retained {s : ℕ} (hs : 5≤s) {e : HubPair s} (he : Retained e) :
    groupPair hs ⟨e,retained_not_reference (by omega) he⟩=e := by
  simp only [groupPair,he.2.1,he.2.2,dite_false]

def group {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) : Finset (HubPair s) :=
  univ.filter (fun e => ∃ h : e≠referencePair (show 2≤s by omega),groupPair hs ⟨e,h⟩=r.1)

theorem mem_group {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) (e : HubPair s) :
    e∈group hs r ↔ ∃ h : e≠referencePair (show 2≤s by omega),groupPair hs ⟨e,h⟩=r.1 := by
  classical
  simp only [group,mem_filter,mem_univ,true_and]

theorem group_nonempty {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) :
    (group hs r).Nonempty := by
  refine ⟨r.1,(mem_group hs r r.1).mpr ?_⟩
  have hr := mem_retainedPairs.mp r.2
  exact ⟨retained_not_reference (by omega) hr,groupPair_of_retained hs hr⟩

theorem group_reference_not_mem {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) :
    referencePair (show 2≤s by omega)∉group hs r := by
  intro h
  obtain ⟨hn,_⟩ := (mem_group hs r _).mp h
  exact hn rfl

theorem group_pairSum {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s))
    {e : HubPair s} (he : e∈group hs r) : pairSum e=pairSum r.1 := by
  obtain ⟨hn,hg⟩ := (mem_group hs r e).mp he
  rw [←hg,groupPair_sum]

theorem equal_sum_matching {s : ℕ} (A : Finset (HubPair s)) (t : ℕ)
    (hA : ∀ e∈A,pairSum e=t) : IsPairMatching A := by
  intro e he f hf hne
  apply disjoint_left.mpr
  intro a hae haf
  have hsum : e.1.1.1.val+e.1.1.2.val=f.1.1.1.val+f.1.1.2.val :=
    (hA e he).trans (hA f hf).symm
  have heord : e.1.1.1.val<e.1.1.2.val := e.1.2.1
  have hford : f.1.1.1.val<f.1.1.2.val := f.1.2.1
  simp only [pairVertices,mem_insert,mem_singleton] at hae haf
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals rcases hae with hae | hae <;> rcases haf with haf | haf
  all_goals have haev := congrArg Fin.val hae
  all_goals have hafv := congrArg Fin.val haf
  all_goals omega

theorem group_matching {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) :
    IsPairMatching (group hs r) :=
  equal_sum_matching _ (pairSum r.1) (fun _ he => group_pairSum hs r he)

theorem group_realizable {s : ℕ} (hs : 5≤s) (r : ↥(retainedPairs s)) :
    PureRealizable (univ : Finset (Fin s)) (-pairIndicator (group hs r)) :=
  pureRealizable_negative_matching (by simpa using (show 3≤s by omega)) _
    (group_matching hs r)

theorem group_unique {s : ℕ} (hs : 5≤s) (r t : ↥(retainedPairs s))
    {e : HubPair s} (hr : e∈group hs r) (ht : e∈group hs t) : r=t := by
  obtain ⟨hn,he⟩ := (mem_group hs r e).mp hr
  obtain ⟨hm,hf⟩ := (mem_group hs t e).mp ht
  exact Subtype.ext (he.symm.trans hf)

theorem group_cover {s : ℕ} (hs : 5≤s) (e : HubPair s)
    (he : e≠referencePair (show 2≤s by omega)) : ∃ r : ↥(retainedPairs s),e∈group hs r := by
  let r : ↥(retainedPairs s) := ⟨groupPair hs ⟨e,he⟩,
    mem_retainedPairs.mpr (groupPair_retained hs ⟨e,he⟩)⟩
  exact ⟨r,(mem_group hs r e).mpr ⟨he,rfl⟩⟩

end GraphicalZonotopes.BooleanModule.Saturated
