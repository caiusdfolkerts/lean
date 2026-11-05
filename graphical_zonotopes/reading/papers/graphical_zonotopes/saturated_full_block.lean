module

public import Papers.GraphicalZonotopes.SaturatedBookRigidity
public import Papers.GraphicalZonotopes.SaturatedPairBases

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def matchingEquiv (s : ℕ) : Fin (retainedPairs s).card ≃ ↥(retainedPairs s) :=
  (finCongr (Fintype.card_coe (retainedPairs s)).symm).trans (Fintype.equivFin _).symm

def matchingWeight (r : ↥(retainedPairs s)) : ℤ := (pairSum r.1 : ℤ)-1

theorem matchingWeight_positive (r : ↥(retainedPairs s)) : 0<matchingWeight r := by
  have hr := mem_retainedPairs.mp r.2
  have huv : r.1.1.1.1.val<r.1.1.1.2.val := r.1.1.2.1
  have hn := hr.1
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matchingWeight_bound (r : ↥(retainedPairs s)) : matchingWeight r≤(2*s : ℕ) := by
  have hu := r.1.1.1.1.isLt
  have hv := r.1.1.1.2.isLt
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matching_vectors_independent (hs : 5≤s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) => -pairIndicator (group hs r)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  have hr := mem_retainedPairs.mp r.2
  have hmem : ∀ t : ↥(retainedPairs s),r.1∈group hs t ↔ t=r := by
    intro t
    let e : ActivePair (show 2≤s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
    have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
    exact (mem_group_iff hs e t).trans (by rw [hidx])
  have h := congrFun hc r.1
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.zero_apply,smul_eq_mul,
    pairIndicator,hmem,neg_ite,neg_zero,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true] at h
  linarith

theorem matching_classes_independent (hs : 5≤s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) =>
      blockClass univ (-pairIndicator (group hs r))) := by
  apply blockClass_linearIndependent_of_reference univ (referencePair (show 2≤s by omega))
    _ (matching_vectors_independent hs)
  intro r
  simp [pairIndicator,group_reference_not_mem]

theorem matching_weighted_vector (hs : 5≤s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • (-pairIndicator (group hs r)))=
      (fun _ : HubPair s => (1 : ℝ))-endpointLabels univ := by
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,smul_eq_mul,mul_neg,sum_neg_distrib]
  by_cases he : e=referencePair (show 2≤s by omega)
  · subst e
    rw [sum_group_indicator_reference]
    norm_num [endpointLabels,referencePair,natPair,orderedPair]
  · let a : ActivePair (show 2≤s by omega) := ⟨e,he⟩
    rw [show (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ)*pairIndicator (group hs r) e)=
      (matchingWeight (groupIndex hs a) : ℝ) from sum_group_indicator hs _ a]
    have hsum := groupPair_sum hs a
    change pairSum (groupIndex hs a).1=pairSum e at hsum
    simp only [matchingWeight,Int.cast_sub,Int.cast_natCast,Int.cast_one]
    rw [hsum]
    simp only [pairSum,Nat.cast_add,endpointLabels]
    ring

theorem matching_weighted_class (hs : 5≤s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • blockClass univ (-pairIndicator (group hs r)))=
      -blockClass univ (endpointLabels univ) := by
  simp only [←map_smul,←map_sum]
  rw [matching_weighted_vector,map_sub]
  have hz : blockClass univ (fun _ : HubPair s => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff univ (referencePair (show 2≤s by omega)) _).mpr ⟨1,fun _ => rfl⟩
  rw [hz,zero_sub]

def matchingPureBlock (hs : 5≤s) :
    WeightedPureBlock (univ : Finset (Fin s)) (2*s : ℕ)
      (-blockClass univ (endpointLabels univ)) (retainedPairs s).card where
  column j := -pairIndicator (group hs (matchingEquiv s j))
  realizable j := group_realizable hs (matchingEquiv s j)
  weight j := matchingWeight (matchingEquiv s j)
  positive j := matchingWeight_positive _
  bounded j := matchingWeight_bound _
  independent := (matching_classes_independent hs).comp (matchingEquiv s) (matchingEquiv s).injective
  weighted_sum := ((matchingEquiv s).sum_comp _).trans (matching_weighted_class hs)

theorem matchingPureBlock_rigidity (hs : 5≤s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (t : Fin (retainedPairs s).card → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d+∑ j,t j • (matchingPureBlock hs).column j)=0) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let w : ↥(retainedPairs s) → ℝ := fun r => t ((matchingEquiv s).symm r)
  have he : (∑ j,t j • (matchingPureBlock hs).column j)=
      -(∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r)) := by
    change (∑ j,t j • (-pairIndicator (group hs (matchingEquiv s j))))=_
    simp only [smul_neg,sum_neg_distrib]
    congr 1
    have hh := (matchingEquiv s).sum_comp (fun r => w r • pairIndicator (group hs r))
    simpa only [w,Equiv.symm_apply_apply] using hh
  rw [he,←sub_eq_add_neg] at hz
  exact (full_block_unique hs d h0 w hz).1

end GraphicalZonotopes.BooleanModule.Saturated
