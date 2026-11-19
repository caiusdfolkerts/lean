module

public import Papers.GraphicalZonotopes.SaturatedFullBlock
public import Papers.GraphicalZonotopes.ScopedAnchorCircuits
public import Papers.GraphicalZonotopes.JunctionStar

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

abbrev fullBlock (hs : 3≤s) : BookBlock (Fin s) :=
  ⟨univ,mem_largeBlocks.mpr ⟨subset_univ _,by simpa using hs⟩⟩

def eta (s : ℕ) : ℝ := (-1 : ℝ)^(s-3)

theorem eta_sign (s : ℕ) : eta s=1 ∨ eta s= -1 := neg_one_pow_eq_or ℝ _

theorem eta_full_factor (hs : 3≤s) : eta s*((-1 : ℝ)^((fullBlock hs).1.card-3))=1 := by
  change eta s*((-1 : ℝ)^((univ : Finset (Fin s)).card-3))=1
  rw [card_univ,Fintype.card_fin]
  change eta s*eta s=1
  rcases eta_sign s with h | h <;> rw [h] <;> norm_num

def anchorFamily (hs : 3≤s) (a : BookAnchor hs) : SetFunction (Fin s) :=
  if eta s=1 then thresholdStar a.1 else junctionStar a.1

theorem anchorFamily_boolean (hs : 3≤s) (a : BookAnchor hs) :
    IsMonotoneBoolean (anchorFamily hs a) := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_boolean _
  · exact junctionStar_boolean (by simpa using (show 2≤s by omega)) _

theorem anchorFamily_essential (hs : 3≤s) (a : BookAnchor hs) (i : Fin s) :
    Essential (anchorFamily hs a) i := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_essential (by simpa using hs) _ _
  · exact junctionStar_essential (by simpa using (show 2≤s by omega)) _ _

theorem anchorFamily_response (hs : 3≤s) (a : BookAnchor hs) :
    responseClass (anchorFamily hs a)=eta s • responseClass (thresholdStar a.1) := by
  unfold anchorFamily
  by_cases h : eta s=1
  · simp only [h,ite_true,one_smul]
  · have he : eta s= -1 := (eta_sign s).resolve_left h
    rw [if_neg h,junctionStar_response_class (by simpa using (show 2≤s by omega)),he,neg_one_smul]

def anchorWeights (hs : 3≤s) (a : BookAnchor hs) : ℤ := (a.1.val : ℤ)

theorem anchorWeights_positive (hs : 3≤s) (a : BookAnchor hs) : 0<anchorWeights hs a := by
  have h := (mem_erase.mp a.2).1
  have hv : a.1.val≠0 := fun he => h (Fin.ext he)
  change 0<(a.1.val : ℤ)
  omega

theorem coefficientExtension_anchor_labels (hs : 3≤s) :
    coefficientExtension ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a => (anchorWeights hs a : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases ha : a=bookZero hs
  · subst a
    simp [coefficientExtension,bookZero]
  · have ham : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨ha,mem_univ _⟩
    simp only [coefficientExtension,dif_pos ham,anchorWeights,Int.cast_natCast]

def pureRank (s : ℕ) (C : BookBlock (Fin s)) : ℕ :=
  if C.1=univ then (retainedPairs s).card else C.1.card.choose 2-1

abbrev anchorSet (hs : 3≤s) : Finset (Fin s) := (univ : Finset (Fin s)).erase (bookZero hs)

theorem pureRank_full (hs : 3≤s) : pureRank s (fullBlock hs)=(retainedPairs s).card := by
  simp [pureRank,fullBlock]

def pureBlock (hs : 5≤s) (C : BookBlock (Fin s)) :
    WeightedPureBlock C.1 (2*s : ℕ)
      (-((eta s*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension (anchorSet (show 3≤s by omega))
          (fun a => (anchorWeights (show 3≤s by omega) a : ℝ)))))) (pureRank s C) := by
  classical
  have hd := coefficientExtension_anchor_labels (show 3≤s by omega)
  by_cases hC : C=fullBlock (show 3≤s by omega)
  · subst C
    let e : Fin (pureRank s (fullBlock (show 3≤s by omega))) ≃
        Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤s by omega))
    refine {
      column := fun j => (matchingPureBlock hs).column (e j)
      realizable := fun j => (matchingPureBlock hs).realizable (e j)
      weight := fun j => (matchingPureBlock hs).weight (e j)
      positive := fun j => (matchingPureBlock hs).positive (e j)
      bounded := fun j => (matchingPureBlock hs).bounded (e j)
      independent := (matchingPureBlock hs).independent.comp e e.injective
      weighted_sum := ?_ }
    rw [e.sum_comp (fun j => ((matchingPureBlock hs).weight j : ℝ) •
      blockClass univ ((matchingPureBlock hs).column j)),
      (matchingPureBlock hs).weighted_sum,eta_full_factor,one_smul,hd]
    rfl
  · have hCu : C.1≠univ := fun h => hC (Subtype.ext h)
    rw [pureRank,if_neg hCu]
    have hε : -(eta s*((-1 : ℝ)^(C.1.card-3)))=1 ∨
        -(eta s*((-1 : ℝ)^(C.1.card-3)))= -1 := by
      rcases eta_sign s with h1 | h1 <;>
        rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h2 | h2 <;> simp [h1,h2]
    let Q := Classical.choice (saturated_pair_basis C.1 (mem_largeBlocks.mp C.2).2 _ hε)
    refine {
      column := Q.column
      realizable := Q.realizable
      weight := Q.weight
      positive := Q.positive
      bounded := Q.bounded
      independent := Q.independent
      weighted_sum := ?_ }
    rw [Q.weighted_sum,hd,neg_smul]
    rfl

theorem pureBlock_full_column (hs : 5≤s)
    (j : Fin (pureRank s (fullBlock (show 3≤s by omega)))) :
    (pureBlock hs (fullBlock (show 3≤s by omega))).column j =
      (matchingPureBlock hs).column (finCongr (pureRank_full (show 3≤s by omega)) j) := by
  unfold pureBlock
  simp only [dite_true] <;> rfl

theorem pureRank_proper (hs : 3≤s) (C : BookBlock (Fin s)) (hC : C≠fullBlock hs) :
    pureRank s C=C.1.card.choose 2-1 := by
  have h : C.1≠univ := fun he => hC (Subtype.ext he)
  simp only [pureRank,h,ite_false]

-- The checked column identity above supplies the data needed below;
-- elaboration need not expand the Boolean realizations of those columns.
attribute [local irreducible] pureBlock matchingPureBlock

/-- The full-clique matching rows force every all-hub anchor scale before any
proper-clique basis is used. -/
theorem general_scale_rigidity (hs : 5≤s) :
    ScopedAnchorRigidity (anchorSet (show 3≤s by omega)) (eta s)
      (anchorWeights (show 3≤s by omega)) (2*s : ℕ) (pureRank s) (pureBlock hs) := by
  intro t ht
  let d := coefficientExtension (anchorSet (show 3≤s by omega)) (fun a => t (.inl a))
  have h0 : d ⟨0,by omega⟩=0 := by
    simp [d,coefficientExtension,anchorSet,bookZero]
  have hfull := ht (fullBlock (show 3≤s by omega))
  dsimp only [scopedAnchorCombination] at hfull
  -- Rewrite the displayed coefficient only. The same coefficient also
  -- occurs in the type of the fixed circuit data, which must stay intact.
  rw (occs := .pos [1]) [eta_full_factor (show 3≤s by omega)] at hfull
  rw [one_smul] at hfull
  let e : Fin (pureRank s (fullBlock (show 3≤s by omega))) ≃
      Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤s by omega))
  let t' : Fin (retainedPairs s).card → ℝ :=
    fun j => t (.inr ⟨fullBlock (show 3≤s by omega),e.symm j⟩)
  have hsum : (∑ j,t (.inr ⟨fullBlock (show 3≤s by omega),j⟩) •
      (pureBlock hs (fullBlock (show 3≤s by omega))).column j) =
      ∑ j,t' j • (matchingPureBlock hs).column j := by
    calc
      _ = ∑ j,t (.inr ⟨fullBlock (show 3≤s by omega),j⟩) •
          (matchingPureBlock hs).column (e j) := by
        apply sum_congr rfl
        intro j hj
        exact congrArg (fun v => t (.inr ⟨fullBlock (show 3≤s by omega),j⟩) • v)
          (pureBlock_full_column hs j)
      _ = _ := by
        have he := e.sum_comp (fun j => t' j • (matchingPureBlock hs).column j)
        simpa only [t',Equiv.symm_apply_apply] using he
  rw [hsum] at hfull
  have hd := matchingPureBlock_rigidity hs d h0 t' hfull
  refine ⟨d ⟨1,by omega⟩,?_⟩
  intro a
  have ha := hd a.1
  change coefficientExtension (anchorSet (show 3≤s by omega)) (fun a => t (.inl a)) a.1=_ at ha
  rw [coefficientExtension_subtype] at ha
  simpa only [anchorWeights,Int.cast_natCast,mul_comm] using ha

theorem sum_bookBlock_split {W : Type*} [AddCommMonoid W] (hs : 3≤s)
    (f : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),f C)=f (fullBlock hs)+
      ∑ C : {C : BookBlock (Fin s) // C≠fullBlock hs},f C.1 := by
  have h := (Equiv.optionSubtypeNe (fullBlock hs)).sum_comp f
  rw [Fintype.sum_option] at h
  exact h.symm

theorem general_circuit_card (hs : 5≤s) :
    Fintype.card (ScopedAnchorIndex (anchorSet (show 3≤s by omega)) (pureRank s))=cliqueCapacity s := by
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,Fintype.card_coe,anchorSet,card_erase_of_mem (mem_univ _),card_univ]
  rw [sum_bookBlock_split (show 3≤s by omega),pureRank_full]
  have hproper : ∀ C : {C : BookBlock (Fin s) // C≠fullBlock (show 3≤s by omega)},
      pureRank s C.1=C.1.1.card.choose 2-1 := fun C =>
    pureRank_proper (show 3≤s by omega) C.1 C.2
  simp_rw [hproper]
  have h := BookBlock_dimension_sum (H:=Fin s)
  rw [sum_bookBlock_split (show 3≤s by omega)] at h
  have hfullcard : (fullBlock (show 3≤s by omega)).1.card=s := by simp [fullBlock]
  rw [hfullcard,Fintype.card_fin] at h
  have hc := retained_count_add_anchors hs
  have hchoose : 1≤s.choose 2 := Nat.choose_pos (by omega)
  omega

end GraphicalZonotopes.BooleanModule.Saturated
