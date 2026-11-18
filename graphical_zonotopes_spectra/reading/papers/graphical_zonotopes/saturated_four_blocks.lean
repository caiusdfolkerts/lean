module

public import Papers.GraphicalZonotopes.ScopedAnchorCircuits
public import Papers.GraphicalZonotopes.SaturatedBookPartition
public import Papers.GraphicalZonotopes.SignedPairBases

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset
open scoped BigOperators
open Saturated

abbrev H := Fin 4
abbrev Cfull : Finset H := univ

def anchors : Finset H := {2,3}

def label (a : H) : ℤ := if a=2 ∨ a=3 then 1 else 0

def column : Fin 4 → PairIn Cfull → ℝ
  | 0 => pairIndicator (starPairs Cfull 2 {0,3})
  | 1 => pairIndicator (starPairs Cfull 2 {1,3})
  | 2 => pairIndicator {natPair 0 3 (by decide) (by decide)}
  | 3 => pairIndicator {natPair 1 3 (by decide) (by decide)}

theorem column_realizable (i : Fin 4) : PureRealizable Cfull (column i) := by
  fin_cases i
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_pair Cfull _
  · exact pureRealizable_pair Cfull _

theorem column_reference (i : Fin 4) : column i (natPair 0 1 (by decide) (by decide))=0 := by
  fin_cases i <;> norm_num [column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair]

theorem column_independent : LinearIndependent ℝ column := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc (natPair 0 2 (by decide) (by decide))
  have h1 := congrFun hc (natPair 1 2 (by decide) (by decide))
  have h2 := congrFun hc (natPair 0 3 (by decide) (by decide))
  have h3 := congrFun hc (natPair 1 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair] at h0 h1 h2 h3
  fin_cases i <;> assumption

theorem column_sum : (∑ i,column i)=endpointCoefficients Cfull (fun a => (label a : ℝ)) := by
  funext e
  obtain ⟨⟨⟨u,v⟩,huv,hG⟩,hu,hv⟩ := e
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,
    natPair,orderedPair,endpointCoefficients,label]

theorem full_rigidity (d : H → ℝ) (h0 : d 0=0) (h1 : d 1=0) (t : Fin 4 → ℝ)
    (hz : blockClass Cfull ((-1 : ℝ) • endpointCoefficients Cfull d+∑ i,t i • column i)=0) :
    d 2=d 3 := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Cfull (natPair 0 1 (by decide) (by decide)) _).mp hz
  have h01 := hc (natPair 0 1 (by decide) (by decide))
  have h02 := hc (natPair 0 2 (by decide) (by decide))
  have h12 := hc (natPair 1 2 (by decide) (by decide))
  have h23 := hc (natPair 2 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair,
    endpointCoefficients,h0,h1] at h01 h02 h12 h23
  linarith

def fullPureBlock : WeightedPureBlock Cfull 1
    (blockClass Cfull (endpointCoefficients Cfull (fun a => (label a : ℝ)))) 4 where
  column := column
  realizable := column_realizable
  weight := fun _ => 1
  positive := fun _ => by norm_num
  bounded := fun _ => le_rfl
  independent := blockClass_linearIndependent_of_reference Cfull
    (natPair 0 1 (by decide) (by decide)) column column_independent column_reference
  weighted_sum := by
    simp only [Int.cast_one,one_smul]
    rw [←map_sum,column_sum]

theorem proper_card {C : BookBlock H} (hC : C.1≠univ) : C.1.card=3 := by
  have h3 := (mem_largeBlocks.mp C.2).2
  have h4 : C.1.card≤4 := by simpa using card_le_card (subset_univ C.1)
  have hlt : C.1.card≠4 := by
    intro he
    apply hC
    exact eq_of_subset_of_card_le (subset_univ _) (by simpa using he.ge)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem proper_reference_exists :
    ∀ C : BookBlock H,C.1≠univ → ∃ e₀ : PairIn C.1,
      (label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2) ∧
      ∀ e : PairIn C.1,e≠e₀ → label e.1.1.1+label e.1.1.2=1 := by
  have hfinite : ∀ C : Finset H,C.card=3 → ∃ u v : H,
      u<v ∧ u∈C ∧ v∈C ∧ (label u+label v=0 ∨ label u+label v=2) ∧
      ∀ a b : H,a<b → a∈C → b∈C → (a≠u ∨ b≠v) → label a+label b=1 := by
    decide
  intro C hC
  obtain ⟨u,v,huv,hu,hv,hl,he⟩ := hfinite C.1 (proper_card hC)
  let e₀ : PairIn C.1 := ⟨⟨(u,v),huv,ne_of_lt huv⟩,hu,hv⟩
  refine ⟨e₀,hl,?_⟩
  intro e hne
  apply he e.1.1.1 e.1.1.2 e.1.2.1 e.2.1 e.2.2
  by_contra hn
  push_neg at hn
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hn.1 hn.2

def properPureBlock (C : BookBlock H) (hC : C.1≠univ) :
    WeightedPureBlock C.1 1 (-blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ)))) 2 := by
  let e₀ : PairIn C.1 := (proper_reference_exists C hC).choose
  have hv : label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2 :=
    (proper_reference_exists C hC).choose_spec.1
  have he : ∀ e : PairIn C.1,e≠e₀ → label e.1.1.1+label e.1.1.2=1 :=
    (proper_reference_exists C hC).choose_spec.2
  let ε : ℝ := if label e₀.1.1.1+label e₀.1.1.2=0 then -1 else 1
  let w : PairIn C.1 → ℤ := fun e => if e=e₀ then 0 else 1
  have hε : ε=1 ∨ ε= -1 := by unfold ε; split_ifs <;> simp
  let P := signed_pair_basis C.1 (mem_largeBlocks.mp C.2).2 e₀ ε hε w
    (by simp [w]) (fun e he => by simp [w,he]) 1 (fun e he => by simp [w,he])
  have htarget : blockClass C.1 (ε • (fun e => (w e : ℝ)))=
      -blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ))) := by
    have hc : blockClass C.1 ((ε • (fun e => (w e : ℝ)))+
        endpointCoefficients C.1 (fun a => (label a : ℝ)))=0 := by
      apply (blockClass_eq_zero_iff C.1 e₀ _).mpr
      refine ⟨((label e₀.1.1.1+label e₀.1.1.2 : ℤ) : ℝ),?_⟩
      intro e
      by_cases heq : e=e₀
      · subst e
        simp [w,endpointCoefficients]
      · have hh := he e heq
        rcases hv with hv | hv
        · have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_pos hv,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
        · have hn : label e₀.1.1.1+label e₀.1.1.2≠0 := by omega
          have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_neg hn,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
    rw [map_add] at hc
    exact eq_neg_of_add_eq_zero_left hc
  have hr : C.1.card.choose 2-1=2 := by rw [proper_card hC]; decide
  exact hr ▸ htarget ▸ P

abbrev fullBlock : BookBlock H := ⟨univ,by simp [mem_largeBlocks]⟩

def rank (C : BookBlock H) : ℕ := if C=fullBlock then 4 else 2

theorem anchor_extension : coefficientExtension anchors (fun _ => (1 : ℝ))=
    fun a => (label a : ℝ) := by
  funext a
  fin_cases a <;> norm_num [coefficientExtension,anchors,label]

def block (C : BookBlock H) :
    WeightedPureBlock C.1 1 (-((1*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
      (endpointCoefficients C.1 (coefficientExtension anchors (fun _ => ((1 : ℤ) : ℝ)))))) (rank C) := by
  classical
  by_cases hC : C=fullBlock
  · subst C
    rw [rank,if_pos rfl]
    refine {
      column := fullPureBlock.column
      realizable := fullPureBlock.realizable
      weight := fullPureBlock.weight
      positive := fullPureBlock.positive
      bounded := fullPureBlock.bounded
      independent := fullPureBlock.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [fullPureBlock.weighted_sum,anchor_extension]
    simp [fullBlock]
  · have hCu : C.1≠univ := fun h => hC (Subtype.ext h)
    rw [rank,if_neg hC]
    let P := properPureBlock C hCu
    refine {
      column := P.column
      realizable := P.realizable
      weight := P.weight
      positive := P.positive
      bounded := P.bounded
      independent := P.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [P.weighted_sum,anchor_extension,proper_card hCu]
    norm_num

theorem block_full_column : (block fullBlock).column=column := by
  unfold block
  simp only [dite_true] <;> rfl

theorem scale_rigidity : ScopedAnchorRigidity anchors 1 (fun _ => 1) 1 rank block := by
  intro t ht
  let d := coefficientExtension anchors (fun a => t (.inl a))
  have h0 : d 0=0 := by simp [d,coefficientExtension,anchors]
  have h1 : d 1=0 := by simp [d,coefficientExtension,anchors]
  have hfull := ht fullBlock
  change blockClass Cfull ((1*((-1 : ℝ)^((fullBlock.1).card-3))) • endpointCoefficients Cfull d+
    ∑ j,t (.inr ⟨fullBlock,j⟩) • (block fullBlock).column j)=0 at hfull
  have hfactor : (1 : ℝ)*(-1)^((fullBlock.1).card-3)= -1 := by norm_num [fullBlock]
  rw [block_full_column,hfactor] at hfull
  have h23 := full_rigidity d h0 h1 (fun j => t (.inr ⟨fullBlock,j⟩)) hfull
  refine ⟨d 2,?_⟩
  intro a
  have ha : a.1=2 ∨ a.1=3 := by simpa only [anchors,mem_insert,mem_singleton] using a.2
  have hd : t (.inl a)=d a.1 :=
    (coefficientExtension_subtype anchors (fun b => t (.inl b)) a).symm
  simp only [Int.cast_one,mul_one]
  rw [hd]
  rcases ha with ha | ha
  · rw [ha]
  · rw [ha,h23]

end GraphicalZonotopes.BooleanModule.SaturatedFour
