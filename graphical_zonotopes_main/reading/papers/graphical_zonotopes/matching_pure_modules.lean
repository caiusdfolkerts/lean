module

public import Papers.GraphicalZonotopes.PureColumnRealization

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def pairVertices {C : Finset H} (e : PairIn C) : Finset H := {e.1.1.1,e.1.1.2}

theorem pairVertices_subset {C : Finset H} (e : PairIn C) : pairVertices e⊆C := by
  simp [pairVertices,insert_subset_iff,singleton_subset_iff,e.2.1,e.2.2]

theorem pairVertices_card {C : Finset H} (e : PairIn C) : (pairVertices e).card=2 :=
  card_pair (ne_of_lt e.1.2.1)

def IsPairMatching {C : Finset H} (A : Finset (PairIn C)) : Prop :=
  ∀ e∈A,∀ f∈A,e≠f → Disjoint (pairVertices e) (pairVertices f)

def matchingBlocks {C : Finset H} (A : Finset (PairIn C)) : Finset (Finset H) :=
  A.image pairVertices ∪ (C.filter (fun a => ∀ e∈A,a∉pairVertices e)).image singleton

theorem mem_matchingBlocks {C : Finset H} (A : Finset (PairIn C)) (B : Finset H) :
    B∈matchingBlocks A ↔
      (∃ e∈A,B=pairVertices e) ∨
      ∃ a∈C,(∀ e∈A,a∉pairVertices e) ∧ B={a} := by
  simp only [matchingBlocks,mem_union,mem_image,mem_filter]
  constructor
  · rintro (⟨e,he,rfl⟩ | ⟨a,⟨ha,hn⟩,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,ha,hn,rfl⟩
  · rintro (⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,⟨ha,hn⟩,rfl⟩

theorem matchingBlocks_cover {C : Finset H} (A : Finset (PairIn C)) {a : H}
    (ha : a∈C) : ∃ B∈matchingBlocks A,a∈B := by
  by_cases he : ∃ e∈A,a∈pairVertices e
  · obtain ⟨e,he,hae⟩ := he
    exact ⟨pairVertices e,(mem_matchingBlocks A _).mpr (Or.inl ⟨e,he,rfl⟩),hae⟩
  · have hn : ∀ e∈A,a∉pairVertices e := by simpa only [not_exists,not_and] using he
    exact ⟨{a},(mem_matchingBlocks A _).mpr (Or.inr ⟨a,ha,hn,rfl⟩),mem_singleton_self _⟩

theorem matchingBlocks_subset {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B⊆C := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · exact pairVertices_subset e
  · exact singleton_subset_iff.mpr ha

theorem matchingBlocks_card_le_two {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B.card≤2 := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · rw [pairVertices_card]
  · simp

theorem matchingBlocks_family {C : Finset H} (hC : 3≤C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    ComplementFamily C (matchingBlocks A) := by
  refine ⟨?_,fun B hB => matchingBlocks_subset A hB,?_,?_⟩
  · by_contra hh
    have hcard : (matchingBlocks A).card≤1 := by omega
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<C.card)
    obtain ⟨B,hB,haB⟩ := matchingBlocks_cover A ha
    have hsub : C⊆B := by
      intro b hb
      obtain ⟨D,hD,hbD⟩ := matchingBlocks_cover A hb
      have he : D=B := (card_le_one.mp hcard) D hD B hB
      exact he ▸ hbD
    have hc := (card_le_card hsub).trans (matchingBlocks_card_le_two A hB)
    omega
  · intro B hB
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · exact ⟨e.1.1.1,by simp [pairVertices]⟩
    · exact singleton_nonempty _
  · intro B hB D hD hBD
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact hA e he f hf (fun h => hBD (congrArg pairVertices h))
      · exact disjoint_singleton_right.mpr (hm e he)
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact disjoint_singleton_left.mpr (hn f hf)
      · exact disjoint_singleton.mpr (fun h => hBD (congrArg singleton h))

theorem pairVertices_membership {C : Finset H} (e f : PairIn C) :
    (e.1.1.1∈pairVertices f ∧ e.1.1.2∈pairVertices f) ↔ e=f := by
  rw [pairVertices,ordered_pair_membership e.1.2.1 f.1.2.1]
  constructor
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hu hv))
  · rintro rfl
    exact ⟨rfl,rfl⟩

theorem crosses_matchingBlocks {C : Finset H} (hC : 3≤C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) (e : PairIn C) :
    Crosses (matchingBlocks A) e.1.1.1 e.1.1.2 ↔ e∉A := by
  let hf := matchingBlocks_family hC A hA
  constructor
  · rintro ⟨B,hB,D,hD,hBD,hu,hv⟩ he
    have hE := (mem_matchingBlocks A (pairVertices e)).mpr (Or.inl ⟨e,he,rfl⟩)
    have hBE := hf.shared_mem_eq hB hE hu (by simp [pairVertices])
    have hDE := hf.shared_mem_eq hD hE hv (by simp [pairVertices])
    exact hBD (hBE.trans hDE.symm)
  · intro he
    obtain ⟨B,hB,hu⟩ := matchingBlocks_cover A e.2.1
    obtain ⟨D,hD,hv⟩ := matchingBlocks_cover A e.2.2
    refine ⟨B,hB,D,hD,?_,hu,hv⟩
    intro hBD
    have hvB : e.1.1.2∈B := hBD.symm ▸ hv
    rcases (mem_matchingBlocks A B).mp hB with ⟨f,hf,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · have hef := (pairVertices_membership e f).mp ⟨hu,hvB⟩
      exact he (hef.symm ▸ hf)
    · have heq : e.1.1.1=e.1.1.2 := (mem_singleton.mp hu).trans (mem_singleton.mp hvB).symm
      exact (ne_of_lt e.1.2.1) heq

/-- Every matching gives an actual all-essential pure Boolean response equal
to its negative edge indicator, modulo the diagonal clique coefficient. -/
theorem pureRealizable_negative_matching {C : Finset H} (hC : 3≤C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    PureRealizable C (-pairIndicator A) := by
  classical
  let hf := matchingBlocks_family hC A hA
  refine ⟨complementModule C (matchingBlocks A),hf.module_boolean,
    fun a ha => hf.essential ha,
    fun a ha S => complementModule_ignores_outside C _ ha S,?_⟩
  rw [responseClass_eq_coefficientClass,complementModule_response_coefficients hf]
  have hcoord : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses (matchingBlocks A) r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      blockCoordinates C (fun e => 1-pairIndicator A e) := by
    funext r
    by_cases hr : rowClique r=C
    · have hc := crosses_matchingBlocks hC A hA (pairAtRow C r hr)
      change (if rowClique r=C ∧ _ then (1 : ℝ) else 0)=
        if h : rowClique r=C then 1-pairIndicator A (pairAtRow C r h) else 0
      rw [dif_pos hr]
      simp only [hr,true_and]
      change (if Crosses (matchingBlocks A) (pairAtRow C r hr).1.1.1
        (pairAtRow C r hr).1.1.2 then (1 : ℝ) else 0)=_
      rw [hc]
      by_cases he : pairAtRow C r hr∈A <;> simp [pairIndicator,he]
    · simp [blockCoordinates,hr]
  rw [hcoord]
  change blockClass C (fun e => 1-pairIndicator A e)=_
  have hfun : (fun e : PairIn C => (1 : ℝ)-pairIndicator A e)=
      (fun _ => (1 : ℝ))+(-pairIndicator A) := by rfl
  have hz : blockClass C (fun _ : PairIn C => (1 : ℝ))=0 := by
    change coefficientClass (blockCoordinates C (fun _ => 1))=0
    have hco : blockCoordinates C (fun _ : PairIn C => (1 : ℝ))=
        fun r : HubResponseRow H => if rowClique r=C then 1 else 0 := by
      funext r
      change (if _h : rowClique r=C then (1 : ℝ) else 0)=_
      split <;> rfl
    rw [hco]
    exact coefficientClass_block_zero C
  rw [hfun,map_add,hz,zero_add]

end GraphicalZonotopes.BooleanModule
