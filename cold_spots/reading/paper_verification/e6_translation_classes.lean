module

public import PaperVerification.E6HoleDescription
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

def l6AddSubgroup : AddSubgroup TriTriple where
  carrier := l6Set
  zero_mem' := (l6Set_iff_integer_glue 0).mpr ⟨0,0,by intro i; simp⟩
  add_mem' := by
    intro z w hz hw
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue z).mp hz
    obtain ⟨n,l,hn⟩ := (l6Set_iff_integer_glue w).mp hw
    apply (l6Set_iff_integer_glue (z+w)).mpr
    refine ⟨m+n,k+l,?_⟩
    intro i
    simp only [Pi.add_apply,hm,hn,map_add,Int.cast_add,add_smul]
    abel
  neg_mem' := by
    intro z hz
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue z).mp hz
    apply (l6Set_iff_integer_glue (-z)).mpr
    refine ⟨-m,-k,?_⟩
    intro i
    simp only [Pi.neg_apply,hm,map_neg,Int.cast_neg,neg_smul]
    abel

theorem triPhase_rep_unique {m n : EisInt} {r s : ZMod 3}
    (h : eisEmbed m+triPhasePoint r=eisEmbed n+triPhasePoint s) : r=s := by
  have hh := congrArg Prod.fst h
  change (m.1:ℝ)+(r.val:ℝ)*(1/3)=(n.1:ℝ)+(s.val:ℝ)*(1/3) at hh
  have hi : (3:ℤ)*(m.1-n.1)=(s.val:ℤ)-(r.val:ℤ) := by
    apply Int.cast_injective (α:=ℝ)
    push_cast
    linarith
  have hm := congrArg (fun k : ℤ ↦ (k:ZMod 3)) hi
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    ZMod.natCast_zmod_val, zmodThree_three_eq_zero, zero_mul] at hm
  linear_combination hm

theorem e6PhaseConfiguration_unique {z : TriTriple} {r s : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) (hs : E6PhaseConfiguration z s) : r=s := by
  obtain ⟨m,hm⟩ := hr
  obtain ⟨n,hn⟩ := hs
  funext i
  exact triPhase_rep_unique ((hm i).symm.trans (hn i))

theorem e6PhaseConfiguration_add_lattice {z l : TriTriple} {r : Fin 3 → ZMod 3}
    (hz : E6PhaseConfiguration z r) (hl : l ∈ l6Set) :
    ∃ q : ZMod 3, E6PhaseConfiguration (z+l) (fun i ↦ r i+q) := by
  obtain ⟨m,hm⟩ := hz
  obtain ⟨n,k,hn⟩ := (l6Set_iff_integer_glue l).mp hl
  choose v hv using (fun i ↦ triPhase_add_integer (r i) k)
  refine ⟨(k:ZMod 3),fun i ↦ m i+n i+v i,?_⟩
  intro i
  simp only [Pi.add_apply,hm,hn,map_add]
  rw [show eisEmbed (m i)+triPhasePoint (r i)+(eisEmbed (n i)+(k:ℝ)•triC)=
    eisEmbed (m i)+eisEmbed (n i)+(triPhasePoint (r i)+(k:ℝ)•triC) by abel,hv i]
  abel

theorem e6Phase_sub_mem_iff {z w : TriTriple} {r s : Fin 3 → ZMod 3}
    (hz : E6PhaseConfiguration z r) (hw : E6PhaseConfiguration w s) :
    z-w ∈ l6Set ↔ ∃ q : ZMod 3, ∀ i, r i=s i+q := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := e6PhaseConfiguration_add_lattice hw h
    have he : w+(z-w)=z := by abel
    rw [he] at hq
    have hr := e6PhaseConfiguration_unique hz hq
    exact ⟨q,fun i ↦ congrFun hr i⟩
  · rintro ⟨q,hq⟩
    obtain ⟨m,hm⟩ := hz
    obtain ⟨n,hn⟩ := hw
    choose v hv using (fun i ↦ triPhase_add_integer (s i) (q.val:ℤ))
    apply (l6Set_iff_integer_glue (z-w)).mpr
    refine ⟨fun i ↦ m i-n i-v i,(q.val:ℤ),?_⟩
    intro i
    have he := hv i
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at he
    rw [← hq i] at he
    simp only [Pi.sub_apply,hm,hn,map_sub,Int.cast_natCast]
    rw [show triPhasePoint (r i)=triPhasePoint (s i)+(q.val:ℝ)•triC-eisEmbed (v i) by
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using he.symm]
    abel

theorem e6BalancedPhases_add_lattice {z l : TriTriple} (hz : E6BalancedPhases z)
    (hl : l ∈ l6Set) : E6BalancedPhases (z+l) := by
  obtain ⟨r,hr,hz⟩ := hz
  obtain ⟨q,hq⟩ := e6PhaseConfiguration_add_lattice hz hl
  exact ⟨fun i ↦ r i+q,(Equiv.addRight q).bijective.comp hr,hq⟩

def e6PositivePhases : Fin 3 → ZMod 3 := ![0,1,2]
def e6NegativePhases : Fin 3 → ZMod 3 := ![0,2,1]

theorem e6HoleWitness_positive_configuration :
    E6PhaseConfiguration e6HoleWitness e6PositivePhases := by
  refine ⟨e6WitnessCorrection,?_⟩
  intro i
  have hi : phaseIndexEquiv i = e6PositivePhases i := by
    fin_cases i <;> rfl
  simpa only [hi] using e6HoleWitness_phase i

theorem e6HoleWitness_negative_configuration :
    E6PhaseConfiguration (-e6HoleWitness) e6NegativePhases := by
  refine ⟨![0,(-1,1),0],?_⟩
  intro i
  fin_cases i <;> ext <;>
    norm_num [e6HoleWitness,e6NegativePhases,triPhasePoint,eisEmbed,triC]

lemma balanced_phase_two_classes (r : Fin 3 → ZMod 3) (hr : Function.Bijective r) :
    (∃ q, ∀ i, r i=e6PositivePhases i+q) ∨
      (∃ q, ∀ i, r i=e6NegativePhases i+q) := by
  have hall : ∀ a b c : ZMod 3, a ≠ b → a ≠ c → b ≠ c →
      (b = 1 + a ∧ c = 2 + a) ∨ (b = 2 + a ∧ c = 1 + a) := by
    have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    intro a b c hab hac hbc
    rcases hcases a with rfl | rfl | rfl <;>
      rcases hcases b with rfl | rfl | rfl <;>
      rcases hcases c with rfl | rfl | rfl
    all_goals solve
      | exact (hab rfl).elim
      | exact (hac rfl).elim
      | exact (hbc rfl).elim
      | exact Or.inl ⟨by decide, by decide⟩
      | exact Or.inr ⟨by decide, by decide⟩
  obtain ⟨h01, h02, h12⟩ := (bijective_fin3_zmod3_iff r).mp hr
  rcases hall (r 0) (r 1) (r 2) h01 h02 h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨r 0, ?_⟩
    intro i
    rcases (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) i with rfl | rfl | rfl
    · simp only [e6PositivePhases, Matrix.cons_val_zero, zero_add]
    · simpa only [e6PositivePhases, Matrix.cons_val_one, Matrix.cons_val_zero] using h1
    · simpa only [e6PositivePhases, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] using h2
  · right
    refine ⟨r 0, ?_⟩
    intro i
    rcases (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) i with rfl | rfl | rfl
    · simp only [e6NegativePhases, Matrix.cons_val_zero, zero_add]
    · simpa only [e6NegativePhases, Matrix.cons_val_one, Matrix.cons_val_zero] using h1
    · simpa only [e6NegativePhases, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons] using h2

theorem e6_two_translation_classes {z : TriTriple} (hz : E6BalancedPhases z) :
    z-e6HoleWitness ∈ l6Set ∨ z-(-e6HoleWitness) ∈ l6Set := by
  obtain ⟨r,hr,hz⟩ := hz
  rcases balanced_phase_two_classes r hr with h | h
  · exact Or.inl ((e6Phase_sub_mem_iff hz e6HoleWitness_positive_configuration).mpr h)
  · exact Or.inr ((e6Phase_sub_mem_iff hz e6HoleWitness_negative_configuration).mpr h)

theorem e6_two_classes_distinct : e6HoleWitness-(-e6HoleWitness) ∉ l6Set := by
  rw [e6Phase_sub_mem_iff e6HoleWitness_positive_configuration e6HoleWitness_negative_configuration]
  rintro ⟨q,hq⟩
  have h0 := hq 0
  have h1 := hq 1
  norm_num [e6PositivePhases,e6NegativePhases] at h0 h1
  rw [← h0] at h1
  exact (show (1 : ZMod 3) ≠ 2 by decide) (by simpa only [add_zero] using h1)

/-- Both classes occur and are interchanged by negation. Together with the
preceding exhaustiveness and distinctness theorems this is the exact count two. -/
theorem e6NegativeWitness_balanced : E6BalancedPhases (-e6HoleWitness) := by
  refine ⟨e6NegativePhases,?_,e6HoleWitness_negative_configuration⟩
  apply (bijective_fin3_zmod3_iff e6NegativePhases).mpr
  change (0 : ZMod 3) ≠ 2 ∧ (0 : ZMod 3) ≠ 1 ∧ (2 : ZMod 3) ≠ 1
  decide

end PaperVerification.ColdSpots
