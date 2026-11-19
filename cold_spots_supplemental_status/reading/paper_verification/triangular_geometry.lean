module
public import PaperVerification.TriangularPhases
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def triangularDepth (z : TriPoint) : ℝ := sInf (Set.range fun m : EisInt ↦ triQ (eisEmbed m-z))

lemma triangularDepth_bdd (z : TriPoint) :
    BddBelow (Set.range fun m : EisInt ↦ triQ (eisEmbed m-z)) :=
  ⟨0,by rintro t ⟨m,rfl⟩; exact triQ_nonneg _⟩

lemma triangularDepth_nonneg (z : TriPoint) : 0 ≤ triangularDepth z := by
  apply le_csInf (Set.range_nonempty _)
  rintro t ⟨m,rfl⟩
  exact triQ_nonneg _

lemma triangularDepth_le (z : TriPoint) (m : EisInt) :
    triangularDepth z ≤ triQ (eisEmbed m-z) :=
  csInf_le (triangularDepth_bdd z) (Set.mem_range_self m)

theorem triangularDepth_periodic (z : TriPoint) (w : EisInt) :
    triangularDepth (z+eisEmbed w) = triangularDepth z := by
  unfold triangularDepth
  congr 1
  ext t
  constructor
  · rintro ⟨m,rfl⟩
    refine ⟨m-w,?_⟩
    change triQ (eisEmbed (m-w)-z) = triQ (eisEmbed m-(z+eisEmbed w))
    rw [map_sub]
    congr 1
    abel
  · rintro ⟨m,rfl⟩
    refine ⟨m+w,?_⟩
    change triQ (eisEmbed (m+w)-(z+eisEmbed w)) = triQ (eisEmbed m-z)
    rw [map_add,add_sub_add_right_eq_sub]

theorem triangularDepth_even (z : TriPoint) : triangularDepth (-z) = triangularDepth z := by
  unfold triangularDepth
  congr 1
  ext t
  constructor <;> rintro ⟨m,rfl⟩ <;> refine ⟨-m,?_⟩
  · change triQ (eisEmbed (-m)-z) = triQ (eisEmbed m- -z)
    rw [map_neg,show -eisEmbed m-z = -(eisEmbed m- -z) by abel,triQ_neg]
  · change triQ (eisEmbed (-m)- -z) = triQ (eisEmbed m-z)
    rw [map_neg,show -eisEmbed m- -z = -(eisEmbed m-z) by abel,triQ_neg]

theorem triangularDepth_zero : triangularDepth 0 = 0 := by
  apply le_antisymm
  · simpa [eisEmbed,triQ] using triangularDepth_le 0 (0,0)
  · exact triangularDepth_nonneg _

lemma triQ_at_c_integer (m : EisInt) :
    triQ (eisEmbed m-triC) =
      ((m.1^2-m.1*m.2+m.2^2-m.1+m.2 : ℤ) : ℝ) + 1/3 := by
  dsimp [triQ,eisEmbed,triC]
  push_cast
  ring

theorem triangularDepth_c : triangularDepth triC = 1/3 := by
  apply le_antisymm
  · have h := triangularDepth_le triC (0,0)
    norm_num [eisEmbed,triQ,triC] at h ⊢
    exact h
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    change 1/3 ≤ triQ (eisEmbed m-triC)
    rw [triQ_at_c_integer]
    let k : ℤ := m.1^2-m.1*m.2+m.2^2-m.1+m.2
    have hn := triQ_nonneg (eisEmbed m-triC)
    rw [triQ_at_c_integer] at hn
    have hk : 0 ≤ k := by
      by_contra hh
      have hi : k ≤ -1 := by omega
      have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hi
      dsimp [k] at hr
      linarith
    have hr : (0:ℝ) ≤ k := by exact_mod_cast hk
    dsimp [k] at hr
    linarith

private lemma triangle_depth_first (u v d : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1)
    (h0 : d ≤ triQ ((0,0)-(u,v))) (h1 : d ≤ triQ ((1,0)-(u,v)))
    (h2 : d ≤ triQ ((1,1)-(u,v))) :
    d ≤ 1/3-triQ ((u,v)-((2/3:ℝ),1/3)) := by
  have hA := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr h0)
  have hB := mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr h1)
  have hC := mul_nonneg hv (sub_nonneg.mpr h2)
  have he : (1-u)*(triQ ((0,0)-(u,v))-d)+(u-v)*(triQ ((1,0)-(u,v))-d)+
      v*(triQ ((1,1)-(u,v))-d) = 1/3-triQ ((u,v)-((2/3:ℝ),1/3))-d := by
    dsimp [triQ]
    ring
  linarith

private lemma triangle_depth_second (u v d : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (h0 : d ≤ triQ ((0,0)-(u,v))) (h1 : d ≤ triQ ((0,1)-(u,v)))
    (h2 : d ≤ triQ ((1,1)-(u,v))) :
    d ≤ 1/3-triQ ((u,v)-((1/3:ℝ),2/3)) := by
  have hA := mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr h0)
  have hB := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr h1)
  have hC := mul_nonneg hu (sub_nonneg.mpr h2)
  have he : (1-v)*(triQ ((0,0)-(u,v))-d)+(v-u)*(triQ ((0,1)-(u,v))-d)+
      u*(triQ ((1,1)-(u,v))-d) = 1/3-triQ ((u,v)-((1/3:ℝ),2/3))-d := by
    dsimp [triQ]
    ring
  linarith

theorem triangularDepth_fundamental (z : TriPoint)
    (hz : z ∈ (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) :
    triangularDepth z ≤ 1/3 ∧
      (triangularDepth z = 1/3 → z=((2/3:ℝ),1/3) ∨ z=((1/3:ℝ),2/3)) := by
  have h0 : triangularDepth z ≤ triQ ((0,0)-(z.1,z.2)) := by
    simpa [eisEmbed] using triangularDepth_le z (0,0)
  have h11 : triangularDepth z ≤ triQ ((1,1)-(z.1,z.2)) := by
    simpa [eisEmbed] using triangularDepth_le z (1,1)
  rcases le_total z.2 z.1 with h | h
  · have h10 : triangularDepth z ≤ triQ ((1,0)-(z.1,z.2)) := by
      simpa [eisEmbed] using triangularDepth_le z (1,0)
    have hd := triangle_depth_first z.1 z.2 (triangularDepth z) hz.2.1 h hz.1.2 h0 h10 h11
    have hq := triQ_nonneg (z-((2/3:ℝ),1/3))
    refine ⟨by linarith,?_⟩
    intro he
    left
    have hl := triQ_lower (z-((2/3:ℝ),1/3))
    have hzq : triQ (z-((2/3:ℝ),1/3))=0 := by linarith
    rw [hzq] at hl
    apply Prod.ext <;> dsimp at hl ⊢ <;>
      nlinarith [sq_nonneg (z.1-2/3),sq_nonneg (z.2-1/3)]
  · have h01 : triangularDepth z ≤ triQ ((0,1)-(z.1,z.2)) := by
      simpa [eisEmbed] using triangularDepth_le z (0,1)
    have hd := triangle_depth_second z.1 z.2 (triangularDepth z) hz.1.1 h hz.2.2 h0 h01 h11
    have hq := triQ_nonneg (z-((1/3:ℝ),2/3))
    refine ⟨by linarith,?_⟩
    intro he
    right
    have hl := triQ_lower (z-((1/3:ℝ),2/3))
    have hzq : triQ (z-((1/3:ℝ),2/3))=0 := by linarith
    rw [hzq] at hl
    apply Prod.ext <;> dsimp at hl ⊢ <;>
      nlinarith [sq_nonneg (z.1-1/3),sq_nonneg (z.2-2/3)]

theorem triangularDepth_le_third (z : TriPoint) : triangularDepth z ≤ 1/3 := by
  rw [← triFraction_add_floor z,triangularDepth_periodic]
  exact (triangularDepth_fundamental _ (triFraction_mem z)).1

def TriHole (z : TriPoint) : Prop :=
  (∃ m : EisInt, z=eisEmbed m+triC) ∨ (∃ m : EisInt, z=eisEmbed m-triC)

theorem triangularDepth_eq_third_iff (z : TriPoint) : triangularDepth z=1/3 ↔ TriHole z := by
  constructor
  · intro hz
    have hf : triangularDepth (triFraction z)=1/3 := by
      rw [← triangularDepth_periodic _ (triFloor z),triFraction_add_floor]
      exact hz
    rcases (triangularDepth_fundamental _ (triFraction_mem z)).2 hf with h | h
    · right
      refine ⟨triFloor z+(1,0),?_⟩
      conv_lhs => rw [← triFraction_add_floor z,h]
      rw [map_add]
      ext <;> dsimp [eisEmbed,triC] <;> ring
    · left
      refine ⟨triFloor z+(0,1),?_⟩
      conv_lhs => rw [← triFraction_add_floor z,h]
      rw [map_add]
      ext <;> dsimp [eisEmbed,triC] <;> ring
  · rintro (⟨m,rfl⟩|⟨m,rfl⟩)
    · rw [add_comm,triangularDepth_periodic,triangularDepth_c]
    · rw [sub_eq_add_neg,add_comm,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]

theorem triHole_both_iff (z : TriPoint) :
    TriHole (z+triC) ∧ TriHole (z-triC) ↔ z ∈ triIntegerLattice := by
  constructor
  · rintro ⟨h1,h2⟩
    rcases h1 with ⟨m,hm⟩|⟨m,hm⟩
    · exact ⟨m,(add_right_cancel hm).symm⟩
    rcases h2 with ⟨n,hn⟩|⟨n,hn⟩
    · have h := congrArg Prod.fst hm
      have h' := congrArg Prod.fst hn
      dsimp [eisEmbed,triC] at h h'
      have hh : (3:ℤ)*(m.1-n.1)=4 := by
        apply Int.cast_injective (α:=ℝ)
        push_cast
        linarith
      omega
    · exact ⟨n,(sub_left_inj.mp hn).symm⟩
  · rintro ⟨m,rfl⟩
    exact ⟨Or.inl ⟨m,rfl⟩,Or.inr ⟨m,rfl⟩⟩

/-- Every residue class has a nearest representative at a triangular hole. -/
theorem exists_nearest_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m-triC)=1/3 := by
  fin_cases r
  · refine ⟨(0,0),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (0,0) = (0 : ZMod 3)
    norm_num [eisResidue] <;> decide
  · refine ⟨(1,0),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (1,0) = (1 : ZMod 3)
    norm_num [eisResidue] <;> decide
  · refine ⟨(0,-1),?_,by norm_num [eisEmbed,triQ,triC]⟩
    change eisResidue (0,-1) = (2 : ZMod 3)
    norm_num [eisResidue] <;> decide

end PaperVerification.ColdSpots
