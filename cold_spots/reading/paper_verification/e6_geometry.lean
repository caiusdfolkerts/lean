module

public import PaperVerification.E6Phases
public import PaperVerification.FiniteThree

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

lemma triangularDepth_neg_two_shift (z : TriPoint) :
    triangularDepth (z-(2:ℝ)•triC)=triangularDepth (z+triC) := by
  have he : z-(2:ℝ)•triC=(z+triC)+eisEmbed (-1,1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularDepth_periodic]

theorem sum_triangular_depth_phases (z : TriPoint) :
    (∑ r : ZMod 3, triangularDepth (z-triPhasePoint r))=triangularDepthSum z := by
  rw [sum_zmod_three]
  norm_num [triPhasePoint,triangularDepth_neg_two_shift,triangularDepthSum,
    add_assoc,add_comm,add_left_comm]

theorem l6CosetDepth_sum (z : TriTriple) :
    l6CosetDepth z 0+l6CosetDepth z 1+l6CosetDepth z 2 =
      triangularDepthSum (z 0)+triangularDepthSum (z 1)+triangularDepthSum (z 2) := by
  rw [← sum_zmod_three]
  unfold l6CosetDepth
  rw [Finset.sum_comm]
  change (∑ i, ∑ r : ZMod 3, triangularDepth (z i-triPhasePoint r))=_
  simp only [sum_triangular_depth_phases]
  simp [Fin.sum_univ_succ,add_assoc]

theorem l6Depth_cosets (z : TriTriple) :
    l6Depth z=min (l6CosetDepth z 0) (min (l6CosetDepth z 1) (l6CosetDepth z 2)) := by
  apply le_antisymm
  · exact le_min (l6Depth_le_cosetDepth z 0)
      (le_min (l6Depth_le_cosetDepth z 1) (l6Depth_le_cosetDepth z 2))
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨⟨r,m⟩,rfl⟩
    have hmin : min (l6CosetDepth z 0) (min (l6CosetDepth z 1) (l6CosetDepth z 2)) ≤
        l6CosetDepth z r := by
      fin_cases r
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    apply hmin.trans
    apply Finset.sum_le_sum
    intro i hi
    have h := triangularDepth_le (z i-(r.val:ℝ)•triC) (m i)
    convert h using 1
    congr 1
    dsimp [l6Point]
    abel

theorem l6Depth_upper (z : TriTriple) : l6Depth z ≤ 2/3 := by
  have h0 := l6Depth_le_cosetDepth z 0
  have h1 := l6Depth_le_cosetDepth z 1
  have h2 := l6Depth_le_cosetDepth z 2
  have hs := l6CosetDepth_sum z
  have h0' := triangularDepthSum_upper (z 0)
  have h1' := triangularDepthSum_upper (z 1)
  have h2' := triangularDepthSum_upper (z 2)
  linarith

theorem l6Depth_equality_iff (z : TriTriple) : l6Depth z=2/3 ↔ E6BalancedPhases z := by
  constructor
  · intro hz
    have h0 := l6Depth_le_cosetDepth z 0
    have h1 := l6Depth_le_cosetDepth z 1
    have h2 := l6Depth_le_cosetDepth z 2
    have hs := l6CosetDepth_sum z
    have h0' := triangularDepthSum_upper (z 0)
    have h1' := triangularDepthSum_upper (z 1)
    have h2' := triangularDepthSum_upper (z 2)
    have hp : ∀ i, TriPhase (z i) := by
      intro i
      apply (triangularDepthSum_eq_iff _).mp
      fin_cases i
      · change triangularDepthSum (z 0)=2/3
        linarith
      · change triangularDepthSum (z 1)=2/3
        linarith
      · change triangularDepthSum (z 2)=2/3
        linarith
    obtain ⟨r,hr⟩ := (exists_E6PhaseConfiguration_iff z).mpr hp
    have he : e6DepthProfile r 0=2/3 ∧ e6DepthProfile r 1=2/3 ∧ e6DepthProfile r 2=2/3 := by
      rw [← l6CosetDepth_of_phases hr 0,← l6CosetDepth_of_phases hr 1,
        ← l6CosetDepth_of_phases hr 2]
      exact ⟨by linarith,by linarith,by linarith⟩
    exact ⟨r,(e6DepthProfile_eq_iff r).mp he,hr⟩
  · rintro ⟨r,hr,hz⟩
    have he := (e6DepthProfile_eq_iff r).mpr hr
    rw [l6Depth_cosets,l6CosetDepth_of_phases hz 0,l6CosetDepth_of_phases hz 1,
      l6CosetDepth_of_phases hz 2,he.1,he.2.1,he.2.2,min_self,min_self]

def e6HoleWitness : TriTriple := ![0,triC,-triC]

theorem e6HoleWitness_balanced : E6BalancedPhases e6HoleWitness := by
  let r : Fin 3 → ZMod 3 := ![0,1,2]
  have hr : Function.Bijective r := by
    rw [bijective_fin3_zmod3_iff]
    change (0 : ZMod 3) ≠ 1 ∧ (0 : ZMod 3) ≠ 2 ∧ (1 : ZMod 3) ≠ 2
    decide
  refine ⟨r,hr,![0,0,(-1,1)],?_⟩
  intro i
  fin_cases i <;> ext <;> norm_num [e6HoleWitness,r,triPhasePoint,eisEmbed,triC]

theorem l6Depth_witness : l6Depth e6HoleWitness=2/3 :=
  (l6Depth_equality_iff _).mpr e6HoleWitness_balanced

theorem isL6DeepHole_iff (z : TriTriple) : IsL6DeepHole z ↔ E6BalancedPhases z := by
  rw [← l6Depth_equality_iff]
  constructor
  · intro h
    have hw := h e6HoleWitness
    rw [l6Depth_witness] at hw
    exact le_antisymm (l6Depth_upper z) hw
  · intro h w
    rw [h]
    exact l6Depth_upper w

end PaperVerification.ColdSpots
