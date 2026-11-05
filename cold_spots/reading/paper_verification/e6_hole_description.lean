module

public import PaperVerification.E6Roots

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def phaseIndexEquiv : Fin 3 ≃ ZMod 3 :=
  Equiv.ofBijective (fun i : Fin 3 ↦ (i.val : ZMod 3)) (by decide)

def e6WitnessCorrection : Fin 3 → EisInt := ![0,0,(-1,1)]

theorem e6HoleWitness_phase (i : Fin 3) :
    e6HoleWitness i=eisEmbed (e6WitnessCorrection i)+triPhasePoint (phaseIndexEquiv i) := by
  fin_cases i <;> ext <;> norm_num [e6HoleWitness,e6WitnessCorrection,triPhasePoint,
    phaseIndexEquiv,eisEmbed,triC]

theorem triPhase_add_integer (r : ZMod 3) (k : ℤ) :
    ∃ m : EisInt, triPhasePoint r+(k:ℝ)•triC =
      eisEmbed m+triPhasePoint (r+(k:ZMod 3)) := by
  let s : ZMod 3 := r+(k:ZMod 3)
  let q : ℤ := ((r.val:ℤ)+k)/3
  have hs : (s.val:ℤ)=((r.val:ℤ)+k)%3 := by
    have h := ZMod.val_intCast (n:=3) ((r.val:ℤ)+k)
    simpa [s] using h
  have hk : (r.val:ℤ)+k=(s.val:ℤ)+3*q := by dsimp [q]; omega
  refine ⟨q•(1,-1),?_⟩
  rw [eisEmbed_zsmul]
  have hkr : (r.val:ℝ)+(k:ℝ)=(s.val:ℝ)+3*(q:ℝ) := by exact_mod_cast hk
  ext <;> dsimp [triPhasePoint,triC,eisEmbed] <;> nlinarith only [hkr]

def E6PaperHole (z : TriTriple) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ l : TriTriple, l ∈ l6Set ∧
    ∀ i, z i=e6HoleWitness (σ i)+l i

theorem e6BalancedPhases_iff_paper (z : TriTriple) : E6BalancedPhases z ↔ E6PaperHole z := by
  constructor
  · rintro ⟨r,hr,m,hm⟩
    let σ : Equiv.Perm (Fin 3) := (Equiv.ofBijective r hr).trans phaseIndexEquiv.symm
    have hσ (i : Fin 3) : phaseIndexEquiv (σ i)=r i := by simp [σ]
    let v : Fin 3 → EisInt := fun i ↦ m i-e6WitnessCorrection (σ i)
    refine ⟨σ,fun i ↦ eisEmbed (v i),?_,?_⟩
    · apply (l6Set_iff_integer_glue _).mpr
      exact ⟨v,0,by intro i; simp⟩
    · intro i
      rw [hm i,e6HoleWitness_phase,hσ]
      dsimp [v]
      rw [map_sub]
      abel
  · rintro ⟨σ,l,hl,hz⟩
    obtain ⟨m,k,hm⟩ := (l6Set_iff_integer_glue l).mp hl
    let r : Fin 3 → ZMod 3 := fun i ↦ phaseIndexEquiv (σ i)+(k:ZMod 3)
    have hr : Function.Bijective r :=
      (Equiv.addRight (k:ZMod 3)).bijective.comp (phaseIndexEquiv.bijective.comp σ.bijective)
    have hex (i : Fin 3) := triPhase_add_integer (phaseIndexEquiv (σ i)) k
    choose v hv using hex
    refine ⟨r,hr,fun i ↦ e6WitnessCorrection (σ i)+m i+v i,?_⟩
    intro i
    rw [hz i,hm i,e6HoleWitness_phase]
    rw [show eisEmbed (e6WitnessCorrection (σ i))+triPhasePoint (phaseIndexEquiv (σ i))+
      (eisEmbed (m i)+(k:ℝ)•triC) =
      eisEmbed (e6WitnessCorrection (σ i))+eisEmbed (m i)+
        (triPhasePoint (phaseIndexEquiv (σ i))+(k:ℝ)•triC) by abel,hv i]
    simp only [map_add]
    dsimp only [r]
    abel

theorem e6_cold_spot_description {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsColdSpot e6Set α (e6PhysicalPoint z) ↔ E6PaperHole z := by
  unfold e6Set e6PhysicalPoint
  rw [isColdSpot_scaled_iff _ (by positivity),Real.sq_sqrt (by norm_num),
    isColdSpot_l6Euclidean_iff,isL6ColdSpot_iff (by positivity),e6BalancedPhases_iff_paper]

theorem e6_deep_hole_description (z : TriTriple) :
    IsDeepHole e6Set (e6PhysicalPoint z) ↔ E6PaperHole z := by
  unfold e6Set e6PhysicalPoint
  rw [isDeepHole_scaled_iff _ (by positivity) _ l6EuclideanSet_nonempty,
    isDeepHole_l6Euclidean_iff,isL6DeepHole_iff,e6BalancedPhases_iff_paper]

end PaperVerification.ColdSpots
