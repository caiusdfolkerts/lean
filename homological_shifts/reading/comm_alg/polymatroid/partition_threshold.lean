import CommAlg.Polymatroid.PowerStabilization

/-! # Exact ceiling thresholds for every subset and every homological degree

The finite maximum over zero-defect partitions is the paper's `c_ρ(A)`;
the ceiling maximum is its `τ_i(A)`.  No degree or ground-set bound is used.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroDefectPartitions (ρ : RankFunction V) (A : Finset V) : Finset (Finpartition A) :=
  univ.filter (fun P => partitionDefect ρ P = 0)

theorem zeroDefectPartitions_nonempty (ρ : RankFunction V) (A : Finset V) :
    (zeroDefectPartitions ρ A).Nonempty := by
  by_cases hA : A = ∅
  · subst A
    refine ⟨Finpartition.empty (Finset V), ?_⟩
    simp [zeroDefectPartitions, partitionDefect]
  · refine ⟨Finpartition.indiscrete hA, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [partitionDefect, Finpartition.indiscrete]

def zeroDefectComponents (ρ : RankFunction V) (A : Finset V) : ℕ :=
  (zeroDefectPartitions ρ A).sup (fun P => P.parts.card)

theorem zeroDefectComponents_le_card (ρ : RankFunction V) (A : Finset V) :
    zeroDefectComponents ρ A ≤ A.card :=
  Finset.sup_le (fun P _ => P.card_parts_le_card)

theorem zeroDefectComponents_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧
      P.parts.card = zeroDefectComponents ρ A := by
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image
    (zeroDefectPartitions ρ A) (fun P => P.parts.card) (zeroDefectPartitions_nonempty ρ A)
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  change P.parts.card = (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
  exact le_antisymm (Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hP)
    (Finset.sup_le (fun Q hQ => hmax Q hQ))

def eventualOffset (ρ : RankFunction V) (A : Finset V) : ℕ :=
  A.card - zeroDefectComponents ρ A

theorem eventualOffset_le_slack (ρ : RankFunction V) {A : Finset V}
    (P : Finpartition A) (hP : partitionDefect ρ P = 0) :
    eventualOffset ρ A ≤ partitionSlack P := by
  have hc : P.parts.card ≤ zeroDefectComponents ρ A := by
    change P.parts.card ≤ (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
    have hm : P ∈ zeroDefectPartitions ρ A := mem_filter.mpr ⟨mem_univ P, hP⟩
    exact Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hm
  exact Nat.sub_le_sub_left hc A.card

theorem eventualOffset_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧ partitionSlack P = eventualOffset ρ A := by
  obtain ⟨P, hd, hc⟩ := zeroDefectComponents_attained ρ A
  exact ⟨P, hd, congrArg (A.card - ·) hc⟩

def eventualCorrection (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  min i (eventualOffset ρ A)

def powerCorrection (ρ : RankFunction V) (i s : ℕ) (A : Finset V) : ℕ :=
  cappedAffineMinimum i (fun P : Finpartition A => partitionDefect ρ P)
    partitionSlack s

def powerThreshold (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  affineThreshold (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack

theorem eventualCorrection_le_zero_slack (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    ∀ P : Finpartition A, partitionDefect ρ P = 0 →
      eventualCorrection ρ i A ≤ partitionSlack P := by
  intro P hP
  exact (min_le_right _ _).trans (eventualOffset_le_slack ρ P hP)

theorem powerCorrection_recap (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A =
      cappedAffineMinimum (eventualCorrection ρ i A)
        (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s := by
  obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ A
  have hmin : finiteMinimum (fun P : Finpartition A => s * partitionDefect ρ P + partitionSlack P) ≤
      eventualOffset ρ A := by
    have h := finiteMinimum_le (fun P : Finpartition A =>
      s * partitionDefect ρ P + partitionSlack P) P
    simpa [hd, hb] using h
  unfold powerCorrection cappedAffineMinimum eventualCorrection
  rw [min_assoc, min_eq_right hmin]

theorem powerThreshold_le (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ i :=
  (affineThreshold_le_cap _ _ _).trans (min_le_left _ _)

theorem powerCorrection_eq_eventual_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A = eventualCorrection ρ i A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap]
  exact cappedAffineMinimum_eq_cap_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap ρ i (s + 1), powerCorrection_recap ρ i s]
  exact cappedAffineMinimum_step_eq_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_strict_step (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hs : s < powerThreshold ρ i A) :
    powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  rw [powerCorrection_recap ρ i s, powerCorrection_recap ρ i (s + 1)]
  exact cappedAffineMinimum_strict_step _ _ _ (eventualCorrection_le_zero_slack ρ i A) hs

@[simp] theorem powerCorrection_zero (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerCorrection ρ i 0 A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := finiteMinimum_le
    (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) (⊥ : Finpartition A)
  have hb : partitionSlack (⊥ : Finpartition A) = 0 := by simp [partitionSlack, Finpartition.card_bot]
  have hbound : powerCorrection ρ i 0 A ≤
      finiteMinimum (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) :=
    min_le_right _ _
  simpa [hb] using hbound.trans h

@[simp] theorem powerThreshold_empty (ρ : RankFunction V) (i : ℕ) :
    powerThreshold ρ i ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := affineThreshold_le_cap (eventualCorrection ρ i ∅)
    (fun P : Finpartition (∅ : Finset V) => partitionDefect ρ P) partitionSlack
  simpa [eventualCorrection, eventualOffset, powerThreshold] using h

theorem powerThreshold_pos (ρ : RankFunction V) {i : ℕ} (hi : 0 < i)
    {A : Finset V} (hA : i ≤ eventualOffset ρ A) : 1 ≤ powerThreshold ρ i A := by
  have he := powerCorrection_eq_eventual_iff ρ i 0 A
  have hκ : eventualCorrection ρ i A = i := min_eq_left hA
  rw [powerCorrection_zero, hκ] at he
  omega

theorem powerCorrection_eq_degree_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : i ≤ eventualOffset ρ A) :
    powerCorrection ρ i s A = i ↔ powerThreshold ρ i A ≤ s := by
  have he := powerCorrection_eq_eventual_iff ρ i s A
  simpa only [eventualCorrection, min_eq_left hA] using he

theorem powerCorrection_lt_degree (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : eventualOffset ρ A < i) : powerCorrection ρ i s A < i := by
  rw [powerCorrection_recap]
  have h := cappedAffineMinimum_le_cap (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s
  have hκ : eventualCorrection ρ i A = eventualOffset ρ A := min_eq_right hA.le
  omega

/-- The paper's maximum over all nonempty subsets; the empty subset contributes zero. -/
def globalPowerThreshold (ρ : RankFunction V) (i : ℕ) : ℕ :=
  univ.sup (powerThreshold ρ i)

theorem powerThreshold_le_global (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ globalPowerThreshold ρ i := Finset.le_sup (mem_univ A)

theorem globalPowerThreshold_le (ρ : RankFunction V) (i : ℕ) :
    globalPowerThreshold ρ i ≤ i := Finset.sup_le (fun A _ => powerThreshold_le ρ i A)

theorem all_powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) :
    (∀ A, powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A) ↔
      globalPowerThreshold ρ i ≤ s := by
  simp only [powerCorrection_step_eq_iff, globalPowerThreshold, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left]

theorem exists_strict_powerCorrection (ρ : RankFunction V) (i s : ℕ)
    (hs : s < globalPowerThreshold ρ i) :
    ∃ A : Finset V, A.Nonempty ∧
      powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  have hex : ∃ A, s < powerThreshold ρ i A := by
    by_contra hn
    push Not at hn
    have hle : globalPowerThreshold ρ i ≤ s := Finset.sup_le (fun A _ => hn A)
    omega
  obtain ⟨A, hA⟩ := hex
  have hne : A ≠ ∅ := by intro heq; simp [heq] at hA
  exact ⟨A, Finset.nonempty_iff_ne_empty.mpr hne, powerCorrection_strict_step ρ i s A hA⟩

end CommAlg.Polymatroid
