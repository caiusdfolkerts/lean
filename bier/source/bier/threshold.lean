import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! Every proper down-set has a unique sign transition along each diagonal line. -/

noncomputable section

namespace Bier

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_face_threshold (face : Finset V → Prop)
    (hempty : face ∅) (hdown : ∀ {s t}, s ⊆ t → face t → face s)
    (hproper : ¬ face Finset.univ) (x : V → ℝ) :
    ∃ t : ℝ, (∃ v, x v = t) ∧
      face (Finset.univ.filter (fun v => t < x v)) ∧
      ¬ face (Finset.univ.filter (fun v => t ≤ x v)) := by
  classical
  have hV : (Finset.univ : Finset V).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hproper
    exact hproper hempty
  let bad : Finset V := Finset.univ.filter
    (fun v => ¬ face (Finset.univ.filter (fun w => x v ≤ x w)))
  have hbad : bad.Nonempty := by
    obtain ⟨v, hv, hmin⟩ := Finset.univ.exists_min_image x hV
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩⟩
    have heq : Finset.univ.filter (fun w => x v ≤ x w) = Finset.univ := by
      ext w
      simp [hmin w (Finset.mem_univ w)]
    simpa only [heq] using hproper
  obtain ⟨v, hv, hmax⟩ := bad.exists_max_image x hbad
  refine ⟨x v, ⟨v, rfl⟩, ?_, (Finset.mem_filter.mp hv).2⟩
  by_contra hn
  let above : Finset V := Finset.univ.filter (fun w => x v < x w)
  have habove : above.Nonempty := by
    by_contra he
    have he' : above = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hn
    change face above
    rwa [he']
  obtain ⟨w, hw, hmin⟩ := above.exists_min_image x habove
  have hwbad : w ∈ bad := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hf
    apply hn
    apply hdown _ hf
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin u hu⟩
  exact (not_lt_of_ge (hmax w hwbad)) (Finset.mem_filter.mp hw).2

/-- The positive and negative supports select one point on each diagonal line.
The statement applies to unnormalized cone coordinates, including the origin. -/
theorem diagonal_difference_eq_zero (face : Finset V → Prop)
    (hdown : ∀ {s t}, s ⊆ t → face t → face s)
    (x y : V → ℝ) (hx : face (Finset.univ.filter (fun v => 0 < x v)))
    (hx' : ¬ face (Finset.univ.filter (fun v => 0 ≤ x v)))
    (hy : face (Finset.univ.filter (fun v => 0 < y v)))
    (hy' : ¬ face (Finset.univ.filter (fun v => 0 ≤ y v)))
    (c : ℝ) (hxy : ∀ v, x v = y v + c) : c = 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exfalso
    apply hx'
    apply hdown _ hy
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [hxy v]⟩
  · exact hc
  · exfalso
    apply hy'
    apply hdown _ hx
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith [hxy v]⟩

end Bier
