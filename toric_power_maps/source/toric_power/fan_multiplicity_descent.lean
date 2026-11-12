module

public import ToricPower.SimplicialStellarFacets
public import ToricPower.RelativeFanRefinement

/-!
# Termination of relative regular subdivision

This is the finite combinatorial termination argument, separated from
the lattice calculation that constructs a decreasing stellar step.
First decrease the number of cones of maximal multiplicity; then
decrease that multiplicity. No estimate on the number of newly created
cones is required. The output is an actual regular fan with exactly
the original support and the prescribed regular subfan retained.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The arithmetic output required from one genuine stellar operation.
The point is integral, every regular old cone avoids it, and each new
full-dimensional cone has smaller multiplicity than an old parent. -/
structure StellarMultiplicityStep (fan : Fan i) (multiplicity : PointedCone ℝ V → ℕ)
    (focus : PointedCone ℝ V) where
  point : N
  nonzero : i point ≠ 0
  focus_contains : i point ∈ focus
  regular_avoids : ∀ C ∈ fan.cones, IsRegularCone i C → i point ∉ C
  decreases : ∀ S ∈ (stellarFan fan point).cones,
    Submodule.span ℝ (S : Set V) = ⊤ →
      (S ∈ fan.cones ∧ i point ∉ S) ∨
        ∃ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ ∧ multiplicity S < multiplicity C

theorem stellarFan_complete (fan : Fan i) (complete : fan.IsComplete)
    (q : N) (nonzero : i q ≠ 0) : (stellarFan fan q).IsComplete := by
  apply (Fan.isComplete_iff _).mpr
  intro x
  have member := (Fan.mem_support fan).mpr ((Fan.isComplete_iff fan).mp complete x)
  rw [← stellarFan_support fan q nonzero] at member
  exact (Fan.mem_support _).mp member

def highMultiplicityCones (fan : Fan i) (multiplicity : PointedCone ℝ V → ℕ) (m : ℕ) :
    Set (PointedCone ℝ V) :=
  {C ∈ fan.cones | Submodule.span ℝ (C : Set V) = ⊤ ∧ multiplicity C = m}

theorem highMultiplicityCones_finite (fan : Fan i)
    (multiplicity : PointedCone ℝ V → ℕ) (m : ℕ) :
    (highMultiplicityCones fan multiplicity m).Finite :=
  fan.finite_cones.subset fun _ h => h.1

theorem stellarMultiplicityStep_retains (original fan : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ fan.cones)
    (multiplicity : PointedCone ℝ V → ℕ) {focus : PointedCone ℝ V}
    (step : StellarMultiplicityStep fan multiplicity focus) :
    original.cones ⊆ (stellarFan fan step.point).cones := by
  intro C hC
  exact stellarFan_old_mem fan step.point (contains hC)
    (step.regular_avoids C (contains hC) (Fan.isRegular_iff.mp regular C hC))

theorem stellarMultiplicityStep_bound (fan : Fan i)
    (multiplicity : PointedCone ℝ V → ℕ) (m : ℕ)
    (bound : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m)
    {focus : PointedCone ℝ V} (step : StellarMultiplicityStep fan multiplicity focus) :
    ∀ S ∈ (stellarFan fan step.point).cones,
      Submodule.span ℝ (S : Set V) = ⊤ → multiplicity S ≤ m := by
  intro S hS full
  rcases step.decreases S hS full with old | ⟨C, hC, fullC, smaller⟩
  · exact bound S old.1 full
  · exact (lt_of_lt_of_le smaller (bound C hC fullC)).le

theorem stellarMultiplicityStep_high_old (fan : Fan i)
    (multiplicity : PointedCone ℝ V → ℕ) (m : ℕ)
    (bound : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m)
    {focus : PointedCone ℝ V} (step : StellarMultiplicityStep fan multiplicity focus)
    {S : PointedCone ℝ V} (member : S ∈ highMultiplicityCones (stellarFan fan step.point) multiplicity m) :
    S ∈ highMultiplicityCones fan multiplicity m ∧ i step.point ∉ S := by
  rcases step.decreases S member.1 member.2.1 with old | ⟨C, hC, fullC, smaller⟩
  · exact ⟨⟨old.1, member.2⟩, old.2⟩
  · have h := lt_of_lt_of_le smaller (bound C hC fullC)
    rw [member.2.2] at h
    exact False.elim (Nat.lt_irrefl _ h)

theorem stellarMultiplicityStep_high_count_lt (fan : Fan i)
    (multiplicity : PointedCone ℝ V → ℕ) (m : ℕ)
    (bound : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m)
    {focus : PointedCone ℝ V} (focusMember : focus ∈ highMultiplicityCones fan multiplicity m)
    (step : StellarMultiplicityStep fan multiplicity focus) :
    (highMultiplicityCones (stellarFan fan step.point) multiplicity m).ncard <
      (highMultiplicityCones fan multiplicity m).ncard := by
  apply Set.ncard_lt_ncard _ (highMultiplicityCones_finite fan multiplicity m)
  refine ⟨fun S hS => (stellarMultiplicityStep_high_old fan multiplicity m bound step hS).1, ?_⟩
  intro reverse
  exact (stellarMultiplicityStep_high_old fan multiplicity m bound step (reverse focusMember)).2
    step.focus_contains

variable (multiplicity : PointedCone ℝ V → ℕ)
  (constructStep : ∀ (fan : Fan i), fan.IsComplete →
    (∀ C ∈ fan.cones, C.IsSimplicial) →
    ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → 1 < multiplicity C →
      Nonempty (StellarMultiplicityStep fan multiplicity C))

include multiplicity constructStep

/-- Remove all cones at one multiplicity level. -/
theorem exists_relative_multiplicity_lt (original : Fan i) (regular : original.IsRegular)
    (m : ℕ) (large : 1 < m) (fan : Fan i) (complete : fan.IsComplete)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (contains : original.cones ⊆ fan.cones)
    (bound : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m) :
    ∃ refined : Fan i,
      original.cones ⊆ refined.cones ∧
      (∀ C ∈ refined.cones, ∃ D ∈ fan.cones, C ≤ D) ∧
      refined.support = fan.support ∧ refined.IsComplete ∧
      (∀ C ∈ refined.cones, C.IsSimplicial) ∧
      ∀ C ∈ refined.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C < m := by
  classical
  generalize countEquation : (highMultiplicityCones fan multiplicity m).ncard = count
  induction count using Nat.strong_induction_on generalizing fan with
  | h count inductionHypothesis =>
    by_cases allSmall : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C < m
    · exact ⟨fan, contains, fun C hC => ⟨C, hC, le_rfl⟩, rfl, complete, simplicial, allSmall⟩
    · push_neg at allSmall
      obtain ⟨focus, focusMember, fullFocus, highFocus⟩ := allSmall
      have focusValue : multiplicity focus = m := le_antisymm (bound focus focusMember fullFocus) highFocus
      obtain ⟨step⟩ := constructStep fan complete simplicial focus focusMember fullFocus
        (by rw [focusValue]; exact large)
      have retained := stellarMultiplicityStep_retains original fan regular contains multiplicity step
      have complete' := stellarFan_complete fan complete step.point step.nonzero
      have simplicial' := stellarFan_isSimplicial fan simplicial step.point
      have bound' := stellarMultiplicityStep_bound fan multiplicity m bound step
      have smaller : (highMultiplicityCones (stellarFan fan step.point) multiplicity m).ncard < count := by
        rw [← countEquation]
        exact stellarMultiplicityStep_high_count_lt fan multiplicity m bound
          ⟨focusMember, fullFocus, focusValue⟩ step
      obtain ⟨refined, retained', refines, support, complete'', simplicial'', small⟩ :=
        inductionHypothesis _ smaller (stellarFan fan step.point) complete' simplicial' retained bound' rfl
      refine ⟨refined, retained', ?_, support.trans (stellarFan_support fan step.point step.nonzero),
        complete'', simplicial'', small⟩
      intro C hC
      obtain ⟨D, hD, hCD⟩ := refines C hC
      obtain ⟨E, hE, hDE⟩ := stellarFan_refines fan step.point hD
      exact ⟨E, hE, hCD.trans hDE⟩

variable (smallRegular : ∀ C : PointedCone ℝ V, IsToricCone i C → C.IsSimplicial →
  Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ 1 → IsRegularCone i C)

include smallRegular

/-- The complete finite descent, assuming the separately proved
arithmetic step and the multiplicity-one criterion. -/
theorem exists_relative_regular_of_multiplicity_bound (original : Fan i)
    (regular : original.IsRegular) (m : ℕ) (fan : Fan i) (complete : fan.IsComplete)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (contains : original.cones ⊆ fan.cones)
    (bound : ∀ C ∈ fan.cones, Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m) :
    Nonempty (RelativeRegularFanRefinement original fan) := by
  induction m using Nat.strong_induction_on generalizing fan with
  | h m inductionHypothesis =>
    by_cases small : m ≤ 1
    · refine ⟨⟨fan, ?_, contains, fun C hC => ⟨C, hC, le_rfl⟩, rfl⟩⟩
      apply regular_of_fullDimensional fan complete
      intro C hC full
      exact smallRegular C (fan.isToricCone hC) (simplicial C hC) full ((bound C hC full).trans small)
    · have large : 1 < m := lt_of_not_ge small
      obtain ⟨intermediate, retained, refines, support, complete', simplicial', smaller⟩ :=
        exists_relative_multiplicity_lt multiplicity constructStep original regular m large
          fan complete simplicial contains bound
      have bound' : ∀ C ∈ intermediate.cones,
          Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m - 1 := by
        intro C hC full
        have h := smaller C hC full
        omega
      obtain ⟨refinement⟩ := inductionHypothesis (m - 1) (by omega)
        intermediate complete' simplicial' retained bound'
      refine ⟨⟨refinement.fan, refinement.regular, refinement.retains, ?_,
        refinement.support_eq.trans support⟩⟩
      intro C hC
      obtain ⟨D, hD, hCD⟩ := refinement.refines C hC
      obtain ⟨E, hE, hDE⟩ := refines D hD
      exact ⟨E, hE, hCD.trans hDE⟩

theorem exists_relative_regular_of_multiplicity_steps (original coarse : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ coarse.cones)
    (complete : coarse.IsComplete) :
    Nonempty (RelativeRegularFanRefinement original coarse) := by
  classical
  obtain ⟨simplicialFan, retained, refines, support, simplicial⟩ :=
    exists_relative_simplicial_refinement original coarse regular contains
  have complete' : simplicialFan.IsComplete := by
    apply (Fan.isComplete_iff _).mpr
    intro x
    have hx := (Fan.mem_support coarse).mpr ((Fan.isComplete_iff coarse).mp complete x)
    rw [← support] at hx
    exact (Fan.mem_support _).mp hx
  let m := simplicialFan.finite_cones.toFinset.sup multiplicity
  have bound : ∀ C ∈ simplicialFan.cones,
      Submodule.span ℝ (C : Set V) = ⊤ → multiplicity C ≤ m := by
    intro C hC _
    exact Finset.le_sup (simplicialFan.finite_cones.mem_toFinset.mpr hC)
  obtain ⟨refinement⟩ := exists_relative_regular_of_multiplicity_bound multiplicity
    constructStep smallRegular original regular m simplicialFan complete' simplicial retained bound
  refine ⟨⟨refinement.fan, refinement.regular, refinement.retains, ?_,
    refinement.support_eq.trans support⟩⟩
  intro C hC
  obtain ⟨D, hD, hCD⟩ := refinement.refines C hC
  obtain ⟨E, hE, hDE⟩ := refines D hD
  exact ⟨E, hE, hCD.trans hDE⟩

end ToricPower.FanSubdivision
end
