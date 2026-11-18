module

public import ToricPower.FanStellarSubdivision
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import Mathlib.Data.Set.Card

/-!
# Relative simplicial refinement

Stellar subdivision is applied first in the smallest dimension in which
a nonsimplicial cone remains. New cones of that dimension are simplicial,
so the finite number of bad cones strictly decreases. Induction on
dimension gives a finite simplicial refinement while retaining every
cone of a prescribed regular subfan.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The dimension is the dimension of the literal real span of the cone. -/
def coneDimension (C : PointedCone ℝ V) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (C : Set V))

theorem coneDimension_le_rank (fan : Fan i) (C : PointedCone ℝ V) :
    coneDimension C ≤ Module.finrank ℤ N := by
  letI := fan.lattice.finiteDimensional
  rw [fan.lattice.finrank_eq]
  exact Submodule.finrank_le _

/-- Coning a proper boundary cell strictly increases its dimension. -/
theorem coneDimension_lt_rayJoin (fan : Fan i) {C F S : PointedCone ℝ V} {p : V}
    (hp : p ∈ C) (face : F.IsFaceOf C) (hpF : p ∉ F) (hS : S ≤ F) :
    coneDimension S < coneDimension (rayJoin p S) := by
  letI := fan.lattice.finiteDimensional
  exact Submodule.finrank_lt_finrank_of_lt (span_base_lt_rayJoin hp face hpF hS)

theorem stellarFan_preserves_regular_subfan (original fan : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ fan.cones)
    {focus : PointedCone ℝ V} (focusMember : focus ∈ fan.cones)
    (singular : ¬ IsRegularCone i focus) (q : N) (focusPoint : i q ∈ focus)
    (determines : ∀ F : PointedCone ℝ V, F.IsFaceOf focus → i q ∈ F → focus ≤ F) :
    original.cones ⊆ (stellarFan fan q).cones := by
  intro σ hσ
  apply stellarFan_old_mem fan q (contains hσ)
  intro hpσ
  have focusLe : focus ≤ σ :=
    (determines (focus ⊓ σ) (fan.inf_isFaceOf_left focusMember (contains hσ))
      ⟨focusPoint, hpσ⟩).trans inf_le_right
  exact singular ((Fan.isRegular_iff.mp regular σ hσ).of_isFaceOf
    (fan.isFaceOf_of_le (contains hσ) focusMember focusLe))

/-- The nonsimplicial cones of dimension at most `d`. -/
def badSimplicialCones (fan : Fan i) (d : ℕ) : Set (PointedCone ℝ V) :=
  {C ∈ fan.cones | coneDimension C ≤ d ∧ ¬ C.IsSimplicial}

theorem badSimplicialCones_finite (fan : Fan i) (d : ℕ) :
    (badSimplicialCones fan d).Finite :=
  fan.finite_cones.subset fun _ h => h.1

/-- A nonsimplicial cone of small dimension in a stellar subdivision
must be an unchanged old cone: every newly coned base has smaller
dimension. -/
theorem stellarFan_bad_is_old (fan : Fan i) (d : ℕ)
    (lower : ∀ C ∈ fan.cones, coneDimension C < d → C.IsSimplicial)
    (q : N) {C : PointedCone ℝ V}
    (bad : C ∈ badSimplicialCones (stellarFan fan q) d) :
    C ∈ badSimplicialCones fan d ∧ i q ∉ C := by
  rcases (stellarFan_mem_iff fan q).mp bad.1 with old |
    ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · exact ⟨⟨old.1, bad.2⟩, old.2⟩
  · have dimension := coneDimension_lt_rayJoin fan hpσ
      (fan.isFaceOf_of_le hσ hτ hτσ) hpτ le_rfl
    exact False.elim (bad.2.2 (rayJoin_isSimplicial hpσ
      (fan.isFaceOf_of_le hσ hτ hτσ) hpτ le_rfl (lower τ hτ (lt_of_lt_of_le dimension bad.2.1))))

theorem stellarFan_simplicial_below (fan : Fan i) (d : ℕ)
    (lower : ∀ C ∈ fan.cones, coneDimension C < d → C.IsSimplicial) (q : N) :
    ∀ C ∈ (stellarFan fan q).cones, coneDimension C < d → C.IsSimplicial := by
  intro C hC small
  by_contra bad
  exact bad (lower C (stellarFan_bad_is_old fan d lower q ⟨hC, small.le, bad⟩).1.1 small)

theorem stellarFan_bad_count_lt (fan : Fan i) (d : ℕ)
    (lower : ∀ C ∈ fan.cones, coneDimension C < d → C.IsSimplicial)
    {focus : PointedCone ℝ V} (badFocus : focus ∈ badSimplicialCones fan d)
    (q : N) (focusPoint : i q ∈ focus) :
    (badSimplicialCones (stellarFan fan q) d).ncard < (badSimplicialCones fan d).ncard := by
  apply Set.ncard_lt_ncard _ (badSimplicialCones_finite fan d)
  refine ⟨fun C hC => (stellarFan_bad_is_old fan d lower q hC).1, ?_⟩
  intro reverse
  exact (stellarFan_bad_is_old fan d lower q (reverse badFocus)).2 focusPoint

/-- Remove all nonsimplicial cones in the next dimension. The inner
induction is on the actual finite set of bad cones, so the construction
terminates without a bound on how many larger cones are introduced. -/
theorem exists_relative_simplicial_through_dimension (original : Fan i)
    (regular : original.IsRegular) (d : ℕ) (fan : Fan i)
    (contains : original.cones ⊆ fan.cones)
    (lower : ∀ C ∈ fan.cones, coneDimension C < d → C.IsSimplicial) :
    ∃ refined : Fan i,
      original.cones ⊆ refined.cones ∧
      (∀ C ∈ refined.cones, ∃ D ∈ fan.cones, C ≤ D) ∧
      refined.support = fan.support ∧
      ∀ C ∈ refined.cones, coneDimension C ≤ d → C.IsSimplicial := by
  classical
  generalize countEquation : (badSimplicialCones fan d).ncard = count
  induction count using Nat.strong_induction_on generalizing fan with
  | h count inductionHypothesis =>
    by_cases complete : ∀ C ∈ fan.cones, coneDimension C ≤ d → C.IsSimplicial
    · exact ⟨fan, contains, fun C hC => ⟨C, hC, le_rfl⟩, rfl, complete⟩
    · push_neg at complete
      obtain ⟨focus, focusMember, focusDimension, nonsimplicial⟩ := complete
      have singular : ¬ IsRegularCone i focus := fun smooth =>
        nonsimplicial (smooth.isSimplicial fan.lattice)
      have focusNonzero : focus ≠ ⊥ := by
        intro zero
        apply singular
        rw [zero]
        exact isRegularCone_bot fan.lattice
      obtain ⟨q, focusPoint, nonzero, determines⟩ :=
        rationalCone_exists_nonzero_integral_interior (fan.isToricCone focusMember) focusNonzero
      have retained := stellarFan_preserves_regular_subfan original fan regular contains
        focusMember singular q focusPoint determines
      have smaller : (badSimplicialCones (stellarFan fan q) d).ncard < count := by
        rw [← countEquation]
        exact stellarFan_bad_count_lt fan d lower ⟨focusMember, focusDimension, nonsimplicial⟩
          q focusPoint
      obtain ⟨refined, retained', refines, support, simplicial⟩ :=
        inductionHypothesis _ smaller (stellarFan fan q) retained
          (stellarFan_simplicial_below fan d lower q) rfl
      refine ⟨refined, retained', ?_, support.trans (stellarFan_support fan q nonzero), simplicial⟩
      intro C hC
      obtain ⟨D, hD, hCD⟩ := refines C hC
      obtain ⟨E, hE, hDE⟩ := stellarFan_refines fan q hD
      exact ⟨E, hE, hCD.trans hDE⟩

/-- Build the simplicial skeleton through an arbitrary dimension. -/
theorem exists_relative_simplicial_below (original coarse : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ coarse.cones) (bound : ℕ) :
    ∃ refined : Fan i,
      original.cones ⊆ refined.cones ∧
      (∀ C ∈ refined.cones, ∃ D ∈ coarse.cones, C ≤ D) ∧
      refined.support = coarse.support ∧
      ∀ C ∈ refined.cones, coneDimension C < bound → C.IsSimplicial := by
  induction bound with
  | zero =>
    exact ⟨coarse, contains, fun C hC => ⟨C, hC, le_rfl⟩, rfl,
      fun _ _ h => False.elim (Nat.not_lt_zero _ h)⟩
  | succ bound inductionHypothesis =>
    obtain ⟨intermediate, retained, refines, support, lower⟩ := inductionHypothesis
    obtain ⟨refined, retained', refines', support', simplicial⟩ :=
      exists_relative_simplicial_through_dimension original regular bound intermediate retained lower
    refine ⟨refined, retained', ?_, support'.trans support, ?_⟩
    · intro C hC
      obtain ⟨D, hD, hCD⟩ := refines' C hC
      obtain ⟨E, hE, hDE⟩ := refines D hD
      exact ⟨E, hE, hCD.trans hDE⟩
    · intro C hC hdim
      exact simplicial C hC (Nat.lt_succ_iff.mp hdim)

/-- A finite rational fan has a finite simplicial refinement preserving
every cone of a prescribed regular subfan, in the same integral lattice. -/
theorem exists_relative_simplicial_refinement (original coarse : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ coarse.cones) :
    ∃ refined : Fan i,
      original.cones ⊆ refined.cones ∧
      (∀ C ∈ refined.cones, ∃ D ∈ coarse.cones, C ≤ D) ∧
      refined.support = coarse.support ∧
      ∀ C ∈ refined.cones, C.IsSimplicial := by
  obtain ⟨refined, retained, refines, support, simplicial⟩ :=
    exists_relative_simplicial_below original coarse regular contains (Module.finrank ℤ N + 1)
  exact ⟨refined, retained, refines, support,
    fun C hC => simplicial C hC (Nat.lt_succ_of_le (coneDimension_le_rank refined C))⟩

end ToricPower.FanSubdivision
end
