module

public import ToricPower.SubfanBoundaryRestrictionCohomology
public import ToricPower.LinearTestFiniteness
public import ToricPower.SchemeCore

/-!
# One boundary twist satisfies every test on a complete extension

Every linear test of the extension restricts to a linear test of the
original fan in precisely the same saturated lattice. Completeness
makes this family finite. The individual eventual nonvanishing bounds
therefore have a common maximum, and every later boundary twist
satisfies the literal all-subspace cohomological criterion.

This proves the cohomological passage in Section 4. Existence of the
smooth divisorial extension and the generator theorem remain separate
mathematical dependencies.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

/-- The full original cohomological criterion supplies one uniform
boundary twist satisfying the full criterion on a complete extension.
All larger integer twists work as well. -/
theorem subfanBoundaryCriterion_eventually
    (hne : fan.cones.Nonempty) (regular : extension.IsRegular)
    (complete : extension.IsComplete) (rayFull : IsFullOnRays fan extension)
    (b : fan.Ray → ℤ)
    (criterion : let nonempty : Nonempty fan.cones := ⟨⟨hne.choose,hne.choose_spec⟩⟩
      letI := toricSchemeIntegral fan nonempty
      linearCohomologyCriterion fan hne (invariantCartierDivisor fan nonempty
        (subfan_isRegular fan extension included regular) b)) :
    let nonempty : Nonempty fan.cones := ⟨⟨hne.choose,hne.choose_spec⟩⟩
    let newNonempty := subfanExtension_nonempty fan extension included nonempty
    letI := toricSchemeIntegral extension newNonempty
    ∃ threshold : ℕ, ∀ a : ℕ, threshold ≤ a →
      linearCohomologyCriterion extension (hne.mono included)
        (invariantCartierDivisor extension newNonempty regular
          (subfanBoundaryTwist fan extension b a)) := by
  classical
  let nonempty : Nonempty fan.cones := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  let newNonempty := subfanExtension_nonempty fan extension included nonempty
  letI := toricSchemeIntegral fan nonempty
  letI := toricSchemeIntegral extension newNonempty
  letI : Fintype (completeLinearTests extension) :=
    (completeLinearTests_finite extension).fintype
  have tests (W : completeLinearTests extension) :
      ∃ threshold : ℕ, ∀ a : ℕ, threshold ≤ a →
        ∃ q : ℕ, Nontrivial (toricSubspacePullbackCohomology extension
          (invariantCartierDivisor extension newNonempty regular
            (subfanBoundaryTwist fan extension b a)).sheaf
          W.val.space W.val.rational q) := by
    apply subfanBoundaryPullbackCohomology_eventually fan extension included
      nonempty regular rayFull b W.val.space W.val.rational
    exact criterion (subfanLinearSubspace fan extension included W.val)
  choose bound eventual using tests
  refine ⟨Finset.univ.sup bound,?_⟩
  intro a large W
  let j : completeLinearTests extension := ⟨W,restrictedFan_complete extension complete W⟩
  exact eventual j a ((Finset.le_sup (f := bound) (Finset.mem_univ j)).trans large)

end ToricPower

end
