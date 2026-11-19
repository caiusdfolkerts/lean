module

public import ToricPower.FanCellShrinking
public import ToricPower.ArrangementNormalizedSupport

/-!
# One shrinking threshold for every possible maximal support cell

The original quotient incidence category is finite. Taking a maximum of
its actual geometric bounds gives one positive threshold which works
for every larger integer, independently of the unbounded target whose
maximal cell will later be chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

/-- Exactly those normalized cells whose genuine normal space is
covered by the integral faces of the original fan. -/
def NormalCoveredNormalizedCell :=
  {c : IncidenceObject (fanArrangementMatrix fan basis rays) //
    ∀ v ∈ universalCellFanNormal fan basis rays
      (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c),
    ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
      (universalCellCharacter fan basis rays
        (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c)) σ}

instance normalCoveredNormalizedCell_finite :
    Finite (NormalCoveredNormalizedCell fan regular basis rays) :=
  inferInstanceAs (Finite {c : IncidenceObject (fanArrangementMatrix fan basis rays) // _})

/-- The target-independent threshold keeps the exact integral affine
compatibility and the complete original bounded test carrier. -/
theorem normalizedCells_uniform_shrinking
    (m : NormalCoveredNormalizedCell fan regular basis rays → Fin n → ℤ)
    (K : Set (Fin n → ℝ)) (bounded : Bornology.IsBounded K) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ ell : ℕ, threshold ≤ ell →
      ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
        ∃ v₀ u : Fin n → ℤ,
          cellCenter (augmentedForms (fanArrangementMatrix fan basis rays))
              (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c.val).2 -
            latticeLift v₀ ∈
              cellDirection (augmentedForms (fanArrangementMatrix fan basis rays))
                (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c.val).2.val.2 ∧
          latticeLift u + latticeLift (m c) - (ell : ℝ) • latticeLift v₀ ∈
            cellDirection (augmentedForms (fanArrangementMatrix fan basis rays))
              (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c.val).2.val.2 ∧
          ∀ z ∈ K, powerInverseBranchPoint ell u z ∈
            localStar (augmentedForms (fanArrangementMatrix fan basis rays))
              (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays))
                (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c.val).2) := by
  classical
  letI : Fintype (NormalCoveredNormalizedCell fan regular basis rays) := Fintype.ofFinite _
  have bounds := fun c : NormalCoveredNormalizedCell fan regular basis rays =>
    universalCell_shrinking_of_normalCover fan basis rays regular
      (normalizedUniversalCell (fanArrangementMatrix fan basis rays) c.val)
      c.property (m c) K bounded
  choose center center_mem localThreshold localPositive shrink using bounds
  refine ⟨Finset.univ.sup localThreshold + 1,by omega,?_⟩
  intro ell large c
  have atLeast : localThreshold c ≤ ell :=
    (Finset.le_sup (f := localThreshold) (Finset.mem_univ c)).trans (by omega)
  obtain ⟨u,compatible,inside⟩ := shrink c ell atLeast
  exact ⟨center c,u,center_mem c,compatible,inside⟩

end ToricPower

end
