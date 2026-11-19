module

public import ToricPower.ArrangementLiftedCech
public import ToricPower.ToricCohomologyFiniteWeights

/-!
# Compact cohomological support of the actual lifted Čech diagram

For a complete smooth fan, the full character cohomology of each Cartier
label has finite support. There are finitely many normalized arrangement
cells, so the lifted diagram has only finitely many nonzero cell/character
coefficients, simultaneously in every cohomological degree. The union of
their actual translated closed cells is therefore compact.

No character cutoff enters the diagram. Finiteness is a proved property
of its cohomology, obtained from the complete-fan geometric theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TauCeti.Toric Set
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V} (fan : Fan latticeMap)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "W" => WeightedIncidenceObject A

variable {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (surjective : Function.Surjective charts) (regular : fan.IsRegular)
  (complete : fan.IsComplete) (anchor : Index) (b : fan.Ray → ℤ)

/-- Every actual integral cell lift at which some cohomology is nonzero. -/
def arrangementLiftedCechSupport : Set W :=
  {c | ∃ q, Nontrivial
    (((arrangementLiftedCech fan basis rays charts b).obj c).homology q)}

include surjective regular complete anchor in
/-- Finiteness holds simultaneously over all cohomological degrees at
each normalized cell. -/
theorem arrangementLiftedCechWeightSupport_finite (c : IncidenceObject A) :
    {m : Fin n → ℤ | (c,m) ∈ arrangementLiftedCechSupport fan basis rays charts b}.Finite := by
  have finiteCharacters := toricCechCohomology_nonzeroWeightSet_finite fan charts
    surjective regular complete (arrangementLiftedCechCoefficients fan basis rays b c) anchor
  have injective : Function.Injective (fun m : Fin n → ℤ => -(basis.equivFun.symm m)) :=
    fun _ _ h => basis.equivFun.symm.injective (neg_injective h)
  apply (Set.Finite.preimage injective.injOn finiteCharacters).subset
  rintro m ⟨q, hq⟩
  exact ⟨q, (arrangementLiftedCech_nontrivial_iff fan basis rays charts b (c,m) q).mp hq⟩

include surjective regular complete anchor in
/-- All integral translates and all degrees together have finite
cohomological support. -/
theorem arrangementLiftedCechSupport_finite :
    (arrangementLiftedCechSupport fan basis rays charts b).Finite := by
  have finiteImages : (⋃ c : IncidenceObject A,
      (Prod.mk c) '' {m | (c,m) ∈ arrangementLiftedCechSupport fan basis rays charts b}).Finite :=
    Set.finite_iUnion fun c =>
      (arrangementLiftedCechWeightSupport_finite fan basis rays charts
        surjective regular complete anchor b c).image (Prod.mk c)
  apply finiteImages.subset
  intro c hc
  exact Set.mem_iUnion.mpr ⟨c.1, Set.mem_image_of_mem (Prod.mk c.1) hc⟩

/-- The literal universal-arrangement cell of a character coefficient.
The negative translation matches the `-m` Laurent character. -/
def arrangementLiftedClosedCell (c : W) : Set (Fin n → ℝ) :=
  let lifted := translateCell A (-c.2) c.1.2.val
  closedCell (augmentedForms A) lifted.val.1 lifted.val.2

/-- Each individual carrier is the genuine compact closed polyhedron. -/
theorem arrangementLiftedClosedCell_isCompact (c : W) :
    IsCompact (arrangementLiftedClosedCell fan basis rays c) :=
  closedCell_isCompact A _ _

/-- A closed geometric carrier containing every nonzero lifted cell. -/
def arrangementLiftedCechCompactCarrier : Set (Fin n → ℝ) :=
  ⋃ c ∈ arrangementLiftedCechSupport fan basis rays charts b,
    arrangementLiftedClosedCell fan basis rays c

include surjective regular complete anchor in
/-- Compactness is derived from actual all-character cohomological
finiteness, rather than imposed as a condition on the lift. -/
theorem arrangementLiftedCechCompactCarrier_isCompact :
    IsCompact (arrangementLiftedCechCompactCarrier fan basis rays charts b) :=
  (arrangementLiftedCechSupport_finite fan basis rays charts
    surjective regular complete anchor b).isCompact_biUnion
      (fun c _ => arrangementLiftedClosedCell_isCompact fan basis rays c)

end ToricPower

end
