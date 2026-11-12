module

public import ToricPower.FanNegativeIncidenceContraction
public import ToricPower.FiniteHalfspaceBoundedness
public import ToricPower.IntegralDualLattice
public import ToricPower.CechContractibleVanishing
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fintype.Powerset

/-! # Finitely many contributing weights on a complete regular fan

A negative pattern with nonzero ordinary reduced singular cohomology has
no nonzero recession direction: such a direction would contract its actual
realization. Its integral feasibility region is therefore finite. There
are only finitely many negative patterns, giving finitely many characters
with any nonzero reduced cohomology, across all degrees simultaneously.

This is a genuine finiteness theorem for the entire integral character
lattice. It imposes no bound, positivity assumption, or divisibility
restriction on the input divisor coefficients.
-/

@[expose] public noncomputable section

open TauCeti.Toric
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open ToricPower.CechReducedSingular
open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace ToricPower

section Definitions

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Ray Index : Type} [Finite Ray]
  (fan : Fan i) (charts : Index → fan.cones) (surjective : Function.Surjective charts)
  (rays : Ray ≃ fan.Ray) (𝕜 : Type) [Field 𝕜]

/-- Ordinary reduced singular cohomology of the selected actual fan rays,
indexed by `degree` for reduced degree `degree - 1`. -/
abbrev fanPatternCohomology (negative : Set fan.Ray) (degree : ℕ) :=
  reducedSingularCohomology 𝕜
    (incidenceRealization (fanNegativeRayIncidence fan charts rays negative) (fun _ => True)) degree

def fanCharacterNegativeSet (b : fan.Ray → ℤ) (m : N →+ ℤ) : Set fan.Ray :=
  {ρ | b ρ + m (fanRayPrimitiveGenerator fan ρ) < 0}

end Definitions

section Normed

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {Ray Index : Type} [Finite Ray]
  (fan : Fan i) (charts : Index → fan.cones) (surjective : Function.Surjective charts)
  (rays : Ray ≃ fan.Ray) (𝕜 : Type) [Field 𝕜]

variable (regular : fan.IsRegular) (complete : fan.IsComplete)

include surjective regular complete in
/-- A nonzero reduced cohomology group excludes every nonzero recession
form, including forms vanishing on some selected rays. -/
theorem fanPattern_recession_zero (negative : Set fan.Ray)
    (nonzero : ∃ degree, Nontrivial (fanPatternCohomology fan charts rays 𝕜 negative degree))
    (d : V →L[ℝ] ℝ)
    (inside : ∀ ρ : fan.Ray, ρ ∈ negative → d (fanRayRealVector fan ρ) ≤ 0)
    (outside : ∀ ρ : fan.Ray, ρ ∉ negative → 0 ≤ d (fanRayRealVector fan ρ)) : d = 0 := by
  by_contra hd
  have linear_nonzero : d.toLinearMap ≠ 0 := by
    intro equality
    apply hd
    ext x
    exact LinearMap.congr_fun equality x
  letI := fanNegativeIncidence_contractible fan charts surjective rays negative regular complete
    d.toLinearMap linear_nonzero inside outside
  obtain ⟨degree, nontrivial⟩ := nonzero
  letI := CechContractibleVanishing.reducedSingularCohomology_subsingleton
    (fanNegativeRayIncidence fan charts rays negative) (fun _ => True) 𝕜 degree
  obtain ⟨a, b, different⟩ := nontrivial.exists_pair_ne
  exact different (Subsingleton.elim a b)

include surjective regular complete in
/-- For a topologically nonzero pattern, every feasible integral character
lies in a proved bounded polyhedron in the actual continuous dual. -/
theorem fanPattern_feasibleCharacters_finite (b : fan.Ray → ℤ) (negative : Set fan.Ray)
    (nonzero : ∃ degree, Nontrivial (fanPatternCohomology fan charts rays 𝕜 negative degree)) :
    {m : N →+ ℤ | fanCharacterNegativeSet fan b m = negative}.Finite := by
  letI := fan.lattice.finiteDimensional
  let dualLattice := integralContinuousCharacter_isIntegralLattice fan.lattice
  letI := dualLattice.finiteDimensional
  let form : fan.Ray → (V →L[ℝ] ℝ) →ₗ[ℝ] ℝ := fun ρ =>
    if ρ ∈ negative then (ContinuousLinearMap.apply ℝ ℝ (fanRayRealVector fan ρ)).toLinearMap
    else -(ContinuousLinearMap.apply ℝ ℝ (fanRayRealVector fan ρ)).toLinearMap
  let bound : fan.Ray → ℝ := fun ρ =>
    if ρ ∈ negative then -(b ρ : ℝ) - 1 else (b ρ : ℝ)
  have recession_zero (d : V →L[ℝ] ℝ) (hd : ∀ ρ, form ρ d ≤ 0) : d = 0 := by
    apply fanPattern_recession_zero fan charts surjective rays 𝕜 regular complete negative nonzero d
    · intro ρ hρ
      have h := hd ρ
      simp only [form, if_pos hρ] at h
      exact h
    · intro ρ hρ
      have h := hd ρ
      simp only [form, if_neg hρ] at h
      change -d (fanRayRealVector fan ρ) ≤ 0 at h
      linarith
  have bounded := finiteHalfspaceIntersection_bounded form bound recession_zero
  have finite := integralLattice_preimage_finite_of_bounded dualLattice bounded
  apply finite.subset
  intro m pattern
  change ∀ ρ, form ρ (integralContinuousCharacter fan.lattice m) ≤ bound ρ
  intro ρ
  have membership : (b ρ + m (fanRayPrimitiveGenerator fan ρ) < 0) ↔ ρ ∈ negative := by
    change ρ ∈ fanCharacterNegativeSet fan b m ↔ ρ ∈ negative
    rw [pattern]
  by_cases hρ : ρ ∈ negative
  · have integer_bound : m (fanRayPrimitiveGenerator fan ρ) ≤ -b ρ - 1 := by
      have h := membership.mpr hρ
      omega
    simp only [form, bound, if_pos hρ]
    change integralContinuousCharacter fan.lattice m (i (fanRayPrimitiveGenerator fan ρ)) ≤ _
    rw [integralContinuousCharacter_lattice_apply]
    exact_mod_cast integer_bound
  · have integer_bound : -m (fanRayPrimitiveGenerator fan ρ) ≤ b ρ := by
      have h : ¬ b ρ + m (fanRayPrimitiveGenerator fan ρ) < 0 :=
        fun h => hρ (membership.mp h)
      omega
    simp only [form, bound, if_neg hρ]
    change -integralContinuousCharacter fan.lattice m (i (fanRayPrimitiveGenerator fan ρ)) ≤ _
    rw [integralContinuousCharacter_lattice_apply]
    exact_mod_cast integer_bound

include surjective regular complete in
/-- The union over every cohomological degree has only finitely many
contributing characters. The complete integral lattice remains the domain. -/
theorem completeFan_nonzeroWeightSet_finite (b : fan.Ray → ℤ) :
    {m : N →+ ℤ | ∃ degree, Nontrivial
      (fanPatternCohomology fan charts rays 𝕜 (fanCharacterNegativeSet fan b m) degree)}.Finite := by
  let fiber (negative : Set fan.Ray) : Set (N →+ ℤ) :=
    {m | fanCharacterNegativeSet fan b m = negative ∧
      ∃ degree, Nontrivial (fanPatternCohomology fan charts rays 𝕜 negative degree)}
  have finiteFiber (negative : Set fan.Ray) : (fiber negative).Finite := by
    by_cases nonzero : ∃ degree,
        Nontrivial (fanPatternCohomology fan charts rays 𝕜 negative degree)
    · exact (fanPattern_feasibleCharacters_finite fan charts surjective rays 𝕜 regular complete
        b negative nonzero).subset (fun _ h => h.1)
    · have empty : fiber negative = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro m hm
        exact nonzero hm.2
      rw [empty]
      exact Set.finite_empty
  apply (Set.finite_iUnion finiteFiber).subset
  intro m nonzero
  exact Set.mem_iUnion.mpr ⟨fanCharacterNegativeSet fan b m, rfl, nonzero⟩

end Normed

section Algebraic

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Ray Index : Type} [Finite Ray]

/-- The topology-free version used by the toric formalization. The
auxiliary norm is constructed from an actual finite basis and is absent
from the statement and from the definition of the negative-ray space. -/
theorem completeFan_nonzeroWeightSet_finite_algebraic
    (fan : Fan i) (charts : Index → fan.cones) (surjective : Function.Surjective charts)
    (rays : Ray ≃ fan.Ray) (𝕜 : Type) [Field 𝕜]
    (regular : fan.IsRegular) (complete : fan.IsComplete) (b : fan.Ray → ℤ) :
    {m : N →+ ℤ | ∃ degree, Nontrivial
      (fanPatternCohomology fan charts rays 𝕜 (fanCharacterNegativeSet fan b m) degree)}.Finite := by
  letI := fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V :=
    NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  exact completeFan_nonzeroWeightSet_finite fan charts surjective rays 𝕜 regular complete b

end Algebraic
end ToricPower
