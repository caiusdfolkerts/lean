module
public import mixed_results.coordinate_ideal_primary
public import shared_results.part011
public import shared_results.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedPrimaryDecomposition -/
section

/-!
# The finite cover formula for mixed products

The covers are the actual minimal vertex covers of the colored row family.
Only their original-row variables generate the ideals on the right. The
power attached to a cover is the sum of the multiplicities of its absent
colors. In particular a zero exponent gives the whole ring, exactly as in
the paragraph following Corollary 5.6.

The proof reduces coefficient membership to the ordinary colored power,
uses the proved network cover theorem, and separates its color weight from
its original-variable weight. The equality holds over every commutative
coefficient ring; over a field these are the displayed coordinate-prime
powers of the paper.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers
open Classical MvPolynomial

theorem coverWeight_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset V) (a : V →₀ ℕ) :
    coverWeight C a = ∑ v, if v ∈ C then a v else 0 := by
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter, coverWeight] using
    (Finset.sum_filter (s := Finset.univ) (fun v => v ∈ C) (fun v => a v))

theorem coverWeight_renameEquiv {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (C : Finset W) (a : V →₀ ℕ) :
    coverWeight C (a.mapDomain e) = ∑ v, if e v ∈ C then a v else 0 := by
  rw [coverWeight_eq_sum]
  rw [← e.sum_comp (fun w => if w ∈ C then (a.mapDomain e) w else 0)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finsupp.mapDomain_apply_of_injective e.injective a v]

end FourPapers

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
universe u
variable {d r : ℕ} (n : Fin d → ℕ)

/-- The coefficient-free minimal covers used by the ordinary colored
network theorem. There are finitely many because the row variables are finite. -/
abbrev MinimalColoredCover (E : Fin r → Finset (FiniteTuple n)) :=
  {C : Finset (RowCutNetwork.Label (coloredRows (r := r) n)) //
    RowCutNetwork.IsMinimalCover (coloredRows (r := r) n) (coloredFamily n E) C}

instance minimalColoredCover_finite (E : Fin r → Finset (FiniteTuple n)) :
    Finite (MinimalColoredCover n E) := by infer_instance

/-- The original variables belonging to a colored cover. -/
def coverBaseVariables (C : Finset (RowCutNetwork.Label (coloredRows (r := r) n))) :
    Finset (FiniteVariable.{u} n) :=
  Finset.univ.filter fun v => (⟨v.1.succ, v.2.down⟩ :
    RowCutNetwork.Label (coloredRows (r := r) n)) ∈ C

def coveredColorMultiplicity
    (C : Finset (RowCutNetwork.Label (coloredRows (r := r) n)))
    (m : ULift.{u} (Fin r) →₀ ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter (fun c : ULift.{u} (Fin r) =>
    (⟨0, c.down⟩ : RowCutNetwork.Label (coloredRows (r := r) n)) ∈ C), m c

/-- Exactly the sum over colors whose variable does not belong to the cover. -/
def absentColorMultiplicity
    (C : Finset (RowCutNetwork.Label (coloredRows (r := r) n)))
    (m : ULift.{u} (Fin r) →₀ ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter (fun c : ULift.{u} (Fin r) =>
    (⟨0, c.down⟩ : RowCutNetwork.Label (coloredRows (r := r) n)) ∉ C), m c

theorem colorMultiplicity_partition
    (C : Finset (RowCutNetwork.Label (coloredRows (r := r) n)))
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    coveredColorMultiplicity n C m + absentColorMultiplicity n C m = m.degree := by
  rw [coveredColorMultiplicity, absentColorMultiplicity,
    Finset.sum_filter_add_sum_filter_not]
  simp only [Finsupp.degree_eq_weight_one, Finsupp.weight_eq_sum,
    smul_eq_mul, mul_one]

theorem colored_coverWeight
    (C : Finset (RowCutNetwork.Label (coloredRows (r := r) n)))
    (m : ULift.{u} (Fin r) →₀ ℕ) (a : Exponent (FiniteVariable.{u} n)) :
    coverWeight C ((coloredExponent m a).mapDomain
      (finiteVariableEquiv (coloredRows (r := r) n))) =
        coveredColorMultiplicity n C m + coverWeight (coverBaseVariables n C) a := by
  rw [coverWeight_renameEquiv]
  rw [← (coloredVariableEquiv n).sum_comp
    (fun v => if finiteVariableEquiv (coloredRows (r := r) n) v ∈ C
      then coloredExponent m a v else 0), Fintype.sum_sum_type]
  change
    (∑ c : ULift.{u} (Fin r),
      if (⟨0,c.down⟩ : RowCutNetwork.Label (coloredRows (r := r) n)) ∈ C then m c else 0) +
    (∑ v : FiniteVariable.{u} n,
      if (⟨v.1.succ,v.2.down⟩ : RowCutNetwork.Label (coloredRows (r := r) n)) ∈ C
        then a v else 0) = _
  simp only [coveredColorMultiplicity, coverBaseVariables, coverWeight, Finset.sum_filter]

/-- The ordinary cover formula in the exact exponent coordinates used by
the monomial Koszul construction. -/
theorem finitePower_contains_minimalCovers (E : Finset (FiniteTuple n))
    (hE : finiteLatticeClosed n E) (s : ℕ) (a : Exponent (FiniteVariable.{u} n)) :
    Contains (exponentPowerFamily (finiteRowFamily n E) s) a ↔
      ∀ C : {C : Finset (RowCutNetwork.Label n) // RowCutNetwork.IsMinimalCover n E C},
        s ≤ coverWeight C.val (a.mapDomain (finiteVariableEquiv n)) := by
  rw [← monomial_mem_iff (k := ULift.{u} ℤ), finitePowerFamily_ideal]
  have hmove :
      monomial a (1 : ULift.{u} ℤ) ∈ finiteSublatticeIdeal n E ^ s ↔
        monomial (a.mapDomain (finiteVariableEquiv n)) (1 : ULift.{u} ℤ) ∈
          RowCutNetwork.monomialIdeal n (ULift.{u} ℤ) E ^ s := by
    have h := (Ideal.apply_mem_of_equiv_iff
      (f := (finiteLabelPolynomialEquiv (K := ULift.{u} ℤ) n).toRingEquiv)
      (I := finiteSublatticeIdeal n (k := ULift.{u} ℤ) E ^ s)
      (x := monomial a 1)).symm
    change monomial a (1 : ULift.{u} ℤ) ∈ finiteSublatticeIdeal n E ^ s ↔
      (finiteLabelPolynomialEquiv (K := ULift.{u} ℤ) n).toRingEquiv
        (monomial a 1) ∈
      Ideal.map (finiteLabelPolynomialEquiv (K := ULift.{u} ℤ) n).toRingEquiv.toRingHom
        (finiteSublatticeIdeal n E ^ s) at h
    rw [finiteSublatticeIdeal_power_rename] at h
    change monomial a (1 : ULift.{u} ℤ) ∈ finiteSublatticeIdeal n E ^ s ↔
      rename (finiteVariableEquiv n) (monomial a 1) ∈
        RowCutNetwork.monomialIdeal n (ULift.{u} ℤ) E ^ s at h
    rw [rename_monomial] at h
    exact h
  rw [hmove, RowCutNetwork.power_eq_iInf_minimalCover n E hE.1 hE.2 s]
  simp only [Submodule.mem_iInf, monomial_mem_coordinateIdeal_power_iff]

theorem mixed_contains_minimalCovers (E : Fin r → Finset (FiniteTuple n))
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    Contains (mixedRowPowerFamily n E m) a ↔
      ∀ C : MinimalColoredCover n E,
        absentColorMultiplicity n C.val m ≤ coverWeight (coverBaseVariables n C.val) a := by
  rw [← coloredPower_contains_iff n E m a,
    finitePower_contains_minimalCovers (coloredRows (r := r) n) (coloredFamily n E)
      ((coloredLatticeClosed_iff n E).mp hE)]
  apply forall_congr'
  intro C
  rw [colored_coverWeight]
  have h := colorMultiplicity_partition n C.val m
  omega

/-- **The finite mixed cover formula after Corollary 5.6.** These are the
literal original ideals, the literal coordinate ideals of their colored
minimal covers, and exactly the absent-color exponents from the paper. -/
theorem mixed_cover_power_intersection {K : Type u} [CommRing K]
    (E : Fin r → Finset (FiniteTuple n)) (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct (coloredIdeals (k := K) n E) m =
      ⨅ C : MinimalColoredCover n E,
        coordinateIdeal (k := K) (coverBaseVariables n C.val) ^
          absentColorMultiplicity n C.val m := by
  apply Ideal.ext
  intro f
  rw [← mixedRowPowerFamily_ideal n E K m, mem_monomialIdeal_iff, Submodule.mem_iInf]
  constructor
  · intro h C
    apply (mem_coordinateIdeal_power_iff _ _ f).mpr
    intro a ha
    exact (mixed_contains_minimalCovers n E hE m a).mp (h a ha) C
  · intro h a ha
    apply (mixed_contains_minimalCovers n E hE m a).mpr
    intro C
    exact (mem_coordinateIdeal_power_iff _ _ f).mp (h C) a ha

/-- Covers with positive absent-color multiplicity are exactly the
nonunit components of the mixed primary decomposition. -/
abbrev RelevantColoredCover (E : Fin r → Finset (FiniteTuple n))
    (m : ULift.{u} (Fin r) →₀ ℕ) :=
  {C : MinimalColoredCover n E // 0 < absentColorMultiplicity n C.val m}

instance relevantColoredCover_finite (E : Fin r → Finset (FiniteTuple n))
    (m : ULift.{u} (Fin r) →₀ ℕ) : Finite (RelevantColoredCover n E m) := by
  infer_instance

/-- The same literal intersection with every unit component removed. -/
theorem mixed_primary_intersection {K : Type u} [CommRing K]
    (E : Fin r → Finset (FiniteTuple n)) (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct (coloredIdeals (k := K) n E) m =
      ⨅ C : RelevantColoredCover n E m,
        coordinateIdeal (k := K) (coverBaseVariables n C.val.val) ^
          absentColorMultiplicity n C.val.val m := by
  rw [mixed_cover_power_intersection n E hE m]
  apply le_antisymm
  · apply le_iInf
    intro C
    exact iInf_le_of_le C.val le_rfl
  · apply le_iInf
    intro C
    by_cases hC : 0 < absentColorMultiplicity n C.val m
    · exact iInf_le_of_le (⟨C,hC⟩ : RelevantColoredCover n E m) le_rfl
    · have hz : absentColorMultiplicity n C.val m = 0 := by omega
      simp only [hz, pow_zero, Ideal.one_eq_top, le_top]

/-- Each retained component is primary, and its radical is exactly the
displayed base-variable prime. This makes the finite intersection an
actual primary decomposition, not merely an equality with ideal powers. -/
theorem mixed_primary_component {K : Type u} [CommRing K] [IsDomain K]
    (E : Fin r → Finset (FiniteTuple n)) (m : ULift.{u} (Fin r) →₀ ℕ)
    (C : RelevantColoredCover n E m) :
    (coordinateIdeal (k := K) (coverBaseVariables n C.val.val) ^
        absentColorMultiplicity n C.val.val m).IsPrimary ∧
    (coordinateIdeal (k := K) (coverBaseVariables n C.val.val) ^
        absentColorMultiplicity n C.val.val m).radical =
      coordinateIdeal (coverBaseVariables n C.val.val) ∧
    (coordinateIdeal (k := K) (coverBaseVariables n C.val.val)).IsPrime :=
  ⟨coordinateIdeal_power_isPrimary _ _ C.property,
    coordinateIdeal_power_radical _ _ C.property,
    coordinateIdeal_isPrime _⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.mixed_cover_power_intersection
#print axioms FourPapers.Sublattice.mixed_primary_intersection
#print axioms FourPapers.Sublattice.mixed_primary_component

end
end
end

end
