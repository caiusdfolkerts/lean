import Characterizations.MinimalLocal
import CommAlg.IntegralClosure.OrdinaryRees
import CommAlg.Polymatroid.IdealBridge

/-!
# The zero-ideal obstruction to an unrestricted regularity formula

The paper admits the zero ideal among polymatroidal ideals. Its Tor support is
empty, so the maximum defining regularity is not attained at any natural number.
Nevertheless every maximal-ideal power times zero is polymatroidal, and the least
such exponent is zero. This is an explicit boundary-case obstruction to reading
Proposition 4.1's regularity conclusion without a nonzero-ideal restriction.
-/

noncomputable section

namespace Characterizations

open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem zero_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0, ?_⟩, ?_⟩ <;> simp [Equigenerated, ExchangeAxiom]

theorem empty_family_equigenerated_two : Equigenerated (∅ : Family V) 2 := by
  simp [Equigenerated]

theorem empty_family_betti_zero (a : Exponent V) (i : ℕ) :
    bettiNumber (k := k) (∅ : Family V) a i = 0 := by
  by_contra h
  exact gradedBettiNonzero_empty a i
    ((bettiNumber_pos_iff _ _ _).mp (Nat.pos_of_ne_zero h))

/-- The actual zero ideal has no attained natural-number Tor regularity. -/
theorem zero_ideal_no_torRegularity :
    ¬ ∃ r : ℕ, IsTorRegularity (k := k) (∅ : Family V) r := by
  rintro ⟨r, _, i, a, ha, _⟩
  exact ha (empty_family_betti_zero a i)

theorem empty_localize_polymatroidal (U : Finset V) :
    IsPolymatroidal (localize (∅ : Family V) U) := by
  simpa [localize, minimalFamily] using (zero_family_polymatroidal (V := V))

theorem empty_thickening_polymatroidal (q : ℕ) :
    IsPolymatroidal (thickening (∅ : Family V) q) := by
  simpa [thickening] using (zero_family_polymatroidal (V := V))

theorem zero_ideal_least_polymatroidal_power :
    IsLeast {q : ℕ | IsPolymatroidal (thickening (∅ : Family V) q)} 0 :=
  ⟨empty_thickening_polymatroidal 0, fun _ _ => Nat.zero_le _⟩

theorem zero_ideal_integralClosure :
    {f : MvPolynomial V k | IntegralOverIdeal (⊥ : Ideal (MvPolynomial V k)) f} =
      (⊥ : Ideal (MvPolynomial V k)) := by
  ext f
  exact ⟨fun h => integrallyClosed_bot f h, fun h => integralOverIdeal_of_mem h⟩

theorem zero_ideal_closure_quotient_finiteLength :
    IsFiniteLength (MvPolynomial V k)
      (Strands.idealDifferenceQuotient (k := k) (∅ : Family V) ∅) := by
  apply Strands.idealDifferenceQuotient_finiteLength
  have he : {a : Exponent V | Contains (∅ : Family V) a ∧ ¬Contains ∅ a} = ∅ := by
    ext a
    simp
  rw [he]
  exact Set.finite_empty

/-- Multiplication by an actual maximal-ideal power cannot alter zero. -/
theorem zero_ideal_all_actual_powers_polymatroidal (q : ℕ) :
    IsPolymatroidalIdeal
      ((Ideal.span (Set.range (MvPolynomial.X : V → MvPolynomial V k))) ^ q * ⊥) := by
  simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))

/-- Formal negation of the unrestricted attained-regularity version of the
"in particular" conclusion of Proposition 4.1. The counterexample is the
empty minimal generating family, representing the actual zero ideal. -/
theorem unrestricted_proposition41_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
          IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r - 2)) := by
  intro h
  obtain ⟨r, hr, _⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  exact zero_ideal_no_torRegularity ⟨r, hr⟩

/-- The actual nonzero Tor degrees `j-i`, embedded in the integers with a
bottom element representing negative infinity. -/
def torRegularityDegrees (B : Family V) : Set (WithBot ℤ) :=
  {x | ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧
    x = (((a.degree : ℤ) - i : ℤ) : WithBot ℤ)}

theorem zero_ideal_regularityDegrees_empty :
    torRegularityDegrees (k := k) (∅ : Family V) = ∅ := by
  ext x
  simp [torRegularityDegrees, empty_family_betti_zero]

/-- Under the standard extended convention, regularity of zero is negative
infinity, the least upper bound of its empty actual Tor-degree support. -/
theorem zero_ideal_extended_regularity :
    IsLUB (torRegularityDegrees (k := k) (∅ : Family V)) ⊥ := by
  rw [zero_ideal_regularityDegrees_empty]
  exact isLUB_empty

/-- Subtracting the chosen generating degree two from negative infinity
still does not give the actual least polymatroidal power, which is zero.
Addition of the embedded integer `-2` is the usual finite degree shift. -/
theorem zero_ideal_extended_regularity_difference_ne_least :
    (0 : WithBot ℤ) ≠ (⊥ : WithBot ℤ) + ((-2 : ℤ) : WithBot ℤ) := by
  simp

/-- The unrestricted formula is false even when regularity is interpreted
as an extended least upper bound, with `reg(0) = -∞`. -/
theorem unrestricted_proposition41_extended_regularity_false :
    ¬ (∀ B : Family V, Equigenerated B 2 →
      (∀ U : Finset V, U ⊂ univ → IsPolymatroidal (localize B U)) →
        ∃ r : WithBot ℤ, IsLUB (torRegularityDegrees (k := k) B) r ∧
          ∃ q : ℕ, IsLeast {n : ℕ | IsPolymatroidal (thickening B n)} q ∧
            ((q : ℤ) : WithBot ℤ) = r + ((-2 : ℤ) : WithBot ℤ)) := by
  intro h
  obtain ⟨r, hr, q, _, he⟩ := h ∅ empty_family_equigenerated_two
    (fun U _ => empty_localize_polymatroidal U)
  have hr0 : r = ⊥ := hr.unique zero_ideal_extended_regularity
  simpa [hr0] using he

end Characterizations
