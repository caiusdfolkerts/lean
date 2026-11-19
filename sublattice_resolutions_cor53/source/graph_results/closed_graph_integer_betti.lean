module
public import shared_results.part021
public import shared_results.part011

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIntegerBetti -/
section

/-! # Theorem 1.1 in every integer ordinary degree

These are integer-graded submodules of the actual derived Tor of the
original graph ideals. The negative pieces vanish because polynomial
and exterior degrees are nonnegative, as established in
`OrdinaryIntegerTor`; no assertion is inserted by a zero-value convention.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

universe u
variable {N : ℕ} {K : Type u} [Field K]

def graphBinomialIntegerBetti (G : SimpleGraph (Fin N)) (s p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber (graphBinomialPowerData (K := K) G s)
    (graphBinomialPower_homogeneous G s) p q

def graphMonomialIntegerBetti (G : SimpleGraph (Fin N)) (s p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber (graphMonomialPowerData (K := K) G s)
    (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily G s)) p q

@[simp] theorem graphBinomialIntegerBetti_nat (G : SimpleGraph (Fin N)) (s p q : ℕ) :
    graphBinomialIntegerBetti (K := K) G s p (q : ℤ) = graphBinomialBetti (K := K) G s p q :=
  ordinaryIntegerIdealBettiNumber_nat _ _ p q

@[simp] theorem graphMonomialIntegerBetti_nat (G : SimpleGraph (Fin N)) (s p q : ℕ) :
    graphMonomialIntegerBetti (K := K) G s p (q : ℤ) = graphMonomialBetti (K := K) G s p q :=
  ordinaryIntegerIdealBettiNumber_nat _ _ p q

/-- Paper Theorem 1.1, retaining all integer ordinary degrees, every
field, every positive power, and the original closed labeling. -/
theorem theorem11_integer_bettiEquality (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s : ℕ) (hs : 0 < s) (p : ℕ) (q : ℤ) :
    graphBinomialIntegerBetti (K := K) G s p q = graphMonomialIntegerBetti (K := K) G s p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, graphBinomialIntegerBetti_nat, graphMonomialIntegerBetti_nat]
    exact theorem11_bettiEquality G hG s hs p q.toNat
  · have hq' : q < 0 := lt_of_not_ge hq
    unfold graphBinomialIntegerBetti graphMonomialIntegerBetti
    rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hq',
      ordinaryIntegerIdealBettiNumber_negative _ _ p q hq']

end FourPapers.Sublattice

end
end
end


end
