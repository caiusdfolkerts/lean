module
public import paper_results.alcove_rees_fiber_monoid
public import Mathlib.RingTheory.MvPolynomial.Ideal

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81AnalyticSpread -/
section

/-!
# Analytic spread in Theorem 8.1

The special fiber is the conventional Rees algebra modulo the extension
of the homogeneous maximal ideal. Its identification with the Hibi algebra
uses the genuine excess-degree quotient, and its dimension is Mathlib's
prime-spectrum Krull dimension.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid FiniteDistributive
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  {k : Type u} [Field k]

/-- Restricting the coefficient field does not change the Rees carrier
or its canonical action by the original polynomial ring. -/
instance standardReesAlgebra_polynomialAlgebra :
    Algebra (MvPolynomial (FiniteVariable.{u} n) k) (standardReesAlgebra (k := k) E) :=
  inferInstanceAs (Algebra (MvPolynomial (FiniteVariable.{u} n) k)
    ↥(reesAlgebra (finiteSublatticeIdeal n (k := k) E)))

instance standardReesAlgebra_polynomialTower :
    IsScalarTower k (MvPolynomial (FiniteVariable.{u} n) k)
      (standardReesAlgebra (k := k) E) :=
  inferInstanceAs (IsScalarTower k (MvPolynomial (FiniteVariable.{u} n) k)
    ↥(reesAlgebra (finiteSublatticeIdeal n (k := k) E)))

/-- The quotient uses the standard ideal-quotient structure on this
unchanged Rees carrier. Giving the carrier explicitly avoids asking
instance search to unfold the scalar restriction. -/
local instance standardReesAlgebra_hasQuotient :
    HasQuotient ↥(standardReesAlgebra (k := k) E)
      (Ideal ↥(standardReesAlgebra (k := k) E)) :=
  @Ideal.instHasQuotient ↥(standardReesAlgebra (k := k) E) inferInstance

/-- The extended homogeneous maximal ideal in the literal Rees algebra. -/
def finiteReesFiberIdeal (E : Finset (FiniteTuple n)) : Ideal (standardReesAlgebra (k:=k) E) :=
  (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).map
    (algebraMap (MvPolynomial (FiniteVariable.{u} n) k) (standardReesAlgebra (k:=k) E))

/-- The conventional special fiber R(I)/mR(I). -/
abbrev finiteReesSpecialFiber (E : Finset (FiniteTuple n)) :=
  ↥(standardReesAlgebra (k:=k) E) ⧸ finiteReesFiberIdeal (k:=k) E

/-- The special fiber carries the canonical ideal-quotient ring structure. -/
instance finiteReesSpecialFiber_commRing :
    CommRing (finiteReesSpecialFiber (k := k) E) :=
  @Ideal.Quotient.commRing ↥(standardReesAlgebra (k := k) E)
    inferInstance (finiteReesFiberIdeal (k := k) E)

def finiteReesMonoidStandardEquiv (E : Finset (FiniteTuple n)) :
    AddMonoidAlgebra k (finiteReesExponentMonoid.{u} E) ≃ₐ[k] standardReesAlgebra (k:=k) E :=
  (finiteReesMonoidEquiv E k).trans (finiteReesStandardEquiv E)

theorem finiteReesMonoidStandardEquiv_base (x : FiniteVariable.{u} n) :
    finiteReesMonoidStandardEquiv (k:=k) E
      (AddMonoidAlgebra.single (finiteReesBaseIndex E x) 1)=
        algebraMap (MvPolynomial (FiniteVariable.{u} n) k)
          (standardReesAlgebra (k:=k) E) (MvPolynomial.X x) := by
  apply Subtype.ext
  change MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)
    (finiteReesMonoidEquiv E k (AddMonoidAlgebra.single (finiteReesBaseIndex E x) 1)).val=
      Polynomial.C (MvPolynomial.X x)
  rw [finiteReesMonoidEquiv_single]
  exact MvPolynomial.optionEquivLeft_X_some k (FiniteVariable.{u} n) x

theorem finiteReesFiberIdeal_eq_excess_map (hE : finiteLatticeClosed n E) :
    finiteReesFiberIdeal (k:=k) E =
      (GradedMonoidFiber.positiveIdeal (k:=k) (finiteReesExcessDegree.{u} E)).map
        (finiteReesMonoidStandardEquiv (k:=k) E).toRingHom := by
  rw [finiteReesExcessIdeal_eq_variables hE,finiteReesFiberIdeal,
    MvPolynomial.idealOfVars,Ideal.map_span,Ideal.map_span,← Set.range_comp',← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext x
  exact (finiteReesMonoidStandardEquiv_base (k:=k) x).symm

def finiteReesFiberMonoidQuotientEquiv (hE : finiteLatticeClosed n E) :
    (AddMonoidAlgebra k (finiteReesExponentMonoid.{u} E) ⧸
      GradedMonoidFiber.positiveIdeal (k:=k) (finiteReesExcessDegree.{u} E)) ≃ₐ[k]
        finiteReesSpecialFiber (k:=k) E :=
  Ideal.quotientEquivAlg _ _ (finiteReesMonoidStandardEquiv E)
    (finiteReesFiberIdeal_eq_excess_map hE)

variable (hE : finiteLatticeClosed n E) (hne : E.Nonempty)

/-- An actual algebra isomorphism from the conventional special fiber to
the Hibi monomial algebra, over every field. -/
def theorem81_specialFiberHibiEquiv :
    finiteReesSpecialFiber (k:=k) E ≃ₐ[k] hibiAlgebra (AlcoveLattice hE) k := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact (finiteReesFiberMonoidQuotientEquiv hE).symm.trans
    ((GradedMonoidFiber.quotientEquiv (k:=k) (finiteReesExcessDegree.{u} E)).trans
      ((AddMonoidAlgebra.domCongr k k (orderConeReesMinimalEquiv.{u} hE hne).symm).trans
        (orderConeHibiAlgebraEquiv (AlcoveLattice hE) k)))

/-- The analytic spread is the Krull dimension of R(I)/mR(I). -/
def finiteSublatticeAnalyticSpread : WithBot ℕ∞ :=
  ringKrullDim (finiteReesSpecialFiber (k:=k) E)

theorem theorem81_analyticSpread :
    finiteSublatticeAnalyticSpread (k:=k) (E:=E) =
      ((finiteLatticeHeight hE hne+1 : ℕ) : WithBot ℕ∞) := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  unfold finiteSublatticeAnalyticSpread
  rw [ringKrullDim_eq_of_ringEquiv (theorem81_specialFiberHibiEquiv (k:=k) hE hne).toRingEquiv]
  exact hibiAlgebra_ringKrullDim (AlcoveLattice hE) k

end FourPapers.Sublattice

end
end
end


end
