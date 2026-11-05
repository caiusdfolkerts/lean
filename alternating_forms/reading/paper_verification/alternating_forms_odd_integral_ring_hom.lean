module

public import PaperVerification.AlternatingFormsOddIntegralPrincipal

/-!
# Arbitrary ring homomorphisms in the integral base-change assertion

The endpoint is quantified over every commutative target ring and every
ring homomorphism out of the paper's Laurent coefficient ring.  All
compatible algebra structures are constructed from that homomorphism,
so no extra algebra or scalar-tower hypothesis remains in the statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms.IntegralOdd

def paper_theorem_7_1_integral_arbitrary_base_change
    (k : ℕ) (T : Type*) [CommRing T] (φ : IntegralLaurentRing k →+* T) :
    Module.Basis (FullGoodOddIndex k) T
      (ExteriorAlgebra T (Fin (2*k+1) → T) ⧸
        exteriorRelationIdeal
          (weightedFirstForm T (fun i => Units.map φ.toMonoidHom (integralLaurentEdge k i)))
          (weightedSecondForm T (fun i => Units.map φ.toMonoidHom (integralLaurentEdge k i)))) := by
  letI : Algebra (IntegralLaurentRing k) T := φ.toAlgebra
  letI : Algebra (IntegralCoefficientRing k) T :=
    (φ.comp (algebraMap (IntegralCoefficientRing k) (IntegralLaurentRing k))).toAlgebra
  letI : IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T :=
    IsScalarTower.of_algebraMap_eq' (R := IntegralCoefficientRing k)
      (S := IntegralLaurentRing k) (A := T) rfl
  exact paper_theorem_7_1_integral_full_basis_after_base_change k T

set_option maxRecDepth 4000 in
@[simp] theorem paper_theorem_7_1_integral_arbitrary_base_change_apply
    (k : ℕ) (T : Type*) [CommRing T] (φ : IntegralLaurentRing k →+* T)
    (s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_arbitrary_base_change k T φ ⟨s,I⟩ =
      Ideal.Quotient.mk _
        (exteriorPower.ιMulti T s
          (fun i => Pi.basisFun T (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra T (Fin (2*k+1) → T)) := by
  letI : Algebra (IntegralLaurentRing k) T := φ.toAlgebra
  letI : Algebra (IntegralCoefficientRing k) T :=
    (φ.comp (algebraMap (IntegralCoefficientRing k) (IntegralLaurentRing k))).toAlgebra
  letI : IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T :=
    IsScalarTower.of_algebraMap_eq' (R := IntegralCoefficientRing k)
      (S := IntegralLaurentRing k) (A := T) rfl
  change paper_theorem_7_1_integral_full_basis_after_base_change k T ⟨s,I⟩ = _
  exact paper_theorem_7_1_integral_full_basis_after_base_change_apply k T s I

end PaperVerification.AlternatingForms.IntegralOdd
