module

public import PaperVerification.AlternatingFormsOddWeightedIntegral
public import PaperVerification.AlternatingFormsExteriorFullBasis

/-!
# The integral statement following Theorem 7.1

This endpoint is a free basis of the full, literal exterior-algebra ideal
quotient over the precise Laurent coefficient ring in the paper.  It also
constructs the same literal good-word basis after every algebra base
change.  The proof includes all degrees and uses the actual homogeneous
decomposition to identify their direct sum with the full quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms.IntegralOdd

abbrev FullGoodOddIndex (k : ℕ) := Σ s : ℕ, GoodOddIndex k s

abbrev IntegralLaurentQuotient (k : ℕ) :=
  ExteriorAlgebra (IntegralLaurentRing k) (Fin (2*k+1) → IntegralLaurentRing k) ⧸
    exteriorRelationIdeal
      (weightedFirstForm (IntegralLaurentRing k) (integralLaurentEdge k))
      (weightedSecondForm (IntegralLaurentRing k) (integralLaurentEdge k))

/-- The full integral weighted-coefficient assertion printed immediately
after Theorem 7.1, with no omitted high-degree component. -/
def paper_theorem_7_1_integral_full_basis (k : ℕ) :
    Module.Basis (FullGoodOddIndex k) (IntegralLaurentRing k) (IntegralLaurentQuotient k) :=
  exteriorFullBasisOfDegreeBases _ _ (paper_integral_laurent_basis k)

@[simp] theorem paper_theorem_7_1_integral_full_basis_apply
    (k s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_full_basis k ⟨s,I⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal
        (weightedFirstForm (IntegralLaurentRing k) (integralLaurentEdge k))
        (weightedSecondForm (IntegralLaurentRing k) (integralLaurentEdge k)))
        (exteriorPower.ιMulti (IntegralLaurentRing k) s
          (fun i => Pi.basisFun (IntegralLaurentRing k) (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra (IntegralLaurentRing k) (Fin (2*k+1) → IntegralLaurentRing k)) := by
  rw [paper_theorem_7_1_integral_full_basis]
  rw [exteriorFullBasisOfDegreeBases_apply _ _ _
    (fun s I => powerBasis (IntegralLaurentRing k) s (2*k+1) I.val)]
  · rw [powerBasis_apply]
  · intro d J
    exact paper_integral_laurent_basis_apply k d J

variable (k : ℕ) (T : Type*) [CommRing T]
  [Algebra (IntegralCoefficientRing k) T] [Algebra (IntegralLaurentRing k) T]
  [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T]

def baseChangedEdge (i : Fin (2*k)) : Tˣ :=
  Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom (integralLaurentEdge k i)

abbrev IntegralBaseChangedQuotient :=
  ExteriorAlgebra T (Fin (2*k+1) → T) ⧸
    exteriorRelationIdeal (weightedFirstForm T (baseChangedEdge k T))
      (weightedSecondForm T (baseChangedEdge k T))

/-- The full free good-monomial basis survives arbitrary base change from
the paper's integral Laurent coefficient ring, including nonreduced rings. -/
def paper_theorem_7_1_integral_full_basis_after_base_change :
    Module.Basis (FullGoodOddIndex k) T (IntegralBaseChangedQuotient k T) :=
  exteriorFullBasisOfDegreeBases _ _
    (fun s => paper_integral_laurent_basis_after_base_change k s T)

@[simp] theorem paper_theorem_7_1_integral_full_basis_after_base_change_apply
    (s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_full_basis_after_base_change k T ⟨s,I⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal
        (weightedFirstForm T (baseChangedEdge k T))
        (weightedSecondForm T (baseChangedEdge k T)))
        (exteriorPower.ιMulti T s
          (fun i => Pi.basisFun T (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra T (Fin (2*k+1) → T)) := by
  rw [paper_theorem_7_1_integral_full_basis_after_base_change]
  rw [exteriorFullBasisOfDegreeBases_apply _ _ _
    (fun s I => powerBasis T s (2*k+1) I.val)]
  · rw [powerBasis_apply]
  · intro d J
    exact paper_integral_laurent_basis_after_base_change_apply k d T J

end PaperVerification.AlternatingForms.IntegralOdd
