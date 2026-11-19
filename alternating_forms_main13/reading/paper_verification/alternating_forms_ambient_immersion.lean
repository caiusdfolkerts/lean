module

public import PaperVerification.HomogeneousQuotientClosedImmersion
public import PaperVerification.AlternatingFormsUniversalCharts

/-!
# The original common-isotropic scheme in the ambient Grassmannian

The ambient Grassmannian is the projective scheme of the original Plücker
ideal, expressed as the empty tuple of isotropy conditions.  Adding the
given alternating forms induces an actual closed immersion of schemes.
This file constructs that morphism independently of the later comparison
with the zero scheme of the tautological alternating section.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- No equations beyond the original Grassmannian Plücker relations. -/
def emptyAlternatingTuple : Fin 0 → StrictPairs n → K := Fin.elim0

@[simp]
theorem isotropicPluckerIdeal_empty :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) =
      matrixPluckerIdeal := by
  simp [isotropicPluckerIdeal, emptyAlternatingTuple, Set.range_eq_empty]

@[simp]
theorem isotropicChartIdeal_empty (p : PluckerIndex (t + 2) n) :
    isotropicChartIdeal p (emptyAlternatingTuple (K := K) (n := n)) = ⊥ := by
  simp [isotropicChartIdeal, emptyAlternatingTuple, Set.range_eq_empty]

/-- The independently specified ambient Grassmannian scheme. -/
def ambientGrassmannian (t n : ℕ) : Scheme :=
  Proj (isotropicProjectiveGrading (t := t)
    (emptyAlternatingTuple (K := K) (n := n)))

theorem ambientPluckerIdeal_le (forms : Fin m → StrictPairs n → K) :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) ≤
      isotropicPluckerIdeal (t := t) forms := by
  rw [isotropicPluckerIdeal_empty]
  exact le_sup_left

/-- The canonical closed immersion into the ambient Grassmannian. -/
def isotropicAmbientImmersion (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ ambientGrassmannian (K := K) t n :=
  HomogeneousQuotientProjective.quotientProjMap _ _
    (isotropicPluckerIdeal_isHomogeneous (emptyAlternatingTuple (K := K) (n := n)))
    (isotropicPluckerIdeal_isHomogeneous forms) (ambientPluckerIdeal_le forms)

instance isotropicAmbientImmersion_isClosedImmersion
    (forms : Fin m → StrictPairs n → K) :
    IsClosedImmersion (isotropicAmbientImmersion (t := t) forms) :=
  HomogeneousQuotientProjective.quotientProjMap_isClosedImmersion _ _ _ _ _

@[simp]
theorem isotropicAmbientImmersion_preimage_chart
    (forms : Fin m → StrictPairs n → K) (p : PluckerIndex (t + 2) n) :
    isotropicAmbientImmersion forms ⁻¹ᵁ
      Proj.basicOpen
        (isotropicProjectiveGrading (t := t) (emptyAlternatingTuple (K := K) (n := n)))
        (Ideal.Quotient.mk _ (X p)) =
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk _ (X p)) := rfl

end PaperVerification.AlternatingForms
