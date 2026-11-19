module

public import PaperVerification.AlternatingFormsGenericKrullDimension

/-!
# The actual one-plane isotropy equations impose no additional ideal

The existing row-evaluation definition is indexed by ranks `t+2`. We extend
the same literal expression to arbitrary rank, prove agreement in that range,
and use every basis-row pair in rank one. These are actual restriction
polynomials, not a definition by an empty list of equations. Their vanishing
holds over every commutative coefficient algebra, including nonreduced algebras.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {n m s t : ℕ}

/-- The original alternating row evaluation, with its row rank left arbitrary. -/
def alternatingRowPairAtRank {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin s) (Fin n) R) (i j : Fin s) : R :=
  ∑ a : StrictPairs n, f a •
    (A i a.val.1 * A j a.val.2 - A i a.val.2 * A j a.val.1)

@[simp] theorem alternatingRowPairAtRank_eq {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t + 2)) (Fin n) R)
    (i j : Fin (t + 2)) :
    alternatingRowPairAtRank f A i j = alternatingRowPair f A i j := rfl

@[simp] theorem alternatingRowPairAtRank_self {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin s) (Fin n) R) (i : Fin s) :
    alternatingRowPairAtRank f A i i = 0 := by
  simp [alternatingRowPairAtRank, mul_comm]

/-- Vanishing holds on every pair of scalar multiples of a line generator.
This is the literal argument of the recovered `onePlane_row_isotropic` theorem. -/
theorem onePlane_restriction_multiples {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (u : Fin n → R) (a b : R) :
    (∑ ij : StrictPairs n, f ij •
      ((a * u ij.val.1) * (b * u ij.val.2) -
        (a * u ij.val.2) * (b * u ij.val.1))) = 0 := by
  apply Finset.sum_eq_zero
  intro ij _
  have h : (a * u ij.val.1) * (b * u ij.val.2) =
      (a * u ij.val.2) * (b * u ij.val.1) := by ring
  rw [h, sub_self, smul_zero]

/-- All restrictions to pairs of basis rows in the original normalized chart. -/
def isotropicChartIdealAtRank (p : PluckerIndex s n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span (Set.range fun a : Fin m × Fin s × Fin s ↦
    alternatingRowPairAtRank (forms a.1) (pluckerChartMatrix p) a.2.1 a.2.2)

/-- In the existing rank range this is exactly the original defining ideal. -/
theorem isotropicChartIdealAtRank_eq (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    isotropicChartIdealAtRank p forms = isotropicChartIdeal p forms := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, i, j⟩, rfl⟩
    exact alternatingRowPair_mem_chartIdeal p forms l i j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, ij⟩, rfl⟩
    exact Ideal.subset_span ⟨(l, ij.val.1, ij.val.2), rfl⟩

/-- The actual one-row restriction ideal is zero, over the full chart ring. -/
theorem onePlaneChartRestrictionIdeal_eq_bot (p : PluckerIndex 1 n)
    (forms : Fin m → StrictPairs n → K) : isotropicChartIdealAtRank p forms = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, i, j⟩, rfl⟩
  have hij : i = j := Subsingleton.elim _ _
  subst j
  change alternatingRowPairAtRank (forms l) (pluckerChartMatrix p) i i ∈
    (⊥ : Ideal (MvPolynomial (PluckerChartVariable p) K))
  rw [alternatingRowPairAtRank_self]
  exact Ideal.zero_mem _

/-- Quotienting by the actual line-restriction equations leaves the original
polynomial chart, through the canonical quotient-by-zero equivalence. -/
def onePlaneRestrictionChartEquiv (p : PluckerIndex 1 n)
    (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdealAtRank p forms) ≃ₐ[K]
      MvPolynomial (PluckerChartVariable p) K :=
  (Ideal.quotientEquivAlgOfEq K (onePlaneChartRestrictionIdeal_eq_bot p forms)).trans
    (AlgEquiv.quotientBot K _)

/-- The one-entry Plücker index of a coordinate of the universal row. -/
def oneRowPluckerIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, by
    intro a b hab
    exact ((ne_of_lt hab) (Subsingleton.elim _ _)).elim⟩

/-- These are the original universal matrix entries under the one-row minor map. -/
theorem oneRowPluckerIndex_genericMinor (i : Fin n) :
    genericPluckerMinor (K := K) (oneRowPluckerIndex i) = X (0, i) := by
  simp only [genericPluckerMinor, Matrix.det_fin_one, Matrix.of_apply, oneRowPluckerIndex]

/-- Restrict every form to every pair of rows of the universal one-row matrix.
The entries are the actual one-row Plücker coordinates. -/
def onePlaneHomogeneousRestrictionIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex 1 n) K) :=
  Ideal.span (Set.range fun a : Fin m × Fin 1 × Fin 1 ↦
    alternatingRowPairAtRank (forms a.1)
      (Matrix.of fun (_ : Fin 1) i ↦ X (oneRowPluckerIndex i)) a.2.1 a.2.2)

theorem onePlaneHomogeneousRestrictionIdeal_eq_bot
    (forms : Fin m → StrictPairs n → K) : onePlaneHomogeneousRestrictionIdeal forms = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, i, j⟩, rfl⟩
  have hij : i = j := Subsingleton.elim _ _
  subst j
  change alternatingRowPairAtRank (forms l)
    (Matrix.of fun (_ : Fin 1) i ↦ X (oneRowPluckerIndex i)) i i ∈
    (⊥ : Ideal (MvPolynomial (PluckerIndex 1 n) K))
  rw [alternatingRowPairAtRank_self]
  exact Ideal.zero_mem _

/-- The original Plücker ideal together with the literal line restrictions. -/
def onePlaneIsotropicPluckerIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex 1 n) K) :=
  matrixPluckerIdeal ⊔ onePlaneHomogeneousRestrictionIdeal forms

theorem onePlaneIsotropicPluckerIdeal_eq (forms : Fin m → StrictPairs n → K) :
    onePlaneIsotropicPluckerIdeal forms = matrixPluckerIdeal := by
  rw [onePlaneIsotropicPluckerIdeal, onePlaneHomogeneousRestrictionIdeal_eq_bot, sup_bot_eq]

theorem onePlaneIsotropicPluckerIdeal_isHomogeneous
    (forms : Fin m → StrictPairs n → K) :
    (onePlaneIsotropicPluckerIdeal forms).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlaneIsotropicPluckerIdeal_eq]
  exact matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)

/-- The genuine projective quotient, with its structure morphism over the field. -/
def onePlaneIsotropicOver (forms : Fin m → StrictPairs n → K) : Over (Spec (.of K)) :=
  Over.mk (HomogeneousQuotientCharts.structureMap (onePlaneIsotropicPluckerIdeal forms)
    (onePlaneIsotropicPluckerIdeal_isHomogeneous forms))

/-- Equality retains both the actual scheme and its original map to `Spec K`. -/
theorem onePlaneIsotropicOver_eq (forms : Fin m → StrictPairs n → K) :
    onePlaneIsotropicOver forms = Over.mk (onePlaneOriginalStructureMap (K := K) n) := by
  let F : { Q : Ideal (MvPolynomial (PluckerIndex 1 n) K) //
      Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (PluckerIndex 1 n) K) } → Over (Spec (.of K)) :=
    fun Q ↦ Over.mk (HomogeneousQuotientCharts.structureMap Q.val Q.property)
  change F ⟨onePlaneIsotropicPluckerIdeal forms,
      onePlaneIsotropicPluckerIdeal_isHomogeneous forms⟩ =
    F ⟨matrixPluckerIdeal, matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)⟩
  exact congrArg F (Subtype.ext (onePlaneIsotropicPluckerIdeal_eq forms))

/-- The accepted one-plane geometry now applies to the scheme defined by the
actual restriction equations, for every collection of alternating forms. -/
theorem onePlaneIsotropic_geometry (forms : Fin m → StrictPairs n → K) (hn : 0 < n) :
    Nonempty (onePlaneIsotropicOver forms).left ∧
      Smooth (onePlaneIsotropicOver forms).hom ∧
      topologicalKrullDim (onePlaneIsotropicOver forms).left =
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  rw [onePlaneIsotropicOver_eq]
  exact onePlaneOriginal_geometry n hn

theorem onePlaneIsotropic_zero_empty (forms : Fin m → StrictPairs 0 → K) :
    IsEmpty (onePlaneIsotropicOver forms).left := by
  rw [onePlaneIsotropicOver_eq]
  exact onePlaneOriginalProj_zero_empty

end PaperVerification.AlternatingForms
