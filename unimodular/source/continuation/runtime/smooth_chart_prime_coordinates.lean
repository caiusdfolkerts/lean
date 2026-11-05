module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Prime coordinates on smooth charts with torus factors

Under the actual polynomial-over-Laurent presentation of a coordinate
cone, each constrained basis character is exactly one polynomial
variable. It is consequently prime over every ground field. The free
basis directions remain in the Laurent coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PaperVerification.ToricCharacters

open scoped Classical

variable {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) (I : Finset ι)

theorem basis_mem_coordinateConeMonoid (i : ι) : b i ∈ coordinateConeMonoid b I := by
  intro j hj
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- A constrained basis vector has exactly its polynomial coordinate and
zero Laurent coordinates under the actual monoid equivalence. -/
theorem polynomialConeEquiv_basis (i : I) :
    polynomialConeEquiv b I ⟨b i.val, basis_mem_coordinateConeMonoid b I i.val⟩ =
      (Finsupp.single i 1, 0) := by
  apply Prod.ext
  · ext j
    change (b.repr (b i.val) j.val).toNat = (Finsupp.single i (1 : ℕ)) j
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun hval => h (Subtype.ext hval)
      simp [h, hval]
  · ext j
    change b.repr (b i.val) j.val = 0
    have hval : i.val ≠ j.val := by
      intro h
      exact j.property (h ▸ i.property)
    simp [hval]

variable (k : Type*) [Field k]

/-- The literal regular function given by a constrained basis character. -/
def coordinateChartGenerator (i : I) : monoidChartAlgebra k (coordinateConeMonoid b I) :=
  chartCharacter k (coordinateConeMonoid b I) (b i.val)
    (basis_mem_coordinateConeMonoid b I i.val)

/-- The polynomial/Laurent equivalence sends each actual coordinate
character to its corresponding polynomial variable. -/
theorem smoothChartAlgebraEquiv_generator (i : I) :
    smoothChartAlgebraEquiv k b I (coordinateChartGenerator b I k i) = MvPolynomial.X i := by
  let z : coordinateConeMonoid b I := ⟨b i.val, basis_mem_coordinateConeMonoid b I i.val⟩
  have hz : monoidChartAlgebraEquiv k (coordinateConeMonoid b I)
      (AddMonoidAlgebra.single z 1) = coordinateChartGenerator b I k i := by
    apply Subtype.ext
    exact monoidChartMap_single k (coordinateConeMonoid b I) z 1
  rw [← hz]
  change smoothSemigroupAlgebraEquiv k b I
    ((monoidChartAlgebraEquiv k (coordinateConeMonoid b I)).symm
      (monoidChartAlgebraEquiv k (coordinateConeMonoid b I) (AddMonoidAlgebra.single z 1))) = _
  rw [AlgEquiv.symm_apply_apply]
  change AddMonoidAlgebra.curryAlgEquiv k
    (AddMonoidAlgebra.domCongr k k (polynomialConeEquiv b I)
      (AddMonoidAlgebra.single z 1)) = _
  rw [AddMonoidAlgebra.domCongr_single,
    show polynomialConeEquiv b I z = (Finsupp.single i 1, 0) from polynomialConeEquiv_basis b I i,
    AddMonoidAlgebra.curryAlgEquiv_single, ← AddMonoidAlgebra.one_def]
  rfl

/-- Constrained basis characters are genuinely prime in the full chart
ring, including in charts with nonzero torus factor. -/
theorem coordinateChartGenerator_prime (i : I) :
    Prime (coordinateChartGenerator b I k i) := by
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  let e := smoothChartAlgebraEquiv k b I
  apply (MulEquiv.prime_iff e.toRingEquiv).mp
  change Prime (smoothChartAlgebraEquiv k b I (coordinateChartGenerator b I k i))
  rw [smoothChartAlgebraEquiv_generator]
  exact MvPolynomial.prime_X

/-- The full coordinate chart, with all Laurent directions, is a domain. -/
theorem coordinateChartAlgebra_isDomain :
    IsDomain (monoidChartAlgebra k (coordinateConeMonoid b I)) := by
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  exact MulEquiv.isDomain _ (smoothChartAlgebraEquiv k b I).toMulEquiv

/-- Unique factorization comes from the actual polynomial/Laurent
presentation and applies without a full-dimensionality assumption. -/
theorem coordinateChartAlgebra_uniqueFactorization :
    UniqueFactorizationMonoid (monoidChartAlgebra k (coordinateConeMonoid b I)) := by
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  letI := finiteCharacterRing_uniqueFactorization k (FreeCoordinate I)
  exact (smoothChartAlgebraEquiv k b I).symm.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.coordinateChartGenerator_prime
