module

public import PaperVerification.ToricCharacterSubrepresentations
public import PaperVerification.ToricMonomialAffineCharts
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Actual invariant affine coordinate algebras are semigroup algebras

The exponent monoid is recovered from the characters actually contained
in a subalgebra of the Laurent algebra. Algebraic coaction stability
implies equality with its semigroup algebra. Finite type implies finite
generation of that monoid. A common actual fraction field implies that
its differences generate the whole character lattice. Normality, when
available, implies saturation by the monic equation `T^N-χ^(Nm)`.
None of these conclusions is included in the definition of the monoid.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

/-- The characters literally belonging to the given affine algebra. -/
def affineExponentMonoid (A : Subalgebra k (AddMonoidAlgebra k M)) : AddSubmonoid M where
  carrier := {m | single m (1 : k) ∈ A}
  zero_mem' := by
    change single (0 : M) (1 : k) ∈ A
    simpa only [AddMonoidAlgebra.one_def] using A.one_mem
  add_mem' := by
    intro m p hm hp
    change single (m+p) (1 : k) ∈ A
    simpa using A.mul_mem hm hp

@[simp] theorem mem_affineExponentMonoid
    (A : Subalgebra k (AddMonoidAlgebra k M)) (m : M) :
    m ∈ affineExponentMonoid k A ↔ single m (1 : k) ∈ A := Iff.rfl

theorem invariantAffineAlgebra_eq_semigroup
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    A = monoidChartAlgebra k (affineExponentMonoid k A) := by
  apply Subalgebra.toSubmodule_injective
  rw [monoidChartAlgebra_toSubmodule]
  exact stable_eq_characterModule k A.toSubmodule hA

/-- The constructed isomorphism retains the literal character embedding
into the ambient Laurent algebra. -/
def invariantAffineSemigroupEquiv
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    AddMonoidAlgebra k (affineExponentMonoid k A) ≃ₐ[k] A :=
  (monoidChartAlgebraEquiv k (affineExponentMonoid k A)).trans
    (Subalgebra.equivOfEq _ _ (invariantAffineAlgebra_eq_semigroup k A hA).symm)

@[simp] theorem invariantAffineSemigroupEquiv_single
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) (m : affineExponentMonoid k A) (r : k) :
    ((invariantAffineSemigroupEquiv k A hA (single m r) : A) : AddMonoidAlgebra k M) =
      single (m : M) r := by
  change monoidChartMap k (affineExponentMonoid k A) (single m r) = _
  exact monoidChartMap_single k _ m r

theorem affineExponentMonoid_finitelyGenerated
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    AddMonoid.FG (affineExponentMonoid k A) := by
  letI : Algebra.FiniteType k (AddMonoidAlgebra k (affineExponentMonoid k A)) :=
    Algebra.FiniteType.equiv inferInstance (invariantAffineSemigroupEquiv k A hA).symm
  exact AddMonoidAlgebra.fg_of_finiteType (R := k)

theorem exists_finite_affine_exponent_generators
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    ∃ S : Finset M, AddSubmonoid.closure (S : Set M) = affineExponentMonoid k A := by
  letI := affineExponentMonoid_finitelyGenerated k A hA
  exact AddSubmonoid.exists_of_isAddFG _

section Coaction

variable {R : Type*} [CommRing R] [Algebra k R]
    (f : R →ₐ[k] AddMonoidAlgebra k M)
    (δ : R →ₗ[k] AddMonoidAlgebra k M ⊗[k] R)

/-- An actual equivariant comorphism gives stability of its actual range.
The equality involves the Hopf comultiplication over all test algebras. -/
theorem range_isCharacterStable_of_coaction
    (hδ : ∀ r : R,
      Coalgebra.comul (R := k) (f r) =
        TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
          f.toLinearMap (δ r)) :
    IsCharacterStable k f.range.toSubmodule := by
  rintro z ⟨r, rfl⟩
  let fr : R →ₗ[k] f.range := f.rangeRestrict.toLinearMap
  refine ⟨TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
    fr (δ r), ?_⟩
  have hmaps :
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        f.range.toSubmodule.subtype).comp
          (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) fr) =
      TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) f.toLinearMap := by
    ext a b
    rfl
  exact (congrArg (fun g => g (δ r)) hmaps).trans (hδ r).symm

end Coaction

section FractionField

variable (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule)
    (K : Type*) [Field K] [Algebra (AddMonoidAlgebra k M) K]
    [Algebra A K]

/-- In this common-fraction-field interface, the scalar tower refers to
the chosen algebra map A→K, rather than the separate inherited action
of the ambient Laurent algebra on K. -/
local instance affineFractionAlgebraSMul : SMul A K :=
  (inferInstance : Algebra A K).toSMul

variable [IsScalarTower A (AddMonoidAlgebra k M) K]
    [IsFractionRing A K]
    (hinj : Function.Injective (algebraMap (AddMonoidAlgebra k M) K))

include hA hinj in
/-- Every lattice character is a quotient of characters from the actual
affine monoid. This follows from the common fraction field, not from a
generating-lattice premise attached to the affine chart. -/
theorem exists_affine_exponent_difference (m : M) :
    ∃ p ∈ affineExponentMonoid k A, ∃ q ∈ affineExponentMonoid k A, m = p-q := by
  letI : IsDomain A := Function.Injective.isDomain (algebraMap A K)
    (IsFractionRing.injective A K)
  obtain ⟨a,b,hb,hfrac⟩ := IsFractionRing.div_surjective A
    (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))
  have hb0 : (b : AddMonoidAlgebra k M) ≠ 0 := by
    intro h
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact Subtype.ext h
  have hK0 : algebraMap A K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul : single m (1:k) * (b : AddMonoidAlgebra k M) = a := by
    apply hinj
    have hbmap : algebraMap (AddMonoidAlgebra k M) K (b : AddMonoidAlgebra k M) =
        algebraMap A K b :=
      (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K b).symm
    have hamap : algebraMap A K a =
        algebraMap (AddMonoidAlgebra k M) K (a : AddMonoidAlgebra k M) :=
      IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K a
    exact (map_mul (algebraMap (AddMonoidAlgebra k M) K)
      (single m (1:k)) (b : AddMonoidAlgebra k M)).trans
        ((congrArg (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)) * ·)
          hbmap).trans (((div_eq_iff hK0).mp hfrac).symm.trans hamap))
  obtain ⟨q,hq⟩ := Finsupp.support_nonempty_iff.mpr (by
    intro hz
    apply hb0
    exact AddMonoidAlgebra.ext hz)
  have hq0 : (b : AddMonoidAlgebra k M).coeff q ≠ 0 := Finsupp.mem_support_iff.mp hq
  have hqA : q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA b b.property q hq0
  have hp0 : (a : AddMonoidAlgebra k M).coeff (m+q) ≠ 0 := by
    rw [← hmul, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
    exact hq0
  have hpA : m+q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA a a.property (m+q) hp0
  exact ⟨m+q,hpA,q,hqA,by abel⟩

include hA hinj in
theorem affineExponentMonoid_groupClosure :
    AddSubgroup.closure (affineExponentMonoid k A : Set M) = ⊤ := by
  apply eq_top_iff.mpr
  intro m hm
  obtain ⟨p,hp,q,hq,rfl⟩ := exists_affine_exponent_difference k A hA K hinj m
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hp)
    (AddSubgroup.subset_closure hq)

include hinj in
/-- Saturation is forced by integral closedness of the actual affine
coordinate ring in its actual fraction field. -/
theorem affineExponentMonoid_saturated [IsIntegrallyClosed A]
    (m : M) {N : ℕ} (hN : 0<N)
    (hm : N • m ∈ affineExponentMonoid k A) :
    m ∈ affineExponentMonoid k A := by
  let x := algebraMap (AddMonoidAlgebra k M) K (single m (1:k))
  let a : A := ⟨single (N • m) 1, hm⟩
  have hpow : x^N = algebraMap A K a := by
    change (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))^N = _
    rw [← map_pow, IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K]
    simp [a]
  have hx : IsIntegral A (x^N) := by
    rw [hpow]
    exact isIntegral_algebraMap
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hN hx
  have he : (y : AddMonoidAlgebra k M) = single m (1:k) := by
    apply hinj
    exact (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K y).symm.trans hy
  change single m (1:k) ∈ A
  exact he ▸ y.property

end FractionField

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.invariantAffineAlgebra_eq_semigroup
#print axioms PaperVerification.ToricCharacters.affineExponentMonoid_finitelyGenerated
#print axioms PaperVerification.ToricCharacters.affineExponentMonoid_groupClosure
