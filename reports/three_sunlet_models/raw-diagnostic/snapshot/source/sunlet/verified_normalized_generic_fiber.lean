module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TotallySplit
public import sunlet.verified_normalized_model

@[expose] public section
set_option Elab.async false

#check "SUNLET_VERIFIEDNORMALIZEDGENERICFIBER_IMPORTS_READY"

section Stage_GenericFiberAlgebra


/-!
# Actual generic fibers of generically finite dominant affine maps

The generic fiber is the tensor product with the fraction field of the
coordinate algebra. Its identification with the source function field is
proved, and separable base change is an actual product-algebra isomorphism.
-/

noncomputable section
open scoped TensorProduct

namespace Sunlet.GenericFiberAlgebra

section Generic

variable (B A F E : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Field F] [Field E] [Algebra B A] [Algebra B F] [IsFractionRing B F]
  [Algebra A E] [IsFractionRing A E] [Algebra B E] [IsScalarTower B A E]
  [Algebra F E] [IsScalarTower B F E] [Algebra.IsAlgebraic F E]

local instance : Algebra A (F ⊗[B] A) := Algebra.TensorProduct.rightAlgebra

abbrev genericFiber := F ⊗[B] A

def evaluate : genericFiber B A F →ₐ[F] E :=
  AlgHom.liftEquiv B F A E (IsScalarTower.toAlgHom B A E)

@[simp] theorem evaluate_source (a : A) :
    evaluate B A F E (algebraMap A (genericFiber B A F) a) = algebraMap A E a := by
  change evaluate B A F E (1 ⊗ₜ[B] a) = _
  simp [evaluate]

theorem evaluate_injective : Function.Injective (evaluate B A F E) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors B))
    (evaluate B A F E).toRingHom).mpr
  intro a b
  constructor
  · exact congrArg (evaluate B A F E)
  · intro h
    have hab : a=b := (IsFractionRing.injective A E) (by
      simpa only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,evaluate_source] using h)
    exact congrArg (algebraMap A (genericFiber B A F)) hab

theorem evaluate_surjective : Function.Surjective (evaluate B A F E) := by
  intro x
  let C := (evaluate B A F E).range
  have hc (a : A) : algebraMap A E a ∈ C :=
    ⟨algebraMap A (genericFiber B A F) a,evaluate_source B A F E a⟩
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective A x
  have hi : (algebraMap A E b)⁻¹ ∈ C :=
    C.inv_mem_of_algebraic (x := ⟨algebraMap A E b,hc b⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
  change algebraMap A E a / algebraMap A E b ∈ C
  simpa only [div_eq_mul_inv] using C.mul_mem (hc a) hi

def genericFiberEquiv : genericFiber B A F ≃ₐ[F] E :=
  AlgEquiv.ofBijective (evaluate B A F E)
    ⟨evaluate_injective B A F E,evaluate_surjective B A F E⟩

end Generic

section Geometric

variable (F E K : Type*) [Field F] [Field E] [Field K]
  [Algebra F E] [Algebra F K] [Module.Finite F E]
  [Algebra.IsSeparable F E] [IsAlgClosed K]

/-- The geometric generic algebra is a product of exactly the separable
degree many copies of the algebraically closed ground field. -/
theorem exists_geometricSplit :
    Nonempty ((K ⊗[F] E) ≃ₐ[K] (Fin (Module.finrank F E) → K)) := by
  letI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  obtain ⟨n,⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K (K ⊗[F] E)
  have hn : n=Module.finrank F E := by
    have hh := e.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,Nat.nsmul_eq_mul,mul_one,Module.finrank_baseChange] using hh.symm
  subst n
  exact ⟨e⟩

end Geometric
end Sunlet.GenericFiberAlgebra
end
end Stage_GenericFiberAlgebra
#check "SUNLET_VERIFIEDNORMALIZEDGENERICFIBER_GenericFiberAlgebra_DONE"

section Stage_NormalizedGenericFiber



/-!
# The actual normalized geometric generic fiber

The source algebra used below is the image of the literal localized
parameter algebra under its proved injective generic evaluation. An
explicit algebra equivalence identifies these two presentations. The
base algebra consists of the actual normalized coordinate functions and
has already been identified with the original model coordinate ring.
Thus the tensor products below describe the generic fiber of the
parameterization itself, rather than an auxiliary finite extension.
-/

noncomputable section
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

namespace Sunlet.NormalizedLatinSystem

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- A faithful presentation of the literal localized normalized source. -/
abbrev NormalizedSourceAlgebra := (L.genericNormalizedEvaluation (k := k) o).range

/-- The coordinate subalgebra of the actual normalized map. -/
abbrev NormalizedCoordinateAlgebra := Algebra.adjoin k
  (Set.range (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o)))

/-- No parameters or equations are removed in passing to the evaluation range. -/
def normalizedLocalizedRingEquivSourceAlgebra :
    Normalization.LocalizedRing k L.identity o ≃ₐ[k] L.NormalizedSourceAlgebra (k := k) o :=
  AlgEquiv.ofInjective (L.genericNormalizedEvaluation o)
    (L.genericNormalizedEvaluation_injective o)

@[simp] theorem normalizedLocalizedRingEquivSourceAlgebra_coe
    (p : Normalization.LocalizedRing k L.identity o) :
    (L.normalizedLocalizedRingEquivSourceAlgebra (k := k) o p :
      L.NormalizedSourceField (k := k) o) = L.genericNormalizedEvaluation o p := rfl

/-- All independent normalized variables generate the entire source field. -/
theorem generic_normalized_variables_generate :
    IntermediateField.adjoin k (Set.range
      (Normalization.variableValues (L.genericNormalizedParameters (k := k) o))) = ⊤ := by
  rw [L.generic_normalized_variableValues o]
  have hr : Set.range (IteratedRationalField.combined ∘ L.normalizedVariableEquiv o) =
      Set.range (IteratedRationalField.combined (k := k)
        (I := ToricPairAlgebra.Index (ι := L.NonidentityColor) o) (J := Ω)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨L.normalizedVariableEquiv o j, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := (L.normalizedVariableEquiv o).surjective j
      exact ⟨i, rfl⟩
  rw [hr]
  exact IteratedRationalField.combined_generated

lemma normalized_polynomial_mem_sourceAlgebra
    (p : Normalization.PolynomialRing k L.identity o) :
    MvPolynomial.aeval
      (Normalization.variableValues (L.genericNormalizedParameters (k := k) o)) p ∈
      L.NormalizedSourceAlgebra (k := k) o := by
  exact ⟨algebraMap (Normalization.PolynomialRing k L.identity o)
    (Normalization.LocalizedRing k L.identity o) p,
    L.genericNormalizedEvaluation_algebraMap o p⟩

/-- The claimed source field is proved to be the fraction field of the
literal source algebra; this is not assumed as a genericity hypothesis. -/
instance normalizedSourceAlgebra_isFractionRing :
    IsFractionRing (L.NormalizedSourceAlgebra (k := k) o)
      (L.NormalizedSourceField (k := k) o) := by
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ IntermediateField.adjoin k (Set.range
      (Normalization.variableValues (L.genericNormalizedParameters (k := k) o))) := by
    rw [L.generic_normalized_variables_generate o]
    trivial
  obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_range_iff k
    (Normalization.variableValues (L.genericNormalizedParameters (k := k) o)) x).mp hx
  refine ⟨⟨_,L.normalized_polynomial_mem_sourceAlgebra o p⟩,
    ⟨_,L.normalized_polynomial_mem_sourceAlgebra o q⟩,?_⟩
  exact hpq

/-- Every output coordinate is an element of the literal source algebra. -/
theorem normalizedCoordinateAlgebra_le_sourceAlgebra :
    L.NormalizedCoordinateAlgebra (k := k) o ≤ L.NormalizedSourceAlgebra (k := k) o := by
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  refine ⟨Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o)
    L.perm (MvPolynomial.X i),?_⟩
  simpa only [MvPolynomial.aeval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    L.genericNormalizedEvaluation_comorphism o (MvPolynomial.X i)

instance normalizedCoordinateSource_algebra :
    Algebra (L.NormalizedCoordinateAlgebra (k := k) o)
      (L.NormalizedSourceAlgebra (k := k) o) :=
  (Subalgebra.inclusion (L.normalizedCoordinateAlgebra_le_sourceAlgebra o)).toAlgebra

instance normalizedCoordinateSource_scalarTower :
    IsScalarTower (L.NormalizedCoordinateAlgebra (k := k) o)
      (L.NormalizedSourceAlgebra (k := k) o) (L.NormalizedSourceField (k := k) o) :=
  Subalgebra.inclusion.isScalarTower_right
    (L.normalizedCoordinateAlgebra_le_sourceAlgebra o) _

/-- The inclusion used in the generic fiber is the actual normalized
coordinate substitution, as verified on every output coordinate. -/
theorem normalized_source_coordinate_compatibility (i : ι × Ω) :
    L.normalizedLocalizedRingEquivSourceAlgebra (k := k) o
      (Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o)
        L.perm (MvPolynomial.X i)) =
      algebraMap (L.NormalizedCoordinateAlgebra (k := k) o)
        (L.NormalizedSourceAlgebra (k := k) o)
        ⟨Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) i,
          Algebra.subset_adjoin ⟨i,rfl⟩⟩ := by
  apply Subtype.ext
  change L.genericNormalizedEvaluation o
    (Normalization.normalizedComorphism (K := k) (e := L.identity) (o := o)
      L.perm (MvPolynomial.X i)) =
    Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) i
  simpa only [MvPolynomial.aeval_X] using
    L.genericNormalizedEvaluation_comorphism o (MvPolynomial.X i)

/-- Tensoring the actual source coordinate algebra with the model's
function field defines the scheme-theoretic generic fiber algebra. -/
abbrev NormalizedGenericFiber :=
  (L.NormalizedImageField (k := k) o) ⊗[L.NormalizedCoordinateAlgebra (k := k) o]
    (L.NormalizedSourceAlgebra (k := k) o)

/-- The generic fiber algebra of the actual normalized map is precisely
its finite source function field. -/
def normalizedGenericFiberEquiv [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    L.NormalizedGenericFiber (k := k) o ≃ₐ[L.NormalizedImageField (k := k) o]
      L.NormalizedSourceField (k := k) o := by
  letI : Module.Finite (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) := L.normalizedSource_finite (k := k) o hm
  letI : Algebra.IsAlgebraic (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) :=
    Algebra.IsAlgebraic.of_finite (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o)
  exact GenericFiberAlgebra.genericFiberEquiv
    (L.NormalizedCoordinateAlgebra (k := k) o) (L.NormalizedSourceAlgebra (k := k) o)
    (L.NormalizedImageField (k := k) o) (L.NormalizedSourceField (k := k) o)

/-- Base change of the actual generic fiber to an algebraically closed
extension of the model function field. -/
abbrev NormalizedGeometricGenericFiber (K : Type*) [Field K]
    [Algebra (L.NormalizedImageField (k := k) o) K] :=
  K ⊗[L.NormalizedImageField (k := k) o] L.NormalizedGenericFiber (k := k) o

/-- The geometric generic fiber is a reduced disjoint union of exactly
2c² points: the statement is an isomorphism of its full coordinate algebra,
not merely a count of closed points or a separability assertion. -/
theorem normalizedGeometricGenericFiber_split [IsAlgClosed k]
    (hm : 5 ≤ Fintype.card Ω) (K : Type*) [Field K] [IsAlgClosed K]
    [Algebra (L.NormalizedImageField (k := k) o) K] :
    Nonempty (L.NormalizedGeometricGenericFiber (k := k) o K ≃ₐ[K]
      (Fin (2 * Nat.card (L.loopAt o).AbelianGroup ^ 2) → K)) := by
  letI : Module.Finite (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) := L.normalizedSource_finite (k := k) o hm
  letI : Algebra.IsSeparable (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) :=
    (isGalois_iff.mp (L.normalized_isGalois (k := k) o hm)).1
  obtain ⟨e⟩ := GenericFiberAlgebra.exists_geometricSplit
    (L.NormalizedImageField (k := k) o) (L.NormalizedSourceField (k := k) o) K
  have hdeg : Module.finrank (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) = 2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 :=
    L.normalized_generic_degree (k := k) o hm
  rw [hdeg] at e
  let e₀ : L.NormalizedGeometricGenericFiber (k := k) o K ≃ₐ[K]
      (K ⊗[L.NormalizedImageField (k := k) o] L.NormalizedSourceField (k := k) o) :=
    Algebra.TensorProduct.congr (R := L.NormalizedImageField (k := k) o) (S := K)
      (AlgEquiv.refl : K ≃ₐ[K] K) (L.normalizedGenericFiberEquiv (k := k) o hm)
  exact ⟨e₀.trans e⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_NormalizedGenericFiber
#check "SUNLET_VERIFIEDNORMALIZEDGENERICFIBER_NormalizedGenericFiber_DONE"

#check Sunlet.NormalizedLatinSystem.normalizedGenericFiberEquiv
#print axioms Sunlet.NormalizedLatinSystem.normalizedGenericFiberEquiv

#check Sunlet.NormalizedLatinSystem.normalizedGeometricGenericFiber_split
#print axioms Sunlet.NormalizedLatinSystem.normalizedGeometricGenericFiber_split
