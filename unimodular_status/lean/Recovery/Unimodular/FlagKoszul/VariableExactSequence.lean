module

public import Recovery.Unimodular.FlagKoszul.VariableQuotients
public import Mathlib.Algebra.Exact.Basic

/-!
# The exact variable-adjoining sequence of the ordinary flag algebra

For j outside S, multiplication by X_j identifies A/J_(S union N(j)) with
its actual image in A/J_S. The following quotient is A/J_(S union {j}).
The maps are A-linear, exact and surjective where claimed; their basis formulas
record the required degree shift without assuming any homological conclusion.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul

variable {E K : Type*} [Field K]

/-- Multiplication by the actual residue class of X_j, followed by quotient. -/
def variableMultiple (R : E → E → Prop) (S : Set E) (j : E) :
    FlagAlgebra R K →ₗ[FlagAlgebra R K] QuotientModule R S K :=
  (variableIdeal R S).mkQ.comp (LinearMap.mulRight (FlagAlgebra R K) (generator (K := K) R j))

@[simp] theorem variableMultiple_apply (R : E → E → Prop) (S : Set E) (j : E)
    (a : FlagAlgebra R K) :
    variableMultiple R S j a = Ideal.Quotient.mk (variableIdeal R S) (a * generator (K := K) R j) := rfl

theorem variableMultiple_kernel {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    LinearMap.ker (variableMultiple R S j (K := K)) = variableIdeal R (S ∪ neighbors R j) := by
  rw [← variableIdeal_colon hrefl hsymm hj]
  ext a
  rw [LinearMap.mem_ker, variableMultiple_apply, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

/-- The injection is induced by actual multiplication in A. -/
def variableInjection {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    QuotientModule R (S ∪ neighbors R j) K →ₗ[FlagAlgebra R K] QuotientModule R S K :=
  (variableIdeal R (S ∪ neighbors R j)).liftQ (variableMultiple R S j)
    (variableMultiple_kernel hrefl hsymm hj).ge

@[simp] theorem variableInjection_mk {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (a : FlagAlgebra R K) :
    variableInjection hrefl hsymm hj (Ideal.Quotient.mk (variableIdeal R (S ∪ neighbors R j)) a) =
      Ideal.Quotient.mk (variableIdeal R S) (a * generator (K := K) R j) := rfl

theorem variableInjection_injective {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    Function.Injective (variableInjection hrefl hsymm hj (K := K)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← variableMultiple_kernel hrefl hsymm hj, LinearMap.mem_ker]
  exact hq

@[simp] theorem variableInjection_qmonomial {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (u : Exp E) :
    variableInjection hrefl hsymm hj (qmonomial R (S ∪ neighbors R j) (K := K) u) =
      qmonomial R S (u + Finsupp.single j 1) := by
  rw [qmonomial, variableInjection_mk]
  change Ideal.Quotient.mk (variableIdeal R S)
    (Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial u 1) *
      Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.X j)) = _
  rw [← map_mul]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one, qmonomial]

def raisePoint {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (u : Point R (S ∪ neighbors R j)) : Point R S :=
  ⟨u.1 + Finsupp.single j 1, (allowed_add_single_iff hrefl hsymm hj u.1).mpr u.2⟩

theorem variableInjection_basis {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (u : Point R (S ∪ neighbors R j)) :
    variableInjection hrefl hsymm hj (quotientBasis R (S ∪ neighbors R j) (K := K) u) =
      quotientBasis R S (raisePoint hrefl hsymm hj u) := by
  rw [quotientBasis_apply, variableInjection_qmonomial, quotientBasis_apply]
  rfl

theorem raisePoint_degree {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (u : Point R (S ∪ neighbors R j)) :
    (raisePoint hrefl hsymm hj u).1.degree = u.1.degree + 1 := by
  simp [raisePoint]

theorem variableIdeal_insert (R : E → E → Prop) (S : Set E) (j : E) :
    variableIdeal R (insert j S) (K := K) = Ideal.span {generator (K := K) R j} ⊔ variableIdeal R S := by
  simp only [variableIdeal, Set.image_insert_eq, Ideal.span_insert]

@[simp] theorem quotientProjection_mk (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T)
    (a : FlagAlgebra R K) :
    quotientProjection R hST (Ideal.Quotient.mk (variableIdeal R S) a) =
      Ideal.Quotient.mk (variableIdeal R T) a := rfl

theorem quotientProjection_surjective (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T) :
    Function.Surjective (quotientProjection R hST (K := K)) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk (variableIdeal R S) a, rfl⟩

theorem variableInjection_projection_zero {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (q : QuotientModule R (S ∪ neighbors R j) K) :
    quotientProjection R (Set.subset_insert j S) (variableInjection hrefl hsymm hj q) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [variableInjection_mk, quotientProjection_mk]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨j, Set.mem_insert j S, rfl⟩

theorem variableProjection_kernel_preimage {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (q : QuotientModule R S K)
    (hq : quotientProjection R (Set.subset_insert j S) q = 0) :
    ∃ t : QuotientModule R (S ∪ neighbors R j) K, variableInjection hrefl hsymm hj t = q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [quotientProjection_mk, Ideal.Quotient.eq_zero_iff_mem, variableIdeal_insert,
    Ideal.mem_span_singleton_sup] at hq
  obtain ⟨b, c, hc, hbc⟩ := hq
  refine ⟨Ideal.Quotient.mk (variableIdeal R (S ∪ neighbors R j)) b, ?_⟩
  rw [variableInjection_mk, ← hbc, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hc, add_zero]

theorem variable_exact_sequence {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    Function.Exact (variableInjection hrefl hsymm hj (K := K))
      (quotientProjection R (Set.subset_insert j S)) := by
  intro q
  constructor
  · exact variableProjection_kernel_preimage hrefl hsymm hj q
  · rintro ⟨t, rfl⟩
    exact variableInjection_projection_zero hrefl hsymm hj t

#print axioms variableInjection_injective
#print axioms variableInjection_basis
#print axioms raisePoint_degree
#print axioms quotientProjection_surjective
#print axioms variable_exact_sequence

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.variable_exact_sequence
