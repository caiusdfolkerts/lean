module

public import Recovery.Unimodular.FlagKoszul.MonomialAlgebra

/-!
# The actual variable quotients of a commutative flag algebra

Every module below is the ordinary quotient A/J_S, with its genuine A-module
structure. The displayed bases are the classes of exactly the compatible
monomials avoiding S, as proved by the coefficient model of the polynomial
quotient. The colon identity is transported to these actual variable ideals.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul

variable {E K : Type*} [Field K]

def generator (R : E → E → Prop) (j : E) : FlagAlgebra R K :=
  Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.X j)

def variableIdeal (R : E → E → Prop) (S : Set E) : Ideal (FlagAlgebra R K) :=
  Ideal.span (generator (K := K) R '' S)

abbrev QuotientModule (R : E → E → Prop) (S : Set E) (K : Type*) [Field K] :=
  FlagAlgebra R K ⧸ variableIdeal R S

theorem variableIdeal_mono (R : E → E → Prop) {S T : Set E} (h : S ⊆ T) :
    variableIdeal R S (K := K) ≤ variableIdeal R T :=
  Ideal.span_mono (Set.image_mono h)

theorem variableIdeal_eq_map (R : E → E → Prop) (S : Set E) :
    variableIdeal R S (K := K) =
      (Ideal.span (MvPolynomial.X '' S)).map (Ideal.Quotient.mk (ideal R ∅)) := by
  rw [Ideal.map_span, Set.image_image]
  rfl

theorem map_ideal_eq_variableIdeal (R : E → E → Prop) (S : Set E) :
    (ideal R S (K := K)).map (Ideal.Quotient.mk (ideal R ∅)) = variableIdeal R S := by
  rw [ideal_eq_sup R S, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    variableIdeal_eq_map]

theorem mem_variableIdeal_mk_iff (R : E → E → Prop) (S : Set E)
    (f : MvPolynomial E K) :
    Ideal.Quotient.mk (ideal R ∅) f ∈ variableIdeal R S ↔ f ∈ ideal R S := by
  rw [← map_ideal_eq_variableIdeal]
  exact Ideal.mem_quotient_iff_mem (ideal_mono R (Set.empty_subset S))

/-- This is the colon identity inside the actual commutative quotient ring. -/
theorem variableIdeal_colon {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    (variableIdeal R S (K := K)).colon {generator (K := K) R j} =
      variableIdeal R (S ∪ neighbors R j) := by
  ext q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  change Ideal.Quotient.mk (ideal R ∅) f *
    Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.X j) ∈ _ ↔ _
  rw [← map_mul, mem_variableIdeal_mk_iff, mem_variableIdeal_mk_iff]
  exact mul_X_mem_ideal_iff hrefl hsymm hj f

def survivorEquiv (R : E → E → Prop) (S : Set E) :
    MonomialQuotient.Good (bad R S) ≃ Point R S where
  toFun u := ⟨u.1, Classical.not_not.mp u.2⟩
  invFun u := ⟨u.1, not_not.mpr u.2⟩
  left_inv u := rfl
  right_inv u := rfl

def polynomialQuotientBasis (R : E → E → Prop) (S : Set E) :
    Module.Basis (Point R S) K (MvPolynomial E K ⧸ ideal R S) :=
  (MonomialQuotient.basis (bad R S) (bad_upper R S)).reindex (survivorEquiv R S)

@[simp] theorem polynomialQuotientBasis_apply (R : E → E → Prop) (S : Set E)
    (u : Point R S) : polynomialQuotientBasis R S (K := K) u =
      Ideal.Quotient.mk (ideal R S) (MvPolynomial.monomial u.1 1) := by
  exact (Module.Basis.reindex_apply
    (MonomialQuotient.basis (bad R S) (bad_upper R S) (K := K))
    (survivorEquiv R S) u).trans
      (MonomialQuotient.basis_apply (bad R S) (bad_upper R S) ((survivorEquiv R S).symm u))

/-- A/J_S is identified with the polynomial quotient by the actual defining
quadratic ideal and the variables in S. -/
def quotientEquiv (R : E → E → Prop) (S : Set E) :
    QuotientModule R S K ≃ₐ[K] (MvPolynomial E K ⧸ ideal R S) :=
  (Ideal.quotientEquivAlgOfEq K (map_ideal_eq_variableIdeal R S (K := K)).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLEₐ K (ideal_mono R (Set.empty_subset S)))

@[simp] theorem quotientEquiv_mk (R : E → E → Prop) (S : Set E)
    (f : MvPolynomial E K) :
    quotientEquiv R S (Ideal.Quotient.mk (variableIdeal R S)
      (Ideal.Quotient.mk (ideal R ∅) f)) = Ideal.Quotient.mk (ideal R S) f := rfl

def quotientBasis (R : E → E → Prop) (S : Set E) :
    Module.Basis (Point R S) K (QuotientModule R S K) :=
  (polynomialQuotientBasis R S).map (quotientEquiv R S).symm.toLinearEquiv

def qmonomial (R : E → E → Prop) (S : Set E) (u : Exp E) : QuotientModule R S K :=
  Ideal.Quotient.mk (variableIdeal R S)
    (Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial u 1))

@[simp] theorem quotientBasis_apply (R : E → E → Prop) (S : Set E) (u : Point R S) :
    quotientBasis R S (K := K) u = qmonomial R S u.1 := by
  apply (quotientEquiv R S).injective
  simp only [quotientBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, qmonomial, quotientEquiv_mk, polynomialQuotientBasis_apply]

theorem qmonomial_eq_zero {R : E → E → Prop} {S : Set E} {u : Exp E}
    (hu : ¬ Allowed R S u) : qmonomial R S (K := K) u = 0 := by
  apply (quotientEquiv R S).injective
  rw [qmonomial, quotientEquiv_mk, map_zero]
  exact MonomialQuotient.monomial_eq_zero_of_bad (bad R S) (bad_upper R S) hu 1

@[simp] theorem variable_smul_qmonomial (R : E → E → Prop) (S : Set E) (j : E) (u : Exp E) :
    generator (K := K) R j • qmonomial R S (K := K) u = qmonomial R S (u + Finsupp.single j 1) := by
  change Ideal.Quotient.mk (variableIdeal R S) (generator (K := K) R j) *
    Ideal.Quotient.mk (variableIdeal R S)
      (Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial u 1)) = _
  rw [← map_mul]
  change Ideal.Quotient.mk (variableIdeal R S)
    (Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.X j) *
      Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial u 1)) = _
  rw [← map_mul]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, qmonomial, add_comm]

/-- The ordinary quotient projection, linear over the actual flag algebra. -/
def quotientProjection (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T) :
    QuotientModule R S K →ₗ[FlagAlgebra R K] QuotientModule R T K :=
  (Ideal.Quotient.factorₐ (FlagAlgebra R K) (variableIdeal_mono R hST)).toLinearMap

@[simp] theorem quotientProjection_qmonomial (R : E → E → Prop)
    {S T : Set E} (hST : S ⊆ T) (u : Exp E) :
    quotientProjection R hST (qmonomial R S (K := K) u) = qmonomial R T u := rfl

theorem quotientProjection_basis_of_allowed (R : E → E → Prop)
    {S T : Set E} (hST : S ⊆ T) (u : Point R S) (hu : Allowed R T u.1) :
    quotientProjection R hST (quotientBasis R S (K := K) u) =
      quotientBasis R T ⟨u.1, hu⟩ := by
  simp only [quotientBasis_apply, quotientProjection_qmonomial]

theorem quotientProjection_basis_of_not_allowed (R : E → E → Prop)
    {S T : Set E} (hST : S ⊆ T) (u : Point R S) (hu : ¬ Allowed R T u.1) :
    quotientProjection R hST (quotientBasis R S (K := K) u) = 0 := by
  rw [quotientBasis_apply, quotientProjection_qmonomial]
  exact qmonomial_eq_zero hu

#print axioms variableIdeal_colon
#print axioms quotientBasis_apply
#print axioms variable_smul_qmonomial
#print axioms quotientProjection_basis_of_allowed
#print axioms quotientProjection_basis_of_not_allowed

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.quotientBasis_apply
