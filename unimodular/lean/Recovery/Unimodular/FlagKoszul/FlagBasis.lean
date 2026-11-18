module

public import Recovery.Unimodular.FlagKoszul.VariableExactSequence
public import Recovery.Unimodular.KoszulSupport.PaperVerification.AugmentedAlgebraBasis
public import Mathlib.Data.Finsupp.Weight

/-!
# Genuine augmentation and homogeneous basis of the commutative flag algebra

The distinguished basis vector is the unit. The other vectors are the actual
nonconstant compatible monomials. The augmentation is induced by the polynomial
constant coefficient, and multiplication preserves the ordinary total degree.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul

attribute [local instance] Classical.propDecidable

variable {E K : Type*} [Field K]

theorem allowed_zero (R : E → E → Prop) (S : Set E) : Allowed R S 0 := by
  simp [Allowed, Valid]

def zeroPoint (R : E → E → Prop) (S : Set E) : Point R S := ⟨0, allowed_zero R S⟩

abbrev Positive (R : E → E → Prop) := {u : Exp E // Valid R u ∧ u ≠ 0}

def positivePoint (R : E → E → Prop) (u : Positive R) : Point R ∅ :=
  ⟨u.1, u.2.1, by simp⟩

def pointOptionEquiv (R : E → E → Prop) : Option (Positive R) ≃ Point R ∅ where
  toFun o := match o with
    | none => zeroPoint R ∅
    | some u => positivePoint R u
  invFun u := if h : u.1 = 0 then none else some ⟨u.1, u.2.1, h⟩
  left_inv o := by
    classical
    cases o with
    | none => simp [zeroPoint]
    | some u => simp [positivePoint, u.2.2]
  right_inv u := by
    classical
    dsimp
    split_ifs with h
    · exact Subtype.ext h.symm
    · rfl

def augmentedBasis (R : E → E → Prop) :
    Module.Basis (Option (Positive R)) K (FlagAlgebra R K) :=
  (polynomialQuotientBasis R ∅).reindex (pointOptionEquiv R).symm

@[simp] theorem augmentedBasis_none (R : E → E → Prop) :
    augmentedBasis R (K := K) none = 1 := by
  rw [augmentedBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    polynomialQuotientBasis_apply]
  simp [pointOptionEquiv, zeroPoint]

@[simp] theorem augmentedBasis_some (R : E → E → Prop) (u : Positive R) :
    augmentedBasis R (K := K) (some u) =
      Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial u.1 1) := by
  rw [augmentedBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    polynomialQuotientBasis_apply]
  rfl

def constantAugmentation : MvPolynomial E K →ₐ[K] K where
  __ := MvPolynomial.constantCoeff
  commutes' c := by simp [MvPolynomial.algebraMap_eq]

def augmentation (R : E → E → Prop) : FlagAlgebra R K →ₐ[K] K :=
  Ideal.Quotient.liftₐ (ideal R ∅) constantAugmentation (by
    intro f hf
    change f.coeff 0 = 0
    by_contra h
    exact ((mem_ideal_iff R ∅ f).mp hf 0 (MvPolynomial.mem_support_iff.mpr h))
      (allowed_zero R ∅))

@[simp] theorem augmentation_mk (R : E → E → Prop) (f : MvPolynomial E K) :
    augmentation R (Ideal.Quotient.mk (ideal R ∅) f) = f.constantCoeff := rfl

@[simp] theorem augmentation_basis_some (R : E → E → Prop) (u : Positive R) :
    augmentation R (augmentedBasis R (K := K) (some u)) = 0 := by
  classical
  rw [augmentedBasis_some, augmentation_mk, MvPolynomial.constantCoeff_monomial,
    if_neg u.2.2]

def positiveDegree (R : E → E → Prop) (u : Positive R) : ℕ := u.1.degree

theorem positiveDegree_pos (R : E → E → Prop) (u : Positive R) :
    0 < positiveDegree R u :=
  Nat.pos_of_ne_zero (fun h => u.2.2 ((Finsupp.degree_eq_zero_iff u.1).mp h))

theorem augmentedBasis_product (R : E → E → Prop) (u v : Positive R) :
    augmentedBasis R (K := K) (some u) * augmentedBasis R (some v) =
      Ideal.Quotient.mk (ideal R ∅) (MvPolynomial.monomial (u.1 + v.1) 1) := by
  rw [augmentedBasis_some, augmentedBasis_some, ← map_mul,
    MvPolynomial.monomial_mul_monomial, one_mul]

theorem positive_add_ne_zero {R : E → E → Prop} (u v : Positive R) : u.1 + v.1 ≠ 0 := by
  intro h
  exact u.2.2 (add_eq_zero.mp h).1

/-- The product coefficients in the actual augmented basis are homogeneous
for the ordinary total degree. -/
theorem product_degree (R : E → E → Prop) (u v w : Positive R)
    (hc : PaperVerification.AugmentedAlgebraBasis.productCoefficients
      (augmentedBasis R (K := K)) u v w ≠ 0) :
    positiveDegree R w = positiveDegree R u + positiveDegree R v := by
  classical
  by_cases hvalid : Valid R (u.1 + v.1)
  · let z : Positive R := ⟨u.1 + v.1, hvalid, positive_add_ne_zero u v⟩
    have hp : augmentedBasis R (K := K) (some u) * augmentedBasis R (some v) =
        augmentedBasis R (some z) := by
      rw [augmentedBasis_product, augmentedBasis_some]
    have hcoef : PaperVerification.AugmentedAlgebraBasis.productCoefficients
        (augmentedBasis R (K := K)) u v w = Finsupp.single (some z) (1 : K) (some w) := by
      change (augmentedBasis R).repr
        (augmentedBasis R (some u) * augmentedBasis R (some v)) (some w) = _
      rw [hp, Module.Basis.repr_self]
    rw [hcoef] at hc
    have hzw : z = w := by
      by_contra hne
      simp [Finsupp.single_apply, hne] at hc
    rw [← hzw]
    simp [positiveDegree, z]
  · have hp : augmentedBasis R (K := K) (some u) * augmentedBasis R (some v) = 0 := by
      rw [augmentedBasis_product]
      exact MonomialQuotient.monomial_eq_zero_of_bad (bad R ∅) (bad_upper R ∅)
        (fun h => hvalid h.1) 1
    change (augmentedBasis R).repr
      (augmentedBasis R (some u) * augmentedBasis R (some v)) (some w) ≠ 0 at hc
    rw [hp, map_zero, Finsupp.zero_apply] at hc
    exact (hc rfl).elim

@[simp] theorem variableIdeal_empty (R : E → E → Prop) :
    variableIdeal R ∅ (K := K) = ⊥ := by
  simp [variableIdeal]

/-- The empty-variable quotient is the free coefficient module A itself. -/
def quotientEmptyEquiv (R : E → E → Prop) :
    QuotientModule R ∅ K ≃ₐ[FlagAlgebra R K] FlagAlgebra R K :=
  (Ideal.quotientEquivAlgOfEq (FlagAlgebra R K) (variableIdeal_empty R)).trans
    (AlgEquiv.quotientBot (FlagAlgebra R K) (FlagAlgebra R K))

@[simp] theorem quotientEmptyEquiv_mk (R : E → E → Prop) (a : FlagAlgebra R K) :
    quotientEmptyEquiv R (Ideal.Quotient.mk (variableIdeal R ∅) a) = a := rfl

theorem allowed_univ_iff (R : E → E → Prop) (u : Exp E) : Allowed R Set.univ u ↔ u = 0 := by
  constructor
  · intro h
    ext i
    exact h.2 i (Set.mem_univ i)
  · rintro rfl
    exact allowed_zero R Set.univ

theorem augmentation_eq_zero_iff (R : E → E → Prop) (a : FlagAlgebra R K) :
    augmentation R a = 0 ↔ a ∈ variableIdeal R Set.univ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [augmentation_mk, mem_variableIdeal_mk_iff, mem_ideal_iff]
  change f.coeff 0 = 0 ↔ _
  constructor
  · intro h u hu hgood
    have hz := (allowed_univ_iff R u).mp hgood
    subst u
    exact (MvPolynomial.mem_support_iff.mp hu) h
  · intro h
    by_contra hf
    exact h 0 (MvPolynomial.mem_support_iff.mpr hf) (allowed_zero R Set.univ)


theorem augmentation_kernel (R : E → E → Prop) :
    RingHom.ker (augmentation R (K := K)) = variableIdeal R Set.univ := by
  ext a
  exact augmentation_eq_zero_iff R a

theorem augmentation_surjective (R : E → E → Prop) :
    Function.Surjective (augmentation R (K := K)) := by
  intro c
  exact ⟨algebraMap K (FlagAlgebra R K) c, (augmentation R).commutes c⟩

/-- The quotient by all variables is the actual residue field, via the
independently defined augmentation. -/
def quotientAllEquiv (R : E → E → Prop) : QuotientModule R Set.univ K ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (augmentation_kernel R).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective R))

@[simp] theorem quotientAllEquiv_mk (R : E → E → Prop) (a : FlagAlgebra R K) :
    quotientAllEquiv R (Ideal.Quotient.mk (variableIdeal R Set.univ) a) =
      augmentation R a := rfl

theorem quotientAllEquiv_qmonomial (R : E → E → Prop) (u : Exp E) :
    quotientAllEquiv R (qmonomial R Set.univ (K := K) u) = if u = 0 then 1 else 0 := by
  classical
  rw [qmonomial, quotientAllEquiv_mk, augmentation_mk, MvPolynomial.constantCoeff_monomial]

theorem quotientAllEquiv_eq_zero_coordinate (R : E → E → Prop)
    (q : QuotientModule R Set.univ K) :
    quotientAllEquiv R q = (quotientBasis R Set.univ).repr q (zeroPoint R Set.univ) := by
  have he : (quotientAllEquiv R (K := K)).toLinearMap =
      (quotientBasis R Set.univ).coord (zeroPoint R Set.univ) := by
    apply (quotientBasis R Set.univ).ext
    intro u
    have hu : u = zeroPoint R Set.univ := Subtype.ext ((allowed_univ_iff R u.1).mp u.2)
    subst u
    change quotientAllEquiv R (quotientBasis R Set.univ (zeroPoint R Set.univ)) =
      (quotientBasis R Set.univ).repr
        (quotientBasis R Set.univ (zeroPoint R Set.univ)) (zeroPoint R Set.univ)
    rw [Module.Basis.repr_self, Finsupp.single_eq_same, quotientBasis_apply,
      quotientAllEquiv_qmonomial]
    simp [zeroPoint]
  exact LinearMap.congr_fun he q

#print axioms augmentedBasis_none
#print axioms augmentation_basis_some
#print axioms positiveDegree_pos
#print axioms product_degree
#print axioms quotientEmptyEquiv
#print axioms augmentation_eq_zero_iff
#print axioms quotientAllEquiv
#print axioms quotientAllEquiv_eq_zero_coordinate

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.product_degree
