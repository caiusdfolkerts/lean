module

public import Recovery.Unimodular.GraphicSectionRing.FilteredSectionAlgebra

/-!
# Normal exponent coordinates for the actual section monomial basis

This is a proved equivalence with all compatible commutative monomials.
The homogeneous degree is the original total exponent degree, not the
auxiliary height used for the filtration.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing

variable {n : ℕ} {σ : Type*}

@[simp] theorem toricDegree_fst (p : σ → Lattice n) (u : σ →₀ ℕ) :
    (toricDegree p u).1 = u.degree := by
  simp [toricDegree, monomialPoints, Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum]

abbrev StandardMonomial (C : Set (Constraint n)) :=
  {u : Point C →₀ ℕ // StandardExponent Subtype.val u}

/-- All and only compatible exponent vectors are the actual lattice monomial basis. -/
def normalMonomialEquiv (C : Set (Constraint n)) :
    sectionSemigroup C ≃ StandardMonomial C where
  toFun z := ⟨normalExponent C z, normalExponent_standard C z⟩
  invFun u := sectionDegree C u.val
  left_inv z := sectionDegree_normalExponent C z
  right_inv u := Subtype.ext (normalExponent_eq_of_standard u.2)

@[simp] theorem normalExponent_degree (C : Set (Constraint n)) (z : sectionSemigroup C) :
    (normalExponent C z).degree = internalDegree C z := by
  have h := congrArg Prod.fst (toricDegree_normalExponent C z)
  simpa only [toricDegree_fst, internalDegree, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using h

@[simp] theorem internalDegree_sectionDegree (C : Set (Constraint n)) (u : Point C →₀ ℕ) :
    internalDegree C (sectionDegree C u) = u.degree :=
  toricDegree_fst _ _

abbrev PositiveStandardMonomial (C : Set (Constraint n)) :=
  {u : Point C →₀ ℕ // StandardExponent Subtype.val u ∧ 0 < u.degree}

def positiveNormalMonomialEquiv (C : Set (Constraint n)) :
    PositiveSection C ≃ PositiveStandardMonomial C where
  toFun z := ⟨normalExponent C z.val, normalExponent_standard C z.val,
    by rw [normalExponent_degree]; exact positive_internalDegree z⟩
  invFun u := ⟨sectionDegree C u.val, by
    intro h
    have hz := congrArg (internalDegree C) h
    rw [internalDegree_sectionDegree, map_zero] at hz
    omega⟩
  left_inv z := Subtype.ext (sectionDegree_normalExponent C z.val)
  right_inv u := Subtype.ext (normalExponent_eq_of_standard u.2.1)

@[simp] theorem positiveNormalMonomialEquiv_val (C : Set (Constraint n))
    (z : PositiveSection C) :
    (positiveNormalMonomialEquiv C z).val = normalExponent C z.val := rfl

@[simp] theorem positiveNormalMonomialEquiv_symm_val (C : Set (Constraint n))
    (u : PositiveStandardMonomial C) :
    ((positiveNormalMonomialEquiv C).symm u).val = sectionDegree C u.val := rfl

/-- When the monomial-model product survives, the two actual basis indices
are identified by ordinary addition of exponents. -/
theorem positiveNormalMonomialEquiv_add (C : Set (Constraint n))
    (s t : PositiveSection C)
    (h : StandardExponent Subtype.val (normalExponent C s.val + normalExponent C t.val)) :
    (positiveNormalMonomialEquiv C (positiveAdd s t)).val =
      (positiveNormalMonomialEquiv C s).val + (positiveNormalMonomialEquiv C t).val :=
  (normalExponent_add_iff C s.val t.val).mpr h

/-- A nonstandard product is precisely a strict drop from its combined height. -/
theorem nonstandard_iff_sectionHeight_drop (C : Set (Constraint n))
    (s t : sectionSemigroup C) :
    ¬ StandardExponent Subtype.val (normalExponent C s + normalExponent C t) ↔
      sectionHeight C (s + t) < sectionHeight C s + sectionHeight C t := by
  constructor
  · exact sectionHeight_add_lt
  · intro h hs
    rw [sectionHeight_add_eq hs] at h
    exact (lt_irrefl _) h

#print axioms normalMonomialEquiv
#print axioms positiveNormalMonomialEquiv
#print axioms positiveNormalMonomialEquiv_add
#print axioms nonstandard_iff_sectionHeight_drop

end Unimodular.GraphicSectionRing
