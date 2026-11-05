module
public import graph_foundation.part013
public import shared_results.part018_rees_homology_complete

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesStandardIdentification -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u v
variable {k : Type u} [Field k]

/-- Scalar restriction is performed abstractly before the row polynomial ring
is instantiated, so the ordinary Rees carrier remains transparent. -/
def coefficientwiseReesAlgebra {R : Type v} [CommRing R] [Algebra k R]
    (I : Ideal R) : Subalgebra k (Polynomial R) :=
  (reesAlgebra I).restrictScalars k

variable {d : ℕ} {n : Fin d → ℕ} (E : Finset (FiniteTuple n))

/-- Regard the conventional coefficientwise Rees algebra as a `k`-algebra. -/
abbrev standardReesAlgebra :
    Subalgebra k (Polynomial (MvPolynomial (FiniteVariable.{u} n) k)) :=
  coefficientwiseReesAlgebra (k := k) (finiteSublatticeIdeal n (k := k) E)

@[simp] lemma mem_standardReesAlgebra
    (f : Polynomial (MvPolynomial (FiniteVariable.{u} n) k)) :
    f ∈ standardReesAlgebra (k := k) E ↔
      ∀ i, f.coeff i ∈ finiteSublatticeIdeal n (k := k) E ^ i := Iff.rfl

lemma reesFineExponent_eq_some (a : finiteReesExponentMonoid.{u} E) :
    a.val.some=finiteReesFineExponent a := by
  ext v
  simp [finiteReesFineExponent]

lemma optionEquiv_rees_basis_mem (a : finiteReesExponentMonoid.{u} E) :
    MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)
      (finiteReesImageBasis E k a).val ∈ standardReesAlgebra (k := k) E := by
  rw [finiteReesImageBasis_val,MvPolynomial.optionEquivLeft_monomial,
    reesFineExponent_eq_some]
  apply reesAlgebra.monomial_mem.mpr
  rw [←finitePowerFamily_ideal]
  exact (monomial_mem_iff _ _).mpr (finiteReesFineExponent_mem a)

lemma optionEquiv_reesImage_mem (f : finiteReesImage E k) :
    MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n) f.val ∈
      standardReesAlgebra (k := k) E := by
  let e := (MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)).toAlgHom.comp
    (finiteReesImage E k).val
  let Q := (standardReesAlgebra (k := k) E).toSubmodule.comap e.toLinearMap
  have h : ⊤ ≤ Q := by
    rw [←(finiteReesImageBasis E k).span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨a,rfl⟩
    exact optionEquiv_rees_basis_mem E a
  exact h (show f∈(⊤ : Submodule k (finiteReesImage E k)) from trivial)

lemma polynomial_monomial_mem_reesImage_map (m : ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (c : k)
    (ha : Contains (exponentPowerFamily (finiteRowFamily n E) m) a) :
    Polynomial.monomial m (MvPolynomial.monomial a c) ∈
      (finiteReesImage E k).map
        (MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)).toAlgHom := by
  let b : finiteReesExponentMonoid.{u} E :=
    ⟨finiteTargetExponent a m,(finiteTarget_mem_rees_iff a m).mpr ha⟩
  let f := finiteReesMonoidEquiv E k (AddMonoidAlgebra.single b c)
  refine ⟨f.val,f.property,?_⟩
  rw [finiteReesMonoidEquiv_single]
  change MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)
    (MvPolynomial.monomial (finiteTargetExponent a m) c) = _
  rw [MvPolynomial.optionEquivLeft_monomial, finiteTargetExponent_none]
  change Polynomial.monomial m (MvPolynomial.monomial (finiteTargetExponent a m).some c) = _
  have hs : (finiteTargetExponent a m).some = a := by
    ext v
    simp
  rw [hs]

/-- The presentation image equals the conventional coefficientwise Rees
algebra under the canonical renaming of the auxiliary variable. -/
theorem finiteReesImage_map_eq_standard :
    (finiteReesImage E k).map
      (MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)).toAlgHom =
        standardReesAlgebra (k := k) E := by
  apply le_antisymm
  · rintro f ⟨g,hg,rfl⟩
    exact optionEquiv_reesImage_mem E ⟨g,hg⟩
  · intro f hf
    let T := (finiteReesImage E k).map
      (MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)).toAlgHom
    change f∈T
    rw [f.as_sum_support]
    apply T.sum_mem
    intro m _
    have hm : f.coeff m∈monomialIdeal k (exponentPowerFamily (finiteRowFamily n E) m) := by
      rw [finitePowerFamily_ideal]
      exact hf m
    have hs := (mem_monomialIdeal_iff _ _).mp hm
    rw [(f.coeff m).as_sum,map_sum]
    apply T.sum_mem
    intro a ha
    exact polynomial_monomial_mem_reesImage_map E m a ((f.coeff m).coeff a) (hs a ha)

/-- A genuine algebra equivalence from the presentation image used in the
formal proof to Mathlib's usual Rees algebra, with no lattice hypothesis needed. -/
def finiteReesStandardEquiv : finiteReesImage E k ≃ₐ[k] standardReesAlgebra (k := k) E :=
  ((MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n)).subalgebraMap
    (finiteReesImage E k)).trans
      (Subalgebra.equivOfEq _ _ (finiteReesImage_map_eq_standard E))

@[simp] lemma finiteReesStandardEquiv_val (f : finiteReesImage E k) :
    (finiteReesStandardEquiv E f).val =
      MvPolynomial.optionEquivLeft k (FiniteVariable.{u} n) f.val := rfl

/-- Every basis vector retains its original auxiliary degree and coefficient
monomial under the identification with the standard Rees algebra. -/
lemma finiteReesStandardEquiv_basis (a : finiteReesExponentMonoid.{u} E) :
    (finiteReesStandardEquiv E (finiteReesImageBasis E k a)).val =
      Polynomial.monomial (a.val none)
        (MvPolynomial.monomial (finiteReesFineExponent a) 1) := by
  rw [finiteReesStandardEquiv_val,finiteReesImageBasis_val,
    MvPolynomial.optionEquivLeft_monomial,reesFineExponent_eq_some]

/-- The algebra equivalence also preserves the polynomial variables whose
Koszul differential defines relative homology. -/
lemma finiteReesStandardEquiv_baseVariable_val (v : FiniteVariable.{u} n) :
    (finiteReesStandardEquiv E (finiteReesBaseVariable (k := k) E v)).val =
      Polynomial.C (MvPolynomial.X v) := by
  rw [finiteReesStandardEquiv_val,finiteReesBaseVariable_val,
    MvPolynomial.optionEquivLeft_X_some]

end FourPapers.Sublattice

end
end
end


end
