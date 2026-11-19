module

public import paper_verification.literal011
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.FinCases
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Linarith
public import paper_verification.literal001
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import paper_verification.literal008
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import paper_verification.literal005
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Expand

set_option Elab.async false

section TAF_LiteralSource_0560
/- Original module: PaperVerification.AlternatingFormsKoszulHilbert -/


/-!
# The full Hilbert formulas for the two-form Koszul homology

This file proves the three Laurent-polynomial identities in Proposition 5.4
for the actual shifted Koszul homology.  Calling these the polynomial-module
Betti polynomials additionally uses the free-resolution tensor comparison;
that comparison is kept separate from this dimension calculation.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

section HilbertOperations

variable {K A B : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

def submoduleProductEquiv (P : Submodule K A) (Q : Submodule K B) :
    P.prod Q ≃ₗ[K] P × Q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1, x.2), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteHilbertLaurent_prod (G : TauCeti.InternalGrading K A)
    (H : TauCeti.InternalGrading K B) :
    finiteHilbertLaurent (G.prod H) = finiteHilbertLaurent G + finiteHilbertLaurent H := by
  ext q
  change (Module.finrank K ((G.prod H).piece q) : ℤ) =
    (Module.finrank K (G.piece q) : ℤ) + (Module.finrank K (H.piece q) : ℤ)
  rw [TauCeti.InternalGrading.prod_piece,
    (submoduleProductEquiv (G.piece q) (H.piece q)).finrank_eq,
    Module.finrank_prod, Nat.cast_add]

theorem finiteHilbertLaurent_shift (G : TauCeti.InternalGrading K A) (c : ℤ) :
    finiteHilbertLaurent (G.shift c) = LaurentPolynomial.T (-c) * finiteHilbertLaurent G := by
  ext q
  simp only [finiteHilbertLaurent_coeff,
    LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_neg]
  rw [TauCeti.InternalGrading.shift_piece, add_comm q c]

theorem toLaurent_coefficient_nat (p : Polynomial ℤ) (q : ℕ) :
    p.toLaurent.coeff (q : ℤ) = p.coeff q := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective (f := Nat.castEmbedding)
    Nat.castEmbedding.injective p.toFinsupp.coeff q

theorem toLaurent_coefficient_negative (p : Polynomial ℤ) {q : ℤ} (hq : q < 0) :
    p.toLaurent.coeff q = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  have : (0 : ℤ) ≤ (m : ℤ) := Nat.cast_nonneg m
  change (m : ℤ) = q at hm
  omega

end HilbertOperations

section ExteriorFormulas

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

theorem exteriorIntegerGrading_hilbert :
    finiteHilbertLaurent (exteriorIntegerGrading (K := K) (M := M)) =
      (1 + LaurentPolynomial.T 1) ^ Module.finrank K M := by
  have hp : (((1 + Polynomial.X) ^ Module.finrank K M : Polynomial ℤ).toLaurent) =
      (1 + LaurentPolynomial.T 1) ^ Module.finrank K M := by simp
  rw [← hp]
  ext q
  rw [finiteHilbertLaurent_coeff, exteriorIntegerGrading_finrank]
  by_cases hq : 0 ≤ q
  · have hq' : q = (q.toNat : ℤ) := by omega
    rw [if_pos hq, hq', toLaurent_coefficient_nat, Polynomial.coeff_one_add_X_pow]
    simp only [Int.toNat_natCast]
  · rw [if_neg hq, Nat.cast_zero,
      toLaurent_coefficient_negative _ (by omega : q < 0)]

theorem exteriorKoszulFirst_range (f g : ⋀[K]^2 M) :
    LinearMap.range (exteriorKoszulFirst f g) =
      (exteriorRelationIdeal f g).restrictScalars K := by
  ext a
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    apply Ideal.mem_span_pair.mpr
    refine ⟨x, y, ?_⟩
    change x * (f : ExteriorAlgebra K M) + y * (g : ExteriorAlgebra K M) =
      (f : ExteriorAlgebra K M) * x + (g : ExteriorAlgebra K M) * y
    rw [(twoForm_commute f x).eq, (twoForm_commute g y).eq]
  · intro ha
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp ha
    refine ⟨(x, y), ?_⟩
    change (f : ExteriorAlgebra K M) * x + (g : ExteriorAlgebra K M) * y = a
    rw [(twoForm_commute f x).eq, (twoForm_commute g y).eq]
    exact hxy

theorem exteriorKoszulH₀_piece (f g : ⋀[K]^2 M) (q : ℤ) :
    (exteriorKoszulH₀Grading f g).piece q =
      (exteriorIntegerGrading.piece q).map (LinearMap.range (exteriorKoszulFirst f g)).mkQ := by
  simp only [exteriorKoszulH₀Grading,shortComplexH₀Grading,
    TauCeti.InternalGrading.quotient_piece,LinearMap.restrictScalars_self,
    exteriorKoszulTerm₀Grading]

/-- Each zeroth Koszul homogeneous component is the component of the actual
exterior quotient by the generated ideal. -/
def exteriorKoszulH₀DegreeEquiv (f g : ⋀[K]^2 M) (q : ℕ) :
    ExteriorQuotientDegree f g q ≃ₗ[K] (exteriorKoszulH₀Grading f g).piece (q : ℤ) := by
  let π := (LinearMap.range (exteriorKoszulFirst f g)).mkQ.comp
    (Submodule.subtype (⋀[K]^q M))
  have hker : LinearMap.ker π = exteriorDegreeRelations f g q := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, exteriorKoszulFirst_range]
    rfl
  have hrange : LinearMap.range π = (exteriorKoszulH₀Grading f g).piece (q : ℤ) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, exteriorKoszulH₀_piece,
      exteriorIntegerGrading_piece_nat]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (π.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

theorem exteriorKoszulH₀_finrank_nat (f g : ⋀[K]^2 M) (q : ℕ) :
    Module.finrank K ((exteriorKoszulH₀Grading f g).piece (q : ℤ)) =
      Module.finrank K (ExteriorQuotientDegree f g q) :=
  (exteriorKoszulH₀DegreeEquiv f g q).finrank_eq.symm

theorem exteriorKoszulH₀_piece_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (exteriorKoszulH₀Grading f g).piece q = ⊥ := by
  rw [exteriorKoszulH₀_piece, exteriorIntegerGrading_piece_negative hq, Submodule.map_bot]

theorem exteriorKoszulH₀_piece_above (f g : ⋀[K]^2 M) {q : ℤ}
    (hq : (Module.finrank K M : ℤ) < q) :
    (exteriorKoszulH₀Grading f g).piece q = ⊥ := by
  rw [exteriorKoszulH₀_piece, exteriorIntegerGrading_piece_above hq, Submodule.map_bot]

abbrev ExteriorKoszulTopKernel (f g : ⋀[K]^2 M) :=
  LinearMap.ker (shortComplexToCycles (exteriorKoszulSecond f g)
    (exteriorKoszulFirst f g) (exteriorKoszul_comp f g))

theorem mem_exteriorKoszulTopKernel (f g : ⋀[K]^2 M) (a : ExteriorAlgebra K M) :
    a ∈ ExteriorKoszulTopKernel f g ↔
      (f : ExteriorAlgebra K M) * a = 0 ∧ (g : ExteriorAlgebra K M) * a = 0 := by
  change shortComplexToCycles (exteriorKoszulSecond f g) (exteriorKoszulFirst f g)
      (exteriorKoszul_comp f g) a = 0 ↔ _
  constructor
  · intro ha
    have hpair := congrArg Subtype.val ha
    have hf := congrArg Prod.snd hpair
    have hg := congrArg Prod.fst hpair
    exact ⟨hf, neg_eq_zero.mp hg⟩
  · rintro ⟨hf, hg⟩
    apply Subtype.ext
    apply Prod.ext
    · change -((g : ExteriorAlgebra K M) * a) = 0
      rw [hg, neg_zero]
    · exact hf

theorem mem_exteriorKoszulH₂_piece (f g : ⋀[K]^2 M) (q : ℤ)
    (a : ExteriorKoszulTopKernel f g) :
    a ∈ (exteriorKoszulH₂Grading f g).piece q ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece (q + -4) := by
  rw [exteriorKoszulH₂Grading,shortComplexH₂Grading,
    TauCeti.InternalGrading.mem_ker_piece,exteriorKoszulTerm₂Grading,
    TauCeti.InternalGrading.shift_piece]

/-- The top Koszul homology in internal degree `p+4` is the common
annihilator in exterior degree `p`, with the shift proved explicitly. -/
def exteriorKoszulH₂DegreeEquiv (f g : ⋀[K]^2 M) (p : ℕ) :
    (exteriorKoszulH₂Grading f g).piece ((p + 4 : ℕ) : ℤ) ≃ₗ[K]
      exteriorCommonAnnihilator f g p where
  toFun a :=
    ⟨⟨a.1.1, by
      have ha := (mem_exteriorKoszulH₂_piece f g _ a.1).mp a.2
      have hp : ((p + 4 : ℕ) : ℤ) + -4 = (p : ℤ) := by omega
      rw [hp, exteriorIntegerGrading_piece_nat] at ha
      exact ha⟩,
      (mem_exteriorCommonAnnihilator f g _).mpr
        ((mem_exteriorKoszulTopKernel f g a.1.1).mp a.1.2)⟩
  invFun a :=
    ⟨⟨a.1.1, (mem_exteriorKoszulTopKernel f g _).mpr
      ((mem_exteriorCommonAnnihilator f g a.1).mp a.2)⟩, by
      apply (mem_exteriorKoszulH₂_piece f g _ _).mpr
      have hp : ((p + 4 : ℕ) : ℤ) + -4 = (p : ℤ) := by omega
      rw [hp, exteriorIntegerGrading_piece_nat]
      exact a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exteriorKoszulH₂_piece_below (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 4) :
    (exteriorKoszulH₂Grading f g).piece q = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  apply Subtype.ext
  have ha' := (mem_exteriorKoszulH₂_piece f g q a).mp ha
  rw [exteriorIntegerGrading_piece_negative (by omega : q + -4 < 0)] at ha'
  exact ha'

theorem exteriorKoszulH₂_piece_above (f g : ⋀[K]^2 M) {q : ℤ}
    (hq : (Module.finrank K M : ℤ) + 4 < q) :
    (exteriorKoszulH₂Grading f g).piece q = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  apply Subtype.ext
  have ha' := (mem_exteriorKoszulH₂_piece f g q a).mp ha
  rw [exteriorIntegerGrading_piece_above (by omega :
    (Module.finrank K M : ℤ) < q + -4)] at ha'
  exact ha'

/-- Complementary-degree duality, including every boundary and every
negative integer degree, for the actual top Koszul homology. -/
theorem exteriorKoszulH₂_duality (f g : ⋀[K]^2 M) (q : ℤ) :
    Module.finrank K ((exteriorKoszulH₂Grading f g).piece q) =
      Module.finrank K ((exteriorKoszulH₀Grading f g).piece
        ((Module.finrank K M : ℤ) + 4 - q)) := by
  by_cases hlow : q < 4
  · rw [exteriorKoszulH₂_piece_below f g hlow,
      exteriorKoszulH₀_piece_above f g (by omega), finrank_bot, finrank_bot]
  · by_cases hhigh : (Module.finrank K M : ℤ) + 4 < q
    · rw [exteriorKoszulH₂_piece_above f g hhigh,
        exteriorKoszulH₀_piece_negative f g (by omega), finrank_bot, finrank_bot]
    · let p := (q - 4).toNat
      let s := Module.finrank K M - p
      have hpq : ((p + 4 : ℕ) : ℤ) = q := by dsimp [p]; omega
      have hs : (s : ℤ) = (Module.finrank K M : ℤ) + 4 - q := by dsimp [s, p]; omega
      have hps : p + s = Module.finrank K M := by dsimp [s, p]; omega
      rw [← hpq, (exteriorKoszulH₂DegreeEquiv f g p).finrank_eq, hpq,
        ← hs, exteriorKoszulH₀_finrank_nat]
      exact exterior_annihilator_quotient_duality hps f g

/-- The polynomial called `H(t)` in the paper, justified componentwise as
the Hilbert series of the actual ideal quotient by `f,g`. -/
def exteriorQuotientHilbert (f g : ⋀[K]^2 M) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (exteriorKoszulH₀Grading f g)

theorem exteriorQuotientHilbert_coeff (f g : ⋀[K]^2 M) (q : ℕ) :
    (exteriorQuotientHilbert f g).coeff (q : ℤ) =
      (Module.finrank K (ExteriorQuotientDegree f g q) : ℤ) := by
  rw [exteriorQuotientHilbert, finiteHilbertLaurent_coeff, exteriorKoszulH₀_finrank_nat]

theorem exteriorKoszulH₂_hilbert (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent (exteriorKoszulH₂Grading f g) =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) := by
  ext q
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    LaurentPolynomial.invert_apply, exteriorQuotientHilbert, finiteHilbertLaurent_coeff]
  rw [exteriorKoszulH₂_duality]
  have hindex : -(-((Module.finrank K M : ℤ) + 4) + q) =
      (Module.finrank K M : ℤ) + 4 - q := by omega
  rw [hindex]

theorem exteriorKoszul_terms_hilbert :
    finiteHilbertLaurent (exteriorKoszulTerm₀Grading (K := K) (M := M)) -
      finiteHilbertLaurent (exteriorKoszulTerm₁Grading (K := K) (M := M)) +
      finiteHilbertLaurent (exteriorKoszulTerm₂Grading (K := K) (M := M)) =
    (1 - LaurentPolynomial.T 2) ^ 2 *
      (1 + LaurentPolynomial.T 1) ^ Module.finrank K M := by
  simp only [exteriorKoszulTerm₀Grading, exteriorKoszulTerm₁Grading,
    exteriorKoszulTerm₂Grading, finiteHilbertLaurent_shift, neg_neg,
    finiteHilbertLaurent_prod, exteriorIntegerGrading_hilbert]
  have hpow : (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) ^ 2 =
      LaurentPolynomial.T 4 := by simp only [LaurentPolynomial.T_pow]; norm_num
  rw [← hpow]
  ring

/-- The complete three-polynomial calculation for every pair of exterior
two-forms.  The subsequent tensor comparison identifies these actual
Koszul homology polynomials with the polynomial-module Betti polynomials. -/
theorem exteriorKoszul_all_hilbert_formulas (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent (exteriorKoszulH₀Grading f g) = exteriorQuotientHilbert f g ∧
    finiteHilbertLaurent (exteriorKoszulH₂Grading f g) =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) ∧
    finiteHilbertLaurent (exteriorKoszulH₁Grading f g) =
      exteriorQuotientHilbert f g +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
        (1 - LaurentPolynomial.T 2) ^ 2 *
          (1 + LaurentPolynomial.T 1) ^ Module.finrank K M := by
  refine ⟨rfl, exteriorKoszulH₂_hilbert f g, ?_⟩
  have h := exteriorKoszul_hilbert_euler f g
  rw [exteriorKoszul_terms_hilbert, exteriorKoszulH₂_hilbert] at h
  change exteriorQuotientHilbert f g - _ + _ = _ at h
  linear_combination -h

end ExteriorFormulas

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0560

section TAF_LiteralSource_0561
/- Original module: PaperVerification.AlternatingFormsPolynomialAction -/


/-!
# The polynomial action and its actual tensor Koszul complex

The polynomial variables act by multiplication by the given exterior
two-forms.  Evaluation is constructed through the centre of the exterior
algebra.  A componentwise tensor isomorphism then identifies the tensor of
the polynomial free resolution with the displayed exterior Koszul complex.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

section Restriction

variable {K R A B : Type u} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [Module K B] [IsScalarTower K R B]

/-- Scalar restriction on the source of a linear equivalence, using the
specified compatible coefficient-field action on its target. -/
def restrictDomainLinearEquiv (e : A ≃ₗ[R] B) :
    ((ModuleCat.restrictScalars (algebraMap K R)).obj (ModuleCat.of R A)) ≃ₗ[K] B where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c a := by
    change e (algebraMap K R c • (show A from a)) = c • e (show A from a)
    exact (e.map_smul (algebraMap K R c) (show A from a)).trans
      (algebraMap_smul R c (e (show A from a)))

@[simp] theorem restrictDomainLinearEquiv_apply (e : A ≃ₗ[R] B) (a : A) :
    restrictDomainLinearEquiv (K := K) e a = e a := rfl

end Restriction

section Action

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

def centralTwoForm (f : ⋀[K]^2 M) : Subalgebra.center K (ExteriorAlgebra K M) :=
  ⟨f, (Subalgebra.mem_center_iff).mpr (fun a => (twoForm_commute f a).eq.symm)⟩

/-- Genuine polynomial evaluation `u ↦ f`, `v ↦ g` into the exterior algebra. -/
def quadraticPolynomialEvaluation (f g : ⋀[K]^2 M) :
    PairPolynomial K →ₐ[K] ExteriorAlgebra K M :=
  (Subalgebra.center K (ExteriorAlgebra K M)).val.comp
    (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then centralTwoForm f else centralTwoForm g))

@[simp] theorem quadraticPolynomialEvaluation_X_zero (f g : ⋀[K]^2 M) :
    quadraticPolynomialEvaluation f g (MvPolynomial.X 0) = (f : ExteriorAlgebra K M) := by
  simp [quadraticPolynomialEvaluation, centralTwoForm]

@[simp] theorem quadraticPolynomialEvaluation_X_one (f g : ⋀[K]^2 M) :
    quadraticPolynomialEvaluation f g (MvPolynomial.X 1) = (g : ExteriorAlgebra K M) := by
  simp [quadraticPolynomialEvaluation, centralTwoForm]

/-- A type synonym records which pair determines the polynomial-module
structure.  Its elements are exactly the original exterior-algebra elements. -/
def ExteriorPairModule (f g : ⋀[K]^2 M) := ExteriorAlgebra K M

instance (f g : ⋀[K]^2 M) : AddCommGroup (ExteriorPairModule f g) :=
  inferInstanceAs (AddCommGroup (ExteriorAlgebra K M))

instance (f g : ⋀[K]^2 M) : Module K (ExteriorPairModule f g) :=
  inferInstanceAs (Module K (ExteriorAlgebra K M))

def exteriorPairModuleEquiv (f g : ⋀[K]^2 M) :
    ExteriorPairModule f g ≃ₗ[K] ExteriorAlgebra K M :=
  LinearEquiv.refl K (ExteriorAlgebra K M)

instance (f g : ⋀[K]^2 M) : Module (PairPolynomial K) (ExteriorPairModule f g) :=
  Module.compHom (ExteriorAlgebra K M) (quadraticPolynomialEvaluation f g).toRingHom

theorem exteriorPair_smul (f g : ⋀[K]^2 M) (p : PairPolynomial K)
    (a : ExteriorPairModule f g) :
    p • a = (quadraticPolynomialEvaluation f g p) * (exteriorPairModuleEquiv f g a) := rfl

instance (f g : ⋀[K]^2 M) : IsScalarTower K (PairPolynomial K) (ExteriorPairModule f g) where
  smul_assoc c p a := by
    change quadraticPolynomialEvaluation f g (c • p) * (exteriorPairModuleEquiv f g a) =
      c • (quadraticPolynomialEvaluation f g p * (exteriorPairModuleEquiv f g a))
    rw [map_smul, smul_mul_assoc]

instance (f g : ⋀[K]^2 M) : SMulCommClass K (PairPolynomial K) (ExteriorPairModule f g) where
  smul_comm c p a := by
    change c • (quadraticPolynomialEvaluation f g p * (exteriorPairModuleEquiv f g a)) =
      quadraticPolynomialEvaluation f g p * (c • (exteriorPairModuleEquiv f g a))
    exact (mul_smul_comm _ _ _).symm

@[simp] theorem exteriorPair_X_zero_smul (f g : ⋀[K]^2 M) (a : ExteriorPairModule f g) :
    MvPolynomial.X (R := K) (0 : Fin 2) • a =
      (f : ExteriorAlgebra K M) * (exteriorPairModuleEquiv f g a) := by
  rw [exteriorPair_smul, quadraticPolynomialEvaluation_X_zero]

@[simp] theorem exteriorPair_X_one_smul (f g : ⋀[K]^2 M) (a : ExteriorPairModule f g) :
    MvPolynomial.X (R := K) (1 : Fin 2) • a =
      (g : ExteriorAlgebra K M) * (exteriorPairModuleEquiv f g a) := by
  rw [exteriorPair_smul, quadraticPolynomialEvaluation_X_one]

def exteriorPolynomialTensorComplex (f g : ⋀[K]^2 M) :
    ChainComplex (ModuleCat (PairPolynomial K)) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj
    (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (pairPolynomialResolution K).complex)

def exteriorPolynomialTensorComplexOverK (f g : ⋀[K]^2 M) :
    ChainComplex (ModuleCat K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (exteriorPolynomialTensorComplex f g)

def exteriorPairComplex (f g : ⋀[K]^2 M) : ChainComplex (ModuleCat K) ℕ :=
  pairComplex (twoFormMultiplication f) (twoFormMultiplication g)
    (twoFormMultiplication_commute f g)

instance exteriorPairTerm_subsingleton (f g : ⋀[K]^2 M) (n : ℕ) :
    Subsingleton ((exteriorPairComplex f g).X (n+3)) := by
  change Subsingleton (⊥ : Submodule K (ExteriorAlgebra K M))
  infer_instance

instance exteriorTensorTerm_subsingleton (f g : ⋀[K]^2 M) (n : ℕ) :
    Subsingleton ((exteriorPolynomialTensorComplexOverK f g).X (n+3)) := by
  change Subsingleton (ExteriorPairModule f g ⊗[PairPolynomial K]
    (⊥ : Submodule (PairPolynomial K) (PairPolynomial K)))
  infer_instance

def exteriorTensorTermEquiv (f g : ⋀[K]^2 M) : (n : ℕ) →
    (exteriorPolynomialTensorComplexOverK f g).X n ≃ₗ[K] (exteriorPairComplex f g).X n
  | 0 => (restrictDomainLinearEquiv (K := K)
      (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))).trans
        (exteriorPairModuleEquiv f g)
  | 1 => (restrictDomainLinearEquiv (K := K)
      ((TensorProduct.prodRight (PairPolynomial K) (PairPolynomial K)
        (ExteriorPairModule f g) (PairPolynomial K) (PairPolynomial K)).trans
          ((TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g)).prodCongr
            (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))))).trans
        ((exteriorPairModuleEquiv f g).prodCongr (exteriorPairModuleEquiv f g))
  | 2 => (restrictDomainLinearEquiv (K := K)
      (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))).trans
        (exteriorPairModuleEquiv f g)
  | _ + 3 => LinearEquiv.ofSubsingleton _ _

@[simp] theorem exteriorTensorTermEquiv_zero_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K) :
    exteriorTensorTermEquiv f g 0 (a ⊗ₜ[PairPolynomial K] p) = p • a := rfl

@[simp] theorem exteriorTensorTermEquiv_one_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K × PairPolynomial K) :
    exteriorTensorTermEquiv f g 1 (a ⊗ₜ[PairPolynomial K] p) = (p.1 • a, p.2 • a) := rfl

@[simp] theorem exteriorTensorTermEquiv_two_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K) :
    exteriorTensorTermEquiv f g 2 (a ⊗ₜ[PairPolynomial K] p) = p • a := rfl

theorem exteriorTensorTermEquiv_comm (f g : ⋀[K]^2 M) (n : ℕ) :
    (exteriorTensorTermEquiv f g (n + 1)).toModuleIso.hom ≫
        (exteriorPairComplex f g).d (n + 1) n =
      (exteriorPolynomialTensorComplexOverK f g).d (n + 1) n ≫
        (exteriorTensorTermEquiv f g n).toModuleIso.hom := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    refine TensorProduct.inductionOn (R := PairPolynomial K) (M := ExteriorPairModule f g)
      (N := PairPolynomial K × PairPolynomial K) z ?_ ?_
    · intro a p
      change (f : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p.1 • a) +
          (g : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p.2 • a) =
        exteriorPairModuleEquiv f g ((MvPolynomial.X 0 * p.1 + MvPolynomial.X 1 * p.2) • a)
      simp only [add_smul, mul_smul, map_add,
        exteriorPair_X_zero_smul, exteriorPair_X_one_smul,
        exteriorPairModuleEquiv, LinearEquiv.refl_apply] <;> rfl
    · intro x y hx hy
      rw [map_add,map_add,hx,hy]
  | succ n =>
    cases n with
    | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      refine TensorProduct.inductionOn (R := PairPolynomial K) (M := ExteriorPairModule f g)
        (N := PairPolynomial K) z ?_ ?_
      · intro a p
        change (-((g : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p • a)),
            (f : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p • a)) =
          (exteriorPairModuleEquiv f g (-(MvPolynomial.X 1 * p) • a),
            exteriorPairModuleEquiv f g ((MvPolynomial.X 0 * p) • a))
        simp only [neg_smul, mul_smul, map_neg,
          exteriorPair_X_one_smul, exteriorPair_X_zero_smul,
          exteriorPairModuleEquiv, LinearEquiv.refl_apply] <;> rfl
      · intro x y hx hy
        rw [map_add,map_add,hx,hy]
    | succ n =>
      have hz : IsZero ((exteriorPolynomialTensorComplexOverK f g).X (n + 3)) :=
        ModuleCat.isZero_of_subsingleton _
      exact hz.eq_of_src _ _

/-- The tensor of the actual polynomial free resolution is isomorphic to
the actual exterior two-form Koszul complex, with every differential checked. -/
def exteriorTensorComplexIso (f g : ⋀[K]^2 M) :
    exteriorPolynomialTensorComplexOverK f g ≅ exteriorPairComplex f g :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (exteriorTensorTermEquiv f g n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      exact exteriorTensorTermEquiv_comm f g j)

/-- Coefficient-field restriction commutes with homology because it is an
exact functor on the genuine module category. -/
def exteriorTensorHomologyRestrictionIso (f g : ⋀[K]^2 M) (i : ℕ) :
    (exteriorPolynomialTensorComplexOverK f g).homology i ≅
      (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
        ((exteriorPolynomialTensorComplex f g).homology i) :=
  ((exteriorPolynomialTensorComplex f g).sc i).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K)))

/-- The actual derived tensor vector space, with coefficient scalars
restricted along the inclusion `K → K[u,v]`. -/
def exteriorPolynomialTor (f g : ⋀[K]^2 M) (i : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).obj
        (ModuleCat.of (PairPolynomial K) (PairResidue K)))

/-- The derived-functor comparison is now specialized to the literal action
by the two exterior forms; the isomorphism introduces no homology assumption. -/
def exteriorPolynomialTorIso (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorPolynomialTor f g i ≅ (exteriorPairComplex f g).homology i :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapIso
      (pairPolynomialTorIso K (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g)) i) ≪≫
    (exteriorTensorHomologyRestrictionIso f g i).symm ≪≫
    HomologicalComplex.homologyMapIso (exteriorTensorComplexIso f g) i

theorem exteriorPolynomialTor_isZero_above (f g : ⋀[K]^2 M) {i : ℕ} (hi : 2 < i) :
    IsZero (exteriorPolynomialTor f g i) :=
  (pairComplex_isZero_homology _ _ _ hi).of_iso (exteriorPolynomialTorIso f g i)

end Action

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0561

section TAF_LiteralSource_0562
/- Original module: PaperVerification.AlternatingFormsBetti -/


/-!
# The graded Betti spaces for the actual polynomial action

The homology comparison in this file uses Mathlib's genuine derived tensor
functor.  The internal grading is induced from the homogeneous polynomial
Koszul resolution, whose two generators have degree two.  In particular the
three exterior terms carry shifts zero, two and four.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

universe u

section GradingTransport

variable {K A B : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem finiteHilbertLaurent_map [FiniteDimensional K A] [FiniteDimensional K B]
    (G : TauCeti.InternalGrading K A) (e : A ≃ₗ[K] B) :
    finiteHilbertLaurent (G.map e) = finiteHilbertLaurent G := by
  ext q
  simp only [finiteHilbertLaurent_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    ((congrArg (fun S : Submodule K B ↦ Module.finrank K S)
      (TauCeti.InternalGrading.map_piece G e q)).trans (e.finrank_map_eq (G.piece q)))

/-- The unique grading on an actual zero vector space. -/
def zeroInternalGrading [Subsingleton A] : TauCeti.InternalGrading K A where
  piece := fun _ => ⊥
  isInternal := by
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro x
      exact ⟨0, Subsingleton.elim _ _⟩

end GradingTransport

section HomologyComparison

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- Degree-zero categorical homology is the literal quotient by the image
of the first displayed exterior differential. -/
def exteriorHomologyZeroEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 0 ≃ₗ[K]
      (ExteriorAlgebra K M ⧸ LinearMap.range (exteriorKoszulFirst f g)) :=
  ((exteriorPairComplex f g).isoHomologyι₀ ≪≫
    (exteriorPairComplex f g).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((exteriorPairComplex f g).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

/-- The middle categorical homology is exactly kernel modulo image, with
the map to cycles induced by the actual second differential. -/
def exteriorHomologyOneEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 1 ≃ₗ[K]
      (LinearMap.ker (exteriorKoszulFirst f g) ⧸
        LinearMap.range (shortComplexToCycles (exteriorKoszulSecond f g)
          (exteriorKoszulFirst f g) (exteriorKoszul_comp f g))) :=
  ((exteriorPairComplex f g).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ((exteriorPairComplex f g).sc' 2 1 0).moduleCatHomologyIso).toLinearEquiv

/-- There is no incoming map in homological degree two.  Its actual
homology is therefore the actual common annihilator, before applying any
dimension or duality theorem. -/
def exteriorHomologyTwoEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 2 ≃ₗ[K] ExteriorKoszulTopKernel f g := by
  let e : (exteriorPairComplex f g).homology 2 ≅
      ModuleCat.of K (LinearMap.ker (exteriorKoszulSecond f g)) :=
    ((exteriorPairComplex f g).isoHomologyπ 3 2 (by simp)
      (by simp [exteriorPairComplex, pairComplex_d, pairDifferential] <;> rfl)).symm ≪≫
      (exteriorPairComplex f g).cyclesIsoSc' 3 2 1 (by simp) (by simp) ≪≫
        ((exteriorPairComplex f g).sc' 3 2 1).moduleCatCyclesIso
  exact e.toLinearEquiv.trans (LinearEquiv.ofEq _ _ (by
    simp only [ExteriorKoszulTopKernel, shortComplexToCycles, LinearMap.ker_codRestrict]))

def exteriorTorZeroEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 0 ≃ₗ[K]
      (ExteriorAlgebra K M ⧸ LinearMap.range (exteriorKoszulFirst f g)) :=
  (exteriorPolynomialTorIso f g 0).toLinearEquiv.trans (exteriorHomologyZeroEquiv f g)

def exteriorTorOneEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 1 ≃ₗ[K]
      (LinearMap.ker (exteriorKoszulFirst f g) ⧸
        LinearMap.range (shortComplexToCycles (exteriorKoszulSecond f g)
          (exteriorKoszulFirst f g) (exteriorKoszul_comp f g))) :=
  (exteriorPolynomialTorIso f g 1).toLinearEquiv.trans (exteriorHomologyOneEquiv f g)

def exteriorTorTwoEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 2 ≃ₗ[K] ExteriorKoszulTopKernel f g :=
  (exteriorPolynomialTorIso f g 2).toLinearEquiv.trans (exteriorHomologyTwoEquiv f g)

instance exteriorPolynomialTor_finite (f g : ⋀[K]^2 M) (i : ℕ) :
    FiniteDimensional K (exteriorPolynomialTor f g i) := by
  cases i with
  | zero => exact Module.Finite.equiv (exteriorTorZeroEquiv f g).symm
  | succ i =>
    cases i with
    | zero => exact Module.Finite.equiv (exteriorTorOneEquiv f g).symm
    | succ i =>
      cases i with
      | zero => exact Module.Finite.equiv (exteriorTorTwoEquiv f g).symm
      | succ i =>
        letI : Subsingleton (exteriorPolynomialTor f g (i + 3)) :=
          ModuleCat.subsingleton_of_isZero (exteriorPolynomialTor_isZero_above f g (by omega))
        infer_instance

/-- The grading on actual Tor, transported along the canonical comparison
from the homogeneous Koszul resolution.  The shifts are those of the
resolution, not shifts chosen to fit a Hilbert-series answer. -/
def exteriorTorGrading (f g : ⋀[K]^2 M) : (i : ℕ) →
    TauCeti.InternalGrading K (exteriorPolynomialTor f g i)
  | 0 => (exteriorKoszulH₀Grading f g).map (exteriorTorZeroEquiv f g).symm
  | 1 => (exteriorKoszulH₁Grading f g).map (exteriorTorOneEquiv f g).symm
  | 2 => (exteriorKoszulH₂Grading f g).map (exteriorTorTwoEquiv f g).symm
  | i + 3 => by
    letI : Subsingleton (exteriorPolynomialTor f g (i + 3)) :=
      ModuleCat.subsingleton_of_isZero (exteriorPolynomialTor_isZero_above f g (by omega))
    exact zeroInternalGrading

/-- The Betti polynomial is the Hilbert series of the actual graded derived
tensor vector space, with the residue field at the origin of `K[u,v]`. -/
def exteriorBettiPolynomial (f g : ⋀[K]^2 M) (i : ℕ) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (exteriorTorGrading f g i)

@[simp] theorem exteriorBettiPolynomial_zero (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 0 = finiteHilbertLaurent (exteriorKoszulH₀Grading f g) :=
  finiteHilbertLaurent_map _ _

set_option maxHeartbeats 1000000 in
@[simp] theorem exteriorBettiPolynomial_one (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 1 = finiteHilbertLaurent (exteriorKoszulH₁Grading f g) :=
  finiteHilbertLaurent_map _ _

set_option maxHeartbeats 1000000 in
@[simp] theorem exteriorBettiPolynomial_two (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 2 = finiteHilbertLaurent (exteriorKoszulH₂Grading f g) :=
  finiteHilbertLaurent_map _ _

theorem exteriorBettiPolynomial_above (f g : ⋀[K]^2 M) {i : ℕ} (hi : 2 < i) :
    exteriorBettiPolynomial f g i = 0 := by
  have hi' : i = (i - 3) + 3 := by omega
  rw [hi']
  ext q
  simp only [exteriorBettiPolynomial, exteriorTorGrading, zeroInternalGrading,
    finiteHilbertLaurent_coeff, finrank_bot, Nat.cast_zero, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] <;> rfl

/-- Proposition 5.4: all graded Betti polynomials, for an arbitrary pair of
exterior two-forms and with no genericity, nondegeneracy, or rank assumption.

`exteriorPolynomialTor` is Mathlib's derived tensor, the polynomial action
is actual multiplication by the two forms, and the residue module is proved
isomorphic to the coefficient field.  The exact comparison with the
homogeneous free Koszul resolution supplies `exteriorTorGrading`.
-/
theorem paper_proposition_5_4 (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 0 = exteriorQuotientHilbert f g ∧
    exteriorBettiPolynomial f g 2 =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) ∧
    exteriorBettiPolynomial f g 1 =
      exteriorQuotientHilbert f g +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
        (1 - LaurentPolynomial.T 2) ^ 2 *
          (1 + LaurentPolynomial.T 1) ^ Module.finrank K M ∧
    ∀ i : ℕ, 2 < i → IsZero (exteriorPolynomialTor f g i) ∧
      exteriorBettiPolynomial f g i = 0 := by
  obtain ⟨h₀, h₂, h₁⟩ := exteriorKoszul_all_hilbert_formulas f g
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [exteriorBettiPolynomial_zero] using h₀
  · simpa only [exteriorBettiPolynomial_two] using h₂
  · simpa only [exteriorBettiPolynomial_one] using h₁
  · intro i hi
    exact ⟨exteriorPolynomialTor_isZero_above f g hi,
      exteriorBettiPolynomial_above f g hi⟩

end HomologyComparison

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0562

section TAF_LiteralSource_0563
/- Original module: PaperVerification.AlternatingFormsBettiGrading -/


/-!
# Faithfulness of the internal degree in Proposition 5.4

The actual polynomial action preserves the grading with both variables of
weight two.  The tensor resolution grading agrees on homogeneous pure
tensors with their tensor-product degree, including the shifts two and four.
These statements justify the internal degree in the derived-Tor comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- The augmentation has degree zero when each polynomial variable has
weight two and the coefficient field is concentrated in degree zero. -/
theorem pairConstantCoefficient_positive_degree {p : PairPolynomial K} {q : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q) (hq : q ≠ 0) :
    pairConstantCoefficient K p = 0 := by
  change MvPolynomial.constantCoeff p = 0
  by_contra h
  have hc : p.coeff 0 ≠ 0 := by
    simpa only [MvPolynomial.constantCoeff_eq] using h
  have h0q : 0 = q := by simpa only [map_zero] using hp hc
  exact hq h0q.symm

theorem quadraticPolynomialEvaluation_monomial (f g : ⋀[K]^2 M)
    (d : Fin 2 →₀ ℕ) (c : K) :
    quadraticPolynomialEvaluation f g (MvPolynomial.monomial d c) =
      c • ((f : ExteriorAlgebra K M) ^ d 0 * (g : ExteriorAlgebra K M) ^ d 1) := by
  classical
  unfold quadraticPolynomialEvaluation
  rw [AlgHom.comp_apply, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_two, centralTwoForm, Algebra.smul_def]

/-- Actual substitution of two exterior forms preserves the degree where
each polynomial variable is assigned weight two. -/
theorem quadraticPolynomialEvaluation_homogeneous (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q) :
    quadraticPolynomialEvaluation f g p ∈ ⋀[K]^q M := by
  classical
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdq := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_two] at hdq
  rw [quadraticPolynomialEvaluation_monomial]
  apply Submodule.smul_mem
  simpa only [hdq] using
    (SetLike.mul_mem_graded (SetLike.pow_mem_graded (d 0) f.property)
      (SetLike.pow_mem_graded (d 1) g.property))

theorem exteriorPair_homogeneous_smul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    ((p • a : ExteriorPairModule f g) : ExteriorAlgebra K M) ∈ ⋀[K]^(q + r) M := by
  change quadraticPolynomialEvaluation f g p * exteriorPairModuleEquiv f g a ∈
    ⋀[K]^(q + r) M
  exact SetLike.mul_mem_graded (quadraticPolynomialEvaluation_homogeneous f g hp)
    (show exteriorPairModuleEquiv f g a ∈ ⋀[K]^r M from ha)

variable [FiniteDimensional K M]

/-- The actual tensor complex has the grading of the free polynomial
resolution: its free basis vectors have internal degrees zero, two and four. -/
def exteriorTensorTermGrading (f g : ⋀[K]^2 M) : (i : ℕ) →
    TauCeti.InternalGrading K ((exteriorPolynomialTensorComplexOverK f g).X i)
  | 0 => exteriorKoszulTerm₀Grading.map (exteriorTensorTermEquiv f g 0).symm
  | 1 => exteriorKoszulTerm₁Grading.map (exteriorTensorTermEquiv f g 1).symm
  | 2 => exteriorKoszulTerm₂Grading.map (exteriorTensorTermEquiv f g 2).symm
  | _ + 3 => zeroInternalGrading

theorem exteriorTensorTermGrading_zero_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 0) :
    x ∈ (exteriorTensorTermGrading f g 0).piece q ↔
      exteriorTensorTermEquiv f g 0 x ∈ exteriorKoszulTerm₀Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_one_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 1) :
    x ∈ (exteriorTensorTermGrading f g 1).piece q ↔
      exteriorTensorTermEquiv f g 1 x ∈ exteriorKoszulTerm₁Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_two_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 2) :
    x ∈ (exteriorTensorTermGrading f g 2).piece q ↔
      exteriorTensorTermEquiv f g 2 x ∈ exteriorKoszulTerm₂Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_zero_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 0).piece ((q + r : ℕ) : ℤ) := by
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _,
    exteriorTensorTermEquiv_zero_tmul f g a p]
  change ((p • a : ExteriorPairModule f g) : ExteriorAlgebra K M) ∈
    exteriorIntegerGrading.piece ((q + r : ℕ) : ℤ)
  rw [exteriorIntegerGrading_piece_nat]
  exact exteriorPair_homogeneous_smul f g hp ha

theorem exteriorTensorTermGrading_one_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K × PairPolynomial K} {q r : ℕ}
    (hp₁ : p.1.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    (hp₂ : p.2.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 1).piece ((q + r : ℕ) + 2 : ℤ) := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (p.1 • a : ExteriorPairModule f g) ∈
      exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 2 + -2) ∧
    (p.2 • a : ExteriorPairModule f g) ∈
      exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 2 + -2)
  have hq : ((q + r : ℕ) : ℤ) + 2 + -2 = ((q + r : ℕ) : ℤ) := by omega
  rw [hq, exteriorIntegerGrading_piece_nat]
  exact ⟨exteriorPair_homogeneous_smul f g hp₁ ha,
    exteriorPair_homogeneous_smul f g hp₂ ha⟩

theorem exteriorTensorTermGrading_two_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 2).piece ((q + r : ℕ) + 4 : ℤ) := by
  rw [exteriorTensorTermGrading_two_mem_iff f g _ _,
    exteriorTensorTermEquiv_two_tmul f g a p]
  rw [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece]
  change (p • a : ExteriorPairModule f g) ∈
    exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 4 + -4)
  have hq : ((q + r : ℕ) : ℤ) + 4 + -4 = ((q + r : ℕ) : ℤ) := by omega
  rw [hq, exteriorIntegerGrading_piece_nat]
  exact exteriorPair_homogeneous_smul f g hp ha

/-- The chosen degree on the actual tensor complex is also characterized
on its polynomial free generators.  Thus it is exactly the usual tensor
grading, with no change of degree in the homology comparison. -/
theorem exteriorTensorTermGrading_zero_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] (1 : PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 0).piece q ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _,
    exteriorTensorTermEquiv_zero_tmul f g a 1, one_smul]
  rfl

theorem exteriorTensorTermGrading_two_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] (1 : PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 2).piece (q + 4) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_two_mem_iff f g _ _,
    exteriorTensorTermEquiv_two_tmul f g a 1, one_smul]
  rw [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece]
  change a ∈ exteriorIntegerGrading.piece (q + 4 + -4) ↔ _
  rw [show q + 4 + -4 = q by omega]

theorem exteriorTensorTermGrading_one_left_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] ((1, 0) : PairPolynomial K × PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 1).piece (q + 2) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (1 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ∧
    (0 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ↔ _
  have hq : q + 2 + -2 = q := by omega
  simp only [hq, one_smul, zero_smul, Submodule.zero_mem, and_true]

theorem exteriorTensorTermGrading_one_right_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] ((0, 1) : PairPolynomial K × PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 1).piece (q + 2) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (0 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ∧
    (1 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ↔ _
  have hq : q + 2 + -2 = q := by omega
  simp only [hq, one_smul, zero_smul, Submodule.zero_mem, true_and]

/-- The first actual tensor differential is homogeneous of degree zero. -/
theorem exteriorTensorFirst_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous
      ((exteriorPolynomialTensorComplexOverK f g).d 1 0).hom
      (exteriorTensorTermGrading f g 1).piece (exteriorTensorTermGrading f g 0).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorTensorTermGrading_one_mem_iff f g q a] at ha
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _]
  have h := (exteriorKoszulFirst_homogeneous f g).map_mem ha
  have he := congrArg
    (fun k : (exteriorPolynomialTensorComplexOverK f g).X 1 ⟶
      (exteriorPairComplex f g).X 0 => k a) (exteriorTensorTermEquiv_comm f g 0)
  change exteriorKoszulFirst f g (exteriorTensorTermEquiv f g 1 a) =
    exteriorTensorTermEquiv f g 0 ((exteriorPolynomialTensorComplexOverK f g).d 1 0 a) at he
  rw [← he]
  exact h

/-- The second actual tensor differential has the same internal degree. -/
theorem exteriorTensorSecond_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous
      ((exteriorPolynomialTensorComplexOverK f g).d 2 1).hom
      (exteriorTensorTermGrading f g 2).piece (exteriorTensorTermGrading f g 1).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorTensorTermGrading_two_mem_iff f g q a] at ha
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _]
  have h := (exteriorKoszulSecond_homogeneous f g).map_mem ha
  have he := congrArg
    (fun k : (exteriorPolynomialTensorComplexOverK f g).X 2 ⟶
      (exteriorPairComplex f g).X 1 => k a) (exteriorTensorTermEquiv_comm f g 1)
  change exteriorKoszulSecond f g (exteriorTensorTermEquiv f g 2 a) =
    exteriorTensorTermEquiv f g 1 ((exteriorPolynomialTensorComplexOverK f g).d 2 1 a) at he
  rw [← he]
  exact h

theorem exteriorKoszulH₁_piece_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (exteriorKoszulH₁Grading f g).piece q = ⊥ := by
  have hker :
      ((exteriorKoszulTerm₁Grading (K := K) (M := M)).ker
        (exteriorKoszulFirst_homogeneous f g)).piece q = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    rw [TauCeti.InternalGrading.mem_ker_piece,exteriorKoszulTerm₁Grading,
      TauCeti.InternalGrading.shift_piece,TauCeti.InternalGrading.prod_piece] at ha
    change a.1.1 ∈ exteriorIntegerGrading.piece (q + -2) ∧
      a.1.2 ∈ exteriorIntegerGrading.piece (q + -2) at ha
    rw [exteriorIntegerGrading_piece_negative (by omega : q + -2 < 0)] at ha
    apply Subtype.ext
    exact Prod.ext ha.1 ha.2
  unfold exteriorKoszulH₁Grading shortComplexH₁Grading
  rw [TauCeti.InternalGrading.quotient_piece, hker, Submodule.map_bot]

/-- Every negative internal degree is zero. Thus the Laurent presentation
of the Betti identities retains ordinary polynomial Hilbert series. -/
theorem exteriorBettiPolynomial_negative (f g : ⋀[K]^2 M) (i : ℕ)
    {q : ℤ} (hq : q < 0) : (exteriorBettiPolynomial f g i).coeff q = 0 := by
  cases i with
  | zero =>
    rw [exteriorBettiPolynomial_zero, finiteHilbertLaurent_coeff,
      exteriorKoszulH₀_piece_negative f g hq, finrank_bot, Nat.cast_zero]
  | succ i =>
    cases i with
    | zero =>
      rw [exteriorBettiPolynomial_one, finiteHilbertLaurent_coeff,
        exteriorKoszulH₁_piece_negative f g hq, finrank_bot, Nat.cast_zero]
    | succ i =>
      cases i with
      | zero =>
        rw [exteriorBettiPolynomial_two, finiteHilbertLaurent_coeff,
          exteriorKoszulH₂_piece_below f g (by omega), finrank_bot, Nat.cast_zero]
      | succ i =>
        rw [exteriorBettiPolynomial_above f g (by omega), AddMonoidAlgebra.coeff_zero] <;> rfl

theorem laurent_trunc_coefficient (F : LaurentPolynomial ℤ) (q : ℕ) :
    (LaurentPolynomial.trunc F).coeff q = F.coeff (q : ℤ) := rfl

theorem toLaurent_trunc_of_nonnegative (F : LaurentPolynomial ℤ)
    (hF : ∀ q : ℤ, q < 0 → F.coeff q = 0) :
    (LaurentPolynomial.trunc F).toLaurent = F := by
  ext q
  by_cases hq : 0 ≤ q
  · have hq' : q = (q.toNat : ℤ) := by omega
    rw [hq', toLaurent_coefficient_nat, laurent_trunc_coefficient]
  · rw [toLaurent_coefficient_negative _ (by omega), hF q (by omega)]

/-- The ordinary polynomial exists uniquely and has precisely the actual
Tor-component dimensions as its coefficients. -/
theorem exteriorBettiPolynomial_is_ordinary (f g : ⋀[K]^2 M) (i : ℕ) :
    ∃! B : Polynomial ℤ, B.toLaurent = exteriorBettiPolynomial f g i := by
  refine ⟨LaurentPolynomial.trunc (exteriorBettiPolynomial f g i),
    toLaurent_trunc_of_nonnegative _ (fun q hq ↦ exteriorBettiPolynomial_negative f g i hq), ?_⟩
  intro B hB
  apply Polynomial.toLaurent_injective
  rw [hB, toLaurent_trunc_of_nonnegative _
    (fun q hq ↦ exteriorBettiPolynomial_negative f g i hq)]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0563

section TAF_LiteralSource_0564
/- Original module: PaperVerification.AlternatingFormsBettiOrigin -/


/-!
# The Betti formulas with the coefficient field at the origin

The residue quotient is identified with the original coefficient field as
a module over the actual polynomial ring. Functoriality of ordinary Tor
then gives the complete formulas with that coefficient-field argument.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

universe u

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- Ordinary Mathlib Tor with the actual coefficient field, on which both
polynomial variables act as zero. -/
def exteriorPolynomialTorAtOrigin (f g : ⋀[K]^2 M) (i : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).obj
        (ModuleCat.of (PairPolynomial K) (PairOriginModule K)))

/-- Naturality in the second argument identifies the two literal Tor
objects through the proved polynomial-linear residue-field isomorphism. -/
def exteriorPolynomialTorOriginIso (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorPolynomialTor f g i ≅ exteriorPolynomialTorAtOrigin f g i :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapIso
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).mapIso
        (pairResidueOriginEquiv K).toModuleIso)

instance exteriorPolynomialTorAtOrigin_finite (f g : ⋀[K]^2 M) (i : ℕ) :
    FiniteDimensional K (exteriorPolynomialTorAtOrigin f g i) :=
  Module.Finite.equiv (exteriorPolynomialTorOriginIso f g i).toLinearEquiv

/-- Transport along the actual residue-field comparison preserves the
internal grading already justified on the homogeneous tensor resolution. -/
def exteriorOriginTorGrading (f g : ⋀[K]^2 M) (i : ℕ) :
    TauCeti.InternalGrading K (exteriorPolynomialTorAtOrigin f g i) :=
  (exteriorTorGrading f g i).map (exteriorPolynomialTorOriginIso f g i).toLinearEquiv

def exteriorOriginBettiPolynomial (f g : ⋀[K]^2 M) (i : ℕ) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (exteriorOriginTorGrading f g i)

theorem exteriorOriginBettiPolynomial_eq (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorOriginBettiPolynomial f g i = exteriorBettiPolynomial f g i :=
  finiteHilbertLaurent_map _ _

/-- Proposition 5.4 with the coefficient field itself as the second Tor
argument, in every homological degree and with all internal shifts intact. -/
theorem paper_proposition_5_4_origin (f g : ⋀[K]^2 M) :
    exteriorOriginBettiPolynomial f g 0 = exteriorQuotientHilbert f g ∧
    exteriorOriginBettiPolynomial f g 2 =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) ∧
    exteriorOriginBettiPolynomial f g 1 =
      exteriorQuotientHilbert f g +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
        (1 - LaurentPolynomial.T 2) ^ 2 *
          (1 + LaurentPolynomial.T 1) ^ Module.finrank K M ∧
    ∀ i : ℕ, 2 < i → IsZero (exteriorPolynomialTorAtOrigin f g i) ∧
      exteriorOriginBettiPolynomial f g i = 0 := by
  obtain ⟨h₀, h₂, h₁, hi⟩ := paper_proposition_5_4 f g
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₀
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₂
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₁
  · intro i h
    refine ⟨(hi i h).1.of_iso (exteriorPolynomialTorOriginIso f g i).symm, ?_⟩
    simpa only [exteriorOriginBettiPolynomial_eq] using (hi i h).2

theorem exteriorOriginBettiPolynomial_is_ordinary (f g : ⋀[K]^2 M) (i : ℕ) :
    ∃! B : Polynomial ℤ, B.toLaurent = exteriorOriginBettiPolynomial f g i := by
  rw [exteriorOriginBettiPolynomial_eq]
  exact exteriorBettiPolynomial_is_ordinary f g i

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0564

section TAF_LiteralSource_0565
/- Original module: PaperVerification.AlternatingFormsExcessDimension -/


/-!
# The exact dimension contribution of two independent extra syzygies

The result is ordinary finite-dimensional rank-nullity. A checked injection
of the Koszul term together with two extra cycles into the full kernel
produces an integer lower bound for the genuine cokernel. No maximal-rank
assertion or Hilbert function is built into a definition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

section LinearAlgebra

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]

/-- The two extra vectors are independent modulo the image of `ψ`.
The hypothesis is the literal relation in `B`, not a presumed dimension. -/
theorem cokernel_finrank_lower_of_two_extra_cycles
    (φ : B →ₗ[K] A) (ψ : C →ₗ[K] B)
    (hcomp : φ.comp ψ = 0) (hψ : Function.Injective ψ)
    (z₁ z₂ : B) (hz₁ : φ z₁ = 0) (hz₂ : φ z₂ = 0)
    (hrel : ∀ (c : C) (α β : K),
      ψ c + α • z₁ + β • z₂ = 0 → α = 0 ∧ β = 0) :
    (Module.finrank K A : ℤ) - (Module.finrank K B : ℤ) +
        (Module.finrank K C : ℤ) + 2 ≤
      (Module.finrank K (A ⧸ LinearMap.range φ) : ℤ) := by
  let e : C × (K × K) →ₗ[K] B :=
    { toFun x := ψ x.1 + x.2.1 • z₁ + x.2.2 • z₂
      map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]; abel
      map_smul' a x := by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
          smul_smul, RingHom.id_apply, smul_eq_mul] }
  have heker (x : C × (K × K)) : e x ∈ LinearMap.ker φ := by
    change φ (ψ x.1 + x.2.1 • z₁ + x.2.2 • z₂) = 0
    have hc : φ (ψ x.1) = 0 := LinearMap.congr_fun hcomp x.1
    simp only [map_add, map_smul, hc, hz₁, hz₂, smul_zero, add_zero]
  let e' : C × (K × K) →ₗ[K] LinearMap.ker φ := e.codRestrict _ heker
  have he : Function.Injective e' := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨c, α, β⟩ hx
    have hx' : ψ c + α • z₁ + β • z₂ = 0 := congrArg Subtype.val hx
    obtain ⟨hα, hβ⟩ := hrel c α β hx'
    have hc : c = 0 := hψ (by simpa only [hα, hβ, zero_smul, add_zero, map_zero] using hx')
    change (c, (α, β)) = (0, (0, 0))
    exact Prod.ext hc (Prod.ext hα hβ)
  have hdim : Module.finrank K C + 2 ≤ Module.finrank K (LinearMap.ker φ) := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_assoc] using
      (LinearMap.finrank_le_finrank_of_injective he)
  have hnull := φ.finrank_range_add_finrank_ker
  have hquot := (LinearMap.range φ).finrank_quotient_add_finrank
  omega

end LinearAlgebra

section ExteriorComplex

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The literal degree `q+4` relation map. -/
def exteriorRelationMapDegree (f g : ⋀[K]^2 M) (q : ℕ) :
    (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) →ₗ[K] ⋀[K]^(q+4) M where
  toFun x := ⟨(f : ExteriorAlgebra K M) * x.1 + (g : ExteriorAlgebra K M) * x.2, by
    apply Submodule.add_mem
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded f.property x.1.property
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded g.property x.2.property⟩
  map_add' x y := by apply Subtype.ext; simp only [Prod.fst_add, Prod.snd_add,
    AddMemClass.coe_add, mul_add]; abel
  map_smul' a x := by apply Subtype.ext; simp only [Prod.smul_fst, Prod.smul_snd,
    SetLike.val_smul, mul_smul_comm, smul_add, RingHom.id_apply]

/-- The actual Koszul syzygy `(Gh,-Fh)`, with its genuine degree. -/
def exteriorKoszulMapDegree (f g : ⋀[K]^2 M) (q : ℕ) :
    ⋀[K]^q M →ₗ[K] (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) where
  toFun h :=
    (⟨(g : ExteriorAlgebra K M) * h, by
      simpa only [Nat.add_comm] using SetLike.mul_mem_graded g.property h.property⟩,
     ⟨-((f : ExteriorAlgebra K M) * h), by
      apply Submodule.neg_mem
      simpa only [Nat.add_comm] using SetLike.mul_mem_graded f.property h.property⟩)
  map_add' x y := by apply Prod.ext <;> apply Subtype.ext <;>
    simp only [AddMemClass.coe_add, mul_add, neg_add_rev, Prod.fst_add, Prod.snd_add,
      add_comm]
  map_smul' a x := by apply Prod.ext <;> apply Subtype.ext <;>
    simp only [SetLike.val_smul, mul_smul_comm, smul_neg, Prod.smul_fst,
      Prod.smul_snd, RingHom.id_apply]

theorem exteriorRelationMapDegree_comp (f g : ⋀[K]^2 M) (q : ℕ) :
    (exteriorRelationMapDegree f g q).comp (exteriorKoszulMapDegree f g q) = 0 := by
  apply LinearMap.ext
  intro h
  apply Subtype.ext
  change (f : ExteriorAlgebra K M) * ((g : ExteriorAlgebra K M) * h) +
    (g : ExteriorAlgebra K M) * (-((f : ExteriorAlgebra K M) * h)) = 0
  rw [mul_neg, ← mul_assoc, ← mul_assoc, (twoForm_commute f (g : ExteriorAlgebra K M)).eq]
  exact add_neg_cancel _

theorem exteriorKoszulMapDegree_injective (f g : ⋀[K]^2 M) (q : ℕ)
    (hF : ∀ h : ⋀[K]^q M, (f : ExteriorAlgebra K M) * h = 0 → h = 0) :
    Function.Injective (exteriorKoszulMapDegree f g q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro h hh
  have hx := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
    (x.2 : ExteriorAlgebra K M)) hh
  change -((f : ExteriorAlgebra K M) * h) = 0 at hx
  exact hF h (neg_eq_zero.mp hx)

/-- The range is precisely the degree of the genuine two-generated ideal. -/
theorem exteriorRelationMapDegree_range (f g : ⋀[K]^2 M) (q : ℕ) :
    LinearMap.range (exteriorRelationMapDegree f g q) =
      exteriorDegreeRelations f g (q+4) := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩, rfl⟩
    change (f : ExteriorAlgebra K M) * a + (g : ExteriorAlgebra K M) * b ∈
      exteriorRelationIdeal f g
    apply Ideal.mem_span_pair.mpr
    refine ⟨(a : ExteriorAlgebra K M), (b : ExteriorAlgebra K M), ?_⟩
    rw [(twoForm_commute f a).eq, (twoForm_commute g b).eq]
  · intro hx
    let x' : ⋀[K]^(2+(q+2)) M := ⟨x.val, by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property⟩
    have hx' : x' ∈ exteriorDegreeRelations f g (2+(q+2)) := hx
    rw [exteriorDegreeRelations_eq_images] at hx'
    obtain ⟨a, ⟨a', rfl⟩, b, ⟨b', rfl⟩, hab⟩ := Submodule.mem_sup.mp hx'
    refine ⟨(a',b'), ?_⟩
    apply Subtype.ext
    change (f : ExteriorAlgebra K M) * (a' : ExteriorAlgebra K M) +
      (g : ExteriorAlgebra K M) * (b' : ExteriorAlgebra K M) = x.val
    simpa only [AddMemClass.coe_add, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]
      using congrArg (fun z : ⋀[K]^(2+(q+2)) M => (z : ExteriorAlgebra K M)) hab


end ExteriorComplex

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0565

section TAF_LiteralSource_0566
/- Original module: PaperVerification.AlternatingFormsSparseProjection -/


/-!
# Sparse projections detecting both Frobenius syzygies

The first projection retains exactly the vertices `4j,4j+1` for `j<r`.
It kills the second path quadratic and sends the first to `r` disjoint pair
monomials. Its `r`th power is the nonzero factorial times their retained
exterior product. Reflection gives the corresponding certificate with the
two path quadrics interchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

section PairedBasis

variable {I ι : Type*} [LinearOrder I] [Fintype ι] [DecidableEq ι]

/-- Pair products built from distinct basis generators are nonzero in the
actual exterior algebra. -/
theorem paired_basis_monomial_ne_zero (b : Module.Basis I K M) (u v : ι → I)
    (huv : Function.Injective (Sum.elim u v : ι ⊕ ι → I)) (P : Finset ι) :
    pairedMonomial (K := K) (fun i => b (u i)) (fun i => b (v i)) P ≠ 0 := by
  classical
  have hu : Function.Injective u := fun i j h => Sum.inl_injective (huv h)
  have hv : Function.Injective v := fun i j h => Sum.inr_injective (huv h)
  have hdis : List.Disjoint (P.toList.map u) (P.toList.map v) := by
    intro i hiu hiv
    obtain ⟨a, ha, hia⟩ := List.mem_map.mp hiu
    obtain ⟨c, hc, hic⟩ := List.mem_map.mp hiv
    have hbad : (Sum.inl a : ι ⊕ ι) = Sum.inr c := huv (hia.trans hic.symm)
    cases hbad
  have hnodup : (P.toList.map u ++ P.toList.map v).Nodup :=
    List.nodup_append.mpr ⟨P.nodup_toList.map hu, P.nodup_toList.map hv,
      fun a ha c hc heq => hdis ha (heq.symm ▸ hc)⟩
  have hperm : (P.toList.map u ++ P.toList.map v).Perm
      (P.toList.flatMap fun i => [u i, v i]) := by
    simpa only [← List.map_eq_flatMap, List.cons_append, List.nil_append] using
      List.flatMap_append_perm P.toList (fun i => [u i]) (fun i => [v i])
  have hn := exterior_basis_word_ne_zero b
    (P.toList.flatMap fun i => [u i, v i]) (hperm.nodup_iff.mp hnodup)
  have heq :
      (((P.toList.flatMap fun i => [u i, v i]).map b).map
        (ExteriorAlgebra.ι K)).prod =
      pairedMonomial (K := K) (fun i => b (u i)) (fun i => b (v i)) P := by
    simpa only [List.map_flatMap, List.map_cons, List.map_nil] using
      pair_word_product (K := K) (fun i => b (u i)) (fun i => b (v i)) P
  rwa [heq] at hn

end PairedBasis

section Sparse

variable {k r : ℕ}

/-- Retained left endpoint of the `j`th separated pair. -/
def sparsePathLeft (hr : 2*r ≤ k) (j : Fin r) : Fin (2*k+1) :=
  ⟨4*j.val, by have := j.isLt; omega⟩

def sparsePathRight (hr : 2*r ≤ k) (j : Fin r) : Fin (2*k+1) :=
  ⟨4*j.val+1, by have := j.isLt; omega⟩

theorem sparsePath_injective (hr : 2*r ≤ k) :
    Function.Injective
      (Sum.elim (sparsePathLeft hr) (sparsePathRight hr) : Fin r ⊕ Fin r → Fin (2*k+1)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 4*a.val = 4*b.val at hv
      omega
    | inr b =>
      have hv := congrArg Fin.val h
      change 4*a.val = 4*b.val+1 at hv
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hv := congrArg Fin.val h
      change 4*a.val+1 = 4*b.val at hv
      omega
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 4*a.val+1 = 4*b.val+1 at hv
      omega

def sparsePathKeep (r : ℕ) (i : Fin (2*k+1)) : Prop :=
  i.val / 4 < r ∧ i.val % 4 < 2

instance sparsePathKeep_decidable (r : ℕ) (i : Fin (2*k+1)) :
    Decidable (sparsePathKeep r i) := inferInstanceAs (Decidable (_ ∧ _))

/-- A literal coordinate projection, extended to the exterior algebra by
its universal property. -/
def sparsePathProjection (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) : M →ₗ[K] M :=
  b.constr K (fun i => if sparsePathKeep r i then b i else 0)

def sparsePathExteriorProjection (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) :
    ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M :=
  ExteriorAlgebra.map (sparsePathProjection b r)

@[simp] theorem sparsePathProjection_basis (b : Module.Basis (Fin (2*k+1)) K M)
    (r : ℕ) (i : Fin (2*k+1)) :
    sparsePathProjection b r (b i) = if sparsePathKeep r i then b i else 0 :=
  b.constr_basis K _ i

@[simp] theorem sparsePathExteriorProjection_basis (b : Module.Basis (Fin (2*k+1)) K M)
    (r : ℕ) (i : Fin (2*k+1)) :
    sparsePathExteriorProjection b r (ExteriorAlgebra.ι K (b i)) =
      if sparsePathKeep r i then ExteriorAlgebra.ι K (b i) else 0 := by
  simp only [sparsePathExteriorProjection, ExteriorAlgebra.map_apply_ι,
    sparsePathProjection_basis]
  split_ifs <;> simp only [map_zero]

/-- No edge of the second matching has both endpoints retained. -/
theorem sparsePathProjection_second (b : Module.Basis (Fin (2*k+1)) K M) (r : ℕ) :
    sparsePathExteriorProjection b r
      (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M) = 0 := by
  rw [oddPathSecondQuadratic, matchingQuadratic_coe, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, sparsePathExteriorProjection_basis, sparsePathExteriorProjection_basis]
  by_cases hi : sparsePathKeep r (oddPathMiddle i)
  · have hn : ¬sparsePathKeep r (oddPathSecondRight i) := by
      dsimp [sparsePathKeep, oddPathMiddle, oddPathSecondRight] at hi ⊢
      omega
    rw [if_neg hn, mul_zero]
  · rw [if_neg hi, zero_mul]

/-- The surviving terms of the first matching are precisely `i=2j` for
`j<r`, each with coefficient one. -/
theorem sparsePathProjection_first (b : Module.Basis (Fin (2*k+1)) K M)
    (hr : 2*r ≤ k) :
    sparsePathExteriorProjection b r
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) =
        ∑ j : Fin r, ExteriorAlgebra.ι K (b (sparsePathLeft hr j)) *
          ExteriorAlgebra.ι K (b (sparsePathRight hr j)) := by
  classical
  let P : Fin k → Prop := fun i => i.val % 2 = 0 ∧ i.val / 2 < r
  rw [oddPathFirstQuadratic, matchingQuadratic_coe, map_sum]
  have hterm (i : Fin k) :
      sparsePathExteriorProjection b r
        (ExteriorAlgebra.ι K (b (oddPathFirstLeft i)) *
          ExteriorAlgebra.ι K (b (oddPathMiddle i))) =
      if P i then ExteriorAlgebra.ι K (b (oddPathFirstLeft i)) *
          ExteriorAlgebra.ι K (b (oddPathMiddle i)) else 0 := by
    rw [map_mul, sparsePathExteriorProjection_basis, sparsePathExteriorProjection_basis]
    by_cases hi : P i
    · have hl : sparsePathKeep r (oddPathFirstLeft i) := by
        dsimp [sparsePathKeep, oddPathFirstLeft, P] at hi ⊢; omega
      have hm : sparsePathKeep r (oddPathMiddle i) := by
        dsimp [sparsePathKeep, oddPathMiddle, P] at hi ⊢; omega
      rw [if_pos hi, if_pos hl, if_pos hm]
    · have hl : ¬sparsePathKeep r (oddPathFirstLeft i) := by
        dsimp [sparsePathKeep, oddPathFirstLeft, P] at hi ⊢; omega
      rw [if_neg hi, if_neg hl, zero_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val / 2,
    (Finset.mem_filter.mp hi).2.2⟩ : Fin r))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi i' hi' heq
    apply Fin.ext
    have h₁ := (Finset.mem_filter.mp hi).2.1
    have h₂ := (Finset.mem_filter.mp hi').2.1
    have h₃ := congrArg Fin.val heq
    dsimp at h₃
    omega
  · intro j hj
    let i : Fin k := ⟨2*j.val, by have := j.isLt; omega⟩
    have hi : i ∈ Finset.univ.filter P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [P, i]
      have := j.isLt
      omega
    refine ⟨i, hi, ?_⟩
    apply Fin.ext
    dsimp [i]
    omega
  · intro i hi
    have heven := (Finset.mem_filter.mp hi).2.1
    congr 3 <;> apply Fin.ext <;>
      dsimp [oddPathFirstLeft, oddPathMiddle, sparsePathLeft, sparsePathRight] <;> omega

/-- The first Frobenius cycle is detected by a projection killing `G`. -/
theorem sparsePathProjection_first_power_ne_zero
    (b : Module.Basis (Fin (2*k+1)) K M) (hr : 2*r ≤ k)
    (hfac : (r.factorial : K) ≠ 0) :
    sparsePathExteriorProjection b r
      ((oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) ^ r) ≠ 0 := by
  rw [map_pow, sparsePathProjection_first b hr]
  have he := exterior_matching_pow_card (K := K)
    (fun j : Fin r => b (sparsePathLeft hr j))
    (fun j : Fin r => b (sparsePathRight hr j))
  simp only [Fintype.card_fin] at he
  rw [he]
  exact smul_ne_zero hfac
    (paired_basis_monomial_ne_zero b (sparsePathLeft hr) (sparsePathRight hr)
      (sparsePath_injective hr) Finset.univ)


/-- Reflection interchanges the second path quadratic with minus the
first, in every characteristic. -/
theorem oddPath_second_reflection (z : Fin (2*k+1) → M) :
    oddPathSecondQuadratic (K := K) (fun i => z i.rev) =
      -oddPathFirstQuadratic (K := K) z := by
  have h := oddPath_reflection (K := K) (fun i => z i.rev)
  have h' : oddPathFirstQuadratic (K := K) z =
      -oddPathSecondQuadratic (K := K) (fun i => z i.rev) := by
    simpa only [Fin.rev_rev] using h
  have hn := congrArg Neg.neg h'
  simp only [neg_neg] at hn
  exact hn.symm

/-- Two actual algebra maps detect the Frobenius powers separately. No
quotient independence or dimension conclusion is assumed. -/
theorem oddPath_frobenius_projection_certificates
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 2*(p-1) ≤ k) :
    ∃ π₁ π₂ : ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M,
      π₁ (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M) = 0 ∧
      π₁ ((oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^(p-1)) ≠ 0 ∧
      π₂ (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M) = 0 ∧
      π₂ ((oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^(p-1)) ≠ 0 := by
  let b' := b.reindex Fin.revPerm
  have hf' : oddPathFirstQuadratic (K := K) b' = -oddPathSecondQuadratic (K := K) b := by
    simpa only [b', Module.Basis.coe_reindex, Fin.revPerm_symm, Fin.revPerm_apply,
      Function.comp_def] using
      oddPath_reflection (K := K) b
  have hg' : oddPathSecondQuadratic (K := K) b' = -oddPathFirstQuadratic (K := K) b := by
    simpa only [b', Module.Basis.coe_reindex, Fin.revPerm_symm, Fin.revPerm_apply,
      Function.comp_def] using
      oddPath_second_reflection (K := K) b
  have hp := (Fact.out : p.Prime).two_le
  have hfac : ((p-1).factorial : K) ≠ 0 :=
    factorial_cast_ne_zero_of_lt_char p (p-1) (by omega)
  refine ⟨sparsePathExteriorProjection b (p-1),
    sparsePathExteriorProjection b' (p-1),
    sparsePathProjection_second b (p-1),
    sparsePathProjection_first_power_ne_zero b hk hfac, ?_, ?_⟩
  · have h := sparsePathProjection_second b' (p-1)
    rw [hg', Submodule.coe_neg, map_neg] at h
    exact neg_eq_zero.mp h
  · have h := sparsePathProjection_first_power_ne_zero b' hk hfac
    rw [hf', Submodule.coe_neg] at h
    intro hz
    have hz' : (sparsePathExteriorProjection b' (p-1)
        (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M))^(p-1) = 0 := by
      simpa only [map_pow] using hz
    apply h
    rw [map_pow, map_neg, neg_pow, hz', mul_zero]

end Sparse

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0566

section TAF_LiteralSource_0567
/- Original module: PaperVerification.AlternatingFormsFrobeniusDimension -/


/-!
# The full integer exterior dimension bound from Frobenius cycles

All terms are actual homogeneous exterior powers. The two sparse algebra
maps prove independence of the extra cycles modulo the Koszul image; the
only injectivity input is subsequently supplied by the matching theorem.
The quotient is the homogeneous component of the actual generated ideal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The rank-nullity mechanism for two nilpotent quadratic forms, with
explicit algebra maps detecting their extra syzygies separately. -/
theorem exterior_quotient_excess_of_frobenius_certificates
    (f g : ⋀[K]^2 M) (r : ℕ) (hr : 1 ≤ r)
    (hf : (f : ExteriorAlgebra K M)^(r+1) = 0)
    (hg : (g : ExteriorAlgebra K M)^(r+1) = 0)
    (hinj : ∀ h : ⋀[K]^(2*r-2) M,
      (f : ExteriorAlgebra K M)*h = 0 → h = 0)
    (π₁ π₂ : ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M)
    (hπ₁ : π₁ (g : ExteriorAlgebra K M) = 0)
    (hπ₁pow : π₁ ((f : ExteriorAlgebra K M)^r) ≠ 0)
    (hπ₂ : π₂ (f : ExteriorAlgebra K M) = 0)
    (hπ₂pow : π₂ ((g : ExteriorAlgebra K M)^r) ≠ 0) :
    ((Module.finrank K M).choose (2*r+2) : ℤ) -
      2*((Module.finrank K M).choose (2*r) : ℤ) +
      ((Module.finrank K M).choose (2*r-2) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree f g (2*r+2)) : ℤ) := by
  let q := 2*r-2
  have hq₂ : q+2 = 2*r := by dsimp [q]; omega
  have hq₄ : q+4 = 2*r+2 := by dsimp [q]; omega
  let fp : ⋀[K]^(q+2) M := ⟨(f : ExteriorAlgebra K M)^r, by
    rw [hq₂]
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (A := fun d : ℕ => ⋀[K]^d M) r f.property⟩
  let gp : ⋀[K]^(q+2) M := ⟨(g : ExteriorAlgebra K M)^r, by
    rw [hq₂]
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (A := fun d : ℕ => ⋀[K]^d M) r g.property⟩
  let z₁ : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M := (fp, 0)
  let z₂ : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M := (0, gp)
  have hz₁ : exteriorRelationMapDegree f g q z₁ = 0 := by
    apply Subtype.ext
    change (f : ExteriorAlgebra K M)*(f : ExteriorAlgebra K M)^r +
      (g : ExteriorAlgebra K M)*0 = 0
    rw [mul_zero, add_zero, ← pow_succ', hf]
  have hz₂ : exteriorRelationMapDegree f g q z₂ = 0 := by
    apply Subtype.ext
    change (f : ExteriorAlgebra K M)*0 +
      (g : ExteriorAlgebra K M)*(g : ExteriorAlgebra K M)^r = 0
    rw [mul_zero, zero_add, ← pow_succ', hg]
  have hrel : ∀ (h : ⋀[K]^q M) (α β : K),
      exteriorKoszulMapDegree f g q h + α • z₁ + β • z₂ = 0 →
        α = 0 ∧ β = 0 := by
    intro h α β heq
    have hleft := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
      (x.1 : ExteriorAlgebra K M)) heq
    have hright := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
      (x.2 : ExteriorAlgebra K M)) heq
    change (g : ExteriorAlgebra K M)*h + α • (f : ExteriorAlgebra K M)^r + β • 0 = 0 at hleft
    change -((f : ExteriorAlgebra K M)*h) + α • 0 + β • (g : ExteriorAlgebra K M)^r = 0 at hright
    have hα := congrArg π₁ hleft
    have hβ := congrArg π₂ hright
    simp only [map_add, map_mul, map_smul, map_zero, hπ₁, zero_mul,
      smul_zero, zero_add, add_zero] at hα
    simp only [map_add, map_neg, map_mul, map_smul, map_zero, hπ₂, zero_mul,
      neg_zero, smul_zero, zero_add, add_zero] at hβ
    exact ⟨(smul_eq_zero.mp hα).resolve_right hπ₁pow,
      (smul_eq_zero.mp hβ).resolve_right hπ₂pow⟩
  have hd := cokernel_finrank_lower_of_two_extra_cycles
    (exteriorRelationMapDegree f g q) (exteriorKoszulMapDegree f g q)
    (exteriorRelationMapDegree_comp f g q)
    (exteriorKoszulMapDegree_injective f g q hinj) z₁ z₂ hz₁ hz₂ hrel
  rw [exteriorRelationMapDegree_range] at hd
  change (Module.finrank K (⋀[K]^(q+4) M) : ℤ) -
    (Module.finrank K (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) : ℤ) +
    (Module.finrank K (⋀[K]^q M) : ℤ) + 2 ≤
    (Module.finrank K (ExteriorQuotientDegree f g (q+4)) : ℤ) at hd
  rw [Module.finrank_prod, hq₂, hq₄] at hd
  simp only [exteriorPower.finrank_eq, Nat.cast_add, q] at hd
  linarith

section OddPath

variable {k : ℕ}

theorem oddPath_first_pow_char (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^p = 0 := by
  rw [oddPathFirstQuadratic, matchingQuadratic_coe]
  exact exterior_matching_pow_char
    (fun i => b (oddPathFirstLeft i)) (fun i => b (oddPathMiddle i)) p

theorem oddPath_second_pow_char (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^p = 0 := by
  rw [oddPathSecondQuadratic, matchingQuadratic_coe]
  exact exterior_matching_pow_char
    (fun i => b (oddPathMiddle i)) (fun i => b (oddPathSecondRight i)) p

/-- The complete numerical lower bound once genuine matching injectivity
is supplied. The next theorem discharges this specific remaining input. -/
theorem oddPath_quotient_excess_of_injective
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k)
    (hinj : ∀ h : ⋀[K]^(2*p-4) M,
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)*h = 0 → h = 0) :
    ((2*k+1).choose (2*p) : ℤ) - 2*((2*k+1).choose (2*p-2) : ℤ) +
      ((2*k+1).choose (2*p-4) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) : ℤ) := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨π₁, π₂, hπ₁, hπ₁pow, hπ₂, hπ₂pow⟩ :=
    oddPath_frobenius_projection_certificates b p (by omega : 2*(p-1) ≤ k)
  have hf : (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^((p-1)+1) = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using oddPath_first_pow_char b p
  have hg : (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^((p-1)+1) = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using oddPath_second_pow_char b p
  have h₀ : 2*(p-1)-2 = 2*p-4 := by omega
  have h₁ : 2*(p-1) = 2*p-2 := by omega
  have h₂ : 2*(p-1)+2 = 2*p := by omega
  have hrank : Module.finrank K M = 2*k+1 := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  have h := exterior_quotient_excess_of_frobenius_certificates
    (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (p-1) (by omega)
    hf hg (by rw [h₀]; exact hinj) π₁ π₂ hπ₁ hπ₁pow hπ₂ hπ₂pow
  rw [h₂, h₀, h₁, hrank] at h
  exact h

end OddPath

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0567

section TAF_LiteralSource_0568
/- Original module: PaperVerification.AlternatingFormsMatchingInjectivity -/


/-!
# Low-degree matching injectivity in prime characteristic

This file supplies the injectivity input of the characteristic-p dimension
argument. Every complementary exterior basis word is divided by the actual
matching form, using the factorial bound from its empty matching pairs.
The established perfect exterior pairing then gives injectivity. The proof
has no ambient-characteristic bound and no assumed rank or Hilbert series.
This source remains a candidate until its complete compilation and audit.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The two parts of a finite sum selection are an actual list permutation. -/
theorem selection_sum_list_permutation {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset (α ⊕ β)) :
    T.toList.Perm (T.toLeft.toList.map Sum.inl ++ T.toRight.toList.map Sum.inr) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append, T.nodup_toList.count,
    (T.toLeft.nodup_toList.map Sum.inl_injective).count,
    (T.toRight.nodup_toList.map Sum.inr_injective).count]
  cases i <;> simp

/-- The paired and unpaired letters of an odd matching, with all letters retained. -/
theorem odd_selection_list_permutation {ι : Type*} [DecidableEq ι]
    (z : (ι ⊕ ι) ⊕ Fin 1 → M) (T : Finset ((ι ⊕ ι) ⊕ Fin 1)) :
    (T.toList.map z).Perm
      ((T.toLeft.toLeft.toList.map (fun i => z (.inl (.inl i))) ++
        T.toLeft.toRight.toList.map (fun i => z (.inl (.inr i)))) ++
        T.toRight.toList.map (fun i => z (.inr i))) := by
  have h₁ := (selection_sum_list_permutation T).map z
  have h₂ := (selection_sum_list_permutation T.toLeft).map (fun i => z (.inl i))
  simp only [List.map_append, List.map_map, Function.comp_def] at h₁ h₂
  exact h₁.trans (h₂.append_right _)

/-- Division of every complementary selection, for all prime characteristics
and arbitrarily many matching pairs. -/
theorem matching_complement_selection_division {k : ℕ}
    (z : (Fin k ⊕ Fin k) ⊕ Fin 1 → M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k)
    (T : Finset ((Fin k ⊕ Fin k) ⊕ Fin 1))
    (hT : T.card = 2*k+1-(2*p-4)) :
    ∃ a : ExteriorAlgebra K M,
      (matchingQuadratic (K := K) (fun i => z (.inl (.inl i)))
        (fun i => z (.inl (.inr i))) : ExteriorAlgebra K M) * a =
        ((T.toList.map z).map (ExteriorAlgebra.ι K)).prod := by
  let A := T.toLeft.toLeft
  let B := T.toLeft.toRight
  let C := T.toRight
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hc : C.card ≤ 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ C
  have hcard : A.card+B.card+C.card = T.card := by
    dsimp only [A, B, C]
    rw [Finset.card_toLeft_add_card_toRight, Finset.card_toLeft_add_card_toRight]
  have hhigh : Fintype.card (Fin k)+1 ≤ A.card+B.card := by
    simp only [Fintype.card_fin]
    omega
  have hU : (A ∪ B).card+((A ∪ B)ᶜ).card = k := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl (A ∪ B)
  have hA : A.card ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_left
  have hB : B.card ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_right
  have hempty : ((A ∪ B)ᶜ).card+1 < p := by omega
  obtain ⟨η, hη⟩ := matching_high_selection_division_charP (K := K)
    (fun i => z (.inl (.inl i))) (fun i => z (.inl (.inr i))) A B p hhigh hempty
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K)
    (odd_selection_list_permutation z T)
  let tail : ExteriorAlgebra K M :=
    ((C.toList.map (fun i => z (.inr i))).map (ExteriorAlgebra.ι K)).prod
  refine ⟨ε • ((η : ExteriorAlgebra K M)*tail), ?_⟩
  rw [mul_smul_comm, ← mul_assoc, matchingQuadratic_coe, hη]
  simpa only [A, B, C, tail, List.map_append, List.prod_append] using heq.symm

/-- The actual complementary-degree relation space is the whole exterior
power; this assertion is proved on the genuine exterior basis. -/
theorem matching_complement_relations_eq_top {k : ℕ}
    (b : Module.Basis ((Fin k ⊕ Fin k) ⊕ Fin 1) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    exteriorDegreeRelations
      (matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
        (fun i => b (.inl (.inr i)))) 0 (2*k+1-(2*p-4)) = ⊤ := by
  classical
  letI : LinearOrder ((Fin k ⊕ Fin k) ⊕ Fin 1) := linearOrderOfSTO WellOrderingRel
  let q := 2*k+1-(2*p-4)
  let F := matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
    (fun i => b (.inl (.inr i)))
  apply eq_top_iff.mpr
  rw [← (b.exteriorPower q).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨T, rfl⟩
  change ((b.exteriorPower q T) : ExteriorAlgebra K M) ∈ exteriorRelationIdeal F 0
  let e := Set.powersetCard.ofFinEmbEquiv.symm T
  have hperm : (List.ofFn (fun i => e i)).Perm T.val.toList := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr e.injective)
      T.val.nodup_toList).mpr
    intro i
    rw [List.mem_ofFn', Finset.mem_toList]
    exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T i
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K) (hperm.map b)
  obtain ⟨a, ha⟩ := matching_complement_selection_division (K := K) b p hk T.val T.property
  apply Ideal.mem_span_pair.mpr
  refine ⟨ε • a, 0, ?_⟩
  rw [zero_mul, add_zero, ← (twoForm_commute F (ε • a)).eq, mul_smul_comm, ha]
  rw [exteriorPower.basis_apply]
  simpa only [exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn, List.map_map, Function.comp_def, e]
    using heq.symm

/-- Complementary division and perfect exterior duality imply actual
left-multiplication injectivity on degree 2p-4. -/
theorem matching_low_degree_injective {k : ℕ}
    (b : Module.Basis ((Fin k ⊕ Fin k) ⊕ Fin 1) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ∀ h : ⋀[K]^(2*p-4) M,
      (matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
        (fun i => b (.inl (.inr i))) : ExteriorAlgebra K M)*h = 0 → h = 0 := by
  letI : FiniteDimensional K M := b.finiteDimensional_of_finite
  let F := matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
    (fun i => b (.inl (.inr i)))
  have hrank : Module.finrank K M = 2*k+1 := by
    simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using
      Module.finrank_eq_card_basis b
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsum : (2*p-4)+(2*k+1-(2*p-4)) = Module.finrank K M := by
    rw [hrank]
    omega
  have hrel : exteriorDegreeRelations F 0 (2*k+1-(2*p-4)) = ⊤ :=
    matching_complement_relations_eq_top b p hk
  haveI : Subsingleton (ExteriorQuotientDegree F 0 (2*k+1-(2*p-4))) := by
    change Subsingleton ((⋀[K]^(2*k+1-(2*p-4)) M) ⧸
      exteriorDegreeRelations F 0 (2*k+1-(2*p-4)))
    rw [hrel]
    infer_instance
  have hdim : Module.finrank K (exteriorCommonAnnihilator F 0 (2*p-4)) = 0 := by
    rw [exterior_annihilator_quotient_duality hsum F 0]
    exact Module.finrank_zero_of_subsingleton
  have hbot : exteriorCommonAnnihilator F 0 (2*p-4) = ⊥ :=
    Submodule.finrank_eq_zero.mp hdim
  intro h hh
  have hm : h ∈ exteriorCommonAnnihilator F 0 (2*p-4) :=
    (mem_exteriorCommonAnnihilator F 0 h).mpr ⟨hh, by simp⟩
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

/-- The explicit even/odd bijection, isolated from the characteristic-zero
straightening development. -/
def matchingEvenOddEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2*k) where
  toFun
    | .inl i => ⟨2*i.val, by have := i.isLt; omega⟩
    | .inr i => ⟨2*i.val+1, by have := i.isLt; omega⟩
  invFun j := if j.val%2=0 then .inl ⟨j.val/2, by have := j.isLt; omega⟩
    else .inr ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : (2*i.val)%2=0 := by omega
        simp only [he, if_pos, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he, if_false, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv j := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

def oddMatchingIndexEquiv (k : ℕ) : ((Fin k ⊕ Fin k) ⊕ Fin 1) ≃ Fin (2*k+1) :=
  (Equiv.sumCongr (matchingEvenOddEquiv k) (Equiv.refl (Fin 1))).trans finSumFinEquiv

@[simp] theorem oddMatchingIndexEquiv_first {k : ℕ} (i : Fin k) :
    oddMatchingIndexEquiv k (.inl (.inl i)) = oddPathFirstLeft i := by
  apply Fin.ext
  rfl

@[simp] theorem oddMatchingIndexEquiv_middle {k : ℕ} (i : Fin k) :
    oddMatchingIndexEquiv k (.inl (.inr i)) = oddPathMiddle i := by
  apply Fin.ext
  rfl

/-- The injectivity statement for the literal first form of the odd canonical
pencil, with every prime and every ambient dimension in the paper's range. -/
theorem oddPath_first_low_degree_injective {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ∀ h : ⋀[K]^(2*p-4) M,
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)*h = 0 → h = 0 := by
  let b' := b.reindex (oddMatchingIndexEquiv k).symm
  have hform : matchingQuadratic (K := K) (fun i => b' (.inl (.inl i)))
      (fun i => b' (.inl (.inr i))) = oddPathFirstQuadratic (K := K) b := by
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm,
      oddMatchingIndexEquiv_first, oddMatchingIndexEquiv_middle, oddPathFirstQuadratic]
  simpa only [hform] using matching_low_degree_injective b' p hk

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0568

section TAF_LiteralSource_0569
/- Original module: PaperVerification.AlternatingFormsCharacteristicPrincipal -/


/-!
# The complete characteristic-p excess theorem

This file joins the actual exterior-algebra and actual bounded-walk chains.
It retains every prime and every odd dimension in the printed range. The
all-odd-dimension statement uses the ordinary vector space `Fin n → K` and
explicitly transported integer indices; the index transport changes no
coordinate value. No rank, nilpotence, projection, or walk formula is an
additional hypothesis of the principal statement.

All new declarations remain candidates until the recorded fresh compiler
run, actual proof-body audit, and independent statement review succeed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The full integer lower bound for the canonical odd pencil, now with
matching injectivity proved rather than assumed. -/
theorem oddPath_quotient_excess_charP [FiniteDimensional K M] {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ((2*k+1).choose (2*p) : ℤ) - 2*((2*k+1).choose (2*p-2) : ℤ) +
      ((2*k+1).choose (2*p-4) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) : ℤ) :=
  oddPath_quotient_excess_of_injective b p hk
    (oddPath_first_low_degree_injective b p hk)

/-- The exact walk-count version for the parameterization `n=2k+1`. -/
theorem oddPath_quotient_excess_walks [FiniteDimensional K M] {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    StripWalks.paperWalkCount (2*k+1) (2*p) + 2 ≤
      Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) := by
  have hp := (Fact.out : p.Prime).two_le
  have hdim := oddPath_quotient_excess_charP b p hk
  have hwalk := StripWalks.high_strip_count (2*k+1) (2*p)
    (by omega : 4 ≤ 2*p) (by omega : 3*(2*p)-3 ≤ 2*k+1)
  rw [← hwalk] at hdim
  exact_mod_cast hdim

/-- The half-dimension parameterization covers every odd natural dimension. -/
theorem odd_half_dimension {n : ℕ} (hn : Odd n) : 2*(n/2)+1 = n := by
  obtain ⟨k, hk⟩ := hn.exists_bit1
  omega

/-- The coordinate index transport has exactly the original natural value. -/
def canonicalOddIndex {n : ℕ} (hn : Odd n) : Fin (2*(n/2)+1) → Fin n :=
  Fin.cast (odd_half_dimension hn)

@[simp] theorem canonicalOddIndex_val {n : ℕ} (hn : Odd n)
    (i : Fin (2*(n/2)+1)) : (canonicalOddIndex hn i).val = i.val := rfl

/-- The literal first canonical matching in an arbitrary odd dimension:
its summands use zero-based indices `2i,2i+1`. -/
def canonicalOddFirst {n : ℕ} (hn : Odd n) (b : Module.Basis (Fin n) K M) :
    ⋀[K]^2 M :=
  oddPathFirstQuadratic (fun i => b (canonicalOddIndex hn i))

/-- The literal second canonical matching, with zero-based indices
`2i+1,2i+2`, in the same actual vector space. -/
def canonicalOddSecond {n : ℕ} (hn : Odd n) (b : Module.Basis (Fin n) K M) :
    ⋀[K]^2 M :=
  oddPathSecondQuadratic (fun i => b (canonicalOddIndex hn i))

/-- Basis transport identifies the arbitrary-odd-dimensional canonical
forms with the `2k+1` forms without changing any vector or coefficient. -/
theorem canonicalOdd_reindex_forms {n : ℕ} (hn : Odd n)
    (b : Module.Basis (Fin n) K M) :
    let b' := b.reindex (finCongr (odd_half_dimension hn)).symm
    oddPathFirstQuadratic (K := K) b' = canonicalOddFirst hn b ∧
    oddPathSecondQuadratic (K := K) b' = canonicalOddSecond hn b := by
  dsimp only
  have hb : (b.reindex (finCongr (odd_half_dimension hn)).symm :
      Fin (2*(n/2)+1) → M) = fun i => b (canonicalOddIndex hn i) := by
    funext i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    rfl
  rw [hb]
  exact ⟨rfl, rfl⟩

/-- Theorem 7.2, in every odd dimension and every prime characteristic.
The quotient and the bounded-path walk count have their actual mathematical
definitions. Algebraic closure is unnecessary for this stronger statement. -/
theorem paper_theorem_7_2
    (p n : ℕ) [Fact p.Prime] [CharP K p] (hn : Odd n) (hlarge : 6*p-3 ≤ n) :
    StripWalks.paperWalkCount n (2*p) + 2 ≤
      Module.finrank K
        (ExteriorQuotientDegree
          (canonicalOddFirst hn (Pi.basisFun K (Fin n)))
          (canonicalOddSecond hn (Pi.basisFun K (Fin n))) (2*p)) := by
  let b := Pi.basisFun K (Fin n)
  let b' := b.reindex (finCongr (odd_half_dimension hn)).symm
  have hp := (Fact.out : p.Prime).two_le
  have hk : 3*p-2 ≤ n/2 := by
    have hhalf := odd_half_dimension hn
    omega
  have h := oddPath_quotient_excess_walks b' p hk
  obtain ⟨hf, hg⟩ := canonicalOdd_reindex_forms hn b
  change oddPathFirstQuadratic (K := K) b' = canonicalOddFirst hn b at hf
  change oddPathSecondQuadratic (K := K) b' = canonicalOddSecond hn b at hg
  rw [hf, hg, odd_half_dimension hn] at h
  exact h

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0569

section TAF_LiteralSource_0570
/- Original module: PaperVerification.GradedInjectiveQuotient -/


/-!
# Hilbert series after quotienting by an injective homogeneous operator

The quotient and every graded piece in this file are actual module quotients
and images of homogeneous submodules.  The proof is rank--nullity applied to
the restriction of the quotient map; homogeneity identifies its kernel.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.GradedInjectiveQuotient

variable {K S M : Type*} [Field K] [Ring S] [SMul K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

variable (G : TauCeti.InternalGrading K M ℕ)
  (U : Submodule S M)
  (hU : DirectSum.SetLike.IsHomogeneous G.piece U)

/-- The literal quotient grading, over the original coefficient field. -/
abbrev quotientGrading := G.quotient U hU

/-- The degreewise restriction of the actual quotient map. -/
def quotientPieceMap (d : ℕ) : G.piece d →ₗ[K] (quotientGrading G U hU).piece d :=
  ((U.mkQ.restrictScalars K).domRestrict (G.piece d)).codRestrict _
    (fun x => G.mk_mem_quotient_piece U hU x.property)

@[simp] theorem quotientPieceMap_apply (d : ℕ) (x : G.piece d) :
    (quotientPieceMap G U hU d x : M ⧸ U) = U.mkQ x := rfl

theorem quotientPieceMap_surjective (d : ℕ) :
    Function.Surjective (quotientPieceMap G U hU d) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := (G.mem_quotient_piece_iff U hU).mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

instance quotientPiece_finite (d : ℕ) [FiniteDimensional K (G.piece d)] :
    FiniteDimensional K ((quotientGrading G U hU).piece d) :=
  Module.Finite.of_surjective (quotientPieceMap G U hU d)
    (quotientPieceMap_surjective G U hU d)

variable (T : M →ₗ[K] M) (e : ℕ)
  (hT : TauCeti.LinearMap.IsHomogeneous T G.piece G.piece e)

include hT

/-- Multiplication or another homogeneous operator restricted to one piece. -/
def operatorPieceMap (d : ℕ) : G.piece d →ₗ[K] G.piece (d+e) :=
  (T.domRestrict (G.piece d)).codRestrict _ (fun x => hT.map_mem x.property)

@[simp] theorem operatorPieceMap_apply (d : ℕ) (x : G.piece d) :
    (operatorPieceMap G T e hT d x : M) = T x := rfl

theorem operatorPieceMap_injective (hinj : Function.Injective T) (d : ℕ) :
    Function.Injective (operatorPieceMap G T e hT d) := by
  intro x y h
  exact Subtype.ext (hinj (congrArg Subtype.val h))

theorem quotientPieceMap_ker
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) :
    LinearMap.ker (quotientPieceMap G U hU (d+e)) =
      LinearMap.range (operatorPieceMap G T e hT d) := by
  ext x
  constructor
  · intro hx
    have hxU : (x : M) ∈ U := by
      apply (Submodule.Quotient.mk_eq_zero U).mp
      exact congrArg Subtype.val hx
    have hxrange : (x : M) ∈ LinearMap.range T := hUT ▸ hxU
    obtain ⟨y, hy⟩ := hxrange
    refine ⟨DirectSum.decompose G.piece y d, Subtype.ext ?_⟩
    change T (DirectSum.decompose G.piece y d : M) = (x : M)
    rw [hT.map_decompose, hy]
    exact DirectSum.decompose_of_mem_same G.piece x.property
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change U.mkQ (T y) = 0
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    have hx : T y ∈ LinearMap.range T := ⟨y, rfl⟩
    change T y ∈ U.restrictScalars K
    rw [hUT]
    exact hx

theorem image_projection_below_degree (d : ℕ) (hde : d < e) (x : M) :
    (DirectSum.decompose G.piece (T x) d : M) = 0 := by
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous j x =>
      exact DirectSum.decompose_of_mem_ne G.piece (hT.map_mem x.property) (by omega)
  | add x y hx hy =>
      simpa only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
        Submodule.coe_add, hx, hy, add_zero]

theorem quotientPieceMap_ker_below
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) (hde : d < e) :
    LinearMap.ker (quotientPieceMap G U hU d) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxU : (x : M) ∈ U :=
      (Submodule.Quotient.mk_eq_zero U).mp (congrArg Subtype.val hx)
    have hxrange : (x : M) ∈ LinearMap.range T := hUT ▸ hxU
    obtain ⟨y, hy⟩ := hxrange
    have hzero := image_projection_below_degree G T e hT d hde y
    rw [hy, DirectSum.decompose_of_mem_same G.piece x.property] at hzero
    exact Subtype.ext hzero
  · exact bot_le

theorem finrank_quotient_piece_add
    (hinj : Function.Injective T)
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ)
    [FiniteDimensional K (G.piece (d+e))] :
    Module.finrank K ((quotientGrading G U hU).piece (d+e)) +
      Module.finrank K (G.piece d) = Module.finrank K (G.piece (d+e)) := by
  have h := (quotientPieceMap G U hU (d+e)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientPieceMap_surjective G U hU (d+e)),
    finrank_top, quotientPieceMap_ker G U hU T e hT hUT d,
    LinearMap.finrank_range_of_inj (operatorPieceMap_injective G T e hT hinj d)] at h
  exact h

theorem finrank_quotient_piece_below
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) (hde : d < e)
    [FiniteDimensional K (G.piece d)] :
    Module.finrank K ((quotientGrading G U hU).piece d) =
      Module.finrank K (G.piece d) := by
  have h := (quotientPieceMap G U hU d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientPieceMap_surjective G U hU d),
    finrank_top, quotientPieceMap_ker_below G U hU T e hT hUT d hde,
    finrank_bot, add_zero] at h
  exact h

/-- The Hilbert series of the literal internally graded module. -/
def hilbertSeries (G : TauCeti.InternalGrading K M ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (G.piece d) : ℤ))

theorem hilbertSeries_quotient
    (hinj : Function.Injective T)
    (hUT : U.restrictScalars K = LinearMap.range T)
    (hfinite : ∀ d, FiniteDimensional K (G.piece d)) :
    hilbertSeries (quotientGrading G U hU) =
      hilbertSeries G * (1-PowerSeries.X^e) := by
  apply PowerSeries.ext
  intro d
  letI := hfinite d
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  split_ifs with hed
  · letI := hfinite (d-e+e)
    have h := finrank_quotient_piece_add G U hU T e hT hinj hUT (d-e)
    rw [Nat.sub_add_cancel hed] at h
    have hz : (Module.finrank K ((quotientGrading G U hU).piece d) : ℤ) +
        (Module.finrank K (G.piece (d-e)) : ℤ) =
        (Module.finrank K (G.piece d) : ℤ) := by exact_mod_cast h
    omega
  · simpa only [sub_zero] using congrArg (fun n : ℕ => (n : ℤ))
      (finrank_quotient_piece_below G U hU T e hT hUT d (by omega))

end PaperVerification.GradedInjectiveQuotient
end
end
end TAF_LiteralSource_0570

section TAF_LiteralSource_0571
/- Original module: PaperVerification.RegularHomogeneousHilbertSeries -/


/-!
# Hilbert series of an actual quotient by a homogeneous regular sequence

The result is proved by successively quotienting the module by each scalar.
At every step the grading is the image of the original homogeneous pieces.
The final linear equivalence is Mathlib's quotient-by-a-list equivalence, so
this construction concerns the literal quotient by the generated ideal.
-/

@[expose] public section
noncomputable section
open scoped Pointwise PowerSeries

namespace PaperVerification.RegularHomogeneousHilbertSeries

open GradedInjectiveQuotient

universe u v w

variable {K : Type u} {R : Type v} {M : Type w}
  [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

/-- Scalar multiplication, viewed over the coefficient field. -/
def scalarMap (r : R) : M →ₗ[K] M :=
  (LinearMap.lsmul R M r).restrictScalars K

@[simp] theorem scalarMap_apply (r : R) (x : M) : scalarMap (K:=K) r x = r • x := rfl

/-- The image of scalar multiplication is the actual scalar-generated submodule. -/
theorem smulTop_restrictScalars_eq_range (r : R) :
    (r • (⊤ : Submodule R M)).restrictScalars K =
      LinearMap.range (scalarMap (K:=K) (M:=M) r) := by
  ext x
  change x ∈ r • (⊤ : Submodule R M) ↔ _
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    LinearMap.mem_range, scalarMap_apply]

variable (G : TauCeti.InternalGrading K M ℕ)

/-- A scalar image is homogeneous when scalar multiplication has one degree. -/
theorem smulTop_homogeneous (r : R) (e : ℕ)
    (hr : TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r) G.piece G.piece e) :
    DirectSum.SetLike.IsHomogeneous G.piece (r • (⊤ : Submodule R M)) := by
  intro d x hx
  have hx' : x ∈ LinearMap.range (scalarMap (K:=K) r) := by
    rw [← smulTop_restrictScalars_eq_range]
    exact hx
  have h := hr.isHomogeneous_range d hx'
  rw [← smulTop_restrictScalars_eq_range] at h
  exact h

/-- A homogeneous scalar acts with the same degree on every homogeneous quotient. -/
theorem scalarMap_quotient_homogeneous (U : Submodule R M)
    (hU : DirectSum.SetLike.IsHomogeneous G.piece U) (r : R) (e : ℕ)
    (hr : TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r) G.piece G.piece e) :
    TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r)
      (G.quotient U hU).piece (G.quotient U hU).piece e := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d x hx
  obtain ⟨y,hy,rfl⟩ := (G.mem_quotient_piece_iff U hU).mp hx
  exact G.mk_mem_quotient_piece U hU (hr.map_mem hy)

/-- Transport across an actual linear equivalence does not change the Hilbert series. -/
theorem hilbertSeries_map {N : Type*} [AddCommGroup N] [Module K N]
    (E : M ≃ₗ[K] N) : hilbertSeries (G.map E) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  have hd : Module.finrank K ((G.map E).piece d) = Module.finrank K (G.piece d) := by
    rw [TauCeti.InternalGrading.map_piece]
    exact E.finrank_map_eq (G.piece d)
  exact congrArg (fun n : ℕ => (n:ℤ)) hd

/-- The quotient by the zero submodule retains every graded-piece dimension. -/
theorem hilbertSeries_quotient_bot
    (hbot : DirectSum.SetLike.IsHomogeneous G.piece (⊥ : Submodule R M)) :
    hilbertSeries (G.quotient (⊥ : Submodule R M) hbot) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  have hi : Function.Injective (quotientPieceMap G (⊥ : Submodule R M) hbot d) := by
    intro x y h
    apply Subtype.ext
    have hxy := congrArg Subtype.val h
    change (Submodule.Quotient.mk (x:M) : M ⧸ (⊥ : Submodule R M)) =
      Submodule.Quotient.mk (y:M) at hxy
    simpa only [Submodule.Quotient.eq, Submodule.mem_bot, sub_eq_zero] using hxy
  have E := LinearEquiv.ofBijective (quotientPieceMap G (⊥ : Submodule R M) hbot d)
    ⟨hi, quotientPieceMap_surjective G (⊥ : Submodule R M) hbot d⟩
  simpa only [hilbertSeries, PowerSeries.coeff_mk] using
    congrArg (fun n : ℕ => (n:ℤ)) E.finrank_eq.symm

/-- The recursive quotient equivalence sends a class to its successive classes. -/
theorem quotientConsEquiv_mk (r : R) (rs : List R) (x : M) :
    Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.Quotient.mk x) := rfl

/-- The quotient has its original image grading and the regular-sequence product
formula. All homogeneous pieces of the initial module may be infinite in total;
only each individual piece is required to be finite-dimensional. -/
theorem exists_quotient_grading_hilbertSeries
    (rs : List (R × ℕ))
    (hhom : ∀ re ∈ rs,
      TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G.piece G.piece re.2)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M (rs.map Prod.fst))
    (hfinite : ∀ d, FiniteDimensional K (G.piece d)) :
    ∃ H : TauCeti.InternalGrading K
        (M ⧸ (Ideal.ofList (rs.map Prod.fst) • ⊤ : Submodule R M)) ℕ,
      (∀ d, H.piece d = (G.piece d).map
        ((Ideal.ofList (rs.map Prod.fst) • ⊤ : Submodule R M).mkQ.restrictScalars K)) ∧
      hilbertSeries H = hilbertSeries G * (rs.map (fun re =>
        (1-PowerSeries.X^re.2 : ℤ⟦X⟧))).prod := by
  induction rs generalizing M with
  | nil =>
      have hbot : DirectSum.SetLike.IsHomogeneous G.piece (⊥ : Submodule R M) := by
        intro d x hx
        have hx0 : x=0 := hx
        simp [hx0]
      let U₀ : Submodule R M := Ideal.ofList (([] : List (R × ℕ)).map Prod.fst) • ⊤
      have hzero : (⊥ : Submodule R M)=U₀ := by simp [U₀]
      let E := (Submodule.quotEquivOfEq (⊥ : Submodule R M) U₀ hzero).restrictScalars K
      refine ⟨(G.quotient ⊥ hbot).map E, ?_, ?_⟩
      · intro d
        rw [TauCeti.InternalGrading.map_piece, TauCeti.InternalGrading.quotient_piece,
          ← Submodule.map_comp]
        rfl
      · rw [hilbertSeries_map, hilbertSeries_quotient_bot]
        simp
  | cons re rs ih =>
      rcases re with ⟨r,e⟩
      have hr := hhom (r,e) (List.mem_cons_self ..)
      have hrest := fun re hre => hhom re (List.mem_cons_of_mem _ hre)
      have hregular := (RingTheory.Sequence.isWeaklyRegular_cons_iff M r
        (rs.map Prod.fst)).mp (by simpa only [List.map_cons] using hreg)
      let U : Submodule R M := r • ⊤
      let hU := smulTop_homogeneous G r e hr
      let G₁ := G.quotient U hU
      have hf₁ : ∀ d, FiniteDimensional K (G₁.piece d) := by
        intro d
        letI := hfinite d
        exact quotientPiece_finite G U hU d
      have hh₁ : ∀ re ∈ rs,
          TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G₁.piece G₁.piece re.2 := by
        intro re hre
        exact scalarMap_quotient_homogeneous G U hU re.1 re.2 (hrest re hre)
      obtain ⟨H₁, hpieces₁, hseries₁⟩ := ih G₁ hh₁ hregular.2 hf₁
      let E := (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r
        (rs.map Prod.fst)).restrictScalars K
      let H := H₁.map E.symm
      refine ⟨H, ?_, ?_⟩
      · intro d
        dsimp only [H]
        rw [TauCeti.InternalGrading.map_piece, hpieces₁]
        dsimp only [G₁]
        rw [TauCeti.InternalGrading.quotient_piece]
        rw [← Submodule.map_comp, ← Submodule.map_comp]
        congr 1
      · have hs₁ : hilbertSeries G₁ = hilbertSeries G * (1-PowerSeries.X^e) :=
          hilbertSeries_quotient G U hU (scalarMap r) e hr hregular.1
            (smulTop_restrictScalars_eq_range r) hfinite
        rw [hilbertSeries_map, hseries₁, hs₁]
        simp only [List.map_cons, List.prod_cons]
        ring

end PaperVerification.RegularHomogeneousHilbertSeries
end
end
end TAF_LiteralSource_0571

section TAF_LiteralSource_0572
/- Original module: PaperVerification.FiniteGradedDimension -/


/-!
# Recovering the dimension of a finite graded module from its Hilbert series

A finite module has finitely many nonzero internal graded pieces. Its Hilbert
series is therefore the image of a polynomial whose value at one is the actual
module dimension. Cancelling the common factors `1-X` before evaluating at one
then proves the usual degree-product formula, without a formal evaluation of an
infinite power series or an analytic limiting argument.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.FiniteGradedDimension

open GradedInjectiveQuotient

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (G : TauCeti.InternalGrading K M ℕ) [FiniteDimensional K M]

/-- The finite support consists precisely of the nonzero graded submodules. -/
def support : Finset ℕ := G.finite_piece_ne_bot.toFinset

@[simp] theorem mem_support (d : ℕ) : d ∈ support G ↔ G.piece d ≠ ⊥ :=
  Set.Finite.mem_toFinset _

/-- The Hilbert polynomial here is the finite Hilbert series, not an eventual
Hilbert function polynomial. -/
def finiteHilbertPolynomial : Polynomial ℤ :=
  ∑ d ∈ support G, Polynomial.monomial d (Module.finrank K (G.piece d) : ℤ)

@[simp] theorem coeff_finiteHilbertPolynomial (d : ℕ) :
    (finiteHilbertPolynomial G).coeff d = (Module.finrank K (G.piece d) : ℤ) := by
  classical
  rw [finiteHilbertPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single d]
  · exact Polynomial.coeff_monomial_same _ _
  · intro b hb hbd
    exact Polynomial.coeff_monomial_of_ne _ hbd.symm
  · intro hd
    have hz : G.piece d=⊥ := by simpa only [mem_support, not_not] using hd
    rw [Polynomial.coeff_monomial_same, hz, finrank_bot, Nat.cast_zero]

theorem coe_finiteHilbertPolynomial :
    (finiteHilbertPolynomial G : ℤ⟦X⟧) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  simp only [Polynomial.coeff_coe, coeff_finiteHilbertPolynomial,
    hilbertSeries, PowerSeries.coeff_mk]

/-- Actual dimension is the sum of the dimensions of all nonzero pieces. -/
theorem finrank_eq_sum_support :
    Module.finrank K M = ∑ d ∈ support G, Module.finrank K (G.piece d) := by
  classical
  letI : Fintype {d : ℕ // G.piece d ≠ ⊥} := G.finite_piece_ne_bot.fintype
  have hI : DirectSum.IsInternal (fun d : {d : ℕ // G.piece d ≠ ⊥} => G.piece d) :=
    DirectSum.isInternal_ne_bot_iff.mpr G.isInternal
  let E := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun d : {d : ℕ // G.piece d ≠ ⊥} => G.piece d)) hI
  rw [← E.finrank_eq, Module.finrank_directSum]
  exact (Finset.sum_subtype (support G) (mem_support G)
    (fun d => Module.finrank K (G.piece d))).symm

@[simp] theorem eval_one_finiteHilbertPolynomial :
    (finiteHilbertPolynomial G).eval 1 = (Module.finrank K M : ℤ) := by
  classical
  simp only [finiteHilbertPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]
  exact_mod_cast (finrank_eq_sum_support G).symm

/-- A polynomial geometric sum, valid also at exponent zero. -/
def geometricPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range n, Polynomial.X^j

@[simp] theorem eval_one_geometricPolynomial (n : ℕ) :
    (geometricPolynomial n).eval 1 = (n : ℤ) := by
  simp [geometricPolynomial]

theorem geometricPolynomial_mul_one_sub_X (n : ℕ) :
    geometricPolynomial n * (1-Polynomial.X) = 1-Polynomial.X^n :=
  geom_sum_mul_neg _ n

/-- Cancel the equal-order vanishing factors before evaluating at one. -/
theorem eval_one_mul_product_degrees {ι : Type*} [Fintype ι]
    (P : Polynomial ℤ) (a b : ι → ℕ)
    (h : P * (∏ i, (1-Polynomial.X^(a i))) =
      ∏ i, (1-Polynomial.X^(b i))) :
    P.eval 1 * (∏ i, (a i : ℤ)) = ∏ i, (b i : ℤ) := by
  classical
  have hnonzero : ((1-Polynomial.X : Polynomial ℤ)^Fintype.card ι) ≠ 0 := by
    apply pow_ne_zero
    intro hz
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) hz
    simp at hc
  have hg (v : ι → ℕ) :
      (∏ i, geometricPolynomial (v i)) * (1-Polynomial.X)^Fintype.card ι =
        ∏ i, (1-Polynomial.X^(v i)) := by
    calc
      _ = ∏ i, (geometricPolynomial (v i)*(1-Polynomial.X)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = _ := by simp only [geometricPolynomial_mul_one_sub_X]
  have hc : P * (∏ i, geometricPolynomial (a i)) =
      ∏ i, geometricPolynomial (b i) := by
    apply mul_right_cancel₀ hnonzero
    rw [mul_assoc, hg, hg]
    exact h
  have he := congrArg (Polynomial.eval 1) hc
  simpa only [Polynomial.eval_mul, Polynomial.eval_prod,
    eval_one_geometricPolynomial] using he

/-- Finite-dimensional degree-product formula, deduced from the literal
power-series identity for this graded module. -/
theorem finrank_mul_product_degrees {ι : Type*} [Fintype ι]
    (a b : ι → ℕ)
    (h : hilbertSeries G * (∏ i, (1-PowerSeries.X^(a i))) =
      ∏ i, (1-PowerSeries.X^(b i))) :
    (Module.finrank K M : ℤ) * (∏ i, (a i : ℤ)) = ∏ i, (b i : ℤ) := by
  have hp : finiteHilbertPolynomial G * (∏ i, (1-Polynomial.X^(a i))) =
      ∏ i, (1-Polynomial.X^(b i)) := by
    apply Polynomial.coe_injective ℤ
    have hprod (f : ι → Polynomial ℤ) :
        ((∏ i, f i : Polynomial ℤ) : ℤ⟦X⟧) = ∏ i, (f i : ℤ⟦X⟧) :=
      map_prod Polynomial.coeToPowerSeries.ringHom f Finset.univ
    simpa only [Polynomial.coe_mul, hprod, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X,
      coe_finiteHilbertPolynomial] using h
  simpa only [eval_one_finiteHilbertPolynomial] using
    eval_one_mul_product_degrees (finiteHilbertPolynomial G) a b hp

/-- Consecutive relation degrees and variable weights `1,...,s` give the
binomial coefficient in Section 4. -/
theorem finrank_eq_choose_of_hilbert_identity (s w : ℕ)
    (h : hilbertSeries G *
        (∏ i : Fin s, (1-PowerSeries.X^(i.val+1))) =
      ∏ i : Fin s, (1-PowerSeries.X^(w+i.val))) :
    Module.finrank K M = (w+s-1).choose s := by
  have hd := finrank_mul_product_degrees G (fun i : Fin s => i.val+1)
    (fun i : Fin s => w+i.val) h
  have hdn : Module.finrank K M * s.factorial = w.ascFactorial s := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.ascFactorial_eq_prod_range]
    have hnat : Module.finrank K M * (∏ i : Fin s, (i.val+1)) =
        ∏ i : Fin s, (w+i.val) := by exact_mod_cast hd
    rw [← Finset.prod_range (fun i : ℕ => i+1),
      ← Finset.prod_range (fun i : ℕ => w+i)] at hnat
    exact hnat
  rw [Nat.ascFactorial_eq_factorial_mul_choose'] at hdn
  exact Nat.eq_of_mul_eq_mul_right s.factorial_pos (by simpa only [mul_comm] using hdn)

end PaperVerification.FiniteGradedDimension
end
end
end TAF_LiteralSource_0572

section TAF_LiteralSource_0573
/- Original module: PaperVerification.WeightedRegularQuotientDimension -/


/-!
# The dimension formula for a finite weighted complete intersection

This module combines the actual monomial basis of a polynomial ring, the
regular-sequence exactness argument, and polynomial evaluation at one.
Both the grading and the quotient are the ordinary Mathlib constructions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.WeightedRegularQuotientDimension

open MvPolynomial GradedInjectiveQuotient RegularHomogeneousHilbertSeries

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The usual weighted grading of the actual multivariable polynomial ring. -/
def polynomialGrading (weights : σ → ℕ) :
    TauCeti.InternalGrading K (MvPolynomial σ K) ℕ := by
  letI := MvPolynomial.weightedDecomposition K weights
  exact TauCeti.InternalGrading.ofDecomposition
    (MvPolynomial.weightedHomogeneousSubmodule K weights)

@[simp] theorem polynomialGrading_piece (weights : σ → ℕ) (d : ℕ) :
    (polynomialGrading (K:=K) weights).piece d =
      MvPolynomial.weightedHomogeneousSubmodule K weights d := by
  simp only [polynomialGrading, TauCeti.InternalGrading.ofDecomposition_piece]

/-- The exact dimension of each weighted monomial piece. -/
theorem finrank_polynomial_piece (weights : σ → ℕ) (d : ℕ) :
    Module.finrank K ((polynomialGrading (K:=K) weights).piece d) =
      Nat.card (WeightedMonomialSeries.Exponents weights d) := by
  rw [polynomialGrading_piece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {a : σ →₀ ℕ | Finsupp.weight weights a=d})

/-- Positive weights make every graded piece finite, without making the
whole polynomial ring finite-dimensional. -/
theorem polynomial_piece_finite (weights : σ → ℕ) (hw : ∀ i, weights i≠0) (d : ℕ) :
    FiniteDimensional K ((polynomialGrading (K:=K) weights).piece d) := by
  rw [polynomialGrading_piece]
  exact Module.Finite.iff_fg.mpr (MvPolynomial.weightedHomogeneousSubmodule_fg K weights hw d)

theorem polynomial_hilbertSeries_denominator (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) :
    hilbertSeries (polynomialGrading (K:=K) weights) *
      (∏ i, (1-PowerSeries.X^(weights i))) = 1 := by
  have hs : hilbertSeries (polynomialGrading (K:=K) weights) =
      PowerSeries.mk (fun d => (Nat.card (WeightedMonomialSeries.Exponents weights d) : ℤ)) := by
    apply PowerSeries.ext
    intro d
    simp only [hilbertSeries, PowerSeries.coeff_mk, finrank_polynomial_piece]
  rw [hs]
  exact WeightedMonomialSeries.series_mul_denominator_eq_one weights hw

/-- The literal quotient has the image grading and the complete-intersection
Hilbert-series identity. The number of equations is unrestricted, and the
quotient need not be finite-dimensional. -/
theorem exists_graded_quotient_hilbertSeries (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) (s : ℕ)
    (relations : Fin s → MvPolynomial σ K) (degrees : Fin s → ℕ)
    (hhom : ∀ i, (relations i).IsWeightedHomogeneous weights (degrees i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) (List.ofFn relations)) :
    ∃ H : TauCeti.InternalGrading K
        (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations)) ℕ,
      (∀ d, H.piece d = ((polynomialGrading (K:=K) weights).piece d).map
        ((Ideal.ofList (List.ofFn relations)).mkQ.restrictScalars K)) ∧
      hilbertSeries H * (∏ i, (1-PowerSeries.X^(weights i))) =
        ∏ i : Fin s, (1-PowerSeries.X^(degrees i)) := by
  classical
  let G := polynomialGrading (K:=K) weights
  let rs : List (MvPolynomial σ K × ℕ) := List.ofFn (fun i => (relations i,degrees i))
  have hrmap : rs.map Prod.fst=List.ofFn relations := by simp [rs,Function.comp_def]
  have hh : ∀ re ∈ rs,
      TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G.piece G.piece re.2 := by
    intro re hre
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hre
    apply TauCeti.LinearMap.isHomogeneous_def.mpr
    intro d x hx
    simp only [G, polynomialGrading_piece, scalarMap_apply, smul_eq_mul] at hx ⊢
    change (relations i*x).IsWeightedHomogeneous weights (d+degrees i)
    change x.IsWeightedHomogeneous weights d at hx
    simpa only [Nat.add_comm] using (hhom i).mul hx
  obtain ⟨H,hpieces,hseries⟩ := exists_quotient_grading_hilbertSeries G rs hh
    (by simpa only [hrmap] using hreg) (polynomial_piece_finite weights hw)
  have hI : (Ideal.ofList (rs.map Prod.fst) •
      (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K))) =
      Ideal.ofList (List.ofFn relations) := by
    rw [hrmap, Ideal.smul_eq_mul, Ideal.mul_top]
  let E := (Submodule.quotEquivOfEq _ _ hI).restrictScalars K
  let HQ := H.map E
  have hseriesQ : hilbertSeries HQ = hilbertSeries G *
      (∏ i : Fin s, (1-PowerSeries.X^(degrees i))) := by
    rw [hilbertSeries_map, hseries]
    simp [rs, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  refine ⟨HQ, ?_, ?_⟩
  · intro d
    rw [TauCeti.InternalGrading.map_piece, hpieces, ← Submodule.map_comp]
    rfl
  · rw [hseriesQ]
    calc
      _ = (hilbertSeries G * (∏ i, (1-PowerSeries.X^(weights i)))) *
          (∏ i : Fin s, (1-PowerSeries.X^(degrees i))) := by ring
      _ = _ := by rw [polynomial_hilbertSeries_denominator weights hw, one_mul]

/-- A finite quotient by exactly as many homogeneous regular equations as
variables has dimension determined by the product of their degrees. -/
theorem finrank_quotient_mul_weights (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) (s : ℕ)
    (relations : Fin s → MvPolynomial σ K) (degrees : Fin s → ℕ)
    (hhom : ∀ i, (relations i).IsWeightedHomogeneous weights (degrees i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) (List.ofFn relations))
    [FiniteDimensional K (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations))]
    (hs : s=Fintype.card σ) :
    (Module.finrank K (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations)) : ℤ) *
      (∏ i, (weights i : ℤ)) = ∏ i, (degrees i : ℤ) := by
  classical
  obtain ⟨HQ, _, hseriesQ⟩ := exists_graded_quotient_hilbertSeries
    weights hw s relations degrees hhom hreg
  let e : Fin s ≃ σ := Fintype.equivOfCardEq (by simpa using hs)
  have hp : hilbertSeries HQ * (∏ i : Fin s, (1-PowerSeries.X^(weights (e i)))) =
      ∏ i : Fin s, (1-PowerSeries.X^(degrees i)) := by
    rw [e.prod_comp (fun i => (1-PowerSeries.X^(weights i) : ℤ⟦X⟧))]
    exact hseriesQ
  have hd := FiniteGradedDimension.finrank_mul_product_degrees HQ
    (fun i => weights (e i)) degrees hp
  simpa only [e.prod_comp (fun i => (weights i : ℤ))] using hd

end PaperVerification.WeightedRegularQuotientDimension
end
end
end TAF_LiteralSource_0573

section TAF_LiteralSource_0574
/- Original module: PaperVerification.AlternatingFormsChernRecurrence -/


/-!
# The finite recurrence in Section 4.3

This file proves the algebraic consequence of the generating-function identity in
Section 4.3 of `Hilbert series of exterior algebras modulo two quadrics`.
The power-series identity and the inverse identity are explicit hypotheses here;
they are not asserted as axioms, and the identification with the paper's symmetric
polynomials is a separate task.  In particular these theorems do not assert the
cohomology presentation.

The result is useful over every characteristic-zero field and in every number of
variables: a consecutive block of `s` zero relations forces all later relations to
vanish, and a polynomial inverse then forces the Chern polynomial to equal one.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K : Type*} [Field K] [CharZero K]

/-- The even part of a coefficient sequence, with its original exponents. -/
noncomputable def evenRelationSeries (R : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if Even n then R n else 0

/-- The odd part of a coefficient sequence, with its original exponents. -/
noncomputable def oddRelationSeries (R : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if Even n then 0 else R n

/-- The Euler differential operator `t d/dt` on a power series. -/
noncomputable def eulerSeries (B : PowerSeries K) : PowerSeries K :=
  PowerSeries.X * PowerSeries.derivative B

@[simp] theorem coeff_evenRelationSeries (R : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (evenRelationSeries R) = if Even n then R n else 0 :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_oddRelationSeries (R : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (oddRelationSeries R) = if Even n then 0 else R n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_eulerSeries (B : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (eulerSeries B) = (n : K) * PowerSeries.coeff n B := by
  cases n with
  | zero => simp [eulerSeries]
  | succ n =>
    simp only [eulerSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

/-- The numerical coefficient `A_{m,i}` in equation (7). -/
noncomputable def chernRecurrenceWeight (m i : ℕ) : K :=
  if Even (m - i) then (m + i : ℕ) else 2

/-- Taking coefficients of the actual formal differential identity gives exactly
the recurrence printed as equation (7), including its parity-dependent factor. -/
theorem chern_recurrence_of_series_identity (C : Polynomial K) (R : ℕ → K)
    (hidentity :
      (C : PowerSeries K) * (eulerSeries (evenRelationSeries R) +
          2 * oddRelationSeries R) +
        2 * eulerSeries (C : PowerSeries K) * evenRelationSeries R = 0)
    (m : ℕ) :
    ∑ i ∈ range (m + 1), C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0 := by
  classical
  have h := congrArg (PowerSeries.coeff m) hidentity
  rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_zero] at h
  simp only [map_add,
    Polynomial.coeff_coe, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_ofNat_mul,
    coeff_eulerSeries, coeff_evenRelationSeries, coeff_oddRelationSeries] at h
  rw [← Finset.sum_add_distrib] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcast : ((m - i : ℕ) : K) + (i : K) = (m : K) := by
    exact_mod_cast Nat.sub_add_cancel hi'
  unfold chernRecurrenceWeight
  split_ifs with he
  · push_cast
    linear_combination -(C.coeff i * R (m - i)) * hcast
  · ring

/-- A length-`s` zero window propagates forever under the Section 4.3 recurrence.
The positivity of `w` is essential because the leading even coefficient at zero
is zero. -/
theorem chern_recurrence_vanishing_propagates {s w : ℕ} (hw : 0 < w)
    (C : Polynomial K) (hC0 : C.coeff 0 = 1) (hdegree : C.natDegree ≤ s)
    (R : ℕ → K)
    (hrecurrence : ∀ m : ℕ,
      ∑ i ∈ range (m + 1), C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0)
    (hwindow : ∀ m, w ≤ m → m < w + s → R m = 0) :
    ∀ m, w ≤ m → R m = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hwm
    by_cases hm : m < w + s
    · exact hwindow m hwm hm
    have hsum := hrecurrence m
    have hrest : ∀ i ∈ range (m + 1), i ≠ 0 →
        C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0 := by
      intro i hi hi0
      by_cases his : i ≤ s
      · have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have him : m - i < m := by omega
        have hwi : w ≤ m - i := by omega
        rw [ih (m - i) him hwi, mul_zero]
      · have hci : C.coeff i = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by omega))
        rw [hci, zero_mul, zero_mul]
    rw [Finset.sum_eq_single 0 (fun i hi hi0 => hrest i hi hi0)
      (by simp), hC0, one_mul, Nat.sub_zero] at hsum
    have hlead : chernRecurrenceWeight (K := K) m 0 ≠ 0 := by
      unfold chernRecurrenceWeight
      split_ifs
      · simpa using (Nat.cast_ne_zero.mpr (show m ≠ 0 by omega) : (m : K) ≠ 0)
      · norm_num
    exact (mul_eq_zero.mp hsum).resolve_left hlead

/-- A formal power series whose coefficients vanish from `w` onwards is the
actual image of its polynomial truncation. -/
theorem powerSeries_eq_trunc_of_tail_zero (B : PowerSeries K) (w : ℕ)
    (hzero : ∀ m, w ≤ m → PowerSeries.coeff m B = 0) :
    B = (PowerSeries.trunc w B : Polynomial K) := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hm : m < w
  · simp [hm]
  · simp [hm, hzero m (by omega)]

/-- The polynomial argument in Section 4.3: a finite relation window, together
with the two stated generating-function identities, forces `C(t)=1`.

There is no assumption that the relation sequence eventually vanishes; that fact
is proved from the recurrence.  `Q` will be `C(-t)` in the application. -/
theorem chern_polynomial_eq_one_of_window {s w : ℕ} (hw : 0 < w)
    (C Q : Polynomial K) (hC0 : C.coeff 0 = 1) (hdegree : C.natDegree ≤ s)
    (R : ℕ → K)
    (hidentity :
      (C : PowerSeries K) * (eulerSeries (evenRelationSeries R) +
          2 * oddRelationSeries R) +
        2 * eulerSeries (C : PowerSeries K) * evenRelationSeries R = 0)
    (hinverse : evenRelationSeries R * (C : PowerSeries K) * (Q : PowerSeries K) = 1)
    (hwindow : ∀ m, w ≤ m → m < w + s → R m = 0) : C = 1 := by
  classical
  have htail := chern_recurrence_vanishing_propagates hw C hC0 hdegree R
    (chern_recurrence_of_series_identity C R hidentity) hwindow
  have hBtail : ∀ m, w ≤ m → PowerSeries.coeff m (evenRelationSeries R) = 0 := by
    intro m hm
    simp [htail m hm]
  let B : Polynomial K := PowerSeries.trunc w (evenRelationSeries R)
  have hB : evenRelationSeries R = (B : PowerSeries K) :=
    powerSeries_eq_trunc_of_tail_zero _ _ hBtail
  have hproduct : B * C * Q = 1 := by
    apply Polynomial.coe_injective K
    simpa only [Polynomial.coe_mul, Polynomial.coe_one, ← hB] using hinverse
  have hunit : IsUnit C := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨B * Q, ?_⟩
    calc
      1 = B * C * Q := hproduct.symm
      _ = C * (B * Q) := by ring
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit),
    hC0, Polynomial.C_1]

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0574

section TAF_LiteralSource_0575
/- Original module: TauCeti.Algebra.BigOperators.Finset.Range -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Range reindexing for finite sums

Generic identities for sums indexed by `Finset.range` and `Finset.Ioo`. These are used by
coderivation/Taylor expansions, which reindex a cut-and-collapse double sum over a triangle to a
square and enlarge a vanishing-off-the-block range, and by divided-power exponential calculations,
which reindex a sum over antidiagonals to a rectangle. Reindexing a sum over a finite subset of a
linear order by the rank of each element turns the recurrences of Catalan-type enumerations, such
as those of noncrossing partitions, into sums over `Finset.range`.

## Main results

* `sum_Ioo_eq_sum_range`: a sum over `Ioo 0 n` equals the sum over `range n` when the summand at
  `0` vanishes.
* `Finset.sum_range_min_diag_flip`: reindex a three-variable truncated triangle as a slice of
  a cube.
* `Finset.sum_smul_mul_sum_smul_of_mul_eq_sum`: turn coefficient-one normal ordering into a
  factorization of finite generating sums.
* `sum_range_triangle`: summing over pairs `(c, p - c)` with `c ≤ p < K` equals the square
  `range K × range K` when the family vanishes off the triangle.
* `sum_range_add_antidiagonal_of_support`: a sum over antidiagonals below `k + l` equals
  the rectangle `range k × range l` when the summand vanishes outside that rectangle.
* `sum_sum_range_eq_of_eq_zero_right`: enlarging both ranges of a double sum that vanishes outside
  a rectangle.
* `sum_range_eq_of_eq_zero_off_pair` and `sum_range_eq_of_eq_zero_off_triple`: convenient
  specializations to supports of size two and three.
* `sum_range_add_add`: splitting a `range n` sum into a prefix, a block, and a suffix.
* `sum_sum_range_split_blocks`: splitting a double sum over the blocks of a word at one position
  into the blocks containing it, those before it, and those after it.
* `sum_range_min_add_two`: the two-step recurrence satisfied by the sums
  `∑_{i ≤ min j r} c^i a (j + r − 2i)`.
* `sum_range_min_zero`: the base case `j = 0` of that recurrence, which its `j + 1` cannot state.
* `two_mul_sum_range_pair`: twice the sum of the products over the pairs `i < j < k` is the
  square of the sum minus the sum of the squares.
* `sum_range_succ_smul_pow_sub`, `sum_range_succ_smul_pow_sub'`: the Horner recursion
  `V (m + 1) = c (m + 1) • 1 + a * V m = c (m + 1) • 1 + V m * a` for the convolutions
  `V m = ∑ k ∈ range (m + 1), c k • a ^ (m - k)` of scalars with the powers of `a`.
* `Finset.sum_range_succ_eq_sum_range_add`: regroup a sum whose successive terms split into
  adjacent contributions, retaining the final boundary term.
* `Finset.prod_range_two_mul_add_one`, `Finset.sum_range_two_mul_add_one`: split a product or sum
  over `range (2 * k + 1)` into its even and odd indices.
* `Finset.four_dvd_sum_range_two_mul_add_one`: a sum over `range (2 * k + 1)` of even terms,
  symmetric under `i ↦ 2 * k - i` and vanishing at the middle index `k`, is divisible by `4`.
* `Finset.prod_card_filter_lt_card_filter_gt`, `Finset.sum_card_filter_lt_card_filter_gt`: reindex
  a product or sum over a finite subset `s` of a linear order by the number of elements of `s`
  before each element.
* `Finset.prod_range_mul_eq_prod_prod`, `Finset.sum_range_mul_eq_sum_sum`: split a product or
  sum over `range (n * q)` into `q` consecutive blocks of `n` terms.
* `Finset.sum_range_two_mul_succ`: the sum `∑_{i=1}^{m} 2i` of the first `m` positive even
  numbers is `m (m + 1)`.
* `Finset.sum_range_add_two_mul`: the sum `∑_{j<J} (D + 2j + 1)` of an arithmetic progression
  with common difference `2` is `J (D + J)`.
* `Finset.sum_range_min_add_one_sub_two_mul`: the Clebsch–Gordan dimension count
  `∑_{k ≤ min m n} (m + n - 2k + 1) = (m + 1)(n + 1)`.
-/

public section

namespace Finset

/-- Regroup a sum whose initial term is `g 0` and whose successive terms are
`g (k + 1) + h k`, retaining the final contribution `g n`. -/
theorem sum_range_succ_eq_sum_range_add {M : Type*} [AddCommMonoid M]
    {f g h : ℕ → M} {n : ℕ} (hzero : f 0 = g 0)
    (hsucc : ∀ k < n, f (k + 1) = g (k + 1) + h k) :
    ∑ k ∈ range (n + 1), f k = (∑ k ∈ range n, (g k + h k)) + g n := by
  rw [sum_range_succ', hzero,
    sum_congr rfl (fun k hk ↦ hsucc k (mem_range.mp hk)), sum_add_distrib, sum_add_distrib]
  have hshift := (sum_range_succ' g n).symm.trans (sum_range_succ g n)
  simpa only [add_assoc, add_left_comm, add_comm] using congrArg (· + ∑ k ∈ range n, h k) hshift

/-- A product over `range (2 * k + 1)` splits into its factors at even and at odd indices. -/
@[to_additive sum_range_two_mul_add_one /-- A sum over `range (2 * k + 1)` splits into its terms at
even and at odd indices. -/]
theorem prod_range_two_mul_add_one {M : Type*} [CommMonoid M] (g : ℕ → M) (k : ℕ) :
    ∏ i ∈ range (2 * k + 1), g i =
      (∏ j ∈ range (k + 1), g (2 * j)) * ∏ j ∈ range k, g (2 * j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ (fun j => g (2 * j)) (k + 1), prod_range_succ (fun j => g (2 * j + 1)) k,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    ac_rfl


/-- A sum over `range (2 * k + 1)` of a family that is symmetric under `i ↦ 2 * k - i`, vanishes
at the middle index `k` and takes even values, is divisible by `4`: it is twice the sum over
`i < k`. -/
theorem four_dvd_sum_range_two_mul_add_one {R : Type*} [Semiring R] (k : ℕ) (h : ℕ → R)
    (hsym : ∀ i ≤ 2 * k, h (2 * k - i) = h i) (hk : h k = 0) (h2 : ∀ i, 2 ∣ h i) :
    4 ∣ ∑ i ∈ range (2 * k + 1), h i := by
  rw [show 2 * k + 1 = (k + 1) + k by ring, sum_range_add, sum_range_succ, hk, add_zero]
  have : ∑ x ∈ range k, h (k + 1 + x) = ∑ x ∈ range k, h x := by
    rw [← sum_range_reflect h k]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [mem_range] at hx
    rw [← hsym (k - 1 - x) (by omega)]
    congr 1
    omega
  rw [this, ← two_mul, ← two_add_two_eq_four, ← two_mul]
  exact mul_dvd_mul_left 2 (dvd_sum fun i _ ↦ h2 i)

/-- Reindexing a product over a finite subset `s` of a linear order by the number `i` of elements
of `s` before each element; there are then `#s - 1 - i` elements of `s` after it. -/
@[to_additive /-- Reindexing a sum over a finite subset `s` of a linear order by the number `i` of
elements of `s` before each element; there are then `#s - 1 - i` elements of `s` after it. -/]
theorem prod_card_filter_lt_card_filter_gt {α M : Type*} [LinearOrder α] [CommMonoid M]
    (s : Finset α) (f : ℕ → ℕ → M) :
    ∏ x ∈ s, f #{y ∈ s | y < x} #{y ∈ s | x < y} = ∏ i ∈ range #s, f i (#s - 1 - i) := by
  -- The elements of `s` other than `x` are those before `x` and those after `x`.
  have hcard {x : α} (hx : x ∈ s) : #{y ∈ s | x < y} = #s - 1 - #{y ∈ s | y < x} := by
    have h1 : {y ∈ s | ¬y < x}.erase x = {y ∈ s | x < y} := by
      ext y
      simp only [mem_erase, mem_filter, not_lt]
      grind
    have h2 := card_erase_add_one (s := {y ∈ s | ¬y < x}) (mem_filter.2 ⟨hx, lt_irrefl x⟩)
    have h3 := card_filter_add_card_filter_not (s := s) (· < x)
    rw [h1] at h2
    omega
  -- The number of elements before `x` is strictly increasing in `x`, with values below `#s`.
  have hinj : Set.InjOn (fun x => #{y ∈ s | y < x}) s :=
    StrictMonoOn.injOn fun x hx x' _ hxx' => card_lt_card <|
      (ssubset_iff_of_subset fun y hy =>
        mem_filter.2 ⟨(mem_filter.1 hy).1, (mem_filter.1 hy).2.trans hxx'⟩).2
        ⟨x, mem_filter.2 ⟨hx, hxx'⟩, fun h => lt_irrefl x (mem_filter.1 h).2⟩
  have himage : s.image (fun x => #{y ∈ s | y < x}) = range #s :=
    eq_of_subset_of_card_le (fun i hi => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
        exact mem_range.2 (card_lt_card (filter_ssubset.2 ⟨x, hx, lt_irrefl x⟩)))
      (by rw [card_range, card_image_of_injOn hinj])
  rw [← himage, prod_image hinj]
  exact prod_congr rfl fun x hx => by rw [hcard hx]

/-- A product over `range (n * q)` is the product of `q` consecutive blocks of `n` factors. -/
@[to_additive sum_range_mul_eq_sum_sum
  /-- A sum over `range (n * q)` is the sum of `q` consecutive blocks of `n` terms. -/]
theorem prod_range_mul_eq_prod_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (n q : ℕ) :
    ∏ l ∈ range (n * q), f l = ∏ j ∈ range q, ∏ l ∈ range n, f (n * j + l) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]

/-- The sum `∑_{i=1}^{m} 2i` of the first `m` positive even numbers is `m (m + 1)`. It is, for
instance, the exponent of the leading power of `q` in `∏_{i=1}^{m} (q^{2i} - 1)`. -/
theorem sum_range_two_mul_succ (m : ℕ) : ∑ i ∈ range m, 2 * (i + 1) = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sum_range_succ, ih]; ring

/-- The sum of the arithmetic progression `D + 1, D + 3, …, D + 2J - 1` of `J` terms with
common difference `2` is `J (D + J)`. -/
theorem sum_range_add_two_mul (D J : ℕ) :
    ∑ j ∈ range J, (D + 2 * j + 1) = J * (D + J) := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ, ih]; ring

/-- The Clebsch–Gordan dimension count: the numbers `m + n - 2k + 1` for `k ≤ min m n` add up to
`(m + 1)(n + 1)`. Reflecting the sum turns the descending terms into the ascending arithmetic
progression starting at `|m - n| + 1`. -/
theorem sum_range_min_add_one_sub_two_mul (m n : ℕ) :
    ∑ k ∈ range (min m n + 1), (m + n - 2 * k + 1) = (m + 1) * (n + 1) := by
  rw [← sum_range_reflect]
  have hrw : ∀ j ∈ range (min m n + 1),
      m + n - 2 * (min m n + 1 - 1 - j) + 1 = (m + n - 2 * min m n) + 2 * j + 1 := by
    intro j hj
    have hj' : j ≤ min m n := by simpa [Nat.lt_succ_iff] using hj
    omega
  rw [sum_congr rfl hrw, sum_range_add_two_mul]
  rcases Nat.le_total m n with h | h
  · rw [Nat.min_eq_left h, show m + n - 2 * m + (m + 1) = n + 1 by omega]
  · rw [Nat.min_eq_right h, show m + n - 2 * n + (n + 1) = m + 1 by omega, mul_comm]

/-- Summing over the truncated triangle `{(m, n, k) | m, n < N, k ≤ min m n}` is the same as summing
over the slice `{(p, k, q) | p + k < N, q + k < N}` of the cube, the summand transported along
`(m, n, k) ↦ (n - k, k, m - k)`. For `N = 0` both sides are empty sums.

This is the three-variable analogue of Mathlib's `Finset.prod_range_diag_flip` and its `to_additive`
twin `Finset.sum_range_diag_flip`, which flip a diagonally-indexed double sum; here the inner bound
is `min m n` rather than `m`, and the image is a slice of the cube rather than a second double sum.
-/
theorem sum_range_min_diag_flip {B : Type*} [AddCommMonoid B]
    (F : ℕ × ℕ × ℕ → B) (N : ℕ) :
    ∑ w ∈ (range N ×ˢ range N).sigma (fun mn => range (min mn.1 mn.2 + 1)),
        F (w.1.2 - w.2, w.2, w.1.1 - w.2) =
      ∑ w ∈ range N ×ˢ range N ×ˢ range N with w.1 + w.2.1 < N ∧ w.2.2 + w.2.1 < N, F w := by
  refine Finset.sum_nbij' (fun w => (w.1.2 - w.2, w.2, w.1.1 - w.2))
    (fun w => ⟨(w.2.2 + w.2.1, w.1 + w.2.1), w.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨m, n⟩, k⟩ hw
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
      le_min_iff] at hw
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨p, k, q⟩ hw
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hw
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
      le_min_iff]
    omega
  · rintro ⟨⟨m, n⟩, k⟩ hw
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
      le_min_iff] at hw
    dsimp only
    rw [Nat.sub_add_cancel hw.2.1, Nat.sub_add_cancel hw.2.2]
  · rintro ⟨p, k, q⟩ _
    simp
  · rintro ⟨⟨m, n⟩, k⟩ _
    rfl

/-- A coefficient-one normal-ordering identity for three sequences gives a factorization of their
finite generating sums, provided the reordered terms outside the truncated triangle vanish.
The scalar parameters only need a commutative monoid, and the coefficients need neither a unit
nor additive inverses. -/
theorem sum_smul_mul_sum_smul_of_mul_eq_sum {R : Type*} [CommMonoid R]
    {B : Type*} [NonUnitalSemiring B] [DistribSMul R B] [IsScalarTower R R B]
    [IsScalarTower R B B] [SMulCommClass R B B]
    (Dx Dy Dz : ℕ → B) (N : ℕ)
    (hno : ∀ m n, Dx m * Dy n =
      ∑ k ∈ range (min m n + 1), Dy (n - k) * Dz k * Dx (m - k))
    (hzero : ∀ p k q : ℕ, N ≤ p + k ∨ N ≤ q + k → Dy p * Dz k * Dx q = 0)
    (t u : R) :
    (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) =
      (∑ p ∈ range N, u ^ p • Dy p) * (∑ k ∈ range N, (t * u) ^ k • Dz k) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
  classical
  set G : ℕ × ℕ × ℕ → B := fun w =>
    (u ^ w.1 * (t * u) ^ w.2.1 * t ^ w.2.2) • (Dy w.1 * Dz w.2.1 * Dx w.2.2) with hG
  -- Step 1: expand the reordered product over the full cube of indices.
  have hbox : ∑ w ∈ range N ×ˢ range N ×ˢ range N, G w =
      (∑ p ∈ range N, u ^ p • Dy p) * (∑ k ∈ range N, (t * u) ^ k • Dz k) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
    rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [hG, Finset.sum_product, Finset.mul_sum, smul_mul_smul_comm, mul_assoc]
  -- Step 2: expand the original product over the reindexing domain.
  have hsrc : ∑ w ∈ (range N ×ˢ range N).sigma (fun mn => range (min mn.1 mn.2 + 1)),
        (t ^ w.1.1 * u ^ w.1.2) • (Dy (w.1.2 - w.2) * Dz w.2 * Dx (w.1.1 - w.2)) =
      (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) := by
    rw [Finset.sum_sigma, Finset.sum_mul_sum]
    simp only [Finset.sum_product, smul_mul_smul_comm, hno, Finset.smul_sum]
  -- Step 3: the reindexing itself, onto the part of the cube it covers.
  have hbij : ∑ w ∈ (range N ×ˢ range N).sigma (fun mn => range (min mn.1 mn.2 + 1)),
        (t ^ w.1.1 * u ^ w.1.2) • (Dy (w.1.2 - w.2) * Dz w.2 * Dx (w.1.1 - w.2)) =
      ∑ w ∈ range N ×ˢ range N ×ˢ range N with w.1 + w.2.1 < N ∧ w.2.2 + w.2.1 < N, G w := by
    rw [← sum_range_min_diag_flip G N]
    refine Finset.sum_congr rfl ?_
    -- On the triangle `m = a + k`, `n = b + k`, so the scalar `t ^ m * u ^ n` is `G`'s
    -- `u ^ b * (t * u) ^ k * t ^ a`.
    rintro ⟨⟨m, n⟩, k⟩ hw
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
      le_min_iff] at hw
    obtain ⟨a, rfl⟩ : ∃ a, m = a + k := ⟨m - k, (Nat.sub_add_cancel hw.2.1).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, n = b + k := ⟨n - k, (Nat.sub_add_cancel hw.2.2).symm⟩
    simp only [hG, Nat.add_sub_cancel]
    congr 1
    rw [mul_pow, pow_add, pow_add]
    ac_rfl
  -- Step 4: the terms of the cube outside that part vanish.
  have hsub : ∑ w ∈ range N ×ˢ range N ×ˢ range N with w.1 + w.2.1 < N ∧ w.2.2 + w.2.1 < N,
        G w = ∑ w ∈ range N ×ˢ range N ×ˢ range N, G w := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    rintro ⟨p, k, q⟩ hmem hnot
    simp only [Finset.mem_product, Finset.mem_range] at hmem
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have hor : N ≤ p + k ∨ N ≤ q + k := by omega
    simp [hG, hzero p k q hor]
  rw [← hsrc, hbij, hsub, hbox]

end Finset

namespace TauCeti

open Finset

/-- Replacing a summation over `Finset.Ioo 0 n` by one over `Finset.range n`, provided the
summand at `0` vanishes. -/
theorem sum_Ioo_eq_sum_range {N : Type*} [AddCommMonoid N] (n : ℕ) (g : ℕ → N)
    (hg : g 0 = 0) : ∑ c ∈ Ioo 0 n, g c = ∑ c ∈ range n, g c := by
  refine sum_subset (fun c hc ↦ ?_) fun c hc hc' ↦ ?_
  · simp only [mem_Ioo, mem_range] at hc ⊢
    omega
  · simp only [mem_range] at hc
    have hc0 : c = 0 := by
      by_contra hne
      exact hc' (mem_Ioo.2 ⟨by omega, hc⟩)
    rw [hc0, hg]

/-- Summing a two-variable family over the pairs `(c, p - c)` with `c ≤ p < K` is the same as
summing it over the square `range K × range K`, when the family vanishes off the triangle. -/
theorem sum_range_triangle {N : Type*} [AddCommMonoid N] (K : ℕ) (g : ℕ → ℕ → N)
    (hg : ∀ c q : ℕ, K ≤ c + q → g c q = 0) :
    ∑ p ∈ range K, ∑ c ∈ range (p + 1), g c (p - c) =
      ∑ c ∈ range K, ∑ q ∈ range K, g c q := by
  rw [sum_range_diag_flip]
  refine sum_congr rfl fun c hc ↦ ?_
  simp only [mem_range] at hc
  exact sum_subset (range_subset_range.mpr (Nat.sub_le K c)) fun q _ hq ↦ by
    simp only [mem_range, not_lt] at hq
    exact hg c q (by omega)

/-- A sum over all antidiagonals below `k + l` equals the sum over the rectangle
`range k × range l`, provided the summand vanishes whenever the first coordinate is at least
`k` or the second coordinate is at least `l`. -/
theorem sum_range_add_antidiagonal_of_support
    {N : Type*} [AddCommMonoid N] (k l : ℕ) (f : ℕ × ℕ → N)
    (hf : ∀ i j, k ≤ i ∨ l ≤ j → f (i, j) = 0) :
    ∑ n ∈ range (k + l), ∑ ij ∈ antidiagonal n, f ij =
      ∑ i ∈ range k, ∑ j ∈ range l, f (i, j) := by
  classical
  let s := (range (k + l)).sigma fun n => antidiagonal n
  let t := s.filter fun q => q.2.1 < k ∧ q.2.2 < l
  rw [Finset.sum_sigma']
  -- `sum_sigma'` leaves the sigma index in the dependent pair `q`; unfolding the local
  -- abbreviation is the only normalization needed to expose the original summand `f q.2`.
  change (∑ q ∈ s, f q.2) = _
  have hfilter : (∑ q ∈ t, f q.2) = ∑ q ∈ s, f q.2 := by
    apply Finset.sum_subset (by simp [t])
    intro q hqs hqt
    rw [Finset.mem_filter] at hqt
    simp only [hqs, true_and, not_and_or, not_lt] at hqt
    exact hf q.2.1 q.2.2 hqt
  rw [← hfilter, ← Finset.sum_product']
  apply Finset.sum_bij (fun q _ => q.2)
  · intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact hq.2
  · intro q₁ hq₁ q₂ hq₂ hqq
    rcases q₁ with ⟨n₁, ij₁⟩
    rcases q₂ with ⟨n₂, ij₂⟩
    dsimp only at hqq
    subst ij₂
    rw [Finset.mem_filter, Finset.mem_sigma, mem_antidiagonal] at hq₁ hq₂
    have hn : n₁ = n₂ := hq₁.1.2.symm.trans hq₂.1.2
    subst n₂
    rfl
  · intro ij hij
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    let q : (_ : ℕ) × (ℕ × ℕ) := ⟨ij.1 + ij.2, ij⟩
    have hsum : ij.1 + ij.2 < k + l := by omega
    have hq : q ∈ t := by
      rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, mem_antidiagonal]
      exact ⟨⟨hsum, rfl⟩, hij⟩
    exact ⟨q, hq, rfl⟩
  · intro q _
    rfl

/-- Enlarging both ranges of a double sum that vanishes for `b ≤ p` or `b < d`. -/
theorem sum_sum_range_eq_of_eq_zero_right {N : Type*} [AddCommMonoid N] {b K : ℕ} (hK : b ≤ K)
    (g : ℕ → ℕ → N) (hg : ∀ p d, b ≤ p ∨ b < d → g p d = 0) :
    ∑ p ∈ range b, ∑ d ∈ range (b + 1), g p d =
      ∑ p ∈ range K, ∑ d ∈ range (K + 1), g p d := by
  have inner : ∀ p : ℕ, ∑ d ∈ range (b + 1), g p d = ∑ d ∈ range (K + 1), g p d :=
    fun p ↦ sum_subset (range_subset_range.mpr (by omega)) fun d _ hd ↦ by
      simp only [mem_range, not_lt] at hd
      exact hg p d (Or.inr (by omega))
  have outer : ∑ p ∈ range b, ∑ d ∈ range (K + 1), g p d =
      ∑ p ∈ range K, ∑ d ∈ range (K + 1), g p d :=
    sum_subset (range_subset_range.mpr hK) fun p _ hp ↦ by
      simp only [mem_range, not_lt] at hp
      exact sum_eq_zero fun d _ ↦ hg p d (Or.inl hp)
  rw [← outer, ← sum_congr rfl fun p _ ↦ inner p]

/-- A sum over `Finset.range t` whose terms vanish outside two distinct positions is the sum of
the terms at those positions. -/
theorem sum_range_eq_of_eq_zero_off_pair {N : Type*} [AddCommMonoid N] {t : ℕ} {f : ℕ → N}
    {a b : ℕ} {v : N} (ha : a < t) (hb : b < t) (hab : a ≠ b)
    (hz : ∀ j < t, j ≠ a → j ≠ b → f j = 0) (hv : f a + f b = v) :
    ∑ j ∈ range t, f j = v := by
  classical
  rw [← Finset.sum_subset (s₁ := ({a, b} : Finset ℕ)) (s₂ := range t)
    (fun x hx ↦ by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa using by omega)
    (fun x hx hx' ↦ by
      simp only [mem_insert, mem_singleton, not_or] at hx'
      exact hz x (mem_range.mp hx) hx'.1 hx'.2),
    Finset.sum_pair hab, hv]

/-- A sum over `Finset.range t` whose terms vanish outside three pairwise distinct positions is
the sum of the terms at those positions. -/
theorem sum_range_eq_of_eq_zero_off_triple {N : Type*} [AddCommMonoid N] {t : ℕ} {f : ℕ → N}
    {a b d : ℕ} {v : N} (ha : a < t) (hb : b < t) (hd : d < t) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (hz : ∀ j < t, j ≠ a → j ≠ b → j ≠ d → f j = 0)
    (hv : f a + f b + f d = v) : ∑ j ∈ range t, f j = v := by
  classical
  rw [← Finset.sum_subset (s₁ := ({a, b, d} : Finset ℕ)) (s₂ := range t)
    (fun x hx ↦ by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa using by omega)
    (fun x hx hx' ↦ by
      simp only [mem_insert, mem_singleton, not_or] at hx'
      exact hz x (mem_range.mp hx) hx'.1 hx'.2.1 hx'.2.2),
    Finset.sum_insert (by simp [hab, had]), Finset.sum_pair hbd, ← add_assoc, hv]

/-- Splitting a sum over `range n` into a prefix of length `p`, a block of length `d`, and the
remaining suffix. -/
theorem sum_range_add_add {N : Type*} [AddCommMonoid N] (g : ℕ → N) {p d n : ℕ}
    (h : p + d ≤ n) :
    ∑ j ∈ range n, g j =
      (∑ j ∈ range p, g j) + (∑ j ∈ range d, g (p + j)) +
        ∑ j ∈ range (n - p - d), g (p + d + j) := by
  have s1 : ∑ j ∈ range n, g j =
      (∑ j ∈ range p, g j) + ∑ j ∈ range (n - p), g (p + j) := by
    have key := sum_range_add g p (n - p)
    rwa [show p + (n - p) = n from Nat.add_sub_cancel' (show p ≤ n from by omega)] at key
  have s2 : ∑ j ∈ range (n - p), g (p + j) =
      (∑ j ∈ range d, g (p + j)) + ∑ j ∈ range (n - p - d), g (p + d + j) := by
    have key := sum_range_add (f := fun k : ℕ => g (p + k)) d (n - p - d)
    rw [show d + (n - p - d) = n - p from by omega] at key
    refine key.trans ?_
    simp only [Nat.add_assoc]
  rw [s1, s2, ← add_assoc]

/-- Splitting a double sum over the blocks `(p, d)` (start and length) of a word of length
`l + 1 + n` at its position `l`.  When the summand vanishes on blocks running past the end of the
word, the sum is the sum over the blocks containing position `l`, those ending before it, and
those starting after it.  The blocks containing position `l` are indexed by their start `j ≤ l`
and the number `k ≤ n` of their letters after position `l`. -/
theorem sum_sum_range_split_blocks {N : Type*} [AddCommMonoid N] (l n : ℕ) (g : ℕ → ℕ → N)
    (hg : ∀ p d, l + 1 + n < p + d → g p d = 0) :
    ∑ p ∈ range (l + 1 + n), ∑ d ∈ range (l + 1 + n + 1), g p d =
      (∑ k ∈ range (n + 1), ∑ j ∈ range (l + 1), g j (l - j + 1 + k) +
        ∑ p ∈ range (l + 1), ∑ d ∈ range (l + 1 + 1), if p + d ≤ l then g p d else 0) +
      ∑ p ∈ range n, ∑ d ∈ range (n + 1), g (l + 1 + p) d := by
  rw [sum_range_add, sum_comm (s := range (n + 1)), ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_range] at hp
    have h₁ : ∑ k ∈ range p, g p (l - p + 1 + (n + 1) + k) = 0 :=
      sum_eq_zero fun k _ ↦ hg p _ (by omega)
    have h₂ : ∑ k ∈ range (p + 1), (if p + (l - p + 1 + k) ≤ l then g p (l - p + 1 + k) else 0) =
        0 := sum_eq_zero fun k _ ↦ ite_eq_right_iff.2 fun h ↦ absurd h (by omega)
    have h₃ : ∑ d ∈ range (l - p + 1), (if p + d ≤ l then g p d else 0) =
        ∑ d ∈ range (l - p + 1), g p d :=
      sum_congr rfl fun d hd ↦ ite_eq_left (by rw [mem_range] at hd; omega)
    -- Cut the lengths of the blocks starting at `p` where they reach position `l` and the end.
    have hlen : l + 1 + n + 1 = (l - p + 1) + (n + 1) + p := by omega
    have hlen' : l + 1 + 1 = (l - p + 1) + (p + 1) := by omega
    rw [hlen, sum_range_add (fun d ↦ g p d) (l - p + 1 + (n + 1)) p,
      sum_range_add (fun d ↦ g p d) (l - p + 1) (n + 1), hlen',
      sum_range_add (fun d ↦ if p + d ≤ l then g p d else 0) (l - p + 1) (p + 1), h₁, h₂, h₃,
      add_zero, add_zero, add_comm]
  · refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_range] at hp
    have h₁ : ∑ k ∈ range (l + 1), g (l + 1 + p) (n + 1 + k) = 0 :=
      sum_eq_zero fun k _ ↦ hg _ _ (by omega)
    have hlen : l + 1 + n + 1 = (n + 1) + (l + 1) := by omega
    rw [hlen, sum_range_add (fun d ↦ g (l + 1 + p) d) (n + 1) (l + 1), h₁, add_zero]



/-! ### The two-step recurrence of the sums `∑_{i ≤ min j r} c^i a (j + r − 2i)` -/

/-- **A two-step recurrence for the sums `S j r = ∑_{i ≤ min j r} c^i a (j + r − 2i)`**:
`S (j+2) (r+1) + c · S j (r+1) = S (j+1) (r+2) + c · S (j+1) r`.

This is the identity the Fourier coefficients of the Hecke operators at a prime power satisfy
(`TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Prime/Power.lean`), with `a t` the
coefficient at `p^t m` and `c = χ(p) p^{k−1}`; the `min` is what makes it hold with no relation
between `j` and `r`. -/
theorem sum_range_min_add_two {R : Type*} [Semiring R] (a : ℕ → R) (c : R) (j r : ℕ) :
    (∑ i ∈ range (min (j + 2) (r + 1) + 1), c ^ i * a (j + 2 + (r + 1) - 2 * i)) +
        c * ∑ i ∈ range (min j (r + 1) + 1), c ^ i * a (j + (r + 1) - 2 * i) =
      (∑ i ∈ range (min (j + 1) (r + 2) + 1), c ^ i * a (j + 1 + (r + 2) - 2 * i)) +
        c * ∑ i ∈ range (min (j + 1) r + 1), c ^ i * a (j + 1 + r - 2 * i) := by
  -- every one of the four sums is a sum of `A i = c^i a (j + r + 3 − 2i)`, the two scalar
  -- multiples with the index shifted by one, and the upper limits pair up, so both sides are the
  -- same pair of sums with the `i = 0` term of one of them removed
  set A : ℕ → R := fun i ↦ c ^ i * a (j + r + 3 - 2 * i) with hA
  -- a sum whose index reads `t - 2 i` with `t = j + r + 3` is a sum of `A`
  have eA : ∀ t n : ℕ, t = j + r + 3 →
      ∑ i ∈ range n, c ^ i * a (t - 2 * i) = ∑ i ∈ range n, A i := by
    rintro t n rfl
    rfl
  -- a scalar multiple of such a sum with `t + 2 = j + r + 3` is a sum of `A` shifted by one
  have eshift : ∀ t n : ℕ, t + 2 = j + r + 3 →
      c * ∑ i ∈ range n, c ^ i * a (t - 2 * i) = ∑ i ∈ range n, A (i + 1) := by
    intro t n ht
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hidx : j + r + 3 - 2 * (i + 1) = t - 2 * i := by omega
    simp only [hA]
    rw [hidx, ← mul_assoc, ← pow_succ']
  -- and a shifted sum is the unshifted one without its `i = 0` term
  have hsh : ∀ n : ℕ, ∑ i ∈ range n, A (i + 1) + A 0 = ∑ i ∈ range (n + 1), A i := fun n ↦
    (Finset.sum_range_succ' A n).symm
  have hmin₁ : min j (r + 1) + 1 + 1 = min (j + 1) (r + 2) + 1 := by omega
  have hmin₂ : min (j + 1) r + 1 + 1 = min (j + 2) (r + 1) + 1 := by omega
  rw [eA (j + 2 + (r + 1)) _ (by omega), eA (j + 1 + (r + 2)) _ (by omega),
    eshift (j + (r + 1)) _ (by omega), eshift (j + 1 + r) _ (by omega)]
  -- both sides become the same pair of sums of `A`, once the shifted ones absorb `A 0`
  have h₁ := hsh (min j (r + 1) + 1)
  have h₂ := hsh (min (j + 1) r + 1)
  rw [hmin₁] at h₁
  rw [hmin₂] at h₂
  -- no cancellation is needed: each unshifted sum is rewritten back into a shifted one plus `A 0`,
  -- after which the two sides differ only by the order of the summands
  rw [← h₁, ← h₂]
  abel

/-- **The base case of the two-step recurrence, at `j = 0`.** `S 0 (r+2) + c · S 0 r = S 1 (r+1)`
for `S j r = ∑_{i ≤ min j r} c^i a (j + r − 2i)`.

`sum_range_min_add_two` states the recurrence only from `j + 1` upwards — its second index is
`j + 1`, never `0` — so the degenerate case where the `min` pins two of the sums to a single term
is stated separately here. Together the two cover every `j`. -/
theorem sum_range_min_zero {R : Type*} [Semiring R] (a : ℕ → R) (c : R) (r : ℕ) :
    (∑ i ∈ range (min 0 (r + 2) + 1), c ^ i * a (0 + (r + 2) - 2 * i)) +
        c * ∑ i ∈ range (min 0 r + 1), c ^ i * a (0 + r - 2 * i) =
      ∑ i ∈ range (min 1 (r + 1) + 1), c ^ i * a (1 + (r + 1) - 2 * i) := by
  -- `min 0 _ = 0` pins the two sums on the left to their `i = 0` terms, and `min 1 (r+1) = 1`
  -- pins the one on the right to its `i = 0` and `i = 1` terms
  have hmin : min 1 (r + 1) + 1 = 2 := by omega
  have hidx : 1 + (r + 1) = r + 2 := by omega
  rw [hmin]
  simp [Finset.sum_range_succ, hidx]


/-- Twice the sum over pairs `i < j < k` is the square of the sum minus the sum of squares. -/
theorem two_mul_sum_range_pair {R : Type*} [CommRing R] (k : ℕ) (d : ℕ → R) :
    2 * ∑ j ∈ range k, ∑ i ∈ range j, d i * d j =
      (∑ i ∈ range k, d i) ^ 2 - ∑ i ∈ range k, d i ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih, ← sum_mul, sum_range_succ d,
      sum_range_succ (fun i ↦ d i ^ 2)]
    ring

/-- **Horner recursion** for the convolution `V m = ∑ k ∈ range (m + 1), c k • a ^ (m - k)` of a
sequence of scalars with the powers of an element `a` of an algebra:
`V (m + 1) = c (m + 1) • 1 + a * V m`. -/
theorem sum_range_succ_smul_pow_sub {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (c : ℕ → R) (a : A) (m : ℕ) :
    ∑ k ∈ range (m + 1 + 1), c k • a ^ (m + 1 - k) =
      c (m + 1) • 1 + a * ∑ k ∈ range (m + 1), c k • a ^ (m - k) := by
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_sum, add_comm]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mul_smul_comm, ← pow_succ', Nat.sub_add_comm (mem_range_succ_iff.mp hk)]

/-- **Horner recursion**, right-multiplication form: the convolution
`V m = ∑ k ∈ range (m + 1), c k • a ^ (m - k)` satisfies `V (m + 1) = c (m + 1) • 1 + V m * a`. -/
theorem sum_range_succ_smul_pow_sub' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (c : ℕ → R) (a : A) (m : ℕ) :
    ∑ k ∈ range (m + 1 + 1), c k • a ^ (m + 1 - k) =
      c (m + 1) • 1 + (∑ k ∈ range (m + 1), c k • a ^ (m - k)) * a := by
  rw [sum_range_succ_smul_pow_sub, mul_sum, sum_mul]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_smul_comm, smul_mul_assoc, ← pow_succ', ← pow_succ]

end TauCeti
end
end TAF_LiteralSource_0575

section TAF_LiteralSource_0576
/- Original module: TauCeti.RingTheory.PowerSeries.Geometric -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The geometric series in `a X`

Mathlib's `PowerSeries.mk_one_mul_one_sub_eq_one` says that `∑ Xⁿ` inverts `1 - X`.  Rescaling
`X` by an element `a` of the coefficient ring turns it into the statement that the geometric
series `∑ aⁿ Xⁿ` inverts `1 - a X`, with no invertibility assumption on `a`.  This is the
one-variable factor of the generating functions of the complete homogeneous symmetric
polynomials, `∏ᵢ (1 - xᵢ X)⁻¹ = ∑ₙ hₙ Xⁿ`.

Its square `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ` inverts `(1 - X) ^ 2`. Dividing a polynomial `p` by
`(1 - X) ^ 2` therefore produces coefficients which, beyond the degree of `p`, are the values
`(n + 1) p (1) - p' (1)` of an affine function of `n`. This is the shape of the coefficients of the
Lefschetz zeta function `det (1 - t P) / (1 - t) ^ 2` of an orientation-preserving map of a closed
connected oriented surface acting by `P` on its first cohomology.

## Main results

* `TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one`:
  `(∑ aⁿ Xⁿ) * (1 - a X) = 1`.
* `TauCeti.powerSeries_one_sub_C_mul_X_mul_mk_sum_smul_pow`,
  `TauCeti.powerSeries_mk_sum_smul_pow_mul_one_sub_C_mul_X`: for scalars `c k` in a commutative
  ring `R` and an element `a` of an `R`-algebra, multiplying the series with coefficients
  `∑ k ∈ range (m + 1), c k • a ^ (m - k)` by `1 - a X`, on either side, gives `∑ c k Xᵏ`.
  This series is the product of `∑ c k Xᵏ` with the geometric series `∑ aⁿ Xⁿ`.
* `PowerSeries.mk_one_sq`: `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ`.
* `Polynomial.coeff_coe_mul_mk_one_sq`: the `a`-th coefficient of `p / (1 - X) ^ 2` is
  `(a + 1) p (1) - p' (1)` once `p` has degree at most `a + 1`.
-/

public section

namespace TauCeti

/-- **The geometric series in `a X`**: `∑ aⁿ Xⁿ` is a multiplicative inverse of `1 - a X`, for
every element `a` of the coefficient ring. -/
theorem powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one {R : Type*} [Ring R] (a : R) :
    PowerSeries.mk (fun n => a ^ n) *
        (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one, ← mul_assoc, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]

/-- **Convolution with the geometric series.** For scalars `c k` and an element `a` of an
algebra, the series with coefficients `∑ k ∈ range (m + 1), c k • a ^ (m - k)` is carried by
`1 - a X`, multiplying on the left, to the series `∑ c k Xᵏ`. -/
theorem powerSeries_one_sub_C_mul_X_mul_mk_sum_smul_pow {R A : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] (c : ℕ → R) (a : A) :
    (1 - PowerSeries.C a * PowerSeries.X) *
        PowerSeries.mk (fun m ↦ ∑ k ∈ Finset.range (m + 1), c k • a ^ (m - k)) =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk c) := by
  ext (_ | m)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, sum_range_succ_smul_pow_sub,
      Algebra.algebraMap_eq_smul_one]

/-- **Convolution with the geometric series.** For scalars `c k` and an element `a` of an
algebra, the series with coefficients `∑ k ∈ range (m + 1), c k • a ^ (m - k)` is carried by
`1 - a X`, multiplying on the right, to the series `∑ c k Xᵏ`. -/
theorem powerSeries_mk_sum_smul_pow_mul_one_sub_C_mul_X {R A : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] (c : ℕ → R) (a : A) :
    PowerSeries.mk (fun m ↦ ∑ k ∈ Finset.range (m + 1), c k • a ^ (m - k)) *
        (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk c) := by
  ext (_ | m)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [mul_sub, ← mul_assoc, PowerSeries.coeff_succ_mul_X, sum_range_succ_smul_pow_sub',
      Algebra.algebraMap_eq_smul_one]

/-- The square of the geometric series: `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ`. -/
theorem _root_.PowerSeries.mk_one_sq (R : Type*) [CommRing R] :
    (PowerSeries.mk 1 : PowerSeries R) ^ 2 = PowerSeries.mk fun n ↦ (n + 1 : R) := by
  rw [← one_add_one_eq_two, PowerSeries.mk_one_pow_eq_mk_choose_add]
  ext n
  simp [add_comm]

open _root_.Polynomial in
/-- The `a`-th coefficient of `p / (1 - X) ^ 2 = p * (∑ Xⁿ) ^ 2` is `(a + 1) p (1) - p' (1)`
whenever the polynomial `p` has degree at most `a + 1`. -/
theorem _root_.Polynomial.coeff_coe_mul_mk_one_sq {R : Type*} [CommRing R] (p : R[X]) {a : ℕ}
    (hp : p.natDegree ≤ a + 1) :
    PowerSeries.coeff a ((p : PowerSeries R) * PowerSeries.mk 1 ^ 2) =
      (a + 1) * p.eval 1 - p.derivative.eval 1 := by
  have hlt : p.natDegree < a + 2 := by omega
  have h (i : ℕ) (hi : i ∈ Finset.range (a + 1)) :
      p.coeff i * ((a - i : ℕ) + 1) = (a + 1) * p.coeff i - p.coeff i * i := by
    rw [Nat.cast_sub (Finset.mem_range_succ_iff.1 hi)]
    ring
  rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt]
  simp [PowerSeries.mk_one_sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ _ (a + 1),
    Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end TauCeti
end
end TAF_LiteralSource_0576

section TAF_LiteralSource_0577
/- Original module: PaperVerification.AlternatingFormsSymmetricSeries -/


/-!
# The actual complete-symmetric and first-variation series

The first variation in Section 4 is a partial derivative of the ordinary complete
homogeneous symmetric polynomial.  This file retains that definition and proves
its generating-function formula.  Coefficientwise differentiation is justified by
the finite convolution formula for multiplication of formal power series.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

section CoefficientDerivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation of the coefficient ring extends coefficientwise to formal power
series.  This differentiates coefficients, leaving the formal variable fixed. -/
noncomputable def coefficientDerivation (D : Derivation R A A) :
    Derivation R (PowerSeries A) (PowerSeries A) where
  toFun f := PowerSeries.mk fun n => D (PowerSeries.coeff n f)
  map_add' f g := by ext n; simp
  map_smul' a f := by ext n; simp [PowerSeries.coeff_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change PowerSeries.mk (fun n => D (PowerSeries.coeff n (f * g))) =
      f * PowerSeries.mk (fun n => D (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => D (PowerSeries.coeff n f))
    rw [mul_comm g]
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, map_add, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _

@[simp] theorem coeff_coefficientDerivation (D : Derivation R A A)
    (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (coefficientDerivation D f) = D (PowerSeries.coeff n f) :=
  by
    change PowerSeries.coeff n
      (PowerSeries.mk fun m => D (PowerSeries.coeff m f)) = D (PowerSeries.coeff n f)
    exact PowerSeries.coeff_mk n _

@[simp] theorem coefficientDerivation_C (D : Derivation R A A) (a : A) :
    coefficientDerivation D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  simp only [coeff_coefficientDerivation, PowerSeries.coeff_C]
  split_ifs <;> simp

@[simp] theorem coefficientDerivation_X (D : Derivation R A A) :
    coefficientDerivation D PowerSeries.X = 0 := by
  ext n
  simp only [coeff_coefficientDerivation, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp

/-- Logarithmic differentiation of a finite product, using explicitly given
multiplicative inverses rather than a field of fractions. -/
theorem derivation_prod_inverse_formula {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (S : Finset ι) (f g : ι → A)
    (hfg : ∀ i ∈ S, f i * g i = 1) :
    D (∏ i ∈ S, f i) = (∏ i ∈ S, f i) * ∑ i ∈ S, g i * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfgS : ∀ i ∈ S, f i * g i = 1 := fun i hi => hfg i (by simp [hi])
    have hfgA := hfg a (by simp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      ih hfgS, smul_eq_mul, smul_eq_mul]
    calc
      f a * ((∏ i ∈ S, f i) * ∑ i ∈ S, g i * D (f i)) +
          (∏ i ∈ S, f i) * D (f a) =
        (f a * ∏ i ∈ S, f i) * (g a * D (f a) + ∑ i ∈ S, g i * D (f i)) := by
          rw [mul_add]
          have hcancel : (f a * ∏ i ∈ S, f i) * (g a * D (f a)) =
              (∏ i ∈ S, f i) * D (f a) := by
            calc
              _ = (f a * g a) * ((∏ i ∈ S, f i) * D (f a)) := by ring
              _ = _ := by rw [hfgA, one_mul]
          rw [hcancel]
          ring

/-- The geometric formal series with coefficient `a^n`. -/
noncomputable def geometricSeries (a : A) : PowerSeries A :=
  PowerSeries.mk fun n => a ^ n

@[simp] theorem geometricSeries_inverse (a : A) :
    geometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 :=
  TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one a

/-- Coefficientwise differentiation of the geometric series. -/
theorem coefficientDerivation_geometric (D : Derivation R A A) (a : A) :
    coefficientDerivation D (geometricSeries a) =
      geometricSeries a ^ 2 * PowerSeries.C (D a) * PowerSeries.X := by
  rw [(coefficientDerivation D).leibniz_of_mul_eq_one (geometricSeries_inverse a)]
  simp only [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, coefficientDerivation_C,
    coefficientDerivation_X, smul_eq_mul, mul_zero, add_zero, zero_sub]
  ring

/-- The product of geometric series has the expected logarithmic derivative. -/
theorem coefficientDerivation_prod_geometric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Derivation R A A) (a : ι → A) :
    coefficientDerivation D (∏ i, geometricSeries (a i)) =
      (∏ i, geometricSeries (a i)) *
        ∑ i, geometricSeries (a i) * PowerSeries.C (D (a i)) * PowerSeries.X := by
  rw [derivation_prod_inverse_formula (coefficientDerivation D) Finset.univ
    (fun i => geometricSeries (a i))
    (fun i => 1 - PowerSeries.C (a i) * PowerSeries.X)
    (fun i _ => geometricSeries_inverse (a i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientDerivation_geometric]
  calc
    _ = (geometricSeries (a i) * (1 - PowerSeries.C (a i) * PowerSeries.X)) *
        (geometricSeries (a i) * PowerSeries.C (D (a i)) * PowerSeries.X) := by ring
    _ = _ := by rw [geometricSeries_inverse, one_mul]

end CoefficientDerivation

section CompleteSymmetric

variable {K σ : Type*} [CommRing K] [Fintype σ] [DecidableEq σ]

/-- The ordinary complete homogeneous symmetric polynomials, assembled into a
formal power series over their polynomial ring. -/
noncomputable def completeSymmetricSeries : PowerSeries (MvPolynomial σ K) :=
  PowerSeries.mk fun n => MvPolynomial.hsymm σ K n

theorem completeSymmetricSeries_eq_prod :
    completeSymmetricSeries (K := K) (σ := σ) =
      ∏ i, geometricSeries (MvPolynomial.X i : MvPolynomial σ K) :=
  TauCeti.mk_hsymm_eq_prod_mk_pow K

/-- The derivative identity for the actual Mathlib complete homogeneous
symmetric polynomials, valid without division or characteristic assumptions. -/
theorem pderiv_completeSymmetricSeries (i : σ) :
    coefficientDerivation (MvPolynomial.pderiv i)
        (completeSymmetricSeries (K := K) (σ := σ)) =
      PowerSeries.X * completeSymmetricSeries * geometricSeries (MvPolynomial.X i) := by
  rw [completeSymmetricSeries_eq_prod, coefficientDerivation_prod_geometric]
  have hsum : (∑ j : σ, geometricSeries (MvPolynomial.X j : MvPolynomial σ K) *
      PowerSeries.C ((MvPolynomial.pderiv i) (MvPolynomial.X j)) * PowerSeries.X) =
      geometricSeries (MvPolynomial.X i) * PowerSeries.X := by
    simp [MvPolynomial.pderiv_X, Pi.single_apply]
  rw [hsum]
  ring

/-- Complete homogeneous polynomials evaluated at an arbitrary family. -/
noncomputable def completeEvaluationSeries (y : σ → K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPolynomial.eval y (MvPolynomial.hsymm σ K n)

/-- The first variation of the actual complete homogeneous polynomial. -/
noncomputable def firstVariationSeries (y z : σ → K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ i, z i *
    MvPolynomial.eval y (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K n))

theorem map_completeSymmetricSeries (y : σ → K) :
    PowerSeries.map (MvPolynomial.eval y) (completeSymmetricSeries (K := K) (σ := σ)) =
      completeEvaluationSeries y := by
  ext n
  simp [completeSymmetricSeries, completeEvaluationSeries]

theorem map_geometricSeries {A : Type*} [CommRing A] (f : A →+* K) (a : A) :
    PowerSeries.map f (geometricSeries a) = geometricSeries (f a) := by
  ext n
  simp [geometricSeries]

theorem completeEvaluationSeries_eq_prod (y : σ → K) :
    completeEvaluationSeries y = ∏ i, geometricSeries (y i) := by
  rw [← map_completeSymmetricSeries, completeSymmetricSeries_eq_prod, map_prod]
  simp only [map_geometricSeries, MvPolynomial.eval_X]

/-- The generating formula for the paper's first variations.  After replacing
`t` by `t²` and dividing the zero-constant series by `t`, this is its odd series
`U(t)`. -/
theorem firstVariationSeries_formula (y z : σ → K) :
    firstVariationSeries y z = PowerSeries.X * completeEvaluationSeries y *
      ∑ i, PowerSeries.C (z i) * geometricSeries (y i) := by
  have hsum : firstVariationSeries y z =
      ∑ i, PowerSeries.C (z i) *
        PowerSeries.map (MvPolynomial.eval y)
          (coefficientDerivation (MvPolynomial.pderiv i)
            (completeSymmetricSeries (K := K) (σ := σ))) := by
    ext n
    simp [firstVariationSeries, completeSymmetricSeries]
  rw [hsum]
  simp only [pderiv_completeSymmetricSeries, map_mul, PowerSeries.map_X,
    map_completeSymmetricSeries, map_geometricSeries, MvPolynomial.eval_X]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end CompleteSymmetric

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0577

