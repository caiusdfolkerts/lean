module

public import PaperVerification.AlternatingFormsKoszulHomology
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

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
