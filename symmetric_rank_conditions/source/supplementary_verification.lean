module
public import schur_theory
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"

@[expose] public section

/- Generated from the separately readable proof sources listed in
   audit/SupplementaryVerification_sources.json. All mathematical commands are copied verbatim.
   Generation alone is not evidence of successful kernel verification. -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "SupplementaryVerification IMPORTS_LOADED\n"
  logInfo "SupplementaryVerification IMPORTS_LOADED"

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "SupplementaryVerification BEGIN OrderTransfer\n"
  logInfo "SupplementaryVerification BEGIN OrderTransfer"

/- Begin OrderTransfer.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Every order selecting the folded antidiagonals

This proves the remark following Corollary 6.1.  A unit-leading Gröbner
basis remains a Gröbner basis when another monomial order gives every
basis polynomial the same leading exponent.  Division for the new order
leaves a remainder supported on the old standard monomials, so an ideal
member has zero remainder.  No comparison of Hilbert functions is needed.

For the actual mixed generators, agreement on the individual minors
implies agreement on their products.  The field theorem uses genuine
symbolic powers.  The integer theorem specializes to every commutative
coefficient ring, including rings with zero divisors and the zero ring.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace MonomialOrder

variable {σ R : Type*} [CommRing R]
    {m : MonomialOrder σ} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- Agreement on the leading exponents of a unit-leading Gröbner basis
is sufficient to transfer the entire Gröbner-basis assertion. -/
theorem IsGroebnerBasis.changeOrder_of_degree_eq
    (hG : m.IsGroebnerBasis G I)
    (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (ω : MonomialOrder σ) (hdegree : ∀ g ∈ G, ω.degree g = m.degree g) :
    ω.IsGroebnerBasis G I := by
  apply isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨hG.subset, ?_⟩
  intro f hf
  have huω : ∀ g ∈ G, g ≠ 0 → IsUnit (ω.leadingCoeff g) := by
    intro g hg hg0
    rw [m.leadingCoeff_eq_of_degree_eq ω (hdegree g hg)]
    exact hu g hg hg0
  obtain ⟨r,hr⟩ := MonomialOrder.exists_isRemainder (m := ω) huω f
  have hrI : r ∈ I := by
    have hsub : f - r ∈ I := by
      rw [hG.ideal_eq_span]
      exact hr.sub_mem_span
    simpa only [sub_sub_cancel] using I.sub_mem hf hsub
  have hself : m.IsRemainder r G r := by
    apply MonomialOrder.isRemainder_self_iff.mpr
    intro d hd g hg hg0
    rw [← hdegree g hg]
    exact hr.not_degree_le hd hg hg0
  have hr0 : r = 0 := (hG.remainder_eq_zero_iff_mem hself).mpr hrI
  simpa only [hr0] using hr

/-- The resulting actual leading-term ideals are equal. -/
theorem IsGroebnerBasis.initial_eq_of_degree_eq
    (hG : m.IsGroebnerBasis G I)
    (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (ω : MonomialOrder σ) (hdegree : ∀ g ∈ G, ω.degree g = m.degree g) :
    Ideal.span (ω.leadingTerm '' (I : Set (MvPolynomial σ R))) =
      Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) := by
  rw [(hG.changeOrder_of_degree_eq hu ω hdegree).span_leadingTerm_image,
    hG.span_leadingTerm_image]
  congr 1
  apply Set.image_congr
  intro g hg
  exact m.leadingTerm_eq_of_degree_eq ω (hdegree g hg)

/-- The individual standard monomial exponents are unchanged as well. -/
theorem IsGroebnerBasis.standardMonomials_eq_of_degree_eq
    (hG : m.IsGroebnerBasis G I)
    (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (ω : MonomialOrder σ) (hdegree : ∀ g ∈ G, ω.degree g = m.degree g) :
    ω.standardMonomials I = m.standardMonomials I := by
  ext d
  rw [(hG.changeOrder_of_degree_eq hu ω hdegree).mem_standardMonomials_iff,
    hG.mem_standardMonomials_iff]
  constructor <;> intro h g hg hg0 <;>
    simpa only [hdegree g hg] using h g hg hg0

end MonomialOrder

namespace FourPapers.Symmetric.OrderTransfer

/-- The hypothesis states the actual leading exponent of each actual minor. -/
def SelectsFoldedAntidiagonals (n : ℕ) (R : Type*) [CommRing R]
    (ω : MonomialOrder (Entry n)) : Prop :=
  ∀ δ : MinorData n, ω.degree (δ.polynomial R) = δ.exponent

theorem foldedOrder_selects (n : ℕ) (R : Type*) [CommRing R] [Nontrivial R] :
    SelectsFoldedAntidiagonals n R (foldedOrder n) :=
  fun δ => δ.degree_polynomial R

theorem minor_degree_eq {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n R ω)
    (δ : MinorData n) :
    ω.degree (δ.polynomial R) = (foldedOrder n).degree (δ.polynomial R) :=
  (hω δ).trans (δ.degree_polynomial R).symm

theorem minor_unit_leading {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n R ω)
    (δ : MinorData n) : IsUnit (ω.leadingCoeff (δ.polynomial R)) := by
  rw [(foldedOrder n).leadingCoeff_eq_of_degree_eq ω (minor_degree_eq R ω hω δ)]
  exact δ.leadingCoeff_polynomial_isUnit R

/-- An order selecting the integral antidiagonals retains them after
coefficient change to every nonzero ring, even when coefficients cancel. -/
theorem selects_after_baseChange {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    SelectsFoldedAntidiagonals n R ω := by
  intro δ
  have hc : (Int.castRingHom R) (ω.leadingCoeff (δ.polynomial ℤ)) ≠ 0 :=
    ((minor_unit_leading ℤ ω hω δ).map (Int.castRingHom R)).ne_zero
  have hm : MvPolynomial.map (Int.castRingHom R) (δ.polynomial ℤ) = δ.polynomial R :=
    map_minor (Int.castRingHom R) δ.rows δ.cols
  rw [← hm,ω.degree_map_of_leadingCoeff_ne_zero (Int.castRingHom R) hc]
  exact hω δ

/-- Agreement on the individual minors automatically includes every exact-score product. -/
theorem mixed_generators_degree_eq {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (r : RankArray n) (conditions : List (ℕ × ℕ))
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n R ω) :
    ∀ g ∈ mixedGenerators R r conditions,
      ω.degree g = (foldedOrder n).degree g := by
  classical
  rintro g (hg | hg)
  · obtain ⟨i,j,a,b,ha,hb,rfl⟩ := hg
    exact minor_degree_eq R ω hω ⟨r i j + 1,a,b⟩
  · obtain ⟨ts,hts,k,δ,hsize,hscore,rfl⟩ := hg
    calc
      ω.degree (∏ j, (δ j).polynomial R) = ∑ j, ω.degree ((δ j).polynomial R) :=
        ω.degree_prod_of_regular (fun j _ => (minor_unit_leading R ω hω (δ j)).isRegular)
      _ = ∑ j, (foldedOrder n).degree ((δ j).polynomial R) := by
        apply Finset.sum_congr rfl
        intro j _
        exact minor_degree_eq R ω hω (δ j)
      _ = (foldedOrder n).degree (∏ j, (δ j).polynomial R) :=
        ((foldedOrder n).degree_prod_of_regular
          (fun j _ => ((δ j).leadingCoeff_polynomial_isUnit R).isRegular)).symm

/-- Every permitted order gives the actual mixed symbolic ideal its displayed basis. -/
theorem mixed_field_groebner (n : ℕ) (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ)) (hc : ValidSymbolicConditions n conditions)
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n K ω) :
    ω.IsGroebnerBasis (mixedGenerators K r conditions) (mixedIdeal K r conditions) :=
  (compatible_rank_and_symbolic_conditions n K r hr conditions hc).changeOrder_of_degree_eq
    (mixedGenerators_unit_leading K r conditions) ω
    (mixed_generators_degree_eq K r conditions ω hω)

/-- The initial ideal is literally the same sum of folded antidiagonal ideals. -/
theorem mixed_field_initial (n : ℕ) (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ)) (hc : ValidSymbolicConditions n conditions)
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n K ω) :
    Simultaneous.orderInitialIdeal ω (mixedIdeal K r conditions) =
      northwestAntidiagonalIdeal K r ⊔
        ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal K n ts.1 ts.2 := by
  have hh := (compatible_rank_and_symbolic_conditions n K r hr conditions hc).initial_eq_of_degree_eq
    (mixedGenerators_unit_leading K r conditions) ω
      (mixed_generators_degree_eq K r conditions ω hω)
  exact hh.trans (compatible_initial_ideal n K r hr conditions hc)

/-- Over the integers, the same order retains the genuine displayed generators. -/
theorem mixed_integral_groebner {n : ℕ} (D : MixedDatum n)
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    ω.IsGroebnerBasis (mixedGenerators ℤ D.rank D.conditions) (mixedIntegralSpan D) :=
  (mixedIntegralSpan_groebner D).changeOrder_of_degree_eq
    (mixedGenerators_unit_leading ℤ D.rank D.conditions) ω
    (mixed_generators_degree_eq ℤ D.rank D.conditions ω hω)

/-- The order assertion specializes to every commutative coefficient ring,
without a nontriviality, characteristic, or flatness hypothesis. -/
theorem mixed_groebner_after_baseChange {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    ω.IsGroebnerBasis (mixedGenerators R D.rank D.conditions)
      (integralMixedIdeal R D.rank D.conditions) := by
  have hh := (mixed_integral_groebner D ω hω).map_of_unit_leading (Int.castRingHom R)
    (fun g hg hg0 => by
      rw [(foldedOrder n).leadingCoeff_eq_of_degree_eq ω
        (mixed_generators_degree_eq ℤ D.rank D.conditions ω hω g hg)]
      exact mixedGenerators_unit_leading ℤ D.rank D.conditions g hg hg0)
  rwa [map_mixedGenerators,← integralMixedIdeal_eq_map_span R D] at hh

/-- The actual antidiagonal initial-ideal formula holds after every
commutative coefficient change, including specialization to the zero ring. -/
theorem mixed_initial_after_baseChange {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    Simultaneous.orderInitialIdeal ω (integralMixedIdeal R D.rank D.conditions) =
      northwestAntidiagonalIdeal R D.rank ⊔
        ∑ ts ∈ D.conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact Subsingleton.elim _ _
  · letI := hR
    have hG := mixed_groebner_after_baseChange R D (foldedOrder n) (foldedOrder_selects n ℤ)
    have hh := hG.initial_eq_of_degree_eq
      (mixedGenerators_unit_leading R D.rank D.conditions) ω
      (mixed_generators_degree_eq R D.rank D.conditions ω (selects_after_baseChange R ω hω))
    apply hh.trans
    rw [hG.span_leadingTerm_image,
      (foldedOrder n).span_leadingTerm_eq_span_monomial_degree_of_units
        (mixedGenerators R D.rank D.conditions)
        (fun g hg => IsUnit.of_mul_eq_one _
          (mixedGenerators_leadingCoeff_mul_self R D.rank D.conditions g hg)),
      monomial_degrees_mixedGenerators,mixedAntidiagonal_span]

/-- For a fixed coefficient ring, it is enough that the order select the
folded antidiagonals in that ring itself.  No integral selector is required. -/
theorem mixed_groebner_of_selects {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n R ω) :
    ω.IsGroebnerBasis (mixedGenerators R D.rank D.conditions)
      (integralMixedIdeal R D.rank D.conditions) := by
  have hG := mixed_groebner_after_baseChange R D (foldedOrder n) (foldedOrder_selects n ℤ)
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    refine hG.changeOrder_of_degree_eq ?_ ω ?_
    · intro g hg hg0
      exact False.elim (hg0 (Subsingleton.elim _ _))
    · intro g hg
      rw [Subsingleton.elim g 0]
      simp
  · letI := hR
    exact hG.changeOrder_of_degree_eq (mixedGenerators_unit_leading R D.rank D.conditions)
      ω (mixed_generators_degree_eq R D.rank D.conditions ω hω)

/-- The same fixed-ring hypothesis gives the literal initial-ideal formula,
including coefficient rings whose characteristic removes other determinant terms. -/
theorem mixed_initial_of_selects {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n R ω) :
    Simultaneous.orderInitialIdeal ω (integralMixedIdeal R D.rank D.conditions) =
      northwestAntidiagonalIdeal R D.rank ⊔
        ∑ ts ∈ D.conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact Subsingleton.elim _ _
  · letI := hR
    have hG := mixed_groebner_after_baseChange R D (foldedOrder n) (foldedOrder_selects n ℤ)
    exact (hG.initial_eq_of_degree_eq
      (mixedGenerators_unit_leading R D.rank D.conditions) ω
      (mixed_generators_degree_eq R D.rank D.conditions ω hω)).trans
        (mixed_initial_after_baseChange R D (foldedOrder n) (foldedOrder_selects n ℤ))

/-- The selected order's literal monomials give a quotient basis over the
fixed coefficient ring, with selection assumed only in that ring. -/
theorem standard_basis_of_selects {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n R ω) :
    let v : ω.standardMonomials (integralMixedIdeal R D.rank D.conditions) →
        CoordinateRing n R ⧸ integralMixedIdeal R D.rank D.conditions :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  have hu : ∀ g ∈ mixedGenerators R D.rank D.conditions,
      g ≠ 0 → IsUnit (ω.leadingCoeff g) := by
    intro g hg hg0
    rcases subsingleton_or_nontrivial R with hR | hR
    · letI := hR
      exact False.elim (hg0 (Subsingleton.elim _ _))
    · letI := hR
      rw [(foldedOrder n).leadingCoeff_eq_of_degree_eq ω
        (mixed_generators_degree_eq R D.rank D.conditions ω hω g hg)]
      exact mixedGenerators_unit_leading R D.rank D.conditions g hg hg0
  have hh := (mixed_groebner_of_selects R D ω hω).fixed_standard_basis_after_basechange
    (RingHom.id R) hu
  have hmap : (MvPolynomial.map (RingHom.id R) : CoordinateRing n R →+* CoordinateRing n R) =
      RingHom.id (CoordinateRing n R) := by
    apply RingHom.ext
    intro p
    exact MvPolynomial.map_id p
  dsimp only at hh ⊢
  erw [hmap, Ideal.map_id] at hh
  exact hh

/-- The fixed integer standard exponent set is independent of the selected order. -/
theorem integral_standardMonomials_eq {n : ℕ} (D : MixedDatum n)
    (ω : MonomialOrder (Entry n)) (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    ω.standardMonomials (mixedIntegralSpan D) =
      (foldedOrder n).standardMonomials (mixedIntegralSpan D) :=
  (mixedIntegralSpan_groebner D).standardMonomials_eq_of_degree_eq
    (mixedGenerators_unit_leading ℤ D.rank D.conditions) ω
    (mixed_generators_degree_eq ℤ D.rank D.conditions ω hω)

/-- The corresponding free quotient basis is unchanged under all coefficient maps. -/
theorem standard_basis_after_baseChange {n : ℕ} (R : Type*) [CommRing R]
    (D : MixedDatum n) (ω : MonomialOrder (Entry n))
    (hω : SelectsFoldedAntidiagonals n ℤ ω) :
    let v : ω.standardMonomials (mixedIntegralSpan D) →
        CoordinateRing n R ⧸ integralMixedIdeal R D.rank D.conditions :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  have hh := (mixed_integral_groebner D ω hω).fixed_standard_basis_after_basechange
    (Int.castRingHom R)
    (fun g hg hg0 => by
      rw [(foldedOrder n).leadingCoeff_eq_of_degree_eq ω
        (mixed_generators_degree_eq ℤ D.rank D.conditions ω hω g hg)]
      exact mixedGenerators_unit_leading ℤ D.rank D.conditions g hg hg0)
  rwa [← integralMixedIdeal_eq_map_span R D] at hh

end FourPapers.Symmetric.OrderTransfer
end




end
/- End OrderTransfer.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "SupplementaryVerification BEGIN TransposeFixedLocus\n"
  logInfo "SupplementaryVerification BEGIN TransposeFixedLocus"

/- Begin TransposeFixedLocus.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# The transpose fixed locus and the determinant degeneration

The coordinate ring of the scheme-theoretic fixed locus of transpose is
computed as the quotient by all differences `f - transpose(f)`.  The
quotient is the ordinary polynomial ring in independent symmetric entries,
over every commutative coefficient ring.  In particular this computation
retains the characteristic-two scheme structure.

The folding homomorphism takes the literal weighted nonsymmetric
determinant to the cleared-denominator symmetric deformation.  The final
example computes its two-by-two polynomial and its doubled special fiber.
-/

noncomputable section
namespace FourPapers.Symmetric.Transpose
open MvPolynomial
open scoped BigOperators

abbrev SquareRing (n : ℕ) (R : Type*) [CommRing R] :=
  MvPolynomial (Fin n × Fin n) R

def foldHom (n : ℕ) (R : Type*) [CommRing R] :
    SquareRing n R →ₐ[R] CoordinateRing n R :=
  MvPolynomial.rename (fun ij => fold ij.1 ij.2)

def transposeHom (n : ℕ) (R : Type*) [CommRing R] :
    SquareRing n R →ₐ[R] SquareRing n R :=
  MvPolynomial.rename Prod.swap

def coordinateDifferenceIdeal (n : ℕ) (R : Type*) [CommRing R] :
    Ideal (SquareRing n R) :=
  Ideal.span (Set.range (fun ij : Fin n × Fin n =>
    (X ij : SquareRing n R) - X ij.swap))

/-- The literal affine fixed-locus ideal, with all polynomial differences. -/
def fixedLocusIdeal (n : ℕ) (R : Type*) [CommRing R] :
    Ideal (SquareRing n R) :=
  Ideal.span (Set.range (fun f : SquareRing n R => f - transposeHom n R f))

private def entryPair {n : ℕ} (e : Entry n) : Fin n × Fin n :=
  ofLex e.val

private theorem entryPair_fold {n : ℕ} (i j : Fin n) :
    entryPair (fold i j) = (max i j, min i j) := by
  simp only [entryPair, fold, ofLex_toLex]

private theorem entryPair_fold_difference {n : ℕ} (R : Type*) [CommRing R]
    (i j : Fin n) :
    (X (entryPair (fold i j)) : SquareRing n R) - X (i,j) ∈
      coordinateDifferenceIdeal n R := by
  rw [entryPair_fold]
  rcases le_total i j with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact Ideal.subset_span ⟨(j,i), rfl⟩
  · simpa only [max_eq_left h, min_eq_right h, sub_self] using
      (coordinateDifferenceIdeal n R).zero_mem

private def quotientSection (n : ℕ) (R : Type*) [CommRing R] :
    CoordinateRing n R →ₐ[R] SquareRing n R ⧸ coordinateDifferenceIdeal n R :=
  MvPolynomial.aeval (fun e => Ideal.Quotient.mk _ (X (entryPair e)))

private theorem quotientSection_comp_foldHom (n : ℕ) (R : Type*) [CommRing R] :
    (quotientSection n R).comp (foldHom n R) =
      Ideal.Quotient.mkₐ R (coordinateDifferenceIdeal n R) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  simp only [AlgHom.comp_apply, foldHom, rename_X, quotientSection, aeval_X,
    Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq.mpr (entryPair_fold_difference R i j)

/-- No relation beyond identifying transposed entries is introduced by folding. -/
theorem ker_foldHom (n : ℕ) (R : Type*) [CommRing R] :
    RingHom.ker (foldHom n R).toRingHom = coordinateDifferenceIdeal n R := by
  apply le_antisymm
  · intro p hp
    have h := DFunLike.congr_fun (quotientSection_comp_foldHom n R) p
    have hz : foldHom n R p = 0 := hp
    have hq : Ideal.Quotient.mk (coordinateDifferenceIdeal n R) p = 0 := by
      simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hz, map_zero] using h.symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i,j⟩, rfl⟩
    change foldHom n R ((X (i,j) : SquareRing n R) - X (j,i)) = 0
    simp [foldHom, fold_comm]

theorem foldHom_surjective (n : ℕ) (R : Type*) [CommRing R] :
    Function.Surjective (foldHom n R) := by
  apply MvPolynomial.rename_surjective
  intro e
  refine ⟨entryPair e, ?_⟩
  have he : (entryPair e).2 ≤ (entryPair e).1 := e.property
  apply Subtype.ext
  change toLex (max (entryPair e).1 (entryPair e).2,
    min (entryPair e).1 (entryPair e).2) = e.val
  rw [max_eq_left he, min_eq_right he]
  simpa only [entryPair, Prod.eta] using toLex_ofLex e.val

/-- Folding is unchanged by transposition, as an equality of algebra maps. -/
theorem foldHom_comp_transposeHom (n : ℕ) (R : Type*) [CommRing R] :
    (foldHom n R).comp (transposeHom n R) = foldHom n R := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i,j⟩
  simp [foldHom, transposeHom, fold_comm]

/-- The all-polynomial fixed-locus equations are exactly the entry equations. -/
theorem fixedLocusIdeal_eq_coordinateDifferenceIdeal (n : ℕ)
    (R : Type*) [CommRing R] :
    fixedLocusIdeal n R = coordinateDifferenceIdeal n R := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,rfl⟩
    rw [← ker_foldHom]
    change foldHom n R (p - transposeHom n R p) = 0
    have hp := DFunLike.congr_fun (foldHom_comp_transposeHom n R) p
    simpa only [map_sub, AlgHom.comp_apply] using sub_eq_zero.mpr hp.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨ij,rfl⟩
    exact Ideal.subset_span ⟨X ij, by simp [transposeHom]⟩

/-- The affine scheme-theoretic fixed locus is symmetric affine space over
any commutative base ring, with its full quotient scheme structure. -/
def coordinateRingEquiv (n : ℕ) (R : Type*) [CommRing R] :
    (SquareRing n R ⧸ fixedLocusIdeal n R) ≃ₐ[R] CoordinateRing n R :=
  (Ideal.quotientEquivAlgOfEq R
    ((fixedLocusIdeal_eq_coordinateDifferenceIdeal n R).trans (ker_foldHom n R).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (foldHom_surjective n R))

/-- The quotient isomorphism takes every original entry to its folded variable. -/
@[simp] theorem coordinateRingEquiv_mk (n : ℕ) (R : Type*) [CommRing R]
    (p : SquareRing n R) :
    coordinateRingEquiv n R (Ideal.Quotient.mk (fixedLocusIdeal n R) p) = foldHom n R p := by
  rfl

/-- The nonsymmetric weighted matrix exists before imposing fixed-locus equations. -/
def weightedGenericMatrix (n : ℕ) (R : Type*) [CommRing R] (q : R) :
    Matrix (Fin n) (Fin n) (SquareRing n R) :=
  fun i j => C (q ^ ((i.val + 1) * (j.val + 1))) * X (i,j)

/-- The normalized nonsymmetric determinant, written as its literal
Leibniz sum before any transposed entries are identified.  The already
proved rearrangement inequality makes every exponent nonnegative. -/
def normalizedMinor {n t : ℕ} (a b : Fin t ↪o Fin n) :
    SquareRing n (Polynomial ℤ) :=
  ∑ π : Equiv.Perm (Fin t),
    C (Polynomial.C (signCoefficient ℤ π) *
      Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b)) *
        ∏ p, X (a (π p), b p)

/-- Before imposing symmetry, the permutation sum is the actual weighted
determinant with its normalizing power cleared.  This also verifies that
natural subtraction in its definition has not truncated any exponent. -/
theorem normalizedMinor_normalized_determinant {n t : ℕ} (a b : Fin t ↪o Fin n) :
    C (Polynomial.X ^ Deformation.minorWeight a b) * normalizedMinor a b =
      ((weightedGenericMatrix n (Polynomial ℤ) Polynomial.X).submatrix a b).det := by
  classical
  rw [normalizedMinor, Finset.mul_sum, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro π hπ
  simp only [Matrix.submatrix_apply, weightedGenericMatrix]
  rw [Finset.prod_mul_distrib]
  have hp : (∏ p : Fin t,
      (C (Polynomial.X ^ (((a (π p)).val + 1) * ((b p).val + 1))) :
        SquareRing n (Polynomial ℤ))) =
      C (Polynomial.X ^ Deformation.termWeight a b π) := by
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  have hs : Equiv.Perm.sign π •
      (C (Polynomial.X ^ Deformation.termWeight a b π) *
        ∏ p, (X (a (π p), b p) : SquareRing n (Polynomial ℤ))) =
      C (Polynomial.C (signCoefficient ℤ π)) *
        (C (Polynomial.X ^ Deformation.termWeight a b π) *
          ∏ p, (X (a (π p), b p) : SquareRing n (Polynomial ℤ))) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
      simp [signCoefficient, h, Units.smul_def, neg_one_mul]
    exact (neg_one_mul _).symm
  rw [hs]
  have hbound := Deformation.minorWeight_le_termWeight a b π
  have he : Deformation.minorWeight a b +
      (Deformation.termWeight a b π - Deformation.minorWeight a b) =
        Deformation.termWeight a b π := by omega
  have hpow : (Polynomial.X : Polynomial ℤ) ^ Deformation.minorWeight a b *
      Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b) =
        Polynomial.X ^ Deformation.termWeight a b π := by
    rw [← pow_add, he]
  calc
    C (Polynomial.X ^ Deformation.minorWeight a b) *
        (C (Polynomial.C (signCoefficient ℤ π) *
          Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b)) *
            ∏ p, X (a (π p), b p)) =
      C (Polynomial.C (signCoefficient ℤ π) *
        (Polynomial.X ^ Deformation.minorWeight a b *
          Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b))) *
            ∏ p, X (a (π p), b p) := by
              simp only [map_mul]
              ring
    _ = C (Polynomial.C (signCoefficient ℤ π) *
        Polynomial.X ^ Deformation.termWeight a b π) * ∏ p, X (a (π p), b p) := by
          rw [hpow]
    _ = _ := by rw [map_mul, mul_assoc]

/-- Restriction of the normalized nonsymmetric family is exactly the
normalized symmetric family, with no extra power of the parameter. -/
theorem foldHom_normalizedMinor {n t : ℕ} (a b : Fin t ↪o Fin n) :
    foldHom n (Polynomial ℤ) (normalizedMinor a b) =
      Deformation.minorDeformation a b := by
  classical
  unfold normalizedMinor Deformation.minorDeformation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [map_mul, map_prod]
  simp only [foldHom, rename_C, rename_X]
  change C (Polynomial.C (signCoefficient ℤ π) *
      Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b)) *
      (∏ p, genericMatrix n (Polynomial ℤ) (a (π p)) (b p)) = _
  rw [permutation_product, C_mul_monomial, mul_one]

/-- Restriction takes its actual determinant to the actual weighted symmetric determinant. -/
theorem foldHom_weighted_determinant {n t : ℕ} (R : Type*) [CommRing R]
    (q : R) (a b : Fin t → Fin n) :
    foldHom n R ((weightedGenericMatrix n R q).submatrix a b).det =
      Matrix.det (Matrix.of (fun i j : Fin t =>
        C (q ^ (((a i).val + 1) * ((b j).val + 1))) *
          (X (fold (a i) (b j)) : CoordinateRing n R))) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [weightedGenericMatrix, foldHom]

/-- The displayed normalized symmetric family is exactly the fixed-locus
restriction of the weighted nonsymmetric determinant, with denominator cleared. -/
theorem fixed_locus_normalized_minor {n t : ℕ} (a b : Fin t ↪o Fin n) :
    foldHom n (Polynomial ℤ)
        ((weightedGenericMatrix n (Polynomial ℤ) Polynomial.X).submatrix a b).det =
      C (Polynomial.X ^ Deformation.minorWeight a b) * Deformation.minorDeformation a b := by
  rw [foldHom_weighted_determinant]
  exact (Deformation.minorDeformation_normalized_determinant a b).symm

/-- The paper's two-by-two example, including the repeated off-diagonal entry. -/
theorem two_by_two_deformation :
    Deformation.minorDeformation ((OrderIso.refl (Fin 2)).toOrderEmbedding) ((OrderIso.refl (Fin 2)).toOrderEmbedding) =
      C Polynomial.X * (X (fold (0 : Fin 2) 0) : CoordinateRing 2 (Polynomial ℤ)) *
        X (fold (1 : Fin 2) 1) - X (fold (0 : Fin 2) 1) ^ 2 := by
  have h := Deformation.minorDeformation_normalized_determinant
    ((OrderIso.refl (Fin 2)).toOrderEmbedding) ((OrderIso.refl (Fin 2)).toOrderEmbedding)
  have hw : Deformation.minorWeight ((OrderIso.refl (Fin 2)).toOrderEmbedding)
      ((OrderIso.refl (Fin 2)).toOrderEmbedding) = 4 := by decide
  rw [hw, Matrix.det_fin_two] at h
  change C (Polynomial.X ^ 4) *
      Deformation.minorDeformation ((OrderIso.refl (Fin 2)).toOrderEmbedding)
        ((OrderIso.refl (Fin 2)).toOrderEmbedding) =
    (C (Polynomial.X ^ 1) * X (fold (0 : Fin 2) 0)) *
      (C (Polynomial.X ^ 4) * X (fold (1 : Fin 2) 1)) -
        (C (Polynomial.X ^ 2) * X (fold (0 : Fin 2) 1)) *
          (C (Polynomial.X ^ 2) * X (fold (1 : Fin 2) 0)) at h
  rw [fold_comm (1 : Fin 2) 0] at h
  apply mul_left_cancel₀ (show (C (Polynomial.X ^ 4) : CoordinateRing 2 (Polynomial ℤ)) ≠ 0 by simp)
  rw [h]
  simp only [map_pow]
  ring

/-- At zero the square remains; the special fiber is not replaced by its reduction. -/
theorem two_by_two_special_fiber :
    Deformation.specialization 0
      (Deformation.minorDeformation ((OrderIso.refl (Fin 2)).toOrderEmbedding) ((OrderIso.refl (Fin 2)).toOrderEmbedding)) =
        -(X (fold (0 : Fin 2) 1) : CoordinateRing 2 ℤ) ^ 2 := by
  rw [two_by_two_deformation]
  simp [Deformation.specialization]

end FourPapers.Symmetric.Transpose
end



end
/- End TransposeFixedLocus.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "SupplementaryVerification BEGIN SchurReesNonnormal\n"
  logInfo "SupplementaryVerification BEGIN SchurReesNonnormal"

/- Begin SchurReesNonnormal.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

/-!
# The nonnormal initial algebra after Corollary 7.1

For a symmetric four-by-four matrix and the two-minor symbolic Rees algebra,
the literal element `u₁₂ u₃₄ T` is absent from the initial algebra, its square
belongs to that algebra, and it is a fraction of two algebra elements with
nonzero denominator. The conclusion is the negation of Mathlib's native
`IsIntegrallyClosed` property, over every coefficient field.
-/

namespace FourPapers.Symmetric.Rees.Nonnormal
open MvPolynomial Finsupp

/-- An actual fraction hole with square in a subalgebra contradicts native
integral closedness. The fraction is formed in that subalgebra's own fraction field. -/
theorem not_isIntegrallyClosed_of_square_hole
    {K R : Type*} [CommRing K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (y : R) (hy : y ∉ A)
    (a b c : A) (ha : (a : R) ≠ 0)
    (hab : (a : R) * y = (b : R)) (hyy : y ^ 2 = (c : R)) :
    ¬ IsIntegrallyClosed A := by
  intro hclosed
  letI : IsIntegrallyClosed A := hclosed
  let F := FractionRing A
  let φ := algebraMap A F
  have hinj : Function.Injective φ := IsFractionRing.injective A F
  have haA : a ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have haF : φ a ≠ 0 := by
    intro h
    exact haA (hinj (h.trans (map_zero φ).symm))
  have hrelation : b ^ 2 = a ^ 2 * c := by
    apply Subtype.ext
    change (b : R) ^ 2 = (a : R) ^ 2 * (c : R)
    rw [← hab, ← hyy]
    ring
  have hmap : (φ b) ^ 2 = (φ a) ^ 2 * φ c := by
    simpa only [map_pow, map_mul] using congrArg φ hrelation
  let x : F := φ b / φ a
  have hxpow : x ^ 2 = φ c := by
    change (φ b / φ a) ^ 2 = φ c
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 haF)).mpr
    exact hmap.trans (mul_comm _ _)
  have hxint : IsIntegral A x := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hxpow]
    exact isIntegral_algebraMap
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxint
  change φ z = φ b / φ a at hz
  have hza : z * a = b := by
    apply hinj
    simpa only [map_mul] using (eq_div_iff haF).mp hz
  have hzy : (z : R) = y := by
    apply mul_left_cancel₀ ha
    calc
      (a : R) * (z : R) = (z : R) * (a : R) := mul_comm _ _
      _ = (b : R) := congrArg Subtype.val hza
      _ = (a : R) * y := hab.symm
  exact hy (hzy ▸ z.property)

/-- The independent symmetric coordinates denoted `u₁₂` and `u₃₄` in the paper. -/
def edge12 : Entry 4 := fold 0 1
def edge34 : Entry 4 := fold 2 3

def holeExponent : Entry 4 →₀ ℕ := single edge12 1 + single edge34 1

private theorem sort_two {α : Type*} [LinearOrder α] (a b : α) (hab : a ≤ b) :
    (a ::ₘ ({b} : Multiset α)).sort (· ≤ ·) = [a,b] := by
  rw [Multiset.sort_cons (a := a) (s := {b}) (r := (· ≤ ·)) (by simpa using hab),
    Multiset.sort_singleton]

private theorem monomialPairs_single_two (e : Entry 4) :
    monomialPairs (single e 2) = [(e.val.2, e.val.1), (e.val.2, e.val.1)] := by
  have hm : (single e 2 : Entry 4 →₀ ℕ).toMultiset = e ::ₘ {e} := by
    rw [Finsupp.toMultiset_single, two_nsmul, Multiset.singleton_add]
  have hs := (congrArg (fun s : Multiset (Entry 4) => s.sort (· ≤ ·)) hm).trans
    (sort_two e e le_rfl)
  exact congrArg (List.map fun a : Entry 4 => ((ofLex a.val).2, (ofLex a.val).1)) hs

private theorem monomialPairs_hole :
    monomialPairs holeExponent = [(0,1),(2,3)] := by
  have hle : edge12 ≤ edge34 := by decide
  have hm : holeExponent.toMultiset = edge12 ::ₘ {edge34} := by
    rw [holeExponent, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
      Finsupp.toMultiset_single, one_nsmul, one_nsmul, Multiset.singleton_add]
  have hs := (congrArg (fun s : Multiset (Entry 4) => s.sort (· ≤ ·)) hm).trans
    (sort_two edge12 edge34 hle)
  exact congrArg (List.map fun a : Entry 4 => ((ofLex a.val).2, (ofLex a.val).1)) hs

/-- The actual insertion tableau of `u₁₂ u₃₄` is one row of length four. -/
theorem pairedTableau_hole : pairedTableau holeExponent = [[0,1,2,3]] := by
  rw [pairedTableau, monomialPairs_hole]
  rfl

@[simp] theorem gamma_hole : gamma 2 holeExponent = 0 := by
  rw [gamma, halfShape, pairedTableau_hole]
  rfl

@[simp] theorem gamma_edge12_square : gamma 2 (single edge12 2) = 1 := by
  rw [gamma, halfShape, pairedTableau, monomialPairs_single_two]
  rfl

@[simp] theorem gamma_edge34_square : gamma 2 (single edge34 2) = 1 := by
  rw [gamma, halfShape, pairedTableau, monomialPairs_single_two]
  rfl

/-- The actual initial algebra in the paper's example. -/
def initialAlgebra42 (K : Type*) [Field K] :
    Subalgebra K (Polynomial (CoordinateRing 4 K)) :=
  initialAlgebra (foldedOrder 4) (determinantalSymbolicRees 4 K 2 (by decide))

private theorem monomial_mem_initialAlgebra42_iff (K : Type*) [Field K]
    (e : Entry 4 →₀ ℕ) (s : ℕ) :
    Polynomial.monomial s (monomial e (1 : K)) ∈ initialAlgebra42 K ↔
      s ≤ gamma 2 e := by
  classical
  rw [initialAlgebra42, mem_initialSymbolicRees_iff_gamma 4 K 2 (by decide) (by decide)]
  constructor
  · intro h
    exact h s e (by simp [MvPolynomial.support_monomial])
  · intro h q d hd
    by_cases hq : s = q
    · subst q
      have hde : d = e := by simpa [MvPolynomial.support_monomial] using hd
      simpa only [hde] using h
    · simp [Polynomial.coeff_monomial, hq, Ne.symm hq] at hd

private theorem C_mem_initialAlgebra42 (K : Type*) [Field K] (f : CoordinateRing 4 K) :
    Polynomial.C f ∈ initialAlgebra42 K := by
  rw [initialAlgebra42, mem_initialSymbolicRees_iff_gamma 4 K 2 (by decide) (by decide)]
  intro s e he
  by_cases hs : s = 0
  · subst s
    exact Nat.zero_le _
  · simp [Polynomial.coeff_C, hs, Ne.symm hs] at he

/-- The literal missing element `u₁₂ u₃₄ T`. -/
def hole (K : Type*) [Field K] : Polynomial (CoordinateRing 4 K) :=
  Polynomial.C (X edge12 * X edge34) * Polynomial.X

theorem hole_eq_monomial (K : Type*) [Field K] :
    hole K = Polynomial.monomial 1 (monomial holeExponent (1 : K)) := by
  have hm : monomial holeExponent (1 : K) = X edge12 * X edge34 := by
    rw [holeExponent, MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial]
    simp only [pow_one]
  rw [hm, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [hole, pow_one]

theorem hole_not_mem (K : Type*) [Field K] : hole K ∉ initialAlgebra42 K := by
  rw [hole_eq_monomial, monomial_mem_initialAlgebra42_iff, gamma_hole]
  omega

private theorem edge12_square_mem (K : Type*) [Field K] :
    Polynomial.monomial 1 ((X edge12 : CoordinateRing 4 K) ^ 2) ∈ initialAlgebra42 K := by
  rw [MvPolynomial.X_pow_eq_monomial, monomial_mem_initialAlgebra42_iff]
  simp only [gamma_edge12_square, le_refl]

private theorem edge34_square_mem (K : Type*) [Field K] :
    Polynomial.monomial 1 ((X edge34 : CoordinateRing 4 K) ^ 2) ∈ initialAlgebra42 K := by
  rw [MvPolynomial.X_pow_eq_monomial, monomial_mem_initialAlgebra42_iff]
  simp only [gamma_edge34_square, le_refl]

/-- The square of the missing element belongs to the actual initial algebra. -/
theorem hole_square_mem (K : Type*) [Field K] :
    hole K ^ 2 ∈ initialAlgebra42 K := by
  have heq : hole K ^ 2 =
      Polynomial.monomial 1 ((X edge12 : CoordinateRing 4 K) ^ 2) *
        Polynomial.monomial 1 ((X edge34 : CoordinateRing 4 K) ^ 2) := by
    simp only [hole, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, map_mul, map_pow]
    ring
  rw [heq]
  exact (initialAlgebra42 K).mul_mem (edge12_square_mem K) (edge34_square_mem K)

/-- The illustrative claim following Corollary 7.1, over every field:
this actual initial symbolic Rees algebra is not integrally closed. -/
theorem initial_symbolic_rees_not_integrallyClosed (K : Type*) [Field K] :
    ¬ IsIntegrallyClosed (initialAlgebra42 K) := by
  let A := initialAlgebra42 K
  let p : A := ⟨Polynomial.monomial 1 ((X edge12 : CoordinateRing 4 K) ^ 2),
    edge12_square_mem K⟩
  let a : A := ⟨Polynomial.C (X edge12), C_mem_initialAlgebra42 K _⟩
  let d : A := ⟨Polynomial.C (X edge34), C_mem_initialAlgebra42 K _⟩
  let b : A := p * d
  let c : A := ⟨hole K ^ 2, hole_square_mem K⟩
  apply not_isIntegrallyClosed_of_square_hole A (hole K) (hole_not_mem K) a b c
  · change Polynomial.C (X edge12 : CoordinateRing 4 K) ≠ 0
    exact Polynomial.C_ne_zero.mpr (MvPolynomial.X_ne_zero edge12)
  · change Polynomial.C (X edge12) * hole K =
      Polynomial.monomial 1 ((X edge12 : CoordinateRing 4 K) ^ 2) * Polynomial.C (X edge34)
    simp only [hole, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, map_mul, map_pow]
    ring
  · rfl

end FourPapers.Symmetric.Rees.Nonnormal
end

end
/- End SchurReesNonnormal.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "SupplementaryVerification BEGIN SchurMathlibCorrespondence\n"
  logInfo "SupplementaryVerification BEGIN SchurMathlibCorrespondence"

/- Begin SchurMathlibCorrespondence.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.Symmetric.Schur
open scoped BigOperators
open MvPolynomial

/-- Mathlib's usual semistandard tableaux, with precisely the finite alphabet
used by the paper (zero-based in Lean). -/
def BoundedMathlibTableaux (n : ℕ) (μ : YoungDiagram) :=
  {S : SemistandardYoungTableau μ // ∀ c : ↥μ.cells, S c.val.1 c.val.2 < n}

namespace ShapeTableaux
variable {n : ℕ} {μ : YoungDiagram}

/-- Extend the actual cell entries by zero outside the Young diagram. -/
def toMathlib (T : ShapeTableaux n μ) : SemistandardYoungTableau μ where
  entry i j := if h : (i,j) ∈ μ then (T.cell ⟨(i,j),h⟩).val else 0
  row_weak' hj hc := by
    rw [dif_pos hc, dif_pos (μ.up_left_mem le_rfl hj.le hc)]
    exact (weakFillingOfRows T.property.1 T.property.2.1).row_mono hj hc
  col_strict' hi hc := by
    rw [dif_pos hc, dif_pos (μ.up_left_mem hi.le le_rfl hc)]
    exact (weakFillingOfRows T.property.1 T.property.2.1).col_strict hi hc
  zeros' hn := dif_neg hn

@[simp] theorem toMathlib_apply_cell (T : ShapeTableaux n μ) (c : ↥μ.cells) :
    T.toMathlib c.val.1 c.val.2 = (T.cell c).val := by
  change (if h : (c.val.1,c.val.2) ∈ μ then _ else 0) = _
  exact dif_pos (show (c.val.1,c.val.2) ∈ μ from c.property)

def toBoundedMathlib (T : ShapeTableaux n μ) : BoundedMathlibTableaux n μ :=
  ⟨T.toMathlib, fun c => by rw [T.toMathlib_apply_cell c]; exact (T.cell c).isLt⟩

end ShapeTableaux

/-- Read Mathlib's filling row by row, retaining every repeated label. -/
def mathlibRows {μ : YoungDiagram} (S : SemistandardYoungTableau μ) : List (List ℕ) :=
  List.ofFn fun i : Fin (μ.colLen 0) =>
    List.ofFn fun j : Fin (μ.rowLen i.val) => S i.val j.val

theorem mathlibRows_shape {μ : YoungDiagram} (S : SemistandardYoungTableau μ) :
    (mathlibRows S).map List.length = μ.rowLens := by
  simp [mathlibRows, YoungDiagram.rowLens, ← List.ofFn_getElem_eq_map]

theorem mathlibRows_isTableauRows {μ : YoungDiagram} (S : SemistandardYoungTableau μ) :
    (mathlibRows S).IsTableauRows := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mathlibRows, List.mem_ofFn]
    rintro ⟨i, hi⟩
    have hpos : 0 < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)
    have hh := congrArg List.length hi
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  · simp only [mathlibRows, List.forall_mem_ofFn_iff]
    intro i
    apply List.sortedLE_iff_pairwise.mpr
    apply List.pairwise_ofFn.mpr
    intro j k hjk
    exact S.row_weak (Fin.lt_def.mp hjk) (YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt)
  · apply List.Pairwise.isChain
    simp only [mathlibRows, List.pairwise_ofFn]
    intro i k hik
    refine ⟨by simpa using μ.rowLen_anti i k (Fin.le_def.mp hik.le), ?_⟩
    intro j hu hl
    simp only [List.length_ofFn] at hu hl
    simpa using S.col_strict (Fin.lt_def.mp hik) (YoungDiagram.mem_iff_lt_rowLen.mpr hl)

def ofBoundedMathlib {n : ℕ} {μ : YoungDiagram}
    (S : BoundedMathlibTableaux n μ) : ShapeTableaux n μ :=
  ⟨mathlibRows S.val, mathlibRows_isTableauRows S.val, mathlibRows_shape S.val, by
    intro x hx
    obtain ⟨row, hrow, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact S.property ⟨(i.val,j.val), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩⟩

@[simp] theorem ofBoundedMathlib_cell {n : ℕ} {μ : YoungDiagram}
    (S : BoundedMathlibTableaux n μ) (c : ↥μ.cells) :
    ((ofBoundedMathlib S).cell c).val = S.val c.val.1 c.val.2 := by
  simp only [ofBoundedMathlib, ShapeTableaux.cell, rowsCellEntry, mathlibRows,
    List.getElem_ofFn]

/-- A literal equivalence with the independent Mathlib tableau type. -/
def shapeTableauEquivMathlib (n : ℕ) (μ : YoungDiagram) :
    ShapeTableaux n μ ≃ BoundedMathlibTableaux n μ where
  toFun := ShapeTableaux.toBoundedMathlib
  invFun := ofBoundedMathlib
  left_inv T := by
    apply ShapeTableaux.cell_injective
    funext c
    apply Fin.ext
    rw [ofBoundedMathlib_cell]
    exact T.toMathlib_apply_cell c
  right_inv S := by
    apply Subtype.ext
    apply SemistandardYoungTableau.ext
    intro i j
    change (ofBoundedMathlib S).toMathlib i j = S.val i j
    by_cases hc : (i,j) ∈ μ
    · rw [ShapeTableaux.toMathlib_apply_cell _ ⟨(i,j),hc⟩,
        ofBoundedMathlib_cell]
    · rw [(ofBoundedMathlib S).toMathlib.zeros hc, S.val.zeros hc]

noncomputable instance (n : ℕ) (μ : YoungDiagram) :
    Fintype (BoundedMathlibTableaux n μ) :=
  Fintype.ofEquiv (ShapeTableaux n μ) (shapeTableauEquivMathlib n μ)

/-- The Schur polynomial is equally the ordinary content generating sum
over Mathlib's semistandard tableaux of the prescribed shape. -/
theorem schurPolynomial_eq_mathlibTableauSum (n : ℕ) (μ : YoungDiagram) :
    schurPolynomial n μ =
      ∑ S : BoundedMathlibTableaux n μ, monomial (rowContent n (mathlibRows S.val)) 1 := by
  classical
  change (∑ T : ShapeTableaux n μ, monomial (rowContent n T.val) 1) =
    ∑ S : BoundedMathlibTableaux n μ,
      monomial (rowContent n ((shapeTableauEquivMathlib n μ).symm S).val) 1
  exact ((shapeTableauEquivMathlib n μ).symm.sum_comp
    (fun T => monomial (rowContent n T.val) (1 : ℕ))).symm

end FourPapers.Symmetric.Schur
end

end
/- End SchurMathlibCorrespondence.lean -/

#print axioms MonomialOrder.IsGroebnerBasis.changeOrder_of_degree_eq
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_field_groebner
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_field_initial
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_groebner_after_baseChange
#print axioms FourPapers.Symmetric.OrderTransfer.standard_basis_after_baseChange
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_initial_after_baseChange
#print axioms FourPapers.Symmetric.OrderTransfer.integral_standardMonomials_eq
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_groebner_of_selects
#print axioms FourPapers.Symmetric.OrderTransfer.mixed_initial_of_selects
#print axioms FourPapers.Symmetric.OrderTransfer.standard_basis_of_selects
#print axioms FourPapers.Symmetric.Transpose.ker_foldHom
#print axioms FourPapers.Symmetric.Transpose.coordinateRingEquiv
#print axioms FourPapers.Symmetric.Transpose.fixed_locus_normalized_minor
#print axioms FourPapers.Symmetric.Transpose.two_by_two_deformation
#print axioms FourPapers.Symmetric.Transpose.two_by_two_special_fiber
#print axioms FourPapers.Symmetric.Transpose.foldHom_normalizedMinor
#print axioms FourPapers.Symmetric.Transpose.normalizedMinor_normalized_determinant
#print axioms FourPapers.Symmetric.Rees.Nonnormal.pairedTableau_hole
#print axioms FourPapers.Symmetric.Rees.Nonnormal.hole_not_mem
#print axioms FourPapers.Symmetric.Rees.Nonnormal.hole_square_mem
#print axioms FourPapers.Symmetric.Rees.Nonnormal.initial_symbolic_rees_not_integrallyClosed
#print axioms FourPapers.Symmetric.Schur.shapeTableauEquivMathlib
#print axioms FourPapers.Symmetric.Schur.schurPolynomial_eq_mathlibTableauSum

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "MonomialOrder.IsGroebnerBasis.changeOrder_of_degree_eq".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_field_groebner".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_field_initial".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_groebner_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.standard_basis_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_initial_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.integral_standardMonomials_eq".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_groebner_of_selects".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_initial_of_selects".toName,
    "FourPapers.Symmetric.OrderTransfer.standard_basis_of_selects".toName,
    "FourPapers.Symmetric.Transpose.ker_foldHom".toName,
    "FourPapers.Symmetric.Transpose.coordinateRingEquiv".toName,
    "FourPapers.Symmetric.Transpose.fixed_locus_normalized_minor".toName,
    "FourPapers.Symmetric.Transpose.two_by_two_deformation".toName,
    "FourPapers.Symmetric.Transpose.two_by_two_special_fiber".toName,
    "FourPapers.Symmetric.Transpose.foldHom_normalizedMinor".toName,
    "FourPapers.Symmetric.Transpose.normalizedMinor_normalized_determinant".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.pairedTableau_hole".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.hole_not_mem".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.hole_square_mem".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.initial_symbolic_rees_not_integrallyClosed".toName,
    "FourPapers.Symmetric.Schur.shapeTableauEquivMathlib".toName,
    "FourPapers.Symmetric.Schur.schurPolynomial_eq_mathlibTableauSum".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/supplementary_dependency_graph.json" (Json.compress graph)
  logInfo m!"SUPPLEMENTARY_VERIFICATION_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."

