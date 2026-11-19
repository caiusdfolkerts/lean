module
public import shared_results.part023
public import paper_results.part005
public import paper_results.dimension_core
public import shared_results.part003
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import paper_results.part002
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import paper_results.ordinary_ideal_tor_bounds
public import graph_foundation.part010
public import paper_results.transfer_formulas
public import paper_results.theorem81_analytic_spread
public import paper_results.torsion_core
public import paper_results.graded_homology_core
public import Mathlib.Algebra.CharP.Basic
public import graph_foundation.part009
public import paper_results.part003
public import paper_results.part004
public import graph_foundation.part008
public import paper_results.part001
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTotalHomologyDimension -/
section

/-! # Total quotient-face homology and the actual graded Betti table

The total complex is split by exterior degree. Its degree-zero summand is
retained, and the natural and integer gradings are compared explicitly.
This permits comparison of dimensions over different coefficient fields.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FilteredHomology GradedHomologyDecomposition
open scoped DirectSum
universe u
section Ring
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotientTotal_basis_zero (B : Family V) (α : Exponent V)
    (F : {F // quotientKoszulFaces B α F}) (hF : F.val.card = 0) :
    quotientTotalDifferential (k := k) B α (totalFaceBasis _ F) = 0 := by
  apply quotientTotalDifferential_zero_degree
  rw [totalFacePiece_eq_basis_span, ← hF]
  exact Grading.basis_mem_piece _ _ F

lemma quotientTotal_basis_lower (B : Family V) (α : Exponent V)
    (F : {F // quotientKoszulFaces B α F}) :
    quotientTotalDifferential (k := k) B α (totalFaceBasis _ F) ∈
      Grading.Piece (totalFaceBasis (quotientKoszulFaces B α))
        (fun G => G.val.card) (F.val.card - 1) := by
  by_cases hF : F.val.card = 0
  · rw [quotientTotal_basis_zero B α F hF]; exact Submodule.zero_mem _
  · obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hF
    rw [hp, Nat.succ_sub_one]
    change _ ∈ Submodule.span k ((totalFaceBasis (quotientKoszulFaces B α)) '' {G | G.val.card = p})
    rw [← totalFacePiece_eq_basis_span]
    apply quotientTotalDifferential_lowers
    rw [totalFacePiece_eq_basis_span]
    exact Submodule.subset_span ⟨F, hp, rfl⟩

abbrev QuotientTotalHomology (B : Family V) (α : Exponent V) :=
  Homology (quotientTotalDifferential (k := k) B α) (quotientTotalDifferential B α)
    (quotientTotalDifferential_comp B α)

abbrev QuotientIntegerHomology (B : Family V) (α : Exponent V) (p : ℤ) :=
  NaturalHomologyDecomposition.IntegerHomology
    (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α) p

def quotientTotalCoordinates (B : Family V) (α : Exponent V) (p : ℕ) :
    totalFacePiece (k := k) (quotientKoszulFaces B α) p ≃ₗ[k] quotientPiece (k := k) B α p :=
  (totalFacePieceEquiv (quotientKoszulFaces B α) p).trans (quotientFaceHomogeneousEquiv B α p)

attribute [local irreducible] quotientFaceDifferential quotientFaceHomogeneousEquiv quotientHomogeneousDifferential

lemma quotientTotalCoordinates_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (x : totalFacePiece (k := k) (quotientKoszulFaces B α) (p+1)) :
    quotientTotalCoordinates B α p ⟨quotientTotalDifferential B α x.val,
      quotientTotalDifferential_lowers B α p x.val x.property⟩ =
      quotientHomogeneousDifferential B α p (quotientTotalCoordinates B α (p+1) x) := by
  have he : totalFacePieceEquiv (quotientKoszulFaces B α) p
      ⟨quotientTotalDifferential B α x.val, quotientTotalDifferential_lowers B α p x.val x.property⟩ =
      quotientFaceDifferential B α p (totalFacePieceEquiv (quotientKoszulFaces B α) (p+1) x) := by
    apply Subtype.ext
    change quotientFaceProjection (k := k) B α (Simplicial.boundary x.val.val) =
      (quotientFaceDifferential (k := k) B α p ⟨x.val.val,x.property⟩).val
    exact (quotientFaceDifferential_val (k := k) B α p ⟨x.val.val,x.property⟩).symm
  change quotientFaceHomogeneousEquiv B α p (totalFacePieceEquiv _ p _) = _
  rw [he]
  exact (quotientFaceHomogeneousEquiv_differential B α p _).symm

def quotientNaturalToTotal (B : Family V) (α : Exponent V) (p : ℕ) :
    Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card) p ≃ₗ[k]
      totalFacePiece (k := k) (quotientKoszulFaces B α) p :=
  LinearEquiv.ofEq _ _ (totalFacePiece_eq_basis_span (quotientKoszulFaces B α) p).symm

def quotientNaturalCoordinates (B : Family V) (α : Exponent V) (p : ℕ) :
    Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card) p ≃ₗ[k]
      quotientPiece (k := k) B α p :=
  (quotientNaturalToTotal B α p).trans (quotientTotalCoordinates B α p)

lemma quotientNaturalToTotal_val (B : Family V) (α : Exponent V) (p : ℕ)
    (x : Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) p) :
    (quotientNaturalToTotal B α p x).val = x.val := rfl

lemma quotientNaturalCoordinates_apply (B : Family V) (α : Exponent V) (p : ℕ)
    (x : Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) p) :
    quotientNaturalCoordinates B α p x =
      quotientTotalCoordinates B α p (quotientNaturalToTotal B α p x) := rfl

def quotientFineToTotal (B : Family V) (α : Exponent V) (p : ℕ) :
    quotientPiece (k := k) B α p →ₗ[k] TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
  (totalFacePiece (quotientKoszulFaces B α) p).subtype.comp
    (quotientTotalCoordinates B α p).symm.toLinearMap

lemma quotientFineToTotal_injective (B : Family V) (α : Exponent V) (p : ℕ) :
    Function.Injective (quotientFineToTotal (k := k) B α p) :=
  Subtype.val_injective.comp (quotientTotalCoordinates B α p).symm.injective

lemma quotientFineToTotal_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (x : totalFacePiece (k := k) (quotientKoszulFaces B α) (p+1)) :
    quotientFineToTotal B α p
        (quotientHomogeneousDifferential B α p (quotientTotalCoordinates B α (p+1) x)) =
      quotientTotalDifferential B α x.val := by
  rw [← quotientTotalCoordinates_differential B α p x]
  simp only [quotientFineToTotal, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply]

lemma quotientNaturalIncoming_compat (B : Family V) (α : Exponent V) (p : ℕ)
    (x : Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) (p+1)) :
    quotientNaturalCoordinates (k := k) B α p
      (NaturalHomologyDecomposition.incoming (R := k)
        (totalFaceBasis (k := k) (quotientKoszulFaces B α))
        (fun F => F.val.card) (quotientTotalDifferential (k := k) B α)
        (quotientTotal_basis_lower (k := k) B α) p x) =
      quotientHomogeneousDifferential (k := k) B α p
        (quotientNaturalCoordinates (k := k) B α (p+1) x) := by
  rw [quotientNaturalCoordinates_apply, quotientNaturalCoordinates_apply]
  have hpiece : quotientNaturalToTotal (k := k) B α p
      (NaturalHomologyDecomposition.incoming (R := k)
        (totalFaceBasis (k := k) (quotientKoszulFaces B α))
        (fun F => F.val.card) (quotientTotalDifferential (k := k) B α)
        (quotientTotal_basis_lower (k := k) B α) p x) =
      ⟨quotientTotalDifferential B α (quotientNaturalToTotal B α (p+1) x).val,
        quotientTotalDifferential_lowers B α p _
          (quotientNaturalToTotal B α (p+1) x).property⟩ := by
    apply Subtype.ext
    simp only [quotientNaturalToTotal_val]
    rfl
  rw [hpiece]
  exact quotientTotalCoordinates_differential B α p (quotientNaturalToTotal B α (p+1) x)

lemma quotientNaturalOutgoing_compat (B : Family V) (α : Exponent V) (p : ℕ)
    (x : Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) p) :
    NaturalHomologyDecomposition.outgoing (R := k)
        (totalFaceBasis (k := k) (quotientKoszulFaces B α))
        (fun F => F.val.card) (quotientTotalDifferential (k := k) B α) p x =
      quotientFineToTotal (k := k) B α p.pred
        (quotientFinePrevious (k := k) B α p (quotientNaturalCoordinates (k := k) B α p x)) := by
  cases p with
  | zero =>
      simp only [quotientFinePrevious, LinearMap.zero_apply, map_zero]
      change quotientTotalDifferential B α x.val = 0
      exact quotientTotalDifferential_zero_degree B α x.val
        (quotientNaturalToTotal B α 0 x).property
  | succ p =>
      change quotientTotalDifferential B α x.val =
        quotientFineToTotal B α p
          (quotientHomogeneousDifferential B α p (quotientNaturalCoordinates B α (p+1) x))
      rw [quotientNaturalCoordinates_apply, quotientFineToTotal_differential,
        quotientNaturalToTotal_val]

attribute [local irreducible] quotientNaturalCoordinates quotientTotalCoordinates
  quotientFineToTotal NaturalHomologyDecomposition.incoming NaturalHomologyDecomposition.outgoing

/-- The natural three-term model is the actual fine Koszul homology at p. -/
def quotientNaturalHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    NaturalHomologyDecomposition.NaturalHomology
      (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
      (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α)
      (quotientTotal_basis_lower B α) p ≃ₗ[k] quotientFineHomologyAt (k := k) B α p :=
  NaturalHomologyDecomposition.homologyEquivOfCoordinates
    (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α)
    (quotientTotal_basis_lower B α) p
    (quotientHomogeneousDifferential B α p) (quotientFinePrevious B α p)
    (quotientFineDifferential_comp B α p) (quotientFineToTotal B α p.pred)
    (quotientFineToTotal_injective B α p.pred)
    (quotientNaturalCoordinates B α (p+1)) (quotientNaturalCoordinates B α p)
    (quotientNaturalIncoming_compat B α p) (quotientNaturalOutgoing_compat B α p)

/-- The actual total quotient-face homology decomposes by all integer degrees. -/
def quotientTotalHomologyDecomposition (B : Family V) (α : Exponent V) :
    QuotientTotalHomology (k := k) B α ≃ₗ[k] ⨁ p : ℤ, QuotientIntegerHomology (k := k) B α p :=
  NaturalHomologyDecomposition.totalHomologyDecomposition
    (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α)
    (quotientTotal_basis_lower B α) (quotientTotal_basis_zero B α)

end Ring
section Field
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance quotientTotalHomology_finite (B : Family V) (α : Exponent V) :
    Module.Finite k (QuotientTotalHomology (k := k) B α) := by
  letI := Module.Finite.of_basis (totalFaceBasis (k := k) (quotientKoszulFaces B α))
  unfold QuotientTotalHomology Homology
  infer_instance

instance quotientIntegerHomology_finite (B : Family V) (α : Exponent V) (p : ℤ) :
    Module.Finite k (QuotientIntegerHomology (k := k) B α p) := by
  letI := Module.Finite.of_basis (totalFaceBasis (k := k) (quotientKoszulFaces B α))
  unfold QuotientIntegerHomology NaturalHomologyDecomposition.IntegerHomology DegreeHomology
  infer_instance

lemma quotientIntegerHomology_finrank (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.finrank k (QuotientIntegerHomology (k := k) B α (p : ℤ)) =
      quotientBettiNumber (k := k) B α p := by
  let e := NaturalHomologyDecomposition.naturalHomologyEquiv
    (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α)
    (quotientTotal_basis_lower B α) (quotientTotal_basis_zero B α) p
  exact (e.symm.trans (quotientNaturalHomologyEquiv B α p)).finrank_eq.trans
    (quotientFineHomologyAt_finrank B α p)

lemma quotientIntegerHomology_finrank_negative (B : Family V) (α : Exponent V)
    (p : ℤ) (hp : p < 0) : Module.finrank k (QuotientIntegerHomology (k := k) B α p) = 0 := by
  letI := NaturalHomologyDecomposition.integerHomology_negative
    (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α) p hp
  exact Module.finrank_zero_of_subsingleton

instance quotientIntegerHomology_directSum_finite (B : Family V) (α : Exponent V) :
    Module.Finite k (⨁ p : ℤ, QuotientIntegerHomology (k := k) B α p) :=
  Module.Finite.equiv (quotientTotalHomologyDecomposition (k := k) B α)

end Field
section CompareFields
variable {V K L : Type u} [Fintype V] [LinearOrder V] [Field K] [Field L]

/-- Equality of every actual fine Betti entry gives equality of total dimensions. -/
theorem quotientTotalHomology_finrank_eq_of_betti_eq (B : Family V) (α : Exponent V)
    (h : ∀ p, quotientBettiNumber (k := K) B α p = quotientBettiNumber (k := L) B α p) :
    Module.finrank K (QuotientTotalHomology (k := K) B α) =
      Module.finrank L (QuotientTotalHomology (k := L) B α) := by
  rw [(quotientTotalHomologyDecomposition (k := K) B α).finrank_eq,
    (quotientTotalHomologyDecomposition (k := L) B α).finrank_eq]
  apply finrank_directSum_eq_of_components
  intro p
  by_cases hp : 0 ≤ p
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [quotientIntegerHomology_finrank, quotientIntegerHomology_finrank, h q]
  · rw [quotientIntegerHomology_finrank_negative B α p (lt_of_not_ge hp),
      quotientIntegerHomology_finrank_negative B α p (lt_of_not_ge hp)]

/-- A componentwise nonnegative characteristic excess cannot cancel in total. -/
theorem quotientBetti_eq_of_totalHomology_finrank_eq (B : Family V) (α : Exponent V)
    (hle : ∀ p, quotientBettiNumber (k := K) B α p ≤ quotientBettiNumber (k := L) B α p)
    (htotal : Module.finrank K (QuotientTotalHomology (k := K) B α) =
      Module.finrank L (QuotientTotalHomology (k := L) B α)) :
    ∀ p, quotientBettiNumber (k := K) B α p = quotientBettiNumber (k := L) B α p := by
  have hs : Module.finrank K (⨁ p : ℤ, QuotientIntegerHomology (k := K) B α p) =
      Module.finrank L (⨁ p : ℤ, QuotientIntegerHomology (k := L) B α p) := by
    rw [← (quotientTotalHomologyDecomposition (k := K) B α).finrank_eq,
      ← (quotientTotalHomologyDecomposition (k := L) B α).finrank_eq]
    exact htotal
  have hi (p : ℤ) : Module.finrank K (QuotientIntegerHomology (k := K) B α p) ≤
      Module.finrank L (QuotientIntegerHomology (k := L) B α p) := by
    by_cases hp : 0 ≤ p
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      rw [quotientIntegerHomology_finrank, quotientIntegerHomology_finrank]
      exact hle q
    · rw [quotientIntegerHomology_finrank_negative B α p (lt_of_not_ge hp),
        quotientIntegerHomology_finrank_negative B α p (lt_of_not_ge hp)]
  have he := component_finrank_eq_of_total_eq
    (fun p : ℤ => QuotientIntegerHomology (k := K) B α p)
    (fun p : ℤ => QuotientIntegerHomology (k := L) B α p) hi hs
  intro p
  simpa only [quotientIntegerHomology_finrank] using he (p : ℤ)

end CompareFields
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientIntegerHomology_finrank

end
end
end


end
