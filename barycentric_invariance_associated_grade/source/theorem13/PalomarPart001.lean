module

public import theorem13.PalomarPart000
import all theorem13.PalomarPart000
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false


-- Restore the original anonymous enclosing source scopes at this boundary.
section
section
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false
/- BEGIN IntegralCoherentComparison.lean -/
section

/-! # A single integral coherent comparison and all its coefficient changes

The maps over an arbitrary ring are defined by extending the actual integral
matrix in the standard bases. Consequently their scalar naturality is a
theorem about the usual coefficient maps, not an additional hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def integralStalkComparison (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) :
    BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p :=
  integralEquivExtension
    (barycentricStalkStandardBasis ℤ hs p) (barycentricStalkStandardBasis K hs p)
    (polynomialStandardBasis (K := ℤ) hs p) (polynomialStandardBasis (K := K) hs p)
    (booleanCoefficientChange (Int.castRingHom K)) (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p)
    (polynomialCoefficientChange_standardBasis hs (Int.castRingHom K) p) e

theorem integralStalkComparison_commutes (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk ℤ p) :
    integralStalkComparison K hs p e (booleanCoefficientChange (Int.castRingHom K) x) =
      polynomialCoefficientChange (Int.castRingHom K) (e x) := by
  rw [integralStalkComparison, integralEquivExtension_apply]
  exact integralLinearExtension_commutes
    (barycentricStalkStandardBasis ℤ hs p) (barycentricStalkStandardBasis K hs p)
    (booleanCoefficientChange (Int.castRingHom K)) (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p) e.toLinearMap x

@[simp] theorem integralStalkComparison_basis (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (a : StandardInside p) :
    integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a) =
      polynomialCoefficientChange (Int.castRingHom K) (e (barycentricStalkStandardBasis ℤ hs p a)) := by
  rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a]
  exact integralStalkComparison_commutes K hs p e _

def integralCoherentComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ)) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component p := integralStalkComparison K hs p (e.component p)
  naturality p q hqp x := by
    have hf : (polynomialRestriction K hqp).toLinearMap.comp
        (integralStalkComparison K hs p (e.component p)).toLinearMap =
        (integralStalkComparison K hs q (e.component q)).toLinearMap.comp
          (booleanRestriction (K := K) (faceVertexInclusion hqp)).toLinearMap := by
      apply (barycentricStalkStandardBasis K hs p).ext
      intro a
      change polynomialRestriction K hqp
        (integralStalkComparison K hs p (e.component p) (barycentricStalkStandardBasis K hs p a)) =
        integralStalkComparison K hs q (e.component q)
          (booleanRestriction (faceVertexInclusion hqp) (barycentricStalkStandardBasis K hs p a))
      rw [integralStalkComparison_basis,
        ← polynomialCoefficientChange_restriction (Int.castRingHom K) hqp]
      have hn := e.naturality p q hqp (barycentricStalkStandardBasis ℤ hs p a)
      change polynomialRestriction ℤ hqp (e.component p (barycentricStalkStandardBasis ℤ hs p a)) =
        e.component q (booleanRestriction (faceVertexInclusion hqp)
          (barycentricStalkStandardBasis ℤ hs p a)) at hn
      rw [hn, ← integralStalkComparison_commutes,
        booleanCoefficientChange_restriction, booleanCoefficientChange_standardBasis]
    exact DFunLike.congr_fun hf x

theorem integralStalkComparison_leading (d : ℕ) (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : HasStandardLeading ℤ hs d p e.toLinearMap) :
    HasStandardLeading K hs d p (integralStalkComparison K hs p e).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a))).val b = _
  rw [integralStalkComparison_basis, polynomialCoefficientChange_coordinates]
  have hh := he a b hab
  change (polynomialStandardCoordinates ℤ hs p
    (e (barycentricStalkStandardBasis ℤ hs p a))).val b = _ at hh
  rw [hh]
  split_ifs <;> simp

theorem integralStalkComparison_degree (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : HasStandardDegree ℤ hs p e.toLinearMap) :
    HasStandardDegree K hs p (integralStalkComparison K hs p e).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a))).val b = 0
  rw [integralStalkComparison_basis, polynomialCoefficientChange_coordinates]
  have hh := he a b hab
  change (polynomialStandardCoordinates ℤ hs p
    (e (barycentricStalkStandardBasis ℤ hs p a))).val b = 0 at hh
  rw [hh, map_zero]

theorem integralStalkComparison_parameters (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : ∀ i : ℕ, ∀ x : BarycentricStalk ℤ p,
      e (booleanRankParameter (i + 1) * x) = polynomialParameter ℤ p (i + 1) * e x)
    (i : ℕ) (x : BarycentricStalk K p) :
    integralStalkComparison K hs p e (booleanRankParameter (i + 1) * x) =
      polynomialParameter K p (i + 1) * integralStalkComparison K hs p e x := by
  have hf : (integralStalkComparison K hs p e).toLinearMap.comp
      (LinearMap.mulLeft K (booleanRankParameter (V := FaceVertex p) (K := K) (i + 1))) =
      (LinearMap.mulLeft K (polynomialParameter K p (i + 1))).comp
        (integralStalkComparison K hs p e).toLinearMap := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
    rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a,
      ← booleanCoefficientChange_parameter (Int.castRingHom K) (i + 1),
      ← booleanCoefficientChange_mul, integralStalkComparison_commutes,
      integralStalkComparison_commutes, he]
    simp only [polynomialCoefficientChange_eq, map_mul, polynomialParameter, MvPolynomial.map_esymm]
  exact DFunLike.congr_fun hf x

variable {L : Type*} [CommRing L]

theorem integralStalkComparison_baseChange (h : K →+* L) (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk K p) :
    polynomialCoefficientChange h (integralStalkComparison K hs p e x) =
      integralStalkComparison L hs p e (booleanCoefficientChange h x) := by
  have hpoly (y : PolynomialStalk ℤ p) :
      polynomialCoefficientChange h (polynomialCoefficientChange (Int.castRingHom K) y) =
        polynomialCoefficientChange (Int.castRingHom L) y := by
    simp only [polynomialCoefficientChange_eq, MvPolynomial.map_map]
    rw [show h.comp (Int.castRingHom K) = Int.castRingHom L from Subsingleton.elim _ _]
  exact basis_constr_baseChange h
    (barycentricStalkStandardBasis K hs p) (barycentricStalkStandardBasis L hs p)
    (booleanCoefficientChange h) (polynomialCoefficientChange h)
    (fun a => polynomialCoefficientChange (Int.castRingHom K)
      (e (barycentricStalkStandardBasis ℤ hs p a)))
    (fun a => polynomialCoefficientChange (Int.castRingHom L)
      (e (barycentricStalkStandardBasis ℤ hs p a)))
    (booleanCoefficientChange_standardBasis hs h p) (fun a => hpoly _) x

/-- Existence of one integral coherent system whose actual coefficient
extensions retain degree, every parameter action, and canonical leading terms. -/
theorem exists_integral_graded_coherent_comparison (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ),
      ∀ p : P,
        HasStandardLeading K hs d p ((integralCoherentComparison K hs e).component p).toLinearMap ∧
        (∀ i : ℕ, ∀ x : BarycentricStalk K p,
          (integralCoherentComparison K hs e).component p (booleanRankParameter (i + 1) * x) =
            polynomialParameter K p (i + 1) * (integralCoherentComparison K hs e).component p x) ∧
        HasStandardDegree K hs p ((integralCoherentComparison K hs e).component p).toLinearMap := by
  obtain ⟨e, he⟩ := exists_graded_coherent_parameter_comparison ℤ hs d hrank
  refine ⟨e, fun p => ?_⟩
  exact ⟨integralStalkComparison_leading K hs d p (e.component p) (he p).1,
    integralStalkComparison_parameters K hs p (e.component p) (he p).2.1,
    integralStalkComparison_degree K hs p (e.component p) (he p).2.2⟩

end FourPapers.Universal

end
end

/- BEGIN RankFaceSums.lean -/
section

/-! # Exact enumeration of rank-selected faces in a Boolean interval -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)

theorem card_stalkVertexSet {p q : P} (hqp : q ≤ p) :
    (stalkVertexSet p q).card = faceRank q := by
  have h := Finset.card_image_of_injective (stalkVertexSet p q) Subtype.val_injective
  rw [image_stalkVertexSet hqp] at h
  exact h.symm

def rankFacesBelow (p : P) (i : ℕ) : Finset P :=
  Finset.univ.filter (fun q => q ≤ p ∧ faceRank q = i)

theorem rankFacesBelow_image (p : P) (i : ℕ) (hi : 0 < i) :
    rankFacesBelow p i =
      (Finset.univ.filter (fun F : BooleanFace (FaceVertex p) => F.val.card = i)).image
        (fun F => (booleanFaceInclusion hs p F).val) := by
  ext q
  simp only [rankFacesBelow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hqp, hqi⟩
    let F : BooleanFace (FaceVertex p) := ⟨stalkVertexSet p q, Finset.card_pos.mp (by
      rw [card_stalkVertexSet hqp, hqi]
      exact hi)⟩
    refine ⟨F, ?_, ?_⟩
    · exact (card_stalkVertexSet hqp).trans hqi
    · have h : (⟨(booleanFaceInclusion hs p F).val, booleanFaceInclusion_le hs p F⟩ : Set.Iic p) =
          ⟨q, hqp⟩ := by
        apply (faceBooleanInterval hs p).injective
        change stalkVertexSet p (booleanFaceInclusion hs p F).val = stalkVertexSet p q
        rw [stalkVertexSet_booleanFaceInclusion]
      exact congrArg Subtype.val h
  · rintro ⟨F, hFi, rfl⟩
    exact ⟨booleanFaceInclusion_le hs p F, (faceRank_booleanFaceInclusion hs p F).trans hFi⟩

theorem sum_rank_faces_below {M : Type*} [AddCommMonoid M] (p : P) (i : ℕ)
    (hi : 0 < i) (g : P → M) (hg : ∀ q, ¬ q ≤ p → g q = 0) :
    (∑ q ∈ Finset.univ.filter (fun q => faceRank q = i), g q) =
      ∑ F : BooleanFace (FaceVertex p), if F.val.card = i then g (booleanFaceInclusion hs p F).val else 0 := by
  have hcut : (∑ q ∈ Finset.univ.filter (fun q => faceRank q = i), g q) =
      ∑ q ∈ rankFacesBelow p i, g q := by
    simp only [rankFacesBelow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqp : q ≤ p
    · simp only [hqp, true_and]
    · simp only [hqp, false_and, if_false, hg q hqp, ite_self]
  rw [hcut, rankFacesBelow_image hs p i hi, Finset.sum_image]
  · exact Finset.sum_filter _ _
  · intro F hF G hG he
    exact (booleanFaceInclusion hs p).injective (Subtype.ext he)

end FourPapers.Universal

end
end

/- BEGIN OriginalParameterEvaluation.lean -/
section

/-! # The original rank sums restrict to the stated local parameters -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem barycentricRingEvaluation_included (p : P) (F : BooleanFace (FaceVertex p)) :
    barycentricRingEvaluation K hs p (barycentricGenerator K (booleanFaceInclusion hs p F).val) =
      faceVariable F := by
  change Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
    (MvPolynomial.killCompl (booleanFaceInclusion hs p).injective
      (faceSymbol K (booleanFaceInclusion hs p F).val)) = _
  rw [faceSymbol_nonzero]
  have h := MvPolynomial.killCompl_rename_app (R := K) (booleanFaceInclusion hs p).injective (X F)
  simp only [MvPolynomial.rename_X] at h
  rw [h]
  rfl

theorem barycentricRingEvaluation_outside (p q : P) (hqp : ¬ q ≤ p) :
    barycentricRingEvaluation K hs p (barycentricGenerator K q) = 0 := by
  have hq : q ≠ ⊥ := by intro h; subst q; exact hqp bot_le
  have hn : (⟨q, hq⟩ : NonzeroFace P) ∉ Set.range (booleanFaceInclusion hs p) := by
    rintro ⟨F, hF⟩
    have h := booleanFaceInclusion_le hs p F
    rw [hF] at h
    exact hqp h
  change Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
    (MvPolynomial.killCompl (booleanFaceInclusion hs p).injective (faceSymbol K q)) = 0
  rw [faceSymbol, dif_neg hq]
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hn, map_zero]

theorem barycentricRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) :
    barycentricRingEvaluation K hs p (barycentricRankParameter K i) =
      booleanRankParameter (V := FaceVertex p) (K := K) i := by
  rw [barycentricRankParameter, map_sum]
  rw [sum_rank_faces_below hs p i hi
    (fun q => barycentricRingEvaluation K hs p (barycentricGenerator K q))
    (barycentricRingEvaluation_outside K hs p)]
  simp only [barycentricRingEvaluation_included, booleanRankParameter]

theorem sum_booleanFaces_card_product {V : Type*} [Fintype V] [DecidableEq V]
    (i : ℕ) (hi : 0 < i) :
    (∑ F : BooleanFace V, if F.val.card = i then (∏ v ∈ F.val, (X v : MvPolynomial V K)) else 0) =
      esymm V K i := by
  rw [← Finset.sum_filter, esymm]
  apply Finset.sum_bij (fun F _ => F.val)
  · intro F hF
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hF).2⟩
  · intro F hF G hG h
    exact Subtype.ext h
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    have hn : s.Nonempty := Finset.card_pos.mp (by rw [hc]; exact hi)
    exact ⟨⟨s, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩
  · intro F hF
    rfl

theorem faceRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) :
    faceRingEvaluation K hs p (faceRankParameter K hs i) = polynomialParameter K p i := by
  rw [faceRankParameter, map_sum]
  simp only [faceRingEvaluation_generator]
  rw [sum_rank_faces_below hs p i hi (faceValue K p) (by
    intro q hq
    simp [faceValue, hq])]
  have he (F : BooleanFace (FaceVertex p)) :
      faceValue K p (booleanFaceInclusion hs p F).val =
        ∏ v ∈ F.val, (X v : PolynomialStalk K p) := by
    rw [faceValue, if_pos (booleanFaceInclusion_le hs p F), faceProduct,
      stalkVertexSet_booleanFaceInclusion]
  simp only [he]
  exact sum_booleanFaces_card_product K i hi

end FourPapers.Universal

end
end

/- BEGIN OriginalComparison.lean -/
section

/-! # The comparison on the original quotient rings and relative kernels -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def originalComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) :
    BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  ((barycentricRingSectionEquiv K hs).trans e.sectionEquiv).trans (faceRingSectionEquiv K hs).symm

theorem originalComparison_evaluation
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (x : BarycentricRing (P := P) K) (p : P) :
    faceRingEvaluation K hs p (originalComparison K hs e x) =
      e.component p (barycentricRingEvaluation K hs p x) := by
  have h : faceRingSectionEquiv K hs (originalComparison K hs e x) =
      e.sectionEquiv (barycentricRingSectionEquiv K hs x) := by
    simp only [originalComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have h' := congrArg (fun s : (polynomialDiagram (P := P) K).sections => s.val p) h
  simpa only [faceRingSectionEquiv_apply, faceRingSection_apply, CoherentEquiv.sectionEquiv_apply,
    barycentricRingSectionEquiv_apply] using h'

def originalParameterComparison (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p : P, ∀ i : ℕ, ∀ x : BarycentricStalk K p,
      e.component p (booleanRankParameter (i + 1) * x) =
        polynomialParameter K p (i + 1) * e.component p x) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) where
  toLinearEquiv := originalComparison K hs e
  map_X_mul i x := by
    simp only [barycentricParameterAction, faceParameterAction, MvPolynomial.aeval_X]
    apply (faceRingSectionEquiv K hs).injective
    apply Subtype.ext
    funext p
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      originalComparison_evaluation, map_mul,
      barycentricRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _),
      faceRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _)]
    exact he p i.val (barycentricRingEvaluation K hs p x)

def barycentricRelative (Q : Set P) : Submodule K (BarycentricRing (P := P) K) where
  carrier := {x | ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0}
  zero_mem' := by intro p hp; exact map_zero _
  add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by intro c x hx p hp; rw [map_smul, hx p hp, smul_zero]

def faceRelative (Q : Set P) : Submodule K (FaceRing K hs) where
  carrier := {x | ∀ p ∈ Q, faceRingEvaluation K hs p x = 0}
  zero_mem' := by intro p hp; exact map_zero _
  add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by intro c x hx p hp; rw [map_smul, hx p hp, smul_zero]

/-- The relative comparison is the restriction of the same global map to the
actual kernel of all face restrictions in the specified set. -/
def originalRelativeComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) (Q : Set P) :
    barycentricRelative K hs Q ≃ₗ[K] faceRelative K hs Q where
  toFun x := ⟨originalComparison K hs e x.val, by
    intro p hp
    rw [originalComparison_evaluation, x.property p hp, LinearEquiv.map_zero]⟩
  invFun y := ⟨(originalComparison K hs e).symm y.val, by
    intro p hp
    apply (e.component p).injective
    rw [LinearEquiv.map_zero, ← originalComparison_evaluation, LinearEquiv.apply_symm_apply]
    exact y.property p hp⟩
  left_inv x := Subtype.ext ((originalComparison K hs e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((originalComparison K hs e).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((originalComparison K hs e).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((originalComparison K hs e).map_smul c x.val)

def universalIntegralComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ) :=
  (exists_graded_coherent_parameter_comparison ℤ hs d hrank).choose

theorem universalIntegralComparison_spec (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P) :
    HasStandardLeading ℤ hs d p ((universalIntegralComparison hs d hrank).component p).toLinearMap ∧
      (∀ i : ℕ, ∀ x : BarycentricStalk ℤ p,
        (universalIntegralComparison hs d hrank).component p (booleanRankParameter (i + 1) * x) =
          polynomialParameter ℤ p (i + 1) * (universalIntegralComparison hs d hrank).component p x) ∧
      HasStandardDegree ℤ hs p ((universalIntegralComparison hs d hrank).component p).toLinearMap :=
  (exists_graded_coherent_parameter_comparison ℤ hs d hrank).choose_spec p

def universalCoherentComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) :=
  integralCoherentComparison K hs (universalIntegralComparison hs d hrank)

def universalOriginalParameterComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) :=
  originalParameterComparison K hs d (universalCoherentComparison K hs d hrank) (fun p =>
    integralStalkComparison_parameters K hs p
      ((universalIntegralComparison hs d hrank).component p)
      (universalIntegralComparison_spec hs d hrank p).2.1)

theorem universalCoherentComparison_spec (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P) :
    HasStandardLeading K hs d p ((universalCoherentComparison K hs d hrank).component p).toLinearMap ∧
      (∀ i : ℕ, ∀ x : BarycentricStalk K p,
        (universalCoherentComparison K hs d hrank).component p (booleanRankParameter (i + 1) * x) =
          polynomialParameter K p (i + 1) * (universalCoherentComparison K hs d hrank).component p x) ∧
      HasStandardDegree K hs p ((universalCoherentComparison K hs d hrank).component p).toLinearMap := by
  let e := universalIntegralComparison hs d hrank
  have he := universalIntegralComparison_spec hs d hrank p
  exact ⟨integralStalkComparison_leading K hs d p (e.component p) he.1,
    integralStalkComparison_parameters K hs p (e.component p) he.2.1,
    integralStalkComparison_degree K hs p (e.component p) he.2.2⟩

theorem universalCoherentComparison_baseChange {L : Type*} [CommRing L]
    (h : K →+* L) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P)
    (x : BarycentricStalk K p) :
    polynomialCoefficientChange h ((universalCoherentComparison K hs d hrank).component p x) =
      (universalCoherentComparison L hs d hrank).component p (booleanCoefficientChange h x) :=
  integralStalkComparison_baseChange K hs h p
    ((universalIntegralComparison hs d hrank).component p) x

end FourPapers.Universal

end
end

/- BEGIN OriginalRelativeParameters.lean -/
section

/-! # Full parameter linearity on the original relative modules -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def barycentricRelativeParameters (d : ℕ) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    Submodule (MvPolynomial (Fin d) K) (BarycentricRing (P := P) K) := by
  letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
  exact {
    carrier := {x | ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0}
    zero_mem' := by intro p hp; exact map_zero _
    add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
    smul_mem' := by
      intro a x hx p hp
      change barycentricRingEvaluation K hs p (barycentricParameterAction K d a * x) = 0
      rw [map_mul, hx p hp, mul_zero] }

def faceRelativeParameters (d : ℕ) (Q : Set P) :
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    Submodule (MvPolynomial (Fin d) K) (FaceRing K hs) := by
  letI := (faceParameterAction K hs d).toRingHom.toAlgebra
  exact {
    carrier := {x | ∀ p ∈ Q, faceRingEvaluation K hs p x = 0}
    zero_mem' := by intro p hp; exact map_zero _
    add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
    smul_mem' := by
      intro a x hx p hp
      change faceRingEvaluation K hs p (faceParameterAction K hs d a * x) = 0
      rw [map_mul, hx p hp, mul_zero] }

def originalRelativeParameterComparison (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p : P, ∀ i : ℕ, ∀ x : BarycentricStalk K p,
      e.component p (booleanRankParameter (i + 1) * x) =
        polynomialParameter K p (i + 1) * e.component p x) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K] faceRelativeParameters K hs d Q := by
  letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
  letI := (faceParameterAction K hs d).toRingHom.toAlgebra
  exact {
    (originalRelativeComparison K hs e Q).toAddEquiv with
    map_smul' := fun a x => Subtype.ext
      ((originalParameterComparison K hs d e he).map_parameter_mul a x.val) }

def universalOriginalRelativeParameterComparison (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K] faceRelativeParameters K hs d Q :=
  originalRelativeParameterComparison K hs d (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).2.1) Q

end FourPapers.Universal

end
end

/- BEGIN OriginalLeadingDegree.lean -/
section

/-! # The actual global standard-monomial coefficients of the comparison -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def barycentricGlobalStandardBasis :
    Module.Basis (StandardFaceIndex P) K (BarycentricRing (P := P) K) :=
  Module.Basis.ofRepr (barycentricMonomialEquiv K)

@[simp] theorem barycentricGlobalStandardBasis_coordinates (a : StandardFaceIndex P) :
    barycentricMonomialEquiv K (barycentricGlobalStandardBasis K a) = Finsupp.single a 1 := by
  exact (barycentricMonomialEquiv K).apply_symm_apply (Finsupp.single a 1)

theorem polynomialSectionCoordinates_atCarrier
    (x : (polynomialDiagram (P := P) K).sections) (a : StandardFaceIndex P) :
    polynomialSectionCoordinates K hs x a =
      (polynomialStandardCoordinates K hs (standardCarrier a) (x.val (standardCarrier a))).val a := rfl

theorem standardFaceBasis_repr_atCarrier (x : FaceRing K hs) (a : StandardFaceIndex P) :
    (standardFaceBasis K hs).repr x a =
      (polynomialStandardCoordinates K hs (standardCarrier a)
        (faceRingEvaluation K hs (standardCarrier a) x)).val a := by
  have h : (standardFaceBasis K hs).repr x =
      polynomialSectionCoordinates K hs (faceRingSection K hs x) := by
    rw [← faceRingSectionEquiv_apply]
    simp only [faceRingSectionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [h, polynomialSectionCoordinates_atCarrier]
  rfl

theorem barycentricRingEvaluation_globalBasis (p : P) (a : StandardFaceIndex P) :
    barycentricRingEvaluation K hs p (barycentricGlobalStandardBasis K a) =
      if h : standardCarrier a ≤ p then barycentricStalkStandardBasis K hs p ⟨a, h⟩ else 0 := by
  apply (barycentricStandardCoordinates K hs p).injective
  rw [barycentricRingEvaluation_coordinates, barycentricGlobalStandardBasis_coordinates]
  by_cases ha : standardCarrier a ≤ p
  · rw [dif_pos ha, barycentricStandardCoordinates_basis]
    apply Subtype.ext
    ext b
    rw [coefficientSection_apply, coefficientUnit_apply]
    by_cases hab : a = b
    · subst b
      simp only [if_pos ha, Finsupp.single_eq_same, if_pos rfl, ite_true]
    · simp only [Finsupp.single_apply, if_neg hab, if_neg (Ne.symm hab), ite_self]
  · rw [dif_neg ha, LinearEquiv.map_zero]
    apply Subtype.ext
    ext b
    rw [coefficientSection_apply]
    by_cases hab : a = b
    · subst b
      simp only [if_neg ha]
      rfl
    · simp only [Finsupp.single_apply, if_neg hab, if_neg (Ne.symm hab), ite_self]
      rfl

theorem originalComparison_leading (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p, HasStandardLeading K hs d p (e.component p).toLinearMap)
    (a b : StandardFaceIndex P) (hab : standardRankWeight d a ≤ standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      (originalComparison K hs e (barycentricGlobalStandardBasis K a)) b =
        if a = b then 1 else 0 := by
  rw [standardFaceBasis_repr_atCarrier, originalComparison_evaluation,
    barycentricRingEvaluation_globalBasis]
  by_cases ha : standardCarrier a ≤ standardCarrier b
  · rw [dif_pos ha]
    exact he (standardCarrier b) ⟨a, ha⟩ b hab
  · rw [dif_neg ha, LinearEquiv.map_zero, LinearEquiv.map_zero]
    have hne : a ≠ b := by intro h; subst b; exact ha le_rfl
    rw [if_neg hne]
    rfl

theorem originalComparison_degree
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p, HasStandardDegree K hs p (e.component p).toLinearMap)
    (a b : StandardFaceIndex P)
    (hab : standardOrdinaryDegree b ≠ standardOrdinaryDegree a) :
    (standardFaceBasis K hs).repr
      (originalComparison K hs e (barycentricGlobalStandardBasis K a)) b = 0 := by
  rw [standardFaceBasis_repr_atCarrier, originalComparison_evaluation,
    barycentricRingEvaluation_globalBasis]
  by_cases ha : standardCarrier a ≤ standardCarrier b
  · rw [dif_pos ha]
    exact he (standardCarrier b) ⟨a, ha⟩ b hab
  · rw [dif_neg ha, LinearEquiv.map_zero, LinearEquiv.map_zero]
    rfl

theorem universalOriginalParameterComparison_leading (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (a b : StandardFaceIndex P)
    (hab : standardRankWeight d a ≤ standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricGlobalStandardBasis K a)) b = if a = b then 1 else 0 :=
  originalComparison_leading K hs d (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).1) a b hab

theorem universalOriginalParameterComparison_degree (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (a b : StandardFaceIndex P)
    (hab : standardOrdinaryDegree b ≠ standardOrdinaryDegree a) :
    (standardFaceBasis K hs).repr
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricGlobalStandardBasis K a)) b = 0 :=
  originalComparison_degree K hs (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).2.2) a b hab

end FourPapers.Universal

end
end

/- BEGIN OriginalAssociatedGraded.lean -/
section

/-! # The actual rank-weight associated graded map is the canonical one -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def originalBarycentricWeightLevel (d : ℕ) (n : ℤ) :
    Submodule K (BarycentricRing (P := P) K) :=
  basisWeightLevel (barycentricGlobalStandardBasis K) (standardRankWeight d) n

def originalFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  basisWeightLevel (standardFaceBasis K hs) (standardRankWeight d) n

def canonicalOriginalComparison : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  canonicalBasisEquiv (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)

set_option backward.isDefEq.respectTransparency false in
theorem universalOriginalParameterComparison_hasWeightLeading (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    HasWeightLeading (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
      (standardRankWeight d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap := by
  intro a b hab
  have h := universalOriginalParameterComparison_leading K hs d hrank a b hab
  by_cases he : a = b
  · simpa only [LinearEquiv.coe_coe, if_pos he] using h
  · simpa only [LinearEquiv.coe_coe, if_neg he] using h

theorem canonicalOriginalComparison_filtered (d : ℕ) (n : ℤ) (x : BarycentricRing (P := P) K) :
    canonicalOriginalComparison K hs x ∈ originalFaceWeightLevel K hs d n ↔
      x ∈ originalBarycentricWeightLevel K d n := by
  change (∀ i, n ≤ standardRankWeight d i →
    (standardFaceBasis K hs).repr (canonicalBasisEquiv
      (barycentricGlobalStandardBasis K) (standardFaceBasis K hs) x) i = 0) ↔ _
  rw [canonicalBasisEquiv_repr]
  rfl

theorem universalOriginalParameterComparison_filtered (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈
      originalFaceWeightLevel K hs d n ↔ x ∈ originalBarycentricWeightLevel K d n :=
  weightLeading_mem_iff (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
    (standardRankWeight d) (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap
    (universalOriginalParameterComparison_hasWeightLeading K hs d hrank) n x

theorem universalOriginalParameterComparison_error_lower (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K)
    (hx : x ∈ originalBarycentricWeightLevel K d (n + 1)) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x - canonicalOriginalComparison K hs x ∈
      originalFaceWeightLevel K hs d n :=
  weightLeading_error_lower (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
    (standardRankWeight d) (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap
    (universalOriginalParameterComparison_hasWeightLeading K hs d hrank) n x hx

/-- This equality is between actual quotient maps on consecutive filtration
levels. The canonical standard-monomial map is defined independently. -/
theorem universalOriginalParameterComparison_associatedGrade (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) :
    weightFiltrationGradeEquiv (originalBarycentricWeightLevel (P := P) K d)
      (originalFaceWeightLevel K hs d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
      (universalOriginalParameterComparison_filtered K hs d hrank) n =
    weightFiltrationGradeEquiv (originalBarycentricWeightLevel (P := P) K d)
      (originalFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_filtered K hs d) n :=
  weightFiltrationGradeEquiv_eq_of_error_lower _ _ _ _
    (universalOriginalParameterComparison_filtered K hs d hrank)
    (canonicalOriginalComparison_filtered K hs d) n
    (universalOriginalParameterComparison_error_lower K hs d hrank n)

end FourPapers.Universal

end
end

/- BEGIN OriginalCoefficientChange.lean -/
section

/-! # The scalar-change square on the original quotient presentations -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable {K L : Type*} [CommRing K] [CommRing L]
variable (hs : IsSimplicialPoset P) (h : K →+* L)

theorem map_faceSymbol (p : P) : MvPolynomial.map h (faceSymbol K p) = faceSymbol L p := by
  unfold faceSymbol
  split_ifs <;> simp only [map_one, MvPolynomial.map_X]

theorem map_faceRelation {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    MvPolynomial.map h f ∈ faceRelations L hs := by
  rcases hf with ⟨p, q, w, hpw, hqw, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · left
    refine ⟨p, q, w, hpw, hqw, ?_⟩
    simp only [map_sub, map_mul, map_sum, map_faceSymbol]
  · right
    refine ⟨p, q, hnone, ?_⟩
    simp only [map_mul, map_faceSymbol]

def originalFaceCoefficientChange : FaceRing K hs →+* FaceRing L hs :=
  letI : (faceIdeal K hs).IsTwoSided := palomarFaceIdealTwoSided K hs
  letI : (faceIdeal L hs).IsTwoSided := palomarFaceIdealTwoSided L hs
  Ideal.quotientMap (faceIdeal L hs) (MvPolynomial.map h) (by
    apply Ideal.span_le.mpr
    intro f hf
    exact Ideal.subset_span (map_faceRelation hs h hf))

@[simp] theorem originalFaceCoefficientChange_mk (f : FacePolynomial (P := P) K) :
    originalFaceCoefficientChange hs h (Ideal.Quotient.mk (faceIdeal K hs) f) =
      Ideal.Quotient.mk (faceIdeal L hs) (MvPolynomial.map h f) := rfl

def originalBarycentricCoefficientChange : BarycentricRing (P := P) K →+* BarycentricRing (P := P) L :=
  (barycentricPresentationEquiv L).symm.toRingHom.comp
    ((monomialCoefficientRingHom BarycentricAllowed barycentricAllowed_divisorClosed h).comp
      (barycentricPresentationEquiv K).toRingHom)

@[simp] theorem originalBarycentricCoefficientChange_mk (f : FacePolynomial (P := P) K) :
    originalBarycentricCoefficientChange (P := P) h (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal L) (MvPolynomial.map h f) := by
  change (barycentricPresentationEquiv L).symm
    (monomialCoefficientMap BarycentricAllowed barycentricAllowed_divisorClosed h
      (Ideal.Quotient.mk (forbiddenIdeal BarycentricAllowed) f)) = _
  rw [monomialCoefficientMap_mk]
  rfl

theorem map_faceValue (p q : P) : MvPolynomial.map h (faceValue K p q) = faceValue L p q := by
  unfold faceValue faceProduct
  split_ifs <;> simp only [map_prod, MvPolynomial.map_X, map_zero]

theorem originalFaceCoefficientChange_evaluation (p : P) (x : FaceRing K hs) :
    faceRingEvaluation L hs p (originalFaceCoefficientChange hs h x) =
      polynomialCoefficientChange h (faceRingEvaluation K hs p x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change faceEvaluation L p (MvPolynomial.map h f) = MvPolynomial.map h (faceEvaluation K p f)
  have he : (faceEvaluation L p).toRingHom.comp (MvPolynomial.map h) =
      (MvPolynomial.map h).comp (faceEvaluation K p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.map_C,
        faceEvaluation, MvPolynomial.aeval_C]
      exact (MvPolynomial.map_C h c).symm
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.map_X,
        faceEvaluation, MvPolynomial.aeval_X, map_faceValue]
  exact DFunLike.congr_fun he f

theorem originalBarycentricCoefficientChange_evaluation (p : P) (x : BarycentricRing (P := P) K) :
    barycentricRingEvaluation L hs p (originalBarycentricCoefficientChange h x) =
      booleanCoefficientChange h (barycentricRingEvaluation K hs p x) := by
  change monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed IsChainExponent
    barycentricAllowed_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)
    (barycentricPresentationEquiv L ((barycentricPresentationEquiv L).symm
      (monomialCoefficientMap BarycentricAllowed barycentricAllowed_divisorClosed h
        (barycentricPresentationEquiv K x)))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (monomialCoefficientMap_restriction h (booleanFaceInclusion hs p)
    BarycentricAllowed IsChainExponent barycentricAllowed_divisorClosed
    isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha) _).symm

/-- The one integral comparison commutes with every coefficient homomorphism
on the original quotient rings, with their usual polynomial coefficient maps. -/
theorem universalOriginalParameterComparison_baseChange (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (x : BarycentricRing (P := P) K) :
    originalFaceCoefficientChange hs h
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) =
    (universalOriginalParameterComparison L hs d hrank).toLinearEquiv
      (originalBarycentricCoefficientChange h x) := by
  apply (faceRingSectionEquiv L hs).injective
  apply Subtype.ext
  funext p
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  change faceRingEvaluation L hs p
    (originalFaceCoefficientChange hs h
      (originalComparison K hs (universalCoherentComparison K hs d hrank) x)) =
    faceRingEvaluation L hs p
      (originalComparison L hs (universalCoherentComparison L hs d hrank)
        (originalBarycentricCoefficientChange h x))
  rw [originalFaceCoefficientChange_evaluation, originalComparison_evaluation,
    originalComparison_evaluation, originalBarycentricCoefficientChange_evaluation]
  exact universalCoherentComparison_baseChange K hs h d hrank p _

end FourPapers.Universal

end
end

/- BEGIN PresentationDegree.lean -/
section

/-! # Ordinary grading from the actual homogeneous polynomial presentations

The usual degree-n piece of a quotient is the image of the weighted
homogeneous polynomial submodule. The lemmas below identify that actual
image with the standard-basis degree block, without a dimension argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {I V K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Zero satisfies the original degree-support predicate. -/
theorem palomarBasisOrdinaryDegreePiece_zero (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) : ∀ i, degree i ≠ n → b.repr (0 : M) i = 0 := by
  intro i hi; simp
/-- Addition preserves the original degree-support predicate. -/
theorem palomarBasisOrdinaryDegreePiece_add (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) :
    ∀ (x y : M), (∀ i, degree i ≠ n → b.repr x i = 0) →
      (∀ i, degree i ≠ n → b.repr y i = 0) → ∀ i, degree i ≠ n → b.repr (x + y) i = 0 := by
  intro x y hx hy i hi; simp only [map_add, Finsupp.add_apply, hx i hi, hy i hi, add_zero]

/-- The original scalar-closure proof for the unchanged coefficient predicate. -/
theorem palomarBasisOrdinaryDegreePiece_smul (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) :
    ∀ (c : K) (x : M), (∀ i, degree i ≠ n → b.repr x i = 0) →
      ∀ i, degree i ≠ n → b.repr (c • x) i = 0 := by intro c x hx i hi; simp only [map_smul, Finsupp.smul_apply, hx i hi, smul_zero]

def basisOrdinaryDegreePiece (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) : Submodule K M where
  carrier := {x | ∀ i, degree i ≠ n →
    (@LinearEquiv.toLinearMap K K _ _ (RingHom.id K) (RingHom.id K)
      (PalomarBarycentric.commutativeCoefficientIdentityInvPair (K := K))
      (PalomarBarycentric.commutativeCoefficientIdentityInvPair (K := K))
      M (I →₀ K) _ _ _ _ b.repr) x i = 0}
  zero_mem' := palomarBasisOrdinaryDegreePiece_zero b degree n
  add_mem' := fun {x y} => palomarBasisOrdinaryDegreePiece_add b degree n x y
  smul_mem' := palomarBasisOrdinaryDegreePiece_smul b degree n

theorem weightedPresentationPiece_eq (q : MvPolynomial V K →ₗ[K] M)
    (b : Module.Basis I K M) (a : I → V →₀ ℕ) (w : V → ℕ) (degree : I → ℕ)
    (hb : ∀ i, q (monomial (a i) 1) = b i)
    (hd : ∀ i, Finsupp.weight w (a i) = degree i)
    (hm : ∀ t r i, degree i ≠ Finsupp.weight w t → b.repr (q (monomial t r)) i = 0)
    (n : ℕ) :
    (weightedHomogeneousSubmodule K w n).map q = basisOrdinaryDegreePiece b degree n := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro i hi
    rw [f.as_sum]
    simp only [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t ht
    apply hm t (f.coeff t) i
    rw [hf (MvPolynomial.mem_support_iff.mp ht)]
    exact hi
  · intro hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    have hdi : degree i = n := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hi (hx i hn)
    exact ⟨monomial (a i) 1, isWeightedHomogeneous_monomial w (a i) 1 ((hd i).trans hdi), hb i⟩

theorem basisOrdinaryDegreePiece_map (b : Module.Basis I K M) (c : Module.Basis I K N)
    (degree : I → ℕ) (f : M →ₗ[K] N)
    (hf : ∀ i j, degree j ≠ degree i → c.repr (f (b i)) j = 0)
    (n : ℕ) (x : M) (hx : x ∈ basisOrdinaryDegreePiece b degree n) :
    f x ∈ basisOrdinaryDegreePiece c degree n := by
  intro j hj
  change c.repr (f x) j = 0
  rw [basis_repr_linear_map]
  apply Finset.sum_eq_zero
  intro i hi
  have hdi : degree i = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (hx i hn)
  rw [hf i j (by rw [hdi]; exact hj), mul_zero]

theorem basisOrdinaryDegreePiece_equiv_iff (b : Module.Basis I K M) (c : Module.Basis I K N)
    (degree : I → ℕ) (e : M ≃ₗ[K] N)
    (he : ∀ i j, degree j ≠ degree i → c.repr (e (b i)) j = 0)
    (n : ℕ) (x : M) :
    e x ∈ basisOrdinaryDegreePiece c degree n ↔ x ∈ basisOrdinaryDegreePiece b degree n := by
  have hi : ∀ i j, degree j ≠ degree i → b.repr (e.symm (c i)) j = 0 := by
    intro i j hij
    have h := basis_repr_homogeneous_symm c (b.map e) degree degree
      (fun k l hkl => by simpa only [Module.Basis.map_apply] using he l k hkl) i j hij
    exact h
  constructor
  · intro hx
    have h := basisOrdinaryDegreePiece_map c b degree e.symm.toLinearMap hi n (e x) hx
    change e.symm (e x) ∈ basisOrdinaryDegreePiece b degree n at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  · exact basisOrdinaryDegreePiece_map b c degree e.toLinearMap he n x

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

def originalPolynomialDegree (a : NonzeroFace P →₀ ℕ) : ℕ :=
  a.sum (fun q n => n * faceRank q.val)

theorem originalPolynomialDegree_eq_weight (a : NonzeroFace P →₀ ℕ) :
    originalPolynomialDegree a = Finsupp.weight (fun q : NonzeroFace P => faceRank q.val) a := by
  simp only [originalPolynomialDegree, Finsupp.weight_apply, smul_eq_mul]

theorem stalkExponent_ordinaryDegree (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    vertexDegree (fun v => stalkExponent p a v) = originalPolynomialDegree a := by
  unfold vertexDegree originalPolynomialDegree
  simp only [stalkExponent_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  change (∑ _v ∈ stalkVertexSet p q.val, a q) = a q * faceRank q.val
  rw [Finset.sum_const, nsmul_eq_mul, card_stalkVertexSet (ha q hq), Nat.mul_comm]
  rfl

theorem originalFace_monomial_degree (a : NonzeroFace P →₀ ℕ) (r : K)
    (b : StandardFaceIndex P) (hb : standardOrdinaryDegree b ≠ originalPolynomialDegree a) :
    (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a r)) b = 0 := by
  change (standardFaceBasis K hs).repr
    ((Ideal.Quotient.mkₐ K (faceIdeal K hs)) (monomial a r)) b = 0
  have hmono : monomial a r = r • monomial a (1 : K) := by
    rw [← (monomial a).map_smul, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, Finsupp.smul_apply]
  suffices h : (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0 by
    change r • (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0
    rw [h, smul_zero]
  rw [standardFaceBasis_repr_atCarrier, polynomialStandardCoordinates_apply_of_inside
    K hs (standardCarrier b) _ ⟨b, le_rfl⟩]
  change (faceEvaluation K (standardCarrier b) (monomial a 1)).coeff
    (stalkExponent (standardCarrier b) b.val) = 0
  by_cases ha : ∀ q ∈ a.support, q.val ≤ standardCarrier b
  · rw [faceEvaluation_monomial_of_inside K _ a ha, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    have hd := congrArg (fun t : FaceVertex (standardCarrier b) →₀ ℕ => vertexDegree (fun v => t v)) he
    rw [stalkExponent_ordinaryDegree _ a ha,
      stalkExponent_ordinaryDegree _ b.val ((standardCarrier_le_iff hs b _).mp le_rfl)] at hd
    exact hb hd.symm
  · rw [faceEvaluation_monomial_of_outside K _ a ha]
    rfl

/-- The conventional degree piece is the image of the actual homogeneous
polynomials in the original presentation. -/
def usualFaceDegreePiece (n : ℕ) : Submodule K (FaceRing K hs) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap

theorem usualFaceDegreePiece_eq (n : ℕ) :
    usualFaceDegreePiece K hs n =
      basisOrdinaryDegreePiece (standardFaceBasis K hs) standardOrdinaryDegree n := by
  apply weightedPresentationPiece_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · intro a
    exact (standardFaceBasis_apply K hs a).symm
  · intro a
    exact (originalPolynomialDegree_eq_weight a.val).symm
  · intro a r b hb
    apply originalFace_monomial_degree K hs a r b
    simpa only [originalPolynomialDegree_eq_weight] using hb

def usualBarycentricDegreePiece (n : ℕ) : Submodule K (BarycentricRing (P := P) K) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap

theorem barycentricGlobalStandardBasis_monomial (a : StandardFaceIndex P) :
    Ideal.Quotient.mk (barycentricIdeal (P := P) K) (monomial a.val 1) =
      barycentricGlobalStandardBasis K a := by
  apply (barycentricMonomialEquiv K).injective
  rw [barycentricMonomialEquiv_mk, barycentricGlobalStandardBasis_coordinates]
  ext b
  rw [standardCoefficients_apply, MvPolynomial.coeff_monomial, Finsupp.single_apply]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
  · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    simp only [if_neg hab, if_neg hval]

theorem usualBarycentricDegreePiece_eq (n : ℕ) :
    usualBarycentricDegreePiece (P := P) K n =
      basisOrdinaryDegreePiece (barycentricGlobalStandardBasis K) standardOrdinaryDegree n := by
  apply weightedPresentationPiece_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · exact barycentricGlobalStandardBasis_monomial K
  · intro a
    exact (originalPolynomialDegree_eq_weight a.val).symm
  · intro a r b hb
    change standardCoefficients BarycentricAllowed (monomial a r) b = 0
    rw [standardCoefficients_apply, MvPolynomial.coeff_monomial]
    apply if_neg
    intro hab
    subst a
    exact hb (originalPolynomialDegree_eq_weight b.val)

/-- Ordinary grading in the conventional quotient presentation, in both
directions of the actual parameter equivalence. -/
theorem universalOriginalParameterComparison_usualDegree (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℕ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈
      usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n := by
  rw [usualFaceDegreePiece_eq, usualBarycentricDegreePiece_eq]
  exact basisOrdinaryDegreePiece_equiv_iff
    (barycentricGlobalStandardBasis K) (standardFaceBasis K hs) standardOrdinaryDegree
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
    (universalOriginalParameterComparison_degree K hs d hrank) n x

end Poset
end FourPapers.Universal

end
end

/- BEGIN RestrictionKernels.lean -/
section

/-! # Conventional restriction ideals and the relative comparison

Restriction to a lower ideal kills the outside face generators.  The statements
below identify the kernel of this actual quotient map with the joint kernel of
the polynomial stalk restrictions.  The bottom symbol is included: a genuinely
empty lower ideal has zero quotient, whereas the lower ideal containing only the
bottom face has the constant coefficient ring.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def faceRestrictionIdeal (Q : Set P) : Ideal (FaceRing K hs) :=
  Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = faceRingGenerator K hs p}

def barycentricRestrictionIdeal (Q : Set P) : Ideal (BarycentricRing (P := P) K) :=
  Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = barycentricGenerator K p}

abbrev faceRestrictionQuotient (Q : Set P) := FaceRing K hs ⧸ faceRestrictionIdeal K hs Q
abbrev barycentricRestrictionQuotient (Q : Set P) :=
  BarycentricRing (P := P) K ⧸ barycentricRestrictionIdeal K Q

def faceRestrictionMap (Q : Set P) :
    FaceRing K hs →ₐ[K] faceRestrictionQuotient K hs Q :=
  Ideal.Quotient.mkₐ K (faceRestrictionIdeal K hs Q)

def barycentricRestrictionMap (Q : Set P) :
    BarycentricRing (P := P) K →ₐ[K] barycentricRestrictionQuotient K Q :=
  Ideal.Quotient.mkₐ K (barycentricRestrictionIdeal K Q)

theorem monomial_factor_at_support (a : NonzeroFace P →₀ ℕ) (q : NonzeroFace P)
    (hq : q ∈ a.support) :
    (monomial a (1 : K) : FacePolynomial K) =
      X q * monomial (a - Finsupp.single q 1) 1 := by
  have hle : Finsupp.single q 1 ≤ a :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq))
  rw [MvPolynomial.X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]

theorem faceBasis_mem_restrictionIdeal (Q : Set P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∉ Q) :
    standardFaceBasis K hs a ∈ faceRestrictionIdeal K hs Q := by
  rcases standardCarrier_mem_or_bot a with hb | ⟨q, hq, he⟩
  · have h1 : (1 : FaceRing K hs) ∈ faceRestrictionIdeal K hs Q := by
      have hm : faceRingGenerator K hs ⊥ ∈ faceRestrictionIdeal K hs Q :=
        Ideal.subset_span ⟨⊥, by simpa only [hb] using ha, rfl⟩
      simpa only [faceRingGenerator, faceSymbol_bot, map_one] using hm
    simpa only [mul_one] using (faceRestrictionIdeal K hs Q).mul_mem_left
      (standardFaceBasis K hs a) h1
  · rw [standardFaceBasis_apply]
    change Ideal.Quotient.mk (faceIdeal K hs) (monomial a.val 1) ∈ _
    rw [monomial_factor_at_support K a.val q hq, map_mul]
    apply (faceRestrictionIdeal K hs Q).mul_mem_right
    have hm : faceRingGenerator K hs q.val ∈ faceRestrictionIdeal K hs Q :=
      Ideal.subset_span ⟨q.val, by simpa only [he] using ha, rfl⟩
    simpa only [faceRingGenerator, faceSymbol_nonzero] using hm

theorem barycentricBasis_mem_restrictionIdeal (Q : Set P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∉ Q) :
    barycentricGlobalStandardBasis K a ∈ barycentricRestrictionIdeal K Q := by
  rcases standardCarrier_mem_or_bot a with hb | ⟨q, hq, he⟩
  · have h1 : (1 : BarycentricRing (P := P) K) ∈ barycentricRestrictionIdeal K Q := by
      have hm : barycentricGenerator K ⊥ ∈ barycentricRestrictionIdeal K Q :=
        Ideal.subset_span ⟨⊥, by simpa only [hb] using ha, rfl⟩
      simpa only [barycentricGenerator, faceSymbol_bot, map_one] using hm
    simpa only [mul_one] using (barycentricRestrictionIdeal K Q).mul_mem_left
      (barycentricGlobalStandardBasis K a) h1
  · rw [← barycentricGlobalStandardBasis_monomial]
    rw [monomial_factor_at_support K a.val q hq, map_mul]
    apply (barycentricRestrictionIdeal K Q).mul_mem_right
    have hm : barycentricGenerator K q.val ∈ barycentricRestrictionIdeal K Q :=
      Ideal.subset_span ⟨q.val, by simpa only [he] using ha, rfl⟩
    simpa only [barycentricGenerator, faceSymbol_nonzero] using hm

theorem faceRestrictionIdeal_mem_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : FaceRing K hs) :
    x ∈ faceRestrictionIdeal K hs Q ↔ ∀ p ∈ Q, faceRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hker : faceRestrictionIdeal K hs Q ≤ RingHom.ker (faceRingEvaluation K hs p).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨q, hq, rfl⟩
      change faceRingEvaluation K hs p (faceRingGenerator K hs q) = 0
      rw [faceRingEvaluation_generator, faceValue, if_neg (fun h => hq (hQ h hp))]
    exact hker hx
  · intro hx
    rw [← (standardFaceBasis K hs).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (faceRestrictionIdeal K hs Q).sum_mem
    intro a ha
    have hout : standardCarrier a ∉ Q := by
      intro hin
      have hz := hx (standardCarrier a) hin
      have hc : (standardFaceBasis K hs).repr x a = 0 := by
        rw [standardFaceBasis_repr_atCarrier, hz, LinearEquiv.map_zero]
        rfl
      exact Finsupp.mem_support_iff.mp ha hc
    exact (faceRestrictionIdeal K hs Q).smul_of_tower_mem
      ((standardFaceBasis K hs).repr x a) (faceBasis_mem_restrictionIdeal K hs Q a hout)

theorem barycentricRestrictionIdeal_mem_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    x ∈ barycentricRestrictionIdeal K Q ↔ ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hker : barycentricRestrictionIdeal K Q ≤ RingHom.ker (barycentricRingEvaluation K hs p).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨q, hq, rfl⟩
      change barycentricRingEvaluation K hs p (barycentricGenerator K q) = 0
      exact barycentricRingEvaluation_outside K hs p q (fun h => hq (hQ h hp))
    exact hker hx
  · intro hx
    rw [← (barycentricGlobalStandardBasis K).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (barycentricRestrictionIdeal K Q).sum_mem
    intro a ha
    have hout : standardCarrier a ∉ Q := by
      intro hin
      have hz := hx (standardCarrier a) hin
      have hc : (barycentricGlobalStandardBasis K).repr x a = 0 := by
        change barycentricMonomialEquiv K x a = 0
        rw [← barycentricRingEvaluation_coefficient K hs (standardCarrier a) x a le_rfl,
          hz, map_zero]
        rfl
      exact Finsupp.mem_support_iff.mp ha hc
    exact (barycentricRestrictionIdeal K Q).smul_of_tower_mem
      ((barycentricGlobalStandardBasis K).repr x a)
      (barycentricBasis_mem_restrictionIdeal K Q a hout)

theorem faceRestrictionMap_eq_zero_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : FaceRing K hs) :
    faceRestrictionMap K hs Q x = 0 ↔ ∀ p ∈ Q, faceRingEvaluation K hs p x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.trans (faceRestrictionIdeal_mem_iff K hs Q hQ x)

theorem barycentricRestrictionMap_eq_zero_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    barycentricRestrictionMap K Q x = 0 ↔ ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.trans (barycentricRestrictionIdeal_mem_iff K hs Q hQ x)

/-- The actual global parameter equivalence identifies the conventional
restriction kernels, simultaneously for every lower ideal. -/
theorem universalOriginalParameterComparison_restrictionKernel (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
    (x : BarycentricRing (P := P) K) :
    faceRestrictionMap K hs Q ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) = 0 ↔
      barycentricRestrictionMap K Q x = 0 := by
  rw [faceRestrictionMap_eq_zero_iff K hs Q hQ,
    barycentricRestrictionMap_eq_zero_iff K hs Q hQ]
  constructor
  · intro hx p hp
    have hh := hx p hp
    rw [show (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x =
        originalComparison K hs (universalCoherentComparison K hs d hrank) x from rfl,
      originalComparison_evaluation] at hh
    exact ((universalCoherentComparison K hs d hrank).component p).injective
      (hh.trans ((universalCoherentComparison K hs d hrank).component p).map_zero.symm)
  · intro hx p hp
    change faceRingEvaluation K hs p
      (originalComparison K hs (universalCoherentComparison K hs d hrank) x) = 0
    rw [originalComparison_evaluation, hx p hp, LinearEquiv.map_zero]

end FourPapers.Universal

end
end

/- BEGIN PresentationWeight.lean -/
section

/-! # The rank-weight filtration of the polynomial presentations

The filtration is defined before quotienting, by the weights of the actual
generators.  Its equality with the standard-chain basis filtration is proved
using the genuine polynomial stalk evaluations and the overlap inequality.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {I V K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The original scalar-closure proof for the unchanged coefficient predicate. -/
theorem palomarPresentationWeightLevel_smul (w : (V →₀ ℕ) → ℤ) (n : ℤ) :
    ∀ (c : K) (f : MvPolynomial V K), (∀ a, n ≤ w a → f.coeff a = 0) →
      ∀ a, n ≤ w a → (c • f).coeff a = 0 := by intro c f hf a ha; simp only [coeff_smul, hf a ha, smul_zero]

def presentationWeightLevel (w : (V →₀ ℕ) → ℤ) (n : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a, n ≤ w a → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by intro f g hf hg a ha; simp only [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := palomarPresentationWeightLevel_smul w n

/-- Membership is determined by every monomial coefficient of weight at least n. -/
theorem mem_presentationWeightLevel_iff (w : (V →₀ ℕ) → ℤ) (n : ℤ) (f : MvPolynomial V K) :
    f ∈ presentationWeightLevel w n ↔ ∀ a, n ≤ w a → f.coeff a = 0 := Iff.rfl

theorem weightedPresentationFiltration_eq (q : MvPolynomial V K →ₗ[K] M)
    (b : Module.Basis I K M) (a : I → V →₀ ℕ)
    (w : (V →₀ ℕ) → ℤ) (weight : I → ℤ)
    (hb : ∀ i, q (monomial (a i) 1) = b i)
    (hd : ∀ i, w (a i) = weight i)
    (hm : ∀ t r i, w t < weight i → b.repr (q (monomial t r)) i = 0) (n : ℤ) :
    (presentationWeightLevel w n).map q = basisWeightLevel b weight n := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro i hi
    rw [f.as_sum]
    simp only [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t ht
    apply hm t (f.coeff t) i
    have hn : w t < n := lt_of_not_ge (fun h => MvPolynomial.mem_support_iff.mp ht (hf t h))
    exact hn.trans_le hi
  · intro hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    refine ⟨monomial (a i) 1, ?_, hb i⟩
    intro t ht
    rw [coeff_monomial]
    apply if_neg
    intro he
    subst t
    exact Finsupp.mem_support_iff.mp hi (hx i (by simpa only [hd] using ht))

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

def originalPolynomialWeight (d : ℕ) (a : NonzeroFace P →₀ ℕ) : ℤ :=
  a.sum (fun q n => (n : ℤ) * rankWeight d (faceRank q.val))

abbrev OriginalExponentFactors (a : NonzeroFace P →₀ ℕ) :=
  Σ q : NonzeroFace P, Fin (a q)

def originalFactorFaces (p : P) (a : NonzeroFace P →₀ ℕ)
    (t : OriginalExponentFactors a) : Finset (FaceVertex p) := stalkVertexSet p t.1.val

theorem originalFactorFaces_occurrence (p : P) (a : NonzeroFace P →₀ ℕ) :
    occurrenceExponent (originalFactorFaces p a) = stalkExponent p a := by
  ext v
  rw [occurrenceExponent_apply, Fintype.sum_sigma]
  simp only [originalFactorFaces, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mem_stalkVertexSet, mul_ite, mul_one, mul_zero]
  rw [stalkExponent_apply]
  exact (Finsupp.sum_fintype a (fun q n => if v.val ≤ q.val then n else 0)
    (fun q => by simp)).symm

theorem originalFactorFaces_weight (d : ℕ) (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    (∑ t : OriginalExponentFactors a, rankWeight d (originalFactorFaces p a t).card) =
      originalPolynomialWeight d a := by
  simp only [Fintype.sum_sigma, originalFactorFaces, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [originalPolynomialWeight, Finsupp.sum_fintype _ _ (fun q => by simp)]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqa : a q = 0
  · simp only [hqa, Nat.cast_zero, zero_mul]
  · rw [card_stalkVertexSet (ha q (Finsupp.mem_support_iff.mpr hqa))]

theorem stalkExponent_rankWeight_le (d : ℕ) (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    polynomialRankWeight d (fun v => stalkExponent p a v) ≤ originalPolynomialWeight d a := by
  have h := polynomialRankWeight_occurrence_le d (originalFactorFaces p a)
  simpa only [originalFactorFaces_occurrence, originalFactorFaces_weight d p a ha] using h

include hs in
theorem stalkExponent_standardRankWeight (d : ℕ) (p : P) (a : StandardInside p) :
    polynomialRankWeight d (fun v => stalkExponent p a.val.val v) = standardRankWeight d a.val := by
  letI : LinearOrder (FaceVertex p) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  let b := (standardInsideEquiv hs p).symm a
  have he := (standardInsideEquiv hs p).apply_symm_apply a
  have hw := standardRankWeight_inside hs d p b
  rw [he] at hw
  have hexp : stalkExponent p a.val.val = chainVertexMap b.val := by
    rw [← standardVertexEquiv_apply hs p a]
    rfl
  rw [hexp, polynomialRankWeight_chainVertexMap d b.property]
  exact hw.symm

theorem originalFace_monomial_weight (d : ℕ) (a : NonzeroFace P →₀ ℕ) (r : K)
    (b : StandardFaceIndex P) (hb : originalPolynomialWeight d a < standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a r)) b = 0 := by
  change (standardFaceBasis K hs).repr
    ((Ideal.Quotient.mkₐ K (faceIdeal K hs)) (monomial a r)) b = 0
  have hmono : monomial a r = r • monomial a (1 : K) := by
    rw [← (monomial a).map_smul, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, Finsupp.smul_apply]
  suffices h : (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0 by
    change r • (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0
    rw [h, smul_zero]
  rw [standardFaceBasis_repr_atCarrier, polynomialStandardCoordinates_apply_of_inside
    K hs (standardCarrier b) _ ⟨b, le_rfl⟩]
  change (faceEvaluation K (standardCarrier b) (monomial a 1)).coeff
    (stalkExponent (standardCarrier b) b.val) = 0
  by_cases ha : ∀ q ∈ a.support, q.val ≤ standardCarrier b
  · rw [faceEvaluation_monomial_of_inside K _ a ha, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    have hw := stalkExponent_rankWeight_le d (standardCarrier b) a ha
    rw [he, stalkExponent_standardRankWeight hs d (standardCarrier b) ⟨b, le_rfl⟩] at hw
    exact (not_lt_of_ge hw) hb
  · rw [faceEvaluation_monomial_of_outside K _ a ha]
    rfl

def usualFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap

def usualBarycentricWeightLevel (d : ℕ) (n : ℤ) : Submodule K (BarycentricRing (P := P) K) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap

theorem usualFaceWeightLevel_eq (d : ℕ) (n : ℤ) :
    usualFaceWeightLevel K hs d n = originalFaceWeightLevel K hs d n := by
  apply weightedPresentationFiltration_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · intro a
    exact (standardFaceBasis_apply K hs a).symm
  · intro a
    rfl
  · exact originalFace_monomial_weight K hs d

theorem usualBarycentricWeightLevel_eq (d : ℕ) (n : ℤ) :
    usualBarycentricWeightLevel (P := P) K d n = originalBarycentricWeightLevel K d n := by
  apply weightedPresentationFiltration_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · exact barycentricGlobalStandardBasis_monomial K
  · intro a
    rfl
  · intro a r b hb
    change standardCoefficients BarycentricAllowed (monomial a r) b = 0
    rw [standardCoefficients_apply, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    subst a
    exact (lt_irrefl (standardRankWeight d b)) hb

/-- Preservation and reflection of the actual filtration induced by assigning
weight `r(2d-r)` to a rank-r generator in the original presentations. -/
theorem universalOriginalParameterComparison_usualWeight (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n := by
  rw [usualFaceWeightLevel_eq, usualBarycentricWeightLevel_eq]
  exact universalOriginalParameterComparison_filtered K hs d hrank n x

end Poset
end FourPapers.Universal

end
end

/- BEGIN LowerIdealPresentation.lean -/
section

/-! # The original face-ring presentation of a lower subposet

A nonempty lower ideal contains the bottom face.  Its intervals and atoms are
identified explicitly with the ambient ones.  Stalk restriction then gives a
homomorphism to its original Stanley quotient, with the usual generator formula.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

structure FaceLowerIdeal (P : Type*) [PartialOrder P] [OrderBot P] where
  carrier : Set P
  lower : ∀ ⦃p q : P⦄, p ≤ q → q ∈ carrier → p ∈ carrier
  bot_mem : (⊥ : P) ∈ carrier

instance : CoeSort (FaceLowerIdeal P) (Type _) := ⟨fun Q => Q.carrier⟩
instance (Q : FaceLowerIdeal P) : PartialOrder Q := inferInstanceAs (PartialOrder Q.carrier)
instance (Q : FaceLowerIdeal P) : Fintype Q := Fintype.ofFinite _
instance (Q : FaceLowerIdeal P) : OrderBot Q where
  bot := ⟨⊥, Q.bot_mem⟩
  bot_le _ := bot_le

def lowerIdealIntervalEquiv (Q : FaceLowerIdeal P) (q : Q) : Set.Iic q ≃o Set.Iic q.val where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val, Q.lower a.property q.property⟩, a.property⟩
  left_inv a := rfl
  right_inv a := rfl
  map_rel_iff' := Iff.rfl

theorem lowerIdealIsSimplicial (hs : IsSimplicialPoset P) (Q : FaceLowerIdeal P) :
    IsSimplicialPoset Q := by
  intro q
  obtain ⟨n, ⟨e⟩⟩ := hs q.val
  exact ⟨n, ⟨(lowerIdealIntervalEquiv Q q).trans e⟩⟩

theorem lowerIdeal_isAtom_iff (Q : FaceLowerIdeal P) (a : Q) : IsAtom a ↔ IsAtom a.val := by
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨fun h => ha (Subtype.ext h), ?_⟩
    intro b hb
    have h := hmin ⟨b, Q.lower hb.le a.property⟩ hb
    exact congrArg Subtype.val h
  · rintro ⟨ha, hmin⟩
    exact ⟨fun h => ha (congrArg Subtype.val h),
      fun b hb => Subtype.ext (hmin b.val hb)⟩

def lowerIdealVertexEquiv (Q : FaceLowerIdeal P) (q : Q) : FaceVertex q ≃ FaceVertex q.val where
  toFun a := ⟨a.val.val, (lowerIdeal_isAtom_iff Q a.val).mp a.property.1, a.property.2⟩
  invFun a := ⟨⟨a.val, Q.lower a.property.2 q.property⟩,
    (lowerIdeal_isAtom_iff Q _).mpr a.property.1, a.property.2⟩
  left_inv a := rfl
  right_inv a := rfl

variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def lowerIdealPolynomialEquiv (Q : FaceLowerIdeal P) (q : Q) :
    PolynomialStalk K q.val ≃ₐ[K] PolynomialStalk K q :=
  MvPolynomial.renameEquiv K (lowerIdealVertexEquiv Q q).symm

theorem lowerIdealPolynomialEquiv_restriction (Q : FaceLowerIdeal P) {p q : Q}
    (hqp : q ≤ p) (f : PolynomialStalk K p.val) :
    polynomialRestriction K hqp (lowerIdealPolynomialEquiv K Q p f) =
      lowerIdealPolynomialEquiv K Q q (polynomialRestriction K (show q.val ≤ p.val from hqp) f) := by
  have he : (polynomialRestriction K hqp).comp (lowerIdealPolynomialEquiv K Q p).toAlgHom =
      (lowerIdealPolynomialEquiv K Q q).toAlgHom.comp
        (polynomialRestriction K (show q.val ≤ p.val from hqp)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, lowerIdealPolynomialEquiv,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, polynomialRestriction_X]
    by_cases h : a.val ≤ q.val
    · have hh : ((lowerIdealVertexEquiv Q p).symm a).val ≤ q := h
      rw [dif_pos hh, dif_pos h, MvPolynomial.rename_X]
      rfl
    · have hh : ¬ ((lowerIdealVertexEquiv Q p).symm a).val ≤ q := h
      rw [dif_neg hh, dif_neg h, map_zero]
  exact DFunLike.congr_fun he f

def lowerIdealPolynomialSections (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₗ[K] (polynomialDiagram (P := Q) K).sections where
  toFun x := ⟨fun q => lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x), by
    intro p q hqp
    change polynomialRestriction K hqp
      (lowerIdealPolynomialEquiv K Q p (faceRingEvaluation K hs p.val x)) =
        lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x)
    rw [lowerIdealPolynomialEquiv_restriction]
    have hh := (faceRingSection K hs x).property p.val q.val hqp
    exact congrArg (lowerIdealPolynomialEquiv K Q q) hh⟩
  map_add' x y := by
    apply Subtype.ext
    funext q
    simp only [map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    funext q
    simp only [map_smul]
    rfl

def lowerIdealFaceRestrictionLinear (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₗ[K] FaceRing K (lowerIdealIsSimplicial hs Q) :=
  (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm.toLinearMap.comp
    (lowerIdealPolynomialSections K hs Q)

theorem lowerIdealFaceRestriction_evaluation (Q : FaceLowerIdeal P) (q : Q) (x : FaceRing K hs) :
    faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q (lowerIdealFaceRestrictionLinear K hs Q x) =
      lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x) := by
  have hh := (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).apply_symm_apply
    (lowerIdealPolynomialSections K hs Q x)
  have hc := congrArg (fun s : (polynomialDiagram (P := Q) K).sections => s.val q) hh
  have hc' : faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      ((faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm
        (lowerIdealPolynomialSections K hs Q x)) =
      (lowerIdealPolynomialSections K hs Q x).val q := by
    simpa only [faceRingSectionEquiv_apply, faceRingSection_apply] using hc
  change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      ((faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm
        (lowerIdealPolynomialSections K hs Q x)) = _
  exact hc'.trans (by rfl)

def lowerIdealFaceRestriction (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₐ[K] FaceRing K (lowerIdealIsSimplicial hs Q) where
  toFun := lowerIdealFaceRestrictionLinear K hs Q
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, map_one]
  map_mul' x y := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, map_mul]
  commutes' c := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, AlgHom.commutes, AlgEquiv.commutes]

theorem lowerIdealPolynomialEquiv_faceProduct (Q : FaceLowerIdeal P) (q p : Q) :
    lowerIdealPolynomialEquiv K Q q (faceProduct K q.val p.val) = faceProduct K q p := by
  simp only [lowerIdealPolynomialEquiv, MvPolynomial.renameEquiv_apply,
    faceProduct, map_prod, MvPolynomial.rename_X]
  apply Finset.prod_bij (fun a _ => (lowerIdealVertexEquiv Q q).symm a)
  · intro a ha
    exact (mem_stalkVertexSet q p _).mpr ((mem_stalkVertexSet q.val p.val a).mp ha)
  · intro a ha b hb he
    exact (lowerIdealVertexEquiv Q q).symm.injective he
  · intro b hb
    refine ⟨lowerIdealVertexEquiv Q q b, ?_, ?_⟩
    · exact (mem_stalkVertexSet q.val p.val _).mpr ((mem_stalkVertexSet q p b).mp hb)
    · exact (lowerIdealVertexEquiv Q q).symm_apply_apply b
  · intro a ha
    rfl

theorem lowerIdealFaceRestriction_generator_inside (Q : FaceLowerIdeal P) (p : Q) :
    lowerIdealFaceRestriction K hs Q (faceRingGenerator K hs p.val) =
      faceRingGenerator K (lowerIdealIsSimplicial hs Q) p := by
  apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
  apply Subtype.ext
  funext q
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
    (lowerIdealFaceRestrictionLinear K hs Q (faceRingGenerator K hs p.val)) = _
  rw [lowerIdealFaceRestriction_evaluation, faceRingEvaluation_generator,
    faceRingEvaluation_generator]
  by_cases h : p ≤ q
  · have hh : p.val ≤ q.val := h
    simp only [faceValue, if_pos h, if_pos hh]
    exact lowerIdealPolynomialEquiv_faceProduct K Q q p
  · have hh : ¬ p.val ≤ q.val := h
    simp only [faceValue, if_neg h, if_neg hh, map_zero]

theorem lowerIdealFaceRestriction_eq_zero_iff (Q : FaceLowerIdeal P) (x : FaceRing K hs) :
    lowerIdealFaceRestriction K hs Q x = 0 ↔ ∀ p ∈ Q.carrier, faceRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hh := congrArg (faceRingEvaluation K (lowerIdealIsSimplicial hs Q) ⟨p, hp⟩) hx
    change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) ⟨p, hp⟩
      (lowerIdealFaceRestrictionLinear K hs Q x) = _ at hh
    rw [lowerIdealFaceRestriction_evaluation, map_zero] at hh
    exact (lowerIdealPolynomialEquiv K Q ⟨p, hp⟩).injective
      (hh.trans (map_zero _).symm)
  · intro hx
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
    change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      (lowerIdealFaceRestrictionLinear K hs Q x) = _
    rw [lowerIdealFaceRestriction_evaluation, hx q.val q.property, map_zero, map_zero]

theorem lowerIdealFaceRestriction_generator_outside (Q : FaceLowerIdeal P)
    (p : P) (hp : p ∉ Q.carrier) :
    lowerIdealFaceRestriction K hs Q (faceRingGenerator K hs p) = 0 := by
  rw [lowerIdealFaceRestriction_eq_zero_iff]
  intro q hq
  rw [faceRingEvaluation_generator, faceValue, if_neg (fun h => hp (Q.lower h hq))]

/-- The kernel of restriction to the smaller poset's original Stanley
presentation is precisely the conventional outside-generator ideal. -/
theorem lowerIdealFaceRestriction_ker (Q : FaceLowerIdeal P) :
    RingHom.ker (lowerIdealFaceRestriction K hs Q).toRingHom = faceRestrictionIdeal K hs Q.carrier := by
  ext x
  exact (lowerIdealFaceRestriction_eq_zero_iff K hs Q x).trans
    (faceRestrictionIdeal_mem_iff K hs Q.carrier Q.lower x).symm

end FourPapers.Universal

end
end

/- BEGIN LowerIdealBarycentric.lean -/
section

/-! # Both conventional lower-ideal targets and their quotient identifications -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def lowerIdealNonzeroEmbedding (Q : FaceLowerIdeal P) : NonzeroFace Q ↪ NonzeroFace P where
  toFun q := ⟨q.val.val, fun h => q.property (Subtype.ext h)⟩
  inj' p q h := Subtype.ext (Subtype.ext (congrArg (fun a : NonzeroFace P => a.val) h))

theorem lowerIdealNonzeroEmbedding_range (Q : FaceLowerIdeal P) (p : NonzeroFace P) :
    p ∈ Set.range (lowerIdealNonzeroEmbedding Q) ↔ p.val ∈ Q.carrier := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.val.property
  · intro hp
    refine ⟨⟨⟨p.val, hp⟩, fun h => p.property (congrArg Subtype.val h)⟩, rfl⟩

theorem lowerIdealFaceRestriction_surjective (Q : FaceLowerIdeal P) :
    Function.Surjective (lowerIdealFaceRestriction K hs Q) := by
  have he : (lowerIdealFaceRestriction K hs Q).comp
      ((Ideal.Quotient.mkₐ K (faceIdeal K hs)).comp
        (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q))) =
      Ideal.Quotient.mkₐ K (faceIdeal K (lowerIdealIsSimplicial hs Q)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X]
    have hh := lowerIdealFaceRestriction_generator_inside K hs Q q.val
    have hsym : faceSymbol K q.val.val = X (lowerIdealNonzeroEmbedding Q q) :=
      faceSymbol_nonzero K (lowerIdealNonzeroEmbedding Q q)
    change lowerIdealFaceRestriction K hs Q
      (Ideal.Quotient.mk (faceIdeal K hs) (X (lowerIdealNonzeroEmbedding Q q))) =
        Ideal.Quotient.mk (faceIdeal K (lowerIdealIsSimplicial hs Q)) (X q)
    simpa only [faceRingGenerator, hsym, faceSymbol_nonzero] using hh
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (faceIdeal K hs) (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q) f), ?_⟩
  exact DFunLike.congr_fun he f

/-- The quotient killing outside generators is the original Stanley face ring
of the lower subposet, as an actual algebra equivalence. -/
def lowerIdealFaceQuotientEquiv (Q : FaceLowerIdeal P) :
    faceRestrictionQuotient K hs Q.carrier ≃ₐ[K] FaceRing K (lowerIdealIsSimplicial hs Q) :=
  (Ideal.quotientEquivAlgOfEq K (lowerIdealFaceRestriction_ker K hs Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lowerIdealFaceRestriction_surjective K hs Q))

theorem lowerIdealChainEmbedding (Q : FaceLowerIdeal P) (a : NonzeroFace Q →₀ ℕ)
    (ha : BarycentricAllowed a) :
    BarycentricAllowed (a.mapDomain (lowerIdealNonzeroEmbedding Q)) := by
  intro p hp q hq
  rw [Finsupp.mapDomain_support_of_injective (lowerIdealNonzeroEmbedding Q).injective] at hp hq
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
  exact ha p' hp' q' hq'

def lowerIdealBarycentricRestriction (Q : FaceLowerIdeal P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricRing (P := Q) K :=
  (barycentricPresentationEquiv (P := Q) K).symm.toAlgHom.comp
    ((monomialRestriction (lowerIdealNonzeroEmbedding Q) BarycentricAllowed BarycentricAllowed
      barycentricAllowed_divisorClosed barycentricAllowed_divisorClosed
      (lowerIdealChainEmbedding Q)).comp (barycentricPresentationEquiv K).toAlgHom)

@[simp] theorem lowerIdealBarycentricRestriction_mk (Q : FaceLowerIdeal P)
    (f : FacePolynomial (P := P) K) :
    lowerIdealBarycentricRestriction K Q (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal (P := Q) K)
        (MvPolynomial.killCompl (lowerIdealNonzeroEmbedding Q).injective f) := rfl

theorem lowerIdealBarycentricRestriction_generator_inside (Q : FaceLowerIdeal P) (p : Q) :
    lowerIdealBarycentricRestriction K Q (barycentricGenerator K p.val) =
      barycentricGenerator K p := by
  by_cases hp : p = ⊥
  · subst p
    change lowerIdealBarycentricRestriction K Q (barycentricGenerator K (⊥ : P)) =
      barycentricGenerator K (⊥ : Q)
    simp only [barycentricGenerator, faceSymbol_bot, map_one]
  · have hpp : p.val ≠ ⊥ := fun h => hp (Subtype.ext h)
    rw [barycentricGenerator, lowerIdealBarycentricRestriction_mk, faceSymbol, dif_neg hpp]
    change Ideal.Quotient.mk (barycentricIdeal (P := Q) K)
      (MvPolynomial.killCompl (lowerIdealNonzeroEmbedding Q).injective
        (X (lowerIdealNonzeroEmbedding Q ⟨p, hp⟩))) = _
    have hh := MvPolynomial.killCompl_rename_app (R := K)
      (lowerIdealNonzeroEmbedding Q).injective (X ⟨p, hp⟩)
    simp only [MvPolynomial.rename_X] at hh
    rw [hh]
    simp only [barycentricGenerator, faceSymbol, dif_neg hp]

theorem lowerIdealBarycentricRestriction_generator_outside (Q : FaceLowerIdeal P)
    (p : P) (hp : p ∉ Q.carrier) :
    lowerIdealBarycentricRestriction K Q (barycentricGenerator K p) = 0 := by
  have hpb : p ≠ ⊥ := fun h => hp (h ▸ Q.bot_mem)
  have hn : (⟨p, hpb⟩ : NonzeroFace P) ∉ Set.range (lowerIdealNonzeroEmbedding Q) :=
    fun h => hp ((lowerIdealNonzeroEmbedding_range Q _).mp h)
  rw [barycentricGenerator, lowerIdealBarycentricRestriction_mk, faceSymbol, dif_neg hpb]
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hn, map_zero]

theorem lowerIdealBarycentricRestriction_coefficient (Q : FaceLowerIdeal P)
    (x : BarycentricRing (P := P) K) (a : StandardFaceIndex Q) :
    barycentricMonomialEquiv (P := Q) K (lowerIdealBarycentricRestriction K Q x) a =
      barycentricMonomialEquiv K x
        ⟨a.val.mapDomain (lowerIdealNonzeroEmbedding Q), lowerIdealChainEmbedding Q a.val a.property⟩ := by
  change standardMonomialEquiv BarycentricAllowed barycentricAllowed_divisorClosed
    ((barycentricPresentationEquiv (P := Q) K)
      ((barycentricPresentationEquiv (P := Q) K).symm
        (monomialRestriction (lowerIdealNonzeroEmbedding Q) BarycentricAllowed BarycentricAllowed
          barycentricAllowed_divisorClosed barycentricAllowed_divisorClosed
          (lowerIdealChainEmbedding Q) (barycentricPresentationEquiv K x)))) a = _
  rw [AlgEquiv.apply_symm_apply]
  exact monomialRestriction_coefficient (lowerIdealNonzeroEmbedding Q)
    BarycentricAllowed BarycentricAllowed barycentricAllowed_divisorClosed
    barycentricAllowed_divisorClosed (lowerIdealChainEmbedding Q) _ a

def lowerIdealChainLift (Q : FaceLowerIdeal P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∈ Q.carrier) : StandardFaceIndex Q :=
  ⟨a.val.comapDomain (lowerIdealNonzeroEmbedding Q) (lowerIdealNonzeroEmbedding Q).injective.injOn, by
    intro p hp q hq
    apply a.property (lowerIdealNonzeroEmbedding Q p) ?_ (lowerIdealNonzeroEmbedding Q q) ?_
    · simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hp
    · simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hq⟩

include hs in
theorem lowerIdealChainLift_map (Q : FaceLowerIdeal P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∈ Q.carrier) :
    (lowerIdealChainLift Q a ha).val.mapDomain (lowerIdealNonzeroEmbedding Q) = a.val := by
  apply Finsupp.mapDomain_comapDomain _ (lowerIdealNonzeroEmbedding Q).injective
  intro p hp
  apply (lowerIdealNonzeroEmbedding_range Q p).mpr
  exact Q.lower ((standardCarrier_le_iff hs a _).mp le_rfl p hp) ha

include hs in
theorem barycentricRestrictionIdeal_mem_iff_coefficient (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    x ∈ barycentricRestrictionIdeal K Q ↔
      ∀ a : StandardFaceIndex P, standardCarrier a ∈ Q → barycentricMonomialEquiv K x a = 0 := by
  rw [barycentricRestrictionIdeal_mem_iff K hs Q hQ]
  constructor
  · intro hx a ha
    rw [← barycentricRingEvaluation_coefficient K hs (standardCarrier a) x a le_rfl,
      hx _ ha, map_zero]
    rfl
  · intro hx p hp
    apply (barycentricStandardCoordinates K hs p).injective
    rw [barycentricRingEvaluation_coordinates, map_zero]
    apply Subtype.ext
    ext a
    rw [coefficientSection_apply]
    by_cases ha : standardCarrier a ≤ p
    · rw [if_pos ha, hx a (hQ ha hp)]
      rfl
    · rw [if_neg ha]
      rfl

include hs in
theorem lowerIdealBarycentricRestriction_ker (Q : FaceLowerIdeal P) :
    RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom = barycentricRestrictionIdeal K Q.carrier := by
  ext x
  constructor
  · intro hx
    change lowerIdealBarycentricRestriction K Q x = 0 at hx
    rw [barycentricRestrictionIdeal_mem_iff_coefficient K hs Q.carrier Q.lower]
    intro a ha
    have hh := lowerIdealBarycentricRestriction_coefficient K Q x (lowerIdealChainLift Q a ha)
    have he : (⟨(lowerIdealChainLift Q a ha).val.mapDomain (lowerIdealNonzeroEmbedding Q),
        lowerIdealChainEmbedding Q _ (lowerIdealChainLift Q a ha).property⟩ : StandardFaceIndex P) = a :=
      Subtype.ext (lowerIdealChainLift_map hs Q a ha)
    rw [hx, map_zero, Finsupp.zero_apply, he] at hh
    exact hh.symm
  · intro hx
    have hker : barycentricRestrictionIdeal K Q.carrier ≤
        RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨p, hp, rfl⟩
      exact lowerIdealBarycentricRestriction_generator_outside K Q p hp
    exact hker hx

theorem lowerIdealBarycentricRestriction_surjective (Q : FaceLowerIdeal P) :
    Function.Surjective (lowerIdealBarycentricRestriction K Q) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (barycentricIdeal (P := P) K)
    (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q) f), ?_⟩
  rw [lowerIdealBarycentricRestriction_mk,
    MvPolynomial.killCompl_rename_app (lowerIdealNonzeroEmbedding Q).injective]

def lowerIdealBarycentricQuotientEquiv (Q : FaceLowerIdeal P) :
    barycentricRestrictionQuotient K Q.carrier ≃ₐ[K] BarycentricRing (P := Q) K :=
  (Ideal.quotientEquivAlgOfEq K (lowerIdealBarycentricRestriction_ker K hs Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lowerIdealBarycentricRestriction_surjective K Q))

theorem universalOriginalParameterComparison_lowerIdealKernel (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : FaceLowerIdeal P)
    (x : BarycentricRing (P := P) K) :
    lowerIdealFaceRestriction K hs Q
        ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) = 0 ↔
      lowerIdealBarycentricRestriction K Q x = 0 := by
  change _ ∈ RingHom.ker (lowerIdealFaceRestriction K hs Q).toRingHom ↔
    x ∈ RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom
  rw [lowerIdealFaceRestriction_ker, lowerIdealBarycentricRestriction_ker K hs]
  exact (Ideal.Quotient.eq_zero_iff_mem.symm).trans
    ((universalOriginalParameterComparison_restrictionKernel K hs d hrank Q.carrier Q.lower x).trans
      Ideal.Quotient.eq_zero_iff_mem)

end FourPapers.Universal

end
end

/- BEGIN OriginalTensorBaseChange.lean -/
section

/-! # Actual tensor extension from the integral quotient rings

The comparison family commutes with usual coefficient maps.  Here these maps
are identified with the canonical maps into genuine tensor-product scalar
extensions, using the already established integral standard bases.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical MvPolynomial
open scoped TensorProduct
variable {I M N K : Type*} [CommRing K]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module K N]

def additiveIntegralSemilinear (f : M →+ N) : M →ₛₗ[Int.castRingHom K] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    exact map_intCast_smul f ℤ K c x

def integralBasisTensorEquiv (b : Module.Basis I ℤ M) (c : Module.Basis I K N) :
    K ⊗[ℤ] M ≃ₗ[K] N :=
  (b.baseChange K).repr.trans c.repr.symm

theorem integralBasisTensorEquiv_tmul
    (b : Module.Basis I ℤ M) (c : Module.Basis I K N)
    (f : M →ₛₗ[Int.castRingHom K] N) (hf : ∀ i, f (b i) = c i)
    (a : K) (x : M) :
    integralBasisTensorEquiv b c (a ⊗ₜ[ℤ] x) = a • f x := by
  apply c.repr.injective
  simp only [integralBasisTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext i
  rw [Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    basis_repr_baseChange (Int.castRingHom K) b c f hf, Finsupp.mapRange_apply]
  change (b.repr x i) • a = a * (b.repr x i : K)
  rw [Algebra.smul_def, mul_comm]
  rfl

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

theorem originalFaceCoefficientChange_standardBasis {L : Type*} [CommRing L]
    (h : K →+* L) (a : StandardFaceIndex P) :
    originalFaceCoefficientChange hs h (standardFaceBasis K hs a) = standardFaceBasis L hs a := by
  rw [standardFaceBasis_apply, standardFaceBasis_apply]
  change originalFaceCoefficientChange hs h
    (Ideal.Quotient.mk (faceIdeal K hs) (monomial a.val 1)) = _
  rw [originalFaceCoefficientChange_mk, MvPolynomial.map_monomial, map_one]
  rfl

theorem originalBarycentricCoefficientChange_standardBasis {L : Type*} [CommRing L]
    (h : K →+* L) (a : StandardFaceIndex P) :
    originalBarycentricCoefficientChange h (barycentricGlobalStandardBasis K a) =
      barycentricGlobalStandardBasis L a := by
  rw [← barycentricGlobalStandardBasis_monomial, ← barycentricGlobalStandardBasis_monomial,
    originalBarycentricCoefficientChange_mk, MvPolynomial.map_monomial, map_one]

def faceIntegralTensorEquiv :
    K ⊗[ℤ] FaceRing ℤ hs ≃ₗ[K] FaceRing K hs :=
  integralBasisTensorEquiv (standardFaceBasis ℤ hs) (standardFaceBasis K hs)

def barycentricIntegralTensorEquiv :
    K ⊗[ℤ] BarycentricRing (P := P) ℤ ≃ₗ[K] BarycentricRing (P := P) K :=
  integralBasisTensorEquiv (barycentricGlobalStandardBasis ℤ) (barycentricGlobalStandardBasis K)

@[simp] theorem faceIntegralTensorEquiv_tmul (a : K) (x : FaceRing ℤ hs) :
    faceIntegralTensorEquiv K hs (a ⊗ₜ[ℤ] x) =
      a • originalFaceCoefficientChange hs (Int.castRingHom K) x :=
  integralBasisTensorEquiv_tmul (standardFaceBasis ℤ hs) (standardFaceBasis K hs)
    (additiveIntegralSemilinear (originalFaceCoefficientChange hs (Int.castRingHom K)).toAddMonoidHom)
    (originalFaceCoefficientChange_standardBasis ℤ hs (Int.castRingHom K)) a x

@[simp] theorem barycentricIntegralTensorEquiv_tmul (a : K)
    (x : BarycentricRing (P := P) ℤ) :
    barycentricIntegralTensorEquiv K (a ⊗ₜ[ℤ] x) =
      a • originalBarycentricCoefficientChange (Int.castRingHom K) x :=
  integralBasisTensorEquiv_tmul (barycentricGlobalStandardBasis ℤ) (barycentricGlobalStandardBasis K)
    (additiveIntegralSemilinear (originalBarycentricCoefficientChange (Int.castRingHom K)).toAddMonoidHom)
    (originalBarycentricCoefficientChange_standardBasis ℤ (Int.castRingHom K)) a x

/-- The family is the genuine tensor extension of its integral member.  No
flatness condition is used: both coefficient rings have the same proven basis. -/
theorem universalOriginalParameterComparison_tensorBaseChange (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d)
    (z : K ⊗[ℤ] BarycentricRing (P := P) ℤ) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricIntegralTensorEquiv K z) =
      faceIntegralTensorEquiv K hs
        ((universalOriginalParameterComparison ℤ hs d hrank).toLinearEquiv.toLinearMap.baseChange K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [barycentricIntegralTensorEquiv_tmul, LinearEquiv.map_smul,
        LinearMap.baseChange_tmul, faceIntegralTensorEquiv_tmul]
      exact congrArg (fun y => a • y)
        (universalOriginalParameterComparison_baseChange hs (Int.castRingHom K) d hrank x).symm

end Poset
end FourPapers.Universal

end
end

/- BEGIN TheoremOne.lean -/
section

/-! # Theorem 1.1 on the original presentations

All structure fields below are conclusions.  The only mathematical hypotheses
are finiteness, Boolean lower intervals, a commutative coefficient ring, and an
upper bound on face rank.  In particular the coefficient ring need not be a
field, reduced, nonzero, or flat over the integers.

The direction of the equivalence is barycentric to original; its inverse gives
the orientation displayed in the paper.  The grading and filtration are images
of the actual weighted polynomial pieces under the quotient presentations.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open scoped TensorProduct
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem canonicalOriginalComparison_usualFiltered (d : ℕ) (n : ℤ)
    (x : BarycentricRing (P := P) K) :
    canonicalOriginalComparison K hs x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n := by
  rw [usualFaceWeightLevel_eq, usualBarycentricWeightLevel_eq]
  exact canonicalOriginalComparison_filtered K hs d n x

/-- Equality of the induced maps on actual successive quotient modules of the
filtration assigned to the generators in the original polynomial presentations. -/
theorem universalOriginalParameterComparison_usualAssociatedGrade (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) :
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
      (universalOriginalParameterComparison_usualWeight K hs d hrank) n =
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_usualFiltered K hs d) n := by
  apply weightFiltrationGradeEquiv_eq_of_error_lower
  intro x hx
  rw [usualFaceWeightLevel_eq]
  rw [usualBarycentricWeightLevel_eq] at hx
  exact universalOriginalParameterComparison_error_lower K hs d hrank n x hx

/-- A faithful package of every assertion of Theorem 1.1.  The parameter actions
in `parameterEquiv` send the variable indexed by `i : Fin d` to the sum of the
face generators of rank `i+1`.  Its `overParameters` is an ordinary linear
equivalence over `MvPolynomial (Fin d) K` with exactly those scalar actions. -/
structure TheoremOneComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) where
  parameterEquiv : ParameterEquiv (barycentricParameterAction (P := P) K d)
    (faceParameterAction K hs d)
  stalkEquiv : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)
  evaluation_compat : ∀ (x : BarycentricRing (P := P) K) (p : P),
    faceRingEvaluation K hs p (parameterEquiv.toLinearEquiv x) =
      stalkEquiv.component p (barycentricRingEvaluation K hs p x)
  graded : ∀ (n : ℕ) (x : BarycentricRing (P := P) K),
    parameterEquiv.toLinearEquiv x ∈ usualFaceDegreePiece K hs n ↔
      x ∈ usualBarycentricDegreePiece K n
  filtered : ∀ (n : ℤ) (x : BarycentricRing (P := P) K),
    parameterEquiv.toLinearEquiv x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n
  associatedGrade : ∀ n : ℤ,
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) parameterEquiv.toLinearEquiv filtered n =
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_usualFiltered K hs d) n
  relativeEquiv : ∀ Q : Set P,
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K]
      faceRelativeParameters K hs d Q
  relative_apply : ∀ (Q : Set P) (x : barycentricRelative K hs Q),
    (relativeEquiv Q x).val = parameterEquiv.toLinearEquiv x.val
  lowerIdealKernel : ∀ (Q : FaceLowerIdeal P) (x : BarycentricRing (P := P) K),
    lowerIdealFaceRestriction K hs Q (parameterEquiv.toLinearEquiv x) = 0 ↔
      lowerIdealBarycentricRestriction K Q x = 0
  everyRestrictionKernel : ∀ (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K),
    faceRestrictionMap K hs Q (parameterEquiv.toLinearEquiv x) = 0 ↔
      barycentricRestrictionMap K Q x = 0
  integral : ∀ z : K ⊗[ℤ] BarycentricRing (P := P) ℤ,
    parameterEquiv.toLinearEquiv (barycentricIntegralTensorEquiv K z) =
      faceIntegralTensorEquiv K hs
        ((universalOriginalParameterComparison ℤ hs d hrank).toLinearEquiv.toLinearMap.baseChange K z)

/-- The single coherent integral construction, extended by scalars and then
identified with the ordinary quotient presentations. -/
def theoremOneComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    TheoremOneComparison K hs d hrank where
  parameterEquiv := universalOriginalParameterComparison K hs d hrank
  stalkEquiv := universalCoherentComparison K hs d hrank
  evaluation_compat := originalComparison_evaluation K hs
    (universalCoherentComparison K hs d hrank)
  graded := universalOriginalParameterComparison_usualDegree K hs d hrank
  filtered := universalOriginalParameterComparison_usualWeight K hs d hrank
  associatedGrade := universalOriginalParameterComparison_usualAssociatedGrade K hs d hrank
  relativeEquiv := universalOriginalRelativeParameterComparison K hs d hrank
  relative_apply := fun _ _ => rfl
  lowerIdealKernel := universalOriginalParameterComparison_lowerIdealKernel K hs d hrank
  everyRestrictionKernel := universalOriginalParameterComparison_restrictionKernel K hs d hrank
  integral := universalOriginalParameterComparison_tensorBaseChange K hs d hrank

/-- **Theorem 1.1.**  A coherent graded parameter-module equivalence, integral
base change, the prescribed associated graded map, and every relative kernel,
for every finite simplicial poset and every commutative coefficient ring. -/
theorem theorem_1_1 (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    Nonempty (TheoremOneComparison K hs d hrank) :=
  ⟨theoremOneComparison K hs d hrank⟩

/-- The actual polynomial-parameter-module isomorphism in the paper's displayed
direction.  Grading, filtration and coherence are supplied by `theorem_1_1`. -/
def theoremOneParameterModuleEquiv (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    FaceRing K hs ≃ₗ[MvPolynomial (Fin d) K] BarycentricRing (P := P) K :=
  (theoremOneComparison K hs d hrank).parameterEquiv.symm.overParameters

end FourPapers.Universal

end
end

#print axioms FourPapers.Universal.universalOriginalParameterComparison

#print axioms FourPapers.Universal.universalCoherentComparison_spec

#print axioms FourPapers.Universal.universalCoherentComparison_baseChange

#print axioms FourPapers.Universal.originalRelativeComparison

#print axioms FourPapers.Universal.universalOriginalRelativeParameterComparison

#print axioms FourPapers.Universal.universalOriginalParameterComparison_leading

#print axioms FourPapers.Universal.universalOriginalParameterComparison_degree

#print axioms FourPapers.Universal.universalOriginalParameterComparison_associatedGrade

#print axioms FourPapers.Universal.universalOriginalParameterComparison_baseChange

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualDegree

#print axioms FourPapers.Universal.faceRestrictionIdeal_mem_iff

#print axioms FourPapers.Universal.barycentricRestrictionIdeal_mem_iff

#print axioms FourPapers.Universal.universalOriginalParameterComparison_restrictionKernel

#print axioms FourPapers.Universal.usualFaceWeightLevel_eq

#print axioms FourPapers.Universal.usualBarycentricWeightLevel_eq

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualWeight

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_generator_inside

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_generator_outside

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_ker

#print axioms FourPapers.Universal.lowerIdealFaceQuotientEquiv

#print axioms FourPapers.Universal.lowerIdealBarycentricQuotientEquiv

#print axioms FourPapers.Universal.universalOriginalParameterComparison_lowerIdealKernel

#print axioms FourPapers.Universal.faceIntegralTensorEquiv_tmul

#print axioms FourPapers.Universal.barycentricIntegralTensorEquiv_tmul

#print axioms FourPapers.Universal.universalOriginalParameterComparison_tensorBaseChange

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualAssociatedGrade

#print axioms FourPapers.Universal.theorem_1_1

#print axioms FourPapers.Universal.theoremOneParameterModuleEquiv

end
end

/- BEGIN FourPapers/Universal/PrimeCycleFlags.lean -/
section

section
/-! # A prime cycle has no fixed sufficiently fine rank flag

The moved vertices are exactly `ZMod p`; the remaining `r` vertices are fixed.
A nonidentity translation is transitive on the moved vertices because p is
prime.  A flag whose successive rank gaps are less than p therefore cannot
be fixed.  All statements quantify over arbitrary prime p and every r > 0.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable (p r : ℕ) [Fact p.Prime]

abbrev PrimeCycleVertex := ZMod p ⊕ Fin r
abbrev PrimeCycleGroup := Multiplicative (ZMod p)

def primeCyclePermutation : PrimeCycleGroup p →* Equiv.Perm (PrimeCycleVertex p r) where
  toFun g := Equiv.sumCongr (Equiv.addLeft g.toAdd) (Equiv.refl (Fin r))
  map_one' := by
    ext x
    rcases x with x | x <;> simp
  map_mul' g h := by
    ext x
    rcases x with x | x <;> simp [add_assoc]

@[simp] theorem primeCyclePermutation_inl (g : PrimeCycleGroup p) (a : ZMod p) :
    primeCyclePermutation p r g (.inl a) = .inl (g.toAdd + a) := rfl

@[simp] theorem primeCyclePermutation_inr (g : PrimeCycleGroup p) (a : Fin r) :
    primeCyclePermutation p r g (.inr a) = .inr a := rfl

/-- Every nonidentity translation is transitive on the moved vertices. -/
theorem primeCycle_fixed_subset_all_moved (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (F : Finset (PrimeCycleVertex p r))
    (hF : F.image (primeCyclePermutation p r g) = F)
    (a : ZMod p) (ha : Sum.inl a ∈ F) : ∀ b : ZMod p, Sum.inl b ∈ F := by
  have hg0 : g.toAdd ≠ 0 := by
    intro h
    apply hg
    exact congrArg Multiplicative.ofAdd h
  have hstep : ∀ x ∈ F, primeCyclePermutation p r g x ∈ F := by
    intro x hx
    rw [← hF]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hn : ∀ n : ℕ, Sum.inl ((n : ZMod p) * g.toAdd + a) ∈ F := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      have hh := hstep _ ih
      simpa only [primeCyclePermutation_inl, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_assoc, add_left_comm] using hh
  intro b
  obtain ⟨n, hn'⟩ := ZMod.natCast_zmod_surjective ((b - a) / g.toAdd)
  have he : (n : ZMod p) * g.toAdd + a = b := by
    rw [hn', div_mul_cancel₀ _ hg0, sub_add_cancel]
  exact he ▸ hn n

def movedVertices : Finset (PrimeCycleVertex p r) := Finset.univ.image Sum.inl

@[simp] theorem movedVertices_card : (movedVertices p r).card = p := by
  rw [movedVertices, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ, ZMod.card]

/-- A rank set has a preceding selected rank within distance p.  Rank zero
is the empty face and need not belong to the selected set. -/
def PrimeFineRanks (p : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n → ∃ m, m < n ∧ (m = 0 ∨ m ∈ S) ∧ n - m < p

/-- A literal chain of subsets with exactly the prescribed ranks. -/
structure RankFlag (V : Type*) (S : Finset ℕ) where
  face : {i : ℕ // i ∈ S} → Finset V
  card : ∀ i, (face i).card = i.val
  nested : ∀ i j, i.val ≤ j.val → face i ⊆ face j

theorem primeCycle_fixed_flag_no_moved (S : Finset ℕ) (hS : PrimeFineRanks p S)
    (F : RankFlag (PrimeCycleVertex p r) S)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfixed : ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i) :
    ∀ i (a : ZMod p), Sum.inl a ∉ F.face i := by
  have hmain : ∀ n, ∀ hn : n ∈ S, ∀ a : ZMod p, Sum.inl a ∉ F.face ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn a ha
      have hn0 : 0 < n := by
        have hp := Finset.card_pos.mpr ⟨Sum.inl a, ha⟩
        rwa [F.card] at hp
      obtain ⟨m, hmn, hm, hgap⟩ := hS n hn hn0
      have hall : movedVertices p r ⊆ F.face ⟨n, hn⟩ := by
        rintro x hx
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
        exact primeCycle_fixed_subset_all_moved p r g hg _ (hfixed ⟨n, hn⟩) a ha b
      rcases hm with rfl | hm
      · have hp := Finset.card_le_card hall
        rw [movedVertices_card, F.card] at hp
        change p ≤ n at hp
        omega
      · have hnone : Disjoint (movedVertices p r) (F.face ⟨m, hm⟩) := by
          apply Finset.disjoint_left.mpr
          intro x hx hxm
          obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
          exact ih m hmn hm b hxm
        have hsub : movedVertices p r ⊆ F.face ⟨n, hn⟩ \ F.face ⟨m, hm⟩ := by
          intro x hx
          exact Finset.mem_sdiff.mpr ⟨hall hx, Finset.disjoint_left.mp hnone hx⟩
        have hp := Finset.card_le_card hsub
        rw [movedVertices_card, Finset.card_sdiff_of_subset (F.nested _ _ hmn.le),
          F.card, F.card] at hp
        change p ≤ n - m at hp
        omega
  intro i a
  exact hmain i.val i.property a

/-- With the full rank selected, the preceding statement excludes every
nonidentity stabilizer of the actual rank flag. -/
theorem primeCycle_rankFlag_not_fixed (S : Finset ℕ) (hS : PrimeFineRanks p S)
    (htop : p + r ∈ S) (F : RankFlag (PrimeCycleVertex p r) S)
    (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    ¬ ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i := by
  intro hfixed
  have hcard : (F.face ⟨p + r, htop⟩).card = Fintype.card (PrimeCycleVertex p r) := by
    rw [F.card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
  have hfull : F.face ⟨p + r, htop⟩ = Finset.univ :=
    (F.face ⟨p + r, htop⟩).eq_univ_of_card hcard
  have hnone := primeCycle_fixed_flag_no_moved p r S hS F g hg hfixed ⟨p + r, htop⟩ 0
  exact hnone (by rw [hfull]; exact Finset.mem_univ _)

/-- These are exactly the positive coefficient ranks of
`(1+T^p) ∏(1+b_i T)` for algebraically independent b_i. -/
def primeCycleActiveRanks : Finset ℕ :=
  (Finset.Icc 1 r) ∪ Finset.Icc p (p + r)

theorem primeCycleActiveRanks_fine (hr : 0 < r) :
    PrimeFineRanks p (primeCycleActiveRanks p r) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  intro n hn hn0
  rcases Finset.mem_union.mp hn with hn | hn
  · have hn' := Finset.mem_Icc.mp hn
    refine ⟨n - 1, by omega, ?_, by omega⟩
    by_cases he : n = 1
    · left
      omega
    · right
      apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · have hn' := Finset.mem_Icc.mp hn
    by_cases he : n = p
    · by_cases hrp : r < p
      · refine ⟨r, by omega, Or.inr ?_, by omega⟩
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hr, le_rfl⟩)
      · refine ⟨p - 1, by omega, Or.inr ?_, by omega⟩
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · refine ⟨n - 1, by omega, Or.inr ?_, by omega⟩
      exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem primeCycleActiveRanks_top : p + r ∈ primeCycleActiveRanks p r :=
  Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨Nat.le_add_right p r, le_rfl⟩)

/-- The concrete prime-cycle active ranks have no fixed flag. -/
theorem primeCycleActiveFlag_not_fixed (hr : 0 < r)
    (F : RankFlag (PrimeCycleVertex p r) (primeCycleActiveRanks p r))
    (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    ¬ ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i :=
  primeCycle_rankFlag_not_fixed p r _ (primeCycleActiveRanks_fine p r hr)
    (primeCycleActiveRanks_top p r) F g hg

end FourPapers.Universal

#print axioms FourPapers.Universal.primeCycle_fixed_subset_all_moved

#print axioms FourPapers.Universal.primeCycleActiveRanks_fine

#print axioms FourPapers.Universal.primeCycleActiveFlag_not_fixed

end
end
end

/- BEGIN FourPapers/Universal/ColorfulMonomials.lean -/
section

section
/-! # Proper coloring and the actual color-graded monomial basis

The indexing equivalence in this file uses the usual sum of vertex exponents
of each color.  Its inverse assigns the given color exponent to the unique
vertex of that color in a face.  It applies to arbitrary finite properly
colored complexes, including rank-colored order complexes.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {V C : Type*} [Fintype V] [Fintype C]

structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)

namespace ProperlyColoredComplex
variable (D : ProperlyColoredComplex V C)

def allowed (a : V →₀ ℕ) : Prop := D.face a.support

theorem allowed_divisorClosed : IsDivisorClosed D.allowed := by
  intro a b hab hb
  exact D.downward (Finsupp.support_mono hab) hb

def colorDegree (a : V →₀ ℕ) : C →₀ ℕ := a.mapDomain D.color

theorem colorDegree_support (a : V →₀ ℕ) :
    (D.colorDegree a).support = a.support.image D.color :=
  Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _) D.color

theorem colorDegree_at_vertex (a : V →₀ ℕ) (ha : D.allowed a) (v : V)
    (hv : v ∈ a.support) : D.colorDegree a (D.color v) = a v := by
  exact Finsupp.mapDomain_apply' (a.support : Set V) a (fun _ h => h)
    (D.proper a.support ha) hv

abbrev FaceWithColors (S : Finset C) :=
  {s : Finset V // D.face s ∧ s.image D.color = S}

abbrev MonomialOfColorDegree (β : C →₀ ℕ) :=
  {a : V →₀ ℕ // D.allowed a ∧ D.colorDegree a = β}

def exponentOnFace (β : C →₀ ℕ) (s : Finset V) : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => if v ∈ s then β (D.color v) else 0)

@[simp] theorem exponentOnFace_apply (β : C →₀ ℕ) (s : Finset V) (v : V) :
    D.exponentOnFace β s v = if v ∈ s then β (D.color v) else 0 := rfl

theorem exponentOnFace_support (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    (D.exponentOnFace β s.val).support = s.val := by
  ext v
  rw [Finsupp.mem_support_iff, exponentOnFace_apply]
  by_cases hv : v ∈ s.val
  · rw [if_pos hv]
    have hc : D.color v ∈ β.support := by
      rw [← s.property.2]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact iff_of_true (Finsupp.mem_support_iff.mp hc) hv
  · simp [hv]

theorem exponentOnFace_allowed (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    D.allowed (D.exponentOnFace β s.val) := by
  unfold allowed
  rw [exponentOnFace_support]
  exact s.property.1

theorem exponentOnFace_colorDegree (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    D.colorDegree (D.exponentOnFace β s.val) = β := by
  ext i
  by_cases hi : i ∈ β.support
  · have his : i ∈ s.val.image D.color := s.property.2.symm ▸ hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp his
    rw [D.colorDegree_at_vertex _ (D.exponentOnFace_allowed β s) v
      (by rw [D.exponentOnFace_support]; exact hv), exponentOnFace_apply, if_pos hv]
  · have hi' : i ∉ (D.colorDegree (D.exponentOnFace β s.val)).support := by
      rw [D.colorDegree_support, D.exponentOnFace_support, s.property.2]
      exact hi
    rw [Finsupp.notMem_support_iff.mp hi', Finsupp.notMem_support_iff.mp hi]

/-- The genuine color degree piece is indexed by faces having exactly the
positive colors, for arbitrary exponents and arbitrary coefficient rings. -/
def monomialColorEquiv (β : C →₀ ℕ) :
    D.MonomialOfColorDegree β ≃ D.FaceWithColors β.support where
  toFun a := ⟨a.val.support, a.property.1, by
    rw [← D.colorDegree_support, a.property.2]⟩
  invFun s := ⟨D.exponentOnFace β s.val, D.exponentOnFace_allowed β s,
    D.exponentOnFace_colorDegree β s⟩
  left_inv a := by
    apply Subtype.ext
    ext v
    rw [D.exponentOnFace_apply]
    by_cases hv : v ∈ a.val.support
    · rw [if_pos hv]
      have hh := congrArg (fun γ : C →₀ ℕ => γ (D.color v)) a.property.2
      exact hh.symm.trans (D.colorDegree_at_vertex a.val a.property.1 v hv)
    · rw [if_neg hv, Finsupp.notMem_support_iff.mp hv]
  right_inv s := Subtype.ext (D.exponentOnFace_support β s)

variable (K : Type*) [CommRing K]

abbrev Ring := MonomialQuotient (K := K) D.allowed

def monomial (a : V →₀ ℕ) : D.Ring K :=
  Ideal.Quotient.mk (forbiddenIdeal D.allowed) (MvPolynomial.monomial a (1 : K))

def colorParameter (i : C) : D.Ring K :=
  ∑ v ∈ Finset.univ.filter (fun v => D.color v = i),
    Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v)

theorem monomial_eq_zero_of_forbidden (a : V →₀ ℕ) (ha : ¬ D.allowed a) :
    D.monomial K a = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨a, ha, rfl⟩

theorem variable_mul_monomial (v : V) (a : V →₀ ℕ) :
    Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v) * D.monomial K a =
      D.monomial K (Finsupp.single v 1 + a) := by
  rw [monomial, ← map_mul]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  rfl

theorem color_collision_forbidden (a : V →₀ ℕ) (ha : D.allowed a)
    (v w : V) (hw : w ∈ a.support) (hc : D.color v = D.color w) (hne : v ≠ w) :
    ¬ D.allowed (Finsupp.single v 1 + a) := by
  intro hall
  have hface : D.face ((Finsupp.single v 1 + a).support) := hall
  have hproper := D.proper ((Finsupp.single v 1 + a).support) hface
  have hv : v ∈ (Finsupp.single v 1 + a).support := by
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hw' : w ∈ (Finsupp.single v 1 + a).support :=
    Finsupp.support_mono (le_add_self : a ≤ Finsupp.single v 1 + a) hw
  exact hne (hproper hv hw' hc)

/-- Once a color is already present, multiplication by its color sum raises
exactly the exponent of its unique vertex; every other summand is a nonface. -/
theorem colorParameter_mul_of_present (a : V →₀ ℕ) (ha : D.allowed a)
    (w : V) (hw : w ∈ a.support) :
    D.colorParameter K (D.color w) * D.monomial K a =
      D.monomial K (Finsupp.single w 1 + a) := by
  rw [colorParameter, Finset.sum_mul]
  rw [Finset.sum_eq_single w]
  · exact D.variable_mul_monomial K w a
  · intro v hv hvw
    rw [D.variable_mul_monomial]
    exact D.monomial_eq_zero_of_forbidden K _
      (D.color_collision_forbidden a ha v w hw (Finset.mem_filter.mp hv).2 hvw)
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl⟩)).elim

end ProperlyColoredComplex

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The rank-selected order complex, with its actual proper rank coloring. -/
def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FiniteOrbitObstruction.lean -/
section

section

/-! # A direct modular obstruction from freely permuted components

An invariant functional vanishes on invariant vectors when the identity is a
sum of freely permuted component operators and the group order is zero in the
coefficient ring. No group-algebra projectivity criterion is required.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {G T K M N : Type*} [Group G] [Fintype G] [Fintype T]
  [MulAction G T] [CommRing K]

/-- A free orbit is explicitly in bijection with the acting group. -/
def freeOrbitEquiv (hfree : ∀ t : T, Function.Injective (fun g : G => g • t)) (t : T) :
    G ≃ MulAction.orbit G t :=
  Equiv.ofBijective (fun g => ⟨g • t, MulAction.mem_orbit t g⟩)
    ⟨fun g h he => hfree t (congrArg Subtype.val he), by
      rintro ⟨s, hs⟩
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hs
      exact ⟨g, Subtype.ext hg⟩⟩

theorem sum_eq_zero_of_free_action
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0) (f : T → K)
    (hf : ∀ (g : G) (t : T), f (g • t) = f t) : ∑ t, f t = 0 := by
  let Q := MulAction.orbitRel.Quotient G T
  letI : Fintype Q := Fintype.ofFinite _
  letI (q : Q) : Fintype (MulAction.orbit G q.out) := Fintype.ofFinite _
  calc
    (∑ t, f t) = ∑ q : (Σ q : Q, MulAction.orbit G q.out), f q.2.val :=
      Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits G T) _ _ (fun _ => rfl)
    _ = ∑ q : Q, ∑ t : MulAction.orbit G q.out, f t.val := Fintype.sum_sigma _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have he := Fintype.sum_equiv (freeOrbitEquiv hfree q.out)
        (fun g : G => f (g • q.out))
        (fun t : MulAction.orbit G q.out => f t.val) (fun _ => rfl)
      rw [← he]
      simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, horder, zero_mul]

variable [AddCommGroup M] [Module K M]

/-- A partition of the identity into component operators is enough for the
obstruction; orthogonality and idempotence need not be assumed here. -/
theorem invariantFunctional_eq_zero_of_free_components
    (ρ : G →* Module.End K M) (component : T → Module.End K M)
    (hidentity : ∀ x, ∑ t, component t x = x)
    (hcovariant : ∀ g t x, component (g • t) (ρ g x) = ρ g (component t x))
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0)
    (ℓ : M →ₗ[K] K) (hℓ : ∀ g x, ℓ (ρ g x) = ℓ x)
    (v : M) (hv : ∀ g, ρ g v = v) : ℓ v = 0 := by
  have hf : ∀ (g : G) (t : T), ℓ (component (g • t) v) = ℓ (component t v) := by
    intro g t
    calc
      ℓ (component (g • t) v) = ℓ (component (g • t) (ρ g v)) := by rw [hv]
      _ = ℓ (ρ g (component t v)) := congrArg ℓ (hcovariant g t v)
      _ = ℓ (component t v) := hℓ g (component t v)
  calc
    ℓ v = ℓ (∑ t, component t v) := congrArg ℓ (hidentity v).symm
    _ = ∑ t, ℓ (component t v) := map_sum ℓ _ _
    _ = 0 := sum_eq_zero_of_free_action hfree horder _ hf

variable [AddCommGroup N] [Module K N] [Nontrivial K]

/-- An equivariant augmentation split by an invariant vector cannot be
transported to such a freely decomposed module in modular characteristic. -/
theorem no_equivariant_equiv_of_free_components
    (ρM : G →* Module.End K M) (ρN : G →* Module.End K N)
    (component : T → Module.End K N)
    (hidentity : ∀ x, ∑ t, component t x = x)
    (hcovariant : ∀ g t x, component (g • t) (ρN g x) = ρN g (component t x))
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0)
    (ℓ : M →ₗ[K] K) (hℓ : ∀ g x, ℓ (ρM g x) = ℓ x)
    (v : M) (hv : ∀ g, ρM g v = v) (hvalue : ℓ v = 1)
    (e : M ≃ₗ[K] N) (he : ∀ g x, e (ρM g x) = ρN g (e x)) : False := by
  have hinv : ∀ g, ρN g (e v) = e v := by
    intro g
    rw [← he, hv]
  have heInv : ∀ g x, e.symm (ρN g x) = ρM g (e.symm x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hfunctional : ∀ g x, (ℓ.comp e.symm.toLinearMap) (ρN g x) =
      (ℓ.comp e.symm.toLinearMap) x := by
    intro g x
    change ℓ (e.symm (ρN g x)) = ℓ (e.symm x)
    rw [heInv, hℓ]
  have hzero := invariantFunctional_eq_zero_of_free_components ρN component
    hidentity hcovariant hfree horder (ℓ.comp e.symm.toLinearMap) hfunctional (e v) hinv
  have hone : (1 : K) = 0 := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      hvalue] using hzero
  exact one_ne_zero hone

end FourPapers.Universal
end
end
end

/- BEGIN FourPapers/Universal/CyclicRankReduction.lean -/
section


section

/-! # Only prime top rank needs modular lifting

If `(d - 1)!` is invertible, ordinary averaging is available in every smaller
rank.  It is also available in rank `d` unless `d` itself is prime.  The only
remaining local construction is therefore the regular action of a cyclic
group of prime order on a simplex of that same rank.
-/

namespace FourPapers.Universal

variable {K : Type*} [CommRing K]

theorem lower_rank_factorial_isUnit {d r : ℕ} (hrd : r < d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((r.factorial : ℕ) : K) := by
  apply isUnit_of_dvd_unit _ hD
  exact map_dvd (Nat.castRingHom K)
    (Nat.factorial_dvd_factorial (by omega : r ≤ d - 1))

theorem composite_rank_isUnit {d : ℕ} (hd : 1 ≤ d) (hp : ¬d.Prime)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) : IsUnit (d : K) := by
  by_cases hdone : d = 1
  · subst d
    simp
  have hd2 : 2 ≤ d := by omega
  obtain ⟨a, b, had, hbd, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hd2).mp hp
  have ha : 0 < a := by
    by_contra hn
    have hzero : a = 0 := by omega
    simp [hzero] at hab
    omega
  have hb : 0 < b := by
    by_contra hn
    have hzero : b = 0 := by omega
    simp [hzero] at hab
    omega
  have hau : IsUnit (a : K) := isUnit_of_dvd_unit
    (map_dvd (Nat.castRingHom K) (Nat.dvd_factorial ha (by omega : a ≤ d - 1))) hD
  have hbu : IsUnit (b : K) := isUnit_of_dvd_unit
    (map_dvd (Nat.castRingHom K) (Nat.dvd_factorial hb (by omega : b ≤ d - 1))) hD
  simpa only [← Nat.cast_mul, hab] using hau.mul hbu

theorem full_factorial_isUnit_or_prime {d : ℕ} (hd : 1 ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((d.factorial : ℕ) : K) ∨ d.Prime := by
  by_cases hp : d.Prime
  · exact Or.inr hp
  · left
    have hu := (composite_rank_isUnit hd hp hD).mul hD
    simpa only [← Nat.cast_mul, Nat.mul_factorial_pred (by omega : d ≠ 0)] using hu

/-- The exact exceptional branch needed for the positive implication of
Theorem 1.3. -/
theorem factorial_rank_exception {d r : ℕ} (hd : 1 ≤ d) (hrd : r ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((r.factorial : ℕ) : K) ∨ (r = d ∧ d.Prime) := by
  rcases lt_or_eq_of_le hrd with hlt | rfl
  · exact Or.inl (lower_rank_factorial_isUnit hlt hD)
  · rcases full_factorial_isUnit_or_prime hd hD with hu | hp
    · exact Or.inl hu
    · exact Or.inr ⟨rfl, hp⟩

end FourPapers.Universal

end
end

/- BEGIN FourPapers/Universal/CyclicRelativeInjectivity.lean -/
section


section

/-! # Relative injectivity of regular permutation modules

The extension in this file is the elementary coinduction argument used in
Section 8 of the paper.  The inclusion is required only to split over the
coefficient ring; its chosen splitting need not be equivariant.
-/

noncomputable section

namespace FourPapers.Universal

/-- A linear group representation, definitionally the standard Mathlib `Representation`. -/
abbrev CyclicRepresentation (K G M : Type*) [CommRing K] [Group G]
    [AddCommGroup M] [Module K M] := G →* (M →ₗ[K] M)

variable {K G M N C T : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup C] [Module K C] [AddCommGroup T] [Module K T]

/-- Left translation on functions, in the usual contragredient convention. -/
def coinducedRepresentation : CyclicRepresentation K G (G → C) where
  toFun g :=
    { toFun := fun f h => f (g⁻¹ * h)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]

@[simp] theorem coinducedRepresentation_apply (g : G) (f : G → C) (h : G) :
    coinducedRepresentation (K := K) (C := C) g f h = f (g⁻¹ * h) := rfl

/-- Equivariance of a coefficient-linear map between two representations. -/
def RepresentationIntertwines (ρ : CyclicRepresentation K G M)
    (τ : CyclicRepresentation K G N) (f : M →ₗ[K] N) : Prop :=
  ∀ g x, f (ρ g x) = τ g (f x)

/-- Coinduction extends a map using just the identity coordinate. -/
def coinducedExtension (ρ : CyclicRepresentation K G N)
    (s : N →ₗ[K] M) (f : M →ₗ[K] (G → C)) : N →ₗ[K] (G → C) where
  toFun n h := f (s (ρ h⁻¹ n)) 1
  map_add' x y := by ext h; simp
  map_smul' a x := by ext h; simp

theorem coinducedExtension_equivariant (ρ : CyclicRepresentation K G N)
    (s : N →ₗ[K] M) (f : M →ₗ[K] (G → C)) :
    RepresentationIntertwines ρ coinducedRepresentation (coinducedExtension ρ s f) := by
  intro g n
  ext h
  change f (s (ρ h⁻¹ (ρ g n))) 1 = f (s (ρ (g⁻¹ * h)⁻¹ n)) 1
  rw [mul_inv_rev, inv_inv, ρ.map_mul]
  rfl

theorem coinducedExtension_restrict
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (G → C))
    (hf : RepresentationIntertwines ρ coinducedRepresentation f) :
    (coinducedExtension τ s f).comp i = f := by
  ext m h
  change f (s (τ h⁻¹ (i m))) 1 = f m h
  rw [← hi]
  have hsi : s (i (ρ h⁻¹ m)) = ρ h⁻¹ m :=
    congrArg (fun q : M →ₗ[K] M => q (ρ h⁻¹ m)) hs
  rw [hsi]
  have hh := congrFun (hf h⁻¹ m) 1
  simpa only [coinducedRepresentation_apply, inv_inv, mul_one] using hh

/-- Every map into a coinduced module extends along an equivariant inclusion
that splits over the coefficient ring. -/
theorem exists_equivariantExtension_coinduced
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (G → C))
    (hf : RepresentationIntertwines ρ coinducedRepresentation f) :
    ∃ F : N →ₗ[K] (G → C),
      RepresentationIntertwines τ coinducedRepresentation F ∧ F.comp i = f :=
  ⟨coinducedExtension τ s f, coinducedExtension_equivariant τ s f,
    coinducedExtension_restrict ρ τ i s hi hs f hf⟩

/-- Relative injectivity is transported across an actual equivariant linear
equivalence; in applications its coordinates are the free orbits of a
permutation basis. -/
theorem exists_equivariantExtension_of_coinduced
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G T) (e : T ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines υ coinducedRepresentation e.toLinearMap)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] T) (hf : RepresentationIntertwines ρ υ f) :
    ∃ F : N →ₗ[K] T, RepresentationIntertwines τ υ F ∧ F.comp i = f := by
  have hf' : RepresentationIntertwines ρ coinducedRepresentation
      (e.toLinearMap.comp f) := by
    intro g m
    change e (f (ρ g m)) = coinducedRepresentation (K := K) (C := C) g (e (f m))
    have hh := he g (f m)
    change e (υ g (f m)) = coinducedRepresentation (K := K) (C := C) g (e (f m)) at hh
    exact (congrArg e (hf g m)).trans hh
  obtain ⟨F, hF, hFi⟩ := exists_equivariantExtension_coinduced ρ τ i s hi hs
    (e.toLinearMap.comp f) hf'
  refine ⟨e.symm.toLinearMap.comp F, ?_, ?_⟩
  · intro g n
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    have hh := he g (e.symm (F n))
    change e (υ g (e.symm (F n))) =
      coinducedRepresentation (K := K) (C := C) g (e (e.symm (F n))) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact (hF g n).trans hh.symm
  · ext m
    apply e.injective
    simpa using congrArg (fun q : M →ₗ[K] (G → C) => q m) hFi

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPermutationInjectivity.lean -/
section


section

/-! # Free permutation coordinates are coinduced

This file proves the free-orbit case of the relative-injectivity assertion in
Section 8.  No field assumption and no division by the group order occur.
-/

noncomputable section

namespace FourPapers.Universal

open Classical

variable {K G X : Type*} [CommRing K] [Group G] [MulAction G X]

def permutationFunctionRepresentation : CyclicRepresentation K G (X → K) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹ • x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    simp [mul_smul]

@[simp] theorem permutationFunctionRepresentation_apply (g : G) (f : X → K) (x : X) :
    permutationFunctionRepresentation (K := K) g f x = f (g⁻¹ • x) := rfl

theorem freeOrbitCoordinate_bijective
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    Function.Bijective
      (fun a : G × MulAction.orbitRel.Quotient G X => a.1 • a.2.out) := by
  constructor
  · rintro ⟨g, q⟩ ⟨h, r⟩ heq
    have hqr : q = r := by
      have h := congrArg (fun x : X => (Quotient.mk'' x :
        MulAction.orbitRel.Quotient G X)) heq
      simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq,
        Quotient.out_eq'] using h
    subst r
    change g • q.out = h • q.out at heq
    have hhg : h⁻¹ * g = 1 := hf _ q.out (by
      rw [mul_smul, heq, inv_smul_smul])
    have hgh : g = h := by
      calc
        g = h * (h⁻¹ * g) := by simp
        _ = h := by rw [hhg, mul_one]
    subst h
    rfl
  · intro x
    let q : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
    have hx : q.out ∈ MulAction.orbit G x :=
      Quotient.exact (Quotient.out_eq' q)
    obtain ⟨g, hg⟩ := hx
    refine ⟨(g⁻¹, q), ?_⟩
    change g⁻¹ • q.out = x
    rw [← hg, inv_smul_smul]

def freeOrbitCoordinateEquiv
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    (G × MulAction.orbitRel.Quotient G X) ≃ X :=
  Equiv.ofBijective _ (freeOrbitCoordinate_bijective hf)

@[simp] theorem freeOrbitCoordinateEquiv_apply
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1)
    (g : G) (q : MulAction.orbitRel.Quotient G X) :
    freeOrbitCoordinateEquiv hf (g, q) = g • q.out := rfl

/-- A free permutation representation is a product of regular function
representations, with one coordinate for each orbit. -/
def freePermutationCoinducedEquiv
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    (X → K) ≃ₗ[K] (G → MulAction.orbitRel.Quotient G X → K) where
  toFun f g q := f (g • q.out)
  invFun f x :=
    let a := (freeOrbitCoordinateEquiv hf).symm x
    f a.1 a.2
  left_inv f := by
    funext x
    change f (freeOrbitCoordinateEquiv hf
      ((freeOrbitCoordinateEquiv hf).symm x)) = f x
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    funext g q
    change f (((freeOrbitCoordinateEquiv hf).symm
      (freeOrbitCoordinateEquiv hf (g, q))).1)
      (((freeOrbitCoordinateEquiv hf).symm
      (freeOrbitCoordinateEquiv hf (g, q))).2) = f g q
    rw [Equiv.symm_apply_apply]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem freePermutationCoinducedEquiv_equivariant
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    RepresentationIntertwines permutationFunctionRepresentation coinducedRepresentation
      (freePermutationCoinducedEquiv (K := K) hf).toLinearMap := by
  intro g f
  ext h q
  change f (g⁻¹ • (h • q.out)) = f ((g⁻¹ * h) • q.out)
  rw [mul_smul]

variable {M N : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- The free permutation case of Section 8's relative injectivity statement,
proved by explicit regular-orbit coordinates. -/
theorem exists_equivariantExtension_freePermutation
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (X → K))
    (hf : RepresentationIntertwines ρ permutationFunctionRepresentation f) :
    ∃ F : N →ₗ[K] (X → K),
      RepresentationIntertwines τ permutationFunctionRepresentation F ∧ F.comp i = f :=
  exists_equivariantExtension_of_coinduced ρ τ permutationFunctionRepresentation
    (freePermutationCoinducedEquiv hfree)
    (freePermutationCoinducedEquiv_equivariant hfree) i s hi hs f hf

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicEquivariantChoice.lean -/
section


section

/-! # Equivariant choices from stabilizer-fixed local choices

Choices are made once on each orbit and transported.  The stabilizer
condition is proved sufficient for independence of the transporting group
element.  In the free-action case this condition is automatic.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

def orbitChoiceRepresentative (x : X) : X :=
  (Quotient.mk'' x : MulAction.orbitRel.Quotient G X).out

theorem exists_orbitChoiceTransport (x : X) :
    ∃ g : G, g • orbitChoiceRepresentative (G := G) x = x := by
  let q : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
  have hx : q.out ∈ MulAction.orbit G x := Quotient.exact (Quotient.out_eq' q)
  obtain ⟨g, hg⟩ := hx
  refine ⟨g⁻¹, ?_⟩
  change g⁻¹ • q.out = x
  rw [← hg, inv_smul_smul]

def orbitChoiceTransport (x : X) : G := (exists_orbitChoiceTransport (G := G) x).choose

theorem orbitChoiceTransport_spec (x : X) :
    orbitChoiceTransport (G := G) x • orbitChoiceRepresentative (G := G) x = x :=
  (exists_orbitChoiceTransport (G := G) x).choose_spec

theorem orbitChoiceRepresentative_smul (g : G) (x : X) :
    orbitChoiceRepresentative (G := G) (g • x) = orbitChoiceRepresentative (G := G) x := by
  unfold orbitChoiceRepresentative
  apply congrArg (fun q : MulAction.orbitRel.Quotient G X => q.out)
  apply Quotient.sound
  exact ⟨g, rfl⟩

theorem exists_equivariant_choice (R : X → Y → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hfixed : ∀ x : X, ∃ y : Y, R x y ∧ ∀ g : G, g • x = x → g • y = y) :
    ∃ f : X → Y, (∀ x, R x (f x)) ∧ ∀ (g : G) x, f (g • x) = g • f x := by
  choose y hyR hyfix using hfixed
  let f : X → Y := fun x => orbitChoiceTransport (G := G) x • y (orbitChoiceRepresentative (G := G) x)
  refine ⟨f, ?_, ?_⟩
  · intro x
    have hh := hR (orbitChoiceTransport (G := G) x)
      (orbitChoiceRepresentative (G := G) x) (y (orbitChoiceRepresentative (G := G) x))
      (hyR (orbitChoiceRepresentative (G := G) x))
    rw [orbitChoiceTransport_spec] at hh
    exact hh
  · intro h x
    let r := orbitChoiceRepresentative (G := G) x
    let a := orbitChoiceTransport (G := G) x
    let b := orbitChoiceTransport (G := G) (h • x)
    have ha : a • r = x := orbitChoiceTransport_spec (G := G) x
    have hb : b • r = h • x := by
      simpa only [orbitChoiceRepresentative_smul] using (orbitChoiceTransport_spec (G := G) (h • x))
    have hk : (b⁻¹ * h * a) • r = r := by
      rw [mul_smul, mul_smul, ha, ← hb, inv_smul_smul]
    have hy : (b⁻¹ * h * a) • y r = y r := hyfix r _ hk
    have hh := congrArg (fun z : Y => b • z) hy
    simp only [mul_smul, smul_inv_smul] at hh
    change b • y (orbitChoiceRepresentative (G := G) (h • x)) = h • (a • y r)
    rw [orbitChoiceRepresentative_smul]
    exact hh.symm

theorem exists_equivariant_choice_of_free (R : X → Y → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (hne : ∀ x : X, ∃ y : Y, R x y) :
    ∃ f : X → Y, (∀ x, R x (f x)) ∧ ∀ (g : G) x, f (g • x) = g • f x := by
  apply exists_equivariant_choice R hR
  intro x
  obtain ⟨y, hy⟩ := hne x
  refine ⟨y, hy, ?_⟩
  intro g hg
  rw [hfree g x hg, one_smul]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicEquivariantInduction.lean -/
section


section

/-! # Equivariant extension along a finite rank filtration

At each rank the boundary is already fixed equivariantly.  Stabilizer-fixed
extensions on orbit representatives give a simultaneous equivariant extension
on that rank.  Strict rank growth ensures that no new compatibility equation
relates two distinct faces introduced at the same stage.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {G P Y : Type*} [Group G] [PartialOrder P] [Fintype P]
  [MulAction G P] [MulAction G Y]

def equivariantRankCut (rank : P → ℕ) (n : ℕ) : Set P := {p | rank p < n}

def equivariantRankCutMulAction (rank : P → ℕ) (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (n : ℕ) : MulAction G (equivariantRankCut rank n) where
  smul g p := ⟨g • p.val, by simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using p.property⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

def rankLevelMulAction (rank : P → ℕ) (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (n : ℕ) : MulAction G {p : P // rank p = n} where
  smul g p := ⟨g • p.val, (hrank g p.val).trans p.property⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

structure EquivariantRankStage (rank : P → ℕ)
    (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (Good : P → Y → Prop) (Compatible : P → P → Y → Y → Prop) (n : ℕ) where
  value : equivariantRankCut rank n → Y
  good : ∀ p, Good p.val (value p)
  compatible : ∀ p q, q.val < p.val → Compatible p.val q.val (value p) (value q)
  equivariant : ∀ (g : G) p,
    value ⟨g • p.val, by simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using p.property⟩ = g • value p

theorem exists_equivariant_rank_family
    (rank : P → ℕ) (hstrict : StrictMono rank)
    (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (hlt : ∀ (g : G) {p q : P}, p < q → g • p < g • q)
    (Good : P → Y → Prop) (Compatible : P → P → Y → Y → Prop)
    (hGood : ∀ (g : G) p y, Good p y → Good (g • p) (g • y))
    (hCompatible : ∀ (g : G) p q y z,
      Compatible p q y z → Compatible (g • p) (g • q) (g • y) (g • z))
    (hlift : ∀ n (old : EquivariantRankStage rank hrank Good Compatible n)
      (p : P), rank p = n → ∃ y : Y,
        Good p y ∧
        (∀ q : equivariantRankCut rank n, q.val < p → Compatible p q.val y (old.value q)) ∧
        ∀ g : G, g • p = p → g • y = y) :
    ∃ f : P → Y, (∀ p, Good p (f p)) ∧
      (∀ p q, q < p → Compatible p q (f p) (f q)) ∧
      ∀ (g : G) p, f (g • p) = g • f p := by
  have stages : ∀ n, Nonempty (EquivariantRankStage rank hrank Good Compatible n) := by
    intro n
    induction n with
    | zero =>
      exact ⟨{
        value := fun p => False.elim (Nat.not_lt_zero _ p.property)
        good := fun p => False.elim (Nat.not_lt_zero _ p.property)
        compatible := fun p => False.elim (Nat.not_lt_zero _ p.property)
        equivariant := fun g p => False.elim (Nat.not_lt_zero _ p.property) }⟩
    | succ n ih =>
      let old := Classical.choice ih
      letI := rankLevelMulAction rank hrank n
      let R : {p : P // rank p = n} → Y → Prop := fun p y =>
        Good p.val y ∧ ∀ q : equivariantRankCut rank n, q.val < p.val → Compatible p.val q.val y (old.value q)
      have hR : ∀ (g : G) p y, R p y → R (g • p) (g • y) := by
        intro g p y hy
        refine ⟨hGood g p.val y hy.1, ?_⟩
        intro q hqp
        let q' : equivariantRankCut rank n := ⟨g⁻¹ • q.val, by
          simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using q.property⟩
        have hq'p : q'.val < p.val := by
          have hh := hlt g⁻¹ hqp
          change g⁻¹ • q.val < g⁻¹ • (g • p.val) at hh
          change g⁻¹ • q.val < p.val
          simpa only [inv_smul_smul] using hh
        have hh := hCompatible g p.val q'.val y (old.value q') (hy.2 q' hq'p)
        have hqeq : g • q'.val = q.val := smul_inv_smul g q.val
        have hv : g • old.value q' = old.value q := by
          rw [← old.equivariant g q']
          congr 1
          exact Subtype.ext hqeq
        change Compatible (g • p.val) q.val (g • y) (old.value q)
        simpa only [hqeq, hv] using hh
      have hfixed : ∀ p : {p : P // rank p = n}, ∃ y : Y,
          R p y ∧ ∀ g : G, g • p = p → g • y = y := by
        intro p
        obtain ⟨y, hy, hb, he⟩ := hlift n old p.val p.property
        exact ⟨y, ⟨hy, hb⟩, fun g hg => he g (congrArg Subtype.val hg)⟩
      obtain ⟨fresh, hfresh, hefresh⟩ := exists_equivariant_choice R hR hfixed
      let value : equivariantRankCut rank (n + 1) → Y := fun p =>
        if h : rank p.val < n then old.value ⟨p.val, h⟩
        else fresh ⟨p.val, by have hp := p.property; change rank p.val < n + 1 at hp; omega⟩
      refine ⟨{ value := value, good := ?_, compatible := ?_, equivariant := ?_ }⟩
      · intro p
        by_cases hp : rank p.val < n
        · simpa only [value, dif_pos hp] using old.good ⟨p.val, hp⟩
        · simpa only [value, dif_neg hp] using (hfresh ⟨p.val, by
            have hh := p.property; change rank p.val < n + 1 at hh; omega⟩).1
      · intro p q hqp
        have hq : rank q.val < n := by
          have hh := hstrict hqp
          have hp := p.property
          change rank p.val < n + 1 at hp
          omega
        by_cases hp : rank p.val < n
        · simpa only [value, dif_pos hp, dif_pos hq] using
            old.compatible ⟨p.val, hp⟩ ⟨q.val, hq⟩ hqp
        · simpa only [value, dif_neg hp, dif_pos hq] using
            (hfresh ⟨p.val, by
              have hh := p.property; change rank p.val < n + 1 at hh; omega⟩).2
                ⟨q.val, hq⟩ hqp
      · intro g p
        by_cases hp : rank p.val < n
        · have hgp : rank (g • p.val) < n := by rwa [hrank]
          simpa only [value, dif_pos hp, dif_pos hgp] using old.equivariant g ⟨p.val, hp⟩
        · have hgp : ¬ rank (g • p.val) < n := by rwa [hrank]
          have hp' : rank p.val = n := by
            have hh := p.property; change rank p.val < n + 1 at hh; omega
          have hh := hefresh g ⟨p.val, hp'⟩
          change fresh ⟨g • p.val, (hrank g p.val).trans hp'⟩ = g • fresh ⟨p.val, hp'⟩ at hh
          simpa only [value, dif_neg hp, dif_neg hgp] using hh
  let n := (Finset.univ.sup rank) + 1
  let final := Classical.choice (stages n)
  have hn (p : P) : rank p < n :=
    Nat.lt_succ_of_le (Finset.le_sup (f := rank) (Finset.mem_univ p))
  refine ⟨fun p => final.value ⟨p, hn p⟩, fun p => final.good ⟨p, hn p⟩,
    fun p q h => final.compatible ⟨p, hn p⟩ ⟨q, hn q⟩ h, ?_⟩
  intro g p
  exact final.equivariant g ⟨p, hn p⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCosetTrace.lean -/
section

section
/-! # Integral trace from subgroup invariants

An element fixed by a subgroup has a well-defined orbit value on the left
coset space.  Summing these values gives a group-fixed element, without any
division.  Every equivariant boundary whose value was already group-fixed
is multiplied by the subgroup index.  All assertions apply to an actual
submodule of coherent parameter maps as well as to an ordinary module.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable {K G M N : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def subgroupFixedSubmodule (ρ : CyclicRepresentation K G M) (H : Subgroup G) : Submodule K M where
  carrier := {x | ∀ h : H, ρ h.val x = x}
  zero_mem' := by intro h; exact map_zero _
  add_mem' := by intro x y hx hy h; rw [map_add, hx h, hy h]
  smul_mem' := by intro c x hx h; rw [map_smul, hx h]

def cosetLeftPermutation (H : Subgroup G) (g : G) : Equiv.Perm (G ⧸ H) where
  toFun := Quotient.map' (fun a => g * a) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab)
  invFun := Quotient.map' (fun a => g⁻¹ * a) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hab)
  left_inv q := by
    induction q using QuotientGroup.induction_on with
    | H a => change (QuotientGroup.mk (g⁻¹ * (g * a)) : G ⧸ H) = QuotientGroup.mk a; simp
  right_inv q := by
    induction q using QuotientGroup.induction_on with
    | H a => change (QuotientGroup.mk (g * (g⁻¹ * a)) : G ⧸ H) = QuotientGroup.mk a; simp

@[simp] theorem cosetLeftPermutation_mk (H : Subgroup G) (g a : G) :
    cosetLeftPermutation H g (QuotientGroup.mk a) = QuotientGroup.mk (g * a) := rfl

def cosetOrbitValue (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) : G ⧸ H → M :=
  Quotient.lift (fun g => ρ g x) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hfixed := hx ⟨a⁻¹ * b, hmem⟩
    calc
      ρ a x = ρ a (ρ (a⁻¹ * b) x) := by rw [hfixed]
      _ = ρ (a * (a⁻¹ * b)) x := by rw [ρ.map_mul a (a⁻¹ * b)]; rfl
      _ = ρ b x := by rw [mul_inv_cancel_left])

@[simp] theorem cosetOrbitValue_mk (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) :
    cosetOrbitValue ρ H x hx (QuotientGroup.mk g) = ρ g x := rfl

theorem cosetOrbitValue_out (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (q : G ⧸ H) :
    cosetOrbitValue ρ H x hx q = ρ q.out x := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

theorem cosetOrbitValue_translate (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) (q : G ⧸ H) :
    cosetOrbitValue ρ H x hx (cosetLeftPermutation H g q) =
      ρ g (cosetOrbitValue ρ H x hx q) := by
  induction q using QuotientGroup.induction_on with
  | H a =>
      change ρ (g * a) x = ρ g (ρ a x)
      rw [ρ.map_mul]
      rfl

variable [Fintype G]

def cosetTrace (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) : M :=
  ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx q

theorem cosetTrace_fixed (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) :
    ρ g (cosetTrace ρ H x hx) = cosetTrace ρ H x hx := by
  rw [cosetTrace, map_sum]
  calc
    ∑ q : G ⧸ H, ρ g (cosetOrbitValue ρ H x hx q) =
        ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx (cosetLeftPermutation H g q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (cosetOrbitValue_translate ρ H x hx g q).symm
    _ = ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx q :=
      Equiv.sum_comp (cosetLeftPermutation H g) (cosetOrbitValue ρ H x hx)

/-- This scalar is the subgroup index, and requires no invertibility. -/
theorem cosetTrace_map_const (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (q : M →+ N) (y : N)
    (hq : ∀ g, q (ρ g x) = y) :
    q (cosetTrace ρ H x hx) = H.index • y := by
  simp only [cosetTrace, map_sum, cosetOrbitValue_out, hq,
    Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]

theorem cosetTrace_map_equivariant (ρ : CyclicRepresentation K G M)
    (τ : CyclicRepresentation K G N) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x)
    (q : M →ₗ[K] N) (hq : RepresentationIntertwines ρ τ q)
    (hfixed : ∀ g, τ g (q x) = q x) :
    q (cosetTrace ρ H x hx) = H.index • q x :=
  cosetTrace_map_const ρ H x hx q.toAddMonoidHom (q x) (fun g => (hq g x).trans (hfixed g))

theorem cosetTrace_mem (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (U : Submodule K M)
    (hU : ∀ g z, z ∈ U → ρ g z ∈ U) (hxU : x ∈ U) :
    cosetTrace ρ H x hx ∈ U := by
  apply U.sum_mem
  intro q hq
  rw [cosetOrbitValue_out]
  exact hU q.out x hxU

def cosetTraceLinear (ρ : CyclicRepresentation K G M) (H : Subgroup G) :
    subgroupFixedSubmodule ρ H →ₗ[K] M where
  toFun x := cosetTrace ρ H x.val x.property
  map_add' x y := by
    simp only [cosetTrace, cosetOrbitValue_out, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [cosetTrace, cosetOrbitValue_out, Submodule.coe_smul, map_smul,
      Finset.smul_sum, RingHom.id_apply]

/-- The index of any embedded group of order `n` in a permutation group on
`n` letters is `(n-1)!`.  The cyclic prime subgroup is the application. -/
theorem permutationEmbedding_index_factorial {V T : Type*} [Fintype V]
    [Group T] (f : T →* Equiv.Perm V) (hf : Function.Injective f)
    (n : ℕ) (hn : 0 < n) (hT : Nat.card T = n) (hV : Fintype.card V = n) :
    f.range.index = (n - 1).factorial := by
  have hrange : Nat.card f.range = n := by
    calc
      Nat.card f.range = Nat.card T := (Nat.card_congr (Equiv.ofInjective f hf)).symm
      _ = n := hT
  have hmul := f.range.card_mul_index
  rw [hrange, Nat.card_eq_fintype_card, Fintype.card_perm, hV] at hmul
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * f.range.index = n.factorial := hmul
    _ = n * (n - 1).factorial := by
      have he : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
      conv_lhs => rw [← he, Nat.factorial_succ]
      rw [he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralAveraging.lean -/
section


section

/-! # Integral affine averaging without division

This is the argument of Lemma A.8.  The group order is never inverted: the
errors of a point fixed modulo the group order are first divided inside the
given lattice, and their sum is the correction to an integral fixed point.
-/

noncomputable section

namespace FourPapers.Universal

open scoped BigOperators

variable {K G M N : Type*} [CommRing K] [Group G] [Fintype G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem representation_sum_fixed (ρ : CyclicRepresentation K G M) (h : G) (x : M) :
    ρ h (∑ g : G, ρ g x) = ∑ g : G, ρ g x := by
  rw [map_sum]
  calc
    ∑ g : G, ρ h (ρ g x) = ∑ g : G, ρ (h * g) x := by
      apply Finset.sum_congr rfl
      intro g hg
      exact (congrArg (fun f : M →ₗ[K] M => f x) (ρ.map_mul h g)).symm
    _ = ∑ g : G, ρ g x :=
      Fintype.sum_equiv (Equiv.mulLeft h) (fun g => ρ (h * g) x)
        (fun g => ρ g x) (fun _ => rfl)

/-- The explicit correction has norm equal to the ordinary group norm. -/
theorem affineCorrection_norm (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    Fintype.card G • (x + ∑ g : G, v g) = ∑ g : G, ρ g x := by
  rw [nsmul_add, Finset.smul_sum]
  simp only [hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]

/-- Lemma A.8 in linear ambient coordinates.  Injectivity of multiplication by
the group order is exactly the torsion-free fact used from the integral
lattice. -/
theorem affineCorrection_fixed (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    ∀ h, ρ h (x + ∑ g : G, v g) = x + ∑ g : G, v g := by
  intro h
  apply hregular
  change Fintype.card G • (ρ h (x + ∑ g : G, v g)) = Fintype.card G • (x + ∑ g : G, v g)
  rw [← map_nsmul, affineCorrection_norm ρ x v hv, representation_sum_fixed]

/-- The integral correction stays in the same affine fiber whenever each
divided error lies in the restriction kernel. -/
theorem exists_fixedPoint_sameFiber (ρ : CyclicRepresentation K G M)
    (q : M →ₗ[K] N) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g)
    (hqv : ∀ g, q (v g) = 0) :
    ∃ y : M, (∀ g, ρ g y = y) ∧ q y = q x := by
  refine ⟨x + ∑ g : G, v g, affineCorrection_fixed ρ x v hregular hv, ?_⟩
  simp [hqv]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeRetraction.lean -/
section


section

/-! # The prime-rank orbit retraction in characteristic `p`

The map first identifies all vertex variables with one variable, retains
only exponents divisible by `p`, and divides those exponents by `p`.  Its
target variable has internal degree `p`.  These are actual polynomial maps,
and parameter compatibility is proved from the binomial coefficients.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators Polynomial

variable {K V : Type*} [CommRing K]

def coefficientCompression (p : ℕ) : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun n => if p ∣ n then Polynomial.monomial (n / p) else 0

@[simp] theorem coefficientCompression_monomial (p n : ℕ) (a : K) :
    coefficientCompression p (Polynomial.monomial n a) =
      if p ∣ n then Polynomial.monomial (n / p) a else 0 := by
  by_cases h : p ∣ n <;> simp [coefficientCompression, Polynomial.lsum_apply, h]

@[simp] theorem coefficientCompression_one (p : ℕ) :
    coefficientCompression (K := K) p 1 = 1 := by
  simpa using coefficientCompression_monomial p 0 (1 : K)

theorem coefficientCompression_X_pow_mul (p : ℕ) (hp : 0 < p) (f : K[X]) :
    coefficientCompression p (Polynomial.X ^ p * f) =
      Polynomial.X * coefficientCompression p f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [mul_add, hf, hg]
  | monomial n a =>
      have hdiv : p ∣ n + p ↔ p ∣ n := by
        simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_self,
          add_zero, Nat.mod_mod]
      rw [Polynomial.X_pow_mul_monomial, coefficientCompression_monomial,
        coefficientCompression_monomial]
      by_cases hn : p ∣ n
      · rw [if_pos (hdiv.mpr hn), if_pos hn, Nat.add_div_right n hp]
        simpa using (Polynomial.X_pow_mul_monomial 1 (n / p) a).symm
      · rw [if_neg (fun h => hn (hdiv.mp h)), if_neg hn, mul_zero]

/-- Diagonal evaluation is invariant under every relabeling of the vertices. -/
def diagonalEvaluation : MvPolynomial V K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun _ => Polynomial.X

@[simp] theorem diagonalEvaluation_rename (e : V → V) (f : MvPolynomial V K) :
    diagonalEvaluation (MvPolynomial.rename e f) = diagonalEvaluation f := by
  unfold diagonalEvaluation
  rw [MvPolynomial.aeval_rename]
  rfl

theorem diagonalEvaluation_monomial (a : V →₀ ℕ) (c : K) :
    diagonalEvaluation (MvPolynomial.monomial a c) =
      Polynomial.monomial (a.sum fun _ n => n) c := by
  rw [diagonalEvaluation, MvPolynomial.aeval_monomial]
  change Polynomial.C c * (∏ v ∈ a.support, Polynomial.X ^ a v) = _
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.C_mul_X_pow_eq_monomial]
  rfl

variable [Fintype V]

theorem diagonalEvaluation_esymm (i : ℕ) :
    diagonalEvaluation (MvPolynomial.esymm V K i) =
      (Fintype.card V).choose i • (Polynomial.X : K[X]) ^ i := by
  unfold diagonalEvaluation MvPolynomial.esymm
  rw [map_sum]
  calc
    ∑ t ∈ Finset.univ.powersetCard i,
        (MvPolynomial.aeval (fun _ : V => (Polynomial.X : K[X])))
          (∏ v ∈ t, MvPolynomial.X v) =
        ∑ _t ∈ Finset.univ.powersetCard i, (Polynomial.X : K[X]) ^ i := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcard : t.card = i := (Finset.mem_powersetCard.mp ht).2
      simp only [map_prod, MvPolynomial.aeval_X, Finset.prod_const, hcard]
    _ = _ := by simp

def primeOrbitRetraction (p : ℕ) : MvPolynomial V K →ₗ[K] K[X] :=
  (coefficientCompression p).comp diagonalEvaluation.toLinearMap

@[simp] theorem primeOrbitRetraction_monomial (p : ℕ) (a : V →₀ ℕ) (c : K) :
    primeOrbitRetraction p (MvPolynomial.monomial a c) =
      if p ∣ a.sum (fun _ n => n) then
        Polynomial.monomial ((a.sum fun _ n => n) / p) c else 0 := by
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    diagonalEvaluation_monomial, coefficientCompression_monomial]

@[simp] theorem primeOrbitRetraction_one (p : ℕ) :
    primeOrbitRetraction (V := V) (K := K) p 1 = 1 := by
  simp [primeOrbitRetraction]

@[simp] theorem primeOrbitRetraction_rename (p : ℕ) (e : V → V)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.rename e f) = primeOrbitRetraction p f := by
  simp [primeOrbitRetraction]

variable (p : ℕ) [CharP K p]

private theorem prime_dvd_interior_binomial (hp : p.Prime) {i : ℕ}
    (hi : 0 < i) (hip : i < p) : p ∣ p.choose i := by
  have hmul := Nat.add_one_mul_choose_eq (p - 1) (i - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p),
    Nat.sub_add_cancel (by omega : 1 ≤ i)] at hmul
  have hdiv : p ∣ p.choose i * i := by
    rw [← hmul]
    exact dvd_mul_right _ _
  exact (hp.dvd_mul.mp hdiv).resolve_right (Nat.not_dvd_of_pos_of_lt hi hip)

theorem primeOrbitRetraction_lower_parameter (hp : p.Prime)
    (hcard : Fintype.card V = p) {i : ℕ} (hi : 0 < i) (hip : i < p)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K i * f) = 0 := by
  have hc : (p.choose i : K[X]) = 0 :=
    (CharP.cast_eq_zero_iff (K[X]) p _).mpr (prime_dvd_interior_binomial p hp hi hip)
  have he : diagonalEvaluation (MvPolynomial.esymm V K i) = 0 := by
    rw [diagonalEvaluation_esymm, hcard, nsmul_eq_mul, hc, zero_mul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, zero_mul, map_zero]

theorem primeOrbitRetraction_top_parameter (hp : 0 < p)
    (hcard : Fintype.card V = p) (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K p * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  have he : diagonalEvaluation (MvPolynomial.esymm V K p) =
      (Polynomial.X : K[X]) ^ p := by
    rw [diagonalEvaluation_esymm, hcard, Nat.choose_self, one_smul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, coefficientCompression_X_pow_mul p hp]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOneDegreeLift.lean -/
section


section

/-! # The equivariant correction in one homogeneous degree

This is the exact extension step in Lemma 8.1.  It keeps both the prescribed
quotient map and the already constructed map on a split subspace.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

/-- Restriction of a representation to an invariant submodule. -/
def invariantSubmoduleRepresentation (ρ : CyclicRepresentation K G M)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U) :
    CyclicRepresentation K G U where
  toFun g :=
    { toFun := fun x => ⟨ρ g x.val, hU g x.val x.property⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    exact congrArg (fun f : M →ₗ[K] M => f x.val) (ρ.map_mul g h)

@[simp] theorem invariantSubmoduleRepresentation_apply
    (ρ : CyclicRepresentation K G M) (U : Submodule K M)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (g : G) (x : U) :
    (invariantSubmoduleRepresentation ρ U hU g x).val = ρ g x.val := rfl

theorem kernel_invariant_of_intertwines
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (f : M →ₗ[K] N) (hf : RepresentationIntertwines ρ τ f) :
    ∀ g x, x ∈ LinearMap.ker f → ρ g x ∈ LinearMap.ker f := by
  intro g x hx
  change f (ρ g x) = 0
  rw [hf, LinearMap.mem_ker.mp hx, map_zero]

/-- Correct an equivariant preliminary lift by a map into its kernel.  The
kernel's regular-orbit coordinates supply the relative-injectivity step. -/
theorem equivariant_lift_extend_subspace
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (s : M →ₗ[K] U) (hs : s.comp U.subtype = LinearMap.id)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (β : M →ₗ[K] N)
    (hβ : RepresentationIntertwines ρ τ β) (hqβ : q.comp β = a)
    (f : U →ₗ[K] N)
    (hf : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU) τ f)
    (hqf : q.comp f = a.comp U.subtype)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ L : M →ₗ[K] N,
      RepresentationIntertwines ρ τ L ∧ L.comp U.subtype = f ∧ q.comp L = a := by
  let δ : U →ₗ[K] LinearMap.ker q :=
    LinearMap.codRestrict (LinearMap.ker q) (f - β.comp U.subtype) (by
      intro x
      change q (f x - β x.val) = 0
      rw [map_sub]
      have h1 := congrArg (fun z : U →ₗ[K] Q => z x) hqf
      have h2 := congrArg (fun z : M →ₗ[K] Q => z x.val) hqβ
      exact sub_eq_zero.mpr (h1.trans h2.symm))
  have hδ : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU)
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) δ := by
    intro g x
    apply Subtype.ext
    change f (invariantSubmoduleRepresentation ρ U hU g x) - β (ρ g x.val) =
      τ g (f x - β x.val)
    rw [hf, hβ, map_sub]
  have hi : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρ U hU) ρ U.subtype := by
    intro g x
    rfl
  obtain ⟨D, hD, hDi⟩ := exists_equivariantExtension_of_coinduced
    (invariantSubmoduleRepresentation ρ U hU) ρ
    (invariantSubmoduleRepresentation τ (LinearMap.ker q)
      (kernel_invariant_of_intertwines τ υ q hq)) e he U.subtype s hi hs δ hδ
  refine ⟨β + (LinearMap.ker q).subtype.comp D, ?_, ?_, ?_⟩
  · intro g x
    change β (ρ g x) + (D (ρ g x)).val = τ g (β x + (D x).val)
    rw [hβ, hD, map_add]
    rfl
  · ext x
    have hd := congrArg (fun z : U →ₗ[K] LinearMap.ker q => (z x).val) hDi
    change β x.val + (D x.val).val = f x
    change (D x.val).val = f x - β x.val at hd
    rw [hd, ← add_sub_assoc, add_comm (β x.val) (f x)]
    exact add_sub_cancel_right (f x) (β x.val)
  · ext x
    have hx := (D x).property
    change q (D x).val = 0 at hx
    change q (β x + (D x).val) = a x
    rw [map_add, hx, add_zero]
    exact congrArg (fun z : M →ₗ[K] Q => z x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSplitKernelLift.lean -/
section


section

/-! # An ordinary lift can be made equivariant

An equivariant kernel with regular-orbit coordinates is relatively injective.
Over a field its inclusion splits as an ordinary linear map, hence also
equivariantly.  Consequently an ordinary lift of an equivariant quotient map
can be corrected to an equivariant lift.  This removes any assumption of an
already equivariant preliminary section from the graded construction.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [Field K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

theorem exists_equivariantLift_of_coinduced_kernel
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (ha : RepresentationIntertwines ρ υ a)
    (β : M →ₗ[K] N) (hqβ : q.comp β = a)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ F : M →ₗ[K] N, RepresentationIntertwines ρ τ F ∧ q.comp F = a := by
  let H := LinearMap.ker q
  let ρH := invariantSubmoduleRepresentation τ H
    (kernel_invariant_of_intertwines τ υ q hq)
  obtain ⟨s, hs⟩ := H.subtype.exists_leftInverse_of_injective H.ker_subtype
  have hi : RepresentationIntertwines ρH τ H.subtype := by
    intro g x
    rfl
  have hid : RepresentationIntertwines ρH ρH (LinearMap.id : H →ₗ[K] H) := by
    intro g x
    rfl
  obtain ⟨r, hre, hri⟩ := exists_equivariantExtension_of_coinduced
    ρH τ ρH e he H.subtype s hi hs LinearMap.id hid
  let P : N →ₗ[K] N := LinearMap.id - H.subtype.comp r
  have hP : RepresentationIntertwines τ τ P := by
    intro g x
    change τ g x - (r (τ g x)).val = τ g (x - (r x).val)
    rw [hre, map_sub]
    rfl
  have hPH (x : H) : P x.val = 0 := by
    have hrx := congrArg (fun F : H →ₗ[K] H => (F x).val) hri
    change x.val - (r x.val).val = 0
    change (r x.val).val = x.val at hrx
    rw [hrx, sub_self]
  have hqP (x : N) : q (P x) = q x := by
    change q (x - (r x).val) = q x
    rw [map_sub, show q (r x).val = 0 from (r x).property, sub_zero]
  refine ⟨P.comp β, ?_, ?_⟩
  · intro g x
    have hx : β (ρ g x) - τ g (β x) ∈ H := by
      change q (β (ρ g x) - τ g (β x)) = 0
      rw [map_sub, hq]
      have hb1 := congrArg (fun F : M →ₗ[K] Q => F (ρ g x)) hqβ
      have hb2 := congrArg (fun F : M →ₗ[K] Q => F x) hqβ
      change q (β (ρ g x)) = a (ρ g x) at hb1
      change q (β x) = a x at hb2
      rw [hb1, hb2, ha, sub_self]
    have hz := hPH ⟨β (ρ g x) - τ g (β x), hx⟩
    rw [map_sub] at hz
    change P (β (ρ g x)) = τ g (P (β x))
    exact (sub_eq_zero.mp hz).trans (hP g (β x))
  · ext x
    change q (P (β x)) = a x
    rw [hqP]
    exact congrArg (fun F : M →ₗ[K] Q => F x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedBasis.lean -/
section


section

/-! # Homogeneous free bases for equivariant lifting

The two bases below are the parameter basis and the coefficient basis of a
graded free module.  In the application they are `booleanColorBasis` and
`booleanParameterBasis`.  The degree properties express positivity of the
parameters, and are proved from their actual color multidegrees.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable (K A M I J : Type*) [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

structure ScalarGradedBasis where
  parameterBasis : Module.Basis I A M
  coefficientBasis : Module.Basis J K M
  generatorDegree : I → ℕ
  degree : J → ℕ
  parent : J → I
  multiplier : J → A
  coefficient_eq : ∀ j, coefficientBasis j = multiplier j • parameterBasis (parent j)
  parent_degree_le : ∀ j, generatorDegree (parent j) ≤ degree j
  equal_degree_eq : ∀ j, degree j = generatorDegree (parent j) →
    coefficientBasis j = parameterBasis (parent j)
  generator_homogeneous : ∀ i j, degree j ≠ generatorDegree i →
    coefficientBasis.repr (parameterBasis i) j = 0

namespace ScalarGradedBasis

variable {K A M I J}
variable (s : ScalarGradedBasis K A M I J)

def piece (n : ℕ) : Submodule K M :=
  basisOrdinaryDegreePiece s.coefficientBasis s.degree n

def cut (n : ℕ) : Submodule A M :=
  Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n})

theorem generator_mem_piece (i : I) :
    s.parameterBasis i ∈ s.piece (s.generatorDegree i) :=
  s.generator_homogeneous i

theorem coefficient_mem_piece (j : J) : s.coefficientBasis j ∈ s.piece (s.degree j) := by
  intro k hk
  change s.coefficientBasis.repr (s.coefficientBasis j) k = 0
  rw [Module.Basis.repr_self]
  have hne : j ≠ k := by
    intro h
    subst k
    exact hk rfl
  simp [Finsupp.single_apply, hne]

theorem generator_mem_cut {n : ℕ} (i : I) (hi : s.generatorDegree i < n) :
    s.parameterBasis i ∈ s.cut n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem coefficient_mem_cut {n : ℕ} (j : J)
    (hj : s.generatorDegree (s.parent j) < n) :
    s.coefficientBasis j ∈ s.cut n := by
  rw [s.coefficient_eq]
  exact (s.cut n).smul_mem _ (s.generator_mem_cut _ hj)

def projection (n : ℕ) : M →ₗ[K] s.piece n :=
  LinearMap.codRestrict (s.piece n)
    (basisDegreeProjection s.coefficientBasis s.degree n) (by
      intro x j hj
      change s.coefficientBasis.repr (basisDegreeProjection s.coefficientBasis s.degree n x) j = 0
      simp only [basisDegreeProjection_repr, if_neg hj])

@[simp] theorem projection_coefficient (n : ℕ) (j : J) (hj : s.degree j = n) :
    s.projection n (s.coefficientBasis j) =
      ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_pos hj)

@[simp] theorem projection_coefficient_of_ne (n : ℕ) (j : J) (hj : s.degree j ≠ n) :
    s.projection n (s.coefficientBasis j) = 0 := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_neg hj)

@[simp] theorem projection_subtype (n : ℕ) (x : s.piece n) :
    s.projection n x.val = x := by
  apply Subtype.ext
  apply s.coefficientBasis.repr.injective
  ext j
  change s.coefficientBasis.repr
    (basisDegreeProjection s.coefficientBasis s.degree n x.val) j = _
  rw [basisDegreeProjection_repr]
  by_cases hj : s.degree j = n
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact (x.property j hj).symm

variable {N : Type*} [AddCommGroup N] [Module K N]

theorem maps_eq_on_piece (n : ℕ) (f : M →ₗ[K] N) (g : s.piece n →ₗ[K] N)
    (h : ∀ j (hj : s.degree j = n),
      f (s.coefficientBasis j) = g ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩)
    (x : s.piece n) : f x.val = g x := by
  have he : f.comp ((s.piece n).subtype.comp (s.projection n)) =
      g.comp (s.projection n) := by
    apply s.coefficientBasis.ext
    intro j
    by_cases hj : s.degree j = n
    · simp only [LinearMap.comp_apply, s.projection_coefficient n j hj,
        Submodule.subtype_apply]
      exact h j hj
    · simp only [LinearMap.comp_apply, s.projection_coefficient_of_ne n j hj,
        map_zero]
  have hx := congrArg (fun z : M →ₗ[K] N => z x.val) he
  simpa using hx

theorem homogeneous_mem_cut {m n : ℕ} (hmn : m < n) (x : M)
    (hx : x ∈ s.piece m) : x ∈ s.cut n := by
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply ((s.cut n).restrictScalars K).sum_mem
  intro j hj
  apply ((s.cut n).restrictScalars K).smul_mem
  have hdeg : s.degree j = m := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  apply s.coefficient_mem_cut j
  calc
    s.generatorDegree (s.parent j) ≤ s.degree j := s.parent_degree_le j
    _ = m := hdeg
    _ < n := hmn

variable [Module A N] [IsScalarTower K A N]

theorem maps_eq_on_cut (n : ℕ) (f g : M →ₗ[A] N)
    (h : ∀ i, s.generatorDegree i < n → f (s.parameterBasis i) = g (s.parameterBasis i))
    (x : M) (hx : x ∈ s.cut n) : f x = g x := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact h i hi
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

theorem graded_of_generators (T : ℕ → Submodule K N)
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (f : M →ₗ[A] N) (hf : ∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i))
    (n : ℕ) (x : M) (hx : x ∈ s.piece n) : f x ∈ T n := by
  let fk : M →ₗ[K] N := f.restrictScalars K
  change fk x ∈ T n
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : s.degree j = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  change f (s.coefficientBasis j) ∈ T n
  rw [s.coefficient_eq, map_smul]
  exact hdeg ▸ hmult j _ (hf (s.parent j))

variable {G : Type*} [Group G]

def restrictRepresentation (ρ : CyclicRepresentation A G M) : CyclicRepresentation K G M where
  toFun g := (ρ g).restrictScalars K
  map_one' := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) ρ.map_one
  map_mul' g h := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) (ρ.map_mul g h)

theorem cut_invariant (ρ : CyclicRepresentation A G M)
    (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
    (n : ℕ) (g : G) (x : M) (hx : x ∈ s.cut n) : ρ g x ∈ s.cut n := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact s.homogeneous_mem_cut hi _ (hρ g _ _ (s.generator_mem_piece i))
  | zero => simpa using (s.cut n).zero_mem
  | add x y hx hy ihx ihy => simpa using (s.cut n).add_mem ihx ihy
  | smul a x hx ih => simpa using (s.cut n).smul_mem a ih

end ScalarGradedBasis

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedLift.lean -/
section


section

/-! # The finite degree induction for equivariant lifting

This file separates the finite induction from the one-degree kernel calculation.
No map on the generators is assumed to intertwine the group action.  The lower
generator span is stable because the action preserves degree, and agreement on
its intersection with the next degree is imposed explicitly.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)

/-- The induction invariant is stated on all parameter-basis generators of
degree below `n`.  A-linearity extends the last two conditions to `cut n`. -/
def LiftStage (n : ℕ) (f : M →ₗ[A] N) : Prop :=
  (∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i)) ∧
  (∀ i, s.generatorDegree i < n → q (f (s.parameterBasis i)) = a (s.parameterBasis i)) ∧
  (∀ g i, s.generatorDegree i < n →
    f (ρ g (s.parameterBasis i)) = τ g (f (s.parameterBasis i)))

theorem LiftStage.quotient_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (x : M) (hx : x ∈ s.cut n) :
    q (f x) = a x :=
  s.maps_eq_on_cut n (q.comp f) a hf.2.1 x hx

theorem LiftStage.equivariant_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (g : G) (x : M) (hx : x ∈ s.cut n) :
    f (ρ g x) = τ g (f x) :=
  s.maps_eq_on_cut n (f.comp (ρ g)) ((τ g).comp f) (hf.2.2 g) x hx

variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)

/-- A one-degree lift, with the previously fixed lower-generator values. -/
def DegreeLift (n : ℕ) (f : M →ₗ[A] N) (L : s.piece n →ₗ[K] N) : Prop :=
  (∀ x, L x ∈ T n) ∧
  (∀ g x, L ⟨ρ g x.val, hρ g n x.val x.property⟩ = τ g (L x)) ∧
  (∀ x, q (L x) = a x.val) ∧
  (∀ x, x.val ∈ s.cut n → L x = f x.val)

/-- The induction step.  Its only input beyond the preceding stage is a lift on
the actual homogeneous component, compatible on the actual intersection. -/
theorem liftStage_succ {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f)
    (L : s.piece n →ₗ[K] N) (hL : s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ F : M →ₗ[A] N, s.LiftStage ρ τ T q a (n + 1) F := by
  let v : I → N := fun i =>
    if hi : s.generatorDegree i = n then
      L ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    else f (s.parameterBasis i)
  let F : M →ₗ[A] N := s.parameterBasis.constr A v
  have hF (i : I) : F (s.parameterBasis i) = v i :=
    s.parameterBasis.constr_basis A v i
  have hFcut (x : M) (hx : x ∈ s.cut n) : F x = f x := by
    apply s.maps_eq_on_cut n F f _ x hx
    intro i hi
    rw [hF]
    exact dif_neg (Nat.ne_of_lt hi)
  have hFpiece (x : s.piece n) : F x.val = L x := by
    apply s.maps_eq_on_piece n (F.restrictScalars K) L _ x
    intro j hj
    have hp : s.generatorDegree (s.parent j) ≤ n := by
      simpa only [hj] using s.parent_degree_le j
    by_cases he : s.generatorDegree (s.parent j) = n
    · have hc : s.coefficientBasis j = s.parameterBasis (s.parent j) :=
        s.equal_degree_eq j (hj.trans he.symm)
      change F (s.coefficientBasis j) = _
      calc
        F (s.coefficientBasis j) = F (s.parameterBasis (s.parent j)) := congrArg F hc
        _ = L ⟨s.parameterBasis (s.parent j), he ▸ s.generator_mem_piece (s.parent j)⟩ := by
          rw [hF]
          exact dif_pos he
        _ = L ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ :=
          congrArg L (Subtype.ext hc.symm)
    · have hlt : s.generatorDegree (s.parent j) < n := lt_of_le_of_ne hp he
      have hcut := s.coefficient_mem_cut j hlt
      change F (s.coefficientBasis j) = _
      rw [hFcut _ hcut]
      exact (hL.2.2.2 ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ hcut).symm
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    rw [hF]
    dsimp only [v]
    split_ifs with hi
    · simpa only [hi] using hL.1
        ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    · exact hf.1 i
  · intro i hi
    by_cases hlt : s.generatorDegree i < n
    · rw [hFcut _ (s.generator_mem_cut i hlt)]
      exact hf.2.1 i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      rw [hFpiece x]
      exact hL.2.2.1 x
  · intro g i hi
    by_cases hlt : s.generatorDegree i < n
    · have hbi : s.parameterBasis i ∈ s.cut n := s.generator_mem_cut i hlt
      rw [hFcut _ (s.cut_invariant ρ hρ n g _ hbi), hFcut _ hbi]
      exact hf.2.2 g i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      let gx : s.piece n := ⟨ρ g x.val, hρ g n x.val x.property⟩
      change F gx.val = τ g (F x.val)
      rw [hFpiece gx, hFpiece x]
      exact hL.2.1 g x

/-- The full finite induction.  The one-degree extension premise is discharged
by the relative-injectivity theorem in the next construction, not postulated as
a property of the paper's face rings. -/
theorem exists_equivariantGradedLift_of_degreeExtensions [Fintype I]
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (hstep : ∀ n f, s.LiftStage ρ τ T q a n f →
      ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have stages : ∀ n, ∃ f : M →ₗ[A] N, s.LiftStage ρ τ T q a n f := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, ?_, ?_, ?_⟩
        · intro i
          exact (T (s.generatorDegree i)).zero_mem
        · intro i hi
          exact False.elim (Nat.not_lt_zero _ hi)
        · intro g i hi
          exact False.elim (Nat.not_lt_zero _ hi)
    | succ n ih =>
        obtain ⟨f, hf⟩ := ih
        obtain ⟨L, hL⟩ := hstep n f hf
        exact s.liftStage_succ ρ τ T q a hρ hf L hL
  let n : ℕ := Finset.univ.sup s.generatorDegree + 1
  obtain ⟨f, hf⟩ := stages n
  have hbound (i : I) : s.generatorDegree i < n :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  refine ⟨f, s.graded_of_generators T hmult f hf.1, ?_, ?_⟩
  · apply s.parameterBasis.ext
    intro i
    exact hf.2.1 i (hbound i)
  · intro g x
    have he : f.comp (ρ g) = (τ g).comp f := by
      apply s.parameterBasis.ext
      intro i
      exact hf.2.2 g i (hbound i)
    exact congrArg (fun F : M →ₗ[A] N => F x) he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedKernelLift.lean -/
section


section

/-! # Graded equivariant lifting from regular-orbit kernels

The hypotheses here are explicit linear maps and explicit equivariant coordinate
equivalences for homogeneous kernels.  They are the objects supplied by the
prime-cyclic polynomial calculation.  The finite induction of
`CyclicGradedLift` then produces one parameter-linear lift in every degree.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (υ : CyclicRepresentation A G Q)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)
variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
variable (hτ : ∀ g n x, x ∈ T n → τ g x ∈ T n)
variable (hq : RepresentationIntertwines τ υ q)

def sourceDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (s.piece n) :=
  invariantSubmoduleRepresentation (restrictRepresentation ρ) (s.piece n)
    (fun g x hx => hρ g n x hx)

def targetDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (T n) :=
  invariantSubmoduleRepresentation (restrictRepresentation τ) (T n)
    (fun g x hx => hτ g n x hx)

def degreeQuotient (n : ℕ) : T n →ₗ[K] Q :=
  (q.restrictScalars K).comp (T n).subtype

def degreeTarget (n : ℕ) : s.piece n →ₗ[K] Q :=
  (a.restrictScalars K).comp (s.piece n).subtype

include hq in
theorem degreeQuotient_intertwines (n : ℕ) :
    RepresentationIntertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n) := by
  intro g x
  exact hq g x.val

def kernelDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (LinearMap.ker (degreeQuotient T q n)) :=
  invariantSubmoduleRepresentation (targetDegreeRepresentation τ T hτ n)
    (LinearMap.ker (degreeQuotient T q n))
    (kernel_invariant_of_intertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n))

variable
  (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
    s.multiplier j • y ∈ T (s.degree j))

include hρ hmult

/-- The full one-degree step, including construction of the lower subspace and
its ordinary linear retraction.  The field assumption is used only to split
that subspace; it is not used to average the group action. -/
theorem degreeLift_of_coinduced_kernel
    {n : ℕ} {f : M →ₗ[A] N} (hf : s.LiftStage ρ τ T q a n f)
    (β : s.piece n →ₗ[K] T n)
    (hβ : RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) β)
    (hqβ : (degreeQuotient T q n).comp β = s.degreeTarget a n)
    {C : Type*} [AddCommGroup C] [Module K C]
    (e : LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation e.toLinearMap) :
    ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L := by
  let ρn := s.sourceDegreeRepresentation ρ hρ n
  let τn := targetDegreeRepresentation τ T hτ n
  let υK := restrictRepresentation (K := K) υ
  let qn := degreeQuotient T q n
  let an := s.degreeTarget a n
  let U : Submodule K (s.piece n) :=
    ((s.cut n).restrictScalars K).comap (s.piece n).subtype
  have hU : ∀ g x, x ∈ U → ρn g x ∈ U := by
    intro g x hx
    change ρ g x.val ∈ s.cut n
    exact s.cut_invariant ρ hρ n g x.val hx
  obtain ⟨r, hr⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  let fU : U →ₗ[K] T n :=
    LinearMap.codRestrict (T n)
      ((f.restrictScalars K).comp ((s.piece n).subtype.comp U.subtype)) (by
        intro x
        exact s.graded_of_generators T hmult f hf.1 n x.val.val x.val.property)
  have hfU : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρn U hU) τn fU := by
    intro g x
    apply Subtype.ext
    exact LiftStage.equivariant_on_cut s ρ τ T q a hf g x.val.val x.property
  have hqfU : qn.comp fU = an.comp U.subtype := by
    ext x
    exact LiftStage.quotient_on_cut s ρ τ T q a hf x.val.val x.property
  have hqn : RepresentationIntertwines τn υK qn :=
    degreeQuotient_intertwines τ υ T q hτ hq n
  obtain ⟨L, hLeq, hLU, hqL⟩ := equivariant_lift_extend_subspace
    ρn τn υK U hU r hr qn hqn an β hβ hqβ fU hfU hqfU e he
  refine ⟨(T n).subtype.comp L, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (L x).property
  · intro g x
    exact congrArg Subtype.val (hLeq g x)
  · intro x
    exact congrArg (fun F : s.piece n →ₗ[K] Q => F x) hqL
  · intro x hx
    let ux : U := ⟨x, hx⟩
    exact congrArg (fun F : U →ₗ[K] T n => (F ux).val) hLU

/-- Graded parameter-linear equivariant lifting, with every one-degree
extension proved from regular-orbit coordinates for its actual kernel. -/
theorem exists_equivariantGradedLift_of_coinduced_kernels [Fintype I]
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hβ : ∀ n, RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) (β n))
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  apply s.exists_equivariantGradedLift_of_degreeExtensions ρ τ T q a hρ hmult
  intro n f hf
  exact s.degreeLift_of_coinduced_kernel ρ τ υ T q a hρ hτ hq hmult hf
    (β n) (hβ n) (hqβ n) (e n) (he n)

/-- The form used for the actual face rings: the preliminary lift is required
only to preserve degree and the prescribed quotient map.  All equivariance is
constructed from the explicit regular-orbit kernels. -/
theorem exists_equivariantGradedLift_of_ordinary_lifts [Fintype I]
    (ha : RepresentationIntertwines ρ υ a)
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have hβeq : ∀ n, ∃ F : s.piece n →ₗ[K] T n,
      RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
        (targetDegreeRepresentation τ T hτ n) F ∧
      (degreeQuotient T q n).comp F = s.degreeTarget a n := by
    intro n
    apply exists_equivariantLift_of_coinduced_kernel
      (s.sourceDegreeRepresentation ρ hρ n) (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n) (s.degreeTarget a n)
      (fun g x => ha g x.val) (β n) (hqβ n) (e n) (he n)
  choose F hF hqF using hβeq
  exact s.exists_equivariantGradedLift_of_coinduced_kernels
    ρ τ υ T q a hρ hτ hq hmult C F hF hqF e he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanGrading.lean -/
section


section

/-! # The actual Boolean descent basis satisfies the lifting hypotheses

The scalar basis and parameter basis are the already proved bases of the
actual barycentric face ring.  Its homogeneous pieces agree with ordinary
rank-weighted polynomial degree, not a grading chosen to make lifting easier.
-/

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem colorOrdinaryDegree_eq_zero_iff (m : ColorExponent V) :
    colorOrdinaryDegree m = 0 ↔ m = 0 := by
  constructor
  · intro hm
    apply Finsupp.ext
    intro c
    have hc : m c ≤ colorOrdinaryDegree m := by
      rw [colorOrdinaryDegree_fintype]
      calc
        m c = m c * 1 := (Nat.mul_one _).symm
        _ ≤ m c * (c.val + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
        _ ≤ ∑ i : Fin (Fintype.card V), m i * (i.val + 1) :=
          Finset.single_le_sum (f := fun i : Fin (Fintype.card V) => m i * (i.val + 1))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    change m c = 0
    omega
  · rintro rfl
    simp [colorOrdinaryDegree]

@[simp] theorem booleanParameterBasis_zero_parameter
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanParameterBasis (K := K) (σ, 0) = booleanColorBasis (K := K) σ := by
  simp [parameterDescentVector, colorPower]

/-- The exact positive graded free-basis structure of the Boolean barycentric
ring used in the prime-rank lift. -/
def booleanScalarGradedBasis :
    ScalarGradedBasis K (MvPolynomial (Fin (Fintype.card V)) K)
      (BooleanBarycentricRing V K)
      (VertexOrdering (Fintype.card V) V)
      (VertexOrdering (Fintype.card V) V × ColorExponent V) where
  parameterBasis := booleanColorBasis
  coefficientBasis := booleanParameterBasis
  generatorDegree σ := colorOrdinaryDegree (descentColorExponent σ)
  degree p := colorOrdinaryDegree p.2 + colorOrdinaryDegree (descentColorExponent p.1)
  parent := Prod.fst
  multiplier p := MvPolynomial.monomial p.2 1
  coefficient_eq p := by
    rw [booleanParameterBasis_apply, booleanColorBasis_apply]
    exact parameterDescentVector_eq_monomial_smul p
  parent_degree_le p := Nat.le_add_left _ _
  equal_degree_eq p hp := by
    obtain ⟨σ, m⟩ := p
    change colorOrdinaryDegree m + colorOrdinaryDegree (descentColorExponent σ) =
      colorOrdinaryDegree (descentColorExponent σ) at hp
    have hm : colorOrdinaryDegree m = 0 := by omega
    have hm0 := (colorOrdinaryDegree_eq_zero_iff m).mp hm
    subst m
    exact booleanParameterBasis_zero_parameter σ
  generator_homogeneous σ p hp := by
    rw [← booleanParameterBasis_zero_parameter, Module.Basis.repr_self]
    have hne : (σ, (0 : ColorExponent V)) ≠ p := by
      intro he
      subst p
      exact hp (by simp [colorOrdinaryDegree])
    simp [Finsupp.single_apply, hne]

theorem basisDegreeProjection_eq_self_iff_mem
    {I M : Type*} [AddCommGroup M] [Module K M]
    (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) (x : M) :
    basisDegreeProjection b degree n x = x ↔
      x ∈ basisOrdinaryDegreePiece b degree n := by
  constructor
  · intro hx i hi
    have h := congrArg (fun y => b.repr y i) hx
    rw [basisDegreeProjection_repr, if_neg hi] at h
    exact h.symm
  · intro hx
    change ∀ i, degree i ≠ n → b.repr x i = 0 at hx
    apply b.repr.injective
    ext i
    rw [basisDegreeProjection_repr]
    by_cases hi : degree i = n
    · rw [if_pos hi]
    · rw [if_neg hi, hx i hi]

theorem booleanParameterDegreeProjection_eq (n : ℕ) :
    basisDegreeProjection (booleanChainBasis (V := V) (K := K))
      (fun a => chainOrdinaryDegree a.val) n =
    basisDegreeProjection (booleanParameterBasis (V := V) (K := K))
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n := by
  apply basisDegreeProjection_eq_of_homogeneous
  intro a p hp
  rw [booleanParameterBasis_apply]
  apply parameterDescentVector_repr_color
  intro he
  apply hp
  rw [← colorOrdinaryDegree_chainColorDegree, he, colorOrdinaryDegree_add]

/-- Faithfulness of the homogeneous pieces in the lifting construction: they
are exactly the standard chain-monomial components of ordinary degree `n`. -/
theorem booleanScalarGradedBasis_piece_eq (n : ℕ) :
    (booleanScalarGradedBasis (V := V) (K := K)).piece n =
      basisOrdinaryDegreePiece (booleanChainBasis (V := V) (K := K))
        (fun a => chainOrdinaryDegree a.val) n := by
  ext x
  change x ∈ basisOrdinaryDegreePiece booleanParameterBasis
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n ↔ _
  rw [← basisDegreeProjection_eq_self_iff_mem,
    ← basisDegreeProjection_eq_self_iff_mem,
    booleanParameterDegreeProjection_eq]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicExponentFreeness.lean -/
section

section
/-! # Homogeneous exponent vectors under a prime cyclic permutation

This is the literal exponent action induced by renaming polynomial variables.
A nonidentity stabilizer forces the exponent vector to be constant. Therefore
all nonconstant exponent vectors have free orbits, and in a degree not divisible
by p every exponent vector has a free orbit.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]

/-- A nonzero translation is transitive on the prime cyclic set, expressed
without any finiteness or algebraic assumptions on the values of the function. -/
theorem primeShift_invariant_constant {A : Type*} (a : ZMod p → A)
    (g : ZMod p) (hg : g ≠ 0) (h : ∀ x, a (g + x) = a x) :
    ∀ x, a x = a 0 := by
  have hn : ∀ n : ℕ, ∀ x : ZMod p, a ((n : ZMod p) * g + x) = a x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        calc
          a (((n + 1 : ℕ) : ZMod p) * g + x) = a (g + ((n : ZMod p) * g + x)) := by
            congr 1
            simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            ac_rfl
          _ = a ((n : ZMod p) * g + x) := h _
          _ = a x := ih x
  intro x
  obtain ⟨n, he⟩ := ZMod.natCast_zmod_surjective (x / g)
  have hx : (n : ZMod p) * g = x := by rw [he, div_mul_cancel₀ _ hg]
  simpa only [hx, add_zero] using hn n 0

def cyclicConstantExponent (m : ℕ) : ZMod p →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => m)

@[simp] theorem cyclicConstantExponent_apply (m : ℕ) (x : ZMod p) :
    cyclicConstantExponent p m x = m := rfl

theorem cyclicConstantExponent_degree (m : ℕ) :
    (cyclicConstantExponent p m).degree = p * m := by
  rw [Finsupp.degree_eq_sum]
  simp only [cyclicConstantExponent_apply, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, Nat.cast_id]

theorem primeShift_fixed_exponent_constant (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) : ∀ x, a x = a 0 := by
  have hg0 : g.toAdd ≠ 0 := by
    intro h
    exact hg (congrArg Multiplicative.ofAdd h)
  apply primeShift_invariant_constant p (fun x => a x) g.toAdd hg0
  intro x
  have hh := congrArg (fun b : ZMod p →₀ ℕ => b (g.toAdd + x)) hfix
  change (a.mapDomain (Equiv.addLeft g.toAdd)) ((Equiv.addLeft g.toAdd) x) =
    a (g.toAdd + x) at hh
  rw [Finsupp.mapDomain_apply_of_injective (Equiv.addLeft g.toAdd).injective] at hh
  exact hh.symm

theorem primeShift_fixed_exponent_degree (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) : a.degree = p * a 0 := by
  have hc := primeShift_fixed_exponent_constant p a g hg hfix
  rw [Finsupp.degree_eq_sum]
  calc
    (∑ x : ZMod p, a x) = ∑ _x : ZMod p, a 0 := Finset.sum_congr rfl (fun x _ => hc x)
    _ = p * a 0 := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id]

theorem primeShift_fixed_exponent_eq (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) :
    a = cyclicConstantExponent p (a.degree / p) := by
  have hc := primeShift_fixed_exponent_constant p a g hg hfix
  have hd := primeShift_fixed_exponent_degree p a g hg hfix
  have hdiv : a.degree / p = a 0 := by
    rw [hd, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
  ext x
  rw [cyclicConstantExponent_apply, hdiv]
  exact hc x

theorem primeShift_no_fixed_exponent_of_not_dvd (a : ZMod p →₀ ℕ)
    (hn : ¬ p ∣ a.degree) (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    a.mapDomain (Equiv.addLeft g.toAdd) ≠ a := by
  intro hfix
  exact hn ⟨a 0, primeShift_fixed_exponent_degree p a g hg hfix⟩

theorem primeShift_constant_exponent_fixed (m : ℕ) (g : PrimeCycleGroup p) :
    (cyclicConstantExponent p m).mapDomain (Equiv.addLeft g.toAdd) =
      cyclicConstantExponent p m := by
  ext x
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

abbrev CyclicHomogeneousExponent (n : ℕ) := {a : ZMod p →₀ ℕ // a.degree = n}

noncomputable instance cyclicHomogeneousExponentFintype (n : ℕ) :
    Fintype (CyclicHomogeneousExponent p n) :=
  (Finsupp.finite_of_degree_eq n).fintype

def cyclicHomogeneousExponentAction (n : ℕ) :
    MulAction (PrimeCycleGroup p) (CyclicHomogeneousExponent p n) where
  smul g a := ⟨a.val.mapDomain (Equiv.addLeft g.toAdd), by
    rw [Finsupp.degree_mapDomain]
    exact a.property⟩
  one_smul a := by
    apply Subtype.ext
    change a.val.mapDomain (Equiv.addLeft (0 : ZMod p)) = a.val
    have he : (Equiv.addLeft (0 : ZMod p) : ZMod p → ZMod p) = id := by
      funext x
      exact zero_add x
    rw [he, Finsupp.mapDomain_id]
  mul_smul g h a := by
    apply Subtype.ext
    change a.val.mapDomain (Equiv.addLeft (g.toAdd + h.toAdd)) =
      (a.val.mapDomain (Equiv.addLeft h.toAdd)).mapDomain (Equiv.addLeft g.toAdd)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext x
    exact add_assoc g.toAdd h.toAdd x

theorem cyclicHomogeneous_nonidentity_fixed_unique (n : ℕ)
    (a : CyclicHomogeneousExponent p n) (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : (cyclicHomogeneousExponentAction p n).smul g a = a) :
    a.val = cyclicConstantExponent p (n / p) := by
  have hh := primeShift_fixed_exponent_eq p a.val g hg (congrArg Subtype.val hfix)
  simpa only [a.property] using hh

theorem cyclicHomogeneous_action_free_of_not_dvd (n : ℕ) (hn : ¬ p ∣ n) :
    ∀ a : CyclicHomogeneousExponent p n,
      Function.Injective (fun g : PrimeCycleGroup p =>
        (cyclicHomogeneousExponentAction p n).smul g a) := by
  letI := cyclicHomogeneousExponentAction p n
  intro a g h heq
  change g • a = h • a at heq
  have hfix : (h⁻¹ * g) • a = a := by rw [mul_smul, heq, inv_smul_smul]
  have hunit : h⁻¹ * g = 1 := by
    by_contra hg
    exact primeShift_no_fixed_exponent_of_not_dvd p a.val
      (by simpa only [a.property] using hn) (h⁻¹ * g) hg (congrArg Subtype.val hfix)
  exact (inv_mul_eq_one.mp hunit).symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicAugmentationKernel.lean -/
section

section
/-! # An explicit basis of an augmentation kernel

For a finite permutation basis with a distinguished fixed vector δ, the
augmentation kernel has basis e_i − e_δ, i ≠ δ. The construction is valid
over every commutative coefficient ring and carries the expected permutation
action. It is used degreewise in the exceptional prime-rank lifting argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

variable {I K : Type*} [Fintype I] [CommRing K]

theorem sum_eq_pivot_add_sum_complement {M : Type*} [AddCommMonoid M]
    (i₀ : I) (f : I → M) :
    (∑ i, f i) = f i₀ + ∑ i : {i : I // i ≠ i₀}, f i.val := by
  have he : (∑ i : {i : I // i ≠ i₀}, f i.val) =
      ∑ i ∈ Finset.univ.erase i₀, f i :=
    (Finset.sum_subtype (Finset.univ.erase i₀) (fun i => by simp) f).symm
  rw [he]
  calc
    (∑ i, f i) = (∑ i ∈ Finset.univ.erase i₀, f i) + f i₀ :=
      (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i₀)).symm
    _ = f i₀ + ∑ i ∈ Finset.univ.erase i₀, f i := add_comm _ _

def finiteAugmentation (K : Type*) [CommRing K] : (I → K) →ₗ[K] K where
  toFun x := ∑ i, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

def augmentedVector (i₀ : I) (x : {i : I // i ≠ i₀} → K) : I → K :=
  fun i => if h : i = i₀ then -(∑ j, x j) else x ⟨i, h⟩

theorem augmentedVector_sum (i₀ : I) (x : {i : I // i ≠ i₀} → K) :
    (∑ i, augmentedVector i₀ x i) = 0 := by
  rw [sum_eq_pivot_add_sum_complement i₀]
  have hrest : (∑ i : {i : I // i ≠ i₀}, augmentedVector i₀ x i.val) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [augmentedVector, dif_neg i.property]
  rw [hrest]
  simp [augmentedVector]

def augmentationKernelEquiv (K : Type*) [CommRing K] (i₀ : I) :
    ({i : I // i ≠ i₀} → K) ≃ₗ[K] LinearMap.ker (finiteAugmentation (I := I) K) where
  toFun x := ⟨augmentedVector i₀ x, augmentedVector_sum i₀ x⟩
  invFun x := fun i => x.val i.val
  left_inv x := by
    funext i
    simp only [augmentedVector, dif_neg i.property]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      simp only [augmentedVector, dif_pos rfl]
      have hx : x.val i₀ + ∑ j : {i : I // i ≠ i₀}, x.val j.val = 0 := by
        rw [← sum_eq_pivot_add_sum_complement]
        exact x.property
      exact (eq_neg_iff_add_eq_zero.mpr hx).symm
    · simp only [augmentedVector, dif_neg hi]
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.sum_add_distrib, neg_add, add_comm]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.mul_sum, smul_eq_mul]

def augmentationKernelBasis (K : Type*) [CommRing K] (i₀ : I) :
    Module.Basis {i : I // i ≠ i₀} K (LinearMap.ker (finiteAugmentation (I := I) K)) :=
  (Pi.basisFun K {i : I // i ≠ i₀}).map (augmentationKernelEquiv K i₀)

/-- These really are the difference vectors in the original finite module. -/
theorem augmentationKernelBasis_apply (i₀ : I) (j : {i : I // i ≠ i₀}) (i : I) :
    (augmentationKernelBasis K i₀ j).val i =
      (if i = j.val then 1 else 0) - (if i = i₀ then 1 else 0) := by
  by_cases hi : i = i₀
  · subst i
    have hj : i₀ ≠ j.val := Ne.symm j.property
    simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hj]
  · simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hi, Subtype.ext_iff, eq_comm]

/-- A permutation fixing the pivot permutes the difference-basis vectors.
The equation is in the original function space, so it applies immediately
after any equivariant monomial-basis identification. -/
theorem augmentationKernelBasis_covariant (i₀ : I) (e : Equiv.Perm I) (he : e i₀ = i₀)
    (j : {i : I // i ≠ i₀}) :
    (fun i => (augmentationKernelBasis K i₀ j).val (e.symm i)) =
      (augmentationKernelBasis K i₀
        ⟨e j.val, by
          intro h
          apply j.property
          exact e.injective (h.trans he.symm)⟩).val := by
  funext i
  rw [augmentationKernelBasis_apply, augmentationKernelBasis_apply]
  have h₁ : e.symm i = j.val ↔ i = e j.val := by
    constructor
    · intro h
      simpa using congrArg e h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  have h₀ : e.symm i = i₀ ↔ i = i₀ := by
    constructor
    · intro h
      have hh := congrArg e h
      simpa only [Equiv.apply_symm_apply, he] using hh
    · intro h
      subst i
      exact e.symm_apply_eq.mpr he.symm
  simp only [h₁, h₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousCoordinates.lean -/
section

section
/-! # Actual homogeneous polynomial coordinates for cyclic lifting

The homogeneous component is the existing `polynomialDegreePiece` submodule
of the ordinary multivariate polynomial ring. Evaluation at all variables
equal to one becomes the finite coefficient sum in its monomial coordinates.
Consequently its actual kernel has the difference-monomial basis used by the
prime-cyclic lifting construction.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

abbrev CyclicPolynomialPiece (n : ℕ) :=
  polynomialDegreePiece (V := ZMod p) (K := K) n

theorem cyclicPolynomialPiece_mem_iff_supported (n : ℕ) (f : MvPolynomial (ZMod p) K) :
    f ∈ CyclicPolynomialPiece p K n ↔
      f.coeff ∈ Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} := by
  rw [Finsupp.mem_supported']
  change (∀ a : ZMod p →₀ ℕ, vertexDegree (fun x => a x) ≠ n → f.coeff a = 0) ↔ _
  simp only [vertexDegree, ← Finsupp.degree_eq_sum, Set.mem_setOf_eq]

def cyclicPolynomialSupportedEquiv (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K]
      Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} where
  toFun f := ⟨f.val.coeff,
    (cyclicPolynomialPiece_mem_iff_supported p K n f.val).mp f.property⟩
  invFun f := ⟨(MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val, by
    apply (cyclicPolynomialPiece_mem_iff_supported p K n _).mpr
    change (MvPolynomial.basisMonomials (ZMod p) K).repr
      ((MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.apply_symm_apply f.val
  map_add' f g := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_smul c f.val

def cyclicPolynomialCoordinates (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K] (CyclicHomogeneousExponent p n → K) :=
  (cyclicPolynomialSupportedEquiv p K n).trans
    ((Finsupp.supportedEquivFinsupp {a : ZMod p →₀ ℕ | a.degree = n}).trans
      (Finsupp.linearEquivFunOnFinite K K (CyclicHomogeneousExponent p n)))

@[simp] theorem cyclicPolynomialCoordinates_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n f a = f.val.coeff a.val := rfl

def cyclicHomogeneousMonomial (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    CyclicPolynomialPiece p K n :=
  ⟨MvPolynomial.monomial a.val 1, by
    have hd : vertexDegree (fun x => a.val x) = n := by
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact a.property
    intro b hb
    have hne : a.val ≠ b := by
      intro he
      subst b
      exact hb hd
    simp only [MvPolynomial.coeff_monomial, if_neg hne]⟩

@[simp] theorem cyclicPolynomialCoordinates_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) = Pi.single a 1 := by
  funext b
  rw [cyclicPolynomialCoordinates_apply]
  simp [cyclicHomogeneousMonomial, MvPolynomial.coeff_monomial,
    Pi.single_apply, Subtype.ext_iff, eq_comm]

def cyclicHomogeneousMonomialBasis (n : ℕ) :
    Module.Basis (CyclicHomogeneousExponent p n) K (CyclicPolynomialPiece p K n) :=
  (Pi.basisFun K (CyclicHomogeneousExponent p n)).map (cyclicPolynomialCoordinates p K n).symm

theorem cyclicHomogeneousMonomialBasis_apply (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousMonomialBasis p K n a = cyclicHomogeneousMonomial p K n a := by
  apply (cyclicPolynomialCoordinates p K n).injective
  simp only [cyclicHomogeneousMonomialBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply, cyclicPolynomialCoordinates_monomial]

theorem rename_equiv_coefficient (e : Equiv.Perm (ZMod p))
    (f : MvPolynomial (ZMod p) K) (a : ZMod p →₀ ℕ) :
    (MvPolynomial.rename e f).coeff a = f.coeff (a.mapDomain e.symm) := by
  have he : (a.mapDomain e.symm).mapDomain e = a := by
    rw [← Finsupp.mapDomain_comp]
    have hh : (e : ZMod p → ZMod p) ∘ e.symm = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hh, Finsupp.mapDomain_id]
  simpa only [he] using
    MvPolynomial.coeff_rename_mapDomain e e.injective f (a.mapDomain e.symm)

def cyclicHomogeneousRename (n : ℕ) (e : Equiv.Perm (ZMod p)) :
    Module.End K (CyclicPolynomialPiece p K n) where
  toFun f := ⟨MvPolynomial.rename e f.val, by
    intro a ha
    rw [rename_equiv_coefficient]
    apply f.property
    have hd : vertexDegree (fun x => (a.mapDomain e.symm) x) = vertexDegree (fun x => a x) := by
      simp only [vertexDegree, ← Finsupp.degree_eq_sum, Finsupp.degree_mapDomain]
    rwa [hd]⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

theorem cyclicPolynomialCoordinates_rename (n : ℕ) (e : Equiv.Perm (ZMod p))
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousRename p K n e f) a =
      cyclicPolynomialCoordinates p K n f
        ⟨a.val.mapDomain e.symm, by rw [Finsupp.degree_mapDomain]; exact a.property⟩ := by
  exact rename_equiv_coefficient p K e f.val a.val

/-- Literal evaluation at the all-one root assignment, restricted to the
actual homogeneous polynomial component. -/
def cyclicHomogeneousAugmentation (n : ℕ) : CyclicPolynomialPiece p K n →ₗ[K] K :=
  (MvPolynomial.aeval (fun _ : ZMod p => (1 : K))).toLinearMap.comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicHomogeneousAugmentation_eq_sum (n : ℕ) :
    cyclicHomogeneousAugmentation p K n =
      (finiteAugmentation (I := CyclicHomogeneousExponent p n) K).comp
        (cyclicPolynomialCoordinates p K n).toLinearMap := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  change MvPolynomial.aeval (fun _ : ZMod p => (1 : K))
      (MvPolynomial.monomial a.val 1) =
    ∑ i, cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) i
  rw [cyclicPolynomialCoordinates_monomial]
  simp [MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod]

def cyclicHomogeneousAugmentationKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      LinearMap.ker (finiteAugmentation (I := CyclicHomogeneousExponent p n) K) where
  toFun f := ⟨cyclicPolynomialCoordinates p K n f.val, by
    change finiteAugmentation K (cyclicPolynomialCoordinates p K n f.val) = 0
    have hh : cyclicHomogeneousAugmentation p K n f.val = 0 := f.property
    simp only [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe] at hh
    exact hh⟩
  invFun f := ⟨(cyclicPolynomialCoordinates p K n).symm f.val, by
    change cyclicHomogeneousAugmentation p K n
      ((cyclicPolynomialCoordinates p K n).symm f.val) = 0
    rw [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ f.val
  right_inv f := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ f.val
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

def cyclicHomogeneousPivot (n : ℕ) (hn : p ∣ n) : CyclicHomogeneousExponent p n :=
  ⟨cyclicConstantExponent p (n / p), by
    rw [cyclicConstantExponent_degree, Nat.mul_comm, Nat.div_mul_cancel hn]⟩

def cyclicHomogeneousDifferenceBasis (n : ℕ) (hn : p ∣ n) :
    Module.Basis {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} K
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn)).map
    (cyclicHomogeneousAugmentationKernelEquiv p K n).symm

/-- The actual kernel vectors are differences of the original monomials;
the pivot is the unique invariant exponent vector in degree n. -/
theorem cyclicHomogeneousDifferenceBasis_apply (n : ℕ) (hn : p ∣ n)
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    (cyclicHomogeneousDifferenceBasis p K n hn a).val =
      cyclicHomogeneousMonomial p K n a.val -
        cyclicHomogeneousMonomial p K n (cyclicHomogeneousPivot p n hn) := by
  apply (cyclicPolynomialCoordinates p K n).injective
  have hleft : cyclicPolynomialCoordinates p K n
      (cyclicHomogeneousDifferenceBasis p K n hn a).val =
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val := by
    change cyclicPolynomialCoordinates p K n
      ((cyclicPolynomialCoordinates p K n).symm
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [hleft, map_sub, cyclicPolynomialCoordinates_monomial,
    cyclicPolynomialCoordinates_monomial]
  funext b
  rw [augmentationKernelBasis_apply]
  simp only [Pi.single_apply, Pi.sub_apply, eq_comm]
  split_ifs <;> rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousAction.lean -/
section

section
/-! # Actual cyclic polynomial actions and free kernel coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem primeTranslation_symm (g : PrimeCycleGroup p) :
    (Equiv.addLeft g.toAdd).symm = Equiv.addLeft (g⁻¹).toAdd := by
  apply Equiv.ext
  intro x
  apply (Equiv.addLeft g.toAdd).injective
  rw [Equiv.apply_symm_apply]
  change x = g.toAdd + (-g.toAdd + x)
  abel

def cyclicPolynomialRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p) (CyclicPolynomialPiece p K n) where
  toFun g := cyclicHomogeneousRename p K n (Equiv.addLeft g.toAdd)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (0 : ZMod p)) f.val = f.val
    have he : (Equiv.addLeft (0 : ZMod p) : ZMod p → ZMod p) = id := by
      funext x
      exact zero_add x
    rw [he, MvPolynomial.rename_id_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (g.toAdd + h.toAdd)) f.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (MvPolynomial.rename (Equiv.addLeft h.toAdd) f.val)
    rw [MvPolynomial.rename_rename]
    have he : (Equiv.addLeft (g.toAdd + h.toAdd) : ZMod p → ZMod p) =
        (Equiv.addLeft g.toAdd) ∘ (Equiv.addLeft h.toAdd) := by
      funext x
      exact add_assoc g.toAdd h.toAdd x
    rw [he]

theorem cyclicPolynomialCoordinates_equivariant (n : ℕ) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicPolynomialRepresentation p K n)
      permutationFunctionRepresentation (cyclicPolynomialCoordinates p K n).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val).coeff a.val =
    f.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val a.val

theorem cyclicHomogeneousAugmentation_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousAugmentation p K n f := by
  letI := cyclicHomogeneousExponentAction p n
  rw [cyclicHomogeneousAugmentation_eq_sum]
  change (∑ a, cyclicPolynomialCoordinates p K n (cyclicPolynomialRepresentation p K n g f) a) =
    ∑ a, cyclicPolynomialCoordinates p K n f a
  calc
    _ = ∑ a, cyclicPolynomialCoordinates p K n f (g⁻¹ • a) :=
      congrArg (fun z : CyclicHomogeneousExponent p n → K => ∑ a, z a)
        (cyclicPolynomialCoordinates_equivariant p K n g f)
    _ = _ := Fintype.sum_equiv (MulAction.toPerm (g⁻¹)) _ _ (fun _ => rfl)

def cyclicAugmentationKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) (by
      intro g f hf
      change cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) = 0
      rw [cyclicHomogeneousAugmentation_invariant]
      exact hf)

theorem cyclicHomogeneousPivot_fixed (n : ℕ) (hn : p ∣ n) (g : PrimeCycleGroup p) :
    (cyclicHomogeneousExponentAction p n).smul g (cyclicHomogeneousPivot p n hn) =
      cyclicHomogeneousPivot p n hn := by
  apply Subtype.ext
  exact primeShift_constant_exponent_fixed p (n / p) g

abbrev CyclicNonpivotExponent (n : ℕ) (hn : p ∣ n) :=
  {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}

def cyclicNonpivotExponentAction (n : ℕ) (hn : p ∣ n) :
    MulAction (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn) := by
  letI := cyclicHomogeneousExponentAction p n
  exact {
    smul := fun g a => ⟨g • a.val, by
      intro h
      have hh := congrArg (fun b => g⁻¹ • b) h
      have hpivot : g⁻¹ • cyclicHomogeneousPivot p n hn =
          cyclicHomogeneousPivot p n hn := cyclicHomogeneousPivot_fixed p n hn g⁻¹
      rw [inv_smul_smul, hpivot] at hh
      exact a.property hh⟩
    one_smul := fun a => Subtype.ext (one_smul (PrimeCycleGroup p) a.val)
    mul_smul := fun g h a => Subtype.ext (mul_smul g h a.val) }

/-- Excluding the unique invariant exponent vector leaves a free action. -/
theorem cyclicNonpivotExponent_no_fixed (n : ℕ) (hn : p ∣ n)
    (g : PrimeCycleGroup p) (a : CyclicNonpivotExponent p n hn)
    (hfix : (cyclicNonpivotExponentAction p n hn).smul g a = a) : g = 1 := by
  by_contra hg
  apply a.property
  apply Subtype.ext
  exact cyclicHomogeneous_nonidentity_fixed_unique p n a.val g hg
    (congrArg Subtype.val hfix)

def cyclicAugmentationComplementCoordinates (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      (CyclicNonpivotExponent p n hn → K) :=
  (cyclicHomogeneousAugmentationKernelEquiv p K n).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicAugmentationComplementCoordinates_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousAugmentation p K n))
    (a : CyclicNonpivotExponent p n hn) :
    cyclicAugmentationComplementCoordinates p K n hn f a = f.val.val.coeff a.val.val := rfl

/-- In the actual homogeneous kernel, the difference-monomial coordinates
carry the free permutation representation on nonpivot exponents. -/
theorem cyclicAugmentationComplementCoordinates_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicAugmentationKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicAugmentationComplementCoordinates p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicAugmentationComplementCoordinates p K n hn
      (cyclicAugmentationKernelRepresentation p K n g f) a =
    cyclicAugmentationComplementCoordinates p K n hn f (g⁻¹ • a)
  rw [cyclicAugmentationComplementCoordinates_apply,
    cyclicAugmentationComplementCoordinates_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicRetractionKernel.lean -/
section


section

/-! # The actual homogeneous kernel of the prime orbit retraction

In degree `n`, the orbit retraction is zero if `p` does not divide `n`.
Otherwise it is the coefficient sum, followed by the monomial embedding in
degree `n / p`.  This identifies its actual kernel with the free cyclic
permutation modules used by the equivariant lifting argument.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

def cyclicHomogeneousOrbitRetraction (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] K[X] :=
  (primeOrbitRetraction p).comp (CyclicPolynomialPiece p K n).subtype

@[simp] theorem cyclicHomogeneousAugmentation_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousAugmentation p K n (cyclicHomogeneousMonomial p K n a) = 1 := by
  change MvPolynomial.eval (fun _ => (1 : K)) (MvPolynomial.monomial a.val (1 : K)) = 1
  simp [MvPolynomial.eval_monomial]

theorem cyclicHomogeneousOrbitRetraction_eq (n : ℕ) :
    cyclicHomogeneousOrbitRetraction p K n =
      if p ∣ n then
        (Polynomial.monomial (n / p)).comp (cyclicHomogeneousAugmentation p K n)
      else 0 := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  have ha : a.val.sum (fun _ i => i) = n := a.property
  have he : cyclicHomogeneousOrbitRetraction p K n
      (cyclicHomogeneousMonomial p K n a) =
      if p ∣ n then Polynomial.monomial (n / p) 1 else 0 := by
    change primeOrbitRetraction p (MvPolynomial.monomial a.val (1 : K)) = _
    rw [primeOrbitRetraction_monomial, ha]
  rw [he]
  by_cases hn : p ∣ n
  · simp only [if_pos hn, LinearMap.comp_apply, cyclicHomogeneousAugmentation_monomial]
  · simp only [if_neg hn, LinearMap.zero_apply]

theorem cyclicHomogeneousOrbitRetraction_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n f =
      if p ∣ n then Polynomial.monomial (n / p)
        (cyclicHomogeneousAugmentation p K n f) else 0 := by
  rw [cyclicHomogeneousOrbitRetraction_eq]
  split_ifs <;> rfl

theorem cyclicHomogeneousOrbitKernel_eq_top (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) = ⊤ := by
  rw [cyclicHomogeneousOrbitRetraction_eq, if_neg hn, LinearMap.ker_zero]

theorem cyclicHomogeneousOrbitKernel_eq_augmentationKernel (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) =
      LinearMap.ker (cyclicHomogeneousAugmentation p K n) := by
  ext f
  change cyclicHomogeneousOrbitRetraction p K n f = 0 ↔
    cyclicHomogeneousAugmentation p K n f = 0
  rw [cyclicHomogeneousOrbitRetraction_apply, if_pos hn]
  exact Polynomial.monomial_eq_zero_iff _ _

def cyclicOrbitKernelCoordinatesOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (CyclicHomogeneousExponent p n → K) :=
  ((LinearEquiv.ofEq _ _ (cyclicHomogeneousOrbitKernel_eq_top p K n hn)).trans
    Submodule.topEquiv).trans (cyclicPolynomialCoordinates p K n)

@[simp] theorem cyclicOrbitKernelCoordinatesOfNotDvd_apply (n : ℕ) (hn : ¬p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : CyclicHomogeneousExponent p n) :
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f a = f.val.val.coeff a.val := by
  change cyclicPolynomialCoordinates p K n f.val a = f.val.val.coeff a.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a

def cyclicOrbitKernelCoordinatesOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      ({a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} → K) :=
  ((LinearEquiv.ofEq _ _
    (cyclicHomogeneousOrbitKernel_eq_augmentationKernel p K n hn)).trans
      (cyclicHomogeneousAugmentationKernelEquiv p K n)).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicOrbitKernelCoordinatesOfDvd_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f a = f.val.val.coeff a.val.val := by
  change cyclicPolynomialCoordinates p K n f.val a.val = f.val.val.coeff a.val.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitKernelCoinduced.lean -/
section


section

/-! # Coinduced coordinates for the actual orbit-retraction kernel

The representation here is the literal variable-renaming action restricted to
the kernel of the homogeneous orbit retraction.  The coordinate equivalences
are built from actual monomial coefficients.  Their free-orbit decomposition
provides the coinduced target required by the equivariant lifting step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem cyclicHomogeneousOrbitRetraction_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousOrbitRetraction p K n f := by
  simp only [cyclicHomogeneousOrbitRetraction_apply,
    cyclicHomogeneousAugmentation_invariant]

theorem cyclicOrbitKernel_invariant (n : ℕ) :
    ∀ (g : PrimeCycleGroup p) (f : CyclicPolynomialPiece p K n),
      f ∈ LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) →
        cyclicPolynomialRepresentation p K n g f ∈
          LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) := by
  intro g f hf
  change cyclicHomogeneousOrbitRetraction p K n
    (cyclicPolynomialRepresentation p K n g f) = 0
  rw [cyclicHomogeneousOrbitRetraction_invariant]
  exact hf

def cyclicOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (cyclicOrbitKernel_invariant p K n)

theorem cyclicOrbitKernelCoordinatesOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfNotDvd_apply, cyclicOrbitKernelCoordinatesOfNotDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val =
    f.val.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val

theorem cyclicOrbitKernelCoordinatesOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfDvd_apply, cyclicOrbitKernelCoordinatesOfDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

abbrev CyclicOrbitIndexOfNotDvd (n : ℕ) : Type :=
  letI := cyclicHomogeneousExponentAction p n
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicHomogeneousExponent p n)

abbrev CyclicOrbitIndexOfDvd (n : ℕ) (hn : p ∣ n) : Type :=
  letI := cyclicNonpivotExponentAction p n hn
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn)

theorem cyclicHomogeneous_no_fixed_of_not_dvd (n : ℕ) (hn : ¬p ∣ n) :
    ∀ (g : PrimeCycleGroup p) (a : CyclicHomogeneousExponent p n),
      (cyclicHomogeneousExponentAction p n).smul g a = a → g = 1 := by
  letI := cyclicHomogeneousExponentAction p n
  intro g a hfix
  apply cyclicHomogeneous_action_free_of_not_dvd p n hn a
  exact hfix.trans (one_smul (PrimeCycleGroup p) a).symm

def cyclicOrbitKernelCoinducedOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfNotDvd p n → K) := by
  letI := cyclicHomogeneousExponentAction p n
  exact (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))

theorem cyclicOrbitKernelCoinducedOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  change freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfNotDvd p n → K) g
      (freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))
    (cyclicOrbitKernelCoordinatesOfNotDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn) g
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))

def cyclicOrbitKernelCoinducedOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfDvd p n hn → K) := by
  letI := cyclicNonpivotExponentAction p n hn
  exact (cyclicOrbitKernelCoordinatesOfDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))

theorem cyclicOrbitKernelCoinducedOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  change freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfDvd p n hn → K) g
      (freePermutationCoinducedEquiv
      (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))
    (cyclicOrbitKernelCoordinatesOfDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicNonpivotExponent_no_fixed p n hn) g
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))

/-- Every degree of the actual orbit-retraction kernel is coinduced, with
no hypothesis on the characteristic or invertibility of the group order. -/
theorem cyclicOrbitKernel_isCoinduced (n : ℕ) :
    ∃ (J : Type) (e : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K)),
      RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  by_cases hn : p ∣ n
  · exact ⟨CyclicOrbitIndexOfDvd p n hn, cyclicOrbitKernelCoinducedOfDvd p K n hn,
      cyclicOrbitKernelCoinducedOfDvd_equivariant p K n hn⟩
  · exact ⟨CyclicOrbitIndexOfNotDvd p n, cyclicOrbitKernelCoinducedOfNotDvd p K n hn,
      cyclicOrbitKernelCoinducedOfNotDvd_equivariant p K n hn⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryKernel.lean -/
section


section

/-! # The combined boundary and orbit kernel

The quotient map records the genuine top-face boundary and the orbit
retraction simultaneously.  Its homogeneous kernel is top multiplication
times the corresponding orbit kernel one rank lower in degree.  Degrees
below the top rank are handled explicitly; both kernels are then zero.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

local instance : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)

def cyclicPolynomialTop : MvPolynomial (ZMod p) K :=
  ∏ v : ZMod p, MvPolynomial.X v

omit [CharP K p] in
theorem cyclicPolynomialTop_eq_esymm :
    cyclicPolynomialTop p K = MvPolynomial.esymm (ZMod p) K p := by
  unfold cyclicPolynomialTop MvPolynomial.esymm
  have hc : (Finset.univ : Finset (ZMod p)).card = p := by simp
  have he : (Finset.univ : Finset (ZMod p)).powersetCard p = {Finset.univ} :=
    (congrArg (fun n => (Finset.univ : Finset (ZMod p)).powersetCard n) hc.symm).trans
      (Finset.powersetCard_self _)
  rw [he]
  simp

omit [CharP K p] in
theorem cyclicPolynomialTop_degree :
    cyclicPolynomialTop p K ∈ CyclicPolynomialPiece p K p := by
  have hd : vertexDegree (fun v : ZMod p => fullExponent (ZMod p) v) = p := by
    simp [vertexDegree, ZMod.card]
  have hh := monomial_mem_polynomialDegreePiece (fullExponent (ZMod p)) (1 : K)
  rw [hd, full_monomial_eq_prod] at hh
  exact hh

omit [CharP K p] in
theorem cyclicPolynomialTop_mul_injective :
    Function.Injective (fun f : MvPolynomial (ZMod p) K => cyclicPolynomialTop p K * f) :=
  (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset (ZMod p))).left

theorem cyclicPolynomialTop_orbitRetraction (f : MvPolynomial (ZMod p) K) :
    primeOrbitRetraction p (cyclicPolynomialTop p K * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  rw [cyclicPolynomialTop_eq_esymm]
  exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f

def cyclicBoundaryOrbitMap :
    MvPolynomial (ZMod p) K →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  polynomialBooleanBoundaryMap.toLinearMap.prod (primeOrbitRetraction p)

def cyclicBoundaryOrbitDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  (cyclicBoundaryOrbitMap p K).comp (CyclicPolynomialPiece p K n).subtype

theorem cyclicBoundaryOrbitDegree_mem_kernel (n : ℕ) (f : CyclicPolynomialPiece p K n) :
    f ∈ LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ↔
      polynomialBooleanBoundaryMap f.val = 0 ∧ primeOrbitRetraction p f.val = 0 := by
  change (polynomialBooleanBoundaryMap f.val, primeOrbitRetraction p f.val) = (0, 0) ↔ _
  exact Prod.mk_inj

omit [CharP K p] in
theorem cyclicPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial (ZMod p) K)
    (hf : cyclicPolynomialTop p K * f ∈ CyclicPolynomialPiece p K (m + p)) :
    f ∈ CyclicPolynomialPiece p K m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) =
      p + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hn : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) ≠ m + p := by
    rw [hdeg]
    omega
  have hh := hf (fullExponent (ZMod p) + a) hn
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem cyclicBoundaryOrbitKernel_zero_below (n : ℕ) (hn : n < p)
    (f : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) : f = 0 := by
  obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
  obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
  have hg0 : g = 0 := by
    ext a
    have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
      change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
      rw [vertexDegree_add]
      simp [vertexDegree]
    have hh := f.val.property (fullExponent (ZMod p) + a) (by omega)
    rw [← hg, ← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
    exact hh
  apply Subtype.ext
  apply Subtype.ext
  change f.val.val = 0
  rw [← hg, hg0, mul_zero]

theorem cyclicOrbitKernel_zero_degree
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K 0)) : f = 0 := by
  have hcoeff : ∀ a : ZMod p →₀ ℕ, f.val.val.coeff a = 0 := by
    intro a
    by_cases ha : a = 0
    · subst a
      have hE := f.property
      change cyclicHomogeneousOrbitRetraction p K 0 f.val = 0 at hE
      rw [cyclicHomogeneousOrbitRetraction_apply, if_pos (dvd_zero p)] at hE
      have haug : cyclicHomogeneousAugmentation p K 0 f.val = 0 :=
        (Polynomial.monomial_eq_zero_iff _ _).mp hE
      rw [cyclicHomogeneousAugmentation_eq_sum] at haug
      change (∑ a : CyclicHomogeneousExponent p 0,
        cyclicPolynomialCoordinates p K 0 f.val a) = 0 at haug
      have hzero : ∀ a : CyclicHomogeneousExponent p 0, a.val = 0 := by
        intro a
        exact (Finsupp.degree_eq_zero_iff a.val).mp a.property
      letI : Unique (CyclicHomogeneousExponent p 0) := {
        default := ⟨0, by simp⟩
        uniq := fun a => Subtype.ext (hzero a) }
      rw [Finset.univ_unique, Finset.sum_singleton, cyclicPolynomialCoordinates_apply] at haug
      simpa only [hzero default] using haug
    · apply f.val.property
      change vertexDegree (fun v => a v) ≠ 0
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
  apply Subtype.ext
  apply Subtype.ext
  exact MvPolynomial.ext _ _ hcoeff

def cyclicBoundaryOrbitTopMap (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) →ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  by_cases hn : p ≤ n
  · refine {
      toFun := fun f => ⟨⟨cyclicPolynomialTop p K * f.val.val, ?_⟩, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
    · have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p K) f.val.val
        (cyclicPolynomialTop_degree p K) f.val.property
      simpa only [Nat.add_sub_of_le hn] using hh
    · apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        exact ⟨f.val.val, rfl⟩
      · rw [cyclicPolynomialTop_orbitRetraction]
        change Polynomial.X * cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0
        rw [show cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0 from f.property,
          mul_zero]
    · intro f g
      apply Subtype.ext
      apply Subtype.ext
      exact mul_add _ _ _
    · intro c f
      apply Subtype.ext
      apply Subtype.ext
      exact mul_smul_comm _ _ _
  · exact 0

theorem cyclicBoundaryOrbitTopMap_apply (n : ℕ) (hn : p ≤ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p))) :
    (cyclicBoundaryOrbitTopMap p K n f).val.val = cyclicPolynomialTop p K * f.val.val := by
  simp only [cyclicBoundaryOrbitTopMap, dif_pos hn]
  rfl

theorem cyclicBoundaryOrbitTopMap_bijective (n : ℕ) :
    Function.Bijective (cyclicBoundaryOrbitTopMap p K n) := by
  by_cases hn : p ≤ n
  · constructor
    · intro f g hfg
      apply Subtype.ext
      apply Subtype.ext
      apply cyclicPolynomialTop_mul_injective p K
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn f).symm.trans
        ((congrArg (fun x => x.val.val) hfg).trans
          (cyclicBoundaryOrbitTopMap_apply p K n hn g))
    · intro f
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
      obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
      have hgdeg : g ∈ CyclicPolynomialPiece p K (n - p) := by
        apply cyclicPolynomialTop_predecessor_degree p K (n - p) g
        rw [Nat.sub_add_cancel hn]
        simpa only [cyclicPolynomialTop, hg] using f.val.property
      have hgE : primeOrbitRetraction p g = 0 := by
        apply (Polynomial.isRegular_X (R := K)).left
        change Polynomial.X * primeOrbitRetraction p g = Polynomial.X * (0 : K[X])
        rw [mul_zero, ← cyclicPolynomialTop_orbitRetraction,
          show cyclicPolynomialTop p K * g = f.val.val from hg]
        exact hE
      let g' : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) :=
        ⟨⟨g, hgdeg⟩, hgE⟩
      refine ⟨g', ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn g').trans hg
  · have hlt : n < p := Nat.lt_of_not_ge hn
    have hz : n - p = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    have hsource : ∀ f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)), f = 0 := by
      rw [hz]
      exact cyclicOrbitKernel_zero_degree p K
    constructor
    · intro f g _
      exact (hsource f).trans (hsource g).symm
    · intro f
      exact ⟨0, (map_zero _).trans (cyclicBoundaryOrbitKernel_zero_below p K n hlt f).symm⟩

def cyclicBoundaryOrbitKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) ≃ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) :=
  LinearEquiv.ofBijective (cyclicBoundaryOrbitTopMap p K n)
    (cyclicBoundaryOrbitTopMap_bijective p K n)

omit [CharP K p] in
theorem cyclicPolynomialTop_rename (e : Equiv.Perm (ZMod p)) :
    MvPolynomial.rename e (cyclicPolynomialTop p K) = cyclicPolynomialTop p K := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

def cyclicBoundaryOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) (by
      intro g f hf
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f).mp hf
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val).mp hb
        change cyclicPolynomialTop p K * x = f.val at hx
        apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
        change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
          MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val
        rw [← hx, map_mul, cyclicPolynomialTop_rename]
      · change primeOrbitRetraction p
          (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val) = 0
        rw [primeOrbitRetraction_rename]
        exact hE)

theorem cyclicBoundaryOrbitKernelEquiv_equivariant (n : ℕ) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K (n - p))
      (cyclicBoundaryOrbitKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelEquiv p K n).toLinearMap := by
  intro g f
  apply Subtype.ext
  apply Subtype.ext
  by_cases hn : p ≤ n
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    rw [cyclicBoundaryOrbitTopMap_apply p K n hn,
      cyclicBoundaryOrbitTopMap_apply p K n hn, map_mul, cyclicPolynomialTop_rename]
    rfl
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    simp [cyclicBoundaryOrbitTopMap, hn]

/-- Every actual homogeneous combined kernel has regular-orbit coordinates.
This supplies the kernel hypothesis in the graded equivariant lifting theorem. -/
theorem cyclicBoundaryOrbitKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicBoundaryOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicOrbitKernel_isCoinduced p K (n - p)
  let t := cyclicBoundaryOrbitKernelEquiv p K n
  refine ⟨J, t.symm.trans e, ?_⟩
  intro g x
  have ht : t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x) =
      cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x) := by
    apply t.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := cyclicBoundaryOrbitKernelEquiv_equivariant p K n g (t.symm x)
    change t (cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x)) =
      cyclicBoundaryOrbitKernelRepresentation p K n g (t (t.symm x)) at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  change e (t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x)) = _
  rw [ht]
  exact he g (t.symm x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicTopCoordinate.lean -/
section


section

/-! # The genuine fixed top-face quotient and its polynomial section

On the barycentric ring the quotient kills every proper face variable and
retains the top face.  On the polynomial side the section substitutes the
product of all vertex variables.  The orbit retraction is a left inverse of
this section, and its parameter action matches the source quotient exactly.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

def booleanTopPolynomialEvaluation : MvPolynomial (BooleanFace V) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun F => if F = booleanTopFace then Polynomial.X else 0)

theorem booleanTopPolynomialEvaluation_forbidden
    (a : BooleanFace V →₀ ℕ) (ha : ¬IsChainExponent a) :
    booleanTopPolynomialEvaluation (K := K) (MvPolynomial.monomial a 1) = 0 := by
  have hx : ∃ F ∈ a.support, F ≠ booleanTopFace := by
    by_contra hn
    apply ha
    intro F hF G hG
    have hFt : F = booleanTopFace := by
      by_contra h
      exact hn ⟨F, hF, h⟩
    have hGt : G = booleanTopFace := by
      by_contra h
      exact hn ⟨G, hG, h⟩
    exact Or.inl (by rw [hFt, hGt])
  obtain ⟨F, hF, hFt⟩ := hx
  rw [booleanTopPolynomialEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul]
  apply Finset.prod_eq_zero hF
  change (if F = booleanTopFace then Polynomial.X else (0 : K[X])) ^ a F = 0
  rw [if_neg hFt, zero_pow (Finsupp.mem_support_iff.mp hF)]

def booleanTopEvaluation : BooleanBarycentricRing V K →ₐ[K] K[X] :=
  Ideal.Quotient.liftₐ (forbiddenIdeal IsChainExponent) booleanTopPolynomialEvaluation (by
    have hi : forbiddenIdeal (K := K) (IsChainExponent (V := V)) ≤
        RingHom.ker booleanTopPolynomialEvaluation.toRingHom := by
      rw [forbiddenIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact booleanTopPolynomialEvaluation_forbidden a ha
    exact fun f hf => hi hf)

@[simp] theorem booleanTopEvaluation_face (F : BooleanFace V) :
    booleanTopEvaluation (K := K) (faceVariable F) =
      if F = booleanTopFace then Polynomial.X else 0 := by
  change booleanTopPolynomialEvaluation (MvPolynomial.X F) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem booleanTopEvaluation_top :
    booleanTopEvaluation (V := V) (K := K) booleanTop = Polynomial.X := by
  simp [booleanTop]

theorem booleanTopEvaluation_rankParameter (r : ℕ) :
    booleanTopEvaluation (V := V) (K := K) (booleanRankParameter r) =
      if r = Fintype.card V then Polynomial.X else 0 := by
  rw [booleanRankParameter, map_sum]
  rw [Finset.sum_eq_single (booleanTopFace (V := V))]
  · by_cases h : r = Fintype.card V <;> simp [h, eq_comm]
  · intro F hF hFt
    by_cases hcard : F.val.card = r <;> simp [hcard, hFt]
  · intro h
    exact (h (Finset.mem_univ _)).elim

def topParameterMap : MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun c => if c.val + 1 = Fintype.card V then Polynomial.X else 0)

theorem booleanTopEvaluation_colorMap :
    (booleanTopEvaluation (V := V) (K := K)).comp booleanColorMap = topParameterMap := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [AlgHom.comp_apply, booleanColorMap, topParameterMap, MvPolynomial.aeval_X]
  rw [← booleanRankParameter_color, booleanTopEvaluation_rankParameter]

theorem booleanTopEvaluation_parameter_mul
    (a : MvPolynomial (Fin (Fintype.card V)) K) (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanColorMap a * x) =
      topParameterMap a * booleanTopEvaluation x := by
  rw [map_mul]
  exact congrArg (fun y : K[X] => y * booleanTopEvaluation x)
    (DFunLike.congr_fun booleanTopEvaluation_colorMap a)

theorem orderingDescentFace_ne_top
    (σ : VertexOrdering (Fintype.card V) V) (c : Fin (Fintype.card V))
    (hc : c ∈ orderingDescents σ) : orderingFace σ c ≠ booleanTopFace := by
  intro he
  have hh := congrArg (fun F : BooleanFace V => F.val.card) he
  change (orderingPrefix σ c).card = (Finset.univ : Finset V).card at hh
  rw [card_orderingPrefix, Finset.card_univ] at hh
  obtain ⟨hlt, _⟩ := (mem_orderingDescents σ c).mp hc
  omega

theorem booleanTopEvaluation_descentVector
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanTopEvaluation (K := K) (descentVector σ) =
      if orderingDescents σ = ∅ then 1 else 0 := by
  by_cases hσ : orderingDescents σ = ∅
  · simp [descentVector, hσ]
  · rw [if_neg hσ, descentVector, map_prod]
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hσ
    apply Finset.prod_eq_zero hc
    rw [booleanTopEvaluation_face, if_neg (orderingDescentFace_ne_top σ c hc)]

end Boolean

section Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

def cyclicTopEmbedding : K[X] →ₐ[K] MvPolynomial (ZMod p) K :=
  Polynomial.aeval (cyclicPolynomialTop p K)

theorem primeOrbitRetraction_top_pow (n : ℕ) :
    primeOrbitRetraction p (cyclicPolynomialTop p K ^ n) = (Polynomial.X : K[X]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', cyclicPolynomialTop_orbitRetraction, ih, pow_succ']

theorem primeOrbitRetraction_topEmbedding (f : K[X]) :
    primeOrbitRetraction p (cyclicTopEmbedding p K f) = f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n c =>
      rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
        primeOrbitRetraction_top_pow, Algebra.smul_def]
      exact Polynomial.C_mul_X_pow_eq_monomial

theorem cyclicTopEmbedding_boundary (f : K[X]) :
    polynomialBooleanBoundaryMap (cyclicTopEmbedding p K f) =
      algebraMap K (PolynomialBoundaryRing (ZMod p) K) (f.coeff 0) := by
  have ht : polynomialBooleanBoundaryMap (cyclicPolynomialTop p K) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    exact ⟨1, mul_one _⟩
  have he : (polynomialBooleanBoundaryMap (V := ZMod p) (K := K)).comp
      (cyclicTopEmbedding p K) = Polynomial.aeval 0 := by
    apply Polynomial.algHom_ext
    simpa [cyclicTopEmbedding] using ht
  have hh := DFunLike.congr_fun he f
  exact hh.trans (Polynomial.coeff_zero_eq_aeval_zero' f).symm

theorem primeOrbitRetraction_parameterLinear :
    IsParameterLinear (polynomialColorMap (V := ZMod p) (K := K))
      (topParameterMap (V := ZMod p) (K := K)) (primeOrbitRetraction p) := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c f
  simp only [polynomialColorMap, topParameterMap, MvPolynomial.aeval_X, ZMod.card]
  by_cases hc : c.val + 1 = p
  · rw [if_pos hc, hc]
    exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f
  · rw [if_neg hc, zero_mul]
    apply primeOrbitRetraction_lower_parameter p (Fact.out : p.Prime) (ZMod.card p)
    · omega
    · have hb : c.val < p := c.isLt.trans_eq (ZMod.card p)
      omega

end Polynomial
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanAction.lean -/
section


section

/-! # Actual Boolean vertex-permutation actions

The action is the existing restriction functor along the inverse vertex
permutation.  The generator formula identifies it with literal relabeling of
faces.  Parameter linearity, ordinary grading, and the fixed top quotient are
proved for this action.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def booleanPermutationAlgEquiv (e : Equiv.Perm V) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing V K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.apply_symm_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanPermutationAlgEquiv_face (e : Equiv.Perm V) (F : BooleanFace V) :
    booleanPermutationAlgEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

@[simp] theorem booleanPermutationAlgEquiv_one (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (1 : Equiv.Perm V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanPermutationAlgEquiv_mul (e f : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (e * f) x =
      booleanPermutationAlgEquiv e (booleanPermutationAlgEquiv f x) := by
  have he : (e * f).symm.toEmbedding = e.symm.toEmbedding.trans f.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e * f).symm.toEmbedding x =
    booleanRestriction e.symm.toEmbedding (booleanRestriction f.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    e.symm.toEmbedding f.symm.toEmbedding) x).symm

theorem booleanPermutationAlgEquiv_parameter (e : Equiv.Perm V) (r : ℕ) :
    booleanPermutationAlgEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

theorem booleanPermutationAlgEquiv_colorMap (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    booleanPermutationAlgEquiv e (booleanColorMap a) = booleanColorMap a := by
  have he : (booleanPermutationAlgEquiv (K := K) e).toAlgHom.comp booleanColorMap =
      booleanColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, booleanColorMap, MvPolynomial.aeval_X]
    rw [← booleanRankParameter_color]
    exact booleanPermutationAlgEquiv_parameter e (c.val + 1)
  exact DFunLike.congr_fun he a

/-- The genuine permutation action is linear over the prescribed rank-sum
parameter algebra, not merely over the coefficient field. -/
def booleanParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (BooleanBarycentricRing V K) where
  toFun e := {
    toFun := booleanPermutationAlgEquiv e
    map_add' := (booleanPermutationAlgEquiv e).map_add
    map_smul' := by
      intro a x
      change booleanPermutationAlgEquiv e (booleanColorMap a * x) =
        booleanColorMap a * booleanPermutationAlgEquiv e x
      rw [map_mul, booleanPermutationAlgEquiv_colorMap] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_one x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_mul e f x

theorem chainOrdinaryDegree_map_faceEmbedding (e : V ↪ V)
    (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = chainOrdinaryDegree a := by
  unfold chainOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanPermutationAlgEquiv_degree (e : Equiv.Perm V) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) :
    booleanPermutationAlgEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by
  intro a ha
  change booleanChainBasis.repr (booleanRestriction e.symm.toEmbedding x) a = 0
  rw [booleanRestriction_coefficient]
  apply hx
  change chainOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e.symm.toEmbedding)) ≠ n
  rw [chainOrdinaryDegree_map_faceEmbedding]
  exact ha

theorem booleanAlgHom_ext {S : Type*} [CommRing S] [Algebra K S]
    (f g : BooleanBarycentricRing V K →ₐ[K] S)
    (h : ∀ F, f (faceVariable F) = g (faceVariable F)) : f = g := by
  have he : f.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) =
      g.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) := by
    apply MvPolynomial.algHom_ext
    exact h
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he a

variable [Nonempty V]

theorem booleanFaceEmbedding_equiv_top (e : Equiv.Perm V) :
    booleanFaceEmbedding e.toEmbedding (booleanTopFace (V := V)) = booleanTopFace := by
  apply Subtype.ext
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  exact Finset.mem_map.mpr ⟨e.symm v, Finset.mem_univ _, e.apply_symm_apply v⟩

theorem booleanTopEvaluation_permutation (e : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanPermutationAlgEquiv e x) = booleanTopEvaluation x := by
  have he : (booleanTopEvaluation (V := V) (K := K)).comp
      (booleanPermutationAlgEquiv e).toAlgHom = booleanTopEvaluation := by
    apply booleanAlgHom_ext
    intro F
    change booleanTopEvaluation (booleanPermutationAlgEquiv e (faceVariable F)) =
      booleanTopEvaluation (faceVariable F)
    rw [booleanPermutationAlgEquiv_face, booleanTopEvaluation_face, booleanTopEvaluation_face]
    have ht : booleanFaceEmbedding e.toEmbedding F = booleanTopFace ↔ F = booleanTopFace := by
      constructor
      · intro h
        exact (booleanFaceEmbedding e.toEmbedding).injective
          (h.trans (booleanFaceEmbedding_equiv_top e).symm)
      · rintro rfl
        exact booleanFaceEmbedding_equiv_top e
    simp only [ht]
  exact DFunLike.congr_fun he x

end General

section Graded

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem booleanParameterPermutationRepresentation_graded (e : Equiv.Perm V)
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n) :
    booleanParameterPermutationRepresentation e x ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx ⊢
  exact booleanPermutationAlgEquiv_degree e n x hx

end Graded
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrdinaryLift.lean -/
section


section

/-! # A normalized ordinary lift to both prescribed quotients

Starting with any graded, normalized parameter-linear boundary lift, correct
the images of the actual descent basis by the top-coordinate section.  The
correction has zero boundary and gives exact compatibility with the fixed
top-face quotient.  No equivariance is assumed at this stage.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped Polynomial

section DegreeFacts

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem descentOrdinaryDegree_eq_zero_iff
    (σ : VertexOrdering (Fintype.card V) V) :
    colorOrdinaryDegree (descentColorExponent σ) = 0 ↔ orderingDescents σ = ∅ := by
  rw [colorOrdinaryDegree_eq_zero_iff]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hh := congrArg (fun a : ColorExponent V => a c) h
    simp only [descentColorExponent_apply, if_pos hc, Finsupp.zero_apply] at hh
    exact Nat.one_ne_zero hh
  · intro h
    simp [descentColorExponent, h]

theorem weightOrdering_zero_no_descents :
    orderingDescents (weightOrdering (fun _ : V => 0)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, hh⟩ := weightOrdering_descent_lt (fun _ : V => 0)
    ((mem_orderingDescents _ _).mp hc)
  exact (Nat.lt_irrefl 0) hh

theorem parameterLinear_ordinary_degree
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : f x ∈ polynomialDegreePiece n := by
  rw [← booleanChainBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : chainOrdinaryDegree a.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (hx a hn)
  rw [← hdeg]
  exact parameterLinear_chain_degree f hf hd a

end DegreeFacts

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicTopEmbedding_monomial_degree (m : ℕ) (c : K) :
    cyclicTopEmbedding p K (Polynomial.monomial m c) ∈
      CyclicPolynomialPiece p K (m * p) := by
  rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  exact polynomialDegreePiece_pow p (cyclicPolynomialTop p K)
    (cyclicPolynomialTop_degree p K) m

theorem cyclicTopEmbedding_orbitRetraction_degree (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicTopEmbedding p K (primeOrbitRetraction p f.val) ∈ CyclicPolynomialPiece p K n := by
  change cyclicTopEmbedding p K (cyclicHomogeneousOrbitRetraction p K n f) ∈ _
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hn : p ∣ n
  · rw [if_pos hn]
    have hh := cyclicTopEmbedding_monomial_degree p K (n / p)
      (cyclicHomogeneousAugmentation p K n f)
    simpa only [Nat.div_mul_cancel hn] using hh
  · rw [if_neg hn, map_zero]
    exact Submodule.zero_mem _

theorem cyclicHomogeneousOrbitRetraction_constant_zero (n : ℕ) (hn : 0 < n)
    (f : CyclicPolynomialPiece p K n) :
    (primeOrbitRetraction p f.val).coeff 0 = 0 := by
  change (cyclicHomogeneousOrbitRetraction p K n f).coeff 0 = 0
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hd : p ∣ n
  · rw [if_pos hd, Polynomial.coeff_monomial]
    have hq : n / p ≠ 0 := by
      intro hzero
      have hh := Nat.div_mul_cancel hd
      rw [hzero, zero_mul] at hh
      omega
    rw [if_neg hq]
  · rw [if_neg hd]
    rfl

def cyclicOrdinaryCorrectedLift
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  exact ((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).restrictScalars K

@[simp] theorem cyclicOrdinaryCorrectedLift_descent
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) =
      f (descentVector σ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  simpa only [cyclicOrdinaryCorrectedLift, LinearMap.restrictScalars_apply,
    booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := K)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (fun τ => f (descentVector τ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector τ) - primeOrbitRetraction p (f (descentVector τ)))) σ

theorem cyclicOrdinaryCorrectedLift_parameterLinear
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    IsParameterLinear booleanColorMap polynomialColorMap (cyclicOrdinaryCorrectedLift p K f) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  intro a x
  exact (((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).map_smul a x)

theorem cyclicOrdinaryCorrectedLift_orbitRetraction
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (x : BooleanBarycentricRing (ZMod p) K) :
    primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f x) = booleanTopEvaluation x := by
  have he : (primeOrbitRetraction p).comp (cyclicOrdinaryCorrectedLift p K f) =
      (booleanTopEvaluation (V := ZMod p) (K := K)).toLinearMap := by
    apply parameterLinear_ext_descent (topParameterMap (V := ZMod p) (K := K))
    · intro a y
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear,
        primeOrbitRetraction_parameterLinear]
      rfl
    · exact booleanTopEvaluation_parameter_mul
    · intro σ
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, primeOrbitRetraction_topEmbedding]
      rw [← add_sub_assoc,
        add_comm (primeOrbitRetraction p (f (descentVector σ)))
          (booleanTopEvaluation (descentVector σ)), add_sub_cancel_right]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_one
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (h1 : f 1 = 1) : cyclicOrdinaryCorrectedLift p K f 1 = 1 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  rw [← hd, cyclicOrdinaryCorrectedLift_descent, hd, h1,
    map_one, primeOrbitRetraction_one, sub_self, map_zero, add_zero]

theorem cyclicOrdinaryCorrectedLift_boundary
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (h1 : f 1 = 1)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (x : BooleanBarycentricRing (ZMod p) K) :
    polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f x) =
      polynomialBooleanBoundaryMap (f x) := by
  have he : polynomialBooleanBoundaryMap.toLinearMap.comp (cyclicOrdinaryCorrectedLift p K f) =
      polynomialBooleanBoundaryMap.toLinearMap.comp f := by
    apply parameterLinear_ext_descent (polynomialBoundaryColorMap (V := ZMod p) (K := K))
    · intro a y
      change polynomialBooleanBoundaryMap
        (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro a y
      change polynomialBooleanBoundaryMap (f (booleanColorMap a * y)) = _
      rw [hf, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro σ
      change polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, cyclicTopEmbedding_boundary]
      have hc : (booleanTopEvaluation (descentVector σ) -
          primeOrbitRetraction p (f (descentVector σ))).coeff 0 = 0 := by
        by_cases hσ : orderingDescents σ = ∅
        · have hh : descentVector (K := K) σ = 1 := by simp [descentVector, hσ]
          rw [hh, h1, map_one, primeOrbitRetraction_one, sub_self]
          rfl
        · rw [Polynomial.coeff_sub, booleanTopEvaluation_descentVector, if_neg hσ]
          have hn : 0 < colorOrdinaryDegree (descentColorExponent σ) :=
            Nat.pos_of_ne_zero (fun h => hσ ((descentOrdinaryDegree_eq_zero_iff σ).mp h))
          rw [cyclicHomogeneousOrbitRetraction_constant_zero p K _ hn
            ⟨f (descentVector σ), hd σ⟩]
          simp
      rw [hc, map_zero, add_zero]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_descent_degree
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [cyclicOrdinaryCorrectedLift_descent, map_sub]
  apply Submodule.add_mem _ (hd σ)
  apply Submodule.sub_mem
  · rw [booleanTopEvaluation_descentVector]
    by_cases hσ : orderingDescents σ = ∅
    · rw [if_pos hσ, map_one, (descentOrdinaryDegree_eq_zero_iff σ).mpr hσ]
      exact polynomialDegreePiece_one
    · rw [if_neg hσ, map_zero]
      exact Submodule.zero_mem _
  · exact cyclicTopEmbedding_orbitRetraction_degree p K _ ⟨f (descentVector σ), hd σ⟩

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicParameterModules.lean -/
section


section

/-! # Parameter modules and the actual controlled quotient

The scoped polynomial module structure is evaluation at elementary symmetric
polynomials.  The controlled submodule is the intersection of the genuine
boundary kernel and the orbit-retraction kernel.  The quotient and all group
actions are induced from these actual maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial

namespace CyclicParameterAction

scoped instance (priority := 2000) polynomialAlgebra {V K : Type*} [Fintype V] [CommRing K] :
    Algebra (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra

scoped instance (priority := 2000) polynomialSMul {V K : Type*} [Fintype V] [CommRing K] :
    SMul (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toSMul _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance (priority := 2000) polynomialModule {V K : Type*} [Fintype V] [CommRing K] :
    Module (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toModule _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance polynomialTower {V K : Type*} [Fintype V] [CommRing K] :
    IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))

end CyclicParameterAction

open scoped CyclicParameterAction

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem polynomialColorMap_rename (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    MvPolynomial.rename e (polynomialColorMap a) = polynomialColorMap a := by
  have he : (MvPolynomial.rename e).comp (polynomialColorMap (V := V) (K := K)) =
      polynomialColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, polynomialColorMap, MvPolynomial.aeval_X,
      MvPolynomial.rename_esymm]
  exact DFunLike.congr_fun he a

def polynomialParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (MvPolynomial V K) where
  toFun e := {
    toFun := MvPolynomial.rename e
    map_add' := (MvPolynomial.rename e).map_add
    map_smul' := by
      intro a x
      change MvPolynomial.rename e (polynomialColorMap a * x) =
        polynomialColorMap a * MvPolynomial.rename e x
      rw [map_mul, polynomialColorMap_rename] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact MvPolynomial.rename_id_apply x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    change MvPolynomial.rename (e * f) x = MvPolynomial.rename e (MvPolynomial.rename f x)
    rw [MvPolynomial.rename_rename]
    rfl

def parameterLinearMap
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f) :
    BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

end General

section QuotientAction

variable {A G N : Type*} [CommRing A] [Group G] [AddCommGroup N] [Module A N]

def invariantQuotientRepresentation (ρ : CyclicRepresentation A G N)
    (H : Submodule A N) (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    CyclicRepresentation A G (N ⧸ H) where
  toFun g := H.mapQ H (ρ g) (fun x hx => hH g x hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ 1 y) = H.mkQ y
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ (g * h) y) = H.mkQ (ρ g (ρ h y))
    rw [ρ.map_mul]
    rfl

@[simp] theorem invariantQuotientRepresentation_mk
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) (g : G) (x : N) :
    invariantQuotientRepresentation ρ H hH g (H.mkQ x) = H.mkQ (ρ g x) := rfl

theorem invariantQuotientRepresentation_mk_intertwines
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    RepresentationIntertwines ρ (invariantQuotientRepresentation ρ H hH) H.mkQ := by
  intro g x
  rfl

end QuotientAction

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

def cyclicVertexPermutation : PrimeCycleGroup p →* Equiv.Perm (ZMod p) where
  toFun g := Equiv.addLeft g.toAdd
  map_one' := by ext v; exact zero_add v
  map_mul' g h := by ext v; exact add_assoc g.toAdd h.toAdd v

def cyclicPolynomialParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (MvPolynomial (ZMod p) K) :=
  polynomialParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

def cyclicBooleanParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (BooleanBarycentricRing (ZMod p) K) :=
  booleanParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

@[simp] theorem cyclicPolynomialParameterRepresentation_apply
    (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K) :
    cyclicPolynomialParameterRepresentation p K g f =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f := rfl

@[simp] theorem cyclicBooleanParameterRepresentation_apply
    (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K) :
    cyclicBooleanParameterRepresentation p K g x =
      booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x := rfl

def cyclicControlledKernel :
    Submodule (MvPolynomial (Fin (Fintype.card (ZMod p))) K) (MvPolynomial (ZMod p) K) where
  carrier := {f | polynomialBooleanBoundaryMap f = 0 ∧ primeOrbitRetraction p f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · rw [map_add, hf.1, hg.1, add_zero]
    · rw [map_add, hf.2, hg.2, add_zero]
  smul_mem' := by
    intro a f hf
    change polynomialBooleanBoundaryMap (polynomialColorMap a * f) = 0 ∧
      primeOrbitRetraction p (polynomialColorMap a * f) = 0
    constructor
    · rw [polynomialBooleanBoundaryMap_parameter_mul, hf.1, mul_zero]
    · rw [primeOrbitRetraction_parameterLinear, hf.2, mul_zero]

theorem cyclicControlledKernel_invariant :
    ∀ (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K),
      f ∈ cyclicControlledKernel p K →
        cyclicPolynomialParameterRepresentation p K g f ∈ cyclicControlledKernel p K := by
  intro g f hf
  constructor
  · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f).mp hf.1
    change cyclicPolynomialTop p K * x = f at hx
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  · rw [cyclicPolynomialParameterRepresentation_apply, primeOrbitRetraction_rename]
    exact hf.2

abbrev CyclicControlledQuotient :=
  MvPolynomial (ZMod p) K ⧸ cyclicControlledKernel p K

def cyclicControlledQuotientRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (CyclicControlledQuotient p K) :=
  invariantQuotientRepresentation (cyclicPolynomialParameterRepresentation p K)
    (cyclicControlledKernel p K) (cyclicControlledKernel_invariant p K)

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicModularLift.lean -/
section


section

/-! # The prime-cyclic controlled lift for actual face rings

This is the exceptional modular construction in the positive direction of
Theorem 1.3.  Every source, action, quotient, and kernel is the one already
defined on the actual Boolean barycentric and polynomial rings.  The sole
input is an ordinary graded normalized boundary lift whose boundary values
are equivariant; equivariance of the full lift is constructed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (f : MvPolynomial (ZMod p) K),
      f ∈ CyclicPolynomialPiece p K n →
        cyclicPolynomialParameterRepresentation p K g f ∈ CyclicPolynomialPiece p K n := by
  intro g n f hf
  exact (cyclicPolynomialRepresentation p K n g ⟨f, hf⟩).property

theorem cyclicBooleanParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (x : BooleanBarycentricRing (ZMod p) K),
      x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        cyclicBooleanParameterRepresentation p K g x ∈
          (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n := by
  intro g n x hx
  exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx

theorem cyclicControlledQuotient_intertwines :
    RepresentationIntertwines (cyclicPolynomialParameterRepresentation p K)
      (cyclicControlledQuotientRepresentation p K) (cyclicControlledKernel p K).mkQ := by
  intro g x
  rfl

def cyclicControlledDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] CyclicControlledQuotient p K :=
  ((cyclicControlledKernel p K).mkQ.restrictScalars K).comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicControlledDegreeKernel_eq (n : ℕ) :
    LinearMap.ker (cyclicControlledDegreeMap p K n) =
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  ext f
  change (cyclicControlledKernel p K).mkQ f.val = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (cyclicBoundaryOrbitDegree_mem_kernel p K n f).symm

def cyclicControlledDegreeKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicControlledDegreeMap p K n)) :=
  ScalarGradedBasis.kernelDegreeRepresentation
    (cyclicPolynomialParameterRepresentation p K) (cyclicControlledQuotientRepresentation p K)
    (CyclicPolynomialPiece p K) (cyclicControlledKernel p K).mkQ
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K) n

theorem cyclicControlledDegreeKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicControlledDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicBoundaryOrbitKernel_isCoinduced p K n
  let t := LinearEquiv.ofEq _ _ (cyclicControlledDegreeKernel_eq p K n)
  have ht : RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelRepresentation p K n) t.toLinearMap := by
    intro g x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  refine ⟨J, t.trans e, ?_⟩
  intro g x
  change e (t (cyclicControlledDegreeKernelRepresentation p K n g x)) =
    coinducedRepresentation (K := K) (C := J → K) g (e (t x))
  exact (congrArg e (ht g x)).trans (he g (t x))

theorem cyclicBoundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) K)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * x = f - g at hx
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename e x = MvPolynomial.rename e (f - g)
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem booleanScalarGradedBasis_one :
    (1 : BooleanBarycentricRing (ZMod p) K) ∈
      (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece 0 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : orderingDescents σ = ∅ := weightOrdering_zero_no_descents
  have hdegree : colorOrdinaryDegree (descentColorExponent σ) = 0 :=
    (descentOrdinaryDegree_eq_zero_iff σ).mpr hd
  have h := (booleanScalarGradedBasis (V := ZMod p) (K := K)).generator_mem_piece σ
  simpa only [booleanScalarGradedBasis, booleanColorBasis_apply, descentVector, hd,
    Finset.prod_empty, hdegree] using h

/-- A full parameter-linear prime-cyclic lift with the prescribed actual
boundary, fixed quotient, ordinary grading, and normalization. -/
theorem exists_primeCyclic_boundary_lift
    (f₀ : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf₀ : IsParameterLinear booleanColorMap polynomialColorMap f₀)
    (h₁ : f₀ 1 = 1)
    (hd₀ : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f₀ (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hb₀ : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K),
      polynomialBooleanBoundaryMap (f₀ (cyclicBooleanParameterRepresentation p K g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p K g (f₀ x))) :
    ∃ F : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K,
      IsParameterLinear booleanColorMap polynomialColorMap F ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        F x ∈ CyclicPolynomialPiece p K n) ∧
      F 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x)) ∧
      (∀ x, primeOrbitRetraction p (F x) = booleanTopEvaluation x) ∧
      (∀ g x, F (cyclicBooleanParameterRepresentation p K g x) =
        cyclicPolynomialParameterRepresentation p K g (F x)) := by
  let s := booleanScalarGradedBasis (V := ZMod p) (K := K)
  let ρ := cyclicBooleanParameterRepresentation p K
  let τ := cyclicPolynomialParameterRepresentation p K
  let υ := cyclicControlledQuotientRepresentation p K
  let H := cyclicControlledKernel p K
  let T := CyclicPolynomialPiece p K
  let f := cyclicOrdinaryCorrectedLift p K f₀
  have hf : IsParameterLinear booleanColorMap polynomialColorMap f :=
    cyclicOrdinaryCorrectedLift_parameterLinear p K f₀
  have hfone : f 1 = 1 := cyclicOrdinaryCorrectedLift_one p K f₀ h₁
  have hfboundary (x) : polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (f₀ x) :=
    cyclicOrdinaryCorrectedLift_boundary p K f₀ hf₀ h₁ hd₀ x
  have hfE (x) : primeOrbitRetraction p (f x) = booleanTopEvaluation x :=
    cyclicOrdinaryCorrectedLift_orbitRetraction p K f₀ x
  have hfgrade : ∀ n x, x ∈ s.piece n → f x ∈ T n := by
    intro n x hx
    rw [booleanScalarGradedBasis_piece_eq] at hx
    exact parameterLinear_ordinary_degree f hf
      (cyclicOrdinaryCorrectedLift_descent_degree p K f₀ hd₀) n x hx
  let fA := parameterLinearMap f hf
  let a := H.mkQ.comp fA
  have ha : RepresentationIntertwines ρ υ a := by
    intro g x
    change H.mkQ (f (ρ g x)) = H.mkQ (τ g (f x))
    apply (Submodule.Quotient.eq H).mpr
    constructor
    · change polynomialBooleanBoundaryMap (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfboundary, hb₀]
      apply sub_eq_zero.mpr
      exact (cyclicBoundary_rename_congr p K (Equiv.addLeft g.toAdd) (f x) (f₀ x)
        (hfboundary x)).symm
    · change primeOrbitRetraction p (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfE, cyclicPolynomialParameterRepresentation_apply,
        primeOrbitRetraction_rename, hfE]
      change booleanTopEvaluation (booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x) -
        booleanTopEvaluation x = 0
      rw [booleanTopEvaluation_permutation, sub_self]
  let β : ∀ n, s.piece n →ₗ[K] T n := fun n =>
    LinearMap.codRestrict (T n) (f.comp (s.piece n).subtype)
      (fun x => hfgrade n x.val x.property)
  have hqβ : ∀ n, (ScalarGradedBasis.degreeQuotient T H.mkQ n).comp (β n) =
      s.degreeTarget a n := by intro n; rfl
  choose J e he using cyclicControlledDegreeKernel_isCoinduced p K
  let C : ℕ → Type _ := fun n => J n → K
  letI : ∀ n, AddCommGroup (C n) := fun _ => inferInstance
  letI : ∀ n, Module K (C n) := fun _ => inferInstance
  have hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j) := by
    intro j y hy
    change polynomialColorMap (MvPolynomial.monomial j.2 1) * y ∈
      polynomialDegreePiece (colorOrdinaryDegree j.2 + colorOrdinaryDegree (descentColorExponent j.1))
    exact polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree j.2) hy
  obtain ⟨F, hFgrade, hFq, hFeq⟩ := s.exists_equivariantGradedLift_of_ordinary_lifts
    ρ τ υ T H.mkQ a (cyclicBooleanParameterRepresentation_graded p K)
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K)
    hmult ha C β hqβ e he
  have hdiff (x : BooleanBarycentricRing (ZMod p) K) : F x - f x ∈ H := by
    apply (Submodule.Quotient.eq H).mp
    exact congrArg (fun L : BooleanBarycentricRing (ZMod p) K →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) K] CyclicControlledQuotient p K => L x) hFq
  have hFboundary (x) : polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x) := by
    have hh := (hdiff x).1
    change polynomialBooleanBoundaryMap (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfboundary x)
  have hFE (x) : primeOrbitRetraction p (F x) = booleanTopEvaluation x := by
    have hh := (hdiff x).2
    change primeOrbitRetraction p (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfE x)
  have hFone : F 1 = 1 := by
    have hd : F 1 - 1 ∈ T 0 := (T 0).sub_mem
      (hFgrade 0 1 (booleanScalarGradedBasis_one p K)) polynomialDegreePiece_one
    have hk : (⟨F 1 - 1, hd⟩ : CyclicPolynomialPiece p K 0) ∈
        LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K 0) := by
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K 0 _).mpr
      have hh := hdiff 1
      change polynomialBooleanBoundaryMap (F 1 - f 1) = 0 ∧
        primeOrbitRetraction p (F 1 - f 1) = 0 at hh
      simpa only [hfone] using hh
    have hz := cyclicBoundaryOrbitKernel_zero_below p K 0 (Fact.out : p.Prime).pos ⟨⟨F 1 - 1, hd⟩, hk⟩
    exact sub_eq_zero.mp (congrArg (fun z => z.val.val) hz)
  refine ⟨F.restrictScalars K, ?_, hFgrade, hFone, hFboundary, hFE, hFeq⟩
  intro b x
  exact F.map_smul b x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedIsomorphism.lean -/
section


section

/-! # A graded boundary lift is an isomorphism

The proof uses a finite triangular argument on the actual parameter basis.
A homogeneous element divisible by the positive-degree top parameter belongs
to the span of strictly lower-degree parameter generators.  Thus two graded
parameter lifts with the same boundary differ by a strictly triangular map
after conjugating by either known lift.  The coefficient ring is arbitrary.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Abstract

variable {K A M I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem ScalarGradedBasis.bijective_of_lower_cut_errors
    (s : ScalarGradedBasis K A M I J) (f : M →ₗ[A] M)
    (hf : ∀ i, f (s.parameterBasis i) - s.parameterBasis i ∈ s.cut (s.generatorDegree i)) :
    Function.Bijective f := by
  have hcoeff (i j : I) (hij : s.generatorDegree i ≤ s.generatorDegree j) :
      s.parameterBasis.repr (f (s.parameterBasis i) - s.parameterBasis i) j = 0 := by
    by_contra hn
    have hs := (s.parameterBasis.mem_span_image).mp (hf i)
    have hj := hs (Finsupp.mem_support_iff.mpr hn)
    exact (Nat.not_lt_of_ge hij) hj
  apply canonicalLeading_bijective s.parameterBasis s.parameterBasis s.generatorDegree f
  constructor
  · intro i
    have hh := hcoeff i i le_rfl
    simpa only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, sub_eq_zero] using hh
  · intro i j hne hij
    have hh := hcoeff i j hij
    simpa [Finsupp.single_apply, hne, Ne.symm hne] using hh

end Abstract

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

theorem chainOrdinaryDegree_add (a b : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + b) = chainOrdinaryDegree a + chainOrdinaryDegree b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])

theorem chainOrdinaryDegree_add_top (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      chainOrdinaryDegree a + Fintype.card V := by
  rw [chainOrdinaryDegree_add]
  simp [chainOrdinaryDegree, booleanTopFace]

theorem booleanTop_mul_shift_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem booleanTop_predecessor_degree (m : ℕ) (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) (m + Fintype.card V)) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ m + Fintype.card V := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  change booleanChainBasis.repr (booleanTop * x) b = 0 at hh
  change booleanChainBasis.repr x a = 0
  rwa [booleanTop_mul_shift_coefficient] at hh

theorem booleanTop_homogeneous_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ n := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    omega
  have hh := hx b hb
  change booleanChainBasis.repr (booleanTop * x) b = 0 at hh
  rw [booleanTop_mul_shift_coefficient] at hh
  exact hh

theorem booleanTop_mul_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n) :
    booleanTop * x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  let c : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hc : c.val + 1 = Fintype.card V := by dsimp [c]; omega
  have ht : booleanTop * x = (MvPolynomial.X c : MvPolynomial (Fin (Fintype.card V)) K) • x := by
    change booleanTop * x = booleanColorMap (MvPolynomial.X c) * x
    rw [booleanColorMap, MvPolynomial.aeval_X, ← booleanRankParameter_color, hc,
      booleanRankParameter_top]
  rw [ht]
  exact ((booleanScalarGradedBasis (V := V) (K := K)).cut n).smul_mem _ hx

/-- A genuine top-boundary kernel element of degree `n` uses only parameter
generators of degree strictly below `n`. -/
theorem booleanBoundary_homogeneous_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : booleanBoundaryMap x = 0) :
    x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hb
  rw [booleanScalarGradedBasis_piece_eq] at hx
  have htop : booleanTop * y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by simpa only [hy] using hx
  by_cases hn : Fintype.card V ≤ n
  · have hydeg : y ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece
        (n - Fintype.card V) := by
      rw [booleanScalarGradedBasis_piece_eq]
      apply booleanTop_predecessor_degree
      simpa only [Nat.sub_add_cancel hn] using htop
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    have hlt : n - Fintype.card V < n := by omega
    rw [← hy]
    exact booleanTop_mul_mem_cut n y
      ((booleanScalarGradedBasis (V := V) (K := K)).homogeneous_mem_cut hlt y hydeg)
  · have hyzero := booleanTop_homogeneous_zero_below n (Nat.lt_of_not_ge hn) y htop
    rw [← hy, hyzero, mul_zero]
    exact Submodule.zero_mem _

theorem booleanParameterEnd_bijective_of_graded_boundary_identity
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K)
    (hd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : ∀ x, booleanBoundaryMap (f x) = booleanBoundaryMap x) :
    Function.Bijective f := by
  let s := booleanScalarGradedBasis (V := V) (K := K)
  apply s.bijective_of_lower_cut_errors f
  intro i
  apply booleanBoundary_homogeneous_mem_cut
  · exact (s.piece (s.generatorDegree i)).sub_mem
      (hd _ _ (s.generator_mem_piece i)) (s.generator_mem_piece i)
  · rw [map_sub, hb, sub_self]

/-- Any graded parameter-linear lift of the same actual boundary is an
isomorphism once one graded parameter comparison is known. -/
theorem parameterLift_bijective_of_same_boundary
    (e : ParameterEquiv (booleanColorMap (V := V) (K := K)) polynomialColorMap)
    (b : LocalBoundaryComparison (V := V) (K := K))
    (he : ∀ x, polynomialBooleanBoundaryMap (e.toLinearEquiv x) =
      b.toLinearEquiv (booleanBoundaryMap x))
    (hed : ∀ n y, y ∈ polynomialDegreePiece n → e.toLinearEquiv.symm y ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ polynomialDegreePiece n)
    (hfb : ∀ x, polynomialBooleanBoundaryMap (f x) =
      polynomialBooleanBoundaryMap (e.toLinearEquiv x)) : Function.Bijective f := by
  let T : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K :=
    e.overParameters.symm.toLinearMap.comp (parameterLinearMap f hf)
  have hT : Function.Bijective T := by
    apply booleanParameterEnd_bijective_of_graded_boundary_identity T
    · intro n x hx
      exact hed n (f x) (hfd n x hx)
    · intro x
      apply b.toLinearEquiv.injective
      rw [← he, ← he]
      change polynomialBooleanBoundaryMap (e.toLinearEquiv (e.toLinearEquiv.symm (f x))) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hfb x
  have hcomp : (fun x => e.toLinearEquiv (T x)) = f := by
    funext x
    exact e.toLinearEquiv.apply_symm_apply (f x)
  rw [← hcomp]
  exact e.toLinearEquiv.bijective.comp hT

end Boolean
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryIsomorphism.lean -/
section

section
/-! # Positive-degree boundary lifting without a previously known isomorphism

This is the graded lifting argument of Lemma 2.1.  The boundary comparison
is an actual isomorphism of the two top-parameter quotients.  Strong induction
on ordinary degree proves injectivity and surjectivity of any graded lift
commuting with the top parameters.  It neither compares the lift with an
already invertible map nor assumes a prescribed leading coefficient matrix.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section GradedLinearAlgebra

variable {K M N I J : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem ordinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  change b.repr (b i) j = 0
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp [Module.Basis.repr_self, Finsupp.single_apply, h]

theorem ordinaryProjection_mem_piece (b : Module.Basis I K M) (w : I → ℕ)
    (n : ℕ) (x : M) :
    basisDegreeProjection b w n x ∈ basisOrdinaryDegreePiece b w n := by
  intro i hi
  change b.repr (basisDegreeProjection b w n x) i = 0
  rw [basisDegreeProjection_repr, if_neg hi]

theorem ordinaryProjection_natural (b : Module.Basis I K M) (c : Module.Basis J K N)
    (w : I → ℕ) (v : J → ℕ) (f : M →ₗ[K] N)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n) (n : ℕ) (x : M) :
    basisDegreeProjection c v n (f x) = f (basisDegreeProjection b w n x) := by
  have he : (basisDegreeProjection c v n).comp f = f.comp (basisDegreeProjection b w n) := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, basisDegreeProjection_basis]
    by_cases hi : w i = n
    · rw [if_pos hi]
      exact (basisDegreeProjection_eq_self_iff_mem c v n (f (b i))).mpr
        (hf n (b i) (hi ▸ ordinaryBasis_mem_piece b w i))
    · rw [if_neg hi, map_zero]
      apply c.repr.injective
      ext j
      rw [basisDegreeProjection_repr, map_zero, Finsupp.zero_apply]
      by_cases hj : v j = n
      · rw [if_pos hj]
        exact hf (w i) (b i) (ordinaryBasis_mem_piece b w i) j
          (fun h => hi (h.symm.trans hj))
      · rw [if_neg hj]
  exact LinearMap.congr_fun he x

variable {Q R : Type*} [AddCommGroup Q] [Module K Q]
  [AddCommGroup R] [Module K R]

/-- A degree-preserving top-parameter lift of an actual boundary isomorphism
is bijective.  All kernel and predecessor hypotheses refer to the given maps
and the given basis degrees; they do not assert any isomorphism of the lifts. -/
theorem gradedBoundaryLift_bijective
    (b : Module.Basis I K M) (c : Module.Basis J K N) (w : I → ℕ) (v : J → ℕ)
    (qM : M →ₗ[K] Q) (qN : N →ₗ[K] R) (boundary : Q ≃ₗ[K] R)
    (σ : M →ₗ[K] M) (τ : N →ₗ[K] N) (r : ℕ) (hr : 0 < r)
    (hτ : Function.Injective τ)
    (hkerM : ∀ x, qM x = 0 → ∃ a, σ a = x)
    (hkerN : ∀ y, qN y = 0 → ∃ a, τ a = y)
    (hσpred : ∀ n a, r ≤ n → σ a ∈ basisOrdinaryDegreePiece b w n →
      a ∈ basisOrdinaryDegreePiece b w (n - r))
    (hτpred : ∀ n a, r ≤ n → τ a ∈ basisOrdinaryDegreePiece c v n →
      a ∈ basisOrdinaryDegreePiece c v (n - r))
    (hσbelow : ∀ n a, n < r → σ a ∈ basisOrdinaryDegreePiece b w n → a = 0)
    (hτbelow : ∀ n a, n < r → τ a ∈ basisOrdinaryDegreePiece c v n → a = 0)
    (hboundary : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n →
      ∃ x, x ∈ basisOrdinaryDegreePiece b w n ∧ qN y = boundary (qM x))
    (f : M →ₗ[K] N)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n)
    (htop : ∀ x, f (σ x) = τ (f x))
    (hquot : ∀ x, qN (f x) = boundary (qM x)) : Function.Bijective f := by
  have hinj : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n → f x = 0 → x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx hfx
        have hqx : qM x = 0 := by
          apply boundary.injective
          rw [← hquot, hfx, map_zero, map_zero]
        obtain ⟨a, ha⟩ := hkerM x hqx
        have hσa : σ a ∈ basisOrdinaryDegreePiece b w n := ha.symm ▸ hx
        by_cases hrn : r ≤ n
        · have hfa : f a = 0 := by
            apply hτ
            rw [← htop, ha, hfx, map_zero]
          have ha0 := ih (n - r) (by omega) a (hσpred n a hrn hσa) hfa
          rw [← ha, ha0, map_zero]
        · have ha0 := hσbelow n a (Nat.lt_of_not_ge hrn) hσa
          rw [← ha, ha0, map_zero]
  have hsurj : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n → ∃ x, f x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hy
        obtain ⟨x, hx, hbx⟩ := hboundary n y hy
        have hqdiff : qN (y - f x) = 0 := by rw [map_sub, hquot, hbx, sub_self]
        obtain ⟨a, ha⟩ := hkerN (y - f x) hqdiff
        have hτa : τ a ∈ basisOrdinaryDegreePiece c v n :=
          ha.symm ▸ (basisOrdinaryDegreePiece c v n).sub_mem hy (hgrade n x hx)
        by_cases hrn : r ≤ n
        · obtain ⟨z, hz⟩ := ih (n - r) (by omega) a (hτpred n a hrn hτa)
          refine ⟨x + σ z, ?_⟩
          rw [map_add, htop, hz, ha]
          abel
        · have ha0 := hτbelow n a (Nat.lt_of_not_ge hrn) hτa
          refine ⟨x, ?_⟩
          have hh : y - f x = 0 := by rw [← ha, ha0, map_zero]
          exact (sub_eq_zero.mp hh).symm
  have hzero : ∀ x, f x = 0 → x = 0 := by
    intro x hfx
    apply b.repr.injective
    ext i
    have hh : basisDegreeProjection b w (w i) x = 0 := by
      apply hinj (w i) _ (ordinaryProjection_mem_piece b w (w i) x)
      rw [← ordinaryProjection_natural b c w v f hgrade, hfx, map_zero]
    have hc := congrArg (fun z => b.repr z i) hh
    simpa only [basisDegreeProjection_repr, if_true, map_zero, Finsupp.zero_apply] using hc
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro y
    choose a ha using fun j : J => hsurj (v j) (c j) (ordinaryBasis_mem_piece c v j)
    refine ⟨∑ j ∈ (c.repr y).support, c.repr y j • a j, ?_⟩
    simp only [map_sum, map_smul, ha]
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using c.linearCombination_repr y

end GradedLinearAlgebra

section BooleanBoundary

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

/-- The actual degree piece in the Boolean top-parameter quotient. -/
def booleanBoundaryOrdinaryPiece (n : ℕ) : Submodule K (BooleanBoundaryRing V K) :=
  (basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) n).map
    booleanBoundaryMap.toLinearMap

/-- The actual degree piece in the polynomial top-monomial quotient. -/
def polynomialBoundaryOrdinaryPiece (n : ℕ) : Submodule K (PolynomialBoundaryRing V K) :=
  (polynomialDegreePiece n).map polynomialBooleanBoundaryMap.toLinearMap

theorem polynomialOrdinaryPiece_eq_basis (n : ℕ) :
    polynomialDegreePiece (V := V) (K := K) n =
      basisOrdinaryDegreePiece (MvPolynomial.basisMonomials V K)
        (fun a => vertexDegree (fun v => a v)) n := by
  ext x
  rfl

theorem fullPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial V K)
    (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece (m + Fintype.card V)) :
    f ∈ polynomialDegreePiece m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent V + a) v) =
      Fintype.card V + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent V v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by rw [hdeg]; omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem fullPolynomialTop_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (f : MvPolynomial V K) (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece n) : f = 0 := by
  ext a
  have hdeg : Fintype.card V ≤ vertexDegree (fun v => (fullExponent V + a) v) := by
    change Fintype.card V ≤ vertexDegree ((fun v => fullExponent V v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem parameterLinear_top
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (x : BooleanBarycentricRing V K) :
    f (booleanTop * x) = (∏ v : V, X v) * f x := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hc : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have h := parameterLinear_intertwinesAllRanks f hf (Fintype.card V - 1) x
  have htop : MvPolynomial.esymm V K (Fintype.card V) = ∏ v : V, X v := by
    unfold MvPolynomial.esymm
    rw [← Finset.card_univ, Finset.powersetCard_self]
    simp
  simpa only [hc, booleanRankParameter_top, htop] using h

/-- Lemma 2.1 on the actual simplex rings.  The inverse boundary map is
assumed graded in the genuine quotient grading, as it is for any graded
boundary isomorphism.  No isomorphism of the full rings is assumed. -/
theorem booleanPolynomialLift_bijective_of_graded_boundary
    (boundary : LocalBoundaryComparison (V := V) (K := K))
    (hbgrade : ∀ n y, y ∈ polynomialBoundaryOrdinaryPiece (V := V) (K := K) n →
      boundary.toLinearEquiv.symm y ∈ booleanBoundaryOrdinaryPiece (V := V) (K := K) n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hquot : ∀ x, polynomialBooleanBoundaryMap (f x) =
      boundary.toLinearEquiv (booleanBoundaryMap x)) : Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis (MvPolynomial.basisMonomials V K)
    (fun a => chainOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    booleanBoundaryMap.toLinearMap polynomialBooleanBoundaryMap.toLinearMap boundary.toLinearEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (∏ v : V, X v)) (Fintype.card V)
    (Fintype.card_pos_iff.mpr inferInstance)
    (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset V)).left
    (fun x hx => (booleanBoundaryMap_eq_zero_iff x).mp hx)
    (fun y hy => (polynomialBooleanBoundaryMap_eq_zero_iff y).mp hy)
    (fun n a hn ha => booleanTop_predecessor_degree (n - Fintype.card V) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card V) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => booleanTop_homogeneous_zero_below n hn a ha)
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by rwa [← polynomialOrdinaryPiece_eq_basis] at ha))
    ?_ f ?_ (parameterLinear_top f hf) hquot
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    have hb := hbgrade n (polynomialBooleanBoundaryMap y) ⟨y, hy', rfl⟩
    obtain ⟨x, hx, he⟩ := hb
    refine ⟨x, hx, ?_⟩
    change polynomialBooleanBoundaryMap y =
      boundary.toLinearEquiv (booleanBoundaryMap x)
    have hh := congrArg boundary.toLinearEquiv he
    simpa only [LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using hh.symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx

end BooleanBoundary
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralHom.lean -/
section


section

/-! # Integral affine correction on parameter-linear maps

Conjugation gives an honest representation on the module of parameter-linear
maps.  The integral correction is therefore applied to the actual maps, not
to independently averaged values on a chosen basis.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable {A G M N : Type*} [CommRing A] [Group G]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def parameterHomRepresentation (ρ : CyclicRepresentation A G M)
    (τ : CyclicRepresentation A G N) : CyclicRepresentation ℤ G (M →ₗ[A] N) where
  toFun g := {
    toFun f := (τ g).comp (f.comp (ρ g⁻¹))
    map_add' := by intro f h; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    change τ (g * h) (f (ρ (g * h)⁻¹ x)) =
      τ g (τ h (f (ρ h⁻¹ (ρ g⁻¹ x))))
    rw [mul_inv_rev, ρ.map_mul, τ.map_mul]
    rfl

@[simp] theorem parameterHomRepresentation_apply
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (g : G) (f : M →ₗ[A] N) (x : M) :
    parameterHomRepresentation ρ τ g f x = τ g (f (ρ g⁻¹ x)) := rfl

theorem parameterHomRepresentation_fixed_iff
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) :
    (∀ g, parameterHomRepresentation ρ τ g f = f) ↔ RepresentationIntertwines ρ τ f := by
  constructor
  · intro h g x
    have hh := congrArg (fun F : M →ₗ[A] N => F (ρ g x)) (h g)
    have hinv : ρ g⁻¹ (ρ g x) = x := by
      change (ρ g⁻¹ * ρ g) x = x
      rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
      rfl
    change τ g (f (ρ g⁻¹ (ρ g x))) = f (ρ g x) at hh
    rw [hinv] at hh
    exact hh.symm
  · intro h g
    ext x
    change τ g (f (ρ g⁻¹ x)) = f x
    rw [h]
    change (τ g * τ g⁻¹) (f x) = f x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl

variable [Fintype G]

theorem parameterHom_nsmul_injective
    (hN : Function.Injective (fun y : N => Fintype.card G • y)) :
    Function.Injective (fun f : M →ₗ[A] N => Fintype.card G • f) := by
  intro f h he
  ext x
  apply hN
  exact congrArg (fun F : M →ₗ[A] N => F x) he

/-- Lemma A.8 applied to actual parameter-linear maps, with exact preservation
of a boundary map and any separately specified homogeneous submodules. -/
theorem exists_integralEquivariant_map_correction
    {Q : Type*} [AddCommGroup Q] (q : N →ₗ[ℤ] Q)
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) (v : G → M →ₗ[A] N)
    (hN : Function.Injective (fun y : N => Fintype.card G • y))
    (hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card G • v g)
    (hqv : ∀ g x, q (v g x) = 0)
    (S : ℕ → Submodule ℤ M) (T : ℕ → Submodule ℤ N)
    (hfgrade : ∀ n x, x ∈ S n → f x ∈ T n)
    (hvgrade : ∀ g n x, x ∈ S n → v g x ∈ T n)
    (x₀ : M) (hv₀ : ∀ g, v g x₀ = 0) :
    ∃ F : M →ₗ[A] N,
      RepresentationIntertwines ρ τ F ∧
      (∀ x, q (F x) = q (f x)) ∧
      (∀ n x, x ∈ S n → F x ∈ T n) ∧ F x₀ = f x₀ := by
  let F : M →ₗ[A] N := f + ∑ g, v g
  have hfixed : ∀ g, parameterHomRepresentation ρ τ g F = F :=
    affineCorrection_fixed (parameterHomRepresentation ρ τ) f v
      (parameterHom_nsmul_injective hN) hv
  refine ⟨F, (parameterHomRepresentation_fixed_iff ρ τ F).mp hfixed, ?_, ?_, ?_⟩
  · intro x
    change q (f x + (∑ g, v g) x) = q (f x)
    simp [hqv]
  · intro n x hx
    change f x + (∑ g, v g) x ∈ T n
    apply (T n).add_mem (hfgrade n x hx)
    rw [LinearMap.sum_apply]
    exact (T n).sum_mem (fun g _ => hvgrade g n x hx)
  · change f x₀ + (∑ g, v g) x₀ = f x₀
    simp [hv₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegerCoefficients.lean -/
section


section

/-! # Exact integer coefficient lifting and division

The integer-to-modular steps are coefficientwise identities in the actual
multivariate polynomial rings.  Homogeneous lifts retain the original
exponent vectors; division is used only after divisibility has been proved.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {V : Type*}

def liftZModPolynomial (p : ℕ) (f : MvPolynomial V (ZMod p)) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ZMod p => (c.val : ℤ)) (by simp) f.coeff)

@[simp] theorem liftZModPolynomial_coeff (p : ℕ) (f : MvPolynomial V (ZMod p))
    (a : V →₀ ℕ) :
    (liftZModPolynomial p f).coeff a = ((f.coeff a).val : ℤ) := rfl

theorem liftZModPolynomial_map (p : ℕ) [NeZero p] (f : MvPolynomial V (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (liftZModPolynomial p f) = f := by
  ext a
  rw [MvPolynomial.coeff_map, liftZModPolynomial_coeff]
  change (((f.coeff a).val : ℤ) : ZMod p) = f.coeff a
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ℤ => c / (p : ℤ)) (by simp) f.coeff)

@[simp] theorem divideIntegerPolynomial_coeff (p : ℕ) (f : MvPolynomial V ℤ)
    (a : V →₀ ℕ) :
    (divideIntegerPolynomial p f).coeff a = f.coeff a / (p : ℤ) := rfl

theorem nsmul_divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ)
    (hf : MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0) :
    p • divideIntegerPolynomial p f = f := by
  ext a
  have hc := congrArg (fun h : MvPolynomial V (ZMod p) => h.coeff a) hf
  rw [MvPolynomial.coeff_map] at hc
  change (f.coeff a : ZMod p) = 0 at hc
  have hd : (p : ℤ) ∣ f.coeff a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc
  rw [MvPolynomial.coeff_smul, divideIntegerPolynomial_coeff, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_of_dvd hd

theorem integerPolynomial_nsmul_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun f : MvPolynomial V ℤ => p • f) := by
  intro f g hfg
  ext a
  have h := congrArg (fun h : MvPolynomial V ℤ => h.coeff a) hfg
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, nsmul_eq_mul, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (by exact_mod_cast hp) h

variable [Fintype V] [LinearOrder V]

theorem liftZModPolynomial_degree (p n : ℕ) (f : MvPolynomial V (ZMod p))
    (hf : f ∈ polynomialDegreePiece n) :
    liftZModPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [liftZModPolynomial_coeff, hf a ha]
  simp

theorem divideIntegerPolynomial_degree (p n : ℕ) (f : MvPolynomial V ℤ)
    (hf : f ∈ polynomialDegreePiece n) :
    divideIntegerPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [divideIntegerPolynomial_coeff, hf a ha]
  simp

theorem integerPolynomial_degree_of_nsmul {p n : ℕ} (hp : p ≠ 0)
    (f : MvPolynomial V ℤ) (hf : p • f ∈ polynomialDegreePiece n) :
    f ∈ polynomialDegreePiece n := by
  intro a ha
  have hh := hf a ha
  rw [MvPolynomial.coeff_smul, nsmul_eq_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hp)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicParameterBaseChange.lean -/
section


section

/-! # Coefficient change of actual parameter-linear maps

Extension is defined by the images of the already verified descent basis.
The comparison with coefficient change is proved on the complete scalar
parameter basis, including every parameter monomial.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V K L : Type*} [Fintype V] [LinearOrder V] [CommRing K] [CommRing L]

theorem booleanCoefficientChange_descent (h : K →+* L)
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanCoefficientChange h (descentVector (K := K) σ) = descentVector (K := L) σ := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (descentVector (K := K) σ) = _
  rw [descentVector, descentVector, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  exact booleanCoefficientChange_face h (orderingFace σ c)

theorem booleanCoefficientChange_color (h : K →+* L) (c : Fin (Fintype.card V)) :
    booleanCoefficientChange h (colorSum (K := K) c) = colorSum (K := L) c := by
  rw [← booleanRankParameter_color, booleanCoefficientChange_parameter, booleanRankParameter_color]

theorem booleanCoefficientChange_colorPower (h : K →+* L) (m : ColorExponent V) :
    booleanCoefficientChange h (colorPower (K := K) m) = colorPower (K := L) m := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (colorPower (K := K) m) = _
  rw [colorPower, colorPower, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  rw [map_pow]
  congr 1
  exact booleanCoefficientChange_color h c

theorem booleanCoefficientChange_parameterBasis (h : K →+* L)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    booleanCoefficientChange h (booleanParameterBasis (K := K) i) =
      booleanParameterBasis (K := L) i := by
  rw [booleanParameterBasis_apply, booleanParameterBasis_apply, parameterDescentVector,
    parameterDescentVector, booleanCoefficientChange_mul,
    booleanCoefficientChange_colorPower, booleanCoefficientChange_descent]

theorem polynomialCoefficientChange_parameterMonomial (h : K →+* L) (m : ColorExponent V) :
    polynomialCoefficientChange h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) =
      polynomialColorMap (K := L) (MvPolynomial.monomial m 1) := by
  change MvPolynomial.map h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) = _
  simp only [polynomialColorMap, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod, map_prod, map_pow, MvPolynomial.map_esymm]

theorem polynomialCoefficientChange_degree (h : K →+* L) (n : ℕ)
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece n) :
    polynomialCoefficientChange h f ∈ polynomialDegreePiece n := by
  intro a ha
  change (MvPolynomial.map h f).coeff a = 0
  rw [MvPolynomial.coeff_map, hf a ha, map_zero]

theorem parameterLinearMap_parameterDescent
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    f (parameterDescentVector i) =
      polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1) := by
  rw [parameterDescentVector_eq_monomial_smul, map_smul]
  rfl

def extendIntegralParameterMap (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V L →ₗ[MvPolynomial (Fin (Fintype.card V)) L] MvPolynomial V L :=
  (booleanColorBasis (V := V) (K := L)).constr (MvPolynomial (Fin (Fintype.card V)) L)
    (fun σ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)))

@[simp] theorem extendIntegralParameterMap_descent (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) =
      polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)) := by
  simpa only [extendIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := L)).constr_basis (MvPolynomial (Fin (Fintype.card V)) L)
      (fun τ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector τ))) σ

theorem extendIntegralParameterMap_commutes (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (x : BooleanBarycentricRing V ℤ) :
    extendIntegralParameterMap L f (booleanCoefficientChange (Int.castRingHom L) x) =
      polynomialCoefficientChange (Int.castRingHom L) (f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanCoefficientChange (Int.castRingHom L)) =
      (polynomialCoefficientChange (Int.castRingHom L)).comp (f.restrictScalars ℤ) := by
    apply (booleanParameterBasis (V := V) (K := ℤ)).ext
    intro i
    change extendIntegralParameterMap L f
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis i)) =
      polynomialCoefficientChange (Int.castRingHom L) (f (booleanParameterBasis i))
    rw [booleanCoefficientChange_parameterBasis, booleanParameterBasis_apply,
      booleanParameterBasis_apply, parameterLinearMap_parameterDescent,
      parameterLinearMap_parameterDescent, extendIntegralParameterMap_descent]
    change _ = MvPolynomial.map (Int.castRingHom L)
      (polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1))
    rw [map_mul]
    rw [← polynomialCoefficientChange_eq, polynomialCoefficientChange_parameterMonomial]
    rfl
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_degree (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [extendIntegralParameterMap_descent]
  exact polynomialCoefficientChange_degree _ _ _ (hf σ)

theorem extendIntegralParameterMap_one (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) :
    extendIntegralParameterMap L f 1 = MvPolynomial.C (m : L) := by
  have h := extendIntegralParameterMap_commutes L f 1
  have h₁ : booleanCoefficientChange (V := V) (Int.castRingHom L) 1 = 1 :=
    (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed (Int.castRingHom L)).map_one
  rw [h₁, hf] at h
  simpa [polynomialCoefficientChange_eq] using h

theorem extendIntegralParameterMap_permutation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V)
    (hf : ∀ x, f (booleanPermutationAlgEquiv e x) = MvPolynomial.rename e (f x)) :
    ∀ x, extendIntegralParameterMap L f (booleanPermutationAlgEquiv e x) =
      MvPolynomial.rename e (extendIntegralParameterMap L f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanPermutationAlgEquiv (K := L) e).toLinearMap =
      (MvPolynomial.rename e).toLinearMap.comp ((extendIntegralParameterMap L f).restrictScalars L) := by
    apply (booleanParameterBasis (V := V) (K := L)).ext
    intro i
    have hBi := booleanCoefficientChange_parameterBasis (Int.castRingHom L) i
    change extendIntegralParameterMap L f (booleanPermutationAlgEquiv e (booleanParameterBasis i)) =
      MvPolynomial.rename e (extendIntegralParameterMap L f (booleanParameterBasis i))
    rw [← hBi]
    have hn := booleanCoefficientChange_restriction (Int.castRingHom L) e.symm.toEmbedding
      (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom L)
        (booleanPermutationAlgEquiv e (booleanParameterBasis (K := ℤ) i)) =
      booleanPermutationAlgEquiv e
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis (K := ℤ) i)) at hn
    rw [← hn, extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes, hf]
    exact MvPolynomial.map_rename (Int.castRingHom L) e _
  intro x
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_conjugation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V) (x : BooleanBarycentricRing V ℤ) :
    polynomialCoefficientChange (Int.castRingHom L)
        (MvPolynomial.rename e (f (booleanPermutationAlgEquiv e.symm x))) =
      MvPolynomial.rename e (extendIntegralParameterMap L f
        (booleanPermutationAlgEquiv e.symm (booleanCoefficientChange (Int.castRingHom L) x))) := by
  rw [polynomialCoefficientChange_eq, MvPolynomial.map_rename]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  exact congrArg (fun y => MvPolynomial.rename e (extendIntegralParameterMap L f y))
    (booleanCoefficientChange_restriction (Int.castRingHom L) e.toEmbedding x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralDivision.lean -/
section


section

/-! # Dividing integral parameter maps after modular vanishing

Division is performed on the genuine descent-basis images.  The resulting
map is parameter-linear by construction, and the multiplication identity is
checked on that full parameter basis.  Boundary and grading conditions then
descend using torsion freeness of the actual coefficient bases.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Basis

variable {I M : Type*} [AddCommGroup M] [Module ℤ M]

theorem integerBasis_nsmul_injective (b : Module.Basis I ℤ M) {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun x : M => p • x) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  have hh := congrArg (fun z => b.repr z i) hxy
  simp only [map_nsmul, Finsupp.nsmul_apply, nsmul_eq_mul] at hh
  exact mul_left_cancel₀ (by exact_mod_cast hp) hh

end Basis

variable {V : Type*} [Fintype V] [LinearOrder V]

def divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ :=
  (booleanColorBasis (V := V) (K := ℤ)).constr (MvPolynomial (Fin (Fintype.card V)) ℤ)
    (fun σ => divideIntegerPolynomial p (f (descentVector σ)))

@[simp] theorem divideIntegralParameterMap_descent (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) = divideIntegerPolynomial p (f (descentVector σ)) := by
  simpa only [divideIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := ℤ)).constr_basis (MvPolynomial (Fin (Fintype.card V)) ℤ)
      (fun τ => divideIntegerPolynomial p (f (descentVector τ))) σ

theorem nsmul_divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0) :
    p • divideIntegralParameterMap p f = f := by
  apply (booleanColorBasis (V := V) (K := ℤ)).ext
  intro σ
  simp only [booleanColorBasis_apply, LinearMap.smul_apply, divideIntegralParameterMap_descent]
  exact nsmul_divideIntegerPolynomial p _ (hf σ)

theorem divideIntegralParameterMap_degree (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [divideIntegralParameterMap_descent]
  exact divideIntegerPolynomial_degree p _ _ (hf σ)

theorem divideIntegralParameterMap_boundary (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (hb : ∀ x, polynomialBooleanBoundaryMap (f x) = 0)
    (x : BooleanBarycentricRing V ℤ) :
    polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) = 0 := by
  apply integerBasis_nsmul_injective
    (standardMonomialBasis (K := ℤ) (OmitsVertex V) (omitsVertex_divisorClosed V)) hp
  change p • polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) =
    p • (0 : PolynomialBoundaryRing V ℤ)
  rw [smul_zero, ← map_nsmul]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  change p • divideIntegralParameterMap p f x = f x at hh
  rw [hh, hb]

theorem divideIntegralParameterMap_zero_at (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (x : BooleanBarycentricRing V ℤ) (hx : f x = 0) :
    divideIntegralParameterMap p f x = 0 := by
  apply integerPolynomial_nsmul_injective hp
  change p • divideIntegralParameterMap p f x = p • (0 : MvPolynomial V ℤ)
  rw [smul_zero]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  exact hh.trans hx

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralCorrection.lean -/
section


section

/-! # Integral correction of an actual prime-cyclic comparison

The input map already has the prescribed integral boundary.  Its failure of
equivariance vanishes after reduction modulo the prime.  We divide this
failure on the actual descent basis and apply the integral affine correction;
the resulting map retains the boundary, ordinary degree, and normalization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem integralParameterMap_graded
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V ℤ)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := ℤ)).piece n) :
    f x ∈ polynomialDegreePiece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx
  exact parameterLinear_ordinary_degree (f.restrictScalars ℤ)
    (fun a y => f.map_smul a y) hf n x hx

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem primeCycle_card : Fintype.card (PrimeCycleGroup p) = p := by
  simp [PrimeCycleGroup, ZMod.card]

theorem exists_integralPrimeCyclic_correction
    (f : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hfmod : ∀ (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)),
      MvPolynomial.map (Int.castRingHom (ZMod p))
        ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
          (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) :
    ∃ F : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
        MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) F ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        F x ∈ polynomialDegreePiece n) ∧ F 1 = MvPolynomial.C m := by
  let ρ := cyclicBooleanParameterRepresentation p ℤ
  let τ := cyclicPolynomialParameterRepresentation p ℤ
  let s := booleanScalarGradedBasis (V := ZMod p) (K := ℤ)
  let δ := fun g : PrimeCycleGroup p => parameterHomRepresentation ρ τ g f - f
  let v := fun g : PrimeCycleGroup p => divideIntegralParameterMap p (δ g)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfg : ∀ n x, x ∈ s.piece n → f x ∈ polynomialDegreePiece n :=
    integralParameterMap_graded f hfgrade
  have hρg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → ρ g x ∈ s.piece n := by
    intro g n x hx
    exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx
  have hτg : ∀ (g : PrimeCycleGroup p) n y,
      y ∈ polynomialDegreePiece n → τ g y ∈ polynomialDegreePiece n := by
    intro g n y hy
    exact (cyclicPolynomialRepresentation p ℤ n g ⟨y, hy⟩).property
  have hδg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → δ g x ∈ polynomialDegreePiece n := by
    intro g n x hx
    exact (polynomialDegreePiece n).sub_mem (hτg g n _ (hfg n _ (hρg g⁻¹ n x hx)))
      (hfg n x hx)
  have hδb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (δ g x) = 0 := by
    intro g x
    change polynomialBooleanBoundaryMap (τ g (f (ρ g⁻¹ x)) - f x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := hfboundary g (ρ g⁻¹ x)
    have hi : ρ g (ρ g⁻¹ x) = x := by
      change (ρ g * ρ g⁻¹) x = x
      rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
      rfl
    rw [hi] at hh
    exact hh.symm
  have hδ₁ : ∀ g : PrimeCycleGroup p, δ g 1 = 0 := by
    intro g
    change MvPolynomial.rename (Equiv.addLeft g.toAdd)
      (f (booleanPermutationAlgEquiv (Equiv.addLeft (g⁻¹).toAdd) 1)) - f 1 = 0
    rw [map_one, hf₁, MvPolynomial.rename_C, sub_self]
  have hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card (PrimeCycleGroup p) • v g := by
    intro g
    rw [primeCycle_card]
    have hdiv := nsmul_divideIntegralParameterMap p (δ g) (hfmod g)
    change parameterHomRepresentation ρ τ g f = f + p • divideIntegralParameterMap p (δ g)
    rw [hdiv]
    change parameterHomRepresentation ρ τ g f = f + (parameterHomRepresentation ρ τ g f - f)
    rw [← add_sub_assoc, add_comm f (parameterHomRepresentation ρ τ g f), add_sub_cancel_right]
  have hvb : ∀ g x, polynomialBooleanBoundaryMap (v g x) = 0 := by
    intro g x
    exact divideIntegralParameterMap_boundary p hp (δ g) (hfmod g) (hδb g) x
  have hvg : ∀ g n x, x ∈ s.piece n → v g x ∈ polynomialDegreePiece n := by
    intro g
    apply integralParameterMap_graded
    intro σ
    exact divideIntegralParameterMap_degree p (δ g)
      (fun σ => hδg g _ _ (by
        simpa only [s, booleanScalarGradedBasis, booleanColorBasis_apply] using
          s.generator_mem_piece σ)) σ
  have hv₁ : ∀ g, v g 1 = 0 := by
    intro g
    exact divideIntegralParameterMap_zero_at p hp (δ g) (hfmod g) 1 (hδ₁ g)
  obtain ⟨F, hFeq, hFb, hFg, hF₁⟩ := exists_integralEquivariant_map_correction
    polynomialBooleanBoundaryMap.toLinearMap ρ τ f v
    (by simpa only [primeCycle_card] using (integerPolynomial_nsmul_injective (V := ZMod p) hp))
    hv hvb s.piece polynomialDegreePiece hfg hvg 1 hv₁
  exact ⟨F, hFeq, hFb, hFg, hF₁.trans hf₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralLift.lean -/
section


section

/-! # Lifting a modular comparison with its exact integral boundary

A modular difference with zero boundary is a multiple of the actual top
monomial.  Lift its quotient coefficient by coefficient, then multiply by
the integral top monomial.  This keeps the prescribed integral boundary
exact, rather than merely congruent modulo the prime.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

abbrev BooleanParameterMap (V K : Type*) [Fintype V] [LinearOrder V] [CommRing K] :=
  BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialTop_map {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) :
    MvPolynomial.map h (cyclicPolynomialTop p K) = cyclicPolynomialTop p L := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.map_X]

theorem cyclicPolynomialTop_factor_zero_below {K : Type*} [CommRing K]
    (n : ℕ) (hn : n < p) (y : MvPolynomial (ZMod p) K)
    (hy : cyclicPolynomialTop p K * y ∈ polynomialDegreePiece n) : y = 0 := by
  ext a
  have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
    change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hy (fullExponent (ZMod p) + a) (by omega)
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

def modularBoundaryDifference (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  F (descentVector σ) - MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ))

theorem modularBoundaryDifference_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    polynomialBooleanBoundaryMap (modularBoundaryDifference p f F σ) = 0 := by
  unfold modularBoundaryDifference
  rw [map_sub, hb, extendIntegralParameterMap_descent, polynomialCoefficientChange_eq, sub_self]

def modularBoundaryCofactor (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  Classical.choose ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

theorem modularBoundaryCofactor_spec (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      modularBoundaryDifference p f F σ :=
  Classical.choose_spec ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

def liftModularParameterMap (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    BooleanParameterMap (ZMod p) ℤ :=
  (booleanColorBasis (V := ZMod p) (K := ℤ)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ)
    (fun σ => f (descentVector σ) + cyclicPolynomialTop p ℤ *
      liftZModPolynomial p (modularBoundaryCofactor p f F hb σ))

@[simp] theorem liftModularParameterMap_descent (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) =
      f (descentVector σ) + cyclicPolynomialTop p ℤ *
        liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) := by
  simpa only [liftModularParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := ℤ)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ) _ σ

theorem liftModularParameterMap_reduction (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    extendIntegralParameterMap (ZMod p) (liftModularParameterMap p f F hb) = F := by
  apply (booleanColorBasis (V := ZMod p) (K := ZMod p)).ext
  intro σ
  rw [booleanColorBasis_apply, extendIntegralParameterMap_descent,
    polynomialCoefficientChange_eq, liftModularParameterMap_descent,
    map_add, map_mul, cyclicPolynomialTop_map, liftZModPolynomial_map,
    modularBoundaryCofactor_spec, modularBoundaryDifference]
  rw [← add_sub_assoc, add_comm _ (F (descentVector σ)), add_sub_cancel_right]

theorem liftModularParameterMap_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (x : BooleanBarycentricRing (ZMod p) ℤ) :
    polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb x) =
      polynomialBooleanBoundaryMap (f x) := by
  let L := liftModularParameterMap p f F hb
  have he := parameterLinear_ext_descent polynomialBoundaryColorMap
    (polynomialBooleanBoundaryMap.toLinearMap.comp (L.restrictScalars ℤ))
    (polynomialBooleanBoundaryMap.toLinearMap.comp (f.restrictScalars ℤ))
    (fun a y => by
      change polynomialBooleanBoundaryMap (L (a • y)) = _
      rw [L.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (L y))
    (fun a y => by
      change polynomialBooleanBoundaryMap (f (a • y)) = _
      rw [f.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (f y))
    (fun σ => by
      change polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb (descentVector σ)) = _
      rw [liftModularParameterMap_descent, map_add]
      have hz : polynomialBooleanBoundaryMap (cyclicPolynomialTop p ℤ *
          liftZModPolynomial p (modularBoundaryCofactor p f F hb σ)) = 0 :=
        (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr ⟨_, rfl⟩
      rw [hz, add_zero]
      rfl)
  exact DFunLike.congr_fun he x

theorem liftModularParameterMap_degree (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hf : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hF : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  let n := colorOrdinaryDegree (descentColorExponent σ)
  let y := modularBoundaryCofactor p f F hb σ
  have hy : cyclicPolynomialTop p (ZMod p) * y ∈ polynomialDegreePiece n := by
    rw [modularBoundaryCofactor_spec]
    exact (polynomialDegreePiece n).sub_mem (hF σ)
      (polynomialCoefficientChange_degree (Int.castRingHom (ZMod p)) n _ (hf σ))
  rw [liftModularParameterMap_descent]
  apply (polynomialDegreePiece n).add_mem (hf σ)
  by_cases hn : p ≤ n
  · have hygrade : y ∈ polynomialDegreePiece (n - p) := by
      apply cyclicPolynomialTop_predecessor_degree p (ZMod p) (n - p) y
      simpa only [Nat.sub_add_cancel hn] using hy
    have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p ℤ)
      (liftZModPolynomial p y) (cyclicPolynomialTop_degree p ℤ)
      (liftZModPolynomial_degree p (n - p) y hygrade)
    simpa only [Nat.add_sub_of_le hn] using hh
  · have hyzero : y = 0 := cyclicPolynomialTop_factor_zero_below p n (by omega) y hy
    have hlift : liftZModPolynomial p y = 0 := by
      ext a
      rw [liftZModPolynomial_coeff, hyzero]
      simp
    change cyclicPolynomialTop p ℤ * liftZModPolynomial p y ∈ polynomialDegreePiece n
    rw [hlift, mul_zero]
    exact (polynomialDegreePiece n).zero_mem

theorem liftModularParameterMap_one (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) (hF : F 1 = MvPolynomial.C (m : ZMod p)) :
    liftModularParameterMap p f F hb 1 = MvPolynomial.C m := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hσ : descentVector (K := ℤ) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hσ' : descentVector (K := ZMod p) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hδ : modularBoundaryDifference p f F σ = 0 := by
    rw [modularBoundaryDifference, hσ, hσ', hf, hF, MvPolynomial.map_C]
    exact sub_self _
  have hy : modularBoundaryCofactor p f F hb σ = 0 := by
    apply cyclicPolynomialTop_mul_injective p (ZMod p)
    change cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      cyclicPolynomialTop p (ZMod p) * 0
    rw [mul_zero, modularBoundaryCofactor_spec, hδ]
  rw [← hσ, liftModularParameterMap_descent, hσ, hf]
  have hlift : liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) = 0 := by
    ext a
    rw [liftZModPolynomial_coeff, hy]
    simp
  rw [hlift, mul_zero, add_zero]

theorem integralCyclic_conjugation_vanishes_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) (extendIntegralParameterMap (ZMod p) f))
    (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0 := by
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let F := extendIntegralParameterMap (ZMod p) f
  let x := booleanCoefficientChange (Int.castRingHom (ZMod p)) (descentVector (K := ℤ) σ)
  have he : (cyclicVertexPermutation p g).symm = cyclicVertexPermutation p g⁻¹ := by
    exact ((cyclicVertexPermutation p).map_inv g).symm
  change MvPolynomial.map (Int.castRingHom (ZMod p))
    (MvPolynomial.rename (cyclicVertexPermutation p g)
      (f (booleanPermutationAlgEquiv (cyclicVertexPermutation p g⁻¹) (descentVector σ))) -
      f (descentVector σ)) = 0
  rw [map_sub, ← he, ← polynomialCoefficientChange_eq,
    extendIntegralParameterMap_conjugation]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  rw [he]
  change τ g (F (ρ g⁻¹ x)) - F x = 0
  rw [hf]
  have hi : τ g (τ g⁻¹ (F x)) = F x := by
    change (τ g * τ g⁻¹) (F x) = F x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl
  rw [hi, sub_self]

theorem integralCyclic_boundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) ℤ)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p ℤ * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    change cyclicPolynomialTop p ℤ * MvPolynomial.rename e y = MvPolynomial.rename e (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem exists_integralPrimeCyclic_lift_of_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hFgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hFequiv : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) F)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) (hF₁ : F 1 = MvPolynomial.C (m : ZMod p)) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = MvPolynomial.C m := by
  let l := liftModularParameterMap p f F hb
  have hlred : extendIntegralParameterMap (ZMod p) l = F :=
    liftModularParameterMap_reduction p f F hb
  have hlb : ∀ x, polynomialBooleanBoundaryMap (l x) = polynomialBooleanBoundaryMap (f x) :=
    liftModularParameterMap_boundary p f F hb
  have hle : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (l (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (l x)) := by
    intro g x
    rw [hlb, hfboundary]
    exact (integralCyclic_boundary_rename_congr p (Equiv.addLeft g.toAdd) (l x) (f x) (hlb x)).symm
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_correction p l
    (liftModularParameterMap_degree p f F hb hfgrade hFgrade) hle
    (integralCyclic_conjugation_vanishes_modular p l (by rwa [hlred]))
    m (liftModularParameterMap_one p f F hb m hf₁ hF₁)
  exact ⟨L, hLe, fun x => (hLb x).trans (hlb x), hLg, hL₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralPrimeLift.lean -/
section


section

/-! # Integral prime-cyclic boundary lifting

This combines the actual modular controlled lift, exact integral lifting of
its top-monomial corrections, and integral affine averaging.  The conclusion
has no modular lifting, kernel splitting, or torsion-freeness hypotheses:
only an ordinary normalized graded lift of an equivariant boundary is input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicBoundary_coefficient_congr {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) (f g : MvPolynomial (ZMod p) K)
    (he : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.map h f) =
      polynomialBooleanBoundaryMap (MvPolynomial.map h g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.map h (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.map h y, ?_⟩
    change cyclicPolynomialTop p L * MvPolynomial.map h y = MvPolynomial.map h (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_map]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem extendIntegralParameterMap_cyclicBoundary (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x))) :
    ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) (ZMod p)),
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
        (cyclicBooleanParameterRepresentation p (ZMod p) g x)) =
      polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p (ZMod p) g
        (extendIntegralParameterMap (ZMod p) f x)) := by
  intro g
  let F := extendIntegralParameterMap (ZMod p) f
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let q : MvPolynomial (ZMod p) (ZMod p) →ₗ[ZMod p] PolynomialBoundaryRing (ZMod p) (ZMod p) :=
    polynomialBooleanBoundaryMap.toLinearMap
  have he : q.comp ((F.restrictScalars (ZMod p)).comp ((ρ g).restrictScalars (ZMod p))) =
      q.comp (((τ g).restrictScalars (ZMod p)).comp (F.restrictScalars (ZMod p))) := by
    apply (booleanParameterBasis (V := ZMod p) (K := ZMod p)).ext
    intro i
    change polynomialBooleanBoundaryMap (F (ρ g (booleanParameterBasis i))) =
      polynomialBooleanBoundaryMap (τ g (F (booleanParameterBasis i)))
    rw [← booleanCoefficientChange_parameterBasis (Int.castRingHom (ZMod p)) i]
    have hact := booleanCoefficientChange_restriction (Int.castRingHom (ZMod p))
      (cyclicVertexPermutation p g).symm.toEmbedding (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)) =
      ρ g (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (booleanParameterBasis (K := ℤ) i)) at hact
    rw [← hact]
    change polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
      (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)))) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (cyclicVertexPermutation p g)
        (extendIntegralParameterMap (ZMod p) f
          (booleanCoefficientChange (Int.castRingHom (ZMod p)) (booleanParameterBasis (K := ℤ) i))))
    rw [extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes,
      polynomialCoefficientChange_eq, polynomialCoefficientChange_eq,
      ← MvPolynomial.map_rename]
    exact cyclicBoundary_coefficient_congr p (Int.castRingHom (ZMod p)) _ _
      (hf g (booleanParameterBasis i))
  intro x
  exact DFunLike.congr_fun he x

theorem exists_integralPrimeCyclic_boundary_lift
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hf₁ : f 1 = 1) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = 1 := by
  let fbar := extendIntegralParameterMap (ZMod p) f
  have hfb : IsParameterLinear booleanColorMap polynomialColorMap
      (fbar.restrictScalars (ZMod p)) := fun a x => fbar.map_smul a x
  have hfbar₁ : fbar 1 = 1 := by
    simpa only [Int.cast_one, map_one] using
      (extendIntegralParameterMap_one (ZMod p) f 1 (by simpa only [map_one] using hf₁))
  obtain ⟨F, hFp, hFg, hF₁, hFb, hFE, hFe⟩ := exists_primeCyclic_boundary_lift p (ZMod p)
    (fbar.restrictScalars (ZMod p)) hfb hfbar₁
    (extendIntegralParameterMap_degree (ZMod p) f hfgrade)
    (extendIntegralParameterMap_cyclicBoundary p f hfboundary)
  let FA := parameterLinearMap F hFp
  have hFgen : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      FA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    change F (descentVector σ) ∈ polynomialDegreePiece _
    apply hFg
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply] using
      (booleanScalarGradedBasis (V := ZMod p) (K := ZMod p)).generator_mem_piece σ
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_lift_of_modular p f FA hFb
    hfgrade hFgen hfboundary hFe 1
    (by simpa only [map_one] using hf₁)
    (by change F 1 = MvPolynomial.C ((1 : ℤ) : ZMod p);
        simpa only [Int.cast_one, MvPolynomial.C_1] using hF₁)
  exact ⟨L, hLe, hLb, hLg, by simpa only [map_one] using hL₁⟩

end FourPapers.Universal

end
end
end


-- Close only the anonymous source scopes reopened by the next shard.
