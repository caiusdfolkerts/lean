module

public import theorem94.PalomarPart000
import all theorem94.PalomarPart000
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega
public meta import Mathlib.Tactic.Ring.Basic

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


-- Restore the original anonymous enclosing source scopes at this boundary.
section
section
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
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

/-- The literal basis coordinate map, with the coefficient inverse pair explicit. -/
def palomarBasisCoordinates (b : Module.Basis I K M) : M →ₗ[K] (I →₀ K) :=
  @LinearEquiv.toLinearMap K K _ _ (RingHom.id K) (RingHom.id K)
    (PalomarBarycentricRelative.coefficientIdentityInvPair (K := K))
    (PalomarBarycentricRelative.coefficientIdentityInvPair (K := K))
    M (I →₀ K) _ _ _ _ b.repr
/-- The original scalar-closure calculation for the unchanged coefficient predicate. -/
theorem palomarBasisOrdinaryDegreePiece_smul (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) :
    ∀ (c : K) (x : M), (∀ i, degree i ≠ n → (palomarBasisCoordinates b) x i = 0) →
      ∀ i, degree i ≠ n → (palomarBasisCoordinates b) (c • x) i = 0 := by intro c x hx i hi; simp only [map_smul, Finsupp.smul_apply, hx i hi, smul_zero]

def basisOrdinaryDegreePiece (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) : Submodule K M where
  carrier := {x | ∀ i, degree i ≠ n → (palomarBasisCoordinates b) x i = 0}
  zero_mem' := by intro i hi; simp
  add_mem' := by intro x y hx hy i hi; simp only [map_add, Finsupp.add_apply, hx i hi, hy i hi, add_zero]
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

def presentationWeightLevel (w : (V →₀ ℕ) → ℤ) (n : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a, n ≤ w a → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by intro f g hf hg a ha; simp only [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := by intro c f hf a ha; simp only [coeff_smul, hf a ha, smul_zero]

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

/- BEGIN FourPapers/Universal/StalkAutomorphisms.lean -/
section

section
/-! # Actual relabeling of face stalks

An order automorphism sends an actual vertex below `p` to an actual vertex
below its image.  The two stalk maps are variable renaming in the polynomial
ring and restriction along the inverse vertex bijection in the Boolean
face ring.  Their compatibility with restriction, rank parameters, and
ordinary degree is proved for these maps.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section VertexRelabeling
variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def booleanVertexRelabelEquiv (e : V ≃ W) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing W K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
        ext v
        exact e.apply_symm_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanVertexRelabelEquiv_refl (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (Equiv.refl V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanVertexRelabelEquiv_trans (e : V ≃ W) (f : W ≃ U)
    (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (e.trans f) x =
      booleanVertexRelabelEquiv f (booleanVertexRelabelEquiv e x) := by
  have he : (e.trans f).symm.toEmbedding = f.symm.toEmbedding.trans e.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e.trans f).symm.toEmbedding x =
    booleanRestriction f.symm.toEmbedding (booleanRestriction e.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    f.symm.toEmbedding e.symm.toEmbedding) x).symm

@[simp] theorem booleanVertexRelabelEquiv_parameter (e : V ≃ W) (r : ℕ) :
    booleanVertexRelabelEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

@[simp] theorem booleanVertexRelabelEquiv_face (e : V ≃ W) (F : BooleanFace V) :
    booleanVertexRelabelEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

theorem vertexDegree_finsupp_sum (a : V →₀ ℕ) :
    vertexDegree (fun v => a v) = a.sum (fun _ n => n) :=
  (Finsupp.sum_fintype a (fun _ n => n) (fun _ => rfl)).symm

theorem vertexDegree_mapDomain (f : V → W) (a : V →₀ ℕ) :
    vertexDegree (fun w => a.mapDomain f w) = vertexDegree (fun v => a v) := by
  rw [vertexDegree_finsupp_sum, vertexDegree_finsupp_sum,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem polynomialRename_degree (f : V → W) (n : ℕ)
    (x : MvPolynomial V K) (hx : x ∈ polynomialDegreePiece n) :
    MvPolynomial.rename f x ∈ polynomialDegreePiece n := by
  intro a ha
  apply MvPolynomial.coeff_rename_eq_zero f x a
  intro b hb
  apply hx b
  intro hd
  apply ha
  rw [← hb, vertexDegree_mapDomain, hd]

/-- The same rank-weighted ordinary degree as `chainOrdinaryDegree`, with no
auxiliary ordering of the vertex type required in its interface. -/
def booleanOrdinaryDegree [DecidableEq V] (a : BooleanFace V →₀ ℕ) : ℕ :=
  a.sum (fun F n => n * F.val.card)

theorem booleanOrdinaryDegree_eq_chainOrdinaryDegree [LinearOrder V]
    (a : BooleanFace V →₀ ℕ) : booleanOrdinaryDegree a = chainOrdinaryDegree a := rfl

theorem chainOrdinaryDegree_map_vertexEmbedding [DecidableEq V] [DecidableEq W] (e : V ↪ W)
    (a : BooleanFace V →₀ ℕ) :
    booleanOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = booleanOrdinaryDegree a := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanRestriction_degree (e : V ↪ W) (n : ℕ)
    (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanRestriction e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  change booleanChainBasis.repr (booleanRestriction e x) a = 0
  rw [booleanRestriction_coefficient]
  apply hx
  change booleanOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e)) ≠ n
  rwa [chainOrdinaryDegree_map_vertexEmbedding]

theorem booleanVertexRelabelEquiv_degree (e : V ≃ W) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanVertexRelabelEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanRestriction_degree e.symm.toEmbedding n x hx

end VertexRelabeling

section Stalks
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

def faceVertexOrderEquiv (e : P ≃o P) (p : P) : FaceVertex p ≃ FaceVertex (e p) where
  toFun a := ⟨e a.val, (e.isAtom_iff a.val).mpr a.property.1, e.monotone a.property.2⟩
  invFun a := ⟨e.symm a.val, (e.symm.isAtom_iff a.val).mpr a.property.1,
    by simpa only [e.symm_apply_apply] using e.symm.monotone a.property.2⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)

@[simp] theorem faceVertexOrderEquiv_apply (e : P ≃o P) (p : P) (a : FaceVertex p) :
    (faceVertexOrderEquiv e p a).val = e a.val := rfl

@[simp] theorem faceVertexOrderEquiv_symm_apply (e : P ≃o P) (p : P)
    (a : FaceVertex (e p)) : ((faceVertexOrderEquiv e p).symm a).val = e.symm a.val := rfl

@[simp] theorem faceVertexOrderEquiv_refl (p : P) :
    faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl _ := by
  ext a
  rfl

theorem faceVertexOrderEquiv_trans (e f : P ≃o P) (p : P) :
    faceVertexOrderEquiv (e.trans f) p =
      (faceVertexOrderEquiv e p).trans (faceVertexOrderEquiv f (e p)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_inclusion (e : P ≃o P) {p q : P} (h : q ≤ p) :
    (faceVertexInclusion h).trans (faceVertexOrderEquiv e p).toEmbedding =
      (faceVertexOrderEquiv e q).toEmbedding.trans (faceVertexInclusion (e.monotone h)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_card (e : P ≃o P) (p : P) :
    Fintype.card (FaceVertex p) = Fintype.card (FaceVertex (e p)) :=
  Fintype.card_congr (faceVertexOrderEquiv e p)

variable (K : Type*) [CommRing K]

def polynomialStalkOrderEquiv (e : P ≃o P) (p : P) :
    PolynomialStalk K p ≃ₐ[K] PolynomialStalk K (e p) :=
  MvPolynomial.renameEquiv K (faceVertexOrderEquiv e p)

def barycentricStalkOrderEquiv (e : P ≃o P) (p : P) :
    BarycentricStalk K p ≃ₐ[K] BarycentricStalk K (e p) :=
  booleanVertexRelabelEquiv (faceVertexOrderEquiv e p)

@[simp] theorem polynomialStalkOrderEquiv_X (e : P ≃o P) (p : P) (a : FaceVertex p) :
    polynomialStalkOrderEquiv K e p (X a) = X (faceVertexOrderEquiv e p a) :=
  MvPolynomial.rename_X _ _

@[simp] theorem polynomialStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    polynomialStalkOrderEquiv K e p (polynomialParameter K p r) =
      polynomialParameter K (e p) r :=
  MvPolynomial.rename_esymm (σ := FaceVertex p) (R := K) r (faceVertexOrderEquiv e p)

@[simp] theorem barycentricStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    barycentricStalkOrderEquiv K e p (booleanRankParameter r) = booleanRankParameter r :=
  booleanVertexRelabelEquiv_parameter (faceVertexOrderEquiv e p) r

@[simp] theorem polynomialStalkOrderEquiv_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  simp only [polynomialStalkOrderEquiv, faceVertexOrderEquiv_refl, MvPolynomial.renameEquiv_refl,
    AlgEquiv.refl]
  rfl

@[simp] theorem barycentricStalkOrderEquiv_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (OrderIso.refl P) p) x = x
  have he : faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl (FaceVertex p) :=
    faceVertexOrderEquiv_refl p
  exact he.symm ▸ booleanVertexRelabelEquiv_refl x

theorem polynomialStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (e.trans f) p x =
      polynomialStalkOrderEquiv K f (e p) (polynomialStalkOrderEquiv K e p x) := by
  rw [polynomialStalkOrderEquiv, faceVertexOrderEquiv_trans, ← MvPolynomial.renameEquiv_trans]
  rfl

theorem barycentricStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (e.trans f) p x =
      barycentricStalkOrderEquiv K f (e p) (barycentricStalkOrderEquiv K e p x) := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (e.trans f) p) x =
    booleanVertexRelabelEquiv (faceVertexOrderEquiv f (e p))
      (booleanVertexRelabelEquiv (faceVertexOrderEquiv e p) x)
  exact (faceVertexOrderEquiv_trans e f p).symm ▸
    booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexOrderEquiv f (e p)) x

theorem polynomialStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : PolynomialStalk K p) :
    polynomialRestriction K (e.monotone h) (polynomialStalkOrderEquiv K e p x) =
      polynomialStalkOrderEquiv K e q (polynomialRestriction K h x) := by
  have he : (polynomialRestriction K (e.monotone h)).comp
      (polynomialStalkOrderEquiv K e p).toAlgHom =
      (polynomialStalkOrderEquiv K e q).toAlgHom.comp (polynomialRestriction K h) := by
    apply MvPolynomial.algHom_ext
    intro a
    by_cases hq : a.val ≤ q
    · have haq : e a.val ≤ e q := e.monotone hq
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_pos hq, dif_pos haq]
      rfl
    · have haq : ¬ e a.val ≤ e q := fun h' => hq (e.le_iff_le.mp h')
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_neg hq, dif_neg haq, map_zero]
  exact DFunLike.congr_fun he x

theorem barycentricStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : BarycentricStalk K p) :
    booleanRestriction (faceVertexInclusion (e.monotone h)) (barycentricStalkOrderEquiv K e p x) =
      barycentricStalkOrderEquiv K e q (booleanRestriction (faceVertexInclusion h) x) := by
  have he : (faceVertexInclusion (e.monotone h)).trans (faceVertexOrderEquiv e p).symm.toEmbedding =
      (faceVertexOrderEquiv e q).symm.toEmbedding.trans (faceVertexInclusion h) := by
    ext a
    rfl
  change booleanRestriction (faceVertexInclusion (e.monotone h))
      (booleanRestriction (faceVertexOrderEquiv e p).symm.toEmbedding x) =
    booleanRestriction (faceVertexOrderEquiv e q).symm.toEmbedding
      (booleanRestriction (faceVertexInclusion h) x)
  calc
    _ = booleanRestriction ((faceVertexInclusion (e.monotone h)).trans
        (faceVertexOrderEquiv e p).symm.toEmbedding) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction ((faceVertexOrderEquiv e q).symm.toEmbedding.trans
        (faceVertexInclusion h)) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

theorem polynomialStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K p) (hx : x ∈ polynomialDegreePiece n) :
    polynomialStalkOrderEquiv K e p x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p) n x hx

theorem barycentricStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricStalkOrderEquiv K e p x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanVertexRelabelEquiv_degree (faceVertexOrderEquiv e p) n x hx

end Stalks
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarCohomologyObstruction.lean -/
section

section
/-! # The cyclic module generated by the comparison obstruction

This is the cohomological algebra needed after the scalar-image calculation
in Theorem 9.4.  The class lies in Mathlib's actual first group cohomology of
the kernel representation.  Its annihilator is proved to be the image of
the invariant elements under the scalar map.  No scalar-image equality for
face rings is assumed to have been established by this generic result.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal.ScalarObstruction
open CategoryTheory groupCohomology
universe u
variable {K G E : Type u} [CommRing K] [Group G] [AddCommGroup E] [Module K E]
variable (ρ : Representation K G E) (ε : E →ₗ[K] K)
variable (hε : ∀ g x, ε (ρ g x) = ε x)

def kernelSubrepresentation : Subrepresentation ρ where
  toSubmodule := LinearMap.ker ε
  apply_mem_toSubmodule g x hx := by
    change ε (ρ g x) = 0
    exact (hε g x).trans hx

abbrev kernelRepresentation : Rep K G :=
  Rep.of (kernelSubrepresentation ρ ε hε).toRepresentation


include hε in
/-- The original value rho(g)x-x belongs to the actual invariant scalar kernel. -/
theorem palomarConnectingValue_mem_kernel (x : E) (g : G) :
    ρ g x - x ∈ LinearMap.ker ε := by
  change ε (ρ g x - x) = 0
  rw [map_sub, hε, sub_self]
/-- The literal original kernel-valued connecting cochain. -/
def palomarConnectingFunction (x : E) : G → kernelRepresentation ρ ε hε :=
  fun g => ⟨ρ g x - x, palomarConnectingValue_mem_kernel ρ ε hε x g⟩
/-- The original group-cocycle calculation, recorded as a semantic support fact. -/
theorem palomarConnectingFunction_isCocycle (x : E) :
    palomarConnectingFunction ρ ε hε x ∈ cocycles₁ (kernelRepresentation ρ ε hε) := by
  apply (mem_cocycles₁_iff _).mpr
  intro g h
  apply Subtype.ext
  change ρ (g * h) x - x = ρ g (ρ h x - x) + (ρ g x - x)
  rw [map_mul, Module.End.mul_apply, map_sub]
  abel

/-- The usual connecting cocycle `g ↦ g x - x`, valued in `ker ε`. -/
def connectingCocycle (x : E) : cocycles₁ (kernelRepresentation ρ ε hε) :=
  ⟨palomarConnectingFunction ρ ε hε x, palomarConnectingFunction_isCocycle ρ ε hε x⟩

def connectingCocycleLinear : E →ₗ[K] cocycles₁ (kernelRepresentation ρ ε hε) where
  toFun := connectingCocycle ρ ε hε
  map_add' x y := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change ρ g (x + y) - (x + y) = (ρ g x - x) + (ρ g y - y)
    rw [map_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change ρ g (c • x) - c • x = c • (ρ g x - x)
    rw [map_smul, smul_sub]

def obstruction (x : E) : H1 (kernelRepresentation ρ ε hε) :=
  H1π _ (connectingCocycle ρ ε hε x)

theorem obstruction_smul (c : K) (x : E) :
    obstruction ρ ε hε (c • x) = c • obstruction ρ ε hε x := by
  change (H1π _).hom (connectingCocycleLinear ρ ε hε (c • x)) = _
  rw [map_smul, map_smul]
  rfl

theorem obstruction_sub (x y : E) :
    obstruction ρ ε hε (x - y) = obstruction ρ ε hε x - obstruction ρ ε hε y := by
  change (H1π _).hom (connectingCocycleLinear ρ ε hε (x - y)) = _
  rw [map_sub, map_sub]
  rfl

/-- The genuine image of invariant elements; an ideal because `K` acts on itself. -/
def invariantScalarIdeal : Ideal K := ρ.invariants.map ε

theorem obstruction_eq_zero_iff (x : E) :
    obstruction ρ ε hε x = 0 ↔
      ∃ y : E, (∀ g, ρ g y = y) ∧ ε y = ε x := by
  change H1π (kernelRepresentation ρ ε hε) (connectingCocycle ρ ε hε x) = 0 ↔ _
  rw [H1π_eq_zero_iff (A := kernelRepresentation ρ ε hε)]
  change (∃ a : LinearMap.ker ε, (d₀₁.{u, u} (kernelRepresentation.{u} ρ ε hε)).hom a =
    (connectingCocycle ρ ε hε x).val) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨x - a.val, ?_, ?_⟩
    · intro g
      have hg := congrArg (fun f : G → LinearMap.ker ε => (f g).val) ha
      change ρ g a.val - a.val = ρ g x - x at hg
      rw [map_sub]
      exact sub_eq_sub_iff_add_eq_add.mpr (by
        have he := sub_eq_sub_iff_add_eq_add.mp hg
        simpa [add_comm, add_left_comm, add_assoc] using he.symm)
    · rw [map_sub, a.property, sub_zero]
  · rintro ⟨y, hy, he⟩
    refine ⟨⟨x - y, ?_⟩, ?_⟩
    · change ε (x - y) = 0
      rw [map_sub, he, sub_self]
    · funext g
      apply Subtype.ext
      change ρ g (x - y) - (x - y) = ρ g x - x
      rw [map_sub, hy]
      abel

/-- The class is independent of the chosen lift of a scalar. -/
theorem obstruction_eq_of_scalar_eq (x y : E) (h : ε x = ε y) :
    obstruction ρ ε hε x = obstruction ρ ε hε y := by
  rw [← sub_eq_zero, ← obstruction_sub, obstruction_eq_zero_iff]
  refine ⟨0, fun g => map_zero (ρ g), ?_⟩
  rw [map_zero, map_sub, h, sub_self]

theorem obstruction_annihilator (x : E) (hx : ε x = 1) (c : K) :
    c • obstruction ρ ε hε x = 0 ↔ c ∈ invariantScalarIdeal ρ ε := by
  rw [← obstruction_smul, obstruction_eq_zero_iff]
  change (∃ y : E, (∀ g, ρ g y = y) ∧ ε y = ε (c • x)) ↔
    ∃ y, y ∈ ρ.invariants ∧ ε y = c
  simp only [map_smul, hx, smul_eq_mul, mul_one, Representation.mem_invariants]

/-- Every invariant scalar lift annihilates the canonical obstruction. -/
theorem invariant_lift_annihilates (x : E) (hx : ε x = 1)
    (y : E) (hy : ∀ g, ρ g y = y) :
    ε y • obstruction ρ ε hε x = 0 :=
  (obstruction_annihilator ρ ε hε x hx (ε y)).mpr ⟨y, hy, rfl⟩

def scalarConnectingMap (x : E) : K →ₗ[K] H1 (kernelRepresentation ρ ε hε) :=
  LinearMap.toSpanSingleton K _ (obstruction ρ ε hε x)

theorem scalarConnectingMap_ker (x : E) (hx : ε x = 1) :
    LinearMap.ker (scalarConnectingMap ρ ε hε x) = invariantScalarIdeal ρ ε := by
  ext c
  exact obstruction_annihilator ρ ε hε x hx c

/-- The cyclic submodule of the actual `H¹` is the quotient by the exact
scalar ideal.  Substituting the ideal equality from Theorem 9.4 gives its
claimed `K / (d-1)!K` description. -/
def obstructionSpanEquiv (x : E) (hx : ε x = 1) :
    (K ⧸ invariantScalarIdeal ρ ε) ≃ₗ[K]
      Submodule.span K {obstruction ρ ε hε x} :=
  (Submodule.quotEquivOfEq _ _ (scalarConnectingMap_ker ρ ε hε x hx).symm).trans
    ((scalarConnectingMap ρ ε hε x).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton _)))

def obstructionSpanEquivOfIdealEq (x : E) (hx : ε x = 1) (D : K)
    (hI : invariantScalarIdeal ρ ε = Ideal.span {D}) :
    (K ⧸ Ideal.span {D}) ≃ₗ[K] Submodule.span K {obstruction ρ ε hε x} :=
  (Submodule.quotEquivOfEq _ _ hI.symm).trans (obstructionSpanEquiv ρ ε hε x hx)

end FourPapers.Universal.ScalarObstruction

end
end
end

/- BEGIN FourPapers/Universal/ScalarStalkFamilies.lean -/
section

section
/-! # The paper's module of coherent maps in the direction `R → B`

The defining conditions are linearity over the coefficient ring, all rank
parameters, ordinary degree zero, and every face restriction square.
No invertibility or prescribed scalar is built into this module.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ScalarFamilies
open Classical MvPolynomial

section Coefficients
variable {V W K : Type*} [Fintype V] [Fintype W] [CommRing K]

def constantCoefficient : BooleanBarycentricRing V K →ₗ[K] K :=
  (Finsupp.lapply ⟨0, isChainExponent_zero⟩).comp
    (@LinearEquiv.toLinearMap K K _ _ (RingHom.id K) (RingHom.id K)
      (PalomarBarycentricRelative.coefficientIdentityInvPair (K := K))
      (PalomarBarycentricRelative.coefficientIdentityInvPair (K := K))
      (BooleanBarycentricRing V K) ({a : BooleanFace V →₀ ℕ // IsChainExponent a} →₀ K)
      _ _ _ _ booleanChainBasis.repr)

theorem zeroBasis_eq_one :
    booleanChainBasis (V := V) (K := K) ⟨0, isChainExponent_zero⟩ = 1 := by
  rw [booleanChainBasis, standardMonomialBasis_apply]
  simp

@[simp] theorem constantCoefficient_one :
    constantCoefficient (V := V) (K := K) 1 = 1 := by
  rw [← zeroBasis_eq_one]
  change booleanChainBasis.repr (booleanChainBasis ⟨0, isChainExponent_zero⟩)
    ⟨0, isChainExponent_zero⟩ = 1
  simp

@[simp] theorem constantCoefficient_smul_one (c : K) :
    constantCoefficient (V := V) (K := K) (c • 1) = c := by
  rw [map_smul, constantCoefficient_one, smul_eq_mul, mul_one]

theorem constantCoefficient_restriction (e : V ↪ W)
    (x : BooleanBarycentricRing W K) :
    constantCoefficient (booleanRestriction e x) = constantCoefficient x := by
  change booleanChainBasis.repr (booleanRestriction e x) ⟨0, isChainExponent_zero⟩ =
    booleanChainBasis.repr x ⟨0, isChainExponent_zero⟩
  rw [booleanRestriction_coefficient]
  congr 1

theorem constantCoefficient_relabel (e : V ≃ W)
    (x : BooleanBarycentricRing V K) :
    constantCoefficient (booleanVertexRelabelEquiv e x) = constantCoefficient x :=
  constantCoefficient_restriction e.symm.toEmbedding x

theorem constantCoefficient_relabel_symm (e : V ≃ W)
    (x : BooleanBarycentricRing W K) :
    constantCoefficient ((booleanVertexRelabelEquiv e).symm x) = constantCoefficient x := by
  have h := constantCoefficient_relabel e ((booleanVertexRelabelEquiv e).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- A degree-zero chain monomial has zero exponent at every nonempty face. -/
theorem booleanOrdinaryDegree_zero_iff (a : BooleanFace V →₀ ℕ) :
    booleanOrdinaryDegree a = 0 ↔ a = 0 := by
  constructor
  · intro h
    ext F
    by_cases ha : a F = 0
    · exact ha
    · have hF : F ∈ a.support := Finsupp.mem_support_iff.mpr ha
      have hle : a F * F.val.card ≤ booleanOrdinaryDegree a := by
        change a F * F.val.card ≤ ∑ F ∈ a.support, a F * F.val.card
        exact Finset.single_le_sum (f := fun G : BooleanFace V => a G * G.val.card)
          (fun _ _ => Nat.zero_le _) hF
      have hpos : 0 < F.val.card := Finset.card_pos.mpr F.property
      have ha' : 0 < a F := Nat.pos_of_ne_zero ha
      have hp := Nat.mul_pos ha' hpos
      omega
  · rintro rfl
    simp [booleanOrdinaryDegree]

theorem degreeZero_eq_smul_one (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) 0) :
    x = constantCoefficient x • 1 := by
  apply booleanChainBasis.repr.injective
  ext a
  rw [map_smul, ← zeroBasis_eq_one, Module.Basis.repr_self]
  by_cases ha : a = ⟨0, isChainExponent_zero⟩
  · subst a
    simp [constantCoefficient]
  · have hdegree : booleanOrdinaryDegree a.val ≠ 0 := by
      intro h
      apply ha
      exact Subtype.ext ((booleanOrdinaryDegree_zero_iff a.val).mp h)
    have hx' : booleanChainBasis.repr x a = 0 := hx a hdegree
    rw [hx']
    simp [ha, Ne.symm ha]

end Coefficients

section Families
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

abbrev Family := ∀ p : P, PolynomialStalk K p →ₗ[K] BarycentricStalk K p
def palomarStalkMapModule (p : P) : Module K (PolynomialStalk K p →ₗ[K] BarycentricStalk K p) := inferInstance
attribute [instance 2400] palomarStalkMapModule

/-- The original scalar-closure proof for commuting face restriction squares. -/
theorem palomarCoherentSmul (c : K) (F : Family (P := P) K)
    (hF : ∀ p q (h : q ≤ p) x,
      booleanRestriction (faceVertexInclusion h) (F p x) = F q (polynomialRestriction K h x)) :
    ∀ p q (h : q ≤ p) x,
      booleanRestriction (faceVertexInclusion h) ((c • F) p x) =
        (c • F) q (polynomialRestriction K h x) := by
  intro p q h x
  change booleanRestriction (faceVertexInclusion h) (c • F p x) = _
  rw [map_smul, hF]
  rfl
theorem palomarCoherentZero :
    ∀ p q (h : q ≤ p) x,
      booleanRestriction (faceVertexInclusion h) ((0 : Family (P := P) K) p x) =
        (0 : Family (P := P) K) q (polynomialRestriction K h x) := by
  intros; simp
def coherent : Submodule K (Family (P := P) K) where
  carrier := {F | ∀ p q (h : q ≤ p) x,
    booleanRestriction (faceVertexInclusion h) (F p x) = F q (polynomialRestriction K h x)}
  zero_mem' := palomarCoherentZero K
  add_mem' := by
    intro F H hF hH p q h x
    change booleanRestriction (faceVertexInclusion h) (F p x + H p x) = _
    rw [map_add, hF, hH]
    rfl
  smul_mem' := palomarCoherentSmul K

def parameterLinear : Submodule K (Family (P := P) K) where
  carrier := {F | ∀ p r x, F p (polynomialParameter K p (r + 1) * x) =
    booleanRankParameter (r + 1) * F p x}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p r x
    change F p _ + H p _ = booleanRankParameter (r + 1) * (F p x + H p x)
    rw [hF, hH, mul_add]
  smul_mem' := by
    intro c F hF p r x
    change c • F p _ = booleanRankParameter (r + 1) * (c • F p x)
    rw [hF, mul_smul_comm]

def graded : Submodule K (Family (P := P) K) where
  carrier := {F | ∀ p n x, x ∈ polynomialDegreePiece n → F p x ∈
    @basisOrdinaryDegreePiece _ K _ _ _ (palomarBarycentricStalkModule K p)
      booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n}
  zero_mem' := by
    intro p n x hx
    exact (basisOrdinaryDegreePiece (booleanChainBasis (V := FaceVertex p) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n).zero_mem
  add_mem' := by intro F H hF hH p n x hx; exact Submodule.add_mem _ (hF p n x hx) (hH p n x hx)
  smul_mem' := by intro c F hF p n x hx; exact Submodule.smul_mem _ c (hF p n x hx)

/-- Exactly the coherent degree-zero parameter-linear families of §3. -/
def comparisonModule : Submodule K (Family (P := P) K) :=
  coherent K ⊓ (parameterLinear K ⊓ graded K)

/-- The additive inverse is the one forced by the actual module over `K`. -/
instance comparisonModuleAddCommGroup : AddCommGroup (comparisonModule (P := P) K) :=
  Module.addCommMonoidToAddCommGroup K

def scalar : comparisonModule (P := P) K →ₗ[K] K where
  toFun F := constantCoefficient (F.val ⊥ 1)
  map_add' F H := by change constantCoefficient (F.val ⊥ 1 + H.val ⊥ 1) = _; rw [map_add]
  map_smul' c F := by change constantCoefficient (c • F.val ⊥ 1) = _; rw [map_smul]; rfl

theorem component_one (F : comparisonModule (P := P) K) (p : P) :
    F.val p 1 = scalar K F • 1 := by
  have hone : (1 : PolynomialStalk K p) ∈ polynomialDegreePiece 0 := by
    intro a ha
    by_cases h : a = 0
    · subst a
      exact (ha (by simp [vertexDegree])).elim
    · simp [MvPolynomial.coeff_one, h, Ne.symm h]
  have h := degreeZero_eq_smul_one (F.val p 1) (F.property.2.2 p 0 1 hone)
  have hc : constantCoefficient (F.val p 1) = constantCoefficient (F.val ⊥ 1) := by
    have hn := F.property.1 p ⊥ bot_le 1
    simp only [map_one] at hn
    exact (constantCoefficient_restriction (faceVertexInclusion (bot_le : (⊥ : P) ≤ p))
      (F.val p 1)).symm.trans (congrArg constantCoefficient hn)
  rw [h, hc]
  rfl

def relabel (e : P ≃o P) : Family (P := P) K →ₗ[K] Family (P := P) K where
  toFun F p := (barycentricStalkOrderEquiv K e.symm p).symm.toLinearMap.comp
    ((F (e.symm p)).comp (polynomialStalkOrderEquiv K e.symm p).toLinearMap)
  map_add' F H := by funext p; apply LinearMap.ext; intro x; simp
  map_smul' c F := by funext p; apply LinearMap.ext; intro x; simp

@[simp] theorem relabel_apply (e : P ≃o P) (F : Family (P := P) K)
    (p : P) (x : PolynomialStalk K p) :
    relabel K e F p x = (barycentricStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (polynomialStalkOrderEquiv K e.symm p x)) := rfl

theorem barycentricStalkOrderEquiv_trans_symm (e f : P ≃o P) (p : P)
    (x : BarycentricStalk K ((e.trans f) p)) :
    (barycentricStalkOrderEquiv K (e.trans f) p).symm x =
      (barycentricStalkOrderEquiv K e p).symm
        ((barycentricStalkOrderEquiv K f (e p)).symm x) := by
  apply (barycentricStalkOrderEquiv K (e.trans f) p).injective
  rw [AlgEquiv.apply_symm_apply, barycentricStalkOrderEquiv_trans,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

theorem relabel_refl (F : Family (P := P) K) : relabel K (OrderIso.refl P) F = F := by
  funext p
  apply LinearMap.ext
  intro x
  apply (barycentricStalkOrderEquiv K (OrderIso.refl P) p).injective
  change barycentricStalkOrderEquiv K (OrderIso.refl P) p
    ((barycentricStalkOrderEquiv K (OrderIso.refl P) p).symm
      (F p (polynomialStalkOrderEquiv K (OrderIso.refl P) p x))) = _
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_refl, barycentricStalkOrderEquiv_refl]

theorem relabel_trans (e f : P ≃o P) (F : Family (P := P) K) :
    relabel K (e.trans f) F = relabel K f (relabel K e F) := by
  funext p
  apply LinearMap.ext
  intro x
  change (barycentricStalkOrderEquiv K (f.symm.trans e.symm) p).symm
    (F (e.symm (f.symm p)) (polynomialStalkOrderEquiv K (f.symm.trans e.symm) p x)) = _
  rw [barycentricStalkOrderEquiv_trans_symm, polynomialStalkOrderEquiv_trans]
  rfl

theorem relabel_coherent (e : P ≃o P) (F : Family (P := P) K)
    (hF : F ∈ coherent K) : relabel K e F ∈ coherent K := by
  intro p q h x
  apply (barycentricStalkOrderEquiv K e.symm q).injective
  have hn := barycentricStalkOrderEquiv_restriction K e.symm h
    ((barycentricStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (polynomialStalkOrderEquiv K e.symm p x)))
  change barycentricStalkOrderEquiv K e.symm q
    (booleanRestriction (faceVertexInclusion h)
      ((barycentricStalkOrderEquiv K e.symm p).symm
        (F (e.symm p) (polynomialStalkOrderEquiv K e.symm p x)))) =
    barycentricStalkOrderEquiv K e.symm q
      ((barycentricStalkOrderEquiv K e.symm q).symm
        (F (e.symm q) (polynomialStalkOrderEquiv K e.symm q
          (polynomialRestriction K h x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hF,
    polynomialStalkOrderEquiv_restriction]

theorem relabel_parameterLinear (e : P ≃o P) (F : Family (P := P) K)
    (hF : F ∈ parameterLinear K) : relabel K e F ∈ parameterLinear K := by
  intro p r x
  apply (barycentricStalkOrderEquiv K e.symm p).injective
  simp only [relabel_apply, map_mul, polynomialStalkOrderEquiv_parameter,
    AlgEquiv.apply_symm_apply, barycentricStalkOrderEquiv_parameter]
  exact hF (e.symm p) r _

theorem relabel_graded (e : P ≃o P) (F : Family (P := P) K)
    (hF : F ∈ graded K) : relabel K e F ∈ graded K := by
  intro p n x hx
  have hh := hF (e.symm p) n _ (polynomialStalkOrderEquiv_degree K e.symm p n x hx)
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv e.symm p).symm
    (F (e.symm p) (polynomialStalkOrderEquiv K e.symm p x)) ∈ _
  exact booleanVertexRelabelEquiv_degree (faceVertexOrderEquiv e.symm p).symm n _ hh

def relabelComparison (e : P ≃o P) :
    comparisonModule (P := P) K →ₗ[K] comparisonModule (P := P) K :=
  (relabel K e).restrict fun F hF =>
    ⟨relabel_coherent K e F hF.1, relabel_parameterLinear K e F hF.2.1,
      relabel_graded K e F hF.2.2⟩

theorem scalar_relabel (e : P ≃o P) (F : comparisonModule (P := P) K) :
    scalar K (relabelComparison K e F) = scalar K F := by
  change constantCoefficient ((barycentricStalkOrderEquiv K e.symm ⊥).symm
    (F.val (e.symm ⊥) (polynomialStalkOrderEquiv K e.symm ⊥ 1))) = _
  rw [map_one, component_one, map_smul, map_one, constantCoefficient_smul_one]

end Families

section Cohomology
universe u
variable {P K G : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
  [CommRing K] [Group G]
variable (K) (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def representation : Representation K G (comparisonModule (P := P) K) where
  toFun g := relabelComparison K (act g)
  map_one' := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    change relabel K (act 1) F.val = F.val
    rw [h₁, relabel_refl]
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    change relabel K (act (g * h)) F.val = relabel K (act g) (relabel K (act h) F.val)
    rw [hmul, relabel_trans]

abbrev obstructionRepresentation : Rep K G :=
  ScalarObstruction.kernelRepresentation (representation (P := P) K act h₁ hmul) (scalar (P := P) K)
    (fun (g : G) (F : comparisonModule (P := P) K) => scalar_relabel K (act g) F)

/-- The literal comparison cocycle of equation (5), in Mathlib's `H1`. -/
def obstruction (F : comparisonModule (P := P) K) :
    groupCohomology.H1 (obstructionRepresentation K act h₁ hmul) :=
  ScalarObstruction.obstruction (representation (P := P) K act h₁ hmul) (scalar (P := P) K)
    (fun (g : G) (F : comparisonModule (P := P) K) => scalar_relabel K (act g) F) F

theorem obstruction_independent (F H : comparisonModule (P := P) K)
    (h : scalar K F = scalar K H) :
    obstruction K act h₁ hmul F = obstruction K act h₁ hmul H :=
  ScalarObstruction.obstruction_eq_of_scalar_eq _ _ _ F H h

def invariantScalarIdeal : Ideal K :=
  ScalarObstruction.invariantScalarIdeal (representation (P := P) K act h₁ hmul) (scalar (P := P) K)

theorem scalar_mem_invariantIdeal_iff (c : K) :
    c ∈ invariantScalarIdeal K act h₁ hmul ↔
      ∃ F : comparisonModule (P := P) K,
        (∀ g, relabelComparison K (act g) F = F) ∧ scalar K F = c := by
  rfl

theorem obstruction_annihilator (F : comparisonModule (P := P) K)
    (hF : scalar K F = 1) (c : K) :
    c • obstruction K act h₁ hmul F = 0 ↔ c ∈ invariantScalarIdeal K act h₁ hmul :=
  ScalarObstruction.obstruction_annihilator _ _ _ F hF c

def obstructionSpanEquiv (F : comparisonModule (P := P) K) (hF : scalar K F = 1) :
    (K ⧸ invariantScalarIdeal K act h₁ hmul) ≃ₗ[K]
      Submodule.span K {obstruction K act h₁ hmul F} :=
  ScalarObstruction.obstructionSpanEquiv _ _ _ F hF

end Cohomology
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/StalkGradingBridge.lean -/
section

section
/-! # Ordinary grading and the existing stalk standard coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

/-- Retain a specified equality procedure when choosing an auxiliary order.
Only the comparison proof changes; the equality field is literally `d`. -/
def linearOrderWithDecidableEq {α : Type*} (o : LinearOrder α) (d : DecidableEq α) :
    LinearOrder α :=
  { o with
    toDecidableEq := d
    compare_eq_compareOfLessAndEq := by
      intro a b
      have hd : d = o.toDecidableEq := Subsingleton.elim _ _
      cases hd
      exact o.compare_eq_compareOfLessAndEq a b }

section Basis
variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
theorem scalarOrdinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  change b.repr (b i) j = 0
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]

end Basis
section Stalk
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (hs : IsSimplicialPoset P)
/-- Standard-coordinate homogeneity is ordinary homogeneity in the literal
polynomial and chain-monomial bases. -/
theorem ordinaryDegree_of_hasStandardDegree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : HasStandardDegree K hs p f) :
    ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n := by
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  have hb (u : BooleanChainExponent (FaceVertex p)) :
      f (booleanChainBasis u) ∈ polynomialDegreePiece (chainOrdinaryDegree u.val) := by
    intro a ha
    let v : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm a
    have hv : chainVertexMap v.val = a := chainVertexEquiv.apply_symm_apply a
    have hd : standardOrdinaryDegree ((standardInsideEquiv hs p) v).val ≠
        standardOrdinaryDegree ((standardInsideEquiv hs p) u).val := by
      rw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside,
        ← vertexDegree_eq_chainOrdinaryDegree, hv]
      exact ha
    have h := hf ((standardInsideEquiv hs p) u) ((standardInsideEquiv hs p) v).val hd
    rw [barycentricStalkStandardBasis_local,
      polynomialStandardCoordinates_chain, hv] at h
    exact h
  intro n x hx
  rw [← (booleanChainBasis (V := FaceVertex p) (K := K)).linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply (polynomialDegreePiece n).sum_mem
  intro u hu
  rw [map_smul]
  apply (polynomialDegreePiece n).smul_mem
  have hd : booleanOrdinaryDegree u.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hu (hx u hn)
  change chainOrdinaryDegree u.val = n at hd
  exact hd ▸ hb u

end Stalk
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarOrdinaryComparison.lean -/
section


section

/-! # Ordinary normalized comparisons in the paper's direction

The previously verified coherent comparison is inverted on each actual
stalk. Its parameter identities, ordinary grading and restriction squares
are transported through the inverse. The leading coefficient at the empty
chain proves normalization, so the resulting element of the actual module
of Section 9 maps to one under its scalar map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section ElementaryGrading
variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

variable {V : Type*} [Fintype V]

theorem scalarPolynomialDegreePiece_zero_eq_C
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece 0) :
    f = MvPolynomial.C (f.coeff 0) := by
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  · rw [MvPolynomial.coeff_C_of_ne_zero ha]
    apply hf a
    intro hd
    apply ha
    ext v
    have hv : a v ≤ vertexDegree (fun w => a w) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    change a v = 0
    omega

theorem scalarPolynomialChainDegreePiece_eq [LinearOrder V] (n : ℕ) :
    basisOrdinaryDegreePiece (polynomialChainBasis (V := V) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n = polynomialDegreePiece n := by
  apply Submodule.ext
  intro f
  constructor
  · intro hf a ha
    let c : BooleanChainExponent V := chainVertexEquiv.symm a
    have hc : chainVertexMap c.val = a := chainVertexEquiv.apply_symm_apply a
    have hn : booleanOrdinaryDegree c.val ≠ n := by
      change chainOrdinaryDegree c.val ≠ n
      rw [← vertexDegree_eq_chainOrdinaryDegree, hc]
      exact ha
    have hh := hf c hn
    change polynomialChainBasis.repr f c = 0 at hh
    simpa only [polynomialChainBasis_repr, hc] using hh
  · intro hf c hc
    change polynomialChainBasis.repr f c = 0
    rw [polynomialChainBasis_repr]
    apply hf
    change chainOrdinaryDegree c.val ≠ n at hc
    simpa only [vertexDegree_eq_chainOrdinaryDegree] using hc

end ElementaryGrading

section StandardDegree
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (hs : IsSimplicialPoset P)

/-- The diagonal leading coefficient at the empty chain is exactly one. -/
theorem hasStandardLeadingDegree_one (d : ℕ) (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hl : HasStandardLeading K hs d p f) (hd : HasStandardDegree K hs p f) :
    f 1 = 1 := by
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  let z : BooleanChainExponent (FaceVertex p) := ⟨0, isChainExponent_zero⟩
  have hz : (booleanChainBasis (K := K)) z = 1 := ScalarFamilies.zeroBasis_eq_one
  have hzdeg : booleanOrdinaryDegree z.val = 0 := by simp [z, booleanOrdinaryDegree]
  have hg := ordinaryDegree_of_hasStandardDegree hs p f hd 0 1
    (by rw [← hz]; simpa only [hzdeg] using
      scalarOrdinaryBasis_mem_piece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) z)
  have hC := scalarPolynomialDegreePiece_zero_eq_C (f 1) hg
  let a := (standardInsideEquiv hs p) z
  have hlead := hl a a.val le_rfl
  rw [if_pos rfl] at hlead
  have hb : barycentricStalkStandardBasis K hs p a = 1 :=
    (barycentricStalkStandardBasis_local K hs p z).trans hz
  rw [hb] at hlead
  have hcoord := polynomialStandardCoordinates_chain K hs p (f 1) z
  have hzero : chainVertexMap z.val = 0 := by
    ext v
    simp [z, chainVertexMap]
  rw [hzero] at hcoord
  have hc : (f 1).coeff 0 = 1 := hcoord.symm.trans hlead
  rw [hC, hc, MvPolynomial.C_1]

end StandardDegree

namespace ScalarFamilies
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- Inversion of actual coherent stalk equivalences. -/
def inverseCoherentFamily
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) :
    Family (P := P) K := fun p => (E.component p).symm.toLinearMap

theorem inverseCoherentFamily_mem
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hp : ∀ p r x, E.component p (booleanRankParameter (r + 1) * x) =
      polynomialParameter K p (r + 1) * E.component p x)
    (hd : ∀ p n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) :
    inverseCoherentFamily K E ∈ comparisonModule K := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q h x
    exact E.symm.naturality p q h x
  · intro p r x
    apply (E.component p).injective
    change E.component p ((E.component p).symm (polynomialParameter K p (r + 1) * x)) =
      E.component p (booleanRankParameter (r + 1) * (E.component p).symm x)
    rw [LinearEquiv.apply_symm_apply, hp, LinearEquiv.apply_symm_apply]
  · intro p n x hx
    letI : LinearOrder (FaceVertex p) :=
      linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
          (Fintype.equivFin (FaceVertex p)).injective) inferInstance
    have he : ∀ (a b : BooleanChainExponent (FaceVertex p)),
        booleanOrdinaryDegree b.val ≠ booleanOrdinaryDegree a.val →
        polynomialChainBasis.repr (E.component p (booleanChainBasis a)) b = 0 := by
      intro a b hab
      rw [polynomialChainBasis_repr]
      apply hd p (booleanOrdinaryDegree a.val) _
        (scalarOrdinaryBasis_mem_piece booleanChainBasis (fun c => booleanOrdinaryDegree c.val) a)
      change chainOrdinaryDegree b.val ≠ chainOrdinaryDegree a.val at hab
      simpa only [vertexDegree_eq_chainOrdinaryDegree,
        booleanOrdinaryDegree_eq_chainOrdinaryDegree] using hab
    apply (basisOrdinaryDegreePiece_equiv_iff booleanChainBasis polynomialChainBasis
      (fun a => booleanOrdinaryDegree a.val) (E.component p) he n ((E.component p).symm x)).mp
    rw [LinearEquiv.apply_symm_apply, scalarPolynomialChainDegreePiece_eq]
    exact hx

theorem inverseCoherentFamily_one
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hE : ∀ p, E.component p 1 = 1) (p : P) : inverseCoherentFamily K E p 1 = 1 := by
  apply (E.component p).injective
  change E.component p ((E.component p).symm 1) = E.component p 1
  rw [LinearEquiv.apply_symm_apply, hE]

/-- Surjectivity of the actual scalar map follows from the already proved
ordinary coherent comparison, over every commutative coefficient ring. -/
theorem exists_normalized_comparisonFamily (hs : IsSimplicialPoset P) :
    ∃ F : comparisonModule (P := P) K, scalar K F = 1 := by
  let d := Fintype.card P
  have hrank : ∀ p : P, faceRank p ≤ d := fun p => Finset.card_le_univ (faceVertices p)
  let E := universalCoherentComparison K hs d hrank
  have hp : ∀ p r x, E.component p (booleanRankParameter (r + 1) * x) =
      polynomialParameter K p (r + 1) * E.component p x :=
    fun p => (universalCoherentComparison_spec K hs d hrank p).2.1
  have hd : ∀ p n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n :=
    fun p => ordinaryDegree_of_hasStandardDegree hs p (E.component p).toLinearMap
      (universalCoherentComparison_spec K hs d hrank p).2.2
  have hE : ∀ p, E.component p 1 = 1 := fun p =>
    hasStandardLeadingDegree_one hs d p (E.component p).toLinearMap
      (universalCoherentComparison_spec K hs d hrank p).1
      (universalCoherentComparison_spec K hs d hrank p).2.2
  refine ⟨⟨inverseCoherentFamily K E, inverseCoherentFamily_mem K E hp hd⟩, ?_⟩
  change constantCoefficient (inverseCoherentFamily K E ⊥ 1) = 1
  rw [inverseCoherentFamily_one K E hE, constantCoefficient_one]

theorem scalar_surjective (hs : IsSimplicialPoset P) :
    Function.Surjective (scalar (P := P) K) := by
  obtain ⟨F, hF⟩ := exists_normalized_comparisonFamily K hs
  intro c
  refine ⟨c • F, ?_⟩
  rw [map_smul, hF, smul_eq_mul, mul_one]

end ScalarFamilies
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SimplexTransportGeometry.lean -/
section

section
/-! # Literal finite-simplex vertex geometry

Shared exact declarations for finite-subset order isomorphisms, simplex
vertices, and finite embeddings. No cyclic lifting theorem is imported.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
section Simplex
variable {V W U : Type*} [Fintype V] [Fintype W] [Fintype U]

def finsetOrderCongr (e : V ≃ W) : Finset V ≃o Finset W :=
  { e.finsetCongr with map_rel_iff' := by intro s t; exact Finset.map_subset_map }

@[simp] theorem finsetOrderCongr_apply (e : V ≃ W) (s : Finset V) :
    finsetOrderCongr e s = s.map e.toEmbedding := rfl

@[simp] theorem finsetOrderCongr_refl : finsetOrderCongr (Equiv.refl V) = OrderIso.refl _ := by
  ext s
  simp

theorem finsetOrderCongr_trans (e : V ≃ W) (f : W ≃ U) :
    finsetOrderCongr (e.trans f) = (finsetOrderCongr e).trans (finsetOrderCongr f) := by
  apply OrderIso.ext
  funext s
  exact congrArg (fun t : Finset V ≃ Finset U => t s) (Equiv.finsetCongr_trans e f).symm

def simplexIntervalOrderEquiv (s : Finset V) : Set.Iic s ≃o Finset s where
  toFun t := t.val.subtype (fun v => v ∈ s)
  invFun t := ⟨t.map (Function.Embedding.subtype _), by
    intro v hv
    exact Finset.property_of_mem_map_subtype t hv⟩
  left_inv t := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun v hv => t.property hv)
  right_inv t := by
    ext v
    simp
  map_rel_iff' := by
    intro t u
    constructor
    · intro h v hv
      have hv' : (⟨v, t.property hv⟩ : s) ∈ t.val.subtype (fun v => v ∈ s) :=
        Finset.mem_subtype.mpr hv
      exact Finset.mem_subtype.mp (h hv')
    · intro h v hv
      exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hv))

theorem simplex_isSimplicialPoset : IsSimplicialPoset (Finset V) := by
  intro s
  exact ⟨Fintype.card s, ⟨(simplexIntervalOrderEquiv s).trans
    (finsetOrderCongr (Fintype.equivFin s))⟩⟩

def simplexAtomMap (s : Finset V) (v : s) : FaceVertex s :=
  ⟨{v.val}, Finset.isAtom_singleton v.val, Finset.singleton_subset_iff.mpr v.property⟩

theorem simplexAtomMap_bijective (s : Finset V) : Function.Bijective (simplexAtomMap s) := by
  constructor
  · intro v w h
    apply Subtype.ext
    have hh := congrArg (fun a : FaceVertex s => a.val) h
    exact Finset.singleton_injective hh
  · intro a
    obtain ⟨v, hv⟩ := Finset.isAtom_iff.mp a.property.1
    have hvs : v ∈ s := by
      apply a.property.2
      rw [hv]
      exact Finset.mem_singleton_self v
    refine ⟨⟨v, hvs⟩, ?_⟩
    apply Subtype.ext
    exact hv.symm

def simplexVertexEquiv (s : Finset V) : FaceVertex s ≃ s :=
  (Equiv.ofBijective (simplexAtomMap s) (simplexAtomMap_bijective s)).symm

@[simp] theorem simplexVertexEquiv_symm (s : Finset V) (v : s) :
    (simplexVertexEquiv s).symm v = simplexAtomMap s v := rfl

theorem simplex_faceRank (s : Finset V) : faceRank s = s.card := by
  rw [← card_faceVertex]
  exact (Fintype.card_congr (simplexVertexEquiv s)).trans (Fintype.card_coe s)

def simplexTopVertexEquiv : FaceVertex (Finset.univ : Finset V) ≃ V :=
  (simplexVertexEquiv Finset.univ).trans {
    toFun := Subtype.val
    invFun := fun v => ⟨v, Finset.mem_univ v⟩
    left_inv := fun v => Subtype.ext rfl
    right_inv := fun v => rfl }

theorem simplexOrderAction_one : finsetOrderCongr (1 : Equiv.Perm V) = OrderIso.refl _ :=
  finsetOrderCongr_refl

theorem simplexOrderAction_mul (e f : Equiv.Perm V) :
    finsetOrderCongr (e * f) = (finsetOrderCongr f).trans (finsetOrderCongr e) :=
  finsetOrderCongr_trans f e

@[simp] theorem finsetOrderCongr_univ (e : Equiv.Perm V) :
    finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ := by
  change Finset.univ.map e.toEmbedding = Finset.univ
  exact Finset.map_univ_equiv e

@[simp] theorem finsetOrderCongr_empty (e : Equiv.Perm V) :
    finsetOrderCongr e (∅ : Finset V) = ∅ := Finset.map_empty _

end Simplex

section Placements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

def embeddingPlacementFace (i : A ↪ V) : Finset V := Finset.univ.map i

def embeddingPlacementEquiv (i : A ↪ V) : A ≃ embeddingPlacementFace i :=
  Equiv.ofBijective (fun a => ⟨i a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
    ⟨fun a b h => i.injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp a.property
      exact ⟨b, Subtype.ext hb⟩⟩

def embeddingPlacementVertex (i : A ↪ V) : A ≃ FaceVertex (embeddingPlacementFace i) :=
  (embeddingPlacementEquiv i).trans (simplexVertexEquiv (embeddingPlacementFace i)).symm

@[simp] theorem embeddingPlacementVertex_val (i : A ↪ V) (a : A) :
    (embeddingPlacementVertex i a).val = {i a} := rfl

theorem finsetOrderCongr_symm (e : V ≃ V) :
    finsetOrderCongr e.symm = (finsetOrderCongr e).symm := rfl

end Placements
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarVandermondeTrace.lean -/
section

section
/-! # A trace-one element in a split separable power fibre

These lemmas replace the Chinese-remainder argument in Lemma 9.3. They use
the determinant expansion over an arbitrary commutative ring, including rings
with zero divisors. No freeness or splitting-algebra assertion is assumed.

For roots `x i` with invertible pairwise differences, the staircase monomial
divided by the Vandermonde determinant has permutation trace one. An
invariant linear functional therefore takes its value at one in the
factorial ideal. The final lemmas prove the required units directly from a
factorization of `X^r - 1` and invertibility of `r`.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {K O : Type*} [CommRing K] [CommRing O] [Algebra K O] {r : ℕ}

def staircaseMonomial (x : Fin r → O) : O := ∏ i, x i ^ i.val

def rootVandermonde (x : Fin r → O) : O := (Matrix.vandermonde x).det

theorem permutationSign_mul_self (σ : Equiv.Perm (Fin r)) :
    (((σ.sign : ℤ) : O) * ((σ.sign : ℤ) : O)) = 1 := by
  rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

theorem rootVandermonde_rename (x : Fin r → O)
    (ρ : Equiv.Perm (Fin r) → O →ₐ[K] O)
    (hx : ∀ σ i, ρ σ (x i) = x (σ i)) (σ : Equiv.Perm (Fin r)) :
    ρ σ (rootVandermonde x) = ((σ.sign : ℤ) : O) * rootVandermonde x := by
  unfold rootVandermonde
  rw [AlgHom.map_det]
  have he : (ρ σ).mapMatrix (Matrix.vandermonde x) =
      (Matrix.vandermonde x).submatrix σ id := by
    ext i j
    change ρ σ (x i ^ j.val) = x (σ i) ^ j.val
    rw [map_pow, hx]
  rw [he, Matrix.det_permute]

theorem rootVandermonde_isUnit (x : Fin r → O)
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) : IsUnit (rootVandermonde x) := by
  rw [rootVandermonde, Matrix.det_vandermonde, IsUnit.prod_univ_iff]
  intro i
  rw [IsUnit.prod_iff]
  intro j hj
  exact hx j i (ne_of_gt (Finset.mem_Ioi.mp hj))

/-- A determinant identity supplies an ordinary, unsigned trace-one element.
The family `ρ` need only have the stated action on roots; the proof does not
silently require an additional group-action hypothesis. -/
theorem exists_permutation_trace_one (x : Fin r → O)
    (ρ : Equiv.Perm (Fin r) → O →ₐ[K] O)
    (hx : ∀ σ i, ρ σ (x i) = x (σ i))
    (hΔ : IsUnit (rootVandermonde x)) :
    ∃ a : O, (∑ σ : Equiv.Perm (Fin r), ρ σ a) = 1 := by
  obtain ⟨u, hu⟩ := hΔ
  let a : O := (↑u⁻¹ : O) * staircaseMonomial x
  have hΔa : rootVandermonde x * a = staircaseMonomial x := by
    rw [← hu]
    simp only [a, ← mul_assoc, Units.mul_inv, one_mul]
  have hterm (σ : Equiv.Perm (Fin r)) :
      rootVandermonde x * ρ σ a =
        ((σ.sign : ℤ) : O) * ∏ i, x (σ i) ^ i.val := by
    have hh := congrArg (ρ σ) hΔa
    rw [map_mul, rootVandermonde_rename x ρ hx σ] at hh
    calc
      rootVandermonde x * ρ σ a =
          (((σ.sign : ℤ) : O) * ((σ.sign : ℤ) : O)) *
            (rootVandermonde x * ρ σ a) := by
              rw [permutationSign_mul_self, one_mul]
      _ = ((σ.sign : ℤ) : O) *
          ((((σ.sign : ℤ) : O) * rootVandermonde x) * ρ σ a) := by ring
      _ = ((σ.sign : ℤ) : O) * ρ σ (staircaseMonomial x) := congrArg _ hh
      _ = _ := by simp only [staircaseMonomial, map_prod, map_pow, hx]
  have hsum : rootVandermonde x * (∑ σ : Equiv.Perm (Fin r), ρ σ a) =
      rootVandermonde x := by
    rw [Finset.mul_sum]
    simp_rw [hterm]
    exact (Matrix.det_apply' (Matrix.vandermonde x)).symm
  refine ⟨a, ?_⟩
  calc
    (∑ σ : Equiv.Perm (Fin r), ρ σ a) =
        (↑u⁻¹ : O) * (rootVandermonde x * ∑ σ : Equiv.Perm (Fin r), ρ σ a) := by
          rw [← hu]
          simp only [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑u⁻¹ : O) * rootVandermonde x := congrArg _ hsum
    _ = 1 := by rw [← hu]; exact Units.inv_mul u

/-- Exact factorial divisibility, rather than divisibility by only the
product of the primes dividing the factorial. -/
theorem invariant_functional_factorial_dvd (x : Fin r → O)
    (ρ : Equiv.Perm (Fin r) → O →ₐ[K] O)
    (hx : ∀ σ i, ρ σ (x i) = x (σ i))
    (hΔ : IsUnit (rootVandermonde x)) (ℓ : O →ₗ[K] K)
    (hℓ : ∀ σ z, ℓ (ρ σ z) = ℓ z) : (r.factorial : K) ∣ ℓ 1 := by
  obtain ⟨a, ha⟩ := exists_permutation_trace_one x ρ hx hΔ
  refine ⟨ℓ a, ?_⟩
  calc
    ℓ 1 = ℓ (∑ σ : Equiv.Perm (Fin r), ρ σ a) := congrArg ℓ ha.symm
    _ = ∑ σ : Equiv.Perm (Fin r), ℓ (ρ σ a) := map_sum ℓ _ _
    _ = ∑ _σ : Equiv.Perm (Fin r), ℓ a := Finset.sum_congr rfl (fun σ _ => hℓ σ a)
    _ = (r.factorial : K) * ℓ a := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]

theorem splitPower_root_pow (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - (1 : Polynomial O)) (i : Fin r) : x i ^ r = 1 := by
  have he := congrArg (Polynomial.eval (x i)) hfactor
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one] at he
  have hz : (∏ j, (x i - x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (x i))
  rw [hz] at he
  exact sub_eq_zero.mp he.symm

theorem splitPower_derivative_at_root (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - (1 : Polynomial O)) (i : Fin r) :
    (∏ j ∈ Finset.univ.erase i, (x i - x j)) = (r : O) * x i ^ (r - 1) := by
  have hseparate : (∏ j, (Polynomial.X - Polynomial.C (x j))) =
      (Polynomial.X - Polynomial.C (x i)) *
        ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have he := congrArg (fun f : Polynomial O => Polynomial.eval (x i) f.derivative) hfactor
  rw [hseparate] at he
  simpa only [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
    Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_zero,
    sub_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
    sub_self, zero_mul, add_zero, one_mul, Polynomial.eval_prod] using he

theorem splitPower_pairwise_difference_isUnit (hr : 0 < r) (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - (1 : Polynomial O)) (hunit : IsUnit (r : O)) :
    ∀ i j, i ≠ j → IsUnit (x i - x j) := by
  have hroot (i : Fin r) : IsUnit (x i) :=
    (isUnit_pow_iff hr.ne').mp (by rw [splitPower_root_pow x hfactor i]; exact isUnit_one)
  intro i j hij
  have hp : IsUnit (∏ k ∈ Finset.univ.erase i, (x i - x k)) := by
    rw [splitPower_derivative_at_root x hfactor i]
    exact hunit.mul ((hroot i).pow (r - 1))
  exact IsUnit.prod_iff.mp hp j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)

theorem splitPower_invariant_functional_factorial_dvd (hr : 0 < r) (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - (1 : Polynomial O)) (hunit : IsUnit (r : O))
    (ρ : Equiv.Perm (Fin r) → O →ₐ[K] O)
    (hx : ∀ σ i, ρ σ (x i) = x (σ i))
    (ℓ : O →ₗ[K] K) (hℓ : ∀ σ z, ℓ (ρ σ z) = ℓ z) :
    (r.factorial : K) ∣ ℓ 1 :=
  invariant_functional_factorial_dvd x ρ hx
    (rootVandermonde_isUnit x (splitPower_pairwise_difference_isUnit hr x hfactor hunit)) ℓ hℓ

/-- The same derivative argument works for every unit constant term. This
form lets the actual parameter quotient use the simpler top value `1`. -/
theorem splitUnitPower_pairwise_difference_isUnit (hr : 0 < r)
    (c : O) (hc : IsUnit c) (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - Polynomial.C c) (hunit : IsUnit (r : O)) :
    ∀ i j, i ≠ j → IsUnit (x i - x j) := by
  have hroot (i : Fin r) : IsUnit (x i) := by
    have he := congrArg (Polynomial.eval (x i)) hfactor
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow] at he
    have hz : (∏ j, (x i - x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (x i))
    rw [hz] at he
    apply (isUnit_pow_iff hr.ne').mp
    rw [sub_eq_zero.mp he.symm]
    exact hc
  intro i j hij
  have hseparate : (∏ j, (Polynomial.X - Polynomial.C (x j))) =
      (Polynomial.X - Polynomial.C (x i)) *
        ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have he := congrArg (fun f : Polynomial O => Polynomial.eval (x i) f.derivative) hfactor
  rw [hseparate] at he
  have hd : (∏ j ∈ Finset.univ.erase i, (x i - x j)) =
      (r : O) * x i ^ (r - 1) := by
    simpa only [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.eval_zero,
      sub_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
      sub_self, zero_mul, add_zero, one_mul, Polynomial.eval_prod] using he
  have hp : IsUnit (∏ k ∈ Finset.univ.erase i, (x i - x k)) := by
    rw [hd]
    exact hunit.mul ((hroot i).pow (r - 1))
  exact IsUnit.prod_iff.mp hp j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)

theorem splitUnitPower_invariant_functional_factorial_dvd (hr : 0 < r)
    (c : O) (hc : IsUnit c) (x : Fin r → O)
    (hfactor : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      Polynomial.X ^ r - Polynomial.C c) (hunit : IsUnit (r : O))
    (ρ : Equiv.Perm (Fin r) → O →ₐ[K] O)
    (hx : ∀ σ i, ρ σ (x i) = x (σ i))
    (ℓ : O →ₗ[K] K) (hℓ : ∀ σ z, ℓ (ρ σ z) = ℓ z) :
    (r.factorial : K) ∣ ℓ 1 :=
  invariant_functional_factorial_dvd x ρ hx
    (rootVandermonde_isUnit x
      (splitUnitPower_pairwise_difference_isUnit hr c hc x hfactor hunit)) ℓ hℓ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarPowerFiber.lean -/
section

section
/-! # The actual elementary-symmetric fibre for the scalar obstruction

The lower elementary symmetric parameters are set to zero and the top one
to one. Thus the negative coordinate roots factor `T^r + 1`. This harmless
choice of unit constant term avoids signs in the parameter character.

Every invariant parameter-eigenfunctional on the original polynomial ring
descends to this literal ideal quotient. The Vandermonde trace-one identity
then proves exact factorial divisibility, without a freeness assumption on
the quotient and without any hypothesis on nilpotents in the coefficient
ring.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

section LinearDescent
variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Elements annihilated by a functional after every ring multiplication. -/
def functionalMultiplicationAnnihilator (ℓ : R →ₗ[K] K) : Ideal R where
  carrier := {a | ∀ x, ℓ (a * x) = 0}
  zero_mem' x := by rw [zero_mul, map_zero]
  add_mem' ha hb x := by rw [add_mul, map_add, ha x, hb x, add_zero]
  smul_mem' r a ha x := by
    change ℓ ((r * a) * x) = 0
    simpa only [mul_assoc, mul_left_comm] using ha (r * x)

theorem ideal_le_functional_kernel (I : Ideal R) (ℓ : R →ₗ[K] K)
    (hI : I ≤ functionalMultiplicationAnnihilator ℓ) :
    I.restrictScalars K ≤ LinearMap.ker ℓ := by
  intro x hx
  change ℓ x = 0
  simpa only [mul_one] using hI hx 1

def descendFunctional (I : Ideal R) (ℓ : R →ₗ[K] K)
    (hI : I ≤ functionalMultiplicationAnnihilator ℓ) : (R ⧸ I) →ₗ[K] K :=
  ((I.restrictScalars K).liftQ ℓ (ideal_le_functional_kernel I ℓ hI)).comp
    (Submodule.Quotient.restrictScalarsEquiv K I).symm.toLinearMap

@[simp] theorem descendFunctional_mk (I : Ideal R) (ℓ : R →ₗ[K] K)
    (hI : I ≤ functionalMultiplicationAnnihilator ℓ) (x : R) :
    descendFunctional I ℓ hI (Ideal.Quotient.mk I x) = ℓ x := rfl

end LinearDescent

variable (r : ℕ) (K : Type*) [CommRing K]

def scalarPowerValue (n : ℕ) : K := if n = r then 1 else 0

def scalarPowerIdeal : Ideal (MvPolynomial (Fin r) K) :=
  Ideal.span (Set.range (fun i : Fin r => MvPolynomial.esymm (Fin r) K (i.val + 1) -
    MvPolynomial.C (scalarPowerValue r K (i.val + 1))))

abbrev ScalarPowerFiber := MvPolynomial (Fin r) K ⧸ scalarPowerIdeal r K

def scalarPowerQuotient : MvPolynomial (Fin r) K →ₐ[K] ScalarPowerFiber r K :=
  Ideal.Quotient.mkₐ K (scalarPowerIdeal r K)

theorem scalarPowerQuotient_esymm (n : ℕ) (hn : 0 < n) (hnr : n ≤ r) :
    scalarPowerQuotient r K (MvPolynomial.esymm (Fin r) K n) =
      algebraMap K (ScalarPowerFiber r K) (scalarPowerValue r K n) := by
  let i : Fin r := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hz : scalarPowerQuotient r K (MvPolynomial.esymm (Fin r) K (i.val + 1) -
      MvPolynomial.C (scalarPowerValue r K (i.val + 1))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [map_sub, sub_eq_zero, hi] at hz
  exact hz

def scalarPowerRoot (i : Fin r) : ScalarPowerFiber r K :=
  -scalarPowerQuotient r K (MvPolynomial.X i)

/-- Vieta's identity in the genuine parameter quotient. -/
theorem scalarPowerRoot_factorization (hr : 0 < r) :
    (∏ i, (Polynomial.X - Polynomial.C (scalarPowerRoot r K i))) =
      Polynomial.X ^ r - Polynomial.C (-1 : ScalarPowerFiber r K) := by
  let q := scalarPowerQuotient r K
  have hv := congrArg (Polynomial.mapRingHom q.toRingHom)
    (MvPolynomial.prod_C_add_X_eq_sum_esymm K (Fin r))
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Fintype.card_fin, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hv
  change (∏ i, (Polynomial.X - Polynomial.C (-q (MvPolynomial.X i)))) = _
  simp only [map_neg, sub_neg_eq_add]
  rw [hv]
  have hzero : 0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.succ_pos r)
  rw [← Finset.add_sum_erase _ _ hzero]
  rw [MvPolynomial.esymm_zero, map_one, Polynomial.C_1, one_mul, Nat.sub_zero]
  have htail : (∑ j ∈ (Finset.range (r + 1)).erase 0,
      Polynomial.C (q (MvPolynomial.esymm (Fin r) K j)) * Polynomial.X ^ (r - j)) = 1 := by
    rw [Finset.sum_eq_single r]
    · rw [scalarPowerQuotient_esymm r K r hr (le_refl r)]
      simp [scalarPowerValue]
    · intro j hj hjr
      have hmem := Finset.mem_erase.mp hj
      have hjpos : 0 < j := Nat.pos_of_ne_zero hmem.1
      have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.2)
      rw [scalarPowerQuotient_esymm r K j hjpos hjle]
      simp only [scalarPowerValue, if_neg hjr, map_zero, Polynomial.C_0, zero_mul]
    · intro hn
      exact False.elim (hn (Finset.mem_erase.mpr
        ⟨hr.ne', Finset.mem_range.mpr (Nat.lt_succ_self r)⟩))
  rw [htail]

def scalarPowerPermutation (σ : Equiv.Perm (Fin r)) :
    ScalarPowerFiber r K →ₐ[K] ScalarPowerFiber r K := by
  let f := (scalarPowerQuotient r K).comp (MvPolynomial.rename σ)
  apply Ideal.Quotient.liftₐ (scalarPowerIdeal r K) f
  have hI : scalarPowerIdeal r K ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change scalarPowerQuotient r K (MvPolynomial.rename σ
      (MvPolynomial.esymm (Fin r) K (i.val + 1) -
        MvPolynomial.C (scalarPowerValue r K (i.val + 1)))) = 0
    rw [map_sub, MvPolynomial.rename_esymm (σ := Fin r) (R := K) (i.val + 1) σ,
      MvPolynomial.rename_C, map_sub,
      scalarPowerQuotient_esymm r K (i.val + 1) (Nat.succ_pos _) (by omega)]
    exact sub_self _
  exact fun f hf => hI hf

@[simp] theorem scalarPowerPermutation_mk (σ : Equiv.Perm (Fin r))
    (f : MvPolynomial (Fin r) K) :
    scalarPowerPermutation r K σ (scalarPowerQuotient r K f) =
      scalarPowerQuotient r K (MvPolynomial.rename σ f) := rfl

theorem scalarPowerPermutation_root (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    scalarPowerPermutation r K σ (scalarPowerRoot r K i) = scalarPowerRoot r K (σ i) := by
  rw [scalarPowerRoot, map_neg, scalarPowerPermutation_mk, MvPolynomial.rename_X]
  rfl

theorem scalarPowerIdeal_le_annihilator (ℓ : MvPolynomial (Fin r) K →ₗ[K] K)
    (hparam : ∀ (i : Fin r) f,
      ℓ (MvPolynomial.esymm (Fin r) K (i.val + 1) * f) =
        scalarPowerValue r K (i.val + 1) * ℓ f) :
    scalarPowerIdeal r K ≤ functionalMultiplicationAnnihilator ℓ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  intro f
  change ℓ ((MvPolynomial.esymm (Fin r) K (i.val + 1) -
    MvPolynomial.C (scalarPowerValue r K (i.val + 1))) * f) = 0
  rw [sub_mul, map_sub, hparam]
  have hc : ℓ (MvPolynomial.C (scalarPowerValue r K (i.val + 1)) * f) =
      scalarPowerValue r K (i.val + 1) * ℓ f := by
    rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
  rw [hc, sub_self]

/-- The full factorial divisor for an invariant eigenfunctional on the
original polynomial ring. All quotient dependencies are constructed here. -/
theorem scalarPower_functional_factorial_dvd (hr : 0 < r) (hu : IsUnit (r : K))
    (ℓ : MvPolynomial (Fin r) K →ₗ[K] K)
    (hparam : ∀ (i : Fin r) f,
      ℓ (MvPolynomial.esymm (Fin r) K (i.val + 1) * f) =
        scalarPowerValue r K (i.val + 1) * ℓ f)
    (hinv : ∀ (σ : Equiv.Perm (Fin r)) f, ℓ (MvPolynomial.rename σ f) = ℓ f) :
    (r.factorial : K) ∣ ℓ 1 := by
  let hI := scalarPowerIdeal_le_annihilator r K ℓ hparam
  let L := descendFunctional (scalarPowerIdeal r K) ℓ hI
  have hL : ∀ (σ : Equiv.Perm (Fin r)) z,
      L (scalarPowerPermutation r K σ z) = L z := by
    intro σ z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    change ℓ (MvPolynomial.rename σ f) = ℓ f
    exact hinv σ f
  have hu' : IsUnit (r : ScalarPowerFiber r K) := by
    simpa only [map_natCast] using hu.map (algebraMap K (ScalarPowerFiber r K))
  have hd := splitUnitPower_invariant_functional_factorial_dvd hr (-1 : ScalarPowerFiber r K)
    (isUnit_neg_one (α := ScalarPowerFiber r K))
    (scalarPowerRoot r K) (scalarPowerRoot_factorization r K hr) hu'
    (scalarPowerPermutation r K) (scalarPowerPermutation_root r K) L hL
  exact hd

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarLocalizationGlue.lean -/
section

section
/-! # Exact ideal membership from two coprime localizations

The conclusion is ideal membership over the original arbitrary commutative
ring. It does not assume that the ring is reduced, noetherian, or a domain.
This is the local-to-global algebra used in the necessity of Theorem 9.4.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

variable {K : Type*} [CommRing K]

theorem ideal_mem_of_coprime_power_multiples (I : Ideal K) (a b x : K)
    (hab : IsCoprime a b) (m n : ℕ)
    (ha : a ^ m * x ∈ I) (hb : b ^ n * x ∈ I) : x ∈ I := by
  obtain ⟨u, v, huv⟩ := hab.pow (m := m) (n := n)
  have hm := I.add_mem (I.mul_mem_left u ha) (I.mul_mem_left v hb)
  have he : u * (a ^ m * x) + v * (b ^ n * x) = x := by
    calc
      _ = (u * a ^ m + v * b ^ n) * x := by ring
      _ = x := by rw [huv, one_mul]
  exact he ▸ hm

theorem ideal_mem_of_two_away_localizations (I : Ideal K) (a b x : K)
    (hab : IsCoprime a b)
    (ha : algebraMap K (Localization.Away a) x ∈
      I.map (algebraMap K (Localization.Away a)))
    (hb : algebraMap K (Localization.Away b) x ∈
      I.map (algebraMap K (Localization.Away b))) : x ∈ I := by
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers a) (Localization.Away a) I x).mp ha
  obtain ⟨t, ht, htb⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers b) (Localization.Away b) I x).mp hb
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff s a).mp hs
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff t b).mp ht
  exact ideal_mem_of_coprime_power_multiples I a b x hab m n hsa htb

theorem factorial_ideal_mem_of_two_localizations (d : ℕ) (hd : 1 ≤ d) (C : K)
    (h₁ : algebraMap K (Localization.Away (d : K)) C ∈
      (Ideal.span {((d - 1).factorial : K)}).map
        (algebraMap K (Localization.Away (d : K))))
    (h₂ : algebraMap K (Localization.Away ((d - 1 : ℕ) : K)) C ∈
      (Ideal.span {((d - 1).factorial : K)}).map
        (algebraMap K (Localization.Away ((d - 1 : ℕ) : K)))) :
    C ∈ Ideal.span {((d - 1).factorial : K)} := by
  apply ideal_mem_of_two_away_localizations _ (d : K) ((d - 1 : ℕ) : K) C _ h₁ h₂
  refine ⟨1, -1, ?_⟩
  have hc : (((d - 1 : ℕ) : K) + 1) = (d : K) := by
    have h := congrArg (fun n : ℕ => (n : K)) (Nat.sub_add_cancel hd)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [one_mul, neg_one_mul, ← hc]
  ring

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarFunctionalExtension.lean -/
section

section
/-! # Coefficient extension of the actual scalar obstruction functional

Only a linear functional on the polynomial ring must be extended to a
localization. Its extension is defined on the genuine monomial basis.
Parameter and permutation identities are checked on that basis, so this
argument does not require a flatness assertion for a comparison module.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical MvPolynomial

section Extension
variable {V K : Type*} [CommRing K] (L : Type*) [CommRing L] [Algebra K L]

def extendPolynomialFunctional (ℓ : MvPolynomial V K →ₗ[K] K) :
    MvPolynomial V L →ₗ[L] L :=
  (MvPolynomial.basisMonomials V L).constr L
    (fun a => algebraMap K L (ℓ (MvPolynomial.monomial a 1)))

@[simp] theorem extendPolynomialFunctional_monomial
    (ℓ : MvPolynomial V K →ₗ[K] K) (a : V →₀ ℕ) :
    extendPolynomialFunctional L ℓ (MvPolynomial.monomial a 1) =
      algebraMap K L (ℓ (MvPolynomial.monomial a 1)) :=
  Module.Basis.constr_basis _ _ _ _

theorem extendPolynomialFunctional_map (ℓ : MvPolynomial V K →ₗ[K] K)
    (f : MvPolynomial V K) :
    extendPolynomialFunctional L ℓ (MvPolynomial.map (algebraMap K L) f) =
      algebraMap K L (ℓ f) := by
  have he : ((extendPolynomialFunctional L ℓ).restrictScalars K).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId K L)).toLinearMap =
      (Algebra.linearMap K L).comp ℓ := by
    apply (MvPolynomial.basisMonomials V K).ext
    intro a
    change extendPolynomialFunctional L ℓ
      (MvPolynomial.map (algebraMap K L) (MvPolynomial.monomial a 1)) =
        algebraMap K L (ℓ (MvPolynomial.monomial a 1))
    rw [MvPolynomial.map_monomial, map_one (algebraMap K L), extendPolynomialFunctional_monomial]
  exact DFunLike.congr_fun he f

@[simp] theorem extendPolynomialFunctional_one (ℓ : MvPolynomial V K →ₗ[K] K) :
    extendPolynomialFunctional L ℓ 1 = algebraMap K L (ℓ 1) := by
  simpa only [map_one] using extendPolynomialFunctional_map L ℓ 1

theorem extendPolynomialFunctional_parameter [Fintype V]
    (ℓ : MvPolynomial V K →ₗ[K] K) (n : ℕ) (c : K)
    (hparam : ∀ f, ℓ (MvPolynomial.esymm V K n * f) = c * ℓ f) :
    ∀ f, extendPolynomialFunctional L ℓ (MvPolynomial.esymm V L n * f) =
      algebraMap K L c * extendPolynomialFunctional L ℓ f := by
  have hm (a : V →₀ ℕ) : extendPolynomialFunctional L ℓ
      (MvPolynomial.esymm V L n * MvPolynomial.monomial a 1) =
        algebraMap K L c * extendPolynomialFunctional L ℓ (MvPolynomial.monomial a 1) := by
    calc
      _ = extendPolynomialFunctional L ℓ (MvPolynomial.map (algebraMap K L)
          (MvPolynomial.esymm V K n * MvPolynomial.monomial a 1)) := by
        rw [map_mul (MvPolynomial.map (algebraMap K L)), MvPolynomial.map_esymm,
          MvPolynomial.map_monomial, map_one (algebraMap K L)]
      _ = algebraMap K L (ℓ (MvPolynomial.esymm V K n * MvPolynomial.monomial a 1)) :=
        extendPolynomialFunctional_map L ℓ _
      _ = algebraMap K L (c * ℓ (MvPolynomial.monomial a 1)) :=
        congrArg (algebraMap K L) (hparam _)
      _ = _ := by
        rw [map_mul (algebraMap K L), extendPolynomialFunctional_monomial]
  have he : (extendPolynomialFunctional L ℓ).comp
      (LinearMap.mulLeft L (MvPolynomial.esymm V L n)) =
      (LinearMap.mulLeft L (algebraMap K L c)).comp (extendPolynomialFunctional L ℓ) := by
    apply (MvPolynomial.basisMonomials V L).ext
    intro a
    simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      MvPolynomial.coe_basisMonomials] using hm a
  intro f
  exact DFunLike.congr_fun he f

theorem extendPolynomialFunctional_invariant (ℓ : MvPolynomial V K →ₗ[K] K)
    (hinv : ∀ (σ : Equiv.Perm V) f, ℓ (MvPolynomial.rename σ f) = ℓ f) :
    ∀ (σ : Equiv.Perm V) f,
      extendPolynomialFunctional L ℓ (MvPolynomial.rename σ f) =
        extendPolynomialFunctional L ℓ f := by
  intro σ
  have he : (extendPolynomialFunctional L ℓ).comp (MvPolynomial.rename σ).toLinearMap =
      extendPolynomialFunctional L ℓ := by
    apply (MvPolynomial.basisMonomials V L).ext
    intro a
    change extendPolynomialFunctional L ℓ
      (MvPolynomial.rename σ (MvPolynomial.monomial a 1)) =
        extendPolynomialFunctional L ℓ (MvPolynomial.monomial a 1)
    have hm : (MvPolynomial.monomial a 1 : MvPolynomial V L) =
        MvPolynomial.map (algebraMap K L) (MvPolynomial.monomial a 1) := by
      rw [MvPolynomial.map_monomial, map_one (algebraMap K L)]
    rw [hm, ← MvPolynomial.map_rename, extendPolynomialFunctional_map,
      extendPolynomialFunctional_map, hinv]
  intro f
  exact DFunLike.congr_fun he f

end Extension

variable {K : Type*} [CommRing K]

/-- This is a functional on the actual polynomial ring, with the explicit
top-unit character and literal permutation action. -/
structure ScalarPowerFunctional (r : ℕ) (C : K) where
  functional : MvPolynomial (Fin r) K →ₗ[K] K
  value_one : functional 1 = C
  parameter : ∀ (i : Fin r) f,
    functional (MvPolynomial.esymm (Fin r) K (i.val + 1) * f) =
      scalarPowerValue r K (i.val + 1) * functional f
  invariant : ∀ (σ : Equiv.Perm (Fin r)) f,
    functional (MvPolynomial.rename σ f) = functional f

def ScalarPowerFunctional.extend (L : Type*) [CommRing L] [Algebra K L]
    {r : ℕ} {C : K} (F : ScalarPowerFunctional r C) :
    ScalarPowerFunctional r (algebraMap K L C) where
  functional := extendPolynomialFunctional L F.functional
  value_one := by rw [extendPolynomialFunctional_one, F.value_one]
  parameter i f := by
    have he := extendPolynomialFunctional_parameter L F.functional (i.val + 1)
      (scalarPowerValue r K (i.val + 1)) (F.parameter i) f
    simpa only [scalarPowerValue, apply_ite, map_one, map_zero] using he
  invariant := extendPolynomialFunctional_invariant L F.functional F.invariant

theorem ScalarPowerFunctional.factorial_dvd {r : ℕ} {C : K}
    (F : ScalarPowerFunctional r C) (hr : 0 < r) (hu : IsUnit (r : K)) :
    (r.factorial : K) ∣ C := by
  rw [← F.value_one]
  exact scalarPower_functional_factorial_dvd r K hr hu F.functional F.parameter F.invariant

/-- The local-to-global necessity in Theorem 9.4, with both actual
rank-functionals as explicit inputs. Their extraction from a coherent
`R → B` family is a separate, directional bridge. -/
theorem scalarPower_two_ranks_factorial_dvd (d : ℕ) (hd : 2 ≤ d) (C : K)
    (Ftop : ScalarPowerFunctional d C) (Ffacet : ScalarPowerFunctional (d - 1) C) :
    ((d - 1).factorial : K) ∣ C := by
  apply Ideal.mem_span_singleton.mp
  apply factorial_ideal_mem_of_two_localizations d (by omega) C
  · let L := Localization.Away (d : K)
    have hu : IsUnit (d : L) := by
      simpa only [map_natCast] using
        (IsLocalization.Away.algebraMap_isUnit (S := L) (d : K))
    have hD : ((d - 1).factorial : L) ∣ (d.factorial : L) := by
      exact map_dvd (Nat.castRingHom L)
        (Nat.factorial_dvd_factorial (show d - 1 ≤ d by omega))
    have hlocal := hD.trans ((Ftop.extend L).factorial_dvd (by omega) hu)
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.mem_span_singleton] using hlocal
  · let L := Localization.Away ((d - 1 : ℕ) : K)
    have hu : IsUnit ((d - 1 : ℕ) : L) := by
      simpa only [map_natCast] using
        (IsLocalization.Away.algebraMap_isUnit (S := L) ((d - 1 : ℕ) : K))
    have hlocal := (Ffacet.extend L).factorial_dvd (by omega) hu
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.mem_span_singleton] using hlocal

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarMapDivisibility.lean -/
section

section
/-! # Lemma 9.3 for the actual polynomial and barycentric rings

The direction is the paper's direction: polynomial ring to barycentric
ring. Composition with the genuine top-face evaluation produces the
eigenfunctional used in the scalar obstruction. The proof even dispenses
with the grading assumption once the scalar value at one is specified.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical MvPolynomial

section TopEvaluation
variable {V K : Type*} [Fintype V] [Nonempty V] [CommRing K]

def booleanTopScalarPolynomialEvaluation : MvPolynomial (BooleanFace V) K →ₐ[K] K :=
  MvPolynomial.aeval (fun F => if F = booleanTopFace then 1 else 0)

theorem booleanTopScalarPolynomialEvaluation_forbidden
    (a : BooleanFace V →₀ ℕ) (ha : ¬ IsChainExponent a) :
    booleanTopScalarPolynomialEvaluation (K := K) (MvPolynomial.monomial a 1) = 0 := by
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
  rw [booleanTopScalarPolynomialEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul]
  apply Finset.prod_eq_zero hF
  change (if F = booleanTopFace then (1 : K) else 0) ^ a F = 0
  rw [if_neg hFt, zero_pow (Finsupp.mem_support_iff.mp hF)]

/-- Literal quotient evaluation sending the top face to one and every
proper nonempty face to zero. -/
def booleanTopScalarEvaluation : BooleanBarycentricRing V K →ₐ[K] K :=
  Ideal.Quotient.liftₐ (forbiddenIdeal IsChainExponent) booleanTopScalarPolynomialEvaluation (by
    have hi : forbiddenIdeal (K := K) (IsChainExponent (V := V)) ≤
        RingHom.ker booleanTopScalarPolynomialEvaluation.toRingHom := by
      rw [forbiddenIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact booleanTopScalarPolynomialEvaluation_forbidden a ha
    exact fun f hf => hi hf)

@[simp] theorem booleanTopScalarEvaluation_face (F : BooleanFace V) :
    booleanTopScalarEvaluation (K := K) (faceVariable F) =
      if F = booleanTopFace then 1 else 0 := by
  change booleanTopScalarPolynomialEvaluation (MvPolynomial.X F) = _
  exact MvPolynomial.aeval_X _ _

theorem booleanTopScalarEvaluation_rankParameter (n : ℕ) :
    booleanTopScalarEvaluation (V := V) (K := K) (booleanRankParameter n) =
      if n = Fintype.card V then 1 else 0 := by
  rw [booleanRankParameter, map_sum]
  rw [Finset.sum_eq_single (booleanTopFace (V := V))]
  · by_cases h : n = Fintype.card V <;> simp [h, eq_comm]
  · intro F hF hFt
    by_cases hcard : F.val.card = n <;> simp [hcard, hFt]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem booleanTopScalarEvaluation_permutation (σ : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanTopScalarEvaluation (booleanVertexRelabelEquiv σ x) =
      booleanTopScalarEvaluation x := by
  have htop : booleanFaceEmbedding σ.toEmbedding (booleanTopFace (V := V)) = booleanTopFace := by
    apply Subtype.ext
    exact Finset.map_univ_equiv σ
  have h : ((booleanTopScalarEvaluation (V := V) (K := K)).comp
      (booleanVertexRelabelEquiv σ).toAlgHom).comp
        (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) =
      (booleanTopScalarEvaluation (V := V) (K := K)).comp
        (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) := by
    apply MvPolynomial.algHom_ext
    intro F
    change booleanTopScalarEvaluation (booleanVertexRelabelEquiv σ (faceVariable F)) =
      booleanTopScalarEvaluation (faceVariable F)
    rw [booleanVertexRelabelEquiv_face, booleanTopScalarEvaluation_face,
      booleanTopScalarEvaluation_face]
    have ht : booleanFaceEmbedding σ.toEmbedding F = booleanTopFace ↔ F = booleanTopFace := by
      constructor
      · intro h
        exact (booleanFaceEmbedding σ.toEmbedding).injective (h.trans htop.symm)
      · rintro rfl
        exact htop
    simp only [ht]
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

end TopEvaluation

variable (r : ℕ) (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq (Fin r) := Classical.decEq _

/-- Extract the actual invariant eigenfunctional from an `R → B` map.
No inverse map and no extra normalization are assumed. -/
def scalarPowerFunctionalOfMap (hr : 0 < r) (C : K)
    (f : MvPolynomial (Fin r) K →ₗ[K] BooleanBarycentricRing (Fin r) K)
    (hparam : ∀ (i : Fin r) x,
      f (MvPolynomial.esymm (Fin r) K (i.val + 1) * x) =
        booleanRankParameter (i.val + 1) * f x)
    (hinv : ∀ (σ : Equiv.Perm (Fin r)) x,
      f (MvPolynomial.rename σ x) = booleanVertexRelabelEquiv σ (f x))
    (hone : f 1 = C • (1 : BooleanBarycentricRing (Fin r) K)) :
    ScalarPowerFunctional r C := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let E := booleanTopScalarEvaluation (V := Fin r) (K := K)
  refine ⟨E.toLinearMap.comp f, ?_, ?_, ?_⟩
  · change E (f 1) = C
    rw [hone, map_smul, map_one, smul_eq_mul, mul_one]
  · intro i x
    change E (f (MvPolynomial.esymm (Fin r) K (i.val + 1) * x)) =
      scalarPowerValue r K (i.val + 1) * E (f x)
    rw [hparam, map_mul]
    change booleanTopScalarEvaluation (booleanRankParameter (i.val + 1)) * E (f x) = _
    rw [booleanTopScalarEvaluation_rankParameter, Fintype.card_fin]
    rfl
  · intro σ x
    change E (f (MvPolynomial.rename σ x)) = E (f x)
    rw [hinv]
    exact booleanTopScalarEvaluation_permutation σ (f x)

/-- **Lemma 9.3.** This statement uses the actual simplex rings and their
actual symmetric-group actions over every commutative coefficient ring. -/
theorem lemma_9_3_factorial_divisibility (hr : 0 < r) (hu : IsUnit (r : K)) (C : K)
    (f : MvPolynomial (Fin r) K →ₗ[K] BooleanBarycentricRing (Fin r) K)
    (hparam : ∀ (i : Fin r) x,
      f (MvPolynomial.esymm (Fin r) K (i.val + 1) * x) =
        booleanRankParameter (i.val + 1) * f x)
    (hinv : ∀ (σ : Equiv.Perm (Fin r)) x,
      f (MvPolynomial.rename σ x) = booleanVertexRelabelEquiv σ (f x))
    (hone : f 1 = C • (1 : BooleanBarycentricRing (Fin r) K)) :
    (r.factorial : K) ∣ C :=
  (scalarPowerFunctionalOfMap r K hr C f hparam hinv hone).factorial_dvd hr hu

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarSimplexNecessity.lean -/
section

section
/-! # Necessity for the actual coherent scalar module

An invariant coherent family in the paper's direction `R → B` gives the
actual scalar eigenfunctional on every face of the simplex. Permutations
of a face extend to ambient permutations, so both the top-rank and facet-rank
functionals have the full symmetry required by the two-localization argument.
The scalar is shared because it was defined at the bottom face and coherence
identifies every component's value at one with it.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal.ScalarFamilies
open Classical Finset MvPolynomial

section Transport
variable {A B C K : Type*} [Fintype A] [Fintype B] [Fintype C] [CommRing K]

def reverseVertexTransport
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B) :
    MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K :=
  (booleanVertexRelabelEquiv e.symm).toLinearMap.comp
    (f.comp (MvPolynomial.rename e).toLinearMap)

@[simp] theorem reverseVertexTransport_apply
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (x : MvPolynomial A K) :
    reverseVertexTransport f e x = booleanVertexRelabelEquiv e.symm (f (rename e x)) := rfl

theorem reverseVertexTransport_trans
    (f : MvPolynomial C K →ₗ[K] BooleanBarycentricRing C K) (e : A ≃ B) (g : B ≃ C) :
    reverseVertexTransport (reverseVertexTransport f g) e =
      reverseVertexTransport f (e.trans g) := by
  apply LinearMap.ext
  intro x
  simp only [reverseVertexTransport_apply, rename_rename,
    ← booleanVertexRelabelEquiv_trans]
  rfl

theorem reverseVertexTransport_of_intertwines
    (f : MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K)
    (g : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (h : ∀ x, g (rename e x) = booleanVertexRelabelEquiv e (f x)) :
    reverseVertexTransport g e = f := by
  apply LinearMap.ext
  intro x
  rw [reverseVertexTransport_apply, h]
  exact (booleanVertexRelabelEquiv e).symm_apply_apply (f x)

theorem reverseVertexTransport_parameter
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (hf : ∀ r x, f (esymm B K (r + 1) * x) = booleanRankParameter (r + 1) * f x)
    (r : ℕ) (x : MvPolynomial A K) :
    reverseVertexTransport f e (esymm A K (r + 1) * x) =
      booleanRankParameter (r + 1) * reverseVertexTransport f e x := by
  rw [reverseVertexTransport_apply, map_mul, MvPolynomial.rename_esymm,
    hf, map_mul, booleanVertexRelabelEquiv_parameter]
  rfl

theorem reverseVertexTransport_scalar
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (c : K) (hf : f 1 = c • 1) : reverseVertexTransport f e 1 = c • 1 := by
  rw [reverseVertexTransport_apply, map_one, hf, map_smul, map_one]

theorem reverseVertexTransport_fixed_iff
    (f : MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K) (e : Equiv.Perm A) :
    reverseVertexTransport f e = f ↔
      ∀ x, f (rename e x) = booleanVertexRelabelEquiv e (f x) := by
  constructor
  · intro h x
    have hh := LinearMap.congr_fun h x
    have ht := congrArg (booleanVertexRelabelEquiv e) hh
    change booleanVertexRelabelEquiv e
      ((booleanVertexRelabelEquiv e).symm (f (rename e x))) = _ at ht
    rwa [AlgEquiv.apply_symm_apply] at ht
  · intro h
    apply LinearMap.ext
    intro x
    rw [reverseVertexTransport_apply, h]
    exact (booleanVertexRelabelEquiv e).symm_apply_apply (f x)

end Transport

section Stalks
variable {P A K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype A] [CommRing K]

theorem invariantFamily_natural
    (F : comparisonModule (P := P) K) (e : P ≃o P)
    (hF : relabelComparison K e.symm F = F) (p : P) (x : PolynomialStalk K p) :
    barycentricStalkOrderEquiv K e p (F.val p x) =
      F.val (e p) (polynomialStalkOrderEquiv K e p x) := by
  have h := congrArg (fun H : comparisonModule (P := P) K => H.val p x) hF
  change (barycentricStalkOrderEquiv K e p).symm
    (F.val (e p) (polynomialStalkOrderEquiv K e p x)) = F.val p x at h
  have hh := congrArg (barycentricStalkOrderEquiv K e p) h
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem reverseVertexTransport_stalk_order
    (F : comparisonModule (P := P) K) (e : P ≃o P)
    (hF : relabelComparison K e.symm F = F) (p q : P)
    (a : A ≃ FaceVertex p) (b : A ≃ FaceVertex q)
    (hq : q = e p) (hb : ∀ x, (b x).val = e (a x).val) :
    reverseVertexTransport (F.val q) b = reverseVertexTransport (F.val p) a := by
  subst q
  have he : b = a.trans (faceVertexOrderEquiv e p) := by
    apply Equiv.ext
    intro x
    exact Subtype.ext (hb x)
  rw [he, ← reverseVertexTransport_trans]
  congr 1
  exact reverseVertexTransport_of_intertwines (F.val p) (F.val (e p))
    (faceVertexOrderEquiv e p) (fun x => (invariantFamily_natural F e hF p x).symm)

end Stalks

section Simplex
variable {V K : Type*} [Fintype V] [CommRing K]

def embeddedScalarMap (F : comparisonModule (P := Finset V) K)
    {A : Type*} [Fintype A] (i : A ↪ V) :
    MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K :=
  reverseVertexTransport (F.val (embeddingPlacementFace i)) (embeddingPlacementVertex i)

theorem embeddedScalarMap_independent (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    {A : Type*} [Fintype A] (i j : A ↪ V) :
    embeddedScalarMap F i = embeddedScalarMap F j := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair i j i.injective j.injective
  have he : i.trans σ.toEmbedding = j := Function.Embedding.ext hσ
  have hs : embeddingPlacementFace j = finsetOrderCongr σ (embeddingPlacementFace i) := by
    simp only [embeddingPlacementFace, finsetOrderCongr_apply, Finset.map_map, he]
  have hfixed : relabelComparison K (finsetOrderCongr σ).symm F = F := by
    rw [← finsetOrderCongr_symm]
    exact hF σ.symm
  symm
  apply reverseVertexTransport_stalk_order F (finsetOrderCongr σ) hfixed
    (embeddingPlacementFace i) (embeddingPlacementFace j)
    (embeddingPlacementVertex i) (embeddingPlacementVertex j) hs
  intro a
  simp only [embeddingPlacementVertex_val, finsetOrderCongr_apply,
    Finset.map_singleton, Equiv.coe_toEmbedding, hσ]

theorem embeddedScalarMap_permutation (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    {A : Type*} [Fintype A] (i : A ↪ V) (σ : Equiv.Perm A) (x : MvPolynomial A K) :
    embeddedScalarMap F i (rename σ x) =
      booleanVertexRelabelEquiv σ (embeddedScalarMap F i x) := by
  have hface : embeddingPlacementFace (σ.toEmbedding.trans i) = embeddingPlacementFace i := by
    simp only [embeddingPlacementFace, ← Finset.map_map, Finset.map_univ_equiv]
  have hfixed : relabelComparison K (OrderIso.refl (Finset V)).symm F = F := by
    apply Subtype.ext
    exact relabel_refl K F.val
  have he : embeddedScalarMap F (σ.toEmbedding.trans i) =
      reverseVertexTransport (embeddedScalarMap F i) σ := by
    calc
      _ = reverseVertexTransport (F.val (embeddingPlacementFace i))
          (σ.trans (embeddingPlacementVertex i)) := by
        apply reverseVertexTransport_stalk_order F (OrderIso.refl (Finset V)) hfixed
          (embeddingPlacementFace i) (embeddingPlacementFace (σ.toEmbedding.trans i))
          (σ.trans (embeddingPlacementVertex i))
          (embeddingPlacementVertex (σ.toEmbedding.trans i)) hface
        intro a
        simp only [embeddingPlacementVertex_val, Equiv.trans_apply]
        rfl
      _ = _ := (reverseVertexTransport_trans _ σ (embeddingPlacementVertex i)).symm
  have hh : reverseVertexTransport (embeddedScalarMap F i) σ = embeddedScalarMap F i := by
    rw [← he]
    exact embeddedScalarMap_independent F hF _ _
  exact (reverseVertexTransport_fixed_iff (embeddedScalarMap F i) σ).mp hh x

/-- The scalar functional on an arbitrary positive-rank face, in the exact
polynomial variables `Fin r` used by the verified splitting argument. -/
def scalarFunctionalAtRank (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (r : ℕ) (hr : 0 < r) (hcard : r ≤ Fintype.card V) :
    ScalarPowerFunctional r (scalar K F) := by
  let i : Fin r ↪ V := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hcard))
  apply scalarPowerFunctionalOfMap r K hr (scalar K F) (embeddedScalarMap F i)
  · intro j x
    exact reverseVertexTransport_parameter _ _
      (fun r x => F.property.2.1 (embeddingPlacementFace i) r x) j.val x
  · intro σ x
    exact embeddedScalarMap_permutation F hF i σ x
  · exact reverseVertexTransport_scalar _ _ (scalar K F)
      (component_one K F (embeddingPlacementFace i))

/-- The necessary ideal inclusion in Theorem 9.4 for the actual invariant
coherent scalar module over an arbitrary commutative ring. -/
theorem scalar_factorial_dvd (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) :
    ((Fintype.card V - 1).factorial : K) ∣ scalar K F := by
  by_cases h : 2 ≤ Fintype.card V
  · exact scalarPower_two_ranks_factorial_dvd (Fintype.card V) h (scalar K F)
      (scalarFunctionalAtRank F hF _ (by omega) le_rfl)
      (scalarFunctionalAtRank F hF _ (by omega) (Nat.sub_le _ _))
  · have he : Fintype.card V - 1 = 0 := by omega
    rw [he, Nat.factorial_zero, Nat.cast_one]
    exact one_dvd _

end Simplex
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/FactorialTraceArithmetic.lean -/
section

section
/-! # The exact factorial in the prime-power transfer argument

For each prime divisor of `d`, use its largest power dividing `d`.  The
indices `d! / p^(v_p(d))` have an integral Bezout combination equal to
`(d-1)!`.  This is the arithmetic part of the scalar construction; it does
not assume or prove the existence of any cyclic comparison template.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

theorem primePowerComplement_product (d p : ℕ) (hd : d ≠ 0)
    (hp : p ∈ d.primeFactors) :
    ∏ q ∈ d.primeFactors \ {p}, q ^ d.factorization q = d / p ^ d.factorization p := by
  apply Nat.eq_div_of_mul_eq_left
    (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [Finset.sdiff_singleton_eq_erase,
    Finset.prod_erase_mul _ _ hp, ← Nat.prod_primeFactors_pow_factorization hd]

theorem exists_primePowerComplement_bezout (d : ℕ) (hd : 1 < d) :
    ∃ μ : ℕ → ℤ, ∑ p ∈ d.primeFactors, μ p * (d / p ^ d.factorization p : ℕ) = 1 := by
  have hc : Pairwise (fun p q : d.primeFactors => IsCoprime
      ((p.val ^ d.factorization p.val : ℕ) : ℤ)
      ((q.val ^ d.factorization q.val : ℕ) : ℤ)) := by
    intro p q hpq
    exact (Nat.pairwise_coprime_pow_primeFactors_factorization hpq).isCoprime
  obtain ⟨μ, hμ⟩ :=
    (exists_sum_eq_one_iff_pairwise_coprime (R := ℤ)
      (s := fun p : ℕ => ((p ^ d.factorization p : ℕ) : ℤ))
      (Nat.nonempty_primeFactors.mpr hd)).mpr hc
  refine ⟨μ, ?_⟩
  calc
    _ = ∑ p ∈ d.primeFactors, μ p *
        ∏ q ∈ d.primeFactors \ {p}, ((q ^ d.factorization q : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Nat.cast_prod, primePowerComplement_product d p (by omega) hp]
    _ = 1 := hμ

theorem factorial_div_primePower (d p : ℕ) (hd : d ≠ 0) :
    d.factorial / p ^ d.factorization p =
      (d - 1).factorial * (d / p ^ d.factorization p) := by
  rw [← Nat.mul_factorial_pred hd, mul_comm d,
    Nat.mul_div_assoc _ (Nat.ordProj_dvd d p)]

/-- The exact integer coefficients needed to combine traces from free
cyclic prime-power subgroups. -/
theorem exists_factorial_trace_coefficients (d : ℕ) (hd : 1 < d) :
    ∃ μ : ℕ → ℤ,
      ∑ p ∈ d.primeFactors, μ p * (d.factorial / p ^ d.factorization p : ℕ) =
        ((d - 1).factorial : ℤ) := by
  obtain ⟨μ, hμ⟩ := exists_primePowerComplement_bezout d hd
  refine ⟨μ, ?_⟩
  calc
    _ = ((d - 1).factorial : ℤ) *
        ∑ p ∈ d.primeFactors, μ p * (d / p ^ d.factorization p : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [factorial_div_primePower d p (by omega), Nat.cast_mul]
      ac_rfl
    _ = ((d - 1).factorial : ℤ) := by rw [hμ, mul_one]

/-- Consequently these transfer scalars generate precisely the factorial
ideal over the integers, including its prime-power multiplicities. -/
theorem factorial_trace_ideal (d : ℕ) (hd : 1 < d) :
    Ideal.span {z : ℤ | ∃ p ∈ d.primeFactors,
      z = (d.factorial / p ^ d.factorization p : ℕ)} =
        Ideal.span {((d - 1).factorial : ℤ)} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z ⟨p, hp, rfl⟩
    change ((d.factorial / p ^ d.factorization p : ℕ) : ℤ) ∈
      Ideal.span {((d - 1).factorial : ℤ)}
    rw [Ideal.mem_span_singleton]
    exact ⟨(d / p ^ d.factorization p : ℕ), by
      rw [factorial_div_primePower d p (by omega), Nat.cast_mul]⟩
  · apply Ideal.span_le.mpr
    intro z hz
    have hz' : z = ((d - 1).factorial : ℤ) := Set.mem_singleton_iff.mp hz
    subst z
    obtain ⟨μ, hμ⟩ := exists_factorial_trace_coefficients d hd
    rw [← hμ]
    apply Submodule.sum_mem
    intro p hp
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, hp, rfl⟩)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarCanonicalObstruction.lean -/
section

section
/-! # The actual comparison obstruction, without an assumed normalized lift

The initial normalized family is supplied by the proved ordinary comparison.
Its choice has no effect on the cohomology class. This is the class denoted
`o_P` in equation (5), for the actual module of coherent `R → B` families.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal.ScalarFamilies
open Classical
universe u
variable {P K G : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
  [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P)

def normalizedComparisonFamily : comparisonModule (P := P) K :=
  Classical.choose (exists_normalized_comparisonFamily K hs)

@[simp] theorem normalizedComparisonFamily_scalar :
    scalar K (normalizedComparisonFamily K hs) = 1 :=
  Classical.choose_spec (exists_normalized_comparisonFamily K hs)

variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def comparisonObstruction : groupCohomology.H1 (obstructionRepresentation K act h₁ hmul) :=
  obstruction K act h₁ hmul (normalizedComparisonFamily K hs)

theorem comparisonObstruction_eq (F : comparisonModule (P := P) K)
    (hF : scalar K F = 1) :
    comparisonObstruction K hs act h₁ hmul = obstruction K act h₁ hmul F :=
  obstruction_independent K act h₁ hmul _ F
    ((normalizedComparisonFamily_scalar K hs).trans hF.symm)

theorem comparisonObstruction_annihilator (c : K) :
    c • comparisonObstruction K hs act h₁ hmul = 0 ↔
      c ∈ invariantScalarIdeal K act h₁ hmul :=
  obstruction_annihilator K act h₁ hmul (normalizedComparisonFamily K hs)
    (normalizedComparisonFamily_scalar K hs) c

/-- Vanishing is exactly solvability of the actual invariant scalar-one
coherent graded parameter-linear equations. -/
theorem comparisonObstruction_zero_iff :
    comparisonObstruction K hs act h₁ hmul = 0 ↔
      ∃ F : comparisonModule (P := P) K,
        (∀ g, relabelComparison K (act g) F = F) ∧ scalar K F = 1 := by
  have h := comparisonObstruction_annihilator K hs act h₁ hmul (1 : K)
  rw [one_smul, scalar_mem_invariantIdeal_iff] at h
  exact h

theorem invariantFamily_annihilates (F : comparisonModule (P := P) K)
    (hF : ∀ g, relabelComparison K (act g) F = F) :
    scalar K F • comparisonObstruction K hs act h₁ hmul = 0 := by
  apply (comparisonObstruction_annihilator K hs act h₁ hmul _).mpr
  exact (scalar_mem_invariantIdeal_iff K act h₁ hmul _).mpr ⟨F, hF, rfl⟩

def comparisonObstructionSpanEquiv :
    (K ⧸ invariantScalarIdeal K act h₁ hmul) ≃ₗ[K]
      Submodule.span K {comparisonObstruction K hs act h₁ hmul} :=
  obstructionSpanEquiv K act h₁ hmul (normalizedComparisonFamily K hs)
    (normalizedComparisonFamily_scalar K hs)

end FourPapers.Universal.ScalarFamilies

end
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

/- BEGIN FourPapers/Universal/ScalarRankInduction.lean -/
section


section

/-! # Controlled equivariant induction for the actual scalar-comparison module

The local maps have the direction `R → B` used in Sections 3 and 9. An extra
predicate records any fixed-face quotient condition. Orbitwise choices preserve
this condition as well as the genuine restriction, parameter and degree laws.
The extension premise is explicit; this generic assembly theorem does not assert
the existence of a controlled local lift.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal.ScalarFamilies
open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def single (p : P) (f : PolynomialStalk K p →ₗ[K] BarycentricStalk K p) :
    Family (P := P) K := Pi.single p f

@[simp] theorem single_same (p : P)
    (f : PolynomialStalk K p →ₗ[K] BarycentricStalk K p) : single K p f p = f := by
  simp [single]

@[simp] theorem single_ne (p q : P) (h : q ≠ p)
    (f : PolynomialStalk K p →ₗ[K] BarycentricStalk K p) : single K p f q = 0 := by
  simp [single, h]

variable (Control : ∀ p : P, (PolynomialStalk K p →ₗ[K] BarycentricStalk K p) → Prop)

def LocalGood (p : P) (F : Family (P := P) K) : Prop :=
  (∀ q, q ≠ p → F q = 0) ∧ F ∈ parameterLinear K ∧ F ∈ graded K ∧
    F p 1 = 1 ∧ Control p (F p)

def LocalCompatible (p q : P) (F H : Family (P := P) K) : Prop :=
  ∀ (h : q ≤ p) x, booleanRestriction (faceVertexInclusion h) (F p x) =
    H q (polynomialRestriction K h x)

theorem single_good (p : P)
    (f : PolynomialStalk K p →ₗ[K] BarycentricStalk K p)
    (hp : ∀ r x, f (polynomialParameter K p (r + 1) * x) =
      booleanRankParameter (r + 1) * f x)
    (hd : ∀ n x, x ∈ polynomialDegreePiece n → f x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n)
    (h₁ : f 1 = 1) (hc : Control p f) : LocalGood K Control p (single K p f) := by
  refine ⟨fun q hq => single_ne K p q hq f, ?_, ?_, ?_, ?_⟩
  · intro q r x
    by_cases hq : q = p
    · subst q; simpa only [single_same] using hp r x
    · rw [single_ne K p q hq f]; simp
  · intro q n x hx
    by_cases hq : q = p
    · subst q; simpa only [single_same] using hd n x hx
    · rw [single_ne K p q hq f]
      exact (basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n).zero_mem
  · simpa only [single_same] using h₁
  · simpa only [single_same] using hc

theorem relabel_good (e : P ≃o P)
    (hcontrol : ∀ p (F : Family (P := P) K),
      Control p (F p) → Control (e p) (relabel K e F (e p)))
    (p : P) (F : Family (P := P) K) (hF : LocalGood K Control p F) :
    LocalGood K Control (e p) (relabel K e F) := by
  refine ⟨?_, relabel_parameterLinear K e F hF.2.1,
    relabel_graded K e F hF.2.2.1, ?_, hcontrol p F hF.2.2.2.2⟩
  · intro q hq
    have hn : e.symm q ≠ p := by
      intro he
      exact hq ((e.apply_symm_apply q).symm.trans (congrArg e he))
    apply LinearMap.ext
    intro x
    rw [relabel_apply, hF.1 _ hn]
    simp
  · rw [relabel_apply, map_one]
    have hhq (q : P) (hq : q = p) : F q 1 = 1 := by
      subst q
      exact hF.2.2.2.1
    rw [hhq _ (e.symm_apply_apply p), map_one]

theorem relabel_compatible (e : P ≃o P) (p q : P)
    (F H : Family (P := P) K) (hFH : LocalCompatible K p q F H) :
    LocalCompatible K (e p) (e q) (relabel K e F) (relabel K e H) := by
  intro h x
  apply (barycentricStalkOrderEquiv K e.symm (e q)).injective
  have hn := barycentricStalkOrderEquiv_restriction K e.symm h
    ((barycentricStalkOrderEquiv K e.symm (e p)).symm
      (F (e.symm (e p)) (polynomialStalkOrderEquiv K e.symm (e p) x)))
  change barycentricStalkOrderEquiv K e.symm (e q)
      (booleanRestriction (faceVertexInclusion h)
        ((barycentricStalkOrderEquiv K e.symm (e p)).symm
          (F (e.symm (e p)) (polynomialStalkOrderEquiv K e.symm (e p) x)))) =
    barycentricStalkOrderEquiv K e.symm (e q)
      ((barycentricStalkOrderEquiv K e.symm (e q)).symm
        (H (e.symm (e q)) (polynomialStalkOrderEquiv K e.symm (e q)
          (polynomialRestriction K h x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [← polynomialStalkOrderEquiv_restriction]
  have hh : LocalCompatible K (e.symm (e p)) (e.symm (e q)) F H := by
    simpa only [e.symm_apply_apply] using hFH
  exact hh (e.symm.monotone h) _

/-- Relabeling preserves actual bijectivity of a component. This permits
`Control` to include bijectivity alongside the fixed-face quotient equation. -/
theorem relabel_component_bijective (e : P ≃o P) (p : P)
    (F : Family (P := P) K) (hF : Function.Bijective (F p)) :
    Function.Bijective (relabel K e F (e p)) := by
  have hhq (q : P) (hq : q = p) : Function.Bijective (F q) := by
    subst q
    exact hF
  have hh : Function.Bijective (F (e.symm (e p))) := hhq _ (e.symm_apply_apply p)
  exact (barycentricStalkOrderEquiv K e.symm (e p)).symm.bijective.comp
    (hh.comp (polynomialStalkOrderEquiv K e.symm (e p)).bijective)

section Action
variable {G : Type*} [Group G]
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def orderAction : MulAction G P where
  smul g p := act g p
  one_smul p := by change act 1 p = p; rw [h₁]; rfl
  mul_smul g h p := by
    change act (g * h) p = act g (act h p)
    rw [hmul]; rfl

def familyAction : MulAction G (Family (P := P) K) where
  smul g F := relabel K (act g) F
  one_smul F := by change relabel K (act 1) F = F; rw [h₁, relabel_refl]
  mul_smul g h F := by
    change relabel K (act (g * h)) F = relabel K (act g) (relabel K (act h) F)
    rw [hmul, relabel_trans]

/-- The exact actions are installed in the type, including the coefficient and
face universes. Thus reading a stage never leaves action metavariables. -/
abbrev RankStage (n : ℕ) :=
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
    (LocalGood K Control) (LocalCompatible K) n

def rankStageValue (n : ℕ) (old : RankStage K Control act h₁ hmul n) :
    equivariantRankCut (fun p : P => faceRank p) n → Family (P := P) K := by
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  exact old.value

theorem exists_controlled_equivariant_family (hs : IsSimplicialPoset P)
    (hcontrol : ∀ (g : G) p (F : Family (P := P) K),
      Control p (F p) → Control (act g p) (relabel K (act g) F (act g p)))
    (hlift : ∀ n (old : RankStage K Control act h₁ hmul n) (p : P),
      faceRank p = n → ∃ y : Family (P := P) K,
        LocalGood K Control p y ∧
        (∀ q : equivariantRankCut faceRank n, q.val < p →
          LocalCompatible K p q.val y (rankStageValue K Control act h₁ hmul n old q)) ∧
        ∀ g : G, act g p = p → relabel K (act g) y = y) :
    ∃ F : comparisonModule (P := P) K,
      scalar K F = 1 ∧ (∀ g : G, relabelComparison K (act g) F = F) ∧
        ∀ p, Control p (F.val p) := by
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  obtain ⟨f, hfg, hfc, hfe⟩ := exists_equivariant_rank_family faceRank
    (faceRank_strictMono hs) (fun g p => faceRank_eq_of_orderIso (act g) p)
    (fun g _ _ h => (act g).strictMono h)
    (LocalGood K Control) (LocalCompatible K)
    (fun g p y hy => relabel_good K Control (act g) (hcontrol g) p y hy)
    (fun g p q y z hy => relabel_compatible K (act g) p q y z hy)
    hlift
  let F : Family (P := P) K := fun p => f p p
  have hF : F ∈ comparisonModule K := by
    refine ⟨?_, ?_, ?_⟩
    · intro p q h x
      by_cases he : q = p
      · subst q
        simp only [polynomialRestriction_refl, faceVertexInclusion_refl,
          booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
      · exact hfc p q (lt_of_le_of_ne h he) h x
    · intro p r x
      exact (hfg p).2.1 p r x
    · intro p n x hx
      exact (hfg p).2.2.1 p n x hx
  refine ⟨⟨F, hF⟩, ?_, ?_, fun p => (hfg p).2.2.2.2⟩
  · change constantCoefficient (f ⊥ ⊥ 1) = 1
    rw [(hfg ⊥).2.2.2.1, constantCoefficient_one]
  · intro g
    apply Subtype.ext
    funext p
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun z : Family (P := P) K => z p x)
      (hfe g ((act g).symm p))
    change f (act g ((act g).symm p)) p x =
      relabel K (act g) (f ((act g).symm p)) p x at hh
    rw [(act g).apply_symm_apply] at hh
    exact hh.symm

end Action
end FourPapers.Universal.ScalarFamilies

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

/- BEGIN FourPapers/Universal/ScalarCosetTrace.lean -/
section


section
/-! # Integral transfers in the actual `R → B` comparison module

These constructions act on the module from Section 3 itself. They therefore
preserve every face restriction square, every parameter identity and ordinary
grading. The final assembly explicitly requires the prime-power invariant
families; the construction of those families is a separate theorem.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal.ScalarFamilies
open Classical Finset

section General
variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K]
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

/-- The actual linear relabeling representation, with independent universes. -/
def comparisonRepresentation :
    CyclicRepresentation K G (comparisonModule (P := P) K) where
  toFun g := relabelComparison K (act g)
  map_one' := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    change relabel K (act 1) F.val = F.val
    rw [h₁, relabel_refl]
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    change relabel K (act (g * h)) F.val = relabel K (act g) (relabel K (act h) F.val)
    rw [hmul, relabel_trans]

variable [Fintype G]

def comparisonTrace (H : Subgroup G) (F : comparisonModule (P := P) K)
    (hF : ∀ h : H, relabelComparison K (act h.val) F = F) :
    comparisonModule (P := P) K :=
  cosetTrace (comparisonRepresentation K act h₁ hmul) H F hF

theorem comparisonTrace_fixed (H : Subgroup G) (F : comparisonModule (P := P) K)
    (hF : ∀ h : H, relabelComparison K (act h.val) F = F) (g : G) :
    relabelComparison K (act g) (comparisonTrace K act h₁ hmul H F hF) =
      comparisonTrace K act h₁ hmul H F hF :=
  cosetTrace_fixed (comparisonRepresentation K act h₁ hmul) H F hF g

theorem comparisonTrace_scalar (H : Subgroup G) (F : comparisonModule (P := P) K)
    (hF : ∀ h : H, relabelComparison K (act h.val) F = F) :
    scalar K (comparisonTrace K act h₁ hmul H F hF) = H.index • scalar K F :=
  cosetTrace_map_const (comparisonRepresentation K act h₁ hmul) H F hF
    (scalar K).toAddMonoidHom (scalar K F) (fun g => scalar_relabel K (act g) F)

end General

section Simplex
variable {V : Type*} [Fintype V]
variable (K : Type*) [CommRing K]

theorem permutationSubgroup_index (H : Subgroup (Equiv.Perm V)) :
    H.index = (Fintype.card V).factorial / Nat.card H := by
  have h := H.index_eq_card_div
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using h

/-- Trace an actual subgroup-fixed normalized comparison family. -/
theorem exists_scalar_index_family (H : Subgroup (Equiv.Perm V))
    (F : comparisonModule (P := Finset V) K)
    (hF : ∀ h : H, relabelComparison K (finsetOrderCongr h.val) F = F)
    (hscalar : scalar K F = 1) :
    ∃ T : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) T = T) ∧
      scalar K T = (H.index : K) := by
  refine ⟨comparisonTrace K finsetOrderCongr simplexOrderAction_one
    simplexOrderAction_mul H F hF, ?_, ?_⟩
  · exact comparisonTrace_fixed K finsetOrderCongr simplexOrderAction_one
      simplexOrderAction_mul H F hF
  · rw [comparisonTrace_scalar, hscalar, nsmul_eq_mul, mul_one]

/-- The exact scalar obtained from all largest prime-power divisors of the
number of vertices. The local template premise is deliberately explicit. -/
theorem exists_factorial_scalar_family_of_primePowerTemplates
    (hd : 1 < Fintype.card V)
    (htemplate : ∀ p ∈ (Fintype.card V).primeFactors,
      ∃ H : Subgroup (Equiv.Perm V),
        Nat.card H = p ^ (Fintype.card V).factorization p ∧
        ∃ F : comparisonModule (P := Finset V) K,
          (∀ h : H, relabelComparison K (finsetOrderCongr h.val) F = F) ∧
            scalar K F = 1) :
    ∃ F : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) ∧
      scalar K F = ((Fintype.card V - 1).factorial : K) := by
  let d := Fintype.card V
  have htrace : ∀ p : d.primeFactors, ∃ F : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) ∧
        scalar K F = (d.factorial / p.val ^ d.factorization p.val : ℕ) := by
    intro p
    obtain ⟨H, hcard, F, hF, hscalar⟩ := htemplate p.val p.property
    obtain ⟨T, hT, hTs⟩ := exists_scalar_index_family K H F hF hscalar
    refine ⟨T, hT, ?_⟩
    rw [hTs, permutationSubgroup_index, hcard]
  choose F hF hscalar using htrace
  obtain ⟨μ, hμ⟩ := exists_factorial_trace_coefficients d hd
  let T : comparisonModule (P := Finset V) K := ∑ p : d.primeFactors, (μ p.val : K) • F p
  refine ⟨T, ?_, ?_⟩
  · intro σ
    dsimp only [T]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [map_smul, hF p σ]
  · dsimp only [T]
    rw [map_sum]
    simp only [map_smul, hscalar, smul_eq_mul]
    change (∑ p ∈ d.primeFactors.attach,
      (μ p.val : K) * (d.factorial / p.val ^ d.factorization p.val : ℕ)) = _
    rw [Finset.sum_attach d.primeFactors
      (fun p => (μ p : K) * (d.factorial / p ^ d.factorization p : ℕ))]
    have hμK := congrArg (Int.castRingHom K) hμ
    simpa only [map_sum, map_mul, Int.coe_castRingHom, Int.cast_natCast] using hμK

end Simplex
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/ScalarSymmetricTransport.lean -/
section

section
/-! # Scalar families on every poset of bounded rank

A symmetric coherent family on one simplex determines a family on every
finite vertex set of at most that cardinality. Independence of the chosen
embedding and compatibility with restrictions are proved on the actual
polynomial and Boolean stalks. No inverse or division by the scalar is used.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ScalarFamilies
open Classical Finset MvPolynomial

section Squares
variable {A B C D K : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [CommRing K]

theorem coeffRenameInverse (e : A ≃ B) (f : MvPolynomial B K) (a : A →₀ ℕ) :
    (rename e.symm f).coeff a = f.coeff (a.mapDomain e) := by
  have h := MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective f (a.mapDomain e)
  simpa only [← Finsupp.mapDomain_comp, e.symm_comp_self, Finsupp.mapDomain_id] using h

theorem killComplEquiv (e : A ≃ B) (f : MvPolynomial B K) :
    killCompl e.injective f = rename e.symm f := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeffRenameInverse]

theorem inverseEmbeddingSquare (i : A ↪ B) (j : C ↪ D) (e : A ≃ C) (g : B ≃ D)
    (h : i.trans g.toEmbedding = e.toEmbedding.trans j) :
    j.trans g.symm.toEmbedding = e.symm.toEmbedding.trans i := by
  apply Function.Embedding.ext
  intro a
  apply g.injective
  have hh := congrArg (fun t : A ↪ D => t (e.symm a)) h
  change g (i (e.symm a)) = j (e (e.symm a)) at hh
  change g (g.symm (j a)) = g (i (e.symm a))
  simpa only [Equiv.apply_symm_apply] using hh.symm

theorem killComplRenameSquare (i : A ↪ B) (j : C ↪ D) (e : A ≃ C) (g : B ≃ D)
    (h : i.trans g.toEmbedding = e.toEmbedding.trans j) (f : MvPolynomial D K) :
    killCompl i.injective (rename g.symm f) =
      rename e.symm (killCompl j.injective f) := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeffRenameInverse, coeffRenameInverse,
    MvPolynomial.coeff_killCompl, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  change f.coeff (a.mapDomain (i.trans g.toEmbedding)) =
    f.coeff (a.mapDomain (e.toEmbedding.trans j))
  rw [h]

theorem booleanRestrictionRelabelSquare (i : A ↪ B) (j : C ↪ D)
    (e : A ≃ C) (g : B ≃ D) (h : i.trans g.toEmbedding = e.toEmbedding.trans j)
    (x : BooleanBarycentricRing B K) :
    booleanVertexRelabelEquiv e (booleanRestriction i x) =
      booleanRestriction j (booleanVertexRelabelEquiv g x) := by
  have he := (inverseEmbeddingSquare i j e g h).symm
  change booleanRestriction e.symm.toEmbedding (booleanRestriction i x) =
    booleanRestriction j (booleanRestriction g.symm.toEmbedding x)
  calc
    _ = booleanRestriction (e.symm.toEmbedding.trans i) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction (j.trans g.symm.toEmbedding) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

theorem reverseVertexTransport_graded
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (hf : ∀ n x, x ∈ polynomialDegreePiece n → f x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (x : MvPolynomial A K) (hx : x ∈ polynomialDegreePiece n) :
    reverseVertexTransport f e x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n :=
  booleanVertexRelabelEquiv_degree e.symm n _
    (hf n _ (polynomialRename_degree e n x hx))

end Squares

section Stalks
variable {P A B K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype A] [Fintype B] [CommRing K]

theorem reverseVertexTransport_stalk_restriction
    (F : comparisonModule (P := P) K) {p q : P} (hqp : q ≤ p)
    (a : A ≃ FaceVertex q) (b : B ≃ FaceVertex p) (i : A ↪ B)
    (hi : i.trans b.toEmbedding = a.toEmbedding.trans (faceVertexInclusion hqp))
    (x : MvPolynomial B K) :
    booleanRestriction i (reverseVertexTransport (F.val p) b x) =
      reverseVertexTransport (F.val q) a (killCompl i.injective x) := by
  have hi' := inverseEmbeddingSquare i (faceVertexInclusion hqp) a b hi
  rw [reverseVertexTransport_apply,
    ← booleanRestrictionRelabelSquare (faceVertexInclusion hqp) i a.symm b.symm hi']
  refine (congrArg (booleanVertexRelabelEquiv a.symm)
    (F.property.1 p q hqp (rename b x))).trans ?_
  exact congrArg (fun z : MvPolynomial (FaceVertex q) K =>
    booleanVertexRelabelEquiv a.symm (F.val q z))
      (by
        rw [polynomialRestriction_eq_killCompl]
        exact killComplRenameSquare (faceVertexInclusion hqp) i a.symm b.symm hi' x)

end Stalks

section Placements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

theorem placementFace_comp_subset (i : B ↪ V) (j : A ↪ B) :
    embeddingPlacementFace (j.trans i) ⊆ embeddingPlacementFace i := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨j a, Finset.mem_univ _, rfl⟩

theorem placementVertex_comp (i : B ↪ V) (j : A ↪ B) :
    j.trans (embeddingPlacementVertex i).toEmbedding =
      (embeddingPlacementVertex (j.trans i)).toEmbedding.trans
        (faceVertexInclusion (placementFace_comp_subset i j)) := by
  apply Function.Embedding.ext
  intro a
  apply Subtype.ext
  rfl

theorem embeddedScalarMap_restriction (F : comparisonModule (P := Finset V) K)
    (i : B ↪ V) (j : A ↪ B) (x : MvPolynomial B K) :
    booleanRestriction j (embeddedScalarMap F i x) =
      embeddedScalarMap F (j.trans i) (killCompl j.injective x) :=
  reverseVertexTransport_stalk_restriction F (placementFace_comp_subset i j)
    (embeddingPlacementVertex (j.trans i)) (embeddingPlacementVertex i) j
    (placementVertex_comp i j) x

def finiteScalarMap (F : comparisonModule (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) :
    MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K :=
  embeddedScalarMap F (Classical.choice (Function.Embedding.nonempty_of_card_le hA))

theorem finiteScalarMap_eq_placement (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (i : A ↪ V) :
    finiteScalarMap F hA = embeddedScalarMap F i :=
  embeddedScalarMap_independent F hF _ i

theorem finiteScalarMap_restriction (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (i : A ↪ B) (x : MvPolynomial B K) :
    booleanRestriction i (finiteScalarMap F hB x) =
      finiteScalarMap F hA (killCompl i.injective x) := by
  let j : B ↪ V := Classical.choice (Function.Embedding.nonempty_of_card_le hB)
  rw [finiteScalarMap_eq_placement F hF hB j,
    finiteScalarMap_eq_placement F hF hA (i.trans j)]
  exact embeddedScalarMap_restriction F j i x

theorem finiteScalarMap_relabel (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (e : A ≃ B) (x : MvPolynomial A K) :
    booleanVertexRelabelEquiv e (finiteScalarMap F hA x) =
      finiteScalarMap F hB (rename e x) := by
  have h := finiteScalarMap_restriction F hF hB hA e.symm.toEmbedding x
  rw [killComplEquiv e.symm] at h
  exact h

theorem finiteScalarMap_parameter (F : comparisonModule (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) (r : ℕ) (x : MvPolynomial A K) :
    finiteScalarMap F hA (esymm A K (r + 1) * x) =
      booleanRankParameter (r + 1) * finiteScalarMap F hA x :=
  reverseVertexTransport_parameter _ _ (fun r x => F.property.2.1 _ r x) r x

theorem finiteScalarMap_graded (F : comparisonModule (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) (n : ℕ) (x : MvPolynomial A K)
    (hx : x ∈ polynomialDegreePiece n) : finiteScalarMap F hA x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n :=
  reverseVertexTransport_graded _ _ (fun n x hx => F.property.2.2 _ n x hx) n x hx

theorem finiteScalarMap_one (F : comparisonModule (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) : finiteScalarMap F hA 1 = scalar K F • 1 :=
  reverseVertexTransport_scalar _ _ (scalar K F) (component_one K F _)

end Placements

section Posets
variable {P V K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype V] [CommRing K]

def transportedFamily (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) : comparisonModule (P := P) K :=
  ⟨fun p => finiteScalarMap F (by rw [card_faceVertex]; exact hP p), by
    refine ⟨?_, ?_, ?_⟩
    · intro p q h x
      rw [polynomialRestriction_eq_killCompl]
      exact finiteScalarMap_restriction F hF _ _ (faceVertexInclusion h) x
    · intro p r x
      exact finiteScalarMap_parameter F _ r x
    · intro p n x hx
      exact finiteScalarMap_graded F _ n x hx⟩

theorem transportedFamily_scalar (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) :
    scalar K (transportedFamily F hF hP) = scalar K F := by
  change constantCoefficient (finiteScalarMap F
    (by rw [card_faceVertex]; exact hP ⊥) 1) = scalar K F
  rw [finiteScalarMap_one, constantCoefficient_smul_one]

theorem transportedFamily_fixed (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) (e : P ≃o P) :
    relabelComparison K e (transportedFamily F hF hP) = transportedFamily F hF hP := by
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro x
  change (barycentricStalkOrderEquiv K e.symm p).symm
    (finiteScalarMap F (by rw [card_faceVertex]; exact hP (e.symm p))
      (polynomialStalkOrderEquiv K e.symm p x)) =
        finiteScalarMap F (by rw [card_faceVertex]; exact hP p) x
  apply (barycentricStalkOrderEquiv K e.symm p).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (finiteScalarMap_relabel F hF _ _ (faceVertexOrderEquiv e.symm p) x).symm

end Posets
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitQuotient.lean -/
section

section
/-! # Free actions on subgroup orbit sets

For a commutative group, the action on the orbit set of any subgroup descends
to the quotient group. A free original action gives a free quotient action.
This is the actual quotient action used in the cyclic prime-power induction.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

variable {G V : Type*} [CommGroup G] [MulAction G V]
variable (Z : Subgroup G)

abbrev SubgroupOrbit := MulAction.orbitRel.Quotient Z V

def subgroupOrbitAction : MulAction G (SubgroupOrbit (V := V) Z) where
  smul g := Quotient.map' (fun v : V => g • v) (by
    intro v w hvw
    obtain ⟨z, hz⟩ := hvw
    change z.val • w = v at hz
    refine ⟨z, ?_⟩
    change z.val • (g • w) = g • v
    rw [smul_smul, mul_comm z.val g, ← smul_smul, hz])
  one_smul q := by
    induction q using Quotient.inductionOn' with
    | h v => exact congrArg (fun x : V => (Quotient.mk'' x : SubgroupOrbit Z)) (one_smul G v)
  mul_smul g h q := by
    induction q using Quotient.inductionOn' with
    | h v => exact congrArg (fun x : V => (Quotient.mk'' x : SubgroupOrbit Z)) (mul_smul g h v)

theorem subgroupOrbitAction_mk (g : G) (v : V) :
    letI := subgroupOrbitAction (V := V) Z
    g • (Quotient.mk'' v : SubgroupOrbit Z) = Quotient.mk'' (g • v) := rfl

def quotientOrbitPermutation : (G ⧸ Z) →* Equiv.Perm (SubgroupOrbit (V := V) Z) := by
  letI := subgroupOrbitAction (V := V) Z
  apply QuotientGroup.lift Z (MulAction.toPermHom G (SubgroupOrbit (V := V) Z))
  intro z hz
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h v =>
    change (Quotient.mk'' (z • v) : SubgroupOrbit Z) = Quotient.mk'' v
    exact Quotient.sound ⟨⟨z, hz⟩, rfl⟩

def quotientOrbitAction : MulAction (G ⧸ Z) (SubgroupOrbit (V := V) Z) :=
  MulAction.compHom _ (quotientOrbitPermutation (V := V) Z)

theorem quotientOrbitAction_mk (g : G) (v : V) :
    letI := quotientOrbitAction (V := V) Z
    (QuotientGroup.mk g : G ⧸ Z) • (Quotient.mk'' v : SubgroupOrbit Z) =
      Quotient.mk'' (g • v) := rfl

theorem quotientOrbitAction_free
    (hf : ∀ (g : G) (v : V), g • v = v → g = 1) :
    letI := quotientOrbitAction (V := V) Z
    ∀ (g : G ⧸ Z) (v : SubgroupOrbit (V := V) Z), g • v = v → g = 1 := by
  letI := quotientOrbitAction (V := V) Z
  intro g v h
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction v using Quotient.inductionOn' with
    | h v =>
      change (Quotient.mk'' (g • v) : SubgroupOrbit Z) = Quotient.mk'' v at h
      obtain ⟨z, hz⟩ := Quotient.exact h
      change z.val • v = g • v at hz
      have hg : g = z.val := by
        have he : z.val⁻¹ * g = 1 := hf _ v (by
          rw [mul_smul, ← hz, inv_smul_smul])
        exact (inv_mul_eq_one.mp he).symm
      rw [hg]
      exact (QuotientGroup.eq_one_iff z.val).mpr z.property

theorem subgroupOrbitAction_restrict_free
    (hf : ∀ (g : G) (v : V), g • v = v → g = 1) :
    ∀ (z : Z) (v : V), z • v = v → z = 1 := by
  intro z v h
  apply Subtype.ext
  exact hf z.val v h

/-- The checked free-orbit coordinates for the literal subgroup action. -/
def subgroupOrbitCoordinates
    (hf : ∀ (g : G) (v : V), g • v = v → g = 1) :
    (Z × SubgroupOrbit (V := V) Z) ≃ V :=
  freeOrbitCoordinateEquiv (subgroupOrbitAction_restrict_free Z hf)

@[simp] theorem subgroupOrbitCoordinates_apply
    (hf : ∀ (g : G) (v : V), g • v = v → g = 1)
    (z : Z) (q : SubgroupOrbit (V := V) Z) :
    subgroupOrbitCoordinates Z hf (z, q) = z.val • q.out := rfl

theorem quotient_card_lt [Finite G] (hZ : 1 < Nat.card Z) :
    Nat.card (G ⧸ Z) < Nat.card G := by
  rw [← Z.index_eq_card, Z.index_eq_card_div]
  exact Nat.div_lt_self Nat.card_pos hZ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FreePermutationBlocks.lean -/
section

section
/-! # Free permutation blocks of any divisor of the vertex cardinality

The regular action on a group coordinate gives a free permutation action
on any finite set whose cardinality is a multiple of the group order.
The subgroup image has exactly that order, so its coset trace has precisely
the scalar used in the prime-power Bezout argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

variable {G A V : Type*} [Group G]

def blockPermutation (e : V ≃ G × A) (g : G) : Equiv.Perm V where
  toFun v := e.symm (g * (e v).1, (e v).2)
  invFun v := e.symm (g⁻¹ * (e v).1, (e v).2)
  left_inv v := by
    simp only [Equiv.apply_symm_apply, inv_mul_cancel_left, Prod.mk.eta,
      Equiv.symm_apply_apply]
  right_inv v := by
    simp only [Equiv.apply_symm_apply, mul_inv_cancel_left, Prod.mk.eta,
      Equiv.symm_apply_apply]

def blockPermutationHom (e : V ≃ G × A) : G →* Equiv.Perm V where
  toFun := blockPermutation e
  map_one' := by
    apply Equiv.ext
    intro v
    change e.symm (1 * (e v).1, (e v).2) = v
    rw [one_mul, Prod.mk.eta, Equiv.symm_apply_apply]
  map_mul' g h := by
    apply Equiv.ext
    intro v
    change e.symm ((g * h) * (e v).1, (e v).2) =
      e.symm (g * (e (e.symm (h * (e v).1, (e v).2))).1,
        (e (e.symm (h * (e v).1, (e v).2))).2)
    rw [Equiv.apply_symm_apply, mul_assoc]

theorem blockPermutationHom_free (e : V ≃ G × A) (g : G) (v : V)
    (h : blockPermutationHom e g v = v) : g = 1 := by
  have hh := congrArg (fun x : V => (e x).1) h
  change (e (e.symm (g * (e v).1, (e v).2))).1 = (e v).1 at hh
  rw [Equiv.apply_symm_apply] at hh
  exact mul_right_cancel (hh.trans (one_mul (e v).1).symm)

theorem blockPermutationHom_injective [Nonempty V] (e : V ≃ G × A) :
    Function.Injective (blockPermutationHom e) := by
  intro g h he
  let v : V := Classical.choice ‹Nonempty V›
  have hh := congrArg (fun σ : Equiv.Perm V => (e (σ v)).1) he
  change (e (e.symm (g * (e v).1, (e v).2))).1 =
    (e (e.symm (h * (e v).1, (e v).2))).1 at hh
  simp only [Equiv.apply_symm_apply] at hh
  exact mul_right_cancel hh

theorem exists_free_permutation_hom [Fintype G] [Fintype V] [Nonempty V]
    (hd : Fintype.card G ∣ Fintype.card V) :
    ∃ ρ : G →* Equiv.Perm V,
      Function.Injective ρ ∧ ∀ (g : G) (v : V), ρ g v = v → g = 1 := by
  let e : V ≃ G × Fin (Fintype.card V / Fintype.card G) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_prod, Fintype.card_fin]
      exact (Nat.mul_div_cancel' hd).symm)
  exact ⟨blockPermutationHom e, blockPermutationHom_injective e,
    blockPermutationHom_free e⟩

theorem free_permutation_range_card [Finite G]
    (ρ : G →* Equiv.Perm V) (hρ : Function.Injective ρ) :
    Nat.card ρ.range = Nat.card G :=
  (Nat.card_congr (Equiv.ofInjective ρ hρ)).symm

end FourPapers.Universal

end
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

/- BEGIN FourPapers/Universal/CyclicMomentWeights.lean -/
section

section
/-! # Integral moment weights on a prime cyclic orbit

The two weights `1` and `-1` replace averaging by division. Translation of
an interior-cardinality subset changes its moment by a nonzero multiple of
the translating element. Consequently the total weight is exactly zero
over every commutative ring, including the integers.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]

def cyclicExponentMoment : (ZMod p →₀ ℕ) →+ ZMod p where
  toFun a := ∑ x : ZMod p, (a x : ZMod p) * x
  map_zero' := by simp
  map_add' a b := by
    simp only [Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem cyclicExponentMoment_single (x : ZMod p) (n : ℕ) :
    cyclicExponentMoment p (Finsupp.single x n) = (n : ZMod p) * x := by
  change (∑ y : ZMod p, ((Finsupp.single x n) y : ZMod p) * y) = _
  rw [Finset.sum_eq_single x]
  · rw [Finsupp.single_eq_same]
  · intro y hy hyx
    simp only [Finsupp.single_apply, if_neg (Ne.symm hyx), Nat.cast_zero, zero_mul]
  · intro hx
    exact False.elim (hx (Finset.mem_univ x))

theorem cyclicExponentMoment_shift (a : ZMod p →₀ ℕ) (g : ZMod p) :
    cyclicExponentMoment p (a.mapDomain (Equiv.addLeft g)) =
      (a.degree : ZMod p) * g + cyclicExponentMoment p a := by
  change (∑ x : ZMod p, ((a.mapDomain (Equiv.addLeft g)) x : ZMod p) * x) = _
  calc
    _ = ∑ x : ZMod p,
        ((a.mapDomain (Equiv.addLeft g)) ((Equiv.addLeft g) x) : ZMod p) *
          ((Equiv.addLeft g) x) :=
      (Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun _ => rfl)).symm
    _ = ∑ x : ZMod p, (a x : ZMod p) * (g + x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finsupp.mapDomain_apply_of_injective (Equiv.addLeft g).injective]
      rfl
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Nat.cast_sum, ← Finsupp.degree_eq_sum]
      rfl

def cyclicSubsetExponent (s : Finset (ZMod p)) : ZMod p →₀ ℕ :=
  ∑ x ∈ s, Finsupp.single x 1

@[simp] theorem cyclicSubsetExponent_degree (s : Finset (ZMod p)) :
    (cyclicSubsetExponent p s).degree = s.card := by
  simp [cyclicSubsetExponent]

def cyclicSubsetMoment (s : Finset (ZMod p)) : ZMod p := ∑ x ∈ s, x

@[simp] theorem cyclicSubsetExponent_moment (s : Finset (ZMod p)) :
    cyclicExponentMoment p (cyclicSubsetExponent p s) = cyclicSubsetMoment p s := by
  simp only [cyclicSubsetExponent, map_sum, cyclicExponentMoment_single, Nat.cast_one,
    one_mul, cyclicSubsetMoment]

theorem cyclicSubsetMoment_shift (s : Finset (ZMod p)) (g : ZMod p) :
    cyclicSubsetMoment p (s.map (Equiv.addLeft g).toEmbedding) =
      (s.card : ZMod p) * g + cyclicSubsetMoment p s := by
  unfold cyclicSubsetMoment
  rw [Finset.sum_map]
  change (∑ x ∈ s, (g + x)) = _
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

abbrev CyclicCardSubset (i : ℕ) := {s : Finset (ZMod p) // s.card = i}

def cyclicCardSubsetShift (i : ℕ) (g : ZMod p) : Equiv.Perm (CyclicCardSubset p i) :=
  (Equiv.finsetCongr (Equiv.addLeft g)).subtypeEquiv (fun s => by
    simp only [Equiv.finsetCongr_apply, Finset.card_map])

theorem cyclicCardSubsetShift_moment (i : ℕ) (g : ZMod p) (s : CyclicCardSubset p i) :
    cyclicSubsetMoment p (cyclicCardSubsetShift p i g s).val =
      (i : ZMod p) * g + cyclicSubsetMoment p s.val := by
  change cyclicSubsetMoment p (s.val.map (Equiv.addLeft g).toEmbedding) = _
  rw [cyclicSubsetMoment_shift, s.property]

variable (K : Type*) [CommRing K]

def primeMomentWeight (t : ZMod p) : K :=
  (if t = 0 then 1 else 0) - (if t = 1 then 1 else 0)

@[simp] theorem primeMomentWeight_zero : primeMomentWeight p K 0 = 1 := by
  simp [primeMomentWeight]

/-- Cancellation is integral: it pairs the zero-moment and one-moment
fibres by a literal translation of subsets. -/
theorem sum_primeMomentWeight_subsets (i : ℕ) (hi : 0 < i) (hip : i < p)
    (A : ZMod p) :
    (∑ s : CyclicCardSubset p i, primeMomentWeight p K (A + cyclicSubsetMoment p s.val)) = 0 := by
  have hi0 : (i : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hi hip
  let e := cyclicCardSubsetShift p i (i : ZMod p)⁻¹
  have hshift (s : CyclicCardSubset p i) :
      A + cyclicSubsetMoment p (e s).val = (A + cyclicSubsetMoment p s.val) + 1 := by
    rw [cyclicCardSubsetShift_moment, mul_inv_cancel₀ hi0]
    ac_rfl
  have hsum : (∑ s : CyclicCardSubset p i,
      if A + cyclicSubsetMoment p s.val = 0 then (1 : K) else 0) =
      ∑ s : CyclicCardSubset p i,
        if A + cyclicSubsetMoment p s.val = 1 then (1 : K) else 0 := by
    apply Fintype.sum_equiv e
    intro s
    rw [hshift]
    simp
  simp only [primeMomentWeight, Finset.sum_sub_distrib, hsum, sub_self]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicMomentRetraction.lean -/
section

section
/-! # An integral retraction along one prime cyclic orbit

The coefficient of a monomial is a difference of two moment indicators.
Centering the moment makes the map commute with multiplication by the full
orbit product, including at the prime two. Interior elementary symmetric
polynomials are annihilated by the integral subset cancellation identity.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

def primeCenteredMoment (a : ZMod p →₀ ℕ) : ZMod p :=
  cyclicExponentMoment p a - ((a.degree / p : ℕ) : ZMod p) * ∑ x : ZMod p, x

def primeMomentCoefficient (a : ZMod p →₀ ℕ) : K :=
  if p ∣ a.degree then primeMomentWeight p K (primeCenteredMoment p a) else 0

@[simp] theorem primeMomentCoefficient_zero :
    primeMomentCoefficient p K 0 = 1 := by
  simp [primeMomentCoefficient, primeCenteredMoment]

theorem cyclicExponentMoment_constant (m : ℕ) :
    cyclicExponentMoment p (cyclicConstantExponent p m) =
      (m : ZMod p) * ∑ x : ZMod p, x := by
  change (∑ x : ZMod p, (m : ZMod p) * x) = _
  exact (Finset.mul_sum _ _ _).symm

theorem primeMomentCoefficient_constant (m : ℕ) :
    primeMomentCoefficient p K (cyclicConstantExponent p m) = 1 := by
  simp only [primeMomentCoefficient, cyclicConstantExponent_degree,
    dvd_mul_right, if_true, primeCenteredMoment, cyclicExponentMoment_constant,
    Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos, sub_self,
    primeMomentWeight_zero]

theorem primeMomentCoefficient_shift (a : ZMod p →₀ ℕ) (g : ZMod p) :
    primeMomentCoefficient p K (a.mapDomain (Equiv.addLeft g)) =
      primeMomentCoefficient p K a := by
  unfold primeMomentCoefficient primeCenteredMoment
  rw [Finsupp.degree_mapDomain, cyclicExponentMoment_shift]
  by_cases h : p ∣ a.degree
  · have hz : (a.degree : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    simp only [if_pos h, hz, zero_mul, zero_add]
  · simp only [if_neg h]

theorem primeMomentCoefficient_add_constant_one (a : ZMod p →₀ ℕ) :
    primeMomentCoefficient p K (a + cyclicConstantExponent p 1) =
      primeMomentCoefficient p K a := by
  have hd : (a + cyclicConstantExponent p 1).degree = a.degree + p := by
    simp only [map_add, cyclicConstantExponent_degree, mul_one]
  unfold primeMomentCoefficient primeCenteredMoment
  simp only [hd, Nat.dvd_add_self_right, Nat.add_div_right _ (Fact.out : p.Prime).pos,
    map_add, cyclicExponentMoment_constant, Nat.cast_one, one_mul,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  simp only [sub_eq_add_neg, neg_add_rev, add_assoc, add_neg_cancel_left]

/-- The actual polynomial retraction, defined over every commutative ring.
For the integral construction the coefficient ring is instantiated by `ℤ`. -/
def primeMomentRetraction : MvPolynomial (ZMod p) K →ₗ[K] Polynomial K :=
  (MvPolynomial.basisMonomials (ZMod p) K).constr K
    (fun a => Polynomial.monomial (a.degree / p) (primeMomentCoefficient p K a))

theorem primeMomentRetraction_monomial_one (a : ZMod p →₀ ℕ) :
    primeMomentRetraction p K (monomial a 1) =
      Polynomial.monomial (a.degree / p) (primeMomentCoefficient p K a) :=
  (MvPolynomial.basisMonomials (ZMod p) K).constr_basis K _ a

theorem primeMomentRetraction_monomial (a : ZMod p →₀ ℕ) (c : K) :
    primeMomentRetraction p K (monomial a c) =
      Polynomial.monomial (a.degree / p) (c * primeMomentCoefficient p K a) := by
  have hm : monomial a c = c • (monomial a 1 : MvPolynomial (ZMod p) K) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, primeMomentRetraction_monomial_one, Polynomial.smul_monomial,
    smul_eq_mul]

@[simp] theorem primeMomentRetraction_one : primeMomentRetraction p K 1 = 1 := by
  rw [show (1 : MvPolynomial (ZMod p) K) = monomial 0 1 from rfl,
    primeMomentRetraction_monomial_one]
  simp

theorem primeMomentRetraction_constant (m : ℕ) :
    primeMomentRetraction p K (monomial (cyclicConstantExponent p m) 1) =
      Polynomial.X ^ m := by
  rw [primeMomentRetraction_monomial_one, cyclicConstantExponent_degree,
    Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos,
    primeMomentCoefficient_constant, Polynomial.monomial_one_right_eq_X_pow]

theorem primeMomentRetraction_rename (g : ZMod p) (f : MvPolynomial (ZMod p) K) :
    primeMomentRetraction p K (MvPolynomial.rename (Equiv.addLeft g) f) =
      primeMomentRetraction p K f := by
  have h : (primeMomentRetraction p K).comp
      (MvPolynomial.rename (Equiv.addLeft g)).toLinearMap = primeMomentRetraction p K := by
    apply (MvPolynomial.basisMonomials (ZMod p) K).ext
    intro a
    change primeMomentRetraction p K (MvPolynomial.rename (Equiv.addLeft g) (monomial a 1)) = _
    rw [MvPolynomial.rename_monomial, primeMomentRetraction_monomial_one,
      Finsupp.degree_mapDomain, primeMomentCoefficient_shift]
    exact (primeMomentRetraction_monomial_one p K a).symm
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply,
    AlgHom.toLinearMap_apply] using
    LinearMap.congr_fun h f

theorem cyclicSubsetExponent_univ :
    cyclicSubsetExponent p (Finset.univ : Finset (ZMod p)) = cyclicConstantExponent p 1 := by
  ext x
  simp [cyclicSubsetExponent]

theorem primeOrbitProduct_eq_monomial :
    (∏ x : ZMod p, (X x : MvPolynomial (ZMod p) K)) =
      monomial (cyclicConstantExponent p 1) 1 := by
  rw [← cyclicSubsetExponent_univ, cyclicSubsetExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem primeMomentRetraction_top (f : MvPolynomial (ZMod p) K) :
    primeMomentRetraction p K ((∏ x : ZMod p, X x) * f) =
      Polynomial.X * primeMomentRetraction p K f := by
  have h : (primeMomentRetraction p K).comp (LinearMap.mulLeft K (∏ x : ZMod p, X x)) =
      (LinearMap.mulLeft K Polynomial.X).comp (primeMomentRetraction p K) := by
    apply (MvPolynomial.basisMonomials (ZMod p) K).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, MvPolynomial.coe_basisMonomials]
    rw [primeOrbitProduct_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
      primeMomentRetraction_monomial_one, primeMomentRetraction_monomial_one,
      add_comm (cyclicConstantExponent p 1) a, primeMomentCoefficient_add_constant_one,
      map_add, cyclicConstantExponent_degree, mul_one,
      Nat.add_div_right _ (Fact.out : p.Prime).pos, Polynomial.X_mul_monomial]
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply,
    AlgHom.toLinearMap_apply] using
    LinearMap.congr_fun h f

theorem primeMomentRetraction_interior_esymm (i : ℕ) (hi : 0 < i) (hip : i < p)
    (f : MvPolynomial (ZMod p) K) :
    primeMomentRetraction p K (MvPolynomial.esymm (ZMod p) K i * f) = 0 := by
  have h : (primeMomentRetraction p K).comp
      (LinearMap.mulLeft K (MvPolynomial.esymm (ZMod p) K i)) = 0 := by
    apply (MvPolynomial.basisMonomials (ZMod p) K).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, MvPolynomial.coe_basisMonomials,
      LinearMap.zero_apply]
    rw [MvPolynomial.esymm_eq_sum_subtype, Finset.sum_mul, map_sum]
    have hm (s : CyclicCardSubset p i) :
        (∏ x ∈ s.val, (X x : MvPolynomial (ZMod p) K)) * monomial a 1 =
          monomial (a + cyclicSubsetExponent p s.val) 1 := by
      have hs : (∏ x ∈ s.val, (X x : MvPolynomial (ZMod p) K)) =
          monomial (cyclicSubsetExponent p s.val) 1 := by
        rw [cyclicSubsetExponent, MvPolynomial.monomial_sum_one]
        rfl
      rw [hs, MvPolynomial.monomial_mul_monomial, one_mul, add_comm]
    simp_rw [hm, primeMomentRetraction_monomial_one]
    have hd (s : CyclicCardSubset p i) :
        (a + cyclicSubsetExponent p s.val).degree = a.degree + i := by
      rw [map_add, cyclicSubsetExponent_degree, s.property]
    simp_rw [hd, primeMomentCoefficient, hd]
    by_cases hdiv : p ∣ a.degree + i
    · simp only [if_pos hdiv]
      let A : ZMod p := cyclicExponentMoment p a -
        (((a.degree + i) / p : ℕ) : ZMod p) * ∑ x : ZMod p, x
      have hc (s : CyclicCardSubset p i) :
          primeCenteredMoment p (a + cyclicSubsetExponent p s.val) =
            A + cyclicSubsetMoment p s.val := by
        unfold primeCenteredMoment
        rw [hd, map_add, cyclicSubsetExponent_moment]
        exact add_sub_right_comm _ _ _
      simp_rw [hc]
      rw [← map_sum, sum_primeMomentWeight_subsets p K i hi hip A, map_zero]
    · simp only [if_neg hdiv, map_zero, Finset.sum_const_zero]
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply,
    AlgHom.toLinearMap_apply] using
    LinearMap.congr_fun h f

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitMomentRetraction.lean -/
section

section
/-! # Integral moment retraction on a union of free prime orbits

The domain variables are the literal pairs `(x,w)`, with `x : ZMod p`.
Coefficients multiply the integral one-orbit moment weights; the output
exponent records each orbit's degree divided by `p`.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime]
variable {W U : Type*} [Fintype W] [Fintype U]

def primeOrbitBlock (a : (ZMod p × W) →₀ ℕ) (w : W) : ZMod p →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => a (x, w))

@[simp] theorem primeOrbitBlock_apply (a : (ZMod p × W) →₀ ℕ) (w : W) (x : ZMod p) :
    primeOrbitBlock p a w x = a (x, w) := rfl

@[simp] theorem primeOrbitBlock_zero (w : W) : primeOrbitBlock p 0 w = 0 := by
  ext x
  rfl

@[simp] theorem primeOrbitBlock_add (a b : (ZMod p × W) →₀ ℕ) (w : W) :
    primeOrbitBlock p (a + b) w = primeOrbitBlock p a w + primeOrbitBlock p b w := by
  ext x
  rfl

def primeOrbitExponent (a : (ZMod p × W) →₀ ℕ) : W →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun w => (primeOrbitBlock p a w).degree / p)

@[simp] theorem primeOrbitExponent_apply (a : (ZMod p × W) →₀ ℕ) (w : W) :
    primeOrbitExponent p a w = (primeOrbitBlock p a w).degree / p := rfl

@[simp] theorem primeOrbitExponent_zero : primeOrbitExponent (W := W) p 0 = 0 := by
  ext w
  simp

def inflatePrimeOrbitExponent (b : W →₀ ℕ) : (ZMod p × W) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => b v.2)

@[simp] theorem primeOrbitBlock_inflate (b : W →₀ ℕ) (w : W) :
    primeOrbitBlock p (inflatePrimeOrbitExponent p b) w = cyclicConstantExponent p (b w) := by
  ext x
  rfl

@[simp] theorem primeOrbitExponent_inflate (b : W →₀ ℕ) :
    primeOrbitExponent p (inflatePrimeOrbitExponent p b) = b := by
  ext w
  rw [primeOrbitExponent_apply, primeOrbitBlock_inflate, cyclicConstantExponent_degree,
    Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]

theorem primeOrbitBlock_degree_sum (a : (ZMod p × W) →₀ ℕ) :
    (∑ w : W, (primeOrbitBlock p a w).degree) = a.degree := by
  simp only [Finsupp.degree_eq_sum, primeOrbitBlock_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

variable (K : Type*) [CommRing K]

def primeOrbitCoefficient (a : (ZMod p × W) →₀ ℕ) : K :=
  ∏ w : W, primeMomentCoefficient p K (primeOrbitBlock p a w)

@[simp] theorem primeOrbitCoefficient_zero : primeOrbitCoefficient (W := W) p K 0 = 1 := by
  simp [primeOrbitCoefficient]

@[simp] theorem primeOrbitCoefficient_inflate (b : W →₀ ℕ) :
    primeOrbitCoefficient p K (inflatePrimeOrbitExponent p b) = 1 := by
  simp only [primeOrbitCoefficient, primeOrbitBlock_inflate,
    primeMomentCoefficient_constant, Finset.prod_const_one]

theorem primeOrbitCoefficient_nonzero_dvd (a : (ZMod p × W) →₀ ℕ)
    (ha : primeOrbitCoefficient p K a ≠ 0) (w : W) : p ∣ (primeOrbitBlock p a w).degree := by
  have hw : primeMomentCoefficient p K (primeOrbitBlock p a w) ≠ 0 := by
    intro hz
    apply ha
    exact Finset.prod_eq_zero (Finset.mem_univ w) hz
  by_contra h
  exact hw (by simp only [primeMomentCoefficient, if_neg h])

theorem primeOrbitCoefficient_nonzero_degree (a : (ZMod p × W) →₀ ℕ)
    (ha : primeOrbitCoefficient p K a ≠ 0) : p * (primeOrbitExponent p a).degree = a.degree := by
  rw [Finsupp.degree_eq_sum, Finset.mul_sum, ← primeOrbitBlock_degree_sum p a]
  apply Finset.sum_congr rfl
  intro w hw
  exact Nat.mul_div_cancel' (primeOrbitCoefficient_nonzero_dvd p K a ha w)

def primeOrbitMomentRetraction :
    MvPolynomial (ZMod p × W) K →ₗ[K] MvPolynomial W K :=
  (MvPolynomial.basisMonomials (ZMod p × W) K).constr K
    (fun a => monomial (primeOrbitExponent p a) (primeOrbitCoefficient p K a))

theorem primeOrbitMomentRetraction_monomial_one (a : (ZMod p × W) →₀ ℕ) :
    primeOrbitMomentRetraction p K (monomial a 1) =
      monomial (primeOrbitExponent p a) (primeOrbitCoefficient p K a) :=
  (MvPolynomial.basisMonomials (ZMod p × W) K).constr_basis K _ a

theorem primeOrbitMomentRetraction_monomial (a : (ZMod p × W) →₀ ℕ) (c : K) :
    primeOrbitMomentRetraction p K (monomial a c) =
      monomial (primeOrbitExponent p a) (c * primeOrbitCoefficient p K a) := by
  have hm : monomial a c = c • (monomial a 1 : MvPolynomial (ZMod p × W) K) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, primeOrbitMomentRetraction_monomial_one, smul_monomial, smul_eq_mul]

@[simp] theorem primeOrbitMomentRetraction_one :
    primeOrbitMomentRetraction (W := W) p K 1 = 1 := by
  rw [show (1 : MvPolynomial (ZMod p × W) K) = monomial 0 1 from rfl,
    primeOrbitMomentRetraction_monomial_one, primeOrbitExponent_zero,
    primeOrbitCoefficient_zero]
  rfl

theorem primeOrbitMomentRetraction_inflate (b : W →₀ ℕ) (c : K) :
    primeOrbitMomentRetraction p K (monomial (inflatePrimeOrbitExponent p b) c) =
      monomial b c := by
  rw [primeOrbitMomentRetraction_monomial, primeOrbitExponent_inflate,
    primeOrbitCoefficient_inflate, mul_one]

theorem primeOrbitMomentRetraction_monomial_zero_of_not_dvd
    (a : (ZMod p × W) →₀ ℕ) (c : K) (ha : ¬ p ∣ a.degree) :
    primeOrbitMomentRetraction p K (monomial a c) = 0 := by
  rw [primeOrbitMomentRetraction_monomial]
  have hz : primeOrbitCoefficient p K a = 0 := by
    by_contra h
    exact ha ⟨(primeOrbitExponent p a).degree,
      (primeOrbitCoefficient_nonzero_degree p K a h).symm⟩
  rw [hz, mul_zero, map_zero]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitMomentSymmetry.lean -/
section

section
/-! # Equivariance of the integral moment retraction

Relabeling free prime orbits consists of a bijection of the orbit labels and
an independent translation inside each orbit. The retraction intertwines
this literal variable permutation with the induced orbit permutation.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime]
variable {W U : Type*} [Fintype W] [Fintype U]

def primeOrbitRelabel (σ : W ≃ U) (g : W → ZMod p) : (ZMod p × W) ≃ (ZMod p × U) where
  toFun v := (g v.2 + v.1, σ v.2)
  invFun v := (v.1 - g (σ.symm v.2), σ.symm v.2)
  left_inv v := by
    apply Prod.ext
    · simp only [Equiv.symm_apply_apply]
      exact add_sub_cancel_left _ _
    · exact σ.symm_apply_apply v.2
  right_inv v := by
    apply Prod.ext
    · exact add_sub_cancel _ _
    · exact σ.apply_symm_apply v.2

theorem primeOrbitRelabel_translation (σ : W ≃ U) (g : W → ZMod p)
    (t : ZMod p) (v : ZMod p × W) :
    primeOrbitRelabel p σ g (t + v.1, v.2) =
      (t + (primeOrbitRelabel p σ g v).1, (primeOrbitRelabel p σ g v).2) := by
  apply Prod.ext
  · change g v.2 + (t + v.1) = t + (g v.2 + v.1)
    ac_rfl
  · rfl

theorem primeOrbitBlock_relabel (σ : W ≃ U) (g : W → ZMod p)
    (a : (ZMod p × W) →₀ ℕ) (w : W) :
    primeOrbitBlock p (a.mapDomain (primeOrbitRelabel p σ g)) (σ w) =
      (primeOrbitBlock p a w).mapDomain (Equiv.addLeft (g w)) := by
  ext x
  rw [primeOrbitBlock_apply, Finsupp.mapDomain_equiv_apply,
    Finsupp.mapDomain_equiv_apply]
  change a (x - g (σ.symm (σ w)), σ.symm (σ w)) = a (-g w + x, w)
  rw [σ.symm_apply_apply]
  congr 2
  exact sub_eq_neg_add x (g w)

theorem primeOrbitExponent_relabel (σ : W ≃ U) (g : W → ZMod p)
    (a : (ZMod p × W) →₀ ℕ) :
    primeOrbitExponent p (a.mapDomain (primeOrbitRelabel p σ g)) =
      (primeOrbitExponent p a).mapDomain σ := by
  ext u
  obtain ⟨w, rfl⟩ := σ.surjective u
  rw [primeOrbitExponent_apply, primeOrbitBlock_relabel, Finsupp.degree_mapDomain,
    Finsupp.mapDomain_apply_of_injective σ.injective, primeOrbitExponent_apply]

variable (K : Type*) [CommRing K]

theorem primeOrbitCoefficient_relabel (σ : W ≃ U) (g : W → ZMod p)
    (a : (ZMod p × W) →₀ ℕ) :
    primeOrbitCoefficient p K (a.mapDomain (primeOrbitRelabel p σ g)) =
      primeOrbitCoefficient p K a := by
  unfold primeOrbitCoefficient
  symm
  apply Fintype.prod_equiv σ
  intro w
  rw [primeOrbitBlock_relabel, primeMomentCoefficient_shift]

theorem primeOrbitMomentRetraction_relabel (σ : W ≃ U) (g : W → ZMod p)
    (f : MvPolynomial (ZMod p × W) K) :
    primeOrbitMomentRetraction p K (MvPolynomial.rename (primeOrbitRelabel p σ g) f) =
      MvPolynomial.rename σ (primeOrbitMomentRetraction p K f) := by
  have h : (primeOrbitMomentRetraction (W := U) p K).comp
      (MvPolynomial.rename (primeOrbitRelabel p σ g)).toLinearMap =
      (MvPolynomial.rename σ).toLinearMap.comp (primeOrbitMomentRetraction (W := W) p K) := by
    apply (MvPolynomial.basisMonomials (ZMod p × W) K).ext
    intro a
    change primeOrbitMomentRetraction p K
        (MvPolynomial.rename (primeOrbitRelabel p σ g) (monomial a 1)) =
      MvPolynomial.rename σ (primeOrbitMomentRetraction p K (monomial a 1))
    rw [MvPolynomial.rename_monomial, primeOrbitMomentRetraction_monomial_one,
      primeOrbitMomentRetraction_monomial_one, MvPolynomial.rename_monomial,
      primeOrbitExponent_relabel, primeOrbitCoefficient_relabel]
  exact LinearMap.congr_fun h f

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitCentralizer.lean -/
section

section
/-! # The literal centralizer of a free prime translation action

A vertex bijection commuting with all translations permutes the orbit
labels and translates each orbit separately.  The orbit permutation and
translation are extracted from its values at `(0,w)`, with bijectivity
proved from the original vertex bijection.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

variable (p : ℕ) [Fact p.Prime]
variable {W U T : Type*} [Fintype W] [Fintype U] [Fintype T]

def CommutesPrimeTranslations (e : (ZMod p × W) ≃ (ZMod p × U)) : Prop :=
  ∀ (t : ZMod p) (v : ZMod p × W),
    e (t + v.1, v.2) = (t + (e v).1, (e v).2)

theorem primeOrbitCentralizer_formula (e : (ZMod p × W) ≃ (ZMod p × U))
    (he : CommutesPrimeTranslations p e) (x : ZMod p) (w : W) :
    e (x, w) = (x + (e (0, w)).1, (e (0, w)).2) := by
  simpa only [add_zero] using he x (0, w)

theorem primeOrbitCentralizer_label_bijective (e : (ZMod p × W) ≃ (ZMod p × U))
    (he : CommutesPrimeTranslations p e) :
    Function.Bijective (fun w : W => (e (0, w)).2) := by
  constructor
  · intro w u h
    have hE : e ((e (0, u)).1 - (e (0, w)).1, w) = e (0, u) := by
      rw [primeOrbitCentralizer_formula p e he]
      apply Prod.ext
      · exact sub_add_cancel _ _
      · exact h
    exact congrArg (fun v : ZMod p × W => v.2) (e.injective hE)
  · intro u
    obtain ⟨⟨x, w⟩, hw⟩ := e.surjective (0, u)
    refine ⟨w, ?_⟩
    have h₁ := congrArg (fun v : ZMod p × U => v.2) hw
    have h₂ := congrArg (fun v : ZMod p × U => v.2)
      (primeOrbitCentralizer_formula p e he x w)
    exact h₂.symm.trans h₁

def primeOrbitLabelEquiv (e : (ZMod p × W) ≃ (ZMod p × U))
    (he : CommutesPrimeTranslations p e) : W ≃ U :=
  Equiv.ofBijective (fun w => (e (0, w)).2) (primeOrbitCentralizer_label_bijective p e he)

@[simp] theorem primeOrbitLabelEquiv_apply (e : (ZMod p × W) ≃ (ZMod p × U))
    (he : CommutesPrimeTranslations p e) (w : W) :
    primeOrbitLabelEquiv p e he w = (e (0, w)).2 := rfl

/-- Every centralizing vertex bijection is the exact relabeling already
handled by the integral moment and fixed-face maps. -/
theorem primeOrbitCentralizer_normalForm (e : (ZMod p × W) ≃ (ZMod p × U))
    (he : CommutesPrimeTranslations p e) :
    e = primeOrbitRelabel p (primeOrbitLabelEquiv p e he) (fun w => (e (0, w)).1) := by
  apply Equiv.ext
  intro v
  rw [primeOrbitCentralizer_formula p e he v.1 v.2]
  apply Prod.ext
  · exact add_comm _ _
  · rfl

theorem commutesPrimeTranslations_trans
    (e : (ZMod p × W) ≃ (ZMod p × U)) (f : (ZMod p × U) ≃ (ZMod p × T))
    (he : CommutesPrimeTranslations p e) (hf : CommutesPrimeTranslations p f) :
    CommutesPrimeTranslations p (e.trans f) := by
  intro t v
  change f (e (t + v.1, v.2)) = (t + (f (e v)).1, (f (e v)).2)
  rw [he, hf]

theorem primeOrbitLabelEquiv_trans
    (e : (ZMod p × W) ≃ (ZMod p × U)) (f : (ZMod p × U) ≃ (ZMod p × T))
    (he : CommutesPrimeTranslations p e) (hf : CommutesPrimeTranslations p f) :
    primeOrbitLabelEquiv p (e.trans f) (commutesPrimeTranslations_trans p e f he hf) =
      (primeOrbitLabelEquiv p e he).trans (primeOrbitLabelEquiv p f hf) := by
  apply Equiv.ext
  intro w
  change (f (e (0, w))).2 = (f (0, (e (0, w)).2)).2
  have h := congrArg (fun v : ZMod p × T => v.2)
    (primeOrbitCentralizer_formula p f hf (e (0, w)).1 (e (0, w)).2)
  exact h

section ParentAction
variable {G : Type*} [Monoid G]

/-- The induced action on the actual orbit labels, as a monoid homomorphism. -/
def primeOrbitParentAction (ρ : G →* Equiv.Perm (ZMod p × W))
    (hρ : ∀ g, CommutesPrimeTranslations p (ρ g)) : G →* Equiv.Perm W where
  toFun g := primeOrbitLabelEquiv p (ρ g) (hρ g)
  map_one' := by
    apply Equiv.ext
    intro w
    change (ρ 1 (0, w)).2 = w
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro w
    change (ρ (g * h) (0, w)).2 = (ρ g (0, (ρ h (0, w)).2)).2
    rw [ρ.map_mul]
    have hh := congrArg (fun v : ZMod p × W => v.2)
      (primeOrbitCentralizer_formula p (ρ g) (hρ g)
        (ρ h (0, w)).1 (ρ h (0, w)).2)
    exact hh

@[simp] theorem primeOrbitParentAction_apply (ρ : G →* Equiv.Perm (ZMod p × W))
    (hρ : ∀ g, CommutesPrimeTranslations p (ρ g)) (g : G) (w : W) :
    primeOrbitParentAction p ρ hρ g w = (ρ g (0, w)).2 := rfl

theorem primeOrbitParentAction_normalForm (ρ : G →* Equiv.Perm (ZMod p × W))
    (hρ : ∀ g, CommutesPrimeTranslations p (ρ g)) (g : G) :
    ρ g = primeOrbitRelabel p (primeOrbitParentAction p ρ hρ g)
      (fun w => (ρ g (0, w)).1) :=
  primeOrbitCentralizer_normalForm p (ρ g) (hρ g)

end ParentAction

theorem primeOrbitMomentRetraction_centralizer (K : Type*) [CommRing K]
    (e : (ZMod p × W) ≃ (ZMod p × U)) (he : CommutesPrimeTranslations p e)
    (f : MvPolynomial (ZMod p × W) K) :
    primeOrbitMomentRetraction p K (MvPolynomial.rename e f) =
      MvPolynomial.rename (primeOrbitLabelEquiv p e he) (primeOrbitMomentRetraction p K f) := by
  have h := primeOrbitMomentRetraction_relabel p K (primeOrbitLabelEquiv p e he)
    (fun w => (e (0, w)).1) f
  rw [← primeOrbitCentralizer_normalForm p e he] at h
  exact h

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FiniteSubsetSeries.lean -/
section

section
/-! # Finite subset generating polynomials

These are literal finite sums. Their coefficients recover fixed-cardinality
subset sums, and the product decomposition records the decomposition of a
subset of a product into its fibres.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
namespace FourPapers.Universal
open Classical Finset

section Subsets
variable {V R : Type*} [Fintype V] [CommRing R]

theorem sum_finset_card_ite (f : Finset V → R) (n : ℕ) :
    (∑ s : Finset V, if s.card = n then f s else 0) =
      ∑ s : {s : Finset V // s.card = n}, f s.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun s => by simp) f

def finiteSubsetSeries (f : Finset V → R) : Polynomial R :=
  ∑ s : Finset V, Polynomial.monomial s.card (f s)

theorem finiteSubsetSeries_coeff (f : Finset V → R) (n : ℕ) :
    (finiteSubsetSeries f).coeff n = ∑ s : {s : Finset V // s.card = n}, f s.val := by
  simp only [finiteSubsetSeries, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  exact sum_finset_card_ite f n

theorem polynomial_prod_monomial {I : Type*} (s : Finset I) (n : I → ℕ) (c : I → R) :
    (∏ i ∈ s, Polynomial.monomial (n i) (c i)) =
      Polynomial.monomial (∑ i ∈ s, n i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih,
        Polynomial.monomial_mul_monomial]

theorem finiteSubsetSeries_prod (f : V → R) :
    finiteSubsetSeries (fun s => ∏ v ∈ s, f v) =
      ∏ v : V, (1 + Polynomial.monomial 1 (f v)) := by
  rw [Finset.prod_one_add]
  change (∑ s : Finset V, Polynomial.monomial s.card (∏ v ∈ s, f v)) = _
  have hu : (Finset.univ : Finset V).powerset = (Finset.univ : Finset (Finset V)) := by
    ext s
    simp
  rw [hu]
  apply Finset.sum_congr rfl
  intro s hs
  rw [polynomial_prod_monomial]
  simp

end Subsets

section ProductSubsets
variable {V W : Type*} [Fintype V] [Fintype W]

def subsetFiber (s : Finset (V × W)) (w : W) : Finset V :=
  Finset.univ.filter (fun v => (v, w) ∈ s)

@[simp] theorem mem_subsetFiber (s : Finset (V × W)) (w : W) (v : V) :
    v ∈ subsetFiber s w ↔ (v, w) ∈ s := by simp [subsetFiber]

def subsetFibersEquiv : Finset (V × W) ≃ (W → Finset V) where
  toFun := subsetFiber
  invFun f := Finset.univ.filter (fun v => v.1 ∈ f v.2)
  left_inv s := by ext v; simp
  right_inv f := by funext w; ext v; simp

theorem subsetFiber_card_sum (s : Finset (V × W)) :
    (∑ w : W, (subsetFiber s w).card) = s.card := by
  calc
    _ = ∑ w : W, ∑ v : V, if (v, w) ∈ s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [subsetFiber, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ v : V, ∑ w : W, if (v, w) ∈ s then 1 else 0 := Finset.sum_comm
    _ = ∑ v : V × W, if v ∈ s then 1 else 0 := by rw [Fintype.sum_prod_type]
    _ = s.card := by simp

variable {R : Type*} [CommRing R]

theorem finiteSubsetSeries_fibers (f : W → Finset V → R) :
    finiteSubsetSeries (fun s : Finset (V × W) => ∏ w : W, f w (subsetFiber s w)) =
      ∏ w : W, finiteSubsetSeries (f w) := by
  unfold finiteSubsetSeries
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (subsetFibersEquiv (V := V) (W := W))
  intro s
  rw [polynomial_prod_monomial]
  simp only [subsetFibersEquiv, Equiv.coe_fn_mk, subsetFiber_card_sum]

end ProductSubsets

section Elementary
variable (V K : Type*) [Fintype V] [CommRing K]

def elementarySubsetSeries : Polynomial (MvPolynomial V K) :=
  finiteSubsetSeries (fun s => ∏ v ∈ s, MvPolynomial.X v)

theorem elementarySubsetSeries_coeff (n : ℕ) :
    (elementarySubsetSeries V K).coeff n = MvPolynomial.esymm V K n := by
  rw [elementarySubsetSeries, finiteSubsetSeries_coeff, MvPolynomial.esymm_eq_sum_subtype]

theorem elementarySubsetSeries_prod :
    elementarySubsetSeries V K =
      ∏ v : V, (1 + Polynomial.monomial 1 (MvPolynomial.X v)) :=
  finiteSubsetSeries_prod _

theorem elementarySubsetSeries_expand (p : ℕ) :
    Polynomial.expand (MvPolynomial V K) p (elementarySubsetSeries V K) =
      ∏ v : V, (1 + Polynomial.monomial p (MvPolynomial.X v)) := by
  rw [elementarySubsetSeries_prod, map_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [map_add, map_one, Polynomial.expand_monomial, one_mul]

theorem elementarySubsetSeries_expand_coeff (p : ℕ) (hp : 0 < p) (n : ℕ) :
    (∏ v : V, (1 + Polynomial.monomial p (MvPolynomial.X v))).coeff n =
      if p ∣ n then MvPolynomial.esymm V K (n / p) else 0 := by
  rw [← elementarySubsetSeries_expand, Polynomial.coeff_expand hp,
    elementarySubsetSeries_coeff]

end Elementary
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitMomentParameters.lean -/
section

section
/-! # Every elementary parameter under the integral orbit retraction

Finite subset generating polynomials turn the tensor product of the checked
one-orbit identities into the complete elementary-symmetric parameter law.
All coefficients are integral; neither an averaging denominator nor a
positive-characteristic assumption occurs.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

section SubsetMonomials
variable {V K : Type*} [Fintype V] [CommRing K]

def finiteSubsetExponent (s : Finset V) : V →₀ ℕ :=
  ∑ v ∈ s, Finsupp.single v 1

@[simp] theorem finiteSubsetExponent_apply (s : Finset V) (v : V) :
    finiteSubsetExponent s v = if v ∈ s then 1 else 0 := by
  simp [finiteSubsetExponent, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem finiteSubsetProduct_eq_monomial (s : Finset V) :
    (∏ v ∈ s, (X v : MvPolynomial V K)) = monomial (finiteSubsetExponent s) 1 := by
  rw [finiteSubsetExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem esymm_mul_monomial_subset (i : ℕ) (a : V →₀ ℕ) :
    MvPolynomial.esymm V K i * monomial a 1 =
      ∑ s : {s : Finset V // s.card = i}, monomial (a + finiteSubsetExponent s.val) 1 := by
  rw [MvPolynomial.esymm_eq_sum_subtype, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [finiteSubsetProduct_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, add_comm]

theorem esymm_eq_zero_of_card_lt (i : ℕ) (hi : Fintype.card V < i) :
    MvPolynomial.esymm V K i = 0 := by
  unfold MvPolynomial.esymm
  rw [Finset.powersetCard_eq_empty.mpr (by simpa only [Finset.card_univ] using hi)]
  exact Finset.sum_empty

end SubsetMonomials

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]
variable {W : Type*} [Fintype W]

def primeSingleValue (w : W) (a : ZMod p →₀ ℕ) : MvPolynomial W K :=
  Polynomial.eval₂RingHom MvPolynomial.C (X w) (primeMomentRetraction p K (monomial a 1))

theorem primeSingleValue_formula (w : W) (a : ZMod p →₀ ℕ) :
    primeSingleValue p K w a =
      monomial (Finsupp.single w (a.degree / p)) (primeMomentCoefficient p K a) := by
  rw [primeSingleValue, primeMomentRetraction_monomial_one,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    MvPolynomial.C_mul_X_pow_eq_monomial]

theorem primeSingleSeries_coeff (w : W) (a : ZMod p →₀ ℕ) (i : ℕ) :
    (finiteSubsetSeries (fun s : Finset (ZMod p) =>
      primeSingleValue p K w (a + cyclicSubsetExponent p s))).coeff i =
      Polynomial.eval₂RingHom MvPolynomial.C (X w)
        (primeMomentRetraction p K (MvPolynomial.esymm (ZMod p) K i * monomial a 1)) := by
  rw [finiteSubsetSeries_coeff, esymm_mul_monomial_subset, map_sum, map_sum]
  rfl

theorem primeSingleSeries (w : W) (a : ZMod p →₀ ℕ) :
    finiteSubsetSeries (fun s : Finset (ZMod p) => primeSingleValue p K w (a + cyclicSubsetExponent p s)) =
      Polynomial.C (primeSingleValue p K w a) * (1 + Polynomial.monomial p (X w)) := by
  apply Polynomial.ext
  intro i
  rw [primeSingleSeries_coeff, mul_add, mul_one, Polynomial.C_mul_monomial,
    Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial]
  by_cases h0 : i = 0
  · subst i
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    simp only [MvPolynomial.esymm_zero, one_mul, ite_true, if_neg hp, add_zero]
    rfl
  · by_cases hp : i = p
    · subst i
      have ht : MvPolynomial.esymm (ZMod p) K p = ∏ x : ZMod p, X x := by
        unfold MvPolynomial.esymm
        have hpowerset : Finset.powersetCard p (Finset.univ : Finset (ZMod p)) = {Finset.univ} := by
          simpa only [Finset.card_univ, ZMod.card] using
            Finset.powersetCard_self (Finset.univ : Finset (ZMod p))
        rw [hpowerset, Finset.sum_singleton]
      rw [ht, primeMomentRetraction_top, map_mul]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, if_neg h0,
        if_pos rfl, zero_add]
      exact mul_comm _ _
    · have hzero : primeMomentRetraction p K
          (MvPolynomial.esymm (ZMod p) K i * monomial a 1) = 0 := by
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · exact primeMomentRetraction_interior_esymm p K i (Nat.pos_of_ne_zero h0) hlt _
        · rw [esymm_eq_zero_of_card_lt i (by simpa only [ZMod.card] using hgt),
            zero_mul, map_zero]
      rw [hzero, map_zero]
      simp only [if_neg h0, if_neg (Ne.symm hp), zero_add]

theorem primeOrbitBlock_subset (s : Finset (ZMod p × W)) (w : W) :
    primeOrbitBlock p (finiteSubsetExponent s) w = cyclicSubsetExponent p (subsetFiber s w) := by
  ext x
  simp only [primeOrbitBlock_apply, finiteSubsetExponent_apply]
  have he : cyclicSubsetExponent p (subsetFiber s w) = finiteSubsetExponent (subsetFiber s w) := rfl
  rw [he, finiteSubsetExponent_apply]
  simp only [mem_subsetFiber]
  split_ifs <;> rfl

theorem primeOrbitMomentRetraction_product (a : (ZMod p × W) →₀ ℕ) :
    primeOrbitMomentRetraction p K (monomial a 1) =
      ∏ w : W, primeSingleValue p K w (primeOrbitBlock p a w) := by
  rw [primeOrbitMomentRetraction_monomial_one]
  simp_rw [primeSingleValue_formula]
  rw [← MvPolynomial.monomial_sum_prod]
  have he : primeOrbitExponent p a =
      ∑ w : W, Finsupp.single w ((primeOrbitBlock p a w).degree / p) := by
    ext w
    simp [primeOrbitExponent_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [he]
  rfl

theorem primeOrbitMomentSeries (a : (ZMod p × W) →₀ ℕ) :
    finiteSubsetSeries (fun s : Finset (ZMod p × W) =>
      primeOrbitMomentRetraction p K (monomial (a + finiteSubsetExponent s) 1)) =
      Polynomial.C (primeOrbitMomentRetraction p K (monomial a 1)) *
        Polynomial.expand (MvPolynomial W K) p (elementarySubsetSeries W K) := by
  have hf : (fun s : Finset (ZMod p × W) =>
      primeOrbitMomentRetraction p K (monomial (a + finiteSubsetExponent s) 1)) =
      fun s => ∏ w : W,
        primeSingleValue p K w (primeOrbitBlock p a w + cyclicSubsetExponent p (subsetFiber s w)) := by
    funext s
    rw [primeOrbitMomentRetraction_product]
    simp only [primeOrbitBlock_add, primeOrbitBlock_subset]
  rw [hf, finiteSubsetSeries_fibers (fun w (s : Finset (ZMod p)) =>
    primeSingleValue p K w (primeOrbitBlock p a w + cyclicSubsetExponent p s))]
  simp_rw [primeSingleSeries]
  rw [Finset.prod_mul_distrib, ← map_prod, ← primeOrbitMomentRetraction_product,
    elementarySubsetSeries_expand]

theorem primeOrbitMomentRetraction_parameter_monomial (i : ℕ) (a : (ZMod p × W) →₀ ℕ) :
    primeOrbitMomentRetraction p K (MvPolynomial.esymm (ZMod p × W) K i * monomial a 1) =
      if p ∣ i then MvPolynomial.esymm W K (i / p) *
        primeOrbitMomentRetraction p K (monomial a 1) else 0 := by
  have h := congrArg (fun f : Polynomial (MvPolynomial W K) => f.coeff i)
    (primeOrbitMomentSeries p K a)
  rw [finiteSubsetSeries_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_expand (Fact.out : p.Prime).pos, elementarySubsetSeries_coeff] at h
  rw [esymm_mul_monomial_subset, map_sum]
  rw [h]
  split_ifs <;> simp only [mul_comm, mul_zero, zero_mul]

/-- Complete parameter compatibility for every elementary parameter, with
its full rank range and over every commutative coefficient ring. -/
theorem primeOrbitMomentRetraction_parameter (i : ℕ) (f : MvPolynomial (ZMod p × W) K) :
    primeOrbitMomentRetraction p K (MvPolynomial.esymm (ZMod p × W) K i * f) =
      if p ∣ i then MvPolynomial.esymm W K (i / p) * primeOrbitMomentRetraction p K f else 0 := by
  let A : MvPolynomial W K := if p ∣ i then MvPolynomial.esymm W K (i / p) else 0
  have h : (primeOrbitMomentRetraction p K).comp
      (LinearMap.mulLeft K (MvPolynomial.esymm (ZMod p × W) K i)) =
      (LinearMap.mulLeft K A).comp (primeOrbitMomentRetraction p K) := by
    apply (MvPolynomial.basisMonomials (ZMod p × W) K).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, MvPolynomial.coe_basisMonomials]
    rw [primeOrbitMomentRetraction_parameter_monomial]
    simp only [A, ite_mul, zero_mul]
  have hh := LinearMap.congr_fun h f
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, A, ite_mul, zero_mul] using hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitMomentRestriction.lean -/
section

section
/-! # Restriction to unions of complete prime orbits

The commuting square uses Mathlib's literal polynomial restriction
`killCompl`, which sends omitted variables to zero. No abstract replacement
of the face restriction is introduced.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime]
variable {U W : Type*} [Fintype U] [Fintype W]

def primeOrbitEmbedding (i : U ↪ W) : (ZMod p × U) ↪ (ZMod p × W) where
  toFun v := (v.1, i v.2)
  inj' a b h := Prod.ext (congrArg (fun v : ZMod p × W => v.1) h)
    (i.injective (congrArg (fun v : ZMod p × W => v.2) h))

theorem primeOrbitBlock_embedding (i : U ↪ W) (a : (ZMod p × U) →₀ ℕ) (u : U) :
    primeOrbitBlock p (a.mapDomain (primeOrbitEmbedding p i)) (i u) = primeOrbitBlock p a u := by
  ext x
  change (a.mapDomain (primeOrbitEmbedding p i)) (primeOrbitEmbedding p i (x, u)) = a (x, u)
  exact Finsupp.mapDomain_apply_of_injective (primeOrbitEmbedding p i).injective a (x, u)

theorem primeOrbitBlock_embedding_outside (i : U ↪ W) (a : (ZMod p × U) →₀ ℕ)
    (w : W) (hw : w ∉ Set.range i) :
    primeOrbitBlock p (a.mapDomain (primeOrbitEmbedding p i)) w = 0 := by
  ext x
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨⟨y, u⟩, h⟩
  exact hw ⟨u, congrArg Prod.snd h⟩

theorem primeOrbitExponent_embedding (i : U ↪ W) (a : (ZMod p × U) →₀ ℕ) :
    primeOrbitExponent p (a.mapDomain (primeOrbitEmbedding p i)) =
      (primeOrbitExponent p a).mapDomain i := by
  ext w
  by_cases hw : w ∈ Set.range i
  · obtain ⟨u, rfl⟩ := hw
    rw [primeOrbitExponent_apply, primeOrbitBlock_embedding,
      Finsupp.mapDomain_apply_of_injective i.injective, primeOrbitExponent_apply]
  · rw [primeOrbitExponent_apply, primeOrbitBlock_embedding_outside p i a w hw,
      map_zero, Nat.zero_div, Finsupp.mapDomain_of_notMem_range _ _ hw]

variable (K : Type*) [CommRing K]

theorem primeOrbitCoefficient_embedding (i : U ↪ W) (a : (ZMod p × U) →₀ ℕ) :
    primeOrbitCoefficient p K (a.mapDomain (primeOrbitEmbedding p i)) =
      primeOrbitCoefficient p K a := by
  unfold primeOrbitCoefficient
  symm
  apply Fintype.prod_of_injective i i.injective
  · intro w hw
    rw [primeOrbitBlock_embedding_outside p i a w hw, primeMomentCoefficient_zero]
  · intro u
    rw [primeOrbitBlock_embedding]

theorem primeOrbitMomentRetraction_embedding (i : U ↪ W)
    (f : MvPolynomial (ZMod p × U) K) :
    primeOrbitMomentRetraction p K (rename (primeOrbitEmbedding p i) f) =
      rename i (primeOrbitMomentRetraction p K f) := by
  have h : (primeOrbitMomentRetraction (W := W) p K).comp
      (rename (primeOrbitEmbedding p i)).toLinearMap =
      (rename i).toLinearMap.comp (primeOrbitMomentRetraction (W := U) p K) := by
    apply (MvPolynomial.basisMonomials (ZMod p × U) K).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    rw [rename_monomial, primeOrbitMomentRetraction_monomial_one,
      primeOrbitMomentRetraction_monomial_one, rename_monomial,
      primeOrbitExponent_embedding, primeOrbitCoefficient_embedding]
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using LinearMap.congr_fun h f

theorem primeOrbitExponent_nonzero_of_input (a : (ZMod p × W) →₀ ℕ)
    (ha : primeOrbitCoefficient p K a ≠ 0) (x : ZMod p) (w : W) (hx : a (x, w) ≠ 0) :
    primeOrbitExponent p a w ≠ 0 := by
  have hd : (primeOrbitBlock p a w).degree ≠ 0 := by
    intro h
    have hz := (Finsupp.degree_eq_zero_iff _).mp h
    exact hx (congrArg (fun b : ZMod p →₀ ℕ => b x) hz)
  intro hzero
  have hdiv := Nat.mul_div_cancel' (primeOrbitCoefficient_nonzero_dvd p K a ha w)
  change p * primeOrbitExponent p a w = (primeOrbitBlock p a w).degree at hdiv
  rw [hzero, mul_zero] at hdiv
  exact hd hdiv.symm

/-- Naturality for every inclusion of a union of full prime orbits. -/
theorem primeOrbitMomentRetraction_restriction (i : U ↪ W)
    (f : MvPolynomial (ZMod p × W) K) :
    primeOrbitMomentRetraction p K
        (MvPolynomial.killCompl (primeOrbitEmbedding p i).injective f) =
      MvPolynomial.killCompl i.injective (primeOrbitMomentRetraction p K f) := by
  have h : (primeOrbitMomentRetraction (W := U) p K).comp
      (MvPolynomial.killCompl (primeOrbitEmbedding p i).injective).toLinearMap =
      (MvPolynomial.killCompl i.injective).toLinearMap.comp
        (primeOrbitMomentRetraction (W := W) p K) := by
    apply (MvPolynomial.basisMonomials (ZMod p × W) K).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    by_cases ha : ↑a.support ⊆ Set.range (primeOrbitEmbedding p i)
    · let b := a.comapDomain (primeOrbitEmbedding p i) (primeOrbitEmbedding p i).injective.injOn
      have he : b.mapDomain (primeOrbitEmbedding p i) = a :=
        Finsupp.mapDomain_comapDomain _ (primeOrbitEmbedding p i).injective a ha
      rw [← he, ← rename_monomial, MvPolynomial.killCompl_rename_app,
        primeOrbitMomentRetraction_embedding, MvPolynomial.killCompl_rename_app]
    · rw [MvPolynomial.killCompl_monomial_eq_zero_of_not_subset _ (1 : K) ha, map_zero]
      symm
      rw [primeOrbitMomentRetraction_monomial_one]
      by_cases hc : primeOrbitCoefficient p K a = 0
      · rw [hc, map_zero, map_zero]
      · obtain ⟨⟨x, w⟩, hx, hw⟩ := Set.not_subset.mp ha
        have hwi : w ∉ Set.range i := by
          rintro ⟨u, hu⟩
          exact hw ⟨(x, u), Prod.ext rfl hu⟩
        have hwpos : w ∈ (primeOrbitExponent p a).support :=
          Finsupp.mem_support_iff.mpr
            (primeOrbitExponent_nonzero_of_input p K a hc x w (Finsupp.mem_support_iff.mp hx))
        exact MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range i.injective
          (primeOrbitCoefficient p K a) hwpos hwi
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using LinearMap.congr_fun h f

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitMomentDegree.lean -/
section

section
/-! # Exact ordinary-degree control for the integral retraction

The degree used here is the sum of the exponent coordinates, exactly the
ordinary degree of an actual multivariate monomial. The statements quantify
over all finite-support polynomials and are independent of a basis choice.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]
variable {W V : Type*} [Fintype W] [Fintype V]

theorem primeOrbitMomentRetraction_support_degree
    (f : MvPolynomial (ZMod p × W) K) (n : ℕ)
    (hf : ∀ a ∈ f.support, a.degree = n)
    (b : W →₀ ℕ) (hb : b ∈ (primeOrbitMomentRetraction p K f).support) :
    p * b.degree = n := by
  have hnz := MvPolynomial.mem_support_iff.mp hb
  have he : (primeOrbitMomentRetraction p K f).coeff b =
      ∑ a ∈ f.support,
        if primeOrbitExponent p a = b then f.coeff a * primeOrbitCoefficient p K a else 0 := by
    conv_lhs => rw [f.as_sum, map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [primeOrbitMomentRetraction_monomial, MvPolynomial.coeff_monomial]
  rw [he] at hnz
  obtain ⟨a, ha, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  by_cases hab : primeOrbitExponent p a = b
  · rw [if_pos hab] at hterm
    have hc : primeOrbitCoefficient p K a ≠ 0 := by
      intro hc
      exact hterm (by rw [hc, mul_zero])
    simpa only [hab, hf a ha] using primeOrbitCoefficient_nonzero_degree p K a hc
  · exact False.elim (hterm (if_neg hab))

theorem primeOrbitMomentRetraction_zero_of_degree_not_dvd
    (f : MvPolynomial (ZMod p × W) K) (n : ℕ)
    (hf : ∀ a ∈ f.support, a.degree = n) (hn : ¬ p ∣ n) :
    primeOrbitMomentRetraction p K f = 0 := by
  apply MvPolynomial.ext
  intro b
  rw [MvPolynomial.coeff_zero]
  by_contra hb
  have he := primeOrbitMomentRetraction_support_degree p K f n hf b
    (MvPolynomial.mem_support_iff.mpr hb)
  exact hn ⟨b.degree, he.symm⟩

theorem primeOrbitMomentRetraction_degree
    (f : MvPolynomial (ZMod p × W) K) (n : ℕ)
    (hf : ∀ a ∈ f.support, a.degree = n) :
    ∀ b ∈ (primeOrbitMomentRetraction p K f).support, b.degree = n / p := by
  intro b hb
  rw [← primeOrbitMomentRetraction_support_degree p K f n hf b hb,
    Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]

/-- Transport from any specified free-orbit parametrization of the original
vertex set. The input remains the actual polynomial ring on those vertices. -/
def primeFreeOrbitRetraction (e : V ≃ ZMod p × W) :
    MvPolynomial V K →ₗ[K] MvPolynomial W K :=
  (primeOrbitMomentRetraction p K).comp (MvPolynomial.rename e).toLinearMap

@[simp] theorem primeFreeOrbitRetraction_apply (e : V ≃ ZMod p × W)
    (f : MvPolynomial V K) :
    primeFreeOrbitRetraction p K e f = primeOrbitMomentRetraction p K (MvPolynomial.rename e f) := rfl

@[simp] theorem primeFreeOrbitRetraction_one (e : V ≃ ZMod p × W) :
    primeFreeOrbitRetraction p K e 1 = 1 := by
  rw [primeFreeOrbitRetraction_apply, map_one, primeOrbitMomentRetraction_one]

theorem primeFreeOrbitRetraction_parameter (e : V ≃ ZMod p × W)
    (i : ℕ) (f : MvPolynomial V K) :
    primeFreeOrbitRetraction p K e (MvPolynomial.esymm V K i * f) =
      if p ∣ i then MvPolynomial.esymm W K (i / p) * primeFreeOrbitRetraction p K e f else 0 := by
  rw [primeFreeOrbitRetraction_apply, map_mul, MvPolynomial.rename_esymm,
    primeOrbitMomentRetraction_parameter]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerActions.lean -/
section


section

/-! # Freeness of the nonfixed chain basis for a cyclic prime-power group

In a cyclic p-group, the subgroup of order p lies in every nontrivial cyclic
subgroup. A permutation preserving a finite chain and its rank fixes every
member of the chain. Consequently a chain monomial containing a face that
is not fixed by the order-p subgroup has trivial stabilizer. This is the
integral regular-module input in the prime-power template construction.
-/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

section PrimeSubgroup
variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/-- The minimal nontrivial subgroup is contained in the subgroup generated by
any nonidentity element; this statement uses actual subgroup cardinalities. -/
theorem primeSubgroup_le_zpowers (hG : IsPGroup p G)
    (Z : Subgroup G) (hZ : Nat.card Z = p) {g : G} (hg : g ≠ 1) :
    Z ≤ Subgroup.zpowers g := by
  apply IsCyclic.subgroup_le_iff_card_dvd.mpr
  rw [hZ, Nat.card_zpowers]
  exact hG.dvd_orderOf hg

theorem primeSubgroup_fixed_of_nonidentity_fixed
    {I : Type*} [MulAction G I] (hG : IsPGroup p G)
    (Z : Subgroup G) (hZ : Nat.card Z = p)
    {g : G} (hg : g ≠ 1) {i : I} (hi : g • i = i) :
    ∀ z : Z, z.val • i = i := by
  have hle : Z ≤ MulAction.stabilizer G i :=
    (primeSubgroup_le_zpowers hG Z hZ hg).trans (Subgroup.zpowers_le.mpr hi)
  intro z
  exact hle z.property

end PrimeSubgroup

section Chain
variable {G I : Type*} [Group G] [PartialOrder I] [MulAction G I]
variable (rank : I → ℕ) (hrank : StrictMono rank)
variable (hpres : ∀ (g : G) (i : I), rank (g • i) = rank i)

include hrank hpres

/-- A rank-preserving permutation cannot move a member inside a finite chain. -/
theorem chainExponent_fixed_support
    (a : I →₀ ℕ)
    (hchain : ∀ i ∈ a.support, ∀ j ∈ a.support, i ≤ j ∨ j ≤ i)
    (g : G) (hfix : Finsupp.mapDomain (fun i => g • i) a = a)
    (i : I) (hi : i ∈ a.support) : g • i = i := by
  have hgi : g • i ∈ a.support := by
    rw [← hfix]
    apply Finsupp.mem_support_iff.mpr
    rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective g)]
    exact Finsupp.mem_support_iff.mp hi
  rcases hchain i hi (g • i) hgi with h | h
  · by_contra hne
    have hlt := hrank (lt_of_le_of_ne h (Ne.symm hne))
    rw [hpres] at hlt
    exact (lt_irrefl _ hlt).elim
  · by_contra hne
    have hlt := hrank (lt_of_le_of_ne h hne)
    rw [hpres] at hlt
    exact (lt_irrefl _ hlt).elim

/-- This is the literal map-domain action on chain exponents. The condition
excludes exactly the basis of the fixed-face quotient, without requiring
invertibility of any group order in a coefficient ring. -/
theorem nonfixedChainExponent_stabilizer_trivial
    {p : ℕ} [Fact p.Prime] [Finite G] [IsCyclic G]
    (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
    (a : I →₀ ℕ)
    (hchain : ∀ i ∈ a.support, ∀ j ∈ a.support, i ≤ j ∨ j ≤ i)
    (hnonfixed : ∃ i ∈ a.support, ∃ z : Z, z.val • i ≠ i)
    (g : G) (hfix : Finsupp.mapDomain (fun i => g • i) a = a) : g = 1 := by
  by_contra hg
  obtain ⟨i, hi, z, hz⟩ := hnonfixed
  have hgi := chainExponent_fixed_support rank hrank hpres a hchain g hfix i hi
  exact hz (primeSubgroup_fixed_of_nonidentity_fixed hG Z hZ hg hgi z)

end Chain
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedFaceGeometry.lean -/
section

section
/-! # Faces fixed by the order-p subgroup of a free orbit action

For the literal free action on `ZMod p × W`, the fixed nonempty faces are
exactly the products `univ × F`.  This identifies their chains with the
ordinary Boolean chains on the orbit set, including all exponent vectors.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]
variable {W U : Type*} [Fintype W] [Fintype U]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq U := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × U) := Classical.decEq _

/-- A face on the orbit set gives the union of precisely those full orbits. -/
def primeFixedFaceEmbedding : BooleanFace W ↪ BooleanFace (ZMod p × W) where
  toFun F := ⟨Finset.univ ×ˢ F.val, by
    obtain ⟨w, hw⟩ := F.property
    exact ⟨(0, w), Finset.mem_product.mpr ⟨Finset.mem_univ _, hw⟩⟩⟩
  inj' F G h := by
    apply Subtype.ext
    ext w
    have hw := congrArg (fun H : BooleanFace (ZMod p × W) => (0, w) ∈ H.val) h
    simpa only [Finset.mem_product, Finset.mem_univ, true_and] using Iff.of_eq hw

@[simp] theorem primeFixedFaceEmbedding_val (F : BooleanFace W) :
    (primeFixedFaceEmbedding p F).val = Finset.univ ×ˢ F.val := rfl

@[simp] theorem mem_primeFixedFaceEmbedding (F : BooleanFace W) (x : ZMod p) (w : W) :
    (x, w) ∈ (primeFixedFaceEmbedding p F).val ↔ w ∈ F.val := by
  simp only [primeFixedFaceEmbedding_val, Finset.mem_product, Finset.mem_univ, true_and]

@[simp] theorem primeFixedFaceEmbedding_card (F : BooleanFace W) :
    (primeFixedFaceEmbedding p F).val.card = p * F.val.card := by
  simp only [primeFixedFaceEmbedding_val, Finset.card_product, Finset.card_univ, ZMod.card]

@[simp] theorem primeFixedFaceEmbedding_subset (F G : BooleanFace W) :
    (primeFixedFaceEmbedding p F).val ⊆ (primeFixedFaceEmbedding p G).val ↔
      F.val ⊆ G.val := by
  constructor
  · intro h w hw
    exact (mem_primeFixedFaceEmbedding p G 0 w).mp
      (h ((mem_primeFixedFaceEmbedding p F 0 w).mpr hw))
  · intro h v hv
    exact (mem_primeFixedFaceEmbedding p G v.1 v.2).mpr
      (h ((mem_primeFixedFaceEmbedding p F v.1 v.2).mp hv))

/-- The range criterion uses actual membership in every orbit. -/
theorem primeFixedFaceEmbedding_range_iff (F : BooleanFace (ZMod p × W)) :
    F ∈ Set.range (primeFixedFaceEmbedding (W := W) p) ↔
      ∀ (x y : ZMod p) (w : W), (x, w) ∈ F.val ↔ (y, w) ∈ F.val := by
  constructor
  · rintro ⟨G, rfl⟩ x y w
    rw [mem_primeFixedFaceEmbedding, mem_primeFixedFaceEmbedding]
  · intro h
    let G : BooleanFace W := ⟨F.val.image Prod.snd, F.property.image Prod.snd⟩
    refine ⟨G, Subtype.ext ?_⟩
    ext v
    rw [mem_primeFixedFaceEmbedding]
    constructor
    · intro hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      exact (h u.1 v.1 v.2).mp (by simpa only [← he] using hu)
    · intro hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Being fixed by all order-p translations is exactly being a full-orbit face. -/
theorem primeFixedFaceEmbedding_range_iff_fixed (F : BooleanFace (ZMod p × W)) :
    F ∈ Set.range (primeFixedFaceEmbedding (W := W) p) ↔
      ∀ t : ZMod p,
        F.val.image (primeOrbitRelabel p (Equiv.refl W) (fun _ => t)) = F.val := by
  rw [primeFixedFaceEmbedding_range_iff]
  constructor
  · intro h t
    ext v
    constructor
    · rintro hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      subst v
      exact (h u.1 (t + u.1) u.2).mp hu
    · intro hv
      refine Finset.mem_image.mpr ⟨(v.1 - t, v.2), ?_, ?_⟩
      · exact (h v.1 (v.1 - t) v.2).mp hv
      · apply Prod.ext
        · change t + (v.1 - t) = v.1
          exact add_sub_cancel _ _
        · rfl
  · intro h x y w
    have himp : ∀ x y : ZMod p, (x, w) ∈ F.val → (y, w) ∈ F.val := by
      intro x y hx
      rw [← h (y - x)]
      refine Finset.mem_image.mpr ⟨(x, w), hx, ?_⟩
      apply Prod.ext
      · exact sub_add_cancel y x
      · rfl
    exact ⟨himp x y, himp y x⟩

theorem primeFixedFaceEmbedding_relabel (σ : W ≃ U) (g : W → ZMod p)
    (F : BooleanFace W) :
    booleanFaceEmbedding (primeOrbitRelabel p σ g).toEmbedding
        (primeFixedFaceEmbedding p F) =
      primeFixedFaceEmbedding p (booleanFaceEmbedding σ.toEmbedding F) := by
  apply Subtype.ext
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hv
    apply (mem_primeFixedFaceEmbedding p (booleanFaceEmbedding σ.toEmbedding F) v.1 v.2).mpr
    refine Finset.mem_map.mpr ⟨u.2, (mem_primeFixedFaceEmbedding p F u.1 u.2).mp hu, ?_⟩
    exact congrArg (fun z : ZMod p × U => z.2) he
  · intro hv
    have hw := (mem_primeFixedFaceEmbedding p (booleanFaceEmbedding σ.toEmbedding F) v.1 v.2).mp hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hw
    refine Finset.mem_map.mpr ⟨(v.1 - g w, w),
      (mem_primeFixedFaceEmbedding p F (v.1 - g w) w).mpr hw, ?_⟩
    apply Prod.ext
    · exact add_sub_cancel _ _
    · exact he

theorem isChainExponent_map_primeFixedFaceEmbedding
    {a : BooleanFace W →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a.mapDomain (primeFixedFaceEmbedding p)) := by
  intro F hF G hG
  rw [Finsupp.mapDomain_support_of_injective (primeFixedFaceEmbedding p).injective] at hF hG
  obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
  exact (ha F' hF' G' hG').imp
    (primeFixedFaceEmbedding_subset p F' G').mpr
    (primeFixedFaceEmbedding_subset p G' F').mpr

theorem isChainExponent_comap_primeFixedFaceEmbedding
    {a : BooleanFace (ZMod p × W) →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a.comapDomain (primeFixedFaceEmbedding p)
      (primeFixedFaceEmbedding p).injective.injOn) := by
  intro F hF G hG
  have hF' : primeFixedFaceEmbedding p F ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hF
  have hG' : primeFixedFaceEmbedding p G ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hG
  exact (ha _ hF' _ hG').imp
    (primeFixedFaceEmbedding_subset p F G).mp
    (primeFixedFaceEmbedding_subset p G F).mp

theorem isChainExponent_map_primeFixedFaceEmbedding_iff (a : BooleanFace W →₀ ℕ) :
    IsChainExponent (a.mapDomain (primeFixedFaceEmbedding p)) ↔ IsChainExponent a := by
  refine ⟨fun h => ?_, isChainExponent_map_primeFixedFaceEmbedding p⟩
  have hc := isChainExponent_comap_primeFixedFaceEmbedding p h
  exact (Finsupp.comapDomain_mapDomain _ (primeFixedFaceEmbedding p).injective a) ▸ hc

def primeFixedChainEmbedding : BooleanChainExponent W ↪
    BooleanChainExponent (ZMod p × W) where
  toFun a := ⟨a.val.mapDomain (primeFixedFaceEmbedding p),
    isChainExponent_map_primeFixedFaceEmbedding p a.property⟩
  inj' a b h := Subtype.ext
    (Finsupp.mapDomain_injective (primeFixedFaceEmbedding p).injective (congrArg Subtype.val h))

theorem primeFixedChainEmbedding_range_iff (a : BooleanChainExponent (ZMod p × W)) :
    a ∈ Set.range (primeFixedChainEmbedding (W := W) p) ↔
      ∀ F ∈ a.val.support, F ∈ Set.range (primeFixedFaceEmbedding (W := W) p) := by
  constructor
  · rintro ⟨b, rfl⟩ F hF
    exact Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hF)
  · intro h
    refine ⟨⟨a.val.comapDomain (primeFixedFaceEmbedding p)
        (primeFixedFaceEmbedding p).injective.injOn,
      isChainExponent_comap_primeFixedFaceEmbedding p a.property⟩, ?_⟩
    apply Subtype.ext
    exact Finsupp.mapDomain_comapDomain _ (primeFixedFaceEmbedding p).injective a.val h

theorem primeFixedChainEmbedding_not_range_iff (a : BooleanChainExponent (ZMod p × W)) :
    a ∉ Set.range (primeFixedChainEmbedding (W := W) p) ↔
      ∃ F ∈ a.val.support, F ∉ Set.range (primeFixedFaceEmbedding (W := W) p) := by
  rw [primeFixedChainEmbedding_range_iff]
  push_neg
  rfl

theorem primeFixedChainEmbedding_nonfixed_iff (a : BooleanChainExponent (ZMod p × W)) :
    a ∉ Set.range (primeFixedChainEmbedding (W := W) p) ↔
      ∃ F ∈ a.val.support, ∃ t : ZMod p,
        F.val.image (primeOrbitRelabel p (Equiv.refl W) (fun _ => t)) ≠ F.val := by
  rw [primeFixedChainEmbedding_not_range_iff]
  simp only [primeFixedFaceEmbedding_range_iff_fixed, not_forall]

theorem booleanOrdinaryDegree_primeFixedChainEmbedding (a : BooleanChainExponent W) :
    booleanOrdinaryDegree (primeFixedChainEmbedding p a).val =
      p * booleanOrdinaryDegree a.val := by
  change (a.val.mapDomain (primeFixedFaceEmbedding p)).sum (fun F n => n * F.val.card) = _
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ i j => by simp [add_mul])]
  simp only [primeFixedFaceEmbedding_card]
  rw [booleanOrdinaryDegree, Finsupp.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  ac_rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedFaceQuotient.lean -/
section

section
/-! # The actual fixed-face quotient and its integral splitting

The quotient map kills precisely the face variables not fixed by the
order-p subgroup.  Both it and its section are maps of the original
Stanley--Reisner quotient algebras.  In particular the kernel below is an
actual submodule of the barycentric ring, over any commutative coefficient
ring.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- The literal quotient by the nonfixed face variables. -/
def primeFixedFaceQuotient :
    BooleanBarycentricRing (ZMod p × W) K →ₐ[K] BooleanBarycentricRing W K :=
  monomialRestriction (primeFixedFaceEmbedding p) IsChainExponent IsChainExponent
    isChainExponent_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => isChainExponent_map_primeFixedFaceEmbedding p ha)

@[simp] theorem primeFixedFaceQuotient_mk
    (f : MvPolynomial (BooleanFace (ZMod p × W)) K) :
    primeFixedFaceQuotient p K (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) f) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.killCompl (primeFixedFaceEmbedding p).injective f) := rfl

theorem primeFixedFaceQuotient_face (F : BooleanFace W) :
    primeFixedFaceQuotient p K (faceVariable (primeFixedFaceEmbedding p F)) =
      faceVariable F := by
  unfold faceVariable
  rw [primeFixedFaceQuotient_mk]
  congr 1
  have h := DFunLike.congr_fun
    (MvPolynomial.killCompl_comp_rename (R := K) (primeFixedFaceEmbedding p).injective)
    (MvPolynomial.X F)
  simpa only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgHom.id_apply] using h

theorem primeFixedFaceQuotient_face_outside (F : BooleanFace (ZMod p × W))
    (hF : F ∉ Set.range (primeFixedFaceEmbedding (W := W) p)) :
    primeFixedFaceQuotient p K (faceVariable F) = 0 := by
  unfold faceVariable
  rw [primeFixedFaceQuotient_mk]
  have h : MvPolynomial.killCompl (R := K) (primeFixedFaceEmbedding p).injective
      (MvPolynomial.X F) = 0 := by
    simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hF]
  rw [h, map_zero]

theorem primeFixedFaceQuotient_coefficient
    (x : BooleanBarycentricRing (ZMod p × W) K) (a : BooleanChainExponent W) :
    (booleanChainBasis (K := K)).repr (primeFixedFaceQuotient p K x) a =
      (booleanChainBasis (K := K)).repr x (primeFixedChainEmbedding p a) :=
  monomialRestriction_coefficient _ _ _ _ _ _ _ _

/-- Renaming an orbit face to its full union gives an algebra section. -/
def primeFixedFaceSection :
    BooleanBarycentricRing W K →ₐ[K] BooleanBarycentricRing (ZMod p × W) K := by
  let f := (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)).comp
    (MvPolynomial.rename (primeFixedFaceEmbedding (W := W) p))
  apply Ideal.Quotient.liftₐ (forbiddenIdeal IsChainExponent) f
  have hle : forbiddenIdeal IsChainExponent ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
      (MvPolynomial.rename (primeFixedFaceEmbedding p) (MvPolynomial.monomial a (1 : K))) = 0
    rw [MvPolynomial.rename_monomial]
    exact chainMonomial_eq_zero
      (fun h => ha ((isChainExponent_map_primeFixedFaceEmbedding_iff p a).mp h))
  exact fun f hf => hle hf

@[simp] theorem primeFixedFaceSection_mk (f : MvPolynomial (BooleanFace W) K) :
    primeFixedFaceSection p K (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) f) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.rename (primeFixedFaceEmbedding p) f) := rfl

@[simp] theorem primeFixedFaceSection_face (F : BooleanFace W) :
    primeFixedFaceSection p K (faceVariable F) =
      faceVariable (primeFixedFaceEmbedding p F) := by
  simp only [faceVariable, primeFixedFaceSection_mk, MvPolynomial.rename_X]

@[simp] theorem primeFixedFaceQuotient_section (x : BooleanBarycentricRing W K) :
    primeFixedFaceQuotient p K (primeFixedFaceSection p K x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [primeFixedFaceSection_mk, primeFixedFaceQuotient_mk,
    MvPolynomial.killCompl_rename_app]

theorem primeFixedFaceSection_basis (a : BooleanChainExponent W) :
    primeFixedFaceSection p K (booleanChainBasis a) =
      booleanChainBasis (primeFixedChainEmbedding p a) := by
  simp only [booleanChainBasis, standardMonomialBasis_apply, primeFixedFaceSection_mk,
    MvPolynomial.rename_monomial]
  rfl

theorem primeFixedFaceQuotient_surjective :
    Function.Surjective (primeFixedFaceQuotient (W := W) p K) :=
  fun x => ⟨primeFixedFaceSection p K x, primeFixedFaceQuotient_section p K x⟩

theorem primeFixedFaceSection_injective :
    Function.Injective (primeFixedFaceSection (W := W) p K) :=
  Function.LeftInverse.injective (primeFixedFaceQuotient_section p K)

theorem primeFixedFaceQuotient_parameter (i : ℕ) :
    primeFixedFaceQuotient (W := W) p K (booleanRankParameter i) =
      if p ∣ i then booleanRankParameter (i / p) else 0 := by
  rw [booleanRankParameter, map_sum]
  trans ∑ G : BooleanFace W,
      primeFixedFaceQuotient p K
        (if (primeFixedFaceEmbedding p G).val.card = i then
          faceVariable (primeFixedFaceEmbedding p G) else 0)
  · symm
    apply Finset.sum_bij_ne_zero (fun G _ _ => primeFixedFaceEmbedding p G)
    · intro G hG hG0
      exact Finset.mem_univ _
    · intro G H hG hH hG0 hH0 he
      exact (primeFixedFaceEmbedding p).injective he
    · intro F hF hF0
      have hmem : F ∈ Set.range (primeFixedFaceEmbedding (W := W) p) := by
        by_contra hn
        apply hF0
        split_ifs <;> simp [primeFixedFaceQuotient_face_outside p K F hn]
      obtain ⟨G, rfl⟩ := hmem
      refine ⟨G, Finset.mem_univ _, ?_, rfl⟩
      by_cases hc : (primeFixedFaceEmbedding p G).val.card = i
      · simpa only [if_pos hc] using hF0
      · simpa only [if_neg hc] using hF0
    · intro G hG hG0
      by_cases hc : (primeFixedFaceEmbedding p G).val.card = i
      · simp only [if_pos hc]
      · simp only [if_neg hc]
  · by_cases hi : p ∣ i
    · rw [if_pos hi, booleanRankParameter]
      apply Finset.sum_congr rfl
      intro G hG
      have hc : p * G.val.card = i ↔ G.val.card = i / p := by
        constructor
        · intro h
          rw [← h, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
        · intro h
          rw [h, Nat.mul_div_cancel' hi]
      simp only [primeFixedFaceEmbedding_card, hc]
      split_ifs <;> simp only [primeFixedFaceQuotient_face, map_zero]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro G hG
      have hc : p * G.val.card ≠ i := by
        intro h
        exact hi ⟨G.val.card, h.symm⟩
      simp only [primeFixedFaceEmbedding_card, if_neg hc, map_zero]

/-- The actual kernel of the full-orbit quotient. -/
abbrev PrimeFixedFaceKernel := LinearMap.ker (primeFixedFaceQuotient (W := W) p K).toLinearMap

abbrev PrimeFixedFaceKernelIndex :=
  {a : BooleanChainExponent (ZMod p × W) //
    a ∉ Set.range (primeFixedChainEmbedding (W := W) p)}

theorem primeFixedFaceKernel_mem_iff (x : BooleanBarycentricRing (ZMod p × W) K) :
    x ∈ PrimeFixedFaceKernel (W := W) p K ↔
      ∀ a : BooleanChainExponent W,
        (booleanChainBasis (K := K)).repr x (primeFixedChainEmbedding p a) = 0 := by
  constructor
  · intro hx a
    have hh := primeFixedFaceQuotient_coefficient p K x a
    change primeFixedFaceQuotient p K x = 0 at hx
    rw [hx, LinearEquiv.map_zero, Finsupp.zero_apply] at hh
    exact hh.symm
  · intro hx
    change primeFixedFaceQuotient p K x = 0
    apply (booleanChainBasis (V := W) (K := K)).repr.injective
    ext a
    rw [primeFixedFaceQuotient_coefficient, LinearEquiv.map_zero, Finsupp.zero_apply]
    exact hx a

theorem primeFixedFaceKernel_mem_iff_range (x : BooleanBarycentricRing (ZMod p × W) K) :
    x ∈ PrimeFixedFaceKernel (W := W) p K ↔
      ∀ a : BooleanChainExponent (ZMod p × W),
        a ∈ Set.range (primeFixedChainEmbedding (W := W) p) →
          (booleanChainBasis (K := K)).repr x a = 0 := by
  rw [primeFixedFaceKernel_mem_iff]
  constructor
  · rintro h a ⟨b, rfl⟩
    exact h b
  · intro h b
    exact h _ ⟨b, rfl⟩

def primeFixedFaceKernelSupportedEquiv :
    PrimeFixedFaceKernel (W := W) p K ≃ₗ[K]
      Finsupp.supported K K
        {a : BooleanChainExponent (ZMod p × W) |
          a ∉ Set.range (primeFixedChainEmbedding (W := W) p)} where
  toFun x := ⟨(booleanChainBasis (K := K)).repr x.val, by
    rw [Finsupp.mem_supported']
    intro a ha
    exact (primeFixedFaceKernel_mem_iff_range p K x.val).mp x.property a (by simpa using ha)⟩
  invFun x := ⟨(booleanChainBasis (K := K)).repr.symm x.val, by
    rw [primeFixedFaceKernel_mem_iff_range]
    intro a ha
    rw [LinearEquiv.apply_symm_apply]
    exact (Finsupp.mem_supported' K x.val).mp x.property a (by simpa using ha)⟩
  left_inv x := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ x.val
  right_inv x := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ x.val
  map_add' x y := by
    apply Subtype.ext
    exact map_add (booleanChainBasis (K := K)).repr x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (booleanChainBasis (K := K)).repr c x.val

def primeFixedFaceKernelCoordinates :
    PrimeFixedFaceKernel (W := W) p K ≃ₗ[K] (PrimeFixedFaceKernelIndex (W := W) p →₀ K) :=
  (primeFixedFaceKernelSupportedEquiv p K).trans
    (Finsupp.supportedEquivFinsupp
      {a : BooleanChainExponent (ZMod p × W) |
        a ∉ Set.range (primeFixedChainEmbedding (W := W) p)})

@[simp] theorem primeFixedFaceKernelCoordinates_apply
    (x : PrimeFixedFaceKernel (W := W) p K) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    primeFixedFaceKernelCoordinates p K x a = (booleanChainBasis (K := K)).repr x.val a.val := rfl

def primeFixedFaceKernelBasis : Module.Basis (PrimeFixedFaceKernelIndex (W := W) p) K
    (PrimeFixedFaceKernel (W := W) p K) :=
  Finsupp.basisSingleOne.map (primeFixedFaceKernelCoordinates p K).symm

/-- The kernel basis consists of the original chain monomials, with no
localization or coefficient division. -/
theorem primeFixedFaceKernelBasis_apply (a : PrimeFixedFaceKernelIndex (W := W) p) :
    (primeFixedFaceKernelBasis p K a).val = booleanChainBasis a.val := by
  apply (booleanChainBasis (K := K)).repr.injective
  change (booleanChainBasis (K := K)).repr
      ((primeFixedFaceKernelCoordinates p K).symm (Finsupp.single a 1)).val =
    (booleanChainBasis (K := K)).repr (booleanChainBasis a.val)
  rw [Module.Basis.repr_self]
  change (booleanChainBasis (K := K)).repr
    ((booleanChainBasis (K := K)).repr.symm
      ((Finsupp.supportedEquivFinsupp (R := K) (M := K) _).symm
        (Finsupp.single a (1 : K))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.supportedEquivFinsupp_symm_single (R := K) _ a (1 : K)

/-- A coordinate retraction onto the actual kernel. -/
def primeFixedFaceKernelProjection :
    BooleanBarycentricRing (ZMod p × W) K →ₗ[K] PrimeFixedFaceKernel (W := W) p K :=
  (primeFixedFaceKernelCoordinates p K).symm.toLinearMap.comp
    ((Finsupp.lsubtypeDomain
      {a : BooleanChainExponent (ZMod p × W) |
        a ∉ Set.range (primeFixedChainEmbedding (W := W) p)}).comp
      (booleanChainBasis (K := K)).repr.toLinearMap)

@[simp] theorem primeFixedFaceKernelProjection_coordinates
    (x : BooleanBarycentricRing (ZMod p × W) K) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    primeFixedFaceKernelCoordinates p K (primeFixedFaceKernelProjection p K x) a =
      (booleanChainBasis (K := K)).repr x a.val := by
  change (primeFixedFaceKernelCoordinates p K)
    ((primeFixedFaceKernelCoordinates p K).symm _) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem primeFixedFaceKernelProjection_retract (x : PrimeFixedFaceKernel (W := W) p K) :
    primeFixedFaceKernelProjection p K x.val = x := by
  apply (primeFixedFaceKernelCoordinates p K).injective
  ext a
  rw [primeFixedFaceKernelProjection_coordinates, primeFixedFaceKernelCoordinates_apply]

theorem primeFixedFaceKernelProjection_coefficient
    (x : BooleanBarycentricRing (ZMod p × W) K) (a : BooleanChainExponent (ZMod p × W)) :
    (booleanChainBasis (K := K)).repr (primeFixedFaceKernelProjection p K x).val a =
      if a ∈ Set.range (primeFixedChainEmbedding (W := W) p) then 0 else
        (booleanChainBasis (K := K)).repr x a := by
  by_cases ha : a ∈ Set.range (primeFixedChainEmbedding (W := W) p)
  · rw [if_pos ha]
    exact (primeFixedFaceKernel_mem_iff_range p K _).mp
      (primeFixedFaceKernelProjection p K x).property a ha
  · rw [if_neg ha]
    exact primeFixedFaceKernelProjection_coordinates p K x ⟨a, ha⟩

theorem primeFixedFaceKernelProjection_degree (n : ℕ)
    (x : BooleanBarycentricRing (ZMod p × W) K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    (primeFixedFaceKernelProjection p K x).val ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  change booleanChainBasis.repr (primeFixedFaceKernelProjection p K x).val a = 0
  rw [primeFixedFaceKernelProjection_coefficient]
  split_ifs
  · rfl
  · exact hx a ha

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedFaceSymmetry.lean -/
section

section
/-! # Equivariance of the actual fixed-face quotient and kernel

The ambient vertex bijections may permute the free orbits and translate
each orbit independently.  All formulas concern the existing quotient
algebra action, and the kernel coordinates are the literal chain monomials.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section General
variable {V W K : Type*} [Fintype V] [Fintype W] [CommRing K]

def booleanChainVertexEquiv (e : V ≃ W) : BooleanChainExponent V ≃ BooleanChainExponent W where
  toFun a := ⟨a.val.mapDomain (booleanFaceEmbedding e.toEmbedding),
    isChainExponent_map_booleanFaceEmbedding e.toEmbedding a.property⟩
  invFun a := ⟨a.val.mapDomain (booleanFaceEmbedding e.symm.toEmbedding),
    isChainExponent_map_booleanFaceEmbedding e.symm.toEmbedding a.property⟩
  left_inv a := by
    apply Subtype.ext
    change Finsupp.mapDomain (booleanFaceEmbedding e.symm.toEmbedding)
      (a.val.mapDomain (booleanFaceEmbedding e.toEmbedding)) = a.val
    rw [← Finsupp.mapDomain_fun_comp]
    have he : (booleanFaceEmbedding e.symm.toEmbedding : BooleanFace W → BooleanFace V) ∘
        booleanFaceEmbedding e.toEmbedding = id := by
      funext F
      rw [Function.comp_apply, booleanFaceEmbedding_trans]
      have h : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      rw [h, booleanFaceEmbedding_refl]
      rfl
    change Finsupp.mapDomain
      ((booleanFaceEmbedding e.symm.toEmbedding : BooleanFace W → BooleanFace V) ∘
        booleanFaceEmbedding e.toEmbedding) a.val = a.val
    rw [he, Finsupp.mapDomain_id]
  right_inv a := by
    apply Subtype.ext
    change Finsupp.mapDomain (booleanFaceEmbedding e.toEmbedding)
      (a.val.mapDomain (booleanFaceEmbedding e.symm.toEmbedding)) = a.val
    rw [← Finsupp.mapDomain_fun_comp]
    have he : (booleanFaceEmbedding e.toEmbedding : BooleanFace V → BooleanFace W) ∘
        booleanFaceEmbedding e.symm.toEmbedding = id := by
      funext F
      rw [Function.comp_apply, booleanFaceEmbedding_trans]
      have h : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
        ext v
        exact e.apply_symm_apply v
      rw [h, booleanFaceEmbedding_refl]
      rfl
    change Finsupp.mapDomain
      ((booleanFaceEmbedding e.toEmbedding : BooleanFace V → BooleanFace W) ∘
        booleanFaceEmbedding e.symm.toEmbedding) a.val = a.val
    rw [he, Finsupp.mapDomain_id]

@[simp] theorem booleanChainVertexEquiv_val (e : V ≃ W) (a : BooleanChainExponent V) :
    (booleanChainVertexEquiv e a).val = a.val.mapDomain (booleanFaceEmbedding e.toEmbedding) := rfl

theorem booleanVertexRelabelEquiv_coefficient (e : V ≃ W)
    (x : BooleanBarycentricRing V K) (a : BooleanChainExponent W) :
    (booleanChainBasis (K := K)).repr (booleanVertexRelabelEquiv e x) a =
      (booleanChainBasis (K := K)).repr x ((booleanChainVertexEquiv e).symm a) :=
  booleanRestriction_coefficient e.symm.toEmbedding x a

theorem booleanVertexRelabelEquiv_basis (e : V ≃ W) (a : BooleanChainExponent V) :
    booleanVertexRelabelEquiv (K := K) e (booleanChainBasis a) =
      booleanChainBasis (booleanChainVertexEquiv e a) := by
  apply (booleanChainBasis (K := K)).repr.injective
  ext b
  rw [booleanVertexRelabelEquiv_coefficient]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Equiv.eq_symm_apply]

end General

variable (p : ℕ) [Fact p.Prime]
variable {W U : Type*} [Fintype W] [Fintype U]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq U := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × U) := Classical.decEq _

theorem primeFixedChainEmbedding_relabel (σ : W ≃ U) (g : W → ZMod p)
    (a : BooleanChainExponent W) :
    booleanChainVertexEquiv (primeOrbitRelabel p σ g) (primeFixedChainEmbedding p a) =
      primeFixedChainEmbedding p (booleanChainVertexEquiv σ a) := by
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding (primeOrbitRelabel p σ g).toEmbedding)
      (a.val.mapDomain (primeFixedFaceEmbedding p)) =
    Finsupp.mapDomain (primeFixedFaceEmbedding p)
      (a.val.mapDomain (booleanFaceEmbedding σ.toEmbedding))
  rw [← Finsupp.mapDomain_fun_comp, ← Finsupp.mapDomain_fun_comp]
  apply Finsupp.mapDomain_congr
  intro F hF
  exact primeFixedFaceEmbedding_relabel p σ g F

theorem primeFixedChainEmbedding_inverse_relabel (σ : W ≃ U) (g : W → ZMod p)
    (a : BooleanChainExponent U) :
    (booleanChainVertexEquiv (primeOrbitRelabel p σ g)).symm (primeFixedChainEmbedding p a) =
      primeFixedChainEmbedding p ((booleanChainVertexEquiv σ).symm a) := by
  apply (booleanChainVertexEquiv (primeOrbitRelabel p σ g)).injective
  rw [Equiv.apply_symm_apply, primeFixedChainEmbedding_relabel, Equiv.apply_symm_apply]

theorem primeFixedChainEmbedding_relabel_range_iff (σ : W ≃ U) (g : W → ZMod p)
    (a : BooleanChainExponent (ZMod p × W)) :
    booleanChainVertexEquiv (primeOrbitRelabel p σ g) a ∈
        Set.range (primeFixedChainEmbedding (W := U) p) ↔
      a ∈ Set.range (primeFixedChainEmbedding (W := W) p) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(booleanChainVertexEquiv σ).symm b, ?_⟩
    apply (booleanChainVertexEquiv (primeOrbitRelabel p σ g)).injective
    rw [primeFixedChainEmbedding_relabel, Equiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    exact ⟨booleanChainVertexEquiv σ b, (primeFixedChainEmbedding_relabel p σ g b).symm⟩

theorem primeFixedFaceQuotient_relabel (σ : W ≃ U) (g : W → ZMod p)
    (x : BooleanBarycentricRing (ZMod p × W) K) :
    primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) x) =
      booleanVertexRelabelEquiv σ (primeFixedFaceQuotient p K x) := by
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  rw [primeFixedFaceQuotient_coefficient, booleanVertexRelabelEquiv_coefficient,
    booleanVertexRelabelEquiv_coefficient, primeFixedFaceQuotient_coefficient,
    primeFixedChainEmbedding_inverse_relabel]

theorem primeFixedFaceSection_relabel (σ : W ≃ U) (g : W → ZMod p)
    (x : BooleanBarycentricRing W K) :
    primeFixedFaceSection p K (booleanVertexRelabelEquiv σ x) =
      booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) (primeFixedFaceSection p K x) := by
  have h : (primeFixedFaceSection (W := U) p K).toLinearMap.comp
      (booleanVertexRelabelEquiv σ).toLinearMap =
      (booleanVertexRelabelEquiv (primeOrbitRelabel p σ g)).toLinearMap.comp
        (primeFixedFaceSection (W := W) p K).toLinearMap := by
    apply (booleanChainBasis (V := W) (K := K)).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
      booleanVertexRelabelEquiv_basis, primeFixedFaceSection_basis,
      primeFixedChainEmbedding_relabel]
  exact LinearMap.congr_fun h x

def primeFixedFaceKernelRelabel (σ : W ≃ U) (g : W → ZMod p) :
    PrimeFixedFaceKernel (W := W) p K →ₗ[K] PrimeFixedFaceKernel (W := U) p K where
  toFun x := ⟨booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) x.val, by
    change primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) x.val) = 0
    rw [primeFixedFaceQuotient_relabel]
    have hx : primeFixedFaceQuotient p K x.val = 0 := x.property
    rw [hx, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

@[simp] theorem primeFixedFaceKernelRelabel_val (σ : W ≃ U) (g : W → ZMod p)
    (x : PrimeFixedFaceKernel (W := W) p K) :
    (primeFixedFaceKernelRelabel p K σ g x).val =
      booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) x.val := rfl

def primeFixedFaceKernelIndexEquiv (σ : W ≃ U) (g : W → ZMod p) :
    PrimeFixedFaceKernelIndex (W := W) p ≃ PrimeFixedFaceKernelIndex (W := U) p where
  toFun a := ⟨booleanChainVertexEquiv (primeOrbitRelabel p σ g) a.val,
    fun h => a.property ((primeFixedChainEmbedding_relabel_range_iff p σ g a.val).mp h)⟩
  invFun a := ⟨(booleanChainVertexEquiv (primeOrbitRelabel p σ g)).symm a.val, by
    intro h
    apply a.property
    have hh := (primeFixedChainEmbedding_relabel_range_iff p σ g _).mpr h
    simpa only [Equiv.apply_symm_apply] using hh⟩
  left_inv a := Subtype.ext ((booleanChainVertexEquiv (primeOrbitRelabel p σ g)).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((booleanChainVertexEquiv (primeOrbitRelabel p σ g)).apply_symm_apply a.val)

/-- The actual kernel action permutes its original monomial basis. -/
theorem primeFixedFaceKernelRelabel_basis (σ : W ≃ U) (g : W → ZMod p)
    (a : PrimeFixedFaceKernelIndex (W := W) p) :
    primeFixedFaceKernelRelabel p K σ g (primeFixedFaceKernelBasis p K a) =
      primeFixedFaceKernelBasis p K (primeFixedFaceKernelIndexEquiv p σ g a) := by
  apply Subtype.ext
  rw [primeFixedFaceKernelRelabel_val, primeFixedFaceKernelBasis_apply,
    booleanVertexRelabelEquiv_basis, primeFixedFaceKernelBasis_apply]
  rfl

theorem primeFixedFaceKernelCoordinates_relabel (σ : W ≃ U) (g : W → ZMod p)
    (x : PrimeFixedFaceKernel (W := W) p K) (a : PrimeFixedFaceKernelIndex (W := U) p) :
    primeFixedFaceKernelCoordinates p K (primeFixedFaceKernelRelabel p K σ g x) a =
      primeFixedFaceKernelCoordinates p K x ((primeFixedFaceKernelIndexEquiv p σ g).symm a) := by
  rw [primeFixedFaceKernelCoordinates_apply, primeFixedFaceKernelRelabel_val,
    booleanVertexRelabelEquiv_coefficient, primeFixedFaceKernelCoordinates_apply]
  rfl

theorem primeFixedFaceKernelProjection_relabel (σ : W ≃ U) (g : W → ZMod p)
    (x : BooleanBarycentricRing (ZMod p × W) K) :
    primeFixedFaceKernelProjection p K (booleanVertexRelabelEquiv (primeOrbitRelabel p σ g) x) =
      primeFixedFaceKernelRelabel p K σ g (primeFixedFaceKernelProjection p K x) := by
  apply (primeFixedFaceKernelCoordinates p K).injective
  ext a
  rw [primeFixedFaceKernelProjection_coordinates, booleanVertexRelabelEquiv_coefficient,
    primeFixedFaceKernelCoordinates_relabel, primeFixedFaceKernelProjection_coordinates]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedFaceGrading.lean -/
section

section
/-! # Ordinary degree in the fixed-face quotient and its section

The quotient divides ordinary degree by p and is zero in degrees not
divisible by p.  Its actual algebra section multiplies degree by p.  These
statements are proved from the literal monomial coefficients.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

theorem primeFixedFaceSection_repr (x : BooleanBarycentricRing W K) :
    (booleanChainBasis (K := K)).repr (primeFixedFaceSection p K x) =
      Finsupp.mapDomain (primeFixedChainEmbedding p) ((booleanChainBasis (K := K)).repr x) := by
  have h : (booleanChainBasis (V := ZMod p × W) (K := K)).repr.toLinearMap.comp
      (primeFixedFaceSection p K).toLinearMap =
      (Finsupp.lmapDomain K K (primeFixedChainEmbedding p)).comp
        (booleanChainBasis (V := W) (K := K)).repr.toLinearMap := by
    apply (booleanChainBasis (V := W) (K := K)).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      primeFixedFaceSection_basis, Module.Basis.repr_self,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun h x

theorem primeFixedFaceSection_coefficient (x : BooleanBarycentricRing W K)
    (a : BooleanChainExponent W) :
    (booleanChainBasis (K := K)).repr (primeFixedFaceSection p K x) (primeFixedChainEmbedding p a) =
      (booleanChainBasis (K := K)).repr x a := by
  rw [primeFixedFaceSection_repr,
    Finsupp.mapDomain_apply_of_injective (primeFixedChainEmbedding p).injective]

theorem primeFixedFaceSection_coefficient_outside (x : BooleanBarycentricRing W K)
    (a : BooleanChainExponent (ZMod p × W))
    (ha : a ∉ Set.range (primeFixedChainEmbedding (W := W) p)) :
    (booleanChainBasis (K := K)).repr (primeFixedFaceSection p K x) a = 0 := by
  rw [primeFixedFaceSection_repr]
  exact Finsupp.mapDomain_of_notMem_range _ _ ha

theorem primeFixedFaceQuotient_degree (n : ℕ)
    (x : BooleanBarycentricRing (ZMod p × W) K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    primeFixedFaceQuotient p K x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (n / p) := by
  intro a ha
  change booleanChainBasis.repr (primeFixedFaceQuotient p K x) a = 0
  rw [primeFixedFaceQuotient_coefficient]
  apply hx
  change booleanOrdinaryDegree (primeFixedChainEmbedding p a).val ≠ n
  rw [booleanOrdinaryDegree_primeFixedChainEmbedding]
  intro he
  apply ha
  rw [← he, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]

theorem primeFixedFaceQuotient_zero_of_degree_not_dvd (n : ℕ) (hn : ¬ p ∣ n)
    (x : BooleanBarycentricRing (ZMod p × W) K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    primeFixedFaceQuotient p K x = 0 := by
  apply (booleanChainBasis (V := W) (K := K)).repr.injective
  ext a
  rw [primeFixedFaceQuotient_coefficient, LinearEquiv.map_zero, Finsupp.zero_apply]
  apply hx
  change booleanOrdinaryDegree (primeFixedChainEmbedding p a).val ≠ n
  rw [booleanOrdinaryDegree_primeFixedChainEmbedding]
  exact fun he => hn ⟨booleanOrdinaryDegree a.val, he.symm⟩

theorem primeFixedFaceSection_degree (n : ℕ) (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    primeFixedFaceSection p K x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (p * n) := by
  intro a ha
  change booleanChainBasis.repr (primeFixedFaceSection p K x) a = 0
  by_cases hmem : a ∈ Set.range (primeFixedChainEmbedding (W := W) p)
  · obtain ⟨b, rfl⟩ := hmem
    rw [primeFixedFaceSection_coefficient]
    apply hx
    intro hb
    change booleanOrdinaryDegree b.val = n at hb
    apply ha
    change booleanOrdinaryDegree (primeFixedChainEmbedding p b).val = p * n
    rw [booleanOrdinaryDegree_primeFixedChainEmbedding, hb]
  · exact primeFixedFaceSection_coefficient_outside p K x a hmem

/-- The coordinate projection is also the elementary split-kernel formula. -/
theorem primeFixedFaceKernelProjection_eq (x : BooleanBarycentricRing (ZMod p × W) K) :
    (primeFixedFaceKernelProjection p K x).val =
      x - primeFixedFaceSection p K (primeFixedFaceQuotient p K x) := by
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  rw [primeFixedFaceKernelProjection_coefficient, map_sub, Finsupp.sub_apply]
  by_cases hmem : a ∈ Set.range (primeFixedChainEmbedding (W := W) p)
  · rw [if_pos hmem]
    obtain ⟨b, rfl⟩ := hmem
    rw [primeFixedFaceSection_coefficient, primeFixedFaceQuotient_coefficient, sub_self]
  · rw [if_neg hmem, primeFixedFaceSection_coefficient_outside p K _ a hmem, sub_zero]

end FourPapers.Universal

end
end
end


-- Close only the anonymous source scopes reopened by the next shard.
