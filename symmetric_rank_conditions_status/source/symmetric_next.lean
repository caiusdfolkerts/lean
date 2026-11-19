module
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import symmetric_local

@[expose] public section

/- LOCAL CONTINUATION SOURCE EndpointGrading.lean -/
section

set_option autoImplicit false

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial Finsupp Finset

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The endpoint multidegree of an independent symmetric coordinate; a diagonal
coordinate contributes twice at its unique endpoint. -/
def endpointWeight {n : ℕ} (e : Entry n) : Fin n →₀ ℕ :=
  single e.val.1 1 + single e.val.2 1

@[simp] theorem endpointWeight_fold {n : ℕ} (i j : Fin n) :
    endpointWeight (fold i j) = single i 1 + single j 1 := by
  change single (max i j) 1 + single (min i j) 1 = _
  by_cases h : i ≤ j
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h)]

/-- The content of the two ordered index sets of a minor, including repeated
endpoints between its row and column index sets. -/
def minorEndpointWeight {n t : ℕ} (a b : Fin t ↪o Fin n) : Fin n →₀ ℕ :=
  (∑ p, single (a p) 1) + ∑ p, single (b p) 1

theorem permutationExponent_endpointWeight {n t : ℕ}
    (a b : Fin t ↪o Fin n) (σ : Equiv.Perm (Fin t)) :
    Finsupp.weight endpointWeight (permutationExponent a b σ) =
      minorEndpointWeight a b := by
  classical
  simp only [permutationExponent, map_sum, Finsupp.weight_single, one_nsmul,
    endpointWeight_fold, Finset.sum_add_distrib, minorEndpointWeight]
  congr 1
  exact Equiv.sum_comp σ (fun p => single (a p) 1)

/-- Every symmetric minor is homogeneous for the actual endpoint grading,
over an arbitrary commutative coefficient ring. -/
theorem minor_endpoint_homogeneous {n t : ℕ} (R : Type*) [CommRing R]
    (a b : Fin t ↪o Fin n) :
    IsWeightedHomogeneous endpointWeight (minor R a b) (minorEndpointWeight a b) := by
  classical
  rw [minor_eq_sum]
  apply IsWeightedHomogeneous.sum
  intro σ _
  exact isWeightedHomogeneous_monomial _ _ _ (permutationExponent_endpointWeight a b σ)

/-- Each prescribed northwest rank ideal is multihomogeneous, whether or not
the array is realized by a matrix. -/
theorem northwestIdeal_endpoint_homogeneous {n : ℕ} (R : Type*) [CommRing R]
    (r : RankArray n) :
    (northwestIdeal R r).IsHomogeneous (weightedHomogeneousSubmodule R endpointWeight) := by
  classical
  letI := weightedGradedAlgebra R (endpointWeight (n := n))
  apply Ideal.homogeneous_span
  rintro f ⟨i, j, a, b, ha, hb, rfl⟩
  exact ⟨minorEndpointWeight a b, minor_endpoint_homogeneous R a b⟩

theorem determinantalIdeal_endpoint_homogeneous (n : ℕ) (R : Type*) [CommRing R]
    (t : ℕ) :
    (determinantalIdeal n R t).IsHomogeneous
      (weightedHomogeneousSubmodule R endpointWeight) := by
  classical
  letI := weightedGradedAlgebra R (endpointWeight (n := n))
  apply Ideal.homogeneous_span
  rintro f ⟨a, b, rfl⟩
  exact ⟨minorEndpointWeight a b, minor_endpoint_homogeneous R a b⟩

/-- The endpoint grading survives genuine symbolic powers once the independent
primality assertion for the determinantal ideal is supplied. The primality
hypothesis here is explicit and is not asserted by this theorem. -/
theorem determinantal_symbolic_endpoint_component (n : ℕ) (R : Type*) [CommRing R]
    (t s : ℕ) [(determinantalIdeal n R t).IsPrime]
    {f : CoordinateRing n R} (hf : f ∈ symbolicPower (determinantalIdeal n R t) s)
    (d : Fin n →₀ ℕ) :
    weightedHomogeneousComponent endpointWeight d f ∈
      symbolicPower (determinantalIdeal n R t) s := by
  apply symbolicPower_weightedHomogeneousComponent endpointWeight _ _ s hf d
  intro p hp d
  exact weightedHomogeneousComponent_mem_of_mem R endpointWeight
    (determinantalIdeal_endpoint_homogeneous n R t) hp d

end FourPapers.Symmetric

#print axioms FourPapers.Symmetric.northwestIdeal_endpoint_homogeneous
#print axioms FourPapers.Symmetric.determinantal_symbolic_endpoint_component
end
end

/- LOCAL CONTINUATION SOURCE FiniteGenerators.lean -/
section

set_option autoImplicit false

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial Finset

theorem MinorData.size_le {n : ℕ} (δ : MinorData n) : δ.size ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ δ.rows.injective

/-- The definition permits every natural minor size; its actual index embeddings
force a finite set of data, without adding a size restriction to the definition. -/
instance minorData_finite (n : ℕ) : Finite (MinorData n) := by
  let f : MinorData n → Σ t : Fin (n + 1),
      (Fin t.val ↪o Fin n) × (Fin t.val ↪o Fin n) :=
    fun δ => ⟨⟨δ.size, Nat.lt_succ_of_le δ.size_le⟩, δ.rows, δ.cols⟩
  apply Finite.of_injective f
  rintro ⟨s, a, b⟩ ⟨t, c, d⟩ h
  have hst : s = t := congrArg (fun x => x.1.val) h
  subst t
  have hab : (a, b) = (c, d) := by
    simpa only [f, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  cases hab
  rfl

/-- An exact symbolic score bounds the number of factors. This uses the literal
score `size - t + 1`, not a substituted degree inequality. -/
theorem factors_le_exact_score {n k t s : ℕ} (δ : Fin k → MinorData n)
    (hscore : (∑ j, ((δ j).size - t + 1)) = s) : k ≤ s := by
  have h : (∑ _j : Fin k, (1 : ℕ)) ≤ ∑ j : Fin k, ((δ j).size - t + 1) := by
    apply Finset.sum_le_sum
    intro j _
    omega
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, hscore] using h

/-- The paper's exact-score family is a genuinely finite set of polynomials over
every commutative ring. Impossible minor sizes and too many factors are ruled out
by their defining data, not by narrowing the family. -/
theorem symbolicGenerators_finite (R : Type*) [CommRing R] (n t s : ℕ) :
    (symbolicGenerators R n t s).Finite := by
  classical
  let F := Σ k : Fin (s + 1), Fin k.val → MinorData n
  let g : F → CoordinateRing n R := fun z => ∏ i, (z.2 i).polynomial R
  apply (Set.finite_range g).subset
  rintro f ⟨k, δ, hsize, hscore, rfl⟩
  exact ⟨⟨⟨k, Nat.lt_succ_of_le (factors_le_exact_score δ hscore)⟩, δ⟩, rfl⟩

theorem fullMinorGenerators_finite (R : Type*) [CommRing R] (n t : ℕ) :
    (fullMinorGenerators n R t).Finite := by
  classical
  let g : (Fin t ↪o Fin n) × (Fin t ↪o Fin n) → CoordinateRing n R :=
    fun z => minor R z.1 z.2
  apply (Set.finite_range g).subset
  rintro f ⟨a, b, rfl⟩
  exact ⟨(a, b), rfl⟩

theorem northwestGenerators_finite (R : Type*) [CommRing R] {n : ℕ} (r : RankArray n) :
    (northwestGenerators R r).Finite := by
  classical
  apply (Set.finite_range (fun δ : MinorData n => δ.polynomial R)).subset
  rintro f ⟨i, j, a, b, ha, hb, rfl⟩
  exact ⟨⟨r i j + 1, a, b⟩, rfl⟩

end FourPapers.Symmetric

#print axioms FourPapers.Symmetric.symbolicGenerators_finite
end
end

/- LOCAL CONTINUATION SOURCE StatementCorrespondence.lean -/
section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace MonomialOrder

theorem span_leadingTerm_eq_span_monomial_degree_of_units {σ R : Type*} [CommRing R]
    (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' G) =
      Ideal.span ((fun g => monomial (m.degree g) (1 : R)) '' G) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    apply (m.leadingTerm_mem_iff
      ((Ideal.span ((fun g => monomial (m.degree g) (1 : R)) '' G)).restrictScalars R)
      (hunit g hg)).mpr
    exact Ideal.subset_span ⟨g, hg, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    apply (m.leadingTerm_mem_iff
      ((Ideal.span (m.leadingTerm '' G)).restrictScalars R) (hunit g hg)).mp
    exact Ideal.subset_span ⟨g, hg, rfl⟩

end MonomialOrder

namespace FourPapers.Symmetric

universe u v

/-- The basis assertion entails exactly the displayed initial ideal, with the
same literal minor products and no replacement of symbolic powers by their
candidate generators. -/
theorem mixed_initial_eq_of_groebner {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (r : RankArray n) (conditions : List (ℕ × ℕ))
    (hG : (foldedOrder n).IsGroebnerBasis (mixedGenerators R r conditions)
      (mixedIdeal R r conditions)) :
    initialIdeal R (mixedIdeal R r conditions) = northwestAntidiagonalIdeal R r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  classical
  unfold initialIdeal
  rw [hG.span_leadingTerm_image,
    (foldedOrder n).span_leadingTerm_eq_span_monomial_degree_of_units
      (mixedGenerators R r conditions)
      (fun g hg => IsUnit.of_mul_eq_one _ (mixedGenerators_leadingCoeff_mul_self R r conditions g hg)),
    monomial_degrees_mixedGenerators, mixedAntidiagonal_span]

/-- The geometric clause of Theorem 1.1 follows from its algebraic clause,
using the separately checked equivalence with the actual rank locus. -/
theorem rankDefiningIdealAssertion_of_rankLocusAssertion
    (h : RankLocusAssertion.{u, v}) : RankDefiningIdealAssertion.{u, v} := by
  intro n F _ w hw K _ _
  exact vanishingIdeal_rankBoundLocus_of_prime (matrixRankArray w) (h n F w hw K).1

theorem symmetricRankLociTheorem_iff_rankLocusAssertion :
    SymmetricRankLociTheorem.{u, v} ↔ RankLocusAssertion.{u, v} :=
  ⟨And.left, fun h => ⟨h, rankDefiningIdealAssertion_of_rankLocusAssertion h⟩⟩

/-- Explicitly restore the initial-ideal conclusion of the manuscript to the
universal basis assertion. This is an equivalence of statements, not a proof
of either unconditional principal assertion. -/
theorem compatibleGroebnerAssertion_iff_basis_and_initial :
    CompatibleGroebnerAssertion.{v} ↔
      ∀ (n : ℕ) (K : Type v) [Field K] (r : RankArray n),
        (∀ i j, r i j = r j i) →
        ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
          (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
            (mixedIdeal K r conditions) ∧
          initialIdeal K (mixedIdeal K r conditions) = northwestAntidiagonalIdeal K r ⊔
            ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal K n ts.1 ts.2 := by
  constructor
  · intro h n K _ r hr conditions hc
    exact ⟨h n K r hr conditions hc,
      mixed_initial_eq_of_groebner K r conditions (h n K r hr conditions hc)⟩
  · intro h n K _ r hr conditions hc
    exact (h n K r hr conditions hc).1

end FourPapers.Symmetric

#print axioms FourPapers.Symmetric.mixed_initial_eq_of_groebner
#print axioms FourPapers.Symmetric.symmetricRankLociTheorem_iff_rankLocusAssertion
#print axioms FourPapers.Symmetric.compatibleGroebnerAssertion_iff_basis_and_initial
end
end

/- LOCAL CONTINUATION SOURCE DeterminantalSchurCore.lean -/
section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The three supporting source sections below are dependency bodies ported from
TauCeti 5ce4390a0a9a3277d048f680244409f42e9faeda; irrelevant later declarations
are omitted. The final coordinate Schur theorem is the original project proof.
No mathematical premise is replaced by a source-level assumption.
-/

noncomputable section

section
namespace MultilinearMap

variable {R ι N : Type*} {M : ι → Type*} [Semiring R] [Finite ι]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- The value of a multilinear map at arguments drawn from the spans of sets `s i` lies in the
span of its values at arguments drawn from the sets `s i`. -/
theorem map_mem_span_image_pi (f : MultilinearMap R M N) (s : ∀ i, Set (M i)) {m : ∀ i, M i}
    (hm : ∀ i, m i ∈ Submodule.span R (s i)) :
    f m ∈ Submodule.span R (f '' Set.univ.pi s) := by
  classical
  cases nonempty_fintype ι
  -- Replace the arguments indexed by `t` by elements of the spans, one coordinate at a time.
  suffices key : ∀ t : Finset ι, ∀ m : ∀ i, M i, (∀ i, m i ∈ Submodule.span R (s i)) →
      (∀ i ∉ t, m i ∈ s i) → f m ∈ Submodule.span R (f '' Set.univ.pi s) from
    key Finset.univ m hm (by simp)
  intro t
  induction t using Finset.induction_on with
  | empty => exact fun m _ h ↦ Submodule.subset_span ⟨m, fun i _ ↦ h i (by simp), rfl⟩
  | insert a t ha ih =>
    intro m hm h
    have hupdate : ∀ x ∈ Submodule.span R (s a),
        f (Function.update m a x) ∈ Submodule.span R (f '' Set.univ.pi s) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun i ↦ ?_) (fun i hi ↦ ?_)
        · rcases eq_or_ne i a with rfl | hia
          · simpa using Submodule.subset_span hx
          · simpa [hia] using hm i
        · rcases eq_or_ne i a with rfl | hia
          · simpa using hx
          · simpa [hia] using h i (by simp [hia, hi])
      | zero => simp
      | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
      | smul c x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ c hx
    simpa using hupdate (m a) (hm a)

end MultilinearMap


end
section
namespace Matrix

/-- Evaluating the row determinant form after a family of linear functionals gives the
matrix of those functionals evaluated on the input vectors. -/
@[simp]
theorem detRowAlternating_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    detRowAlternating (fun i => LinearMap.pi f (v i)) =
      (Matrix.of fun i j => f j (v i)).det := by
  have hmatrix : (fun i => LinearMap.pi f (v i)) = Matrix.of (fun i j => f j (v i)) := by
    ext i j
    simp only [LinearMap.pi_apply, Matrix.of_apply]
  -- Mathlib defines `det` as evaluation of `detRowAlternating` on the rows.
  simpa only [Matrix.det] using congrArg Matrix.det hmatrix

/-- The multilinear form obtained by precomposing the row determinant with a family of linear
functionals evaluates to the determinant of their evaluation matrix. -/
theorem detRowAlternating_compLinearMap_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    (detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap v =
      (Matrix.of fun i j => f j (v i)).det := by
  rw [AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply,
    detRowAlternating_pi_apply]

end Matrix

namespace TauCeti

/-- If an ideal contains all evaluation determinants whose rows lie in a set, it also contains
those whose rows lie in the linear span of that set. The row and functional families may be
indexed by any finite type. -/
theorem det_mem_of_mem_span {ι R F : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup F] [Module R F] {s : Set F} {I : Ideal R}
    (f : ι → Module.Dual R F) {v : ι → F}
    (hv : ∀ i, v i ∈ Submodule.span R s)
    (h : ∀ w : ι → F, (∀ i, w i ∈ s) → (Matrix.of fun i j ↦ f j (w i)).det ∈ I) :
    (Matrix.of fun i j ↦ f j (v i)).det ∈ I := by
  rw [← Matrix.detRowAlternating_compLinearMap_pi_apply]
  refine Submodule.span_le.2 ?_ <|
    MultilinearMap.map_mem_span_image_pi
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap (fun _ ↦ s) hv
  rintro _ ⟨w, hw, rfl⟩
  rw [Matrix.detRowAlternating_compLinearMap_pi_apply]
  exact h w fun i ↦ hw i trivial

end TauCeti

end
section
open Function LinearMap Module

namespace Submodule

variable {R F F' G M : Type*} [CommRing R] [AddCommGroup F] [Module R F]
  [AddCommGroup F'] [Module R F'] [AddCommGroup G] [Module R G] [AddCommGroup M] [Module R M]

/-- The ideal of `p × p` minors of a submodule `N` of `F`: the ideal generated by the
determinants `det (f j (v i))` of `p` linear functionals `f j` on `F` evaluated at `p` elements
`v i` of `N`. -/
def minorsIdeal (N : Submodule R F) (p : ℕ) : Ideal R :=
  Ideal.span {r | ∃ (f : Fin p → Dual R F) (v : Fin p → F), (∀ i, v i ∈ N) ∧
    (Matrix.of fun i j ↦ f j (v i)).det = r}

variable {N N' : Submodule R F} {p : ℕ}

/-- Each determinant `det (f j (v i))` with all `v i ∈ N` lies in the ideal of minors. -/
theorem det_mem_minorsIdeal (f : Fin p → Dual R F) {v : Fin p → F} (hv : ∀ i, v i ∈ N) :
    (Matrix.of fun i j ↦ f j (v i)).det ∈ N.minorsIdeal p :=
  Ideal.subset_span ⟨f, v, hv, rfl⟩

/-- The ideal of minors is contained in `I` exactly when all its generating determinants are. -/
theorem minorsIdeal_le_iff {I : Ideal R} :
    N.minorsIdeal p ≤ I ↔ ∀ (f : Fin p → Dual R F) (v : Fin p → F), (∀ i, v i ∈ N) →
      (Matrix.of fun i j ↦ f j (v i)).det ∈ I := by
  refine ⟨fun h f v hv ↦ h (det_mem_minorsIdeal f hv), fun h ↦ Ideal.span_le.2 ?_⟩
  rintro _ ⟨f, v, hv, rfl⟩
  exact h f v hv

/-- The ideal of `0 × 0` minors is the unit ideal. -/
@[simp]
theorem minorsIdeal_zero (N : Submodule R F) : N.minorsIdeal 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 <| by
    simpa using det_mem_minorsIdeal (N := N) finZeroElim (v := finZeroElim) finZeroElim

/-- Laplace expansion along the first row: every `(p + 1) × (p + 1)` minor is a combination of
`p × p` minors. -/
theorem minorsIdeal_succ_le (N : Submodule R F) (p : ℕ) :
    N.minorsIdeal (p + 1) ≤ N.minorsIdeal p := by
  refine minorsIdeal_le_iff.2 fun f v hv ↦ ?_
  rw [Matrix.det_succ_row_zero]
  exact sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ <|
    det_mem_minorsIdeal (fun k ↦ f (j.succAbove k)) fun i ↦ hv i.succ

/-- The minors ideals decrease with the size of the minors. -/
theorem minorsIdeal_antitone (N : Submodule R F) : Antitone N.minorsIdeal :=
  antitone_nat_of_succ_le N.minorsIdeal_succ_le

/-- The minors ideals grow with the submodule. -/
theorem minorsIdeal_mono (h : N ≤ N') (p : ℕ) : N.minorsIdeal p ≤ N'.minorsIdeal p :=
  minorsIdeal_le_iff.2 fun f _ hv ↦ det_mem_minorsIdeal f fun i ↦ h (hv i)

/-- The minors ideals can only shrink under a linear map, since functionals pull back. -/
theorem minorsIdeal_map_le (φ : F →ₗ[R] F') (N : Submodule R F) (p : ℕ) :
    (N.map φ).minorsIdeal p ≤ N.minorsIdeal p := by
  refine minorsIdeal_le_iff.2 fun f v hv ↦ ?_
  choose w hw hwv using fun i ↦ mem_map.1 (hv i)
  obtain rfl : v = fun i ↦ φ (w i) := funext fun i ↦ (hwv i).symm
  exact det_mem_minorsIdeal (fun j ↦ f j ∘ₗ φ) hw

/-- The minors ideals are invariant under linear equivalences of the ambient module. -/
@[simp]
theorem minorsIdeal_map_equiv (e : F ≃ₗ[R] F') (N : Submodule R F) (p : ℕ) :
    (N.map (e : F →ₗ[R] F')).minorsIdeal p = N.minorsIdeal p := by
  refine le_antisymm (minorsIdeal_map_le _ _ _) ?_
  calc N.minorsIdeal p = ((N.map (e : F →ₗ[R] F')).map (e.symm : F' →ₗ[R] F)).minorsIdeal p := by
        rw [(map_symm_eq_iff e).2 rfl]
    _ ≤ (N.map (e : F →ₗ[R] F')).minorsIdeal p := minorsIdeal_map_le _ _ _

/-- The minors ideals are invariant under linear equivalences of the ambient module. -/
@[simp]
theorem minorsIdeal_comap_equiv (e : F ≃ₗ[R] F') (N : Submodule R F') (p : ℕ) :
    (N.comap (e : F →ₗ[R] F')).minorsIdeal p = N.minorsIdeal p := by
  rw [comap_equiv_eq_map_symm, minorsIdeal_map_equiv]

/-- The zero submodule has no nonzero minors of positive size. -/
@[simp]
theorem minorsIdeal_bot (p : ℕ) : (⊥ : Submodule R F).minorsIdeal (p + 1) = ⊥ := by
  refine le_bot_iff.1 (minorsIdeal_le_iff.2 fun f v hv ↦ ?_)
  rw [Ideal.mem_bot]
  exact Matrix.det_eq_zero_of_row_eq_zero 0 fun j ↦ by simp [(mem_bot R).1 (hv 0)]

/-- A determinant `det (f j (w i))` whose rows `w i` lie in `N × 0` except for at most one row
equal to `(0, 1)` lies in the minors ideal of `N` of one size less. -/
private theorem det_mem_minorsIdeal_of_mem_insert (N : Submodule R F)
    (f : Fin (p + 1) → Dual R (F × R)) {w : Fin (p + 1) → F × R}
    (hw : ∀ i, w i ∈ insert ((0 : F), (1 : R)) (LinearMap.inl R F R '' N)) :
    (Matrix.of fun i j ↦ f j (w i)).det ∈ N.minorsIdeal p := by
  by_cases h : ∃ i₀, w i₀ = (0, 1)
  · obtain ⟨i₀, hi₀⟩ := h
    by_cases h' : ∃ i, i ≠ i₀ ∧ w i = (0, 1)
    · -- Two rows equal to `(0, 1)` make the determinant vanish.
      obtain ⟨i, hi, hwi⟩ := h'
      rw [Matrix.det_zero_of_row_eq hi (by ext j; simp [hwi, hi₀])]
      exact zero_mem _
    · -- Expand along the row `(0, 1)`; the remaining rows lie in `N × 0`.
      push Not at h'
      choose! x hx hxw using fun i (hi : i ≠ i₀) ↦ (hw i).resolve_left (h' i hi)
      rw [Matrix.det_succ_row _ i₀]
      refine sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ ?_
      convert det_mem_minorsIdeal (fun k ↦ f (j.succAbove k) ∘ₗ LinearMap.inl R F R)
        (v := fun k ↦ x (i₀.succAbove k)) fun k ↦ hx _ (Fin.succAbove_ne _ _) using 2
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.of_apply, LinearMap.comp_apply,
        ← hxw _ (Fin.succAbove_ne i₀ a)]
  · -- All rows lie in `N × 0`.
    push Not at h
    choose x hx hxw using fun i ↦ (hw i).resolve_left (h i)
    obtain rfl : w = fun i ↦ LinearMap.inl R F R (x i) := funext fun i ↦ (hxw i).symm
    exact minorsIdeal_succ_le N p (det_mem_minorsIdeal (fun j ↦ f j ∘ₗ LinearMap.inl R F R) hx)

/-- Adjoining a free summand `R` to a submodule and to its ambient module shifts the minors
ideals by one. -/
private theorem minorsIdeal_prod_top_succ (N : Submodule R F) (p : ℕ) :
    (N.prod (⊤ : Submodule R R)).minorsIdeal (p + 1) = N.minorsIdeal p := by
  refine le_antisymm (minorsIdeal_le_iff.2 fun f v hv ↦ ?_) (minorsIdeal_le_iff.2 fun f v hv ↦ ?_)
  · -- The determinant is multilinear in the rows, and `N × R` is spanned by `N × 0` and `(0, 1)`.
    set T : Set (F × R) := insert (0, 1) (LinearMap.inl R F R '' N)
    have hT (i : Fin (p + 1)) : v i ∈ span R T := by
      have hvi : (v i).1 ∈ N := (mem_prod.1 (hv i)).1
      have hsplit : v i = LinearMap.inl R F R (v i).1 + (v i).2 • ((0 : F), (1 : R)) := by
        ext <;> simp
      rw [hsplit]
      exact add_mem (subset_span (Set.mem_insert_of_mem _ ⟨_, hvi, rfl⟩))
        (smul_mem _ _ (subset_span (Set.mem_insert _ _)))
    exact TauCeti.det_mem_of_mem_span f hT fun _ hw ↦ det_mem_minorsIdeal_of_mem_insert N f hw
  · -- Border the matrix by the row `(0, 1)` and the functional `snd`.
    convert det_mem_minorsIdeal (N := N.prod ⊤)
      (Fin.cons (LinearMap.snd R F R) fun j ↦ f j ∘ₗ LinearMap.fst R F R)
      (v := Fin.cons ((0 : F), (1 : R)) fun i ↦ ((v i, 0) : F × R))
      (Fin.cases (by simp) fun i ↦ by simpa using hv i) using 1
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.submatrix]

/-- Adjoining the free summand `Fin r → R` shifts the minors ideals by `r`. -/
private theorem minorsIdeal_prod_top_pi (N : Submodule R F) (r p : ℕ) :
    (N.prod (⊤ : Submodule R (Fin r → R))).minorsIdeal (p + r) = N.minorsIdeal p := by
  induction r generalizing p with
  | zero =>
    let e : (F × (Fin 0 → R)) ≃ₗ[R] F := LinearEquiv.prodUnique
    have he : (N.prod (⊤ : Submodule R (Fin 0 → R))).map (e : (F × (Fin 0 → R)) →ₗ[R] F) = N := by
      ext x
      simp [mem_map_equiv, e]
    rw [Nat.add_zero, ← minorsIdeal_map_equiv e, he]
  | succ r ih =>
    let e : (F × (Fin (r + 1) → R)) ≃ₗ[R] (F × (Fin r → R)) × R :=
      ((LinearEquiv.refl R F).prodCongr (((Fin.consLinearEquiv R fun _ : Fin (r + 1) ↦ R).symm :
        (Fin (r + 1) → R) ≃ₗ[R] R × (Fin r → R)).trans
          (LinearEquiv.prodComm R R (Fin r → R)))).trans (LinearEquiv.prodAssoc R F _ R).symm
    have he : ((N.prod (⊤ : Submodule R (Fin r → R))).prod (⊤ : Submodule R R)).comap
        (e : (F × (Fin (r + 1) → R)) →ₗ[R] (F × (Fin r → R)) × R) =
        N.prod ⊤ := by
      ext ⟨x, y⟩
      simp only [mem_comap, mem_prod, mem_top, and_true]
      simp [e, LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply,
        LinearEquiv.prodAssoc]
    rw [← he, minorsIdeal_comap_equiv, ← add_assoc, minorsIdeal_prod_top_succ, ih]

/-- Adjoining a free summand `G` of finite rank shifts the minors ideals by the rank of `G`. -/
theorem minorsIdeal_prod_top [Free R G] [Module.Finite R G] (N : Submodule R F) (p : ℕ) :
    (N.prod (⊤ : Submodule R G)).minorsIdeal (p + finrank R G) = N.minorsIdeal p := by
  nontriviality R
  let e : (F × G) ≃ₗ[R] F × (Fin (finrank R G) → R) :=
    (LinearEquiv.refl R F).prodCongr (finBasis R G).equivFun
  have he : (N.prod (⊤ : Submodule R (Fin (finrank R G) → R))).comap
      (e : (F × G) →ₗ[R] F × (Fin (finrank R G) → R)) = N.prod ⊤ := by
    ext ⟨x, y⟩
    simp [e]
  rw [← he, minorsIdeal_comap_equiv, minorsIdeal_prod_top_pi]


end Submodule

end
section

set_option autoImplicit false

/-!
# Determinantal Schur reduction

The coordinate-minor ideal is identified with the minors ideal of the image module. This
identification is proved in both directions, so the module-theoretic shift by an invertible
summand has its genuine determinantal meaning.
-/

namespace FourPapers.Symmetric

open Matrix Finset LinearMap

variable {R m n p : Type*} [CommRing R]

private theorem linearFunctional_eq_sum [Fintype m] [DecidableEq m]
    (f : Module.Dual R (m → R)) (x : m → R) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  calc
    f x = f (∑ i, x i • Pi.single i (1 : R)) := congrArg f (pi_eq_sum_univ' x)
    _ = ∑ i, x i * f (Pi.single i 1) := by simp only [map_sum, map_smul, smul_eq_mul]

/-- Coordinate minors and the intrinsic minors of the column-image module generate the
same ideal. This holds for every rectangular matrix over a commutative ring. -/
theorem matrixMinorIdeal_eq_minorsIdeal_range [Fintype m] [Fintype n]
    (M : Matrix m n R) (t : ℕ) :
    matrixMinorIdeal M t = (LinearMap.range M.mulVecLin).minorsIdeal t := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    have h := Submodule.det_mem_minorsIdeal
      (N := LinearMap.range M.mulVecLin) (fun j => LinearMap.proj (a j))
      (v := fun i => M.col (b i)) (fun i =>
        ⟨Pi.single (b i) 1, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩)
    have hmatrix : (Matrix.of fun (i j : Fin t) => (M.col (b i)) (a j)) =
        (M.submatrix a b).transpose := rfl
    simp only [LinearMap.proj_apply] at h
    rw [hmatrix, Matrix.det_transpose] at h
    exact h
  · apply Submodule.minorsIdeal_le_iff.mpr
    intro f v hv
    choose w hw using hv
    let W : Matrix (Fin t) n R := Matrix.of fun i j => w i j
    let F : Matrix m (Fin t) R := Matrix.of fun i j => f j (Pi.single i 1)
    have hmatrix : (Matrix.of fun i j => f j (v i)) = W * M.transpose * F := by
      ext i j
      rw [Matrix.of_apply, ← hw i, linearFunctional_eq_sum]
      simp only [Matrix.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, W, F, Matrix.of_apply, mul_comm]
    rw [hmatrix]
    have h := matrixMinorIdeal_mul_mul_le W M.transpose F t
      (det_submatrix_mem_matrixMinorIdeal (W * M.transpose * F) t _root_.id _root_.id)
    change (W * M.transpose * F).det ∈ matrixMinorIdeal M.transpose t at h
    simpa only [matrixMinorIdeal_transpose] using h

/-- The exact coordinate-ring ideal used in the paper agrees with this intrinsic ideal. -/
theorem determinantalIdeal_eq_matrixMinorIdeal (n : ℕ) (K : Type*) [CommRing K] (t : ℕ) :
    determinantalIdeal n K t = matrixMinorIdeal (genericMatrix n K) t := by
  rw [matrixMinorIdeal_eq_ordered]
  rfl

/-- An invertible block contributes its full size to every determinantal bound. -/
theorem matrixMinorIdeal_fromBlocks_unit [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] (D : Matrix m n R) (A : Matrix p p R) (hA : IsUnit A) (t : ℕ) :
    matrixMinorIdeal (Matrix.fromBlocks D 0 0 A) (t + Fintype.card p) =
      matrixMinorIdeal D t := by
  classical
  nontriviality R
  let eout := LinearEquiv.sumArrowLequivProdArrow m p R R
  let ein := LinearEquiv.sumArrowLequivProdArrow n p R R
  have hlin : eout.toLinearMap.comp (Matrix.fromBlocks D 0 0 A).mulVecLin =
      (D.mulVecLin.prodMap A.mulVecLin).comp ein.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> funext i <;>
      simp [eout, ein, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec,
        LinearMap.prodMap_apply, Function.comp_def, LinearEquiv.sumArrowLequivProdArrow,
        Equiv.sumArrowEquivProdArrow]
  have hAtop : LinearMap.range A.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hA)
  have hrange : (LinearMap.range (Matrix.fromBlocks D 0 0 A).mulVecLin).map eout.toLinearMap =
      (LinearMap.range D.mulVecLin).prod ⊤ := by
    rw [← LinearMap.range_comp, hlin, LinearEquiv.range_comp,
      LinearMap.range_prodMap, hAtop]
  rw [matrixMinorIdeal_eq_minorsIdeal_range, matrixMinorIdeal_eq_minorsIdeal_range]
  rw [← Submodule.minorsIdeal_map_equiv eout
    (LinearMap.range (Matrix.fromBlocks D 0 0 A).mulVecLin) (t + Fintype.card p)]
  rw [hrange]
  have hdim : Module.finrank R (p → R) = Fintype.card p := Module.finrank_pi R
  rw [← hdim, Submodule.minorsIdeal_prod_top]

/-- The block may equally be placed first; both row and column relabelings are accounted for. -/
theorem matrixMinorIdeal_fromBlocks_unit_first [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p] (A : Matrix p p R) (D : Matrix m n R) (hA : IsUnit A) (t : ℕ) :
    matrixMinorIdeal (Matrix.fromBlocks A 0 0 D) (t + Fintype.card p) =
      matrixMinorIdeal D t := by
  have h := matrixMinorIdeal_submatrix_equiv (Matrix.fromBlocks A 0 0 D)
    (Equiv.sumComm m p) (Equiv.sumComm n p) (t + Fintype.card p)
  change matrixMinorIdeal ((Matrix.fromBlocks A 0 0 D).submatrix Sum.swap Sum.swap)
    (t + Fintype.card p) = _ at h
  rw [Matrix.fromBlocks_submatrix_sum_swap_sum_swap] at h
  rw [← h]
  exact matrixMinorIdeal_fromBlocks_unit D A hA t

/-- The all-size determinantal Schur chart: an invertible pivot block lowers the size of
every minor condition by exactly the size of that block. This includes one-by-one and
two-by-two symmetric pivots without any restriction on the characteristic. -/
theorem matrixMinorIdeal_schur [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix p p R) (B : Matrix p n R) (C : Matrix m p R) (D : Matrix m n R)
    [Invertible A] (t : ℕ) :
    matrixMinorIdeal (Matrix.fromBlocks A B C D) (t + Fintype.card p) =
      matrixMinorIdeal (D - C * ⅟A * B) t := by
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
  rw [matrixMinorIdeal_mul_mul_of_isUnit]
  · exact matrixMinorIdeal_fromBlocks_unit_first A (D - C * ⅟A * B)
      (isUnit_of_invertible A) t
  · rw [Matrix.isUnit_fromBlocks_zero₁₂]
    exact ⟨isUnit_one, isUnit_one⟩
  · rw [Matrix.isUnit_fromBlocks_zero₂₁]
    exact ⟨isUnit_one, isUnit_one⟩

end FourPapers.Symmetric
end
#print axioms FourPapers.Symmetric.matrixMinorIdeal_schur
end
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  for (name, ci) in constants do
    if ci.isAxiom || ci.isUnsafe || ci.isPartial then
      throwError "Unapproved local declaration: {name}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in constants do
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then
        throwError "Unapproved axiom in supporting declaration {name}: {ax}"
  let roots : Array Name := #[`FourPapers.Symmetric.northwestIdeal_endpoint_homogeneous, `FourPapers.Symmetric.determinantal_symbolic_endpoint_component, `FourPapers.Symmetric.symbolicGenerators_finite, `FourPapers.Symmetric.mixed_initial_eq_of_groebner, `FourPapers.Symmetric.symmetricRankLociTheorem_iff_rankLocusAssertion, `FourPapers.Symmetric.compatibleGroebnerAssertion_iff_basis_and_initial, `FourPapers.Symmetric.matrixMinorIdeal_schur]
  for root in roots do
    let axs ← collectAxioms root
    for ax in axs do
      if !allowed.contains ax then
        throwError "Unapproved axiom in {root}: {ax}"
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
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    Json.arr #[toJson (index name), toJson (typeDeps.map index),
      toJson (valueDeps.map index), toJson ((ctors ci).map index),
      toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index))]
  logInfo m!"DEPENDENCY_GRAPH {Json.compress graph}"
  logInfo m!"AUDIT_OK {constants.size} local declarations; {roots.size} roots; no local axioms, unsafe or partial declarations."
