module

public import verified.main
import all verified.main
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section ExtensionPart0
/- Source: Correspondence/PolynomialWeights.lean -/








/-!
# Extremal weights of polynomial support

The coefficient ring of `gradeLift` retains every original monomial. Distinct
monomials of the same weight therefore cannot cancel merely because their
weights agree. Ordinary univariate degree and trailing degree then prove
additivity of the largest and smallest support weights over an integral domain.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GraphicalZonotopes.PolynomialWeights

variable {σ R : Type*} [CommSemiring R]

/-- The nonnegative integer weight of an exponent vector. -/
def weight (w : σ → ℕ) (d : σ →₀ ℕ) : ℕ :=
  d.sum fun i k => w i * k

/-- Adjoin a variable recording weight, while retaining the original monomial
in the coefficient ring. -/
def gradeLift (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

@[simp]
theorem gradeLift_monomial (w : σ → ℕ) (d : σ →₀ ℕ) (a : R) :
    gradeLift w (MvPolynomial.monomial d a) =
      Polynomial.monomial (weight w d) (MvPolynomial.monomial d a) := by
  classical
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.monomial d a) = _
  rw [MvPolynomial.eval₂Hom_monomial]
  calc
    (Polynomial.C.comp MvPolynomial.C) a *
        d.prod (fun i k => (Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i) ^ k) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.C (d.prod fun i k => (MvPolynomial.X i : MvPolynomial σ R) ^ k) *
          Polynomial.X ^ weight w d) := by
            simp only [RingHom.comp_apply, Finsupp.prod, Finsupp.sum, weight,
              mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod,
              ← pow_mul, Finset.prod_pow_eq_pow_sum]
    _ = Polynomial.C (MvPolynomial.monomial d a) * Polynomial.X ^ weight w d := by
      simp only [MvPolynomial.monomial_eq, map_mul, mul_assoc]
    _ = _ := Polynomial.C_mul_X_pow_eq_monomial

/-- Expansion of the lift into its original monomials. -/
theorem gradeLift_eq_sum (w : σ → ℕ) (p : MvPolynomial σ R) :
    gradeLift w p = ∑ d ∈ p.support,
      Polynomial.monomial (weight w d) (MvPolynomial.monomial d (p.coeff d)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => gradeLift_monomial w d (p.coeff d)

/-- Taking first the weight coefficient and then the original monomial
coefficient recovers the original coefficient exactly. -/
theorem coeff_gradeLift (w : σ → ℕ) (p : MvPolynomial σ R)
    (k : ℕ) (e : σ →₀ ℕ) :
    ((gradeLift w p).coeff k).coeff e =
      if weight w e = k then p.coeff e else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      rw [gradeLift_monomial, Polynomial.coeff_monomial]
      by_cases hde : d = e
      · subst d
        by_cases hw : weight w e = k <;> simp [hw]
      · have hzero : (MvPolynomial.monomial d a).coeff e = 0 := by
          simp [hde]
        by_cases hw : weight w d = k <;> simp [hw, hzero]
  | add p q hp hq =>
      simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
      split_ifs <;> simp

/-- The lift records exactly the weights occurring in the original support. -/
theorem support_gradeLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (gradeLift w p).support = p.support.image (weight w) := by
  classical
  ext k
  rw [Polynomial.mem_support_iff, Finset.mem_image]
  constructor
  · intro hk
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [coeff_gradeLift] at hd
    split_ifs at hd with hwd
    · exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hwd⟩
    · exact False.elim (hd rfl)
  · rintro ⟨d, hd, hwd⟩ hzero
    have hcoeff := congrArg (fun q : MvPolynomial σ R => q.coeff d) hzero
    rw [coeff_gradeLift, hwd, if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
    exact MvPolynomial.mem_support_iff.mp hd hcoeff

@[simp]
theorem gradeLift_eq_zero_iff (w : σ → ℕ) (p : MvPolynomial σ R) :
    gradeLift w p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply MvPolynomial.ext
    intro d
    have hc := congrArg
      (fun q : Polynomial (MvPolynomial σ R) => (q.coeff (weight w d)).coeff d) h
    simpa [coeff_gradeLift] using hc
  · rintro rfl
    exact map_zero _

theorem gradeLift_ne_zero (w : σ → ℕ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    gradeLift w p ≠ 0 :=
  (gradeLift_eq_zero_iff w p).not.mpr hp

/-- Smallest support weight, with value zero on the zero polynomial. -/
def minWeight (w : σ → ℕ) (p : MvPolynomial σ R) : ℕ :=
  (gradeLift w p).natTrailingDegree

/-- Largest support weight, with value zero on the zero polynomial. -/
def maxWeight (w : σ → ℕ) (p : MvPolynomial σ R) : ℕ :=
  (gradeLift w p).natDegree

theorem minWeight_le_of_mem_support (w : σ → ℕ) {p : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : minWeight w p ≤ weight w d := by
  classical
  apply Polynomial.natTrailingDegree_le_of_mem_supp
  rw [support_gradeLift]
  exact Finset.mem_image_of_mem _ hd

theorem weight_le_maxWeight_of_mem_support (w : σ → ℕ) {p : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : weight w d ≤ maxWeight w p := by
  classical
  apply Polynomial.le_natDegree_of_mem_supp
  rw [support_gradeLift]
  exact Finset.mem_image_of_mem _ hd

theorem exists_weight_eq_minWeight (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) : ∃ d ∈ p.support, weight w d = minWeight w p := by
  classical
  have h := Polynomial.natTrailingDegree_mem_support_of_nonzero (gradeLift_ne_zero w hp)
  rw [support_gradeLift] at h
  exact Finset.mem_image.mp h

theorem exists_weight_eq_maxWeight (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) : ∃ d ∈ p.support, weight w d = maxWeight w p := by
  classical
  have h := Polynomial.natDegree_mem_support_of_nonzero (gradeLift_ne_zero w hp)
  rw [support_gradeLift] at h
  exact Finset.mem_image.mp h

theorem minWeight_le_maxWeight (w : σ → ℕ) (p : MvPolynomial σ R) :
    minWeight w p ≤ maxWeight w p :=
  Polynomial.natTrailingDegree_le_natDegree _

theorem le_minWeight_iff (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) (k : ℕ) :
    k ≤ minWeight w p ↔ ∀ d ∈ p.support, k ≤ weight w d := by
  constructor
  · intro hk d hd
    exact hk.trans (minWeight_le_of_mem_support w hd)
  · intro h
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_minWeight w hp
    exact hwd ▸ h d hd

theorem maxWeight_le_iff (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) (k : ℕ) :
    maxWeight w p ≤ k ↔ ∀ d ∈ p.support, weight w d ≤ k := by
  constructor
  · intro hk d hd
    exact (weight_le_maxWeight_of_mem_support w hd).trans hk
  · intro h
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_maxWeight w hp
    exact hwd ▸ h d hd

section Domain

variable [NoZeroDivisors R]

/-- Lowest weights add: cancellation cannot remove the product of the
lowest nonzero homogeneous components. -/
theorem minWeight_mul (w : σ → ℕ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    minWeight w (p * q) = minWeight w p + minWeight w q := by
  unfold minWeight
  rw [map_mul]
  exact Polynomial.natTrailingDegree_mul (gradeLift_ne_zero w hp) (gradeLift_ne_zero w hq)

/-- Highest weights add over a domain as well. -/
theorem maxWeight_mul (w : σ → ℕ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    maxWeight w (p * q) = maxWeight w p + maxWeight w q := by
  unfold maxWeight
  rw [map_mul]
  exact Polynomial.natDegree_mul (gradeLift_ne_zero w hp) (gradeLift_ne_zero w hq)

end Domain

section FiniteVariables

variable [Fintype σ]

theorem weight_eq_sum (w : σ → ℕ) (d : σ →₀ ℕ) :
    weight w d = ∑ i, w i * d i := by
  classical
  exact d.sum_fintype (fun i k => w i * k) (fun _ => mul_zero _)

theorem weight_indicator [DecidableEq σ] (S : Finset σ) (d : σ →₀ ℕ) :
    weight (fun i => if i ∈ S then 1 else 0) d = ∑ i ∈ S, d i := by
  classical
  rw [weight_eq_sum]
  simp [ite_mul, Finset.sum_ite_mem]

theorem weight_one (d : σ →₀ ℕ) : weight (fun _ : σ => 1) d = ∑ i, d i := by
  rw [weight_eq_sum]
  simp

theorem weight_add (w : σ → ℕ) (d e : σ →₀ ℕ) :
    weight w (d + e) = weight w d + weight w e := by
  simp only [weight_eq_sum, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

end FiniteVariables

end GraphicalZonotopes.PolynomialWeights

end
end
end ExtensionPart0

section ExtensionPart1
/- Source: Correspondence/BookSpectrum.lean -/







/-! # The full dimension spectrum and prescribed supports of clique books

This file proves both assertions of Corollary 7.11. The coordinate-support
predicate means literal constancy of every outside coordinate. It does not
require every allowed edge inside the support to be an actual direction.

The key bridge restricts any such polytope to the induced coordinate graph.
It is proved from lower-support reconstruction and exposed edges; it is not
an additional hypothesis on the summand.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.BookSpectrum
open Finset SetFunctionEmbedding

section CoordinateSupport

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

/-- Every coordinate outside `U` is constant on the actual polytope. The
constant can depend on the coordinate and need not be zero. -/
def FixesOutside (Q : Set (V → ℝ)) (U : Finset V) : Prop :=
  ∀ u, u ∉ U → ∃ c : ℝ, ∀ x ∈ Q, x u = c

/-- Ordinary polytopal indecomposability, dimension `|U| - 1`, and literal
fixed outside coordinates, all in the original ambient coordinate space. -/
def HasFullSupportedSummand (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = U.card - 1 ∧ FixesOutside Q U

theorem FixesOutside.no_root_edge {Q : Set (V → ℝ)} {U : Finset V}
    (hfix : FixesOutside Q U) {u v : V} (hu : u ∉ U) :
    ¬ ActualRootEdge Q u v := by
  rintro ⟨huv, p, q, ⟨hpq, l, a, hl, hface⟩, c, hc, hdir⟩
  obtain ⟨b, hb⟩ := hfix u hu
  have hp : p ∈ Q := by
    have hm := left_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hq : q ∈ Q := by
    have hm := right_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have he := congrFun hdir u
  apply hc
  simpa [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_apply,
    huv, Ne.symm huv, hb p hp, hb q hq] using he.symm

theorem card_eq_of_embedding_range (e : W ↪ V) {U : Finset V}
    (hrange : ∀ v, v ∈ U ↔ v ∈ Set.range e) : U.card = Fintype.card W := by
  have he : univ.map e = U := by
    ext v
    simpa only [mem_map, mem_univ, true_and, Set.mem_range] using (hrange v).symm
  rw [← he, card_map, card_univ]

/-- Removing the constant coordinates gives precisely the ordinary
full-dimensional summand problem on the induced coordinate graph. -/
theorem supported_iff_embedding (e : W ↪ V) {G : SimpleGraph V} {U : Finset V}
    (hU : 2 ≤ U.card) (hrange : ∀ v, v ∈ U ↔ v ∈ Set.range e) :
    HasFullSupportedSummand G U ↔ SupportsFullIndecomposable (G.comap e) := by
  have hcard := card_eq_of_embedding_range e hrange
  constructor
  · rintro ⟨Q, hQ, hi, hw, hd, hfix⟩
    have hic := (weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi
    obtain ⟨z, hzs, hze, hdim, hactual⟩ := weak_summand_normalized_function hQ hic hw
    have hext : ExtremeSupermodular z.1 := by
      rcases hze with hz | hz
      · rw [hz, basePolytope_zero, _root_.vectorSpan_singleton, finrank_bot] at hdim
        omega
      · exact hz
    have hrec : extend e (restrict e z.1) = z.1 := by
      apply reconstruct_of_insert_absent e z.1
      intro u hu
      apply insert_absent_of_zero_deltas z.2.1 u
      intro v huv S huS hvS
      by_contra hdelta
      have hedge := (actualRootEdge_iff_nonzero_delta z.2.1.1 hzs u v).mpr
        ⟨huv, S, huS, hvS, hdelta⟩
      have hedgeQ : ActualRootEdge Q u v := by
        change (actualDirectionGraph Q).Adj u v
        rw [hactual]
        exact hedge
      exact hfix.no_root_edge (fun hm => hu ((hrange u).mp hm)) hedgeQ
    have hf := extreme_restrict_of_reconstruction e hext hrec
    have hgp : IsGeneralizedPermutahedron (basePolytope (restrict e z.1)) :=
      ⟨restrict e z.1, hf.1.1, hf.2.1, rfl⟩
    refine ⟨basePolytope (restrict e z.1), hgp.finitePolytope,
      hf.minkowskiIndecomposable, ?_, ?_⟩
    · have he := finrank_vectorSpan_extend e (restrict_translationNormalized e z.2.1)
      rw [hrec] at he
      change Module.finrank ℝ (vectorSpan ℝ (basePolytope (restrict e z.1))) =
        Fintype.card W - 1
      rw [← hcard]
      exact he.symm.trans (hdim.symm.trans hd)
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (restrict_graphical e z.2.2)
  · rintro ⟨Q, hQ, hi, hd, hw⟩
    obtain ⟨z, hzs, hze, hdim⟩ := weak_summand_extreme_or_zero hQ hi hw
    have hd' : Module.finrank ℝ (vectorSpan ℝ Q) = U.card - 1 := by
      simpa only [FullDimension, ← hcard] using hd
    have hext : ExtremeSupermodular z.1 := by
      rcases hze with hz | hz
      · rw [hz, basePolytope_zero, _root_.vectorSpan_singleton, finrank_bot] at hdim
        omega
      · exact hz
    have hf := extend_extreme e hext
    have hgp : IsGeneralizedPermutahedron (basePolytope (extend e z.1)) :=
      ⟨extend e z.1, hf.1.1, hf.2.1, rfl⟩
    refine ⟨basePolytope (extend e z.1), hgp.finitePolytope,
      (minkowskiIndecomposable_iff_polytopal hgp).mp hf.minkowskiIndecomposable,
      (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (extend_graphical e z.2.2), ?_, ?_⟩
    · rw [finrank_vectorSpan_extend e z.2.1]
      exact hdim.symm.trans hd'
    · intro u hu
      refine ⟨0, ?_⟩
      intro x hx
      rw [basePolytope_extend e z.2.1] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact pushVector_outside e y u (fun hm => hu ((hrange u).mpr hm))

end CoordinateSupport

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))

local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

/-- The prescribed hubs, counted in the original book. -/
def hubs {s k : ℕ} (U : Finset (Vertex s k)) : Finset (Fin s) :=
  univ.filter (fun i => Sum.inl i ∈ U)

/-- The prescribed outer vertices, counted in the original book. -/
def outers {s k : ℕ} (U : Finset (Vertex s k)) : Finset (Fin k) :=
  univ.filter (fun j => Sum.inr j ∈ U)

private def enumerate {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    Fin S.card ≃ S :=
  (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm

private def prescribedEmbedding {s k : ℕ} (U : Finset (Vertex s k)) :
    Vertex (hubs U).card (outers U).card ↪ Vertex s k :=
  Function.Embedding.sumMap
    ((enumerate (hubs U)).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩)
    ((enumerate (outers U)).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩)

private theorem prescribedEmbedding_range {s k : ℕ} (U : Finset (Vertex s k))
    (v : Vertex s k) : v ∈ U ↔ v ∈ Set.range (prescribedEmbedding U) := by
  cases v with
  | inl i =>
    constructor
    · intro hi
      have hm : i ∈ hubs U := by simpa [hubs] using hi
      refine ⟨Sum.inl ((enumerate (hubs U)).symm ⟨i, hm⟩), ?_⟩
      simp [prescribedEmbedding]
    · rintro ⟨v, hv⟩
      cases v with
      | inl a =>
        have he : ((enumerate (hubs U)) a).1 = i := Sum.inl_injective hv
        have hm := ((enumerate (hubs U)) a).2
        rw [he] at hm
        simpa [hubs] using hm
      | inr b => exact (Sum.inr_ne_inl hv).elim
  | inr j =>
    constructor
    · intro hj
      have hm : j ∈ outers U := by simpa [outers] using hj
      refine ⟨Sum.inr ((enumerate (outers U)).symm ⟨j, hm⟩), ?_⟩
      simp [prescribedEmbedding]
    · rintro ⟨v, hv⟩
      cases v with
      | inl a => exact (Sum.inl_ne_inr hv).elim
      | inr b =>
        have he : ((enumerate (outers U)) b).1 = j := Sum.inr_injective hv
        have hm := ((enumerate (outers U)) b).2
        rw [he] at hm
        simpa [outers] using hm

private theorem prescribedEmbedding_graph {s k : ℕ} (U : Finset (Vertex s k)) :
    (cliqueBook s k).comap (prescribedEmbedding U) =
      cliqueBook (hubs U).card (outers U).card := by
  ext u v
  change (prescribedEmbedding U u ≠ prescribedEmbedding U v ∧
    ((prescribedEmbedding U u).isLeft ∨ (prescribedEmbedding U v).isLeft)) ↔
    (u ≠ v ∧ (u.isLeft ∨ v.isLeft))
  rw [(prescribedEmbedding U).injective.ne_iff]
  cases u <;> cases v <;> rfl

theorem prescribed_card {s k : ℕ} (U : Finset (Vertex s k)) :
    U.card = (hubs U).card + (outers U).card := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    card_eq_of_embedding_range (prescribedEmbedding U) (prescribedEmbedding_range U)

private theorem book_complete_support {h t : ℕ} (hcard : 2 ≤ h + t) (ht : t ≤ 1) :
    SupportsFullIndecomposable (cliqueBook h t) := by
  have hcl : (cliqueBook h t).IsClique (univ : Finset (Vertex h t)) := by
    intro u hu v hv huv
    refine ⟨huv, ?_⟩
    cases u with
    | inl i => exact Or.inl rfl
    | inr i =>
      cases v with
      | inl j => exact Or.inr rfl
      | inr j =>
        have he : i = j := Fin.ext (by omega)
        exact (huv (congrArg Sum.inr he)).elim
  obtain ⟨Q, hQ, hi, hw, hd⟩ := clique_simplex_witness
    (G := cliqueBook h t) (C := univ)
    (by simpa only [card_univ, Fintype.card_sum, Fintype.card_fin] using hcard) hcl
  exact ⟨Q, hQ.finitePolytope, hi, by simpa only [FullDimension, card_univ] using hd, hw⟩

private theorem one_hub_triangleFree (t : ℕ) : (cliqueBook 1 t).CliqueFree 3 := by
  have unique : ∀ u v : Vertex 1 t, u.isLeft → v.isLeft → u = v := by
    intro u v hu hv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (Subsingleton.elim i j)
      | inr j => simp at hv
    | inr i => simp at hu
  intro C hC
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := card_eq_three.mp hC.card_eq
  have hab := hC.isClique (by simp) (by simp) huv
  have hac := hC.isClique (by simp) (by simp) huw
  have hbc := hC.isClique (by simp) (by simp) hvw
  have hnab : ¬ (u.isLeft ∧ v.isLeft) := fun hh => huv (unique u v hh.1 hh.2)
  have hnac : ¬ (u.isLeft ∧ w.isLeft) := fun hh => huw (unique u w hh.1 hh.2)
  have hnbc : ¬ (v.isLeft ∧ w.isLeft) := fun hh => hvw (unique v w hh.1 hh.2)
  have hab' := hab.2
  have hac' := hac.2
  have hbc' := hbc.2
  tauto

/-- The exact full-dimensional classification also at zero and one hub.
Only the nontrivial-coordinate assumption is imposed. -/
theorem book_full_criterion (h t : ℕ) (hcard : 2 ≤ h + t) :
    SupportsFullIndecomposable (cliqueBook h t) ↔
      t = 0 ∨ (h = 1 ∧ t = 1) ∨ (2 ≤ h ∧ 1 ≤ t ∧ t ≤ cliqueCapacity h) := by
  constructor
  · intro hsupp
    by_cases ht : t = 0
    · exact Or.inl ht
    have htpos : 1 ≤ t := by omega
    by_cases hh : h = 0
    · subst h
      obtain ⟨Q, hQ, hi, hd, hw⟩ := hsupp
      have hz : maximumIndecomposableDimension (cliqueBook 0 t) = 0 :=
        edgeless_maximum_dimension (by
          intro u v hadj
          cases u with
          | inl i => exact Fin.elim0 i
          | inr i =>
            cases v with
            | inl j => exact Fin.elim0 j
            | inr j => simpa [cliqueBook] using hadj)
      have hb := dimension_le_maximum hQ hi hw
      rw [hz] at hb
      simp only [FullDimension, Fintype.card_sum, Fintype.card_fin] at hd
      omega
    by_cases hh1 : h = 1
    · subst h
      obtain ⟨Q, hQ, hi, hd, hw⟩ := hsupp
      have hb := triangleFree_summand_dimension_le_one (one_hub_triangleFree t) hQ hi hw
      simp only [FullDimension, Fintype.card_sum, Fintype.card_fin] at hd
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · have hh2 : 2 ≤ h := by omega
      exact Or.inr (Or.inr ⟨hh2, htpos,
        (clique_book_classification h t hh2 htpos).2.1.mp hsupp⟩)
  · rintro (ht | ⟨hh, ht⟩ | ⟨hh, ht, hcap⟩)
    · exact book_complete_support hcard (by omega)
    · exact book_complete_support hcard (by omega)
    · exact (clique_book_classification h t hh ht).2.1.mpr hcap

/-- Corollary 7.11, prescribed-coordinate form. The set is arbitrary, its
size may be two or three, and all zero-hub and one-hub cases are retained. -/
theorem prescribed_coordinate_criterion {s k : ℕ} (U : Finset (Vertex s k))
    (hU : 2 ≤ U.card) :
    HasFullSupportedSummand (cliqueBook s k) U ↔
      (outers U).card = 0 ∨
      ((hubs U).card = 1 ∧ (outers U).card = 1) ∨
      (2 ≤ (hubs U).card ∧ 1 ≤ (outers U).card ∧
        (outers U).card ≤ cliqueCapacity (hubs U).card) := by
  rw [supported_iff_embedding (prescribedEmbedding U) hU (prescribedEmbedding_range U),
    prescribedEmbedding_graph]
  exact book_full_criterion _ _ (by rwa [← prescribed_card U])

/-- Every positive dimension through the sharp bound has a lattice witness. -/
theorem lattice_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) (hmax : d ≤ min (s + k - 1) (s + cliqueCapacity s - 1)) :
    ∃ Q : Set (Vertex s k → ℝ), LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hds : d ≤ s
  · let j : Fin k := ⟨0, by omega⟩
    let C : Finset (Vertex s k) := insert (Sum.inr j) (univ.image Sum.inl)
    have hC : C.card = s + 1 := by
      simp [C, card_image_of_injective _ Sum.inl_injective]
    have hcl : (cliqueBook s k).IsClique C := by
      intro u hu v hv huv
      refine ⟨huv, ?_⟩
      rcases mem_insert.mp hu with rfl | hu
      · rcases mem_insert.mp hv with rfl | hv
        · exact (huv rfl).elim
        · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
          exact Or.inr rfl
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
        exact Or.inl rfl
    obtain ⟨D, hDC, hD⟩ := exists_subset_card_eq (s := C) (n := d + 1) (by omega)
    obtain ⟨Q, hQ, hi, hw, hdim⟩ := clique_simplex_witness (by omega : 2 ≤ D.card)
      (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q, hQ, (weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,
      hw, by omega⟩
  · let t := d - s + 1
    have hst : s + t - 1 = d := by
      change s + (d - s + 1) - 1 = d
      omega
    have ht : 1 ≤ t := by omega
    have htk : t ≤ k := by omega
    have htcap : t ≤ cliqueCapacity s := by omega
    have hatt := (book_lattice_full s t hs ht htcap).embed
      (bookOuterEmbedding s htk) (bookOuterEmbedding_edges s htk)
    obtain ⟨f, hn, hint, hext, hg, hdim, hb⟩ := hatt
    have hgp : IsGeneralizedPermutahedron (basePolytope f) := ⟨f, hn.1, hext.2.1, rfl⟩
    exact ⟨basePolytope f, hint.basePolytope hn.1 hext.2.1,
      (minkowskiIndecomposable_iff_polytopal hgp).mp hext.minkowskiIndecomposable,
      (isWeakMinkowskiSummand_graphical_iff hn.1 hext.2.1).mpr hg, hdim.trans hst⟩

/-- Corollary 7.11, full positive spectrum, with necessity for every ordinary
polytopal weak summand and sufficiency for every integer in the interval. -/
theorem positive_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) :
    (∃ Q : Set (Vertex s k → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d) ↔
      d ≤ min (s + k - 1) (s + cliqueCapacity s - 1) := by
  constructor
  · rintro ⟨Q, hQ, hi, hw, hdim⟩
    rw [← hdim]
    exact BookDimension.actual_summand_dimension_bound s k hs hQ
      ((weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi) hw
  · intro hmax
    obtain ⟨Q, hQ, hi, hw, hdim⟩ := lattice_dimension_spectrum s k d hs hk hd hmax
    exact ⟨Q, hQ.finitePolytope, hi, hw, hdim⟩

end GraphicalZonotopes.BookSpectrum

end
end
end ExtensionPart1

section ExtensionPart2
/- Source: Correspondence/PolyhedralFace.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The minimal face of a finite homogeneous inequality cone

This optional extension identifies the ordinary minimal convex face through a
point with the tight-inequality face. Its linear span and affine direction space
are exactly the complete tight kernel. The assertion of minimality quantifies
over all convex extreme subsets, using Mathlib's `Convex` and `IsExtreme`.
-/

noncomputable section

namespace GraphicalZonotopes.Polyhedral

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

/-- The actual solution set of the homogeneous linear inequalities. -/
def nonnegativeCone (A : I → E →ₗ[ℝ] ℝ) : Set E := {x | Nonnegative A x}

/-- The part of the cone on which every inequality tight at `y` remains tight. -/
def tightFace (A : I → E →ₗ[ℝ] ℝ) (y : E) : Set E :=
  {x | Nonnegative A x ∧ x ∈ tightKernel A y}

theorem self_mem_tightFace {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) : y ∈ tightFace A y :=
  ⟨hy, self_mem_tightKernel A y⟩

theorem zero_mem_tightFace (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    (0 : E) ∈ tightFace A y :=
  ⟨by intro i; simp, (tightKernel A y).zero_mem⟩

theorem tightFace_convex (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    Convex ℝ (tightFace A y) := by
  apply convex_iff_add_mem.mpr
  intro u hu v hv a b ha hb _hab
  refine ⟨?_, (tightKernel A y).add_mem
    ((tightKernel A y).smul_mem a hu.2) ((tightKernel A y).smul_mem b hv.2)⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i))

theorem tightFace_isExtreme (A : I → E →ₗ[ℝ] ℝ) (y : E) :
    IsExtreme ℝ (nonnegativeCone A) (tightFace A y) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro u hu v hv z hz ⟨a, b, ha, hb, _hab, habz⟩
  refine ⟨hu, ?_⟩
  intro i hi
  have hz0 : A i z = 0 := hz.2 i hi
  have hrow := congrArg (A i) habz
  simp only [map_add, map_smul, smul_eq_mul] at hrow
  have hv0 : 0 ≤ b * A i v := mul_nonneg hb.le (hv i)
  have hu0 : a * A i u = 0 :=
    le_antisymm (by linarith) (mul_nonneg ha.le (hu i))
  exact (mul_eq_zero.mp hu0).resolve_left (ne_of_gt ha)

/-- Every extreme subset of the cone containing `y` contains the tight face.

The finite-inequality perturbation lemma puts `y` in an open segment from any
point of the tight face to another point of the cone. The defining property of
an extreme subset then forces that first endpoint into the subset.
-/
theorem tightFace_subset_of_isExtreme {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) {F : Set E}
    (hF : IsExtreme ℝ (nonnegativeCone A) F) (hyF : y ∈ F) :
    tightFace A y ⊆ F := by
  intro v hv
  obtain ⟨ε, hε, _hp, hm⟩ := exists_two_sided_perturbation hy hv.2
  let r : ℝ := 1 + ε
  have hr : 0 < r := by dsimp [r]; linarith
  let w : E := r • y - ε • v
  have hw : Nonnegative A w := by
    intro i
    dsimp [w]
    simp only [map_sub, map_smul, smul_eq_mul]
    have hmi := hm i
    simp only [map_sub, map_smul, smul_eq_mul] at hmi
    have hrest : 0 ≤ (r - 1 / 2) * A i y :=
      mul_nonneg (by dsimp [r]; linarith) (hy i)
    linarith
  have hsum : ε * r⁻¹ + r⁻¹ = 1 := by
    calc
      ε * r⁻¹ + r⁻¹ = (ε + 1) * r⁻¹ := by ring
      _ = 1 := by simpa [r, add_comm] using mul_inv_cancel₀ (ne_of_gt hr)
  have hcomb : (ε * r⁻¹) • v + r⁻¹ • w = y := by
    calc
      (ε * r⁻¹) • v + r⁻¹ • w =
          (r⁻¹ * r) • y + (ε * r⁻¹ - r⁻¹ * ε) • v := by dsimp [w]; module
      _ = y := by rw [inv_mul_cancel₀ (ne_of_gt hr)]; simp [mul_comm]
  exact hF.left_mem_of_mem_openSegment hv.1 hw hyF
    ⟨ε * r⁻¹, r⁻¹, mul_pos hε (inv_pos.mpr hr), inv_pos.mpr hr, hsum, hcomb⟩

/-- The tight face is the least ordinary convex face of the cone containing `y`.
No pointedness or finite-dimensionality hypothesis is needed. -/
theorem tightFace_isLeast {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    IsLeast {F : Set E | Convex ℝ F ∧ IsExtreme ℝ (nonnegativeCone A) F ∧ y ∈ F}
      (tightFace A y) := by
  refine ⟨⟨tightFace_convex A y, tightFace_isExtreme A y, self_mem_tightFace hy⟩, ?_⟩
  intro F hF
  exact tightFace_subset_of_isExtreme hy hF.2.1 hF.2.2

theorem span_tightFace_eq_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    Submodule.span ℝ (tightFace A y) = tightKernel A y := by
  refine le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) ?_
  intro v hv
  obtain ⟨ε, hε, hp, _hm⟩ := exists_two_sided_perturbation hy hv
  have hyF : y ∈ tightFace A y := self_mem_tightFace hy
  have hpF : (1 / 2 : ℝ) • y + ε • v ∈ tightFace A y :=
    ⟨hp, (tightKernel A y).add_mem
      ((tightKernel A y).smul_mem (1 / 2 : ℝ) (self_mem_tightKernel A y))
      ((tightKernel A y).smul_mem ε hv)⟩
  have hvε : ε • v ∈ Submodule.span ℝ (tightFace A y) := by
    have h := (Submodule.span ℝ (tightFace A y)).sub_mem
      (Submodule.subset_span hpF)
      ((Submodule.span ℝ (tightFace A y)).smul_mem (1 / 2 : ℝ)
        (Submodule.subset_span hyF))
    simpa only [add_sub_cancel_left] using h
  have h := (Submodule.span ℝ (tightFace A y)).smul_mem ε⁻¹ hvε
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] using h

theorem vectorSpan_tightFace_eq_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) : vectorSpan ℝ (tightFace A y) = tightKernel A y := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (zero_mem_tightFace A y)]
  simpa only [vsub_eq_sub, sub_zero, Set.image_id'] using span_tightFace_eq_tightKernel hy

/-- Literal minimal-face and complete-kernel correspondence for the finite
inequality cone underlying Lemma 2.2 of the paper. -/
theorem minimal_face_tight_kernel {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : Nonnegative A y) :
    IsLeast {F : Set E | Convex ℝ F ∧ IsExtreme ℝ (nonnegativeCone A) F ∧ y ∈ F}
        (tightFace A y) ∧
      Submodule.span ℝ (tightFace A y) = tightKernel A y ∧
      vectorSpan ℝ (tightFace A y) = tightKernel A y :=
  ⟨tightFace_isLeast hy, span_tightFace_eq_tightKernel hy,
    vectorSpan_tightFace_eq_tightKernel hy⟩

theorem extremeRay_iff_minimal_face_span {A : I → E →ₗ[ℝ] ℝ}
    (hA : Pointed A) {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ Submodule.span ℝ (tightFace A y) = Submodule.span ℝ {y} := by
  rw [span_tightFace_eq_tightKernel hy]
  exact extremeRay_iff_tightKernel hA hy hne

/-- The dimension-one criterion for the actual minimal convex face. -/
theorem extremeRay_iff_minimal_face_finrank {A : I → E →ₗ[ℝ] ℝ}
    (hA : Pointed A) {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ Module.finrank ℝ (vectorSpan ℝ (tightFace A y)) = 1 := by
  rw [vectorSpan_tightFace_eq_tightKernel hy]
  constructor
  · intro he
    rw [he.tightKernel_eq_span]
    exact finrank_span_singleton hne
  · intro hd
    exact extremeRay_of_tightKernel hA hy hne
      (eq_span_singleton_of_mem_of_finrank_eq_one hd (self_mem_tightKernel A y) hne)

end GraphicalZonotopes.Polyhedral

end
end
end ExtensionPart2

section ExtensionPart3
/- Source: Correspondence/SeparatorFace.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The separator relation space as the span of an actual minimal face

This optional extension combines Theorem 5.4's exact tight-kernel isomorphism
with the ordinary minimal-face theorem for a finite inequality cone. The ambient
cone below is literally the supermodular cone in `graphicalFunctionSpace G`.
-/

noncomputable section
open scoped Classical

namespace GraphicalZonotopes.Separator

section Ordered

variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The canonical tight face through the positively glued graphical function.
The theorem below proves that it is the actual least convex face containing it. -/
def gluedMinimalFace (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Set (graphicalFunctionSpace G) :=
  Polyhedral.tightFace (contextRow G) (functionEquiv h (gluedCoordinates f z lam))

/-- The exact relation-space interpretation of the actual minimal face.

The hypotheses are the literal private-kernel equalities of Theorem 5.4. The
conclusion includes universal minimality among all convex extreme subsets of
the genuine supermodular cone, a linear isomorphism of its span with the response
relation space, and the corresponding affine-dimension identity.
-/
theorem positive_response_gluing_minimal_face (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
    (hlam : ∀ j, 0 < lam j) (hf : ∀ j, f j ≠ 0)
    (hi : ∀ j r, 0 ≤ (rowData h).internal j r (f j))
    (hprivate : ∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
      Submodule.span ℝ {f j})
    (hclose : (rowData h).Closure (conditionalMin h f) z lam) :
    IsLeast {F : Set (graphicalFunctionSpace G) |
        Convex ℝ F ∧ IsExtreme ℝ {q | Supermodular q.1} F ∧
          functionEquiv h (gluedCoordinates f z lam) ∈ F}
        (gluedMinimalFace h f z lam) ∧
      Nonempty ((Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
        LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) ∧
      Module.finrank ℝ (vectorSpan ℝ (gluedMinimalFace h f z lam)) =
        Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) := by
  have hline : ∀ j g, (rowData h).PrivateKernel f (conditionalMin h f) j g →
      ∃ c : ℝ, g = c • f j :=
    fun j => (Gluing.privateKernelSpace_eq_span_iff
      (rowData h) f (conditionalMin h f) j).mp (hprivate j)
  have hp : Polyhedral.Nonnegative (contextRow G)
      (functionEquiv h (gluedCoordinates f z lam)) :=
    (supermodular_iff_boundarySlacks_nonnegative G _).mp
      (glued_supermodular h f z lam hlam hf hi hline hclose)
  have hcone : Polyhedral.nonnegativeCone (contextRow G) =
      {q : graphicalFunctionSpace G | Supermodular q.1} := by
    ext q
    exact (supermodular_iff_boundarySlacks_nonnegative G q).symm
  have hleast := Polyhedral.tightFace_isLeast hp
  rw [hcone] at hleast
  have hequiv : (Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
      LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)) :=
    (LinearEquiv.ofEq _ _ (Polyhedral.span_tightFace_eq_tightKernel hp)).trans
      (graphicalTightRelationEquiv h f z lam hlam hf hi hline hclose)
  refine ⟨hleast, ⟨hequiv⟩, ?_⟩
  change Module.finrank ℝ (vectorSpan ℝ
    (Polyhedral.tightFace (contextRow G) (functionEquiv h (gluedCoordinates f z lam)))) = _
  rw [Polyhedral.vectorSpan_tightFace_eq_tightKernel hp]
  exact graphical_tight_finrank_eq_relation_finrank h f z lam hlam hf hi hline hclose

end Ordered

/-- The ordinary-face interpretation on every finite vertex type. The order
used to orient unordered edges is chosen internally, exactly as in the finite
version of Theorem 5.4; it is not additional structure on the input graph. -/
theorem positive_response_gluing_minimal_face_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ {J : Type*} [Fintype J] [DecidableEq J]
      {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
      (h : Partition G B A)
      (f : ∀ j, privateIndex G B A j → ℝ)
      (z : boundaryIndex G B → ℝ) (lam : J → ℝ),
      (∀ j, 0 < lam j) → (∀ j, f j ≠ 0) →
      (∀ j r, 0 ≤ (rowData h).internal j r (f j)) →
      (∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
        Submodule.span ℝ {f j}) →
      (rowData h).Closure (conditionalMin h f) z lam →
      IsLeast {F : Set (graphicalFunctionSpace G) |
          Convex ℝ F ∧ IsExtreme ℝ {q | Supermodular q.1} F ∧
            functionEquiv h (gluedCoordinates f z lam) ∈ F}
          (gluedMinimalFace h f z lam) ∧
        Nonempty ((Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
          LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) ∧
        Module.finrank ℝ (vectorSpan ℝ (gluedMinimalFace h f z lam)) =
          Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) := by
  letI : LinearOrder V := finiteVertexOrder V
  intro J _ _ G B A h f z lam hlam hf hi hprivate hclose
  exact positive_response_gluing_minimal_face h f z lam hlam hf hi hprivate hclose

end GraphicalZonotopes.Separator

end
end
end ExtensionPart3

section ExtensionPart4
/- Source: Correspondence/NewtonGeometry.lean -/








/-!
# Every polynomial with the path Newton polytope is absolutely irreducible

The Newton polytope is the ordinary real convex hull of the exponent support.
For a product whose Newton polytope is a supermodular base polytope, minimum
subset weights and maximum total weight prove the actual Minkowski identity.
This avoids needing a generic Newton-product theorem for arbitrary polytopes.

The factorization argument uses the original supermodular extreme ray and one
literal slack of value one. Factor Newton polytopes have integral lower-support
values and nonnegative coordinates. The singleton minima of the two factors
therefore vanish separately, so their lower-support functions need no further
translation normalization.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.NewtonGeometry

open Finset
open PolynomialWeights

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

/-- Exponents are embedded in the actual standard real coordinate space. -/
def exponentVector (d : V →₀ ℕ) : V → ℝ := fun v => (d v : ℝ)

/-- The ordinary Newton polytope, including the empty polytope for zero. -/
def newtonPolytope (p : MvPolynomial V R) : Set (V → ℝ) :=
  convexHull ℝ (exponentVector '' (p.support : Set (V →₀ ℕ)))

@[simp] theorem exponentVector_zero : exponentVector (0 : V →₀ ℕ) = 0 := by
  funext v
  simp [exponentVector]

@[simp] theorem exponentVector_add (d e : V →₀ ℕ) :
    exponentVector (d + e) = exponentVector d + exponentVector e := by
  funext v
  simp [exponentVector, Nat.cast_add]

theorem support_mem_newton {p : MvPolynomial V R} {d : V →₀ ℕ}
    (hd : d ∈ p.support) : exponentVector d ∈ newtonPolytope p :=
  subset_convexHull ℝ _ ⟨d, hd, rfl⟩

@[simp] theorem newton_zero : newtonPolytope (0 : MvPolynomial V R) = ∅ := by
  simp [newtonPolytope]

theorem newton_nonempty {p : MvPolynomial V R} (hp : p ≠ 0) :
    (newtonPolytope p).Nonempty := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp
  exact ⟨exponentVector d, support_mem_newton hd⟩

theorem newton_lattice (p : MvPolynomial V R) : LatticePolytope (newtonPolytope p) := by
  classical
  refine ⟨p.support.image (fun d => fun v => (d v : ℤ)), ?_⟩
  unfold newtonPolytope
  congr 1
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun v => (d v : ℤ), mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    funext v
    simp [exponentVector]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hy
    refine ⟨d, hd, ?_⟩
    funext v
    simp [exponentVector]

theorem newton_C {c : R} (hc : c ≠ 0) :
    newtonPolytope (MvPolynomial.C c : MvPolynomial V R) = {0} := by
  classical
  simp [newtonPolytope, MvPolynomial.support_C, hc]

theorem newton_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (p : MvPolynomial V R) :
    newtonPolytope (MvPolynomial.map f p) = newtonPolytope p := by
  unfold newtonPolytope
  rw [MvPolynomial.support_map_of_injective p hf]

def subsetWeight (S : Finset V) : V → ℕ := fun v => if v ∈ S then 1 else 0

theorem subsetSum_exponentVector (d : V →₀ ℕ) (S : Finset V) :
    subsetSum (exponentVector d) S = (weight (subsetWeight S) d : ℝ) := by
  change subsetSum (exponentVector d) S =
    (weight (fun v => if v ∈ S then 1 else 0) d : ℝ)
  rw [weight_indicator]
  simp [subsetSum, exponentVector]

private theorem convex_subsetSum_ge (S : Finset V) (c : ℝ) :
    Convex ℝ {x : V → ℝ | c ≤ subsetSum x S} := by
  intro x hx y hy a b ha hb hab
  change c ≤ subsetSum (a • x + b • y) S
  rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * subsetSum x S + b * subsetSum y S :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

private theorem convex_subsetSum_le (S : Finset V) (c : ℝ) :
    Convex ℝ {x : V → ℝ | subsetSum x S ≤ c} := by
  intro x hx y hy a b ha hb hab
  change subsetSum (a • x + b • y) S ≤ c
  rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
  calc
    a * subsetSum x S + b * subsetSum y S ≤ a * c + b * c :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = c := by rw [← add_mul, hab, one_mul]

theorem lower_weight_bound (p : MvPolynomial V R) (S : Finset V)
    {x : V → ℝ} (hx : x ∈ newtonPolytope p) :
    (minWeight (subsetWeight S) p : ℝ) ≤ subsetSum x S := by
  apply convexHull_min ?_ (convex_subsetSum_ge S _) hx
  rintro y ⟨d, hd, rfl⟩
  change (minWeight (subsetWeight S) p : ℝ) ≤ subsetSum (exponentVector d) S
  rw [subsetSum_exponentVector]
  exact_mod_cast minWeight_le_of_mem_support (subsetWeight S) hd

theorem upper_weight_bound (p : MvPolynomial V R) (S : Finset V)
    {x : V → ℝ} (hx : x ∈ newtonPolytope p) :
    subsetSum x S ≤ (maxWeight (subsetWeight S) p : ℝ) := by
  apply convexHull_min ?_ (convex_subsetSum_le S _) hx
  rintro y ⟨d, hd, rfl⟩
  change subsetSum (exponentVector d) S ≤ (maxWeight (subsetWeight S) p : ℝ)
  rw [subsetSum_exponentVector]
  exact_mod_cast weight_le_maxWeight_of_mem_support (subsetWeight S) hd

/-- The ordinary geometric lower support is exactly the smallest subset weight. -/
theorem lowerSupport_newton {p : MvPolynomial V R} (hp : p ≠ 0) (S : Finset V) :
    lowerSupport (newtonPolytope p) S = (minWeight (subsetWeight S) p : ℝ) := by
  obtain ⟨d, hd, hwd⟩ := exists_weight_eq_minWeight (subsetWeight S) hp
  have hleast : IsLeast ((fun x => subsetSum x S) '' newtonPolytope p)
      (minWeight (subsetWeight S) p : ℝ) := by
    refine ⟨⟨exponentVector d, support_mem_newton hd, ?_⟩, ?_⟩
    · change subsetSum (exponentVector d) S = (minWeight (subsetWeight S) p : ℝ)
      rw [subsetSum_exponentVector, hwd]
    · rintro _ ⟨x, hx, rfl⟩
      exact lower_weight_bound p S hx
  exact hleast.csInf_eq

theorem lowerSupport_newton_nonnegative {p : MvPolynomial V R} (hp : p ≠ 0)
    (S : Finset V) : 0 ≤ lowerSupport (newtonPolytope p) S := by
  rw [lowerSupport_newton hp S]
  exact Nat.cast_nonneg _

/-- The easy direction uses only support containment for multiplication. -/
theorem newton_product_subset_sum (p q : MvPolynomial V R) :
    newtonPolytope (p * q) ⊆ newtonPolytope p + newtonPolytope q := by
  apply convexHull_min ?_ ((newton_lattice p).convex.add (newton_lattice q).convex)
  rintro x ⟨d, hd, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [← hab, exponentVector_add]
  exact Set.add_mem_add (support_mem_newton ha) (support_mem_newton hb)

section Domain

variable [NoZeroDivisors R]

/-- Subset minima add even when coefficients of individual product monomials
cancel. The retained-monomial weight lift proves the needed noncancellation. -/
theorem lowerSupport_newton_mul {p q : MvPolynomial V R} (hp : p ≠ 0) (hq : q ≠ 0) :
    lowerSupport (newtonPolytope (p * q)) =
      lowerSupport (newtonPolytope p) + lowerSupport (newtonPolytope q) := by
  funext S
  simp only [Pi.add_apply, lowerSupport_newton (mul_ne_zero hp hq),
    lowerSupport_newton hp, lowerSupport_newton hq, minWeight_mul _ hp hq, Nat.cast_add]

/-- The actual Newton-product identity when the product polytope is a
supermodular base polytope. All lower facet inequalities and the total affine
hyperplane are proved from extremal polynomial support weights. -/
theorem newton_mul_of_basePolytope {p q : MvPolynomial V R} (hp : p ≠ 0) (hq : q ≠ 0)
    {z : SetFunction V} (hn : Normalized z) (hs : Supermodular z)
    (hnewt : newtonPolytope (p * q) = basePolytope z) :
    newtonPolytope p + newtonPolytope q = basePolytope z := by
  have hsum : lowerSupport (newtonPolytope p) + lowerSupport (newtonPolytope q) = z := by
    rw [← lowerSupport_newton_mul hp hq, hnewt, lowerSupport_basePolytope hn hs]
  have hmax : (maxWeight (subsetWeight univ) (p * q) : ℝ) = z univ := by
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_maxWeight (subsetWeight univ) (mul_ne_zero hp hq)
    have hmem := support_mem_newton hd
    rw [hnewt] at hmem
    have ht := hmem.1
    rw [subsetSum_exponentVector, hwd] at ht
    exact ht
  have hmaxsum : (maxWeight (subsetWeight univ) p : ℝ) +
      (maxWeight (subsetWeight univ) q : ℝ) = z univ := by
    rw [← Nat.cast_add, ← maxWeight_mul _ hp hq]
    exact hmax
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    have hlower : ∀ S, z S ≤ subsetSum (x + y) S := by
      intro S
      have he := congrFun hsum S
      change lowerSupport (newtonPolytope p) S + lowerSupport (newtonPolytope q) S = z S at he
      rw [← he, subsetSum_add]
      exact add_le_add (lowerSupport_le (newton_lattice p).compact hx S)
        (lowerSupport_le (newton_lattice q).compact hy S)
    refine ⟨le_antisymm ?_ (hlower univ), hlower⟩
    calc
      subsetSum (x + y) univ = subsetSum x univ + subsetSum y univ := subsetSum_add _ _ _
      _ ≤ (maxWeight (subsetWeight univ) p : ℝ) +
          (maxWeight (subsetWeight univ) q : ℝ) :=
        add_le_add (upper_weight_bound p univ hx) (upper_weight_bound q univ hy)
      _ = z univ := hmaxsum
  · rw [← hnewt]
    exact newton_product_subset_sum p q

end Domain

section Field

variable {K : Type*} [Field K]

theorem isUnit_of_newton_zero {p : MvPolynomial V K} (hp : p ≠ 0)
    (hnewt : newtonPolytope p = {0}) : IsUnit p := by
  have he : p = MvPolynomial.monomial 0 (p.coeff 0) := by
    apply MvPolynomial.eq_monomial_of_support_subset_singleton
    intro d hd
    have hd0 := support_mem_newton hd
    rw [hnewt, Set.mem_singleton_iff] at hd0
    ext v
    have hv := congrFun hd0 v
    change (d v : ℝ) = 0 at hv
    exact_mod_cast hv
  rw [← MvPolynomial.C_apply] at he
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [he, hc, map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- A factorization of a normalized extreme base polytope with a unit slack
has a factor whose Newton polytope is the origin. -/
theorem factor_newton_zero_of_extreme_unit_slack {p q : MvPolynomial V K}
    (hp : p ≠ 0) (hq : q ≠ 0) {z : SetFunction V}
    (hz : ExtremeSupermodular z) {u v : V} {S : Finset V}
    (hδ : delta z u v S = 1)
    (hnewt : newtonPolytope (p * q) = basePolytope z) :
    newtonPolytope p = {0} ∨ newtonPolytope q = {0} := by
  let P := newtonPolytope p
  let Q := newtonPolytope q
  let f := lowerSupport P
  let g := lowerSupport Q
  have hP : IsCompact P := (newton_lattice p).compact
  have hQ : IsCompact Q := (newton_lattice q).compact
  have hnP : P.Nonempty := newton_nonempty hp
  have hnQ : Q.Nonempty := newton_nonempty hq
  have he : P + Q = basePolytope z := newton_mul_of_basePolytope hp hq hz.1.1 hz.2.1 hnewt
  have hes : Q + P = basePolytope z := by rw [add_comm]; exact he
  have hsum : f + g = z := by
    change lowerSupport P + lowerSupport Q = z
    rw [← lowerSupport_add hP hQ hnP hnQ, he, lowerSupport_basePolytope hz.1.1 hz.2.1]
  have hf0 : ∀ T, 0 ≤ f T := fun T => lowerSupport_newton_nonnegative hp T
  have hg0 : ∀ T, 0 ≤ g T := fun T => lowerSupport_newton_nonnegative hq T
  have hfn : TranslationNormalized f := by
    refine ⟨lowerSupport_normalized hP hnP, ?_⟩
    intro w
    have ht := congrFun hsum {w}
    change f {w} + g {w} = z {w} at ht
    rw [hz.1.2 w] at ht
    exact le_antisymm (by linarith [hg0 {w}]) (hf0 {w})
  have hgn : TranslationNormalized g := by
    refine ⟨lowerSupport_normalized hQ hnQ, ?_⟩
    intro w
    have ht := congrFun hsum {w}
    change f {w} + g {w} = z {w} at ht
    rw [hz.1.2 w] at ht
    exact le_antisymm (by linarith [hf0 {w}]) (hg0 {w})
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hz.1.1 hz.2.1 hP hQ hnP hnQ he
  have hgs : Supermodular g :=
    summand_lowerSupport_supermodular hz.1.1 hz.2.1 hQ hP hnQ hnP hes
  have hfi : IntegerValued f := (newton_lattice p).lowerSupport_integerValued hnP
  have hgi : IntegerValued g := (newton_lattice q).lowerSupport_integerValued hnQ
  have hbodyP : P = basePolytope f :=
    summand_eq_basePolytope hz.1.1 hz.2.1 hP hQ (newton_lattice p).convex hnP hnQ he
  have hbodyQ : Q = basePolytope g :=
    summand_eq_basePolytope hz.1.1 hz.2.1 hQ hP (newton_lattice q).convex hnQ hnP hes
  obtain ⟨a, ha, hfa⟩ := hz.2.2.2 f g hfn hgn hfs hgs hsum
  obtain ⟨b, hb, hgb⟩ := hz.2.2.2 g f hgn hfn hgs hfs (by rw [add_comm]; exact hsum)
  have hdf : delta f u v S = a := by rw [hfa, delta_smul, hδ, mul_one]
  have hdg : delta g u v S = b := by rw [hgb, delta_smul, hδ, mul_one]
  by_cases ha0 : a = 0
  · left
    change P = {0}
    rw [hbodyP, hfa, ha0, zero_smul, basePolytope_zero]
  by_cases hb0 : b = 0
  · right
    change Q = {0}
    rw [hbodyQ, hgb, hb0, zero_smul, basePolytope_zero]
  have hdf1 := hfi.positive_delta_ge_one u v S
    (by rw [hdf]; exact lt_of_le_of_ne ha (Ne.symm ha0))
  have hdg1 := hgi.positive_delta_ge_one u v S
    (by rw [hdg]; exact lt_of_le_of_ne hb (Ne.symm hb0))
  have hdsum : delta f u v S + delta g u v S = 1 := by rw [← delta_add, hsum, hδ]
  exfalso
  linarith

/-- A general characteristic-independent criterion: an exact normalized
extreme Newton base polytope with one unit elemental slack forces irreducibility. -/
theorem irreducible_of_newton_base_extreme_unit_slack {p : MvPolynomial V K}
    {z : SetFunction V} (hz : ExtremeSupermodular z) {u v : V} {S : Finset V}
    (hδ : delta z u v S = 1) (hnewt : newtonPolytope p = basePolytope z) :
    Irreducible p := by
  have hp : p ≠ 0 := by
    intro hp0
    have hn := basePolytope_nonempty hz.1.1 hz.2.1
    rw [← hnewt, hp0, newton_zero] at hn
    exact Set.not_nonempty_empty hn
  constructor
  · intro hu
    obtain ⟨c, hc, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    have hzero : basePolytope z = ({0} : Set (V → ℝ)) :=
      hnewt.symm.trans (newton_C hc.ne_zero)
    have hls := congrArg lowerSupport hzero
    rw [lowerSupport_basePolytope hz.1.1 hz.2.1] at hls
    apply hz.2.2.1
    calc
      z = lowerSupport ({0} : Set (V → ℝ)) := hls
      _ = 0 := by funext T; simp [lowerSupport, subsetSum]
  · intro a b hab
    have ha : a ≠ 0 := by intro ha0; apply hp; rw [hab, ha0, zero_mul]
    have hb : b ≠ 0 := by intro hb0; apply hp; rw [hab, hb0, mul_zero]
    have hn : newtonPolytope (a * b) = basePolytope z := by rw [← hab]; exact hnewt
    rcases factor_newton_zero_of_extreme_unit_slack ha hb hz hδ hn with ha0 | hb0
    · exact Or.inl (isUnit_of_newton_zero ha ha0)
    · exact Or.inr (isUnit_of_newton_zero hb hb0)

end Field

section Path

variable {K : Type*} [Field K]

/-- The ordinary irreducibility assertion for every polynomial with the
literal path Newton polytope, in every field and for every `n ≥ 4`. -/
theorem irreducible_of_newton_path {n : ℕ} (hn : 4 ≤ n)
    {p : MvPolynomial (Fin n) K} (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible p := by
  obtain ⟨S, _hu, _hv, hδ⟩ := Path.consecutive_positive_slack hn
    (⟨0, by omega⟩ : Fin (n - 1))
  exact irreducible_of_newton_base_extreme_unit_slack (Path.setFunction_extreme hn) hδ hnewt

/-- The conclusion persists under every field embedding, because scalar
extension preserves the entire exponent support. -/
theorem irreducible_map_of_newton_path {L : Type*} [Field L] (f : K →+* L)
    {n : ℕ} (hn : 4 ≤ n) {p : MvPolynomial (Fin n) K}
    (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible (MvPolynomial.map f p) := by
  apply irreducible_of_newton_path hn
  rw [newton_map f f.injective p, hnewt]

/-- Corollary A.3: every polynomial with exactly `Q_n` as its Newton polytope
is irreducible after extension to an algebraic closure. -/
theorem corollary_A_3_absoluteIrreducible {n : ℕ} (hn : 4 ≤ n)
    {p : MvPolynomial (Fin n) K} (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) p) :=
  irreducible_map_of_newton_path (algebraMap K (AlgebraicClosure K)) hn hnewt

end Path

end GraphicalZonotopes.NewtonGeometry

end
end
end ExtensionPart4

#print_proof_audit_bundle [
  GraphicalZonotopes.Path.principal_path_theorem,
  GraphicalZonotopes.Path.polytope_defining_equations,
  GraphicalZonotopes.Path.polytope_defining_equations_real,
  GraphicalZonotopes.Path.polytope_defining_equations_sums,
  GraphicalZonotopes.Path.setFunction_expansion,
  GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction,
  GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete,
  GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal,
  GraphicalZonotopes.sharp_direction_bounds,
  GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root,
  GraphicalZonotopes.root_parallel_pair_eq,
  GraphicalZonotopes.direction_bounds_polytopal,
  GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra,
  GraphicalZonotopes.edge_bound_of_connected_tetrahedra,
  GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra,
  GraphicalZonotopes.Path.setFunction_eq_booleanFormula,
  GraphicalZonotopes.Path.polytope_boolean_defining_equations,
  GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem,
  GraphicalZonotopes.BooleanFourier.boolean_face_line,
  GraphicalZonotopes.BooleanFourier.faceKernel_finrank,
  GraphicalZonotopes.threeTree_classification_polytopal,
  GraphicalZonotopes.threeTree_classification,
  GraphicalZonotopes.threeTree_classification_literal,
  GraphicalZonotopes.admissible_threeTree_lattice_witness,
  GraphicalZonotopes.threeTree_lattice_dilation_sharp,
  GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal,
  GraphicalZonotopes.Separator.induced_separator_capacity_finite,
  GraphicalZonotopes.Separator.positive_response_gluing_finite,
  GraphicalZonotopes.Separator.clique_separator_capacity_finite,
  GraphicalZonotopes.unit_lattice_classification_sharp,
  GraphicalZonotopes.unit_lattice_classification_polytopal,
  GraphicalZonotopes.unit_translated_lattice_classification_polytopal,
  GraphicalZonotopes.threeTree_translated_lattice_lower_bound,
  GraphicalZonotopes.FourPartCompletion.cartesian_completion,
  GraphicalZonotopes.four_partite_spanning_threeTrees,
  GraphicalZonotopes.four_partite_threeTree_dimension_attained,
  GraphicalZonotopes.threeTree_actual_dimension_admissible,
  GraphicalZonotopes.admissible_threeTree_active_witness,
  GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal,
  GraphicalZonotopes.optimal_k5_free_dilation,
  GraphicalZonotopes.optimal_k5_free_dilation_attained,
  GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal,
  GraphicalZonotopes.DoubledParts.one_singleton_decomposition,
  GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition,
  GraphicalZonotopes.boolean_decomposition_every_dimension,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books,
  GraphicalZonotopes.BooleanModule.one_outer_lattice_book,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1,
  GraphicalZonotopes.DiamondBook.maximum_dimension,
  GraphicalZonotopes.DiamondBook.diamond_witness_multipartite,
  GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree,
  GraphicalZonotopes.BooleanModule.positive_star_interpolation,
  GraphicalZonotopes.BooleanModule.negative_star_interpolation,
  GraphicalZonotopes.BooleanModule.threshold_book_interval,
  GraphicalZonotopes.BooleanModule.book_upper_interval,
  GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal,
  GraphicalZonotopes.not_fullLatticeSummandAt_zero,
  GraphicalZonotopes.PathJoin.corollary_nine_four,
  GraphicalZonotopes.PathJoin.appendix_B_one,
  GraphicalZonotopes.clique_book_classification,
  GraphicalZonotopes.clique_book_classification_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric,
  GraphicalZonotopes.saturatedHubNeighbors_closed_formula,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal,
  GraphicalZonotopes.TwoHub.exponential_lattice_summand,
  GraphicalZonotopes.TwoHub.exponential_family,
  GraphicalZonotopes.TwoHub.exponential_polytopal_summand,
  GraphicalZonotopes.TwoHub.two_singleton_classification,
  GraphicalZonotopes.TwoHub.classification_polytopal,
  GraphicalZonotopes.TwoHub.full_polytopal_iff,
  GraphicalZonotopes.TwoHub.lattice_polytopal_attainment,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum,
  GraphicalZonotopes.threeTree_dimension_and_spectrum,
  GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite,
  GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one,
  GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle,
  GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected,
  GraphicalZonotopes.weak_summand_exposed_edge_direction,
  GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal,
  GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.partial_threeTree_polytope_support,
  GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula,
  GraphicalZonotopes.TwoHub.paper_corollary_8_5,
  GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le,
  GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian,
  GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite,
  GraphicalZonotopes.actualEdgeDirectionLines_finite,
  GraphicalZonotopes.directionCount_eq_geometric_line_count,
  GraphicalZonotopes.three_hub_book_maximum,
  GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree,
  GraphicalZonotopes.TreeJoin.maximum_dimension,
  GraphicalZonotopes.TreeJoin.supports_full_iff,
  GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join,
  GraphicalZonotopes.SparseFamily.complete_family,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid,
  GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper,
  GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq,
  GraphicalZonotopes.TwoHub.decision_tree_lattice_summand,
  GraphicalZonotopes.TwoHub.paper_lemma_8_6,
  GraphicalZonotopes.paper_corollary_6_4,
  GraphicalZonotopes.paper_corollary_6_4_stacked,
  GraphicalZonotopes.paper_corollary_6_5,
  GraphicalZonotopes.planar_threeTree_lattice_witness_finite,
  GraphicalZonotopes.HasPlaneDrawing.triangle_apex_separated,
  GraphicalZonotopes.TetrahedronComponents.maximumDimension_eq,
  GraphicalZonotopes.TetrahedronComponents.adj_iff_shared_triangle,
  GraphicalZonotopes.boundaryTriangles_after_attachment,
  Graph.IsArcK5.elim,
  GraphicalZonotopes.paper_corollary_5_2,
  GraphicalZonotopes.full_generalized_permutahedron_triangle_separators,
  GraphicalZonotopes.unit_lattice_active_classification_finite,
  GraphicalZonotopes.HasPlaneStraightLineDrawing.hasPlaneDrawing,
  GraphicalZonotopes.PathDrawing.path_hasPlaneDrawing,
  GraphicalZonotopes.IsPartialThreeTree.incidence_isAcyclic,
  GraphicalZonotopes.PolynomialWeights.minWeight_mul,
  GraphicalZonotopes.PolynomialWeights.maxWeight_mul,
  GraphicalZonotopes.BookSpectrum.prescribed_coordinate_criterion,
  GraphicalZonotopes.BookSpectrum.lattice_dimension_spectrum,
  GraphicalZonotopes.BookSpectrum.positive_dimension_spectrum,
  GraphicalZonotopes.Polyhedral.minimal_face_tight_kernel,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_span,
  GraphicalZonotopes.Polyhedral.extremeRay_iff_minimal_face_finrank,
  GraphicalZonotopes.Separator.positive_response_gluing_minimal_face_finite,
  GraphicalZonotopes.NewtonGeometry.newton_mul_of_basePolytope,
  GraphicalZonotopes.NewtonGeometry.irreducible_of_newton_base_extreme_unit_slack,
  GraphicalZonotopes.NewtonGeometry.corollary_A_3_absoluteIrreducible
]
