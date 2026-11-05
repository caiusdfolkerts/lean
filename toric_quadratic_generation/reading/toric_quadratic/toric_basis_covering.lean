module
public import PaperVerification.ToricGramBalance
public import PaperVerification.ToricLatticeCovering
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
@[expose] public section
/-!
# Covering by averaged basis boxes

This file connects the Gram balancing construction to the actual Euclidean
covering statement. Closed additive subgroups suffice for the geometric proof;
full lattices are a special case.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators InnerProductSpace
open Filter Topology

variable {d n : ℕ}

def matrixColumn (V : Matrix (Fin d) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => V i j)

/-- Nonvanishing of a maximal minor is exactly linear independence of the
selected vectors in the actual Euclidean ambient space. -/
lemma column_minor_ne_zero_iff_linearIndependent
    (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) (hs : s.card = d) :
    (PaperVerification.CauchyBinet.colsSubmatrix V s hs).det ≠ 0 ↔
      LinearIndependent ℝ (fun i => matrixColumn V (s.orderEmbOfFin hs i)) := by
  let e : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
    WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  have he : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hmap := e.toLinearMap.linearIndependent_iff
    (v := fun i => matrixColumn V (s.orderEmbOfFin hs i)) he
  change LinearIndependent ℝ (PaperVerification.CauchyBinet.colsSubmatrix V s hs).col ↔
    LinearIndependent ℝ (fun i => matrixColumn V (s.orderEmbOfFin hs i)) at hmap
  rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hmap
  exact hmap

/-- The maximal-minor predicate used in `ColumnBasis` is equivalent to the
existence of a genuine real vector-space basis with those selected columns. -/
lemma column_minor_ne_zero_iff_basis
    (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) (hs : s.card = d) :
    (PaperVerification.CauchyBinet.colsSubmatrix V s hs).det ≠ 0 ↔
      ∃ b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
        ∀ i, b i = matrixColumn V (s.orderEmbOfFin hs i) := by
  rw [column_minor_ne_zero_iff_linearIndependent]
  constructor
  · intro hli
    let b := basisOfLinearIndependentOfCardEqFinrank'
      (fun i => matrixColumn V (s.orderEmbOfFin hs i)) hli (by simp)
    refine ⟨b, ?_⟩
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)) i
  · rintro ⟨b, hb⟩
    have heq : (fun i => matrixColumn V (s.orderEmbOfFin hs i)) = fun i => b i :=
      funext (fun i => (hb i).symm)
    rw [heq]
    exact b.linearIndependent

def matrixOperator (A : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  A.toEuclideanLin.toContinuousLinearMap

lemma matrixOperator_apply (A : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    matrixOperator A x = WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl

lemma euclidean_inner_eq_dot (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫_ℝ = x.ofLp ⬝ᵥ y.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma matrixOperator_positive (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    ∀ x ≠ 0, 0 < quadraticValue (matrixOperator A) x := by
  intro x hx
  have hx' : x.ofLp ≠ 0 := by
    intro h
    apply hx
    exact WithLp.ofLp_injective 2 h
  simpa [quadraticValue, matrixOperator_apply, euclidean_inner_eq_dot] using
    hA.dotProduct_mulVec_pos hx'

lemma matrixOperator_symmetric (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    ∀ x y : EuclideanSpace ℝ (Fin d),
      ⟪x, matrixOperator A y⟫_ℝ = ⟪y, matrixOperator A x⟫_ℝ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  intro x y
  change ⟪x, A.toEuclideanLin y⟫_ℝ = ⟪y, A.toEuclideanLin x⟫_ℝ
  rw [← hs x y]
  exact real_inner_comm y (A.toEuclideanLin x)

lemma gram_inverse_frame (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (hunit : IsUnit (weightedGram V a).det)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∑ j, (a j * ⟪matrixColumn V j, matrixOperator (weightedGram V a)⁻¹ y⟫_ℝ) •
      matrixColumn V j = y := by
  let z : Fin d → ℝ := (weightedGram V a)⁻¹ *ᵥ y.ofLp
  have hfactor : weightedGram V a *ᵥ z =
      V *ᵥ (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z)) := by
    simp only [Matrix.mulVec_mulVec, weightedGram, Matrix.mul_assoc]
  have hcancel : weightedGram V a *ᵥ z = y.ofLp := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  apply PiLp.ext
  intro i
  rw [euclidean_sum_apply]
  calc
    (∑ j, ((a j * ⟪matrixColumn V j,
        matrixOperator (weightedGram V a)⁻¹ y⟫_ℝ) • matrixColumn V j) i) =
        (V *ᵥ (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z))) i := by
      simp only [PiLp.smul_apply, smul_eq_mul, matrixColumn, PiLp.toLp_apply,
        euclidean_inner_eq_dot, matrixOperator_apply, WithLp.ofLp_toLp]
      change (∑ j, (a j * ((fun k => V k j) ⬝ᵥ z)) * V i j) =
        ∑ j, V i j * (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z)) j
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_diagonal]
      change a j * (∑ k, V k j * z k) * V i j =
        V i j * (a j * (∑ k, V k j * z k))
      ring
    _ = y i := by simpa only [← hfactor, hcancel]

/-- Covering for strictly positive combinations of all basis indicators. -/
theorem positive_basis_average_covering (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 < p B) (hpsum : ∑ B, p B = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) (basisBarycenter V p) := by
  obtain ⟨a, ha, hwidth⟩ := basisBarycenter_realized V p hp hpsum
  have hG := weightedGram_posDef V a ha
  have hQ := hG.inv
  have hunit : IsUnit (weightedGram V a).det :=
    isUnit_iff_ne_zero.mpr (weightedGram_det_pos V a ha).ne'
  obtain ⟨z, hz, herror⟩ := ellipsoidal_frame_covering Γ hclosed
    (matrixOperator (weightedGram V a)⁻¹)
    (matrixOperator_symmetric _ hQ.isHermitian)
    (matrixOperator_positive _ hQ) (matrixColumn V) hv a (fun j => (ha j).le)
    (gram_inverse_frame V a hunit) x
  refine ⟨z, hz, ?_⟩
  convert herror using 1
  congr 1
  funext j
  rw [hwidth]
  simp [quadraticValue, matrixColumn, matrixOperator_apply, euclidean_inner_eq_dot]

/-- The covering property passes to limits of uniformly bounded width vectors.
Only closedness of the additive subgroup is used in the limiting step. -/
theorem centeredZonotope_covering_limit {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (v : ι → E) (c : ι → ℝ) (cseq : ℕ → ι → ℝ)
    (hlim : ∀ j, Tendsto (fun k => cseq k j) atTop (𝓝 (c j)))
    (hbound : ∀ k j, cseq k j ≤ 1) (x : E)
    (hcover : ∀ k, ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (cseq k)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v c := by
  classical
  have hdata : ∀ k, ∃ t : ι → ℝ,
      (∀ j, |t j| ≤ cseq k j / 2) ∧ x - ∑ j, t j • v j ∈ Γ := by
    intro k
    obtain ⟨z, hz, t, ht, hsum⟩ := hcover k
    refine ⟨t, ht, ?_⟩
    rw [hsum]
    convert hz using 1 <;> congr 1 <;> abel
  choose t ht hΓ using hdata
  have htmem : ∀ k, t k ∈ Set.Icc (fun _ : ι => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
    intro k
    constructor <;> intro j
    · have h := (abs_le.mp (ht k j)).1
      have h' := hbound k j
      linarith
    · have h := (abs_le.mp (ht k j)).2
      have h' := hbound k j
      linarith
  obtain ⟨t₀, _, φ, hφ, htlim⟩ := isCompact_Icc.tendsto_subseq htmem
  have hcoord (j : ι) : Tendsto (fun k => t (φ k) j) atTop (𝓝 (t₀ j)) :=
    (continuous_apply j).continuousAt.tendsto.comp htlim
  have htbound : ∀ j, |t₀ j| ≤ c j / 2 := by
    intro j
    exact le_of_tendsto_of_tendsto' (hcoord j).abs
      ((hlim j).comp hφ.tendsto_atTop |>.div_const 2) (fun k => ht (φ k) j)
  have hcont : Continuous (fun u : ι → ℝ => x - ∑ j, u j • v j) :=
    continuous_const.sub <| continuous_finset_sum _
      (fun j _ => (continuous_apply j).smul continuous_const)
  have hΓ₀ : x - ∑ j, t₀ j • v j ∈ Γ :=
    hclosed.mem_of_tendsto (hcont.continuousAt.tendsto.comp htlim)
      (Eventually.of_forall (fun k => hΓ (φ k)))
  refine ⟨x - ∑ j, t₀ j • v j, hΓ₀, t₀, htbound, ?_⟩
  abel

lemma basisBarycenter_le_one (V : Matrix (Fin d) (Fin n) ℝ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 ≤ p B) (hpsum : ∑ B, p B = 1)
    (j : Fin n) : basisBarycenter V p j ≤ 1 := by
  rw [basisBarycenter_apply, ← hpsum]
  apply Finset.sum_le_sum
  intro B _
  split_ifs <;> simp [hp B]

/-- Covering for every convex combination of the basis indicators, including
all boundary points of the representable matroid base polytope. -/
theorem basis_average_covering (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 ≤ p B) (hpsum : ∑ B, p B = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) (basisBarycenter V p) := by
  let N : ℝ := Fintype.card (ColumnBasis V)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεle (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let pseq : ℕ → ColumnBasis V → ℝ :=
    fun k B => ε k * N⁻¹ + (1 - ε k) * p B
  have hpseq (k : ℕ) (B : ColumnBasis V) : 0 < pseq k B := by
    dsimp [pseq]
    exact add_pos_of_pos_of_nonneg (mul_pos (hεpos k) (inv_pos.mpr hN))
      (mul_nonneg (sub_nonneg.mpr (hεle k)) (hp B))
  have hsumseq (k : ℕ) : ∑ B, pseq k B = 1 := by
    simp only [pseq, Finset.sum_add_distrib, ← Finset.mul_sum, hpsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change ε k * (N * N⁻¹) + (1 - ε k) * 1 = 1
    rw [mul_inv_cancel₀ hN.ne']
    ring
  have hplim (B : ColumnBasis V) : Tendsto (fun k => pseq k B) atTop (𝓝 (p B)) := by
    simpa [pseq] using
      (hεlim.mul_const N⁻¹).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).mul_const (p B))
  refine centeredZonotope_covering_limit Γ hclosed (matrixColumn V) (basisBarycenter V p)
    (fun k => basisBarycenter V (pseq k)) ?_ ?_ x ?_
  · intro j
    simp only [basisBarycenter_apply]
    apply tendsto_finsetSum
    intro B _
    by_cases hj : j ∈ B.val
    · simpa [hj] using hplim B
    · simp only [hj, if_false]
      exact tendsto_const_nhds
  · intro k j
    exact basisBarycenter_le_one V (pseq k) (fun B => (hpseq k B).le) (hsumseq k) j
  · intro k
    exact positive_basis_average_covering V Γ hclosed hv (pseq k) (hpseq k) (hsumseq k) x

/-- Lemma 4.1, in standard Euclidean coordinates. The hypothesis on the widths
is membership in the actual convex hull of the incidence vectors of all
nonsingular maximal column subsets. The result includes boundary widths.

The subgroup assumption is weaker than the manuscript's full-lattice
assumption, while every direction must still belong to that subgroup. -/
theorem matroid_basis_polytope_covering (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (c : EuclideanSpace ℝ (Fin n))
    (hc : c ∈ convexHull ℝ (Set.range (basisIncidence V)))
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) c := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hc
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hc
  have hsne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hs
    simp [hs] at hsum
  obtain ⟨B, _⟩ := hsne
  letI : Nonempty (ColumnBasis V) := ⟨B⟩
  let p : ColumnBasis V → ℝ := fun B => if B ∈ s then w B else 0
  have hp : ∀ B, 0 ≤ p B := by
    intro B
    by_cases hB : B ∈ s
    · simpa [p, hB] using hw B hB
    · simp [p, hB]
  have hpsum : ∑ B, p B = 1 := by simpa [p, Finset.sum_ite_mem] using hsum
  have hpc : basisBarycenter V p = c := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
    simpa [basisBarycenter, p, ite_smul, Finset.sum_ite_mem] using hcomb
  simpa [hpc] using basis_average_covering V Γ hclosed hv p hp hpsum x

/-- The full-lattice formulation of Lemma 4.1. The final conclusion explicitly
states that the zonotope meets the coset represented by every ambient point. -/
theorem lattice_basis_polytope_covering (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (c : EuclideanSpace ℝ (Fin n))
    (hc : c ∈ convexHull ℝ (Set.range (basisIncidence V)))
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ y ∈ CenteredZonotope (matrixColumn V) c, y - x ∈ Γ := by
  letI : DiscreteTopology Γ.toAddSubgroup := inferInstanceAs (DiscreteTopology Γ)
  have hclosed : IsClosed (Γ.toAddSubgroup : Set (EuclideanSpace ℝ (Fin d))) :=
    AddSubgroup.isClosed_of_discreteTopology
  obtain ⟨z, hz, herror⟩ :=
    matroid_basis_polytope_covering V Γ.toAddSubgroup hclosed hv c hc x
  refine ⟨x - z, herror, ?_⟩
  convert Γ.neg_mem hz using 1 <;> congr 1 <;> abel

end PaperVerification.Toric
