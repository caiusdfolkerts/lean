module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part04
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.CauchyBinet

/-
  PaperVerification/CauchyBinet.lean

  Cauchy–Binet formula over a commutative ring (Sun arXiv:2609.04176v1 §4).
  Mathlib v4.32.2 has no Cauchy–Binet; proved from `det_apply'` / `det_mul`-style
  Leibniz expansion, vanishing on non-injective column maps, and partitioning
  injectives by image via `Finset.orderEmbOfFin`.
-/
set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

noncomputable section

namespace PaperVerification.CauchyBinet

open Matrix Finset Equiv
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

local notation "ε " σ:arg => ((Equiv.Perm.sign σ : ℤ) : R)

/-! ## Column / row minors via `orderEmbOfFin` -/

/-- Square column minor of an `m × n` matrix on an `m`-element column set. -/
def colsSubmatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  A.submatrix id (s.orderEmbOfFin hs)

/-- Square row minor of an `n × m` matrix on an `m`-element row set. -/
def rowsSubmatrix {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  B.submatrix (s.orderEmbOfFin hs) id

@[simp] theorem colsSubmatrix_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    colsSubmatrix A s hs i j = A i (s.orderEmbOfFin hs j) :=
  rfl

@[simp] theorem rowsSubmatrix_apply {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    rowsSubmatrix B s hs i j = B (s.orderEmbOfFin hs i) j :=
  rfl

/-! ## CB0: `m = 0` and `m = 1` -/

theorem det_mul_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det = 1 :=
  det_fin_zero

theorem det_mul_eq_sum_minors_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 0,
        if hs : s.card = 0 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  simp [det_fin_zero, colsSubmatrix, rowsSubmatrix, powersetCard_zero]

theorem det_mul_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det = ∑ k : Fin n, A 0 k * B k 0 := by
  rw [det_fin_one, Matrix.mul_apply]

theorem det_mul_eq_sum_minors_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 1,
        if hs : s.card = 1 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [det_mul_fin_one]
  have hmap :
      (univ : Finset (Fin n)).powersetCard 1 =
        (univ : Finset (Fin n)).map ⟨fun k => {k}, singleton_injective⟩ :=
    powersetCard_one _
  rw [hmap, sum_map]
  refine Fintype.sum_congr _ _ fun k => ?_
  have hs : ({k} : Finset (Fin n)).card = 1 := card_singleton k
  simp only [Function.Embedding.coeFn_mk, dif_pos hs, det_fin_one,
    colsSubmatrix_apply, rowsSubmatrix_apply, orderEmbOfFin_singleton]

/-! ## Helpers: expansion, vanishing, permutations of a column image -/

/-- Leibniz expansion of `det(A * B)` as a sum over column-selection maps. -/
theorem det_mul_eq_sum_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i : Fin m, B (p i) i := by
  calc
    (A * B).det
        = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i) * B (p i) i := by
          simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
            Fintype.piFinset_univ]
          rw [sum_comm]
    _ = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m),
              (ε σ * ∏ i, A (σ i) (p i)) * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => sum_congr rfl fun σ _ => ?_
          rw [prod_mul_distrib, mul_assoc]
    _ = ∑ p : Fin m → Fin n,
            (∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i)) *
              ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          exact (Finset.sum_mul _ _ _).symm
    _ = ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          congr 1
          simpa [submatrix_apply] using (det_apply' (A.submatrix id p)).symm

/-- Non-injective column selection forces a repeated column, hence determinant zero. -/
theorem det_submatrix_eq_zero_of_not_injective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) {p : Fin m → Fin n}
    (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  simp only [Function.Injective] at hp
  push Not at hp
  obtain ⟨i, j, hpij, hij⟩ := hp
  exact det_zero_of_column_eq hij fun k => by simp [hpij]

/-- Only injective column maps contribute to the expansion. -/
theorem det_mul_eq_sum_injective_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n,
        if Function.Injective p then
          (A.submatrix id p).det * ∏ i : Fin m, B (p i) i
        else 0 := by
  rw [det_mul_eq_sum_colMap]
  refine sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · rw [det_submatrix_eq_zero_of_not_injective A hp, zero_mul]

/-- The unique permutation realizing an injective map as `orderEmbOfFin ∘ τ`. -/
def permOfImage {m n : ℕ} (p : Fin m → Fin n) (hp : Function.Injective p)
    (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) : Perm (Fin m) :=
  let emb : Fin m → Fin n := s.orderEmbOfFin hs
  have hrangep : Set.range p = (s : Set (Fin n)) := by
    rw [← him, coe_image, coe_univ, Set.image_univ]
  have hrangee : Set.range emb = (s : Set (Fin n)) := range_orderEmbOfFin s hs
  (Equiv.ofInjective p hp).trans <|
    (Set.equivOfEq (hrangep.trans hrangee.symm)).trans
      (Equiv.ofInjective emb (s.orderEmbOfFin hs).injective).symm

theorem apply_orderEmb_permOfImage {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) (i : Fin m) :
    s.orderEmbOfFin hs (permOfImage p hp s hs him i) = p i := by
  dsimp [permOfImage]
  exact Equiv.apply_ofInjective_symm (s.orderEmbOfFin hs).injective _

theorem permOfImage_comp {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) :
    (s.orderEmbOfFin hs : Fin m → Fin n) ∘ permOfImage p hp s hs him = p :=
  funext fun i => apply_orderEmb_permOfImage p hp s hs him i

/-- Image of an injective `Fin m → Fin n` is an `m`-element subset of `univ`. -/
theorem image_mem_powersetCard {m n : ℕ} {p : Fin m → Fin n}
    (hp : Function.Injective p) :
    image p univ ∈ (univ : Finset (Fin n)).powersetCard m := by
  refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
  rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]

/-- `orderEmbOfFin` of the full universe is the identity map. -/
theorem orderEmbOfFin_univ_eq_id (m : ℕ) :
    ((univ : Finset (Fin m)).orderEmbOfFin (by simp [card_univ, Fintype.card_fin]) :
      Fin m → Fin m) =
      id := by
  have h :
      (id : Fin m → Fin m) =
        (univ : Finset (Fin m)).orderEmbOfFin
          (by simp [card_univ, Fintype.card_fin]) :=
    orderEmbOfFin_unique (s := (univ : Finset (Fin m)))
      (by simp [card_univ, Fintype.card_fin]) (fun _ => mem_univ _)
      (strictMono_id : StrictMono (id : Fin m → Fin m))
  exact h.symm

/-! ## CB1: square case `m = n` -/

theorem powersetCard_univ_self (m : ℕ) :
    (univ : Finset (Fin m)).powersetCard m = {univ} := by
  ext s
  simp only [mem_powersetCard, mem_singleton, subset_univ, true_and]
  exact ⟨fun hs => eq_univ_of_card _ (hs.trans (by simp [card_univ, Fintype.card_fin])),
    fun hs => hs ▸ by simp [card_univ, Fintype.card_fin]⟩

theorem colsSubmatrix_univ {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    colsSubmatrix A univ (by simp [card_univ, Fintype.card_fin]) = A := by
  ext i j
  simp [colsSubmatrix, orderEmbOfFin_univ_eq_id]

theorem rowsSubmatrix_univ {m : ℕ} (B : Matrix (Fin m) (Fin m) R) :
    rowsSubmatrix B univ (by simp [card_univ, Fintype.card_fin]) = B := by
  ext i j
  simp [rowsSubmatrix, orderEmbOfFin_univ_eq_id]

/-- Square Cauchy–Binet collapses to `Matrix.det_mul`. -/
theorem det_mul_eq_sum_minors_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin m)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [powersetCard_univ_self, sum_singleton]
  have hs : (univ : Finset (Fin m)).card = m := by simp [card_univ, Fintype.card_fin]
  simp only [dif_pos hs, colsSubmatrix_univ, rowsSubmatrix_univ, Matrix.det_mul]

/-! ## Fiber of a fixed image: sum over permutations -/

theorem det_submatrix_comp_perm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (emb : Fin m → Fin n) (τ : Perm (Fin m)) :
    (A.submatrix id (emb ∘ τ)).det = ε τ * (A.submatrix id emb).det := by
  have h : A.submatrix id (emb ∘ τ) = (A.submatrix id emb).submatrix id τ := by
    ext; simp [Function.comp_apply]
  rw [h, det_permute']

theorem sum_fiber_eq_det_mul_det {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ τ : Perm (Fin m),
        (A.submatrix id ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ)).det *
          (∏ i : Fin m, B (((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) i) i)) =
      (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det := by
  let emb : Fin m → Fin n := fun i => s.orderEmbOfFin hs i
  change ∑ τ : Perm (Fin m),
      (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
    (A.submatrix id emb).det * (B.submatrix emb id).det
  have hsum :
      ∑ τ : Perm (Fin m),
          (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
        ∑ τ : Perm (Fin m),
          (A.submatrix id emb).det * (ε τ * (∏ i : Fin m, B (emb (τ i)) i)) := by
    refine sum_congr rfl fun τ _ => ?_
    rw [det_submatrix_comp_perm A emb τ]
    ring
  rw [hsum, ← Finset.mul_sum]
  congr 1
  exact (det_apply' (B.submatrix emb id)).symm

/-- Enumerate injective maps with a fixed image by permutations of `orderEmbOfFin`. -/
theorem sum_injective_with_image {m n : ℕ}
    (f : (Fin m → Fin n) → R) (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ p : Fin m → Fin n,
        if Function.Injective p ∧ image p univ = s then f p else 0) =
      ∑ τ : Perm (Fin m), f ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) := by
  classical
  let emb : Fin m → Fin n := (s.orderEmbOfFin hs : Fin m → Fin n)
  have hembinj : Function.Injective emb := (s.orderEmbOfFin hs).injective
  have himemb : image emb univ = s := image_orderEmbOfFin_univ s hs
  have hfilter :
      ∑ τ : Perm (Fin m), f (emb ∘ τ) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f := by
    refine sum_bij (fun τ _ => emb ∘ (τ : Fin m → Fin m)) ?mem ?inj ?surj ?eq
    · intro τ _
      refine mem_filter.mpr ⟨mem_univ _, hembinj.comp τ.injective, ?_⟩
      have himτ : image (τ : Fin m → Fin m) univ = univ := by
        rw [← coe_inj, coe_image, coe_univ, Set.image_univ, τ.surjective.range_eq]
      rw [image_comp, himτ, himemb]
    · intro τ₁ _ τ₂ _ h
      exact Equiv.Perm.ext fun i => hembinj (congrFun h i)
    · intro p hp
      obtain ⟨_, hpinj, him⟩ := mem_filter.mp hp
      refine ⟨permOfImage p hpinj s hs him, mem_univ _, ?_⟩
      -- `emb ∘ permOfImage = p`
      simpa [emb] using permOfImage_comp p hpinj s hs him
    · intro τ _; rfl
  have hsplit :
      (∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f :=
    (sum_filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
      (f := f)).symm
  exact hsplit.trans hfilter.symm

/-! ## CB2: general Cauchy–Binet -/

/-- Group injective column maps by their image in `powersetCard m`. -/
theorem sum_injective_eq_sum_powerset {m n : ℕ} (f : (Fin m → Fin n) → R) :
    (∑ p : Fin m → Fin n, if Function.Injective p then f p else 0) =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        ∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0 := by
  classical
  have hswap :
      (∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
          ∑ p : Fin m → Fin n,
            if Function.Injective p ∧ image p univ = s then f p else 0) =
        ∑ p : Fin m → Fin n,
          ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
            if Function.Injective p ∧ image p univ = s then f p else 0 :=
    sum_comm
  rw [hswap]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : Function.Injective p
  · have him : image p univ ∈ (univ : Finset (Fin n)).powersetCard m :=
      image_mem_powersetCard hp
    rw [sum_eq_single (image p univ)]
    · simp [hp]
    · intro s hs hne
      simp only [hp, true_and]
      split_ifs with h
      · exact (hne h.symm).elim
      · rfl
    · intro hnot
      exact (hnot him).elim
  · simp only [hp, false_and, ite_false, sum_const_zero]

/-- **Cauchy–Binet.** For `A : m × n` and `B : n × m` over a commutative ring,
`det(A * B)` equals the sum of products of complementary minors over all
`m`-element subsets of `Fin n`. -/
theorem det_mul_eq_sum_minors {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  classical
  rw [det_mul_eq_sum_injective_colMap]
  have hgroup :=
    sum_injective_eq_sum_powerset
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
  rw [hgroup]
  refine sum_congr rfl fun s hs => ?_
  have hcard : s.card = m := (mem_powersetCard.mp hs).2
  simp only [dif_pos hcard]
  have hfiber :=
    sum_injective_with_image
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
      s hcard
  rw [hfiber, sum_fiber_eq_det_mul_det A B s hcard]

/-! ## CB3: corollaries -/

/-- If `m > n`, there are no `m`-column subsets, so `det(A * B) = 0`. -/
theorem det_mul_eq_zero_of_card_lt {m n : ℕ} (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  have hempty : (univ : Finset (Fin n)).powersetCard m = ∅ := by
    rw [powersetCard_eq_empty]
    simpa [card_univ, Fintype.card_fin] using hmn
  simp [hempty]

/-- Square re-export of `Matrix.det_mul` through the Cauchy–Binet packaging. -/
theorem det_mul_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

end PaperVerification.CauchyBinet
end
-- END PaperVerification.CauchyBinet
end

section
-- BEGIN PaperVerification.ToricGramDeterminant
/-!
# Gram determinants and basis marginals

These identities provide the algebraic part of the lattice-covering lemma.
The leverage identity is obtained by doubling one column weight and applying
the rank-one determinant formula; no differentiation of a matrix inverse or
an unproved log-determinant identity is required.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- The positive weighted Gram matrix of a column configuration. -/
def weightedGram (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := V * Matrix.diagonal a * V.transpose

/-- The squared maximal minor, extended by zero to subsets of other sizes. -/
def squaredMinor (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) : ℝ :=
  if hs : s.card = d then (colsSubmatrix V s hs).det ^ 2 else 0

lemma squaredMinor_nonneg (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 ≤ squaredMinor V s := by
  unfold squaredMinor
  split_ifs <;> positivity

lemma prod_orderEmbOfFin (s : Finset (Fin n)) (hs : s.card = d) (a : Fin n → ℝ) :
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) = ∏ j ∈ s, a j := by
  calc
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) =
        ∏ j ∈ Finset.univ.map (s.orderEmbOfFin hs).toEmbedding, a j := by
          rw [Finset.prod_map]
          rfl
    _ = _ := by rw [Finset.map_orderEmbOfFin_univ]

lemma weightedGram_apply (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ)
    (i j : Fin d) : weightedGram V a i j = ∑ k, a k * V i k * V j k := by
  rw [weightedGram, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The weighted Cauchy–Binet expansion, with all zero minors retained. -/
theorem weightedGram_det (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ s : Finset (Fin n), squaredMinor V s * ∏ j ∈ s, a j := by
  classical
  rw [weightedGram, det_mul_eq_sum_minors]
  have hminor (s : Finset (Fin n)) (hs : s.card = d) :
      (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
        (rowsSubmatrix V.transpose s hs).det =
          squaredMinor V s * ∏ j ∈ s, a j := by
    have hc : colsSubmatrix (V * Matrix.diagonal a) s hs =
        colsSubmatrix V s hs *
          Matrix.diagonal (fun i => a (s.orderEmbOfFin hs i)) := by
      ext i j
      simp [colsSubmatrix, Matrix.mul_diagonal]
    have hr : rowsSubmatrix V.transpose s hs = (colsSubmatrix V s hs).transpose := by
      ext i j
      rfl
    rw [hc, hr, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
      prod_orderEmbOfFin, squaredMinor, dif_pos hs]
    ring
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        if hs : s.card = d then
          (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
            (rowsSubmatrix V.transpose s hs).det else 0) =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
          squaredMinor V s * ∏ j ∈ s, a j := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcard := (Finset.mem_powersetCard.mp hs).2
      rw [dif_pos hcard]
      exact hminor s hcard
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      have hcard : s.card ≠ d := by
        intro heq
        exact hs (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heq⟩)
      simp [squaredMinor, hcard]

lemma prod_update_double (a : Fin n → ℝ) (j : Fin n) (s : Finset (Fin n)) :
    (∏ k ∈ s, Function.update a j (2 * a j) k) =
      (∏ k ∈ s, a k) + if j ∈ s then ∏ k ∈ s, a k else 0 := by
  by_cases hj : j ∈ s
  · rw [Finset.prod_update_of_mem hj, if_pos hj,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj a]
    ring
  · rw [Finset.prod_update_of_notMem hj, if_neg hj, add_zero]

/-- Doubling a column weight adds exactly the basis mass of subsets containing it. -/
theorem weightedGram_det_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    (weightedGram V (Function.update a j (2 * a j))).det =
      (weightedGram V a).det +
        ∑ s : Finset (Fin n),
          if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  rw [weightedGram_det, weightedGram_det, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [prod_update_double]
  by_cases hj : j ∈ s <;> simp [hj, mul_add]

lemma weightedGram_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    weightedGram V (Function.update a j (2 * a j)) = weightedGram V a +
      Matrix.replicateCol Unit (a j • fun i => V i j) *
        Matrix.replicateRow Unit (fun i => V i j) := by
  ext i k
  have hterm (r : Fin n) :
      Function.update a j (2 * a j) r * V i r * V k r =
        a r * V i r * V k r + if r = j then a j * V i j * V k j else 0 := by
    by_cases hr : r = j
    · subst r
      simp only [Function.update_self, if_true]
      ring
    · simp [Function.update_of_ne hr, hr]
  simp only [weightedGram_apply, hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_unique, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Pi.smul_apply, smul_eq_mul]

/-- The basis-marginal identity used to match zonotope widths to an inverse
weighted Gram matrix. The only nondegeneracy hypothesis is invertibility. -/
theorem weightedGram_basis_marginal (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (hunit : IsUnit (weightedGram V a).det) (j : Fin n) :
    (weightedGram V a).det *
        (a j * ((fun i => V i j) ⬝ᵥ
          ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j)))) =
      ∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  have hdet := weightedGram_det_update_double V a j
  rw [weightedGram_update_double,
    Matrix.det_add_replicateCol_mul_replicateRow hunit] at hdet
  rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
    Matrix.det_unique (n := Unit)] at hdet
  simp only [Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hdet
  nlinarith

end PaperVerification.Toric
end
-- END PaperVerification.ToricGramDeterminant
end

section
-- BEGIN PaperVerification.ToricGramBalance
/-!
# Realizing matroid-base weights by a weighted Gram matrix

The basis set below consists precisely of nonsingular maximal column minors.
Every strictly positive probability distribution on these bases determines
widths realized by the inverse Gram matrix leverage formula.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators InnerProductSpace
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- Unordered vector-space bases among the columns of a matrix. -/
def ColumnBasis (V : Matrix (Fin d) (Fin n) ℝ) :=
  {s : Finset (Fin n) // 0 < squaredMinor V s}

instance (V : Matrix (Fin d) (Fin n) ℝ) : Fintype (ColumnBasis V) := by
  classical
  unfold ColumnBasis
  infer_instance

lemma squaredMinor_pos_iff (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 < squaredMinor V s ↔
      ∃ hs : s.card = d, (colsSubmatrix V s hs).det ≠ 0 := by
  by_cases hs : s.card = d
  · simp [squaredMinor, hs, sq_pos_iff]
  · simp [squaredMinor, hs]

/-- Incidence vector of a column basis in the real Euclidean coordinate space. -/
def basisIncidence (V : Matrix (Fin d) (Fin n) ℝ) (B : ColumnBasis V) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => if j ∈ B.val then 1 else 0)

@[simp] lemma basisIncidence_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (j : Fin n) :
    basisIncidence V B j = if j ∈ B.val then 1 else 0 := rfl

/-- The width vector associated with a probability distribution on bases. -/
def basisBarycenter (V : Matrix (Fin d) (Fin n) ℝ) (p : ColumnBasis V → ℝ) :
    EuclideanSpace ℝ (Fin n) := ∑ B, p B • basisIncidence V B

lemma euclidean_sum_apply {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j := by
  change ((∑ i, f i).ofLp) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

lemma basisBarycenter_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (p : ColumnBasis V → ℝ) (j : Fin n) :
    basisBarycenter V p j = ∑ B, if j ∈ B.val then p B else 0 := by
  rw [basisBarycenter, euclidean_sum_apply]
  apply Finset.sum_congr rfl
  intro B _
  simp [basisIncidence]

lemma basisIncidence_exp_inner (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp ⟪basisIncidence V B, x⟫_ℝ = ∏ j ∈ B.val, Real.exp (x j) := by
  have hi : ⟪basisIncidence V B, x⟫_ℝ = ∑ j ∈ B.val, x j := by
    simp [basisIncidence, PiLp.inner_apply, Finset.sum_ite_mem, mul_comm]
  rw [hi, Real.exp_sum]

/-- Remove zero terms from a sum indexed by all column subsets. -/
lemma sum_columnBasis_eq (V : Matrix (Fin d) (Fin n) ℝ)
    (f : Finset (Fin n) → ℝ)
    (hf : ∀ s, squaredMinor V s = 0 → f s = 0) :
    (∑ B : ColumnBasis V, f B.val) = ∑ s, f s := by
  classical
  calc
    (∑ B : ColumnBasis V, f B.val) =
        ∑ s ∈ Finset.univ.filter (fun s => 0 < squaredMinor V s), f s := by
      exact (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s _ hs
      have hnot : ¬ 0 < squaredMinor V s := by simpa using hs
      exact hf s (le_antisymm (le_of_not_gt hnot) (squaredMinor_nonneg V s))

lemma weightedGram_det_eq_basis_sum (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ B : ColumnBasis V, squaredMinor V B.val * ∏ j ∈ B.val, a j := by
  rw [weightedGram_det]
  exact (sum_columnBasis_eq V _ (by intro s hs; simp [hs])).symm

lemma weightedGram_det_pos (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    0 < (weightedGram V a).det := by
  rw [weightedGram_det_eq_basis_sum]
  exact Finset.sum_pos
    (fun B _ => mul_pos B.property (Finset.prod_pos (fun j _ => ha j)))
    Finset.univ_nonempty

lemma weightedGram_posDef (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (weightedGram V a).PosDef := by
  have hpsd : (weightedGram V a).PosSemidef := by
    have hdiag : (Matrix.diagonal a).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun j => (ha j).le)
    simpa [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same V
  exact (hpsd.posDef_iff_det_ne_zero).mpr (weightedGram_det_pos V a ha).ne'

/-- Every positive convex combination of basis indicators is realized by a
positive column weighting and its inverse Gram matrix. -/
theorem basisBarycenter_realized (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 < p B) (hpsum : ∑ B, p B = 1) :
    ∃ a : Fin n → ℝ, (∀ j, 0 < a j) ∧
      ∀ j, basisBarycenter V p j =
        a j * ((fun i => V i j) ⬝ᵥ ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j))) := by
  obtain ⟨x, hx⟩ := finite_exponential_barycenter
    (basisIncidence V) p hp hpsum (fun B => squaredMinor V B.val)
    (fun B => B.property)
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * Real.exp ⟪basisIncidence V B, x⟫_ℝ) •
      (basisIncidence V B - basisBarycenter V p)) = 0 at hx
  let a : Fin n → ℝ := fun j => Real.exp (x j)
  have ha : ∀ j, 0 < a j := fun j => Real.exp_pos _
  have hdet : 0 < (weightedGram V a).det := weightedGram_det_pos V a ha
  refine ⟨a, ha, ?_⟩
  intro j
  have hj := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) hx
  simp only [euclidean_sum_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply,
    basisIncidence_exp_inner, basisIncidence_apply, smul_eq_mul] at hj
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
      ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) = 0 at hj
  have hmass :
      (∑ B : ColumnBasis V,
        if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    have hsplit :
        (∑ B : ColumnBasis V,
          (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
            ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) =
          (∑ B : ColumnBasis V,
            if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) -
            (weightedGram V a).det * basisBarycenter V p j := by
      rw [weightedGram_det_eq_basis_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro B _
      split_ifs <;> ring
    rw [hsplit] at hj
    exact sub_eq_zero.mp hj
  have hsum :
      (∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    rw [← sum_columnBasis_eq V _ (by intro s hs; simp [hs])]
    exact hmass
  have hmarg := weightedGram_basis_marginal V a (isUnit_iff_ne_zero.mpr hdet.ne') j
  rw [hsum] at hmarg
  exact (mul_left_cancel₀ hdet.ne' hmarg).symm

end PaperVerification.Toric
end
-- END PaperVerification.ToricGramBalance
end

section
-- BEGIN PaperVerification.ToricLatticeCovering
/-!
# The nearest-point step in the lattice-covering argument

This module proves the geometric part of Lemma 4.1. The existence of a
balancing inner product for every point of the matroid base polytope is a
separate analytic theorem, not an assumption silently discharged here.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace

/-- A centered zonotope with half-widths `c i / 2` in directions `v i`. -/
def CenteredZonotope {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (v : ι → E) (c : ι → ℝ) : Set E :=
  {y | ∃ t : ι → ℝ, (∀ i, |t i| ≤ c i / 2) ∧ ∑ i, t i • v i = y}

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every Euclidean nearest-point error satisfies all neighboring-point inequalities. -/
theorem nearest_error_inner_bound (Γ : AddSubgroup E) (x z : E)
    (hz : z ∈ Γ) (hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖)
    (v : E) (hv : v ∈ Γ) :
    |⟪v, x - z⟫_ℝ| ≤ ‖v‖ ^ 2 / 2 := by
  have hminus : ‖x - z‖ ≤ ‖(x - z) - v‖ := by
    have h := hnearest (z + v) (Γ.add_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hplus : ‖x - z‖ ≤ ‖(x - z) + v‖ := by
    have h := hnearest (z - v) (Γ.sub_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hminus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) - v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hminus
  have hplus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) + v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hplus
  rw [norm_sub_sq_real (x - z) v] at hminus2
  rw [norm_add_sq_real (x - z) v] at hplus2
  rw [real_inner_comm (x - z) v]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A weighted tight frame gives a covering zonotope for every closed additive
subgroup containing its vectors, in a proper real inner-product space.

Applied after the log-determinant balancing step, this is exactly the
nearest-lattice-point argument in Lemma 4.1. No lattice-covering conclusion
is included among the hypotheses.
-/
theorem balanced_frame_covering [ProperSpace E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * ‖v i‖ ^ 2) := by
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist ⟨0, Γ.zero_mem⟩ x
  have hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [← dist_eq_norm, ← dist_eq_norm, ← hdist]
    exact Metric.infDist_le_dist_of_mem hy
  refine ⟨z, hz, fun i => w i * ⟪v i, x - z⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have h := nearest_error_inner_bound Γ x z hz hnearest (v i) (hv i)
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left h (hw i)
  nlinarith

/-- The quadratic norm-square determined by a real continuous linear operator. -/
def quadraticValue (T : E →L[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫_ℝ

lemma quadraticValue_continuous (T : E →L[ℝ] E) : Continuous (quadraticValue T) :=
  continuous_id.inner T.continuous

lemma quadraticValue_smul (T : E →L[ℝ] E) (x : E) (a : ℝ) :
    quadraticValue T (a • x) = a ^ 2 * quadraticValue T x := by
  simp only [quadraticValue, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Positive definite quadratic forms have a uniform norm-square lower bound. -/
theorem quadraticValue_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) :
    ∃ ε > 0, ∀ x, ε * ‖x‖ ^ 2 ≤ quadraticValue T x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (quadraticValue_continuous T).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨quadraticValue T u, hpos u hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, quadraticValue]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : quadraticValue T u ≤ quadraticValue T (‖x‖⁻¹ • x) := hmin hxunit
  rw [quadraticValue_smul] at h
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
  simpa [mul_assoc, mul_comm, mul_left_comm, ← mul_pow, hnorm.ne'] using hmul

/-- A positive definite quadratic distance attains its minimum on every closed
additive subgroup. Discreteness and full rank are not needed for this step. -/
theorem exists_quadratic_nearest [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) (x : E) :
    ∃ z ∈ Γ, ∀ y ∈ Γ, quadraticValue T (x - z) ≤ quadraticValue T (x - y) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    refine ⟨0, Γ.zero_mem, ?_⟩
    intro y _
    exact le_of_eq (congrArg (fun z => quadraticValue T (x - z)) (Subsingleton.elim 0 y))
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := quadraticValue_lower_bound T hpos
  have hnorm : Filter.Tendsto (fun y : E => ‖x - y‖) (Filter.cocompact E)
      Filter.atTop := by
    simpa only [Function.comp_def, ← Metric.cobounded_eq_cocompact] using
      tendsto_norm_cobounded_atTop.comp (tendsto_const_sub_cobounded x)
  have hpow : Filter.Tendsto (fun y : E => ‖x - y‖ ^ 2) (Filter.cocompact E)
      Filter.atTop := (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnorm
  have hlim : Filter.Tendsto (fun y : E => quadraticValue T (x - y))
      (Filter.cocompact E) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun y => hbound (x - y))
      (Filter.Tendsto.const_mul_atTop hε hpow)
  have hcont : Continuous (fun y : E => quadraticValue T (x - y)) :=
    (quadraticValue_continuous T).comp (continuous_const.sub continuous_id)
  have hev : ∀ᶠ y in Filter.cocompact E,
      quadraticValue T (x - 0) ≤ quadraticValue T (x - y) :=
    hlim.eventually (Filter.eventually_ge_atTop _)
  obtain ⟨z, hz, hmin⟩ := hcont.continuousOn.exists_isMinOn' hclosed Γ.zero_mem
    (hev.filter_mono inf_le_left)
  exact ⟨z, hz, fun y hy => hmin hy⟩

/-- Symmetric quadratic expansion. -/
lemma quadraticValue_add (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a + b) =
      quadraticValue T a + 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_add, inner_add_left, inner_add_right]
  rw [hsym a b]
  ring

lemma quadraticValue_sub (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a - b) =
      quadraticValue T a - 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_sub, inner_sub_left, inner_sub_right]
  rw [hsym a b]
  ring

/-- The full ellipsoidal nearest-point step used in Lemma 4.1. -/
theorem ellipsoidal_frame_covering [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ)
    (hpos : ∀ x ≠ 0, 0 < quadraticValue T x)
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, T y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * quadraticValue T (v i)) := by
  obtain ⟨z, hz, hnearest⟩ := exists_quadratic_nearest Γ hclosed T hpos x
  refine ⟨z, hz, fun i => w i * ⟪v i, T (x - z)⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have hminus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) - v i) := by
    have h := hnearest (z + v i) (Γ.add_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  have hplus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) + v i) := by
    have h := hnearest (z - v i) (Γ.sub_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  rw [quadraticValue_sub T hsym (x - z) (v i)] at hminus
  rw [quadraticValue_add T hsym (x - z) (v i)] at hplus
  have habs : |⟪v i, T (x - z)⟫_ℝ| ≤ quadraticValue T (v i) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left habs (hw i)
  nlinarith

end PaperVerification.Toric
end
-- END PaperVerification.ToricLatticeCovering
end

section
-- BEGIN PaperVerification.ToricBasisCovering
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
    continuous_const.sub <| continuous_finsetSum _
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
end
-- END PaperVerification.ToricBasisCovering
end

section
-- BEGIN PaperVerification.ToricBoxAverages
/-!
# Matched box averages and lattice decompositions

This is equation (7) of the toric manuscript, with the centered zonotope and
all convex-combination hypotheses made explicit. Different boxes may use
unrelated bases of the common ambient real vector space.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J ι E : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centered unit box in a selected subset of the vector configuration. -/
def SubsetBox (v : ι → E) (s : Finset ι) : Set E :=
  CenteredZonotope v (fun j => if j ∈ s then 1 else 0)

/-- Total occurrence weight of each vector in a family of selected subsets. -/
def averagedWidths (s : J → Finset ι) (p : J → ℝ) (j : ι) : ℝ :=
  ∑ B, if j ∈ s B then p B else 0

lemma averagedWidths_nonneg (s : J → Finset ι) (p : J → ℝ) (hp : ∀ B, 0 ≤ p B)
    (j : ι) : 0 ≤ averagedWidths s p j := by
  apply Finset.sum_nonneg
  intro B _
  split_ifs <;> simp [hp B]

lemma neg_mem_centeredZonotope (v : ι → E) (c : ι → ℝ) {z : E}
    (hz : z ∈ CenteredZonotope v c) : -z ∈ CenteredZonotope v c := by
  obtain ⟨t, ht, hsum⟩ := hz
  refine ⟨fun j => -t j, ?_, ?_⟩
  · intro j
    simpa using ht j
  · simpa only [neg_smul, Finset.sum_neg_distrib, hsum]

/-- A point of the averaged-width zonotope is an actual convex Minkowski
average of points of the individual unit boxes. Zero width coordinates and
zero probability weights are included. -/
theorem zonotope_exists_box_average (v : ι → E) (s : J → Finset ι)
    (p : J → ℝ) (hp : ∀ B, 0 ≤ p B) {z : E}
    (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    ∃ q : J → E, (∀ B, q B ∈ SubsetBox v (s B)) ∧ ∑ B, p B • q B = z := by
  classical
  obtain ⟨t, ht, hsum⟩ := hz
  let c : ι → ℝ := averagedWidths s p
  let u : J → ι → ℝ := fun B j => if j ∈ s B then t j / c j else 0
  have hc (j : ι) : 0 ≤ c j := averagedWidths_nonneg s p hp j
  have htzero (j : ι) (hj : c j = 0) : t j = 0 := by
    have h := ht j
    change |t j| ≤ c j / 2 at h
    rw [hj, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hu (B : J) (j : ι) : |u B j| ≤ (if j ∈ s B then 1 else 0) / 2 := by
    by_cases hmem : j ∈ s B
    · simp only [u, hmem, if_true]
      by_cases hj : c j = 0
      · simp [hj]
      · have hcpos : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hj)
        rw [abs_div, abs_of_pos hcpos]
        apply (div_le_iff₀ hcpos).mpr
        have h := ht j
        change |t j| ≤ c j / 2 at h
        linarith
    · simp [u, hmem]
  have hcoeff (j : ι) : ∑ B, p B * u B j = t j := by
    calc
      (∑ B, p B * u B j) =
          (∑ B, if j ∈ s B then p B else 0) * (t j / c j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B _
        by_cases hj : j ∈ s B <;> simp [u, hj]
      _ = t j := by
        change c j * (t j / c j) = t j
        by_cases hj : c j = 0
        · simp [hj, htzero j hj]
        · field_simp [hj]
  refine ⟨fun B => ∑ j, u B j • v j, ?_, ?_⟩
  · intro B
    exact ⟨u B, hu B, rfl⟩
  · calc
      (∑ B, p B • ∑ j, u B j • v j) = ∑ j, ∑ B, (p B * u B j) • v j := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
      _ = ∑ j, t j • v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, hcoeff]
      _ = z := hsum

/-- Equation (7): matched box centers and the common average zonotope give
points simultaneously in the first polytope and in the reflected second one. -/
theorem matched_boxes_average (A B : Set E) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (v : ι → E) (s : J → Finset ι) (p : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → E)
    (hboxA : ∀ i z, z ∈ SubsetBox v (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox v (s i) → b i + z ∈ B)
    (m : E) (hm : m = ∑ i, p i • (a i + b i))
    {z : E} (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    (∑ i, p i • a i) + z ∈ A ∧ m - ((∑ i, p i • a i) + z) ∈ B := by
  obtain ⟨q, hq, hqsum⟩ := zonotope_exists_box_average v s p hp hz
  have hfirst := hA.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxA i (q i) (hq i))
  have hsecond := hB.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxB i (-q i) (neg_mem_centeredZonotope v _ (hq i)))
  constructor
  · simpa only [smul_add, Finset.sum_add_distrib, hqsum] using hfirst
  · have hsum : (∑ i, p i • (b i + -q i)) =
        m - ((∑ i, p i • a i) + z) := by
      rw [hm]
      simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hqsum]
      abel
    rw [← hsum]
    exact hsecond

/-- Lattice decomposition supplied by matched integral basis boxes. This is
the common geometric consequence of Lemma 4.1 and equation (7). -/
theorem matched_boxes_lattice_decomposition {d n : ℕ}
    (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (s : J → Finset (Fin n)) (hs : ∀ i, 0 < squaredMinor V (s i))
    (p : J → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → b i + z ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ i, p i • (a i + b i)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let C : EuclideanSpace ℝ (Fin n) :=
    ∑ i, p i • basisIncidence V ⟨s i, hs i⟩
  have hC : C ∈ convexHull ℝ (Set.range (basisIncidence V)) :=
    mem_convexHull_of_exists_fintype p (fun i => basisIncidence V ⟨s i, hs i⟩)
      hp hpsum (fun i => Set.mem_range_self _) rfl
  have hwidth : (C : Fin n → ℝ) = averagedWidths s p := by
    funext j
    dsimp only [C]
    rw [euclidean_sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [basisIncidence]
  let ac : EuclideanSpace ℝ (Fin d) := ∑ i, p i • a i
  obtain ⟨x, hxΓ, hxerror⟩ := matroid_basis_polytope_covering V Γ hclosed hv C hC ac
  have hxbox : x - ac ∈ CenteredZonotope (matrixColumn V) (averagedWidths s p) := by
    have hn := neg_mem_centeredZonotope (matrixColumn V) C hxerror
    simpa only [neg_sub, hwidth] using hn
  have hboth := matched_boxes_average A B hA hB (matrixColumn V) s p hp hpsum
    a b hboxA hboxB m hm hxbox
  have hAx : x ∈ A := by
    simpa [ac, add_sub_cancel_left] using hboth.1
  have hBy : m - x ∈ B := by
    simpa [ac, add_sub_cancel_left] using hboth.2
  exact ⟨x, hAx, m - x, hBy, hxΓ, Γ.sub_mem hmΓ hxΓ, by abel⟩

end PaperVerification.Toric
end
-- END PaperVerification.ToricBoxAverages
end

section
-- BEGIN PaperVerification.ToricCornerBoxes
/-!
# Unit corner boxes and their facet-center slack

The unit-box assertion needed for integer decomposition follows directly from
convexity and long edge segments. It does not require contraction theory.
The second part proves the half-integral facet slack of every contained unit
basis box, which is the Cartier-center estimate in Lemma 4.2.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A simplex of edge extent `r` contains every nonnegative coordinate
combination with total coordinate sum at most `r`. -/
theorem corner_simplex_mem {d : ℕ} (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (r : ℝ) (hr : 0 < r) (hv : ∀ i, p + r • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i ≤ r) :
    p + ∑ i, t i • v i ∈ A := by
  let L : (Fin d → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  have hL (x : Fin d → ℝ) : L x = ∑ i, x i • v i := by simp [L]
  let S : Set (Fin d → ℝ) := {x | p + L x ∈ A}
  have hS : Convex ℝ S := (hA.translate_preimage_right p).linear_preimage L
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i r) ⊆ S := by
    rintro x (rfl | ⟨i, rfl⟩)
    · simpa [S] using hp
    · simpa [S, L, Pi.single_apply] using hv i
  have htSimplex : t ∈ RealSimplex d r := ⟨ht, hsum⟩
  rw [realSimplex_eq_convexHull hr] at htSimplex
  have hmem := convexHull_min hverts hS htSimplex
  simpa [S, hL] using hmem

/-- Any convex body containing `d` long outgoing edge segments contains their
entire unit corner box. The directions need not be linearly independent for
this convexity statement. -/
theorem unit_corner_box_of_long_segments {d : ℕ} (hd : 0 < d)
    (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (lengths : Fin d → ℝ)
    (hlength : ∀ i, (d : ℝ) ≤ lengths i)
    (hv : ∀ i, p + lengths i • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    p + ∑ i, t i • v i ∈ A := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hv' (i : Fin d) : p + (d : ℝ) • v i ∈ A := by
    have hlen : 0 < lengths i := hdR.trans_le (hlength i)
    have hratio : (d : ℝ) / lengths i ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hdR.le hlen.le, (div_le_one hlen).mpr (hlength i)⟩
    have h := hA.lineMap_mem hp (hv i) hratio
    simpa [AffineMap.lineMap_apply_module', smul_smul, hlen.ne', add_comm] using h
  apply corner_simplex_mem A hA p hp v (d : ℝ) hdR hv' t (fun i => (ht i).1)
  calc
    (∑ i, t i) ≤ ∑ _ : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (ht i).2)
    _ = d := by simp

/-- A contained centered unit box forces the stated slack for any supporting
affine functional. -/
theorem unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (c : E) (v : ι → E)
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • v i)) :
    (∑ i, |f.linear (v i)|) / 2 ≤ f c := by
  let t : ι → ℝ := fun i => if 0 ≤ f.linear (v i) then -(1 / 2) else 1 / 2
  have ht : ∀ i, |t i| ≤ 1 / 2 := by
    intro i
    dsimp [t]
    split_ifs <;> norm_num
  have hterm (i : ι) : t i * f.linear (v i) = -(|f.linear (v i)| / 2) := by
    by_cases hi : 0 ≤ f.linear (v i)
    · simp [t, hi, abs_of_nonneg hi] <;> ring
    · simp [t, hi, abs_of_neg (lt_of_not_ge hi)] <;> ring
  have hf : f (c + ∑ i, t i • v i) = f c + ∑ i, t i * f.linear (v i) := by
    rw [add_comm]
    change f ((∑ i, t i • v i) +ᵥ c) = _
    rw [AffineMap.map_vadd]
    simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]
  have h := hbox t ht
  rw [hf] at h
  simp only [hterm, Finset.sum_neg_distrib, ← Finset.sum_div] at h
  linarith

/-- An integral, nonzero normal has total absolute coefficient at least one
on every genuine real basis on which it takes integer values. -/
theorem integral_basis_normal_abs_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f (b i)) :
    1 ≤ ∑ i, |f (b i)| := by
  have hne : ∃ i, f (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    exact b.ext (fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := hne
  have hzi : z i ≠ 0 := by
    intro hzero
    apply hi
    rw [← hz i, hzero, Int.cast_zero]
  have hziabs : (1 : ℤ) ≤ |z i| := Int.one_le_abs hzi
  have hiabs : (1 : ℝ) ≤ |f (b i)| := by
    rw [← hz i]
    exact_mod_cast hziabs
  have hsum : |f (b i)| ≤ ∑ j, |f (b j)| :=
    Finset.single_le_sum (f := fun j => |f (b j)|)
      (fun j _ => abs_nonneg (f (b j))) (Finset.mem_univ i)
  exact hiabs.trans hsum

/-- The center slack estimate of Lemma 4.2 for every nonzero integral facet
normal: a contained unit basis box has center slack at least one half. -/
theorem integral_unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : E) (b : Module.Basis ι ℝ E)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f.linear (b i))
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • b i)) :
    1 / 2 ≤ f c := by
  have h₁ := unit_box_center_slack f c b hbox
  have h₂ := integral_basis_normal_abs_sum b f.linear hf z hz
  linarith

end PaperVerification.Toric
end
-- END PaperVerification.ToricCornerBoxes
end

section
-- BEGIN PaperVerification.ToricIntegralBasis
/-!
# Integral edge bases and real corner boxes

The integral basis appearing in the literal smoothness definition is extended to
an actual real basis. The extension preserves every lattice coordinate. Thus
integer supporting normals and the geometric edge lengths can be used directly
in the real box covering argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

@[simp] theorem embed_int_smul {n : ℕ} (k : ℤ) (z : Lattice n) :
    embed n (k • z) = (k : ℝ) • embed n z := by
  ext i
  simp [embed, Int.cast_mul]

/-- The standard integral lattice as a genuine real-space submodule. -/
def standardIntegerLattice (n : ℕ) : Submodule ℤ (Ambient n) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

instance standardIntegerLattice_discreteTopology (n : ℕ) :
    DiscreteTopology (standardIntegerLattice n) := by
  exact ZSpan.discreteTopology_pi_basisFun (ι := Fin n)

instance standardIntegerLattice_isZLattice (n : ℕ) :
    IsZLattice ℝ (standardIntegerLattice n) := by
  dsimp [standardIntegerLattice]
  infer_instance

/-- The usual coordinate lattice and its embedded real submodule are linearly equivalent. -/
def standardLatticeEquiv (n : ℕ) : Lattice n ≃ₗ[ℤ] standardIntegerLattice n :=
  ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm

@[simp] theorem standardLatticeEquiv_coe {n : ℕ} (z : Lattice n) :
    ((standardLatticeEquiv n z : standardIntegerLattice n) : Ambient n) = embed n z := by
  classical
  change (((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm z : Ambient n) = _
  rw [Module.Basis.equivFun_symm_apply]
  ext j
  simp [Submodule.coe_sum, Submodule.coe_smul_of_tower, Module.Basis.restrictScalars_apply,
    Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, embed]

/-- Every integral basis of the coordinate lattice gives the same vectors as a real basis. -/
def integralBasisReal {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℝ (Ambient n) :=
  (b.map (standardLatticeEquiv n)).ofZLatticeBasis ℝ (standardIntegerLattice n)

@[simp] theorem integralBasisReal_apply {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    integralBasisReal b i = embed n (b i) := by
  simp [integralBasisReal]

/-- Real coordinates of a lattice vector in an integral basis are exactly its integer coordinates. -/
@[simp] theorem integralBasisReal_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralBasisReal b).repr (embed n z) i = (b.repr z i : ℝ) := by
  have h := (b.map (standardLatticeEquiv n)).ofZLatticeBasis_repr_apply
    ℝ (standardIntegerLattice n) (standardLatticeEquiv n z) i
  simpa only [integralBasisReal, standardLatticeEquiv_coe, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

/-- Each real dual basis functional is integral on the embedded coordinate lattice. -/
theorem integralBasisReal_coordinate_integral {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    ∃ k : ℤ, (integralBasisReal b).repr (embed n z) i = k :=
  ⟨b.repr z i, integralBasisReal_repr b z i⟩

namespace LatticePolytope

/-- A specified integral edge basis with the required actual edge lengths
contains its entire unit corner box. This formulation keeps the chosen basis
fixed when matching two polytopes with the same normal fan. -/
theorem integral_edges_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hlength : P.EdgesAtLeast n) (vZ : Lattice n)
    (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    embed n vZ + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim (embed 0 vZ)
      (embed 0 vZ + ∑ i, t i • integralBasisReal b i)) ▸ hv
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) (embed n vZ) hv (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      exact_mod_cast P.edge_basis_length_bound hlength vZ b i (lengths i) (hedges i)
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i)).2.1
      simpa only [map_add, embed_int_smul, integralBasisReal_apply,
        Int.cast_natCast] using hmem

/-- The ordinary unit corner box supplied by every smooth vertex and the exact
edge-length bound of Theorem 1.1. This includes dimension zero. -/
theorem smooth_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlength : P.EdgesAtLeast n)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
      embed n vZ = v ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
        v + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, hvZ, ?_⟩
  intro t ht
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim v (v + ∑ i, t i • integralBasisReal b i)) ▸ hv.1
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) v hv.1 (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      have hbound := P.edge_basis_length_bound hlength vZ b i (lengths i)
        (by simpa only [hvZ] using (hedges i).2)
      exact_mod_cast hbound
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i).2).2.1
      have he : embed n (vZ + (lengths i : ℤ) • b i) =
          v + (lengths i : ℝ) • integralBasisReal b i := by
        rw [map_add, hvZ, integralBasisReal_apply]
        ext j
        simp [embed, Int.cast_mul]
      rwa [he] at hmem

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricIntegralBasis
end

#eval "TORIC_DICTIONARY_PART_05_EOF"
