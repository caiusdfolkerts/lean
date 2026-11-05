module
public import Projection.Normalization.MinorMaximum
public import Projection.Normalization.MinorScales
public import Projection.Normalization.PivotNormalizer
public import Mathlib.Logic.Equiv.Set

/-!
# Normalization by maximal minors

The proof uses actual minors of the input matrix. A maximizing pivot of order
strictly below `k` determines a bounded change of rows. The change fixes every
vector supported outside the pivot coordinates and has exactly the determinant
factor required for the marked mixed volumes with `k` segment arguments.

No nonsingularity hypothesis on the input matrix is needed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace ProjectionVolumes

/-- Complete an injection by its set-theoretic complement, without choosing an
ordering of that complement. -/
def selectionEquiv {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    ι ⊕ {x : κ // x ∉ Set.range f} ≃ κ := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun x => x ∈ Set.range f))

@[simp] lemma selectionEquiv_inl {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (i : ι) : selectionEquiv f hf (Sum.inl i) = f i := rfl

@[simp] lemma selectionEquiv_inr {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (i : {x : κ // x ∉ Set.range f}) :
    selectionEquiv f hf (Sum.inr i) = i := rfl

/-- The entry of any matrix is a minor of order one. -/
lemma entry_le_minorMaximum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |M i j| ≤ minorMaximum M 1 := by
  simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using
    minor_le_maximum M (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)

/-- All quantitative bounds for the pivot transformation. The tail row and
column maps may be arbitrary; the eventual application uses their complements.
-/
theorem maximalMinor_block_bounds {n r k : ℕ} {τ κ : Type*}
    [Fintype τ] [DecidableEq τ]
    (M : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin (r + 1) → Fin n) (tailRows : τ → Fin n) (tailCols : κ → Fin n)
    (g : ℝ) (hg : 1 ≤ g) (hrk : r + 1 < k)
    (hpivot : |(M.submatrix rows cols).det| = minorMaximum M (r + 1))
    (hexact : minorMaximum M (r + 1) = g ^ (k - (r + 1)))
    (hmax : ∀ j < k, minorMaximum M j ≤ g ^ (k - j)) :
    let B := M.submatrix rows cols
    let A := M.submatrix rows tailCols
    let C := M.submatrix tailRows cols
    let D := M.submatrix tailRows tailCols
    (∀ i j, |pivotNormalizer g B C i j| ≤ 1) ∧
    (∀ i j, |(g • (pivotNormalizer g B C * Matrix.fromBlocks B A C D)) i j| ≤
      max 1 (minorMaximum M k)) ∧
    g ^ k * |(pivotNormalizer g B C).det| = 1 := by
  classical
  dsimp only
  let B := M.submatrix rows cols
  let A := M.submatrix rows tailCols
  let C := M.submatrix tailRows cols
  let D := M.submatrix tailRows tailCols
  have hgpos : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hp : |B.det| = minorMaximum M (r + 1) := hpivot
  have hdp : 0 < minorMaximum M (r + 1) := active_minor_pos hg hexact
  have hbpos : 0 < |B.det| := hp.symm ▸ hdp
  have hb : B.det ≠ 0 := abs_pos.mp hbpos
  have hprevious : minorMaximum M r ≤ g * minorMaximum M (r + 1) := by
    simpa only [Nat.add_sub_cancel] using
      previous_minor_le (d := minorMaximum M) (by omega) hrk hexact hmax
  have hBbound : ∀ i j, |B⁻¹ i j| ≤ g := by
    intro i j
    refine (inverse_entry_bound B hb (minorMaximum M r)
      (cofactor_minor_bound M rows cols) i j).trans ?_
    apply (div_le_iff₀ hbpos).mpr
    simpa only [hp] using hprevious
  have hAbound : ∀ i j, |(B⁻¹ * A) i j| ≤ 1 := by
    intro i j
    exact inverse_mulVec_bound B (fun a => M (rows a) (tailCols j)) hb
      (fun a => hp.symm ▸ replacement_column_minor_bound M rows cols a (tailCols j)) i
  have hCbound : ∀ i j, |(C * B⁻¹) i j| ≤ 1 := by
    intro i j
    exact vecMul_inverse_bound B (fun a => M (tailRows i) (cols a)) hb
      (fun a => hp.symm ▸ replacement_row_minor_bound M rows cols a (tailRows i)) j
  have hSchur : ∀ i j, |g * (D - C * B⁻¹ * A) i j| ≤ max 1 (minorMaximum M k) := by
    intro i j
    have hbminor : |(Matrix.fromBlocks B (fun a (_ : Unit) => A a j)
        (fun (_ : Unit) b => C i b) (fun (_ _ : Unit) => D i j)).det| ≤
        minorMaximum M (r + 1 + 1) := by
      simpa only [B, A, C, D, Matrix.submatrix_apply] using
        bordered_minor_bound M rows cols (tailRows i) (tailCols j)
    rw [bordered_pivot_det B A C D hb i j, abs_mul, hp] at hbminor
    rw [abs_mul, abs_of_pos hgpos]
    by_cases hnext : r + 1 + 1 < k
    · have hn := next_minor_le hgpos.le hnext hexact hmax
      have hbound : g * |(D - C * B⁻¹ * A) i j| ≤ 1 := by
        apply (mul_le_mul_iff_of_pos_left hdp).mp
        calc
          minorMaximum M (r + 1) * (g * |(D - C * B⁻¹ * A) i j|) =
              g * (minorMaximum M (r + 1) * |(D - C * B⁻¹ * A) i j|) := by
                rw [mul_left_comm]
          _ ≤ g * minorMaximum M (r + 1 + 1) :=
            mul_le_mul_of_nonneg_left hbminor hgpos.le
          _ ≤ minorMaximum M (r + 1) := hn
          _ = minorMaximum M (r + 1) * 1 := (mul_one _).symm
      exact hbound.trans (le_max_left _ _)
    · have hlast : r + 1 + 1 = k := by omega
      have hdg := last_active_minor_eq_scale hlast hexact
      rw [hdg, hlast] at hbminor
      exact hbminor.trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change |g⁻¹ * B⁻¹ i j| ≤ 1
        rw [abs_mul, abs_inv, abs_of_pos hgpos]
        have h := mul_le_mul_of_nonneg_left (hBbound i j) (inv_nonneg.mpr hgpos.le)
        simpa only [inv_mul_cancel₀ hgpos.ne'] using h
      | inr j => simp [pivotNormalizer]
    | inr i =>
      cases j with
      | inl j => simpa only [pivotNormalizer, Matrix.fromBlocks_apply₂₁,
          Matrix.neg_apply, abs_neg] using hCbound i j
      | inr j =>
        by_cases h : i = j <;> simp [pivotNormalizer, Matrix.one_apply, h]
  · rw [pivotNormalizer_mul g hgpos.ne' B A C D hb]
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hi : |(1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j| ≤ 1 := by
          by_cases h : i = j <;> simp [Matrix.one_apply, h]
        exact hi.trans (le_max_left _ _)
      | inr j => exact (hAbound i j).trans (le_max_left _ _)
    | inr i =>
      cases j with
      | inl j =>
        simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, abs_zero] using
          (zero_le_one.trans (le_max_left (1 : ℝ) (minorMaximum M k)))
      | inr j => exact hSchur i j
  · apply pivotNormalizer_scaling g hgpos B C
    · simpa only [Fintype.card_fin] using hrk.le
    · simpa only [Fintype.card_fin] using hp.trans hexact

/-- Every square real matrix admits a uniformly bounded row normalization
fixing the complement of fewer than `k` coordinates. The transformed entries
are controlled solely by its minors of order `k`.

The determinant identity is exact. In particular, the normalizing matrix is
invertible. This theorem applies to all `k > 0`, so it includes the entire
parameter range used in Theorem 3.1 of the paper.
-/
theorem exists_matrix_normalization {n k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (g : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)),
      1 ≤ g ∧ G.det ≠ 0 ∧ s.card < k ∧
      (∀ i j, |G i j| ≤ 1) ∧
      (∀ i j, |(g • (G * M)) i j| ≤ max 1 (minorMaximum M k)) ∧
      g ^ k * |G.det| = 1 ∧
      (∀ v : Fin n → ℝ, (∀ i ∈ s, v i = 0) → G *ᵥ v = v) := by
  classical
  obtain ⟨q, hqk, g, hg, hexact, hmax⟩ := exists_minor_scale hk (minorMaximum M)
    (fun j _ => minorMaximum_nonneg M j) (minorMaximum_zero M)
  cases q with
  | zero =>
    have hg1 : g = 1 := (pow_eq_one_iff_of_nonneg (zero_le_one.trans hg) hk.ne').mp
      (by simpa only [minorMaximum_zero, Nat.sub_zero] using hexact.symm)
    subst g
    refine ⟨1, 1, ∅, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa only [Finset.card_empty] using hk
    · intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · intro i j
      simp only [one_smul, Matrix.one_mul]
      by_cases hk1 : k = 1
      · simpa only [hk1] using
          (entry_le_minorMaximum M i j).trans (le_max_right 1 (minorMaximum M 1))
      · have h1 : 1 < k := by omega
        exact ((entry_le_minorMaximum M i j).trans
          (by simpa only [one_pow] using hmax 1 h1)).trans (le_max_left _ _)
    · simp
    · intro v _
      exact Matrix.one_mulVec v
  | succ r =>
    have hdp : 0 < minorMaximum M (r + 1) := active_minor_pos hg hexact
    obtain ⟨rows, cols, hpivot⟩ := exists_maximal_minor M hdp
    have hb : (M.submatrix rows cols).det ≠ 0 := abs_pos.mp (hpivot.symm ▸ hdp)
    have hrows := injective_rows_of_minor_ne_zero M rows cols hb
    have hcols := injective_cols_of_minor_ne_zero M rows cols hb
    let τ := {i : Fin n // i ∉ Set.range rows}
    let κ := {i : Fin n // i ∉ Set.range cols}
    let er : Fin (r + 1) ⊕ τ ≃ Fin n := selectionEquiv rows hrows
    let ec : Fin (r + 1) ⊕ κ ≃ Fin n := selectionEquiv cols hcols
    let B := M.submatrix rows cols
    let A := M.submatrix rows (fun i : κ => i.val)
    let C := M.submatrix (fun i : τ => i.val) cols
    let D := M.submatrix (fun i : τ => i.val) (fun i : κ => i.val)
    let Gb := pivotNormalizer g B C
    let G := Gb.submatrix er.symm er.symm
    let s := Finset.univ.image rows
    obtain ⟨hGb, hGbM, hscale⟩ := maximalMinor_block_bounds M rows cols
      (fun i : τ => i.val) (fun i : κ => i.val) g hg hqk hpivot hexact hmax
    have hblock : M.submatrix er ec = Matrix.fromBlocks B A C D := by
      ext i j
      cases i <;> cases j <;> rfl
    have hdet : G.det = Gb.det := Matrix.det_submatrix_equiv_self er.symm Gb
    have hscaleG : g ^ k * |G.det| = 1 := by rwa [hdet]
    have hne : G.det ≠ 0 := by
      intro hz
      rw [hz, abs_zero, mul_zero] at hscaleG
      exact zero_ne_one hscaleG
    have hGpull : G.submatrix er er = Gb := by
      ext i j
      exact congrArg₂ Gb (er.symm_apply_apply i) (er.symm_apply_apply j)
    have hproduct : (g • (G * M)).submatrix er ec =
        g • (Gb * Matrix.fromBlocks B A C D) := by
      simp only [Matrix.submatrix_smul, Pi.smul_apply]
      rw [← Matrix.submatrix_mul_equiv G M er er ec,
        hGpull, hblock]
    refine ⟨g, G, s, hg, hne, ?_, ?_, ?_, hscaleG, ?_⟩
    · simpa only [s, Finset.card_image_of_injective _ hrows,
        Finset.card_univ, Fintype.card_fin] using hqk
    · intro i j
      exact hGb (er.symm i) (er.symm j)
    · intro i j
      have h := hGbM (er.symm i) (ec.symm j)
      rw [← hproduct] at h
      simpa only [Matrix.submatrix_apply, er.apply_symm_apply, ec.apply_symm_apply] using h
    · intro v hv
      have hvrows : ∀ i, v (rows i) = 0 := fun i =>
        hv (rows i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hvpull : v ∘ er = Sum.elim (fun _ => 0) (fun i : τ => v i.val) := by
        funext i
        cases i with
        | inl i => exact hvrows i
        | inr i => rfl
      change Gb.submatrix er.symm er.symm *ᵥ v = v
      rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hvpull, pivotNormalizer_fixes]
      funext i
      have h := congrFun hvpull (er.symm i)
      simpa only [Function.comp_apply, er.apply_symm_apply] using h.symm

end ProjectionVolumes
