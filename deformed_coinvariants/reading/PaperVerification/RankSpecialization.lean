module

public import PaperVerification.MatrixRank
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.FractionRing
public import Lean.Elab.Tactic.Omega

/-!
# Rank bounds for polynomial complexes

This proves the full linear-algebra statement of Lemma 2.1 in the deformed
coinvariant paper. The coefficient ring is allowed to be any integral domain;
multivariate polynomial parameter rings are a special case. The maps must form
an actual complex over the coefficient ring, and exactness is assumed only at
the specified fiber.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open Matrix Module

namespace PaperVerification.RankSpecialization

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable {u v w : Type*} [Fintype u] [Fintype v] [Fintype w]

/-- A specialization cannot have larger matrix rank than the fraction-field matrix. -/
theorem rank_specialization_le {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
    (A : Matrix v u R) (φ : R →+* K) :
    (A.map φ).rank ≤ (A.map (algebraMap R L)).rank := by
  obtain ⟨r, c, hminor⟩ :=
    (Matrix.le_rank_iff_exists_det_submatrix_ne_zero).mp
      (le_rfl : (A.map φ).rank ≤ (A.map φ).rank)
  apply Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mpr
  refine ⟨r, c, ?_⟩
  simp only [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hminor ⊢
  exact (map_ne_zero_iff (algebraMap R L) (IsFractionRing.injective R L)).mpr
    (fun hzero => hminor (by simp only [hzero, map_zero]))

/-- Exactness at the middle of a finite complex gives the rank sum equality. -/
theorem rank_sum_of_exact (F : Matrix w v K) (G : Matrix v u K)
    (hexact : LinearMap.range G.mulVecLin = LinearMap.ker F.mulVecLin) :
    F.rank + G.rank = Fintype.card v := by
  have hn := F.mulVecLin.finrank_range_add_finrank_ker
  rw [← hexact] at hn
  simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using hn

/-- The exact fiber may have a different residue field from the fiber being
bounded. This is needed when the exact fiber retains independent coefficient
indeterminates while the other fiber specializes them to arbitrary scalars. -/
theorem rank_le_at_exact_fiber_of_distinct_fields
    {K₀ : Type*} [Field K₀]
    (F : Matrix w v R) (G : Matrix v u R) (hcomplex : F * G = 0)
    (φ₀ : R →+* K₀) (φ : R →+* K)
    (hexact : LinearMap.range (G.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin) :
    (F.map φ).rank ≤ (F.map φ₀).rank := by
  let L := FractionRing R
  let FL : Matrix w v L := F.map (algebraMap R L)
  let matrixG : Matrix v u L := G.map (algebraMap R L)
  have hFG : FL * matrixG = 0 := by
    dsimp [FL, matrixG]
    rw [← Matrix.map_mul, hcomplex]
    simp
  have hsum : FL.rank + matrixG.rank ≤ Fintype.card v := by
    have hsub : LinearMap.range matrixG.mulVecLin ≤ LinearMap.ker FL.mulVecLin := by
      apply LinearMap.range_le_ker_iff.mpr
      rw [← Matrix.mulVecLin_mul, hFG]
      simp
    have hle := Submodule.finrank_mono hsub
    have heq := FL.mulVecLin.finrank_range_add_finrank_ker
    change matrixG.rank ≤ Module.finrank L (LinearMap.ker FL.mulVecLin) at hle
    change FL.rank + Module.finrank L (LinearMap.ker FL.mulVecLin) =
      Module.finrank L (v → L) at heq
    rw [Module.finrank_fintype_fun_eq_card] at heq
    omega
  have hF₀ := rank_specialization_le (L := L) F φ₀
  have hG₀ := rank_specialization_le (L := L) G φ₀
  have heq := rank_sum_of_exact (F.map φ₀) (G.map φ₀) hexact
  have hF := rank_specialization_le (L := L) F φ
  change (F.map φ₀).rank ≤ FL.rank at hF₀
  change (G.map φ₀).rank ≤ matrixG.rank at hG₀
  change (F.map φ).rank ≤ FL.rank at hF
  omega

/-- A complex over a domain that is exact at one fiber has maximal first-map rank
at that fiber. This is the matrix form of the paper's Lemma 2.1. -/
theorem rank_le_at_exact_fiber
    (F : Matrix w v R) (G : Matrix v u R) (hcomplex : F * G = 0)
    (φ₀ φ : R →+* K)
    (hexact : LinearMap.range (G.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin) :
    (F.map φ).rank ≤ (F.map φ₀).rank := by
  let L := FractionRing R
  let FL : Matrix w v L := F.map (algebraMap R L)
  let matrixG : Matrix v u L := G.map (algebraMap R L)
  have hFG : FL * matrixG = 0 := by
    dsimp [FL, matrixG]
    rw [← Matrix.map_mul, hcomplex]
    simp
  have hsum : FL.rank + matrixG.rank ≤ Fintype.card v := by
    have hsub : LinearMap.range matrixG.mulVecLin ≤ LinearMap.ker FL.mulVecLin := by
      apply LinearMap.range_le_ker_iff.mpr
      rw [← Matrix.mulVecLin_mul, hFG]
      simp
    have hle := Submodule.finrank_mono hsub
    have heq := FL.mulVecLin.finrank_range_add_finrank_ker
    change matrixG.rank ≤ Module.finrank L (LinearMap.ker FL.mulVecLin) at hle
    change FL.rank + Module.finrank L (LinearMap.ker FL.mulVecLin) =
      Module.finrank L (v → L) at heq
    rw [Module.finrank_fintype_fun_eq_card] at heq
    omega
  have hF₀ := rank_specialization_le (L := L) F φ₀
  have hG₀ := rank_specialization_le (L := L) G φ₀
  have heq := rank_sum_of_exact (F.map φ₀) (G.map φ₀) hexact
  have hF := rank_specialization_le (L := L) F φ
  change (F.map φ₀).rank ≤ FL.rank at hF₀
  change (G.map φ₀).rank ≤ matrixG.rank at hG₀
  change (F.map φ).rank ≤ FL.rank at hF
  omega

/-- The same statement for any number of polynomial parameters. -/
theorem polynomial_rank_le_at_exact_parameter
    {σ : Type*} (F : Matrix w v (MvPolynomial σ K))
    (G : Matrix v u (MvPolynomial σ K)) (hcomplex : F * G = 0)
    (t₀ t : σ → K)
    (hexact : LinearMap.range (G.map (MvPolynomial.eval t₀)).mulVecLin =
      LinearMap.ker (F.map (MvPolynomial.eval t₀)).mulVecLin) :
    (F.map (MvPolynomial.eval t)).rank ≤ (F.map (MvPolynomial.eval t₀)).rank := by
  exact rank_le_at_exact_fiber F G hcomplex (MvPolynomial.eval t₀) (MvPolynomial.eval t) hexact

end PaperVerification.RankSpecialization
