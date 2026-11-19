module

public import ToricPower.ParametricPolytope
public import NormalProjective.Geometry

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixRows (C : Matrix ι (Fin n) ℝ) (i : ι) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp C.mulVecLin

@[simp] lemma matrixRows_apply (C : Matrix ι (Fin n) ℝ)
    (i : ι) (x : Fin n → ℝ) : matrixRows C i x = (C *ᵥ x) i := rfl

lemma facetCoefficientMatrix_matrixRows (C : Matrix ι (Fin n) ℝ) :
    NormalProjective.facetCoefficientMatrix (matrixRows C) = C := by
  ext i j
  simp [NormalProjective.facetCoefficientMatrix, matrixRows, Matrix.mulVec,
    dotProduct, Pi.single_apply]

def basicMatrix (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) :
    Matrix (Fin n) (Fin n) ℤ := C.submatrix I id

def basicSolution (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (I : Fin n → ι) : Fin n → ℝ :=
  ((basicMatrix C I).det : ℝ)⁻¹ •
    ((realMatrix (basicMatrix C I)).adjugate *ᵥ (fun k => h (I k)))

theorem basicSolution_solves (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (I : Fin n → ι) (hI : (basicMatrix C I).det ≠ 0) :
    realMatrix (basicMatrix C I) *ᵥ basicSolution C h I = fun k => h (I k) := by
  have hd : ((basicMatrix C I).det : ℝ) ≠ 0 := by exact_mod_cast hI
  rw [basicSolution, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
    realMatrix_det, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem basicSolution_unique (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (I : Fin n → ι) (hI : (basicMatrix C I).det ≠ 0)
    (x : Fin n → ℝ)
    (hx : realMatrix (basicMatrix C I) *ᵥ x = fun k => h (I k)) :
    x = basicSolution C h I := by
  apply realMatrix_solution_unique (basicMatrix C I) hI
  rw [hx, basicSolution_solves C h I hI]

theorem basicSolution_affine (C : Matrix ι (Fin n) ℤ)
    (d e : ι → ℝ) (I : Fin n → ι) (t : ℝ) :
    basicSolution C (fun j => t * d j + e j) I =
      t • basicSolution C d I + basicSolution C e I := by
  change ((basicMatrix C I).det : ℝ)⁻¹ •
    ((realMatrix (basicMatrix C I)).adjugate *ᵥ
      (t • (fun k => d (I k)) + (fun k => e (I k)))) = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_comm]
  rfl

def feasibleBases (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ) :
    Set (Fin n → ι) :=
  {I | (basicMatrix C I).det ≠ 0 ∧
    basicSolution C h I ∈ NormalProjective.halfspaceRegion
      (matrixRows (C.map (Int.castRingHom ℝ))) h}

theorem extremePoint_is_basicSolution (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (x : Fin n → ℝ)
    (hx : x ∈ (NormalProjective.halfspaceRegion
      (matrixRows (C.map (Int.castRingHom ℝ))) h).extremePoints ℝ) :
    ∃ I ∈ feasibleBases C h, x = basicSolution C h I := by
  obtain ⟨I, hdet, hsolve⟩ :=
    NormalProjective.extremePoint_has_nonsingular_active_minor
      (matrixRows (C.map (Int.castRingHom ℝ))) h hx
  rw [facetCoefficientMatrix_matrixRows] at hdet hsolve
  have hI : (basicMatrix C I).det ≠ 0 := by
    intro hz
    apply hdet
    change (realMatrix (basicMatrix C I)).det = 0
    rw [realMatrix_det, hz]
    simp
  have hx' : x = basicSolution C h I := basicSolution_unique C h I hI x hsolve
  refine ⟨I, ⟨hI, ?_⟩, hx'⟩
  rw [← hx']
  exact hx.1

theorem compact_halfspace_eq_convexHull_basicSolutions
    (C : Matrix ι (Fin n) ℤ) (h : ι → ℝ)
    (hc : IsCompact (NormalProjective.halfspaceRegion
      (matrixRows (C.map (Int.castRingHom ℝ))) h)) :
    NormalProjective.halfspaceRegion (matrixRows (C.map (Int.castRingHom ℝ))) h =
      convexHull ℝ (basicSolution C h '' feasibleBases C h) := by
  apply le_antisymm
  · rw [NormalProjective.compact_halfspace_eq_convexHull_extremePoints
      (matrixRows (C.map (Int.castRingHom ℝ))) h hc]
    apply convexHull_mono
    intro x hx
    obtain ⟨I, hI, hxI⟩ := extremePoint_is_basicSolution C h x hx
    exact ⟨I, hI, hxI.symm⟩
  · apply convexHull_min
    · rintro x ⟨I, hI, rfl⟩
      exact hI.2
    · exact NormalProjective.convex_halfspaceRegion _ _

end ToricPower
