module

public import PaperVerification.DivergenceDegreeSpaces
public import PaperVerification.RankSpecialization

/-!
# Finite matrices of the actual divergence--Koszul maps

All entries are coefficients of the actual operators. The second matrix
records the exact shifted output projection; this is enough because the
first map commutes with it. The matrix-complex identity and exactness of its
zero fiber are proved from the actual maps, not supplied as matrix premises.

This supporting source has not yet been compiled.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DivergenceDegrees

open MvPolynomial Module Matrix DivergenceCocycle
open WeightedPolynomialPieces
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

variable (w : ι → ℕ) [∀ i, NeZero (w i)]

def decode (s d : ℕ) : (Index w s d → K) →ₗ[K] P :=
  (piece (K := K) w s d).subtype.comp
    (basis (K := K) w s d).equivFun.symm.toLinearMap

theorem decode_mem (s d : ℕ) (v : Index w s d → K) :
    decode w s d v ∈ piece w s d :=
  ((basis (K := K) w s d).equivFun.symm v).property

theorem basis_equivFun_apply (s d : ℕ) (p : piece (K := K) w s d)
    (a : Index w s d) : (basis w s d).equivFun p a=(p : P).coeff a.val := by
  rw [Basis.equivFun_apply]
  exact basisRestrictSupport_repr_apply p a

@[simp] theorem decode_coeff (s d : ℕ) (v : Index w s d → K) (a : Index w s d) :
    (decode w s d v).coeff a.val=v a := by
  have h := congrFun ((basis (K := K) w s d).equivFun.apply_symm_apply v) a
  rw [basis_equivFun_apply] at h
  exact h

theorem decode_coeffs (s d : ℕ) (p : P) (hp : p ∈ piece w s d) :
    decode w s d (fun a => p.coeff a.val)=p := by
  have he : (fun a : Index w s d => p.coeff a.val)=
      (basis (K := K) w s d).equivFun ⟨p,hp⟩ := by
    funext a
    exact (basis_equivFun_apply w s d ⟨p,hp⟩ a).symm
  rw [he]
  change (((basis (K := K) w s d).equivFun.symm
    ((basis (K := K) w s d).equivFun ⟨p,hp⟩) : piece w s d) : P)=p
  rw [LinearEquiv.symm_apply_apply]

theorem project_coeff (s d : ℕ) (p : P) (a : Index w s d) :
    (project w s d p).coeff a.val=p.coeff a.val := by
  classical
  simp only [project,coeff_weightedHomogeneousComponent,integer_weight]
  rw [if_pos]
  have ha := a.property
  omega

theorem decode_coeffs_project (s d : ℕ) (p : P) :
    decode w s d (fun a => p.coeff a.val)=project w s d p := by
  have h := decode_coeffs w s d (project w s d p) (project_mem w s d p)
  simpa only [project_coeff] using h

theorem decode_eq_sum (s d : ℕ) (v : Index w s d → K) :
    decode w s d v=∑ a,v a • monomial a.val (1 : K) := by
  change (((basis (K := K) w s d).equivFun.symm v : piece w s d) : P)=_
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,basis,basisRestrictSupport_apply_coe]

variable (L : LieRinehartSubalgebra P Der)
variable {r : ℕ} (b : Basis (Fin r) P L)
variable (δ : Fin r → ℕ) (ω : L →ₗ[P] P)

abbrev FirstIndex (d : ℕ) := (i : Fin r) × Index w (δ i) d
abbrev SecondIndex (d : ℕ) := (i : Fin r) × (j : Fin r) × Index w (δ i+δ j) d

def firstDecode (d : ℕ) (v : FirstIndex w δ d → K) : Fin r → P :=
  fun i => decode w (δ i) d (fun a => v ⟨i,a⟩)

def secondDecode (d : ℕ) (A : SecondIndex w δ d → K) : Fin r → Fin r → P :=
  fun i j => decode w (δ i+δ j) d (fun a => A ⟨i,j,a⟩)

def elementaryCoordinates (t : K) (i j : Fin r) : P →ₗ[K] (Fin r → P) :=
  (b.equivFun.restrictScalars K).toLinearMap.comp (elementarySecond L b ω t i j)

theorem secondCoordinates_eq_sum (t : K) (A : Fin r → Fin r → P) :
    secondCoordinates L b ω t A=∑ i,∑ j,elementaryCoordinates L b ω t i j (A j i) := by
  simp only [secondCoordinates_apply,second,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,elementaryCoordinates,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply]

def firstMatrix (t : K) (d : ℕ) : Matrix (Index w 0 d) (FirstIndex w δ d) K :=
  fun a c => (operator L ω t (b c.1) (monomial c.2.val 1)).coeff a.val

def secondMatrix (t : K) (d : ℕ) : Matrix (FirstIndex w δ d) (SecondIndex w δ d) K :=
  fun a c => (elementaryCoordinates L b ω t c.2.1 c.1
    (monomial c.2.2.val 1) a.1).coeff a.2.val

theorem firstMatrix_mulVec (t : K) (d : ℕ) (v : FirstIndex w δ d → K)
    (a : Index w 0 d) :
    (firstMatrix w L b δ ω t d *ᵥ v) a=
      (first L b ω t (firstDecode w δ d v)).coeff a.val := by
  classical
  simp only [Matrix.mulVec,dotProduct,firstMatrix,Fintype.sum_sigma,
    first_apply,firstDecode,decode_eq_sum,map_sum,map_smul,
    coeff_sum,coeff_smul,smul_eq_mul,mul_comm]

theorem secondMatrix_mulVec (t : K) (d : ℕ) (A : SecondIndex w δ d → K)
    (a : FirstIndex w δ d) :
    (secondMatrix w L b δ ω t d *ᵥ A) a=
      (secondCoordinates L b ω t (secondDecode w δ d A) a.1).coeff a.2.val := by
  classical
  rw [secondCoordinates_eq_sum,Finset.sum_comm]
  simp only [Matrix.mulVec,dotProduct,secondMatrix,Fintype.sum_sigma,
    secondDecode,decode_eq_sum,map_sum,map_smul,Finset.sum_apply,
    Pi.smul_apply,coeff_sum,coeff_smul,smul_eq_mul,mul_comm]

theorem first_mem_piece
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω)
    (t : K) (d : ℕ) (v : Fin r → P) (hv : ∀ i,v i ∈ piece w (δ i) d) :
    first L b ω t v ∈ piece w 0 d := by
  have hp : projectCoefficients w δ d v=v := by
    funext i
    exact project_of_mem w (δ i) d (hv i)
  have he := project_first L b w δ ω hfields hvalues t d v
  rw [hp] at he
  rw [←he]
  exact project_mem w 0 d _

theorem decode_firstMatrix
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω)
    (t : K) (d : ℕ) (v : FirstIndex w δ d → K) :
    decode w 0 d (firstMatrix w L b δ ω t d *ᵥ v)=
      first L b ω t (firstDecode w δ d v) := by
  rw [show firstMatrix w L b δ ω t d *ᵥ v=
      (fun a => (first L b ω t (firstDecode w δ d v)).coeff a.val) from
    funext (firstMatrix_mulVec w L b δ ω t d v)]
  exact decode_coeffs w 0 d _
    (first_mem_piece w L b δ ω hfields hvalues t d _ (fun i => decode_mem _ _ _ _))

theorem firstDecode_secondMatrix (t : K) (d : ℕ) (A : SecondIndex w δ d → K) :
    firstDecode w δ d (secondMatrix w L b δ ω t d *ᵥ A)=
      projectCoefficients w δ d (secondCoordinates L b ω t (secondDecode w δ d A)) := by
  funext i
  change decode w (δ i) d (fun a => (secondMatrix w L b δ ω t d *ᵥ A) ⟨i,a⟩)=_
  rw [show (fun a => (secondMatrix w L b δ ω t d *ᵥ A) ⟨i,a⟩)=
      (fun a => (secondCoordinates L b ω t (secondDecode w δ d A) i).coeff a.val) from
    funext (fun a => secondMatrix_mulVec w L b δ ω t d A ⟨i,a⟩)]
  exact decode_coeffs_project w (δ i) d _

/-- The entries are actual operator coefficients, and their product is zero
at every scalar parameter. -/
theorem matrix_complex
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (hω : IsClosed L ω)
    (t : K) (d : ℕ) : firstMatrix w L b δ ω t d * secondMatrix w L b δ ω t d=0 := by
  apply Matrix.mulVec_injective
  funext A
  rw [←Matrix.mulVec_mulVec]
  funext a
  rw [firstMatrix_mulVec,firstDecode_secondMatrix,
    first_projected_secondCoordinates L b w δ ω hfields hvalues hω]
  simp only [coeff_zero,Matrix.zero_mulVec,Pi.zero_apply]

/-- Exactness of the finite zero-fiber complex follows from the actual
regular sequence and an explicitly constructed homogeneous preimage. -/
theorem zero_matrix_exact
    (hfields : HomogeneousFields L b w δ)
    (hvalues : HomogeneousValues L b w δ ω) (hω : IsClosed L ω)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin r => ω (b i))) (d : ℕ) :
    LinearMap.range (secondMatrix w L b δ ω 0 d).mulVecLin=
      LinearMap.ker (firstMatrix w L b δ ω 0 d).mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [←Matrix.mulVecLin_mul,matrix_complex w L b δ ω hfields hvalues hω,
      Matrix.mulVecLin_zero]
  · intro v hv
    have hz : first L b ω 0 (firstDecode w δ d v)=0 := by
      rw [←decode_firstMatrix w L b δ ω hfields hvalues]
      change decode w 0 d ((firstMatrix w L b δ ω 0 d).mulVecLin v)=0
      rw [LinearMap.mem_ker.mp hv,map_zero]
    obtain ⟨A,hA,hAv⟩ := zero_parameter_degree_preimage L b w δ ω hvalues hregular d
      (firstDecode w δ d v) (fun i => decode_mem _ _ _ _) hz
    let c : SecondIndex w δ d → K := fun a => (A a.1 a.2.1).coeff a.2.2.val
    have hc : secondDecode w δ d c=A := by
      funext i j
      exact decode_coeffs w (δ i+δ j) d _ (hA i j)
    refine ⟨c,?_⟩
    funext a
    change (secondMatrix w L b δ ω 0 d *ᵥ c) a=v a
    rw [secondMatrix_mulVec,hc,hAv]
    exact decode_coeff w (δ a.1) d (fun z => v ⟨a.1,z⟩) a.2

end PaperVerification.DivergenceDegrees
