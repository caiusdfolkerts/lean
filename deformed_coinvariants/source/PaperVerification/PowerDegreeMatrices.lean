module

public import PaperVerification.PowerDegreeSpaces
public import PaperVerification.PowerCoefficientMap
public import PaperVerification.PowerGenericParameters
public import PaperVerification.RankSpecialization
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The finite matrices used in power-tail specialization

Rows and columns are the exact shifted monomial sets, so no negative-degree
piece is replaced by a constant piece. Every matrix entry is a coefficient of
the actual differential operator or corrected syzygy. The complex identity,
change of coefficient ring, and exactness at the independent-coefficient
zero-slope fiber are derived before applying the rank-specialization theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module Matrix
open scoped BigOperators

namespace PaperVerification.PowerOperators

abbrev TailDegreeIndex (n m d : ℕ) :=
  (i : Fin n) × ShiftedExponent n (m+i.val) d

abbrev SyzygyDegreeIndex (n m d : ℕ) :=
  (i : Fin n) × (j : Fin n) × ShiftedExponent n ((m+i.val)+(m+j.val)) d

section Coordinates

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Decode a finite coordinate vector in the genuine shifted monomial basis. -/
def shiftedDecode (s d : ℕ) :
    (ShiftedExponent n s d → R) →ₗ[R] MvPolynomial (Fin n) R :=
  (shiftedPiece R n s d).subtype.comp
    (shiftedPieceBasis R n s d).equivFun.symm.toLinearMap

theorem shiftedDecode_mem (s d : ℕ) (v : ShiftedExponent n s d → R) :
    shiftedDecode s d v ∈ shiftedPiece R n s d :=
  ((shiftedPieceBasis R n s d).equivFun.symm v).property

theorem shiftedPieceBasis_equivFun_apply (s d : ℕ) (p : shiftedPiece R n s d)
    (a : ShiftedExponent n s d) :
    (shiftedPieceBasis R n s d).equivFun p a = (p : MvPolynomial (Fin n) R).coeff a.val := by
  rw [Basis.equivFun_apply]
  exact basisRestrictSupport_repr_apply p a

@[simp] theorem shiftedDecode_coeff (s d : ℕ) (v : ShiftedExponent n s d → R)
    (a : ShiftedExponent n s d) :
    (shiftedDecode s d v).coeff a.val = v a := by
  have h := congrFun ((shiftedPieceBasis R n s d).equivFun.apply_symm_apply v) a
  rw [shiftedPieceBasis_equivFun_apply] at h
  exact h

theorem shiftedDecode_coeffs (s d : ℕ) (p : MvPolynomial (Fin n) R)
    (hp : p ∈ shiftedPiece R n s d) :
    shiftedDecode s d (fun a => p.coeff a.val) = p := by
  have he : (fun a : ShiftedExponent n s d => p.coeff a.val) =
      (shiftedPieceBasis R n s d).equivFun ⟨p,hp⟩ := by
    funext a
    exact (shiftedPieceBasis_equivFun_apply s d ⟨p,hp⟩ a).symm
  rw [he]
  change (((shiftedPieceBasis R n s d).equivFun.symm
    ((shiftedPieceBasis R n s d).equivFun ⟨p, hp⟩) : shiftedPiece R n s d) :
      MvPolynomial (Fin n) R) = p
  rw [LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 800000 in
theorem shiftedDecode_eq_sum (s d : ℕ) (v : ShiftedExponent n s d → R) :
    shiftedDecode s d v = ∑ a, v a • monomial a.val (1 : R) := by
  change (((shiftedPieceBasis R n s d).equivFun.symm v : shiftedPiece R n s d) :
    MvPolynomial (Fin n) R) = _
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro a _
  change v a • ((basisRestrictSupport R {b : Fin n →₀ ℕ | b.degree + s = d}) a :
    MvPolynomial (Fin n) R) = v a • monomial a.val (1 : R)
  exact congrArg (fun p : MvPolynomial (Fin n) R => v a • p)
    (basisRestrictSupport_apply_coe (R := R)
      (s := {a : Fin n →₀ ℕ | a.degree + s = d}) a)

def tailDegreeDecode (m d : ℕ) (v : TailDegreeIndex n m d → R) :
    Fin n → MvPolynomial (Fin n) R :=
  fun i => shiftedDecode (m+i.val) d (fun a => v ⟨i, a⟩)

def syzygyDegreeDecode (m d : ℕ) (A : SyzygyDegreeIndex n m d → R) :
    Fin n → Fin n → MvPolynomial (Fin n) R :=
  fun i j => shiftedDecode ((m+i.val)+(m+j.val)) d (fun a => A ⟨i, j, a⟩)

theorem tailMap_mem_shiftedPiece (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : Fin n → MvPolynomial (Fin n) R)
    (hv : ∀ i, v i ∈ shiftedPiece R n (m+i.val) d) :
    tailMap c lam m v ∈ shiftedPiece R n 0 d := by
  have he : shiftedProjection 0 d (tailMap c lam m v) = tailMap c lam m v := by
    simp only [tailMap_apply, map_sum, shiftedProjection_reversed, Nat.zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [shiftedProjection_of_mem (hv i)]
  rw [← he]
  exact shiftedProjection_mem _ _ _

theorem syzygyMap_mem_shiftedPiece (c : Fin n → R) (lam : R) (m d : ℕ)
    (A : Fin n → Fin n → MvPolynomial (Fin n) R)
    (hA : ∀ i j, A i j ∈ shiftedPiece R n ((m+i.val)+(m+j.val)) d) (l : Fin n) :
    syzygyMap c lam m A l ∈ shiftedPiece R n (m+l.val) d := by
  have he : shiftedProjection (m+l.val) d (syzygyMap c lam m A l) =
      syzygyMap c lam m A l := by
    simp only [syzygyMap_apply, Finset.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [shiftedProjection_elementarySyzygy]
    have hji : A j i ∈ shiftedPiece R n ((m+i.val)+(m+j.val)) d := by
      simpa only [Nat.add_comm (m+j.val) (m+i.val)] using hA j i
    rw [shiftedProjection_of_mem hji]
  rw [← he]
  exact shiftedProjection_mem _ _ _

/-- The actual matrix of the first map in degree `d`. -/
def tailDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ) :
    Matrix (ShiftedExponent n 0 d) (TailDegreeIndex n m d) R :=
  fun b a => (reversed c lam (m+a.1.val) (monomial a.2.val 1)).coeff b.val

/-- The actual corrected-syzygy matrix. The column `(i,j,a)` encodes the
coefficient `A i j`, hence uses the elementary syzygy with arguments `j,i`. -/
def syzygyDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ) :
    Matrix (TailDegreeIndex n m d) (SyzygyDegreeIndex n m d) R :=
  fun b a =>
    (elementarySyzygy c lam m a.2.1 a.1 (monomial a.2.2.val 1) b.1).coeff b.2.val

theorem tailDegreeMatrix_mulVec (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : TailDegreeIndex n m d → R) (b : ShiftedExponent n 0 d) :
    (tailDegreeMatrix c lam m d *ᵥ v) b =
      (tailMap c lam m (tailDegreeDecode m d v)).coeff b.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, tailDegreeMatrix, Fintype.sum_sigma,
    tailMap_apply, tailDegreeDecode, shiftedDecode_eq_sum, map_sum, map_smul,
    coeff_sum, coeff_smul, smul_eq_mul, mul_comm]

theorem syzygyDegreeMatrix_mulVec (c : Fin n → R) (lam : R) (m d : ℕ)
    (A : SyzygyDegreeIndex n m d → R) (b : TailDegreeIndex n m d) :
    (syzygyDegreeMatrix c lam m d *ᵥ A) b =
      (syzygyMap c lam m (syzygyDegreeDecode m d A) b.1).coeff b.2.val := by
  classical
  rw [syzygyMap_apply, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, syzygyDegreeMatrix, Fintype.sum_sigma,
    syzygyDegreeDecode, shiftedDecode_eq_sum, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, coeff_sum, coeff_smul, smul_eq_mul, mul_comm]

theorem shiftedDecode_tailDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : TailDegreeIndex n m d → R) :
    shiftedDecode 0 d (tailDegreeMatrix c lam m d *ᵥ v) =
      tailMap c lam m (tailDegreeDecode m d v) := by
  rw [show tailDegreeMatrix c lam m d *ᵥ v =
      (fun b => (tailMap c lam m (tailDegreeDecode m d v)).coeff b.val) from
    funext (tailDegreeMatrix_mulVec c lam m d v)]
  exact shiftedDecode_coeffs _ _ _
    (tailMap_mem_shiftedPiece c lam m d _ (fun i => shiftedDecode_mem _ _ _))

theorem tailDegreeDecode_syzygyDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ)
    (A : SyzygyDegreeIndex n m d → R) :
    tailDegreeDecode m d (syzygyDegreeMatrix c lam m d *ᵥ A) =
      syzygyMap c lam m (syzygyDegreeDecode m d A) := by
  funext l
  change shiftedDecode (m+l.val) d
    (fun a => (syzygyDegreeMatrix c lam m d *ᵥ A) ⟨l, a⟩) = _
  rw [show (fun a => (syzygyDegreeMatrix c lam m d *ᵥ A) ⟨l, a⟩) =
      (fun a => (syzygyMap c lam m (syzygyDegreeDecode m d A) l).coeff a.val) from
    funext (fun a => syzygyDegreeMatrix_mulVec c lam m d A ⟨l, a⟩)]
  exact shiftedDecode_coeffs _ _ _
    (syzygyMap_mem_shiftedPiece c lam m d _ (fun i j => shiftedDecode_mem _ _ _) l)

/-- Polynomially in every parameter, the two finite matrices form a complex. -/
theorem tailDegreeMatrix_mul_syzygyDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ) :
    tailDegreeMatrix c lam m d * syzygyDegreeMatrix c lam m d = 0 := by
  apply Matrix.mulVec_injective
  funext A
  rw [← Matrix.mulVec_mulVec]
  funext b
  rw [tailDegreeMatrix_mulVec, tailDegreeDecode_syzygyDegreeMatrix,
    tailMap_syzygyMap]
  simp only [MvPolynomial.coeff_zero, Finsupp.zero_apply, Matrix.zero_mulVec, Pi.zero_apply]

set_option maxHeartbeats 800000 in
/-- Exactness in degree `d` is inherited from the actual Koszul complex by
projecting every preimage to its precise shifted homogeneous component. -/
theorem zero_slope_degree_exact (c : Fin n → R) (m d : ℕ)
    (hf : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) R)
      (List.ofFn fun i : Fin n => weightedPower c (m+i.val))) :
    LinearMap.range (syzygyDegreeMatrix c 0 m d).mulVecLin =
      LinearMap.ker (tailDegreeMatrix c 0 m d).mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul, tailDegreeMatrix_mul_syzygyDegreeMatrix]
    simp only [Matrix.mulVecLin_zero]
  · intro v hv
    have hvzero : tailDegreeMatrix c 0 m d *ᵥ v = 0 := hv
    have hz : tailMap c 0 m (tailDegreeDecode m d v) = 0 := by
      rw [← shiftedDecode_tailDegreeMatrix, hvzero, map_zero]
    obtain ⟨A, hA, hAv⟩ := zero_slope_homogeneous_syzygies c m d hf
      (tailDegreeDecode m d v) (fun i => shiftedDecode_mem _ _ _) hz
    let z : SyzygyDegreeIndex n m d → R :=
      fun a => (A a.1 a.2.1).coeff a.2.2.val
    have hzA : syzygyDegreeDecode m d z = A := by
      funext i j
      change shiftedDecode ((m+i.val)+(m+j.val)) d
        (fun a => (A i j).coeff a.val) = A i j
      exact shiftedDecode_coeffs ((m+i.val)+(m+j.val)) d (A i j) (hA i j)
    refine ⟨z, ?_⟩
    ext a
    rw [Matrix.mulVecLin_apply, syzygyDegreeMatrix_mulVec, hzA, hAv]
    exact shiftedDecode_coeff _ _ _ a.2

end Coordinates

section Specialization

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Entrywise specialization is the matrix of the specialized operator. -/
theorem map_tailDegreeMatrix (φ : R →+* S) (c : Fin n → R) (lam : R) (m d : ℕ) :
    (tailDegreeMatrix c lam m d).map φ =
      tailDegreeMatrix (fun i => φ (c i)) (φ lam) m d := by
  ext b a
  change φ ((reversed c lam (m+a.1.val) (monomial a.2.val 1)).coeff b.val) = _
  rw [← coeff_map, map_reversed, MvPolynomial.map_monomial, map_one]
  rfl

theorem map_syzygyDegreeMatrix (φ : R →+* S) (c : Fin n → R) (lam : R) (m d : ℕ) :
    (syzygyDegreeMatrix c lam m d).map φ =
      syzygyDegreeMatrix (fun i => φ (c i)) (φ lam) m d := by
  ext b a
  change φ ((elementarySyzygy c lam m a.2.1 a.1 (monomial a.2.2.val 1) b.1).coeff
    b.2.val) = _
  rw [← coeff_map, map_elementarySyzygy, MvPolynomial.map_monomial, map_one]
  rfl

variable (K : Type*) [Field K]

theorem generic_zero_slope_degree_exact (m d : ℕ) (hm : 0 < m) :
    LinearMap.range (syzygyDegreeMatrix (genericCoefficient K n) 0 m d).mulVecLin =
      LinearMap.ker (tailDegreeMatrix (genericCoefficient K n) 0 m d).mulVecLin :=
  zero_slope_degree_exact _ _ _ (generic_weighted_power_regular K m hm)

/-- The precise lower-bound rank comparison used in Theorem 2.2, over every
field and for every number of variables and degree. No complex, regularity,
genericity, or rank assumption is supplied by the caller. -/
theorem tailDegreeMatrix_rank_le_generic_zero
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) :
    (tailDegreeMatrix c lam m d).rank ≤
      (tailDegreeMatrix (genericCoefficient K n) 0 m d).rank := by
  let U := MvPolynomial (Option (Fin n)) K
  let cU : Fin n → U := fun i => X (some i)
  let lamU : U := X none
  let φ : U →+* K := MvPolynomial.eval (fun a => a.elim lam c)
  let φ₀ : U →+* GenericCoefficientField K n :=
    MvPolynomial.eval₂Hom (algebraMap K (GenericCoefficientField K n))
      (fun a => a.elim 0 (genericCoefficient K n))
  have hcφ : (fun i => φ (cU i)) = c := by
    funext i
    exact MvPolynomial.eval_X _
  have hlφ : φ lamU = lam := MvPolynomial.eval_X _
  have hcφ₀ : (fun i => φ₀ (cU i)) = genericCoefficient K n := by
    funext i
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hlφ₀ : φ₀ lamU = 0 := MvPolynomial.eval₂Hom_X' _ _ _
  have hF : (tailDegreeMatrix cU lamU m d).map φ = tailDegreeMatrix c lam m d := by
    rw [map_tailDegreeMatrix, hcφ, hlφ]
  have hF₀ : (tailDegreeMatrix cU lamU m d).map φ₀ =
      tailDegreeMatrix (genericCoefficient K n) 0 m d := by
    rw [map_tailDegreeMatrix, hcφ₀, hlφ₀]
  have hG₀ : (syzygyDegreeMatrix cU lamU m d).map φ₀ =
      syzygyDegreeMatrix (genericCoefficient K n) 0 m d := by
    rw [map_syzygyDegreeMatrix, hcφ₀, hlφ₀]
  have hexact : LinearMap.range ((syzygyDegreeMatrix cU lamU m d).map φ₀).mulVecLin =
      LinearMap.ker ((tailDegreeMatrix cU lamU m d).map φ₀).mulVecLin := by
    rw [hF₀, hG₀]
    exact generic_zero_slope_degree_exact K m d hm
  have h := RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields
    (tailDegreeMatrix cU lamU m d) (syzygyDegreeMatrix cU lamU m d)
    (tailDegreeMatrix_mul_syzygyDegreeMatrix cU lamU m d) φ₀ φ hexact
  simpa only [hF, hF₀] using h

end Specialization

end PaperVerification.PowerOperators
