module

public import PaperVerification.PowerDegreeActions

/-!
# Literal finite homogeneous Koszul matrices

The degree indices and their zero pieces are the same exact shifted monomial
sets used for the differential deformation. Here the maps are the ordinary
coefficient and alternating-matrix Koszul maps for an arbitrary homogeneous
family of degrees `m+i`. Exactness is obtained from the actual regular-sequence
Koszul theorem by projecting every preimage to its correct homogeneous piece.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Coordinates

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R

def tailDecodeLinear (m d : ℕ) : (TailDegreeIndex n m d → R) →ₗ[R] (Fin n → P) where
  toFun := tailDegreeDecode m d
  map_add' v w := by
    funext i
    exact (shiftedDecode (R := R) (n := n) (m+i.val) d).map_add _ _
  map_smul' a v := by
    funext i
    exact (shiftedDecode (R := R) (n := n) (m+i.val) d).map_smul a _

def syzygyDecodeLinear (m d : ℕ) :
    (SyzygyDegreeIndex n m d → R) →ₗ[R] (Fin n → Fin n → P) where
  toFun := syzygyDegreeDecode m d
  map_add' v w := by
    funext i j
    exact (shiftedDecode (R := R) (n := n) ((m+i.val)+(m+j.val)) d).map_add _ _
  map_smul' a v := by
    funext i j
    exact (shiftedDecode (R := R) (n := n) ((m+i.val)+(m+j.val)) d).map_smul a _

def tailEncodeLinear (m d : ℕ) : (Fin n → P) →ₗ[R] (TailDegreeIndex n m d → R) where
  toFun v a := (v a.1).coeff a.2.val
  map_add' v w := by ext a; exact MvPolynomial.coeff_add _ _ _
  map_smul' c v := by ext a; exact MvPolynomial.coeff_smul _ _ _

@[simp] theorem tailEncode_decode (m d : ℕ) (v : TailDegreeIndex n m d → R) :
    tailEncodeLinear m d (tailDegreeDecode m d v) = v := by
  ext a
  exact shiftedDecode_coeff _ _ _ _

theorem tailDegreeDecode_injective (m d : ℕ) :
    Function.Injective (tailDegreeDecode (R := R) (n := n) m d) := by
  intro v w h
  have hc := congrArg (tailEncodeLinear m d) h
  simpa only [tailEncode_decode] using hc

def ordinaryDegreeFirst (f : Fin n → P) (m d : ℕ) :
    (TailDegreeIndex n m d → R) →ₗ[R] (ShiftedExponent n 0 d → R) :=
  (shiftedEncode 0 d).comp
    (((KoszulSyzygies.coefficient f).restrictScalars R).comp (tailDecodeLinear m d))

def ordinaryDegreeSecond (f : Fin n → P) (m d : ℕ) :
    (SyzygyDegreeIndex n m d → R) →ₗ[R] (TailDegreeIndex n m d → R) :=
  (tailEncodeLinear m d).comp
    (((KoszulSyzygies.boundary f).restrictScalars R).comp (syzygyDecodeLinear m d))

def ordinaryFirstMatrix (f : Fin n → P) (m d : ℕ) :
    Matrix (ShiftedExponent n 0 d) (TailDegreeIndex n m d) R := by
  classical
  exact LinearMap.toMatrix' (ordinaryDegreeFirst f m d)

def ordinarySecondMatrix (f : Fin n → P) (m d : ℕ) :
    Matrix (TailDegreeIndex n m d) (SyzygyDegreeIndex n m d) R := by
  classical
  exact LinearMap.toMatrix' (ordinaryDegreeSecond f m d)

@[simp] theorem ordinaryFirstMatrix_mulVec (f : Fin n → P) (m d : ℕ)
    (v : TailDegreeIndex n m d → R) (a : ShiftedExponent n 0 d) :
    (ordinaryFirstMatrix f m d *ᵥ v) a =
      (KoszulSyzygies.coefficient f (tailDegreeDecode m d v)).coeff a.val := by
  classical
  rw [ordinaryFirstMatrix,LinearMap.toMatrix'_mulVec]
  rfl

@[simp] theorem ordinarySecondMatrix_mulVec (f : Fin n → P) (m d : ℕ)
    (v : SyzygyDegreeIndex n m d → R) (a : TailDegreeIndex n m d) :
    (ordinarySecondMatrix f m d *ᵥ v) a =
      (KoszulSyzygies.boundary f (syzygyDegreeDecode m d v) a.1).coeff a.2.val := by
  classical
  rw [ordinarySecondMatrix,LinearMap.toMatrix'_mulVec]
  rfl

theorem shiftedProjection_coefficient (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (v : Fin n → P) :
    shiftedProjection 0 d (KoszulSyzygies.coefficient f v) =
      KoszulSyzygies.coefficient f (fun i => shiftedProjection (m+i.val) d (v i)) := by
  simp only [KoszulSyzygies.coefficient_apply,map_sum,
    shiftedProjection_mul (hf _),Nat.zero_add]

theorem shiftedProjection_boundary (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (A : Fin n → Fin n → P) (i : Fin n) :
    shiftedProjection (m+i.val) d (KoszulSyzygies.boundary f A i) =
      KoszulSyzygies.boundary f
        (fun j k => shiftedProjection ((m+j.val)+(m+k.val)) d (A j k)) i := by
  simp only [KoszulSyzygies.boundary_apply,map_sum,mul_sub,map_sub]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (f j) (A j i),mul_comm (f j) (A i j),
    shiftedProjection_mul (hf j),shiftedProjection_mul (hf j)]
  simp only [mul_comm, Nat.add_comm (m+i.val) (m+j.val)]

theorem ordinaryCoefficient_mem_shiftedPiece (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (v : Fin n → P)
    (hv : ∀ i, v i ∈ shiftedPiece R n (m+i.val) d) :
    KoszulSyzygies.coefficient f v ∈ shiftedPiece R n 0 d := by
  have he : shiftedProjection 0 d (KoszulSyzygies.coefficient f v) =
      KoszulSyzygies.coefficient f v := by
    rw [shiftedProjection_coefficient f m d hf]
    congr 1
    funext i
    exact shiftedProjection_of_mem (hv i)
  rw [← he]
  exact shiftedProjection_mem _ _ _

theorem ordinaryBoundary_mem_shiftedPiece (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (A : Fin n → Fin n → P)
    (hA : ∀ i j, A i j ∈ shiftedPiece R n ((m+i.val)+(m+j.val)) d) (i : Fin n) :
    KoszulSyzygies.boundary f A i ∈ shiftedPiece R n (m+i.val) d := by
  have he : shiftedProjection (m+i.val) d (KoszulSyzygies.boundary f A i) =
      KoszulSyzygies.boundary f A i := by
    rw [shiftedProjection_boundary f m d hf]
    apply congrArg (fun B => KoszulSyzygies.boundary f B i)
    funext j k
    exact shiftedProjection_of_mem (hA j k)
  rw [← he]
  exact shiftedProjection_mem _ _ _

theorem shiftedDecode_ordinaryFirst (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (v : TailDegreeIndex n m d → R) :
    shiftedDecode 0 d (ordinaryFirstMatrix f m d *ᵥ v) =
      KoszulSyzygies.coefficient f (tailDegreeDecode m d v) := by
  rw [show ordinaryFirstMatrix f m d *ᵥ v =
    (fun a => (KoszulSyzygies.coefficient f (tailDegreeDecode m d v)).coeff a.val) from
      funext (ordinaryFirstMatrix_mulVec f m d v)]
  exact shiftedDecode_coeffs _ _ _
    (ordinaryCoefficient_mem_shiftedPiece f m d hf _ (fun _ => shiftedDecode_mem _ _ _))

theorem tailDegreeDecode_ordinarySecond (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) (v : SyzygyDegreeIndex n m d → R) :
    tailDegreeDecode m d (ordinarySecondMatrix f m d *ᵥ v) =
      KoszulSyzygies.boundary f (syzygyDegreeDecode m d v) := by
  funext i
  change shiftedDecode (m+i.val) d _ = _
  simp only [ordinarySecondMatrix_mulVec]
  exact shiftedDecode_coeffs _ _ _
    (ordinaryBoundary_mem_shiftedPiece f m d hf _ (fun _ _ => shiftedDecode_mem _ _ _) i)

theorem ordinaryMatrices_complex (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val)) :
    ordinaryFirstMatrix f m d * ordinarySecondMatrix f m d = 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  apply shiftedDecode_injective 0 d
  rw [shiftedDecode_ordinaryFirst f m d hf,tailDegreeDecode_ordinarySecond f m d hf,
    KoszulSyzygies.coefficient_boundary,map_zero]

set_option maxHeartbeats 800000 in
theorem ordinaryMatrices_exact (f : Fin n → P) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f)) :
    LinearMap.range (ordinarySecondMatrix f m d).mulVecLin =
      LinearMap.ker (ordinaryFirstMatrix f m d).mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul,ordinaryMatrices_complex f m d hf,Matrix.mulVecLin_zero]
  · intro v hv
    have hz : KoszulSyzygies.coefficient f (tailDegreeDecode m d v) = 0 := by
      rw [← shiftedDecode_ordinaryFirst f m d hf]
      change ordinaryFirstMatrix f m d *ᵥ v = 0 at hv
      rw [hv,map_zero]
    obtain ⟨B,hB⟩ := (KoszulSyzygies.kernel_eq_boundary_range f hregular).le hz
    let A := fun i j => shiftedProjection ((m+i.val)+(m+j.val)) d (B i j)
    let z : SyzygyDegreeIndex n m d → R := fun a => (A a.1 a.2.1).coeff a.2.2.val
    have hzA : syzygyDegreeDecode m d z = A := by
      funext i j
      change shiftedDecode ((m+i.val)+(m+j.val)) d
        (fun a => (A i j).coeff a.val) = A i j
      exact shiftedDecode_coeffs _ _ (A i j) (shiftedProjection_mem _ _ (B i j))
    refine ⟨z, ?_⟩
    apply tailDegreeDecode_injective m d
    rw [Matrix.mulVecLin_apply,tailDegreeDecode_ordinarySecond f m d hf,hzA]
    funext i
    change KoszulSyzygies.boundary f
      (fun j k => shiftedProjection ((m+j.val)+(m+k.val)) d (B j k)) i = _
    rw [← shiftedProjection_boundary f m d hf,hB]
    exact shiftedProjection_of_mem (shiftedDecode_mem _ _ _)

end Coordinates

section Maps

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem map_ordinaryCoefficient (φ : R →+* S) (f v : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (KoszulSyzygies.coefficient f v) =
      KoszulSyzygies.coefficient (fun i => MvPolynomial.map φ (f i))
        (fun i => MvPolynomial.map φ (v i)) := by
  simp only [KoszulSyzygies.coefficient_apply,map_sum,map_mul]

theorem map_ordinaryBoundary (φ : R →+* S) (f : Fin n → MvPolynomial (Fin n) R)
    (A : Fin n → Fin n → MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial.map φ (KoszulSyzygies.boundary f A i) =
      KoszulSyzygies.boundary (fun j => MvPolynomial.map φ (f j))
        (fun j k => MvPolynomial.map φ (A j k)) i := by
  simp only [KoszulSyzygies.boundary_apply,map_sum,map_mul,map_sub]

theorem map_ordinaryFirstMatrix (φ : R →+* S) (f : Fin n → MvPolynomial (Fin n) R)
    (m d : ℕ) :
    (ordinaryFirstMatrix f m d).map φ = ordinaryFirstMatrix (fun i => MvPolynomial.map φ (f i)) m d := by
  classical
  ext a b
  simp only [ordinaryFirstMatrix, Matrix.map_apply, LinearMap.toMatrix'_apply]
  change φ ((KoszulSyzygies.coefficient f (tailDegreeDecode m d (Pi.single b 1))).coeff a.val) =
    (KoszulSyzygies.coefficient (fun i => MvPolynomial.map φ (f i))
      (tailDegreeDecode m d (Pi.single b 1))).coeff a.val
  rw [← coeff_map,map_ordinaryCoefficient]
  apply congrArg (fun v => (KoszulSyzygies.coefficient
    (fun i => MvPolynomial.map φ (f i)) v).coeff a.val)
  funext i
  simp only [tailDegreeDecode, map_shiftedDecode]
  apply congrArg (shiftedDecode (m+i.val) d)
  funext j
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

theorem map_ordinarySecondMatrix (φ : R →+* S) (f : Fin n → MvPolynomial (Fin n) R)
    (m d : ℕ) :
    (ordinarySecondMatrix f m d).map φ = ordinarySecondMatrix (fun i => MvPolynomial.map φ (f i)) m d := by
  classical
  ext a b
  simp only [ordinarySecondMatrix, Matrix.map_apply, LinearMap.toMatrix'_apply]
  change φ ((KoszulSyzygies.boundary f (syzygyDegreeDecode m d (Pi.single b 1)) a.1).coeff a.2.val) =
    (KoszulSyzygies.boundary (fun i => MvPolynomial.map φ (f i))
      (syzygyDegreeDecode m d (Pi.single b 1)) a.1).coeff a.2.val
  rw [← coeff_map,map_ordinaryBoundary]
  apply congrArg (fun v => (KoszulSyzygies.boundary
    (fun i => MvPolynomial.map φ (f i)) v a.1).coeff a.2.val)
  funext i j
  simp only [syzygyDegreeDecode, map_shiftedDecode]
  apply congrArg (shiftedDecode ((m+i.val)+(m+j.val)) d)
  funext k
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

end Maps

end PaperVerification.PowerOperators
