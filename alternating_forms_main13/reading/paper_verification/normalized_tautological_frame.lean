module

public import PaperVerification.NormalizedTautologicalKernel

/-!
# The explicit free frame of the exterior-incidence kernel

The equations are the augmented determinants, and the linear equivalence is
the original row map with pivot projection as inverse. This construction is
valid over an arbitrary commutative ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace PaperVerification.NormalizedTautologicalKernel

variable {R : Type*} [CommRing R] {s n : ℕ}

theorem incidence_eq_sum (A : Matrix (Fin s) (Fin n) R)
    (v : Fin n → R) (J : Fin (s+1) → Fin n) :
    incidence A v J = ∑ q : Fin (s+1), (-1 : R)^q.val * v (J q) *
      Matrix.det (A.submatrix id (fun z => J (q.succAbove z))) := by
  rw [incidence, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [augmented, Matrix.submatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ,
    id_eq]

/-- The actual exterior-incidence equations, assembled as a linear map. -/
def incidenceLinearMap (A : Matrix (Fin s) (Fin n) R) :
    (Fin n → R) →ₗ[R] ((Fin (s+1) → Fin n) → R) where
  toFun v J := incidence A v J
  map_add' v w := by
    funext J
    simp only [incidence_eq_sum, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' r v := by
    funext J
    simp only [incidence_eq_sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring

/-- The normalized rows give a free frame of the genuine incidence kernel. -/
def incidenceKernelEquiv (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1) :
    (Fin s → R) ≃ₗ[R] (incidenceLinearMap A).ker where
  toFun x := ⟨x ᵥ* A, by
    apply LinearMap.mem_ker.mpr
    funext J
    exact incidence_rowCombination A x J⟩
  invFun v i := v.val (p i)
  left_inv x := by
    funext i
    exact rowCombination_pivot A p hp x i
  right_inv v := by
    apply Subtype.ext
    have h : ∀ J, incidence A v.val J=0 := fun J =>
      congrFun (LinearMap.mem_ker.mp v.property) J
    exact ((incidence_zero_iff_rowCombination A p hp v.val).mp h).symm
  map_add' x y := by
    apply Subtype.ext
    exact (A.vecMulLinear).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (A.vecMulLinear).map_smul r x

@[simp] theorem incidenceKernelEquiv_apply (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1) (x : Fin s → R) :
    (incidenceKernelEquiv A p hp x).val=x ᵥ* A := rfl

@[simp] theorem incidenceKernelEquiv_symm_apply (A : Matrix (Fin s) (Fin n) R)
    (p : Fin s → Fin n) (hp : A.submatrix id p=1)
    (v : (incidenceLinearMap A).ker) (i : Fin s) :
    (incidenceKernelEquiv A p hp).symm v i=v.val (p i) := rfl

/-- Normalization is preserved by every coefficient-ring homomorphism. -/
theorem pivot_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1) : (A.map φ).submatrix id p=1 := by
  change φ.mapMatrix (A.submatrix id p)=1
  rw [hp,map_one]

/-- For any presentation of the same actual incidence equations, pivot
projection identifies its kernel with the free coordinate module. -/
theorem kernel_pivot_bijective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M ≃ₗ[R] (Fin n → R))
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p=1)
    (h : ∀ x, f x=0 ↔ ∀ J, incidence A (e x) J=0) :
    Function.Bijective (fun x : f.ker => fun i => e x.val (p i)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    have hx := (incidence_zero_iff_rowCombination A p hp (e x.val)).mp
      ((h x.val).mp (LinearMap.mem_ker.mp x.property))
    have hy := (incidence_zero_iff_rowCombination A p hp (e y.val)).mp
      ((h y.val).mp (LinearMap.mem_ker.mp y.property))
    rw [hx, hy]
    exact congrArg (fun c : Fin s → R => c ᵥ* A) hxy
  · intro c
    let v := e.symm (c ᵥ* A)
    have hv : f v=0 := (h v).mpr (by
      intro J
      change incidence A (e (e.symm (c ᵥ* A))) J=0
      rw [e.apply_symm_apply]
      exact incidence_rowCombination A c J)
    refine ⟨⟨v,LinearMap.mem_ker.mpr hv⟩,?_⟩
    funext i
    change e (e.symm (c ᵥ* A)) (p i)=c i
    rw [e.apply_symm_apply]
    exact rowCombination_pivot A p hp c i

end PaperVerification.NormalizedTautologicalKernel
