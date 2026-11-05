module

public import PaperVerification.FermionDefinitions
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Literal wreath actions and the original invariant-generated ideal

The ambient algebra is the paper's actual
polynomial tensor exterior algebra. The acting group is the semidirect
product of its n independent r-th-root scalings with the full permutation
group. Its actions are defined on the original generators, before any
moment ideal or quotient is used. Positive invariants mean invariant
polynomials with zero augmentation, not elements defined to lie in the
proposed moment ideal.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.Coinvariants

section Ambient

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The original even generator in the actual tensor algebra. -/
def even (i : Fin n) : SuperRing R n :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (MvPolynomial.X i)

/-- Algebra maps are determined by the actual three families of generators. -/
theorem superAlgHom_ext {A : Type*} [Ring A] [Algebra R A]
    (f g : SuperRing R n →ₐ[R] A)
    (hx : ∀ i,f (even i)=g (even i))
    (ht : ∀ i,f (theta R n i)=g (theta R n i))
    (hz : ∀ i,f (xi R n i)=g (xi R n i)) : f=g := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    exact hx i
  · apply ExteriorAlgebra.hom_ext
    apply (Pi.basisFun R (OddIndex n)).ext
    intro j
    cases j with
    | inl i =>
        simpa only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
          AlgHom.restrictScalars_apply,Pi.basisFun_apply,theta] using ht i
    | inr i =>
        simpa only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
          AlgHom.restrictScalars_apply,Pi.basisFun_apply,xi] using hz i

theorem superAlgEquiv_ext (f g : SuperRing R n ≃ₐ[R] SuperRing R n)
    (hx : ∀ i,f (even i)=g (even i))
    (ht : ∀ i,f (theta R n i)=g (theta R n i))
    (hz : ∀ i,f (xi R n i)=g (xi R n i)) : f=g := by
  have h := superAlgHom_ext f.toAlgHom g.toAlgHom hx ht hz
  exact AlgEquiv.ext (fun x ↦ DFunLike.congr_fun h x)

/-- The exterior algebra map induced by an actual invertible odd linear map. -/
def exteriorEquiv (e : OddModule R n ≃ₗ[R] OddModule R n) :
    ExteriorAlgebra R (OddModule R n) ≃ₐ[R] ExteriorAlgebra R (OddModule R n) :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
    (ExteriorAlgebra.map e.symm.toLinearMap)
    (by
      apply ExteriorAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        ExteriorAlgebra.map_apply_ι,AlgHom.id_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply])
    (by
      apply ExteriorAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        ExteriorAlgebra.map_apply_ι,AlgHom.id_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply])

@[simp] theorem exteriorEquiv_ι (e : OddModule R n ≃ₗ[R] OddModule R n)
    (v : OddModule R n) :
    exteriorEquiv e (ExteriorAlgebra.ι R v)=ExteriorAlgebra.ι R (e v) :=
  ExteriorAlgebra.map_apply_ι e.toLinearMap v

/-- Simultaneous permutation of both original odd families. -/
def oddPermutation (σ : Equiv.Perm (Fin n)) : OddModule R n ≃ₗ[R] OddModule R n :=
  LinearEquiv.piCongrLeft' R (fun _ : OddIndex n ↦ R) (σ.sumCongr σ)

@[simp] theorem oddPermutation_single (σ : Equiv.Perm (Fin n)) (j : OddIndex n) :
    oddPermutation (R := R) σ (Pi.single j 1)=Pi.single ((σ.sumCongr σ) j) 1 := by
  funext k
  change (Pi.single j (1 : R) : OddModule R n) ((σ.sumCongr σ).symm k)=
    (Pi.single ((σ.sumCongr σ) j) (1 : R) : OddModule R n) k
  by_cases h : k=(σ.sumCongr σ) j
  · subst k; simp
  · have h' : (σ.sumCongr σ).symm k≠j := by
      intro he
      exact h (by simpa only [Equiv.apply_symm_apply] using congrArg (σ.sumCongr σ) he)
    rw [Pi.single_eq_of_ne h',Pi.single_eq_of_ne h]

def permutation (σ : Equiv.Perm (Fin n)) : SuperRing R n ≃ₐ[R] SuperRing R n :=
  Algebra.TensorProduct.congr (R := R) (S := R)
    (MvPolynomial.renameEquiv R σ) (exteriorEquiv (oddPermutation σ))

@[simp] theorem permutation_even (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutation (R := R) σ (even i)=even (σ i) := by
  simp only [permutation,even,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,map_one]

@[simp] theorem permutation_theta (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutation (R := R) σ (theta R n i)=theta R n (σ i) := by
  simp only [permutation,theta,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
    AlgEquiv.coe_toAlgHom,exteriorEquiv_ι,oddPermutation_single,
    Equiv.sumCongr_apply,Sum.map_inl]

@[simp] theorem permutation_xi (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutation (R := R) σ (xi R n i)=xi R n (σ i) := by
  simp only [permutation,xi,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
    AlgEquiv.coe_toAlgHom,exteriorEquiv_ι,oddPermutation_single,
    Equiv.sumCongr_apply,Sum.map_inr]

@[simp] theorem permutation_one : permutation (R := R) (n := n) 1=1 := by
  apply superAlgEquiv_ext <;> intro i <;> simp

theorem permutation_mul (σ τ : Equiv.Perm (Fin n)) :
    permutation (R := R) (σ*τ)=permutation σ*permutation τ := by
  apply superAlgEquiv_ext <;> intro i <;>
    simp only [AlgEquiv.mul_apply,permutation_even,permutation_theta,permutation_xi,
      Equiv.Perm.coe_mul,Function.comp_apply]

def permutationAction : Equiv.Perm (Fin n) →* (SuperRing R n ≃ₐ[R] SuperRing R n) where
  toFun := permutation
  map_one' := permutation_one
  map_mul' := permutation_mul

/-- Literal polynomial scaling; all coefficients of the base ring are fixed. -/
def polynomialScale (c : Fin n → Rˣ) : PolynomialRing R n →ₐ[R] PolynomialRing R n :=
  MvPolynomial.aeval (fun i ↦ MvPolynomial.C (c i : R)*MvPolynomial.X i)

@[simp] theorem polynomialScale_X (c : Fin n → Rˣ) (i : Fin n) :
    polynomialScale c (MvPolynomial.X i)=MvPolynomial.C (c i : R)*MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem polynomialScale_C (c : Fin n → Rˣ) (a : R) :
    polynomialScale c (MvPolynomial.C a)=MvPolynomial.C a :=
  MvPolynomial.aeval_C _ _

def polynomialScaleEquiv (c : Fin n → Rˣ) :
    PolynomialRing R n ≃ₐ[R] PolynomialRing R n :=
  AlgEquiv.ofAlgHom (polynomialScale c) (polynomialScale c⁻¹)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply,polynomialScale_X,map_mul,polynomialScale_C,
        AlgHom.id_apply,Pi.inv_apply]
      rw [←mul_assoc,←MvPolynomial.C_mul]
      simp)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply,polynomialScale_X,map_mul,polynomialScale_C,
        AlgHom.id_apply,Pi.inv_apply]
      rw [←mul_assoc,←MvPolynomial.C_mul]
      simp)

/-- Independent unit scaling on the original odd coordinates. -/
def oddScale (c : OddIndex n → Rˣ) : OddModule R n ≃ₗ[R] OddModule R n where
  toFun v j := (c j : R)*v j
  invFun v j := (((c j)⁻¹ : Rˣ) : R)*v j
  left_inv v := by funext j; simp [mul_assoc]
  right_inv v := by funext j; simp [mul_assoc]
  map_add' v w := by funext j; simp only [Pi.add_apply,mul_add]
  map_smul' a v := by funext j; simp [smul_eq_mul,mul_assoc,mul_left_comm]

@[simp] theorem oddScale_single (c : OddIndex n → Rˣ) (j : OddIndex n) :
    oddScale c (Pi.single j 1)=(c j : R) • Pi.single j 1 := by
  funext k
  by_cases h : k=j
  · subst k; simp [oddScale,Pi.single_apply]
  · simp [oddScale,Pi.single_apply,h,Ne.symm h]

/-- Characters p and q on theta and xi, and character one on x. -/
def diagonal (p q : ℕ) (c : Fin n → Rˣ) : SuperRing R n ≃ₐ[R] SuperRing R n :=
  Algebra.TensorProduct.congr (R := R) (S := R) (polynomialScaleEquiv c)
    (exteriorEquiv (oddScale (Sum.elim (fun i ↦ c i^p) (fun i ↦ c i^q))))

@[simp] theorem diagonal_even (p q : ℕ) (c : Fin n → Rˣ) (i : Fin n) :
    diagonal p q c (even i)=(c i : R) • even i := by
  simp only [diagonal,even,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
    AlgEquiv.coe_toAlgHom]
  change polynomialScale c (MvPolynomial.X i) ⊗ₜ[R]
      (1 : ExteriorAlgebra R (OddModule R n))=_
  rw [polynomialScale_X,←MvPolynomial.smul_eq_C_mul,TensorProduct.smul_tmul']

@[simp] theorem diagonal_theta (p q : ℕ) (c : Fin n → Rˣ) (i : Fin n) :
    diagonal p q c (theta R n i)=(c i : R)^p • theta R n i := by
  simp only [diagonal,theta,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
    AlgEquiv.coe_toAlgHom,exteriorEquiv_ι,oddScale_single,map_smul,
    TensorProduct.tmul_smul,Sum.elim_inl,Units.val_pow_eq_pow_val]

@[simp] theorem diagonal_xi (p q : ℕ) (c : Fin n → Rˣ) (i : Fin n) :
    diagonal p q c (xi R n i)=(c i : R)^q • xi R n i := by
  simp only [diagonal,xi,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
    AlgEquiv.coe_toAlgHom,exteriorEquiv_ι,oddScale_single,map_smul,
    TensorProduct.tmul_smul,Sum.elim_inr,Units.val_pow_eq_pow_val]

@[simp] theorem diagonal_one (p q : ℕ) : diagonal (R := R) (n := n) p q 1=1 := by
  apply superAlgEquiv_ext <;> intro i <;> simp

theorem diagonal_mul (p q : ℕ) (c d : Fin n → Rˣ) :
    diagonal p q (c*d)=diagonal p q c*diagonal p q d := by
  apply superAlgEquiv_ext <;> intro i <;>
    simp only [AlgEquiv.mul_apply,diagonal_even,diagonal_theta,diagonal_xi,
      map_smul,smul_smul,Pi.mul_apply,Units.val_mul,mul_pow] <;>
    congr 1 <;> ring

/-- The semidirect-product commutation relation is verified on original generators. -/
theorem permutation_diagonal (p q : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ) :
    permutation σ*diagonal p q c=
      diagonal p q (fun i ↦ c (σ.symm i))*permutation (R := R) σ := by
  apply superAlgEquiv_ext <;> intro i <;>
    simp only [AlgEquiv.mul_apply,diagonal_even,diagonal_theta,diagonal_xi,
      permutation_even,permutation_theta,permutation_xi,map_smul,Equiv.symm_apply_apply]

/-- The connected augmentation sets every original even and odd generator to zero. -/
def augmentation : SuperRing R n →ₐ[R] R :=
  Algebra.TensorProduct.lift (MvPolynomial.aeval (fun _ : Fin n ↦ (0 : R)))
    (ExteriorAlgebra.lift R ⟨0,fun _ ↦ by simp⟩)
      (fun _ _ ↦ Commute.all _ _)

@[simp] theorem augmentation_even (i : Fin n) : augmentation (even (R := R) i)=0 := by
  simp [augmentation,even,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.lift_tmul]

@[simp] theorem augmentation_theta (i : Fin n) : augmentation (theta R n i)=0 := by
  simp [augmentation,theta,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul,ExteriorAlgebra.lift_ι_apply]

@[simp] theorem augmentation_xi (i : Fin n) : augmentation (xi R n i)=0 := by
  simp [augmentation,xi,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul,ExteriorAlgebra.lift_ι_apply]

end Ambient

section Wreath

variable {G : Type*} [Group G] {n : ℕ}

/-- The actual permutation action on n independent diagonal factors. -/
def coordinatePermutation (σ : Equiv.Perm (Fin n)) : MulAut (Fin n → G) where
  toFun c i := c (σ.symm i)
  invFun c i := c (σ i)
  left_inv c := by funext i; simp
  right_inv c := by funext i; simp
  map_mul' c d := rfl

def coordinatePermutationAction : Equiv.Perm (Fin n) →* MulAut (Fin n → G) where
  toFun := coordinatePermutation
  map_one' := by ext c i; rfl
  map_mul' σ τ := by ext c i; rfl

variable (R : Type*) [CommRing R] (n r : ℕ)

/-- The standard wreath group mu_r^n semidirect S_n, not an assumed action. -/
abbrev WreathGroup :=
  (Fin n → rootsOfUnity r R) ⋊[coordinatePermutationAction] Equiv.Perm (Fin n)

variable {R n r}

/-- Original algebra action with prescribed exterior characters. -/
def wreathAction (p q : ℕ) : WreathGroup R n r →*
    (SuperRing R n ≃ₐ[R] SuperRing R n) where
  toFun g := diagonal p q (fun i ↦ (g.left i : Rˣ))*permutation g.right
  map_one' := by
    change diagonal p q (1 : Fin n → Rˣ)*permutation (1 : Equiv.Perm (Fin n))=1
    rw [diagonal_one,permutation_one,mul_one]
  map_mul' g h := by
    change diagonal p q
      (fun i ↦ (g.left i : Rˣ)*(h.left (g.right.symm i) : Rˣ)) *
        permutation (g.right*h.right)=
      (diagonal p q (fun i ↦ (g.left i : Rˣ))*permutation g.right)*
        (diagonal p q (fun i ↦ (h.left i : Rˣ))*permutation h.right)
    rw [show (fun i ↦ (g.left i : Rˣ)*(h.left (g.right.symm i) : Rˣ))=
      (fun i ↦ (g.left i : Rˣ))*(fun i ↦ (h.left (g.right.symm i) : Rˣ)) from rfl,
      diagonal_mul,permutation_mul]
    simp only [mul_assoc]
    congr 1
    rw [←mul_assoc,←permutation_diagonal p q g.right (fun i ↦ (h.left i : Rˣ)),
      mul_assoc]

@[simp] theorem wreathAction_even (p q : ℕ) (g : WreathGroup R n r) (i : Fin n) :
    wreathAction p q g (even i)=((g.left (g.right i) : Rˣ) : R) • even (g.right i) := by
  simp only [wreathAction,MonoidHom.coe_mk,OneHom.coe_mk,AlgEquiv.mul_apply,
    permutation_even,diagonal_even]

@[simp] theorem wreathAction_theta (p q : ℕ) (g : WreathGroup R n r) (i : Fin n) :
    wreathAction p q g (theta R n i)=
      ((g.left (g.right i) : Rˣ) : R)^p • theta R n (g.right i) := by
  simp only [wreathAction,MonoidHom.coe_mk,OneHom.coe_mk,AlgEquiv.mul_apply,
    permutation_theta,diagonal_theta]

@[simp] theorem wreathAction_xi (p q : ℕ) (g : WreathGroup R n r) (i : Fin n) :
    wreathAction p q g (xi R n i)=
      ((g.left (g.right i) : Rˣ) : R)^q • xi R n (g.right i) := by
  simp only [wreathAction,MonoidHom.coe_mk,OneHom.coe_mk,AlgEquiv.mul_apply,
    permutation_xi,diagonal_xi]

/-- On the actual group of r-th roots, exponent `r-a` is the inverse
of character `a`. No field or invertibility hypothesis on r is needed. -/
theorem rootOfUnity_pow_sub_eq_inv_pow {a : ℕ} (har : a ≤ r)
    (ζ : rootsOfUnity r R) :
    (ζ : Rˣ)^(r-a)=((ζ : Rˣ)^a)⁻¹ := by
  have hζ : (ζ : Rˣ)^r=1 := (mem_rootsOfUnity r (ζ : Rˣ)).mp ζ.property
  rw [pow_sub (ζ : Rˣ) har,hζ,one_mul]

/-- The original xi generator carries exactly the signed integer character
`-a` printed in Section 8.1, including the permutation of its index. -/
theorem wreathAction_opposite_xi {a : ℕ} (har : a ≤ r)
    (g : WreathGroup R n r) (i : Fin n) :
    wreathAction a (r-a) g (xi R n i)=
      (((g.left (g.right i) : Rˣ)^(-(a : ℤ)) : Rˣ) : R) • xi R n (g.right i) := by
  have hpow : ((g.left (g.right i) : Rˣ) : R)^(r-a)=
      ((((g.left (g.right i) : Rˣ)^a)⁻¹ : Rˣ) : R) := by
    simpa only [Units.val_pow_eq_pow_val] using
      congrArg (fun u : Rˣ ↦ (u : R))
        (rootOfUnity_pow_sub_eq_inv_pow har (g.left (g.right i)))
  rw [wreathAction_xi,hpow,zpow_neg,zpow_natCast]

/-- The full, original positive invariant-generated ideal. It is defined
independently of every moment family and of the proposed basis theorem. -/
def positiveInvariantIdeal (p q : ℕ) : TwoSidedIdeal (SuperRing R n) :=
  TwoSidedIdeal.span {f | augmentation f=0 ∧
    ∀ g : WreathGroup R n r,wreathAction p q g f=f}

/-- The genuine invariant-theoretic coinvariant algebra for this action. -/
abbrev CoinvariantAlgebra (p q : ℕ) :=
  (positiveInvariantIdeal (R := R) (n := n) (r := r) p q).ringCon.Quotient

end Wreath
end PaperVerification.Fermion.Coinvariants
