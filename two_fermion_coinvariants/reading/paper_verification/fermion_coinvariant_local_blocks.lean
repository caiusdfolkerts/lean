module

public import PaperVerification.FermionCoinvariantActions
public import Mathlib.Data.Fintype.BigOperators
public import Lean.Elab.Tactic.Omega

/-!
# Actual local invariant blocks and the moment-ideal inclusion

This file proves that every original moment
generator is a genuine positive invariant for the independently defined
wreath action. The reverse ideal inclusion requires the full Reynolds and
occupied-index argument; it is not postulated here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.Coinvariants

variable {R : Type*} [CommRing R] {n r : ℕ}

def oddPart : MomentKind → Fin n → SuperRing R n
  | .polynomial,_ => 1
  | .theta,i => theta R n i
  | .xi,i => xi R n i
  | .mixed,i => theta R n i*xi R n i

def oddWeight (p q : ℕ) : MomentKind → ℕ
  | .polynomial => 0
  | .theta => p
  | .xi => q
  | .mixed => p+q

/-- The literal one-index block, including all four exterior possibilities. -/
def localBlock (d : ℕ) (a : MomentKind) (i : Fin n) : SuperRing R n :=
  even (R := R) i^d*oddPart a i

def blockSum (d : ℕ) (a : MomentKind) : SuperRing R n := ∑ i,localBlock d a i

@[simp] theorem permutation_oddPart (σ : Equiv.Perm (Fin n)) (a : MomentKind) (i : Fin n) :
    permutation (R := R) σ (oddPart a i)=oddPart a (σ i) := by
  cases a <;> simp only [oddPart,map_one,map_mul,permutation_theta,permutation_xi]

@[simp] theorem permutation_localBlock (σ : Equiv.Perm (Fin n))
    (d : ℕ) (a : MomentKind) (i : Fin n) :
    permutation (R := R) σ (localBlock d a i)=localBlock d a (σ i) := by
  simp only [localBlock,map_mul,map_pow,permutation_even,permutation_oddPart]

@[simp] theorem diagonal_oddPart (p q : ℕ) (c : Fin n → Rˣ)
    (a : MomentKind) (i : Fin n) :
    diagonal p q c (oddPart a i)=(c i : R)^oddWeight p q a • oddPart a i := by
  cases a <;> simp only [oddPart,oddWeight,map_one,map_mul,diagonal_theta,
    diagonal_xi,pow_zero,one_smul,pow_add,smul_mul_smul_comm]

@[simp] theorem diagonal_localBlock (p q : ℕ) (c : Fin n → Rˣ)
    (d : ℕ) (a : MomentKind) (i : Fin n) :
    diagonal p q c (localBlock d a i)=(c i : R)^(d+oddWeight p q a) • localBlock d a i := by
  simp only [localBlock,map_mul,map_pow,diagonal_even,diagonal_oddPart,
    smul_pow,smul_mul_smul_comm,pow_add]

@[simp] theorem wreathAction_localBlock (p q : ℕ) (g : WreathGroup R n r)
    (d : ℕ) (a : MomentKind) (i : Fin n) :
    wreathAction p q g (localBlock d a i)=
      ((g.left (g.right i) : Rˣ) : R)^(d+oddWeight p q a) • localBlock d a (g.right i) := by
  change diagonal p q (fun j ↦ (g.left j : Rˣ))
    (permutation g.right (localBlock d a i))=_
  rw [permutation_localBlock,diagonal_localBlock]

theorem root_pow_eq_one_of_dvd (z : rootsOfUnity r R) {d : ℕ} (hd : r∣d) :
    ((z : Rˣ) : R)^d=1 := by
  obtain ⟨k,rfl⟩ := hd
  rw [pow_mul,(mem_rootsOfUnity' r z.val).mp z.property,one_pow]

/-- The natural exponent `r-a` is exactly the character `-a` on the
original cyclic factor, not an additional character assumption. -/
theorem root_opposite_character {a : ℕ} (ha : a≤r) (z : rootsOfUnity r R) :
    (z : Rˣ)^(r-a)=((z : Rˣ)^a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [←pow_add,Nat.add_sub_of_le ha]
  exact (mem_rootsOfUnity r z.val).mp z.property

/-- The divisibility condition is exactly the local cyclic-character condition. -/
theorem blockSum_invariant (p q : ℕ) (d : ℕ) (a : MomentKind)
    (hd : r∣d+oddWeight p q a) (g : WreathGroup R n r) :
    wreathAction p q g (blockSum (R := R) (n := n) d a)=blockSum d a := by
  simp only [blockSum,map_sum,wreathAction_localBlock,
    root_pow_eq_one_of_dvd _ hd,one_smul]
  exact Equiv.sum_comp g.right (localBlock d a)

@[simp] theorem augmentation_localBlock (d : ℕ) (a : MomentKind) (i : Fin n)
    (hp : 0<d ∨ a≠.polynomial) : augmentation (localBlock (R := R) d a i)=0 := by
  cases a with
  | polynomial =>
      have hd : d≠0 := Nat.ne_of_gt (hp.resolve_right (by simp))
      simp only [localBlock,oddPart,map_mul,map_pow,map_one,augmentation_even,
        zero_pow hd,mul_one]
  | theta => simp only [localBlock,oddPart,map_mul,augmentation_theta,mul_zero]
  | xi => simp only [localBlock,oddPart,map_mul,augmentation_xi,mul_zero]
  | mixed => simp only [localBlock,oddPart,map_mul,augmentation_theta,
      augmentation_xi,mul_zero]

theorem blockSum_mem_positiveInvariantIdeal (p q : ℕ) (d : ℕ) (a : MomentKind)
    (hd : r∣d+oddWeight p q a) (hp : 0<d ∨ a≠.polynomial) :
    blockSum (R := R) (n := n) d a∈positiveInvariantIdeal (r := r) p q := by
  apply TwoSidedIdeal.subset_span
  refine ⟨?_,blockSum_invariant p q d a hd⟩
  simp only [blockSum,map_sum,augmentation_localBlock d a _ hp,Finset.sum_const_zero]

/-- The four exponents printed in Section 8.1, including the positive ordinary family. -/
def oppositeExponent (r a : ℕ) : MomentKind → ℕ → ℕ
  | .polynomial,k => r*(k+1)
  | .theta,k => r-a+r*k
  | .xi,k => a+r*k
  | .mixed,k => r*k

theorem oppositeExponent_weight_dvd (r a : ℕ) (ha : a≤r)
    (c : MomentKind) (k : ℕ) : r∣oppositeExponent r a c k+oddWeight a (r-a) c := by
  cases c <;> refine ⟨k+1,?_⟩ <;>
    simp only [oppositeExponent,oddWeight,Nat.mul_add,Nat.mul_one] <;> omega

theorem oppositeExponent_positive (r a : ℕ) (hr : 0<r)
    (c : MomentKind) (k : ℕ) : 0<oppositeExponent r a c k ∨ c≠.polynomial := by
  cases c
  · exact Or.inl (Nat.mul_pos hr (Nat.succ_pos k))
  all_goals exact Or.inr (by decide)

/-- The two-sided scalar action is the genuine polynomial inclusion. -/
theorem polynomial_smul_eq_even_mul (p : PolynomialRing R n) (x : SuperRing R n) :
    p • x=Algebra.TensorProduct.includeLeft (R := R) (S := R) p*x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero,mul_zero]
  | tmul a b =>
      simp only [TensorProduct.smul_tmul',smul_eq_mul,
        Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [smul_add,mul_add,hx,hy]

theorem moment_local_monomials (r : ℕ) (d : Fin n → ℕ)
    (v : Fin n → SuperRing R n) (k : ℕ) :
    moment (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)
      (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^d i • v i) k=
      ∑ i,even (R := R) i^(r*k+d i)*v i := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [←pow_mul,smul_smul,←pow_add,polynomial_smul_eq_even_mul,map_pow]
  rfl

def oppositeBaseExponent (r a : ℕ) : MomentKind → ℕ
  | .polynomial => r
  | .theta => r-a
  | .xi => a
  | .mixed => 0

theorem pairedCoefficients_opposite (r a : ℕ) (ha : a≤r)
    (c : MomentKind) (i : Fin n) :
    pairedCoefficients (fun _ : Fin n ↦ (1 : R))
      (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^a)
      (fun i ↦ (MvPolynomial.X i)^ (r-a)) c i=
      (MvPolynomial.X i : PolynomialRing R n)^oppositeBaseExponent r a c •
        oddPart (R := R) c i := by
  cases c with
  | polynomial =>
      simp only [pairedCoefficients,oppositeBaseExponent,oddPart,MvPolynomial.C_1,one_mul]
      rw [←pow_add,Nat.add_sub_of_le ha]
  | theta => rfl
  | xi => simp only [pairedCoefficients,oppositeBaseExponent,oddPart,MvPolynomial.C_1,one_mul]
  | mixed => simp only [pairedCoefficients,oppositeBaseExponent,oddPart,pow_zero,one_smul]

theorem paired_moment_eq_opposite_blockSum (r a : ℕ) (ha : a≤r)
    (c : MomentKind) (k : ℕ) :
    moment (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)
      (pairedCoefficients (fun _ : Fin n ↦ (1 : R))
        (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a)) c) k=
      blockSum (oppositeExponent r a c k) c := by
  have hcoeff := funext (pairedCoefficients_opposite (R := R) (n := n) r a ha c)
  rw [hcoeff,moment_local_monomials]
  unfold blockSum localBlock
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  cases c <;> simp [oppositeBaseExponent,oppositeExponent,Nat.mul_add,Nat.add_comm]

/-- Every paired moment generator is a genuine positive wreath invariant.
This is one direction of the intended equality, not a claim of completion. -/
theorem pairedMomentIdeal_le_positiveInvariantIdeal (r a : ℕ) (hr : 0<r) (ha : a≤r) :
    pairedIdeal (fun _ : Fin n ↦ (1 : R))
      (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)
      (fun i ↦ (MvPolynomial.X i)^a) (fun i ↦ (MvPolynomial.X i)^(r-a))≤
        positiveInvariantIdeal (R := R) (n := n) (r := r) a (r-a) := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨⟨c,k⟩,rfl⟩
  dsimp only
  rw [paired_moment_eq_opposite_blockSum r a ha]
  exact blockSum_mem_positiveInvariantIdeal a (r-a) _ c
    (oppositeExponent_weight_dvd r a ha c k) (oppositeExponent_positive r a hr c k)

/-- The strict-family exponents for trivial exterior cyclic characters. -/
def strictExponent (r : ℕ) : MomentKind → ℕ → ℕ
  | .polynomial,k => r*(k+1)
  | _,k => r*k

theorem strictCoefficients_one (r : ℕ) (c : MomentKind) (i : Fin n) :
    strictCoefficients (fun _ : Fin n ↦ (1 : R))
      (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r) c i=
      (MvPolynomial.X i : PolynomialRing R n)^(if c=.polynomial then r else 0) •
        oddPart (R := R) c i := by
  cases c <;> simp [strictCoefficients,oddPart]

theorem strict_moment_eq_blockSum (r : ℕ) (c : MomentKind) (k : ℕ) :
    moment (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)
      (strictCoefficients (fun _ : Fin n ↦ (1 : R))
        (fun i ↦ (MvPolynomial.X i)^r) c) k=
      blockSum (strictExponent r c k) c := by
  have hcoeff := funext (strictCoefficients_one (R := R) (n := n) r c)
  rw [hcoeff,moment_local_monomials]
  unfold blockSum localBlock
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  cases c <;> simp [strictExponent,Nat.mul_add]

/-- The strict moments also lie in the independently defined positive
invariant ideal, with both exterior characters genuinely trivial. -/
theorem strictMomentIdeal_le_positiveInvariantIdeal (r : ℕ) (hr : 0<r) :
    strictIdeal (fun _ : Fin n ↦ (1 : R))
      (fun i ↦ (MvPolynomial.X i : PolynomialRing R n)^r)≤
        positiveInvariantIdeal (R := R) (n := n) (r := r) 0 0 := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨⟨c,k⟩,rfl⟩
  dsimp only
  rw [strict_moment_eq_blockSum r c k]
  apply blockSum_mem_positiveInvariantIdeal 0 0 _ c
  · cases c <;> simp [strictExponent,oddWeight]
  · cases c
    · exact Or.inl (Nat.mul_pos hr (Nat.succ_pos k))
    all_goals exact Or.inr (by decide)

end PaperVerification.Fermion.Coinvariants
