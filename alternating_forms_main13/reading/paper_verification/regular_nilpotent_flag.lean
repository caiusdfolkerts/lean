module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic

/-!
# Invariant subspaces of a single nilpotent Jordan chain

The dimension argument is independent of a choice of Jordan normal form.
A nilpotent endomorphism annihilates an invariant subspace after at most its
own dimension many powers. If the ambient kernels have the dimensions of a
single Jordan block, that invariant subspace must equal the corresponding
kernel. The concrete weighted shift below verifies those kernel dimensions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RegularNilpotentFlag

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Nilpotence on a finite-dimensional space is detected at its dimension. -/
theorem nilpotent_pow_finrank_eq_zero [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T) : T ^ Module.finrank K V = 0 := by
  obtain ⟨m,hm⟩ := hT
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  have h := Module.End.ker_pow_le_ker_pow_finrank T m
  simpa only [hm, LinearMap.ker_zero] using h

/-- Restricting a nilpotent map to an invariant subspace preserves nilpotence. -/
theorem nilpotent_restrict (T : Module.End K V) (hT : IsNilpotent T)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) :
    IsNilpotent (T.restrict hU) := by
  obtain ⟨m,hm⟩ := hT
  refine ⟨m,?_⟩
  rw [Module.End.pow_restrict m hU]
  ext x
  change (T^m) x = 0
  rw [hm, LinearMap.zero_apply]

/-- Any invariant `s`-plane of a nilpotent map lies in its `s`th kernel. -/
theorem invariant_le_ker_pow_finrank [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) :
    U  ≤  LinearMap.ker (T ^ Module.finrank K U) := by
  have hz := nilpotent_pow_finrank_eq_zero (T.restrict hU)
    (nilpotent_restrict T hT U hU)
  intro x hx
  change (T ^ Module.finrank K U) x = 0
  have h := congrArg (fun f : Module.End K U => (f ⟨x,hx⟩ : V)) hz
  rw [Module.End.pow_restrict (Module.finrank K U) hU] at h
  simpa only [LinearMap.coe_restrict_apply,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] using h

/-- The usual single-Jordan-block uniqueness statement, proved by dimensions. -/
theorem invariant_eq_ker_pow [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T) (s : ℕ)
    (hker : Module.finrank K (LinearMap.ker (T^s)) = s)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U)
    (hdim : Module.finrank K U = s) : U = LinearMap.ker (T^s) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · simpa only [hdim] using invariant_le_ker_pow_finrank T hT U hU
  · exact hdim.trans hker.symm

section WeightedShift

variable {n : ℕ}

/-- In coordinates ordered along a Jordan chain, nonzero coefficients may
rescale the arrows without changing the invariant subspaces. -/
def weightedShift (a : Fin n → K) : Module.End K (Fin n → K) where
  toFun v i := if h : i.val+1 < n then a i * v ⟨i.val+1,h⟩ else 0
  map_add' u v := by
    funext i
    by_cases h : i.val+1 < n <;> simp [h,mul_add]
  map_smul' r v := by
    funext i
    by_cases h : i.val+1 < n <;> simp [h,mul_left_comm]

@[simp] theorem weightedShift_apply (a : Fin n → K) (v : Fin n → K) (i : Fin n) :
    weightedShift a v i = if h : i.val+1 < n then a i * v ⟨i.val+1,h⟩ else 0 := rfl

@[simp] theorem weightedShift_single_zero {n : ℕ} (a : Fin (n+1) → K) :
    weightedShift a (Pi.single 0 1)=0 := by
  funext i
  rw [weightedShift_apply]
  split_ifs with h
  · have hz : (0 : Fin (n+1)) ≠ ⟨i.val+1,h⟩ := by
      intro he
      have he' := congrArg Fin.val he
      simp only [Fin.val_zero,Fin.val_mk] at he'
      omega
    simp only [Pi.single_apply,if_neg hz.symm,mul_zero,Pi.zero_apply]
  · rfl

@[simp] theorem weightedShift_single_succ {n : ℕ} (a : Fin (n+1) → K) (i : Fin n) :
    weightedShift a (Pi.single i.succ 1)=a i.castSucc • Pi.single i.castSucc 1 := by
  ext j
  by_cases h : j=i.castSucc
  · subst j
    simp [weightedShift_apply,Pi.single_apply,Fin.ext_iff,show i.val+1 < n+1 by omega]
  · have hv : j.val≠i.val := fun he => h (Fin.ext he)
    rw [weightedShift_apply]
    split_ifs <;> simp [Pi.single_apply,Fin.ext_iff,hv,Ne.symm hv]

/-- Once a power passes the end of the chain, its coordinate is zero. -/
theorem weightedShift_pow_apply_of_le (a : Fin n → K) (m : ℕ)
    (v : Fin n → K) (i : Fin n) (hi : n ≤ i.val+m) :
    ((weightedShift a)^m) v i = 0 := by
  induction m generalizing i with
  | zero => have := i.isLt; omega
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, weightedShift_apply]
    split_ifs with h
    · rw [ih ⟨i.val+1,h⟩ (by dsimp; omega), mul_zero]
    · rfl

/-- Before the end of the chain, every coefficient is a product of nonzero
arrow coefficients, so a coordinate vanishes exactly when its source does. -/
theorem weightedShift_pow_apply_eq_zero_iff (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ)
    (v : Fin n → K) (i : Fin n) (hi : i.val+m < n) :
    ((weightedShift a)^m) v i = 0 ↔ v ⟨i.val+m,hi⟩ = 0 := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, weightedShift_apply,
      dif_pos (show i.val+1 < n by omega), mul_eq_zero]
    simp only [ha i (by omega), false_or]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih ⟨i.val+1,by omega⟩ (by dsimp; omega)

/-- The kernel of each power is exactly the space supported on the initial
segment; this identifies actual vectors and actual linear kernels. -/
theorem weightedShift_pow_eq_zero_iff (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) (v : Fin n → K) :
    ((weightedShift a)^m) v = 0 ↔ ∀ j : Fin n, m ≤ j.val → v j = 0 := by
  constructor
  · intro h j hj
    let i : Fin n := ⟨j.val-m, by omega⟩
    have hi : i.val+m < n := by dsimp [i]; omega
    have hz : ((weightedShift a)^m) v i = 0 := congrFun h i
    have hsource := (weightedShift_pow_apply_eq_zero_iff a ha m v i hi).mp hz
    convert hsource using 1
    apply congrArg v
    apply Fin.ext
    dsimp [i]
    omega
  · intro h
    funext i
    by_cases hi : i.val+m < n
    · exact (weightedShift_pow_apply_eq_zero_iff a ha m v i hi).mpr
        (h ⟨i.val+m,hi⟩ (by dsimp; omega))
    · exact weightedShift_pow_apply_of_le a m v i (by omega)

theorem weightedShift_ker_pow (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) :
    LinearMap.ker ((weightedShift a)^m) =
      Pi.spanSubset K {i : Fin n | i.val < m} := by
  ext v
  rw [LinearMap.mem_ker, weightedShift_pow_eq_zero_iff a ha,
    Pi.mem_spanSubset_iff]
  simp only [Set.mem_setOf_eq, not_lt]

theorem weightedShift_nilpotent (a : Fin n → K) : IsNilpotent (weightedShift a) := by
  refine ⟨n,?_⟩
  apply LinearMap.ext
  intro v
  funext i
  change ((weightedShift a)^n) v i = 0
  exact weightedShift_pow_apply_of_le a n v i (by omega)

/-- The initial coordinate segment has its actual expected dimension. -/
theorem finrank_prefix (m : ℕ) (hm : m ≤ n) :
    Module.finrank K (Pi.spanSubset K {i : Fin n | i.val < m}) = m := by
  rw [Pi.dim_spanSubset, ← Nat.card_coe_set_eq]
  let e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun i => ⟨i.val.val,i.property⟩
      invFun := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hm⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_fin m)

/-- Initial coordinate spaces are invariant under every weighted lowering map. -/
theorem weightedShift_prefix_invariant (a : Fin n → K) (m : ℕ)
    (v : Fin n → K) (hv : v ∈ Pi.spanSubset K {i : Fin n | i.val < m}) :
    weightedShift a v ∈ Pi.spanSubset K {i : Fin n | i.val < m} := by
  rw [Pi.mem_spanSubset_iff] at hv ⊢
  intro i hi
  rw [weightedShift_apply]
  split_ifs with h
  · have hige : m ≤ i.val := by simpa only [Set.mem_setOf_eq,not_lt] using hi
    rw [hv ⟨i.val+1,h⟩ (by simp only [Set.mem_setOf_eq,not_lt]; omega),mul_zero]
  · rfl

/-- Every invariant subspace of a weighted single Jordan chain is the initial
coordinate subspace of the same dimension. -/
theorem weightedShift_invariant_subspace_unique (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) (hm : m ≤ n)
    (U : Submodule K (Fin n → K))
    (hU : ∀ x ∈ U, weightedShift a x ∈ U)
    (hdim : Module.finrank K U = m) :
    U = Pi.spanSubset K {i : Fin n | i.val < m} := by
  rw [← weightedShift_ker_pow a ha]
  apply invariant_eq_ker_pow _ (weightedShift_nilpotent a) m _ U hU hdim
  rw [weightedShift_ker_pow a ha, finrank_prefix m hm]

end WeightedShift

end PaperVerification.RegularNilpotentFlag
