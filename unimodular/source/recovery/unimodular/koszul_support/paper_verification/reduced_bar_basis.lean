module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.AugmentedAlgebraBasis
public import Mathlib.Tactic.Abel

/-!
# The actual normalized bar differential in a positive algebra basis

A basis word denotes a tensor of augmentation-ideal basis vectors. The
map merges adjacent tensor factors using their actual multiplication
coefficients and alternating signs. Associativity of the original algebra
proves that its square is zero. These are genuine coefficient formulas;
no differential or complex identity is supplied as an assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.ReducedBarBasis

open scoped BigOperators
open AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

local notation "W" => List I →₀ K

def prepend (i : I) : W →ₗ[K] W :=
  Finsupp.linearCombination K (fun L => Finsupp.single (i::L) 1)

def appendTail (L : List I) : (I →₀ K) →ₗ[K] W :=
  Finsupp.linearCombination K (fun i => Finsupp.single (i::L) 1)

@[simp] theorem prefix_single (i : I) (L : List I) (c : K) :
    prepend i (Finsupp.single L c : W)=Finsupp.single (i::L) c := by
  simp only [prepend,Finsupp.linearCombination_single,Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem appendTail_single (L : List I) (i : I) (c : K) :
    appendTail L (Finsupp.single i c : I →₀ K)=Finsupp.single (i::L) c := by
  simp only [appendTail,Finsupp.linearCombination_single,Finsupp.smul_single,smul_eq_mul,mul_one]

def mergeBasis (i : I) : List I → W
  | [] => 0
  | j::L => appendTail L (productCoefficients B i j)

def merge (i : I) : W →ₗ[K] W := Finsupp.linearCombination K (mergeBasis B i)

@[simp] theorem merge_single (i : I) (L : List I) (c : K) :
    merge B i (Finsupp.single L c)=c • mergeBasis B i L :=
  Finsupp.linearCombination_single _ _ _

/-- Multiplication of the first tensor factor by a fixed augmentation
basis vector, written as an actual finite sum of prepend maps. -/
theorem merge_prefix (i j : I) (z : W) :
    merge B i (prepend j z)=
      (productCoefficients B i j).sum (fun a c => c • prepend a z) := by
  have he : (merge B i).comp (prepend j)=
      Finsupp.linearCombination K (fun a => prepend (K := K) a) (productCoefficients B i j) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,prefix_single,merge_single,mergeBasis,
      Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
      LinearMap.smul_apply,prefix_single,appendTail,Finsupp.linearCombination_apply]
    simp only [Finset.smul_sum,Finsupp.smul_single,smul_eq_mul,mul_one]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_comm]
  have h := LinearMap.congr_fun he z
  simpa only [LinearMap.comp_apply,Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
    LinearMap.smul_apply] using h

include hunit hε in
/-- Successive first-factor multiplications retain the original algebra's
associativity, including all actual structure coefficients. -/
theorem merge_merge (i j : I) (z : W) :
    merge B i (merge B j z)=
      (productCoefficients B i j).sum (fun a c => c • merge B a z) := by
  have he : (merge B i).comp (merge B j)=
      Finsupp.linearCombination K (merge B) (productCoefficients B i j) := by
    apply Finsupp.lhom_ext
    intro L c
    cases L with
    | nil => simp only [LinearMap.comp_apply,merge_single,mergeBasis,smul_zero,map_zero,
        Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
        LinearMap.smul_apply,Finset.sum_const_zero]
    | cons k L =>
        have h := congrArg (appendTail (K := K) L)
          (productCoefficients_associative ε B hunit hε i j k)
        simp only [Finsupp.sum,map_sum,map_smul] at h
        simp only [LinearMap.comp_apply,merge_single,mergeBasis,map_smul,
          appendTail,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,
          Finsupp.linearCombination_apply,LinearMap.sum_apply,LinearMap.smul_apply,
          Finset.smul_sum,smul_smul] at h ⊢
        simpa only [Finset.smul_sum,smul_smul,mul_comm,mul_left_comm,mul_assoc,one_mul,mul_one] using
          congrArg (c • ·) h.symm
  have h := LinearMap.congr_fun he z
  simpa only [LinearMap.comp_apply,Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
    LinearMap.smul_apply] using h

/-- The alternating sum of adjacent multiplication operations, defined
recursively on the actual positive-basis tensor word. -/
def differentialBasis : List I → W
  | [] => 0
  | i::L => merge B i (Finsupp.single L 1)-prepend i (differentialBasis L)

def differential : W →ₗ[K] W := Finsupp.linearCombination K (differentialBasis B)

@[simp] theorem differential_single (L : List I) (c : K) :
    differential B (Finsupp.single L c)=c • differentialBasis B L :=
  Finsupp.linearCombination_single _ _ _

theorem differential_prefix (i : I) (z : W) :
    differential B (prepend i z)=merge B i z-prepend i (differential B z) := by
  have he : (differential B).comp (prepend i)=
      merge B i-(prepend i).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,prefix_single,differential_single,
      differentialBasis,merge_single,map_smul,smul_sub,one_smul]
  exact LinearMap.congr_fun he z

include hunit hε in
/-- Associativity is exactly the commutation needed for the square-zero
bar differential. -/
theorem differential_merge (i : I) (z : W) :
    differential B (merge B i z)=merge B i (differential B z) := by
  have hprefix (j : I) (z : W) :
      differential B (merge B i (prepend j z))=merge B i (differential B (prepend j z)) := by
    rw [merge_prefix,differential_prefix,map_sub]
    simp only [Finsupp.sum,map_sum,map_smul,differential_prefix,smul_sub,
      Finset.sum_sub_distrib]
    have h₁ := merge_merge ε B hunit hε i j z
    have h₂ := merge_prefix B i j (differential B z)
    simpa only [Finsupp.sum] using congrArg₂ (fun x y : W ↦ x-y) h₁.symm h₂.symm
  have he : (differential B).comp (merge B i)=(merge B i).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    cases L with
    | nil => simp only [LinearMap.comp_apply,merge_single,mergeBasis,smul_zero,map_zero,
        differential_single,differentialBasis]
    | cons j L =>
        have h := hprefix j (Finsupp.single L c)
        simpa only [prefix_single,LinearMap.comp_apply] using h
  exact LinearMap.congr_fun he z

include hunit hε in
theorem differentialBasis_squared (L : List I) :
    differential B (differentialBasis B L)=0 := by
  induction L with
  | nil => exact map_zero _
  | cons i L ih =>
      rw [differentialBasis,map_sub,differential_merge ε B hunit hε,
        differential_prefix,differential_single,one_smul,ih,map_zero,sub_zero,sub_self]

include hunit hε in
/-- The literal adjacent-product differential squares to zero. -/
theorem differential_squared (z : W) : differential B (differential B z)=0 := by
  have he : (differential B).comp (differential B)=0 := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,differential_single,map_smul,
      differentialBasis_squared ε B hunit hε,smul_zero,LinearMap.zero_apply]
  exact LinearMap.congr_fun he z

/-- A two-tensor is sent to its actual product in the augmentation ideal. -/
theorem differential_pair (i j : I) :
    differential B (Finsupp.single [i,j] (1 : K))=
      (productCoefficients B i j).sum (fun a c => Finsupp.single [a] c) := by
  simp only [differential_single,one_smul,differentialBasis,merge_single,mergeBasis,
    smul_zero,map_zero,sub_zero,appendTail,Finsupp.linearCombination_apply,
    Finsupp.smul_single,smul_eq_mul,mul_one]

end PaperVerification.ReducedBarBasis
