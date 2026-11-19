module

public import PaperVerification.ReducedBarBasis
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Module.BigOperators

/-!
# The normalized free bar differential of an augmented algebra

The free module is indexed by words in the positive basis. Its differential
has the actual left multiplication term and the actual adjacent-product terms.
All coefficients come from the supplied algebra and its unit-plus-augmentation
basis; no differential identity or homological exactness is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BarFree

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

abbrev Words (I A : Type*) [Zero A] := List I →₀ A

/-- Extension of word coefficients along the actual algebra map. -/
def lift : Words I K →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun L ↦ Finsupp.single L 1)

@[simp] theorem lift_single (L : List I) (c : K) :
    lift (A := A) (Finsupp.single L c)=c • Finsupp.single L 1 :=
  Finsupp.linearCombination_single _ _ _

def prepend (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.lmapDomain A A (List.cons i)

@[simp] theorem prefix_single (i : I) (L : List I) (a : A) :
    prepend i (Finsupp.single L a)=Finsupp.single (i::L) a := by
  simp [prepend]

def frontBasis : List I → Words I A
  | [] => 0
  | i::L => Finsupp.single L (positiveVector B i)

/-- The term that multiplies the free coefficient by the first bar factor. -/
def front : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (frontBasis B)

@[simp] theorem front_single (L : List I) (a : A) :
    front B (Finsupp.single L a)=a • frontBasis B L :=
  Finsupp.linearCombination_single _ _ _

/-- The scalar extension of the actual positive-basis adjacent-product differential. -/
def internal : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.differentialBasis B L))

@[simp] theorem internal_single (L : List I) (a : A) :
    internal B (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.differentialBasis B L) :=
  Finsupp.linearCombination_single _ _ _

theorem lift_prefix (i : I) (z : Words I K) :
    lift (PaperVerification.ReducedBarBasis.prepend i z)=
      prepend i (lift (A := A) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,prefix_single]

theorem internal_lift (z : Words I K) :
    internal B (lift z)=lift (PaperVerification.ReducedBarBasis.differential B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [lift_single,LinearMap.map_smul_of_tower,internal_single,one_smul,
      PaperVerification.ReducedBarBasis.differential_single,map_smul]

theorem front_lift_prefix (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.prepend i z))=
      positiveVector B i • lift z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul]
    rw [smul_comm]
    congr 1
    simp only [Finsupp.smul_single,smul_eq_mul,mul_one]

theorem front_lift_appendTail (L : List I) (c : I →₀ K) :
    front B (lift (PaperVerification.ReducedBarBasis.appendTail L c))=
      Finsupp.single L (positiveCombination B c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.single_zero]
  | add c d hc hd => simp only [map_add,Finsupp.single_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul,
      positiveCombination,Finsupp.linearCombination_single,Finsupp.smul_single,
      smul_assoc,one_smul]

include hunit hε in
theorem front_lift_merge (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.merge B i z))=
      positiveVector B i • front B (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,
        lift_single,LinearMap.map_smul_of_tower,front_single,frontBasis]
    | cons j L =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,map_smul,
        LinearMap.map_smul_of_tower,front_lift_appendTail,
        product_expansion ε B hunit hε,lift_single,front_single,frontBasis,one_smul]
      rw [smul_comm]
      congr 1
      simp only [Finsupp.smul_single,smul_eq_mul]

include hunit hε in
theorem internal_squared (z : Words I A) : internal B (internal B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    rw [internal_single,map_smul,internal_lift,
      PaperVerification.ReducedBarBasis.differentialBasis_squared ε B hunit hε,
      map_zero,smul_zero]

include hunit hε in
/-- The first multiplication term and the internal terms satisfy the identity
that leaves exactly the square of the first multiplication term. -/
theorem front_internal (z : Words I A) :
    front B (internal B z)+internal B (front B z)=front B (front B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    rw [show front B (internal B z)+front B (internal B w)+
      (internal B (front B z)+internal B (front B w))=
      (front B (internal B z)+internal B (front B z))+
      (front B (internal B w)+internal B (front B w)) by abel,hz,hw]
  | single L a =>
    have h : front B (internal B (Finsupp.single L 1))+
        internal B (front B (Finsupp.single L 1))=
        front B (front B (Finsupp.single L 1)) := by
      cases L with
      | nil =>
        simp only [internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          front_single,frontBasis,map_zero,smul_zero,add_zero]
      | cons i L =>
        simp only [internal_single,one_smul,
          PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
          front_lift_merge ε B hunit hε,front_lift_prefix,
          front_single,frontBasis,map_smul,internal_single,one_smul,lift_single,
          LinearMap.map_smul_of_tower]
        abel
    have ha : Finsupp.single L a=a • (Finsupp.single L 1 : Words I A) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [ha]
    simp only [map_smul,←smul_add,h]

/-- The genuine normalized free bar differential, with the standard signs. -/
def differential : Words I A →ₗ[A] Words I A := front B-internal B

include hunit hε in
theorem differential_squared (z : Words I A) :
    differential B (differential B z)=0 := by
  change front B (front B z-internal B z)-
    internal B (front B z-internal B z)=0
  rw [map_sub,map_sub,internal_squared ε B hunit hε,sub_zero]
  have h := front_internal ε B hunit hε z
  rw [←h]
  abel

/-- The positive-part prepend used in the actual contracting homotopy. -/
def positivePrefix (L : List I) : A →ₗ[K] Words I A :=
  (Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)).comp
    (positiveCoordinates B)

/-- This map increases bar length by one and is K-linear, as a contraction
of a free A-resolution should be. It is not asserted to be A-linear. -/
def homotopy : Words I A →ₗ[K] Words I A :=
  Finsupp.lsum K (positivePrefix B)

@[simp] theorem homotopy_single (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)
        (positiveCoordinates B a) := by
  simp only [homotopy,Finsupp.lsum_single,positivePrefix,LinearMap.comp_apply]

include hunit in
@[simp] theorem homotopy_single_one (L : List I) :
    homotopy B (Finsupp.single L (1 : A))=0 := by
  rw [homotopy_single,positiveCoordinates_one B hunit,map_zero]

@[simp] theorem homotopy_single_positive (L : List I) (i : I) :
    homotopy B (Finsupp.single L (positiveVector B i))=Finsupp.single (i::L) 1 := by
  rw [homotopy_single,positiveCoordinates_vector,
    Finsupp.linearCombination_single,one_smul]

/-- Scalar extension of multiplication of the first positive tensor factor. -/
def merge (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.mergeBasis B i L))

@[simp] theorem merge_single (i : I) (L : List I) (a : A) :
    merge B i (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.mergeBasis B i L) :=
  Finsupp.linearCombination_single _ _ _

theorem front_prefix (i : I) (z : Words I A) :
    front B (prepend i z)=positiveVector B i • z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L a =>
    simp only [prefix_single,front_single,frontBasis,Finsupp.smul_single,smul_eq_mul,mul_comm]

theorem internal_prefix (i : I) (z : Words I A) :
    internal B (prepend i z)=merge B i z-prepend i (internal B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,sub_zero]
  | add z w hz hw => simp only [map_add,hz,hw]; abel
  | single L a =>
    simp only [prefix_single,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
      PaperVerification.ReducedBarBasis.merge_single,one_smul,
      lift_prefix,smul_sub,merge_single,map_smul]

def positivePrefixMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (prepend (A := A) i).restrictScalars K)
    (positiveCoordinates B a)

def positiveMergeMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (merge B i).restrictScalars K)
    (positiveCoordinates B a)

theorem homotopy_single_eq_prefix (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      positivePrefixMap B a (Finsupp.single L 1) := by
  simp only [homotopy_single,positivePrefixMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,prefix_single]

theorem homotopy_smul_lift (a : A) (z : Words I K) :
    homotopy B (a • lift z)=positivePrefixMap B a (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    calc
      homotopy B (a • lift (Finsupp.single L c)) =
          homotopy B (c • (a • (Finsupp.single L 1 : Words I A))) := by
        rw [lift_single,smul_comm a c]
      _ = c • homotopy B (Finsupp.single L a) := by
        rw [map_smul]
        congr 1
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      _ = c • positivePrefixMap B a (Finsupp.single L 1) := by
        rw [homotopy_single_eq_prefix]
      _ = positivePrefixMap B a (lift (Finsupp.single L c)) := by
        rw [lift_single,map_smul]

theorem front_positivePrefixMap (a : A) (z : Words I A) :
    front B (positivePrefixMap B a z)=
      positiveCombination B (positiveCoordinates B a) • z := by
  simp only [positivePrefixMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,front_prefix,positiveCombination_apply,
    Finset.sum_smul,smul_assoc]

theorem internal_positivePrefixMap (a : A) (z : Words I A) :
    internal B (positivePrefixMap B a z)=
      positiveMergeMap B a z-positivePrefixMap B a (internal B z) := by
  simp only [positivePrefixMap,positiveMergeMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,internal_prefix,smul_sub,Finset.sum_sub_distrib]

include hunit hε in
theorem front_positivePrefixMap_add_scalar (a : A) (z : Words I A) :
    front B (positivePrefixMap B a z)+ε a • z=a • z := by
  rw [front_positivePrefixMap]
  have h := congrArg (fun x : A ↦ x • z) (scalar_add_positive ε B hunit hε a)
  simp only [add_smul,smul_assoc,one_smul] at h
  simpa only [add_comm] using h

theorem lift_appendTail (L : List I) (c : I →₀ K) :
    lift (A := A) (PaperVerification.ReducedBarBasis.appendTail L c)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) (1 : A)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      Finsupp.linearCombination_single]

include hunit hε in
/-- The coefficient splitting of a product gives exactly the two terms that
cancel the first adjacent multiplication in the homotopy identity. -/
theorem homotopy_front_cons (a : A) (i : I) (L : List I) :
    homotopy B (front B (Finsupp.single (i::L) a))=
      ε a • Finsupp.single (i::L) 1+
        positiveMergeMap B a (Finsupp.single (i::L) 1) := by
  rw [front_single]
  change homotopy B (a • Finsupp.single L (positiveVector B i))=_
  rw [Finsupp.smul_single]
  change homotopy B (Finsupp.single L (a*positiveVector B i))=_
  rw [homotopy_single,positiveCoordinates_mul_vector ε B hunit hε,
    map_add,map_smul,Finsupp.linearCombination_single]
  simp only [Finsupp.sum,map_sum,map_smul,positiveMergeMap,
    Finsupp.linearCombination_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,merge_single,one_smul,
    PaperVerification.ReducedBarBasis.mergeBasis,lift_appendTail]

theorem positiveMergeMap_nil (a : A) :
    positiveMergeMap B a (Finsupp.single [] (1 : A))=0 := by
  simp only [positiveMergeMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    merge_single,PaperVerification.ReducedBarBasis.mergeBasis,map_zero,smul_zero,
    Finset.sum_const_zero]

/-- Augmentation followed by the degree-zero unit inclusion. -/
def augmentationProjection : Words I A →ₗ[K] Words I A :=
  (ε.toLinearMap.smulRight (Finsupp.single [] (1 : A))).comp
    (Finsupp.lapply [])

@[simp] theorem augmentationProjection_nil (a : A) :
    augmentationProjection (I := I) ε (Finsupp.single [] a)=
      ε a • Finsupp.single [] 1 := by
  simp [augmentationProjection]

@[simp] theorem augmentationProjection_cons (i : I) (L : List I) (a : A) :
    augmentationProjection ε (Finsupp.single (i::L) a)=0 := by
  simp [augmentationProjection]

include hunit hε in
/-- The explicit K-linear contraction of the augmented normalized free bar
complex. Together with the length restriction, this proves actual exactness. -/
theorem contracting_identity (z : Words I A) :
    differential B (homotopy B z)+homotopy B (differential B z)+
      augmentationProjection ε z=z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    calc
      _ = (differential B (homotopy B z)+homotopy B (differential B z)+
          augmentationProjection ε z)+
        (differential B (homotopy B w)+homotopy B (differential B w)+
          augmentationProjection ε w) := by abel
      _ = _ := by rw [hz,hw]
  | single L a =>
    cases L with
    | nil =>
      rw [homotopy_single_eq_prefix,augmentationProjection_nil]
      have hd : differential B (Finsupp.single [] a)=0 := by
        simp only [differential,LinearMap.sub_apply,front_single,frontBasis,
          internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          map_zero,smul_zero,sub_zero]
      rw [hd,map_zero,add_zero]
      change front B (positivePrefixMap B a (Finsupp.single [] 1))-
        internal B (positivePrefixMap B a (Finsupp.single [] 1))+
          ε a • Finsupp.single [] 1=Finsupp.single [] a
      rw [internal_positivePrefixMap,positiveMergeMap_nil,internal_single,
        PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,
        map_zero,sub_zero,sub_zero,front_positivePrefixMap_add_scalar ε B hunit hε]
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    | cons i L =>
      rw [homotopy_single_eq_prefix,augmentationProjection_cons,add_zero]
      have hd : homotopy B (differential B (Finsupp.single (i::L) a))=
          ε a • Finsupp.single (i::L) 1+
            positiveMergeMap B a (Finsupp.single (i::L) 1)-
            positivePrefixMap B a
              (lift (PaperVerification.ReducedBarBasis.differentialBasis B (i::L))) := by
        change homotopy B (front B (Finsupp.single (i::L) a)-
          internal B (Finsupp.single (i::L) a))=_
        rw [map_sub,homotopy_front_cons ε B hunit hε,internal_single,homotopy_smul_lift]
      rw [hd]
      change (front B (positivePrefixMap B a (Finsupp.single (i::L) 1))-
        internal B (positivePrefixMap B a (Finsupp.single (i::L) 1)))+_=_
      rw [internal_positivePrefixMap,internal_single,one_smul]
      have h := front_positivePrefixMap_add_scalar ε B hunit hε a
        (Finsupp.single (i::L) (1 : A))
      have ha : a • (Finsupp.single (i::L) 1 : Words I A)=Finsupp.single (i::L) a := by
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      rw [ha] at h
      calc
        _ = front B (positivePrefixMap B a (Finsupp.single (i::L) 1))+
            ε a • Finsupp.single (i::L) 1 := by abel
        _ = _ := h

end PaperVerification.AlternatingForms.BarFree
