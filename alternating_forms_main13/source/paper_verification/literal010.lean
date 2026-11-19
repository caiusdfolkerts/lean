module

public import paper_verification.literal009
public import Mathlib.LinearAlgebra.Dual.Basis
public import paper_verification.literal004
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.RingQuot
import all Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.FreeAlgebra
import all Mathlib.LinearAlgebra.FreeAlgebra
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import paper_verification.literal007
public import paper_verification.literal008
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import paper_verification.literal001
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Operations
public import paper_verification.literal002
public import paper_verification.literal003

set_option Elab.async false

section TAF_LiteralSource_0508
/- Original module: PaperVerification.DiagonalBarWords -/


/-!
# The actual word bases on the diagonal and immediately below it

Positive original degrees force a tensor of length n and degree n to
have only degree-one factors. A tensor of length n-1 and degree n has
exactly one degree-two factor. The equivalences below are proved from
those degree equations, including degree zero, and apply to the actual
coefficient complex of ordinary augmentation Tor.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.DiagonalBarWords

open WeightedBar

universe u
variable {I : Type u} (δ : I → ℕ) (hpos : ∀ i,0<δ i)

abbrev DegreeOne := {i : I // δ i=1}
abbrev DegreeTwo := {i : I // δ i=2}

def embedWord (L : List (DegreeOne δ)) : List I := L.map Subtype.val

@[simp] theorem embedWord_nil : embedWord δ []=[] := rfl
@[simp] theorem embedWord_cons (i : DegreeOne δ) (L : List (DegreeOne δ)) :
    embedWord δ (i::L)=i.val::embedWord δ L := rfl
@[simp] theorem embedWord_length (L : List (DegreeOne δ)) :
    (embedWord δ L).length=L.length := List.length_map _

theorem embedWord_injective : Function.Injective (embedWord δ) := by
  intro L T h
  exact (List.map_inj_right Subtype.val_injective).mp h

@[simp] theorem totalDegree_embedWord (L : List (DegreeOne δ)) :
    totalDegree δ (embedWord δ L)=L.length := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      rw [embedWord_cons,totalDegree_cons,i.property,ih,List.length_cons,Nat.add_comm]

include hpos in
theorem degree_one_of_diagonal (L : List I) (hL : totalDegree δ L=L.length) :
    ∀ i∈L,δ i=1 := by
  induction L with
  | nil => simp only [List.not_mem_nil,false_implies,implies_true]
  | cons a L ih =>
      have ha := hpos a
      have hbound := length_le_totalDegree δ hpos L
      have hd : δ a+totalDegree δ L=L.length+1 := hL
      have ha1 : δ a=1 := by omega
      have ht : totalDegree δ L=L.length := by omega
      intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact ha1
      · exact ih ht i hi

theorem exists_pure_lift (L : List I) (hL : ∀ i∈L,δ i=1) :
    ∃ T : List (DegreeOne δ),embedWord δ T=L := by
  induction L with
  | nil => exact ⟨[],rfl⟩
  | cons a L ih =>
      obtain ⟨T,hT⟩ := ih (fun i hi ↦ hL i (List.mem_cons_of_mem a hi))
      exact ⟨⟨a,hL a (List.mem_cons_self)⟩::T,by rw [embedWord_cons,hT]⟩

def PureWord (n : ℕ) := {L : List (DegreeOne δ) // L.length=n}

def pureToIndex (n : ℕ) (L : PureWord δ n) : Index δ n n :=
  ⟨embedWord δ L.val,by rw [embedWord_length,totalDegree_embedWord];exact ⟨L.property,L.property⟩⟩

theorem pureToIndex_injective (n : ℕ) : Function.Injective (pureToIndex δ n) := by
  intro L T h
  apply Subtype.ext
  exact embedWord_injective δ (congrArg Subtype.val h)

include hpos in
theorem pureToIndex_surjective (n : ℕ) : Function.Surjective (pureToIndex δ n) := by
  intro L
  obtain ⟨T,hT⟩ := exists_pure_lift δ L.val
    (degree_one_of_diagonal δ hpos L.val (L.property.2.trans L.property.1.symm))
  have ht : T.length=n := by rw [←embedWord_length δ T,hT];exact L.property.1
  exact ⟨⟨T,ht⟩,Subtype.ext hT⟩

def pureIndexEquiv (n : ℕ) : PureWord δ n ≃ Index δ n n :=
  Equiv.ofBijective (pureToIndex δ n)
    ⟨pureToIndex_injective δ n,pureToIndex_surjective δ hpos n⟩

instance pureWordFinite [Finite I] (n : ℕ) : Finite (PureWord δ n) :=
  Finite.of_injective (pureToIndex δ n) (pureToIndex_injective δ n)

instance pureWordFintype [Fintype I] (n : ℕ) : Fintype (PureWord δ n) :=
  Fintype.ofFinite _

variable {K : Type u} [Field K]

def diagonalBasis (n : ℕ) : Module.Basis (PureWord δ n) K (piece (K := K) δ n n) :=
  (basis δ n n).reindex (pureIndexEquiv δ hpos n).symm

@[simp] theorem diagonalBasis_val (n : ℕ) (L : PureWord δ n) :
    (diagonalBasis (K := K) δ hpos n L).val=Finsupp.single (embedWord δ L.val) 1 := by
  rw [diagonalBasis,Module.Basis.reindex_apply]
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {T : List I | T.length=n ∧ totalDegree δ T=n}).symm
      (Finsupp.single (pureToIndex δ n L) 1)).val=Finsupp.single (embedWord δ L.val) 1
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp] theorem diagonalBasis_repr (n : ℕ) (z : piece (K := K) δ n n)
    (L : PureWord δ n) :
    (diagonalBasis δ hpos n).repr z L=z.val (embedWord δ L.val) := by
  rw [diagonalBasis,Module.Basis.repr_reindex_apply]
  rfl

include hpos in
/-- Every word one step below the diagonal has precisely one factor of
actual degree two and otherwise actual degree-one factors. -/
theorem defect_one_decomposition (L : List I)
    (hL : totalDegree δ L=L.length+1) :
    ∃ P : List (DegreeOne δ),∃ a : DegreeTwo δ,∃ Q : List (DegreeOne δ),
      L=embedWord δ P++a.val::embedWord δ Q := by
  induction L with
  | nil => simp only [totalDegree_nil,List.length_nil] at hL;omega
  | cons a L ih =>
      have ha := hpos a
      have hbound := length_le_totalDegree δ hpos L
      have hd : δ a+totalDegree δ L=(L.length+1)+1 := hL
      by_cases ha2 : δ a=2
      · have ht : totalDegree δ L=L.length := by omega
        obtain ⟨Q,hQ⟩ := exists_pure_lift δ L (degree_one_of_diagonal δ hpos L ht)
        exact ⟨[],⟨a,ha2⟩,Q,by simp only [embedWord_nil,List.nil_append,hQ]⟩
      · have ha1 : δ a=1 := by omega
        have ht : totalDegree δ L=L.length+1 := by omega
        obtain ⟨P,b,Q,h⟩ := ih ht
        refine ⟨⟨a,ha1⟩::P,b,Q,?_⟩
        rw [embedWord_cons,List.cons_append,←h]

end PaperVerification.DiagonalBarWords
end
end
end TAF_LiteralSource_0508

section TAF_LiteralSource_0509
/- Original module: PaperVerification.BarCoefficientRecursion -/


/-!
# Literal coefficient recursion for the normalized bar differential

These formulas retain the original multiplication coefficients and the
actual alternating bar signs. They are intended for the comparison of
diagonal bar cycles with the annihilator relations of a quadratic dual.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BarCoefficientRecursion

open ReducedBarBasis AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option I) K A)

local notation "W" => List I →₀ K

theorem prepend_nil (i : I) (z : W) : prepend i z []=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw,add_zero]
  | single L c => simp only [prefix_single,Finsupp.single_apply,List.cons_ne_nil,if_false]

theorem prepend_cons (i j : I) (z : W) (L : List I) :
    prepend i z (j::L)=if i=j then z L else 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw]
      split_ifs <;> simp only [add_zero]
  | single T c =>
      rw [prefix_single]
      by_cases h : i=j
      · subst j
        simp only [Finsupp.single_apply,List.cons.injEq,true_and,if_pos rfl,ite_true]
      · simp only [Finsupp.single_apply,List.cons.injEq,h,false_and,if_false]

theorem appendTail_nil (z : I →₀ K) (L : List I) : appendTail L z []=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw,add_zero]
  | single i c => simp only [appendTail_single,Finsupp.single_apply,List.cons_ne_nil,if_false]

theorem appendTail_cons (z : I →₀ K) (L T : List I) (i : I) :
    appendTail L z (i::T)=if L=T then z i else 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw]
      split_ifs <;> simp only [add_zero]
  | single j c =>
      rw [appendTail_single]
      by_cases h : L=T
      · subst T
        simp only [Finsupp.single_apply,List.cons.injEq,and_true,if_pos rfl,ite_true]
      · simp only [Finsupp.single_apply,List.cons.injEq,h,and_false,if_false]

theorem differentialBasis_nil_coefficient (L : List I) : differentialBasis B L []=0 := by
  cases L with
  | nil => rfl
  | cons a L =>
      cases L with
      | nil => simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,
          sub_zero,Finsupp.zero_apply]
      | cons b L =>
          rw [differentialBasis,merge_single,one_smul,mergeBasis,Finsupp.sub_apply,
            appendTail_nil,prepend_nil,sub_zero]

/-- The first merge contributes the actual product coefficient; the
remaining merges carry precisely the negative of the shorter differential. -/
theorem differentialBasis_cons_cons (a b c : I) (L T : List I) :
    differentialBasis B (a::b::L) (c::T)=
      (if L=T then productCoefficients B a b c else 0)-
        (if a=c then differentialBasis B (b::L) T else 0) := by
  rw [differentialBasis,merge_single,one_smul,mergeBasis,Finsupp.sub_apply,
    appendTail_cons,prepend_cons]

def slice (i : I) : W →ₗ[K] W :=
  Finsupp.lcomapDomain (List.cons i) (fun _ _ h ↦ List.cons.inj h |>.2)

@[simp] theorem slice_apply (i : I) (z : W) (L : List I) :
    slice i z L=z (i::L) := rfl

@[simp] theorem slice_single_nil (i : I) (c : K) : slice i (Finsupp.single [] c)=0 := by
  apply Finsupp.ext
  intro L
  simp [slice_apply]

@[simp] theorem slice_single_cons (i j : I) (L : List I) (c : K) :
    slice i (Finsupp.single (j::L) c)=if j=i then Finsupp.single L c else 0 := by
  apply Finsupp.ext
  intro T
  rw [slice_apply]
  by_cases h : j=i
  · subst j
    simp only [Finsupp.single_apply,List.cons.injEq,true_and,if_pos rfl,ite_true]
  · simp only [Finsupp.single_apply,List.cons.injEq,h,false_and,if_false,Finsupp.zero_apply]

variable [Fintype I]

theorem merge_cons (a c : I) (z : W) (T : List I) :
    merge B a z (c::T)=∑ b : I,productCoefficients B a b c*z (b::T) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,mul_zero,Finset.sum_const_zero]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw,mul_add,Finset.sum_add_distrib]
  | single L t =>
      cases L with
      | nil => simp [merge_single,mergeBasis]
      | cons b L =>
          rw [merge_single,mergeBasis,Finsupp.smul_apply,smul_eq_mul,appendTail_cons]
          by_cases h : L=T
          · subst T
            simp [Finsupp.single_apply,List.cons.injEq,mul_comm]
          · simp only [h,if_false,mul_zero,Finsupp.single_apply,List.cons.injEq,
              and_false,Finset.sum_const_zero]

theorem differential_cons_slice (c : I) (z : W) (T : List I) :
    differential B z (c::T)=
      (∑ a : I,merge B a (slice a z) (c::T))-differential B (slice c z) T := by
  induction z using Finsupp.induction_linear with
  | zero =>
      simp only [map_zero,Finsupp.zero_apply,Finset.sum_const_zero,sub_zero]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw,Finset.sum_add_distrib]
      abel
  | single L t =>
      cases L with
      | nil => simp only [differential_single,differentialBasis,smul_zero,
          Finsupp.zero_apply,slice_single_nil,map_zero,Finset.sum_const_zero,sub_zero]
      | cons a L =>
          have hd := congrArg (fun w : W ↦ w (c::T))
            (differential_prefix B a (Finsupp.single L t))
          rw [prefix_single,Finsupp.sub_apply,prepend_cons] at hd
          have hs : (∑ j : I,merge B j (slice j (Finsupp.single (a::L) t)) (c::T))=
              merge B a (Finsupp.single L t) (c::T) := by
            calc
              _=merge B a (slice a (Finsupp.single (a::L) t)) (c::T) := by
                apply Finset.sum_eq_single a
                · intro j hj hja
                  rw [slice_single_cons,if_neg (Ne.symm hja),map_zero,Finsupp.zero_apply]
                · intro ha
                  exact (ha (Finset.mem_univ a)).elim
              _=merge B a (Finsupp.single L t) (c::T) := by
                rw [slice_single_cons,if_pos rfl]
          rw [hs,slice_single_cons]
          by_cases hac : a=c
          · subst c
            simpa only [if_pos rfl,ite_true] using hd
          · simpa only [hac,if_false,map_zero,Finsupp.zero_apply] using hd

/-- Coefficients of the actual differential are the original quadratic
multiplication coefficients followed by the recursive alternating tail. -/
theorem differential_cons (c : I) (z : W) (T : List I) :
    differential B z (c::T)=
      (∑ a : I,∑ b : I,productCoefficients B a b c*z (a::b::T))-
        differential B (slice c z) T := by
  rw [differential_cons_slice]
  simp_rw [merge_cons,slice_apply]

end PaperVerification.BarCoefficientRecursion
end
end
end TAF_LiteralSource_0509

section TAF_LiteralSource_0510
/- Original module: PaperVerification.DiagonalBarRelations -/


/-!
# Diagonal bar cycles satisfy exactly the quadratic context equations

The equations here use the actual multiplication coefficients of the
augmented algebra, its original positive degrees, and its actual bar
differential. Both implications are proved. They will be compared with
the independently defined genuine quadratic quotient, not used to
define away the homology condition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.DiagonalBarRelations

open WeightedBar DiagonalBarWords ReducedBarBasis AugmentedAlgebraBasis
open BarCoefficientRecursion

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "W" => List I →₀ K

include hpos hδ in
theorem product_degree_one_zero (a b : I) (c : DegreeOne δ) :
    productCoefficients B a b c.val=0 := by
  by_contra h
  have he := hδ a b c.val h
  have ha := hpos a
  have hb := hpos b
  have hc := c.property
  omega

include hpos hδ in
theorem differential_degree_one_prefix (c : DegreeOne δ) (z : W) (L : List I) :
    differential B z (c.val::L)= -differential B (slice c.val z) L := by
  rw [differential_cons]
  have hz : (∑ a : I,∑ b : I,productCoefficients B a b c.val*z (a::b::L))=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [product_degree_one_zero B δ hpos hδ a b c,zero_mul]
  rw [hz,zero_sub]

def prefixSlice : List (DegreeOne δ) → W →ₗ[K] W
  | [] => LinearMap.id
  | c::P => (prefixSlice P).comp (slice c.val)

@[simp] theorem prefixSlice_apply (P : List (DegreeOne δ)) (z : W) (L : List I) :
    prefixSlice δ P z L=z (embedWord δ P++L) := by
  induction P generalizing z with
  | nil => rfl
  | cons c P ih =>
      rw [prefixSlice,LinearMap.comp_apply,ih,slice_apply,embedWord_cons,List.cons_append]

include hpos hδ in
theorem differential_pure_prefix (P : List (DegreeOne δ)) (z : W) (L : List I) :
    differential B z (embedWord δ P++L)=
      (-1 : K)^P.length*differential B (prefixSlice δ P z) L := by
  induction P generalizing z with
  | nil => simp only [embedWord_nil,List.nil_append,List.length_nil,pow_zero,one_mul,
      prefixSlice,LinearMap.id_apply]
  | cons c P ih =>
      rw [embedWord_cons,List.cons_append,
        differential_degree_one_prefix B δ hpos hδ,ih]
      simp only [prefixSlice,LinearMap.comp_apply,List.length_cons,pow_succ,mul_neg,mul_one,
        neg_mul]

include hpos in
theorem slice_degree_two_zero (n : ℕ) (z : piece (K := K) δ n n)
    (P : List (DegreeOne δ)) (c : DegreeTwo δ) :
    slice c.val (prefixSlice δ P z.val)=0 := by
  apply Finsupp.ext
  intro L
  rw [slice_apply,prefixSlice_apply,Finsupp.zero_apply]
  by_contra h
  have hz := z.property (Finsupp.mem_support_iff.mpr h)
  have hpure := degree_one_of_diagonal δ hpos _ (hz.2.trans hz.1.symm)
  have h1 := hpure c.val (List.mem_append_right _ List.mem_cons_self)
  have h2 := c.property
  omega

include hpos hδ in
theorem differential_context_all_indices (n : ℕ) (z : piece (K := K) δ n n)
    (P : List (DegreeOne δ)) (c : DegreeTwo δ) (Q : List (DegreeOne δ)) :
    differential B z.val (embedWord δ P++c.val::embedWord δ Q)=
      (-1 : K)^P.length*
        (∑ a : I,∑ b : I,productCoefficients B a b c.val*
          z.val (embedWord δ P++a::b::embedWord δ Q)) := by
  rw [differential_pure_prefix B δ hpos hδ,differential_cons,
    slice_degree_two_zero δ hpos,map_zero,Finsupp.zero_apply,sub_zero]
  simp only [prefixSlice_apply]

theorem sum_degreeOne (f : I → K) (hf : ∀ i,δ i≠1 → f i=0) :
    (∑ i : I,f i)=∑ i : DegreeOne δ,f i.val := by
  have he := Fintype.sum_subtype_add_sum_subtype (fun i ↦ δ i=1) f
  have hz : (∑ i : {i : I // ¬δ i=1},f i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hf i.val i.property
  rw [hz,add_zero] at he
  exact he.symm

include hpos hδ in
theorem product_degree_two_zero (a b : I) (c : DegreeTwo δ)
    (h : δ a≠1 ∨ δ b≠1) : productCoefficients B a b c.val=0 := by
  by_contra hn
  have he := hδ a b c.val hn
  have ha := hpos a
  have hb := hpos b
  have hc := c.property
  rcases h with h|h <;> omega

/-- The row equations use precisely the actual degree-one factors. -/
def contextRow (z : W) (P : List (DegreeOne δ)) (c : DegreeTwo δ)
    (Q : List (DegreeOne δ)) : K :=
  ∑ a : DegreeOne δ,∑ b : DegreeOne δ,productCoefficients B a.val b.val c.val*
    z (embedWord δ P++a.val::b.val::embedWord δ Q)

include hpos hδ in
theorem differential_context (n : ℕ) (z : piece (K := K) δ n n)
    (P : List (DegreeOne δ)) (c : DegreeTwo δ) (Q : List (DegreeOne δ)) :
    differential B z.val (embedWord δ P++c.val::embedWord δ Q)=
      (-1 : K)^P.length*contextRow B δ z.val P c Q := by
  rw [differential_context_all_indices B δ hpos hδ]
  congr 1
  rw [sum_degreeOne δ _ (by
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [product_degree_two_zero B δ hpos hδ a b c (Or.inl ha),zero_mul])]
  apply Finset.sum_congr rfl
  intro a ha
  exact sum_degreeOne δ _ (by
    intro b hb
    rw [product_degree_two_zero B δ hpos hδ a.val b c (Or.inr hb),zero_mul])

include hpos hδ in
/-- This is an exact characterization of the actual outgoing differential
kernel in every positive diagonal degree. -/
theorem differential_eq_zero_iff_contexts (r : ℕ)
    (z : piece (K := K) δ (r+1) (r+1)) :
    differential B z.val=0 ↔
      ∀ P : List (DegreeOne δ),∀ c : DegreeTwo δ,∀ Q : List (DegreeOne δ),
        contextRow B δ z.val P c Q=0 := by
  constructor
  · intro hz P c Q
    have he := congrArg (fun w : W ↦ w (embedWord δ P++c.val::embedWord δ Q)) hz
    rw [differential_context B δ hpos hδ,Finsupp.zero_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro h
    apply Finsupp.ext
    intro L
    change differential B z.val L=0
    by_contra hn
    have hm := differential_mem_piece B δ hδ z.val z.property
    have hp := hm (Finsupp.mem_support_iff.mpr hn)
    have hd : totalDegree δ L=L.length+1 := by rw [hp.1,hp.2]
    obtain ⟨P,c,Q,hL⟩ := defect_one_decomposition δ hpos L hd
    rw [hL,differential_context B δ hpos hδ,h P c Q,mul_zero] at hn
    exact hn rfl

end PaperVerification.DiagonalBarRelations
end
end
end TAF_LiteralSource_0510

section TAF_LiteralSource_0511
/- Original module: PaperVerification.RingQuotLinearRelations -/


/-!
# The actual linear relations of a noncommutative algebra presentation

The kernel of the genuine algebra quotient is exactly the linear span of
all two-sided contexts of the defining relations. This supplies the
linear-algebra interface needed to compare tensor-annihilator relations
with actual quadratic dual algebras. No kernel or presentation equality
is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.RingQuotLinearRelations

variable {K A V : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V]
  (r : A → A → Prop) (F : A →ₗ[K] V)
  (hF : ∀ {x y},r x y → ∀ a b,F (a*x*b)=F (a*y*b))

include hF in
theorem context_respects_closure {x y : A} (h : RingQuot.Rel r x y) :
    ∀ a b,F (a*x*b)=F (a*y*b) := by
  induction h with
  | of h => exact hF h
  | @add_left x y z h ih =>
      intro a b
      simp only [mul_add,add_mul,map_add,ih]
  | @mul_left x y z h ih =>
      intro a b
      simpa only [mul_assoc] using ih a (z*b)
  | @mul_right x y z h ih =>
      intro a b
      simpa only [mul_assoc] using ih (a*x) b

/-- A genuine linear map out of the algebra quotient, provided the
original linear functional kills every context of a defining relation. -/
def lift : RingQuot r →ₗ[K] V where
  toFun z := Quot.lift F (fun x y h ↦ by
    simpa only [one_mul,mul_one] using context_respects_closure r F hF h 1 1) z.toQuot
  map_add' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [RingQuot.add_quot,map_add]
  map_smul' := by
    rintro c ⟨⟨x⟩⟩
    simp only [RingQuot.smul_quot,map_smul,RingHom.id_apply]

@[simp] theorem lift_mk (x : A) : lift r F hF (RingQuot.mkAlgHom K r x)=F x := by
  simp only [RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def]
  rfl

/-- Literal linear span of two-sided contexts, retaining the actual
noncommutative multiplication order. -/
def relationSpan : Submodule K A :=
  Submodule.span K {z | ∃ a b x y,r x y ∧ a*(x-y)*b=z}

/-- No further linear relations arise in the genuine algebra quotient. -/
theorem relationSpan_eq_kernel :
    relationSpan (K := K) r=LinearMap.ker (RingQuot.mkAlgHom K r).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a,b,x,y,h,rfl⟩
    change RingQuot.mkAlgHom K r (a*(x-y)*b)=0
    rw [map_mul,map_mul,map_sub,RingQuot.mkAlgHom_rel K h,sub_self,mul_zero,zero_mul]
  · intro z hz
    let S := relationSpan (K := K) r
    have hrespect : ∀ {x y},r x y → ∀ a b,S.mkQ (a*x*b)=S.mkQ (a*y*b) := by
      intro x y h a b
      apply (Submodule.Quotient.eq S).mpr
      change a*x*b-a*y*b∈S
      rw [←sub_mul,←mul_sub]
      exact Submodule.subset_span ⟨a,b,x,y,h,rfl⟩
    have he := congrArg (lift r S.mkQ hrespect)
      (show RingQuot.mkAlgHom K r z=0 from hz)
    rw [lift_mk,map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero S).mp he

/-- The independently specified linear quotient and the actual algebra
quotient have the same underlying module, by a proved kernel identity. -/
def quotientEquiv : (A ⧸ relationSpan (K := K) r) ≃ₗ[K] RingQuot r :=
  (Submodule.quotEquivOfEq _ _ (relationSpan_eq_kernel (K := K) r)).trans
    ((RingQuot.mkAlgHom K r).toLinearMap.quotKerEquivOfSurjective
      (RingQuot.mkAlgHom_surjective K r))

@[simp] theorem quotientEquiv_mk (x : A) :
    quotientEquiv (K := K) r (Submodule.Quotient.mk x)=RingQuot.mkAlgHom K r x := by
  rfl

/-- The dual of the genuine algebra quotient consists precisely of the
linear functionals annihilating all actual relation contexts. -/
def dualEquiv : Module.Dual K (RingQuot r) ≃ₗ[K]
    (relationSpan (K := K) r).dualAnnihilator :=
  (quotientEquiv (K := K) r).dualMap.trans
    (Submodule.dualQuotEquivDualAnnihilator (relationSpan (K := K) r))

end PaperVerification.RingQuotLinearRelations
end
end
end TAF_LiteralSource_0511

section TAF_LiteralSource_0512
/- Original module: PaperVerification.QuadraticWordFunctionals -/


/-!
# Functionals on the genuine homogeneous pieces of a quadratic quotient

A multiplicative word basis determines the original word degree. We prove
that the dual of the actual image of its degree-n space in the algebra
quotient is exactly the space of functionals satisfying all degree-n
contexts of the quadratic relations. The relation space is independently
given and homogeneous of degree two. No assertion about Koszulness,
quadratic duality, or quotient kernels is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordFunctionals

variable {K A J : Type*} [Field K] [Ring A] [Algebra K A]
  (B : Module.Basis (List J) K A)

def degreeSpace (n : ℕ) : Submodule K A :=
  Submodule.span K (B '' {L | L.length=n})

theorem basis_mem_degreeSpace (L : List J) : B L∈degreeSpace B L.length :=
  Submodule.subset_span ⟨L,rfl,rfl⟩

def projection (n : ℕ) : A →ₗ[K] A :=
  B.constr K (fun L ↦ if L.length=n then B L else 0)

@[simp] theorem projection_basis (n : ℕ) (L : List J) :
    projection B n (B L)=if L.length=n then B L else 0 :=
  B.constr_basis K _ L

theorem projection_homogeneous (n m : ℕ) (x : A) (hx : x∈degreeSpace B m) :
    projection B n x=if m=n then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L,hL,rfl⟩ := hx
      change L.length=m at hL
      rw [projection_basis,hL]
  | zero => simp only [map_zero,ite_self]
  | add x y hx hy ihx ihy =>
      rw [map_add,ihx,ihy]
      split_ifs <;> simp only [add_zero]
  | smul c x hx ih =>
      rw [map_smul,ih]
      split_ifs <;> simp only [smul_zero]

theorem projection_mem (n : ℕ) (x : A) : projection B n x∈degreeSpace B n := by
  have hr : LinearMap.range (projection B n)≤degreeSpace B n := by
    rw [projection,Module.Basis.constr_range]
    apply Submodule.span_le.mpr
    rintro _ ⟨L,rfl⟩
    change (if L.length=n then B L else 0)∈degreeSpace B n
    by_cases h : L.length=n
    · rw [if_pos h]
      exact Submodule.subset_span ⟨L,h,rfl⟩
    · rw [if_neg h]
      exact Submodule.zero_mem _
  exact hr ⟨x,rfl⟩

def projectionToPiece (n : ℕ) : A →ₗ[K] degreeSpace B n :=
  (projection B n).codRestrict _ (projection_mem B n)

@[simp] theorem projectionToPiece_val (n : ℕ) (x : A) :
    (projectionToPiece B n x).val=projection B n x := rfl

theorem projectionToPiece_retraction (n : ℕ) (x : degreeSpace B n) :
    projectionToPiece B n x.val=x := by
  apply Subtype.ext
  exact (projection_homogeneous B n n x.val x.property).trans (if_pos rfl)

variable (hmul : ∀ L M,B (L++M)=B L*B M)

include hmul in
theorem degree_mul {n m : ℕ} {x y : A}
    (hx : x∈degreeSpace B n) (hy : y∈degreeSpace B m) :
    x*y∈degreeSpace B (n+m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L,hL,rfl⟩ := hx
      change L.length=n at hL
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨M,hM,rfl⟩ := hy
          change M.length=m at hM
          rw [←hmul]
          exact Submodule.subset_span ⟨L++M,by
            change (L++M).length=n+m
            rw [List.length_append,hL,hM],rfl⟩
      | zero => simpa only [mul_zero] using (degreeSpace B (n+m)).zero_mem
      | add y z hy hz ihy ihz =>
          simpa only [mul_add] using (degreeSpace B (n+m)).add_mem ihy ihz
      | smul c y hy ih =>
          simpa only [mul_smul_comm] using (degreeSpace B (n+m)).smul_mem c ih
  | zero => simpa only [zero_mul] using (degreeSpace B (n+m)).zero_mem
  | add x z hx hz ihx ihz =>
      simpa only [add_mul] using (degreeSpace B (n+m)).add_mem ihx ihz
  | smul c x hx ih =>
      simpa only [smul_mul_assoc] using (degreeSpace B (n+m)).smul_mem c ih

/-- Testing contexts on a basis really tests every two-sided context. -/
theorem context_vanishes (F : A →ₗ[K] K) (q : A)
    (h : ∀ L M,F (B L*q*B M)=0) (a b : A) : F (a*q*b)=0 := by
  have hright (L : List J) : ∀ b,F (B L*q*b)=0 := by
    have he : F.comp (LinearMap.mulLeft K (B L*q))=0 := by
      apply B.ext
      intro M
      exact h L M
    intro b
    exact LinearMap.congr_fun he b
  have he : (F.comp (LinearMap.mulRight K b)).comp (LinearMap.mulRight K q)=0 := by
    apply B.ext
    intro L
    exact hright L b
  exact LinearMap.congr_fun he a

variable (S : Submodule K A)

inductive Relation : A → A → Prop
  | relation (q : A) (hq : q∈S) : Relation q 0

abbrev Quotient := RingQuot (Relation S)

def quotientMap : A →ₐ[K] Quotient S := RingQuot.mkAlgHom K (Relation S)

def quotientPiece (n : ℕ) : Submodule K (Quotient S) :=
  (degreeSpace B n).map (quotientMap S).toLinearMap

def pieceMap (n : ℕ) : degreeSpace B n →ₗ[K] quotientPiece B S n where
  toFun x := ⟨quotientMap S x,⟨x.val,x.property,rfl⟩⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

theorem pieceMap_surjective (n : ℕ) : Function.Surjective (pieceMap B S n) := by
  rintro ⟨x,hx⟩
  obtain ⟨y,hy,hxy⟩ := hx
  exact ⟨⟨y,hy⟩,Subtype.ext hxy⟩

/-- The independently written linear equations imposed by all quadratic
contexts after projection to the original word degree. -/
def relationFunctionals (n : ℕ) : Submodule K (Module.Dual K (degreeSpace B n)) where
  carrier := {φ | ∀ L M q,q∈S → φ (projectionToPiece B n (B L*q*B M))=0}
  zero_mem' := by simp only [Set.mem_setOf_eq,LinearMap.zero_apply,implies_true]
  add_mem' := by
    intro φ ψ hφ hψ L M q hq
    simp only [LinearMap.add_apply,hφ L M q hq,hψ L M q hq,add_zero]
  smul_mem' := by
    intro c φ hφ L M q hq
    simp only [LinearMap.smul_apply,hφ L M q hq,smul_zero]

variable (hS : S≤degreeSpace B 2)

include hmul hS in
theorem restriction_mem (n : ℕ) (φ : Module.Dual K (quotientPiece B S n)) :
    φ.comp (pieceMap B S n)∈relationFunctionals B S n := by
  intro L M q hq
  have hc : B L*q*B M∈degreeSpace B (L.length+2+M.length) :=
    degree_mul B hmul
      (degree_mul B hmul (basis_mem_degreeSpace B L) (hS hq))
      (basis_mem_degreeSpace B M)
  have he : pieceMap B S n (projectionToPiece B n (B L*q*B M))=0 := by
    apply Subtype.ext
    change quotientMap S (projection B n (B L*q*B M))=0
    rw [projection_homogeneous B n _ _ hc]
    split_ifs
    · rw [map_mul,map_mul]
      have hq0 : quotientMap S q=0 :=
        (RingQuot.mkAlgHom_rel K (Relation.relation q hq)).trans (map_zero _)
      rw [hq0,mul_zero,zero_mul]
    · exact map_zero _
  change φ (pieceMap B S n (projectionToPiece B n (B L*q*B M)))=0
  rw [he,map_zero]

def restriction (n : ℕ) :
    Module.Dual K (quotientPiece B S n) →ₗ[K] relationFunctionals B S n where
  toFun φ := ⟨φ.comp (pieceMap B S n),restriction_mem B hmul S hS n φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    rfl
  map_smul' c φ := by
    apply Subtype.ext
    rfl

theorem functional_respects_relation (n : ℕ) (φ : relationFunctionals B S n) :
    ∀ {x y},Relation S x y → ∀ a b,
      (φ.val.comp (projectionToPiece B n)) (a*x*b)=
        (φ.val.comp (projectionToPiece B n)) (a*y*b) := by
  intro x y h a b
  cases h with
  | relation hq =>
      simp only [mul_zero,zero_mul,map_zero]
      exact context_vanishes B (φ.val.comp (projectionToPiece B n)) x
        (fun L M ↦ φ.property L M x hq) a b

/-- A solution of the relation equations extends to an actual functional
on the algebra quotient by the proved linear quotient construction. -/
def liftFunctional (n : ℕ) (φ : relationFunctionals B S n) :
    Module.Dual K (Quotient S) :=
  RingQuotLinearRelations.lift (Relation S) (φ.val.comp (projectionToPiece B n))
    (functional_respects_relation B S n φ)

@[simp] theorem liftFunctional_mk (n : ℕ) (φ : relationFunctionals B S n) (x : A) :
    liftFunctional B S n φ (quotientMap S x)=φ.val (projectionToPiece B n x) :=
  RingQuotLinearRelations.lift_mk (K := K) (Relation S)
    (φ.val.comp (projectionToPiece B n)) (functional_respects_relation B S n φ) x

include hmul hS in
theorem restriction_bijective (n : ℕ) : Function.Bijective (restriction B hmul S hS n) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := pieceMap_surjective B S n x
    exact LinearMap.congr_fun (congrArg Subtype.val h) y
  · intro φ
    refine ⟨(liftFunctional B S n φ).comp (quotientPiece B S n).subtype,?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change liftFunctional B S n φ (quotientMap S x.val)=φ.val x
    rw [liftFunctional_mk,projectionToPiece_retraction]

/-- Actual degree-n quotient dual, with no assumed grading or kernel identity. -/
def dualPieceEquiv (n : ℕ) :
    Module.Dual K (quotientPiece B S n) ≃ₗ[K] relationFunctionals B S n :=
  LinearEquiv.ofBijective (restriction B hmul S hS n)
    (restriction_bijective B hmul S hS n)

end PaperVerification.QuadraticWordFunctionals
end
end
end TAF_LiteralSource_0512

section TAF_LiteralSource_0513
/- Original module: PaperVerification.FreeAlgebraWordDegree -/


/-!
# Original generator degree in the actual free algebra

The canonical word basis is multiplicative. Its length-n span equals the
nth power of the original generator space, including degree zero. These
identities connect homogeneous quadratic quotient functionals with the
usual generator grading rather than an auxiliary weight convention.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise

namespace PaperVerification.QuadraticWordFunctionals

variable {K A J : Type*} [Field K] [Ring A] [Algebra K A]
  (B : Module.Basis (List J) K A)
  (hmul : ∀ L M,B (L++M)=B L*B M) (hunit : B []=1)

include hunit in
theorem degreeSpace_zero : degreeSpace B 0=1 := by
  have hs : B '' {L | L.length=0}=({1} : Set A) := by
    ext x
    constructor
    · rintro ⟨L,hL,rfl⟩
      have he : L=[] := List.length_eq_zero_iff.mp hL
      simpa only [he,hunit,Set.mem_singleton_iff]
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨[],rfl,hunit⟩
  rw [degreeSpace,hs,←Submodule.one_eq_span]

include hmul in
theorem degreeSpace_succ (n : ℕ) :
    degreeSpace B (n+1)=degreeSpace B 1*degreeSpace B n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨L,hL,rfl⟩
    change L.length=n+1 at hL
    cases L with
    | nil => simp only [List.length_nil] at hL; omega
    | cons i L =>
        have hlen : L.length=n := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hL
        rw [show i::L=[i]++L from rfl,hmul]
        apply Submodule.mul_mem_mul
        · exact basis_mem_degreeSpace B [i]
        · simpa only [hlen] using basis_mem_degreeSpace B L
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    simpa only [Nat.add_comm 1 n] using degree_mul B hmul hx hy

include hmul hunit in
theorem degreeSpace_eq_power (n : ℕ) : degreeSpace B n=(degreeSpace B 1)^n := by
  induction n with
  | zero => rw [degreeSpace_zero B hunit,pow_zero]
  | succ n ih => rw [degreeSpace_succ B hmul,ih,pow_succ']

include hmul hunit in
theorem quotientPiece_eq_power (S : Submodule K A) (n : ℕ) :
    quotientPiece B S n=(quotientPiece B S 1)^n := by
  rw [quotientPiece,degreeSpace_eq_power B hmul hunit,Submodule.map_pow]
  rfl

end PaperVerification.QuadraticWordFunctionals

namespace PaperVerification.FreeAlgebraWordDegree

variable {K J : Type*} [Field K]

abbrev basis : Module.Basis (List J) K (FreeAlgebra K J) :=
  (FreeAlgebra.basisFreeMonoid K J).reindex FreeMonoid.toList

local notation "E" => (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
  FreeAlgebra K J ≃ₐ[K] MonoidAlgebra K (FreeMonoid J))

@[simp] theorem basis_single (L : List J) :
    basis (K := K) L=(E).symm (MonoidAlgebra.single (FreeMonoid.ofList L) (1 : K)) := by
  rw [basis,Module.Basis.reindex_apply]
  change FreeAlgebra.basisFreeMonoid K J (FreeMonoid.ofList L)=_
  rw [FreeAlgebra.basisFreeMonoid,Module.Basis.map_apply,Finsupp.coe_basisSingleOne]
  rfl

@[simp] theorem map_basis (L : List J) :
    E (basis (K := K) L)=MonoidAlgebra.single (FreeMonoid.ofList L) (1 : K) := by
  rw [basis_single,AlgEquiv.apply_symm_apply]

theorem basis_append (L M : List J) :
    basis (K := K) (L++M)=basis (K := K) L*basis (K := K) M := by
  apply (E).injective
  rw [map_mul,map_basis,map_basis,map_basis,MonoidAlgebra.single_mul_single,one_mul,
    FreeMonoid.ofList_append]

@[simp] theorem basis_nil : basis (K := K) (J := J) []=1 := by
  apply (E).injective
  rw [map_basis,map_one,FreeMonoid.ofList_nil,MonoidAlgebra.one_def]

@[simp] theorem basis_singleton (i : J) : basis (K := K) [i]=FreeAlgebra.ι K i := by
  apply (E).injective
  rw [map_basis]
  change MonoidAlgebra.single (FreeMonoid.ofList [i]) (1 : K)=
    FreeAlgebra.lift K (fun j ↦ MonoidAlgebra.of K (FreeMonoid J) (FreeMonoid.of j))
      (FreeAlgebra.ι K i)
  rw [FreeAlgebra.lift_ι_apply]
  rfl

def generatorSpace : Submodule K (FreeAlgebra K J) :=
  Submodule.span K (Set.range (FreeAlgebra.ι K : J → FreeAlgebra K J))

theorem degreeSpace_one :
    QuadraticWordFunctionals.degreeSpace (basis (K := K) (J := J)) 1=generatorSpace := by
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨L,hL,rfl⟩
    obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hL
    exact ⟨i,(basis_singleton i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨[i],rfl,basis_singleton i⟩

theorem degreeSpace_eq_generatorPower (n : ℕ) :
    QuadraticWordFunctionals.degreeSpace (basis (K := K) (J := J)) n=generatorSpace^n := by
  rw [QuadraticWordFunctionals.degreeSpace_eq_power basis basis_append basis_nil,degreeSpace_one]

end PaperVerification.FreeAlgebraWordDegree
end
end
end TAF_LiteralSource_0513

section TAF_LiteralSource_0514
/- Original module: PaperVerification.BarQuadraticPairing -/


/-!
# The actual finite pairing between diagonal bar words and quadratic words

The pairing is the coefficient pairing on the literal degree-one letters.
It identifies the actual outgoing differential kernel with the dual of
an actual RingQuot homogeneous piece. The defining quadratic relations
are the multiplication rows of the given algebra, not an assumed Koszul
Hilbert identity or a definition of homology.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BarQuadraticPairing

open WeightedBar DiagonalBarWords DiagonalBarRelations AugmentedAlgebraBasis
open QuadraticWordFunctionals

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "J₁" => DegreeOne δ
local notation "F" => FreeAlgebra K J₁
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := J₁))

def wordSpaceBasis (n : ℕ) : Module.Basis (PureWord δ n) K (degreeSpace b n) := by
  let v : PureWord δ n → F := fun L ↦ b L.val
  have hli : LinearIndependent K v :=
    (b).linearIndependent.comp Subtype.val Subtype.val_injective
  have hs : Submodule.span K (Set.range v)=degreeSpace b n := by
    congr 1
    ext x
    constructor
    · rintro ⟨L,rfl⟩
      exact ⟨L.val,L.property,rfl⟩
    · rintro ⟨L,hL,rfl⟩
      exact ⟨⟨L,hL⟩,rfl⟩
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs)

@[simp] theorem wordSpaceBasis_val (n : ℕ) (L : PureWord δ n) :
    (wordSpaceBasis (K := K) δ n L).val=b L.val := by
  simp only [wordSpaceBasis,Module.Basis.map_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (Module.Basis.coe_span_apply _ L)

/-- Finite coefficient pairing on the actual diagonal word basis. -/
def pairing (n : ℕ) : piece (K := K) δ n n ≃ₗ[K] Module.Dual K (degreeSpace b n) :=
  (diagonalBasis δ hpos n).repr.trans (wordSpaceBasis δ n).dualBasis.repr.symm

@[simp] theorem pairing_basis (n : ℕ) (z : piece (K := K) δ n n)
    (L : PureWord δ n) :
    pairing δ hpos n z (wordSpaceBasis δ n L)=z.val (embedWord δ L.val) := by
  rw [←Module.Basis.dualBasis_repr]
  change (wordSpaceBasis δ n).dualBasis.repr
    ((wordSpaceBasis δ n).dualBasis.repr.symm ((diagonalBasis δ hpos n).repr z)) L=_
  rw [LinearEquiv.apply_symm_apply,diagonalBasis_repr]

/-- Extend a homogeneous functional by the genuine word-degree projection. -/
def extendedPairing (n : ℕ) (z : piece (K := K) δ n n) : F →ₗ[K] K :=
  (pairing δ hpos n z).comp (projectionToPiece b n)

@[simp] theorem extendedPairing_basis (n : ℕ) (z : piece (K := K) δ n n)
    (L : List J₁) : extendedPairing δ hpos n z (b L)=z.val (embedWord δ L) := by
  by_cases hL : L.length=n
  · have he : projectionToPiece b n (b L)=wordSpaceBasis δ n ⟨L,hL⟩ := by
      apply Subtype.ext
      rw [projectionToPiece_val,projection_basis,if_pos hL,wordSpaceBasis_val]
    change pairing δ hpos n z (projectionToPiece b n (b L))=_
    rw [he,pairing_basis]
  · have he : projectionToPiece b n (b L)=0 := by
      apply Subtype.ext
      rw [projectionToPiece_val,projection_basis,if_neg hL]
      rfl
    change pairing δ hpos n z (projectionToPiece b n (b L))=_
    rw [he,map_zero]
    symm
    by_contra hn
    have hz := z.property (Finsupp.mem_support_iff.mpr hn)
    exact hL ((embedWord_length δ L).symm.trans hz.1)

/-- Literal multiplication-row relation in the actual free algebra. -/
def rowRelation (c : DegreeTwo δ) : F :=
  ∑ a : J₁,∑ d : J₁,productCoefficients B a.val d.val c.val • b [a,d]

def relationSpace : Submodule K F := Submodule.span K (Set.range (rowRelation B δ))

theorem relationSpace_homogeneous : relationSpace B δ≤degreeSpace b 2 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro d hd
  exact Submodule.smul_mem _ _ (basis_mem_degreeSpace b [a,d])

include hpos in
theorem extendedPairing_row (n : ℕ) (z : piece (K := K) δ n n)
    (P : List J₁) (c : DegreeTwo δ) (Q : List J₁) :
    extendedPairing δ hpos n z (b P*rowRelation B δ c*b Q)=
      contextRow B δ z.val P c Q := by
  simp only [rowRelation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  rw [←FreeAlgebraWordDegree.basis_append,←FreeAlgebraWordDegree.basis_append,
    extendedPairing_basis]
  simp only [embedWord,List.map_append,List.map_cons,List.map_nil,
    List.append_assoc,List.cons_append,List.nil_append]

include hpos in
theorem pairing_mem_relationFunctionals_iff (n : ℕ) (z : piece (K := K) δ n n) :
    pairing δ hpos n z∈relationFunctionals b (relationSpace B δ) n ↔
      ∀ P : List J₁,∀ c : DegreeTwo δ,∀ Q : List J₁,contextRow B δ z.val P c Q=0 := by
  constructor
  · intro h P c Q
    have he := h P Q (rowRelation B δ c) (Submodule.subset_span ⟨c,rfl⟩)
    exact (extendedPairing_row B δ hpos n z P c Q).symm.trans he
  · intro h P Q q hq
    change extendedPairing δ hpos n z (b P*q*b Q)=0
    induction hq using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨c,rfl⟩ := hq
        exact (extendedPairing_row B δ hpos n z P c Q).trans (h P c Q)
    | zero => simp only [mul_zero,zero_mul,map_zero]
    | add x y hx hy ihx ihy =>
        simp only [mul_add,add_mul,map_add,ihx,ihy,add_zero]
    | smul a x hx ih =>
        simp only [mul_smul_comm,smul_mul_assoc,map_smul,ih,smul_zero]

/-- Kernel of the actual reduced-bar outgoing differential, in its original degree. -/
def diagonalCycles (n : ℕ) : Submodule K (piece (K := K) δ n n) :=
  LinearMap.ker ((ReducedBarBasis.differential B).comp (piece δ n n).subtype)

include hpos hδ in
theorem diagonalCycles_eq_comap (r : ℕ) :
    diagonalCycles B δ (r+1)=
      (relationFunctionals b (relationSpace B δ) (r+1)).comap
        (pairing δ hpos (r+1)).toLinearMap := by
  ext z
  change ReducedBarBasis.differential B z.val=0 ↔
    pairing δ hpos (r+1) z∈relationFunctionals b (relationSpace B δ) (r+1)
  rw [differential_eq_zero_iff_contexts B δ hpos hδ,
    pairing_mem_relationFunctionals_iff B δ hpos]

/-- Actual diagonal cycles are dual to the actual multiplication-row quotient piece. -/
def cyclesDualQuotientEquiv (r : ℕ) :
    diagonalCycles B δ (r+1) ≃ₗ[K]
      Module.Dual K (quotientPiece b (relationSpace B δ) (r+1)) :=
  ((LinearEquiv.ofEq _ _ (diagonalCycles_eq_comap B δ hpos hδ r)).trans
    ((pairing δ hpos (r+1)).ofSubmodule'
      (relationFunctionals b (relationSpace B δ) (r+1)))).trans
    (dualPieceEquiv b FreeAlgebraWordDegree.basis_append (relationSpace B δ)
      (relationSpace_homogeneous B δ) (r+1)).symm

end PaperVerification.BarQuadraticPairing
end
end
end TAF_LiteralSource_0514

section TAF_LiteralSource_0515
/- Original module: PaperVerification.BarDiagonalHomology -/


/-!
# Actual diagonal bar homology and the multiplication-row quadratic quotient

Positivity makes the incoming top differential vanish. This file uses
Mathlib's genuine homology-to-cycles isomorphism, then the explicit finite
coefficient pairing, to identify every positive diagonal homology group
with the dual of the actual homogeneous quadratic quotient piece.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.BarDiagonalHomology

open WeightedBar DiagonalBarWords BarQuadraticPairing AugmentedAlgebraBasis
open QuadraticWordFunctionals

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ) (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "C" n => internalComplex ε B hunit hε δ hδ n
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := DegreeOne δ))

theorem internalKernel_eq_diagonalCycles (r : ℕ) :
    LinearMap.ker (internalDifferential B δ hδ r (r+1))=
      diagonalCycles B δ (r+1) := by
  ext z
  change internalDifferential B δ hδ r (r+1) z=0 ↔
    ReducedBarBasis.differential B z.val=0
  constructor
  · intro hz
    have he := congrArg Subtype.val hz
    exact neg_eq_zero.mp he
  · intro hz
    apply Subtype.ext
    change -ReducedBarBasis.differential B z.val=0
    rw [hz,neg_zero]

/-- Incoming boundaries vanish by actual internal degree, so the actual
categorical homology is precisely the actual outgoing kernel. -/
def homologyCyclesEquiv (r : ℕ) :
    ((C (r+1)).homology (r+1)) ≃ₗ[K] diagonalCycles B δ (r+1) := by
  let e : ((C (r+1)).homology (r+1)) ≅
      ModuleCat.of K (LinearMap.ker (((C (r+1)).d (r+1) r).hom)) :=
    ((C (r+1)).isoHomologyπ (r+2) (r+1) (by simp)
      (internalComplex_top_differential ε B hunit hε δ hδ hpos (r+1))).symm ≪≫
      (C (r+1)).cyclesIsoSc' (r+2) (r+1) r (by simp) (by simp) ≪≫
        ((C (r+1)).sc' (r+2) (r+1) r).moduleCatCyclesIso
  exact e.toLinearEquiv.trans (LinearEquiv.ofEq _ _ (by
    rw [internalComplex_d]
    exact internalKernel_eq_diagonalCycles B δ hδ r))

/-- The comparison is with an independently defined genuine algebra
quotient, and holds without a Koszulness hypothesis. -/
def homologyDualQuotientEquiv (r : ℕ) :
    ((C (r+1)).homology (r+1)) ≃ₗ[K]
      Module.Dual K (quotientPiece b (relationSpace B δ) (r+1)) :=
  (homologyCyclesEquiv ε B hunit hε δ hpos hδ r).trans
    (cyclesDualQuotientEquiv B δ hpos hδ r)

include hpos in
theorem diagonal_finrank_eq_quotient_finrank (r : ℕ) :
    Module.finrank K ((C (r+1)).homology (r+1))=
      Module.finrank K (quotientPiece b (relationSpace B δ) (r+1)) := by
  letI : Module.Finite K (degreeSpace b (r+1)) :=
    Module.Finite.of_basis (wordSpaceBasis (K := K) δ (r+1))
  letI : Module.Finite K (quotientPiece b (relationSpace B δ) (r+1)) :=
    Module.Finite.of_surjective (pieceMap b (relationSpace B δ) (r+1))
      (pieceMap_surjective b (relationSpace B δ) (r+1))
  exact (homologyDualQuotientEquiv ε B hunit hε δ hpos hδ r).finrank_eq.trans
    (Subspace.dual_finrank_eq)

end PaperVerification.BarDiagonalHomology
end
end
end TAF_LiteralSource_0515

section TAF_LiteralSource_0516
/- Original module: PaperVerification.HomogeneousMultiplicationRows -/


/-!
# Actual homogeneous multiplication rows and the tensor annihilator

The degree-one and degree-two bases restrict a genuine homogeneous augmented
basis to its actual homogeneous pieces. Multiplication is independently
defined by the original ring product. Its coefficient rows span exactly
the annihilator of its kernel, with the canonical tensor evaluation pairing.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.HomogeneousMultiplicationRows

open AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))

/-- Literal homogeneous vectors form a basis of the actual piece. -/
def homogeneousBasis (d : ℕ) (hd : 0<d) :
    Module.Basis {i : I // δ i=d} K (G.piece d) :=
  (Module.Basis.span (B.linearIndependent.comp
    (fun i : {i : I // δ i=d} => some i.val)
    (fun i j h => Subtype.ext (Option.some.inj h)))).map
      (LinearEquiv.ofEq _ _
        (HomogeneousBasisProfile.span_degree G B δ hzero hunit hhom d hd))

@[simp] theorem homogeneousBasis_val (d : ℕ) (hd : 0<d)
    (i : {i : I // δ i=d}) :
    (homogeneousBasis G B δ hzero hunit hhom d hd i : A)=B (some i.val) := by
  simp only [homogeneousBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply,Function.comp_apply]

/-- Restricted dual coordinates are the original coefficients. -/
theorem homogeneousBasis_dual_eval (d : ℕ) (hd : 0<d)
    (i : {i : I // δ i=d}) (x : G.piece d) :
    (homogeneousBasis G B δ hzero hunit hhom d hd).dualBasis i x=
      B.repr x.val (some i.val) := by
  have he : (homogeneousBasis G B δ hzero hunit hhom d hd).dualBasis i=
      (B.coord (some i.val)).comp (G.piece d).subtype := by
    apply (homogeneousBasis G B δ hzero hunit hhom d hd).ext
    intro j
    rw [Module.Basis.dualBasis_apply_self]
    simp only [LinearMap.comp_apply,Submodule.subtype_apply,homogeneousBasis_val,
      Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      Option.some.injEq,Subtype.ext_iff]
  rw [he]
  rfl

/-- Original multiplication, restricted only in its domain. -/
def multiplicationAmbient : (G.piece 1 ⊗[K] G.piece 1) →ₗ[K] A :=
  TensorProduct.lift ((LinearMap.mul K A).compl₁₂
    (G.piece 1).subtype (G.piece 1).subtype)

@[simp] theorem multiplicationAmbient_tmul (x y : G.piece 1) :
    multiplicationAmbient G (x ⊗ₜ[K] y)=x.val*y.val := rfl

variable (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hmul in
theorem multiplicationAmbient_mem (z : G.piece 1 ⊗[K] G.piece 1) :
    multiplicationAmbient G z∈G.piece 2 := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | tmul x y =>
      rw [multiplicationAmbient_tmul]
      exact hmul 1 1 x.val y.val x.property y.property
  | add z w hz hw =>
      rw [map_add]
      exact Submodule.add_mem _ hz hw

/-- Actual multiplication into the actual degree-two piece. -/
def multiplication : (G.piece 1 ⊗[K] G.piece 1) →ₗ[K] G.piece 2 :=
  (multiplicationAmbient G).codRestrict (G.piece 2) (multiplicationAmbient_mem G hmul)

@[simp] theorem multiplication_val (z : G.piece 1 ⊗[K] G.piece 1) :
    (multiplication G hmul z : A)=multiplicationAmbient G z := rfl

@[simp] theorem multiplication_tmul_val (x y : G.piece 1) :
    (multiplication G hmul (x ⊗ₜ[K] y) : A)=x.val*y.val := rfl

theorem multiplication_eq_zero_iff (z : G.piece 1 ⊗[K] G.piece 1) :
    multiplication G hmul z=0 ↔ multiplicationAmbient G z=0 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- An actual degree-two coordinate pulled back by multiplication. -/
def row (c : {i : I // δ i=2}) :
    Module.Dual K (G.piece 1 ⊗[K] G.piece 1) :=
  (multiplication G hmul).dualMap
    ((homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c)

theorem row_tmul (c : {i : I // δ i=2}) (x y : G.piece 1) :
    row G B δ hzero hunit hhom hmul c (x ⊗ₜ[K] y)=
      B.repr (x.val*y.val) (some c.val) := by
  change (homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c
    (multiplication G hmul (x ⊗ₜ[K] y))=_
  rw [homogeneousBasis_dual_eval,multiplication_tmul_val]

/-- The entries are literally productCoefficients of the original basis. -/
theorem row_tmul_basis (c : {i : I // δ i=2})
    (a b : {i : I // δ i=1}) :
    row G B δ hzero hunit hhom hmul c
      (homogeneousBasis G B δ hzero hunit hhom 1 (by decide) a ⊗ₜ[K]
       homogeneousBasis G B δ hzero hunit hhom 1 (by decide) b)=
      productCoefficients B a.val b.val c.val := by
  rw [row_tmul,homogeneousBasis_val,homogeneousBasis_val]
  rfl

/-- Linear duality for an abstract module map, before specializing to grading data. -/
theorem span_range_dualMap_basis {V W J : Type*}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] [Finite J] [DecidableEq J]
    (f : V →ₗ[K] W) (b : Module.Basis J K W) :
    Submodule.span K (Set.range (fun j => f.dualMap (b.dualBasis j)))=
      (LinearMap.ker f).dualAnnihilator := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  calc
    Submodule.span K (Set.range (fun j => f.dualMap (b.dualBasis j)))=
        (Submodule.span K (Set.range b.dualBasis)).map f.dualMap := by
      rw [Submodule.map_span,←Set.range_comp]
      rfl
    _ = LinearMap.range f.dualMap := by
      rw [b.dualBasis.span_eq,Submodule.map_top]
    _ = (LinearMap.ker f).dualAnnihilator :=
      LinearMap.range_dualMap_eq_dualAnnihilator_ker f

set_option maxHeartbeats 800000 in
/-- No surjectivity or rank hypothesis on multiplication is used. -/
theorem row_span_eq_dualAnnihilator :
    Submodule.span K (Set.range (row G B δ hzero hunit hhom hmul))=
      (LinearMap.ker (multiplication G hmul)).dualAnnihilator := by
  have h := span_range_dualMap_basis (K := K)
    (V := G.piece 1 ⊗[K] G.piece 1) (W := G.piece 2)
    (J := {i : I // δ i=2}) (multiplication G hmul)
    (homogeneousBasis G B δ hzero hunit hhom 2 (by decide))
  have hr : row G B δ hzero hunit hhom hmul =
      (fun c : {i : I // δ i=2} => (multiplication G hmul).dualMap
        ((homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c)) := by
    funext c
    rfl
  exact (congrArg (fun f : {i : I // δ i=2} →
    Module.Dual K (G.piece 1 ⊗[K] G.piece 1) => Submodule.span K (Set.range f)) hr).trans h

/-- A literal coefficient row in the actual degree-one dual tensor square. -/
def tensorRow (c : {i : I // δ i=2}) :
    Module.Dual K (G.piece 1) ⊗[K] Module.Dual K (G.piece 1) :=
  ∑ a : {i : I // δ i=1},∑ b : {i : I // δ i=1},
    productCoefficients B a.val b.val c.val •
      ((homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis a ⊗ₜ[K]
       (homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis b)

/-- Canonical tensor evaluation identifies the coefficient row. -/
theorem dualDistrib_tensorRow (c : {i : I // δ i=2}) :
    TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)
        (tensorRow G B δ hzero hunit hhom c)=
      row G B δ hzero hunit hhom hmul c := by
  apply ((homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).tensorProduct
    (homogeneousBasis G B δ hzero hunit hhom 1 (by decide))).ext
  rintro ⟨a,b⟩
  rw [Module.Basis.tensorProduct_apply,row_tmul_basis]
  simp [tensorRow,TensorProduct.dualDistrib_apply,
    Module.Basis.dualBasis_apply_self,Finsupp.single_apply,smul_eq_mul,mul_ite,ite_mul]

/-- Equality with the conventional annihilator in the actual dual tensor square. -/
theorem tensorRow_span_eq_actual_annihilator :
    Submodule.span K (Set.range (tensorRow G B δ hzero hunit hhom))=
      (LinearMap.ker (multiplication G hmul)).dualAnnihilator.comap
        (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
  letI : Module.Finite K (G.piece 1) :=
    Module.Finite.of_basis (homogeneousBasis G B δ hzero hunit hhom 1 (by decide))
  have hi : Function.Injective (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
    rw [←TensorProduct.toLinearMap_dualDistribEquiv]
    exact (TensorProduct.dualDistribEquiv K (G.piece 1) (G.piece 1)).injective
  have hs : Function.Surjective (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
    rw [←TensorProduct.toLinearMap_dualDistribEquiv]
    exact (TensorProduct.dualDistribEquiv K (G.piece 1) (G.piece 1)).surjective
  apply Submodule.map_injective_of_injective hi
  rw [Submodule.map_comap_eq_of_surjective hs,Submodule.map_span,←Set.range_comp]
  have he :
      (fun c : {i : I // δ i=2} =>
        TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)
          (tensorRow G B δ hzero hunit hhom c))=
        row G B δ hzero hunit hhom hmul := by
    funext c
    exact dualDistrib_tensorRow G B δ hzero hunit hhom hmul c
  simp only [Function.comp_def]
  rw [he]
  exact row_span_eq_dualAnnihilator G B δ hzero hunit hhom hmul

end PaperVerification.HomogeneousMultiplicationRows
end
end
end TAF_LiteralSource_0516

section TAF_LiteralSource_0517
/- Original module: PaperVerification.HomogeneousQuadraticDual -/


/-!
# The multiplication-row quotient is the conventional quadratic dual

The intrinsic dual is the actual tensor algebra on the actual degree-one
dual, modulo the annihilator of actual multiplication. It does not depend
on a choice of homogeneous basis. The proved comparison with the literal
multiplication-row quotient preserves generators and all their powers.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct Pointwise

namespace PaperVerification.HomogeneousQuadraticDual

section QuotientTransport
variable {K A D : Type*} [Field K] [Ring A] [Algebra K A] [Ring D] [Algebra K D]

theorem relation_iff (S : Submodule K A) (x y : A) :
    QuadraticWordFunctionals.Relation S x y ↔ x∈S ∧ y=0 := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact QuadraticWordFunctionals.Relation.relation x hx

def ofRelationEq {r s : A → A → Prop} (h : r=s) : RingQuot r ≃ₐ[K] RingQuot s := by
  cases h
  exact AlgEquiv.refl

@[simp] theorem ofRelationEq_mk {r s : A → A → Prop} (h : r=s) (x : A) :
    ofRelationEq (K := K) h (RingQuot.mkAlgHom K r x)=RingQuot.mkAlgHom K s x := by
  cases h
  rfl

theorem transported_relation (e : A ≃ₐ[K] D) (S : Submodule K A) :
    (fun x y : D => QuadraticWordFunctionals.Relation S (e.symm x) (e.symm y))=
      QuadraticWordFunctionals.Relation (S.map e.toLinearMap) := by
  funext x y
  apply propext
  rw [relation_iff,relation_iff,Submodule.mem_map_equiv (e := e.toLinearEquiv)]
  change (e.symm x∈S ∧ e.symm y=0) ↔ (e.symm x∈S ∧ y=0)
  exact and_congr_right (fun _ => e.symm.toRingEquiv.map_eq_zero_iff)

def quotientEquivMap (e : A ≃ₐ[K] D) (S : Submodule K A) :
    QuadraticWordFunctionals.Quotient S ≃ₐ[K]
      QuadraticWordFunctionals.Quotient (S.map e.toLinearMap) :=
  (RingQuot.algEquivQuotAlgEquiv e (QuadraticWordFunctionals.Relation S)).trans
    (ofRelationEq (transported_relation e S))

@[simp] theorem quotientEquivMap_mk (e : A ≃ₐ[K] D) (S : Submodule K A) (x : A) :
    quotientEquivMap e S (QuadraticWordFunctionals.quotientMap S x)=
      QuadraticWordFunctionals.quotientMap (S.map e.toLinearMap) (e x) := by
  simp only [quotientEquivMap,QuadraticWordFunctionals.quotientMap,AlgEquiv.trans_apply,
    RingQuot.algEquivQuotAlgEquiv,AlgEquiv.ofAlgHom_apply,
    RingQuot.liftAlgHom_mkAlgHom_apply,AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,
    ofRelationEq_mk]

def ofSubmoduleEq {S T : Submodule K A} (h : S=T) :
    QuadraticWordFunctionals.Quotient S ≃ₐ[K] QuadraticWordFunctionals.Quotient T := by
  cases h
  exact AlgEquiv.refl

@[simp] theorem ofSubmoduleEq_mk {S T : Submodule K A} (h : S=T) (x : A) :
    ofSubmoduleEq h (QuadraticWordFunctionals.quotientMap S x)=
      QuadraticWordFunctionals.quotientMap T x := by
  cases h
  rfl
end QuotientTransport

section TensorInclusion
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The genuine degree-two inclusion in the tensor algebra. -/
def quadraticInclusion : (V ⊗[K] V) →ₗ[K] TensorAlgebra K V :=
  TensorProduct.lift ((LinearMap.mul K (TensorAlgebra K V)).compl₁₂
    (TensorAlgebra.ι K) (TensorAlgebra.ι K))

@[simp] theorem quadraticInclusion_tmul (x y : V) :
    quadraticInclusion (x ⊗ₜ[K] y)=TensorAlgebra.ι K x*TensorAlgebra.ι K y := rfl
end TensorInclusion

section Intrinsic
universe u
variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (G : TauCeti.InternalGrading K A ℕ)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

/-- Conventional annihilator of the actual quadratic multiplication kernel. -/
def dualRelations : Submodule K (Module.Dual K (G.piece 1) ⊗[K] Module.Dual K (G.piece 1)) :=
  (LinearMap.ker (HomogeneousMultiplicationRows.multiplication G hmul)).dualAnnihilator.comap
    (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1))

def tensorRelationSpace : Submodule K (TensorAlgebra K (Module.Dual K (G.piece 1))) :=
  (dualRelations G hmul).map
    (quadraticInclusion (K := K) (V := Module.Dual K (G.piece 1)))

/-- The actual tensor-algebra quadratic dual, independent of B and δ. -/
abbrev conventionalDual := QuadraticWordFunctionals.Quotient (tensorRelationSpace G hmul)

def generatorMap : Module.Dual K (G.piece 1) →ₗ[K] conventionalDual G hmul :=
  (QuadraticWordFunctionals.quotientMap (tensorRelationSpace G hmul)).toLinearMap.comp
    (TensorAlgebra.ι K)

def wordPiece (n : ℕ) : Submodule K (conventionalDual G hmul) :=
  (generatorMap G hmul).range^n
end Intrinsic

section Coordinates
universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

local notation "J₁" => DiagonalBarWords.DegreeOne δ
local notation "J₂" => DiagonalBarWords.DegreeTwo δ
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := J₁))

def coordinateEquiv : TensorAlgebra K (Module.Dual K (G.piece 1)) ≃ₐ[K] FreeAlgebra K J₁ :=
  TensorAlgebra.equivFreeAlgebra
    (HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis

theorem freeWord_pair (a d : J₁) :
    b [a,d]=FreeAlgebra.ι K a*FreeAlgebra.ι K d := by
  change b ([a]++[d])=_
  rw [FreeAlgebraWordDegree.basis_append,FreeAlgebraWordDegree.basis_singleton,
    FreeAlgebraWordDegree.basis_singleton]

/-- Literal row tensors map to the independently defined free-algebra rows. -/
theorem tensorRow_image (c : J₂) :
    coordinateEquiv G B δ hzero hunit hhom
        (quadraticInclusion (HomogeneousMultiplicationRows.tensorRow G B δ hzero hunit hhom c))=
      BarQuadraticPairing.rowRelation B δ c := by
  simp only [HomogeneousMultiplicationRows.tensorRow,map_sum,map_smul,
    quadraticInclusion_tmul,map_mul,coordinateEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply,BarQuadraticPairing.rowRelation,freeWord_pair]

theorem tensorRelationSpace_image_eq :
    (tensorRelationSpace G hmul).map (coordinateEquiv G B δ hzero hunit hhom).toLinearMap=
      BarQuadraticPairing.relationSpace B δ := by
  rw [tensorRelationSpace,dualRelations,
    ←HomogeneousMultiplicationRows.tensorRow_span_eq_actual_annihilator G B δ hzero hunit hhom hmul,
    ←Submodule.map_comp,Submodule.map_span,←Set.range_comp]
  change Submodule.span K (Set.range (fun c : J₂ =>
      coordinateEquiv G B δ hzero hunit hhom
        (quadraticInclusion (HomogeneousMultiplicationRows.tensorRow G B δ hzero hunit hhom c))))=
    Submodule.span K (Set.range (BarQuadraticPairing.rowRelation B δ))
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext c
  exact tensorRow_image G B δ hzero hunit hhom c

/-- A genuine algebra equivalence from the conventional dual to the row quotient. -/
def rowQuotientEquiv : conventionalDual G hmul ≃ₐ[K]
    QuadraticWordFunctionals.Quotient (BarQuadraticPairing.relationSpace B δ) :=
  (quotientEquivMap (coordinateEquiv G B δ hzero hunit hhom)
    (tensorRelationSpace G hmul)).trans
      (ofSubmoduleEq (tensorRelationSpace_image_eq G B δ hzero hunit hhom hmul))

@[simp] theorem rowQuotientEquiv_generator (i : J₁) :
    rowQuotientEquiv G B δ hzero hunit hhom hmul
        (generatorMap G hmul
          ((HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1
            (by decide)).dualBasis i))=
      QuadraticWordFunctionals.quotientMap (BarQuadraticPairing.relationSpace B δ)
        (FreeAlgebra.ι K i) := by
  simp only [rowQuotientEquiv,AlgEquiv.trans_apply,generatorMap,LinearMap.comp_apply,
    AlgHom.toLinearMap_apply,quotientEquivMap_mk,ofSubmoduleEq_mk,coordinateEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply]

theorem generatorSpace_transport :
    (generatorMap G hmul).range.map (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap=
      QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) 1 := by
  rw [←LinearMap.range_comp]
  let b₁ := (HomogeneousMultiplicationRows.homogeneousBasis G B δ hzero hunit hhom 1
    (by decide)).dualBasis
  let L := (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap.comp
    (generatorMap G hmul)
  change LinearMap.range L=_
  calc
    LinearMap.range L=(Submodule.span K (Set.range b₁)).map L := by
      rw [b₁.span_eq,Submodule.map_top]
    _ = Submodule.span K (Set.range (fun i : J₁ =>
        QuadraticWordFunctionals.quotientMap (BarQuadraticPairing.relationSpace B δ)
          (FreeAlgebra.ι K i))) := by
      rw [Submodule.map_span,←Set.range_comp]
      apply congrArg (Submodule.span K)
      apply congrArg Set.range
      funext i
      exact rowQuotientEquiv_generator G B δ hzero hunit hhom hmul i
    _ = QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) 1 := by
      rw [QuadraticWordFunctionals.quotientPiece,FreeAlgebraWordDegree.degreeSpace_one,
        FreeAlgebraWordDegree.generatorSpace,Submodule.map_span,←Set.range_comp]
      rfl

/-- Every natural generator degree is preserved, including degree zero. -/
theorem wordPiece_transport (n : ℕ) :
    (wordPiece G hmul n).map (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap=
      QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n := by
  change ((generatorMap G hmul).range^n).map
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((generatorMap G hmul).range.map
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap)^n = _
  rw [generatorSpace_transport]
  exact (QuadraticWordFunctionals.quotientPiece_eq_power b
    FreeAlgebraWordDegree.basis_append FreeAlgebraWordDegree.basis_nil
    (BarQuadraticPairing.relationSpace B δ) n).symm

def rowDegreeEquiv (n : ℕ) : wordPiece G hmul n ≃ₗ[K]
    QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n :=
  (Submodule.equivMapOfInjective
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).toLinearMap
    (rowQuotientEquiv G B δ hzero hunit hhom hmul).injective (wordPiece G hmul n)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport G B δ hzero hunit hhom hmul n))

include hzero hunit hhom in
theorem degree_finrank_eq (n : ℕ) :
    Module.finrank K (wordPiece G hmul n)=
      Module.finrank K
        (QuadraticWordFunctionals.quotientPiece b (BarQuadraticPairing.relationSpace B δ) n) :=
  (rowDegreeEquiv G B δ hzero hunit hhom hmul n).finrank_eq
end Coordinates

end PaperVerification.HomogeneousQuadraticDual
end
end
end TAF_LiteralSource_0517

section TAF_LiteralSource_0518
/- Original module: PaperVerification.HomogeneousDiagonalDuality -/


/-!
# Actual positive diagonal homology equals the intrinsic quadratic-dual degree

This comparison is basis independent on its quadratic-dual side. It uses
the actual bar differential, actual categorical homology, original algebra
multiplication, and the canonical tensor annihilator. Koszulness is not a
hypothesis. All positive degrees and every finite homogeneous basis are
included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.HomogeneousDiagonalDuality

open AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)
  (hε : ∀ i,ε (B (some i))=0)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hzero hhom hpos in
theorem diagonal_finrank_eq_intrinsic (r : ℕ) :
    Module.finrank K
      ((WeightedBar.internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1))=
      Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
  (BarDiagonalHomology.diagonal_finrank_eq_quotient_finrank
    ε B hunit hε δ hpos hδ r).trans
      (HomogeneousQuadraticDual.degree_finrank_eq G B δ hzero hunit hhom hmul (r+1)).symm

end PaperVerification.HomogeneousDiagonalDuality
end
end
end TAF_LiteralSource_0518

section TAF_LiteralSource_0519
/- Original module: PaperVerification.KoszulDiagonalSeries -/


/-!
# Converting actual diagonal homology dimensions into the Koszul identity

This general comparison lemma uses ordinary Tor concentration, the proved
finite bar Euler identity, and an explicitly supplied comparison with the
actual positive diagonal homology dimensions. The constant term follows
from Euler itself. Applications must prove every dimension comparison;
none is inserted as a new axiom or a definition of Koszulness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped PowerSeries

namespace PaperVerification.KoszulDiagonalSeries

open WeightedBar AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ) (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hpos in
/-- All comparison assumptions are explicit and concern actual categorical
homology, independently constructed before the Hilbert identity. -/
theorem one_add_mul_signed_series
    (H : PowerSeries ℤ) (hzero : PowerSeries.coeff 0 H=1)
    (hdim : ∀ r,(Module.finrank K
      ((internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1)) : ℤ)=
        PowerSeries.coeff (r+1) H)
    (hKoszul : HasDiagonalTor ε B hunit hε δ hδ) :
    (1+positiveSeries δ)*PowerSeries.rescale (-1 : ℤ) H=1 := by
  let D := WeightedBarEuler.diagonalHomologySeries
    (internalComplex ε B hunit hε δ hδ)
  have hEuler : (1+positiveSeries δ)*D=1 :=
    one_add_mul_signed_diagonalTor ε B hunit hε δ hδ hpos hKoszul
  have hDzero : PowerSeries.coeff 0 D=1 := by
    have he := congrArg PowerSeries.constantCoeff hEuler
    simp only [map_mul,map_add,map_one,positiveSeries_constantCoeff δ hpos,
      add_zero,one_mul] at he
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using he
  have he : D=PowerSeries.rescale (-1 : ℤ) H := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        rw [hDzero,PowerSeries.coeff_rescale,pow_zero,one_mul,hzero]
    | succ r =>
        simp only [D,WeightedBarEuler.diagonalHomologySeries,PowerSeries.coeff_mk,
          PowerSeries.coeff_rescale]
        rw [hdim r]
  rw [←he]
  exact hEuler

end PaperVerification.KoszulDiagonalSeries
end
end
end TAF_LiteralSource_0519

section TAF_LiteralSource_0520
/- Original module: PaperVerification.AlternatingFormsIntrinsicTensorFunctor -/


/-! # Tensor-algebra functoriality and the canonical dual pairing

These exact generic maps support the intrinsic quadratic-dual identification.
They are split from that application solely to check their actual proof bodies
with the abstract diagonal-homology dependencies.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.IntrinsicQuadraticDual

section TensorFunctor

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def tensorAlgebraMap (e : V →ₗ[K] W) : TensorAlgebra K V →ₐ[K] TensorAlgebra K W :=
  TensorAlgebra.lift K ((TensorAlgebra.ι K).comp e)

@[simp] theorem tensorAlgebraMap_ι (e : V →ₗ[K] W) (x : V) :
    tensorAlgebraMap e (TensorAlgebra.ι K x)=TensorAlgebra.ι K (e x) := by
  rw [tensorAlgebraMap,TensorAlgebra.lift_ι_apply,LinearMap.comp_apply]

def tensorAlgebraCongr (e : V ≃ₗ[K] W) : TensorAlgebra K V ≃ₐ[K] TensorAlgebra K W :=
  AlgEquiv.ofAlgHom (tensorAlgebraMap e.toLinearMap) (tensorAlgebraMap e.symm.toLinearMap)
    (by
      apply TensorAlgebra.hom_ext
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        tensorAlgebraMap_ι,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,AlgHom.id_apply])
    (by
      apply TensorAlgebra.hom_ext
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,AlgHom.comp_apply,
        tensorAlgebraMap_ι,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,AlgHom.id_apply])

@[simp] theorem tensorAlgebraCongr_ι (e : V ≃ₗ[K] W) (x : V) :
    tensorAlgebraCongr e (TensorAlgebra.ι K x)=TensorAlgebra.ι K (e x) :=
  tensorAlgebraMap_ι e.toLinearMap x

theorem tensorAlgebraCongr_quadratic (e : V ≃ₗ[K] W) :
    (tensorAlgebraCongr e).toLinearMap.comp
        (HomogeneousQuadraticDual.quadraticInclusion (K := K) (V := V))=
      HomogeneousQuadraticDual.quadraticInclusion.comp
        (TensorProduct.congr e e).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change tensorAlgebraCongr e
      (HomogeneousQuadraticDual.quadraticInclusion (x ⊗ₜ[K] y))=
    HomogeneousQuadraticDual.quadraticInclusion
      (TensorProduct.congr e e (x ⊗ₜ[K] y))
  rw [HomogeneousQuadraticDual.quadraticInclusion_tmul,TensorProduct.congr_tmul,
    HomogeneousQuadraticDual.quadraticInclusion_tmul,map_mul,
    tensorAlgebraCongr_ι,tensorAlgebraCongr_ι]

/-- Functoriality of the actual canonical tensor evaluation pairing. -/
theorem tensorDual_pairing (e : V ≃ₗ[K] W)
    (q : Module.Dual K W ⊗[K] Module.Dual K W) (z : V ⊗[K] V) :
    TensorProduct.dualDistrib K V V (TensorProduct.congr e.dualMap e.dualMap q) z=
      TensorProduct.dualDistrib K W W q (TensorProduct.congr e e z) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [map_zero,LinearMap.zero_apply]
  | tmul φ ψ =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y =>
          simp only [TensorProduct.congr_tmul,TensorProduct.dualDistrib_apply,
            LinearEquiv.dualMap_apply]
      | add z w hz hw => simp only [map_add,hz,hw]
  | add q r hq hr =>
      simp only [map_add,LinearMap.add_apply,hq,hr]

end TensorFunctor

end PaperVerification.AlternatingForms.IntrinsicQuadraticDual
end
end
end TAF_LiteralSource_0520

section TAF_LiteralSource_0521
/- Original module: PaperVerification.AlternatingFormsActualQuadraticKernel -/


/-!
# The actual exterior quotient multiplication kernel

The generator map is the original exterior inclusion followed by the
literal quotient map. Its tensor-square multiplication is proved to factor
through the ordinary wedge map. The kernel is exactly the inverse image
of the span of the two given forms, and the actual dual-tensor annihilator
is exactly the relation space used by the quadratic dual. No genericity,
rank, or Koszul premise enters these comparisons.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The actual degree-one generators in the original ring quotient. -/
def actualGenerator : (ν → K) →ₗ[K] ExteriorAugmented.Quotient f g :=
  (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap.comp (ExteriorAlgebra.ι K)

@[simp] theorem actualGenerator_apply (v : ν → K) :
    actualGenerator f g v=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (ExteriorAlgebra.ι K v) := rfl

theorem actualGenerator_injective : Function.Injective (actualGenerator f g) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change actualGenerator f g v=0 at hv
  have hι : ExteriorAlgebra.ι K v∈(⋀[K]^1 (ν → K)) := by
    rw [ExteriorAlgebra.exteriorPower,pow_one]
    exact ⟨v,rfl⟩
  have hrel : (⟨ExteriorAlgebra.ι K v,hι⟩ : ⋀[K]^1 (ν → K))∈
      exteriorDegreeRelations f g 1 := by
    change ExteriorAlgebra.ι K v∈exteriorRelationIdeal f g
    exact Ideal.Quotient.eq_zero_iff_mem.mp hv
  rw [exteriorDegreeRelations_eq_bot f g (by decide)] at hrel
  have hz : ExteriorAlgebra.ι K v=0 := congrArg Subtype.val ((Submodule.mem_bot K).mp hrel)
  exact (Submodule.mem_bot K).mpr ((ExteriorAlgebra.ι_eq_zero_iff v).mp hz)

theorem actualGenerator_range :
    LinearMap.range (actualGenerator f g)=(ExteriorAugmented.grading f g).piece 1 := by
  rw [ExteriorAugmented.grading_piece,ExteriorAlgebra.exteriorPower,pow_one,
    actualGenerator,LinearMap.range_comp]

def actualDegreeOneEquiv : (ν → K) ≃ₗ[K] (ExteriorAugmented.grading f g).piece 1 :=
  (LinearEquiv.ofInjective (actualGenerator f g) (actualGenerator_injective f g)).trans
    (LinearEquiv.ofEq _ _ (actualGenerator_range f g))

@[simp] theorem actualDegreeOneEquiv_apply (v : ν → K) :
    (actualDegreeOneEquiv f g v : ExteriorAugmented.Quotient f g)=actualGenerator f g v := rfl

/-- The ordinary multiplication of the actual degree-one generators. -/
def actualQuadraticMultiplication :
    ((ν → K) ⊗[K] (ν → K)) →ₗ[K] ExteriorAugmented.Quotient f g :=
  TensorProduct.lift
    ((LinearMap.mul K (ExteriorAugmented.Quotient f g)).compl₁₂
      (actualGenerator f g) (actualGenerator f g))

@[simp] theorem actualQuadraticMultiplication_tmul (v w : ν → K) :
    actualQuadraticMultiplication f g (v ⊗ₜ[K] w)=
      actualGenerator f g v*actualGenerator f g w := rfl

/-- The literal inclusion of degree two followed by the original quotient. -/
def actualDegreeTwoProjection :
    (⋀[K]^2 (ν → K)) →ₗ[K] ExteriorAugmented.Quotient f g :=
  (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap.comp
    (Submodule.subtype (⋀[K]^2 (ν → K)))

@[simp] theorem actualDegreeTwoProjection_apply (x : ⋀[K]^2 (ν → K)) :
    actualDegreeTwoProjection f g x=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (x : ExteriorAlgebra K (ν → K)) := rfl

theorem actualDegreeTwoProjection_range :
    LinearMap.range (actualDegreeTwoProjection f g)=(ExteriorAugmented.grading f g).piece 2 := by
  rw [ExteriorAugmented.grading_piece,actualDegreeTwoProjection,
    LinearMap.range_comp,Submodule.range_subtype]

/-- The degree-two kernel is proved from the actual homogeneous ideal. -/
theorem actualDegreeTwoProjection_ker :
    LinearMap.ker (actualDegreeTwoProjection f g)=
      Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  ext x
  change (Ideal.Quotient.mk (exteriorRelationIdeal f g)
    (x : ExteriorAlgebra K (ν → K))=0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x∈exteriorDegreeRelations f g 2 ↔ _
  rw [exterior_degree_two_relations]

@[simp] theorem tensorCoordinates_basis (i j : ν) :
    tensorCoordinates (Pi.basisFun K ν i ⊗ₜ[K] Pi.basisFun K ν j)=
      Pi.basisFun K (ν × ν) (i,j) := by
  ext p
  rcases p with ⟨a,b⟩
  simp only [tensorCoordinates_tmul,Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The wedge comparison is an identity between independently defined maps. -/
theorem actualQuadraticMultiplication_eq :
    actualQuadraticMultiplication f g=
      (actualDegreeTwoProjection f g).comp
        (wedgeMap.comp (tensorCoordinates (K := K) (ν := ν)).toLinearMap) := by
  apply ((Pi.basisFun K ν).tensorProduct (Pi.basisFun K ν)).ext
  rintro ⟨i,j⟩
  simp only [Module.Basis.tensorProduct_apply,actualQuadraticMultiplication_tmul,
    LinearMap.comp_apply,LinearEquiv.coe_coe,tensorCoordinates_basis,wedgeMap_basis,
    actualDegreeTwoProjection_apply,actualGenerator_apply]
  rw [←map_mul]
  congr 1
  simp only [exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply,Matrix.vecTail,Matrix.cons_val_zero,
    Matrix.cons_val_one,mul_one]
  rfl

/-- Products of the actual generators span exactly the original degree-two piece. -/
theorem actualQuadraticMultiplication_range :
    LinearMap.range (actualQuadraticMultiplication f g)=(ExteriorAugmented.grading f g).piece 2 := by
  have hs : Function.Surjective
      (wedgeMap.comp (tensorCoordinates (K := K) (ν := ν)).toLinearMap) :=
    (wedgeMap_surjective (K := K) (ν := ν)).comp
      (tensorCoordinates (K := K) (ν := ν)).surjective
  rw [actualQuadraticMultiplication_eq,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hs,Submodule.map_top,actualDegreeTwoProjection_range]

/-- The kernel condition in literal tensor coordinates. -/
theorem actualQuadraticMultiplication_eq_zero_iff
    (z : (ν → K) ⊗[K] (ν → K)) :
    actualQuadraticMultiplication f g z=0 ↔
      wedgeMap (tensorCoordinates z)∈
        Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  rw [actualQuadraticMultiplication_eq]
  change actualDegreeTwoProjection f g (wedgeMap (tensorCoordinates z))=0 ↔ _
  rw [←LinearMap.mem_ker,actualDegreeTwoProjection_ker]

/-- The actual tensor-square multiplication kernel is exactly the relation
space used by the quadratic dual, under the proved tensor coordinates. -/
theorem actualQuadraticMultiplication_ker :
    LinearMap.ker (actualQuadraticMultiplication f g)=
      (originalRelations f g).comap (tensorCoordinates (K := K) (ν := ν)).toLinearMap := by
  ext z
  exact actualQuadraticMultiplication_eq_zero_iff f g z

theorem actualQuadraticMultiplication_ker_coordinates :
    (LinearMap.ker (actualQuadraticMultiplication f g)).map
        (tensorCoordinates (K := K) (ν := ν)).toLinearMap=originalRelations f g := by
  rw [actualQuadraticMultiplication_ker]
  exact Submodule.map_comap_eq_of_surjective
    (tensorCoordinates (K := K) (ν := ν)).surjective (originalRelations f g)

/-- The independent canonical tensor evaluation pairing, applied to the
annihilator of actual multiplication relations. -/
def actualTensorDualRelations :
    Submodule K (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) :=
  (LinearMap.ker (actualQuadraticMultiplication f g)).dualAnnihilator.comap
    (TensorProduct.dualDistrib K (ν → K) (ν → K))

/-- Coordinate dual relations are the annihilator of literal multiplication,
not a relation space chosen solely to obtain a desired Hilbert series. -/
theorem mem_dualRelations_iff_actual_multiplication
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔
      ∀ z : (ν → K) ⊗[K] (ν → K),actualQuadraticMultiplication f g z=0 →
        TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorCoordinates.symm q) z=0 := by
  rw [mem_dualRelations_actual]
  simp only [actualQuadraticMultiplication_eq_zero_iff]

/-- Equality of submodules in the actual tensor square of the actual dual
space, with no self-duality convention or nondegeneracy assumption. -/
theorem actualTensorDualRelations_eq :
    actualTensorDualRelations f g=
      (dualRelations f g).comap (dualTensorCoordinates (K := K) (ν := ν)).toLinearMap := by
  ext q
  simp only [actualTensorDualRelations,Submodule.mem_comap,Submodule.mem_dualAnnihilator]
  rw [mem_dualRelations_iff_actual_multiplication]
  simp only [LinearMap.mem_ker,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

end PaperVerification.AlternatingForms.QuadraticDual
end
end
end TAF_LiteralSource_0521

section TAF_LiteralSource_0522
/- Original module: PaperVerification.AlternatingFormsIntrinsicQuadraticDual -/


/-!
# The intrinsic quadratic dual of the actual exterior quotient

The actual degree-one equivalence induces the dual tensor and tensor-algebra
maps. The canonical evaluation pairing transports the annihilator of the
actual multiplication kernel to the original exterior relation annihilator.
The resulting ordinary quotient equivalence preserves the original generator
map, every generator power, and therefore every Hilbert coefficient.
No genericity, rank, or Koszul hypothesis enters this identification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct PowerSeries

namespace PaperVerification.AlternatingForms.IntrinsicQuadraticDual

open HomogeneousQuadraticDual HomogeneousMultiplicationRows


universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

local notation "G" => ExteriorAugmented.grading f g
local notation "hmul" => ExteriorAugmented.grading_mul f g

def primalTensorEquiv :
    ((ν → K) ⊗[K] (ν → K)) ≃ₗ[K] ((G).piece 1 ⊗[K] (G).piece 1) :=
  TensorProduct.congr (QuadraticDual.actualDegreeOneEquiv f g)
    (QuadraticDual.actualDegreeOneEquiv f g)

def dualGeneratorEquiv : Module.Dual K ((G).piece 1) ≃ₗ[K] Module.Dual K (ν → K) :=
  (QuadraticDual.actualDegreeOneEquiv f g).dualMap

def dualTensorEquiv :
    (Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1)) ≃ₗ[K]
      (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) :=
  TensorProduct.congr (dualGeneratorEquiv f g) (dualGeneratorEquiv f g)

/-- The independent actual multiplication maps agree on the original generators. -/
theorem multiplication_transport (z : (ν → K) ⊗[K] (ν → K)) :
    (HomogeneousMultiplicationRows.multiplication G hmul (primalTensorEquiv f g z) :
      ExteriorAugmented.Quotient f g)=QuadraticDual.actualQuadraticMultiplication f g z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [(primalTensorEquiv f g).map_zero,
        (HomogeneousMultiplicationRows.multiplication G hmul).map_zero,
        (QuadraticDual.actualQuadraticMultiplication f g).map_zero]
      rfl
  | tmul x y =>
      simp only [primalTensorEquiv,TensorProduct.congr_tmul,
        HomogeneousMultiplicationRows.multiplication_tmul_val,
        QuadraticDual.actualDegreeOneEquiv_apply,QuadraticDual.actualQuadraticMultiplication_tmul]
  | add z w hz hw => simp only [map_add,Submodule.coe_add,hz,hw]

theorem multiplication_zero_iff (z : (ν → K) ⊗[K] (ν → K)) :
    HomogeneousMultiplicationRows.multiplication G hmul (primalTensorEquiv f g z)=0 ↔
      QuadraticDual.actualQuadraticMultiplication f g z=0 := by
  constructor
  · intro h
    exact (multiplication_transport f g z).symm.trans (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (multiplication_transport f g z).trans h

theorem pairing_transport
    (q : Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1))
    (z : (ν → K) ⊗[K] (ν → K)) :
    TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorEquiv f g q) z=
      TensorProduct.dualDistrib K ((G).piece 1) ((G).piece 1) q (primalTensorEquiv f g z) :=
  tensorDual_pairing (QuadraticDual.actualDegreeOneEquiv f g) q z

/-- Exact annihilator transport, not an assumed quadratic-dual identification. -/
theorem mem_dualRelations_iff
    (q : Module.Dual K ((G).piece 1) ⊗[K] Module.Dual K ((G).piece 1)) :
    q∈HomogeneousQuadraticDual.dualRelations G hmul ↔
      dualTensorEquiv f g q∈QuadraticDual.actualTensorDualRelations f g := by
  simp only [HomogeneousQuadraticDual.dualRelations,QuadraticDual.actualTensorDualRelations,
    Submodule.mem_comap,Submodule.mem_dualAnnihilator,LinearMap.mem_ker]
  constructor
  · intro h z hz
    rw [pairing_transport]
    exact h (primalTensorEquiv f g z) ((multiplication_zero_iff f g z).mpr hz)
  · intro h z hz
    obtain ⟨w,rfl⟩ := (primalTensorEquiv f g).surjective z
    rw [←pairing_transport]
    exact h w ((multiplication_zero_iff f g w).mp hz)

theorem dualRelations_image :
    (HomogeneousQuadraticDual.dualRelations G hmul).map (dualTensorEquiv f g).toLinearMap=
      QuadraticDual.actualTensorDualRelations f g := by
  ext q
  rw [Submodule.mem_map_equiv]
  simpa only [LinearEquiv.apply_symm_apply] using
    (mem_dualRelations_iff f g ((dualTensorEquiv f g).symm q))

def originalTensorAlgebraEquiv :
    TensorAlgebra K (Module.Dual K ((G).piece 1)) ≃ₐ[K]
      TensorAlgebra K (Module.Dual K (ν → K)) :=
  tensorAlgebraCongr (dualGeneratorEquiv f g)

theorem originalTensorAlgebraEquiv_quadratic :
    (originalTensorAlgebraEquiv f g).toLinearMap.comp
        (HomogeneousQuadraticDual.quadraticInclusion (K := K)
          (V := Module.Dual K ((G).piece 1)))=
      QuadraticDual.tensorQuadraticInclusion.comp (dualTensorEquiv f g).toLinearMap :=
  tensorAlgebraCongr_quadratic (dualGeneratorEquiv f g)

theorem tensorRelationSpace_image :
    (HomogeneousQuadraticDual.tensorRelationSpace G hmul).map
        (originalTensorAlgebraEquiv f g).toLinearMap=
      (QuadraticDual.dualRelations f g).map QuadraticDual.tensorWordMap := by
  rw [HomogeneousQuadraticDual.tensorRelationSpace,←Submodule.map_comp,
    originalTensorAlgebraEquiv_quadratic,Submodule.map_comp,dualRelations_image,
    QuadraticDual.actualTensorDualRelations_eq,Submodule.comap_equiv_eq_map_symm,
    ←Submodule.map_comp,←QuadraticDual.tensorWordMap_eq_actual_inclusion]

/-- The coordinate-generated tensor relations and the submodule relation
presentation define exactly the same ordinary relation. -/
theorem originalTensorRelation_eq :
    QuadraticWordFunctionals.Relation
        ((QuadraticDual.dualRelations f g).map QuadraticDual.tensorWordMap)=
      QuadraticDual.TensorDualRelation f g := by
  funext x y
  apply propext
  rw [HomogeneousQuadraticDual.relation_iff]
  constructor
  · rintro ⟨hx,rfl⟩
    obtain ⟨q,hq,rfl⟩ := hx
    exact QuadraticDual.TensorDualRelation.annihilator q hq
  · intro h
    cases h with
    | annihilator q hq => exact ⟨⟨q,hq,rfl⟩,rfl⟩

/-- Actual algebra equivalence from the intrinsic dual of A to the original
annihilator presentation. Every relation and both inverse laws are proved. -/
def intrinsicTensorEquiv : HomogeneousQuadraticDual.conventionalDual G hmul ≃ₐ[K]
    QuadraticDual.TensorQuadraticDual f g :=
  ((HomogeneousQuadraticDual.quotientEquivMap (originalTensorAlgebraEquiv f g)
      (HomogeneousQuadraticDual.tensorRelationSpace G hmul)).trans
    (HomogeneousQuadraticDual.ofSubmoduleEq (tensorRelationSpace_image f g))).trans
      (HomogeneousQuadraticDual.ofRelationEq (originalTensorRelation_eq f g))

@[simp] theorem intrinsicTensorEquiv_generator (φ : Module.Dual K ((G).piece 1)) :
    intrinsicTensorEquiv f g (HomogeneousQuadraticDual.generatorMap G hmul φ)=
      QuadraticDual.tensorGeneratorMap f g (dualGeneratorEquiv f g φ) := by
  simp only [intrinsicTensorEquiv,AlgEquiv.trans_apply,
    HomogeneousQuadraticDual.generatorMap,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    HomogeneousQuadraticDual.quotientEquivMap_mk,HomogeneousQuadraticDual.ofSubmoduleEq_mk,
    HomogeneousQuadraticDual.ofRelationEq_mk,originalTensorAlgebraEquiv,tensorAlgebraCongr_ι,
    QuadraticDual.tensorGeneratorMap]
  simp only [QuadraticWordFunctionals.quotientMap,HomogeneousQuadraticDual.ofRelationEq_mk]

theorem generatorMap_transport :
    (intrinsicTensorEquiv f g).toLinearMap.comp (HomogeneousQuadraticDual.generatorMap G hmul)=
      (QuadraticDual.tensorGeneratorMap f g).comp (dualGeneratorEquiv f g).toLinearMap := by
  apply LinearMap.ext
  intro φ
  exact intrinsicTensorEquiv_generator f g φ

/-- All original generator powers are transported, including degree zero. -/
theorem wordPiece_transport (n : ℕ) :
    (HomogeneousQuadraticDual.wordPiece G hmul n).map (intrinsicTensorEquiv f g).toLinearMap=
      QuadraticDual.tensorWordPiece f g n := by
  change ((HomogeneousQuadraticDual.generatorMap G hmul).range^n).map
    (intrinsicTensorEquiv f g).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((HomogeneousQuadraticDual.generatorMap G hmul).range.map
    (intrinsicTensorEquiv f g).toLinearMap)^n=_
  rw [←LinearMap.range_comp,generatorMap_transport,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (dualGeneratorEquiv f g).surjective,Submodule.map_top]
  rfl

def degreeEquiv (n : ℕ) : HomogeneousQuadraticDual.wordPiece G hmul n ≃ₗ[K]
    QuadraticDual.tensorWordPiece f g n :=
  (Submodule.equivMapOfInjective (intrinsicTensorEquiv f g).toLinearMap
    (intrinsicTensorEquiv f g).injective (HomogeneousQuadraticDual.wordPiece G hmul n)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport f g n))

theorem degree_finrank_eq (n : ℕ) :
    Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul n)=
      Module.finrank K (QuadraticDual.tensorWordPiece f g n) :=
  (degreeEquiv f g n).finrank_eq

/-- The coefficient of the genuine original quadratic-dual Hilbert series. -/
theorem degree_finrank_eq_coeff (n : ℕ) :
    (Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul n) : ℤ)=
      PowerSeries.coeff n (QuadraticDual.tensorHilbertSeries f g) := by
  rw [QuadraticDual.tensorHilbertSeries,PowerSeries.coeff_mk,degree_finrank_eq]

end PaperVerification.AlternatingForms.IntrinsicQuadraticDual
end
end
end TAF_LiteralSource_0522

section TAF_LiteralSource_0523
/- Original module: PaperVerification.ExteriorKoszulSeriesObstruction -/


/-!
# The actual exterior quotient and quadratic-dual series obstruction

This file specializes the proved formal-series contradiction to the literal
exterior quotient and its annihilator-defined tensor quadratic dual. The
injectivity hypothesis is the precise input to the separate PBW theorem;
this result is not the full generic Koszul classification.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.KoszulBarObstruction

open PaperVerification.AlternatingForms

def actualExteriorSeries {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (f g : ⋀[K]^2 M) : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (ExteriorQuotientDegree f g d) : ℤ))

/-- This obstruction uses the literal exterior quotient and the actual
annihilator-defined tensor quadratic dual, not arbitrary Hilbert series. -/
theorem actual_exterior_dual_no_koszul_identity
    {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    actualExteriorSeries f g *
      PowerSeries.rescale (-1 : ℤ) (QuadraticDual.tensorHilbertSeries f g)≠1 := by
  apply no_bounded_koszul_identity (Fintype.card ν)
  · simp only [actualExteriorSeries,PowerSeries.coeff_mk]
    rw [exteriorQuotientDegree_finrank_eq_zero_high f g _ (by simp),Nat.cast_zero]
  · exact QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g hinj

end PaperVerification.KoszulBarObstruction
end
end
end TAF_LiteralSource_0523

section TAF_LiteralSource_0524
/- Original module: PaperVerification.AlternatingFormsNonKoszul -/


/-!
# The complete higher-dimensional non-Koszul direction

For every finite homogeneous augmented basis, the actual diagonal bar
homology is compared with the independently defined ordinary quadratic
dual. Koszul concentration therefore gives its genuine Hilbert identity.
The proved PBW formula contradicts the actual exterior degree cutoff.
The final generic theorem constructs a nonempty principal open in the
full coefficient space in every dimension at least six.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.NonKoszul

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The constant coefficient follows from the actual proved PBW series. -/
theorem dual_constant (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    PowerSeries.coeff 0 (QuadraticDual.tensorHilbertSeries f g)=1 := by
  have h := congrArg PowerSeries.constantCoeff
    (QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g hinj)
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h

/-- Every homogeneous basis of the actual original quotient has
non-diagonal ordinary Tor when the cubic wedge map is injective. -/
theorem not_hasDiagonalTor
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(ExteriorAugmented.grading f g).piece (δ i))
    (hε : ∀ i,ExteriorAugmented.augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b) :
    ¬WeightedBar.HasDiagonalTor (ExteriorAugmented.augmentation f g)
      B hunit hε δ hδ := by
  intro hKoszul
  have hdim : ∀ r,(Module.finrank K
      ((WeightedBar.internalComplex (ExteriorAugmented.augmentation f g)
        B hunit hε δ hδ (r+1)).homology (r+1)) : ℤ)=
      PowerSeries.coeff (r+1) (QuadraticDual.tensorHilbertSeries f g) := by
    intro r
    have he := HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
      (ExteriorAugmented.grading f g) (ExteriorAugmented.augmentation f g)
      B δ (ExteriorAugmented.grading_zero f g) hunit hhom hpos hε hδ
      (ExteriorAugmented.grading_mul f g) r
    exact (congrArg (fun m : ℕ => (m : ℤ)) he).trans
      (IntrinsicQuadraticDual.degree_finrank_eq_coeff f g (r+1))
  have hseries : 1+WeightedBar.positiveSeries δ=
      KoszulBarObstruction.actualExteriorSeries f g := by
    refine (HomogeneousBasisHilbert.one_add_positiveSeries_eq
      (ExteriorAugmented.grading f g) (ExteriorAugmented.augmentation f g)
      B δ (ExteriorAugmented.grading_zero f g) hunit hhom hpos).trans ?_
    apply PowerSeries.ext
    intro d
    simp only [HomogeneousBasisHilbert.series,KoszulBarObstruction.actualExteriorSeries,
      PowerSeries.coeff_mk]
    exact congrArg (fun m : ℕ => (m : ℤ)) (ExteriorAugmented.grading_piece_finrank f g d)
  apply KoszulBarObstruction.actual_exterior_dual_no_koszul_identity f g hinj
  rw [←hseries]
  exact KoszulDiagonalSeries.one_add_mul_signed_series
    (ExteriorAugmented.augmentation f g) B hunit hε δ hpos hδ
    (QuadraticDual.tensorHilbertSeries f g) (dual_constant f g hinj) hdim hKoszul

/-- The conclusion rules out every actual homogeneous Koszul certificate,
not just the particular basis used in the Hilbert computation. -/
theorem not_certificate (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate f g) := by
  rintro ⟨C⟩
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  exact not_hasDiagonalTor f g hinj C.Index C.basis C.unit C.degree C.positive
    C.homogeneous C.augmentation_zero C.product_degree C.diagonal

end PaperVerification.AlternatingForms.NonKoszul

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K]

/-- All dimensions at least six, one nonempty principal open of the full
space of pairs, and the actual original-graded ordinary-Tor conclusion. -/
theorem paper_proposition_5_3_non_koszul_large (n : ℕ) (hn : 6≤n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  letI : NeZero n := ⟨by omega⟩
  have hdim : Module.finrank K (Fin n → K)=n := by simp
  obtain ⟨ι,fin,h⟩ := generic_cubic_wedge_injective (K := K) (M := Fin n → K) n hn hdim
  letI := fin
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
  exact ⟨ι,fin,b₂,Q,hQ,hpoint,fun y hy => NonKoszul.not_certificate _ _ (h y hy)⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0524

section TAF_LiteralSource_0525
/- Original module: PaperVerification.WeightedBarTorOrthogonality -/


/-!
# Orthogonal original-degree summands in ordinary augmentation Tor

The actual chain-level degree projections split the inclusions and kill
all other internal degrees. Their transported maps on ordinary Tor prove
disjointness of distinct degree summands. Together with the already proved
exhaustion, diagonal concentration is equivalent to the diagonal summand
being the whole Tor module. The zeroth off-diagonal summands vanish directly
because the unique length-zero word has original degree zero.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PaperVerification.NoncommutativeBar PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "internal" => internalComplex ε B hunit hε δ hδ

theorem internalProjection_inclusion_of_ne (r N M : ℕ) (hMN : M≠N)
    (z : piece (K := K) δ r M) :
    internalProjection δ r N (internalInclusion δ r M z)=0 := by
  apply Subtype.ext
  change degreeProjection δ N z.val=0
  have hz : z.val∈lengthPiece I K r ⊓ degreePiece δ M := by
    rw [←piece_eq_inf]
    exact z.property
  exact (degreeProjection_homogeneous δ N M z.val hz.2).trans (if_neg hMN)

theorem inclusion_projection_eq_zero (N M : ℕ) (hMN : M≠N) :
    inclusionChain ε B hunit hε δ hδ M ≫
      projectionChain ε B hunit hε δ hδ N=0 := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact internalProjection_inclusion_of_ne δ r N M hMN z

/-- Projection from actual ordinary Tor to its original internal degree. -/
def torProjection (r N : ℕ) :
    AugmentationCoinvariants.augmentationTor ε r ⟶ (internal N).homology r :=
  (ordinaryTorReducedBarIso ε B hunit hε r).hom ≫
    homologyMap (projectionChain ε B hunit hε δ hδ N) r

theorem internalTorMap_projection (r N : ℕ) :
    internalTorMap ε B hunit hε δ hδ r N ≫
      torProjection ε B hunit hε δ hδ r N=𝟙 _ := by
  simp only [internalTorMap,torProjection,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←homologyMap_comp,chain_retraction,homologyMap_id]

theorem internalTorMap_projection_of_ne (r N M : ℕ) (hMN : M≠N) :
    internalTorMap ε B hunit hε δ hδ r M ≫
      torProjection ε B hunit hε δ hδ r N=0 := by
  simp only [internalTorMap,torProjection,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←homologyMap_comp,inclusion_projection_eq_zero ε B hunit hε δ hδ N M hMN,
    homologyMap_zero]

theorem torProjection_internalTorMap_self (r N : ℕ) (z : (internal N).homology r) :
    torProjection ε B hunit hε δ hδ r N
      (internalTorMap ε B hunit hε δ hδ r N z)=z :=
  congrArg (fun f => f z) (internalTorMap_projection ε B hunit hε δ hδ r N)

theorem torProjection_internalTorMap_of_ne (r N M : ℕ) (hMN : M≠N)
    (z : (internal M).homology r) :
    torProjection ε B hunit hε δ hδ r N
      (internalTorMap ε B hunit hε δ hδ r M z)=0 :=
  congrArg (fun f => f z) (internalTorMap_projection_of_ne ε B hunit hε δ hδ r N M hMN)

/-- Distinct original internal degrees have zero intersection in actual Tor. -/
theorem torPiece_disjoint (r N M : ℕ) (hNM : N≠M) :
    Disjoint (torPiece ε B hunit hε δ hδ r N) (torPiece ε B hunit hε δ hδ r M) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨z,hz⟩ := hy
  have hy0 : y=0 := by
    calc
      y=torProjection ε B hunit hε δ hδ r N
          (internalTorMap ε B hunit hε δ hδ r N y) :=
        (torProjection_internalTorMap_self ε B hunit hε δ hδ r N y).symm
      _ = torProjection ε B hunit hε δ hδ r N
          (internalTorMap ε B hunit hε δ hδ r M z) :=
        congrArg (fun t => torProjection ε B hunit hε δ hδ r N t) hz.symm
      _ = 0 := torProjection_internalTorMap_of_ne ε B hunit hε δ hδ r N M
        (Ne.symm hNM) z
  change internalTorMap ε B hunit hε δ hδ r N y=0
  rw [hy0,map_zero]

/-- Under actual diagonal concentration, its diagonal summand is all of Tor. -/
theorem diagonal_top_of_hasDiagonalTor (h : HasDiagonalTor ε B hunit hε δ hδ)
    (r : ℕ) : torPiece ε B hunit hε δ hδ r r=⊤ := by
  apply top_unique
  rw [←torPieces_iSup ε B hunit hε δ hδ r]
  apply iSup_le
  intro N
  by_cases hN : r=N
  · subst N
    exact le_rfl
  · rw [h r N hN]
    exact bot_le

theorem hasDiagonalTor_iff_diagonal_top : HasDiagonalTor ε B hunit hε δ hδ ↔
    ∀ r,torPiece ε B hunit hε δ hδ r r=⊤ := by
  constructor
  · exact diagonal_top_of_hasDiagonalTor ε B hunit hε δ hδ
  · intro h r N hN
    have hd := torPiece_disjoint ε B hunit hε δ hδ r r N hN
    simpa only [h r,top_disjoint] using hd

/-- Degree zero of the bar complex has only the empty word. No Koszul
assumption, finite basis, or positivity premise is needed here. -/
theorem torPiece_zero_off_diagonal (N : ℕ) (hN : 0≠N) :
    torPiece ε B hunit hε δ hδ 0 N=⊥ := by
  apply (torPiece_eq_bot_iff ε B hunit hε δ hδ 0 N).mpr
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero (ModuleCat.of K (piece (K := K) δ 0 N))
  have hzero (z : piece (K := K) δ 0 N) : z=0 := by
    apply Subtype.ext
    apply Finsupp.ext
    intro L
    change z.val L=0
    apply (Finsupp.mem_supported' K z.val).mp z.property
    rintro ⟨hL,hW⟩
    have hn : L=[] := List.length_eq_zero_iff.mp hL
    subst L
    exact hN hW
  letI : Subsingleton (piece (K := K) δ 0 N) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end PaperVerification.WeightedBar
end
end
end TAF_LiteralSource_0525

section TAF_LiteralSource_0526
/- Original module: PaperVerification.HomogeneousKoszulInvariance -/


/-!
# Independence of diagonal ordinary Tor from a homogeneous basis

For every finite homogeneous augmented basis, positive diagonal homology
has the dimension of the same intrinsic quadratic-dual piece. If one
basis gives diagonal concentration, its diagonal image exhausts ordinary
Tor. Finite dimension then forces the other basis's diagonal image to be
all of that same Tor module. Orthogonality kills its off-diagonal pieces.
The zeroth homological degree is treated directly by the empty bar word.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.HomogeneousKoszulInvariance

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AugmentedAlgebraBasis WeightedBar

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

/-- An actual internal bar homology group is finite-dimensional because
its cycles embed in a finite word space and its homology is their quotient. -/
theorem internalHomology_finite (r N : ℕ) :
    Module.Finite K ((internalComplex ε B hunit hε δ hδ N).homology r) := by
  let C := internalComplex ε B hunit hε δ hδ N
  haveI : Module.Finite K (C.X r) := by
    change Module.Finite K (piece (K := K) δ r N)
    infer_instance
  haveI : Module.Finite K (C.cycles r) :=
    Module.Finite.of_injective (C.iCycles r).hom
      ((ModuleCat.mono_iff_injective (C.iCycles r)).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ r).hom
    ((ModuleCat.epi_iff_surjective (C.homologyπ r)).mp inferInstance)

variable (G : TauCeti.InternalGrading K A ℕ)
  (hzero : G.piece 0=(1 : Submodule K A))
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))
  {J : Type u} [Fintype J]
  (B' : Module.Basis (Option J) K A)
  (hunit' : B' none=1) (hε' : ∀ i,ε (B' (some i))=0)
  (δ' : J → ℕ)
  (hδ' : ∀ a b c,productCoefficients B' a b c≠0 → δ' c=δ' a+δ' b)
  (hhom' : ∀ i,B' (some i)∈G.piece (δ' i)) (hpos' : ∀ i,0<δ' i)

include hzero hhom hpos hmul hhom' hpos' in
/-- Diagonal ordinary Tor concentration transfers to every other actual
finite homogeneous augmented basis for the same original grading. -/
theorem hasDiagonalTor_transfer
    (h : HasDiagonalTor ε B hunit hε δ hδ) :
    HasDiagonalTor ε B' hunit' hε' δ' hδ' := by
  intro r N hne
  rcases r with _ | r
  · exact torPiece_zero_off_diagonal ε B' hunit' hε' δ' hδ' N hne
  · have htop := diagonal_top_of_hasDiagonalTor ε B hunit hε δ hδ h (r+1)
    let e : (internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1) ≃ₗ[K]
        AugmentationCoinvariants.augmentationTor ε (r+1) :=
      (internalTorEquiv ε B hunit hε δ hδ (r+1) (r+1)).trans
        ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)
    haveI : Module.Finite K
        ((internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1)) :=
      internalHomology_finite ε B hunit hε δ hδ (r+1) (r+1)
    haveI : Module.Finite K (AugmentationCoinvariants.augmentationTor ε (r+1)) :=
      Module.Finite.equiv e
    have hdim : Module.finrank K (AugmentationCoinvariants.augmentationTor ε (r+1))=
        Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
      e.finrank_eq.symm.trans
        (HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
          G ε B δ hzero hunit hhom hpos hε hδ hmul r)
    have hdim' : Module.finrank K (torPiece ε B' hunit' hε' δ' hδ' (r+1) (r+1))=
        Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
      (internalTorEquiv ε B' hunit' hε' δ' hδ' (r+1) (r+1)).finrank_eq.symm.trans
        (HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
          G ε B' δ' hzero hunit' hhom' hpos' hε' hδ' hmul r)
    have htop' : torPiece ε B' hunit' hε' δ' hδ' (r+1) (r+1)=⊤ :=
      Submodule.eq_top_of_finrank_eq (hdim'.trans hdim.symm)
    have hd := torPiece_disjoint ε B' hunit' hε' δ' hδ' (r+1) N (r+1) (Ne.symm hne)
    rw [htop'] at hd
    exact disjoint_top.mp hd

include hzero hhom hpos hmul hhom' hpos' in
/-- The concentration property is independent of every compatible finite
homogeneous basis, without assuming Koszulness or a Hilbert formula. -/
theorem hasDiagonalTor_iff :
    HasDiagonalTor ε B hunit hε δ hδ ↔ HasDiagonalTor ε B' hunit' hε' δ' hδ' := by
  constructor
  · exact hasDiagonalTor_transfer ε B hunit hε δ hδ G hzero hhom hpos hmul
      B' hunit' hε' δ' hδ' hhom' hpos'
  · exact hasDiagonalTor_transfer ε B' hunit' hε' δ' hδ' G hzero hhom' hpos' hmul
      B hunit hε δ hδ hhom hpos

end PaperVerification.HomogeneousKoszulInvariance
end
end
end TAF_LiteralSource_0526

section TAF_LiteralSource_0527
/- Original module: PaperVerification.HomogeneousAugmentedBasis -/


/-!
# A finite homogeneous augmented basis with prescribed degree-one vectors

The degree-zero vector is literally one. The degree-one basis is supplied
as a basis of the actual degree-one subspace and is retained exactly. All
higher vectors are chosen inside their actual homogeneous subspaces. The
full algebra's finite dimensionality proves the resulting positive index
finite; no cutoff, Hilbert formula, or Koszul assertion is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.HomogeneousAugmentedBasis

universe u
variable {K A ν : Type u} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  (G : TauCeti.InternalGrading K A ℕ)

abbrev DegreeIndex : ℕ → Type u
  | 0 => ULift.{u} (Fin 1)
  | 1 => ν
  | d+2 => ULift.{u} (Fin (Module.finrank K (G.piece (d+2))))

abbrev PositiveIndex := ν ⊕ (Σ d : ℕ,ULift.{u} (Fin (Module.finrank K (G.piece (d+2)))))

def positiveDegree : PositiveIndex (ν := ν) G → ℕ
  | .inl _ => 1
  | .inr ⟨d,_⟩ => d+2

theorem positiveDegree_pos (i : PositiveIndex (ν := ν) G) : 0<positiveDegree G i := by
  rcases i with i | ⟨d,i⟩ <;> simp only [positiveDegree] <;> omega

def indexEquiv : (Σ d,DegreeIndex (ν := ν) G d) ≃ Option (PositiveIndex (ν := ν) G) where
  toFun
    | ⟨0,_⟩ => none
    | ⟨1,i⟩ => some (.inl i)
    | ⟨d+2,i⟩ => some (.inr ⟨d,i⟩)
  invFun
    | none => ⟨0,⟨0⟩⟩
    | some (.inl i) => ⟨1,i⟩
    | some (.inr ⟨d,i⟩) => ⟨d+2,i⟩
  left_inv := by
    rintro ⟨d,i⟩
    rcases d with _ | _ | d
    · have hi : i=(⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
    · rfl
  right_inv := by
    rintro (_ | i | ⟨d,i⟩) <;> rfl

variable (ε : A →ₐ[K] K) (hzero : G.piece 0=(1 : Submodule K A))
  (b₁ : Module.Basis ν K (G.piece 1))

def degreeBasis : (d : ℕ) → Module.Basis (DegreeIndex (ν := ν) G d) K (G.piece d)
  | 0 => (Module.Basis.singleton (ULift.{u} (Fin 1)) K).map
      (DimensionFiveGradedBasis.scalarPieceEquiv G ε hzero)
  | 1 => b₁
  | d+2 => (Module.finBasis K (G.piece (d+2))).reindex Equiv.ulift.symm

def basis : Module.Basis (Option (PositiveIndex (ν := ν) G)) K A :=
  (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)).reindex (indexEquiv G)

/-- Finite dimensionality, rather than an assumed finite degree cutoff,
proves that the actual collected basis has finitely many positive vectors. -/
def positiveFintype : Fintype (PositiveIndex (ν := ν) G) := by
  haveI : Finite (Option (PositiveIndex (ν := ν) G)) :=
    Module.Finite.finite_basis (basis G ε hzero b₁)
  haveI : Finite (PositiveIndex (ν := ν) G) :=
    Finite.of_injective (some : PositiveIndex (ν := ν) G → Option (PositiveIndex (ν := ν) G))
      (Option.some_injective _)
  exact Fintype.ofFinite _

theorem basis_none : basis G ε hzero b₁ none=1 := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  change ((degreeBasis G ε hzero b₁ 0) (⟨0⟩ : ULift.{u} (Fin 1)) : A)=1
  simp only [degreeBasis,Module.Basis.map_apply,Module.Basis.singleton_apply,
    DimensionFiveGradedBasis.scalarPieceEquiv_val,map_one]

/-- The supplied degree-one vectors are retained literally. -/
theorem basis_one (i : ν) : basis G ε hzero b₁ (some (.inl i))=(b₁ i : A) := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  rfl

theorem basis_positive_mem (i : PositiveIndex (ν := ν) G) :
    basis G ε hzero b₁ (some i)∈G.piece (positiveDegree G i) := by
  rw [basis,Module.Basis.reindex_apply]
  rcases i with i | ⟨d,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)) ⟨1,i⟩∈G.piece 1
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero b₁) ⟨1,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)) ⟨d+2,i⟩∈G.piece (d+2)
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero b₁) ⟨d+2,i⟩

theorem basis_repr_of_mem_ne {d : ℕ} {x : A} (hx : x∈G.piece d)
    (i : PositiveIndex (ν := ν) G) (hi : d≠positiveDegree G i) :
    (basis G ε hzero b₁).repr x (some i)=0 := by
  rw [basis,Module.Basis.repr_reindex_apply]
  rcases i with i | ⟨q,i⟩ <;>
    exact G.isInternal.collectedBasis_repr_of_mem_ne (degreeBasis G ε hzero b₁) hi hx

/-- Exactly the originally prescribed vectors have internal degree one. -/
def degreeOneIndexEquiv : ν ≃ {i : PositiveIndex (ν := ν) G // positiveDegree G i=1} where
  toFun i := ⟨.inl i,rfl⟩
  invFun
    | ⟨.inl i,_⟩ => i
    | ⟨.inr ⟨d,_⟩,h⟩ => False.elim (by change d+2=1 at h; omega)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i | ⟨d,i⟩,h⟩
    · rfl
    · change d+2=1 at h
      omega

variable (hε : ∀ d,0<d → ∀ x,x∈G.piece d → ε x=0)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hε in
theorem basis_positive_augmentation (i : PositiveIndex (ν := ν) G) :
    ε (basis G ε hzero b₁ (some i))=0 :=
  hε _ (positiveDegree_pos G i) _ (basis_positive_mem G ε hzero b₁ i)

include hmul in
theorem product_homogeneous (a b c : PositiveIndex (ν := ν) G)
    (h : AugmentedAlgebraBasis.productCoefficients (basis G ε hzero b₁) a b c≠0) :
    positiveDegree G c=positiveDegree G a+positiveDegree G b := by
  by_contra hc
  apply h
  change (basis G ε hzero b₁).repr
    (basis G ε hzero b₁ (some a)*basis G ε hzero b₁ (some b)) (some c)=0
  exact basis_repr_of_mem_ne G ε hzero b₁
    (hmul _ _ _ _ (basis_positive_mem G ε hzero b₁ a)
      (basis_positive_mem G ε hzero b₁ b)) c (Ne.symm hc)

end PaperVerification.HomogeneousAugmentedBasis
end
end
end TAF_LiteralSource_0527

section TAF_LiteralSource_0528
/- Original module: PaperVerification.AlternatingFormsExteriorHomogeneousBasis -/


/-!
# Actual homogeneous augmented bases for every exterior quadratic quotient

This construction supplies the finite bar-basis data, original degrees,
and exact degree-one coordinate generators for arbitrary f and g. The
full exterior quotient and its grading are already defined independently.
No genericity, rank formula, cutoff, or Koszul hypothesis is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.AlternatingForms.ExteriorHomogeneousBasis

open ExteriorAugmented QuadraticDual

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

instance quotientFinite : Module.Finite K (ExteriorAugmented.Quotient f g) := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  haveI : Module.Finite K (ExteriorAlgebra K (ν → K)) :=
    Module.Finite.of_basis (Pi.basisFun K ν).ExteriorAlgebra
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K (exteriorRelationIdeal f g))

/-- This is exactly the original coordinate generator basis in degree one. -/
def degreeOneBasis : Module.Basis ν K ((grading f g).piece 1) :=
  (Pi.basisFun K ν).map (actualDegreeOneEquiv f g)

abbrev PositiveIndex := HomogeneousAugmentedBasis.PositiveIndex (ν := ν) (grading f g)

abbrev positiveDegree : PositiveIndex f g → ℕ :=
  HomogeneousAugmentedBasis.positiveDegree (grading f g)

def basis : Module.Basis (Option (PositiveIndex f g)) K (ExteriorAugmented.Quotient f g) :=
  HomogeneousAugmentedBasis.basis (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

def positiveFintype : Fintype (PositiveIndex f g) :=
  HomogeneousAugmentedBasis.positiveFintype (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

theorem basis_none : basis f g none=1 :=
  HomogeneousAugmentedBasis.basis_none (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

theorem basis_one (i : ν) :
    basis f g (some (.inl i))=actualGenerator f g (Pi.basisFun K ν i) := by
  rw [basis,HomogeneousAugmentedBasis.basis_one,degreeOneBasis,Module.Basis.map_apply]
  exact actualDegreeOneEquiv_apply f g _

theorem basis_positive_mem (i : PositiveIndex f g) :
    basis f g (some i)∈(grading f g).piece (positiveDegree f g i) :=
  HomogeneousAugmentedBasis.basis_positive_mem (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) i

theorem positiveDegree_pos (i : PositiveIndex f g) : 0<positiveDegree f g i :=
  HomogeneousAugmentedBasis.positiveDegree_pos (grading f g) i

theorem basis_positive_augmentation (i : PositiveIndex f g) :
    augmentation f g (basis f g (some i))=0 :=
  HomogeneousAugmentedBasis.basis_positive_augmentation (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) (augmentation_piece_zero f g) i

theorem product_homogeneous (a b c : PositiveIndex f g)
    (h : AugmentedAlgebraBasis.productCoefficients (basis f g) a b c≠0) :
    positiveDegree f g c=positiveDegree f g a+positiveDegree f g b :=
  HomogeneousAugmentedBasis.product_homogeneous (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) (grading_mul f g) a b c h

def degreeOneIndexEquiv : ν ≃ {i : PositiveIndex f g // positiveDegree f g i=1} :=
  HomogeneousAugmentedBasis.degreeOneIndexEquiv (grading f g)

@[simp] theorem degreeOneIndexEquiv_val (i : ν) : (degreeOneIndexEquiv f g i).val=Sum.inl i := rfl

/-- The positive basis counts in each degree are the intrinsic quotient dimensions. -/
theorem card_degree (d : ℕ) (hd : 0<d) :
    letI := positiveFintype f g
    Fintype.card {i : PositiveIndex f g // positiveDegree f g i=d}=
      Module.finrank K (ExteriorQuotientDegree f g d) := by
  letI := positiveFintype f g
  exact (HomogeneousBasisProfile.card_degree (grading f g) (basis f g) (positiveDegree f g)
    (grading_zero f g) (basis_none f g) (basis_positive_mem f g) d hd).trans
      (grading_piece_finrank f g d)

/-- The actual complete exterior Hilbert series, with every natural degree. -/
def actualHilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (ExteriorQuotientDegree f g d) : ℤ))

theorem degree_zero_finrank : Module.finrank K (ExteriorQuotientDegree f g 0)=1 := by
  rw [←grading_piece_finrank f g 0]
  have he := (DimensionFiveGradedBasis.scalarPieceEquiv
    (grading f g) (augmentation f g) (grading_zero f g)).finrank_eq
  simpa only [Module.finrank_self] using he.symm

/-- The bar-basis Hilbert series is rigorously the actual exterior quotient series. -/
theorem one_add_positiveSeries_eq :
    letI := positiveFintype f g
    1+WeightedBar.positiveSeries (positiveDegree f g)=actualHilbertSeries f g := by
  letI := positiveFintype f g
  apply PowerSeries.ext
  intro d
  rw [map_add,PowerSeries.coeff_one,HomogeneousBasisProfile.coeff_positiveSeries,
    actualHilbertSeries,PowerSeries.coeff_mk]
  by_cases hd : d=0
  · subst d
    have hn : ∀ i : PositiveIndex f g,positiveDegree f g i≠0 :=
      fun i => Nat.ne_of_gt (positiveDegree_pos f g i)
    simp [hn,degree_zero_finrank]
  · rw [card_degree f g d (Nat.pos_of_ne_zero hd)]
    simp [hd]

end PaperVerification.AlternatingForms.ExteriorHomogeneousBasis
end
end
end TAF_LiteralSource_0528

section TAF_LiteralSource_0529
/- Original module: PaperVerification.AlternatingFormsIntrinsicKoszul -/


/-!
# Basis-independent Koszulness of the actual exterior quotient

The predicate quantifies over every finite homogeneous augmented basis
compatible with the original grading, and asserts concentration of actual
ordinary augmentation Tor. Basis independence is proved, not assumed.
The independently constructed homogeneous basis shows this quantification
is nonvacuous and proves its equivalence to the constructive certificates
used in the principal generic classification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open ExteriorAugmented AugmentedAlgebraBasis

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Diagonal concentration of ordinary Tor for the original grading,
independently of all choices of compatible finite homogeneous coordinates. -/
def IsKoszul (f g : ⋀[K]^2 M) : Prop :=
  ∀ (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(grading f g).piece (δ i))
    (hε : ∀ i,augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b),
    WeightedBar.HasDiagonalTor (augmentation f g) B hunit hε δ hδ

/-- A single constructive certificate forces concentration for every
compatible homogeneous basis, by a proved ordinary-Tor dimension argument. -/
theorem isKoszul_of_certificate (f g : ⋀[K]^2 M)
    (hC : Nonempty (HomogeneousKoszulCertificate f g)) : IsKoszul f g := by
  obtain ⟨C⟩ := hC
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  intro I inst B hunit δ hpos hhom hε hδ
  exact HomogeneousKoszulInvariance.hasDiagonalTor_transfer
    (augmentation f g) C.basis C.unit C.augmentation_zero C.degree C.product_degree
    (grading f g) (grading_zero f g) C.homogeneous C.positive (grading_mul f g)
    B hunit hε δ hδ hhom hpos C.diagonal

section CoordinateSpace

variable {ν : Type u} [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

/-- The actual quotient has an independently constructed finite homogeneous
basis for every pair, including zero-dimensional ambient spaces. -/
def certificateOfIsKoszul (h : IsKoszul f g) : HomogeneousKoszulCertificate f g := by
  letI := ExteriorHomogeneousBasis.positiveFintype f g
  exact {
    Index := ExteriorHomogeneousBasis.PositiveIndex f g
    finite := inferInstance
    basis := ExteriorHomogeneousBasis.basis f g
    degree := ExteriorHomogeneousBasis.positiveDegree f g
    unit := ExteriorHomogeneousBasis.basis_none f g
    positive := ExteriorHomogeneousBasis.positiveDegree_pos f g
    homogeneous := ExteriorHomogeneousBasis.basis_positive_mem f g
    augmentation_zero := ExteriorHomogeneousBasis.basis_positive_augmentation f g
    product_degree := ExteriorHomogeneousBasis.product_homogeneous f g
    diagonal := h (ExteriorHomogeneousBasis.PositiveIndex f g)
      (ExteriorHomogeneousBasis.basis f g) (ExteriorHomogeneousBasis.basis_none f g)
      (ExteriorHomogeneousBasis.positiveDegree f g)
      (ExteriorHomogeneousBasis.positiveDegree_pos f g)
      (ExteriorHomogeneousBasis.basis_positive_mem f g)
      (ExteriorHomogeneousBasis.basis_positive_augmentation f g)
      (ExteriorHomogeneousBasis.product_homogeneous f g) }

/-- Exact equivalence between basis-independent ordinary graded Koszulness
and the constructive certificates, with no normal-form or rank premise. -/
theorem isKoszul_iff_nonempty_certificate :
    IsKoszul f g ↔ Nonempty (HomogeneousKoszulCertificate f g) := by
  constructor
  · intro h
    exact ⟨certificateOfIsKoszul f g h⟩
  · exact isKoszul_of_certificate f g

end CoordinateSpace

end PaperVerification.AlternatingForms.ExteriorKoszul
end
end
end TAF_LiteralSource_0529

section TAF_LiteralSource_0530
/- Original module: PaperVerification.AlternatingFormsKoszulClassification -/


/-!
# Proposition 5.3: the unrestricted-dimensional generic Koszul classification

The positive branch, the exceptional dimension-five obstruction, and the
higher-dimensional actual quadratic-dual obstruction are assembled on
nonempty principal opens of the entire original coefficient space. Every
natural dimension is covered. The independent dual/enveloping/PBW clause
is `paper_proposition_5_3_dual_clause`, with its full original grading.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

/-- The complete generic iff, with no dimension cutoff, normal-form premise,
additional homology assumption, or replacement of ordinary Tor by a model. -/
theorem paper_proposition_5_3_certificate_classification (n : ℕ) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            (Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) ↔ n≤4) := by
  by_cases hn : n≤4
  · obtain ⟨m,b₂,Q,hQ,hpoint,h⟩ :=
      SmallExteriorKoszul.paper_proposition_5_3_koszul_small
        (K := K) (M := Fin n → K) (by simpa using hn)
    exact ⟨Fin m,inferInstance,b₂,Q,hQ,hpoint,fun y hy =>
      ⟨fun _ => hn,fun _ => h y hy⟩⟩
  · by_cases h5 : n=5
    · subst n
      obtain ⟨b₂,Q,hQ,hpoint,h⟩ :=
        DimensionFiveKoszul.paper_proposition_5_3_dimension_five_not_koszul
          (K := K) (M := Fin 5 → K) (by simp)
      refine ⟨OddOrbitSlot 1,inferInstance,b₂,Q,hQ,hpoint,?_⟩
      intro y hy
      constructor
      · intro hC
        exact (h y hy hC).elim
      · intro hdim
        omega
    · have h6 : 6≤n := by omega
      obtain ⟨ι,fin,h⟩ := paper_proposition_5_3_non_koszul_large K n h6
      letI := fin
      obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
      refine ⟨ι,fin,b₂,Q,hQ,hpoint,?_⟩
      intro y hy
      constructor
      · intro hC
        exact (h y hy hC).elim
      · intro hdim
        exact (hn hdim).elim

/-- Proposition 5.3 with ordinary graded Koszulness independent of every
compatible homogeneous basis. The certificate formulation above is proved
equivalent using actual ordinary Tor, degree orthogonality, and the intrinsic
quadratic dual; no choice of basis or homology comparison is assumed. -/
theorem paper_proposition_5_3_koszul_classification (n : ℕ) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            (ExteriorKoszul.IsKoszul
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 ↔ n≤4) := by
  obtain ⟨ι,fin,h⟩ := paper_proposition_5_3_certificate_classification K n
  letI := fin
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
  refine ⟨ι,fin,b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  exact (ExteriorKoszul.isKoszul_iff_nonempty_certificate _ _).trans (h y hy)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0530

section TAF_LiteralSource_0531
/- Original module: PaperVerification.AlternatingFormsExteriorScalarChange -/


/-!
# Scalar change on the actual finite exterior powers

The maps are the universal exterior-algebra maps induced by coefficient
change.  Increasing exterior words give their literal coordinate formula.
In particular a surjective coefficient map is surjective on every exterior
power, and reduction modulo an ideal has precisely the expected kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R]

def powerBasis (s n : ℕ) :
    Module.Basis (PluckerIndex s n) R (⋀[R]^s (Fin n → R)) :=
  ((Pi.basisFun R (Fin n)).exteriorPower s).reindex (pluckerSubsetEquiv s n).symm

theorem powerBasis_apply {s n : ℕ} (I : PluckerIndex s n) :
    powerBasis R s n I =
      exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I.val i)) := by
  simp only [powerBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    pluckerSubsetEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

def firstForm (k : ℕ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathFirstLeft i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i)]

def secondForm (k : ℕ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathSecondRight i)]

abbrev quotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree (firstForm R k) (secondForm R k) s

variable (S : Type*) [CommRing S] [Algebra R S]

def vectorMap (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → S) :=
  (Pi.basisFun R (Fin n)).constr R (Pi.basisFun S (Fin n))

@[simp] theorem vectorMap_basis (n : ℕ) (i : Fin n) :
    vectorMap R S n (Pi.basisFun R (Fin n) i) = Pi.basisFun S (Fin n) i :=
  Module.Basis.constr_basis _ _ _ _

def exteriorMap (n : ℕ) :
    ExteriorAlgebra R (Fin n → R) →ₐ[R] ExteriorAlgebra S (Fin n → S) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S).restrictScalars R).comp (vectorMap R S n),
      fun x => ExteriorAlgebra.ι_sq_zero (R := S) (vectorMap R S n x)⟩

@[simp] theorem exteriorMap_ι_basis (n : ℕ) (i : Fin n) :
    exteriorMap R S n (ExteriorAlgebra.ι R (Pi.basisFun R (Fin n) i)) =
      ExteriorAlgebra.ι S (Pi.basisFun S (Fin n) i) := by
  erw [exteriorMap, ExteriorAlgebra.lift_ι_apply]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, vectorMap_basis]

theorem exteriorMap_word {s n : ℕ} (I : Fin s → Fin n) :
    exteriorMap R S n
      (ExteriorAlgebra.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I i))) =
      ExteriorAlgebra.ιMulti S s (fun i => Pi.basisFun S (Fin n) (I i)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_map, List.map_ofFn,
    Function.comp_def, exteriorMap_ι_basis]

def powerMap (s n : ℕ) : (⋀[R]^s (Fin n → R)) →ₗ[R] (⋀[S]^s (Fin n → S)) :=
  (powerBasis R s n).constr R (powerBasis S s n)

@[simp] theorem powerMap_basis {s n : ℕ} (I : PluckerIndex s n) :
    powerMap R S s n (powerBasis R s n I) = powerBasis S s n I :=
  Module.Basis.constr_basis _ _ _ _

theorem powerMap_coe {s n : ℕ} (x : ⋀[R]^s (Fin n → R)) :
    (powerMap R S s n x : ExteriorAlgebra S (Fin n → S)) =
      exteriorMap R S n x := by
  have h : ((Submodule.subtype (⋀[S]^s (Fin n → S))).restrictScalars R).comp
      (powerMap R S s n) =
      (exteriorMap R S n).toLinearMap.comp (Submodule.subtype (⋀[R]^s (Fin n → R))) := by
    apply (powerBasis R s n).ext
    intro I
    change (powerMap R S s n (powerBasis R s n I) :
      ExteriorAlgebra S (Fin n → S)) = exteriorMap R S n (powerBasis R s n I)
    rw [powerMap_basis]
    simpa only [powerBasis_apply, exteriorPower.ιMulti_apply_coe] using
      (exteriorMap_word R S I.val).symm
  exact congrArg (fun L : (⋀[R]^s (Fin n → R)) →ₗ[R]
    ExteriorAlgebra S (Fin n → S) => L x) h

theorem powerMap_repr {s n : ℕ} (x : ⋀[R]^s (Fin n → R)) (I : PluckerIndex s n) :
    (powerBasis S s n).repr (powerMap R S s n x) I =
      algebraMap R S ((powerBasis R s n).repr x I) := by
  classical
  conv_lhs => rw [← (powerBasis R s n).sum_repr x, map_sum]
  simp only [map_smul, powerMap_basis]
  simp_rw [← IsScalarTower.algebraMap_smul (R := R) S]
  simp only [map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem powerMap_injective (h : Function.Injective (algebraMap R S)) (s n : ℕ) :
    Function.Injective (powerMap R S s n) := by
  intro x y hxy
  apply (powerBasis R s n).repr.injective
  ext I
  apply h
  rw [← powerMap_repr R S x I, ← powerMap_repr R S y I, hxy]

theorem powerMap_surjective (h : Function.Surjective (algebraMap R S)) (s n : ℕ) :
    Function.Surjective (powerMap R S s n) := by
  classical
  intro y
  choose c hc using fun I : PluckerIndex s n => h ((powerBasis S s n).repr y I)
  refine ⟨(powerBasis R s n).equivFun.symm c, ?_⟩
  apply (powerBasis S s n).repr.injective
  ext I
  rw [powerMap_repr]
  change algebraMap R S ((powerBasis R s n).coord I
    ((powerBasis R s n).equivFun.symm c)) = _
  rw [Module.Basis.coord_equivFun_symm]
  exact hc I

theorem powerMap_word {s n : ℕ} (I : Fin s → Fin n) :
    powerMap R S s n
      (exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I i))) =
      exteriorPower.ιMulti S s (fun i => Pi.basisFun S (Fin n) (I i)) := by
  apply Subtype.ext
  rw [powerMap_coe]
  exact exteriorMap_word R S I

theorem powerMap_pair {n : ℕ} (u v : Fin n) :
    powerMap R S 2 n
      (exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin n) u, Pi.basisFun R (Fin n) v]) =
      exteriorPower.ιMulti S 2 ![Pi.basisFun S (Fin n) u, Pi.basisFun S (Fin n) v] := by
  apply Subtype.ext
  rw [powerMap_coe]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, mul_one, map_mul, exteriorMap_ι_basis]

@[simp] theorem powerMap_firstForm (k : ℕ) :
    powerMap R S 2 (2*k+1) (firstForm R k) = firstForm S k := by
  simp only [firstForm, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact powerMap_pair R S (oddPathFirstLeft i) (oddPathMiddle i)

@[simp] theorem powerMap_secondForm (k : ℕ) :
    powerMap R S 2 (2*k+1) (secondForm R k) = secondForm S k := by
  simp only [secondForm, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact powerMap_pair R S (oddPathMiddle i) (oddPathSecondRight i)

theorem powerMap_wedge {n a b : ℕ}
    (x : ⋀[R]^a (Fin n → R)) (y : ⋀[R]^b (Fin n → R)) :
    powerMap R S (a+b) n (exteriorPower.wedge R _ a b x y) =
      exteriorPower.wedge S _ a b (powerMap R S a n x) (powerMap R S b n y) := by
  apply Subtype.ext
  rw [powerMap_coe]
  simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    map_mul, ← powerMap_coe]

theorem powerMap_relations_mem {k s : ℕ}
    (x : ⋀[R]^s (Fin (2*k+1) → R))
    (hx : x∈exteriorDegreeRelations (firstForm R k) (secondForm R k) s) :
    powerMap R S s (2*k+1) x∈
      exteriorDegreeRelations (firstForm S k) (secondForm S k) s := by
  change (x : ExteriorAlgebra R (Fin (2*k+1) → R))∈exteriorRelationIdeal _ _ at hx
  change (powerMap R S s (2*k+1) x : ExteriorAlgebra S (Fin (2*k+1) → S))∈
    exteriorRelationIdeal _ _
  obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hx
  apply Ideal.mem_span_pair.mpr
  refine ⟨exteriorMap R S _ a, exteriorMap R S _ b, ?_⟩
  have hf := congrArg Subtype.val (powerMap_firstForm R S k)
  have hg := congrArg Subtype.val (powerMap_secondForm R S k)
  rw [powerMap_coe] at hf hg
  rw [powerMap_coe, ← hab, map_add, map_mul, map_mul, hf, hg]

def quotientMap (k s : ℕ) : quotientDegree R k s →ₗ[R] quotientDegree S k s :=
  (Submodule.Quotient.restrictScalarsEquiv R
    (exteriorDegreeRelations (firstForm S k) (secondForm S k) s)).toLinearMap.comp
      ((exteriorDegreeRelations (firstForm R k) (secondForm R k) s).mapQ
        ((exteriorDegreeRelations (firstForm S k) (secondForm S k) s).restrictScalars R)
        (powerMap R S s (2*k+1)) (fun x hx => powerMap_relations_mem R S x hx))

@[simp] theorem quotientMap_mk {k s : ℕ} (x : ⋀[R]^s (Fin (2*k+1) → R)) :
    quotientMap R S k s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (powerMap R S s (2*k+1) x) := rfl

theorem powerMap_relations_surjective
    (h : Function.Surjective (algebraMap R S)) (k s : ℕ) :
    (exteriorDegreeRelations (firstForm R k) (secondForm R k) s).map
        (powerMap R S s (2*k+1)) =
      (exteriorDegreeRelations (firstForm S k) (secondForm S k) s).restrictScalars R := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact powerMap_relations_mem R S y hy
  · intro x hx
    by_cases hs : s<2
    · rw [exteriorDegreeRelations_eq_bot _ _ hs] at hx
      have hz : x=0 := hx
      rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hs)
      change x∈exteriorDegreeRelations (firstForm S k) (secondForm S k) (2+q) at hx
      rw [exteriorDegreeRelations_eq_images] at hx
      obtain ⟨a,⟨y,rfl⟩,b,⟨z,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨y',hy'⟩ := powerMap_surjective R S h q (2*k+1) y
      obtain ⟨z',hz'⟩ := powerMap_surjective R S h q (2*k+1) z
      refine ⟨exteriorPower.wedge R _ 2 q (firstForm R k) y' +
        exteriorPower.wedge R _ 2 q (secondForm R k) z', ?_, ?_⟩
      · rw [exteriorDegreeRelations_eq_images]
        exact Submodule.mem_sup.mpr
          ⟨_,LinearMap.mem_range_self _ y',_,LinearMap.mem_range_self _ z',rfl⟩
      · rw [map_add, powerMap_wedge, powerMap_wedge,
          powerMap_firstForm, powerMap_secondForm, hy', hz']

theorem quotientMap_surjective
    (h : Function.Surjective (algebraMap R S)) (k s : ℕ) :
    Function.Surjective (quotientMap R S k s) := by
  intro y
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (exteriorDegreeRelations (firstForm S k) (secondForm S k) s) y
  obtain ⟨x',hx'⟩ := powerMap_surjective R S h s (2*k+1) x
  refine ⟨Submodule.Quotient.mk x', ?_⟩
  rw [quotientMap_mk, hx']
  rfl

variable {S}

theorem powerMap_quotient_ker (J : Ideal R) (s n : ℕ) :
    (powerMap R (R⧸J) s n).ker = J • (⊤ : Submodule R (⋀[R]^s (Fin n → R))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hz : powerMap R (R⧸J) s n x=0 := hx
    have hc (I : PluckerIndex s n) : (powerBasis R s n).repr x I∈J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change algebraMap R (R⧸J) ((powerBasis R s n).repr x I)=0
      rw [← powerMap_repr, hz, map_zero, Finsupp.zero_apply]
    rw [← (powerBasis R s n).sum_repr x]
    exact Submodule.sum_mem _ fun I hI => Submodule.smul_mem_smul (hc I) (Submodule.mem_top)
  · apply Submodule.smul_le.mpr
    intro r hr x hx
    change powerMap R (R⧸J) s n (r • x)=0
    rw [map_smul, ← IsScalarTower.algebraMap_smul (R⧸J),
      show algebraMap R (R⧸J) r=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_smul]

theorem quotientMap_quotient_ker (J : Ideal R) (k s : ℕ) :
    (quotientMap R (R⧸J) k s).ker =
      J • (⊤ : Submodule R (quotientDegree R k s)) := by
  classical
  let N := exteriorDegreeRelations (firstForm R k) (secondForm R k) s
  let π : (⋀[R]^s (Fin (2*k+1) → R)) →ₗ[R] quotientDegree R k s := N.mkQ
  have hred : Function.Surjective (algebraMap R (R⧸J)) := Ideal.Quotient.mk_surjective
  apply le_antisymm
  · intro z hz
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective N z
    have hx : powerMap R (R⧸J) s (2*k+1) x ∈
        exteriorDegreeRelations (firstForm (R⧸J) k) (secondForm (R⧸J) k) s := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact hz
    have hm := powerMap_relations_surjective R (R⧸J) hred k s
    change powerMap R (R⧸J) s (2*k+1) x ∈
      (exteriorDegreeRelations (firstForm (R⧸J) k)
        (secondForm (R⧸J) k) s).restrictScalars R at hx
    rw [← hm] at hx
    obtain ⟨y,hy,hyx⟩ := hx
    have hxy : x-y∈J • (⊤ : Submodule R (⋀[R]^s (Fin (2*k+1) → R))) := by
      rw [← powerMap_quotient_ker R J s (2*k+1)]
      change powerMap R (R⧸J) s (2*k+1) (x-y)=0
      rw [map_sub, hyx, sub_self]
    have hmap : π (x-y)∈
        (J • (⊤ : Submodule R (⋀[R]^s (Fin (2*k+1) → R)))).map π :=
      Submodule.mem_map_of_mem hxy
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
      (Submodule.mkQ_surjective N)] at hmap
    simpa only [π, map_sub, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hy, sub_zero] using hmap
  · apply Submodule.smul_le.mpr
    intro r hr x hx
    change quotientMap R (R⧸J) k s (r • x)=0
    rw [map_smul, ← IsScalarTower.algebraMap_smul (R⧸J),
      show algebraMap R (R⧸J) r=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_smul]

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0531

section TAF_LiteralSource_0532
/- Original module: PaperVerification.AlternatingFormsPrefixCharacteristic -/


/-!
# Supported prefix division with the exact characteristic restriction

The inverse retains every singleton of the input word.  Its only required
denominator is the factorial of the number of doubly occupied pairs.  This
number is at most half the total exterior degree, which yields precisely
the strict inequality `s < 2*p` in Theorem 7.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [DecidableEq ι] [Fintype ι]

/-- The complete supported prefix inverse, with its actual factorial
condition in place of a characteristic-zero assumption. -/
theorem prefix_selection_division_with_support_of_factorial
    (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
    ∃ η : ⋀[K]^(Fintype.card ι-1) M,
      (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η =
        ((A.toList.map u++B.toList.map v).map (ExteriorAlgebra.ι K)).prod ∧
      (η : ExteriorAlgebra K M) ∈ prefixInverseSpace u v A B := by
  classical
  let S := prefixSingletons A B
  let L := prefixSingletonWord u v A B
  let n := (A ∩ B).card-1
  have hcounts := prefix_occupancy_counts A B hdegree
  have hP := doublePairs_disjoint_singletons A B
  have hPS : ∀ i ∈ A ∩ B,i ∉ S := hP
  have hn : n+1=(A ∩ B).card := by dsimp only [n]; omega
  have hfac' : ((n+1).factorial : K) ≠ 0 := by simpa only [hn] using hfac
  let P : FixedSubsets (PrefixFreePair A B) (n+1) :=
    ⟨(A ∩ B).subtype (fun i => i ∉ S),by
      rw [Finset.card_subtype,Finset.filter_eq_self.mpr hPS]
      exact hn.symm⟩
  let z : ExteriorAlgebra K M := (L.map (ExteriorAlgebra.ι K)).prod
  let η₀ : ExteriorAlgebra K M := z *
    ∑ T : FixedSubsets (PrefixFreePair A B) n,
      inverseCoefficient (K := K) n (T.val ∩ P.val).card •
        pairedMonomial (fun i : PrefixFreePair A B => u i.val)
          (fun i : PrefixFreePair A B => v i.val) T.val
  have hηmem : η₀ ∈ prefixInverseSpace (K := K) u v A B := by
    dsimp only [η₀]
    rw [Finset.mul_sum]
    apply Submodule.sum_mem
    intro T hT
    rw [mul_smul_comm]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨T,rfl⟩
  have hL : ∀ i ∈ S,u i∈L ∨ v i∈L := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Or.inl (List.mem_append_left _
        (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))
    · exact Or.inr (List.mem_append_right _
        (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))
  have hη := local_exterior_pair_division_with_singletons_of_factorial (K := K)
    u v S L hL n hfac' hcounts.2.1 P
  obtain ⟨ε,hε,heq⟩ := exterior_monomial_singleton_pair_factorization (K := K) u v A B
  have hηscaled : ε • η₀ ∈ prefixInverseSpace (K := K) u v A B :=
    Submodule.smul_mem _ _ hηmem
  refine ⟨⟨ε • η₀,prefixInverseSpace_le_degree u v A B hdegree hηscaled⟩,?_,hηscaled⟩
  change (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*(ε • η₀)=_
  rw [mul_smul_comm]
  change ε • ((∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η₀)=_
  rw [show (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η₀ =
    z * pairedMonomial (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) P.val from hη]
  have hpair : pairedMonomial (K := K) (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) P.val = pairedMonomial (K := K) u v (A ∩ B) := by
    exact pairedMonomial_subtype (K := K) (S := S) hPS u v
  rw [hpair]
  exact heq.symm

/-- Each double occupancy consumes two letters of the original word. -/
theorem prefix_double_pair_bound (A B : Finset ι) :
    2*(A ∩ B).card ≤ A.card+B.card := by
  have ha := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
  have hb := Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
  omega

/-- The denominator condition follows from the literal exterior degree,
without an ambient-dimension or number-of-pairs restriction. -/
theorem prefix_factorial_ne_zero_below_twice_characteristic
    (p s : ℕ) [Fact p.Prime] [CharP K p]
    (A B : Finset ι) (hsize : A.card+B.card≤s) (hs : s<2*p) :
    ((A ∩ B).card.factorial : K) ≠ 0 := by
  apply factorial_cast_ne_zero_of_lt_char p
  have hpair := prefix_double_pair_bound A B
  omega

/-- Every prefix division needed in degree `s < 2*p` has the same actual
singleton-preserving support as the characteristic-zero division. -/
theorem prefix_selection_division_with_support_below_twice_characteristic
    (p s : ℕ) [Fact p.Prime] [CharP K p]
    (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1)
    (hsize : A.card+B.card≤s) (hs : s<2*p) :
    ∃ η : ⋀[K]^(Fintype.card ι-1) M,
      (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η =
        ((A.toList.map u++B.toList.map v).map (ExteriorAlgebra.ι K)).prod ∧
      (η : ExteriorAlgebra K M) ∈ prefixInverseSpace u v A B :=
  prefix_selection_division_with_support_of_factorial u v A B hdegree
    (prefix_factorial_ne_zero_below_twice_characteristic p s A B hsize hs)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0532

section TAF_LiteralSource_0533
/- Original module: PaperVerification.AlternatingFormsInitialCharacteristic -/


/-!
# Both initial containments with only the required factorial inverses

Every relation below belongs to the actual isotropy ideal.  The common
vertex weight, retained suffix, singleton support, and nonzero exterior
reordering sign are the same as in the characteristic-zero argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k h s t : ℕ}

/-- Exactly the local factorials that may occur in exterior degree `s`. -/
def DegreeFactorials (K : Type*) [Field K] (s : ℕ) : Prop :=
  ∀ r : ℕ, 2*r≤s → (r.factorial : K) ≠ 0

theorem degreeFactorials_of_lt_twice_characteristic (p s : ℕ)
    [Fact p.Prime] [CharP K p] (hs : s<2*p) : DegreeFactorials K s := by
  intro r hr
  apply factorial_cast_ne_zero_of_lt_char p
  omega

theorem degreeFactorials_charZero [CharZero K] (s : ℕ) : DegreeFactorials K s := by
  intro r hr
  exact_mod_cast Nat.factorial_ne_zero r

set_option maxHeartbeats 800000 in
theorem oddPrefix_actual_lower_relation_of_factorial
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=t+2)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
    ∃ g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K,
      g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) ∧
      totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
        (indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
          B.toList.map (oddPrefixRight hk)++L))+g ∈
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  let u : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixLeft hk i)
  let v : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixRight hk i)
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support_of_factorial (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree) hfac
  let ηE : ExteriorAlgebra K (Fin (2*k+1) → K) := η
  have hηdegree : (η : ExteriorAlgebra K (Fin (2*k+1) → K))∈
      ⋀[K]^(h-1) (Fin (2*k+1) → K) := by
    simpa only [Fintype.card_fin] using η.property
  have hηidentity :
      (∑ i : Fin h,indexExteriorWord (K := K) [oddPrefixLeft hk i,oddPrefixRight hk i])*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
      indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)) := by
    simpa only [u,v,indexExteriorWord,List.map_append,List.map_map,Function.comp_def,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hη
  have hlen : h-1+L.length=t := by
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    omega
  let x : ExteriorAlgebra K (Fin (2*k+1) → K) := ηE*indexExteriorWord (K := K) L
  have hx : x∈⋀[K]^t (Fin (2*k+1) → K) := by
    rw [←hlen]
    exact SetLike.mul_mem_graded hηdegree (indexExteriorWord_mem L)
  let g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
    ∑ j∈(oddPrefixPairs hk)ᶜ,prefixCorrectionCoordinates (K := K) (t+2) (2*k+1)
      (oddPathFirstLeft j) (oddPathMiddle j) L ηE
  have hg : g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
      (((A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
    apply Submodule.sum_mem
    intro j hj
    have hj' : h≤j.val := by
      have hn := Finset.mem_compl.mp hj
      rw [mem_oddPrefixPairs] at hn
      omega
    exact oddPrefix_supported_correction_lower (K := K) hk A B hdegree j hj' L hs ηE hηsupport
  refine ⟨g,hg,?_⟩
  have hmem := totalExteriorPluckerCoordinates_wedge_mem
    (oddPluckerForms (K := K) k) (0 : Fin 2) x hx
  rw [oddPluckerForms_first] at hmem
  have he :
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x=
      indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L)+
        ∑ j∈(oddPrefixPairs hk)ᶜ,
          (indexExteriorWord (K := K) [oddPathFirstLeft j,oddPathMiddle j]*ηE)*indexExteriorWord L := by
    rw [oddPathFirst_split_prefix (K := K) hk,add_mul]
    dsimp only [x]
    rw [←mul_assoc,hηidentity,←indexExteriorWord_append]
    simp only [Finset.sum_mul,mul_assoc,List.append_assoc]
  rw [he,map_add,map_sum] at hmem
  simpa only [g,prefixCorrectionCoordinates,LinearMap.comp_apply,
    LinearMap.mulRight_apply,LinearMap.mulLeft_apply] using hmem

theorem odd_left_variable_mem_initial_of_degree_factorials
    (hfac : DegreeFactorials K (t+2))
    (I : PluckerIndex (t+2) (2*k+1))
    (hbad : ∃ i,(I.val i).val<2*i.val) :
    X I∈initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  obtain ⟨h,hpos,hk,hdegree⟩ := odd_left_failure_matching_selection I.val I.property hbad
  let A := tuplePrefixLeft I.val I.property h
  let B := tuplePrefixRight I.val I.property h
  let L := (tuplePrefixSuffix I.val h).toList
  have hs : (A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).length=t+2 := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc] using
      (tuplePrefixWord_length I.val I.property hk)
  have hfac' : ((A ∩ B).card.factorial : K) ≠ 0 := by
    apply hfac
    have hpair := prefix_double_pair_bound A B
    have hsize := hs
    simp only [List.length_append,List.length_map,Finset.length_toList] at hsize
    omega
  obtain ⟨g,hg,hrel⟩ := oddPrefix_actual_lower_relation_of_factorial
    hk hpos A B hdegree L hs hfac' 
  obtain ⟨ε,hε,hlead⟩ := tuplePrefixWord_coordinates (K := K) I hk
  have hw : ((A.toList.map (oddPrefixLeft hk)++
      B.toList.map (oddPrefixRight hk)++L).map (oddNatVertexWeight k)).sum=
      pluckerVertexWeight (oddNatVertexWeight k) I := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc,pluckerVertexWeight] using
      (tuplePrefixWord_weight I.val I.property hk (oddNatVertexWeight k))
  have hlead' : totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
      (indexExteriorWord (A.toList.map (oddPrefixLeft hk)++
        B.toList.map (oddPrefixRight hk)++L))=ε • X I := by
    simpa only [A,B,L,tuplePrefixWord,List.append_assoc] using hlead
  rw [hw] at hg
  rw [hlead'] at hrel
  exact variable_mem_initialIdeal_of_lower_relation _ _ I ε hε g hg hrel

set_option maxHeartbeats 800000 in
theorem reflectedPrefix_actual_lower_relation_of_factorial
    (hk : h≤k) (hpos : 0<h) (A B : Finset (Fin h))
    (hdegree : A.card+B.card=h+1) (L : List (Fin (2*k+1)))
    (hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=t+2)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
    ∃ g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K,
      g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
        (((A.toList.map (reflectedPrefixLeft hk)++
          B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) ∧
      totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
        (indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
          B.toList.map (reflectedPrefixRight hk)++L))+g ∈
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  let u : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixLeft hk i)
  let v : Fin h → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (reflectedPrefixRight hk i)
  obtain ⟨η,hη,hηsupport⟩ := prefix_selection_division_with_support_of_factorial (K := K) u v A B
    (by simpa only [Fintype.card_fin] using hdegree) hfac
  have hηdegree : (η : ExteriorAlgebra K (Fin (2*k+1) → K))∈
      ⋀[K]^(h-1) (Fin (2*k+1) → K) := by
    simpa only [Fintype.card_fin] using η.property
  have hηidentity :
      (∑ i : Fin h,indexExteriorWord (K := K) [reflectedPrefixLeft hk i,reflectedPrefixRight hk i])*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
      indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)) := by
    simpa only [indexExteriorWord_pair,u,v,indexExteriorWord,List.map_append,
      List.map_map,Function.comp_def,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one] using hη
  have hlen : h-1+L.length=t := by
    simp only [List.length_append,List.length_map,Finset.length_toList] at hs
    omega
  let x : ExteriorAlgebra K (Fin (2*k+1) → K) :=
    (η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord (K := K) L
  have hx : x∈⋀[K]^t (Fin (2*k+1) → K) := by
    rw [←hlen]
    exact SetLike.mul_mem_graded hηdegree (indexExteriorWord_mem (K := K) L)
  let g : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
    ∑ j∈(oddPrefixPairs hk)ᶜ,prefixCorrectionCoordinates (K := K) (t+2) (2*k+1)
      (oddPathFirstLeft j).rev (oddPathMiddle j).rev L
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))
  have hg : g∈lowerWeightSpace (pluckerVertexWeight (oddNatVertexWeight k))
      (((A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum) := by
    apply Submodule.sum_mem
    intro j hj
    have hj' : h≤j.val := by
      have hn := Finset.mem_compl.mp hj
      rw [mem_oddPrefixPairs] at hn
      omega
    exact reflectedPrefix_supported_correction_lower hk A B hdegree j hj' L hs
      (η : ExteriorAlgebra K (Fin (2*k+1) → K)) hηsupport
  refine ⟨g,hg,?_⟩
  have hmemSecond := totalExteriorPluckerCoordinates_wedge_mem (K := K) (t := t)
    (oddPluckerForms (K := K) k) (1 : Fin 2) x hx
  rw [oddPluckerForms_second] at hmemSecond
  have hmem : totalExteriorPluckerCoordinates (K := K) (t+2) (2*k+1)
      ((oddPathFirstQuadratic (K := K) (fun i => Pi.basisFun K (Fin (2*k+1)) i.rev) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x)∈
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
    rw [oddPath_reflection,Submodule.coe_neg,neg_mul,map_neg]
    exact (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)).neg_mem hmemSecond
  have he :
      (oddPathFirstQuadratic (K := K) (fun i => Pi.basisFun K (Fin (2*k+1)) i.rev) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*x=
      indexExteriorWord (A.toList.map (reflectedPrefixLeft hk)++
        B.toList.map (reflectedPrefixRight hk)++L)+
        ∑ j∈(oddPrefixPairs hk)ᶜ,
          (indexExteriorWord (K := K) [(oddPathFirstLeft j).rev,(oddPathMiddle j).rev]*
            (η : ExteriorAlgebra K (Fin (2*k+1) → K)))*indexExteriorWord (K := K) L := by
    rw [reflectedFirst_split_prefix hk,add_mul]
    dsimp only [x]
    rw [←mul_assoc,hηidentity,←indexExteriorWord_append]
    simp only [Finset.sum_mul,mul_assoc,List.append_assoc]
  rw [he,map_add,map_sum] at hmem
  simpa only [g,prefixCorrectionCoordinates,LinearMap.comp_apply,
    LinearMap.mulRight_apply,LinearMap.mulLeft_apply] using hmem

theorem odd_right_variable_mem_initial_of_degree_factorials
    (hfac : DegreeFactorials K (t+2))
    (I : PluckerIndex (t+2) (2*k+1))
    (hbad : ∃ i,2*k+2+2*i.val<(I.val i).val+2*(t+2)) :
    X I∈initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  let J := reflectSelection I.val
  have hJ : StrictMono J := reflectSelection_strictMono I.val I.property
  have hbadJ : ∃ i,(J i).val<2*i.val := by
    apply right_failure_becomes_left I.val
    obtain ⟨i,hi⟩ := hbad
    exact ⟨i,by omega⟩
  obtain ⟨h,hpos,hk,hdegree⟩ := odd_left_failure_matching_selection J hJ hbadJ
  let A := tuplePrefixLeft J hJ h
  let B := tuplePrefixRight J hJ h
  let L := (tuplePrefixSuffix J h).toList.map Fin.rev
  have hword : A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L=reflectedPrefixWord I hk := by
    simp only [A,B,L,J,reflectedPrefixWord,tuplePrefixWord,reflectedPrefixLeft,
      reflectedPrefixRight,List.map_append,List.map_map,Function.comp_def,List.append_assoc]
    rfl
  have hs : (A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).length=t+2 := by
    rw [hword,reflectedPrefixWord_length]
  have hfac' : ((A ∩ B).card.factorial : K) ≠ 0 := by
    apply hfac
    have hpair := prefix_double_pair_bound A B
    have hsize := hs
    simp only [List.length_append,List.length_map,Finset.length_toList] at hsize
    omega
  obtain ⟨g,hg,hrel⟩ := reflectedPrefix_actual_lower_relation_of_factorial
    hk hpos A B hdegree L hs hfac' 
  obtain ⟨ε,hε,hlead⟩ := reflectedPrefixWord_coordinates (K := K) I hk
  have hw : ((A.toList.map (reflectedPrefixLeft hk)++
      B.toList.map (reflectedPrefixRight hk)++L).map (oddNatVertexWeight k)).sum=
      pluckerVertexWeight (oddNatVertexWeight k) I := by
    rw [hword,reflectedPrefixWord_weight]
    rfl
  rw [hw] at hg
  rw [hword,hlead] at hrel
  exact variable_mem_initialIdeal_of_lower_relation _ _ I ε hε g hg hrel

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0533

section TAF_LiteralSource_0534
/- Original module: PaperVerification.AlternatingFormsOddInitialCharacteristic -/


/-!
# The exact odd initial ideal with the degree-dependent factorial condition

The full Richardson ideal is proved equal to the actual weight initial
ideal.  No dimension, primality, or extra relation is assumed: the interval
domain and its dimension are supplied by integral standard monomials, and
the opposite dimension inequality comes from the actual isotropic chart.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K]

theorem odd_interval_le_initial_of_degree_factorials
    (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    intervalPluckerIdeal (K := K) (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs) ≤
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  apply sup_le
  · exact matrixPluckerIdeal_le_initial_isotropic _ _
  · apply Ideal.span_le.mpr
    rintro _ ⟨I,hbad,rfl⟩
    obtain ⟨i,hi⟩ := not_forall.mp hbad
    by_cases hl : oddIntervalLower k (t+2) hs i≤I.val i
    · have hr : ¬ I.val i≤oddIntervalUpper k (t+2) hs i :=
        fun h => hi ⟨hl,h⟩
      apply odd_right_variable_mem_initial_of_degree_factorials hfac I
      refine ⟨i,?_⟩
      have hv : 2*(k+1-(t+2)+i.val)<(I.val i).val := lt_of_not_ge hr
      omega
    · apply odd_left_variable_mem_initial_of_degree_factorials hfac I
      exact ⟨i,lt_of_not_ge hl⟩

theorem odd_isotropic_initial_eq_interval_of_degree_factorials
    (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) := by
  letI := intervalPluckerIdeal_isPrime (K := K)
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)
  exact initial_eq_of_prime_candidate _ _ _ ((t+2)*(2*k+2-2*(t+2))+1)
    (odd_interval_le_initial_of_degree_factorials k t hs hfac)
    (oddInterval_krullDim k (t+2) hs (by omega))
    (odd_isotropic_Plucker_cone_dimension_ge k t hs)

/-- The initial-ideal assertion of Theorem 7.1, for every prime, including
two, and every plane dimension at least two in the stated range. -/
theorem paper_theorem_7_1_initial_ideal
    (p k t : ℕ) [Fact p.Prime] [CharP K p]
    (hs : t+2≤k+1) (hp : t+2<2*p) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) :=
  odd_isotropic_initial_eq_interval_of_degree_factorials k t hs
    (degreeFactorials_of_lt_twice_characteristic p (t+2) hp)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0534

