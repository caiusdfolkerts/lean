module

public import PaperVerification.DiagonalBarWords
public import PaperVerification.BarCoefficientRecursion
public import Mathlib.Data.Fintype.BigOperators

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
