module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import sunlet.arbitrary_orbit_classification
public import sunlet.dimension_algebra
public import sunlet.permutation_families
public import sunlet.polynomial_image
public import sunlet.rational_partials
public import sunlet.verified_network_algebra
public import sunlet.verified_network_graph
public import sunlet.weighted_initial

/-! Exact ordinary proof stage 3 of 3.
All source bodies below are preserved from the canonical project.
Generation alone is not verification; require a successful stock Lean check. -/

@[expose] public section

#eval IO.println "NETWORK_STAGE_IMPORTS_COMPLETE VerifiedNetworkConclusion"

section NetworkStageSource_Sunlet_NetworkPathKernel


/-!
# The exponent kernel along an arbitrary caterpillar

The cycle-flow coordinates at successive vertices are independent. A mixed
difference in two adjacent coordinates isolates the function on their common
edge. The resulting additive function on the finite group vanishes. This
argument works at every path length and for arbitrary finite abelian groups.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkPathKernel

variable {G V : Type*} [AddCommGroup G] [Fintype G] [DecidableEq V]

def pairConfiguration (a b : V) (x y : G) : V → G :=
  fun v => if v = a then x else if v = b then y else 0

def mixed (a b : V) (x y : G) (F : (V → G) → ℚ) : ℚ :=
  F (pairConfiguration a b x y) - F (pairConfiguration a b x 0) -
    F (pairConfiguration a b 0 y) + F (pairConfiguration a b 0 0)

theorem mixed_add (a b : V) (x y : G) (F H : (V → G) → ℚ) :
    mixed a b x y (fun p => F p+H p) = mixed a b x y F+mixed a b x y H := by
  unfold mixed
  ring

theorem mixed_sum {I : Type*} [Fintype I] (a b : V) (x y : G)
    (F : I → (V → G) → ℚ) :
    mixed a b x y (fun p => ∑ i,F i p) = ∑ i,mixed a b x y (F i) := by
  simp only [mixed,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem mixed_vertex (a b v : V) (x y : G) (f : G → ℚ) :
    mixed a b x y (fun p => f (p v)) = 0 := by
  by_cases ha : v=a
  · subst v
    simp [mixed,pairConfiguration]
  · by_cases hb : v=b
    · subst v
      simp [mixed,pairConfiguration,ha]
    · simp [mixed,pairConfiguration,ha,hb]

variable {k : ℕ}

theorem edge_mixed (i : Fin k) (x y : G) (f : G → ℚ) :
    mixed i.castSucc i.succ x y
      (fun p : Fin (k+1) → G => f (p i.succ-p i.castSucc)) =
        f (y-x)-f (-x)-f y+f 0 := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_succ] at this
    omega
  simp [mixed,pairConfiguration,hne,hne.symm]

theorem other_edge_mixed (i j : Fin k) (hji : j ≠ i)
    (x y : G) (f : G → ℚ) :
    mixed i.castSucc i.succ x y
      (fun p : Fin (k+1) → G => f (p j.succ-p j.castSucc)) = 0 := by
  have hll : j.castSucc ≠ i.castSucc := by
    intro h
    exact hji (Fin.castSucc_inj.mp h)
  have hrr : j.succ ≠ i.succ := by
    intro h
    apply hji
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [Fin.val_succ] at hh
    omega
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  by_cases hlr : j.castSucc = i.succ
  · have hrl : j.succ ≠ i.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      have hh' := congrArg Fin.val hlr
      simp only [Fin.val_castSucc,Fin.val_succ] at hh hh'
      omega
    simp [mixed,pairConfiguration,hll,hrr,hlr,hrl,hne,hne.symm]
  · by_cases hrl : j.succ = i.castSucc <;>
      simp [mixed,pairConfiguration,hll,hrr,hlr,hrl,hne,hne.symm]

def pathFunctional (f : Fin (k+1) → G → ℚ) (b : Fin k → G → ℚ)
    (p : Fin (k+1) → G) : ℚ :=
  (∑ j,f j (p j)) + ∑ i,b i (p i.succ-p i.castSucc)

/-- The literal functional kernel on a finite path is zero, after fixing
the value at the group identity in each coefficient function. -/
theorem path_kernel_zero
    (f : Fin (k+1) → G → ℚ) (b : Fin k → G → ℚ)
    (hf0 : ∀ j,f j 0=0) (hb0 : ∀ i,b i 0=0)
    (h : ∀ p,pathFunctional f b p=0) : f=0 ∧ b=0 := by
  have hbDiff (i : Fin k) (x y : G) : b i (y-x)=b i (-x)+b i y := by
    have hm : mixed i.castSucc i.succ x y (pathFunctional f b)=0 := by
      simp only [mixed,h]
      ring
    change mixed i.castSucc i.succ x y
      (fun p => (∑ j,f j (p j)) + ∑ j,b j (p j.succ-p j.castSucc))=0 at hm
    have hm' : (∑ j,mixed i.castSucc i.succ x y
        (fun p : Fin (k+1) → G => f j (p j))) +
        (∑ j,mixed i.castSucc i.succ x y
          (fun p : Fin (k+1) → G => b j (p j.succ-p j.castSucc)))=0 := by
      simpa only [mixed_add,mixed_sum] using hm
    simp only [mixed_vertex,Finset.sum_const_zero,zero_add] at hm'
    rw [Finset.sum_eq_single i] at hm'
    · rw [edge_mixed,hb0] at hm'
      linear_combination hm'
    · intro j _ hji
      exact other_edge_mixed i j hji x y (b j)
    · simp
  have hbAdd (i : Fin k) (x y : G) : b i (x+y)=b i x+b i y := by
    have hh := hbDiff i (-x) y
    simpa only [neg_neg,sub_neg_eq_add,add_comm] using hh
  have hb : b=0 := by
    funext i x
    exact NetworkClaw.additive_function_zero (b i) (hbAdd i) x
  refine ⟨?_,hb⟩
  funext j x
  have hh := h (Pi.single j x)
  simp only [pathFunctional,hb,Pi.zero_apply,Finset.sum_const_zero,add_zero] at hh
  rw [Finset.sum_eq_single j] at hh
  · simpa [Pi.single_apply] using hh
  · intro i _ hij
    simp [Pi.single_apply,hij,hf0]
  · simp

end Sunlet.NetworkPathKernel
end
end NetworkStageSource_Sunlet_NetworkPathKernel
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkPathKernel"

section NetworkStageSource_Sunlet_NetworkFourSunletKernel


/-!
# The selected exponent kernel of the four-sunlet

The selection is the literal one from the cited network dimension proof:
the second monomial is selected exactly when the reticulation flow is
nonzero and the next leaf flow is zero. The functions below are parameter
exponent coefficients, not a replacement definition of model dimension.
-/

noncomputable section

namespace Sunlet.NetworkFourSunletKernel

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem punctured_translation_zero (hm : 3 ≤ Fintype.card G)
    (A U : G → ℚ) (hA0 : A 0 = 0) (hU0 : U 0 = 0)
    (h : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 → A (x+y)-A y = U x) :
    A = 0 ∧ U = 0 := by
  classical
  let P : Set G := {x | x ≠ 0}
  let π : G → Equiv.Perm G := fun x => Equiv.addLeft x
  have hc : 1 < (Finset.univ.erase (0 : G)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0),Finset.card_univ]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hc
  have htwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b := by
    refine ⟨a,(Finset.mem_erase.mp ha).1,b,(Finset.mem_erase.mp hb).1,?_⟩
    intro he
    apply hab
    simpa [π] using congrArg (fun p : Equiv.Perm G => p 0) he
  have hne : ∀ a ∈ P, π a ≠ 1 := by
    intro a ha he
    apply ha
    simpa [π] using congrArg (fun p : Equiv.Perm G => p 0) he
  have hh := PuncturedDifferences.family_outgoing (o := (0 : G))
    (π := π) (P := P) (F := A) (c := U) hne htwo
    (by intro a ha y hy; exact h a ha y hy)
  constructor
  · funext a
    by_cases ha : a = 0
    · simpa [ha] using hA0
    · have he := (hh a ha).2 0
      simpa [π,hA0] using he
  · funext a
    by_cases ha : a = 0
    · simpa [ha] using hU0
    · exact (hh a ha).1

def selectedRelation (z : ℚ) (U V A B C D E : G → ℚ) (x y t : G) : ℚ :=
  z + A y + B (-(x+y+t)) + C t +
    if x = 0 ∨ y ≠ 0 then U x + D (x+y) + E (-t)
    else V x + D y + E (-(x+t))

/-- No nonzero relation remains after the six explicit normalizations of
the contracted four-sunlet. This holds for every finite abelian group of
order at least three. -/
theorem selected_kernel_zero (hm : 3 ≤ Fintype.card G)
    (z : ℚ) (U V A B C D E : G → ℚ)
    (hU0 : U 0 = 0) (hV0 : V 0 = 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hC0 : C 0 = 0)
    (hD0 : D 0 = 0) (hE0 : E 0 = 0)
    (h : ∀ x y t, selectedRelation z U V A B C D E x y t = 0) :
    z = 0 ∧ U = 0 ∧ V = 0 ∧ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 := by
  have hz : z = 0 := by
    simpa [selectedRelation,hU0,hA0,hB0,hC0,hD0,hE0] using h 0 0 0
  have hclaw (y t : G) :
      (A y+D y)+(C t+E (-t))+B (-(y+t)) = 0 := by
    have hh := h 0 y t
    simp only [selectedRelation,hz,zero_add,eq_self, true_or,if_true,hU0] at hh
    linear_combination hh
  obtain ⟨hAD,hCE,hB⟩ := NetworkClaw.normalized_relation_zero
    (E := ℚ) (fun x : G => x) Function.surjective_id
    (fun y => A y+D y) (fun t => C t+E (-t)) B
    (by simp [hA0,hD0]) (by simp [hC0,hE0]) hclaw
  have hD (a : G) : D a = -A a := by
    have hh := congrFun hAD a
    change A a+D a=0 at hh
    linear_combination hh
  have hE (a : G) : E a = -C (-a) := by
    have hh := congrFun hCE (-a)
    change C (-a)+E (- -a)=0 at hh
    simp only [neg_neg] at hh
    linear_combination hh
  have hV (x t : G) : V x+C t-C (x+t)=0 := by
    by_cases hx : x=0
    · simp [hx,hV0]
    · have hh := h x 0 t
      simp [selectedRelation,hz,hA0,hB,hD0,hx,hE] at hh
      linear_combination hh
  have hVC (x : G) : V x=C x := by
    have hh := hV x 0
    simp only [hC0,add_zero] at hh
    linear_combination hh
  have hCadd (x t : G) : C (x+t)=C x+C t := by
    have hh := hV x t
    rw [hVC] at hh
    linear_combination -hh
  have hC : C=0 := funext (NetworkClaw.additive_function_zero C hCadd)
  have hVV : V=0 := by ext x; rw [hVC,hC]
  have hEE : E=0 := by ext x; simp [hE,hC]
  have hUrel : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 → A (x+y)-A y=U x := by
    intro x hx y hy
    have hh := h x y 0
    simp [selectedRelation,hz,hB,hC,hEE,hy,hD] at hh
    linear_combination -hh
  obtain ⟨hA,hU⟩ := punctured_translation_zero hm A U hA0 hU0 hUrel
  have hDD : D=0 := by ext x; simp [hD,hA]
  exact ⟨hz,hU,hVV,hA,hB,hC,hDD,hEE⟩

end Sunlet.NetworkFourSunletKernel
end
end NetworkStageSource_Sunlet_NetworkFourSunletKernel
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFourSunletKernel"

section NetworkStageSource_Sunlet_NetworkSunletKernel


/-!
# The selected exponent kernel for every sunlet of length at least four

There are k+1 independent successive cycle-flow coordinates, with k≥1.
Mixed differences first remove the internal leaf and cycle coefficients;
the two endpoint coordinates then give exactly the four-sunlet kernel.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletKernel

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {k : ℕ}

def selectedRelation (z : ℚ) (U V A C : G → ℚ)
    (B : Fin k → G → ℚ) (D : Fin (k+1) → G → ℚ)
    (x : G) (p : Fin (k+1) → G) : ℚ :=
  z+A (p 0-x)+(∑ i,B i (p i.succ-p i.castSucc))+C (-p (Fin.last k))+
    if x=0 ∨ p 0≠x then U x+∑ j,D j (p j)
    else V x+∑ j,D j (p j-x)

theorem endpoints_distinct (hk : 1≤k) : (0 : Fin (k+1))≠Fin.last k := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_zero,Fin.val_last] at hh
  omega

def pathVertex (A C : G → ℚ) (D : Fin (k+1) → G → ℚ)
    (j : Fin (k+1)) (x : G) : ℚ :=
  D j x+(if j=0 then A x else 0)+(if j=Fin.last k then C (-x) else 0)

theorem pathVertex_sum (A C : G → ℚ) (D : Fin (k+1) → G → ℚ)
    (p : Fin (k+1) → G) :
    (∑ j,pathVertex A C D j (p j))=
      (∑ j,D j (p j))+A (p 0)+C (-p (Fin.last k)) := by
  simp [pathVertex,Finset.sum_add_distrib]

theorem sum_endpoints (hk : 1≤k) (D : Fin (k+1) → G → ℚ)
    (hD : ∀ j,j≠0 → j≠Fin.last k → D j=0) (p : Fin (k+1) → G) :
    (∑ j,D j (p j))=D 0 (p 0)+D (Fin.last k) (p (Fin.last k)) := by
  have hs : (∑ j∈({0,Fin.last k} : Finset (Fin (k+1))),D j (p j))=
      ∑ j,D j (p j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj0 : j≠0 := by intro h; subst j; simp at hj
    have hjk : j≠Fin.last k := by intro h; subst j; simp at hj
    simp [hD j hj0 hjk]
  rw [← hs]
  simp [endpoints_distinct hk]

/-- The full selected exponent relation is zero for every path length,
not merely for a bounded list of sunlets. -/
theorem selected_kernel_zero (hk : 1≤k) (hm : 3≤Fintype.card G)
    (z : ℚ) (U V A C : G → ℚ)
    (B : Fin k → G → ℚ) (D : Fin (k+1) → G → ℚ)
    (hU0 : U 0=0) (hV0 : V 0=0) (hA0 : A 0=0) (hC0 : C 0=0)
    (hB0 : ∀ i,B i 0=0) (hD0 : ∀ j,D j 0=0)
    (h : ∀ x p,selectedRelation z U V A C B D x p=0) :
    z=0 ∧ U=0 ∧ V=0 ∧ A=0 ∧ C=0 ∧ B=0 ∧ D=0 := by
  have hz : z=0 := by
    simpa [selectedRelation,hU0,hA0,hC0,hB0,hD0] using h 0 (fun _ => 0)
  have hp : ∀ p,NetworkPathKernel.pathFunctional (pathVertex A C D) B p=0 := by
    intro p
    have hh := h 0 p
    simp only [selectedRelation,hz,zero_add,sub_zero,eq_self,true_or,if_true,hU0] at hh
    rw [NetworkPathKernel.pathFunctional,pathVertex_sum]
    linear_combination hh
  obtain ⟨hf,hB⟩ := NetworkPathKernel.path_kernel_zero (pathVertex A C D) B
    (by intro j; simp [pathVertex,hD0,hA0,hC0]) hB0 hp
  have hDmid : ∀ j,j≠0 → j≠Fin.last k → D j=0 := by
    intro j hj0 hjk
    funext a
    have hh := congrFun (congrFun hf j) a
    simpa [pathVertex,hj0,hjk] using hh
  have hfour : ∀ x y t,NetworkFourSunletKernel.selectedRelation z U V A 0 C
      (D 0) (D (Fin.last k)) x y t=0 := by
    intro x y t
    let p := NetworkPathKernel.pairConfiguration (0 : Fin (k+1)) (Fin.last k) (x+y) (-t)
    have hp0 : p 0=x+y := by simp [p,NetworkPathKernel.pairConfiguration]
    have hpk : p (Fin.last k)=-t := by
      simp [p,NetworkPathKernel.pairConfiguration,(endpoints_distinct hk).symm]
    have hh := h x p
    rw [selectedRelation,sum_endpoints hk D hDmid p,
      sum_endpoints hk D hDmid (fun j => p j-x)] at hh
    simp only [hp0,hpk,Pi.zero_apply,hB,Finset.sum_const_zero,add_zero,neg_neg] at hh
    have hleft : x+y-x=y := by abel
    have hcond : (x=0 ∨ x+y≠x) ↔ (x=0 ∨ y≠0) := by simp
    have hright : -t-x=-(x+t) := by abel
    simpa only [NetworkFourSunletKernel.selectedRelation,Pi.zero_apply,add_zero,
      hleft,hcond,hright,add_assoc] using hh
  obtain ⟨_,hU,hV,hA,_,hC,hDfirst,hDlast⟩ :=
    NetworkFourSunletKernel.selected_kernel_zero hm z U V A 0 C (D 0) (D (Fin.last k))
      hU0 hV0 hA0 rfl hC0 (hD0 0) (hD0 (Fin.last k)) hfour
  refine ⟨hz,hU,hV,hA,hC,hB,?_⟩
  funext j a
  by_cases hj0 : j=0
  · subst j
    exact congrFun hDfirst a
  · by_cases hjk : j=Fin.last k
    · subst j
      exact congrFun hDlast a
    · exact congrFun (hDmid j hj0 hjk) a

end Sunlet.NetworkSunletKernel
end
end NetworkStageSource_Sunlet_NetworkSunletKernel
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletKernel"

section NetworkStageSource_Sunlet_NetworkSunletExponents


/-! Literal coordinate polynomials and their selected exponent matrix for
the contracted s-sunlet, uniformly for s=k+3 and k≥1. -/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletExponents

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] [Field K] {k : ℕ}

abbrev Family (k : ℕ) := Fin 4 ⊕ (Fin k ⊕ Fin (k+1))
abbrev Parameter (k : ℕ) (C : Type*) := Family k × C
abbrev Flow (k : ℕ) (G : Type*) := G × (Fin (k+1) → G)

def aFamily : Family k := .inl 0
def cFamily : Family k := .inl 1
def uFamily : Family k := .inl 2
def vFamily : Family k := .inl 3
def bFamily (i : Fin k) : Family k := .inr (.inl i)
def dFamily (j : Fin (k+1)) : Family k := .inr (.inr j)

def leafExponent (q : G → C) (f : Flow k G) : Parameter k C →₀ ℕ :=
  Finsupp.single (aFamily,q (f.2 0-f.1)) 1+
    (∑ i,Finsupp.single (bFamily i,q (f.2 i.succ-f.2 i.castSucc)) 1)+
    Finsupp.single (cFamily,q (-f.2 (Fin.last k))) 1

def uExponent (q : G → C) (f : Flow k G) : Parameter k C →₀ ℕ :=
  leafExponent q f+Finsupp.single (uFamily,q f.1) 1+
    ∑ j,Finsupp.single (dFamily j,q (f.2 j)) 1

def vExponent (q : G → C) (f : Flow k G) : Parameter k C →₀ ℕ :=
  leafExponent q f+Finsupp.single (vFamily,q f.1) 1+
    ∑ j,Finsupp.single (dFamily j,q (f.2 j-f.1)) 1

def selectsU (f : Flow k G) : Prop := f.1=0 ∨ f.2 0≠f.1

instance (f : Flow k G) : Decidable (selectsU f) := by
  unfold selectsU
  infer_instance

def selectedExponent (q : G → C) (f : Flow k G) : Parameter k C →₀ ℕ :=
  if selectsU f then uExponent q f else vExponent q f

/-- The actual sum of the two tree monomials. All original edge-class
variables, including their zero classes, remain present. -/
def coordinate (q : G → C) (f : Flow k G) : MvPolynomial (Parameter k C) K :=
  MvPolynomial.monomial (uExponent q f) 1+MvPolynomial.monomial (vExponent q f) 1

def dot (d : Parameter k C →₀ ℕ) (w : Parameter k C → ℚ) : ℚ :=
  ∑ i,(d i : ℚ)*w i

@[simp] theorem dot_single (j : Parameter k C) (w : Parameter k C → ℚ) :
    dot (Finsupp.single j 1) w=w j := by
  simp [dot,Finsupp.single_apply]

theorem dot_add (d e : Parameter k C →₀ ℕ) (w : Parameter k C → ℚ) :
    dot (d+e) w=dot d w+dot e w := by
  simp [dot,Finsupp.add_apply,Nat.cast_add,add_mul,Finset.sum_add_distrib]

theorem dot_sum {I : Type*} [Fintype I] (d : I → Parameter k C →₀ ℕ)
    (w : Parameter k C → ℚ) : dot (∑ i,d i) w=∑ i,dot (d i) w := by
  simp only [dot,Finsupp.finsetSum_apply,Nat.cast_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem dot_selected (q : G → C) (f : Flow k G) (w : Parameter k C → ℚ) :
    dot (selectedExponent q f) w=
      NetworkSunletKernel.selectedRelation 0
        (fun x => w (uFamily,q x)) (fun x => w (vFamily,q x))
        (fun x => w (aFamily,q x)) (fun x => w (cFamily,q x))
        (fun i x => w (bFamily i,q x)) (fun j x => w (dFamily j,q x)) f.1 f.2 := by
  by_cases hs : f.1=0 ∨ f.2 0≠f.1 <;>
    simp [selectedExponent,selectsU,hs,uExponent,vExponent,leafExponent,dot_add,dot_sum,
      NetworkSunletKernel.selectedRelation] <;> ring

def reverseWeight (c0 : C) (j : Parameter k C) : ℕ :=
  if j.1=uFamily then 1 else if j.1=dFamily 0 ∧ j.2=c0 then 2 else 0

def liftedVariable (c0 : C) (j : Parameter k C) : WithBot (Parameter k C) →₀ ℕ :=
  Finsupp.single (j : WithBot (Parameter k C)) 1+Finsupp.single ⊥ (reverseWeight c0 j)

def liftExponent (c0 : C) (d : Parameter k C →₀ ℕ) :
    WithBot (Parameter k C) →₀ ℕ :=
  Finsupp.linearCombination ℕ (liftedVariable c0) d

def weightHom (c0 : C) :
    MvPolynomial (Parameter k C) K →ₐ[K] MvPolynomial (WithBot (Parameter k C)) K :=
  MvPolynomial.aeval (R := K) (fun j => MvPolynomial.monomial (liftedVariable c0 j) 1)

@[simp] theorem liftExponent_single (c0 : C) (j : Parameter k C) :
    liftExponent c0 (Finsupp.single j 1)=liftedVariable c0 j := by
  simp [liftExponent]

theorem liftExponent_add (c0 : C) (d e : Parameter k C →₀ ℕ) :
    liftExponent c0 (d+e)=liftExponent c0 d+liftExponent c0 e := map_add _ _ _

theorem liftExponent_sum {I : Type*} [Fintype I] (c0 : C)
    (d : I → Parameter k C →₀ ℕ) :
    liftExponent c0 (∑ i,d i)=∑ i,liftExponent c0 (d i) := map_sum _ _ _

@[simp] theorem liftExponent_coe (c0 : C) (d : Parameter k C →₀ ℕ)
    (j : Parameter k C) : liftExponent c0 d (j : WithBot (Parameter k C))=d j := by
  induction d using Finsupp.induction with
  | zero => simp [liftExponent]
  | single_add a n d ha hn ih =>
    rw [liftExponent_add,Finsupp.add_apply,ih,Finsupp.add_apply]
    congr 1
    by_cases h : a=j <;> simp [liftExponent,liftedVariable,Finsupp.single_apply,h]

theorem lifted_u_weight (q : G → C) (hzero : ∀ x,q x=q 0 ↔ x=0) (f : Flow k G) :
    liftExponent (q 0) (uExponent q f) ⊥=1+(if f.2 0=0 then 2 else 0) := by
  simp [uExponent,leafExponent,liftExponent_add,liftExponent_sum,liftedVariable,
    reverseWeight,aFamily,cFamily,uFamily,vFamily,bFamily,dFamily,hzero]
  rw [Finset.sum_eq_single (0 : Fin (k+1))] <;> simp_all

theorem lifted_v_weight (q : G → C) (hzero : ∀ x,q x=q 0 ↔ x=0) (f : Flow k G) :
    liftExponent (q 0) (vExponent q f) ⊥=(if f.2 0=f.1 then 2 else 0) := by
  simp [vExponent,leafExponent,liftExponent_add,liftExponent_sum,liftedVariable,
    reverseWeight,aFamily,cFamily,uFamily,vFamily,bFamily,dFamily,hzero,sub_eq_zero]
  rw [Finset.sum_eq_single (0 : Fin (k+1))] <;> simp_all

theorem strict_selected_weight (q : G → C) (hzero : ∀ x,q x=q 0 ↔ x=0)
    (f : Flow k G) :
    if selectsU f then
      liftExponent (q 0) (vExponent q f) ⊥<liftExponent (q 0) (uExponent q f) ⊥
    else liftExponent (q 0) (uExponent q f) ⊥<liftExponent (q 0) (vExponent q f) ⊥ := by
  rw [lifted_u_weight q hzero,lifted_v_weight q hzero]
  by_cases hx : f.1=0 <;> by_cases hp : f.2 0=f.1 <;> by_cases hp0 : f.2 0=0 <;>
    simp_all [selectsU]

end Sunlet.NetworkSunletExponents
end
end NetworkStageSource_Sunlet_NetworkSunletExponents
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletExponents"

section NetworkStageSource_Sunlet_NetworkSunletRank


/-! The selected exponent matrix has the full normalized rank at every
sunlet length; its rows are still the original polynomial exponents. -/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletExponents

variable {G C : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] {k : ℕ}

abbrev Reduced (k : ℕ) (c0 : C) := Option (Family k × {c : C // c≠c0})

def normalizedCoefficient (c0 : C) (w : Reduced k c0 → ℚ) (f : Family k) (c : C) : ℚ :=
  if hc : c=c0 then 0 else w (some (f,⟨c,hc⟩))

@[simp] theorem normalizedCoefficient_zero (c0 : C) (w : Reduced k c0 → ℚ)
    (f : Family k) : normalizedCoefficient c0 w f c0=0 := by
  simp [normalizedCoefficient]

def coefficientLift (c0 : C) : (Reduced k c0 → ℚ) →ₗ[ℚ] (Parameter k C → ℚ) where
  toFun w j := normalizedCoefficient c0 w j.1 j.2+
    if j.1=uFamily ∨ j.1=vFamily then w none else 0
  map_add' w v := by
    funext j
    simp only [normalizedCoefficient,Pi.add_apply]
    split_ifs <;> ring
  map_smul' a w := by
    funext j
    simp only [normalizedCoefficient,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> ring

def selectedMatrix (q : G → C) : Matrix (Flow k G) (Parameter k C) ℚ :=
  fun f j => (selectedExponent q f j : ℚ)

theorem relation_lift (q : G → C) (w : Reduced k (q 0) → ℚ) (f : Flow k G) :
    (selectedMatrix (k := k) q).mulVecLin (coefficientLift (q 0) w) f=
      NetworkSunletKernel.selectedRelation (w none)
        (fun x => normalizedCoefficient (q 0) w uFamily (q x))
        (fun x => normalizedCoefficient (q 0) w vFamily (q x))
        (fun x => normalizedCoefficient (q 0) w aFamily (q x))
        (fun x => normalizedCoefficient (q 0) w cFamily (q x))
        (fun i x => normalizedCoefficient (q 0) w (bFamily i) (q x))
        (fun j x => normalizedCoefficient (q 0) w (dFamily j) (q x)) f.1 f.2 := by
  change dot (selectedExponent q f) (coefficientLift (q 0) w)=_
  rw [dot_selected]
  simp [NetworkSunletKernel.selectedRelation,coefficientLift,
    aFamily,cFamily,uFamily,vFamily,bFamily,dFamily]
  split_ifs <;> ring

theorem lifted_relation_injective (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) :
    Function.Injective ((selectedMatrix (k := k) q).mulVecLin.comp
      (coefficientLift (q 0))) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  have hrel : ∀ x p,NetworkSunletKernel.selectedRelation (w none)
      (fun x => normalizedCoefficient (q 0) w uFamily (q x))
      (fun x => normalizedCoefficient (q 0) w vFamily (q x))
      (fun x => normalizedCoefficient (q 0) w aFamily (q x))
      (fun x => normalizedCoefficient (q 0) w cFamily (q x))
      (fun i x => normalizedCoefficient (q 0) w (bFamily i) (q x))
      (fun j x => normalizedCoefficient (q 0) w (dFamily j) (q x)) x p=0 := by
    intro x p
    have hh := congrFun hw (x,p)
    simpa only [LinearMap.comp_apply,relation_lift,Pi.zero_apply] using hh
  obtain ⟨hz,hU,hV,hA,hC,hB,hD⟩ := NetworkSunletKernel.selected_kernel_zero hk hm
    (w none)
    (fun x => normalizedCoefficient (q 0) w uFamily (q x))
    (fun x => normalizedCoefficient (q 0) w vFamily (q x))
    (fun x => normalizedCoefficient (q 0) w aFamily (q x))
    (fun x => normalizedCoefficient (q 0) w cFamily (q x))
    (fun i x => normalizedCoefficient (q 0) w (bFamily i) (q x))
    (fun j x => normalizedCoefficient (q 0) w (dFamily j) (q x))
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hrel
  funext j
  rcases j with _|⟨f,c⟩
  · exact hz
  · obtain ⟨x,hx⟩ := hq c.val
    have hc : q x≠q 0 := by simpa only [hx] using c.property
    rcases f with t | i | j
    · fin_cases t
      · simpa [normalizedCoefficient,hx,c.property,aFamily] using congrFun hA x
      · simpa [normalizedCoefficient,hx,c.property,cFamily] using congrFun hC x
      · simpa [normalizedCoefficient,hx,c.property,uFamily] using congrFun hU x
      · simpa [normalizedCoefficient,hx,c.property,vFamily] using congrFun hV x
    · simpa [normalizedCoefficient,hx,c.property,bFamily] using congrFun (congrFun hB i) x
    · simpa [normalizedCoefficient,hx,c.property,dFamily] using congrFun (congrFun hD j) x

theorem family_card : Fintype.card (Family k)=2*k+5 := by
  simp only [Family,Fintype.card_sum,Fintype.card_fin]
  omega

theorem reduced_card (c0 : C) :
    Fintype.card (Reduced k c0)=1+(2*k+5)*(Fintype.card C-1) := by
  have hc : Fintype.card {c : C // c≠c0}=Fintype.card C-1 := by
    simpa using Fintype.card_subtype_compl (fun c : C => c=c0)
  simp only [Reduced,Fintype.card_option,Fintype.card_prod,family_card,hc]
  omega

/-- Full rank lower bound for the original exponent matrix; the proof
uses an injective coefficient subspace rather than assuming a rank value. -/
theorem selected_rank_ge (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) :
    1+(2*k+5)*(Fintype.card C-1)≤(selectedMatrix (k := k) q).rank := by
  let M := (selectedMatrix (k := k) q).mulVecLin
  let R := M.comp (coefficientLift (q 0))
  have hR : Function.Injective R := lifted_relation_injective hk hm q hq
  have hr : R.range≤M.range := by
    rintro _ ⟨w,rfl⟩
    exact ⟨coefficientLift (q 0) w,rfl⟩
  calc
    1+(2*k+5)*(Fintype.card C-1)=Module.finrank ℚ (Reduced k (q 0) → ℚ) := by
      simp [reduced_card] <;> ring
    _=Module.finrank ℚ R.range := (LinearMap.finrank_range_of_inj hR).symm
    _≤Module.finrank ℚ M.range := Submodule.finrank_mono hr

end Sunlet.NetworkSunletExponents
end
end NetworkStageSource_Sunlet_NetworkSunletRank
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletRank"

section NetworkStageSource_Sunlet_NetworkSunletLowerBound


/-! The initial monomial rank is converted to the ordinary Krull dimension
of the literal sunlet coordinate algebra. -/

noncomputable section
open scoped BigOperators MonomialOrder

namespace Sunlet.NetworkSunletExponents

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] [Field K] {k : ℕ}

theorem weightHom_monomial (c0 : C) (d : Parameter k C →₀ ℕ) :
    weightHom (K := K) c0 (MvPolynomial.monomial d 1)=
      MvPolynomial.monomial (liftExponent c0 d) 1 := by
  change MvPolynomial.aeval (R := K)
    (fun j => MvPolynomial.monomial (liftedVariable c0 j) 1)
    (MvPolynomial.monomial d 1)=_
  rw [MvPolynomial.aeval_monomial,map_one,one_mul]
  rw [liftExponent,Finsupp.linearCombination_apply,
    MvPolynomial.monomial_finsupp_sum_index]
  simp only [map_one,one_mul,MvPolynomial.monomial_pow,one_pow]

theorem weightHom_coordinate (q : G → C) (f : Flow k G) :
    weightHom (K := K) (q 0) (coordinate q f)=
      MvPolynomial.monomial (liftExponent (q 0) (uExponent q f)) 1+
      MvPolynomial.monomial (liftExponent (q 0) (vExponent q f)) 1 := by
  rw [coordinate,map_add,weightHom_monomial,weightHom_monomial]

lemma lex_lt_of_bot {J : Type*} [Finite J] [LinearOrder J] {d e : WithBot J →₀ ℕ}
    (h : d ⊥ < e ⊥) : d ≺[MonomialOrder.lex] e := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  exact ⟨⊥, fun i hi => (not_lt_of_ge bot_le hi).elim, h⟩

theorem weighted_leading [LinearOrder (Parameter k C)]
    (q : G → C) (hzero : ∀ x,q x=q 0 ↔ x=0) (f : Flow k G) :
    MonomialOrder.lex.degree (weightHom (K := K) (q 0) (coordinate q f))=
        liftExponent (q 0) (selectedExponent q f) ∧
      MonomialOrder.lex.Monic (weightHom (K := K) (q 0) (coordinate q f)) := by
  classical
  let m : MonomialOrder (WithBot (Parameter k C)) := MonomialOrder.lex
  have hdeg (d : WithBot (Parameter k C) →₀ ℕ) :
      m.degree (MvPolynomial.monomial d (1 : K))=d := by
    simp only [m.degree_monomial,one_ne_zero,ite_false]
  have hw := strict_selected_weight q hzero f
  rw [weightHom_coordinate,selectedExponent]
  change m.degree _=_ ∧ m.Monic _
  by_cases hs : selectsU f
  · simp only [if_pos hs] at hw ⊢
    have hlt : m.degree (MvPolynomial.monomial (liftExponent (q 0) (vExponent q f)) (1 : K)) ≺[m]
        m.degree (MvPolynomial.monomial (liftExponent (q 0) (uExponent q f)) (1 : K)) := by
      simpa only [hdeg] using lex_lt_of_bot hw
    exact ⟨(m.degree_add_of_lt hlt).trans (hdeg _),
      m.monic_monomial_one.add_of_lt hlt⟩
  · simp only [if_neg hs] at hw ⊢
    have hlt : m.degree (MvPolynomial.monomial (liftExponent (q 0) (uExponent q f)) (1 : K)) ≺[m]
        m.degree (MvPolynomial.monomial (liftExponent (q 0) (vExponent q f)) (1 : K)) := by
      simpa only [hdeg] using lex_lt_of_bot hw
    refine ⟨(m.degree_add_eq_right_of_lt hlt).trans (hdeg _),?_⟩
    exact (congrArg m.Monic (add_comm
      (MvPolynomial.monomial (liftExponent (q 0) (uExponent q f)) (1 : K))
      (MvPolynomial.monomial (liftExponent (q 0) (vExponent q f)) (1 : K)))).mpr
        (m.monic_monomial_one.add_of_lt hlt)

def forgetWeight : (WithBot (Parameter k C) → ℚ) →ₗ[ℚ] (Parameter k C → ℚ) where
  toFun w j := w j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinate_subfamily_independent {I : Type*} [Fintype I]
    (q : G → C) (hzero : ∀ x,q x=q 0 ↔ x=0) (r : I → Flow k G)
    (hr : LinearIndependent ℚ (fun i j => (selectedExponent q (r i) j : ℚ))) :
    AlgebraicIndependent K (fun i => coordinate (K := K) q (r i)) := by
  classical
  letI : LinearOrder (Parameter k C) := LinearOrder.lift'
    (Fintype.equivFin (Parameter k C)) (Fintype.equivFin (Parameter k C)).injective
  let m : MonomialOrder (WithBot (Parameter k C)) := MonomialOrder.lex
  let f : I → MvPolynomial (Parameter k C) K := fun i => coordinate q (r i)
  let φ := weightHom (k := k) (K := K) (q 0)
  have hdeg (i : I) : m.degree (φ (f i))=liftExponent (q 0) (selectedExponent q (r i)) :=
    (weighted_leading q hzero (r i)).1
  have hn (i : I) : φ (f i)≠0 := (weighted_leading q hzero (r i)).2.ne_zero
  have hlin : LinearIndependent ℚ (fun i j => (m.degree (φ (f i)) j : ℚ)) := by
    apply LinearIndependent.of_comp (forgetWeight (k := k) (C := C))
    convert hr using 1
    funext i j
    simp only [Function.comp_apply,forgetWeight,LinearMap.coe_mk,AddHom.coe_mk,
      hdeg,liftExponent_coe]
  exact AlgebraicIndependent.of_comp φ
    (InitialIndependence.algebraicIndependent_of_rational_leading_exponents m
      (fun i => φ (f i)) hn hlin)

/-- Uniform lower bound for the actual coordinate-ring dimension. -/
theorem coordinate_dimension_ge (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) (hzero : ∀ x,q x=q 0 ↔ x=0) :
    (1+(2*k+5)*(Fintype.card C-1) : ℕ)≤
      ringKrullDim (MvPolynomial (Flow k G) K ⧸
        PolynomialImage.definingIdeal (coordinate (K := K) q)) := by
  classical
  let M := selectedMatrix (k := k) q
  obtain ⟨I,r,hrinj,hspan,hr⟩ := exists_linearIndependent' ℚ M.row
  letI : Fintype I := Fintype.ofInjective r hrinj
  have hcard : Fintype.card I=M.rank := by
    rw [M.rank_eq_finrank_span_row,← hspan]
    exact (finrank_span_eq_card hr).symm
  have halg : AlgebraicIndependent K (fun i => coordinate (K := K) q (r i)) :=
    coordinate_subfamily_independent q hzero r hr
  let A := PolynomialImage.imageAlgebra (coordinate (k := k) (K := K) q)
  let x : I → A := fun i => ⟨coordinate q (r i),by
    refine ⟨MvPolynomial.X (r i),?_⟩
    simp [PolynomialImage.comorphism]⟩
  have hx : AlgebraicIndependent K x := AlgebraicIndependent.of_comp A.val halg
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (PolynomialImage.comorphism (coordinate (K := K) q)).rangeRestrict
    (PolynomialImage.comorphism (coordinate (K := K) q)).rangeRestrict_surjective
  have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A x hx
  have hrank := selected_rank_ge hk hm q hq
  rw [ringKrullDim_eq_of_ringEquiv
    (PolynomialImage.coordinateRingEquivImage (coordinate (K := K) q)).toRingEquiv]
  rw [← hcard] at hrank
  calc
    _ ≤ (Fintype.card I : WithBot ℕ∞) := by exact_mod_cast hrank
    _ ≤ _ := hd

end Sunlet.NetworkSunletExponents
end
end NetworkStageSource_Sunlet_NetworkSunletLowerBound
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletLowerBound"

section NetworkStageSource_Sunlet_NetworkSunletNormalization


/-! Exact removal of the edge scalings and the zero-reticulation affine
redundancy. Equality of the substitution kernels preserves the entire model. -/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletExponents

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] [Field K] {k : ℕ}

abbrev OriginalRing (k : ℕ) (C K : Type*) [Field K] := MvPolynomial (Parameter k C) K
abbrev OriginalField (k : ℕ) (C K : Type*) [Field K] := FractionRing (OriginalRing k C K)
abbrev NormalizedRing (k : ℕ) (c0 : C) (K : Type*) [Field K] := MvPolynomial (Reduced k c0) K

def originalX (j : Parameter k C) : OriginalField k C K :=
  algebraMap (OriginalRing k C K) (OriginalField k C K) (MvPolynomial.X j)

theorem originalX_ne_zero (j : Parameter k C) : originalX (K := K) j≠0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := K) j
  exact IsFractionRing.injective (OriginalRing k C K) (OriginalField k C K) (by simpa [originalX] using h)

theorem originalX_def (j : Parameter k C) : originalX (K := K) j=
    algebraMap (OriginalRing k C K) (OriginalField k C K) (MvPolynomial.X j) := rfl

def gamma (c0 : C) : OriginalField k C K :=
  originalX (uFamily,c0)+originalX (vFamily,c0)

theorem gamma_ne_zero (c0 : C) : gamma (k := k) (K := K) c0≠0 := by
  intro h
  have hp : (MvPolynomial.X (uFamily,c0)+MvPolynomial.X (vFamily,c0) : OriginalRing k C K)=0 := by
    apply IsFractionRing.injective (OriginalRing k C K) (OriginalField k C K)
    simpa only [map_add,map_zero,originalX,gamma] using h
  have hh := congrArg (MvPolynomial.eval
    (fun j : Parameter k C => if j=(uFamily,c0) then (1 : K) else 0)) hp
  simpa [uFamily,vFamily] using hh

def scaleProduct (c0 : C) : OriginalField k C K :=
  gamma c0*originalX (aFamily,c0)*originalX (cFamily,c0)*
    (∏ i : Fin k,originalX (bFamily i,c0))*
    ∏ j : Fin (k+1),originalX (dFamily j,c0)

def normalizedValue (c0 : C) (f : Family k) (c : C) : NormalizedRing k c0 K :=
  if hc : c=c0 then (if f=vFamily then 0 else 1)
  else MvPolynomial.X (some (f,⟨c,hc⟩))

def specialize (c0 : C) : OriginalRing k C K →ₐ[K] NormalizedRing k c0 K :=
  MvPolynomial.aeval (R := K) fun j =>
    if j.1=aFamily then MvPolynomial.X none*normalizedValue c0 j.1 j.2
    else normalizedValue c0 j.1 j.2

def normalizedCoordinate (q : G → C) (f : Flow k G) : NormalizedRing k (q 0) K :=
  specialize (q 0) (coordinate q f)

def rescale (c0 : C) : NormalizedRing k c0 K →ₐ[K] OriginalField k C K :=
  MvPolynomial.aeval (R := K) fun j => match j with
  | none => scaleProduct c0
  | some (f,c) => if f=uFamily ∨ f=vFamily then originalX (f,c.val)/gamma c0
      else originalX (f,c.val)/originalX (f,c0)

theorem rescale_X_none (c0 : C) :
    rescale (k := k) (K := K) c0 (MvPolynomial.X none)=scaleProduct c0 := by
  simp [rescale]

theorem rescale_normalizedValue_nonretic (c0 : C) (f : Family k) (c : C)
    (hu : f≠uFamily) (hv : f≠vFamily) :
    rescale (K := K) c0 (normalizedValue c0 f c)=originalX (f,c)/originalX (f,c0) := by
  by_cases hc : c=c0
  · subst c
    simp [normalizedValue,hv,originalX_ne_zero]
  · simp [normalizedValue,hc,rescale,hu,hv]

theorem rescale_normalizedValue_u (c0 : C) (c : C) :
    rescale (K := K) c0 (normalizedValue c0 (uFamily : Family k) c)=
      if c=c0 then 1 else originalX (uFamily,c)/gamma c0 := by
  by_cases hc : c=c0 <;> simp [normalizedValue,hc,rescale,uFamily,vFamily]

theorem rescale_normalizedValue_v (c0 : C) (c : C) :
    rescale (K := K) c0 (normalizedValue c0 (vFamily : Family k) c)=
      if c=c0 then 0 else originalX (vFamily,c)/gamma c0 := by
  by_cases hc : c=c0 <;> simp [normalizedValue,hc,rescale,uFamily,vFamily]

theorem coordinate_product (q : G → C) (f : Flow k G) :
    coordinate (K := K) q f=
      MvPolynomial.X (aFamily,q (f.2 0-f.1))*
        (∏ i,MvPolynomial.X (bFamily i,q (f.2 i.succ-f.2 i.castSucc)))*
        MvPolynomial.X (cFamily,q (-f.2 (Fin.last k)))*
        (MvPolynomial.X (uFamily,q f.1)*(∏ j,MvPolynomial.X (dFamily j,q (f.2 j)))+
         MvPolynomial.X (vFamily,q f.1)*(∏ j,MvPolynomial.X (dFamily j,q (f.2 j-f.1)))) := by
  have hm (d e : Parameter k C →₀ ℕ) :
      MvPolynomial.monomial (d+e) (1 : K)=
        MvPolynomial.monomial d 1*MvPolynomial.monomial e 1 := by
    rw [MvPolynomial.monomial_mul,one_mul]
  simp only [coordinate,uExponent,vExponent,leafExponent,hm,
    MvPolynomial.monomial_sum_one,MvPolynomial.X]
  ring

theorem rescale_normalizedCoordinate (q : G → C)
    (hzero : ∀ x,q x=q 0 ↔ x=0) (f : Flow k G) :
    rescale (K := K) (q 0) (normalizedCoordinate q f)=
      algebraMap (OriginalRing k C K) (OriginalField k C K) (coordinate q f) := by
  have hA := originalX_ne_zero (K := K) (aFamily (k := k),q 0)
  have hC := originalX_ne_zero (K := K) (cFamily (k := k),q 0)
  have hB : (∏ i : Fin k,originalX (K := K) (bFamily i,q 0))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => originalX_ne_zero _)
  have hD : (∏ j : Fin (k+1),originalX (K := K) (dFamily j,q 0))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => originalX_ne_zero _)
  have hΓ := gamma_ne_zero (k := k) (K := K) (q 0)
  rw [normalizedCoordinate,coordinate_product]
  simp only [map_mul,map_add,map_prod]
  have hspA (c : C) : specialize (k := k) (K := K) (q 0)
      (MvPolynomial.X (aFamily,c))=MvPolynomial.X none*normalizedValue (q 0) aFamily c := by
    simp [specialize]
  have hsp (a : Family k) (c : C) (ha : a≠aFamily) :
      specialize (K := K) (q 0) (MvPolynomial.X (a,c))=normalizedValue (q 0) a c := by
    simp [specialize,ha]
  have hspB (i : Fin k) (c : C) := hsp (bFamily i) c (by simp [bFamily,aFamily])
  have hspD (j : Fin (k+1)) (c : C) := hsp (dFamily j) c (by simp [dFamily,aFamily])
  simp_rw [hspA,hspB,hspD]
  rw [hsp cFamily _ (by simp [aFamily,cFamily,uFamily,vFamily]),hsp uFamily _ (by simp [aFamily,cFamily,uFamily,vFamily]),hsp vFamily _ (by simp [aFamily,cFamily,uFamily,vFamily])]
  simp only [map_mul,map_add,map_prod,rescale_X_none]
  rw [rescale_normalizedValue_nonretic (k := k) (K := K) (q 0) aFamily _ (by simp [aFamily,cFamily,uFamily,vFamily]) (by simp [aFamily,cFamily,uFamily,vFamily]),
    rescale_normalizedValue_nonretic (k := k) (K := K) (q 0) cFamily _ (by simp [aFamily,cFamily,uFamily,vFamily]) (by simp [aFamily,cFamily,uFamily,vFamily]),
    rescale_normalizedValue_u (k := k) (K := K),
    rescale_normalizedValue_v (k := k) (K := K)]
  have hbNorm (i : Fin k) (c : C) :
      rescale (K := K) (q 0) (normalizedValue (q 0) (bFamily i) c)=
        originalX (bFamily i,c)/originalX (bFamily i,q 0) :=
    rescale_normalizedValue_nonretic (q 0) (bFamily i) c
      (by simp [bFamily,uFamily]) (by simp [bFamily,vFamily])
  have hdNorm (j : Fin (k+1)) (c : C) :
      rescale (K := K) (q 0) (normalizedValue (q 0) (dFamily j) c)=
        originalX (dFamily j,c)/originalX (dFamily j,q 0) :=
    rescale_normalizedValue_nonretic (q 0) (dFamily j) c
      (by simp [dFamily,uFamily]) (by simp [dFamily,vFamily])
  simp_rw [hbNorm,hdNorm]
  simp only [Finset.prod_div_distrib,← originalX_def]
  by_cases hx : f.1=0
  · simp only [hx,eq_self,ite_true,sub_zero,one_mul,zero_mul,add_zero,scaleProduct,gamma]
    field_simp [hA,hC,hB,hD]
    <;> ring
  · have hqx : q f.1≠q 0 := fun h => hx ((hzero _).mp h)
    simp only [hqx,if_false,scaleProduct]
    field_simp [hA,hC,hB,hD,hΓ]
    <;> ring

/-- The original and normalized polynomial maps have exactly the same
defining ideal. Both containments are proved by actual algebra maps. -/
theorem definingIdeal_eq_normalized (q : G → C)
    (hzero : ∀ x,q x=q 0 ↔ x=0) :
    PolynomialImage.definingIdeal (coordinate (k := k) (K := K) q)=
      PolynomialImage.definingIdeal (normalizedCoordinate (k := k) (K := K) q) := by
  let f := PolynomialImage.comorphism (coordinate (k := k) (K := K) q)
  let g := PolynomialImage.comorphism (normalizedCoordinate (k := k) (K := K) q)
  have hfg : (specialize (K := K) (q 0)).comp f=g := by
    ext x : 1
    simp only [AlgHom.comp_apply,f,g,PolynomialImage.comorphism,
      MvPolynomial.aeval_X,normalizedCoordinate]
  have hgf : (rescale (K := K) (q 0)).comp g=
      (IsScalarTower.toAlgHom K (OriginalRing k C K) (OriginalField k C K)).comp f := by
    ext x : 1
    simp only [AlgHom.comp_apply,f,g,PolynomialImage.comorphism,
      MvPolynomial.aeval_X,IsScalarTower.toAlgHom_apply]
    exact rescale_normalizedCoordinate (K := K) q hzero x
  ext p
  change f p=0 ↔ g p=0
  constructor
  · intro hp
    rw [← hfg]
    simp [hp]
  · intro hp
    apply IsFractionRing.injective (OriginalRing k C K) (OriginalField k C K)
    have hh := AlgHom.congr_fun hgf p
    simpa only [AlgHom.comp_apply,IsScalarTower.toAlgHom_apply,hp,map_zero] using hh.symm

theorem normalized_dimension_le (q : G → C) :
    ringKrullDim (MvPolynomial (Flow k G) K ⧸
      PolynomialImage.definingIdeal (normalizedCoordinate (K := K) q))≤
      (1+(2*k+5)*(Fintype.card C-1) : ℕ) := by
  let A := PolynomialImage.imageAlgebra (normalizedCoordinate (k := k) (K := K) q)
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (PolynomialImage.comorphism (normalizedCoordinate (k := k) (K := K) q)).rangeRestrict
    (PolynomialImage.comorphism (normalizedCoordinate (k := k) (K := K) q)).rangeRestrict_surjective
  rw [ringKrullDim_eq_of_ringEquiv
    (PolynomialImage.coordinateRingEquivImage (normalizedCoordinate (K := K) q)).toRingEquiv]
  change ringKrullDim A≤_
  rw [DimensionAlgebra.ringKrullDim_eq_trdeg_toNat K A]
  have hfinite : Algebra.trdeg K (NormalizedRing k (q 0) K)<Cardinal.aleph0 := by
    change Algebra.trdeg K (MvPolynomial (Reduced k (q 0)) K)<Cardinal.aleph0
    rw [MvPolynomial.trdeg_of_isDomain,Cardinal.lift_lt_aleph0]
    exact Cardinal.mk_lt_aleph0
  have hh := Cardinal.toNat_le_toNat
    (lift_trdeg_le_of_injective A.val Subtype.val_injective)
    (by simpa only [Cardinal.lift_lt_aleph0] using hfinite)
  have hn : (Algebra.trdeg K A).toNat≤1+(2*k+5)*(Fintype.card C-1) := by
    simpa only [NormalizedRing,MvPolynomial.trdeg_of_isDomain,Cardinal.toNat_lift,
      Cardinal.mk_fintype,Cardinal.toNat_natCast,reduced_card] using hh
  exact_mod_cast hn

/-- Exact dimension for every contracted sunlet of length k+3≥4,
for every finite abelian group and orbit partition allowed in the paper. -/
theorem coordinate_dimension (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) (hzero : ∀ x,q x=q 0 ↔ x=0) :
    ringKrullDim (MvPolynomial (Flow k G) K ⧸
      PolynomialImage.definingIdeal (coordinate (K := K) q))=
      (1+(2*k+5)*(Fintype.card C-1) : ℕ) := by
  apply le_antisymm
  · rw [definingIdeal_eq_normalized q hzero]
    exact normalized_dimension_le q
  · exact coordinate_dimension_ge hk hm q hq hzero

theorem imageClosure_dimension [Infinite K] (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) (hzero : ∀ x,q x=q 0 ↔ x=0) :
    ringKrullDim (MvPolynomial (Flow k G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (coordinate (K := K) q)))=
      (1+(2*k+5)*(Fintype.card C-1) : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  exact coordinate_dimension hk hm q hq hzero

end Sunlet.NetworkSunletExponents
end
end NetworkStageSource_Sunlet_NetworkSunletNormalization
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletNormalization"

section NetworkStageSource_Sunlet_NetworkSunletFlow


/-!
# Literal leaf flows and the uncontracted sunlet

The leaf set has three distinguished elements and k further elements. Its
zero-sum assignments are in explicit bijection with the path coordinates used
in the rank calculation. The extra reticulation leaf parameter is retained in
the uncontracted model; multiplying it into the two reticulation parameters and
specializing it to one prove equality of the two substitution kernels.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletExponents

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] [Field K] {k : ℕ}

abbrev Leaf (k : ℕ) := Fin 3 ⊕ Fin k
abbrev LeafFlow (k : ℕ) (G : Type*) [AddCommGroup G] :=
  {g : Leaf k → G // ∑ i,g i=0}

def leafValue (f : Flow k G) : Leaf k → G
  | .inl i => ![f.1,f.2 0-f.1,-f.2 (Fin.last k)] i
  | .inr i => f.2 i.succ-f.2 i.castSucc

lemma sum_path_differences (p : Fin (k+1) → G) :
    (∑ i : Fin k,(p i.succ-p i.castSucc))=p (Fin.last k)-p 0 := by
  have hh : p 0+∑ i : Fin k,p i.succ = (∑ i : Fin k,p i.castSucc)+p (Fin.last k) := by
    rw [← Fin.sum_univ_succ,← Fin.sum_univ_castSucc]
  rw [Finset.sum_sub_distrib]
  calc
    (∑ i : Fin k,p i.succ)-(∑ i : Fin k,p i.castSucc) =
        (p 0+∑ i : Fin k,p i.succ)-((∑ i : Fin k,p i.castSucc)+p 0) := by abel
    _ = ((∑ i : Fin k,p i.castSucc)+p (Fin.last k))-
        ((∑ i : Fin k,p i.castSucc)+p 0) := by rw [hh]
    _ = p (Fin.last k)-p 0 := by abel

lemma sum_leafValue (f : Flow k G) : ∑ i,leafValue f i=0 := by
  rw [Fintype.sum_sum_type,Fin.sum_univ_three]
  simp only [leafValue,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.cons_val_fin_one]
  rw [sum_path_differences]
  abel <;> simp [neg_one_zsmul,add_assoc,add_comm,add_left_comm]

def pathOfLeaf (g : LeafFlow k G) : Fin (k+1) → G :=
  fun j => g.val (.inl 0)+g.val (.inl 1)+Fin.partialSum (fun i => g.val (.inr i)) j

lemma pathOfLeaf_zero (g : LeafFlow k G) :
    pathOfLeaf g 0=g.val (.inl 0)+g.val (.inl 1) := by
  simp [pathOfLeaf]

lemma pathOfLeaf_difference (g : LeafFlow k G) (i : Fin k) :
    pathOfLeaf g i.succ-pathOfLeaf g i.castSucc=g.val (.inr i) := by
  simp only [pathOfLeaf,Fin.partialSum_succ]
  abel

lemma pathOfLeaf_last (g : LeafFlow k G) :
    pathOfLeaf g (Fin.last k)=-g.val (.inl 2) := by
  have hsum := g.property
  rw [Fintype.sum_sum_type,Fin.sum_univ_three] at hsum
  have hd := sum_path_differences (pathOfLeaf g)
  simp only [pathOfLeaf_difference,pathOfLeaf_zero] at hd
  calc
    pathOfLeaf g (Fin.last k) =
        (g.val (.inl 0)+g.val (.inl 1))+(∑ i : Fin k,g.val (.inr i)) := by
          rw [hd]
          abel
    _ = -g.val (.inl 2) := eq_neg_iff_add_eq_zero.mpr (by
      convert hsum using 1 <;> abel)

/-- A bijection with every zero-sum leaf assignment, not a subset of flows. -/
def leafFlowEquiv : Flow k G ≃ LeafFlow k G where
  toFun f := ⟨leafValue f,sum_leafValue f⟩
  invFun g := (g.val (.inl 0),pathOfLeaf g)
  left_inv f := by
    apply Prod.ext
    · rfl
    · funext j
      change f.1+(f.2 0-f.1)+Fin.partialSum
        (fun i => f.2 i.succ-f.2 i.castSucc) j=f.2 j
      have hh : ∀ j : Fin (k+1),
          f.2 0+Fin.partialSum (fun i => f.2 i.succ-f.2 i.castSucc) j=f.2 j := by
        intro j
        induction j using Fin.inductionOn with
        | zero => simp
        | succ i ih =>
          rw [Fin.partialSum_succ,← add_assoc,ih]
          abel
      calc
        _=f.2 0+Fin.partialSum (fun i => f.2 i.succ-f.2 i.castSucc) j := by abel
        _=f.2 j := hh j
  right_inv g := by
    apply Subtype.ext
    funext i
    rcases i with i|i
    · fin_cases i
      · rfl
      · simp [leafValue,pathOfLeaf_zero]
      · simp [leafValue,pathOfLeaf_last]
    · exact pathOfLeaf_difference g i

abbrev UncontractedParameter (k : ℕ) (C : Type*) := Option (Family k) × C

def edgeInclusion : Parameter k C → UncontractedParameter k C :=
  fun fc => (some fc.1,fc.2)

/-- The extra factor is the actual leaf edge incident with the reticulation;
all 2(k+3) edge families of the uncontracted sunlet are present. -/
def uncontractedCoordinate (q : G → C) (g : LeafFlow k G) :
    MvPolynomial (UncontractedParameter k C) K :=
  MvPolynomial.X (none,q (g.val (.inl 0))) *
    MvPolynomial.rename edgeInclusion (coordinate q (leafFlowEquiv.symm g))

def contractParameters :
    MvPolynomial (Parameter k C) K →ₐ[K]
      MvPolynomial (UncontractedParameter k C) K :=
  MvPolynomial.aeval (R := K) fun fc =>
    if fc.1=uFamily ∨ fc.1=vFamily then
      MvPolynomial.X (none,fc.2)*MvPolynomial.X (some fc.1,fc.2)
    else MvPolynomial.X (some fc.1,fc.2)

def forgetReticulationLeaf :
    MvPolynomial (UncontractedParameter k C) K →ₐ[K]
      MvPolynomial (Parameter k C) K :=
  MvPolynomial.aeval (R := K) fun fc => match fc.1 with
    | none => 1
    | some f => MvPolynomial.X (f,fc.2)

lemma forget_contract :
    (forgetReticulationLeaf (K := K) (k := k) (C := C)).comp contractParameters=
      AlgHom.id K _ := by
  ext fc
  rcases fc with ⟨f,c⟩
  by_cases h : f=uFamily ∨ f=vFamily <;>
    simp [contractParameters,forgetReticulationLeaf,h]

lemma contract_coordinate (q : G → C) (f : Flow k G) :
    contractParameters (coordinate (K := K) q f)=
      uncontractedCoordinate q (leafFlowEquiv f) := by
  rw [coordinate_product,uncontractedCoordinate,Equiv.symm_apply_apply]
  simp only [leafFlowEquiv,leafValue,Fin.isValue,Matrix.cons_val_zero]
  simp [contractParameters,coordinate_product,edgeInclusion,leafValue,MvPolynomial.rename_X,
    aFamily,bFamily,cFamily,dFamily,uFamily,vFamily,map_mul,map_add,map_prod,
    mul_add]
  <;> ring

/-- Eliminating the redundant reticulation edge preserves the complete ideal
of polynomial equations. -/
theorem uncontracted_kernel_eq (q : G → C) :
    RingHom.ker (MvPolynomial.aeval (R := K) (fun f : Flow k G =>
      uncontractedCoordinate (K := K) q (leafFlowEquiv f)))=
    RingHom.ker (MvPolynomial.aeval (R := K) (coordinate (K := K) q)) := by
  have hc : (MvPolynomial.aeval (R := K) (fun f : Flow k G =>
      uncontractedCoordinate (K := K) q (leafFlowEquiv f)))=
      contractParameters.comp (MvPolynomial.aeval (R := K) (coordinate (K := K) q)) := by
    ext f
    simp only [MvPolynomial.aeval_X,AlgHom.comp_apply,contract_coordinate]
  rw [hc]
  ext p
  simp only [RingHom.mem_ker,AlgHom.comp_apply]
  constructor
  · intro hp
    have hh := congrArg (forgetReticulationLeaf (K := K) (k := k) (C := C)) hp
    have hid := AlgHom.congr_fun (forget_contract (K := K) (k := k) (C := C))
      (MvPolynomial.aeval (R := K) (coordinate q) p)
    simpa only [AlgHom.comp_apply,AlgHom.id_apply,map_zero] using hid.symm.trans hh
  · intro hp
    rw [hp,map_zero]

end Sunlet.NetworkSunletExponents
end
end NetworkStageSource_Sunlet_NetworkSunletFlow
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletFlow"

section NetworkStageSource_Sunlet_NetworkLocalModels


/-!
# Literal incidence models for the terminal network blocks

The models below retain their vertices, edges, leaves and displayed-tree
choices. Conservation is solved explicitly, and the resulting polynomial
maps are identified with the local maps used in the dimension calculations.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkLocalModels

open NetworkIncidenceFlows

variable {G C K L : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C]

/-- The star whose leaves are indexed by `L`, with all edges directed from
the leaves to its central vertex. -/
def clawData (L : Type*) [Fintype L] : Data (Option L) L L PUnit where
  source := some
  target := fun _ => none
  leaf := some
  active := fun _ => Finset.univ

theorem claw_valid_iff (g : NetworkFlowGluing.Flow L G) (s : PUnit) (x : L → G) :
    Valid (clawData L) g.val s x ↔ x=g.val := by
  constructor
  · intro h
    funext l
    simpa [divergence,leafBoundary,clawData] using h.2 (some l)
  · rintro rfl
    constructor
    · simp [clawData]
    · intro v
      cases v with
      | none => simp [divergence,leafBoundary,clawData,g.property]
      | some l => simp [divergence,leafBoundary,clawData]

def clawTerm (g : NetworkFlowGluing.Flow L G) : Term (clawData L) g.val :=
  ⟨(PUnit.unit,g.val),(claw_valid_iff g _ _).mpr rfl⟩

theorem clawTerm_unique (g : NetworkFlowGluing.Flow L G) (t : Term (clawData L) g.val) :
    t=clawTerm g := by
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) ((claw_valid_iff g _ _).mp t.property)

def clawTermEquiv (g : NetworkFlowGluing.Flow L G) : Term (clawData L) g.val ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => clawTerm g
  left_inv t := (clawTerm_unique g t).symm
  right_inv _ := Subsingleton.elim _ _

theorem claw_terms_exist (g : NetworkFlowGluing.Flow L G) :
    Nonempty (Term (clawData L) g.val) := ⟨clawTerm g⟩

theorem claw_coordinate [CommSemiring K] (q : G → C)
    (g : NetworkFlowGluing.Flow L G) :
    NetworkIncidenceFlows.coordinate (K := K) (clawData L) q g=∏ l,MvPolynomial.X (l,q (g.val l)) := by
  rw [coordinate_eq_sum_terms]
  calc
    (∑ t : Term (clawData L) g.val,termPolynomial (clawData L) q t)=
        ∑ _ : PUnit.{1},termPolynomial (clawData L) q (clawTerm g) := by
      apply Fintype.sum_equiv (clawTermEquiv g)
      intro t
      rw [clawTerm_unique g t]
    _ = _ := by simp [termPolynomial_eq_prod,clawData,clawTerm]

/-- The ordinary three-leaf tree is identified with the actual pair/flow
coordinate calculation, including the zero-class parameters. -/
theorem claw_dimension [Field K] [CharZero K]
    (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Fin 3) G) K ⧸
      PolynomialImage.definingIdeal (NetworkIncidenceFlows.coordinate (K := K) (clawData (Fin 3)) q))=
        (3*Fintype.card C-2 : ℕ) := by
  have hmap : NetworkIncidenceFlows.coordinate (K := K) (clawData (Fin 3)) q=
      NetworkClaw.flowCoordinate (k := K) q := by
    funext g
    exact claw_coordinate q g
  rw [hmap,← PolynomialImage.vanishingIdeal_imageClosure]
  exact NetworkClaw.three_leaf_flow_dimension q hq

/-- One edge with its two endpoints as leaves. -/
def edgeData : Data (Fin 2) PUnit (Fin 2) PUnit where
  source := fun _ => 0
  target := fun _ => 1
  leaf := id
  active := fun _ => Finset.univ

theorem edge_flow_neg (g : NetworkFlowGluing.Flow (Fin 2) G) :
    -g.val 0=g.val 1 := by
  apply neg_eq_iff_add_eq_zero.mpr
  simpa [Fin.sum_univ_two] using g.property

theorem edge_valid_iff (g : NetworkFlowGluing.Flow (Fin 2) G)
    (s : PUnit) (x : PUnit → G) :
    Valid edgeData g.val s x ↔ x PUnit.unit=g.val 0 := by
  constructor
  · intro h
    simpa [divergence,leafBoundary,edgeData,Fin.sum_univ_two] using h.2 0
  · intro h
    constructor
    · simp [edgeData]
    · intro v
      fin_cases v
      · simpa [divergence,leafBoundary,edgeData,Fin.sum_univ_two] using h
      · simpa [divergence,leafBoundary,edgeData,Fin.sum_univ_two,h] using edge_flow_neg g

def edgeTerm (g : NetworkFlowGluing.Flow (Fin 2) G) : Term edgeData g.val :=
  ⟨(PUnit.unit,fun _ => g.val 0),(edge_valid_iff g _ _).mpr rfl⟩

theorem edgeTerm_unique (g : NetworkFlowGluing.Flow (Fin 2) G) (t : Term edgeData g.val) :
    t=edgeTerm g := by
  apply Subtype.ext
  apply Prod.ext (Subsingleton.elim _ _)
  funext e
  have he : e=PUnit.unit := Subsingleton.elim _ _
  simpa [he,edgeTerm] using (edge_valid_iff g _ _).mp t.property

def edgeTermEquiv (g : NetworkFlowGluing.Flow (Fin 2) G) : Term edgeData g.val ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => edgeTerm g
  left_inv t := (edgeTerm_unique g t).symm
  right_inv _ := Subsingleton.elim _ _

theorem edge_terms_exist (g : NetworkFlowGluing.Flow (Fin 2) G) :
    Nonempty (Term edgeData g.val) := ⟨edgeTerm g⟩

theorem edge_coordinate [CommSemiring K] (q : G → C)
    (g : NetworkFlowGluing.Flow (Fin 2) G) :
    NetworkIncidenceFlows.coordinate (K := K) edgeData q g=MvPolynomial.X (PUnit.unit,q (g.val 0)) := by
  rw [coordinate_eq_sum_terms]
  calc
    (∑ t : Term edgeData g.val,termPolynomial edgeData q t)=
        ∑ _ : PUnit.{1},termPolynomial edgeData q (edgeTerm g) := by
      apply Fintype.sum_equiv (edgeTermEquiv g)
      intro t
      rw [edgeTerm_unique g t]
    _ = _ := by simp [termPolynomial_eq_prod,edgeData,edgeTerm]

def edgeClass (q : G → C) (g : NetworkFlowGluing.Flow (Fin 2) G) : PUnit × C :=
  (PUnit.unit,q (g.val 0))

theorem edgeClass_surjective (q : G → C) (hq : Function.Surjective q) :
    Function.Surjective (edgeClass q) := by
  rintro ⟨u,c⟩
  obtain ⟨a,ha⟩ := hq c
  refine ⟨⟨![a,-a],by simp [Fin.sum_univ_two]⟩,?_⟩
  apply Prod.ext (Subsingleton.elim _ _)
  simpa [edgeClass] using ha

/-- The single-edge base case is the full affine space on all orbit
classes. It includes the two-leaf network allowed by the paper. -/
theorem edge_dimension [Field K] [CharZero K]
    (q : G → C) (hq : Function.Surjective q) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Fin 2) G) K ⧸
      PolynomialImage.definingIdeal (NetworkIncidenceFlows.coordinate (K := K) edgeData q))=
        (Fintype.card C : ℕ) := by
  have hmap : NetworkIncidenceFlows.coordinate (K := K) edgeData q=
      NetworkLeafEdge.coordinatePolynomial (K := K) (edgeClass q) := by
    funext g
    exact edge_coordinate q g
  rw [hmap]
  rw [ringKrullDim_eq_of_ringEquiv
    (NetworkLeafEdge.coordinateRingEquiv (K := K) (edgeClass q) (edgeClass_surjective q hq))]
  simp

end Sunlet.NetworkLocalModels
end
end NetworkStageSource_Sunlet_NetworkLocalModels
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkLocalModels"

section NetworkStageSource_Sunlet_NetworkSunletIncidence


/-!
# Solving conservation on every displayed tree of a sunlet

All `2(k+3)` edges of the uncontracted sunlet occur in this incidence
presentation. The two displayed-tree choices omit one of the two marked
cycle edges. Their conserved flows are solved explicitly; consequently
the literal graph Fourier sum is exactly the polynomial parametrization
used in the local dimension proof.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkSunletIncidence

open NetworkIncidenceFlows NetworkSunletExponents

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] {k : ℕ}

abbrev Vertex (k : ℕ) := Leaf k ⊕ Option (Fin (k+2))
abbrev Edge (k : ℕ) := Option (Family k)

def leafEdge : Leaf k → Edge k
  | .inl i => ![none,some aFamily,some cFamily] i
  | .inr i => some (bFamily i)

def source : Edge k → Vertex k
  | none => .inl (.inl 0)
  | some (.inl i) => ![.inl (.inl 1),.inl (.inl 2),.inr none,.inr none] i
  | some (.inr (.inl i)) => .inl (.inr i)
  | some (.inr (.inr j)) => .inr (some j.castSucc)

def target : Edge k → Vertex k
  | none => .inr none
  | some (.inl i) => ![.inr (some 0),.inr (some (Fin.last (k+1))),
      .inr (some 0),.inr (some (Fin.last (k+1)))] i
  | some (.inr (.inl i)) => .inr (some i.castSucc.succ)
  | some (.inr (.inr j)) => .inr (some j.succ)

def omitted (s : Bool) : Edge k := some (if s then uFamily else vFamily)

def data (k : ℕ) : Data (Vertex k) (Edge k) (Leaf k) Bool where
  source := source
  target := target
  leaf := Sum.inl
  active s := Finset.univ.filter (fun e => e≠omitted s)

theorem divergence_leaf (x : Edge k → G) (l : Leaf k) :
    divergence source target x (.inl l)=x (leafEdge l) := by
  rcases l with i|i
  · fin_cases i <;>
      simp [divergence,source,target,leafEdge,aFamily,cFamily,
        Fintype.sum_option,Fintype.sum_sum_type,Fin.sum_univ_succ]
  · simp [divergence,source,target,leafEdge,bFamily,
      Fintype.sum_option,Fintype.sum_sum_type,Fin.sum_univ_succ]

theorem divergence_reticulation (x : Edge k → G) :
    divergence source target x (.inr none)=
      x (some uFamily)+x (some vFamily)-x none := by
  simp [divergence,source,target,uFamily,vFamily,
    Fintype.sum_option,Fintype.sum_sum_type,Fin.sum_univ_succ]

theorem divergence_first (x : Edge k → G) :
    divergence source target x (.inr (some 0))=
      x (some (dFamily 0))-x (some aFamily)-x (some uFamily) := by
  simp [divergence,source,target,aFamily,uFamily,dFamily,
    Fintype.sum_option,Fintype.sum_sum_type,Fin.sum_univ_succ,
    Fin.castSucc_inj,Fin.castSucc_ne_last] <;> abel

theorem divergence_middle (x : Edge k → G) (i : Fin k) :
    divergence source target x (.inr (some i.castSucc.succ))=
      x (some (dFamily i.succ))-x (some (bFamily i))-
        x (some (dFamily i.castSucc)) := by
  have hs : (∑ e,if source e=Sum.inr (some i.castSucc.succ) then x e else 0)=
      x (some (dFamily i.succ)) := by
    simp [source,dFamily,Fintype.sum_option,Fintype.sum_sum_type,
      Fin.sum_univ_four,← Fin.castSucc_succ,Fin.castSucc_inj]
  have h0 : (0 : Fin (k+2))≠i.castSucc.succ := Ne.symm (Fin.succ_ne_zero _)
  have hlast : Fin.last (k+1)≠i.castSucc.succ := by
    rw [← Fin.castSucc_succ]
    exact Ne.symm (Fin.castSucc_ne_last _)
  have ht : (∑ e,if target e=Sum.inr (some i.castSucc.succ) then x e else 0)=
      x (some (bFamily i))+x (some (dFamily i.castSucc)) := by
    simp [target,bFamily,dFamily,Fintype.sum_option,Fintype.sum_sum_type,
      Fin.sum_univ_four,h0,hlast,Fin.succ_inj,Fin.castSucc_inj]
  rw [divergence,hs,ht]
  abel

theorem divergence_last (x : Edge k → G) :
    divergence source target x (.inr (some (Fin.last (k+1))))=
      -x (some cFamily)-x (some vFamily)-x (some (dFamily (Fin.last k))) := by
  simp [divergence,source,target,cFamily,vFamily,dFamily,
    Fintype.sum_option,Fintype.sum_sum_type,Fin.sum_univ_succ,
    Fin.castSucc_inj,Fin.castSucc_ne_last,← Fin.castSucc_succ] <;> abel

def edgeFlow (f : Flow k G) (s : Bool) : Edge k → G
  | none => f.1
  | some (.inl i) => ![f.2 0-f.1,-f.2 (Fin.last k),
      if s then 0 else f.1,if s then f.1 else 0] i
  | some (.inr (.inl i)) => f.2 i.succ-f.2 i.castSucc
  | some (.inr (.inr j)) => f.2 j-(if s then f.1 else 0)

theorem edgeFlow_leaf (f : Flow k G) (s : Bool) (l : Leaf k) :
    edgeFlow f s (leafEdge l)=leafValue f l := by
  rcases l with i|i
  · fin_cases i <;> rfl
  · rfl

theorem edgeFlow_valid (f : Flow k G) (s : Bool) :
    Valid (data k) (leafValue f) s (edgeFlow f s) := by
  constructor
  · intro e he
    have he' : e=omitted s := by simpa [data] using he
    subst e
    cases s <;> simp [omitted,edgeFlow,uFamily,vFamily]
  · intro v
    rcases v with l|v
    · rw [show (data k).source=source from rfl,
        show (data k).target=target from rfl,divergence_leaf,edgeFlow_leaf]
      simp [leafBoundary,data]
    · have hb : leafBoundary (data k).leaf (leafValue f) (.inr v)=0 := by
        simp [leafBoundary,data]
      rw [hb]
      change divergence source target (edgeFlow f s) (.inr v)=0
      cases v with
      | none =>
        rw [divergence_reticulation]
        cases s <;> simp [edgeFlow,uFamily,vFamily]
      | some j =>
        refine Fin.cases ?_ (fun i => ?_) j
        · rw [divergence_first]
          cases s <;> simp [edgeFlow,aFamily,uFamily,dFamily] <;> abel
        · refine Fin.lastCases ?_ (fun i => ?_) i
          · rw [Fin.succ_last,divergence_last]
            cases s <;> simp [edgeFlow,cFamily,vFamily,dFamily] <;> abel
          · rw [divergence_middle]
            cases s <;> simp [edgeFlow,bFamily,dFamily] <;> abel

theorem valid_edgeFlow_unique (f : Flow k G) (s : Bool) (x : Edge k → G)
    (h : Valid (data k) (leafValue f) s x) : x=edgeFlow f s := by
  have hl (l : Leaf k) : x (leafEdge l)=leafValue f l := by
    have hv := h.2 (.inl l)
    simpa [data,divergence_leaf,leafBoundary] using hv
  have ho : x (omitted s)=0 := h.1 _ (by simp [data])
  have hr : x (some uFamily)+x (some vFamily)=f.1 := by
    have hv := h.2 (.inr none)
    have hleaf := hl (.inl 0)
    simp only [leafEdge,leafValue,Fin.isValue,Matrix.cons_val_zero] at hleaf
    simpa [data,divergence_reticulation,leafBoundary,hleaf,sub_eq_zero] using hv
  have hu : x (some uFamily)=if s then 0 else f.1 := by
    cases s
    · simp only [omitted,Bool.false_eq_true,if_false] at ho
      simpa [ho] using hr
    · simpa [omitted] using ho
  have hv : x (some vFamily)=if s then f.1 else 0 := by
    cases s
    · simpa [omitted] using ho
    · simp only [omitted,if_true] at ho
      simpa [ho] using hr
  have hd : ∀ j : Fin (k+1),x (some (dFamily j))=f.2 j-(if s then f.1 else 0) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      have hf := h.2 (.inr (some 0))
      have ha := hl (.inl 1)
      change x (some aFamily)=f.2 0-f.1 at ha
      have heq : x (some (dFamily 0))-(f.2 0-f.1)-
          (if s then 0 else f.1)=0 := by
        simpa [data,divergence_first,leafBoundary,ha,hu] using hf
      cases s <;> simp only [Bool.false_eq_true,if_false,if_true] at heq ⊢ <;>
        apply sub_eq_zero.mp <;> convert heq using 1 <;> abel
    | succ i hi =>
      have hm := h.2 (.inr (some i.castSucc.succ))
      have hb := hl (.inr i)
      change x (some (bFamily i))=f.2 i.succ-f.2 i.castSucc at hb
      have heq : x (some (dFamily i.succ))-(f.2 i.succ-f.2 i.castSucc)-
          (f.2 i.castSucc-(if s then f.1 else 0))=0 := by
        simpa [data,divergence_middle,leafBoundary,leafEdge,leafValue,hi,hb] using hm
      apply sub_eq_zero.mp
      convert heq using 1 <;> abel
  funext e
  cases e with
  | none => simpa [leafEdge,leafValue,edgeFlow] using hl (.inl 0)
  | some e =>
    rcases e with i|i
    · fin_cases i
      · simpa [leafEdge,leafValue,edgeFlow,aFamily] using hl (.inl 1)
      · simpa [leafEdge,leafValue,edgeFlow,cFamily] using hl (.inl 2)
      · simpa [edgeFlow,uFamily] using hu
      · simpa [edgeFlow,vFamily] using hv
    · rcases i with i|j
      · simpa [leafEdge,leafValue,edgeFlow,bFamily] using hl (.inr i)
      · exact hd j

def canonicalTerm (f : Flow k G) (s : Bool) : Term (data k) (leafValue f) :=
  ⟨(s,edgeFlow f s),edgeFlow_valid f s⟩

theorem canonicalTerm_unique (f : Flow k G) (t : Term (data k) (leafValue f)) :
    t=canonicalTerm f t.val.1 := by
  apply Subtype.ext
  exact Prod.ext rfl (valid_edgeFlow_unique f _ _ t.property)

def termEquiv (f : Flow k G) : Term (data k) (leafValue f) ≃ Bool where
  toFun t := t.val.1
  invFun := canonicalTerm f
  left_inv t := (canonicalTerm_unique f t).symm
  right_inv _ := rfl

theorem terms_exist (g : LeafFlow k G) : Nonempty (Term (data k) g.val) := by
  have h := (leafFlowEquiv (k := k) (G := G)).apply_symm_apply g
  have ht : Nonempty (Term (data k) (leafFlowEquiv (leafFlowEquiv.symm g)).val) :=
    ⟨canonicalTerm (leafFlowEquiv.symm g) false⟩
  simpa only [h] using ht

theorem coordinate_eq_uncontracted [Field K] (q : G → C) (g : LeafFlow k G) :
    NetworkIncidenceFlows.coordinate (K := K) (data k) q g=uncontractedCoordinate q g := by
  obtain ⟨f,rfl⟩ := (leafFlowEquiv (k := k) (G := G)).surjective g
  rw [coordinate_eq_sum_terms,uncontractedCoordinate,Equiv.symm_apply_apply]
  calc
    (∑ t : Term (data k) (leafValue f),termPolynomial (data k) q t)=
        ∑ s : Bool,termPolynomial (data k) q (canonicalTerm f s) := by
      apply Fintype.sum_equiv (termEquiv f)
      intro t
      rw [canonicalTerm_unique f t]
      rfl
    _ = _ := by
      simp [termPolynomial_eq_prod,canonicalTerm,data,omitted,edgeFlow,
        uncontractedCoordinate,coordinate_product,edgeInclusion,leafFlowEquiv,leafValue,
        aFamily,cFamily,uFamily,vFamily,bFamily,dFamily,Finset.prod_filter,
        Fintype.prod_option,Fintype.prod_sum_type,Fin.prod_univ_succ,
        MvPolynomial.rename_X,map_mul,map_add,map_prod,
        mul_add]
      <;> ring

theorem uncontracted_dimension_eq [Field K] (q : G → C) :
    ringKrullDim (MvPolynomial (LeafFlow k G) K ⧸
      PolynomialImage.definingIdeal (uncontractedCoordinate (k := k) (K := K) q))=
      ringKrullDim (MvPolynomial (Flow k G) K ⧸
        PolynomialImage.definingIdeal (NetworkSunletExponents.coordinate (K := K) q)) := by
  have hr : Set.range (uncontractedCoordinate (k := k) (K := K) q)=
      Set.range (fun f : Flow k G =>uncontractedCoordinate (K := K) q (leafFlowEquiv f)) := by
    ext p
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨leafFlowEquiv.symm g,by simp⟩
    · rintro ⟨f,rfl⟩
      exact ⟨leafFlowEquiv f,rfl⟩
  change ringKrullDim (MvPolynomial (LeafFlow k G) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) (uncontractedCoordinate (k := k) (K := K) q)))=_
  rw [NetworkPolynomialGluing.dimension_eq_of_range (K := K) _ _ hr]
  change ringKrullDim (MvPolynomial (Flow k G) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) (fun f =>uncontractedCoordinate q (leafFlowEquiv f))))=_
  rw [uncontracted_kernel_eq]
  rfl

theorem uncontracted_dimension [Field K] [CharZero K]
    (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) (hzero : ∀ x,q x=q 0 ↔ x=0) :
    ringKrullDim (MvPolynomial (LeafFlow k G) K ⧸
      PolynomialImage.definingIdeal (uncontractedCoordinate (k := k) (K := K) q))=
        (1+(2*k+5)*(Fintype.card C-1) : ℕ) := by
  rw [uncontracted_dimension_eq]
  exact NetworkSunletExponents.coordinate_dimension hk hm q hq hzero

/-- The literal uncontracted incidence model of every sunlet with at
least four leaves has the full dimension used in Corollary8.1. -/
theorem sunlet_dimension [Field K] [CharZero K]
    (hk : 1≤k) (hm : 3≤Fintype.card G)
    (q : G → C) (hq : Function.Surjective q) (hzero : ∀ x,q x=q 0 ↔ x=0) :
    ringKrullDim (MvPolynomial (LeafFlow k G) K ⧸
      PolynomialImage.definingIdeal (NetworkIncidenceFlows.coordinate (K := K) (data k) q))=
        (1+(2*k+5)*(Fintype.card C-1) : ℕ) := by
  have heq : NetworkIncidenceFlows.coordinate (K := K) (data k) q=uncontractedCoordinate q :=
    funext (coordinate_eq_uncontracted q)
  rw [heq]
  exact uncontracted_dimension hk hm q hq hzero

end Sunlet.NetworkSunletIncidence
end
end NetworkStageSource_Sunlet_NetworkSunletIncidence
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkSunletIncidence"

section NetworkStageSource_Sunlet_NetworkTriangleIncidence


/-!
# The triangle block, including both orbit exceptions

The three-sunlet incidence map is matched to Theorem7.1 by an explicit
index bijection and an injective edge-parameter renaming. Negation acts
on the third leaf family through its actual permutation of orbit classes.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkTriangleIncidence

open NetworkSunletExponents

attribute [local instance] Classical.propDecidable

variable {G C K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C]

def pairFlowEquiv : G × G ≃ Flow 0 G where
  toFun ab := (ab.1,fun _ => ab.1+ab.2)
  invFun f := (f.1,f.2 0-f.1)
  left_inv ab := by
    dsimp only
    apply Prod.ext
    · rfl
    · dsimp
      abel
  right_inv f := by
    dsimp only
    apply Prod.ext
    · rfl
    · funext j
      have hj : j=0 := by apply Fin.ext; omega
      subst j
      dsimp
      abel

def parameterRename (neg : C ≃ C) : ParamVar C C → Parameter 0 C
  | .s c => (aFamily,c)
  | .t c => (cFamily,neg c)
  | .h c => (dFamily 0,c)
  | .u c => (uFamily,c)
  | .v c => (vFamily,c)

theorem parameterRename_injective (neg : C ≃ C) :
    Function.Injective (parameterRename neg) := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [parameterRename,aFamily,cFamily,dFamily,uFamily,vFamily,neg.injective.eq_iff]

theorem rename_coordinate [Field K] (q : G → C) (neg : C ≃ C)
    (hneg : ∀ a,q (-a)=neg (q a)) (ab : G × G) :
    MvPolynomial.rename (parameterRename neg) (Identified.coordinatePolynomial (K := K) q ab)=
      NetworkSunletExponents.coordinate (K := K) q (pairFlowEquiv ab) := by
  rw [coordinate_product]
  have hn : q (-ab.2 + -ab.1)=neg (q (ab.1+ab.2)) := by
    simpa only [neg_add_rev] using hneg (ab.1+ab.2)
  simp [Identified.coordinatePolynomial,parameterRename,pairFlowEquiv,hneg,hn,
    MvPolynomial.rename_X,Fin.prod_univ_succ]
  <;> ring

theorem kernel_coordinate [Field K] (q : G → C) (neg : C ≃ C)
    (hneg : ∀ a,q (-a)=neg (q a)) :
    RingHom.ker (MvPolynomial.aeval (R := K) (fun ab : G × G =>
      NetworkSunletExponents.coordinate (K := K) q (pairFlowEquiv ab)))=
        PolynomialImage.definingIdeal (Identified.coordinatePolynomial (K := K) q) := by
  have heq : (fun ab : G × G =>NetworkSunletExponents.coordinate (K := K) q (pairFlowEquiv ab))=
      fun ab =>MvPolynomial.rename (parameterRename neg) (Identified.coordinatePolynomial q ab) :=
    funext fun ab =>(rename_coordinate q neg hneg ab).symm
  rw [heq,NetworkPolynomialGluing.kernel_aeval_of_injective (K := K) _
    (MvPolynomial.rename_injective _ (parameterRename_injective neg))]
  rfl

theorem contracted_dimension [Field K] [IsAlgClosed K]
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (Flow 0 G) K ⧸
      PolynomialImage.definingIdeal (NetworkSunletExponents.coordinate (k := 0) (K := K) (OrbitClasses.classOf B)))=
      (if Fintype.card (OrbitClasses.Class B)=2 then (5 : ℕ)
        else if OrbitClasses.OrbitIndexTwoException B then 10
        else 5*Fintype.card (OrbitClasses.Class B)-4) := by
  classical
  let q := OrbitClasses.classOf B
  have hr : Set.range (NetworkSunletExponents.coordinate (k := 0) (K := K) q)=
      Set.range (fun ab : G × G =>NetworkSunletExponents.coordinate (K := K) q (pairFlowEquiv ab)) := by
    ext p
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨pairFlowEquiv.symm f,by simp⟩
    · rintro ⟨ab,rfl⟩
      exact ⟨pairFlowEquiv ab,rfl⟩
  change ringKrullDim (MvPolynomial (Flow 0 G) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K)
      (NetworkSunletExponents.coordinate (k := 0) (K := K) q))) = _
  rw [NetworkPolynomialGluing.dimension_eq_of_range (K := K) _ _ hr,
    kernel_coordinate q (OrbitClasses.negClass B) (fun a => (OrbitClasses.negClass_classOf B a).symm),
    ← PolynomialImage.vanishingIdeal_imageClosure]
  exact OrbitClasses.arbitrary_orbit_imageClosure_dimension B hm

def defect (B : AddSubgroup (AddAut G)) : ℕ := by
  classical
  exact if Fintype.card (OrbitClasses.Class B)=2 ∨ OrbitClasses.OrbitIndexTwoException B then 1 else 0

theorem defect_le_one (B : AddSubgroup (AddAut G)) : defect B≤1 := by
  classical
  unfold defect
  split_ifs <;> omega

/-- Exact literal incidence-model dimension for triangles, with the two
and only two deficits stated in the paper. -/
theorem triangle_dimension [Field K] [IsAlgClosed K]
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (LeafFlow 0 G) K ⧸
      PolynomialImage.definingIdeal (NetworkIncidenceFlows.coordinate (K := K)
        (NetworkSunletIncidence.data 0) (OrbitClasses.classOf B)))=
        (5*(Fintype.card (OrbitClasses.Class B)-1)+1-defect B : ℕ) := by
  classical
  have hmap : NetworkIncidenceFlows.coordinate (K := K) (NetworkSunletIncidence.data 0)
      (OrbitClasses.classOf B)=uncontractedCoordinate (OrbitClasses.classOf B) :=
    funext (NetworkSunletIncidence.coordinate_eq_uncontracted _)
  rw [hmap,NetworkSunletIncidence.uncontracted_dimension_eq,contracted_dimension B hm]
  letI : Nonempty (OrbitClasses.Class B) := ⟨OrbitClasses.classOf B 0⟩
  have hr : 1≤Fintype.card (OrbitClasses.Class B) := Fintype.card_pos
  by_cases htwo : Fintype.card (OrbitClasses.Class B)=2
  · simp [defect,htwo]
  · by_cases hex : OrbitClasses.OrbitIndexTwoException B
    · have hthree := OrbitClasses.orbit_index_two_exception_card B hm hex
      simp [defect,htwo,hex,hthree]
    · simp only [if_neg htwo,if_neg hex,defect,htwo,hex,or_self,if_false,Nat.sub_zero]
      have hdimNat : 5*Fintype.card (OrbitClasses.Class B)-4 =
          5*(Fintype.card (OrbitClasses.Class B)-1)+1 := by omega
      exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hdimNat

/-- A single formula for every local sunlet, including the triangle
exceptions. The number of edges is `2(k+3)` and there is exactly one cycle. -/
theorem sunlet_dimension [Field K] [IsAlgClosed K] [CharZero K]
    (k : ℕ) (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (LeafFlow k G) K ⧸
      PolynomialImage.definingIdeal (NetworkIncidenceFlows.coordinate (K := K)
        (NetworkSunletIncidence.data k) (OrbitClasses.classOf B)))=
        ((Fintype.card (OrbitClasses.Class B)-1)*(2*k+5)+1-
          defect B*(if k=0 then 1 else 0) : ℕ) := by
  classical
  by_cases hk : k=0
  · subst k
    simpa [Nat.mul_comm] using triangle_dimension (K := K) B hm
  · simpa [hk,Nat.mul_comm,Nat.add_comm] using
      NetworkSunletIncidence.sunlet_dimension (K := K) (by omega : 1≤k)
        (by omega : 3≤Fintype.card G) (OrbitClasses.classOf B)
        (OrbitClasses.classOf_surjective B) (OrbitClasses.zero_class_iff B)

end Sunlet.NetworkTriangleIncidence
end
end NetworkStageSource_Sunlet_NetworkTriangleIncidence
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkTriangleIncidence"

section NetworkStageSource_Sunlet_NetworkDimensionFormula


/-!
# The exact arithmetic in the network dimension induction

The graph-count bounds justify every natural-number subtraction in the
paper's formula. In particular the cut-edge recurrence is proved as an
identity of the actual nonnegative dimensions.
-/

noncomputable section

namespace Sunlet.NetworkDimensionFormula

open SimpleGraph NetworkGraphDecomposition

attribute [local instance] Classical.propDecidable

variable {V G : Type*} [Fintype V] [DecidableEq V] [AddCommGroup G] [Fintype G]

def expected (r δ E C T : ℕ) : ℕ := (r-1)*(E-C)+1-δ*T

theorem triangleCount_le_cycleCount (H : SimpleGraph V) : triangleCount H≤cycleCount H :=
  Nat.card_le_card_of_injective (fun c : {c : Cycle H //c.val.card=3} =>c.val) Subtype.val_injective

theorem cycleCount_le_edgeCount_sub (H : SimpleGraph V) (hH : IsBinaryCactus H) :
    cycleCount H≤edgeCount H-cycleCount H := by
  obtain ⟨he,hn⟩ := binaryCactus_counts H hH
  omega

theorem expected_add_defect (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (r δ : ℕ) (hr : 2≤r) (hδ : δ≤1) :
    expected r δ (edgeCount H) (cycleCount H) (triangleCount H)+δ*triangleCount H=
      (r-1)*(edgeCount H-cycleCount H)+1 := by
  have hδT : δ*triangleCount H≤triangleCount H := by
    simpa only [one_mul] using Nat.mul_le_mul_right (triangleCount H) hδ
  have hT := triangleCount_le_cycleCount H
  have hC := cycleCount_le_edgeCount_sub H hH
  have hprod : edgeCount H-cycleCount H≤(r-1)*(edgeCount H-cycleCount H) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (edgeCount H-cycleCount H)
      (by omega : 1≤r-1)
  exact Nat.sub_add_cancel (by
    exact le_trans (le_trans (le_trans hδT hT) hC) (Nat.le_succ_of_le hprod))

theorem expected_cut (H : SimpleGraph V) (hH : IsBinaryCactus H) (u v : V)
    (hadj : H.Adj u v) (hb : H.IsBridge s(u,v))
    (r δ : ℕ) (hr : 2≤r) (hδ : δ≤1) :
    expected r δ (edgeCount (cutGraph H u v)) (cycleCount (cutGraph H u v))
        (triangleCount (cutGraph H u v))+
      expected r δ (edgeCount (cutGraph H v u)) (cycleCount (cutGraph H v u))
        (triangleCount (cutGraph H v u))-r=
      expected r δ (edgeCount H) (cycleCount H) (triangleCount H) := by
  have hb' := NetworkGraphCut.swap_bridge H u v hb
  have hL := cutGraph_isBinaryCactus H hH u v hadj hb
  have hR := cutGraph_isBinaryCactus H hH v u hadj.symm hb'
  have hE := cut_edgeCounts H u v hH.connected hadj hb
  have hC := cut_cycleCounts H u v hH.connected hb
  have hT := cut_triangleCounts H u v hH.connected hb
  have hSL := cycleCount_le_edgeCount_sub (cutGraph H u v) hL
  have hSR := cycleCount_le_edgeCount_sub (cutGraph H v u) hR
  have hS := cycleCount_le_edgeCount_sub H hH
  have hsum : (edgeCount (cutGraph H u v)-cycleCount (cutGraph H u v))+
      (edgeCount (cutGraph H v u)-cycleCount (cutGraph H v u))=
        edgeCount H-cycleCount H+1 := by omega
  have hmul : (r-1)*(edgeCount (cutGraph H u v)-cycleCount (cutGraph H u v))+
      (r-1)*(edgeCount (cutGraph H v u)-cycleCount (cutGraph H v u))=
        (r-1)*(edgeCount H-cycleCount H)+(r-1) := by
    rw [← Nat.mul_add,hsum,Nat.mul_add,Nat.mul_one]
  have hδmul : δ*triangleCount (cutGraph H u v)+δ*triangleCount (cutGraph H v u)=
      δ*triangleCount H := by rw [← Nat.mul_add,hT]
  have hdL := expected_add_defect (cutGraph H u v) hL r δ hr hδ
  have hdR := expected_add_defect (cutGraph H v u) hR r δ hr hδ
  have hd := expected_add_defect H hH r δ hr hδ
  omega

theorem class_card_ge_two (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    2≤Fintype.card (OrbitClasses.Class B) := by
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (0 : G)
  have hq : OrbitClasses.classOf B a≠OrbitClasses.classOf B 0 :=
    fun h =>ha ((OrbitClasses.zero_class_iff B a).mp h)
  letI : Nontrivial (OrbitClasses.Class B) := ⟨⟨_,_,hq⟩⟩
  exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

theorem orbit_relabelling (B : AddSubgroup (AddAut G)) (x y : G)
    (h : OrbitClasses.classOf B x=OrbitClasses.classOf B y) :
    ∃ φ : G ≃+ G,(∀ z,OrbitClasses.classOf B (φ z)=OrbitClasses.classOf B z) ∧φ x=y := by
  obtain ⟨φ,hφ⟩ := (OrbitClasses.classOf_eq_iff B x y).mp h
  refine ⟨φ.val,?_,hφ⟩
  intro z
  symm
  exact (OrbitClasses.classOf_eq_iff B z (φ.val z)).mpr ⟨φ,rfl⟩

end Sunlet.NetworkDimensionFormula
end
end NetworkStageSource_Sunlet_NetworkDimensionFormula
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkDimensionFormula"

section NetworkStageSource_Sunlet_NetworkGraphLocalPresentation


/-!
# Identifying the actual terminal graphs with their incidence models

The graph-theoretic presentations are converted into bijections of all
vertices, edges, leaves and displayed-tree choices. Edge orientations
are chosen by the model and transported along the edge bijection. Thus
the resulting incidence isomorphisms concern the literal flow sums.
-/

noncomputable section

namespace Sunlet.NetworkGraphLocalPresentation

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkIncidenceFlows

section Transport

variable {V V₀ E₀ L₀ S₀ : Type*} [Fintype V] [DecidableEq V]
  [Fintype V₀] [Fintype E₀] [Fintype L₀] [Fintype S₀]
  [DecidableEq V₀] [DecidableEq E₀]
  (H : SimpleGraph V) (N : Data V₀ E₀ L₀ S₀)
  (vertices : V₀ ≃ V) (edges : E₀ ≃ H.edgeSet)

def orientationOfPresentation
    (he : ∀ e, s(vertices (N.source e), vertices (N.target e)) = (edges e).val) :
    Orientation H where
  source e := vertices (N.source (edges.symm e))
  target e := vertices (N.target (edges.symm e))
  edge_eq e := (he (edges.symm e)).trans (congrArg Subtype.val (edges.apply_symm_apply e))

def incidenceIsoOfPresentation (R : ReticulationData H)
    (leaves : L₀ ≃ Leaf H) (choices : S₀ ≃ Choice H)
    (he : ∀ e, s(vertices (N.source e), vertices (N.target e)) = (edges e).val)
    (hl : ∀ l, vertices (N.leaf l) = (leaves l).val)
    (ha : ∀ s e, e ∈ N.active s ↔ edges e ∈ activeEdges H R (choices s)) :
    NetworkIncidenceIso.Iso N
      (incidenceData H (orientationOfPresentation H N vertices edges he) R) where
  vertices := vertices
  edges := edges
  leaves := leaves
  choices := choices
  source e := by simp only [incidenceData, orientationOfPresentation, Equiv.symm_apply_apply]
  target e := by simp only [incidenceData, orientationOfPresentation, Equiv.symm_apply_apply]
  leaf := hl
  active := ha

end Transport

section Star

variable {V : Type*} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) {center : V} (P : StarPresentation H center)

def starEdgeEquiv : H.neighborSet center ≃ H.edgeSet := by
  refine Equiv.ofBijective (fun x => (⟨s(x.val, center), x.property.symm⟩ : H.edgeSet)) ⟨?_, ?_⟩
  · intro x y he
    have h := Sym2.eq_iff.mp (congrArg Subtype.val he)
    rcases h with ⟨hxy, _⟩ | ⟨hxc, hcy⟩
    · exact Subtype.ext hxy
    · exact (H.irrefl (hxc ▸ x.property)).elim
  · rintro ⟨e, he⟩
    revert he
    refine Sym2.ind ?_ e
    intro x y hxy
    rcases P.covers x with rfl | hx
    · refine ⟨⟨y, hxy⟩, Subtype.ext ?_⟩
      exact Sym2.eq_swap
    · have hy : y = center := leaf_neighbor_unique H (P.neighbors_are_leaves x hx) hxy hx.symm
      subst y
      exact ⟨⟨x, hx⟩, rfl⟩

def emptyCycleChoiceEquiv (hbin : IsBinary H) : PUnit ≃ Choice H := by
  have hzero := P.cycleCount_eq_zero hbin
  have hempty : IsEmpty (Cycle H) := ⟨fun c => by
    letI : Nonempty (Cycle H) := ⟨c⟩
    have hpos : 0 < Nat.card (Cycle H) := Nat.card_pos
    change Nat.card (Cycle H) = 0 at hzero
    omega⟩
  letI := hempty
  exact
    { toFun := fun _ c => isEmptyElim c
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => funext (fun c => isEmptyElim c) }

include P in
theorem activeEdges_star (hbin : IsBinary H) (R : ReticulationData H)
    (s : Choice H) (e : H.edgeSet) : e ∈ activeEdges H R s := by
  have hzero := P.cycleCount_eq_zero hbin
  simp only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c he
  letI : Nonempty (Cycle H) := ⟨c⟩
  have hpos : 0 < Nat.card (Cycle H) := Nat.card_pos
  change Nat.card (Cycle H) = 0 at hzero
  omega

def clawNeighborEquiv (hc : vertexDegree H center = 3) : Fin 3 ≃ H.neighborSet center := by
  classical
  exact (Fintype.equivFinOfCardEq
    (by simpa only [vertexDegree, Nat.card_eq_fintype_card] using hc)).symm

def clawVertices (hc : vertexDegree H center = 3) : Option (Fin 3) ≃ V :=
  (Equiv.optionCongr (clawNeighborEquiv H hc)).trans P.vertexEquiv

def clawEdges (hc : vertexDegree H center = 3) : Fin 3 ≃ H.edgeSet :=
  (clawNeighborEquiv H hc).trans (starEdgeEquiv H P)

def clawLeaves (hc : vertexDegree H center = 3) : Fin 3 ≃ Leaf H :=
  (clawNeighborEquiv H hc).trans (P.leafEquivNeighbor hc).symm

theorem claw_edge_endpoints (hc : vertexDegree H center = 3) (e : Fin 3) :
    s(clawVertices H P hc ((NetworkLocalModels.clawData.{0,0} (Fin 3)).source e),
      clawVertices H P hc ((NetworkLocalModels.clawData.{0,0} (Fin 3)).target e)) =
        (clawEdges H P hc e).val := rfl

def clawOrientation (hc : vertexDegree H center = 3) : Orientation H :=
  orientationOfPresentation H (NetworkLocalModels.clawData.{0,0} (Fin 3))
    (clawVertices H P hc) (clawEdges H P hc) (claw_edge_endpoints H P hc)

def clawIncidenceIso (hbin : IsBinary H) (hc : vertexDegree H center = 3)
    (R : ReticulationData H) :
    NetworkIncidenceIso.Iso (NetworkLocalModels.clawData.{0,0} (Fin 3))
      (incidenceData H (clawOrientation H P hc) R) :=
  incidenceIsoOfPresentation H (NetworkLocalModels.clawData.{0,0} (Fin 3))
    (clawVertices H P hc) (clawEdges H P hc) R (clawLeaves H P hc)
    (emptyCycleChoiceEquiv H P hbin) (claw_edge_endpoints H P hc) (fun _ => rfl)
    (by intro s e; exact iff_of_true (Finset.mem_univ _) (activeEdges_star H P hbin R _ _))

def edgeNeighbor (hc : vertexDegree H center = 1) : H.neighborSet center :=
  Classical.choice (Nat.card_ne_zero.mp (by change vertexDegree H center ≠ 0; omega)).1

theorem edgeNeighbor_unique (hc : vertexDegree H center = 1) (x : H.neighborSet center) :
    x = edgeNeighbor H hc :=
  (Nat.card_eq_one_iff_unique.mp hc).1.elim _ _

include P in
def edgeVertices (hc : vertexDegree H center = 1) : Fin 2 ≃ V := by
  refine Equiv.ofBijective (fun i => if i = 0 then center else (edgeNeighbor H hc).val) ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [↓reduceIte] at hij ⊢
    · exact ((edgeNeighbor H hc).property.ne hij).elim
    · exact ((edgeNeighbor H hc).property.ne hij.symm).elim
  · intro x
    rcases P.covers x with rfl | hx
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simpa only [if_neg h10] using
        congrArg Subtype.val (edgeNeighbor_unique H hc ⟨x, hx⟩).symm

def edgeEdges (hc : vertexDegree H center = 1) : PUnit ≃ H.edgeSet := by
  refine (Equiv.ofBijective (fun _ : PUnit => edgeNeighbor H hc) ⟨?_, ?_⟩).trans (starEdgeEquiv H P)
  · intro a b _
    exact Subsingleton.elim _ _
  · intro x
    exact ⟨PUnit.unit, (edgeNeighbor_unique H hc x).symm⟩

def edgeLeaves (hc : vertexDegree H center = 1) : Fin 2 ≃ Leaf H := by
  let e := edgeVertices H P hc
  have hall (x : V) : vertexDegree H x = 1 := by
    rcases P.covers x with rfl | hx
    · exact hc
    · exact P.neighbors_are_leaves x hx
  exact e.trans
    { toFun := fun x => ⟨x, hall x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem edge_edge_endpoints (hc : vertexDegree H center = 1) (e : PUnit) :
    s(edgeVertices H P hc (NetworkLocalModels.edgeData.{0,0}.source e),
      edgeVertices H P hc (NetworkLocalModels.edgeData.{0,0}.target e)) =
        (edgeEdges H P hc e).val := by
  change s(center, (edgeNeighbor H hc).val) = s((edgeNeighbor H hc).val, center)
  exact Sym2.eq_swap

def edgeOrientation (hc : vertexDegree H center = 1) : Orientation H :=
  orientationOfPresentation H NetworkLocalModels.edgeData.{0,0}
    (edgeVertices H P hc) (edgeEdges H P hc) (edge_edge_endpoints H P hc)

def edgeIncidenceIso (hbin : IsBinary H) (hc : vertexDegree H center = 1)
    (R : ReticulationData H) :
    NetworkIncidenceIso.Iso NetworkLocalModels.edgeData.{0,0}
      (incidenceData H (edgeOrientation H P hc) R) :=
  incidenceIsoOfPresentation H NetworkLocalModels.edgeData.{0,0}
    (edgeVertices H P hc) (edgeEdges H P hc) R (edgeLeaves H P hc)
    (emptyCycleChoiceEquiv H P hbin) (edge_edge_endpoints H P hc) (fun _ => rfl)
    (by intro s e; exact iff_of_true (Finset.mem_univ _) (activeEdges_star H P hbin R _ _))

include P in
theorem star_counts (hbin : IsBinary H) :
    edgeCount H = vertexDegree H center ∧ cycleCount H = 0 ∧ triangleCount H = 0 := by
  have hzero := P.cycleCount_eq_zero hbin
  have htri := P.triangleCount_eq_zero hbin
  have hedge : edgeCount H = vertexDegree H center :=
    (Nat.card_congr (starEdgeEquiv H P)).symm
  exact ⟨hedge, hzero, htri⟩

end Star

section StandardSunletIndices

open NetworkSunletExponents NetworkSunletIncidence

variable (k : ℕ)

def leafPosition : NetworkSunletExponents.Leaf k → Fin (k + 3)
  | Sum.inl i => ![0, 1, Fin.last (k + 2)] i
  | Sum.inr i => i.castSucc.succ.succ

theorem leafPosition_surjective : Function.Surjective (leafPosition k) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨Sum.inl 0, rfl⟩
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨Sum.inl 1, rfl⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · exact ⟨Sum.inl 2, by simp [leafPosition, Fin.succ_last]⟩
      · exact ⟨Sum.inr j, rfl⟩

def leafPositionEquiv : NetworkSunletExponents.Leaf k ≃ Fin (k + 3) :=
  Equiv.ofBijective (leafPosition k)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨leafPosition_surjective k, by simp only [NetworkSunletExponents.Leaf,
        Fintype.card_sum, Fintype.card_fin]; omega⟩)

def innerPositionEquiv : Option (Fin (k + 2)) ≃ Fin (k + 3) := (finSuccEquiv (k + 2)).symm

def edgeKind : NetworkSunletIncidence.Edge k →
    NetworkSunletExponents.Leaf k ⊕ Fin (k + 3)
  | none => Sum.inl (Sum.inl 0)
  | some (Sum.inl i) => ![Sum.inl (Sum.inl 1), Sum.inl (Sum.inl 2), Sum.inr 0, Sum.inr (-1)] i
  | some (Sum.inr (Sum.inl i)) => Sum.inl (Sum.inr i)
  | some (Sum.inr (Sum.inr j)) => Sum.inr j.castSucc.succ

theorem edgeKind_surjective : Function.Surjective (edgeKind k) := by
  rintro (l | i)
  · rcases l with i | i
    · fin_cases i
      · exact ⟨none, rfl⟩
      · exact ⟨some aFamily, rfl⟩
      · exact ⟨some cFamily, rfl⟩
    · exact ⟨some (bFamily i), rfl⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨some uFamily, rfl⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · refine ⟨some vFamily, ?_⟩
        apply congrArg Sum.inr
        apply Fin.ext
        simp only [Fin.coe_neg_one, Fin.val_succ, Fin.val_last]
      · exact ⟨some (dFamily j), rfl⟩

def edgeKindEquiv : NetworkSunletIncidence.Edge k ≃
    NetworkSunletExponents.Leaf k ⊕ Fin (k + 3) :=
  Equiv.ofBijective (edgeKind k)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨edgeKind_surjective k, by simp only [NetworkSunletIncidence.Edge,
        NetworkSunletExponents.Family, NetworkSunletExponents.Leaf,
        Fintype.card_option, Fintype.card_sum, Fintype.card_fin]; omega⟩)

theorem cycle_next_adj (i : Fin (k + 3)) :
    (SimpleGraph.cycleGraph (k + 3)).Adj i (i + 1) := by
  change i + 1 ∈ (SimpleGraph.cycleGraph (k + 3)).neighborSet i
  rw [SimpleGraph.cycleGraph_neighborSet]
  exact Or.inr rfl

def cycleEdge : Fin (k + 3) → (SimpleGraph.cycleGraph (k + 3)).edgeSet :=
  fun i => ⟨s(i, i + 1), cycle_next_adj k i⟩

theorem cycleEdge_injective : Function.Injective (cycleEdge k) := by
  intro i j he
  rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with ⟨hij, _⟩ | ⟨hi, hj⟩
  · exact hij
  · have htwo : (2 : Fin (k + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv
    have heq : j + 2 = j + 0 := by
      calc
        j + 2 = (j + 1) + 1 := by
          rw [add_assoc]
          apply congrArg (fun a : Fin (k+3) => j+a)
          apply Fin.ext
          change 2 % (k+3) = (1 % (k+3)+1 % (k+3)) % (k+3)
          simp [Nat.mod_eq_of_lt (by omega : 1 < k+3)]
        _ = i + 1 := congrArg (fun x => x + 1) hi.symm
        _ = j + 0 := by simpa only [add_zero] using hj
    exact (htwo (add_left_cancel heq)).elim

theorem cycleEdge_surjective : Function.Surjective (cycleEdge k) := by
  rintro ⟨e, he⟩
  revert he
  refine Sym2.ind ?_ e
  intro i j hij
  change j ∈ (SimpleGraph.cycleGraph (k + 3)).neighborSet i at hij
  rw [SimpleGraph.cycleGraph_neighborSet] at hij
  rcases hij with h | h
  · refine ⟨j, Subtype.ext ?_⟩
    have hj : j + 1 = i := by rw [h, sub_add_cancel]
    change s(j, j + 1) = s(i, j)
    rw [hj]
    exact Sym2.eq_swap
  · exact ⟨i, Subtype.ext (by change s(i, i + 1) = s(i, j); rw [h])⟩

def cycleEdgeEquiv : Fin (k + 3) ≃ (SimpleGraph.cycleGraph (k + 3)).edgeSet :=
  Equiv.ofBijective (cycleEdge k) ⟨cycleEdge_injective k, cycleEdge_surjective k⟩

theorem path_successor (j : Fin (k + 1)) :
    (j.castSucc.succ : Fin (k + 3)) + 1 = j.succ.succ := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_succ, Fin.val_castSucc, Fin.val_one]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem last_eq_neg_one : (Fin.last (k + 2) : Fin (k + 3)) = -1 := by
  apply Fin.ext
  simp only [Fin.val_last, Fin.coe_neg_one]

end StandardSunletIndices

section Sunlet

open NetworkSunletExponents NetworkSunletIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) {c : Cycle H} (P : SunletPresentation H c) (Q : CycleOrder H c)

def sunletAbstractEdge : (cycleVertices H c) ⊕ Fin (Q.extra + 3) → H.edgeSet
  | Sum.inl x => ⟨s(P.leaf x, x.val), (P.leaf_adj x).symm⟩
  | Sum.inr i => ⟨s((Q.vertex i).val, (Q.vertex (i + 1)).val),
      (P.cycle_adj_iff _ _).mpr ((Q.adj_iff _ _).mpr (cycle_next_adj Q.extra i))⟩

theorem sunletAbstractEdge_injective : Function.Injective (sunletAbstractEdge H P Q) := by
  rintro (x | i) (y | j) he
  · rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with ⟨_, hxy⟩ | ⟨hxy, _⟩
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exact (P.leaf_outside x (hxy.symm ▸ y.property)).elim
  · rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact (P.leaf_outside x (hx.symm ▸ (Q.vertex j).property)).elim
    · exact (P.leaf_outside x (hx.symm ▸ (Q.vertex (j + 1)).property)).elim
  · have h := he.symm
    rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨hy, _⟩ | ⟨hy, _⟩
    · exact (P.leaf_outside y (hy.symm ▸ (Q.vertex i).property)).elim
    · exact (P.leaf_outside y (hy.symm ▸ (Q.vertex (i + 1)).property)).elim
  · have hinj : Function.Injective (fun t => (Q.vertex t).val) :=
      Subtype.val_injective.comp Q.vertex.injective
    have hsym : s(i, i + 1) = s(j, j + 1) :=
      Sym2.map.injective hinj (congrArg Subtype.val he)
    exact congrArg Sum.inr (cycleEdge_injective Q.extra (Subtype.ext hsym))

theorem sunletAbstractEdge_surjective : Function.Surjective (sunletAbstractEdge H P Q) := by
  rintro ⟨e, he⟩
  revert he
  refine Sym2.ind ?_ e
  intro x y hxy
  rcases P.covers x with hx | ⟨x', rfl⟩ <;> rcases P.covers y with hy | ⟨y', rfl⟩
  · let i := Q.vertex.symm ⟨x, hx⟩
    let j := Q.vertex.symm ⟨y, hy⟩
    have hij : (SimpleGraph.cycleGraph (Q.extra + 3)).Adj i j := by
      apply (Q.adj_iff i j).mp
      simpa only [i, j, Equiv.apply_symm_apply] using (P.cycle_adj_iff ⟨x, hx⟩ ⟨y, hy⟩).mp hxy
    obtain ⟨a, ha⟩ := cycleEdge_surjective Q.extra ⟨s(i, j), hij⟩
    refine ⟨Sum.inr a, Subtype.ext ?_⟩
    have hmap := congrArg (fun e : (SimpleGraph.cycleGraph (Q.extra + 3)).edgeSet =>
      Sym2.map (fun t => (Q.vertex t).val) e.val) ha
    simpa only [sunletAbstractEdge,cycleEdge, Sym2.map_mk, i, j, Equiv.apply_symm_apply] using hmap
  · have hx' : (⟨x, hx⟩ : cycleVertices H c) = y' := (P.cycle_leaf_adj_iff _ _).mp hxy
    refine ⟨Sum.inl y', Subtype.ext ?_⟩
    change s(P.leaf y', y'.val) = s(x, P.leaf y')
    rw [← congrArg Subtype.val hx']
    exact Sym2.eq_swap
  · have hy' : (⟨y, hy⟩ : cycleVertices H c) = x' := (P.cycle_leaf_adj_iff _ _).mp hxy.symm
    refine ⟨Sum.inl x', Subtype.ext ?_⟩
    change s(P.leaf x', x'.val) = s(P.leaf x', y)
    rw [← congrArg Subtype.val hy']
  · exact (P.leaf_not_adj x' y' hxy).elim

def sunletAbstractEdgeEquiv : (cycleVertices H c) ⊕ Fin (Q.extra + 3) ≃ H.edgeSet :=
  Equiv.ofBijective (sunletAbstractEdge H P Q)
    ⟨sunletAbstractEdge_injective H P Q, sunletAbstractEdge_surjective H P Q⟩

def sunletVertices : NetworkSunletIncidence.Vertex Q.extra ≃ V :=
  ((Equiv.sumCongr ((leafPositionEquiv Q.extra).trans Q.vertex)
    ((innerPositionEquiv Q.extra).trans Q.vertex)).trans (Equiv.sumComm _ _)).trans P.vertexEquiv

def sunletEdges : NetworkSunletIncidence.Edge Q.extra ≃ H.edgeSet :=
  ((edgeKindEquiv Q.extra).trans
    (Equiv.sumCongr ((leafPositionEquiv Q.extra).trans Q.vertex) (Equiv.refl _))).trans
      (sunletAbstractEdgeEquiv H P Q)

def sunletLeaves (hbin : IsBinary H) :
    NetworkSunletExponents.Leaf Q.extra ≃ NetworkGraphDecomposition.Leaf H :=
  ((leafPositionEquiv Q.extra).trans Q.vertex).trans (P.leafEquivCycleVertices hbin).symm

@[simp] theorem sunletVertices_leaf (l : NetworkSunletExponents.Leaf Q.extra) :
    sunletVertices H P Q (Sum.inl l) = P.leaf (Q.vertex (leafPosition Q.extra l)) := rfl

@[simp] theorem sunletVertices_inner (v : Option (Fin (Q.extra + 2))) :
    sunletVertices H P Q (Sum.inr v) = (Q.vertex (innerPositionEquiv Q.extra v)).val := rfl

theorem sunlet_edge_endpoints (e : NetworkSunletIncidence.Edge Q.extra) :
    s(sunletVertices H P Q ((NetworkSunletIncidence.data Q.extra).source e),
      sunletVertices H P Q ((NetworkSunletIncidence.data Q.extra).target e)) =
        (sunletEdges H P Q e).val := by
  cases e with
  | none => rfl
  | some e =>
    rcases e with i | i
    · fin_cases i
      · rfl
      · rfl
      · change s((Q.vertex 0).val, (Q.vertex 1).val) =
          s((Q.vertex 0).val, (Q.vertex (0 + 1)).val)
        rw [zero_add]
      · change s((Q.vertex 0).val, (Q.vertex (Fin.last (Q.extra + 2))).val) =
          s((Q.vertex (-1)).val, (Q.vertex (-1 + 1)).val)
        rw [last_eq_neg_one, neg_add_cancel]
        exact Sym2.eq_swap
    · rcases i with i | j
      · rfl
      · change s((Q.vertex j.castSucc.succ).val, (Q.vertex j.succ.succ).val) =
          s((Q.vertex j.castSucc.succ).val, (Q.vertex (j.castSucc.succ + 1)).val)
        rw [path_successor]

def sunletOrientation : Orientation H :=
  orientationOfPresentation H (NetworkSunletIncidence.data Q.extra)
    (sunletVertices H P Q) (sunletEdges H P Q) (sunlet_edge_endpoints H P Q)

def sunletChoiceEquiv (hH : IsBinaryCactus H) : Bool ≃ Choice H where
  toFun s := fun _ => !s
  invFun s := !(s c)
  left_inv s := Bool.not_not s
  right_inv s := by
    funext d
    rw [P.cycle_eq hH d]
    exact Bool.not_not _

theorem sunlet_omitted (R : ReticulationData H)
    (hu : (R.incoming c false).val = s((Q.vertex 0).val, (Q.vertex 1).val))
    (hv : (R.incoming c true).val = s((Q.vertex 0).val, (Q.vertex (-1)).val))
    (s : Bool) :
    sunletEdges H P Q (NetworkSunletIncidence.omitted s) = R.incoming c (!s) := by
  apply Subtype.ext
  cases s
  · change s((Q.vertex (-1)).val, (Q.vertex (-1 + 1)).val) = (R.incoming c true).val
    rw [hv, neg_add_cancel]
    exact Sym2.eq_swap
  · change s((Q.vertex 0).val, (Q.vertex (0 + 1)).val) = (R.incoming c false).val
    rw [hu, zero_add]

def sunletIncidenceIso (hH : IsBinaryCactus H) (R : ReticulationData H)
    (hu : (R.incoming c false).val = s((Q.vertex 0).val, (Q.vertex 1).val))
    (hv : (R.incoming c true).val = s((Q.vertex 0).val, (Q.vertex (-1)).val)) :
    NetworkIncidenceIso.Iso (NetworkSunletIncidence.data Q.extra)
      (incidenceData H (sunletOrientation H P Q) R) := by
  refine incidenceIsoOfPresentation H (NetworkSunletIncidence.data Q.extra)
    (sunletVertices H P Q) (sunletEdges H P Q) R (sunletLeaves H P Q hH.binary)
    (sunletChoiceEquiv H P hH) (sunlet_edge_endpoints H P Q) (fun _ => rfl) ?_
  intro s e
  simp only [NetworkSunletIncidence.data, activeEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro he d hed
    rw [P.cycle_eq hH d] at hed
    change sunletEdges H P Q e = R.incoming c (!s) at hed
    rw [← sunlet_omitted H P Q R hu hv s] at hed
    exact he ((sunletEdges H P Q).injective hed)
  · intro he heq
    apply he c
    change sunletEdges H P Q e = R.incoming c (!s)
    rw [heq]
    exact sunlet_omitted H P Q R hu hv s

include P in
/-- Every genuine sunlet terminal block, with any adjacent marked
reticulation pair, is literally one of the incidence models used in the
all-orbit local dimension theorem. -/
theorem exists_sunletIncidenceIso (hH : IsBinaryCactus H) (R : ReticulationData H) :
    ∃ k : ℕ, ∃ O : Orientation H,
      Nonempty (NetworkIncidenceIso.Iso (NetworkSunletIncidence.data k) (incidenceData H O R)) := by
  obtain ⟨Q, hu, hv⟩ := exists_cycleOrder_marked H c
    (R.incoming c false).val (R.incoming c true).val
    (R.cycle_mem c false) (R.cycle_mem c true)
    (fun h => R.distinct c (Subtype.ext h)) (R.common_vertex c)
  exact ⟨Q.extra, sunletOrientation H P Q, ⟨sunletIncidenceIso H P Q hH R hu hv⟩⟩

include P in
theorem sunlet_counts (hH : IsBinaryCactus H) :
    edgeCount H = 2 * Q.extra + 6 ∧ cycleCount H = 1 ∧
      triangleCount H = (if Q.extra = 0 then 1 else 0) := by
  have hn : leafCount H = Q.extra + 3 := by
    rw [P.leafCount_eq hH.binary, Nat.card_eq_fintype_card, Fintype.card_coe,
      cycleVertices_card_eq]
    exact Q.length_eq.symm
  have hC := P.cycleCount_eq_one hH
  have he := (P.counts hH).1
  have hT := P.triangleCount_eq hH
  have hlength : c.val.card = 3 ↔ Q.extra = 0 := by have := Q.length_eq; omega
  simp only [hlength] at hT
  exact ⟨by omega, hC, hT⟩

include P in
theorem exists_sunletIncidenceIso_counts (hH : IsBinaryCactus H) (R : ReticulationData H) :
    ∃ k : ℕ, ∃ O : Orientation H,
      Nonempty (NetworkIncidenceIso.Iso (NetworkSunletIncidence.data k) (incidenceData H O R)) ∧
        edgeCount H = 2 * k + 6 ∧ cycleCount H = 1 ∧
          triangleCount H = (if k = 0 then 1 else 0) := by
  obtain ⟨Q, hu, hv⟩ := exists_cycleOrder_marked H c
    (R.incoming c false).val (R.incoming c true).val
    (R.cycle_mem c false) (R.cycle_mem c true)
    (fun h => R.distinct c (Subtype.ext h)) (R.common_vertex c)
  exact ⟨Q.extra, sunletOrientation H P Q, ⟨sunletIncidenceIso H P Q hH R hu hv⟩,
    sunlet_counts H P Q hH⟩

end Sunlet

end Sunlet.NetworkGraphLocalPresentation
end
end NetworkStageSource_Sunlet_NetworkGraphLocalPresentation
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphLocalPresentation"

section NetworkStageSource_Sunlet_NetworkTheorem


/-!
# Corollary8.1 for every decorated binary level-one graph

The induction predicate quantifies over all orientations and all actual
reticulation decorations. Its dimensions are those of the literal Fourier
polynomial maps, with no decomposition certificate or gluing law assumed.
-/

noncomputable section

namespace Sunlet.NetworkTheorem

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkGraphCut
open NetworkDimensionFormula NetworkGraphLocalPresentation

attribute [local instance] Classical.propDecidable

universe u

variable {G K : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Field K] [IsAlgClosed K] [CharZero K]

def Verified {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (B : AddSubgroup (AddAut G)) : Prop :=
  ∀ (O : Orientation H) (R : ReticulationData H),
    HasAllFlows (G := G) H O R ∧
      ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
        NetworkGraphModel.definingIdeal (K := K) H O R (OrbitClasses.classOf B))=
          (expected (Fintype.card (OrbitClasses.Class B)) (NetworkTriangleIncidence.defect B)
            (edgeCount H) (cycleCount H) (triangleCount H) : ℕ)

/-- Complete graph induction, simultaneously establishing nonvanishing
flow coordinates and the full dimension formula. -/
theorem verified {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) : Verified (K := K) H B := by
  classical
  let q := OrbitClasses.classOf B
  let r := Fintype.card (OrbitClasses.Class B)
  let δ := NetworkTriangleIncidence.defect B
  have hr : 2≤r := class_card_ge_two B hm
  have hδ : δ≤1 := NetworkTriangleIncidence.defect_le_one B
  let P : {W : Type u} → [Finite W] → [DecidableEq W] → SimpleGraph W → Prop :=
    fun {W} _ _ J => ∀ f : Fintype W,letI := f; Verified (K := K) J B
  have hP : P H := by
    apply binaryCactus_induction (P := P) ?_ ?_ ?_ H hH
    · intro W _ _ J hJ center Ps f
      letI := f
      intro O R
      obtain ⟨hE,hC,hT⟩ := star_counts J Ps hJ.binary
      rcases hJ.binary center with h1|h3
      · let I := edgeIncidenceIso J Ps hJ.binary h1 R
        have hf := I.terms_exist_transport (NetworkLocalModels.edge_terms_exist (G := G))
        refine ⟨NetworkGraphOrientation.terms_exist J (edgeOrientation J Ps h1) O R hf,?_⟩
        rw [NetworkGraphOrientation.definingIdeal_eq J (edgeOrientation J Ps h1) O R q
          (OrbitClasses.negClass B) (fun a => (OrbitClasses.negClass_classOf B a).symm)]
        have hd := (I.dimension_transport (k := K) q).symm.trans
          (NetworkLocalModels.edge_dimension (K := K) q (OrbitClasses.classOf_surjective B))
        have he : expected r δ (edgeCount J) (cycleCount J) (triangleCount J)=r := by
          simp only [expected,hE,h1,hC,hT,Nat.sub_zero,Nat.mul_zero,Nat.mul_one]
          omega
        rw [he]
        exact hd
      · let I := clawIncidenceIso J Ps hJ.binary h3 R
        have hf := I.terms_exist_transport (NetworkLocalModels.claw_terms_exist (G := G))
        refine ⟨NetworkGraphOrientation.terms_exist J (clawOrientation J Ps h3) O R hf,?_⟩
        rw [NetworkGraphOrientation.definingIdeal_eq J (clawOrientation J Ps h3) O R q
          (OrbitClasses.negClass B) (fun a => (OrbitClasses.negClass_classOf B a).symm)]
        have hd := (I.dimension_transport (k := K) q).symm.trans
          (NetworkLocalModels.claw_dimension (K := K) q (OrbitClasses.classOf_surjective B))
        have he : expected r δ (edgeCount J) (cycleCount J) (triangleCount J)=3*r-2 := by
          simp only [expected,hE,h3,hC,hT,Nat.sub_zero,Nat.mul_zero]
          omega
        rw [he]
        exact hd
    · intro W _ _ J hJ c Ps f
      letI := f
      intro O R
      obtain ⟨k,O₀,⟨I⟩,hE,hC,hT⟩ := exists_sunletIncidenceIso_counts J Ps hJ R
      have hf := I.terms_exist_transport (NetworkSunletIncidence.terms_exist (G := G))
      refine ⟨NetworkGraphOrientation.terms_exist J O₀ O R hf,?_⟩
      rw [NetworkGraphOrientation.definingIdeal_eq J O₀ O R q
        (OrbitClasses.negClass B) (fun a => (OrbitClasses.negClass_classOf B a).symm)]
      have hd := (I.dimension_transport (k := K) q).symm.trans
        (NetworkTriangleIncidence.sunlet_dimension (K := K) k B hm)
      simp only [expected,hE,hC,hT]
      rw [show 2*k+6-1=2*k+5 by omega]
      exact hd
    · intro W _ _ J hJ u v hbridge hL hR f
      letI := f
      intro O R
      obtain ⟨hadj,hb,hu,hv⟩ := hbridge
      have hleft := hL (inferInstance : Fintype (cutVertices J u v))
        (outOrientation J R u v hadj hb) (cutReticulation J R u v)
      have hright := hR (inferInstance : Fintype (cutVertices J v u))
        (inOrientation J R v u hadj.symm (swap_bridge J u v hb)) (cutReticulation J R v u)
      letI : Nonempty (OldLeafSide J u v) := oldLeafSide_nonempty J hJ u v hadj hb
      letI : Nonempty (OldLeafSide J v u) :=
        oldLeafSide_nonempty J hJ v u hadj.symm (swap_bridge J u v hb)
      refine ⟨hasAllFlows_cut J O R u v hJ.connected hadj hb hleft.1 hright.1,?_⟩
      have hd := dimension_cut (K := K) J O R u v hJ.connected hadj hb q
        (OrbitClasses.classOf_surjective B) (orbit_relabelling B)
        (OrbitClasses.negClass B) (fun a => (OrbitClasses.negClass_classOf B a).symm) hleft.1 hright.1
        (expected r δ (edgeCount (cutGraph J u v)) (cycleCount (cutGraph J u v))
          (triangleCount (cutGraph J u v)))
        (expected r δ (edgeCount (cutGraph J v u)) (cycleCount (cutGraph J v u))
          (triangleCount (cutGraph J v u))) hleft.2 hright.2
      rw [expected_cut J hJ u v hadj hb r δ hr hδ] at hd
      exact hd
  exact hP inferInstance

/-- Corollary8.1, formula (10): the full Fourier model for every finite
binary graph with vertex-disjoint cycles, all finite abelian groups of
order at least five, and every automorphism subgroup. -/
theorem paper_corollary_8_1 {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
      MvPolynomial.vanishingIdeal K
        (PolynomialImage.closure (NetworkGraphModel.coordinate (K := K) H O R
          (OrbitClasses.classOf B))))=
        ((Fintype.card (OrbitClasses.Class B)-1)*(edgeCount H-cycleCount H)+1-
          NetworkTriangleIncidence.defect B*triangleCount H : ℕ) := by
  rw [PolynomialImage.vanishingIdeal_imageClosure]
  exact (verified (K := K) H hH B hm O R).2

end Sunlet.NetworkTheorem
end
end NetworkStageSource_Sunlet_NetworkTheorem
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkTheorem"

section NetworkStageSource_Sunlet_NetworkClassRenaming


/-!
# Faithful renaming of classes and the unrestricted network formula

Injective relabelling of edge classes preserves the complete substitution
ideal. The trivial automorphism subgroup therefore gives exactly the
unrestricted group-labelled Fourier map, rather than only an equal count
of abstract parameter classes.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkClassRenaming

attribute [local instance] Classical.propDecidable

open NetworkIncidenceFlows NetworkGraphModel NetworkGraphDecomposition

variable {V E L S G C D K : Type*}
  [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]
  [DecidableEq C] [DecidableEq D] [CommSemiring K]

theorem rename_coordinate (N : Data V E L S) (q : G → C) (f : C → D)
    (g : NetworkFlowGluing.Flow L G) :
    MvPolynomial.rename (fun ec : E × C =>(ec.1,f ec.2)) (NetworkIncidenceFlows.coordinate (K := K) N q g)=
      NetworkIncidenceFlows.coordinate N (fun a =>f (q a)) g := by
  rw [coordinate_eq_sum_terms,coordinate_eq_sum_terms,map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [termPolynomial_eq_prod,termPolynomial_eq_prod,map_prod]
  apply Finset.prod_congr rfl
  intro e he
  simp

theorem kernel_coordinate (N : Data V E L S) (q : G → C) (f : C → D)
    (hf : Function.Injective f) :
    RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N (fun a =>f (q a))))=
      RingHom.ker (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q)) := by
  have h : MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N (fun a =>f (q a)))=
      (MvPolynomial.rename (fun ec : E × C =>(ec.1,f ec.2))).comp
        (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q)) := by
    ext g : 1
    simpa only [MvPolynomial.aeval_X,AlgHom.comp_apply] using (rename_coordinate N q f g).symm
  have hinj : Function.Injective (fun ec : E × C =>(ec.1,f ec.2)) := by
    rintro ⟨e,c⟩ ⟨e',c'⟩ h
    have he : e=e' := congrArg (fun z : E × D =>z.1) h
    have hc : f c=f c' := congrArg (fun z : E × D =>z.2) h
    exact Prod.ext he (hf hc)
  rw [h]
  ext p
  change MvPolynomial.rename (R := K) (fun ec : E × C =>(ec.1,f ec.2))
      (MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q) p)=0 ↔
    MvPolynomial.aeval (R := K) (NetworkIncidenceFlows.coordinate (K := K) N q) p=0
  constructor
  · intro hp
    apply MvPolynomial.rename_injective (R := K) _ hinj
    simpa only [map_zero] using hp
  · intro hp
    simp only [hp,map_zero]

theorem bottom_class_injective : Function.Injective (OrbitClasses.classOf (⊥ : AddSubgroup (AddAut G))) := by
  intro a b h
  obtain ⟨φ,hφ⟩ := (OrbitClasses.classOf_eq_iff ⊥ a b).mp h
  have hz : φ.val=0 := φ.property
  rw [hz] at hφ
  exact hφ

def bottomClassEquiv : G ≃ OrbitClasses.Class (⊥ : AddSubgroup (AddAut G)) :=
  Equiv.ofBijective (OrbitClasses.classOf ⊥)
    ⟨bottom_class_injective,OrbitClasses.classOf_surjective ⊥⟩

theorem bottom_class_card :
    Fintype.card (OrbitClasses.Class (⊥ : AddSubgroup (AddAut G)))=Fintype.card G :=
  (Fintype.card_congr (bottomClassEquiv (G := G))).symm

theorem bottom_defect (hm : 5≤Fintype.card G) :
    NetworkTriangleIncidence.defect (⊥ : AddSubgroup (AddAut G))=0 := by
  classical
  have htwo : Fintype.card (OrbitClasses.Class (⊥ : AddSubgroup (AddAut G)))≠2 := by
    rw [bottom_class_card]
    omega
  have hno : ¬OrbitClasses.OrbitIndexTwoException (⊥ : AddSubgroup (AddAut G)) := by
    intro h
    have hc := OrbitClasses.orbit_index_two_exception_card (⊥ : AddSubgroup (AddAut G)) hm h
    rw [bottom_class_card] at hc
    omega
  simp [NetworkTriangleIncidence.defect,htwo,hno]

theorem graph_bottom_kernel (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H) :
    NetworkGraphModel.definingIdeal (K := K) H O R
      (OrbitClasses.classOf (⊥ : AddSubgroup (AddAut G)))=
        NetworkGraphModel.definingIdeal (K := K) H O R (id : G → G) :=
  kernel_coordinate (incidenceData H O R) (id : G → G) (OrbitClasses.classOf ⊥)
    bottom_class_injective

end Sunlet.NetworkClassRenaming

namespace Sunlet.NetworkTheorem

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkClassRenaming

variable {V G K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Field K] [IsAlgClosed K] [CharZero K]

/-- The unrestricted conclusion of Corollary8.1, for the actual model with
group-labelled edge parameters and every zero-sum leaf assignment. -/
theorem paper_corollary_8_1_unrestricted (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
      MvPolynomial.vanishingIdeal K
        (PolynomialImage.closure (NetworkGraphModel.coordinate (K := K) H O R (id : G → G))))=
        ((Fintype.card G-1)*(2*leafCount H-3+2*cycleCount H)+1 : ℕ) := by
  classical
  have h := paper_corollary_8_1 (K := K) H hH O R (⊥ : AddSubgroup (AddAut G)) hm
  rw [PolynomialImage.vanishingIdeal_imageClosure] at h ⊢
  change ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
    NetworkGraphModel.definingIdeal (K := K) H O R
      (OrbitClasses.classOf (⊥ : AddSubgroup (AddAut G)))) = _ at h
  change ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
    NetworkGraphModel.definingIdeal (K := K) H O R (id : G → G))=_
  rw [graph_bottom_kernel,bottom_class_card,bottom_defect hm,Nat.zero_mul,Nat.sub_zero] at h
  have he := binaryCactus_edgeCount H hH
  have hsub : edgeCount H-cycleCount H=2*leafCount H-3+2*cycleCount H := by omega
  simpa only [hsub] using h

end Sunlet.NetworkTheorem
end
end NetworkStageSource_Sunlet_NetworkClassRenaming
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkClassRenaming"

section NetworkStageSource_Sunlet_NetworkDisplayedFlowCuts


/-!
# Corollary8.1 for the literal displayed-tree leaf-cut Fourier map

The polynomial identity with conserved flows is proved independently in
`NetworkLeafCutCoordinates`; this module applies the network dimension theorem.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkTheorem

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel NetworkDisplayedFlowCuts

attribute [local instance] Classical.propDecidable

variable {V G K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Field K] [IsAlgClosed K] [CharZero K]

/-- Formula (10) for the paper's leaf-cut Fourier map itself. The proof
therefore includes the complete equivalence with conserved edge flows. -/
theorem paper_corollary_8_1_leaf_cut (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
      MvPolynomial.vanishingIdeal K
        (PolynomialImage.closure (leafCutCoordinate (K := K) H O R
          (OrbitClasses.classOf B))))=
        ((Fintype.card (OrbitClasses.Class B)-1)*(edgeCount H-cycleCount H)+1-
          NetworkTriangleIncidence.defect B*triangleCount H : ℕ) := by
  rw [leafCutCoordinate_eq_coordinate H hH O R]
  exact paper_corollary_8_1 H hH O R B hm

/-- The unrestricted conclusion on the literal group-labelled leaf-cut
Fourier map, with the original graph's leaf and cycle counts. -/
theorem paper_corollary_8_1_unrestricted_leaf_cut
    (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K ⧸
      MvPolynomial.vanishingIdeal K
        (PolynomialImage.closure (leafCutCoordinate (K := K) H O R (id : G → G))))=
        ((Fintype.card G-1)*(2*leafCount H-3+2*cycleCount H)+1 : ℕ) := by
  rw [leafCutCoordinate_eq_coordinate H hH O R]
  exact paper_corollary_8_1_unrestricted H hH O R hm

end Sunlet.NetworkTheorem
end
end NetworkStageSource_Sunlet_NetworkDisplayedFlowCuts
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkDisplayedFlowCuts"

#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_leaf_cut
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut
#eval IO.println "NETWORK_STAGE_SOURCE_COMPLETE VerifiedNetworkConclusion"
