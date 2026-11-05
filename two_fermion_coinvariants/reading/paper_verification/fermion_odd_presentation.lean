module

public import PaperVerification.FermionDiagonalExterior
public import PaperVerification.FermionOddCurrentNormalization
public import PaperVerification.FermionTensorQuotient

/-!
# The genuine odd relation ideals over the local coefficient algebra

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

inductive LocalOddFamily
  | theta
  | xi
  | mixed
  deriving DecidableEq

instance : Fintype LocalOddFamily where
  elems := {.theta,.xi,.mixed}
  complete x := by cases x <;> simp

theorem span_family_killed_iff {C D τ : Type*} [Ring C] [Ring D]
    (gen : τ → C) (q : C →+* D) :
    (∀ x∈TwoSidedIdeal.span (Set.range gen),q x=0) ↔ ∀ i,q (gen i)=0 := by
  constructor
  · intro h i
    exact h _ (TwoSidedIdeal.subset_span ⟨i,rfl⟩)
  · intro h
    have hle : TwoSidedIdeal.span (Set.range gen)≤
        TwoSidedIdeal.ofRingCon (RingCon.ker q) := by
      apply TwoSidedIdeal.span_le.mpr
      rintro x ⟨i,rfl⟩
      change q (gen i)=q 0
      simpa only [map_zero] using h i
    intro x hx
    have he := hle hx
    change q x=q 0 at he
    simpa only [map_zero] using he

variable {A B ι κ : Type*} [CommRing A] [Ring B] [Algebra A B]
  [Fintype ι] [Fintype κ]

def separatedOddCurrent (node beta a b : ι → A) (family : LocalOddFamily) (k : ℕ) :
    ClusterExterior A ι :=
  match family with
  | .theta => ∑ i,node i^k • (b i • clusterTheta i)
  | .xi => ∑ i,node i^k • ((beta i*a i) • clusterXi i)
  | .mixed => ∑ i,node i^k • (clusterTheta i*clusterXi i)

def separatedOddIdeal (node beta a b : ι → A) : TwoSidedIdeal (ClusterExterior A ι) :=
  TwoSidedIdeal.span (Set.range (fun p : LocalOddFamily×ℕ ↦
    separatedOddCurrent node beta a b p.1 p.2))

abbrev SeparatedOddQuotient (node beta a b : ι → A) :=
  (separatedOddIdeal node beta a b).ringCon.Quotient

def clusterOddCurrent (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (family : LocalOddFamily) (c : κ) (k : ℕ) : ClusterExterior A ι :=
  match family with
  | .theta => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • (z i.1^v i.1 • clusterTheta i.1)
  | .xi => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • ((beta i.1*z i.1^u i.1) • clusterXi i.1)
  | .mixed => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • (clusterTheta i.1*clusterXi i.1)

def clusterOddIdeal (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    TwoSidedIdeal (ClusterExterior A ι) :=
  TwoSidedIdeal.span (Set.range (fun p : κ×(LocalOddFamily×ℕ) ↦
    clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2))

abbrev ClusterOddQuotient (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :=
  (clusterOddIdeal cluster z beta r u v).ringCon.Quotient

theorem separatedOddIdeal_killed_iff (node beta a b : ι → A)
    (q : ClusterExterior A ι →ₐ[A] B) :
    (∀ x∈separatedOddIdeal node beta a b,q x=0) ↔
      HasSeparatedOddCurrents node beta a b
        (fun i ↦ q (clusterTheta i)) (fun i ↦ q (clusterXi i))
        (fun i ↦ q (clusterTheta i)*q (clusterXi i)) := by
  change (∀ x∈TwoSidedIdeal.span (Set.range
    (fun p : LocalOddFamily×ℕ ↦ separatedOddCurrent node beta a b p.1 p.2)),
      q.toRingHom x=0) ↔ _
  rw [span_family_killed_iff]
  change (∀ p : LocalOddFamily×ℕ,q (separatedOddCurrent node beta a b p.1 p.2)=0) ↔ _
  constructor
  · intro h
    exact ⟨fun k ↦ by simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using h (.theta,k),
      fun k ↦ by simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using h (.xi,k),
      fun k ↦ by simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using h (.mixed,k)⟩
  · rintro ⟨ht,hx,hm⟩ ⟨family,k⟩
    cases family
    · simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using ht k
    · simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using hx k
    · simpa only [separatedOddCurrent,map_sum,map_smul,map_mul] using hm k

theorem clusterOddIdeal_killed_iff (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (q : ClusterExterior A ι →ₐ[A] B) :
    (∀ x∈clusterOddIdeal cluster z beta r u v,q x=0) ↔
      HasClusterOddCurrents cluster z beta r u v
        (fun i ↦ q (clusterTheta i)) (fun i ↦ q (clusterXi i))
        (fun i ↦ q (clusterTheta i)*q (clusterXi i)) := by
  change (∀ x∈TwoSidedIdeal.span (Set.range
    (fun p : κ×(LocalOddFamily×ℕ) ↦
      clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2)),q.toRingHom x=0) ↔ _
  rw [span_family_killed_iff]
  change (∀ p : κ×(LocalOddFamily×ℕ),
    q (clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2)=0) ↔ _
  constructor
  · intro h
    exact ⟨fun c k ↦ by simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using h (c,.theta,k),
      fun c k ↦ by simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using h (c,.xi,k),
      fun c k ↦ by simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using h (c,.mixed,k)⟩
  · rintro ⟨ht,hx,hm⟩ ⟨c,family,k⟩
    cases family
    · simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using ht c k
    · simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using hx c k
    · simpa only [clusterOddCurrent,map_sum,map_smul,map_mul] using hm c k

end PaperVerification.Fermion
