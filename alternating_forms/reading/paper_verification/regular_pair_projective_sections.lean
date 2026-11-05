module

public import PaperVerification.RegularPairLocalizationIntersection
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.Ring

/-!
# Genuine global sections from a degree-one regular pair

This file concerns the actual twisting sheaves on the actual projective
spectrum of a graded ring.  A cover by regular degree-one elements and a
regular pair among them imply that every global section is represented by
one homogeneous element of the original ring.  Equality of local fractions
is the existing localization equality for those sheaves; power divisibility
is the regular-pair theorem in the literal principal-ideal quotient.

The canonical maps are bijective in every nonnegative degree and preserve
the actual multiplication of twisting-sheaf sections.  Negative-degree
global sections vanish.  These statements do not replace sections by a new
algebraic definition and do not assume the desired section-ring comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.RegularPairProjectiveSections

open CategoryTheory AlgebraicGeometry
open PaperVerification.RegularPairLocalizationIntersection

universe u
variable {A : Type u} {σ I : Type*} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (x : I → A) (hx : ∀ i,x i∈𝒜 1) (hregular : ∀ i,IsRegular (x i))

include hx hregular

/-- Equality of the two restrictions gives literal cross multiplication,
because the overlap denominator is a regular element of the original ring. -/
theorem mul_eq_mul_of_restrict_eq {n : ℤ} {i j : I}
    {kᵢ kⱼ jᵢ jⱼ : ℕ}
    (hᵢ : (jᵢ : ℤ)=(kᵢ*1 : ℕ)+n) (hⱼ : (jⱼ : ℤ)=(kⱼ*1 : ℕ)+n)
    {rᵢ rⱼ : A} (hrᵢ : rᵢ∈𝒜 jᵢ) (hrⱼ : rⱼ∈𝒜 jⱼ)
    (hsᵢ : x i^kᵢ∈𝒜 (kᵢ*1)) (hsⱼ : x j^kⱼ∈𝒜 (kⱼ*1))
    (hUᵢ : Proj.basicOpen 𝒜 (x i)≤Proj.basicOpen 𝒜 (x i^kᵢ))
    (hUⱼ : Proj.basicOpen 𝒜 (x j)≤Proj.basicOpen 𝒜 (x j^kⱼ))
    (s : Γ(Proj.twistingSheaf 𝒜 n,⊤))
    (eᵢ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s=
      Proj.twistingSheaf.const hᵢ rᵢ _ hrᵢ hsᵢ _ hUᵢ)
    (eⱼ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s=
      Proj.twistingSheaf.const hⱼ rⱼ _ hrⱼ hsⱼ _ hUⱼ) :
    x j^kⱼ*rᵢ=x i^kᵢ*rⱼ := by
  have hle := (Proj.basicOpen_mul 𝒜 (x i) (x j)).le
  have e : (Proj.twistingSheaf 𝒜 n).presheaf.map
      (homOfLE (hle.trans inf_le_left)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)=
      (Proj.twistingSheaf 𝒜 n).presheaf.map
      (homOfLE (hle.trans inf_le_right)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) :=
    Proj.twistingSheaf.ext fun _ ↦ rfl
  rw [eᵢ,eⱼ,Proj.twistingSheaf.res_const,Proj.twistingSheaf.res_const,
    Proj.twistingSheaf.const_eq_const_iff
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 two_pos
        (SetLike.mul_mem_graded (hx i) (hx j)))] at e
  obtain ⟨N,hN⟩ := e
  exact sub_eq_zero.mp ((((hregular i).mul (hregular j)).pow N).left.mul_left_eq_zero_iff.mp hN)

variable (hcover : (⨆ i,Proj.basicOpen 𝒜 (x i))=⊤)
  (i j : I)
  (hpair : IsRegular (Ideal.Quotient.mk (Ideal.span ({x i} : Set A)) (x j)))

include hcover hpair

/-- Every actual global section has a denominator-one representation at
every point.  A single regular pair removes the denominator globally. -/
theorem exists_forall_apply_eq {n : ℤ} (s : Γ(Proj.twistingSheaf 𝒜 n,⊤)) :
    ∃ (k d : ℕ) (_ : (d : ℤ)=k+n) (q : A),
      x i^k*q∈𝒜 d ∧ ∀ y,s.1 y=Localization.mk q 1 := by
  choose k d h r hr H using fun l : I ↦
    Proj.twistingSheaf.exists_eq_const_basicOpen (hx l) one_pos
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)
  have hrel (l l' : I) : x l'^k l'*r l=x l^k l*r l' :=
    mul_eq_mul_of_restrict_eq 𝒜 x hx hregular
      (h l) (h l') (hr l) (hr l') _ _ _ _ s (H l) (H l')
  obtain ⟨q,hq⟩ :=
    (pow_dvd_pow_mul_iff (hregular i) hpair (k i) (k j) (r i)).mp
      ⟨r j,hrel i j⟩
  have hrq (l : I) : r l=x l^k l*q :=
    ((hregular i).pow (k i)).left (by
      beta_reduce
      rw [←hrel,hq]
      ring)
  refine ⟨k i,d i,by simpa using h i,q,hq ▸ hr i,fun y ↦ ?_⟩
  obtain ⟨l,hl⟩ : ∃ l,y.1∈Proj.basicOpen 𝒜 (x l) := by
    have hy : y.1∈⨆ l,Proj.basicOpen 𝒜 (x l) := by rw [hcover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have e := Proj.twistingSheaf.res_apply
    (homOfLE (le_top (a := Proj.basicOpen 𝒜 (x l)))) s ⟨y.1,hl⟩
  rw [H l] at e
  refine e.symm.trans ((Proj.twistingSheaf.const_apply ..).trans
    (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1,?_⟩)))
  simp [hrq l,mul_comm]

/-- All negative twists have zero actual global sections under the same
regular-pair hypotheses. -/
theorem twistingSheaf_top_eq_zero_of_neg {n : ℤ} (hn : n<0)
    (s : Γ(Proj.twistingSheaf 𝒜 n,⊤)) : s=0 := by
  obtain ⟨k,d,hd,q,hq,hs⟩ :=
    exists_forall_apply_eq 𝒜 x hx hregular hcover i j hpair s
  have hpow : x i^k∈𝒜 k := by
    simpa using SetLike.pow_mem_graded k (hx i)
  have hq0 : x i^k*q=0 := by
    rw [←DirectSum.decompose_of_mem_same 𝒜 hq,
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hpow (by omega)]
  apply Proj.twistingSheaf.ext
  intro y
  rw [hs,((hregular i).pow k).left.mul_left_eq_zero_iff.mp hq0,Localization.mk_zero]
  exact (Proj.twistingSheaf.zero_apply y).symm

/-- In every nonnegative degree the canonical original-element-to-section
map, for the actual twisting sheaf on Proj, is bijective. -/
theorem bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  have hpow (k : ℕ) : x i^k∈𝒜 k := by
    simpa using SetLike.pow_mem_graded k (hx i)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_,fun s ↦ ?_⟩
  · have e := congrArg ((Proj.twistingSheaf 𝒜 d).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (x i)))).op) hr
    rw [Proj.res_toTwistingSheaf,map_zero,Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff
        (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos (hx i))] at e
    obtain ⟨N,hN⟩ := e
    exact Subtype.ext (((hregular i).pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k,d',hd',q,hq,hs⟩ :=
      exists_forall_apply_eq 𝒜 x hx hregular hcover i j hpair s
    have hqd : q=DirectSum.decompose 𝒜 q d := by
      refine ((hregular i).pow k).left ?_
      beta_reduce
      rw [←DirectSum.decompose_of_mem_same 𝒜 hq,
        DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 (hpow k) (by omega),
        show d'-k=d by omega]
    refine ⟨⟨q,hqd ▸ (DirectSum.decompose 𝒜 q d).2⟩,
      Proj.twistingSheaf.ext fun y ↦ ?_⟩
    exact (Proj.toTwistingSheaf_apply_apply ..).trans (hs y).symm

/-- The component isomorphism is the canonical map r ↦ r/1, not a
noncanonical isomorphism obtained by counting dimensions. -/
def homogeneousGlobalSectionsEquiv (d : ℕ) :
    𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 d,⊤) :=
  AddEquiv.ofBijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)
    (bijective_toTwistingSheaf_top 𝒜 x hx hregular hcover i j hpair d)

@[simp] theorem homogeneousGlobalSectionsEquiv_apply (d : ℕ) (r : 𝒜 d) :
    homogeneousGlobalSectionsEquiv 𝒜 x hx hregular hcover i j hpair d r=
      Proj.toTwistingSheaf 𝒜 rfl ⊤ r := rfl

omit hx hregular hcover hpair in
/-- The component comparison respects the actual multiplication of
sections of the two twisting sheaves, in all pairs of degrees. -/
theorem toTwistingSheaf_top_mul (a b : ℕ) (r : 𝒜 a) (s : 𝒜 b) :
    Proj.twistingSheaf.mul 𝒜 ⊤ (a : ℤ) (b : ℤ)
      (Proj.toTwistingSheaf 𝒜 rfl ⊤ r)
      (Proj.toTwistingSheaf 𝒜 rfl ⊤ s)=
    Proj.toTwistingSheaf 𝒜 (by omega : ((a+b : ℕ) : ℤ)=(a : ℤ)+(b : ℤ)) ⊤
      ⟨r*s,SetLike.mul_mem_graded r.2 s.2⟩ :=
  Proj.mul_toTwistingSheaf (𝒜 := 𝒜) rfl rfl ⊤ r s

end PaperVerification.RegularPairProjectiveSections
