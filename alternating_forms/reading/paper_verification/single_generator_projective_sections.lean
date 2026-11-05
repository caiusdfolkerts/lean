module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Tactic.Ring

/-!
# Actual complete sections for a homogeneous one-generator ring

This is the projective-point boundary of the regular-pair argument.  If a
regular degree-one element covers Proj and every degree-d component is a
multiple of its d-th power by a degree-zero element, the canonical map to
actual global sections of O(d) is bijective for every d >= 0.  No vanishing
for negative twists is claimed: such a statement would be false for a point.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.SingleGeneratorProjectiveSections

open CategoryTheory AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (x : A) (hx : x∈𝒜 1) (hregular : IsRegular x)
  (hcover : Proj.basicOpen 𝒜 x=⊤)
  (hpieces : ∀ (d : ℕ) (r : A),r∈𝒜 d → ∃ c,c∈𝒜 0 ∧ r=c*x^d)

include hx hregular hcover hpieces

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-d section map is bijective, including degree zero. -/
theorem bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_,fun s ↦ ?_⟩
  · have e := congrArg ((Proj.twistingSheaf 𝒜 d).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 x))).op) hr
    rw [Proj.res_toTwistingSheaf,map_zero,Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff
        (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos hx)] at e
    obtain ⟨N,hN⟩ := e
    exact Subtype.ext ((hregular.pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k,j,hj,r,hr,H⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen hx one_pos
      ((Proj.twistingSheaf 𝒜 d).presheaf.map (homOfLE le_top).op s)
    obtain ⟨c,hc,hrc⟩ := hpieces j r hr
    have hj' : j=k+d := by omega
    let q := c*x^d
    have hq : q∈𝒜 d := by
      have hpow : x^d∈𝒜 d := by simpa using SetLike.pow_mem_graded d hx
      simpa only [zero_add] using SetLike.mul_mem_graded hc hpow
    have hrq : r=x^k*q := by
      rw [hrc,hj',pow_add]
      dsimp only [q]
      ring
    refine ⟨⟨q,hq⟩,Proj.twistingSheaf.ext fun y ↦ ?_⟩
    have hy : y.1∈Proj.basicOpen 𝒜 x := by rw [hcover]; trivial
    have e := Proj.twistingSheaf.res_apply
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 x))) s ⟨y.1,hy⟩
    rw [H] at e
    erw [Proj.twistingSheaf.const_apply] at e
    erw [Proj.toTwistingSheaf_apply_apply]
    refine Eq.trans ?_ e
    apply Localization.mk_eq_mk_iff.mpr
    apply Localization.r_iff_exists.mpr
    refine ⟨1, ?_⟩
    simp [hrq,mul_comm]

/-- The component equivalence is the original element divided by one. -/
def homogeneousGlobalSectionsEquiv (d : ℕ) :
    𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 d,⊤) :=
  AddEquiv.ofBijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)
    (bijective_toTwistingSheaf_top 𝒜 x hx hregular hcover hpieces d)

end PaperVerification.SingleGeneratorProjectiveSections
