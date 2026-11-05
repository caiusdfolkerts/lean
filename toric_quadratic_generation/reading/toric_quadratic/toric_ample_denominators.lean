module

public import PaperVerification.ToricCartierAmple
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

/-!
# Clearing denominators by powers of an actual Cartier section

The local calculation is the universal property of localization on an
affine principal open. Quasi-compactness supplies one exponent for the
whole scheme. This is the section-extension step needed to construct an
embedding from an ample sheaf; it does not assume a fan or an embedding.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X]

/-- A rational function regular on an affine principal open has a
denominator which is a power of its defining regular function. -/
theorem affine_regular_after_power
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) (a : Γ(X,U))
    (r : X.functionField)
    (hr : ∀ x∈X.basicOpen a,r∈regularAtSubring X x) :
    ∃ N : ℕ,∀ x∈U,
      r*(X.germToFunctionField U a)^N∈regularAtSubring X x := by
  by_cases ha : X.germToFunctionField U a=0
  · exact ⟨1,by intro x hx; simp only [ha,pow_one,mul_zero]; exact Subring.zero_mem _⟩
  have hη : genericPoint X∈U := genericPoint_mem_open X U
  have hηa : genericPoint X∈X.basicOpen a := by
    rw [X.mem_basicOpen a (genericPoint X) hη]
    change IsUnit (X.germToFunctionField U a)
    exact isUnit_iff_ne_zero.mpr ha
  letI : Nonempty (X.basicOpen a) := ⟨⟨genericPoint X,hηa⟩⟩
  obtain ⟨s,hs⟩ := exists_regularSection_of_stalkwise X (X.basicOpen a) r hr
  letI : IsLocalization.Away a Γ(X,X.basicOpen a) := hU.isLocalization_basicOpen a
  obtain ⟨N,t,ht⟩ := IsLocalization.Away.surj a s
  have halg (v : Γ(X,U)) :
      X.germToFunctionField (X.basicOpen a)
        (algebraMap Γ(X,U) Γ(X,X.basicOpen a) v) = X.germToFunctionField U v :=
    germToFunctionField_restrict X (homOfLE (X.basicOpen_le a)) v
  have hrt : r*(X.germToFunctionField U a)^N=X.germToFunctionField U t := by
    have he := congrArg (X.germToFunctionField (X.basicOpen a)) ht
    simpa only [map_mul,map_pow,halg,hs] using he
  refine ⟨N,?_⟩
  intro x hx
  rw [hrt]
  exact regular_germ_mem_regularAt X U t x hx

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def localCoefficientOn (i : C.index) (U : X.Opens) (hUi : U≤C.openSet i)
    (s : Γ(C.sheaf,⊤)) : Γ(X,U) :=
  X.presheaf.map (homOfLE hUi).op (C.localCoefficient i s)

theorem localCoefficientOn_value (i : C.index) (U : X.Opens) [Nonempty U]
    (hUi : U≤C.openSet i) (s : Γ(C.sheaf,⊤)) :
    X.germToFunctionField U (C.localCoefficientOn i U hUi s) =
      C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField) := by
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.choice (inferInstance : Nonempty U)).val,
      hUi (Classical.choice (inferInstance : Nonempty U)).property⟩⟩
  rw [localCoefficientOn,germToFunctionField_restrict,C.localCoefficient_value]

theorem localCoefficientOn_basicOpen (i : C.index) (U : X.Opens)
    (hUi : U≤C.openSet i) (s : Γ(C.sheaf,⊤)) :
    X.basicOpen (C.localCoefficientOn i U hUi s)=U⊓C.nonvanishingOpen s := by
  rw [localCoefficientOn,X.basicOpen_res]
  ext x
  constructor
  · rintro ⟨hx,hsa⟩
    exact ⟨hx,Opens.mem_iSup.mpr ⟨i,hsa⟩⟩
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    exact (X.mem_basicOpen (C.localCoefficient i s) x (hUi hx)).mpr
      ((C.mem_nonvanishingOpen_iff i s x (hUi hx)).mp hs)

/-- Quasi-compactness gives finitely many actual affine opens carrying
chosen frames of this Cartier sheaf. -/
theorem exists_finite_affine_frame_cover [CompactSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι→X.Opens) (i : ι→C.index),
      (∀ j,Nonempty (U j)) ∧ (∀ j,IsAffineOpen (U j)) ∧
      (∀ j,U j≤C.openSet (i j)) ∧ (⨆ j,U j)=⊤ := by
  classical
  have hlocal : ∀ x : X,∃ (i : C.index) (U : X.Opens),
      IsAffineOpen U ∧ x∈U ∧ U≤C.openSet i := by
    intro x
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨U,hU,hx,hUi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨i,U,hU,hx,hUi⟩
  choose i U hU hx hUi using hlocal
  have hcover : IsOpenCover U := by
    apply le_antisymm le_top
    intro x hxTop
    exact Opens.mem_iSup.mpr ⟨x,hx x⟩
  obtain ⟨t,ht⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨t,inferInstance,fun j=>U j.val,fun j=>i j.val,
    fun j=>⟨⟨j.val,hx j.val⟩⟩,fun j=>hU j.val,fun j=>hUi j.val,ht⟩

/-- Every rational function regular where `s` is nonvanishing extends
after multiplication by every sufficiently large power of `s`. The
conclusion is an actual global section of the actual Cartier power. -/
theorem eventually_section_extension [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) (r : X.functionField)
    (hr : ∀ x∈C.nonvanishingOpen s,r∈regularAtSubring X x) :
    ∃ N₀ : ℕ,0<N₀ ∧ ∀ N : ℕ,N₀≤N→
      ∃ t : Γ((C.pow N).sheaf,⊤),
        (C.pow N).toCartierData.sectionValue ⊤ t =
          r*(C.toCartierData.sectionValue ⊤ s)^N := by
  classical
  obtain ⟨ι,hι,U,i,hne,hU,hUi,hcover⟩ := C.exists_finite_affine_frame_cover
  letI : Fintype ι := hι
  letI (j : ι) : Nonempty (U j) := hne j
  let a (j : ι) := C.localCoefficientOn (i j) (U j) (hUi j) s
  have hloc (j : ι) : ∃ N : ℕ,∀ x∈U j,
      r*(X.germToFunctionField (U j) (a j))^N∈regularAtSubring X x := by
    apply affine_regular_after_power (U j) (hU j) (a j) r
    intro x hx
    have hsub : X.basicOpen (a j)≤C.nonvanishingOpen s := by
      rw [show a j=C.localCoefficientOn (i j) (U j) (hUi j) s from rfl,
        C.localCoefficientOn_basicOpen]
      exact inf_le_right
    exact hr x (hsub hx)
  choose N hN using hloc
  refine ⟨(∑ j,N j)+1,Nat.succ_pos _,?_⟩
  intro m hm
  let v := C.toCartierData.sectionValue ⊤ s
  have hNm (j : ι) : N j≤m :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_succ _).trans hm)
  have hregular (j : ι) (x : X) (hx : x∈U j) :
      r*(v/(C.generator (i j) : X.functionField))^m∈regularAtSubring X x := by
    have hold := hN j x hx
    rw [show a j=C.localCoefficientOn (i j) (U j) (hUi j) s from rfl,
      C.localCoefficientOn_value] at hold
    have hbase : v/(C.generator (i j) : X.functionField)∈regularAtSubring X x := by
      change rationalValue X ⊤ s.val / (C.generator (i j) : X.functionField) ∈
        regularAtSubring X x
      exact s.property (i j) ⟨x,trivial⟩ (hUi j hx)
    have hpow := (regularAtSubring X x).pow_mem hbase (m-N j)
    have he : r*(v/(C.generator (i j) : X.functionField))^m =
        (r*(v/(C.generator (i j) : X.functionField))^(N j))*
          (v/(C.generator (i j) : X.functionField))^(m-N j) := by
      rw [mul_assoc,← pow_add,Nat.add_sub_of_le (hNm j)]
    rw [he]
    exact (regularAtSubring X x).mul_mem hold hpow
  let raw : Γ(rationalFunctions X,⊤) := (rationalValue X ⊤).symm (r*v^m)
  have hrawvalue : rationalValue X ⊤ raw=r*v^m :=
    (rationalValue X ⊤).apply_symm_apply _
  have hraw : raw∈(C.pow m).presheafSubmodule.obj (op ⊤) := by
    intro l x hxl
    have hxcover : x.val∈⨆ j,U j := by rw [hcover]; trivial
    obtain ⟨j,hxj⟩ := Opens.mem_iSup.mp hxcover
    have hreg := hregular j x.val hxj
    have htrans := (regularAtSubring X x.val).pow_mem
      (C.transition (i j) l x.val (hUi j hxj) hxl) m
    have he : (r*(v/(C.generator (i j) : X.functionField))^m)*
        ((C.generator (i j) : X.functionField)/(C.generator l : X.functionField))^m =
          (r*v^m)/(C.generator l : X.functionField)^m := by
      rw [mul_assoc,← mul_pow,
        div_mul_div_cancel₀ (Units.ne_zero (C.generator (i j))),div_pow,mul_div_assoc]
    change rationalValue X ⊤ raw / (C.generator l : X.functionField)^m ∈
      regularAtSubring X x.val
    rw [hrawvalue]
    exact (congrArg (fun z : X.functionField => z∈regularAtSubring X x.val) he).mp
      ((regularAtSubring X x.val).mul_mem hreg htrans)
  refine ⟨⟨raw,hraw⟩,?_⟩
  change rationalValue X ⊤ raw=r*v^m
  exact (rationalValue X ⊤).apply_symm_apply _

theorem exists_section_extension [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) (r : X.functionField)
    (hr : ∀ x∈C.nonvanishingOpen s,r∈regularAtSubring X x) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      (C.pow N).toCartierData.sectionValue ⊤ t =
        r*(C.toCartierData.sectionValue ⊤ s)^N := by
  obtain ⟨N,hN,h⟩ := C.eventually_section_extension s r hr
  obtain ⟨t,ht⟩ := h N le_rfl
  exact ⟨N,hN,t,ht⟩

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.eventually_section_extension
