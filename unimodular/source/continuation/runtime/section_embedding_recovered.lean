module

public import Continuation.Divisor.FanoClosure
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual section morphisms and ample-power embeddings

Eleven complete recovered proof sections are retained, including denominator
clearing, finite affine generators, the genuine glued projective morphism,
and its actual chart-ring quotient proofs. Selection hashes and original
source identities are recorded in the accompanying manifest. No theorem is
replaced by an assumption, and no sections-to-projective-space dictionary
is taken on faith.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

section
-- BEGIN ToricAmpleDenominators



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
end
-- END ToricAmpleDenominators
end

section
-- BEGIN ToricAmpleCommonPower



/-! # A common positive power for a finite affine section cover -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- Flatten an arbitrary section of an iterated tensor power using the
literal equality of its local rational generators. -/
def flattenPowSection (a b : ℕ) (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    Γ((C.pow (a*b)).sheaf,⊤) := by
  refine ⟨t.val,?_⟩
  intro i x hx
  have ht : rationalValue X ⊤ t.val /
      ((C.generator i : X.functionField)^a)^b ∈ regularAtSubring X x.val :=
    t.property i x hx
  change rationalValue X ⊤ t.val / (C.generator i : X.functionField)^(a*b) ∈
    regularAtSubring X x.val
  simpa only [pow_mul] using ht

@[simp] theorem flattenPowSection_value (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.flattenPowSection a b t)=
      ((C.pow a).pow b).toCartierData.sectionValue ⊤ t := rfl

theorem flattenPowSection_localCoefficient (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) (i : C.index) :
    (C.pow (a*b)).localCoefficient i (C.flattenPowSection a b t)=
      ((C.pow a).pow b).localCoefficient i t := by
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow (a*b)).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    letI : Nonempty (((C.pow a).pow b).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.flattenPowSection a b t) /
          (C.generator i : X.functionField)^(a*b) :=
        (C.pow (a*b)).localCoefficient_value i (C.flattenPowSection a b t)
      _ = ((C.pow a).pow b).toCartierData.sectionValue ⊤ t /
          ((C.generator i : X.functionField)^a)^b := by
        rw [C.flattenPowSection_value,pow_mul]
      _ = _ := (((C.pow a).pow b).localCoefficient_value i t).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

theorem nonvanishingOpen_flattenPowSection (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    (C.pow (a*b)).nonvanishingOpen (C.flattenPowSection a b t)=
      ((C.pow a).pow b).nonvanishingOpen t := by
  change (⨆ i : C.index,X.basicOpen ((C.pow (a*b)).localCoefficient i
      (C.flattenPowSection a b t))) =
    ⨆ i : C.index,X.basicOpen (((C.pow a).pow b).localCoefficient i t)
  apply iSup_congr
  intro i
  exact congrArg (fun r : Γ(X,C.openSet i) => X.basicOpen r)
    (C.flattenPowSection_localCoefficient a b t i)

/-- The actual power of a section, with nested Cartier powers identified
by their equal local rational generators. -/
def powerSection (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤)) :
    Γ((C.pow (a*b)).sheaf,⊤) :=
  C.flattenPowSection a b ((C.pow a).sectionPow b s)

@[simp] theorem powerSection_value (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.powerSection a b s) =
      ((C.pow a).toCartierData.sectionValue ⊤ s)^b :=
  (C.flattenPowSection_value a b ((C.pow a).sectionPow b s)).trans
    ((C.pow a).sectionPow_value b s)

theorem powerSection_localCoefficient (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤))
    (i : C.index) :
    (C.pow (a*b)).localCoefficient i (C.powerSection a b s) =
      ((C.pow a).localCoefficient i s)^b :=
  (C.flattenPowSection_localCoefficient a b ((C.pow a).sectionPow b s) i).trans
    ((C.pow a).localCoefficient_sectionPow b i s)

theorem nonvanishingOpen_powerSection (a b : ℕ) (hb : 0<b)
    (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow (a*b)).nonvanishingOpen (C.powerSection a b s)=
      (C.pow a).nonvanishingOpen s := by
  calc
    _ = ((C.pow a).pow b).nonvanishingOpen ((C.pow a).sectionPow b s) :=
      C.nonvanishingOpen_flattenPowSection a b ((C.pow a).sectionPow b s)
    _ = _ := (C.pow a).nonvanishingOpen_sectionPow b hb s

def powerSectionTo (a b N : ℕ) (h : a*b=N)
    (s : Γ((C.pow a).sheaf,⊤)) : Γ((C.pow N).sheaf,⊤) :=
  h ▸ C.powerSection a b s

theorem nonvanishingOpen_powerSectionTo (a b N : ℕ) (h : a*b=N) (hb : 0<b)
    (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow N).nonvanishingOpen (C.powerSectionTo a b N h s)=
      (C.pow a).nonvanishingOpen s := by
  subst N
  exact C.nonvanishingOpen_powerSection a b hb s

/-- One positive tensor power has finitely many actual sections whose
nonvanishing opens retain the affine cover supplied by ampleness. -/
theorem IsAmple.exists_common_power_affine_cover (hC : C.IsAmple) :
    ∃ (N : ℕ),0<N ∧ ∃ (ι : Type u) (_ : Fintype ι)
      (s : ι→Γ((C.pow N).sheaf,⊤)),
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow N).nonvanishingOpen (s i))=⊤ := by
  obtain ⟨ι,hι,n,s,hn,ha,hcover⟩ := hC.exists_finite_cover
  letI : Fintype ι := hι
  let N := ∏ i,n i
  have hN : 0<N := Finset.prod_pos (fun i _=>hn i)
  have hmultiple (i : ι) : ∃ b : ℕ,0<b ∧ n i*b=N := by
    have hdvd : n i∣N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    obtain ⟨b,hb⟩ := hdvd
    refine ⟨b,?_,hb.symm⟩
    rw [hb] at hN
    exact (mul_pos_iff_of_pos_left (hn i)).mp hN
  choose b hb hmul using hmultiple
  let t (i : ι) := C.powerSectionTo (n i) (b i) N (hmul i) (s i)
  have hopen (i : ι) : (C.pow N).nonvanishingOpen (t i)=
      (C.pow (n i)).nonvanishingOpen (s i) :=
    C.nonvanishingOpen_powerSectionTo (n i) (b i) N (hmul i) (hb i) (s i)
  exact ⟨N,hN,ι,hι,t,(fun i=>by rw [hopen]; exact ha i),
    by simpa only [hopen] using hcover⟩

theorem IsAmple.exists_common_power_nonempty_affine_cover (hC : C.IsAmple) :
    ∃ (N : ℕ),0<N ∧ ∃ (ι : Type u) (_ : Fintype ι)
      (s : ι→Γ((C.pow N).sheaf,⊤)),
      (∀ i,Nonempty ((C.pow N).nonvanishingOpen (s i))) ∧
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow N).nonvanishingOpen (s i))=⊤ := by
  obtain ⟨N,hN,ι,hι,s,ha,hcover⟩ := hC.exists_common_power_affine_cover
  letI : Fintype ι := hι
  let J := {i : ι // Nonempty ((C.pow N).nonvanishingOpen (s i))}
  refine ⟨N,hN,J,inferInstance,(fun i=>s i),
    (fun i=>i.property),(fun i=>ha i),?_⟩
  apply top_unique
  intro x _
  have hx : x∈⨆ i,(C.pow N).nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨⟨i,⟨⟨x,hxi⟩⟩⟩,hxi⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 2000000 in
/-- The actual rational product satisfies the precise successor-power
section predicate on the original Cartier cover. The two input predicates
are the literal membership conditions of their Cartier section modules. -/
theorem sectionSuccProduct_isSection (N : ℕ)
    (t s : Γ(rationalFunctions X,⊤))
    (ht : (C.pow N).IsSection ⊤ t) (hs : C.IsSection ⊤ s) :
    (C.pow (N+1)).IsSection ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) := by
  intro i x hx
  have ht' : rationalValue X ⊤ t / (C.generator i : X.functionField)^N ∈
      regularAtSubring X x.val := ht i x hx
  have hs' : rationalValue X ⊤ s / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val := hs i x hx
  have h := (regularAtSubring X x.val).mul_mem ht' hs'
  have hvalue : rationalValue X ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) =
      rationalValue X ⊤ t * rationalValue X ⊤ s :=
    rationalValue_mul (X := X) (⊤ : X.Opens) t s
  change rationalValue X ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) /
    (C.generator i : X.functionField)^(N+1) ∈ regularAtSubring X x.val
  rw [hvalue]
  simpa only [pow_succ,div_mul_div_comm] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Multiply an actual section of the `N`th power by an actual section
of the original Cartier sheaf, retaining the literal local generators. -/
def sectionSuccProduct (N : ℕ) (t : Γ((C.pow N).sheaf,⊤))
    (s : Γ(C.sheaf,⊤)) : Γ((C.pow (N+1)).sheaf,⊤) :=
  ⟨rationalMul (X := X) (⊤ : X.Opens) t.val s.val,
    C.sectionSuccProduct_isSection N t.val s.val t.property s.property⟩

@[simp] theorem sectionSuccProduct_value (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) :
    (C.pow (N+1)).toCartierData.sectionValue ⊤ (C.sectionSuccProduct N t s) =
      (C.pow N).toCartierData.sectionValue ⊤ t *
        C.toCartierData.sectionValue ⊤ s :=
  map_mul (rationalSectionValueIso X (⊤ : X.Opens)).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from t.val)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val)

theorem localCoefficient_sectionSuccProduct (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) (i : C.index) :
    (C.pow (N+1)).localCoefficient i (C.sectionSuccProduct N t s) =
      (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t) *
        C.localCoefficient i s := by
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow N).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    letI : Nonempty ((C.pow (N+1)).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow (N+1)).toCartierData.sectionValue ⊤ (C.sectionSuccProduct N t s) /
          (C.generator i : X.functionField)^(N+1) :=
        (C.pow (N+1)).localCoefficient_value i (C.sectionSuccProduct N t s)
      _ = ((C.pow N).toCartierData.sectionValue ⊤ t /
          (C.generator i : X.functionField)^N) *
          (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField)) := by
        rw [C.sectionSuccProduct_value,pow_succ,div_mul_div_comm]
      _ = X.germToFunctionField (C.openSet i) ((C.pow N).localCoefficient i t) *
          X.germToFunctionField (C.openSet i) (C.localCoefficient i s) :=
        congrArg₂ (fun a b : X.functionField => a*b)
          ((C.pow N).localCoefficient_value i t).symm (C.localCoefficient_value i s).symm
      _ = _ := (map_mul (X.germToFunctionField (C.openSet i)).hom _ _).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

/-- Products vanish wherever either factor vanishes. This is a statement
about units in the genuine local rings, including boundary points. -/
theorem nonvanishingOpen_sectionSuccProduct (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) :
    (C.pow (N+1)).nonvanishingOpen (C.sectionSuccProduct N t s) =
      (C.pow N).nonvanishingOpen t ⊓ C.nonvanishingOpen s := by
  ext x
  obtain ⟨i,hi⟩ := C.covers x
  change x∈(C.pow (N+1)).nonvanishingOpen (C.sectionSuccProduct N t s) ↔
    x∈(C.pow N).nonvanishingOpen t ∧ x∈C.nonvanishingOpen s
  rw [(C.pow (N+1)).mem_nonvanishingOpen_iff i _ x hi,
    (C.pow N).mem_nonvanishingOpen_iff i t x hi,
    C.mem_nonvanishingOpen_iff i s x hi]
  have hcoeff := C.localCoefficient_sectionSuccProduct N t s i
  have hg := congrArg
    (fun z : Γ(X,C.openSet i) => X.presheaf.germ (C.openSet i) x hi z) hcoeff
  have hm := map_mul (X.presheaf.germ (C.openSet i) x hi).hom
    (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t)
    (C.localCoefficient i s)
  exact (Iff.of_eq (congrArg IsUnit (hg.trans hm))).trans IsUnit.mul_iff

/-- Every principal open inside the nonvanishing locus of a Cartier
section is exactly the nonvanishing locus of a section of a positive
power. The extra multiplication by `s` excludes all boundary points. -/
theorem exists_power_section_basicOpen [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) [Nonempty (C.nonvanishingOpen s)]
    (a : Γ(X,C.nonvanishingOpen s)) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      (C.pow N).nonvanishingOpen t=X.basicOpen a := by
  let r := X.germToFunctionField (C.nonvanishingOpen s) a
  obtain ⟨N,hN,t,ht⟩ := C.exists_section_extension s r
    (regular_germ_mem_regularAt X (C.nonvanishingOpen s) a)
  let w := C.sectionSuccProduct N t s
  refine ⟨N+1,Nat.succ_pos _,w,?_⟩
  have hsub : (C.pow (N+1)).nonvanishingOpen w≤C.nonvanishingOpen s := by
    rw [show w=C.sectionSuccProduct N t s from rfl,
      C.nonvanishingOpen_sectionSuccProduct]
    exact inf_le_right
  have hlocal (x : X) (hx : x∈C.nonvanishingOpen s) :
      x∈(C.pow (N+1)).nonvanishingOpen w ↔ x∈X.basicOpen a := by
    obtain ⟨i,hi⟩ := C.covers x
    letI : Nonempty (C.openSet i) := ⟨⟨x,hi⟩⟩
    letI : Nonempty ((C.pow N).openSet i) := by
      change Nonempty (C.openSet i)
      exact ⟨⟨x,hi⟩⟩
    have hsunit : IsUnit (X.presheaf.germ (C.openSet i) x hi
        (C.localCoefficient i s)) :=
      (C.mem_nonvanishingOpen_iff i s x hi).mp hx
    have hcoeff : X.presheaf.germ (C.openSet i) x hi
        ((C.pow N).localCoefficient i t) =
      X.presheaf.germ (C.nonvanishingOpen s) x hx a *
        (X.presheaf.germ (C.openSet i) x hi (C.localCoefficient i s))^N := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      have hleft := X.algebraMap_germ_eq_germToFunctionField hi
        (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t)
      have htvalue : X.germToFunctionField (C.openSet i)
          (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t) =
          (C.pow N).toCartierData.sectionValue ⊤ t /
            (C.generator i : X.functionField)^N :=
        (C.pow N).localCoefficient_value i t
      have he : (C.pow N).toCartierData.sectionValue ⊤ t /
          (C.generator i : X.functionField)^N =
          r*(X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^N := by
        calc
          _ = (r*(C.toCartierData.sectionValue ⊤ s)^N) /
              (C.generator i : X.functionField)^N :=
            congrArg (fun z : X.functionField => z/(C.generator i : X.functionField)^N) ht
          _ = r*(C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField))^N := by
            rw [div_pow,mul_div_assoc]
          _ = _ := congrArg (fun z : X.functionField => r*z^N)
            (C.localCoefficient_value i s).symm
      let stalkMap := algebraMap (X.presheaf.stalk x) X.functionField
      have hright : stalkMap (X.presheaf.germ (C.nonvanishingOpen s) x hx a *
          (X.presheaf.germ (C.openSet i) x hi (C.localCoefficient i s))^N) =
          r*(X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^N :=
        (map_mul stalkMap _ _).trans (congrArg₂ (· * ·)
          (X.algebraMap_germ_eq_germToFunctionField hx a)
          ((map_pow stalkMap _ N).trans (congrArg (fun z : X.functionField => z^N)
            (X.algebraMap_germ_eq_germToFunctionField hi (C.localCoefficient i s)))))
      exact (hleft.trans (htvalue.trans he)).trans hright.symm
    have hwp : (C.pow (N+1)).nonvanishingOpen w =
        (C.pow N).nonvanishingOpen t ⊓ C.nonvanishingOpen s :=
      C.nonvanishingOpen_sectionSuccProduct N t s
    have hw : x∈(C.pow (N+1)).nonvanishingOpen w ↔
        x∈(C.pow N).nonvanishingOpen t :=
      (Iff.of_eq (congrArg (fun V : X.Opens => x∈V) hwp)).trans (and_iff_left hx)
    have hunit : IsUnit (X.presheaf.germ (C.openSet i) x hi
        ((C.pow N).localCoefficient i t)) ↔
        IsUnit (X.presheaf.germ (C.nonvanishingOpen s) x hx a) :=
      (Iff.of_eq (congrArg IsUnit hcoeff)).trans
        (IsUnit.mul_iff.trans (and_iff_left (hsunit.pow N)))
    exact hw.trans (((C.pow N).mem_nonvanishingOpen_iff i t x hi).trans
      (hunit.trans (X.mem_basicOpen a x hx).symm))
  ext x
  constructor
  · intro hx
    exact (hlocal x (hsub hx)).mp hx
  · intro hx
    exact (hlocal x (X.basicOpen_le a hx)).mpr hx

/-- The affine-cover criterion for ampleness supplies affine
nonvanishing neighborhoods inside every prescribed open neighborhood. -/
theorem IsAmple.exists_affine_nonvanishing_subset (hC : C.IsAmple)
    {V : X.Opens} (x : X) (hx : x∈V) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      x∈(C.pow N).nonvanishingOpen t ∧
      (C.pow N).nonvanishingOpen t≤V ∧
      IsAffineOpen ((C.pow N).nonvanishingOpen t) := by
  letI : CompactSpace X := hC.1
  obtain ⟨a,ha,s,hxs,hUs⟩ := hC.2 x
  letI : Nonempty ((C.pow a).nonvanishingOpen s) := ⟨⟨x,hxs⟩⟩
  obtain ⟨f,hfV,hxf⟩ := hUs.exists_basicOpen_le ⟨x,hx⟩ hxs
  obtain ⟨b,hb,t,ht⟩ := (C.pow a).exists_power_section_basicOpen s f
  refine ⟨a*b,Nat.mul_pos ha hb,C.flattenPowSection a b t,?_⟩
  rw [C.nonvanishingOpen_flattenPowSection,ht]
  exact ⟨hxf,hfV,hUs.basicOpen f⟩

/-- The usual collection of affine nonvanishing opens of sections of
positive powers, without a fan or a projective embedding in its definition. -/
def affinePowerNonvanishingOpens : Set X.Opens :=
  {U | ∃ N : ℕ,0<N ∧ ∃ s : Γ((C.pow N).sheaf,⊤),
    U=(C.pow N).nonvanishingOpen s ∧ IsAffineOpen U}

/-- Equivalence with the ordinary topological-basis criterion for an
ample invertible sheaf on a quasi-compact integral scheme. -/
theorem isAmple_iff_isBasis_affinePowerNonvanishingOpens :
    C.IsAmple ↔ CompactSpace X ∧ Opens.IsBasis C.affinePowerNonvanishingOpens := by
  constructor
  · intro hC
    refine ⟨hC.1,Opens.isBasis_iff_nbhd.mpr ?_⟩
    intro V x hx
    obtain ⟨N,hN,s,hxs,hsub,haff⟩ :=
      IsAmple.exists_affine_nonvanishing_subset (C := C) hC x hx
    exact ⟨(C.pow N).nonvanishingOpen s,⟨N,hN,s,rfl,haff⟩,hxs,hsub⟩
  · rintro ⟨hcompact,hbasis⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨U,⟨N,hN,s,rfl,haff⟩,hx,-⟩ :=
      Opens.isBasis_iff_nbhd.mp hbasis (show x∈(⊤ : X.Opens) from trivial)
    exact ⟨N,hN,s,hx,haff⟩

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_common_power_affine_cover
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.isAmple_iff_isBasis_affinePowerNonvanishingOpens

namespace PaperVerification.ToricSchemes.CartierData

open AlgebraicGeometry TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] (D : CartierData X)

/-- The principal theorems' ampleness hypothesis is equivalent to the
standard affine nonvanishing-basis criterion for its actual Cartier sheaf. -/
theorem isAmple_iff_isBasis_affinePowerNonvanishingOpens :
    D.IsAmple ↔ CompactSpace X ∧
      Opens.IsBasis D.localCocycle.affinePowerNonvanishingOpens :=
  D.localCocycle.isAmple_iff_isBasis_affinePowerNonvanishingOpens

end PaperVerification.ToricSchemes.CartierData

#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_iff_isBasis_affinePowerNonvanishingOpens
end
-- END ToricAmpleCommonPower
end

section
-- BEGIN ToricSectionRatios



/-! # Actual regular ratios of sections on nonvanishing opens -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem nonvanishing_iff_value (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

theorem sectionValue_ne_zero_of_nonvanishing (s : Γ(C.sheaf,⊤))
    [hU : Nonempty (C.nonvanishingOpen s)] : C.toCartierData.sectionValue ⊤ s≠0 := by
  let x := Classical.choice hU
  obtain ⟨i,hxi⟩ := C.covers x.val
  exact ((C.nonvanishing_iff_value i s x.val hxi).mp x.property).1

theorem section_ratio_regular (t s : Γ(C.sheaf,⊤))
    (x : X) (hx : x∈C.nonvanishingOpen s) :
    C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s∈
      regularAtSubring X x := by
  obtain ⟨i,hxi⟩ := C.covers x
  have hs := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
  have ht : C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField)∈
      regularAtSubring X x := by
    change rationalValue X ⊤ t.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact t.property i ⟨x,trivial⟩ hxi
  have he : (C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField))*
      ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
    field_simp [Units.ne_zero]
  simpa only [he] using (regularAtSubring X x).mul_mem ht hs

/-- The quotient is an actual section of the structure sheaf on the
actual nonvanishing open, including its unique value on the empty open. -/
def ratioSection (t s : Γ(C.sheaf,⊤)) : Γ(X,C.nonvanishingOpen s) := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    exact Classical.choose (exists_regularSection_of_stalkwise X
      (C.nonvanishingOpen s)
      (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
      (C.section_ratio_regular t s))
  · exact 0

theorem ratioSection_value (t s : Γ(C.sheaf,⊤))
    [Nonempty (C.nonvanishingOpen s)] :
    X.germToFunctionField (C.nonvanishingOpen s) (C.ratioSection t s)=
      C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
  unfold ratioSection
  rw [dif_pos (show Nonempty (C.nonvanishingOpen s) from inferInstance)]
  exact Classical.choose_spec (exists_regularSection_of_stalkwise X
    (C.nonvanishingOpen s)
    (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
    (C.section_ratio_regular t s))

@[simp] theorem ratioSection_self (s : Γ(C.sheaf,⊤)) : C.ratioSection s s=1 := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen s)
    rw [C.ratioSection_value,map_one,div_self (C.sectionValue_ne_zero_of_nonvanishing s)]
  · have hbot : C.nonvanishingOpen s=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen s) hbot
    exact Subsingleton.elim _ _

/-- The coordinate ratio cuts out exactly the intersection of the two
actual nonvanishing opens. -/
theorem ratioSection_basicOpen (t s : Γ(C.sheaf,⊤)) :
    X.basicOpen (C.ratioSection t s)=C.nonvanishingOpen s⊓C.nonvanishingOpen t := by
  ext x
  by_cases hx : x∈C.nonvanishingOpen s
  · letI : Nonempty (C.nonvanishingOpen s) := ⟨⟨x,hx⟩⟩
    obtain ⟨i,hxi⟩ := C.covers x
    have hs0 := C.sectionValue_ne_zero_of_nonvanishing s
    have hsInv := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
    have hs : C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)∈
        regularAtSubring X x := by
      change rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
        regularAtSubring X x
      exact s.property i ⟨x,trivial⟩ hxi
    refine (X.mem_basicOpen (C.ratioSection t s) x hx).trans ?_
    change IsUnit (X.presheaf.germ (C.nonvanishingOpen s) x hx (C.ratioSection t s)) ↔
      x∈C.nonvanishingOpen s ∧ x∈C.nonvanishingOpen t
    rw [isUnit_stalk_iff,
      X.algebraMap_germ_eq_germToFunctionField hx,C.ratioSection_value]
    simp only [Opens.mem_inf,hx,true_and,inv_div]
    rw [C.nonvanishing_iff_value i t x hxi]
    constructor
    · rintro ⟨hfrac0,ht⟩
      refine ⟨(div_ne_zero_iff.mp hfrac0).1,?_⟩
      have he : ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s)*
          (C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t)=
            (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t := by
        field_simp [hs0]
      simpa only [he] using (regularAtSubring X x).mul_mem hsInv ht
    · rintro ⟨ht0,ht⟩
      refine ⟨div_ne_zero ht0 hs0,?_⟩
      have he : (C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField))*
          ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t)=
            C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t := by
        field_simp [Units.ne_zero]
      simpa only [he] using (regularAtSubring X x).mul_mem hs ht
  · constructor
    · intro h
      exact (hx (X.basicOpen_le _ h)).elim
    · exact fun h=>(hx h.1).elim

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.BaseSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap_top (U : X.Opens) [Nonempty U] (a : k) :
    X.germToFunctionField U (scalarMap k X U a)=
      X.germToFunctionField ⊤ (scalarMap k X ⊤ a) := by
  simp only [scalarMap,RingHom.comp_apply]
  rw [germToFunctionField_restrict,germToFunctionField_restrict]

end PaperVerification.ToricSchemes.BaseSections

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.ratioSection_basicOpen
end
-- END ToricSectionRatios
end

section
-- BEGIN ToricSectionProjectiveMap



/-!
# The actual projective morphism defined by generating Cartier sections

The construction uses the genuine ratios in the structure sheaf on the
nonvanishing opens. Compatibility is proved on the generic stalk and then
on each integral overlap by separatedness of Proj. It does not assume a
sections-to-projective-space dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericStalkMap_isDominant :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint X.functionField,X.fromSpecStalk_closedPoint⟩

theorem genericStalkMapToOpen_isDominant (U : X.Opens)
    (hU : genericPoint X∈U) :
    IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU) := by
  letI : IsDominant
      (U.fromSpecStalkOfMem (genericPoint X) hU ≫ U.ι) := by
    rw [U.fromSpecStalkOfMem_ι]
    exact genericStalkMap_isDominant
  exact IsDominant.of_comp_of_isOpenImmersion _ U.ι

theorem genericStalkMapToOpen_homOfLE {U V : X.Opens}
    (hUV : U≤V) (hU : genericPoint X∈U) (hV : genericPoint X∈V) :
    U.fromSpecStalkOfMem (genericPoint X) hU ≫ X.homOfLE hUV =
      V.fromSpecStalkOfMem (genericPoint X) hV := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc,Scheme.homOfLE_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- A variable lies in the degree-one piece of the actual polynomial grading. -/
theorem polynomialVariable_mem_degreeOne (k : Type u) [CommRing k]
    {ι : Type u} (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u}
    (s : ι→Γ(C.sheaf,⊤))

/-- The coordinate map of the chart where the i-th actual section does
not vanish. Its selected coordinate is literally one. -/
def sectionProjectiveChartRingMap (i : ι) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen (s i)) :=
  MvPolynomial.eval₂Hom
    (BaseSections.scalarMap k X (C.nonvanishingOpen (s i)))
    (fun j=>C.ratioSection (s j) (s i))

@[simp] theorem sectionProjectiveChartRingMap_X (i j : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)=
      C.ratioSection (s j) (s i) := by
  simp [sectionProjectiveChartRingMap]

@[simp] theorem sectionProjectiveChartRingMap_self (i : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i)=1 := by
  simp

/-- The chart map is a morphism of actual schemes through the actual
homogeneous degree-zero localization of the polynomial ring. -/
def sectionProjectiveChart (i : ι) :
    (C.nonvanishingOpen (s i)).toScheme⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
          (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one))) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide)

def sectionProjectiveFieldMap : MvPolynomial ι k→+*X.functionField :=
  MvPolynomial.eval₂Hom
    ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
    (fun j=>C.toCartierData.sectionValue ⊤ (s j))

theorem sectionProjectiveChartRingMap_germ (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (C.sectionProjectiveChartRingMap k s i) =
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ (s i))⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionProjectiveChartRingMap,
      MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    rw [RingHom.comp_apply, C.sectionProjectiveChartRingMap_X k s i j,
      MvPolynomial.eval₂Hom_X', C.ratioSection_value]
    simp only [div_eq_mul_inv, mul_comm]

/-- Every local projective chart restricts to the projective point given
by the genuine rational values of the sections. -/
theorem sectionProjectiveChart_generic (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))]
    (hη : genericPoint X∈C.nonvanishingOpen (s i)) :
    (C.nonvanishingOpen (s i)).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionProjectiveChart k s i =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa [sectionProjectiveFieldMap] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  have hs := C.sectionValue_ne_zero_of_nonvanishing (s i)
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (j : ι) := C.toCartierData.sectionValue ⊤ (s j)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i)
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom
    (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
  let E := MvPolynomial.eval₂Hom F (fun j => (v i)⁻¹ * v j)
  have hEi : IsUnit (E (MvPolynomial.X i)) := by
    have hv : v i ≠ 0 := hs
    simp only [E, MvPolynomial.eval₂Hom_X', inv_mul_cancel₀ hv]
    exact isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k →+* X.functionField)
      (hF : F₁ = F₂) (h₁ : IsUnit (F₁ (MvPolynomial.X i)))
      (h₂ : IsUnit (F₂ (MvPolynomial.X i))) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₁ (MvPolynomial.X i) h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₂ (MvPolynomial.X i) h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans
    (heval _ E (C.sectionProjectiveChartRingMap_germ k s i) _ hEi)
  unfold sectionProjectiveChart
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun j=>(v i)⁻¹*v j)) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide) (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (v i)⁻¹ (inv_ne_zero hs)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) (by decide)
    (by simpa [v] using hs)

theorem sectionProjectiveChart_overlap (i j : ι) :
    X.homOfLE (U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j))
        inf_le_left ≫ C.sectionProjectiveChart k s i =
      X.homOfLE inf_le_right ≫ C.sectionProjectiveChart k s j := by
  classical
  let U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j)
  by_cases hU : Nonempty U
  · letI := hU
    letI : Nonempty (C.nonvanishingOpen (s i)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.1⟩⟩
    letI : Nonempty (C.nonvanishingOpen (s j)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.2⟩⟩
    have hηU : genericPoint X∈U := genericPoint_mem_open X U
    let η := U.fromSpecStalkOfMem (genericPoint X) hηU
    letI : IsDominant η := genericStalkMapToOpen_isDominant U hηU
    apply ext_of_isDominant η
    rw [← Category.assoc,← Category.assoc,
      genericStalkMapToOpen_homOfLE inf_le_left hηU hηU.1,
      genericStalkMapToOpen_homOfLE inf_le_right hηU hηU.2,
      C.sectionProjectiveChart_generic k s i hηU.1,
      C.sectionProjectiveChart_generic k s j hηU.2]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      (MvPolynomial.X i) (MvPolynomial.X j)
      (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)
      (by decide) (by decide) _ _
  · letI : IsEmpty U := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Generating sections define an actual global morphism to Proj. -/
def sectionProjectiveMap
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    X⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).glueMorphisms
    (C.sectionProjectiveChart k s) (by
      intro i j
      change Limits.pullback.fst (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s i =
        Limits.pullback.snd (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s j
      apply (cancel_epi (isPullback_opens_inf
        (C.nonvanishingOpen (s i)) (C.nonvanishingOpen (s j))).isoPullback.hom).mp
      simpa only [Category.assoc,IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc] using
        C.sectionProjectiveChart_overlap k s i j)

@[reassoc (attr := simp)] theorem sectionProjectiveMap_chart
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι) :
    (C.nonvanishingOpen (s i)).ι ≫ C.sectionProjectiveMap k s hcover =
      C.sectionProjectiveChart k s i := by
  exact (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).ι_glueMorphisms _ _ i

theorem sectionProjectiveChartRingMap_away_variable (i j : ι) :
    unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)) =
        C.ratioSection (s j) (s i) := by
  have he := unitHomogeneousAwayEvaluation_mk_of_eq_one
    (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveChartRingMap k s i)
    (C.sectionProjectiveChartRingMap_self k s i)
    (show (MvPolynomial.X i : MvPolynomial ι k) ∈
      MvPolynomial.homogeneousSubmodule ι k 1 from polynomialVariable_mem_degreeOne k i)
    1 ((MvPolynomial.X j : MvPolynomial ι k) ^ 1)
    (by simpa only [one_smul, pow_one] using polynomialVariable_mem_degreeOne k j)
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    C.sectionProjectiveChartRingMap_X k s i j] using he

theorem sectionProjectiveChart_preimage (i j : ι) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ C.nonvanishingOpen (s j) := by
  have he := C.sectionProjectiveChartRingMap_away_variable k s i j
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      (polynomialVariable_mem_degreeOne k j) (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

/-- The projective basic opens have exactly the expected inverse images;
this is a statement about scheme morphisms and actual open subsets. -/
theorem sectionProjectiveMap_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (j : ι) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      C.nonvanishingOpen (s j) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_preimage k s i j)
  have hpre' : C.sectionProjectiveChart k s i ⟨x, hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x, hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x, hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j)
  rw [hchart]
  exact hpre'

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_chart
end
-- END ToricSectionProjectiveMap
end

section
-- BEGIN ToricSectionProjectiveBase



/-! # The section morphism preserves the actual base structure map -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] (ι : Type u)

def polynomialGradeZeroScalarMap :
    k→+*MvPolynomial.homogeneousSubmodule ι k 0 where
  toFun a := ⟨MvPolynomial.C a,MvPolynomial.isHomogeneous_C ι a⟩
  map_one' := Subtype.ext (MvPolynomial.C.map_one)
  map_mul' a b := Subtype.ext (MvPolynomial.C.map_mul a b)
  map_zero' := Subtype.ext (MvPolynomial.C.map_zero)
  map_add' a b := Subtype.ext (MvPolynomial.C.map_add a b)

/-- The literal structural morphism of polynomial projective space. -/
def polynomialProjectiveToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k)⟶Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroScalarMap k ι))

instance polynomialProjectiveToSpec_isSeparated :
    IsSeparated (polynomialProjectiveToSpec k ι) := by
  unfold polynomialProjectiveToSpec
  infer_instance

namespace BaseSections

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

theorem toSpec_scalarMap (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (scalarMap k X U)) =
      U.ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  unfold scalarMap
  rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,
    Spec.map_comp,CommRingCat.ofHom_hom,CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom,← Category.assoc,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc,toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end BaseSections

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_toSpec (i : ι) :
    C.sectionProjectiveChart k s i ≫ polynomialProjectiveToSpec k ι =
      (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  let F := C.sectionProjectiveChartRingMap k s i
  have hunit : IsUnit (F (MvPolynomial.X i)) := by
    change IsUnit (C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i))
    rw [C.sectionProjectiveChartRingMap_self k s i]
    exact isUnit_one
  let E := unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    F (MvPolynomial.X i) hunit
  have hscalar : E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))=
        BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) := by
    ext a
    change Localization.awayLift F (MvPolynomial.X i) hunit
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
    simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
      F,sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]
  unfold sectionProjectiveChart polynomialProjectiveToSpec
  rw [Category.assoc,Category.assoc,Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp,← Spec.map_comp]
  change (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))))=_
  rw [hscalar,BaseSections.toSpec_scalarMap]

theorem sectionProjectiveMap_toSpec
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι =
      (X ↘ Spec (CommRingCat.of k)) := by
  apply (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).hom_ext
  intro i
  change (C.nonvanishingOpen (s i)).ι ≫
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) =
    (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k))
  rw [← Category.assoc,C.sectionProjectiveMap_chart k s hcover i,
    C.sectionProjectiveChart_toSpec k s i]

/-- Properness follows from the genuine base-compatible map to the
separated projective target. -/
theorem sectionProjectiveMap_isProper
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    IsProper (C.sectionProjectiveMap k s hcover) := by
  letI : IsProper
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) := by
    rw [C.sectionProjectiveMap_toSpec k s hcover]
    infer_instance
  exact IsProper.of_comp _ (polynomialProjectiveToSpec k ι)

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isProper
end
-- END ToricSectionProjectiveBase
end

section
-- BEGIN ToricSectionProjectiveEmbedding



/-! # A genuine closed immersion from actual affine coordinate generators -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartCoordinates (i : ι) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X i)→+*Γ(X,C.nonvanishingOpen (s i)) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)

theorem sectionProjectiveChart_isPreimmersion (i : ι)
    (hU : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion (C.sectionProjectiveChart k s i) := by
  letI : IsAffine (C.nonvanishingOpen (s i)) := hU
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))) :=
    IsClosedImmersion.spec_of_surjective _ hgen
  let q := Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (polynomialVariable_mem_degreeOne k i) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

/-- If some of the nonvanishing affine charts cover X and their actual
ratio maps generate their coordinate rings, the section map is a
preimmersion. No global immersion statement is built into the premise. -/
theorem sectionProjectiveMap_isPreimmersion_of_chartGenerators
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsPreimmersion (C.sectionProjectiveMap k s hcover) := by
  let f := C.sectionProjectiveMap k s hcover
  let U (i : κ) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : κ) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X (chooseChart i))
  have hlocal (i : κ) : IsPreimmersion ((U i).ι ≫ f) := by
    change IsPreimmersion ((C.nonvanishingOpen (s (chooseChart i))).ι ≫
      C.sectionProjectiveMap k s hcover)
    rw [C.sectionProjectiveMap_chart k s hcover (chooseChart i)]
    exact C.sectionProjectiveChart_isPreimmersion k s _ (ha i) (hgen i)
  letI : SurjectiveOnStalks f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hchosen (fun i=>by
      letI := hlocal i
      infer_instance)
  refine { isEmbedding := ?_ }
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
    (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
  · rintro y ⟨x,rfl⟩
    have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
    obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
    apply Opens.mem_iSup.mpr
    refine ⟨i,?_⟩
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    change x ∈ C.sectionProjectiveMap k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X (chooseChart i))
    rw [hp]
    exact hxi
  · intro i
    exact (U i).ι.continuous
  · intro i x hx
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    have hxi : x∈U i := by
      change x∈C.nonvanishingOpen (s (chooseChart i))
      rw [← hp]
      exact hx
    exact ⟨⟨x,hxi⟩,rfl⟩
  · intro i
    letI := hlocal i
    exact ((U i).ι ≫ f).isEmbedding

/-- Properness supplies the closed image. Together with the explicit
local coordinate-ring quotients this gives a genuine closed immersion. -/
theorem sectionProjectiveMap_isClosedImmersion_of_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k s hcover) := by
  letI := C.sectionProjectiveMap_isPreimmersion_of_chartGenerators k s
    hcover chooseChart hchosen ha hgen
  letI := C.sectionProjectiveMap_isProper k s hcover
  exact IsClosedImmersion.of_isPreimmersion _
    (C.sectionProjectiveMap k s hcover).isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_chartGenerators
end
-- END ToricSectionProjectiveEmbedding
end

section
-- BEGIN ToricSectionChartGenerators



/-! # Actual affine coordinate generators as ratios of global sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

theorem scalarMap_finiteType [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (scalarMap k X U).FiniteType := by
  let f := X ↘ Spec (CommRingCat.of k)
  have htop := f.finiteType_appLE (isAffineOpen_top _) hU
    (show U≤f ⁻¹ᵁ ⊤ by simp)
  have hc := RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso _).2
  convert htop.comp hc using 1
  ext a
  simp only [scalarMap,RingHom.comp_apply,Scheme.Hom.appLE,
    CommRingCat.hom_comp,ConcreteCategory.comp_apply]
  rfl

theorem exists_finite_polynomial_generators
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι→Γ(X,U)),
      Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U) g) := by
  letI : Algebra.FiniteType k Γ(X,U) := scalarMap_finiteType k U hU
  obtain ⟨g,F,hF⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (show Algebra.FiniteType k Γ(X,U) from inferInstance))
  refine ⟨g,inferInstance,(fun j=>F (MvPolynomial.X j)),?_⟩
  have he : MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>F (MvPolynomial.X j))=F.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C]
      change algebraMap k Γ(X,U) a = F (algebraMap k (MvPolynomial g k) a)
      exact (F.commutes a).symm
    · intro j
      simp
  rw [he]
  change Function.Surjective F
  exact hF

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartConstant (s : ι→Γ(C.sheaf,⊤)) (i : ι) :
    k→+*HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι k)
    (Submonoid.powers (MvPolynomial.X i))).comp (polynomialGradeZeroScalarMap k ι)

@[simp] theorem sectionProjectiveChartCoordinates_constant (i : ι) (a : k) :
    C.sectionProjectiveChartCoordinates k s i
        (C.sectionProjectiveChartConstant k s i a)=
      BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) a := by
  change Localization.awayLift (C.sectionProjectiveChartRingMap k s i)
    (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
  simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
    sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]

@[simp] theorem sectionProjectiveChartCoordinates_variable (i j : ι) :
    C.sectionProjectiveChartCoordinates k s i
      (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k j))=
      C.ratioSection (s j) (s i) := by
  exact C.sectionProjectiveChartRingMap_away_variable k s i j

/-- Every polynomial in actual generating ratios lifts to an actual
element of the homogeneous affine chart ring. -/
theorem sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
    (i : ι) {κ : Type u} (j : κ→ι)
    (g : κ→Γ(X,C.nonvanishingOpen (s i)))
    (hpoly : Function.Surjective (MvPolynomial.eval₂Hom
      (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g))
    (hgen : ∀ t,C.ratioSection (s (j t)) (s i)=g t) :
    Function.Surjective (C.sectionProjectiveChartCoordinates k s i) := by
  let F := MvPolynomial.eval₂Hom (C.sectionProjectiveChartConstant k s i)
    (fun t=>HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k (j t)))
  have hcomp : (C.sectionProjectiveChartCoordinates k s i).comp F=
      MvPolynomial.eval₂Hom
        (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_C,
        C.sectionProjectiveChartCoordinates_constant k s i a]
    · intro t
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_X',
        C.sectionProjectiveChartCoordinates_variable k s i (j t),hgen t]
  have hs : Function.Surjective ((C.sectionProjectiveChartCoordinates k s i).comp F) := by
    rw [hcomp]
    exact hpoly
  exact Function.Surjective.of_comp hs

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
end
-- END ToricSectionChartGenerators
end

section
-- BEGIN ToricAmpleProjectiveEmbedding



/-!
# A finite projective embedding obtained from intrinsic ampleness

Choose finite generators in each genuine affine nonvanishing chart.
The denominator lemma extends every generator after multiplication by a
common positive power of the chart section. Those finitely many actual
global sections give all coordinate-ring quotients needed by the closed
immersion theorem.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

theorem polynomial_generators_transport (k : Type u) [CommRing k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    {U V : X.Opens} (h : U=V) {ι : Type u} (g : ι→Γ(X,V))
    (hg : Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X V) g)) :
    Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>X.presheaf.map (eqToHom h).op (g j))) := by
  subst V
  have hid : (fun j => X.presheaf.map (eqToHom (rfl : U = U)).op (g j)) = g := by
    funext j
    change X.presheaf.map (𝟙 (op U)) (g j) = g j
    exact congrArg (fun f : Γ(X,U) ⟶ Γ(X,U) => f (g j))
      (X.presheaf.map_id (op U))
  rw [hid]
  exact hg

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The finite ratio-generation construction, before using properness.
The output sections belong to an actual positive tensor power. -/
theorem exists_power_chart_generators [CompactSpace X]
    {ι : Type u} [Fintype ι] (s : ι→Γ(C.sheaf,⊤))
    (hnonempty : ∀ i,Nonempty (C.nonvanishingOpen (s i)))
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s i)))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    ∃ N : ℕ,0<N ∧ ∃ (J : Type u) (_ : Fintype J)
      (t : J→Γ((C.pow N).sheaf,⊤)) (chooseChart : ι→J),
      (∀ i,t (chooseChart i)=C.sectionPow N (s i)) ∧
      (⨆ j,(C.pow N).nonvanishingOpen (t j))=⊤ ∧
      (⨆ i,(C.pow N).nonvanishingOpen (t (chooseChart i)))=⊤ ∧
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (t (chooseChart i)))) ∧
      (∀ i,Function.Surjective
        ((C.pow N).sectionProjectiveChartCoordinates k t (chooseChart i))) := by
  choose G hG g hg using fun i=>BaseSections.exists_finite_polynomial_generators
    k (C.nonvanishingOpen (s i)) (ha i)
  letI (i : ι) : Fintype (G i) := hG i
  letI (i : ι) : Nonempty (C.nonvanishingOpen (s i)) := hnonempty i
  let P := (i : ι) × G i
  let r (p : P) : X.functionField :=
    X.germToFunctionField (C.nonvanishingOpen (s p.1)) (g p.1 p.2)
  have hext (p : P) : ∃ B : ℕ,0<B ∧ ∀ N : ℕ,B≤N→
      ∃ u : Γ((C.pow N).sheaf,⊤),
        (C.pow N).toCartierData.sectionValue ⊤ u=
          r p*(C.toCartierData.sectionValue ⊤ (s p.1))^N :=
    C.eventually_section_extension (s p.1) (r p)
      (regular_germ_mem_regularAt X _ (g p.1 p.2))
  choose B hB hext using hext
  let N := (∑ p : P,B p)+1
  have hN : 0<N := Nat.succ_pos _
  have hBN (p : P) : B p≤N :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ p)).trans
      (Nat.le_add_right _ 1)
  choose u hu using fun p : P=>hext p N (hBN p)
  let J := ι⊕P
  let t : J→Γ((C.pow N).sheaf,⊤) :=
    Sum.elim (fun i=>C.sectionPow N (s i)) u
  have hopen (i : ι) : (C.pow N).nonvanishingOpen (t (Sum.inl i))=
      C.nonvanishingOpen (s i) := C.nonvanishingOpen_sectionPow N hN (s i)
  have hc : (⨆ i,(C.pow N).nonvanishingOpen (t (Sum.inl i)))=⊤ := by
    simpa only [hopen] using hcover
  refine ⟨N,hN,J,inferInstance,t,Sum.inl,(fun _=>rfl),?_,hc,?_,?_⟩
  · apply top_unique
    rw [← hc]
    exact iSup_le fun i=>le_iSup_of_le (Sum.inl i) le_rfl
  · intro i
    rw [hopen]
    exact ha i
  · intro i
    let U := (C.pow N).nonvanishingOpen (t (Sum.inl i))
    letI : Nonempty U := by
      obtain ⟨x⟩ := hnonempty i
      refine ⟨⟨x.val, ?_⟩⟩
      change x.val ∈ (C.pow N).nonvanishingOpen (t (Sum.inl i))
      rw [hopen i]
      exact x.property
    let g' (j : G i) : Γ(X,U) :=
      X.presheaf.map (eqToHom (hopen i)).op (g i j)
    have hpoly : Function.Surjective
        (MvPolynomial.eval₂Hom (BaseSections.scalarMap k X U) g') :=
      BaseSections.polynomial_generators_transport k (hopen i) (g i) (hg i)
    apply (C.pow N).sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
      k t (Sum.inl i) (fun j=>Sum.inr ⟨i,j⟩) g' hpoly
    intro j
    apply X.germToFunctionField_injective U
    rw [(C.pow N).ratioSection_value]
    change (C.pow N).toCartierData.sectionValue ⊤ (u ⟨i,j⟩)/
      (C.pow N).toCartierData.sectionValue ⊤ (C.sectionPow N (s i)) = _
    rw [hu,C.sectionPow_value]
    have hs : C.toCartierData.sectionValue ⊤ (s i)≠0 :=
      C.sectionValue_ne_zero_of_nonvanishing (s i)
    rw [mul_div_cancel_right₀ _ (pow_ne_zero N hs)]
    change X.germToFunctionField _ (g i j)=
      X.germToFunctionField U (X.presheaf.map (eqToHom (hopen i)).op (g i j))
    exact (germToFunctionField_restrict X (eqToHom (hopen i)) (g i j)).symm

/-- Intrinsic ampleness on a proper finite-type integral scheme yields
a genuine finite projective closed immersion. The sections are actual
sections of two positive, explicitly nested tensor powers of C. -/
theorem IsAmple.exists_finite_projective_embedding
    [IsProper (X ↘ Spec (CommRingCat.of k))] (hC : C.IsAmple) :
    ∃ a : ℕ,0<a ∧ ∃ b : ℕ,0<b ∧
      ∃ (J : Type u) (_ : Fintype J)
        (t : J→Γ(((C.pow a).pow b).sheaf,⊤)),
        ∃ hcover : (⨆ j,((C.pow a).pow b).nonvanishingOpen (t j))=⊤,
          IsClosedImmersion (((C.pow a).pow b).sectionProjectiveMap k t hcover) := by
  letI : CompactSpace X := hC.1
  obtain ⟨a,ha,ι,hι,s,hnonempty,haff,hcover⟩ :=
    hC.exists_common_power_nonempty_affine_cover
  letI : Fintype ι := hι
  obtain ⟨b,hb,J,hJ,t,chooseChart,ht,hall,hchosen,haff',hgen⟩ :=
    (C.pow a).exists_power_chart_generators k s hnonempty haff hcover
  letI : Fintype J := hJ
  exact ⟨a,ha,b,hb,J,hJ,t,hall,
    ((C.pow a).pow b).sectionProjectiveMap_isClosedImmersion_of_chartGenerators
      k t hall chooseChart hchosen haff' hgen⟩

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_projective_embedding
end
-- END ToricAmpleProjectiveEmbedding
end

section
-- BEGIN ToricSectionLinearSystems



/-! # Linear changes of an actual finite system of Cartier sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι : Type u}

def sectionLinearForm (c : ι→₀k) : MvPolynomial ι k :=
  c.sum (fun i a=>MvPolynomial.C a*MvPolynomial.X i)

theorem sectionLinearForm_isHomogeneous (c : ι→₀k) :
    (sectionLinearForm k c).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem sectionLinearForm_eval {R : Type u} [CommRing R]
    (F : k→+*R) (v : ι→R) (c : ι→₀k) :
    MvPolynomial.eval₂Hom F v (sectionLinearForm k c)=
      c.sum (fun i a=>F a*v i) := by
  simp only [sectionLinearForm,Finsupp.sum,map_sum,map_mul,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X']

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The local coefficients of genuine sections are linear over the
actual base ring. -/
def localCoefficientLinear (i : C.index) :
    Γ(C.sheaf,⊤)→ₗ[k]Γ(X,C.openSet i) where
  toFun := C.localCoefficient i
  map_add' s t := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      have hst : C.toCartierData.sectionValue ⊤ (s+t) =
          C.toCartierData.sectionValue ⊤ s+C.toCartierData.sectionValue ⊤ t :=
        (C.toCartierData.globalSectionValue k).map_add s t
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (s+t)) =
            C.toCartierData.sectionValue ⊤ (s+t)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (s+t)
        _ = C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)+
            C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField) := by
          rw [hst,add_div]
        _ = X.germToFunctionField (C.openSet i) (C.localCoefficient i s)+
            X.germToFunctionField (C.openSet i) (C.localCoefficient i t) :=
          congrArg₂ (·+·) (C.localCoefficient_value i s).symm
            (C.localCoefficient_value i t).symm
        _ = X.germToFunctionField (C.openSet i)
            (C.localCoefficient i s+C.localCoefficient i t) :=
          (map_add (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _
  map_smul' a s := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      change X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s))=
        X.germToFunctionField (C.openSet i)
          (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s)
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s)) =
            C.toCartierData.globalSectionValue k (a • s)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (a • s)
        _ = (algebraMap k X.functionField a*C.toCartierData.globalSectionValue k s)/
            (C.generator i : X.functionField) :=
          congrArg (fun z : X.functionField=>z/(C.generator i : X.functionField))
            ((C.toCartierData.globalSectionValue k).map_smul a s)
        _ = algebraMap k X.functionField a*
            (C.toCartierData.globalSectionValue k s/(C.generator i : X.functionField)) :=
          mul_div_assoc _ _ _
        _ = X.germToFunctionField (C.openSet i) (BaseSections.scalarMap k X (C.openSet i) a)*
            X.germToFunctionField (C.openSet i) (C.localCoefficient i s) :=
          congrArg₂ (·*·) (BaseSections.germ_scalarMap k (C.openSet i) a).symm
            (C.localCoefficient_value i s).symm
        _ = X.germToFunctionField (C.openSet i)
            (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s) :=
          (map_mul (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _

theorem localCoefficient_linearCombination (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k)
    (i : C.index) :
    C.localCoefficient i (Finsupp.linearCombination k s c)=
      c.sum (fun j a=>BaseSections.scalarMap k X (C.openSet i) a*
        C.localCoefficient i (s j)) := by
  change C.localCoefficientLinear k i (Finsupp.linearCombination k s c)=_
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    localCoefficientLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def]
  all_goals rfl

/-- The nonvanishing open of a linear combination lies in the union of
the nonvanishing opens of the genuine sections in that combination. -/
theorem nonvanishingOpen_linearCombination_le (s : ι→Γ(C.sheaf,⊤))
    (c : ι→₀k) :
    C.nonvanishingOpen (Finsupp.linearCombination k s c)≤
      ⨆ j,C.nonvanishingOpen (s j) := by
  intro x hx
  by_contra hnone
  have hnone' (j : ι) : x∉C.nonvanishingOpen (s j) :=
    fun hj=>hnone (Opens.mem_iSup.mpr ⟨j,hj⟩)
  obtain ⟨i,hxi⟩ := C.covers x
  have ht := (C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i _ x hxi).mp hx
  apply ht
  rw [C.localCoefficient_linearCombination k s c i]
  simp only [Finsupp.sum,map_sum,map_mul]
  apply Ideal.sum_mem
  intro j hj
  apply Ideal.mul_mem_left
  exact not_not.mp (fun h=>hnone' j
    ((C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i (s j) x hxi).mpr h))

theorem nonvanishing_cover_of_spans {κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    (hspan : ∀ i,∃ c : κ→₀k,Finsupp.linearCombination k t c=s i) :
    (⨆ j,C.nonvanishingOpen (t j))=⊤ := by
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  obtain ⟨c,hc⟩ := hspan i
  rw [← hc]
  exact C.nonvanishingOpen_linearCombination_le k t c

theorem sectionLinearForm_fieldValue (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionProjectiveFieldMap k s (sectionLinearForm k c)=
      C.toCartierData.sectionValue ⊤ (Finsupp.linearCombination k s c) := by
  rw [sectionProjectiveFieldMap,sectionLinearForm_eval]
  change _=C.toCartierData.globalSectionValue k (Finsupp.linearCombination k s c)
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    Algebra.smul_def,RingHom.comp_apply]
  rfl

def sectionRatioPolynomialMap (s : ι→Γ(C.sheaf,⊤)) (den : Γ(C.sheaf,⊤)) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen den) :=
  MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.nonvanishingOpen den))
    (fun j=>C.ratioSection (s j) den)

theorem sectionRatioPolynomialMap_germ (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) [Nonempty (C.nonvanishingOpen den)] :
    (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
        (C.sectionRatioPolynomialMap k s den)=
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ den)⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_X',
      C.ratioSection_value,div_eq_mul_inv,mul_comm]

theorem sectionRatioPolynomialMap_linearForm (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionRatioPolynomialMap k s den (sectionLinearForm k c)=
      C.ratioSection (Finsupp.linearCombination k s c) den := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen den)
    rw [C.ratioSection_value]
    change ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)) (sectionLinearForm k c)=_
    rw [C.sectionRatioPolynomialMap_germ k s den]
    rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled _ _ _ _ 1
      (sectionLinearForm_isHomogeneous k c),pow_one]
    rw [← C.sectionLinearForm_fieldValue k s c]
    simp only [sectionProjectiveFieldMap,MvPolynomial.coe_eval₂Hom,div_eq_mul_inv,mul_comm]
  · have hbot : C.nonvanishingOpen den=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen den) hbot
    exact Subsingleton.elim _ _

theorem sectionProjectiveMap_generic (s : ι→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    X.fromSpecStalk (genericPoint X) ≫ C.sectionProjectiveMap k s hcover =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  rw [← (C.nonvanishingOpen (s i)).fromSpecStalkOfMem_ι
    (genericPoint X) (genericPoint_mem_open X _),Category.assoc,
    C.sectionProjectiveMap_chart k s hcover i]
  exact C.sectionProjectiveChart_generic k s i _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishing_cover_of_spans
end
-- END ToricSectionLinearSystems
end

section
-- BEGIN ToricSectionLinearCharts



/-! # Genuine projective charts at linear combinations of sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι κ : Type u}

def sectionLinearGradedMap (c : ι→κ→₀k) :
    MvPolynomial.homogeneousSubmodule ι k →+*ᵍ
      MvPolynomial.homogeneousSubmodule κ k where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>sectionLinearForm k (c i))
  map_mem {i} {p} hp := by
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have hp' : p.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i p).mp hp
    simpa only [MvPolynomial.coe_eval₂Hom,one_mul] using
      hp'.eval₂ MvPolynomial.C (fun j=>sectionLinearForm k (c j))
        (MvPolynomial.isHomogeneous_C κ) (fun j=>sectionLinearForm_isHomogeneous k (c j))

@[simp] theorem sectionLinearGradedMap_X (c : ι→κ→₀k) (i : ι) :
    sectionLinearGradedMap k c (MvPolynomial.X i)=sectionLinearForm k (c i) := by
  simp [sectionLinearGradedMap]

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_linearForm_preimage (i : ι) (c : ι→₀k) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ
        C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  have he : unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (sectionLinearForm_isHomogeneous k c)))=
        C.ratioSection (Finsupp.linearCombination k s c) (s i) := by
    unfold HomogeneousLocalization.Away.isLocalizationElem
    rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
    simp only [pow_one]
    exact C.sectionRatioPolynomialMap_linearForm k s (s i) c
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (sectionLinearForm_isHomogeneous k c))
      (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

theorem sectionProjectiveMap_linearForm_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (c : ι→₀k) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_linearForm_preimage k s i c)
  have hpre' : C.sectionProjectiveChart k s i ⟨x,hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x,hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x,hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c)
  rw [hchart]
  exact hpre'

variable (den : Γ(C.sheaf,⊤)) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous 1)
    (hvalue : C.sectionProjectiveFieldMap k s p=C.toCartierData.sectionValue ⊤ den)

theorem sectionRatioPolynomialMap_eq_one
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    IsUnit (C.sectionRatioPolynomialMap k s den p) := hunit ▸ isUnit_one

def sectionLinearChartCoordinates
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p→+*
      Γ(X,C.nonvanishingOpen den) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den) p (hunit ▸ isUnit_one)

def sectionLinearChart
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    (C.nonvanishingOpen den).toScheme⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen den).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (C.sectionLinearChartCoordinates k s den p hunit)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) p
      ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)

theorem sectionLinearChart_generic
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    [Nonempty (C.nonvanishingOpen den)]
    (hη : genericPoint X∈C.nonvanishingOpen den) :
    (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionLinearChart k s den p hp hunit =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) p
        ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den) := by
  have hd := C.sectionValue_ne_zero_of_nonvanishing den
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (i : ι) := C.toCartierData.sectionValue ⊤ (s i)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den)
    (X.germToFunctionField (C.nonvanishingOpen den)).hom p (hunit ▸ isUnit_one)
  let E := MvPolynomial.eval₂Hom F
    (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i)
  have hEq : (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)=E :=
    C.sectionRatioPolynomialMap_germ k s den
  have hEp : E p=1 := by
    calc
      E p = (X.germToFunctionField (C.nonvanishingOpen den)).hom
          (C.sectionRatioPolynomialMap k s den p) :=
        congrArg (fun Q : MvPolynomial ι k→+*X.functionField => Q p) hEq.symm
      _ = 1 := by rw [hunit,map_one]
  have hEi : IsUnit (E p) := hEp ▸ isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k→+*X.functionField)
      (hF : F₁=F₂) (h₁ : IsUnit (F₁ p)) (h₂ : IsUnit (F₂ p)) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₁ p h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₂ p h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans (heval _ E hEq _ hEi)
  unfold sectionLinearChart sectionLinearChartCoordinates
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i))
      p ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (C.toCartierData.sectionValue ⊤ den)⁻¹
    (inv_ne_zero hd) p hp (by decide) (by
      change C.sectionProjectiveFieldMap k s p≠0
      exact hvalue.symm ▸ hd)

include hvalue in
theorem sectionLinearChart_eq
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionLinearChart k s den p hp hunit=
      (C.nonvanishingOpen den).ι ≫ C.sectionProjectiveMap k s hcover := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    have hη := genericPoint_mem_open X (C.nonvanishingOpen den)
    let η := (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη
    letI : IsDominant η := genericStalkMapToOpen_isDominant _ hη
    have hηcover : genericPoint X∈⨆ i,C.nonvanishingOpen (s i) := by
      rw [hcover]; trivial
    obtain ⟨i,hηi⟩ := Opens.mem_iSup.mp hηcover
    letI : Nonempty (C.nonvanishingOpen (s i)) := ⟨⟨genericPoint X,hηi⟩⟩
    apply ext_of_isDominant η
    rw [C.sectionLinearChart_generic k s den p hp hvalue hunit hη,
      ← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_ι,
      C.sectionProjectiveMap_generic k s hcover i]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      p (MvPolynomial.X i) ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp)
      (polynomialVariable_mem_degreeOne k i)
      (by decide) (by decide)
      (by exact hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den)
      (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
        C.sectionValue_ne_zero_of_nonvanishing (s i))
  · letI : IsEmpty (C.nonvanishingOpen den) := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionLinearChart_eq
end
-- END ToricSectionLinearCharts
end

section
-- BEGIN ToricSectionSpanningEmbedding



/-!
# Replacing an embedding system by a finite spanning character system

The old affine coordinate ring is a quotient of its homogeneous chart.
A genuine graded substitution sends every old coordinate to its linear
combination of new coordinates. The resulting map of homogeneous
localizations proves that every old affine coordinate generator remains
available. Thus the replacement preserves the actual closed immersion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (c : ι→κ→₀k) (hc : ∀ i,Finsupp.linearCombination k t (c i)=s i)

include hc in
theorem sectionLinearSubstitution_ratioMap (i : ι) :
    (C.sectionRatioPolynomialMap k t (s i)).comp
        (sectionLinearGradedMap k c).toRingHom=
      C.sectionProjectiveChartRingMap k s i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionLinearGradedMap,MvPolynomial.eval₂Hom_C,
      sectionRatioPolynomialMap,sectionProjectiveChartRingMap]
  · intro j
    change C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X j)) =
        C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)
    rw [sectionLinearGradedMap_X k c j,
      C.sectionRatioPolynomialMap_linearForm k t (s i) (c j),hc j]
    exact (C.sectionProjectiveChartRingMap_X k s i j).symm

include hc in
theorem sectionLinearSubstitution_unit (i : ι) :
    C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))=1 := by
  change ((C.sectionRatioPolynomialMap k t (s i)).comp
    (sectionLinearGradedMap k c).toRingHom) (MvPolynomial.X i)=1
  rw [C.sectionLinearSubstitution_ratioMap k s t c hc]
  exact C.sectionProjectiveChartRingMap_self k s i

include hc in
theorem sectionLinearSubstitution_fieldValue (i : ι) :
    C.sectionProjectiveFieldMap k t
      (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.toCartierData.sectionValue ⊤ (s i) := by
  rw [sectionLinearGradedMap_X k c i,C.sectionLinearForm_fieldValue k t (c i),hc i]

theorem sectionLinearSubstitution_chartCoordinates (i : ι) :
    (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
      (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
        (MvPolynomial.X i))=
      C.sectionProjectiveChartCoordinates k s i := by
  ext z
  obtain ⟨m,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule ι k) (polynomialVariable_mem_degreeOne k i) z
  rw [RingHom.comp_apply,HomogeneousLocalization.Away.map_mk]
  unfold sectionLinearChartCoordinates sectionProjectiveChartCoordinates
  rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionLinearSubstitution_unit k s t c hc i),
    unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
  exact congrArg (fun F=>F p) (C.sectionLinearSubstitution_ratioMap k s t c hc i)

theorem sectionLinearSubstitution_chartCoordinates_surjective (i : ι)
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    Function.Surjective (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)) := by
  apply Function.Surjective.of_comp
    (g := HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
      (MvPolynomial.X i))
  change Function.Surjective
    ((C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
        (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
          (MvPolynomial.X i)))
  rw [C.sectionLinearSubstitution_chartCoordinates k s t c hc i]
  exact hgen

include hc in
theorem sectionLinearSubstitution_localPreimmersion
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι)
    (ha : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion ((C.nonvanishingOpen (s i)).ι ≫
      C.sectionProjectiveMap k t hnew) := by
  let p := sectionLinearGradedMap k c (MvPolynomial.X i)
  have hp : p.IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 p).mp
      ((sectionLinearGradedMap k c).map_mem (polynomialVariable_mem_degreeOne k i))
  have hunit := C.sectionLinearSubstitution_unit k s t c hc i
  rw [← C.sectionLinearChart_eq k t (s i) p hp
    (C.sectionLinearSubstitution_fieldValue k s t c hc i) hunit hnew]
  letI : IsAffine (C.nonvanishingOpen (s i)) := ha
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← ha.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (C.sectionLinearChartCoordinates k t (s i) p hunit))) :=
    IsClosedImmersion.spec_of_surjective _
      (C.sectionLinearSubstitution_chartCoordinates_surjective k s t c hc i hgen)
  let q := Spec.map (CommRingCat.ofHom
    (C.sectionLinearChartCoordinates k t (s i) p hunit))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule κ k) p
    ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

include hc in
theorem sectionLinearSubstitution_preimage
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι) :
    C.sectionProjectiveMap k t hnew ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
        (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.nonvanishingOpen (s i) := by
  rw [sectionLinearGradedMap_X k c i,
    C.sectionProjectiveMap_linearForm_preimage k t hnew (c i),hc i]

include hc in
/-- A spanning replacement of a genuine embedding system remains a
genuine closed immersion, including when the new sections are characters. -/
theorem sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤)
    {α : Type u} (chooseChart : α→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k t hnew) := by
  let f := C.sectionProjectiveMap k t hnew
  let U (i : α) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : α) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
    (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
  have hlocal (i : α) : IsPreimmersion ((U i).ι ≫ f) :=
    C.sectionLinearSubstitution_localPreimmersion k s t c hc hnew
      (chooseChart i) (ha i) (hgen i)
  letI : SurjectiveOnStalks f := IsZariskiLocalAtSource.of_iSup_eq_top U hchosen
    (fun i=>by letI := hlocal i; infer_instance)
  letI : IsPreimmersion f := by
    refine { isEmbedding := ?_ }
    apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
      (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
    · rintro y ⟨x,rfl⟩
      have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
      obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
      apply Opens.mem_iSup.mpr
      refine ⟨i,?_⟩
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      change x∈C.sectionProjectiveMap k t hnew ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
          (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
      rw [hp]
      exact hxi
    · exact fun i=>(U i).ι.continuous
    · intro i x hx
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      have hxi : x∈U i := by
        change x∈C.nonvanishingOpen (s (chooseChart i))
        rw [← hp]
        exact hx
      exact ⟨⟨x,hxi⟩,rfl⟩
    · intro i
      letI := hlocal i
      exact ((U i).ι ≫ f).isEmbedding
  letI : IsProper f := C.sectionProjectiveMap_isProper k t hnew
  change IsClosedImmersion f
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
end
-- END ToricSectionSpanningEmbedding
end

end
