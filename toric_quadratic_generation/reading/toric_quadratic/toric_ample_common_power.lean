module

public import PaperVerification.ToricAmpleDenominators

@[expose] public section

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
