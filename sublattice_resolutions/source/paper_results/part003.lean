module
public import graph_foundation.part005
public import shared_results.part002
public import paper_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.HibiAlgebraDimension -/
section

/-!
# The actual Hibi monomial algebra has dimension h+1

The upper bound is an actual algebra embedding into h+1 polynomial
variables. The lower bound comes from the bottom and the saturated maximal
chain; injectivity is proved by recovering every exponent from successive
tail sums. The dimension conclusion is Mathlib's prime-spectrum Krull
dimension, not a renamed exponent-rank invariant.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FiniteDistributive

open Classical MvPolynomial

variable (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L]

def hibiExponent (a : L) : Option (Irreducible L) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun o =>
    match o with
    | none => 1
    | some p => if p.val ≤ a then 1 else 0

@[simp] theorem hibiExponent_none (a : L) : hibiExponent L a none=1 := rfl
@[simp] theorem hibiExponent_some (a : L) (p : Irreducible L) :
    hibiExponent L a (some p) = if p.val ≤ a then 1 else 0 := rfl

theorem le_maximalChain_iff (p : Irreducible L) (j : Fin (height L+1)) :
    p.val ≤ maximalChain L j ↔ (position L p).val<j.val := by
  change p ∈ OrderIso.lowerSetSupIrred
    (OrderIso.lowerSetSupIrred.symm (initialIdeal L j)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

def hibiExponentMap : (L →₀ ℕ) →+ (Option (Irreducible L) →₀ ℕ) :=
  Finsupp.weight (hibiExponent L)

def maximalChainExponentMap : (Fin (height L+1) →₀ ℕ) →+ (Option (Irreducible L) →₀ ℕ) :=
  Finsupp.weight fun j => hibiExponent L (maximalChain L j)

def tailSum {m : ℕ} (b : Fin m →₀ ℕ) (t : ℕ) : ℕ :=
  ∑ j, if t≤j.val then b j else 0

theorem tailSum_zero {m : ℕ} (b : Fin m →₀ ℕ) : tailSum b 0 = ∑ j, b j := by
  simp only [tailSum,Nat.zero_le,if_true]

theorem tailSum_terminal {m : ℕ} (b : Fin m →₀ ℕ) : tailSum b m=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact if_neg (Nat.not_le.mpr j.isLt)

theorem tailSum_step {m : ℕ} (b : Fin m →₀ ℕ) (i : Fin m) :
    tailSum b i.val = b i+tailSum b (i.val+1) := by
  have hterm : ∀ j : Fin m,
      (if i.val≤j.val then b j else 0) =
        (if j=i then b i else 0)+(if i.val+1≤j.val then b j else 0) := by
    intro j
    by_cases hji : j=i
    · subst j
      simp only [le_refl,if_true,Nat.not_succ_le_self,if_false,add_zero]
    · have hval : j.val≠i.val := fun h => hji (Fin.ext h)
      by_cases hij : i.val<j.val
      · simp only [if_pos (Nat.le_of_lt hij),if_neg hji,if_pos (Nat.succ_le_of_lt hij),zero_add]
      · have hlt : j.val < i.val := by omega
        simp only [if_neg (Nat.not_le.mpr hlt),if_neg hji,
          if_neg (by omega : ¬i.val+1≤j.val),zero_add]
  simp_rw [tailSum,hterm]
  rw [Finset.sum_add_distrib,Finset.sum_ite_eq']
  simp only [Finset.mem_univ,if_true]

@[simp] theorem maximalChainExponentMap_none (b : Fin (height L+1) →₀ ℕ) :
    maximalChainExponentMap L b none=tailSum b 0 := by
  simp only [maximalChainExponentMap,Finsupp.weight_eq_sum,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,hibiExponent_none,nsmul_eq_mul,mul_one,tailSum_zero,Nat.cast_id]

@[simp] theorem maximalChainExponentMap_some (b : Fin (height L+1) →₀ ℕ)
    (p : Irreducible L) :
    maximalChainExponentMap L b (some p)=tailSum b ((position L p).val+1) := by
  simp only [maximalChainExponentMap,Finsupp.weight_eq_sum,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,hibiExponent_some,le_maximalChain_iff,nsmul_eq_mul,tailSum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (position L p).val<j.val
  · simp only [if_pos h,mul_one,if_pos (Nat.succ_le_of_lt h),Nat.cast_id]
  · simp only [if_neg h,mul_zero,if_neg (by omega : ¬(position L p).val+1≤j.val)]

theorem maximalChainExponentMap_injective : Function.Injective (maximalChainExponentMap L) := by
  intro b c he
  have ht : ∀ t≤height L+1, tailSum b t=tailSum c t := by
    intro t ht
    rcases t with _ | t
    · simpa only [maximalChainExponentMap_none] using congrArg (fun f => f none) he
    · by_cases hlast : t=height L
      · subst t
        rw [tailSum_terminal,tailSum_terminal]
      · have hlt : t<height L := by omega
        have hh := congrArg (fun f => f (some (enumeration L ⟨t,hlt⟩))) he
        simpa only [maximalChainExponentMap_some,position_enumeration] using hh
  ext i
  have h₁ := ht i.val (by omega)
  have h₂ := ht (i.val+1) (Nat.succ_le_of_lt i.isLt)
  rw [tailSum_step,tailSum_step] at h₁
  omega

section Ring
variable (k : Type*) [CommRing k]

def hibiPresentation : MvPolynomial L k →ₐ[k] MvPolynomial (Option (Irreducible L)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (hibiExponentMap L)

def hibiAlgebra : Subalgebra k (MvPolynomial (Option (Irreducible L)) k) :=
  (hibiPresentation L k).range

instance hibiAlgebra_finiteType : Algebra.FiniteType k (hibiAlgebra L k) :=
  Algebra.FiniteType.of_surjective (hibiPresentation L k).rangeRestrict
    (hibiPresentation L k).rangeRestrict_surjective

def maximalChainPolynomialMap :
    MvPolynomial (Fin (height L+1)) k →ₐ[k] MvPolynomial (Option (Irreducible L)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (maximalChainExponentMap L)

theorem maximalChainPolynomialMap_injective : Function.Injective (maximalChainPolynomialMap L k) :=
  AddMonoidAlgebra.mapDomain_injective (maximalChainExponentMap_injective L)

def maximalChainHibiMap : MvPolynomial (Fin (height L+1)) k →ₐ[k] hibiAlgebra L k :=
  (hibiPresentation L k).rangeRestrict.comp (MvPolynomial.rename (maximalChain L))

theorem maximalChainHibiMap_val (f : MvPolynomial (Fin (height L+1)) k) :
    (maximalChainHibiMap L k f).val=maximalChainPolynomialMap L k f := by
  have he : (Subalgebra.val (hibiAlgebra L k)).comp (maximalChainHibiMap L k) =
      maximalChainPolynomialMap L k := by
    apply MvPolynomial.algHom_ext
    intro j
    change (hibiPresentation L k) (MvPolynomial.rename (maximalChain L) (X j)) =
      maximalChainPolynomialMap L k (X j)
    rw [MvPolynomial.rename_X]
    change AddMonoidAlgebra.mapDomainAlgHom k k (Finsupp.weight (hibiExponent L))
      (AddMonoidAlgebra.single (Finsupp.single (maximalChain L j) 1) (1 : k)) =
        AddMonoidAlgebra.mapDomainAlgHom k k
          (Finsupp.weight fun i => hibiExponent L (maximalChain L i))
            (AddMonoidAlgebra.single (Finsupp.single j 1) (1 : k))
    simp only [AddMonoidAlgebra.mapDomainAlgHom_apply,AddMonoidAlgebra.mapDomain_single,
      Finsupp.weight_single,one_smul]
  exact AlgHom.congr_fun he f

theorem maximalChainHibiMap_injective : Function.Injective (maximalChainHibiMap L k) := by
  intro f g he
  apply maximalChainPolynomialMap_injective L k
  simpa only [maximalChainHibiMap_val] using congrArg Subtype.val he

end Ring

variable (k : Type*) [Field k]

theorem hibiAlgebra_trdeg :
    Algebra.trdeg k (hibiAlgebra L k)=((height L+1 : ℕ) : Cardinal) := by
  have hlo := lift_trdeg_le_of_injective (maximalChainHibiMap L k)
    (maximalChainHibiMap_injective L k)
  have hhi := lift_trdeg_le_of_injective (Subalgebra.val (hibiAlgebra L k))
    Subtype.val_injective
  simp only [MvPolynomial.trdeg_of_isDomain,Cardinal.mk_fintype,Fintype.card_fin,
    Fintype.card_option,Cardinal.lift_natCast,height] at hlo hhi ⊢
  apply le_antisymm
  · apply Cardinal.lift_le.mp
    simpa only [Cardinal.lift_natCast] using hhi
  · apply Cardinal.lift_le.mp
    simpa only [Cardinal.lift_natCast] using hlo

/-- The actual prime-spectrum dimension needed for analytic spread. The
remaining application is the explicit identification of the special fiber
of the row ideal with this monomial algebra. -/
theorem hibiAlgebra_ringKrullDim :
    ringKrullDim (hibiAlgebra L k)=((height L+1 : ℕ) : WithBot ℕ∞) := by
  exact FourPapers.ringKrullDim_eq_nat_of_trdeg (hibiAlgebra_trdeg L k)

end FourPapers.FiniteDistributive

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.MonoidImageAlgebra -/
section

/-! # Monoid images and their actual monomial algebra images -/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers
open Classical
variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  (k : Type*) [CommRing k] (f : M →+ N)

theorem monoidImage_mapDomain_surjective :
    Function.Surjective (AddMonoidAlgebra.mapDomainAlgHom k k f.mrangeRestrict) := by
  intro x
  obtain ⟨y,hy⟩ := Finsupp.mapDomain_surjective f.mrangeRestrict_surjective x.coeff
  exact ⟨AddMonoidAlgebra.ofCoeff y,congrArg AddMonoidAlgebra.ofCoeff hy⟩

theorem monoidImage_algebraRange :
    (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.mrange f).subtype).range =
      (AddMonoidAlgebra.mapDomainAlgHom k k f).range := by
  have he : (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.mrange f).subtype).comp
      (AddMonoidAlgebra.mapDomainAlgHom k k f.mrangeRestrict)=
        AddMonoidAlgebra.mapDomainAlgHom k k f := by
    rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
    rfl
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := monoidImage_mapDomain_surjective k f y
    exact ⟨z,(AlgHom.congr_fun he z).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨AddMonoidAlgebra.mapDomainAlgHom k k f.mrangeRestrict z,
      AlgHom.congr_fun he z⟩

def monoidImageAlgebraEquiv : AddMonoidAlgebra k (AddMonoidHom.mrange f) ≃ₐ[k]
    (AddMonoidAlgebra.mapDomainAlgHom k k f).range :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.mrange f).subtype)
    (AddMonoidAlgebra.mapDomain_injective Subtype.val_injective)).trans
      (Subalgebra.equivOfEq _ _ (monoidImage_algebraRange k f))

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.HibiOrderCone -/
section

/-! # The actual Hibi exponent monoid is the integral order cone -/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.FiniteDistributive
open Classical
variable (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L]

def orderCone : AddSubmonoid (Option (Irreducible L) →₀ ℕ) where
  carrier := {a | (∀ p,a (some p)≤a none) ∧
    ∀ p q : Irreducible L,p≤q → a (some q)≤a (some p)}
  zero_mem' := ⟨fun _ => le_rfl,fun _ _ _ => le_rfl⟩
  add_mem' ha hb := ⟨fun p => add_le_add (ha.1 p) (hb.1 p),
    fun p q hpq => add_le_add (ha.2 p q hpq) (hb.2 p q hpq)⟩

def orderConePoint (a : orderCone L) : OrderPoint L (a.val none) :=
  ⟨fun p => ⟨a.val (some p),Nat.lt_succ_of_le (a.property.1 p)⟩,
    fun _ _ hpq => a.property.2 _ _ hpq⟩

def orderPointCone (m : ℕ) (f : OrderPoint L m) : orderCone L :=
  ⟨Finsupp.equivFunOnFinite.symm (fun o => match o with
    | none => m
    | some p => (f.val p).val),
      ⟨fun p => Nat.le_of_lt_succ (f.val p).isLt,
        fun _ _ hpq => f.property hpq⟩⟩

@[simp] theorem orderPointCone_none (m : ℕ) (f : OrderPoint L m) :
    (orderPointCone L m f).val none=m := rfl

@[simp] theorem orderConePoint_pointCone (m : ℕ) (f : OrderPoint L m) :
    orderConePoint L (orderPointCone L m f)=f := by
  apply Subtype.ext
  funext p
  apply Fin.ext
  rfl

@[simp] theorem orderPointCone_conePoint (a : orderCone L) :
    orderPointCone L (a.val none) (orderConePoint L a)=a := by
  apply Subtype.ext
  ext o
  cases o <;> rfl

theorem hibiExponent_mem_orderCone (a : L) : hibiExponent L a∈orderCone L := by
  constructor
  · intro p
    simp only [hibiExponent_some,hibiExponent_none]
    split_ifs <;> omega
  · intro p q hpq
    simp only [hibiExponent_some]
    by_cases hq : q.val≤a
    · simp only [if_pos hq,if_pos ((show p.val ≤ q.val from hpq).trans hq),le_refl]
    · simp only [if_neg hq,Nat.zero_le]

theorem hibiExponentMap_mem_orderCone (t : L →₀ ℕ) :
    hibiExponentMap L t∈orderCone L := by
  rw [hibiExponentMap,Finsupp.weight_eq_sum]
  apply AddSubmonoid.sum_mem
  intro a ha
  exact (orderCone L).nsmul_mem (hibiExponent_mem_orderCone L a) (t a)

def orderPointPresentation (m : ℕ) (f : OrderPoint L m) : L →₀ ℕ :=
  ∑ s : Fin m,Finsupp.single ((pointChain L m f).val s) 1

theorem orderPointPresentation_image (m : ℕ) (f : OrderPoint L m) :
    hibiExponentMap L (orderPointPresentation L m f) =
      Finsupp.equivFunOnFinite.symm (fun o => match o with
        | none => m
        | some p => (f.val p).val) := by
  ext o
  rw [orderPointPresentation,map_sum]
  simp only [hibiExponentMap,Finsupp.weight_single,one_smul,Finsupp.finsetSum_apply]
  cases o with
  | none => simp [hibiExponent_none,Finsupp.coe_equivFunOnFinite_symm]
  | some p =>
      have he := congrArg (fun q : OrderPoint L m => (q.val p).val)
        (chainPoint_pointChain L m f)
      simpa only [chainPoint,Finset.card_filter,hibiExponent_some,
        Finsupp.coe_equivFunOnFinite_symm] using he

theorem orderCone_eq_hibiRange : orderCone L=AddMonoidHom.mrange (hibiExponentMap L) := by
  apply le_antisymm
  · intro a ha
    refine ⟨orderPointPresentation L (a none) (orderConePoint L ⟨a,ha⟩),?_⟩
    rw [orderPointPresentation_image]
    ext o
    cases o <;> rfl
  · rintro a ⟨t,rfl⟩
    exact hibiExponentMap_mem_orderCone L t

def orderConeHibiMonoidEquiv : orderCone L ≃+ AddMonoidHom.mrange (hibiExponentMap L) where
  toFun a := ⟨a.val,(orderCone_eq_hibiRange L) ▸ a.property⟩
  invFun a := ⟨a.val,(orderCone_eq_hibiRange L).symm ▸ a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def orderConeHibiAlgebraEquiv (k : Type*) [CommRing k] :
    AddMonoidAlgebra k (orderCone L) ≃ₐ[k] hibiAlgebra L k :=
  (AddMonoidAlgebra.domCongr k k (orderConeHibiMonoidEquiv L)).trans
    (FourPapers.monoidImageAlgebraEquiv k (hibiExponentMap L))

end FourPapers.FiniteDistributive

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CoefficientLineSum -/
section

/-! # The actual direct sum of zero-or-one coefficient lines -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.CoefficientLineSum
open Classical DirectSum
variable {k I : Type*} [CommRing k] [Fintype I] (P : I→Prop)

def line (i : I) : Submodule k k := if P i then ⊤ else ⊥

theorem val_zero (i : I) (hi : ¬P i) (x : line (k:=k) P i) : x.val=0 := by
  have hx := x.property
  simpa only [line,if_neg hi,Submodule.mem_bot] using hx

def equivalence : (⨁i,line (k:=k) P i) ≃ₗ[k] (Subtype P →₀ k) where
  toFun x := Finsupp.equivFunOnFinite.symm (fun i : Subtype P => (x i.val).val)
  invFun y := DFinsupp.equivFunOnFintype.symm (fun i =>
    ⟨if hi : P i then y ⟨i,hi⟩ else 0,by
      by_cases hi : P i
      · simp only [line,if_pos hi,dif_pos hi,Submodule.mem_top]
      · simp only [line,if_neg hi,dif_neg hi,Submodule.zero_mem]⟩)
  left_inv x := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    by_cases hi : P i
    · change (if hi : P i then (x i).val else 0)=(x i).val
      rw [dif_pos hi]
    · change (if hi : P i then (x i).val else 0)=(x i).val
      rw [dif_neg hi,val_zero P i hi]
  right_inv y := by
    ext i
    change (if hi : P i.val then y ⟨i.val,hi⟩ else 0)=y i
    rw [dif_pos i.property]
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl

@[simp] theorem equivalence_apply (x : ⨁i,line (k:=k) P i) (i : Subtype P) :
    equivalence P x i=(x i.val).val := rfl

theorem equivalence_lof (i : I) (x : line (k:=k) P i) :
    equivalence P (DirectSum.lof k I (fun i => ↥(line (k := k) P i)) i x)=
      if hi : P i then Finsupp.single ⟨i,hi⟩ x.val else 0 := by
  ext j
  rw [equivalence_apply]
  by_cases hi : P i
  · rw [dif_pos hi]
    by_cases hij : i=j.val
    · subst i
      simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same,Finsupp.single_apply,Subtype.ext_iff,if_true]
    · simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij),
        ZeroMemClass.coe_zero,Finsupp.single_apply,Subtype.ext_iff,if_neg hij]
  · rw [dif_neg hi]
    have hij : i≠j.val := fun h=>hi (h.symm ▸ j.property)
    simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij),
      ZeroMemClass.coe_zero,Finsupp.zero_apply]

end FourPapers.CoefficientLineSum

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RP2Matrices -/
section

/-! Explicit integer change-of-basis certificates for the six-vertex complex.
Generated by scripts/generate_rp2_matrices.py. The displayed matrix
identities are proved by closed `decide` terms. -/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace FourPapers.Sublattice.RP2Matrices

def D1 : Matrix (Fin 1) (Fin 6) ℤ :=
  ![![1, 1, 1, 1, 1, 1]]

def D2 : Matrix (Fin 6) (Fin 15) ℤ :=
  ![![-1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, -1, 0],
  ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1]]

def D3 : Matrix (Fin 15) (Fin 10) ℤ :=
  ![![1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, -1, -1, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
  ![0, 0, 0, 0, 0, -1, 0, -1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 1, 0, 0, 0, 0, 0, -1, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0]]

def T1 : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![1, -1, -1, -1, -1, -1],
  ![0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 1]]

def T2 : Matrix (Fin 15) (Fin 15) ℤ :=
  ![![1, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, -1, 0, 0, 1, 0, 1, -1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 1, 1, 0, -1],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0]]

def T3 : Matrix (Fin 10) (Fin 10) ℤ :=
  ![![1, 0, 0, -1, 0, 0, 1, 0, 0, -1],
  ![0, 1, -1, 0, 0, 0, -1, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 1, 0, 0, -1, 0, 0, 1],
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def R1 : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![1, 1, 1, 1, 1, 1],
  ![0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 1]]

def R2 : Matrix (Fin 15) (Fin 15) ℤ :=
  ![![1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, -1, 0],
  ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 0, -1, -1, 0, 0]]

def R3 : Matrix (Fin 10) (Fin 10) ℤ :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def N1 : Matrix (Fin 1) (Fin 6) ℤ :=
  ![![1, 0, 0, 0, 0, 0]]

def N2 : Matrix (Fin 6) (Fin 15) ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def N3 : Matrix (Fin 15) (Fin 10) ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2]]

theorem R1_T1 : R1 * T1=1 := by decide
theorem T1_R1 : T1 * R1=1 := by decide

theorem R2_T2 : R2 * T2=1 := by decide
theorem T2_R2 : T2 * R2=1 := by decide

theorem R3_T3 : R3 * T3=1 := by decide
theorem T3_R3 : T3 * R3=1 := by decide

theorem normal1 : D1*T1=N1 := by decide

theorem normal2 : R1*D2*T2=N2 := by decide

theorem normal3 : R2*D3*T3=N3 := by decide

theorem D1_D2 : D1*D2=0 := by decide

theorem D2_D3 : D2*D3=0 := by decide

end FourPapers.Sublattice.RP2Matrices

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceSublattice -/
section

/-!
# The actual two-stage incidence sublattice of Section 10

An incidence coordinate remembers one left and one right endpoint. Lower
vertices take values zero and one; upper vertices take values one and two.
The image is a sublattice, and surjectivity of the two endpoint maps gives
the exact cardinality 2^|L| + 2^|R| - 1. The final specialization is the
30-coordinate, 1087-element lattice used in Proposition 10.2.

These declarations establish the lattice construction only. The integral
homology realization in Lemma 10.1 and Proposition 10.2 is a separate
obligation, not an assumption or a conclusion of this module.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.Sublattice
open Classical

variable {L R T : Type*} [Fintype L] [Fintype R] [Fintype T]
  [DecidableEq L] [DecidableEq R]

def incidenceLower (left : T → L) (D : Finset L) : T → Fin 3 :=
  fun e => if left e ∈ D then 1 else 0

def incidenceUpper (right : T → R) (F : Finset R) : T → Fin 3 :=
  fun e => if right e ∈ F then 2 else 1

def incidenceLowerStage (left : T → L) : Finset (T → Fin 3) :=
  Finset.univ.image (incidenceLower left)

def incidenceUpperStage (right : T → R) : Finset (T → Fin 3) :=
  Finset.univ.image (incidenceUpper right)

def incidenceSublattice (left : T → L) (right : T → R) : Finset (T → Fin 3) :=
  incidenceLowerStage left ∪ incidenceUpperStage right

@[simp] lemma incidenceLower_inter (left : T → L) (D E : Finset L) :
    incidenceLower left (D ∩ E) = incidenceLower left D ⊓ incidenceLower left E := by
  funext e
  by_cases hd : left e ∈ D <;> by_cases he : left e ∈ E <;>
    simp [incidenceLower, hd, he]

@[simp] lemma incidenceLower_union (left : T → L) (D E : Finset L) :
    incidenceLower left (D ∪ E) = incidenceLower left D ⊔ incidenceLower left E := by
  funext e
  by_cases hd : left e ∈ D <;> by_cases he : left e ∈ E <;>
    simp [incidenceLower, hd, he]

@[simp] lemma incidenceUpper_inter (right : T → R) (D E : Finset R) :
    incidenceUpper right (D ∩ E) = incidenceUpper right D ⊓ incidenceUpper right E := by
  funext e
  by_cases hd : right e ∈ D <;> by_cases he : right e ∈ E <;>
    simp [incidenceUpper, hd, he]

@[simp] lemma incidenceUpper_union (right : T → R) (D E : Finset R) :
    incidenceUpper right (D ∪ E) = incidenceUpper right D ⊔ incidenceUpper right E := by
  funext e
  by_cases hd : right e ∈ D <;> by_cases he : right e ∈ E <;>
    simp [incidenceUpper, hd, he]

lemma incidenceLower_le_upper (left : T → L) (right : T → R)
    (D : Finset L) (F : Finset R) : incidenceLower left D ≤ incidenceUpper right F := by
  intro e
  by_cases hd : left e ∈ D <;> by_cases hf : right e ∈ F <;>
    simp [incidenceLower, incidenceUpper, hd, hf]

theorem incidenceSublattice_closed (left : T → L) (right : T → R) :
    (∀ a ∈ incidenceSublattice left right, ∀ b ∈ incidenceSublattice left right,
      a ⊓ b ∈ incidenceSublattice left right) ∧
    (∀ a ∈ incidenceSublattice left right, ∀ b ∈ incidenceSublattice left right,
      a ⊔ b ∈ incidenceSublattice left right) := by
  constructor <;> intro a ha b hb
  · rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨D ∩ E,Finset.mem_univ _,incidenceLower_inter left D E⟩)
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hb
      rw [inf_eq_left.mpr (incidenceLower_le_upper left right D F)]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩)
    · obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hb
      rw [inf_eq_right.mpr (incidenceLower_le_upper left right D F)]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩)
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨D ∩ E,Finset.mem_univ _,incidenceUpper_inter right D E⟩)
  · rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨D ∪ E,Finset.mem_univ _,incidenceLower_union left D E⟩)
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hb
      rw [sup_eq_right.mpr (incidenceLower_le_upper left right D F)]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨F,Finset.mem_univ _,rfl⟩)
    · obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hb
      rw [sup_eq_left.mpr (incidenceLower_le_upper left right D F)]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨F,Finset.mem_univ _,rfl⟩)
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨D ∪ E,Finset.mem_univ _,incidenceUpper_union right D E⟩)

theorem incidenceLower_injective (left : T → L) (hl : Function.Surjective left) :
    Function.Injective (incidenceLower left) := by
  intro D E he
  apply Finset.ext
  intro a
  obtain ⟨e,rfl⟩ := hl a
  have hh := congrFun he e
  by_cases hd : left e ∈ D <;> by_cases he : left e ∈ E <;>
    simp_all [incidenceLower]

theorem incidenceUpper_injective (right : T → R) (hr : Function.Surjective right) :
    Function.Injective (incidenceUpper right) := by
  intro D E he
  apply Finset.ext
  intro a
  obtain ⟨e,rfl⟩ := hr a
  have hh := congrFun he e
  by_cases hd : right e ∈ D <;> by_cases he : right e ∈ E <;>
    simp_all [incidenceUpper]

theorem incidenceStages_inter (left : T → L) (right : T → R) :
    incidenceLowerStage left ∩ incidenceUpperStage right = {fun _ : T => (1 : Fin 3)} := by
  ext a
  constructor
  · intro ha
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp ha
    obtain ⟨D,_,hD⟩ := Finset.mem_image.mp ha
    obtain ⟨F,_,hF⟩ := Finset.mem_image.mp hb
    apply Finset.mem_singleton.mpr
    funext e
    have hh := congrFun (hD.trans hF.symm) e
    have hval := congrFun hD e
    by_cases hd : left e ∈ D <;> by_cases hf : right e ∈ F <;>
      simp_all [incidenceLower,incidenceUpper]
  · intro ha
    obtain rfl := Finset.mem_singleton.mp ha
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨Finset.univ,Finset.mem_univ _,by
        funext e; simp [incidenceLower]⟩
    · exact Finset.mem_image.mpr ⟨∅,Finset.mem_univ _,by
        funext e; simp [incidenceUpper]⟩

theorem incidenceSublattice_card (left : T → L) (right : T → R)
    (hl : Function.Surjective left) (hr : Function.Surjective right) :
    (incidenceSublattice left right).card = 2 ^ Fintype.card L + 2 ^ Fintype.card R - 1 := by
  have hL : (incidenceLowerStage left).card = 2 ^ Fintype.card L := by
    rw [incidenceLowerStage, Finset.card_image_of_injective _ (incidenceLower_injective left hl)]
    simp
  have hR : (incidenceUpperStage right).card = 2 ^ Fintype.card R := by
    rw [incidenceUpperStage, Finset.card_image_of_injective _ (incidenceUpper_injective right hr)]
    simp
  have hc := Finset.card_union_add_card_inter
    (incidenceLowerStage left) (incidenceUpperStage right)
  rw [incidenceStages_inter, Finset.card_singleton, hL, hR] at hc
  unfold incidenceSublattice
  omega

/-- The ten minimal nonfaces, in the manuscript's order, with vertex
labels reduced by one to inhabit Fin 6. -/
def projectivePlaneIncidenceRight : Fin 30 → Fin 6 :=
  ![0,1,4, 0,1,5, 0,2,3, 0,2,5, 0,3,4,
    1,2,3, 1,2,4, 1,3,5, 2,4,5, 3,4,5]

def projectivePlaneIncidenceLeft (e : Fin 30) : Fin 10 :=
  ⟨e.val / 3, by omega⟩

lemma projectivePlaneIncidenceLeft_surjective :
    Function.Surjective projectivePlaneIncidenceLeft := by decide

lemma projectivePlaneIncidenceRight_surjective :
    Function.Surjective projectivePlaneIncidenceRight := by decide

def projectivePlaneSublattice : Finset (FiniteTuple (fun _ : Fin 30 => 3)) :=
  incidenceSublattice projectivePlaneIncidenceLeft projectivePlaneIncidenceRight

theorem projectivePlaneSublattice_closed :
    finiteLatticeClosed (fun _ : Fin 30 => 3) projectivePlaneSublattice :=
  incidenceSublattice_closed projectivePlaneIncidenceLeft projectivePlaneIncidenceRight

theorem projectivePlaneSublattice_card : projectivePlaneSublattice.card = 1087 := by
  rw [projectivePlaneSublattice, incidenceSublattice_card _ _
    projectivePlaneIncidenceLeft_surjective projectivePlaneIncidenceRight_surjective]
  norm_num

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceTopColon -/
section

/-! # The exact top predecessor colon of the incidence sublattice

The generators are computed in the actual finite row ring. The lower
stage contributes every product choosing its complete zero block or its
complete one block at each left vertex; the upper stage contributes the
one blocks at the right vertices. This is an equality with the literal
ideal colon, not an additional assumption on a combinatorial model.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {M : ℕ} (left : Fin M → L) (right : Fin M → R)

abbrev IncidenceRows (M : ℕ) : Fin M → ℕ := fun _ => 3
def incidenceTop : FiniteTuple (IncidenceRows M) := fun _ => 2

theorem incidenceTop_mem :
    incidenceTop (M := M) ∈ incidenceSublattice left right := by
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨Finset.univ,Finset.mem_univ _,?_⟩
  funext e
  simp [incidenceUpper,incidenceTop]

def incidenceRowRightExponent (r : R) : Exponent (FiniteVariable.{u} (IncidenceRows M)) :=
  Finsupp.equivFunOnFinite.symm fun v => if right v.1 = r ∧ v.2.down = 1 then 1 else 0

@[simp] theorem incidenceRowRightExponent_apply (r : R)
    (v : FiniteVariable.{u} (IncidenceRows M)) :
    incidenceRowRightExponent right r v = if right v.1 = r ∧ v.2.down = 1 then 1 else 0 := rfl

def incidenceTopFamily : Family (FiniteVariable.{u} (IncidenceRows M)) :=
  (Finset.univ.image fun D : Finset L =>
    finiteRowExponent (IncidenceRows M) (incidenceLower left D)) ∪
      Finset.univ.image (incidenceRowRightExponent right)

theorem incidenceLower_top_ratio (D : Finset L) :
    finiteRowExponent (IncidenceRows M) (incidenceLower left D) -
      finiteRowExponent (IncidenceRows M) (incidenceTop (M := M)) =
        finiteRowExponent (IncidenceRows M) (incidenceLower left D) := by
  ext v
  rcases v with ⟨e,⟨j⟩⟩
  fin_cases j <;> by_cases he : left e ∈ D <;>
    simp [Finsupp.tsub_apply,finiteRowExponent_apply,incidenceLower,incidenceTop,he]

theorem incidenceUpper_top_ratio (F : Finset R) (r : R) (hr : r ∉ F) :
    incidenceRowRightExponent right r ≤
      finiteRowExponent (IncidenceRows M) (incidenceUpper right F) -
        finiteRowExponent (IncidenceRows M) (incidenceTop (M := M)) := by
  rintro ⟨e,⟨j⟩⟩
  by_cases her : right e = r
  · have he : right e ∉ F := by simpa only [her] using hr
    fin_cases j <;> simp [incidenceRowRightExponent_apply,Finsupp.tsub_apply,
      finiteRowExponent_apply,incidenceUpper,incidenceTop,her,he,hr]
  · simp [incidenceRowRightExponent_apply,her]

theorem incidenceUpper_erase_top_ratio (r : R) :
    finiteRowExponent (IncidenceRows M) (incidenceUpper right (Finset.univ.erase r)) -
      finiteRowExponent (IncidenceRows M) (incidenceTop (M := M)) =
        incidenceRowRightExponent right r := by
  ext v
  rcases v with ⟨e,⟨j⟩⟩
  fin_cases j <;> by_cases he : right e = r <;>
    simp [incidenceRowRightExponent_apply,Finsupp.tsub_apply,
      finiteRowExponent_apply,incidenceUpper,incidenceTop,he,eq_comm]

theorem incidenceTopFamily_contains_iff (hM : 0 < M) (hr : Function.Surjective right)
    (α : Exponent (FiniteVariable.{u} (IncidenceRows M))) :
    Contains (finitePredecessorFamily (IncidenceRows M) (incidenceSublattice left right)
      (incidenceTop (M := M))) α ↔ Contains (incidenceTopFamily left right) α := by
  rw [← finiteCoordinatePredecessor_contains_iff
    (incidenceSublattice_closed left right) (incidenceTop_mem left right) α]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨haE,hat,hne⟩ := Finset.mem_filter.mp ha
    rcases Finset.mem_union.mp haE with hlow | hupp
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hlow
      rw [incidenceLower_top_ratio] at hba
      exact ⟨_,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩),hba⟩
    · obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hupp
      obtain ⟨e,he⟩ : ∃ e : Fin M, right e ∉ F := by
        by_contra! hh
        apply hne
        funext e
        simp [incidenceUpper,incidenceTop,hh e]
      exact ⟨_,Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨right e,Finset.mem_univ _,rfl⟩), (incidenceUpper_top_ratio right F (right e) he).trans hba⟩
  · rintro ⟨b,hb,hba⟩
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hb
      have hlow : incidenceLower left D ≠ incidenceTop (M := M) := by
        intro he
        have hh := congrFun he (⟨0,hM⟩ : Fin M)
        by_cases hD : left ⟨0,hM⟩ ∈ D <;> simp [incidenceLower,incidenceTop,hD] at hh
      refine ⟨_,Finset.mem_image.mpr ⟨incidenceLower left D,Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩),?_,hlow⟩,rfl⟩,?_⟩
      · intro e
        by_cases hD : left e ∈ D <;> simp [incidenceLower,incidenceTop,hD]
      · rwa [incidenceLower_top_ratio]
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨e,her⟩ := hr r
      have hupp : incidenceUpper right (Finset.univ.erase r) ≠ incidenceTop (M := M) := by
        intro he
        have hh := congrFun he e
        simp [incidenceUpper,incidenceTop,her] at hh
      refine ⟨_,Finset.mem_image.mpr ⟨incidenceUpper right (Finset.univ.erase r),
        Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨Finset.univ.erase r,Finset.mem_univ _,rfl⟩),?_,hupp⟩,rfl⟩,?_⟩
      · intro e
        by_cases hF : right e ∈ Finset.univ.erase r <;> simp [incidenceUpper,incidenceTop,hF]
      · rwa [incidenceUpper_erase_top_ratio]

/-- The computed family generates exactly the actual colon in the paper. -/
theorem incidenceTopColon_eq {k : Type*} [CommSemiring k]
    (hM : 0 < M) (hr : Function.Surjective right) :
    finitePredecessorColon (IncidenceRows M) (k := k) (incidenceSublattice left right)
      (incidenceTop (M := M)) = monomialIdeal k (incidenceTopFamily left right) := by
  rw [finitePredecessorColon_eq]
  ext f
  simp_rw [mem_monomialIdeal_iff,incidenceTopFamily_contains_iff left right hM hr]

theorem incidenceTopFamily_unused_top (e : Fin M) :
    UnusedVariable (incidenceTopFamily left right) ⟨e,ULift.up 2⟩ := by
  intro b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hb
    by_cases he : left e ∈ D <;> simp [finiteRowExponent_apply,incidenceLower,he]
  · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
    simp [incidenceRowRightExponent_apply]

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.RankMinors -/
section

set_option autoImplicit false

/-!
# Matrix rank detected by actual minors

The field argument is adapted with its proof retained from
`TauCeti.LinearAlgebra.Matrix.Rank`, commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362` (Apache-2.0).
The construction chooses independent rows and then independent columns. No rank
criterion is imported as an unverified assertion.
-/

noncomputable section

namespace FourPapers.Symmetric

open Matrix

 theorem independent_rows_iff_nonzero_minor {m n K : Type*} [Fintype m]
    [DecidableEq m] [Finite n] [Field K] {A : Matrix m n K} :
    LinearIndependent K A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  have : Fintype n := Fintype.ofFinite n
  refine ⟨fun h => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card m = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        ← rank_eq_finrank_span_cols, h.rank_matrix]
    let e : m ↪ n := (Fintype.equivOfCardEq hcard).toEmbedding.trans ⟨a, ha⟩
    have hcol : LinearIndependent K (A.submatrix id e).col :=
      hli.comp _ (Fintype.equivOfCardEq hcard).injective
    exact ⟨e, ((isUnit_iff_isUnit_det _).1 (linearIndependent_col_iff_isUnit.1 hcol)).ne_zero⟩
  · exact LinearIndependent.of_comp (LinearMap.funLeft K K e)
      (linearIndependent_rows_of_det_ne_zero he)

 theorem le_rank_iff_nonzero_minor {m n K : Type*} [Field K] [Finite m] [Fintype n]
    {A : Matrix m n K} {p : ℕ} :
    p ≤ A.rank ↔ ∃ (r : Fin p ↪ m) (c : Fin p ↪ n), (A.submatrix r c).det ≠ 0 := by
  refine ⟨fun hp => ?_, fun ⟨r, c, h⟩ => ?_⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : A.rank = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        rank_eq_finrank_span_row]
    let r : Fin p ↪ m :=
      ((Fin.castLEEmb (hcard ▸ hp)).trans (Fintype.equivFin κ).symm.toEmbedding).trans ⟨a, ha⟩
    have hr : LinearIndependent K (A.submatrix r id).row :=
      hli.comp _ (Fin.castLEEmb _ |>.trans (Fintype.equivFin κ).symm.toEmbedding).injective
    obtain ⟨c, hc⟩ := independent_rows_iff_nonzero_minor.1 hr
    exact ⟨r, c, by rwa [submatrix_submatrix] at hc⟩
  · classical
    simpa [rank_of_det_ne_zero h] using rank_submatrix_le A r c

/-- The vanishing-minor characterization retains every rectangular dimension and
all rank bounds, including bounds larger than either dimension. -/
theorem rank_le_iff_vanishing_minors {m n K : Type*} [Field K] [Finite m] [Fintype n]
    {A : Matrix m n K} {p : ℕ} :
    A.rank ≤ p ↔ ∀ (r : Fin (p + 1) ↪ m) (c : Fin (p + 1) ↪ n),
      (A.submatrix r c).det = 0 := by
  rw [← not_lt, Nat.lt_iff_add_one_le, le_rank_iff_nonzero_minor]
  simp only [not_exists, ne_eq, not_not]

end FourPapers.Symmetric

end
end

/- BEGIN EXACT BODY: FourPapers.Common.DirectSumDimensionComparison -/
section

/-! # Comparing graded dimensions over different fields

The grading may be infinite. The finite basis-index set of the total direct
sum replaces any implicit assumption that only finitely many indices exist.
Nonnegative increases in individual dimensions cannot cancel in the total.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace FourPapers
open Classical DirectSum

lemma finite_sigma_fin_eq_of_le {I : Type*} (f g : I → ℕ)
    [Finite (Σ i, Fin (f i))] [Finite (Σ i, Fin (g i))]
    (hle : ∀ i, f i ≤ g i)
    (hcard : Nat.card (Σ i, Fin (f i)) = Nat.card (Σ i, Fin (g i))) :
    ∀ i, f i = g i := by
  let e : (Σ i, Fin (f i)) → (Σ i, Fin (g i)) :=
    fun x => ⟨x.1, x.2.castLE (hle x.1)⟩
  have he : Function.Injective e := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hxy : x.val = y.val := congrArg (fun z : Σ i, Fin (g i) => z.2.val) h
    exact congrArg (Sigma.mk i) (Fin.ext hxy)
  letI := Fintype.ofFinite (Σ i, Fin (f i))
  letI := Fintype.ofFinite (Σ i, Fin (g i))
  have hs : Function.Surjective e := by
    by_contra h
    have hh := Fintype.card_lt_of_injective_not_surjective e he h
    simpa only [← Nat.card_eq_fintype_card, hcard, lt_self_iff_false] using hh
  intro i
  by_contra hne
  have hlt : f i < g i := lt_of_le_of_ne (hle i) hne
  obtain ⟨⟨j, x⟩, hx⟩ := hs ⟨i, ⟨f i, hlt⟩⟩
  have hji : j = i := congrArg Sigma.fst hx
  subst j
  have hv : x.val = f i := congrArg (fun z : Σ i, Fin (g i) => z.2.val) hx
  exact (Nat.ne_of_lt x.isLt) hv

section DirectSum
variable {K L I : Type*} [Field K] [Field L] [DecidableEq I]
  (V : I → Type*) (W : I → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module.Finite K (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)] [∀ i, Module.Finite L (W i)]

lemma finrank_directSum_eq_of_components
    (h : ∀ i, Module.finrank K (V i) = Module.finrank L (W i)) :
    Module.finrank K (⨁ i, V i) = Module.finrank L (⨁ i, W i) := by
  let b : Module.Basis (Σ i, Fin (Module.finrank K (V i))) K (⨁ i, V i) :=
    DFinsupp.basis (fun i => Module.finBasis K (V i))
  let c : Module.Basis (Σ i, Fin (Module.finrank L (W i))) L (⨁ i, W i) :=
    DFinsupp.basis (fun i => Module.finBasis L (W i))
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis c]
  exact Nat.card_congr (Equiv.sigmaCongrRight (fun i => finCongr (h i)))

/-- Over different fields, equality of the finite total dimension forces each
componentwise nonnegative excess to vanish. -/
lemma component_finrank_eq_of_total_eq
    [Module.Finite K (⨁ i, V i)] [Module.Finite L (⨁ i, W i)]
    (hle : ∀ i, Module.finrank K (V i) ≤ Module.finrank L (W i))
    (htotal : Module.finrank K (⨁ i, V i) = Module.finrank L (⨁ i, W i)) :
    ∀ i, Module.finrank K (V i) = Module.finrank L (W i) := by
  let b : Module.Basis (Σ i, Fin (Module.finrank K (V i))) K (⨁ i, V i) :=
    DFinsupp.basis (fun i => Module.finBasis K (V i))
  let c : Module.Basis (Σ i, Fin (Module.finrank L (W i))) L (⨁ i, W i) :=
    DFinsupp.basis (fun i => Module.finBasis L (W i))
  letI : Finite (Σ i, Fin (Module.finrank K (V i))) := Module.Finite.finite_basis b
  letI : Finite (Σ i, Fin (Module.finrank L (W i))) := Module.Finite.finite_basis c
  apply finite_sigma_fin_eq_of_le _ _ hle
  rw [← Module.finrank_eq_nat_card_basis b, ← Module.finrank_eq_nat_card_basis c]
  exact htotal

end DirectSum
end FourPapers

#print axioms FourPapers.component_finrank_eq_of_total_eq

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.NormalizedInverse -/
section

/-! # A square-zero odd generalized inverse

The normalization is purely algebraic. Starting with `d h d = d`, first
replace `h` by `h d h`, then replace it by `h - h h d`. This produces the
side conditions needed for a strong contraction, and retains odd parity.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace FourPapers
section Ring
variable {A : Type*} [Ring A]

theorem reflexive_inverse_dhd (d h : A) (hdhd : d * h * d = d) :
    d * (h * d * h) * d = d := by
  calc
    _ = (d * h * d) * h * d := by noncomm_ring
    _ = d := by rw [hdhd, hdhd]

theorem reflexive_inverse_hdh (d h : A) (hdhd : d * h * d = d) :
    (h * d * h) * d * (h * d * h) = h * d * h := by
  calc
    _ = h * (d * h * d) * h * d * h := by noncomm_ring
    _ = h * (d * h * d) * h := by nth_rw 1 [hdhd]; noncomm_ring
    _ = h * d * h := by rw [hdhd]

theorem normalize_inverse_dhd (d h : A) (hdd : d * d = 0)
    (hdhd : d * h * d = d) :
    d * (h - h * h * d) * d = d := by
  calc
    _ = d * h * d - d * h * h * (d * d) := by noncomm_ring
    _ = d := by rw [hdhd, hdd, mul_zero, sub_zero]

theorem normalize_inverse_square (d h : A) (hhdh : h * d * h = h) :
    (h - h * h * d) * (h - h * h * d) = 0 := by
  calc
    _ = h * h - h * h * h * d - h * (h * d * h) +
        h * (h * d * h) * h * d := by noncomm_ring
    _ = 0 := by rw [hhdh]; noncomm_ring

theorem normalize_inverse_reflexive (d h : A) (hdd : d * d = 0)
    (hhdh : h * d * h = h) :
    (h - h * h * d) * d * (h - h * h * d) = h - h * h * d := by
  calc
    _ = h * d * h - (h * d * h) * h * d - h * h * (d * d) * h +
        h * h * (d * d) * h * h * d := by noncomm_ring
    _ = _ := by rw [hhdh, hdd]; noncomm_ring

theorem reflexive_inverse_odd (d h s : A)
    (hds : d * s = -(s * d)) (hhs : h * s = -(s * h)) :
    (h * d * h) * s = -(s * (h * d * h)) := by
  calc
    _ = h * d * (h * s) := by noncomm_ring
    _ = -(h * (d * s) * h) := by rw [hhs]; noncomm_ring
    _ = (h * s) * d * h := by rw [hds]; noncomm_ring
    _ = _ := by rw [hhs]; noncomm_ring

theorem normalize_inverse_odd (d h s : A)
    (hds : d * s = -(s * d)) (hhs : h * s = -(s * h)) :
    (h - h * h * d) * s = -(s * (h - h * h * d)) := by
  have heven : h * h * s = s * h * h := by
    calc
      _ = h * (h * s) := mul_assoc _ _ _
      _ = -(h * s) * h := by nth_rw 1 [hhs]; noncomm_ring
      _ = _ := by rw [hhs]; noncomm_ring
  calc
    _ = h * s - h * h * (d * s) := by noncomm_ring
    _ = -(s * h) + (h * h * s) * d := by rw [hhs, hds]; noncomm_ring
    _ = _ := by rw [heven]; noncomm_ring

/-- Pure algebraic normalization; no division and no characteristic restriction. -/
theorem exists_squareZero_odd_inverse (d h s : A)
    (hdd : d * d = 0) (hdhd : d * h * d = d)
    (hds : d * s = -(s * d)) (hhs : h * s = -(s * h)) :
    ∃ H : A, d * H * d = d ∧ H * H = 0 ∧ H * d * H = H ∧ H * s = -(s * H) := by
  let u := h * d * h
  have hdu : d * u * d = d := reflexive_inverse_dhd d h hdhd
  have hud : u * d * u = u := reflexive_inverse_hdh d h hdhd
  have hus : u * s = -(s * u) := reflexive_inverse_odd d h s hds hhs
  exact ⟨u - u * u * d, normalize_inverse_dhd d u hdd hdu,
    normalize_inverse_square d u hud, normalize_inverse_reflexive d u hdd hud,
    normalize_inverse_odd d u s hds hus⟩

end Ring
end FourPapers

#print axioms FourPapers.exists_squareZero_odd_inverse

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.EmptyRowDepthClarification -/
section

/-!
# The empty-product boundary case of the depth clause

If zero rows are admitted, the unique row monomial is the empty product 1.
The resulting ideal is the unit ideal, and its quotient has depth infinity.
Consequently the printed finite depth formula needs the usual positive-row
convention, or equivalently the requirement that the ideal be proper.
This file records the literal exceptional example separately from the
positive-row theorem. It does not change the meaning of depth.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice.EmptyRowDepthClarification
open Classical MvPolynomial
universe u

def rows : Fin 0 → ℕ := Fin.elim0
def lattice : Finset (FiniteTuple rows) := Finset.univ

theorem lattice_nonempty : lattice.Nonempty :=
  ⟨fun i => Fin.elim0 i, Finset.mem_univ _⟩

theorem lattice_closed : finiteLatticeClosed rows lattice := by
  constructor <;> intro a ha b hb <;> exact Finset.mem_univ _

theorem variables_card : Fintype.card (FiniteVariable.{u} rows) = 0 := by
  letI : IsEmpty (FiniteVariable.{u} rows) := ⟨fun x => Fin.elim0 x.1⟩
  exact Fintype.card_eq_zero

theorem height_zero : finiteLatticeHeight lattice_closed lattice_nonempty = 0 := by
  letI : DistribLattice lattice := finiteTupleDistribLattice lattice_closed
  letI : OrderBot lattice := finiteTupleOrderBot lattice_closed lattice_nonempty
  letI : IsEmpty (FourPapers.FiniteDistributive.Irreducible lattice) :=
    ⟨fun a => a.property.ne_bot (Subsingleton.elim a.val ⊥)⟩
  change Fintype.card (FourPapers.FiniteDistributive.Irreducible lattice) = 0
  exact Fintype.card_eq_zero

variable {k : Type u} [Field k]

theorem ideal_eq_top : finiteSublatticeIdeal rows (k := k) lattice = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  have hm : finiteRowMonomial rows (k := k) (fun i => Fin.elim0 i) ∈
      finiteSublatticeIdeal rows (k := k) lattice := by
    apply Ideal.subset_span
    exact ⟨(fun i => Fin.elim0 i), Finset.mem_univ _, rfl⟩
  simpa only [finiteSublatticeIdeal, finiteRowMonomial, Finset.univ_eq_empty,
    Finset.prod_empty] using hm

theorem actual_depth_infinite (m : ℕ) :
    (idealOfVars (FiniteVariable.{u} rows) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} rows) k)
        (MvPolynomial (FiniteVariable.{u} rows) k ⧸
          (finiteSublatticeIdeal rows (k := k) lattice)^m)) = ⊤ := by
  have ht : (finiteSublatticeIdeal rows (k := k) lattice)^m = ⊤ := by
    rw [ideal_eq_top, Ideal.top_pow]
  letI : Subsingleton (MvPolynomial (FiniteVariable.{u} rows) k ⧸
      (finiteSublatticeIdeal rows (k := k) lattice)^m) :=
    Ideal.Quotient.subsingleton_iff.mpr ht
  exact Ideal.depth_eq_top_of_subsingleton _ _

/-- Explicit violation of the unrestricted empty-row reading of the
printed depth formula, even at the positive power m=1. -/
theorem depth_clause_fails :
    (idealOfVars (FiniteVariable.{u} rows) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} rows) k)
        (MvPolynomial (FiniteVariable.{u} rows) k ⧸
          (finiteSublatticeIdeal rows (k := k) lattice)^1)) ≠
      ((Fintype.card (FiniteVariable.{u} rows) -
        finiteLatticeHeight lattice_closed lattice_nonempty - 1 : ℕ) : ℕ∞) := by
  rw [actual_depth_infinite, variables_card, height_zero]
  simp

/-- The paper's subtraction is integer subtraction. In the exceptional
zero-row example its displayed finite right-hand side is literally `-1`. -/
theorem printed_depth_rhs :
    (Fintype.card (FiniteVariable.{u} rows) : ℤ) -
      (finiteLatticeHeight lattice_closed lattice_nonempty : ℤ) - 1 = -1 := by
  rw [variables_card, height_zero]
  rfl

/-- Literal contradiction of the unrestricted printed integer formula.
`WithTop.map` sends finite natural depths to the same integers and retains
infinity; it does not truncate the right-hand side's subtraction. -/
theorem depth_clause_fails_integer :
    WithTop.map (fun n : ℕ => (n : ℤ))
      ((idealOfVars (FiniteVariable.{u} rows) k).depth
        (ModuleCat.of (MvPolynomial (FiniteVariable.{u} rows) k)
          (MvPolynomial (FiniteVariable.{u} rows) k ⧸
            (finiteSublatticeIdeal rows (k := k) lattice)^1))) ≠
      (((Fintype.card (FiniteVariable.{u} rows) : ℤ) -
        (finiteLatticeHeight lattice_closed lattice_nonempty : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  rw [actual_depth_infinite]
  change (⊤ : WithTop ℤ) ≠ _
  exact WithTop.top_ne_coe

end FourPapers.Sublattice.EmptyRowDepthClarification
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TwoSimplexContraction -/
section

/-! # Integral contraction of a disjoint union of two simplices

The row generator is z-e. Projection is minus the augmentation of the
one-simplex vertex part. Consequently it is natural when the one block
increases, including the transition from an empty one block. The empty
face is filled by z, a fixed zero-block vertex.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.TwoSimplex
open Classical CommAlg CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def Faces (Z E : Finset V) (F : Finset V) : Prop := F ⊆ Z ∨ F ⊆ E

theorem downward (Z E : Finset V) : Downward (Faces Z E) := by
  intro F H hHF hF
  exact hF.imp (hHF.trans ·) (hHF.trans ·)

def emptyCoefficient : Ambient V k →ₗ[k] k :=
  (Finsupp.lapply ∅).comp (basis (V := V) (k := k)).repr.toLinearMap

@[simp] theorem emptyCoefficient_basis (F : Finset V) :
    emptyCoefficient (k := k) (basis F) = if F=∅ then 1 else 0 := by
  simp [emptyCoefficient,Finsupp.single_apply,eq_comm]

def positiveSimplexPart (E : Finset V) : Module.End k (Ambient V k) :=
  (basis (V := V) (k := k)).constr k fun F => if F ⊆ E ∧ F ≠ ∅ then basis F else 0

@[simp] theorem positiveSimplexPart_basis (E F : Finset V) :
    positiveSimplexPart (k := k) E (basis F) =
      if F ⊆ E ∧ F ≠ ∅ then basis F else 0 := by
  simp only [positiveSimplexPart, Module.Basis.constr_basis]

theorem positiveSimplexPart_on_simplex (E : Finset V) (x : Ambient V k)
    (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ E)) :
    positiveSimplexPart E x = x-emptyCoefficient x • basis ∅ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      change F ⊆ E at hF
      by_cases h0 : F=∅
      · subst F; simp
      · simp [hF,h0]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy,add_smul]; abel
  | smul r x hx ih => simp only [map_smul,ih,smul_sub,smul_smul,smul_eq_mul]

theorem positiveSimplexPart_on_disjoint (Z E : Finset V) (hZE : Disjoint Z E)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ Z)) :
    positiveSimplexPart E x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rw [positiveSimplexPart_basis]
      apply if_neg
      rintro ⟨hFE,hFn⟩
      obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hFn
      exact Finset.disjoint_left.mp hZE (hF hv) (hFE hv)
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul r x hx ih => rw [map_smul,ih,smul_zero]

theorem simplex_downward (E : Finset V) : Downward (fun F : Finset V => F ⊆ E) :=
  fun _ _ hFG hGE => hFG.trans hGE

theorem boundary_empty : boundary (basis (V := V) (k := k) ∅)=0 := by
  exact boundary_zero_degree_zero (basis_mem (K := fun _ => True) trivial rfl)

theorem creation_empty (v : V) : creation (k := k) v (basis ∅)=basis {v} := by
  change ExteriorAlgebra.ι k ((Pi.basisFun k V) v) * basis ∅ = _
  rw [show basis (V := V) (k := k) ∅=1 by
    simp [basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort],mul_one]
  exact (TauCeti.ExteriorAlgebra.basis_singleton (Pi.basisFun k V) v).symm

theorem boundary_singleton (v : V) : boundary (basis (k := k) {v})=basis ∅ := by
  rw [← creation_empty,boundary_creation,boundary_empty,map_zero,sub_zero]

theorem emptyCoefficient_creation (v : V) (x : Ambient V k) :
    emptyCoefficient (creation v x)=0 := by
  have hm : (emptyCoefficient (V := V) (k := k)).comp (creation v)=0 := by
    apply (basis (V := V) (k := k)).ext
    intro F
    change emptyCoefficient (creation v (basis F))=0
    rw [creation_basis]
    split_ifs <;> simp [map_smul,emptyCoefficient_basis]
  exact LinearMap.congr_fun hm x

theorem creation_square (v : V) (x : Ambient V k) : creation v (creation v x)=0 := by
  change ExteriorAlgebra.ι k ((Pi.basisFun k V) v) *
    (ExteriorAlgebra.ι k ((Pi.basisFun k V) v) * x)=0
  rw [← mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]

/-- The sole defect of the nonempty simplex projection is the empty face. -/
theorem positiveSimplexPart_commutator (Z E : Finset V) (hZE : Disjoint Z E)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (Faces Z E)) :
    boundary (positiveSimplexPart E x)-positiveSimplexPart E (boundary x)=
      emptyCoefficient (boundary (positiveSimplexPart E x)) • basis ∅ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rcases hF with hZ | hE
      · have hxZ : basis (k := k) F ∈ TotalFaceModule (fun F : Finset V => F ⊆ Z) :=
          Submodule.subset_span ⟨F,hZ,rfl⟩
        rw [positiveSimplexPart_on_disjoint Z E hZE _ hxZ,
          positiveSimplexPart_on_disjoint Z E hZE _
            (boundary_mem_basisSpan (simplex_downward Z) hxZ),map_zero,map_zero,sub_self,zero_smul]
      · have hxE : basis (k := k) F ∈ TotalFaceModule (fun F : Finset V => F ⊆ E) :=
          Submodule.subset_span ⟨F,hE,rfl⟩
        rw [positiveSimplexPart_on_simplex E _ hxE,
          positiveSimplexPart_on_simplex E _ (boundary_mem_basisSpan (simplex_downward E) hxE)]
        simp only [map_sub,map_smul,boundary_empty,smul_zero,sub_zero]
        abel
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp only [map_add,add_smul,add_sub_add_comm,ihx,ihy]
  | smul r x hx ih => simp only [map_smul,← smul_sub,ih,smul_smul,smul_eq_mul]

def projectionAmbient (E : Finset V) : Ambient V k →ₗ[k] k :=
  -emptyCoefficient.comp (boundary.comp (positiveSimplexPart E))

def homotopyAmbient (E : Finset V) (z e : V) : Module.End k (Ambient V k) :=
  creation z + (creation (k := k) e-creation (k := k) z).comp (positiveSimplexPart E)

def generator (z e : V) : Ambient V k := basis {z}-basis {e}

theorem homotopy_on_zero_simplex (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (x : Ambient V k) (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ Z)) :
    homotopyAmbient E z e x=creation z x := by
  change creation z x + (creation (k := k) e-creation (k := k) z) (positiveSimplexPart E x)=_
  rw [positiveSimplexPart_on_disjoint Z E hZE _ hx,map_zero,add_zero]

theorem homotopy_on_one_simplex (E : Finset V) (z e : V) (x : Ambient V k)
    (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ E)) :
    homotopyAmbient E z e x=creation e x + emptyCoefficient x • generator z e := by
  change creation z x + (creation (k := k) e-creation (k := k) z) (positiveSimplexPart E x)=_
  rw [positiveSimplexPart_on_simplex E _ hx]
  simp only [LinearMap.sub_apply,map_sub,map_smul,creation_empty,generator,smul_sub]
  abel

theorem homotopy_identity (Z E : Finset V) (hZE : Disjoint Z E) (z e : V)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (Faces Z E)) :
    boundary (homotopyAmbient E z e x)+homotopyAmbient E z e (boundary x)=
      x-projectionAmbient E x • generator z e := by
  have hq := positiveSimplexPart_commutator Z E hZE x hx
  have heq := congrArg (creation (k := k) e-creation (k := k) z) hq
  simp only [map_sub,map_smul,LinearMap.sub_apply,creation_empty] at heq
  change boundary (creation z x + (creation e (positiveSimplexPart E x)-
    creation z (positiveSimplexPart E x))) +
    (creation z (boundary x) + (creation e (positiveSimplexPart E (boundary x))-
      creation z (positiveSimplexPart E (boundary x)))) = _
  rw [map_add,map_sub,boundary_creation,boundary_creation,boundary_creation]
  change _ = x-(-emptyCoefficient (boundary (positiveSimplexPart E x))) • generator z e
  dsimp only [generator]
  erw [neg_smul,smul_sub]
  erw [smul_sub] at heq
  convert congrArg (fun y : Ambient V k => x-y) heq using 1 <;> abel

theorem projection_generator (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) :
    projectionAmbient (k := k) E (generator z e)=1 := by
  have hzE : z ∉ E := fun h => Finset.disjoint_left.mp hZE hz h
  simp [projectionAmbient,generator,positiveSimplexPart_basis,hzE,he,boundary_singleton]

theorem generator_cycle (z e : V) : boundary (generator (k := k) z e)=0 := by
  rw [generator,map_sub,boundary_singleton,boundary_singleton,sub_self]

theorem projection_on_zero_simplex (Z E : Finset V) (hZE : Disjoint Z E)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ Z)) :
    projectionAmbient E x=0 := by
  change -emptyCoefficient (boundary (positiveSimplexPart E x))=0
  rw [positiveSimplexPart_on_disjoint Z E hZE _ hx,map_zero,map_zero,neg_zero]

/-- Projection is natural even if the smaller one block is empty. -/
theorem projection_natural (Z E E' : Finset V) (hZE' : Disjoint Z E') (hEE' : E ⊆ E')
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (Faces Z E)) :
    projectionAmbient E' x=projectionAmbient E x := by
  have hZE : Disjoint Z E := hZE'.mono_right hEE'
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rcases hF with hZ | hE
      · rw [projection_on_zero_simplex Z E' hZE' _ (Submodule.subset_span ⟨F,hZ,rfl⟩),
          projection_on_zero_simplex Z E hZE _ (Submodule.subset_span ⟨F,hZ,rfl⟩)]
      · change -emptyCoefficient (boundary (positiveSimplexPart E' (basis F)))=
          -emptyCoefficient (boundary (positiveSimplexPart E (basis F)))
        rw [positiveSimplexPart_on_simplex E' _ (Submodule.subset_span ⟨F,hE.trans hEE',rfl⟩),
          positiveSimplexPart_on_simplex E _ (Submodule.subset_span ⟨F,hE,rfl⟩)]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add,map_add,ihx,ihy]
  | smul r x hx ih => rw [map_smul,map_smul,ih]

theorem creation_mem_simplex (A : Finset V) (v : V) (hv : v ∈ A)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (fun F : Finset V => F ⊆ A)) :
    creation v x ∈ TotalFaceModule (fun F : Finset V => F ⊆ A) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rw [creation_basis]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨insert v F,Finset.insert_subset hv hF,rfl⟩)
  | zero => simpa using Submodule.zero_mem (TotalFaceModule (k := k) (fun F : Finset V => F ⊆ A))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem homotopy_generator (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) :
    homotopyAmbient (k := k) E z e (generator z e)=0 := by
  rw [generator,map_sub,
    homotopy_on_zero_simplex Z E hZE z e _ (Submodule.subset_span ⟨{z},by simpa using hz,rfl⟩),
    homotopy_on_one_simplex E z e _ (Submodule.subset_span ⟨{e},by simpa using he,rfl⟩)]
  simp only [emptyCoefficient_basis,Finset.singleton_ne_empty,if_false,zero_smul,add_zero]
  rw [← creation_empty,← creation_empty,creation_square,creation_square,sub_self]

theorem homotopy_square (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (Faces Z E)) :
    homotopyAmbient E z e (homotopyAmbient E z e x)=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rcases hF with hF | hF
      · have hZ := (Submodule.subset_span ⟨F,hF,rfl⟩ :
          basis (k := k) F ∈ TotalFaceModule (fun F : Finset V => F ⊆ Z))
        rw [homotopy_on_zero_simplex Z E hZE z e _ hZ,
          homotopy_on_zero_simplex Z E hZE z e _ (creation_mem_simplex Z z hz _ hZ),creation_square]
      · have hE := (Submodule.subset_span ⟨F,hF,rfl⟩ :
          basis (k := k) F ∈ TotalFaceModule (fun F : Finset V => F ⊆ E))
        rw [homotopy_on_one_simplex E z e _ hE,map_add,map_smul,
          homotopy_on_one_simplex E z e _ (creation_mem_simplex E e he _ hE),
          creation_square,emptyCoefficient_creation,zero_smul,add_zero,
          homotopy_generator Z E hZE z e hz he,smul_zero,add_zero]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add,map_add,ihx,ihy,add_zero]
  | smul r x hx ih => rw [map_smul,map_smul,ih,smul_zero]

theorem homotopy_raises (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) (p : ℕ)
    (x : Ambient V k) (hx : x ∈ Chains (Faces Z E) p) :
    homotopyAmbient E z e x ∈ Chains (Faces Z E) (p+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,⟨hF,hcard⟩,rfl⟩ := hx
      rcases hF with hF | hF
      · have hxZ : basis (k := k) F ∈ TotalFaceModule (fun G : Finset V => G ⊆ Z) :=
          Submodule.subset_span ⟨F,hF,rfl⟩
        rw [homotopy_on_zero_simplex (k := k) Z E hZE z e _ hxZ]
        exact chains_mono (k := k) (K := fun G : Finset V => G ⊆ Z)
          (L := Faces Z E) (fun G hG => Or.inl hG) (p+1)
          (creation_mem_chains (k := k) (P := fun G : Finset V => G ⊆ Z) z
            (fun G hG => Finset.insert_subset hz hG) (basis_mem hF hcard))
      · by_cases h0 : F=∅
        · subst F
          have hp : p=0 := by simpa using hcard.symm
          subst p
          have hxZ : basis (k := k) (∅ : Finset V) ∈
              TotalFaceModule (fun G : Finset V => G ⊆ Z) :=
            Submodule.subset_span ⟨∅,Finset.empty_subset Z,rfl⟩
          rw [homotopy_on_zero_simplex (k := k) Z E hZE z e _ hxZ,creation_empty]
          exact basis_mem (Or.inl (by simpa using hz)) (by simp)
        · have hxE : basis (k := k) F ∈ TotalFaceModule (fun G : Finset V => G ⊆ E) :=
            Submodule.subset_span ⟨F,hF,rfl⟩
          rw [homotopy_on_one_simplex (k := k) E z e _ hxE,
            emptyCoefficient_basis,if_neg h0,zero_smul,add_zero]
          exact chains_mono (k := k) (K := fun G : Finset V => G ⊆ E)
            (L := Faces Z E) (fun G hG => Or.inr hG) (p+1)
            (creation_mem_chains (k := k) (P := fun G : Finset V => G ⊆ E) e
              (fun G hG => Finset.insert_subset he hG) (basis_mem hF hcard))
  | zero => simpa using Submodule.zero_mem (Chains (k := k) (Faces Z E) (p+1))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem homotopy_mem (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E)
    (x : Ambient V k) (hx : x ∈ TotalFaceModule (Faces Z E)) :
    homotopyAmbient E z e x ∈ TotalFaceModule (Faces Z E) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      exact chains_mem_basisSpan (homotopy_raises Z E hZE z e hz he F.card _ (basis_mem hF rfl))
  | zero => simpa using Submodule.zero_mem (TotalFaceModule (k := k) (Faces Z E))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

set_option diagnostics true in
set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- Strong contraction onto the single genuine homology generator. All
side identities are proved, as required for homological perturbation. -/
def contraction (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) :
    HomologicalPerturbation.LinearContraction (R := k)
      (M := TotalFaceModule (k := k) (Faces Z E)) (H := k) := by
  let D : Module.End k (TotalFaceModule (k := k) (Faces Z E)) :=
    idealTotalDifferential (k := k) (downward Z E)
  let H : Module.End k (TotalFaceModule (k := k) (Faces Z E)) :=
    ((homotopyAmbient (k := k) E z e).domRestrict (TotalFaceModule (Faces Z E))).codRestrict _
    (fun x => homotopy_mem Z E hZE z e hz he x.val x.property)
  have hgen : generator (k := k) z e ∈ TotalFaceModule (Faces Z E) :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨{z},Or.inl (by simpa using hz),rfl⟩)
      (Submodule.subset_span ⟨{e},Or.inr (by simpa using he),rfl⟩)
  let g : TotalFaceModule (k := k) (Faces Z E) := ⟨generator (k := k) z e,hgen⟩
  let I : k →ₗ[k] TotalFaceModule (k := k) (Faces Z E) :=
    LinearMap.toSpanSingleton k (TotalFaceModule (k := k) (Faces Z E)) g
  let P : TotalFaceModule (k := k) (Faces Z E) →ₗ[k] k :=
    (projectionAmbient E).comp (TotalFaceModule (k := k) (Faces Z E)).subtype
  have hPg : P g=1 := projection_generator (k := k) Z E hZE z e hz he
  have hDg : D g=0 := Subtype.ext (generator_cycle (k := k) z e)
  have hHg : H g=0 := Subtype.ext (homotopy_generator (k := k) Z E hZE z e hz he)
  have hPI : ∀ r : k,P (I r)=r := by
    intro r
    calc
      P (I r) = r • P g := P.map_smul r g
      _ = r := by rw [hPg]; exact mul_one r
  have hDI : ∀ r : k,D (I r)=0 := by
    intro r
    calc
      D (I r) = r • D g := D.map_smul r g
      _ = 0 := by rw [hDg,smul_zero]
  have hHI : ∀ r : k,H (I r)=0 := by
    intro r
    calc
      H (I r) = r • H g := H.map_smul r g
      _ = 0 := by rw [hHg,smul_zero]
  have hDD : ∀ x,D (D x)=0 := fun x => Subtype.ext (boundary_boundary x.val)
  have hHH : ∀ x,H (H x)=0 := fun x =>
    Subtype.ext (homotopy_square Z E hZE z e hz he x.val x.property)
  have hid : ∀ x,D (H x)+H (D x)=x-I (P x) := fun x =>
    Subtype.ext (homotopy_identity Z E hZE z e x.val x.property)
  have hPD : ∀ x,P (D x)=0 := by
    intro x
    have h₁ := congrArg D (hid x)
    have h₂ := hid (D x)
    simp only [map_add,map_sub,hDD,hDI,zero_add,sub_zero] at h₁
    simp only [hDD,map_zero,add_zero] at h₂
    have hi : I (P (D x))=0 := by rw [h₁] at h₂; exact (sub_eq_self.mp h₂.symm)
    have hh := congrArg P hi
    simpa only [hPI,map_zero] using hh
  have hPH : ∀ x,P (H x)=0 := by
    intro x
    have h₁ := congrArg H (hid x)
    have h₂ := hid (H x)
    simp only [map_add,map_sub,hHH,hHI,add_zero,sub_zero] at h₁
    simp only [hHH,map_zero,zero_add] at h₂
    have hi : I (P (H x))=0 := by rw [h₁] at h₂; exact (sub_eq_self.mp h₂.symm)
    have hh := congrArg P hi
    simpa only [hPI,map_zero] using hh
  exact
    { d := D
      h := H
      inclusion := I
      projection := P
      differential := LinearMap.ext hDD
      retract := LinearMap.ext hPI
      inclusion_cycle := LinearMap.ext hDI
      projection_boundary := LinearMap.ext hPD
      homotopy := LinearMap.ext hid
      squareHomotopy := LinearMap.ext hHH
      homotopyInclusion := LinearMap.ext hHI
      projectionHomotopy := LinearMap.ext hPH }

@[simp] theorem contraction_d (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) :
    (contraction (k := k) Z E hZE z e hz he).d =
      idealTotalDifferential (downward Z E) := rfl

@[simp] theorem contraction_h_val (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E)
    (x : TotalFaceModule (k := k) (Faces Z E)) :
    ((contraction Z E hZE z e hz he).h x).val = homotopyAmbient E z e x.val := rfl

@[simp] theorem contraction_projection (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E)
    (x : TotalFaceModule (k := k) (Faces Z E)) :
    (contraction Z E hZE z e hz he).projection x=projectionAmbient E x.val := rfl

@[simp] theorem contraction_inclusion_val (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z ∈ Z) (he : e ∈ E) (r : k) :
    ((contraction Z E hZE z e hz he).inclusion r).val=r • generator z e := rfl

end FourPapers.Sublattice.TwoSimplex
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.FullSimplexContraction -/
section

/-! # Strong augmented contractions of full simplices, including the empty simplex -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.FullSimplex
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
universe u
variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]

def faces (A F : Finset V) : Prop := F⊆A

theorem downward (A : Finset V) : Simplicial.Downward (faces A) := fun _ _ h hF => h.trans hF

/-- The empty simplex has its augmented empty-face class. A nonempty
simplex has zero augmented homology. Both cases use actual free modules. -/
abbrev HomologyIndex (A : Finset V) : Type := {z : PUnit.{1} // A=∅}
abbrev HomologyModule (A : Finset V) : Type u := HomologyIndex A →₀ k

def emptyIndexEquiv (A : Finset V) (hA : A=∅) :
    {F : Finset V // faces A F} ≃ HomologyIndex A where
  toFun _ := ⟨PUnit.unit,hA⟩
  invFun _ := ⟨∅,Finset.empty_subset _⟩
  left_inv F := by
    apply Subtype.ext
    exact (Finset.eq_empty_iff_forall_notMem.mpr
      (fun v hv => Finset.notMem_empty v (hA ▸ F.property hv))).symm
  right_inv _ := by apply Subtype.ext; exact Subsingleton.elim _ _

def emptyEquiv (A : Finset V) (hA : A=∅) :
    TotalFaceModule (k:=k) (faces A) ≃ₗ[k] HomologyModule (k:=k) A :=
  (totalFaceBasis (faces A)).equiv (Finsupp.basisSingleOne) (emptyIndexEquiv A hA)

theorem empty_differential (A : Finset V) (hA : A=∅) :
    idealTotalDifferential (k:=k) (downward A)=0 := by
  apply (totalFaceBasis (k:=k) (faces A)).ext
  intro F
  apply Subtype.ext
  have hF : F.val=∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun v hv => Finset.notMem_empty v (hA ▸ F.property hv))
  change Simplicial.boundary (totalFaceBasis (k := k) (faces A) F).val=0
  rw [totalFaceBasis_val,hF]
  simp only [Simplicial.boundary_eq_sum,Simplicial.contraction_basis,Finset.notMem_empty,
    if_false,Finset.sum_const_zero]

theorem creation_mem (A : Finset V) {v : V} (hv : v∈A)
    {z : Simplicial.Ambient V k} (hz : z∈TotalFaceModule (k:=k) (faces A)) :
    Simplicial.creation v z∈TotalFaceModule (faces A) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      rw [Simplicial.creation_basis]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨insert v F,Finset.insert_subset hv hF,rfl⟩)
  | zero => simpa only [map_zero] using (TotalFaceModule (k:=k) (faces A)).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

def contraction (A : Finset V) : LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (faces A)) (H:=HomologyModule (k:=k) A) := by
  by_cases hA : A=∅
  · let e := emptyEquiv (k:=k) A hA
    exact
      { d := idealTotalDifferential (downward A)
        h := 0
        inclusion := e.symm.toLinearMap
        projection := e.toLinearMap
        differential := by rw [empty_differential A hA,zero_mul]
        retract := by apply LinearMap.ext; intro x; exact e.apply_symm_apply x
        inclusion_cycle := by rw [empty_differential A hA,LinearMap.zero_comp]
        projection_boundary := by rw [empty_differential A hA,LinearMap.comp_zero]
        homotopy := by
          apply LinearMap.ext
          intro x
          simp only [mul_zero,zero_mul,add_zero,LinearMap.zero_apply,
            LinearMap.sub_apply,Module.End.one_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
            e.symm_apply_apply,sub_self]
        squareHomotopy := zero_mul _
        homotopyInclusion := LinearMap.zero_comp _
        projectionHomotopy := LinearMap.comp_zero _ }
  · letI : IsEmpty (HomologyIndex A) := ⟨fun x => hA x.property⟩
    let hex := Finset.nonempty_iff_ne_empty.mpr hA
    let v := Classical.choose hex
    have hv : v∈A := Classical.choose_spec hex
    let H : Module.End k (TotalFaceModule (k:=k) (faces A)) :=
      ((Simplicial.creation v).domRestrict (TotalFaceModule (faces A))).codRestrict _
        (fun x => creation_mem A hv x.property)
    exact
      { d := idealTotalDifferential (downward A)
        h := H
        inclusion := 0
        projection := 0
        differential := by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val)
        retract := by apply LinearMap.ext; intro x; exact Subsingleton.elim _ _
        inclusion_cycle := LinearMap.comp_zero _
        projection_boundary := LinearMap.zero_comp _
        homotopy := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          change Simplicial.boundary (Simplicial.creation v x.val)+
            Simplicial.creation v (Simplicial.boundary x.val)=x.val-0
          rw [Simplicial.boundary_creation,sub_add_cancel,sub_zero]
        squareHomotopy := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          change ExteriorAlgebra.ι k ((Pi.basisFun k V) v)*
            (ExteriorAlgebra.ι k ((Pi.basisFun k V) v)*x.val)=0
          rw [← mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]
        homotopyInclusion := LinearMap.comp_zero _
        projectionHomotopy := LinearMap.zero_comp _ }

theorem contraction_d (A : Finset V) :
    (contraction (k:=k) A).d=idealTotalDifferential (downward A) := by
  unfold contraction
  split_ifs <;> rfl

theorem contraction_projection_basis (A : Finset V)
    (F : {F : Finset V // faces A F}) :
    (contraction (k:=k) A).projection (totalFaceBasis (faces A) F)=
      if hA : A=∅ then Finsupp.single ⟨PUnit.unit,hA⟩ 1 else 0 := by
  unfold contraction
  split_ifs with hA
  · change emptyEquiv A hA (totalFaceBasis (faces A) F)=_
    rw [emptyEquiv,Module.Basis.equiv_apply]
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency true in
theorem contraction_h_raises (A : Finset V) (p : ℕ)
    (x : TotalFaceModule (k:=k) (faces A))
    (hx : x.val∈Simplicial.Chains (faces A) p) :
    ((contraction A).h x).val∈Simplicial.Chains (faces A) (p+1) := by
  unfold contraction
  split_ifs with hA
  · exact Submodule.zero_mem _
  · let v : V := Classical.choose (Finset.nonempty_iff_ne_empty.mpr hA)
    have hv : v∈A := Classical.choose_spec (Finset.nonempty_iff_ne_empty.mpr hA)
    change Simplicial.creation v x.val∈Simplicial.Chains (faces A) (p+1)
    exact creation_mem_chains (k := k) (P := faces A) v
      (fun F hF => Finset.insert_subset hv hF) hx

theorem contraction_inclusion_basis (A : Finset V) (i : HomologyIndex A) :
    (contraction (k:=k) A).inclusion (Finsupp.single i 1)=
      totalFaceBasis (faces A) ⟨∅,Finset.empty_subset _⟩ := by
  unfold contraction
  rw [dif_pos i.property]
  change (emptyEquiv A i.property).symm (Finsupp.single i 1)=_
  apply (emptyEquiv A i.property).injective
  rw [LinearEquiv.apply_symm_apply,emptyEquiv,Module.Basis.equiv_apply]
  congr 1

end FourPapers.FullSimplex

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ContractionHomology -/
section

/-! # A contraction identifies the literal kernel/image quotient

The map is induced by the stated projection. Its kernel is proved to be the
actual boundary submodule using the chain homotopy identity.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearContraction
open Classical FourPapers.FilteredHomology
variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))

def cycleProjection : LinearMap.ker C.d →ₗ[R] H :=
  C.projection.comp (LinearMap.ker C.d).subtype

lemma cycleProjection_surjective : Function.Surjective C.cycleProjection := by
  intro x
  exact ⟨⟨C.inclusion x, C.differential_inclusion_apply x⟩,
    C.projection_inclusion_apply x⟩

lemma cycleProjection_ker :
    LinearMap.ker C.cycleProjection =
      LinearMap.range (boundaryMap C.d C.d C.differential) := by
  ext x
  constructor
  · intro hx
    have hp : C.projection x.val = 0 := hx
    have he := LinearMap.congr_fun C.homotopy x.val
    change C.d (C.h x.val) + C.h (C.d x.val) =
      x.val - C.inclusion (C.projection x.val) at he
    rw [x.property, map_zero, hp, map_zero, add_zero, sub_zero] at he
    exact ⟨C.h x.val, Subtype.ext he⟩
  · rintro ⟨y, rfl⟩
    exact C.projection_differential_apply y

/-- The homology equivalence of the actual contraction, over an arbitrary ring. -/
def homologyEquiv : Homology C.d C.d C.differential ≃ₗ[R] H :=
  (Submodule.quotEquivOfEq _ _ C.cycleProjection_ker.symm).trans
    (C.cycleProjection.quotKerEquivOfSurjective C.cycleProjection_surjective)

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OddContraction -/
section

/-! # Strong odd contractions of vector-space differentials

The target is the range of an explicit idempotent. The previous module proves
that this target is isomorphic to the actual cycle/boundary quotient. The
construction works in characteristic two with the actual identity parity.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.HomologicalPerturbation
open Classical
section General
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (d h : Module.End R M) (hdd : d * d = 0) (hdhd : d * h * d = d)
  (hhh : h * h = 0) (hhdh : h * d * h = h)

def inverseProjection : Module.End R M := 1 - d * h - h * d

include hdd hdhd hhh in
lemma inverseProjection_square : inverseProjection d h * inverseProjection d h =
    inverseProjection d h := by
  unfold inverseProjection
  calc
    _ = (1 - d*h - h*d) + (d*h*d-d)*h + h*(d*h*d-d) +
        d*(h*h)*d + h*(d*d)*h := by noncomm_ring
    _ = _ := by rw [hdhd, hhh, hdd]; noncomm_ring

include hdd hdhd in
lemma differential_inverseProjection : d * inverseProjection d h = 0 := by
  unfold inverseProjection
  calc
    _ = d - (d*d)*h - d*h*d := by noncomm_ring
    _ = 0 := by rw [hdd, hdhd]; noncomm_ring

include hdd hdhd in
lemma inverseProjection_differential : inverseProjection d h * d = 0 := by
  unfold inverseProjection
  calc
    _ = d - d*h*d - h*(d*d) := by noncomm_ring
    _ = 0 := by rw [hdd, hdhd]; noncomm_ring

include hhh hhdh in
lemma homotopy_inverseProjection : h * inverseProjection d h = 0 := by
  unfold inverseProjection
  calc
    _ = h - h*d*h - (h*h)*d := by noncomm_ring
    _ = 0 := by rw [hhh, hhdh]; noncomm_ring

include hhh hhdh in
lemma inverseProjection_homotopy : inverseProjection d h * h = 0 := by
  unfold inverseProjection
  calc
    _ = h - d*(h*h) - h*d*h := by noncomm_ring
    _ = 0 := by rw [hhh, hhdh]; noncomm_ring

def contractionOfInverse :
    LinearContraction (R := R) (M := M) (H := LinearMap.range (inverseProjection d h)) where
  d := d
  h := h
  inclusion := (LinearMap.range (inverseProjection d h)).subtype
  projection := (inverseProjection d h).rangeRestrict
  differential := hdd
  retract := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change inverseProjection d h x.val = x.val
    rw [← hy]
    exact LinearMap.congr_fun (inverseProjection_square d h hdd hdhd hhh) y
  inclusion_cycle := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := x.property
    change d x.val = 0
    rw [← hy]
    exact LinearMap.congr_fun (differential_inverseProjection d h hdd hdhd) y
  projection_boundary := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (inverseProjection_differential d h hdd hdhd) x
  homotopy := by
    change d * h + h * d = 1 - inverseProjection d h
    unfold inverseProjection
    noncomm_ring
  squareHomotopy := hhh
  homotopyInclusion := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := x.property
    change h x.val = 0
    rw [← hy]
    exact LinearMap.congr_fun (homotopy_inverseProjection d h hhh hhdh) y
  projectionHomotopy := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (inverseProjection_homotopy d h hhh hhdh) x

end General
section Field
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (d s : Module.End K M) (hdd : d*d=0) (hs : s*s=1)
  (hds : d*s=-(s*d)) (hchar : (2 : K)=0 → s=1)

include hdd hs hds hchar in
theorem exists_odd_strong_inverse :
    ∃ h : Module.End K M, d*h*d=d ∧ h*h=0 ∧ h*d*h=h ∧ h*s=-(s*h) := by
  obtain ⟨h, hdhd, hsh⟩ := TensorCycleSpanning.exists_odd_generalizedInverse d s hs hds hchar
  exact exists_squareZero_odd_inverse d h s hdd hdhd hds
    (add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using hsh))

def oddHomotopy : Module.End K M :=
  (exists_odd_strong_inverse d s hdd hs hds hchar).choose

lemma oddHomotopy_spec :
    d * oddHomotopy d s hdd hs hds hchar * d = d ∧
    oddHomotopy d s hdd hs hds hchar * oddHomotopy d s hdd hs hds hchar = 0 ∧
    oddHomotopy d s hdd hs hds hchar * d * oddHomotopy d s hdd hs hds hchar =
      oddHomotopy d s hdd hs hds hchar ∧
    oddHomotopy d s hdd hs hds hchar * s = -(s * oddHomotopy d s hdd hs hds hchar) :=
  (exists_odd_strong_inverse d s hdd hs hds hchar).choose_spec

abbrev OddHomologyModel :=
  LinearMap.range (inverseProjection d (oddHomotopy d s hdd hs hds hchar))

def oddContraction :
    LinearContraction (R := K) (M := M) (H := OddHomologyModel d s hdd hs hds hchar) :=
  contractionOfInverse d (oddHomotopy d s hdd hs hds hchar) hdd
    (oddHomotopy_spec d s hdd hs hds hchar).1
    (oddHomotopy_spec d s hdd hs hds hchar).2.1
    (oddHomotopy_spec d s hdd hs hds hchar).2.2.1

@[simp] theorem oddContraction_d : (oddContraction d s hdd hs hds hchar).d = d := rfl

theorem oddContraction_parity :
    s * (oddContraction d s hdd hs hds hchar).h +
      (oddContraction d s hdd hs hds hchar).h * s = 0 := by
  change s * oddHomotopy d s hdd hs hds hchar +
    oddHomotopy d s hdd hs hds hchar * s = 0
  rw [(oddHomotopy_spec d s hdd hs hds hchar).2.2.2, add_neg_cancel]

end Field
end FourPapers.HomologicalPerturbation

#print axioms FourPapers.HomologicalPerturbation.oddContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyMapInjection -/
section

/-!
# Injection of the actual filtered homology map

An injective associated homology map reflects boundaries when the target
boundary differential has actual leading-cycle lifts. The proof lowers a
finite natural filtration index; it uses neither a dimension comparison
nor a choice of an unrelated injection between the homology modules.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.FilteredHomology

variable {K X Y Z X' Y' Z' : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']

def filteredCycleMap
    (G : Filtration (K := K) Y) (G' : Filtration (K := K) Y')
    (g : Y →ₗ[K] Z) (g' : Y' →ₗ[K] Z')
    (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hgc : ∀ y, c (g y) = g' (b y)) (hb : Preserves G G' b) (n : ℕ) :
    cycleLevel G g n →ₗ[K] cycleLevel G' g' n :=
  ((threeTermCycleMap g g' b c hgc).comp (cycleLevel G g n).subtype).codRestrict _
    (fun z => hb n z.val.val z.property)

variable
  (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (H : Filtration (K := K) Z)
  (F' : Filtration (K := K) X') (G' : Filtration (K := K) Y')
  (H' : Filtration (K := K) Z')
  (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
  (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
  (hf : Preserves F G f) (hg : Preserves G H g)
  (hf' : Preserves F' G' f') (hg' : Preserves G' H' g')
  (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
  (hfa : ∀ x, b (f x) = f' (a x)) (hgc : ∀ y, c (g y) = g' (b y))
  (hb : Preserves G G' b)
  (ψ : ∀ n, GradedHomology F G H f g hf hg hfg n →ₗ[K]
    GradedHomology F' G' H' f' g' hf' hg' hfg' n)
  (hψ : ∀ n (z : cycleLevel G g (n + 1)),
    ψ n (leadingHomologyClass F G H f g hf hg hfg n z) =
      leadingHomologyClass F' G' H' f' g' hf' hg' hfg' n
        (filteredCycleMap G G' g g' b c hgc hb (n + 1) z))
  (hψinj : ∀ n, Function.Injective (ψ n))
  (hlift : LiftsCycles F' G' f')

include hfa hgc hb hψ hψinj hlift in
/-- Every source cycle whose literal image is a boundary is filled in its
own filtration level. The supplied graded maps must commute with the actual
leading classes; their injectivity is used on those specific classes. -/
theorem boundary_reflects_of_gradedMap (n : ℕ) (y : Y)
    (hy : y ∈ G.level n) (hgy : g y = 0) (hby : ∃ w, f' w = b y) :
    ∃ x, x ∈ F.level n ∧ f x = y := by
  induction n generalizing y with
  | zero =>
      have hy0 : y = 0 := by simpa only [G.zero, Submodule.mem_bot] using hy
      exact ⟨0, (F.level 0).zero_mem, (f.map_zero).trans hy0.symm⟩
  | succ n ih =>
      let z : cycleLevel G g (n + 1) := ⟨⟨y, hgy⟩, hy⟩
      obtain ⟨w, hw⟩ := hby
      have hfw : f' w ∈ G'.level (n + 1) := by
        rw [hw]
        exact hb (n + 1) y hy
      obtain ⟨w', hw', he⟩ := strict_of_liftsCycles F' G' f' hlift (n + 1) w hfw
      have htarget : leadingHomologyClass F' G' H' f' g' hf' hg' hfg' n
          (filteredCycleMap G G' g g' b c hgc hb (n + 1) z) = 0 := by
        apply (leadingHomologyClass_eq_zero_iff F' G' H' f' g' hf' hg' hfg' n _).mpr
        refine ⟨w', hw', ?_⟩
        change b y - f' w' ∈ G'.level n
        rw [he, hw, sub_self]
        exact (G'.level n).zero_mem
      have hsource : leadingHomologyClass F G H f g hf hg hfg n z = 0 := by
        apply hψinj n
        rw [(ψ n).map_zero, hψ n z]
        exact htarget
      obtain ⟨x, hx, hrest⟩ :=
        (leadingHomologyClass_eq_zero_iff F G H f g hf hg hfg n z).mp hsource
      have hgrest : g (y - f x) = 0 := by
        rw [g.map_sub, hgy, show g (f x) = 0 from LinearMap.congr_fun hfg x, sub_self]
      have hbrest : ∃ v, f' v = b (y - f x) := by
        refine ⟨w - a x, ?_⟩
        rw [f'.map_sub, hw, ← hfa x, b.map_sub]
      obtain ⟨x', hx', hfx'⟩ := ih (y - f x) hrest hgrest hbrest
      refine ⟨x + x', (F.level (n + 1)).add_mem hx (F.mono (Nat.le_succ n) hx'), ?_⟩
      rw [f.map_add, hfx']
      abel

include hf hg hf' hg' hb hψ hψinj hlift in
/-- The induced map is the quotient map constructed from `a,b,c` themselves.
Only target boundary strictness is needed; no injectivity assumption on a
chain group, no rank inequality, and no source splitting is inserted. -/
theorem threeTermHomologyMap_injective_of_gradedMap :
    Function.Injective (threeTermHomologyMap f g hfg f' g' hfg' a b c hfa hgc) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
  change threeTermHomologyMap f g hfg f' g' hfg' a b c hfa hgc
    (homologyClass f g hfg z) = 0 at hx
  rw [threeTermHomologyMap_class] at hx
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap f' g' hfg'))).mp hx
  have hfw : f' w = b z.val := congrArg Subtype.val hw
  obtain ⟨n, hn⟩ := G.exhaustive z.val
  obtain ⟨y, _, hy⟩ := boundary_reflects_of_gradedMap
    F G H F' G' H' f g hfg f' g' hfg' hf hg hf' hg'
    a b c hfa hgc hb ψ hψ hψinj hlift n z.val hn z.property ⟨w, hfw⟩
  apply (Submodule.mem_bot K).mpr
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (boundaryMap f g hfg))).mpr
  exact ⟨y, Subtype.ext hy⟩

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyRetraction -/
section

/-!
# Injectivity from an actual retraction of the leading chain map

The retraction need commute only with the special differentials. Its defect
for the original differentials strictly lowers the filtration. Target cycle
lifting gives a bounded preimage of every boundary; finite downward correction
then proves that the original chain map reflects boundaries.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.FilteredHomology

variable {K X Y : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (d d₀ : Module.End K X) (e e₀ : Module.End K Y)
  (hdd : d.comp d = 0) (hee : e.comp e = 0)
  (b : X →ₗ[K] Y) (r : Y →ₗ[K] X)
  (hb : Preserves F G b) (hr : Preserves G F r)
  (hchain : ∀ x, b (d x) = e (b x))
  (hretract : ∀ x, r (b x) = x)
  (hspecial : ∀ y, r (e₀ y) = d₀ (r y))
  (hdifference : ∀ n x, x ∈ F.level (n+1) → d x - d₀ x ∈ F.level n)
  (hedifference : ∀ n y, y ∈ G.level (n+1) → e y - e₀ y ∈ G.level n)
  (hlift : LiftsCycles G G e)

include hb hr hchain hretract hspecial hdifference hedifference hlift hdd in
theorem boundary_reflects_of_filtered_retraction
    (x : X) (hx : d x = 0) (hbx : b x ∈ LinearMap.range e) :
    x ∈ LinearMap.range d := by
  obtain ⟨n, hn⟩ := F.exhaustive x
  induction n generalizing x with
  | zero =>
      have hx0 : x = 0 := by simpa only [F.zero, Submodule.mem_bot] using hn
      simpa only [hx0] using (LinearMap.range d).zero_mem
  | succ n ih =>
      obtain ⟨y, hy⟩ := hbx
      have hey : e y ∈ G.level (n+1) := hy.symm ▸ hb (n+1) x hn
      obtain ⟨z, hz, hez⟩ := strict_of_liftsCycles G G e hlift (n+1) y hey
      have hezb : e z = b x := hez.trans hy
      have hR : r z ∈ F.level (n+1) := hr (n+1) z hz
      have hlower : x - d (r z) ∈ F.level n := by
        have he := hr n (e z - e₀ z) (hedifference n z hz)
        have hd := hdifference n (r z) hR
        have hid : r (e z - e₀ z) - (d (r z) - d₀ (r z)) = x - d (r z) := by
          rw [map_sub, hezb, hretract, hspecial]
          abel
        exact hid ▸ (F.level n).sub_mem he hd
      have hcycle : d (x - d (r z)) = 0 := by
        rw [map_sub, hx, show d (d (r z)) = 0 from LinearMap.congr_fun hdd (r z), sub_self]
      have hboundary : b (x - d (r z)) ∈ LinearMap.range e := by
        refine ⟨z - b (r z), ?_⟩
        rw [map_sub, map_sub, hchain, hezb]
      obtain ⟨a, ha⟩ := ih (x - d (r z)) hcycle hboundary hlower
      refine ⟨r z + a, ?_⟩
      rw [map_add, ha]
      abel

include hb hr hchain hretract hspecial hdifference hedifference hlift in
/-- The injective map is induced by the given original chain map `b`.
No identification or arbitrary injection is substituted for that map. -/
theorem threeTermHomologyMap_injective_of_filtered_retraction :
    Function.Injective
      (threeTermHomologyMap d d hdd e e hee b b b hchain hchain) := by
  apply threeTermHomologyMap_injective_of_reflects_boundaries
  intro x hx hbx
  exact boundary_reflects_of_filtered_retraction F G d d₀ e e₀ hdd b r
    hb hr hchain hretract hspecial hdifference hedifference hlift x hx hbx

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ThreeTermHomologyBoundaryReflection -/
section

/-! # Injective homology maps reflect actual boundaries -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.FilteredHomology

variable {K X Y Z X' Y' Z' : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']

/-- An injective induced homology map reflects boundaries of cycles.
All structure maps are inferred from the given, already constructed map;
the conclusion retains actual chain representatives and actual fillings. -/
theorem threeTermHomologyMap_reflects_boundaries_of_injective
    {f : X →ₗ[K] Y} {g : Y →ₗ[K] Z} {hfg : g.comp f = 0}
    {f' : X' →ₗ[K] Y'} {g' : Y' →ₗ[K] Z'} {hfg' : g'.comp f' = 0}
    {a : X →ₗ[K] X'} {b : Y →ₗ[K] Y'} {c : Z →ₗ[K] Z'}
    {hf : ∀ x, b (f x) = f' (a x)}
    {hg : ∀ y, c (g y) = g' (b y)}
    (hinj : Function.Injective (threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg))
    (y : Y) (hy : g y = 0) (hb : ∃ x', f' x' = b y) :
    ∃ x, f x = y := by
  let z : LinearMap.ker g := ⟨y, hy⟩
  have hm : threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg
      (homologyClass f g hfg z) = 0 := by
    rw [threeTermHomologyMap_class]
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (boundaryMap f' g' hfg'))).mpr
    obtain ⟨x', hx'⟩ := hb
    exact ⟨x', Subtype.ext hx'⟩
  have hz : homologyClass f g hfg z = 0 :=
    hinj (hm.trans (threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg).map_zero.symm)
  obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap f g hfg))).mp hz
  exact ⟨x, congrArg Subtype.val hx⟩

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.MonomialIdealCoefficientChange -/
section

/-! # Actual monomial ideals under arbitrary coefficient base change -/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
variable {R A X : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype X] [LinearOrder X] (B : Family X)

theorem coefficientIdeal_restrict_eq_span (k : Type*) [CommRing k] :
    (monomialIdeal k B).restrictScalars k=
      Submodule.span k ((MvPolynomial.basisMonomials X k) '' {a | Contains B a}) := by
  ext f
  change f∈monomialIdeal k B ↔ _
  rw [mem_monomialIdeal_iff,Module.Basis.mem_span_image]
  rfl

def coefficientIdealScalarEquiv (k : Type*) [CommRing k] :
    (monomialIdeal k B).restrictScalars k ≃ₗ[k] monomialIdeal k B where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The span presentation and the literal ideal are identified by the
underlying polynomial, avoiding a transport of module structures. -/
def coefficientIdealSpanEquiv (k : Type*) [CommRing k] :
    Submodule.span k ((MvPolynomial.basisMonomials X k) '' {a | Contains B a})
      ≃ₗ[k] monomialIdeal k B where
  toFun x := ⟨x.val, (coefficientIdeal_restrict_eq_span B k).ge x.property⟩
  invFun x := ⟨x.val, (coefficientIdeal_restrict_eq_span B k).le x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient and exponent universes are independent, permitting
the literal coefficient ring ℤ with variables in any universe. -/
def coefficientIdealBasis (k : Type*) [CommRing k] :
    Module.Basis {a : Exponent X // Contains B a} k (monomialIdeal k B) :=
  (Grading.restrictedBasis (MvPolynomial.basisMonomials X k) (Contains B)).map
    (coefficientIdealSpanEquiv B k)

@[simp] theorem coefficientIdealBasis_val (k : Type*) [CommRing k]
    (a : {a : Exponent X // Contains B a}) :
    (coefficientIdealBasis B k a).val=MvPolynomial.monomial a.val 1 := by
  change (Grading.restrictedBasis (MvPolynomial.basisMonomials X k) (Contains B) a).val = _
  exact Grading.restrictedBasis_val _ _ _

def monomialIdealCoefficientEquiv :
    (A ⊗[R] monomialIdeal R B) ≃ₗ[A] monomialIdeal A B :=
  ((coefficientIdealBasis B R).baseChange A).equiv (coefficientIdealBasis B A) (Equiv.refl _)

theorem monomialIdealCoefficientEquiv_tmul_val (a : A) (f : monomialIdeal R B) :
    (monomialIdealCoefficientEquiv B (a ⊗ₜ[R] f)).val=
      a • MvPolynomial.map (algebraMap R A) f.val := by
  have he : ((monomialIdeal A B).restrictScalars A).subtype.comp
      (monomialIdealCoefficientEquiv (R:=R) (A:=A) B).toLinearMap =
        (MvPolynomial.algebraTensorAlgEquiv R A).toLinearEquiv.toLinearMap.comp
          (((monomialIdeal R B).restrictScalars R).subtype.baseChange A) := by
    apply ((coefficientIdealBasis B R).baseChange A).ext
    intro b
    change (monomialIdealCoefficientEquiv (R:=R) (A:=A) B
      (((coefficientIdealBasis B R).baseChange A) b)).val = _
    rw [show monomialIdealCoefficientEquiv (R:=R) (A:=A) B
        (((coefficientIdealBasis B R).baseChange A) b) = coefficientIdealBasis B A b from
      Module.Basis.equiv_apply (b := (coefficientIdealBasis B R).baseChange A)
        (b' := coefficientIdealBasis B A) (e := Equiv.refl _) (i := b)]
    rw [LinearMap.comp_apply, Module.Basis.baseChange_apply]
    change (coefficientIdealBasis B A b).val =
      MvPolynomial.algebraTensorAlgEquiv R A
        ((((monomialIdeal R B).restrictScalars R).subtype.baseChange A)
          (1 ⊗ₜ[R] coefficientIdealBasis B R b))
    rw [LinearMap.baseChange_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp only [Submodule.subtype_apply, coefficientIdealBasis_val,
      MvPolynomial.map_monomial, map_one, one_smul]
  have hh := LinearMap.congr_fun he (a ⊗ₜ[R] f)
  change (monomialIdealCoefficientEquiv B (a ⊗ₜ[R] f)).val =
    MvPolynomial.algebraTensorAlgEquiv R A
      ((((monomialIdeal R B).restrictScalars R).subtype.baseChange A) (a ⊗ₜ[R] f)) at hh
  rw [LinearMap.baseChange_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul] at hh
  exact hh

def monomialIdealCoefficientRealization :
    PolynomialCoefficientBaseChange.Realization (R:=R) (V:=X) A
      (monomialIdeal R B) (monomialIdeal A B) where
  equivalence := monomialIdealCoefficientEquiv B
  multiply p z := by
    apply Subtype.ext
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add,smul_add,Submodule.coe_add,hx,hy,mul_add]
    | tmul a f =>
        simp only [LinearMap.baseChange_tmul,monomialIdealCoefficientEquiv_tmul_val,
          PolynomialCoefficientBaseChange.sourceMultiply_apply,Submodule.coe_smul,
          smul_eq_mul,map_mul,mul_smul_comm]

end FourPapers

end
end
end


end
