/-
The proof of `addMonoidAlgebra_localization` is an additive adaptation of
TauCeti.Algebra.MonoidAlgebra.Localization at commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362, released under Apache 2.0.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
-/
module

public import PaperVerification.SegreCechVanishing
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Coordinate localizations as literal Laurent monomial algebras

Inverting the product of the coordinates indexed by `S` gives exactly the
Laurent monomials whose exponents outside `S` are nonnegative. The proof gives
the full universal localization property; it does not merely embed a selected
finite set of fractions. This is the local algebra needed to connect the
monomial Čech calculation to sections on intersections of projective charts.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]

/-- Exponents of exactly the monomials available after inverting the coordinates in `S`. -/
def allowedExponents (S : Finset I) : AddSubmonoid (I → ℤ) where
  carrier := {a | ∀ i, i ∉ S → 0≤a i}
  zero_mem' := by intro i _; exact le_refl 0
  add_mem' ha hb := by intro i hi; exact add_nonneg (ha i hi) (hb i hi)

def naturalExponentMap (S : Finset I) : (I →₀ ℕ) →+ allowedExponents S where
  toFun a := ⟨fun i => (a i : ℤ),by intro i _; exact Int.natCast_nonneg _⟩
  map_zero' := Subtype.ext (by funext i; rfl)
  map_add' a b := Subtype.ext (by funext i; exact Int.natCast_add _ _)

theorem naturalExponentMap_injective (S : Finset I) : Function.Injective (naturalExponentMap S) := by
  intro a b hab
  ext i
  exact Int.natCast_inj.mp (congrFun (congrArg Subtype.val hab) i)

/-- The squarefree exponent of the product of the coordinates in `S`. -/
noncomputable def denominatorExponent (S : Finset I) : I →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem denominatorExponent_apply (S : Finset I) (i : I) :
    denominatorExponent S i=if i∈S then 1 else 0 := by
  classical
  simp [denominatorExponent,Finsupp.single_apply]

noncomputable def inverseDenominator (S : Finset I) : allowedExponents S :=
  ⟨fun i => if i∈S then -1 else 0,by intro i hi; simp only [if_neg hi,le_refl]⟩

theorem denominator_add_inverse (S : Finset I) :
    naturalExponentMap S (denominatorExponent S)+inverseDenominator S=0 := by
  apply Subtype.ext
  funext i
  change (denominatorExponent S i : ℤ)+(if i∈S then -1 else 0)=0
  rw [denominatorExponent_apply]
  split_ifs <;> rfl

/-- A common denominator clears every negative exponent in a Laurent monomial. -/
theorem exponent_clear_denominator (S : Finset I) (a : allowedExponents S) :
    ∃ m : ℕ, a+m • naturalExponentMap S (denominatorExponent S) ∈ Set.range (naturalExponentMap S) := by
  classical
  let m : ℕ := ∑ i, (-a.val i).toNat
  have hm (i : I) : (-a.val i).toNat≤m := by
    change (-a.val i).toNat≤∑ j,(-a.val j).toNat
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((-a.val j).toNat))
      (Finset.mem_univ i)
  have hn (i : I) : 0≤a.val i+(if i∈S then (m : ℤ) else 0) := by
    by_cases hi : i∈S
    · rw [if_pos hi]
      have := hm i
      have hc : -a.val i≤((-a.val i).toNat : ℤ) := by omega
      omega
    · rw [if_neg hi,add_zero]
      exact a.property i hi
  let b : I →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun i => (a.val i+(if i∈S then (m : ℤ) else 0)).toNat)
  refine ⟨m,b,?_⟩
  apply Subtype.ext
  funext i
  change ((a.val i+(if i∈S then (m : ℤ) else 0)).toNat : ℤ) =
    a.val i + m • ((denominatorExponent S i : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (hn i),denominatorExponent_apply]
  split_ifs <;> simp

/-- The exact monomial algebra of a coordinate localization. -/
abbrev LocalLaurent (K I : Type*) [CommRing K] (S : Finset I) :=
  AddMonoidAlgebra K (allowedExponents S)

noncomputable def localizationMap (S : Finset I) : MvPolynomial I K →ₐ[K] LocalLaurent K I S :=
  AddMonoidAlgebra.mapDomainAlgHom K K (naturalExponentMap S)

noncomputable instance localizationAlgebra (S : Finset I) :
    Algebra (MvPolynomial I K) (LocalLaurent K I S) :=
  (localizationMap (K := K) S).toRingHom.toAlgebra

theorem localizationMap_injective (S : Finset I) : Function.Injective (localizationMap (K := K) S) :=
  AddMonoidAlgebra.mapDomain_injective (naturalExponentMap_injective S)

/-- The image of the denominator monomial has its literal negative-exponent inverse. -/
theorem denominator_isUnit (S : Finset I) :
    IsUnit (AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)) := by
  refine ⟨⟨AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K),
    AddMonoidAlgebra.single (inverseDenominator S) 1,?_,?_⟩,rfl⟩
  · change AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)*
      AddMonoidAlgebra.single (inverseDenominator S) (1 : K)=1
    rw [AddMonoidAlgebra.single_mul_single,denominator_add_inverse,one_mul,
      ← AddMonoidAlgebra.one_def]
  · change AddMonoidAlgebra.single (inverseDenominator S) (1 : K)*
      AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) (1 : K)=1
    rw [AddMonoidAlgebra.single_mul_single,add_comm,denominator_add_inverse,one_mul,
      ← AddMonoidAlgebra.one_def]

section GeneralMonoidLocalization

variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]

/-- The induced monoid-algebra map has the full localization property. -/
theorem addMonoidAlgebra_localization (f : M →+ N) (hf : Function.Injective f) (x : M)
    (hx : IsUnit (AddMonoidAlgebra.single (f x) (1 : K)))
    (hsurj : ∀ y : N, ∃ m : ℕ, y+m • f x ∈ Set.range f) :
    letI := (AddMonoidAlgebra.mapDomainRingHom K f).toAlgebra
    IsLocalization.Away (AddMonoidAlgebra.single x (1 : K)) (AddMonoidAlgebra K N) := by
  letI := (AddMonoidAlgebra.mapDomainRingHom K f).toAlgebra
  have halg : ∀ a : AddMonoidAlgebra K M,
      algebraMap (AddMonoidAlgebra K M) (AddMonoidAlgebra K N) a =
        AddMonoidAlgebra.mapDomain f a := fun a => by
    rw [RingHom.algebraMap_toAlgebra,AddMonoidAlgebra.mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [halg,AddMonoidAlgebra.mapDomain_single]
    exact hx
  · intro s
    induction s using AddMonoidAlgebra.induction_on with
    | of y =>
      obtain ⟨m,z,hz⟩ := hsurj y
      refine ⟨m,AddMonoidAlgebra.single z 1,?_⟩
      simp [halg,hz]
    | add s t hs ht =>
      obtain ⟨m,a,ha⟩ := hs
      obtain ⟨r,b,hb⟩ := ht
      refine ⟨m+r,a*AddMonoidAlgebra.single x 1^r+b*AddMonoidAlgebra.single x 1^m,?_⟩
      simp only [map_add,map_mul,map_pow]
      rw [← ha,← hb]
      ring
    | smul c s hs =>
      obtain ⟨m,a,ha⟩ := hs
      refine ⟨m,algebraMap K (AddMonoidAlgebra K M) c*a,?_⟩
      have ha' : s*AddMonoidAlgebra.mapDomain f (AddMonoidAlgebra.single x 1)^m =
          AddMonoidAlgebra.mapDomain f a := by simpa only [halg] using ha
      simp only [Algebra.smul_def,halg]
      rw [mul_assoc,ha',AddMonoidAlgebra.mapDomain_mul]
      congr 1
      exact ((AddMonoidAlgebra.mapDomainAlgHom K K f).commutes c).symm
  · intro a b hab
    exact ⟨0,by rw [AddMonoidAlgebra.mapDomain_injective hf hab]⟩

end GeneralMonoidLocalization

theorem denominator_monomial_eq_prod (S : Finset I) :
    MvPolynomial.monomial (denominatorExponent S) (1 : K) = ∏ i ∈ S, MvPolynomial.X i := by
  rw [denominatorExponent,MvPolynomial.monomial_sum_one]
  rfl

/-- All and only coordinate Laurent polynomials form the standard coordinate localization. -/
noncomputable instance localLaurent_isLocalization (S : Finset I) :
    IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K)) (LocalLaurent K I S) := by
  rw [← denominator_monomial_eq_prod]
  exact addMonoidAlgebra_localization (naturalExponentMap S) (naturalExponentMap_injective S)
    (denominatorExponent S) (denominator_isUnit S) (exponent_clear_denominator S)

/-- The actual localization is canonically the Laurent coefficient model. -/
noncomputable def coordinateLocalizationEquiv (S : Finset I) :
    Localization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K)) ≃ₐ[MvPolynomial I K]
      LocalLaurent K I S :=
  IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K))) _ _

end PaperVerification.Segre.CoordinateLocalization
