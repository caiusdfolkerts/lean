module

public import PaperVerification.AlternatingFormsHibiPresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Removing the forbidden variables from the actual Richardson presentation

The source ring has exactly the interval variables. Its map to the full
Richardson quotient is proved surjective by setting the forbidden variables
to zero. Its kernel is the kernel of the literal band-minor substitution,
using the previously proved injectivity of the actual band chart map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

def goodBandMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K :=
  aeval (fun I => bandMinor α β I.val.val)

def goodBandIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  RingHom.ker (goodBandMap α β).toRingHom

def goodToInterval : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)).comp
    (rename (fun I : IntervalIndex α β => I.val))

def eraseForbidden : MvPolynomial (PluckerIndex s n) K →ₐ[K]
    MvPolynomial (IntervalIndex α β) K :=
  aeval (fun I => if h : ∀ i,α i≤I.val i ∧ I.val i≤β i then X ⟨I,h⟩ else 0)

theorem goodToInterval_eraseForbidden (p : MvPolynomial (PluckerIndex s n) K) :
    goodToInterval α β (eraseForbidden α β p)=Ideal.Quotient.mkₐ K _ p := by
  have he : (goodToInterval (K := K) α β).comp (eraseForbidden α β)=
      Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) := by
    apply MvPolynomial.algHom_ext
    intro I
    simp only [AlgHom.comp_apply,eraseForbidden,aeval_X]
    split_ifs with h
    · unfold goodToInterval
      simp only [AlgHom.comp_apply]
      erw [MvPolynomial.rename_X]
    · rw [map_zero]
      symm
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.subset_span ⟨I,h,rfl⟩))
  exact congrArg (fun f : MvPolynomial (PluckerIndex s n) K →ₐ[K]
    (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) => f p) he

theorem goodToInterval_surjective : Function.Surjective (goodToInterval (K := K) α β) := by
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K (intervalPluckerIdeal α β) z
  exact ⟨eraseForbidden α β p,goodToInterval_eraseForbidden α β p⟩

theorem intervalBandMap_goodToInterval (hα : Monotone α) (hβ : Monotone β)
    (p : MvPolynomial (IntervalIndex α β) K) :
    intervalBandMap α β hα hβ (goodToInterval α β p)=goodBandMap α β p := by
  have he : (intervalBandMap (K := K) α β hα hβ).comp (goodToInterval α β)=
      goodBandMap α β := by
    apply MvPolynomial.algHom_ext
    intro I
    unfold goodToInterval intervalBandMap goodBandMap bandPluckerMap
    simp only [AlgHom.comp_apply,rename_X,Ideal.Quotient.mkₐ_eq_mk]
    erw [Ideal.Quotient.liftₐ_apply,Ideal.Quotient.lift_mk,MvPolynomial.aeval_X]
    exact (MvPolynomial.aeval_X
      (fun J : IntervalIndex α β => bandMinor (K := K) α β J.val.val) I).symm
  exact congrArg (fun f : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K => f p) he

theorem goodToInterval_kernel (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    RingHom.ker (goodToInterval (K := K) α β).toRingHom=goodBandIdeal α β := by
  ext p
  change goodToInterval α β p=0 ↔ goodBandMap α β p=0
  rw [←intervalBandMap_goodToInterval α β hα hβ p,
    ←map_zero (intervalBandMap (K := K) α β hα hβ)]
  exact (intervalBandMap_injective α β hα hβ hs).eq_iff.symm

def goodBandQuotientEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    (MvPolynomial (IntervalIndex α β) K⧸goodBandIdeal α β) ≃ₐ[K]
      (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (Ideal.quotientEquivAlgOfEq K (goodToInterval_kernel α β hα hβ hs).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (goodToInterval_surjective α β))

@[simp] theorem goodBandQuotientEquiv_mk (hα : Monotone α) (hβ : Monotone β)
    (hs : 0<s) (p : MvPolynomial (IntervalIndex α β) K) :
    goodBandQuotientEquiv α β hα hβ hs (Ideal.Quotient.mk _ p)=goodToInterval α β p := by
  rfl

theorem goodBandMap_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    goodBandMap (K := K) α β (standardPolynomial α β C)=bandStandardProduct α β C := by
  unfold standardPolynomial bandStandardProduct
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact MvPolynomial.aeval_X (f := fun I : IntervalIndex α β =>
    bandMinor (K := K) α β I.val.val) (intervalIndexOfChain α β C i)

theorem goodToInterval_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    goodToInterval (K := K) α β (standardPolynomial α β C)=intervalStandardProduct α β C := by
  unfold goodToInterval standardPolynomial
  simp only [AlgHom.comp_apply,map_prod,intervalIndexOfChain,
    intervalStandardProduct,chainPluckerProduct,Ideal.Quotient.mkₐ_eq_mk,map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  erw [MvPolynomial.rename_X]

theorem goodBandMap_mem_standardSpan (hα : Monotone α) (hβ : Monotone β)
    (p : MvPolynomial (IntervalIndex α β) K) :
    goodBandMap α β p∈Submodule.span K
      (Set.range (fun C : Σ r,BandChain α β r =>
        goodBandMap α β (standardPolynomial α β C.2))) := by
  have h : goodToInterval α β p∈intervalStandardSpan (K := K) α β := by
    rw [intervalStandardSpan_eq_top]
    trivial
  rw [←intervalBandMap_goodToInterval α β hα hβ]
  generalize hz : goodToInterval α β p = z at h ⊢
  clear hz
  induction h using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨C,rfl⟩ := hz
      apply Submodule.subset_span
      exact ⟨C,by
        change goodBandMap α β (standardPolynomial α β C.2)=_
        rw [goodBandMap_standardPolynomial]
        exact (intervalBandMap_standardProduct α β hα hβ C.2).symm⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

end PaperVerification.AlternatingForms.Hibi
