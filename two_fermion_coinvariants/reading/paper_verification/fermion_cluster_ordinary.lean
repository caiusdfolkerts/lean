module

public import PaperVerification.FermionMomentNilpotence
public import PaperVerification.FermionNilpotentPolynomial
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual homogeneous ordinary cluster presentation

Each cluster has its own moment equations. The ring below is the polynomial
quotient by those equations, not an algebra transported from a proposed local
factor. Its nilpotent coordinates, finite generation as a module, residue map,
and local-ring property are all derived from the presentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped Classical BigOperators
variable {R ι κ : Type*} [CommRing R] [Fintype ι]

def clusterPowerMoment (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ)
    (s : κ → ℕ) (c : κ) (k : ℕ) : MvPolynomial ι R :=
  ∑ i : {i : ι // cluster i=c},
    MvPolynomial.C (beta i.1)*MvPolynomial.X i.1^(r i.1*(s c+k))

def clusterPowerIdeal (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) :
    Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (fun p : κ×ℕ ↦ clusterPowerMoment beta cluster r s p.1 p.2))

abbrev ClusterOrdinary (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) :=
  MvPolynomial ι R ⧸ clusterPowerIdeal beta cluster r s

def clusterZ (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ)
    (i : ι) : ClusterOrdinary beta cluster r s :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem clusterPowerMoment_mem (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (c : κ) (k : ℕ) :
    clusterPowerMoment beta cluster r s c k∈clusterPowerIdeal beta cluster r s :=
  Ideal.subset_span ⟨(c,k),rfl⟩

theorem clusterZ_moments (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) (c : κ) (k : ℕ) :
    ∑ i : {i : ι // cluster i=c},
      algebraMap R (ClusterOrdinary beta cluster r s) (beta i.1)*
        clusterZ beta cluster r s i.1^(r i.1*(s c+k))=0 := by
  let q := Ideal.Quotient.mkₐ R (clusterPowerIdeal beta cluster r s)
  have h : q (clusterPowerMoment beta cluster r s c k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (clusterPowerMoment_mem beta cluster r s c k)
  have hC : ∀ a : R,q (MvPolynomial.C a)=algebraMap R _ a := fun a ↦ q.commutes a
  simpa only [clusterPowerMoment,map_sum,map_mul,map_pow,hC,clusterZ,q,
    Ideal.Quotient.mkₐ_eq_mk] using h

theorem subset_weights_restrict (beta : ι → R)
    (hbeta : ∀ t : Finset ι,t.Nonempty → IsUnit (∑ i∈t,beta i))
    (p : ι → Prop) [DecidablePred p] :
    ∀ t : Finset {i // p i},t.Nonempty → IsUnit (∑ i∈t,beta i.1) := by
  classical
  intro t ht
  let e : {i // p i} ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
  have hne : (t.map e).Nonempty := by
    obtain ⟨i,hi⟩ := ht
    exact ⟨e i,Finset.mem_map.mpr ⟨i,hi,rfl⟩⟩
  simpa only [Finset.sum_map,e,Function.Embedding.coeFn_mk] using hbeta (t.map e) hne

theorem clusterZ_nilpotent (beta : ι → R)
    (hbeta : ∀ t : Finset ι,t.Nonempty → IsUnit (∑ i∈t,beta i))
    (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (i : ι) :
    IsNilpotent (clusterZ beta cluster r s i) := by
  classical
  exact weighted_power_moments_nilpotent
    (fun j : {j : ι // cluster j=cluster i} ↦ beta j.1)
    (subset_weights_restrict beta hbeta (fun j ↦ cluster j=cluster i))
    (fun j ↦ clusterZ beta cluster r s j.1) (fun j ↦ r j.1) (s (cluster i))
    (clusterZ_moments beta cluster r s (cluster i)) ⟨i,rfl⟩

theorem clusterZ_aeval_eq_mk (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) :
    MvPolynomial.aeval (clusterZ beta cluster r s)=
      Ideal.Quotient.mkₐ R (clusterPowerIdeal beta cluster r s) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X,clusterZ,Ideal.Quotient.mkₐ_eq_mk]

theorem clusterZ_generates (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (s : κ → ℕ) :
    Function.Surjective (MvPolynomial.aeval (R := R) (clusterZ beta cluster r s)) := by
  rw [clusterZ_aeval_eq_mk]
  exact Ideal.Quotient.mkₐ_surjective R _

theorem clusterOrdinary_finite (beta : ι → R)
    (hbeta : ∀ t : Finset ι,t.Nonempty → IsUnit (∑ i∈t,beta i))
    (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) :
    Module.Finite R (ClusterOrdinary beta cluster r s) :=
  finite_of_nilpotent_polynomial_generators (clusterZ beta cluster r s)
    (clusterZ_nilpotent beta hbeta cluster r s)
    (clusterZ_generates beta cluster r s)

section Universal

variable {A : Type*} [CommRing A] [Algebra R A]
variable (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ)

def clusterOrdinaryLift (z : ι → A)
    (hm : ∀ c k,∑ i : {i : ι // cluster i=c},
      algebraMap R A (beta i.1)*z i.1^(r i.1*(s c+k))=0) :
    ClusterOrdinary beta cluster r s →ₐ[R] A :=
  Ideal.Quotient.liftₐ (clusterPowerIdeal beta cluster r s)
    (MvPolynomial.aeval z) (by
      have hle : clusterPowerIdeal beta cluster r s ≤
          RingHom.ker (MvPolynomial.aeval (R := R) z).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨⟨c,k⟩,rfl⟩
        change MvPolynomial.aeval z (clusterPowerMoment beta cluster r s c k)=0
        simpa only [clusterPowerMoment,map_sum,map_mul,map_pow,
          MvPolynomial.aeval_C,MvPolynomial.aeval_X] using hm c k
      exact fun p hp ↦ hle hp)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem clusterOrdinaryLift_z (z : ι → A)
    (hm : ∀ c k,∑ i : {i : ι // cluster i=c},
      algebraMap R A (beta i.1)*z i.1^(r i.1*(s c+k))=0) (i : ι) :
    clusterOrdinaryLift beta cluster r s z hm (clusterZ beta cluster r s i)=z i := by
  change (MvPolynomial.aeval (R := R) z) (MvPolynomial.X i)=z i
  exact MvPolynomial.aeval_X z i

theorem clusterOrdinary_hom_ext
    {f g : ClusterOrdinary beta cluster r s →ₐ[R] A}
    (h : ∀ i,f (clusterZ beta cluster r s i)=g (clusterZ beta cluster r s i)) : f=g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end Universal

def clusterResidue (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (hr : ∀ i,0<r i) (s : κ → ℕ) (hs : ∀ i,0<s (cluster i)) :
    ClusterOrdinary beta cluster r s →ₐ[R] R :=
  clusterOrdinaryLift beta cluster r s (fun _ ↦ 0) (by
    intro c k
    apply Finset.sum_eq_zero
    intro i hi
    have hsc : 0<s c := by simpa only [i.property] using hs i.1
    simp only [zero_pow (Nat.ne_of_gt (Nat.mul_pos (hr i.1)
      (lt_of_lt_of_le hsc (Nat.le_add_right _ _)))),mul_zero])

@[simp] theorem clusterResidue_z (beta : ι → R) (cluster : ι → κ)
    (r : ι → ℕ) (hr : ∀ i,0<r i) (s : κ → ℕ) (hs : ∀ i,0<s (cluster i)) (i : ι) :
    clusterResidue beta cluster r hr s hs (clusterZ beta cluster r s i)=0 := by
  exact clusterOrdinaryLift_z beta cluster r s (fun _ ↦ 0) _ i

section Field

variable {F : Type*} [Field F]

theorem clusterOrdinary_unit_iff_residue (beta : ι → F)
    (hbeta : ∀ t : Finset ι,t.Nonempty → IsUnit (∑ i∈t,beta i))
    (cluster : ι → κ) (r : ι → ℕ) (hr : ∀ i,0<r i)
    (s : κ → ℕ) (hs : ∀ i,0<s (cluster i))
    (a : ClusterOrdinary beta cluster r s) :
    IsUnit a ↔ clusterResidue beta cluster r hr s hs a≠0 :=
  unit_iff_residue_of_nilpotent_generators (clusterZ beta cluster r s)
    (clusterZ_nilpotent beta hbeta cluster r s) (clusterZ_generates beta cluster r s)
    (clusterResidue beta cluster r hr s hs) (clusterResidue_z beta cluster r hr s hs) a

theorem clusterOrdinary_localRing (beta : ι → F)
    (hbeta : ∀ t : Finset ι,t.Nonempty → IsUnit (∑ i∈t,beta i))
    (cluster : ι → κ) (r : ι → ℕ) (hr : ∀ i,0<r i)
    (s : κ → ℕ) (hs : ∀ i,0<s (cluster i)) :
    IsLocalRing (ClusterOrdinary beta cluster r s) :=
  localRing_of_nilpotent_generators (clusterZ beta cluster r s)
    (clusterZ_nilpotent beta hbeta cluster r s) (clusterZ_generates beta cluster r s)
    (clusterResidue beta cluster r hr s hs) (clusterResidue_z beta cluster r hr s hs)

end Field
end PaperVerification.Fermion
