module

public import PaperVerification.FermionRadical
public import PaperVerification.FermionLocalRoots
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The actual separated ordinary quotient and its local coefficient rings

The coefficient algebra is the quotient by the literal first-n moment
equations. Finiteness and Artinianness follow from the weighted radical
argument, rather than being part of the data.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped BigOperators Classical

variable {F : Type*} [Field F] {n : ℕ}

structure SeparatedOrdinaryData (F : Type*) [Field F] (n : ℕ) where
  beta : Fin n → F
  G : Polynomial F
  phi : Fin n → Polynomial F
  beta_units : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i)
  G_monic : G.Monic
  G_pos : 0<G.natDegree
  phi_monic : ∀ i,(phi i).Monic
  phi_pos : ∀ i,0<(phi i).natDegree

namespace SeparatedOrdinaryData

variable (d : SeparatedOrdinaryData F n)

abbrev Ordinary := MvPolynomial (Fin n) F ⧸ separatedOrdinaryIdeal d.beta d.G d.phi

def ordinaryMk : MvPolynomial (Fin n) F →ₐ[F] d.Ordinary :=
  Ideal.Quotient.mkₐ F (separatedOrdinaryIdeal d.beta d.G d.phi)

def ordinaryX (i : Fin n) : d.Ordinary := d.ordinaryMk (MvPolynomial.X i)

def ordinaryNode (i : Fin n) : d.Ordinary :=
  Polynomial.aeval (d.ordinaryX i) (d.phi i)

instance ordinary_finite : Module.Finite F d.Ordinary :=
  separated_ordinary_finite d.beta d.G d.phi d.beta_units
    (fun i ↦ d.G_monic.comp (d.phi_monic i) (d.phi_pos i).ne')

instance ordinary_artinian : IsArtinianRing d.Ordinary :=
  IsArtinianRing.of_finite F d.Ordinary

theorem ordinaryX_aeval_eq_mk :
    MvPolynomial.aeval (R := F) d.ordinaryX=d.ordinaryMk := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [ordinaryX]

theorem ordinaryX_generates : Function.Surjective (MvPolynomial.aeval (R := F) d.ordinaryX) := by
  rw [d.ordinaryX_aeval_eq_mk]
  exact Ideal.Quotient.mkₐ_surjective F _

theorem ordinary_moments (k : ℕ) :
    ∑ i,algebraMap F d.Ordinary (d.beta i)*d.ordinaryNode i^k*
      Polynomial.aeval (d.ordinaryNode i) d.G=0 := by
  have h := ordinaryMoment_mem
    (fun i ↦ Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i)) d.beta d.G k
  have hz : d.ordinaryMk
      (moment (fun i ↦ Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i))
        (fun i ↦ algebraMap F (MvPolynomial (Fin n) F) (d.beta i) *
          Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i)) d.G) k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h
  simpa only [moment,smul_eq_mul,map_sum,map_mul,map_pow,d.ordinaryMk.commutes,
    ←Polynomial.aeval_algHom_apply,ordinaryNode,ordinaryX,mul_left_comm,mul_assoc] using hz

/-- A point in the actual finite support; no choice of ordering of roots. -/
abbrev SupportPoint :=
  {rho : Fin n → F // ∀ i,d.G.eval ((d.phi i).eval (rho i))=0}

def pointEval (rho : d.SupportPoint) : MvPolynomial (Fin n) F →ₐ[F] F :=
  MvPolynomial.aeval rho.1

theorem pointEval_kills (rho : d.SupportPoint) :
    separatedOrdinaryIdeal d.beta d.G d.phi ≤ RingHom.ker (d.pointEval rho).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨k,rfl⟩
  change d.pointEval rho
    (moment (fun i ↦ Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i))
      (fun i ↦ algebraMap F (MvPolynomial (Fin n) F) (d.beta i)*
        Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i)) d.G) k)=0
  have hphi (i : Fin n) :
      d.pointEval rho
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i)) =
      (d.phi i).eval (rho.1 i) := by
    rw [←Polynomial.aeval_algHom_apply]
    rw [show d.pointEval rho (MvPolynomial.X i)=rho.1 i from
      MvPolynomial.aeval_X rho.1 i]
    rfl
  have hG (i : Fin n) :
      d.pointEval rho (Polynomial.aeval
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (d.phi i)) d.G)=0 := by
    rw [←Polynomial.aeval_algHom_apply,hphi]
    exact rho.property i
  simp only [moment,smul_eq_mul,map_sum,map_mul,map_pow,hG,mul_zero,Finset.sum_const_zero]

def pointResidue (rho : d.SupportPoint) : d.Ordinary →ₐ[F] F :=
  Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
    (d.pointEval rho) (fun p hp ↦ d.pointEval_kills rho hp)

@[simp] theorem pointResidue_x (rho : d.SupportPoint) (i : Fin n) :
    d.pointResidue rho (d.ordinaryX i)=rho.1 i := by
  simp [pointResidue,ordinaryX,ordinaryMk,pointEval]

def pointMaximal (rho : d.SupportPoint) : Ideal d.Ordinary :=
  RingHom.ker (d.pointResidue rho).toRingHom

instance pointMaximal_isMaximal (rho : d.SupportPoint) : (d.pointMaximal rho).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (d.pointResidue rho).toRingHom
    (residueAlgHom_surjective (d.pointResidue rho))

abbrev LocalOrdinary (rho : d.SupportPoint) := Localization.AtPrime (d.pointMaximal rho)

def localMap (rho : d.SupportPoint) : d.Ordinary →ₐ[F] d.LocalOrdinary rho :=
  Algebra.algHom F _ _

def localX (rho : d.SupportPoint) (i : Fin n) : d.LocalOrdinary rho :=
  d.localMap rho (d.ordinaryX i)

def localNode (rho : d.SupportPoint) (i : Fin n) : d.LocalOrdinary rho :=
  Polynomial.aeval (d.localX rho i) (d.phi i)

instance localOrdinary_localRing (rho : d.SupportPoint) : IsLocalRing (d.LocalOrdinary rho) :=
  IsLocalization.AtPrime.isLocalRing _ (d.pointMaximal rho)

instance localOrdinary_artinian (rho : d.SupportPoint) : IsArtinianRing (d.LocalOrdinary rho) :=
  IsArtinianRing.localization_artinian (d.pointMaximal rho).primeCompl _

def localResidue (rho : d.SupportPoint) : d.LocalOrdinary rho →ₐ[F] F :=
  IsLocalization.liftAlgHom (f := d.pointResidue rho)
    (fun y : (d.pointMaximal rho).primeCompl ↦ isUnit_iff_ne_zero.mpr y.property)

@[simp] theorem localResidue_map (rho : d.SupportPoint) (a : d.Ordinary) :
    d.localResidue rho (d.localMap rho a)=d.pointResidue rho a :=
  IsLocalization.lift_eq _ a

@[simp] theorem localResidue_x (rho : d.SupportPoint) (i : Fin n) :
    d.localResidue rho (d.localX rho i)=rho.1 i := by
  simp [localX]

@[simp] theorem localResidue_node (rho : d.SupportPoint) (i : Fin n) :
    d.localResidue rho (d.localNode rho i)=(d.phi i).eval (rho.1 i) := by
  rw [localNode,←Polynomial.aeval_algHom_apply,localResidue_x]
  simp only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]

theorem localX_generates (rho : d.SupportPoint) :
    Function.Surjective (MvPolynomial.aeval (R := F) (d.localX rho)) := by
  have he : MvPolynomial.aeval (R := F) (d.localX rho)=
      (d.localMap rho).comp (MvPolynomial.aeval (R := F) d.ordinaryX) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [localX]
  rw [he]
  exact (IsArtinianRing.localization_surjective (d.pointMaximal rho).primeCompl
    (d.LocalOrdinary rho)).comp d.ordinaryX_generates

theorem local_hom_ext {A : Type*} [Semiring A] [Algebra F A] (rho : d.SupportPoint)
    {f g : d.LocalOrdinary rho →ₐ[F] A}
    (h : ∀ i,f (d.localX rho i)=g (d.localX rho i)) : f=g := by
  have he : f.comp (MvPolynomial.aeval (R := F) (d.localX rho))=
      g.comp (MvPolynomial.aeval (R := F) (d.localX rho)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_X] using h i
  apply AlgHom.ext
  intro a
  obtain ⟨p,rfl⟩ := d.localX_generates rho a
  exact AlgHom.congr_fun he p

theorem local_moments (rho : d.SupportPoint) (k : ℕ) :
    ∑ i,algebraMap F (d.LocalOrdinary rho) (d.beta i)*d.localNode rho i^k*
      Polynomial.aeval (d.localNode rho i) d.G=0 := by
  have h := congrArg (d.localMap rho) (d.ordinary_moments k)
  simpa only [map_sum,map_mul,map_pow,map_zero,(d.localMap rho).commutes,
    ←Polynomial.aeval_algHom_apply,ordinaryNode,localNode,localX] using h

/-- The residue-kernel is nilpotent in the actual Artinian localization. -/
theorem local_nilpotent_of_residue_zero (rho : d.SupportPoint)
    (a : d.LocalOrdinary rho) (ha : d.localResidue rho a=0) : IsNilpotent a := by
  have hm : a∈IsLocalRing.maximalIdeal (d.LocalOrdinary rho) := by
    have hk := residueAlgHom_ker (F := F) (A := d.LocalOrdinary rho) (d.localResidue rho)
    exact hk ▸ (show a∈RingHom.ker (d.localResidue rho).toRingHom from ha)
  have hj := IsLocalRing.jacobson_eq_maximalIdeal
    (R := d.LocalOrdinary rho) (I := ⊥)
      (show (⊥ : Ideal (d.LocalOrdinary rho))≠⊤ from bot_ne_top)
  have hn : IsNilpotent (IsLocalRing.maximalIdeal (d.LocalOrdinary rho)) :=
    hj ▸ IsArtinianRing.isNilpotent_jacobson_bot (R := d.LocalOrdinary rho)
  obtain ⟨N,hN⟩ := hn
  refine ⟨N,?_⟩
  have hp := Ideal.pow_mem_pow hm N
  rw [hN] at hp
  exact hp

theorem localX_centered_nilpotent (rho : d.SupportPoint) (i : Fin n) :
    IsNilpotent (d.localX rho i-algebraMap F (d.LocalOrdinary rho) (rho.1 i)) := by
  apply d.local_nilpotent_of_residue_zero rho
  simp only [map_sub,localResidue_x,(d.localResidue rho).commutes,
    Algebra.algebraMap_self,RingHom.id_apply,sub_self]

theorem localNode_centered_nilpotent (rho : d.SupportPoint) (i : Fin n) :
    IsNilpotent (d.localNode rho i-
      algebraMap F (d.LocalOrdinary rho) ((d.phi i).eval (rho.1 i))) := by
  apply d.local_nilpotent_of_residue_zero rho
  simp only [map_sub,localResidue_node,(d.localResidue rho).commutes,
    Algebra.algebraMap_self,RingHom.id_apply,sub_self]

theorem local_uniform_nilpotence (rho : d.SupportPoint) :
    ∃ N : ℕ,∀ i,(d.localNode rho i-
      algebraMap F (d.LocalOrdinary rho) ((d.phi i).eval (rho.1 i)))^N=0 := by
  choose N hN using d.localNode_centered_nilpotent rho
  refine ⟨Finset.univ.sup N,fun i ↦ ?_⟩
  exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hN i)

end SeparatedOrdinaryData
end PaperVerification.Fermion

