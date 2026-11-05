module

public import PaperVerification.FermionLocalCoefficientTransport
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exact support indexing of the Artinian product

Every maximal ideal is recovered from a point with G(phi_i(rho_i))=0, using
finiteness of the actual ordinary quotient and algebraic closedness. Thus the
product index is the paper's actual support, not a selected subset of points.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

theorem residueAlgHom_eq_of_ker_eq {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (f g : A →ₐ[F] F) (h : RingHom.ker f.toRingHom=RingHom.ker g.toRingHom) : f=g := by
  apply AlgHom.ext
  intro a
  have hf : a-algebraMap F A (f a)∈RingHom.ker f.toRingHom := by
    change f (a-algebraMap F A (f a))=0
    simp only [map_sub,f.commutes,Algebra.algebraMap_self,RingHom.id_apply,sub_self]
  rw [h] at hf
  change g (a-algebraMap F A (f a))=0 at hf
  have he : g a-f a=0 := by
    simpa only [map_sub,g.commutes,Algebra.algebraMap_self,RingHom.id_apply] using hf
  exact (sub_eq_zero.mp he).symm

namespace SeparatedOrdinaryData
variable {F : Type*} [Field F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n)

theorem ordinary_hom_ext {A : Type*} [Semiring A] [Algebra F A]
    {f g : d.Ordinary →ₐ[F] A}
    (h : ∀ i,f (d.ordinaryX i)=g (d.ordinaryX i)) : f=g := by
  apply Ideal.Quotient.algHom_ext F
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

def maximalFieldEquiv (m : MaximalSpectrum d.Ordinary) :
    F ≃ₐ[F] (d.Ordinary ⧸ m.asIdeal) := by
  letI : Field (d.Ordinary ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact AlgEquiv.ofBijective (Algebra.ofId F (d.Ordinary ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

def maximalResidue (m : MaximalSpectrum d.Ordinary) : d.Ordinary →ₐ[F] F :=
  (d.maximalFieldEquiv m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ F m.asIdeal)

theorem maximalResidue_kernel (m : MaximalSpectrum d.Ordinary) :
    RingHom.ker (d.maximalResidue m).toRingHom=m.asIdeal := by
  ext a
  change (d.maximalFieldEquiv m).symm (Ideal.Quotient.mk m.asIdeal a)=0 ↔ a∈m.asIdeal
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (d.maximalFieldEquiv m).symm.injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]

theorem maximalResidue_support (m : MaximalSpectrum d.Ordinary) (i : Fin n) :
    d.G.eval ((d.phi i).eval (d.maximalResidue m (d.ordinaryX i)))=0 := by
  let f := d.maximalResidue m
  have hmap (p : Polynomial F) (a : d.Ordinary) :
      f (Polynomial.aeval a p)=p.eval (f a) := by
    rw [←Polynomial.aeval_algHom_apply]
    simp only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]
  have hm : ∀ k : ℕ,∑ j,d.beta j*(f (d.ordinaryNode j))^k*
      d.G.eval (f (d.ordinaryNode j))=0 := by
    intro k
    have he := congrArg f (d.ordinary_moments k)
    simpa only [map_sum,map_mul,map_pow,map_zero,f.commutes,
      Algebra.algebraMap_self,RingHom.id_apply,hmap] using he
  have he := weighted_moments_zero_field d.beta (fun j ↦ f (d.ordinaryNode j))
    d.G.eval (fun U hU ↦ (d.beta_units U hU).ne_zero) hm i
  have hnode (j : Fin n) : f (d.ordinaryNode j)=(d.phi j).eval (f (d.ordinaryX j)) :=
    hmap (d.phi j) (d.ordinaryX j)
  simpa only [hnode,f] using he

def maximalPoint (m : MaximalSpectrum d.Ordinary) : d.SupportPoint :=
  ⟨fun i ↦ d.maximalResidue m (d.ordinaryX i),d.maximalResidue_support m⟩

theorem pointResidue_maximalPoint (m : MaximalSpectrum d.Ordinary) :
    d.pointResidue (d.maximalPoint m)=d.maximalResidue m := by
  apply d.ordinary_hom_ext
  intro i
  rw [d.pointResidue_x]
  rfl

theorem pointMaximal_maximalPoint (m : MaximalSpectrum d.Ordinary) :
    d.pointMaximal (d.maximalPoint m)=m.asIdeal := by
  rw [pointMaximal,d.pointResidue_maximalPoint,d.maximalResidue_kernel]

theorem pointMaximal_injective : Function.Injective d.pointMaximal := by
  intro rho sigma he
  have hf := residueAlgHom_eq_of_ker_eq (d.pointResidue rho) (d.pointResidue sigma) he
  apply Subtype.ext
  funext i
  simpa only [pointResidue_x] using AlgHom.congr_fun hf (d.ordinaryX i)

/-- Exact bijection of support points with all maximal ideals. -/
def supportEquivMaximal : d.SupportPoint ≃ MaximalSpectrum d.Ordinary :=
  Equiv.ofBijective (fun rho ↦ ⟨d.pointMaximal rho,inferInstance⟩)
    ⟨fun rho sigma he ↦ d.pointMaximal_injective
      (congrArg MaximalSpectrum.asIdeal he),
      fun m ↦ ⟨d.maximalPoint m,MaximalSpectrum.ext (d.pointMaximal_maximalPoint m)⟩⟩

instance supportPoint_finite : Finite d.SupportPoint :=
  Finite.of_equiv (MaximalSpectrum d.Ordinary) d.supportEquivMaximal.symm

end SeparatedOrdinaryData

namespace SeparatedPairedData
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n)

/-- The full algebra is the finite product of its actual local factors,
indexed by precisely the support points stated in the paper. -/
def superProductOverSupport :
    d.SuperQuotient ≃ₐ[F] ∀ rho : d.O.SupportPoint,d.LocalSuper rho :=
  ((d.superProductEquiv).restrictScalars F).trans
    ((AlgEquiv.piCongrLeft F
      (fun m : MaximalSpectrum d.O.Ordinary ↦
        Localization.AtPrime m.asIdeal ⊗[d.O.Ordinary] d.SuperQuotient)
      d.O.supportEquivMaximal).symm)

/-- A complete literal presentation of every factor of the original
global algebra, with its original roots and their ramification orders. -/
def superProductHomogeneousClusters :
    d.SuperQuotient ≃ₐ[F] ∀ rho : d.O.SupportPoint,d.HomogeneousClusterQuotient rho :=
  d.superProductOverSupport.trans
    (AlgEquiv.piCongrRight (fun rho ↦ d.localSuperEquivHomogeneousCluster rho))

end SeparatedPairedData
end PaperVerification.Fermion

