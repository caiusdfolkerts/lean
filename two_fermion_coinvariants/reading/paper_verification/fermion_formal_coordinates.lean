module

public import PaperVerification.FermionRamification
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Genuine invertible ramified formal coordinates

Hensel lifting is used in F[[t]], not merely in a local quotient. The resulting
coordinate has invertible linear coefficient, so Mathlib's two-sided formal
substitution inverse gives an actual algebra automorphism. This supplies the
coordinate inverse required for the local factor theorem.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsLocalRing A]

/-- The root extraction lemma for a general Henselian local coefficient ring. -/
theorem exists_unit_root_henselian_with_residue
    [HenselianRing A (IsLocalRing.maximalIdeal A)]
    (residueMap : A →ₐ[F] F) (u : A) (r : ℕ) (hr : 0<r)
    (hrunit : IsUnit (r : A)) (c : F) (hc : c≠0) (hcr : c^r=residueMap u) :
    ∃ v : A,v^r=u ∧ residueMap v=c ∧ IsUnit v := by
  let f : Polynomial A := X^r-C u
  let a₀ : A := algebraMap F A c
  have ha₀ : IsUnit a₀ := (isUnit_iff_ne_zero.mpr hc).map (algebraMap F A)
  have hfa₀ : f.eval a₀∈IsLocalRing.maximalIdeal A := by
    rw [←residueAlgHom_ker residueMap,RingHom.mem_ker]
    simp only [f,eval_sub,eval_pow,eval_X,eval_C,map_sub,map_pow,a₀]
    change residueMap (algebraMap F A c)^r-residueMap u=0
    rw [residueMap.commutes]
    simp only [Algebra.algebraMap_self,RingHom.id_apply,hcr,sub_self]
  have hder : IsUnit (f.derivative.eval a₀) := by
    simpa only [f,derivative_sub,derivative_X_pow,derivative_C,sub_zero,
      eval_mul,eval_C,eval_pow,eval_X] using hrunit.mul (ha₀.pow (r-1))
  obtain ⟨v,hv,hva₀⟩ := HenselianRing.is_henselian
    (I := IsLocalRing.maximalIdeal A) f (monic_X_pow_sub_C u (Nat.ne_of_gt hr)) a₀ hfa₀
    (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  have hvr : v^r=u := by
    simpa only [Polynomial.IsRoot,f,eval_sub,eval_pow,eval_X,eval_C,sub_eq_zero] using hv
  have hvc : residueMap v=c := by
    rw [←residueAlgHom_ker residueMap,RingHom.mem_ker,map_sub] at hva₀
    have ha : residueMap a₀=c := by
      simpa only [a₀,Algebra.algebraMap_self,RingHom.id_apply] using residueMap.commutes c
    change residueMap v-residueMap a₀=0 at hva₀
    rwa [ha,sub_eq_zero] at hva₀
  exact ⟨v,hvr,hvc,(unit_iff_residue_ne_zero residueMap v).mpr (hvc.symm ▸ hc)⟩

def powerSeriesResidue : PowerSeries F →ₐ[F] F where
  toRingHom := PowerSeries.constantCoeff
  commutes' _ := rfl

variable [CharZero F] [IsAlgClosed F]

theorem exists_powerSeries_unit_root (u : PowerSeries F) (hu : IsUnit u)
    (r : ℕ) (hr : 0<r) :
    ∃ v : PowerSeries F,v^r=u ∧ IsUnit v := by
  letI : HenselianRing (PowerSeries F) (IsLocalRing.maximalIdeal (PowerSeries F)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hru : IsUnit (r : PowerSeries F) := by
    have h : IsUnit (r : F) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))
    simpa only [map_natCast] using h.map (algebraMap F (PowerSeries F))
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq (powerSeriesResidue u) hr
  have hc0 : c≠0 := by
    intro he
    have hz : powerSeriesResidue u=0 := by simpa only [he,zero_pow (Nat.ne_of_gt hr)] using hc.symm
    exact ((unit_iff_residue_ne_zero powerSeriesResidue u).mp hu) hz
  obtain ⟨v,hv,_,huv⟩ :=
    exists_unit_root_henselian_with_residue powerSeriesResidue u r hr hru c hc0 hc
  exact ⟨v,hv,huv⟩

/-- Substitution by a series with invertible linear coefficient is an
algebra automorphism, with Mathlib's explicit compositional inverse. -/
def formalCoordinateEquiv (f : PowerSeries F) (h₀ : f.constantCoeff=0)
    (h₁ : IsUnit (f.coeff 1)) : PowerSeries F ≃ₐ[F] PowerSeries F := by
  let hf : PowerSeries.HasSubst f := .of_constantCoeff_zero' h₀
  let g := f.substInvOfIsUnit h₁
  let hg : PowerSeries.HasSubst g := PowerSeries.HasSubst.substInvOfIsUnit f h₁
  refine AlgEquiv.ofAlgHom (PowerSeries.substAlgHom hf) (PowerSeries.substAlgHom hg) ?_ ?_
  · apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply,PowerSeries.coe_substAlgHom,AlgHom.id_apply]
    rw [PowerSeries.subst_comp_subst_apply hg hf]
    change p.subst ((f.substInvOfIsUnit h₁).subst f)=p
    rw [PowerSeries.subst_substInvOfIsUnit_left f h₀ h₁,PowerSeries.X_subst]
  · apply AlgHom.ext
    intro p
    simp only [AlgHom.comp_apply,PowerSeries.coe_substAlgHom,AlgHom.id_apply]
    rw [PowerSeries.subst_comp_subst_apply hf hg]
    change p.subst (f.subst (f.substInvOfIsUnit h₁))=p
    rw [PowerSeries.subst_substInvOfIsUnit_right f h₀ h₁,PowerSeries.X_subst]

@[simp]
theorem formalCoordinateEquiv_X (f : PowerSeries F) (h₀ : f.constantCoeff=0)
    (h₁ : IsUnit (f.coeff 1)) :
    formalCoordinateEquiv f h₀ h₁ PowerSeries.X=f := by
  change (PowerSeries.substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero' h₀)) PowerSeries.X=f
  exact PowerSeries.substAlgHom_X _

/-- A separated cover is exactly a pure power in an invertible formal
coordinate centered at its specified root. -/
theorem exists_ramified_formal_coordinate (phi : Polynomial F) (rho : F)
    (hphi : phi-C (phi.eval rho)≠0) :
    ∃ f : PowerSeries F,∃ h₀ : f.constantCoeff=0,∃ h₁ : IsUnit (f.coeff 1),
      f^((phi-C (phi.eval rho)).rootMultiplicity rho)=
        Polynomial.aeval (PowerSeries.X+PowerSeries.C rho) phi-
          PowerSeries.C (phi.eval rho) ∧
      formalCoordinateEquiv f h₀ h₁ PowerSeries.X=f := by
  let p := phi-C (phi.eval rho)
  let r := p.rootMultiplicity rho
  let q := rootCofactor p rho
  let shift : Polynomial F →ₐ[F] PowerSeries F :=
    Polynomial.aeval (PowerSeries.X+PowerSeries.C rho)
  have hr : 0<r := (Polynomial.rootMultiplicity_pos hphi).mpr (by simp [p,Polynomial.IsRoot])
  have hq : q.eval rho≠0 := rootCofactor_eval_ne_zero p hphi rho
  have hres : powerSeriesResidue (shift q)=q.eval rho := by
    rw [←Polynomial.aeval_algHom_apply]
    change Polynomial.aeval
      (PowerSeries.constantCoeff (PowerSeries.X+PowerSeries.C rho)) q=q.eval rho
    rw [map_add,PowerSeries.constantCoeff_X,PowerSeries.constantCoeff_C,zero_add]
    simp only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]
  have hu : IsUnit (shift q) :=
    (unit_iff_residue_ne_zero powerSeriesResidue _).mpr (hres.symm ▸ hq)
  obtain ⟨v,hv,hvu⟩ := exists_powerSeries_unit_root (shift q) hu r hr
  let f := PowerSeries.X*v
  have h₀ : f.constantCoeff=0 := by simp [f]
  have h₁ : IsUnit (f.coeff 1) := by
    simpa only [f,PowerSeries.coeff_one_mul,PowerSeries.coeff_one_X,
      PowerSeries.constantCoeff_X,one_mul,mul_zero,add_zero] using
      PowerSeries.isUnit_constantCoeff v hvu
  refine ⟨f,h₀,h₁,?_,formalCoordinateEquiv_X f h₀ h₁⟩
  have he := congrArg shift (rootCofactor_factorization p rho)
  have he' : PowerSeries.X^r*shift q=shift p := by
    simpa only [map_mul,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
      shift,PowerSeries.algebraMap_eq,add_sub_cancel_right] using he
  calc
    (PowerSeries.X*v)^r=shift p := by rw [mul_pow,hv]; exact he'
    _=Polynomial.aeval (PowerSeries.X+PowerSeries.C rho) phi-
        PowerSeries.C (phi.eval rho) := by
      simp only [shift,p,map_sub,Polynomial.aeval_C,PowerSeries.algebraMap_eq]

end PaperVerification.Fermion
