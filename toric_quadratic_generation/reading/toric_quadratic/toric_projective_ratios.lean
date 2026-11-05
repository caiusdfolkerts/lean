module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-!
# Actual projective chart maps from homogeneous ratios

These maps use Mathlib's degree-zero homogeneous localization and its
actual affine open immersion into Proj. Homogeneous scaling cancels in
every fraction, so changing a local frame does not change the induced
projective morphism.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical

section UnitEvaluation

variable {σ A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

/-- Homogeneous ratios may be evaluated in any ring when the selected
denominator is a unit. This is the actual affine-chart coordinate map. -/
def unitHomogeneousAwayEvaluation (F : A→+*B) (t : A) (ht : IsUnit (F t)) :
    Away 𝒜 t→+*B :=
  (Localization.awayLift F t ht).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem unitHomogeneousAwayEvaluation_mk_of_eq_one (F : A→+*B)
    {t : A} (ht : F t=1) {d : ℕ} (htd : t∈𝒜 d)
    (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    unitHomogeneousAwayEvaluation 𝒜 F t (ht ▸ isUnit_one)
        (Away.mk 𝒜 htd m p hp)=F p := by
  change Localization.awayLift F t (ht ▸ isUnit_one)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p 1 (by simpa only [mul_one] using ht)]
  simp

theorem unitHomogeneousAwayEvaluation_map (F : A→+*B) (G : B→+*D)
    (t : A) (ht : IsUnit (F t)) :
    G.comp (unitHomogeneousAwayEvaluation 𝒜 F t ht)=
      unitHomogeneousAwayEvaluation 𝒜 (G.comp F) t (ht.map G) := by
  have h : G.comp (Localization.awayLift F t ht)=
      Localization.awayLift (G.comp F) t (ht.map G) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,Localization.awayLift,IsLocalization.Away.lift_eq]
  exact congrArg (fun f=>f.comp (algebraMap (Away 𝒜 t) (Localization.Away t))) h

end UnitEvaluation

section HomogeneousEvaluation

variable {σ A K : Type u} [CommRing A] [Field K] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

def homogeneousAwayEvaluation (F : A→+*K) (t : A) (ht : F t≠0) :
    Away 𝒜 t→+*K :=
  (Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem homogeneousAwayEvaluation_mk (F : A→+*K) {t : A} (ht : F t≠0)
    {d : ℕ} (htd : t∈𝒜 d) (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    homogeneousAwayEvaluation 𝒜 F t ht (Away.mk 𝒜 htd m p hp)=
      F p/(F t)^m := by
  change Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p (F t)⁻¹ (mul_inv_cancel₀ ht)]
  simp only [div_eq_mul_inv,inv_pow]

theorem homogeneousAwayEvaluation_awayMap (F : A→+*K)
    {t q x : A} {d : ℕ} (hq : q∈𝒜 d) (hx : x=t*q)
    (ht : F t≠0) (hxx : F x≠0) :
    (homogeneousAwayEvaluation 𝒜 F x hxx).comp (awayMap 𝒜 hq hx)=
      homogeneousAwayEvaluation 𝒜 F t ht := by
  let G : Localization.Away t→+*Localization.Away x :=
    Localization.awayLift (algebraMap A (Localization.Away x)) t
      (isUnit_of_dvd_unit (map_dvd _ ⟨q,hx⟩)
        (IsLocalization.Away.algebraMap_isUnit x))
  have hG : (Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)).comp G =
      Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,G,Localization.awayLift,IsLocalization.Away.lift_eq]
  ext a
  change Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)
      ((awayMap 𝒜 hq hx a).val) =
    Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) a.val
  rw [val_awayMap]
  exact congrArg (fun g=>g a.val) hG

/-- An actual morphism into a genuine affine chart of Proj. -/
def projectiveFieldChart (F : A→+*K) (t : A) {d : ℕ}
    (htd : t∈𝒜 d) (hd : 0<d) (ht : F t≠0) :
    Spec (CommRingCat.of K)⟶Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation 𝒜 F t ht)) ≫
    Proj.awayι 𝒜 t htd hd

theorem projectiveFieldChart_mul (F : A→+*K) (t q x : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d)
    (hx : x=t*q) (ht : F t≠0) (hxx : F x≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F x (hx ▸ SetLike.mul_mem_graded htd hqe)
        (hd.trans_le (Nat.le_add_right d e)) hxx := by
  unfold projectiveFieldChart
  rw [← homogeneousAwayEvaluation_awayMap 𝒜 F hqe hx ht hxx,
    CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,
    Proj.SpecMap_awayMap_awayι]

/-- A nonzero homogeneous coordinate may be chosen arbitrarily. -/
theorem projectiveFieldChart_independent (F : A→+*K) (t q : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d) (he : 0<e)
    (ht : F t≠0) (hq : F q≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F q hqe he hq := by
  have hp : F (t*q)≠0 := by rw [map_mul]; exact mul_ne_zero ht hq
  rw [projectiveFieldChart_mul 𝒜 F t q (t*q) htd hqe hd rfl ht hp,
    projectiveFieldChart_mul 𝒜 F q t (t*q) hqe htd he (mul_comm t q) hq hp]
  rfl

end HomogeneousEvaluation

section PolynomialScaling

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι R K : Type u} [CommRing R] [Field K]

/-- Scaling all variables multiplies a homogeneous polynomial by the
corresponding scalar power, over any field and in every degree. -/
theorem homogeneous_eval_scaled (F : R→+*K) (v : ι→K) (c : K)
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d) :
    p.eval₂ F (fun i=>c*v i)=c^d*p.eval₂ F v := by
  rw [MvPolynomial.eval₂_eq,MvPolynomial.eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hm]
  ring

theorem homogeneousAwayEvaluation_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (ht : t.eval₂ F v≠0) :
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t ht := by
  ext z
  have htd' : t ∈ MvPolynomial.homogeneousSubmodule ι R d := htd
  obtain ⟨m,p,hp,rfl⟩ :=
    Away.mk_surjective (MvPolynomial.homogeneousSubmodule ι R) htd' z
  have hscaled : (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t ≠ 0 := by
    change t.eval₂ F (fun i=>c*v i) ≠ 0
    rw [homogeneous_eval_scaled F v c t d htd]
    exact mul_ne_zero (pow_ne_zero _ hc) ht
  have hleft := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F (fun i=>c*v i)) hscaled htd' m p hp
  have hright := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F v) ht htd' m p hp
  refine hleft.trans (Eq.trans ?_ hright.symm)
  change p.eval₂ F (fun i=>c*v i) / (t.eval₂ F (fun i=>c*v i))^m =
    p.eval₂ F v / (t.eval₂ F v)^m
  rw [homogeneous_eval_scaled F v c p (m • d) hp,
    homogeneous_eval_scaled F v c t d htd,mul_pow]
  simp only [smul_eq_mul,Nat.mul_comm m d,pow_mul]
  field_simp [hc,ht]

/-- Frame rescaling leaves the actual morphism to projective space
unchanged, because its actual homogeneous-localization map is unchanged. -/
theorem projectiveFieldChart_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (hd : 0<d) (ht : t.eval₂ F v≠0) :
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t htd hd
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t htd hd ht := by
  unfold projectiveFieldChart
  rw [homogeneousAwayEvaluation_scaled F v c hc t htd ht]

end PolynomialScaling
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_independent
#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_scaled
