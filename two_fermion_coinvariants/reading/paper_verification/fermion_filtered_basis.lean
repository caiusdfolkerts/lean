module

public import PaperVerification.FermionFilteredRegularSequence
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.Abel

/-!
# Literal basis and colon-block lifting under weighted perturbation

Leading regularity is used for independence, through the proved initial-ideal
containment. Spanning uses finite descending weighted reduction. The resulting
basis consists of the original chosen homogeneous polynomial representatives.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators

variable {R ι E : Type*} [CommRing R] (w : ι → ℕ)

theorem bound_weightedTotalDegree (p : MvPolynomial ι R) : Bound w (weightedTotalDegree w p) p :=
  fun a ha ↦ le_weightedTotalDegree w (mem_support_iff.mpr ha)

theorem strictBound_zero_eq_zero {p : MvPolynomial ι R} (hp : StrictBound w 0 p) : p = 0 := by
  ext a
  by_contra ha
  have h := hp a (by simpa only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using ha)
  omega

theorem component_mem_homogeneous_span
    (v : E → MvPolynomial ι R) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (p : MvPolynomial ι R) (hp : p ∈ Submodule.span R (Set.range v)) (D : ℕ) :
    weightedHomogeneousComponent w D p ∈ Submodule.span R (Set.range v) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨e,rfl⟩ := hp
      rw [weightedHomogeneousComponent_of_mem (hv e)]
      split_ifs
      · exact Submodule.subset_span ⟨e,rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (Submodule.span R (Set.range v)).zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using (Submodule.span R (Set.range v)).add_mem ihp ihq
  | smul c p hp ih =>
      simpa only [map_smul] using (Submodule.span R (Set.range v)).smul_mem c ih

variable {m : ℕ}

/-- Leading-form independence on a homogeneous subspace survives the
perturbation of both the regular ideal and the colon multiplier. -/
theorem perturbed_colon_subspace_injective
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (V : Submodule R (MvPolynomial ι R))
    (hV : ∀ D p, p ∈ V → weightedHomogeneousComponent w D p ∈ V)
    (F F₀ : MvPolynomial ι R) (d : ℕ) (hF : Bound w d F)
    (hF₀ : weightedHomogeneousComponent w d F = F₀)
    (hinj : ∀ p ∈ V, p * F₀ ∈ Ideal.span (Set.range g) → p = 0)
    (p : MvPolynomial ι R) (hpV : p ∈ V) (hpI : p * F ∈ Ideal.span (Set.range f)) : p = 0 := by
  have hstep : ∀ D : ℕ, ∀ p : MvPolynomial ι R, Bound w D p → p ∈ V →
      p * F ∈ Ideal.span (Set.range f) → p = 0 := by
    intro D
    induction D with
    | zero =>
        intro p hp hpV hpI
        have htop := leading_component_mem_homogeneous_ideal w f g degree hf hg hreg
          (p * F) (0 + d) (bound_mul w hp hF) hpI
        rw [component_mul_top w hp hF,hF₀] at htop
        have hz := hinj (weightedHomogeneousComponent w 0 p) (hV 0 p hpV) htop
        have hstrict := strict_of_bound_component_zero w hp hz
        exact strictBound_zero_eq_zero w hstrict
    | succ D ih =>
        intro p hp hpV hpI
        have htop := leading_component_mem_homogeneous_ideal w f g degree hf hg hreg
          (p * F) (D + 1 + d) (bound_mul w hp hF) hpI
        rw [component_mul_top w hp hF,hF₀] at htop
        have hz := hinj (weightedHomogeneousComponent w (D + 1) p) (hV _ p hpV) htop
        have hstrict := strict_of_bound_component_zero w hp hz
        apply ih p
        · intro a ha
          exact Nat.le_of_lt_succ (hstrict a ha)
        · exact hpV
        · exact hpI
  exact hstep _ p (bound_weightedTotalDegree w p) hpV hpI

theorem polynomial_multiplier_independent_lifts [Fintype E]
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (v : E → MvPolynomial ι R) (vdegree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (vdegree e))
    (F F₀ : MvPolynomial ι R) (d : ℕ) (hF : Bound w d F)
    (hF₀ : weightedHomogeneousComponent w d F = F₀)
    (h₀ : LinearIndependent R (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e * F₀))) :
    LinearIndependent R (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (v e * F)) := by
  classical
  let V := Submodule.span R (Set.range v)
  have hinj : ∀ p ∈ V, p * F₀ ∈ Ideal.span (Set.range g) → p = 0 := by
    intro p hp hpI
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hp
    have hsum : (∑ e, c e • Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e * F₀)) = 0 := by
      have hzero : (Ideal.Quotient.mkₐ R (Ideal.span (Set.range g))) (p * F₀) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hpI
      rw [← hc] at hzero
      simpa only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hzero
    have hz := Fintype.linearIndependent_iff.mp h₀ c hsum
    rw [← hc]
    simp only [hz,zero_smul,Finset.sum_const_zero]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let p := ∑ e, c e • v e
  have hpV : p ∈ V := Submodule.sum_mem _ (fun e he ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨e,rfl⟩))
  have hpI : p * F ∈ Ideal.span (Set.range f) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) ((∑ e, c e • v e) * F) = 0
    simpa only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hc
  have hp0 := perturbed_colon_subspace_injective w f g degree hf hg hreg V
    (fun D p hp ↦ component_mem_homogeneous_span w v vdegree hv p hp D)
    F F₀ d hF hF₀ hinj p hpV hpI
  apply Fintype.linearIndependent_iff.mp h₀ c
  have hz : (Ideal.Quotient.mkₐ R (Ideal.span (Set.range g))) (p * F₀) = 0 := by
    rw [hp0,zero_mul,map_zero]
  simpa only [p,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hz

theorem component_homogeneous_coefficient
    (g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (degree i))
    (a : Fin m → MvPolynomial ι R) (D : ℕ) :
    weightedHomogeneousComponent w D (KoszulSyzygies.coefficient g a) =
      KoszulSyzygies.coefficient g (fun i ↦ shiftedProjection w (degree i) D (a i)) := by
  simp only [KoszulSyzygies.coefficient_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [component_mul_homogeneous w (hg i),shiftedProjection]
  split_ifs <;> simp only [LinearMap.zero_apply,zero_mul]

theorem coefficient_bound
    (f : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i)) (D : ℕ)
    (a : Fin m → MvPolynomial ι R) (ha : ∀ i, ShiftBound w (degree i) D (a i)) :
    Bound w D (KoszulSyzygies.coefficient f a) := by
  apply bound_sum w Finset.univ _ _
  intro i hi
  have h := shiftBound_mul w (s := 0) (d := degree i) (by simpa using ha i) (hf i)
  simpa only [Bound,ShiftBound,add_zero,smul_eq_mul] using h

/-- Descending reduction lifts a homogeneous spanning family. This part
does not require regularity; it is exactly the filtered spanning argument. -/
theorem polynomial_spanning_lifts [Fintype E]
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (v : E → MvPolynomial ι R) (vdegree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (vdegree e))
    (hspan : Submodule.span R (Set.range
      (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e))) = ⊤) :
    Submodule.span R (Set.range (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (v e))) = ⊤ := by
  classical
  let V := Submodule.span R (Set.range v)
  let I := Ideal.span (Set.range f)
  let J := Ideal.span (Set.range g)
  have hgHom (i : Fin m) : (g i).IsWeightedHomogeneous w (degree i) := by
    rw [← hg i]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hstep : ∀ D : ℕ, ∀ p : MvPolynomial ι R, Bound w D p → ∃ z ∈ V, p - z ∈ I := by
    intro D
    induction D with
    | zero =>
        intro p hp
        have hrec := hspan
        have hm : Ideal.Quotient.mk J p ∈
            V.map (Ideal.Quotient.mkₐ R J).toLinearMap := by
          dsimp only [V]
          rw [Submodule.map_span,← Set.range_comp']
          change Ideal.Quotient.mk J p ∈ Submodule.span R
            (Set.range (fun e ↦ Ideal.Quotient.mk J (v e)))
          rw [hspan]
          trivial
        obtain ⟨z,hz,hzp⟩ := hm
        have hI : p - z ∈ J := Ideal.Quotient.eq.mp hzp.symm
        have hrange : p - z ∈ LinearMap.range (KoszulSyzygies.coefficient g) := by
          simpa only [KoszulSyzygies.coefficient,Fintype.range_linearCombination] using hI
        obtain ⟨a,ha⟩ := hrange
        let a' := fun i ↦ shiftedProjection w (degree i) 0 (a i)
        let z' := weightedHomogeneousComponent w 0 z
        have htop : weightedHomogeneousComponent w 0 p - z' = KoszulSyzygies.coefficient g a' := by
          rw [← map_sub,← ha,component_homogeneous_coefficient w g degree hgHom]
        have hcoeff := shifted_top_coefficient w f g degree hf hg 0 a'
          (fun i ↦ shiftBound_projection w _ _ _)
        simp only [a',shiftedProjection_idempotent] at hcoeff
        change weightedHomogeneousComponent w _ (KoszulSyzygies.coefficient f a') =
          KoszulSyzygies.coefficient g a' at hcoeff
        let e := p - z' - KoszulSyzygies.coefficient f a'
        have heB : Bound w 0 e := bound_sub w (bound_sub w hp (bound_component w 0 z))
          (coefficient_bound w f degree hf 0 a' (fun i ↦ shiftBound_projection w _ _ _))
        have he0 : weightedHomogeneousComponent w 0 e = 0 := by
          change weightedHomogeneousComponent w 0
            (p - z' - KoszulSyzygies.coefficient f a') = 0
          rw [map_sub,map_sub]
          have hz' : weightedHomogeneousComponent w 0 z' = z' :=
            weightedHomogeneousComponent_eq_self
              (weightedHomogeneousComponent_isWeightedHomogeneous 0 z)
          rw [hz',hcoeff,← htop,sub_self]
        have he := strictBound_zero_eq_zero w (strict_of_bound_component_zero w heB he0)
        refine ⟨z',component_mem_homogeneous_span w v vdegree hv z hz 0,?_⟩
        have hpz : p - z' = KoszulSyzygies.coefficient f a' := sub_eq_zero.mp he
        rw [hpz,KoszulSyzygies.coefficient_apply]
        exact Ideal.sum_mem _ (fun i hi ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩))
    | succ D ih =>
        intro p hp
        have hm : Ideal.Quotient.mk J p ∈ V.map (Ideal.Quotient.mkₐ R J).toLinearMap := by
          dsimp only [V]
          rw [Submodule.map_span,← Set.range_comp']
          change Ideal.Quotient.mk J p ∈ Submodule.span R
            (Set.range (fun e ↦ Ideal.Quotient.mk J (v e)))
          rw [hspan]
          trivial
        obtain ⟨z,hz,hzp⟩ := hm
        have hI : p - z ∈ J := Ideal.Quotient.eq.mp hzp.symm
        have hrange : p - z ∈ LinearMap.range (KoszulSyzygies.coefficient g) := by
          simpa only [KoszulSyzygies.coefficient,Fintype.range_linearCombination] using hI
        obtain ⟨a,ha⟩ := hrange
        let a' := fun i ↦ shiftedProjection w (degree i) (D + 1) (a i)
        let z' := weightedHomogeneousComponent w (D + 1) z
        have htop : weightedHomogeneousComponent w (D + 1) p - z' = KoszulSyzygies.coefficient g a' := by
          rw [← map_sub,← ha,component_homogeneous_coefficient w g degree hgHom]
        have hcoeff := shifted_top_coefficient w f g degree hf hg (D + 1) a'
          (fun i ↦ shiftBound_projection w _ _ _)
        simp only [a',shiftedProjection_idempotent] at hcoeff
        change weightedHomogeneousComponent w _ (KoszulSyzygies.coefficient f a') =
          KoszulSyzygies.coefficient g a' at hcoeff
        let e := p - z' - KoszulSyzygies.coefficient f a'
        have heB : Bound w (D + 1) e := bound_sub w
          (bound_sub w hp (bound_component w (D + 1) z))
          (coefficient_bound w f degree hf (D + 1) a' (fun i ↦ shiftBound_projection w _ _ _))
        have he0 : weightedHomogeneousComponent w (D + 1) e = 0 := by
          change weightedHomogeneousComponent w (D + 1)
            (p - z' - KoszulSyzygies.coefficient f a') = 0
          rw [map_sub,map_sub]
          have hz' : weightedHomogeneousComponent w (D + 1) z' = z' :=
            weightedHomogeneousComponent_eq_self
              (weightedHomogeneousComponent_isWeightedHomogeneous (D + 1) z)
          rw [hz',hcoeff,← htop,sub_self]
        have hstrict := strict_of_bound_component_zero w heB he0
        obtain ⟨y,hy,hey⟩ := ih e (fun a ha ↦ Nat.le_of_lt_succ (hstrict a ha))
        refine ⟨z' + y,V.add_mem
          (component_mem_homogeneous_span w v vdegree hv z hz (D + 1)) hy,?_⟩
        have hcf : KoszulSyzygies.coefficient f a' ∈ I := by
          rw [KoszulSyzygies.coefficient_apply]
          exact Ideal.sum_mem _ (fun i hi ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩))
        convert I.add_mem hey hcf using 1
        dsimp only [e]
        abel
  apply top_unique
  intro z hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨v',hv',hpv⟩ := hstep _ p (bound_weightedTotalDegree w p)
  have he : Ideal.Quotient.mk I p = Ideal.Quotient.mk I v' := Ideal.Quotient.eq.mpr hpv
  rw [he]
  have hmap : (Submodule.span R (Set.range v)).map (Ideal.Quotient.mkₐ R I).toLinearMap =
      Submodule.span R (Set.range (fun e ↦ Ideal.Quotient.mk I (v e))) := by
    rw [Submodule.map_span,← Set.range_comp']
    rfl
  rw [← hmap]
  exact ⟨v',hv',rfl⟩

/-- The actual quotient basis lifts with its prescribed representatives.
Regularity and leading forms are the only algebraic input beyond the
already known homogeneous basis. -/
def basisOfRegularHighestForms [Fintype E]
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (v : E → MvPolynomial ι R) (vdegree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (vdegree e))
    (B : Module.Basis E R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)))
    (hB : ∀ e, B e = Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e)) :
    Module.Basis E R (MvPolynomial ι R ⧸ Ideal.span (Set.range f)) := by
  have hli₀ : LinearIndependent R
      (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e * 1)) := by
    simpa only [mul_one,← hB] using B.linearIndependent
  have hli := polynomial_multiplier_independent_lifts w f g degree hf hg hreg v vdegree hv
    1 1 0 (homogeneous_bound w (isWeightedHomogeneous_one R w))
    (weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one R w)) hli₀
  simp only [mul_one] at hli
  have hspan₀ : Submodule.span R (Set.range
      (fun e ↦ Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e))) = ⊤ := by
    simpa only [← hB] using B.span_eq
  exact Module.Basis.mk hli
    (polynomial_spanning_lifts w f g degree hf hg v vdegree hv hspan₀).ge

@[simp] theorem basisOfRegularHighestForms_apply [Fintype E]
    (f g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hf : ∀ i, Bound w (degree i) (f i))
    (hg : ∀ i, weightedHomogeneousComponent w (degree i) (f i) = g i)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (v : E → MvPolynomial ι R) (vdegree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (vdegree e))
    (B : Module.Basis E R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)))
    (hB : ∀ e, B e = Ideal.Quotient.mk (Ideal.span (Set.range g)) (v e)) (e : E) :
    basisOfRegularHighestForms w f g degree hf hg hreg v vdegree hv B hB e =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (v e) := by
  unfold basisOfRegularHighestForms
  exact Module.Basis.mk_apply _ _ e

end PaperVerification.Fermion.Filtered
