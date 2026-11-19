module
public import graph_foundation.part011
public import shared_results.part003
public import paper_results.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FiniteTensorContraction -/
section

/-! # Strong contraction of a finite signed tensor product

The homotopy is the sum of the signed one-slot homotopies, preceded by
the already projected factors. Its identity telescopes through the
successive tensor projections. The construction is valid over any
commutative ring and retains the given inclusion and projection maps.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers
lemma linearMap_sum_comp {R I W X Y : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (s : Finset I) (f : I → X →ₗ[R] Y) (g : W →ₗ[R] X) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
lemma linearMap_comp_sum {R I W X Y : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (s : Finset I) (f : X →ₗ[R] Y) (g : I → W →ₗ[R] X) :
    f.comp (∑ i ∈ s, g i) = ∑ i ∈ s, f.comp (g i) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
end FourPapers
namespace FourPapers.HomologicalPerturbation.LinearContraction
open Classical FourPapers.TensorCycleSpanning
open scoped TensorProduct
variable {R : Type*} [CommRing R] {m : ℕ} {M H : Fin m → Type*}
  [∀ p,AddCommGroup (M p)] [∀ p,Module R (M p)]
  [∀ p,AddCommGroup (H p)] [∀ p,Module R (H p)]
  (C : ∀ p,LinearContraction (R := R) (M := M p) (H := H p))
  (s : ∀ p,Module.End R (M p))
  (hs : ∀ p,s p*s p=1)
  (hds : ∀ p,(C p).d*s p=-(s p*(C p).d))
  (hsh : ∀ p,s p*(C p).h+(C p).h*s p=0)

def q (p : Fin m) : Module.End R (M p) := (C p).summandProjection

private theorem dq (p : Fin m) : (C p).d*q C p=0 := by
  ext x
  exact (C p).differential_inclusion_apply ((C p).projection x)

private theorem qd (p : Fin m) : q C p*(C p).d=0 := by
  ext x
  change (C p).inclusion ((C p).projection ((C p).d x))=0
  rw [(C p).projection_differential_apply,map_zero]

private theorem hq (p : Fin m) : (C p).h*q C p=0 := by
  ext x
  exact (C p).homotopy_inclusion_apply ((C p).projection x)

private theorem qh (p : Fin m) : q C p*(C p).h=0 := by
  ext x
  change (C p).inclusion ((C p).projection ((C p).h x))=0
  rw [(C p).projection_homotopy_apply,map_zero]

private theorem q_formula (p : Fin m) :
    q C p=1-(C p).d*(C p).h-(C p).h*(C p).d := by
  have hh := (C p).homotopy
  change (C p).d*(C p).h+(C p).h*(C p).d=1-q C p at hh
  rw [← sub_add_eq_sub_sub]
  exact eq_sub_iff_add_eq.mpr (by rw [hh]; abel)

include hds hsh in
private theorem qs (p : Fin m) : s p*q C p=q C p*s p := by
  have hhs : (C p).h*s p=-(s p*(C p).h) := by
    apply add_eq_zero_iff_eq_neg.mp
    simpa only [add_comm] using hsh p
  have h₁ : (C p).d*(C p).h*s p=s p*(C p).d*(C p).h := by
    rw [mul_assoc,hhs,mul_neg,← mul_assoc,hds,neg_mul,neg_neg]
  have h₂ : (C p).h*(C p).d*s p=s p*(C p).h*(C p).d := by
    rw [mul_assoc,hds,mul_neg,← mul_assoc,hhs,neg_mul,neg_neg]
  rw [q_formula C p]
  calc
    _ = s p-s p*(C p).d*(C p).h-s p*(C p).h*(C p).d := by noncomm_ring
    _ = s p-(C p).d*(C p).h*s p-(C p).h*(C p).d*s p := by rw [h₁,h₂]
    _ = _ := by noncomm_ring

def tensorD : Module.End R (⨂[R] p,M p) :=
  TensorCycleSpanning.differential (fun p => (C p).d) s

include hds hsh in
private theorem prefix_commutes (j : ℕ) :
    tensorD C s * prefixMap (q C) j = prefixMap (q C) j * tensorD C s := by
  rw [tensorD,TensorCycleSpanning.differential,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [prefixMap,← PiTensorProduct.map_mul,← PiTensorProduct.map_mul]
  apply congrArg PiTensorProduct.map
  funext a
  by_cases haj : a.val<j
  · simp only [if_pos haj]
    by_cases hap : a=p
    · subst a
      simp only [factor,lt_self_iff_false,if_false,if_pos rfl,ite_true,dq,qd]
    · by_cases halt : a<p
      · simpa only [factor,if_pos halt] using qs C s hds hsh a
      · simp [factor,halt,hap]
  · simp [haj]

def tensorHomotopyTerm (p : Fin m) : Module.End R (⨂[R] a,M a) :=
  PiTensorProduct.map (factor (fun a => (C a).h) s p) * prefixMap (q C) p.val

def tensorHomotopy : Module.End R (⨂[R] a,M a) := ∑ p,tensorHomotopyTerm C s p

private def homotopyFactor (p a : Fin m) : Module.End R (M a) :=
  if a<p then s a*q C a else if a=p then (C a).h else 1

private theorem tensorHomotopyTerm_eq (p : Fin m) :
    tensorHomotopyTerm C s p=PiTensorProduct.map (homotopyFactor C s p) := by
  rw [tensorHomotopyTerm,prefixMap,← PiTensorProduct.map_mul]
  apply congrArg PiTensorProduct.map
  funext a
  by_cases hap : a<p
  · simp [factor,homotopyFactor,hap]
  · by_cases he : a=p
    · subst a; simp [factor,homotopyFactor]
    · simp [factor,homotopyFactor,hap,he]

include hs hds hsh in
private theorem homotopy_term_identity (p : Fin m) :
    tensorD C s*tensorHomotopyTerm C s p+tensorHomotopyTerm C s p*tensorD C s =
      prefixMap (q C) p.val-prefixMap (q C) (p.val+1) := by
  have ht := tensor_slot_homotopy (fun a => (C a).d) s (fun a => (C a).h) hs hds hsh p
  rw [← q_formula C p] at ht
  rw [prefixMap_succ]
  calc
    _ = (tensorD C s*PiTensorProduct.map (factor (fun a => (C a).h) s p)+
      PiTensorProduct.map (factor (fun a => (C a).h) s p)*tensorD C s)*prefixMap (q C) p.val := by
        rw [tensorHomotopyTerm,
          mul_assoc (PiTensorProduct.map (factor (fun a => (C a).h) s p))
            (prefixMap (q C) p.val) (tensorD C s),
          ← prefix_commutes C s hds hsh p.val, add_mul]
        simp only [mul_assoc]
    _ = (1-slot p (q C p))*prefixMap (q C) p.val :=
      congrArg (fun z => z * prefixMap (q C) p.val) ht
    _ = _ := by rw [sub_mul, one_mul]

private theorem finite_telescope {A : Type*} [AddCommGroup A] (f : ℕ → A) (n : ℕ) :
    (∑ i : Fin n, (f i.val - f (i.val + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,ih]
      abel

include hs hds hsh in
private theorem tensorHomotopy_identity :
    tensorD C s*tensorHomotopy C s+tensorHomotopy C s*tensorD C s =
      1-PiTensorProduct.map (q C) := by
  rw [tensorHomotopy,Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  simp_rw [homotopy_term_identity C s hs hds hsh]
  rw [finite_telescope,prefixMap_zero,prefixMap_full]

include hds hsh in
private theorem tensorHomotopyTerm_mul (p a : Fin m) :
    tensorHomotopyTerm C s p*tensorHomotopyTerm C s a=0 := by
  rw [tensorHomotopyTerm_eq,tensorHomotopyTerm_eq,← PiTensorProduct.map_mul]
  change (PiTensorProduct.mapMultilinear R M M)
    (fun b => homotopyFactor C s p b*homotopyFactor C s a b)=0
  rcases lt_trichotomy p a with hpa | hpa | hap
  · apply MultilinearMap.map_coord_zero (i := p)
    simp only [homotopyFactor,lt_self_iff_false,if_false,if_pos rfl,if_pos hpa, ite_true]
    rw [qs C s hds hsh p,← mul_assoc,hq,zero_mul]
  · subst a
    apply MultilinearMap.map_coord_zero (i := p)
    simpa only [homotopyFactor,lt_self_iff_false,if_false,if_pos rfl, ite_true] using (C p).squareHomotopy
  · apply MultilinearMap.map_coord_zero (i := a)
    simp only [homotopyFactor,if_pos hap,lt_self_iff_false,if_false,if_pos rfl, ite_true]
    rw [mul_assoc,qh,mul_zero]

include hds hsh in
theorem tensorHomotopy_square : tensorHomotopy C s*tensorHomotopy C s=0 := by
  rw [tensorHomotopy,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun a ha => tensorHomotopyTerm_mul C s hds hsh p a

/-- The signed tensor contraction keeps the literal tensor of the given
projections. This is needed for naturality of the incidence cover. -/
def finiteTensor : LinearContraction (R := R) (M := ⨂[R] p,M p) (H := ⨂[R] p,H p) where
  d := tensorD C s
  h := tensorHomotopy C s
  inclusion := PiTensorProduct.map (fun p => (C p).inclusion)
  projection := PiTensorProduct.map (fun p => (C p).projection)
  differential := differential_square_zero _ s (fun p => (C p).differential) hds
  retract := by
    rw [← PiTensorProduct.map_comp]
    have he : (fun p => (C p).projection.comp (C p).inclusion)=
        (fun p => (LinearMap.id : H p →ₗ[R] H p)) := funext (fun p => (C p).retract)
    rw [he,PiTensorProduct.map_id]
  inclusion_cycle := by
    rw [tensorD,TensorCycleSpanning.differential,linearMap_sum_comp]
    apply Finset.sum_eq_zero
    intro p hp
    rw [← PiTensorProduct.map_comp]
    change (PiTensorProduct.mapMultilinear R H M) _=0
    apply MultilinearMap.map_coord_zero (i := p)
    simpa [factor] using (C p).inclusion_cycle
  projection_boundary := by
    rw [tensorD,TensorCycleSpanning.differential,linearMap_comp_sum]
    apply Finset.sum_eq_zero
    intro p hp
    rw [← PiTensorProduct.map_comp]
    change (PiTensorProduct.mapMultilinear R M H) _=0
    apply MultilinearMap.map_coord_zero (i := p)
    simpa [factor] using (C p).projection_boundary
  homotopy := by
    rw [tensorHomotopy_identity C s hs hds hsh,← PiTensorProduct.map_comp]
    rfl
  squareHomotopy := tensorHomotopy_square C s hds hsh
  homotopyInclusion := by
    rw [tensorHomotopy,linearMap_sum_comp]
    apply Finset.sum_eq_zero
    intro p hp
    rw [tensorHomotopyTerm_eq,← PiTensorProduct.map_comp]
    change (PiTensorProduct.mapMultilinear R H M) _=0
    apply MultilinearMap.map_coord_zero (i := p)
    simpa [homotopyFactor] using (C p).homotopyInclusion
  projectionHomotopy := by
    rw [tensorHomotopy,linearMap_comp_sum]
    apply Finset.sum_eq_zero
    intro p hp
    rw [tensorHomotopyTerm_eq,← PiTensorProduct.map_comp]
    change (PiTensorProduct.mapMultilinear R M H) _=0
    apply MultilinearMap.map_coord_zero (i := p)
    simpa [homotopyFactor] using (C p).projectionHomotopy

@[simp] theorem finiteTensor_projection :
    (finiteTensor C s hs hds hsh).projection=PiTensorProduct.map (fun p => (C p).projection) := rfl

@[simp] theorem finiteTensor_inclusion :
    (finiteTensor C s hs hds hsh).inclusion=PiTensorProduct.map (fun p => (C p).inclusion) := rfl

@[simp] theorem finiteTensor_d :
    (finiteTensor C s hs hds hsh).d=TensorCycleSpanning.differential (fun p => (C p).d) s := rfl

/-- The explicit homotopy formula makes its grading transparent. -/
theorem finiteTensor_h :
    (finiteTensor C s hs hds hsh).h=
      ∑ p,PiTensorProduct.map (fun a => if a<p then s a*(C a).summandProjection
        else if a=p then (C a).h else 1) := by
  change tensorHomotopy C s=_
  unfold tensorHomotopy
  apply Finset.sum_congr rfl
  intro p _
  exact tensorHomotopyTerm_eq C s p

end FourPapers.HomologicalPerturbation.LinearContraction
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerGradedPerturbation -/
section

/-! # Integer degree bookkeeping for an actual perturbation contraction -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearContraction
variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R:=R) (M:=M) (H:=H))
  (P : ℤ→Module.End R M) (Q : ℤ→Module.End R H)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M)=1+δ*C.h)
  (hh : ∀p,C.h*P p=P (p+1)*C.h)
  (hδ : ∀p,δ*P p=P (p-1)*δ)
  (hi : ∀p,C.inclusion.comp (Q p)=(P p).comp C.inclusion)
  (hp : ∀p,C.projection.comp (P p)=(Q p).comp C.projection)

include hu hh hδ in
theorem integerUnit_commutes (p : ℤ) : Commute (u : Module.End R M) (P p) := by
  change (u : Module.End R M)*P p=P p*(u : Module.End R M)
  rw [hu,add_mul,mul_add,one_mul,mul_one]
  congr 1
  rw [mul_assoc,hh p,← mul_assoc,hδ (p+1)]
  simp only [add_sub_cancel_right,mul_assoc]

include hu hh hδ in
theorem integerCorrection_lowers (p : ℤ) :
    correction u δ*P p=P (p-1)*correction u δ := by
  have hc := (C.integerUnit_commutes P δ u hu hh hδ (p-1)).units_inv_left
  rw [correction,mul_assoc,hδ p,← mul_assoc,hc.eq,mul_assoc]

include hu hh hδ in
theorem integer_h_correction_commutes (p : ℤ) :
    (C.h*correction u δ)*P p=P p*(C.h*correction u δ) := by
  rw [mul_assoc,C.integerCorrection_lowers P δ u hu hh hδ p,← mul_assoc,hh (p-1)]
  simp only [sub_add_cancel,mul_assoc]

include hu hh hδ in
theorem integer_correction_h_commutes (p : ℤ) :
    (correction u δ*C.h)*P p=P p*(correction u δ*C.h) := by
  rw [mul_assoc,hh p,← mul_assoc,C.integerCorrection_lowers P δ u hu hh hδ (p+1)]
  simp only [add_sub_cancel_right,mul_assoc]

include hu hh hδ hi in
theorem integerTransferredInclusion (p : ℤ) :
    (C.transferredInclusion δ u).comp (Q p)=
      (P p).comp (C.transferredInclusion δ u) := by
  ext x
  change C.inclusion (Q p x)-C.h (correction u δ (C.inclusion (Q p x)))=
    P p (C.inclusion x-C.h (correction u δ (C.inclusion x)))
  have hi' := LinearMap.congr_fun (hi p) x
  change C.inclusion (Q p x)=P p (C.inclusion x) at hi'
  have hc := LinearMap.congr_fun (C.integer_h_correction_commutes P δ u hu hh hδ p) (C.inclusion x)
  change C.h (correction u δ (P p (C.inclusion x)))=
    P p (C.h (correction u δ (C.inclusion x))) at hc
  rw [hi',hc,map_sub]

include hu hh hδ hp in
theorem integerTransferredProjection (p : ℤ) :
    (C.transferredProjection δ u).comp (P p)=
      (Q p).comp (C.transferredProjection δ u) := by
  ext x
  change C.projection (P p x-correction u δ (C.h (P p x)))=
    Q p (C.projection (x-correction u δ (C.h x)))
  have hc := LinearMap.congr_fun (C.integer_correction_h_commutes P δ u hu hh hδ p) x
  change correction u δ (C.h (P p x))=P p (correction u δ (C.h x)) at hc
  rw [hc,← map_sub]
  exact LinearMap.congr_fun (hp p) _

include hu hh hδ in
theorem integerTransferredHomotopy (p : ℤ) :
    C.transferredHomotopy δ u*P p=P (p+1)*C.transferredHomotopy δ u := by
  change (C.h-C.h*correction u δ*C.h)*P p=
    P (p+1)*(C.h-C.h*correction u δ*C.h)
  rw [sub_mul,mul_sub,hh p]
  congr 1
  calc
    (C.h*correction u δ*C.h)*P p=C.h*correction u δ*(C.h*P p) := by noncomm_ring
    _=C.h*correction u δ*(P (p+1)*C.h) := by rw [hh p]
    _=C.h*(correction u δ*P (p+1))*C.h := by noncomm_ring
    _=C.h*(P p*correction u δ)*C.h := by
      rw [C.integerCorrection_lowers P δ u hu hh hδ (p+1),add_sub_cancel_right]
    _=P (p+1)*(C.h*correction u δ*C.h) := by
      rw [← mul_assoc,hh p]
      noncomm_ring

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedPerturbationFromBasis -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearContraction
open CommAlg
variable {R M H I J : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R:=R) (M:=M) (H:=H))
  (b : Module.Basis I R M) (c : Module.Basis J R H) (deg : I→ℤ) (degree : J→ℤ)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M)=1+δ*C.h)
  (hh : ∀i,C.h (b i)∈Grading.Piece b deg (deg i+1))
  (hδ : ∀i,δ (b i)∈Grading.Piece b deg (deg i-1))
  (hi : ∀j,C.inclusion (c j)∈Grading.Piece b deg (degree j))
  (hp : ∀i,C.projection (b i)∈Grading.Piece c degree (deg i))

include hh in
private theorem h_projection (p : ℤ) :
    C.h*Grading.projection b deg p=Grading.projection b deg (p+1)*C.h :=
  shiftedProjection_commutes b b deg deg (fun p:ℤ=>p+1)
    (fun _ _ h=>add_right_cancel h) C.h hh p

include hδ in
private theorem δ_projection (p : ℤ) :
    δ*Grading.projection b deg p=Grading.projection b deg (p-1)*δ :=
  shiftedProjection_commutes b b deg deg (fun p:ℤ=>p-1)
    (fun _ _ h=>sub_left_inj.mp h) δ hδ p

include hi in
private theorem i_projection (p : ℤ) :
    C.inclusion.comp (Grading.projection c degree p)=
      (Grading.projection b deg p).comp C.inclusion :=
  shiftedProjection_commutes c b degree deg id Function.injective_id C.inclusion hi p

include hp in
private theorem p_projection (p : ℤ) :
    C.projection.comp (Grading.projection b deg p)=
      (Grading.projection c degree p).comp C.projection :=
  shiftedProjection_commutes b c deg degree id Function.injective_id C.projection hp p

include hu hh hδ hi in
theorem transferredInclusion_mem_piece (p : ℤ) (x : H) (hx : x∈Grading.Piece c degree p) :
    C.transferredInclusion δ u x∈Grading.Piece b deg p := by
  have he := LinearMap.congr_fun (C.integerTransferredInclusion
    (Grading.projection b deg) (Grading.projection c degree) δ u hu
    (h_projection C b deg hh) (δ_projection b deg δ hδ) (i_projection C b c deg degree hi) p) x
  change C.transferredInclusion δ u (Grading.projection c degree p x)=
    Grading.projection b deg p (C.transferredInclusion δ u x) at he
  rw [Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

include hu hh hδ hp in
theorem transferredProjection_mem_piece (p : ℤ) (x : M) (hx : x∈Grading.Piece b deg p) :
    C.transferredProjection δ u x∈Grading.Piece c degree p := by
  have he := LinearMap.congr_fun (C.integerTransferredProjection
    (Grading.projection b deg) (Grading.projection c degree) δ u hu
    (h_projection C b deg hh) (δ_projection b deg δ hδ) (p_projection C b c deg degree hp) p) x
  change C.transferredProjection δ u (Grading.projection b deg p x)=
    Grading.projection c degree p (C.transferredProjection δ u x) at he
  rw [Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

include hu hh hδ in
theorem transferredHomotopy_mem_piece (p : ℤ) (x : M) (hx : x∈Grading.Piece b deg p) :
    C.transferredHomotopy δ u x∈Grading.Piece b deg (p+1) := by
  have he := LinearMap.congr_fun (C.integerTransferredHomotopy
    (Grading.projection b deg) δ u hu (h_projection C b deg hh) (δ_projection b deg δ hδ) p) x
  change C.transferredHomotopy δ u (Grading.projection b deg p x)=
    Grading.projection b deg (p+1) (C.transferredHomotopy δ u x) at he
  rw [Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedRetractionHomology -/
section

/-! # Homology of an actual graded linear deformation retract

The quotient below retains the specified degree-p cycles and boundaries
from degree p+1. It therefore does not infer a graded result merely from
an equivalence on the ungraded direct sum.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.GradedRetractionHomology
open HomologicalPerturbation
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : ℕ → Submodule R M) (D : Module.End R M)
  (hD : D*D=0) (hDP : ∀p x,x∈P (p+1)→D x∈P p)

def cycles (p : ℕ) : Submodule R M := P p ⊓ LinearMap.ker D

def boundary (p : ℕ) : P (p+1) →ₗ[R] cycles P D p :=
  (D.domRestrict (P (p+1))).codRestrict _
    (fun x => ⟨hDP p x.val x.property,LinearMap.congr_fun hD x.val⟩)

abbrev Homology (p : ℕ) := cycles P D p ⧸ LinearMap.range (boundary P D hD hDP p)

/-- Equality of differentials identifies the actual cycle and boundary
quotients. All square-zero and degree-preservation proofs are propositionally
irrelevant, so this transport introduces no additional mathematical input. -/
def homologyEquivOfDifferential (D' : Module.End R M) (h : D = D')
    (hD' : D' * D' = 0) (hDP' : ∀ p x, x ∈ P (p+1) → D' x ∈ P p) (p : ℕ) :
    Homology P D hD hDP p ≃ₗ[R] Homology P D' hD' hDP' p := by
  subst D'
  exact LinearEquiv.refl R _

theorem class_eq_iff (p : ℕ) (x y : cycles P D p) :
    (Submodule.Quotient.mk x : Homology P D hD hDP p)=Submodule.Quotient.mk y ↔
      ∃ z : P (p+1),D z.val=x.val-y.val := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,congrArg Subtype.val hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,Subtype.ext hz⟩

variable (Q : ℕ → Submodule R N) (d : Module.End R N)
  (hd : d*d=0) (hdQ : ∀p x,x∈Q (p+1)→d x∈Q p)
  (f : M →ₗ[R] N) (hf : ∀p x,x∈P p→f x∈Q p)
  (hfd : d.comp f=f.comp D)

def cycleMap (p : ℕ) : cycles P D p →ₗ[R] cycles Q d p :=
  (f.domRestrict (cycles P D p)).codRestrict _ (by
    intro x
    refine ⟨hf p x.val x.property.1,?_⟩
    change d (f x.val) = 0
    have he := LinearMap.congr_fun hfd x.val
    change d (f x.val)=f (D x.val) at he
    rw [he,x.property.2,map_zero])

def homologyMap (p : ℕ) : Homology P D hD hDP p →ₗ[R] Homology Q d hd hdQ p :=
  (LinearMap.range (boundary P D hD hDP p)).liftQ
    ((LinearMap.range (boundary Q d hd hdQ p)).mkQ.comp (cycleMap P D Q d f hf hfd p)) (by
      rintro x ⟨z,rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨⟨f z.val,hf (p+1) z.val z.property⟩,?_⟩
      apply Subtype.ext
      exact LinearMap.congr_fun hfd z.val)

@[simp] theorem homologyMap_class (p : ℕ) (x : cycles P D p) :
    homologyMap P D hD hDP Q d hd hdQ f hf hfd p (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (cycleMap P D Q d f hf hfd p x) := rfl

section Deformation
variable (C : LinearDeformationRetract (R:=R) (M:=M) (H:=N))
  (hP : ∀p x,x∈P (p+1)→C.sourceD x∈P p)
  (hQ : ∀p x,x∈Q (p+1)→C.targetD x∈Q p)
  (hi : ∀p x,x∈Q p→C.inclusion x∈P p)
  (hp : ∀p x,x∈P p→C.projection x∈Q p)
  (hh : ∀p x,x∈P p→C.homotopy x∈P (p+1))

/-- Explicit source/target cycle maps and an explicit boundary preimage
give a degreewise homology equivalence over every commutative ring. -/
def deformationEquiv (p : ℕ) :
    Homology P C.sourceD C.source_square hP p ≃ₗ[R]
      Homology Q C.targetD C.target_square hQ p := by
  let F := homologyMap P C.sourceD C.source_square hP Q C.targetD C.target_square hQ
    C.projection hp C.projection_chain.symm p
  apply LinearEquiv.ofBijective F
  constructor
  · intro x y hxy
    obtain ⟨z,rfl⟩ := (LinearMap.range (boundary P C.sourceD C.source_square hP p)).mkQ_surjective x
    obtain ⟨w,rfl⟩ := (LinearMap.range (boundary P C.sourceD C.source_square hP p)).mkQ_surjective y
    obtain ⟨a,ha⟩ := (class_eq_iff Q C.targetD C.target_square hQ p _ _).mp hxy
    apply (class_eq_iff P C.sourceD C.source_square hP p z w).mpr
    refine ⟨⟨C.inclusion a.val+C.homotopy (z.val-w.val),
      Submodule.add_mem _ (hi (p+1) a.val a.property)
        (hh p _ (Submodule.sub_mem _ z.property.1 w.property.1))⟩,?_⟩
    apply C.boundary_of_projected_boundary (z.val-w.val)
    · rw [map_sub,z.property.2,w.property.2,sub_self]
    · simpa only [cycleMap,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,map_sub] using ha
  · intro y
    obtain ⟨z,rfl⟩ := (LinearMap.range (boundary Q C.targetD C.target_square hQ p)).mkQ_surjective y
    have hz : C.sourceD (C.inclusion z.val)=0 := by
      rw [C.inclusion_differential,z.property.2,map_zero]
    refine ⟨Submodule.Quotient.mk ⟨C.inclusion z.val,hi p z.val z.property.1,hz⟩,?_⟩
    change Submodule.Quotient.mk (cycleMap P C.sourceD Q C.targetD C.projection hp
      C.projection_chain.symm p ⟨C.inclusion z.val,hi p z.val z.property.1,hz⟩)=_
    congr 1
    exact Subtype.ext (C.projection_inclusion z.val)

end Deformation
end FourPapers.GradedRetractionHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedHomologyShift -/
section

/-! # Shifting the degree labels of an actual chain complex

The cycle module at q of the shifted grading is literally the cycle module
at q+ell of the original grading. Boundary sources are identified by the
proved equality (q+1)+ell=(q+ell)+1. The resulting equivalence retains the
actual differential and the actual quotient by its image.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.GradedRetractionHomology
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (P : ℕ → Submodule R M) (D : Module.End R M)
  (hD : D * D = 0) (hDP : ∀ p x, x ∈ P (p+1) → D x ∈ P p)

/-- Translation of degree labels preserves the literal graded homology. -/
def homologyShiftEquiv (ell : ℕ)
    (hShift : ∀ p x, x ∈ P ((p+1)+ell) → D x ∈ P (p+ell)) (q : ℕ) :
    Homology (fun p => P (p+ell)) D hD hShift q ≃ₗ[R]
      Homology P D hD hDP (q+ell) := by
  apply Submodule.Quotient.equiv (R := R) (R₂ := R)
    (M := cycles (fun p => P (p+ell)) D q)
    (N := cycles P D (q+ell))
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    _ _ (LinearEquiv.refl R _)
  have hindex : (q+1)+ell=(q+ell)+1 := Nat.add_right_comm q 1 ell
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    refine ⟨⟨y.val,?_⟩,Subtype.ext rfl⟩
    simpa only [hindex] using y.property
  · rintro ⟨y,rfl⟩
    let y' : P ((q+1)+ell) := ⟨y.val,by simpa only [hindex] using y.property⟩
    exact ⟨_,⟨y',rfl⟩,Subtype.ext rfl⟩

end FourPapers.GradedRetractionHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedHomologyVanishing -/
section

/-! # Vanishing from an explicit graded deformation retract

A cycle in a degree where the retraction projection is zero is filled by
the displayed homotopy. The quotient argument is carried out for abstract
modules, retaining the actual differential and its boundary map.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.GradedRetractionHomology
open HomologicalPerturbation
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The actual degree-p homology vanishes when the retraction has zero
projection in that degree and its homotopy raises the prescribed degree. -/
theorem homology_subsingleton_of_zero_projection
    (P : ℕ → Submodule R M)
    (C : LinearDeformationRetract (R := R) (M := M) (H := N))
    (hP : ∀ q x, x ∈ P (q+1) → C.sourceD x ∈ P q) (p : ℕ)
    (hzero : ∀ x, x ∈ P p → C.projection x = 0)
    (hraise : ∀ x, x ∈ P p → C.homotopy x ∈ P (p+1)) :
    Subsingleton (Homology P C.sourceD C.source_square hP p) := by
  have hz : ∀ x : Homology P C.sourceD C.source_square hP p, x=0 := by
    intro x
    obtain ⟨z,rfl⟩ :=
      (LinearMap.range (boundary P C.sourceD C.source_square hP p)).mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨⟨C.homotopy z.val,hraise z.val z.property.1⟩,?_⟩
    apply Subtype.ext
    have hf := C.cycle_decomposition z.val z.property.2
    rw [hzero z.val z.property.1,map_zero,zero_add] at hf
    exact hf.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end FourPapers.GradedRetractionHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerMatrixSpecialization -/
section

/-!
# Characteristic comparison from actual integer boundary matrices

A nonzero minor after specialization was already nonzero before an
injective specialization. Consequently an integer matrix has no larger
rank over an arbitrary field than over the rationals. The homology
comparison below concerns the actual kernel/image quotient of a short
complex; it does not define homology by a numerical rank formula.

-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.IntegerMatrixSpecialization

open Classical CategoryTheory Matrix

variable {R K L I J : Type*} [CommRing R] [Field K] [Field L]
  [Finite I] [Fintype J]

/-- Specializing entries cannot increase rank relative to an injective
field realization of the coefficient ring. No flatness assumption is used. -/
theorem rank_map_le_of_injective (A : Matrix I J R)
    (φ : R →+* K) (ψ : R →+* L) (hψ : Function.Injective ψ) :
    (A.map φ).rank ≤ (A.map ψ).rank := by
  apply FourPapers.Symmetric.rank_le_iff_vanishing_minors.mpr
  intro r c
  have hL : ((A.map ψ).submatrix r c).det=0 :=
    FourPapers.Symmetric.rank_le_iff_vanishing_minors.mp
      (le_refl (A.map ψ).rank) r c
  have hz : (A.submatrix r c).det=0 := by
    apply hψ
    rw [map_zero,ψ.map_det]
    exact hL
  rw [show ((A.map φ).submatrix r c).det=φ ((A.submatrix r c).det) from
    (φ.map_det (A.submatrix r c)).symm,hz,map_zero]

theorem rank_map_eq_of_injective (A : Matrix I J R)
    (φ : R →+* K) (ψ : R →+* L)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    (A.map φ).rank=(A.map ψ).rank :=
  le_antisymm (rank_map_le_of_injective A φ ψ hψ)
    (rank_map_le_of_injective A ψ φ hφ)

/-- The rational rank is an upper bound in every characteristic. -/
theorem integer_rank_le_rational (A : Matrix I J ℤ) (K : Type*) [Field K] :
    (A.map (Int.castRingHom K)).rank ≤ (A.map (Int.castRingHom ℚ)).rank :=
  rank_map_le_of_injective A (Int.castRingHom K) (Int.castRingHom ℚ)
    (by intro a b h; exact Int.cast_injective h)

theorem integer_rank_eq_rational (A : Matrix I J ℤ) (K : Type*)
    [Field K] [CharZero K] :
    (A.map (Int.castRingHom K)).rank=(A.map (Int.castRingHom ℚ)).rank :=
  rank_map_eq_of_injective A (Int.castRingHom K) (Int.castRingHom ℚ)
    (by intro a b h; exact Int.cast_injective h)
    (by intro a b h; exact Int.cast_injective h)

section Homology

universe u v
variable {F : Type u} [Field F]
  (S : ShortComplex (ModuleCat.{v} F))
  {I₁ I₂ I₃ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
  (b₁ : Module.Basis I₁ F S.X₁) (b₂ : Module.Basis I₂ F S.X₂)
  (b₃ : Module.Basis I₃ F S.X₃)

/-- The dimension identity is proved from the categorical homology's
canonical identification with the genuine kernel/image quotient. -/
theorem homology_finrank_add_matrix_ranks :
    Module.finrank F S.homology+
      (LinearMap.toMatrix b₁ b₂ S.f.hom).rank+
      (LinearMap.toMatrix b₂ b₃ S.g.hom).rank=Fintype.card I₂ := by
  letI : Module.Finite F S.X₁ := b₁.finiteDimensional_of_finite
  letI : Module.Finite F S.X₂ := b₂.finiteDimensional_of_finite
  letI : Module.Finite F S.X₃ := b₃.finiteDimensional_of_finite
  have hfg : S.g.hom.comp S.f.hom=0 := ModuleCat.hom_ext_iff.mp S.zero
  have hH := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank F S.homology=
    Module.finrank F (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hH
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have hb := (FilteredHomology.boundaryRangeEquiv S.f.hom S.g.hom hfg).finrank_eq
  change Module.finrank F (LinearMap.range S.moduleCatToCycles)=
    Module.finrank F (LinearMap.range S.f.hom) at hb
  have hg := LinearMap.finrank_range_add_finrank_ker S.g.hom
  have hm := Module.finrank_eq_card_basis b₂
  have hfM : (LinearMap.toMatrix b₁ b₂ S.f.hom).rank =
      Module.finrank F (LinearMap.range S.f.hom) := by
    exact (Matrix.rank_eq_finrank_range_toLin
      (LinearMap.toMatrix b₁ b₂ S.f.hom) b₂ b₁).trans
      (congrArg (fun f : S.X₁ →ₗ[F] S.X₂ =>
        Module.finrank F (LinearMap.range f))
        ((LinearMap.toMatrix b₁ b₂).symm_apply_apply S.f.hom))
  have hgM : (LinearMap.toMatrix b₂ b₃ S.g.hom).rank =
      Module.finrank F (LinearMap.range S.g.hom) := by
    exact (Matrix.rank_eq_finrank_range_toLin
      (LinearMap.toMatrix b₂ b₃ S.g.hom) b₃ b₂).trans
      (congrArg (fun f : S.X₂ →ₗ[F] S.X₃ =>
        Module.finrank F (LinearMap.range f))
        ((LinearMap.toMatrix b₂ b₃).symm_apply_apply S.g.hom))
  omega

end Homology

/-- A pair of finite short complexes obtained from the same two integer
matrices has at least as much actual homology over any field as over ℚ.
The hypotheses identify real differentials in actual finite bases. -/
theorem homology_finrank_le_specialization
    {F : Type*} [Field F]
    {I₁ I₂ I₃ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (SQ : ShortComplex (ModuleCat ℚ)) (SF : ShortComplex (ModuleCat F))
    (q₁ : Module.Basis I₁ ℚ SQ.X₁) (q₂ : Module.Basis I₂ ℚ SQ.X₂)
    (q₃ : Module.Basis I₃ ℚ SQ.X₃)
    (f₁ : Module.Basis I₁ F SF.X₁) (f₂ : Module.Basis I₂ F SF.X₂)
    (f₃ : Module.Basis I₃ F SF.X₃)
    (A : Matrix I₂ I₁ ℤ) (B : Matrix I₃ I₂ ℤ)
    (hAQ : LinearMap.toMatrix q₁ q₂ SQ.f.hom=A.map (Int.castRingHom ℚ))
    (hBQ : LinearMap.toMatrix q₂ q₃ SQ.g.hom=B.map (Int.castRingHom ℚ))
    (hAF : LinearMap.toMatrix f₁ f₂ SF.f.hom=A.map (Int.castRingHom F))
    (hBF : LinearMap.toMatrix f₂ f₃ SF.g.hom=B.map (Int.castRingHom F)) :
    Module.finrank ℚ SQ.homology ≤ Module.finrank F SF.homology := by
  have hQ := homology_finrank_add_matrix_ranks SQ q₁ q₂ q₃
  have hF := homology_finrank_add_matrix_ranks SF f₁ f₂ f₃
  rw [hAQ,hBQ] at hQ
  rw [hAF,hBF] at hF
  have ha := integer_rank_le_rational A F
  have hb := integer_rank_le_rational B F
  omega

/-- The same comparison with any characteristic-zero coefficient field;
this formulation also supports arbitrary Lean universe levels directly. -/
theorem homology_finrank_le_charZero
    {Q F : Type*} [Field Q] [CharZero Q] [Field F]
    {I₁ I₂ I₃ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (SQ : ShortComplex (ModuleCat Q)) (SF : ShortComplex (ModuleCat F))
    (q₁ : Module.Basis I₁ Q SQ.X₁) (q₂ : Module.Basis I₂ Q SQ.X₂)
    (q₃ : Module.Basis I₃ Q SQ.X₃)
    (f₁ : Module.Basis I₁ F SF.X₁) (f₂ : Module.Basis I₂ F SF.X₂)
    (f₃ : Module.Basis I₃ F SF.X₃)
    (A : Matrix I₂ I₁ ℤ) (B : Matrix I₃ I₂ ℤ)
    (hAQ : LinearMap.toMatrix q₁ q₂ SQ.f.hom=A.map (Int.castRingHom Q))
    (hBQ : LinearMap.toMatrix q₂ q₃ SQ.g.hom=B.map (Int.castRingHom Q))
    (hAF : LinearMap.toMatrix f₁ f₂ SF.f.hom=A.map (Int.castRingHom F))
    (hBF : LinearMap.toMatrix f₂ f₃ SF.g.hom=B.map (Int.castRingHom F)) :
    Module.finrank Q SQ.homology ≤ Module.finrank F SF.homology := by
  have hQ := homology_finrank_add_matrix_ranks SQ q₁ q₂ q₃
  have hF := homology_finrank_add_matrix_ranks SF f₁ f₂ f₃
  rw [hAQ,hBQ] at hQ
  rw [hAF,hBF] at hF
  have ha := rank_map_le_of_injective A (Int.castRingHom F) (Int.castRingHom Q)
    (by intro a b h; exact Int.cast_injective h)
  have hb := rank_map_le_of_injective B (Int.castRingHom F) (Int.castRingHom Q)
    (by intro a b h; exact Int.cast_injective h)
  omega

end FourPapers.IntegerMatrixSpecialization

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CharacteristicBettiComparison -/
section

/-!
# Nonnegative characteristic excess in genuine fine quotient Tor

The integer matrices below are the coefficients of the actual projected
exterior boundary. Their finite bases depend only on the monomial ideal
and fine degree. Matrix specialization therefore proves the numerical
universal-coefficient inequality without assuming a universal-coefficient
theorem or freeness of integral homology.

This supplies the coefficient comparison used in Corollary 10.4.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Polymatroid CommAlg.Koszul

universe u
variable {V : Type u} [Fintype V] [LinearOrder V]

/-- The literal signed deletion matrix, including the terms killed in
the monomial quotient. Its entries are integers independently of the
eventual coefficient field. -/
def quotientIntegerBoundaryMatrix (B : Family V) (a : Exponent V) (p : ℕ) :
    Matrix (QuotientFaceIndex B a p) (QuotientFaceIndex B a (p+1)) ℤ :=
  fun t s => ∑ j : {j // j∈s.val},
    if h : QuotientAllowed B (a-faceExponent s.val+Finsupp.single j.val 1) then
      if eraseQuotientFace s j h=t then
        TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val else 0
    else 0

theorem quotientFaceDifferential_toMatrix {k : Type u} [CommRing k]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    LinearMap.toMatrix (quotientFaceBasis (k:=k) B a (p+1))
      (quotientFaceBasis (k:=k) B a p) (quotientFaceDifferential B a p)=
      (quotientIntegerBoundaryMatrix B a p).map (Int.castRingHom k) := by
  ext t s
  rw [LinearMap.toMatrix_apply,quotientFaceDifferential_basis]
  simp only [map_sum,Finsupp.finsetSum_apply,Matrix.map_apply,
    quotientIntegerBoundaryMatrix]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : QuotientAllowed B (a-faceExponent s.val+Finsupp.single j.val 1)
  · rw [dif_pos h,dif_pos h]
    by_cases he : eraseQuotientFace s j h=t
    · simp [he,Module.Basis.repr_self,map_zsmul_unit,Finsupp.single_apply,
        Units.smul_def,Int.smul_one_eq_cast]
    · simp [he,Module.Basis.repr_self,map_zsmul_unit,Finsupp.single_apply]
  · simp [h]

/-- Degree zero has the actual zero outgoing map. No fictitious
negative chain group is inserted into the dimension calculation. -/
def quotientIntegerOutgoingMatrix (B : Family V) (a : Exponent V) :
    (p : ℕ) → Matrix (QuotientFaceIndex B a p.pred) (QuotientFaceIndex B a p) ℤ
  | 0 => 0
  | p+1 => quotientIntegerBoundaryMatrix B a p

abbrev quotientFaceShortComplex {k : Type u} [CommRing k]
    (B : Family V) (a : Exponent V) (p : ℕ) : ShortComplex (ModuleCat.{u} k) :=
  (quotientFaceComplex (k:=k) B a).sc' (p+1) p p.pred

theorem quotientFaceShortComplex_incoming_matrix {k : Type u} [CommRing k]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    LinearMap.toMatrix (quotientFaceBasis (k:=k) B a (p+1))
      (quotientFaceBasis (k:=k) B a p) (quotientFaceShortComplex (k:=k) B a p).f.hom=
      (quotientIntegerBoundaryMatrix B a p).map (Int.castRingHom k) := by
  change LinearMap.toMatrix _ _ ((quotientFaceComplex (k:=k) B a).d (p+1) p).hom=_
  rw [quotientFaceComplex_d]
  exact quotientFaceDifferential_toMatrix B a p

theorem quotientFaceShortComplex_outgoing_matrix {k : Type u} [CommRing k]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    LinearMap.toMatrix (quotientFaceBasis (k:=k) B a p)
      (quotientFaceBasis (k:=k) B a p.pred) (quotientFaceShortComplex (k:=k) B a p).g.hom=
      (quotientIntegerOutgoingMatrix B a p).map (Int.castRingHom k) := by
  cases p with
  | zero =>
      change LinearMap.toMatrix _ _ ((quotientFaceComplex (k:=k) B a).d 0 0).hom=_
      rw [(quotientFaceComplex (k:=k) B a).shape 0 0 (by simp)]
      simp [quotientIntegerOutgoingMatrix]
  | succ p =>
      change LinearMap.toMatrix _ _ ((quotientFaceComplex (k:=k) B a).d (p+1) p).hom=_
      rw [quotientFaceComplex_d]
      exact quotientFaceDifferential_toMatrix B a p

def quotientFaceShortHomologyIso {k : Type u} [CommRing k]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k:=k) B a).homology p ≅
      (quotientFaceShortComplex (k:=k) B a p).homology :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) p).mapIso
      (quotientFacesIso (k:=k) B a).symm ≪≫
    (quotientFaceComplex (k:=k) B a).homologyIsoSc' (p+1) p p.pred
      (by simp) (by cases p <;> simp)

/-- Every fine Betti number of the actual polynomial quotient over a
characteristic-zero field is bounded by that over any coefficient field.
This includes homological degree zero and all natural fine degrees. -/
theorem quotientBettiNumber_charZero_le (Q K : Type u)
    [Field Q] [CharZero Q] [Field K]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    quotientBettiNumber (k:=Q) B a p ≤ quotientBettiNumber (k:=K) B a p := by
  rw [quotientBettiNumber_eq_homology,quotientBettiNumber_eq_homology,
    (quotientFaceShortHomologyIso (k:=Q) B a p).toLinearEquiv.finrank_eq,
    (quotientFaceShortHomologyIso (k:=K) B a p).toLinearEquiv.finrank_eq]
  exact IntegerMatrixSpecialization.homology_finrank_le_charZero
    (Q := Q) (F := K)
    (I₁ := QuotientFaceIndex B a (p+1))
    (I₂ := QuotientFaceIndex B a p)
    (I₃ := QuotientFaceIndex B a p.pred)
    (quotientFaceShortComplex (k:=Q) B a p) (quotientFaceShortComplex (k:=K) B a p)
    (quotientFaceBasis (k:=Q) B a (p+1))
    (quotientFaceBasis (k:=Q) B a p) (quotientFaceBasis (k:=Q) B a p.pred)
    (quotientFaceBasis (k:=K) B a (p+1))
    (quotientFaceBasis (k:=K) B a p) (quotientFaceBasis (k:=K) B a p.pred)
    (quotientIntegerBoundaryMatrix B a p) (quotientIntegerOutgoingMatrix B a p)
    (by
      apply Matrix.ext
      intro t s
      simpa only [LinearMap.toMatrix_apply] using!
        congrFun (congrFun (quotientFaceShortComplex_incoming_matrix (k:=Q) B a p) t) s)
    (by
      apply Matrix.ext
      intro t s
      simpa only [LinearMap.toMatrix_apply] using!
        congrFun (congrFun (quotientFaceShortComplex_outgoing_matrix (k:=Q) B a p) t) s)
    (by
      apply Matrix.ext
      intro t s
      simpa only [LinearMap.toMatrix_apply] using!
        congrFun (congrFun (quotientFaceShortComplex_incoming_matrix (k:=K) B a p) t) s)
    (by
      apply Matrix.ext
      intro t s
      simpa only [LinearMap.toMatrix_apply] using!
        congrFun (congrFun (quotientFaceShortComplex_outgoing_matrix (k:=K) B a p) t) s)

/-- All characteristic-zero coefficient fields give the same fine table. -/
theorem quotientBettiNumber_charZero_eq (Q K : Type u)
    [Field Q] [CharZero Q] [Field K] [CharZero K]
    (B : Family V) (a : Exponent V) (p : ℕ) :
    quotientBettiNumber (k:=Q) B a p=quotientBettiNumber (k:=K) B a p :=
  le_antisymm (quotientBettiNumber_charZero_le Q K B a p)
    (quotientBettiNumber_charZero_le K Q B a p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteTensorHomologyRank -/
section

/-! # Total homology dimension of a finite signed tensor product

This is the field Künneth dimension formula for the actual signed tensor
complex. It follows from explicit strong contractions of the factors, rather
than from an assumed tensor-product homology theorem.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers
open Classical FilteredHomology HomologicalPerturbation TensorCycleSpanning
open scoped TensorProduct

lemma finrank_piTensorProduct {K I : Type*} [Field K] [Fintype I]
    (H : I → Type*) [∀ i, AddCommGroup (H i)] [∀ i, Module K (H i)]
    [∀ i, Module.Finite K (H i)] :
    Module.finrank K (⨂[K] i, H i) = ∏ i, Module.finrank K (H i) := by
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun i => Module.finBasis K (H i)))]
  simp only [Fintype.card_pi, Fintype.card_fin]

variable {K : Type*} [Field K] {m : ℕ} {M : Fin m → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, Module.Finite K (M i)]
  (d s : ∀ i, Module.End K (M i))
  (hdd : ∀ i, d i * d i = 0) (hs : ∀ i, s i * s i = 1)
  (hds : ∀ i, d i * s i = -(s i * d i))
  (hchar : ∀ i, (2 : K) = 0 → s i = 1)

include hs hchar in
/-- Every factor is the actual kernel/image quotient, over any field. -/
theorem finrank_signedTensorHomology :
    Module.finrank K (Homology (differential d s) (differential d s)
      (differential_square_zero d s hdd hds)) =
      ∏ i, Module.finrank K (Homology (d i) (d i) (hdd i)) := by
  let H := fun i => OddHomologyModel (d i) (s i) (hdd i) (hs i) (hds i) (hchar i)
  let C := fun i => oddContraction (d i) (s i) (hdd i) (hs i) (hds i) (hchar i)
  let T := LinearContraction.finiteTensor C s hs hds
    (fun i => oddContraction_parity (d i) (s i) (hdd i) (hs i) (hds i) (hchar i))
  have hfactor (i : Fin m) :
      Module.finrank K (H i) = Module.finrank K (Homology (d i) (d i) (hdd i)) :=
    (C i).homologyEquiv.finrank_eq.symm
  calc
    _ = Module.finrank K (⨂[K] i, H i) := T.homologyEquiv.finrank_eq
    _ = ∏ i, Module.finrank K (H i) := finrank_piTensorProduct (K := K) (fun i => ↥(H i))
    _ = _ := Finset.prod_congr rfl (fun i _ => hfactor i)

end FourPapers

#print axioms FourPapers.finrank_signedTensorHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LabelledSimplicialStrands -/
section

/-! # Every polynomial strand is the actual divisor simplicial complex

The equivalence sends the coefficient monomial of exponent b−lcm(F)
times the generator F to the literal oriented face F. Its bijectivity and
compatibility with the signed differentials are proved on the displayed
bases, over arbitrary commutative coefficient rings.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.LabelledSimplicial

open Classical CommAlg MvPolynomial Sublattice
open scoped BigOperators

universe u v w
variable {k : Type u} {X : Type w} {V : Type v} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype X] (K : Finset V → Prop) (hK : Simplicial.Downward K)
  (u : V → X →₀ ℕ)

def divisorFaces (b : X →₀ ℕ) (F : Finset V) : Prop := K F ∧ ∀ v∈F,u v≤b

theorem divisorFaces_iff (b : X →₀ ℕ) (F : Finset V) :
    divisorFaces K u b F ↔ K F ∧ faceLabel u F≤b := by
  simp only [divisorFaces,faceLabel,Finset.sup_le_iff]

include hK in
theorem divisorFaces_downward (b : X →₀ ℕ) : Simplicial.Downward (divisorFaces K u b) :=
  fun _ _ hFG hG => ⟨hK hFG hG.1,fun v hv => hG.2 v (hFG hv)⟩

abbrev FineIndex (b : X →₀ ℕ) := {a : Σ F : Face K,X →₀ ℕ // fineDegree K u a=b}

def fineBasis (b : X →₀ ℕ) : Module.Basis (FineIndex K u b) k (finePiece (k:=k) K u b) :=
  Grading.restrictedBasis (coefficientBasis K) (fun a => fineDegree K u a=b)

@[simp] theorem fineBasis_val (b : X →₀ ℕ) (a : FineIndex K u b) :
    (fineBasis (k:=k) K u b a).val=coefficientBasis K a.val :=
  Grading.restrictedBasis_val _ _ _

def fineIndexEquiv (b : X →₀ ℕ) : FineIndex K u b ≃ {F : Finset V // divisorFaces K u b F} where
  toFun a := ⟨a.val.1.val,(divisorFaces_iff K u b _).mpr ⟨a.val.1.property,by
    intro v
    have he := congrArg (fun c : X →₀ ℕ => c v) a.property
    change a.val.2 v + faceLabel u a.val.1.val v = b v at he
    change faceLabel u a.val.1.val v ≤ b v
    omega⟩⟩
  invFun F := ⟨⟨⟨F.val,F.property.1⟩,b-faceLabel u F.val⟩,
    tsub_add_cancel_of_le ((divisorFaces_iff K u b F.val).mp F.property).2⟩
  left_inv a := by
    rcases a with ⟨⟨⟨F,hF⟩,c⟩,ha⟩
    apply Subtype.ext
    change (⟨⟨F,hF⟩, b - faceLabel u F⟩ : Σ F : Face K, X →₀ ℕ) = ⟨⟨F,hF⟩,c⟩
    apply congrArg (fun c : X →₀ ℕ => (⟨⟨F,hF⟩,c⟩ : Σ F : Face K, X →₀ ℕ))
    ext v
    have he := congrArg (fun c : X →₀ ℕ => c v) ha
    change c v+faceLabel u F v=b v at he
    change b v-faceLabel u F v=c v
    omega
  right_inv F := Subtype.ext rfl

@[simp] theorem fineIndexEquiv_val (b : X →₀ ℕ) (a : FineIndex K u b) :
    (fineIndexEquiv K u b a).val = a.val.1.val := rfl

@[simp] theorem fineIndexEquiv_symm_val (b : X →₀ ℕ)
    (F : {F : Finset V // divisorFaces K u b F}) :
    ((fineIndexEquiv K u b).symm F).val.1.val = F.val := rfl

/-- Literal fine homogeneous coordinates equal literal divisor-face coordinates. -/
def fineFaceEquiv (b : X →₀ ℕ) :
    finePiece (k:=k) K u b ≃ₗ[k] TotalFaceModule (k:=k) (divisorFaces K u b) :=
  (fineBasis K u b).equiv (totalFaceBasis (divisorFaces K u b)) (fineIndexEquiv K u b)

@[simp] theorem fineFaceEquiv_basis (b : X →₀ ℕ) (a : FineIndex K u b) :
    fineFaceEquiv (k:=k) K u b (fineBasis K u b a)=
      totalFaceBasis (divisorFaces K u b) (fineIndexEquiv K u b a) :=
  Module.Basis.equiv_apply _ _ _ _

def fineDifferential (b : X →₀ ℕ) : Module.End k (finePiece (k:=k) K u b) :=
  (((differential K hK u).restrictScalars k).domRestrict (finePiece K u b)).codRestrict _
    (fun z => differential_fine K hK u b z.val z.property)

def erasedFineIndex (b : X →₀ ℕ) (a : FineIndex K u b) (v : V) : FineIndex K u b :=
  ⟨erasedCoefficientIndex K hK u a.val v,(fineDegree_erase K hK u a.val v).trans a.property⟩

theorem fineDifferential_basis (b : X →₀ ℕ) (a : FineIndex K u b) :
    fineDifferential K hK u b (fineBasis (k:=k) K u b a)=
      ∑ v : {v // v∈a.val.1.val},TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val •
        fineBasis K u b (erasedFineIndex K hK u b a v.val) := by
  apply Subtype.ext
  simp only [fineDifferential,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,
    LinearMap.restrictScalars_apply,fineBasis_val,Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  exact differential_coefficientBasis K hK u a.val

theorem fineFaceEquiv_differential (b : X →₀ ℕ) (z : finePiece (k:=k) K u b) :
    fineFaceEquiv K u b (fineDifferential K hK u b z)=
      idealTotalDifferential (divisorFaces_downward K hK u b) (fineFaceEquiv K u b z) := by
  have he : (fineFaceEquiv (k:=k) K u b).toLinearMap.comp (fineDifferential K hK u b)=
      (idealTotalDifferential (divisorFaces_downward K hK u b)).comp
        (fineFaceEquiv K u b).toLinearMap := by
    apply (fineBasis K u b).ext
    intro a
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,fineDifferential_basis,
      map_sum,map_zsmul_unit,fineFaceEquiv_basis,idealTotalDifferential_basis,
      fineIndexEquiv_val]
    apply Finset.sum_congr rfl
    intro v _
    calc
      fineFaceEquiv K u b
          (TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val •
            fineBasis K u b (erasedFineIndex K hK u b a v.val)) =
          TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val •
            fineFaceEquiv K u b
              (fineBasis K u b (erasedFineIndex K hK u b a v.val)) :=
        LinearMapClass.map_smul_of_tower (R:=ℤˣ) (S:=k)
          (fineFaceEquiv K u b) _ _
      _ = TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val •
          totalFaceBasis (divisorFaces K u b)
            (fineIndexEquiv K u b (erasedFineIndex K hK u b a v.val)) :=
        congrArg (fun z => TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val • z)
          (fineFaceEquiv_basis K u b (erasedFineIndex K hK u b a v.val))
      _ = _ := by
        apply congrArg (fun z => TauCeti.ExteriorAlgebra.basisEraseSign v.val a.val.1.val •
          totalFaceBasis (divisorFaces K u b) z)
        exact Subtype.ext rfl
  exact LinearMap.congr_fun he z

theorem coefficientBasis_repr (z : FreeModule (k:=k) (X:=X) K)
    (a : Σ F : Face K,X →₀ ℕ) : (coefficientBasis K).repr z a=(z a.1).coeff a.2 := by
  have he : (coefficientBasis (k:=k) K).coord a=
      (MvPolynomial.lcoeff k a.2).comp (Finsupp.lapply a.1) := by
    apply (coefficientBasis K).ext
    rintro ⟨G,c⟩
    rcases a with ⟨F,a⟩
    simp only [Module.Basis.coord_apply,Module.Basis.repr_self,LinearMap.comp_apply]
    simp only [coefficientBasis_apply,Finsupp.lapply_apply,Finsupp.single_apply,
      MvPolynomial.lcoeff_apply]
    by_cases hF : G=F
    ·
      subst G
      simp [coeff_monomial]
    · have hba : (⟨G,c⟩ : Σ F : Face K, X →₀ ℕ) ≠ ⟨F,a⟩ :=
        fun h => hF (congrArg Sigma.fst h)
      simp only [if_neg hba,if_neg hF,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  exact LinearMap.congr_fun he z

theorem chainPiece_coeff_iff (i : ℕ) (z : FreeModule (k:=k) (X:=X) K) :
    z∈chainPiece K i ↔ ∀ a : Σ F : Face K,X →₀ ℕ,
      (coefficientBasis K).repr z a≠0 → a.1.val.card=i := by
  rw [chainPiece,Grading.mem_piece]
  change (∀ F : Face K,z F≠0→F.val.card=i) ↔ _
  constructor
  · intro hz a ha
    apply hz a.1
    intro hzero
    rw [coefficientBasis_repr,hzero,AddMonoidAlgebra.coeff_zero] at ha
    exact ha rfl
  · intro hz F hF
    by_contra hcard
    apply hF
    ext a
    by_contra ha
    exact hcard (hz ⟨F,a⟩ (by
      simpa only [coefficientBasis_repr,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using ha))

theorem fineProjection_chain (b : X →₀ ℕ) (i : ℕ)
    (z : FreeModule (k:=k) (X:=X) K) (hz : z∈chainPiece K i) :
    fineProjection K u b z∈chainPiece K i := by
  rw [chainPiece_coeff_iff] at hz ⊢
  intro a ha
  apply hz a
  simp only [fineProjection,Grading.projection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,Grading.filterMap_apply,Finsupp.filter_apply] at ha
  split_ifs at ha
  · exact ha
  · exact (ha rfl).elim

def fineChainPiece (b : X →₀ ℕ) (i : ℕ) : Submodule k (finePiece (k:=k) K u b) :=
  Grading.Piece (fineBasis K u b) (fun a => a.val.1.val.card) i

theorem fineChainPiece_mem_iff (b : X →₀ ℕ) (i : ℕ) (z : finePiece (k:=k) K u b) :
    z∈fineChainPiece K u b i ↔ z.val∈chainPiece K i := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a,ha,rfl⟩ := hx
        rw [fineBasis_val,coefficientBasis_eq_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a.val.1,ha,rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih => exact Submodule.smul_of_tower_mem _ c ih
  · intro hz
    rw [fineChainPiece,Grading.mem_piece]
    intro a ha
    apply (chainPiece_coeff_iff K i z.val).mp hz a.val
    have he : (fineBasis (k:=k) K u b).repr z a =
        (coefficientBasis K).repr z.val a.val :=
      FourPapers.restrictedBasis_repr (coefficientBasis K)
        (fun a => fineDegree K u a = b) z a
    rwa [he] at ha

theorem fineFaceEquiv_chain (b : X →₀ ℕ) (i : ℕ) (z : finePiece (k:=k) K u b) :
    fineFaceEquiv K u b z∈totalFacePiece (divisorFaces K u b) i ↔ z.val∈chainPiece K i := by
  rw [← fineChainPiece_mem_iff K u b i z,totalFacePiece_eq_basis_span]
  exact linearEquiv_mem_piece_iff_of_basis (R:=k)
    (X:=finePiece (k:=k) K u b)
    (Y:=TotalFaceModule (k:=k) (divisorFaces K u b))
    (fineBasis K u b) (totalFaceBasis (divisorFaces K u b))
    (fun a => a.val.1.val.card) (fun F => F.val.card)
    (fineFaceEquiv K u b) (fineIndexEquiv K u b)
    (fineFaceEquiv_basis K u b)
    (fun a => congrArg Finset.card (fineIndexEquiv_val K u b a)) i z

end FourPapers.LabelledSimplicial

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LabelledSimplicialExactness -/
section

/-! # Actual exactness and augmentation of the labelled polynomial complex -/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.LabelledSimplicial

open Classical CommAlg MvPolynomial Sublattice
open scoped BigOperators

universe u v w
variable {k : Type u} {X : Type w} {V : Type v} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype X] (K : Finset V → Prop) (hK : Simplicial.Downward K)
  (u : V → X →₀ ℕ)
  (contract : ∀ b : X →₀ ℕ,(∃ v,K {v} ∧ u v≤b) →
    SimplicialDomination.FaceContraction (k:=k) (divisorFaces K u b))

include hK contract in
theorem divisor_positive_exact (b : X →₀ ℕ) (i : ℕ) :
    Simplicial.ExactIn (k:=k) (divisorFaces K u b) (i+1) := by
  by_cases hb : ∃ v,K {v} ∧ u v≤b
  · exact (contract b hb).exactIn (i+1)
  · apply Simplicial.exactIn_of_no_face
    intro F hF hcard
    have hne : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v,hv⟩ := hne
    exact hb ⟨v,hK (Finset.singleton_subset_iff.mpr hv) hF.1,hF.2 v hv⟩

include contract in
theorem fine_positive_filling (b : X →₀ ℕ) (i : ℕ) (z : finePiece (k:=k) K u b)
    (hz : z.val∈chainPiece K (i+1)) (hdz : differential K hK u z.val=0) :
    ∃ y : finePiece (k:=k) K u b,y.val∈chainPiece K (i+2) ∧
      differential K hK u y.val=z.val := by
  let q := fineFaceEquiv K u b z
  have hq : q.val∈Simplicial.Chains (divisorFaces K u b) (i+1) :=
    (fineFaceEquiv_chain K u b (i+1) z).mpr hz
  have hdq : Simplicial.boundary q.val=0 := by
    have he := fineFaceEquiv_differential K hK u b z
    have hdz' : fineDifferential K hK u b z=0 := Subtype.ext hdz
    rw [hdz',map_zero] at he
    exact (congrArg Subtype.val he).symm
  obtain ⟨y,hy,hdy⟩ := divisor_positive_exact K hK u contract b i q.val hq hdq
  let y' : TotalFaceModule (k:=k) (divisorFaces K u b) := ⟨y,chains_mem_basisSpan hy⟩
  let w := (fineFaceEquiv (k:=k) K u b).symm y'
  refine ⟨w,?_,?_⟩
  · apply (fineFaceEquiv_chain K u b (i+2) w).mp
    change fineFaceEquiv K u b ((fineFaceEquiv K u b).symm y')∈_
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · have he : fineDifferential K hK u b w=z := by
      apply (fineFaceEquiv K u b).injective
      rw [fineFaceEquiv_differential]
      change idealTotalDifferential (divisorFaces_downward K hK u b)
        (fineFaceEquiv K u b ((fineFaceEquiv K u b).symm y'))=q
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext hdy
    exact congrArg Subtype.val he

include contract in
/-- Exactness is obtained by filling each of the finitely many actual
polynomial degrees and summing those fillings. -/
theorem positive_filling (i : ℕ) (z : FreeModule (k:=k) (X:=X) K)
    (hz : z∈chainPiece K (i+1)) (hdz : differential K hK u z=0) :
    ∃ y : FreeModule (k:=k) (X:=X) K,y∈chainPiece K (i+2) ∧ differential K hK u y=z := by
  have hf (b : X →₀ ℕ) : ∃ y : finePiece (k:=k) K u b,
      y.val∈chainPiece K (i+2) ∧ differential K hK u y.val=fineProjection K u b z := by
    apply fine_positive_filling K hK u contract b i
      ⟨fineProjection K u b z,Grading.projection_mem _ _ _ _⟩
      (fineProjection_chain K u b (i+1) z hz)
    rw [differential_fineProjection,hdz,map_zero]
  choose y hy hdy using hf
  let s := ((coefficientBasis K).repr z).support.image (fineDegree K u)
  refine ⟨∑ b∈s,(y b).val,Submodule.sum_mem _ (fun b _ => hy b),?_⟩
  rw [map_sum]
  simp_rw [hdy]
  exact Grading.sum_projections (coefficientBasis K) (fineDegree K u) z

def generatorIdeal : Ideal (PolynomialRing (k:=k) (X:=X)) :=
  Ideal.span {f | ∃ v,K {v} ∧ f=monomial (u v) 1}

/-- The augmented coefficient is extracted from the actual exterior
boundary; on a vertex generator it is its specified monomial label. -/
def augmentationPolynomial : FreeModule (k:=k) (X:=X) K →ₗ[PolynomialRing (k:=k) (X:=X)]
    PolynomialRing (k:=k) (X:=X) :=
  (Simplicial.basis.coord (∅ : Finset V)).comp
    (Simplicial.boundary.comp (labelledEmbedding K u))

theorem boundary_singleton (v : V) :
    Simplicial.boundary (Simplicial.basis (k:=k) {v})=Simplicial.basis ∅ := by
  simp [Simplicial.basis,TauCeti.ExteriorAlgebra.basis_singleton,
    Simplicial.boundary,CliffordAlgebra.contractLeft_ι,
    Fintype.linearCombination_apply,Pi.basisFun_apply,Pi.single_apply,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort]

theorem augmentationPolynomial_vertex (v : V) (hv : K {v}) :
    augmentationPolynomial (k:=k) K u (freeBasis K ⟨{v},hv⟩)=monomial (u v) 1 := by
  simp only [augmentationPolynomial,LinearMap.comp_apply,labelledEmbedding_basis,
    map_smul,faceLabel_singleton,boundary_singleton,Module.Basis.coord_apply,
    Module.Basis.repr_self,Finsupp.single_eq_same,smul_eq_mul,mul_one]

theorem augmentationPolynomial_boundary (z : FreeModule (k:=k) (X:=X) K) :
    augmentationPolynomial K u (differential K hK u z)=0 := by
  change Simplicial.basis.coord ∅ (Simplicial.boundary
    (labelledEmbedding K u (differential K hK u z)))=0
  rw [labelledEmbedding_differential,Simplicial.boundary_boundary,map_zero]

theorem augmentationPolynomial_mem (z : FreeModule (k:=k) (X:=X) K)
    (hz : z∈chainPiece K 1) : augmentationPolynomial K u z∈generatorIdeal K u := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hF
      have he : F=⟨{v},hv ▸ F.property⟩ := Subtype.ext hv
      rw [he,augmentationPolynomial_vertex]
      exact Ideal.subset_span ⟨v,hv ▸ F.property,rfl⟩
  | zero => simpa only [map_zero] using (generatorIdeal (k:=k) K u).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def augmentation : chainPiece (k:=k) (X:=X) K 1 →ₗ[PolynomialRing (k:=k) (X:=X)]
    generatorIdeal (k:=k) K u :=
  ((augmentationPolynomial K u).domRestrict (chainPiece K 1)).codRestrict _
    (fun z => augmentationPolynomial_mem K u z.val z.property)

theorem augmentation_surjective : Function.Surjective (augmentation (k:=k) K u) := by
  have hr : generatorIdeal (k:=k) K u≤
      LinearMap.range ((augmentationPolynomial K u).domRestrict (chainPiece K 1)) := by
    apply Ideal.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    refine ⟨⟨freeBasis K ⟨{v},hv⟩,
      Submodule.subset_span ⟨⟨{v},hv⟩,Finset.card_singleton v,rfl⟩⟩,?_⟩
    exact augmentationPolynomial_vertex K u v hv
  intro f
  obtain ⟨z,hz⟩ := hr f.property
  exact ⟨z,Subtype.ext hz⟩

theorem labelledEmbedding_degree_zero (z : FreeModule (k:=k) (X:=X) K)
    (hz : z∈chainPiece K 0) :
    labelledEmbedding K u z=
      Simplicial.basis.coord ∅ (labelledEmbedding K u z) • Simplicial.basis ∅ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      have hF0 := Finset.card_eq_zero.mp hF
      simp only [labelledEmbedding_basis,hF0,faceLabel_empty,monomial_zero',
        C_1,one_smul,Module.Basis.coord_apply,Module.Basis.repr_self,
        Finsupp.single_eq_same]
  | zero => simp only [map_zero,zero_smul]
  | add x y hx hy ihx ihy =>
      simpa only [map_add,add_smul] using congrArg₂ (·+·) ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul,smul_smul,smul_eq_mul] using congrArg (c • ·) ih

theorem augmentation_cycle_iff (z : chainPiece (k:=k) (X:=X) K 1) :
    augmentation K u z=0 ↔ differential K hK u z.val=0 := by
  constructor
  · intro hz
    apply labelledEmbedding_injective K u
    rw [map_zero,labelledEmbedding_degree_zero K u _ (differential_lowers K hK u 0 _ z.property)]
    have he : Simplicial.basis.coord ∅ (labelledEmbedding K u (differential K hK u z.val))=0 := by
      rw [labelledEmbedding_differential]
      exact congrArg Subtype.val hz
    rw [he,zero_smul]
  · intro hz
    apply Subtype.ext
    change Simplicial.basis.coord ∅ (Simplicial.boundary (labelledEmbedding K u z.val))=0
    rw [← labelledEmbedding_differential K hK u z.val,hz,map_zero,map_zero]

end FourPapers.LabelledSimplicial

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LabelledSimplicialResolution -/
section

/-! # A genuine finite free resolution from divisor contractions

The resolution has one polynomial basis vector for each nonempty face.
Its homological degree is cardinality minus one and its fine shift is the
least common multiple of the vertex monomials. Exactness is the actual
polynomial exactness proved by the fine-strand equivalences.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.LabelledSimplicial

open Classical CommAlg CategoryTheory HomologicalComplex

universe u w
variable {k : Type u} {X : Type w} {V : Type} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype X] (K : Finset V → Prop) (hK : Simplicial.Downward K)
  (u : V → X →₀ ℕ)
  (contract : ∀ b : X →₀ ℕ,(∃ v,K {v} ∧ u v≤b) →
    SimplicialDomination.FaceContraction (k:=k) (divisorFaces K u b))

def resolutionData : SubmoduleComplexData (PolynomialRing (k:=k) (X:=X))
    (FreeModule (k:=k) (X:=X) K) where
  piece p := chainPiece K (p+1)
  d := differential K hK u
  square_zero := differential_square K hK u
  lowers p := differential_lowers K hK u (p+1)

def resolutionComplex : ChainComplex (ModuleCat.{max u w} (PolynomialRing (k:=k) (X:=X))) ℕ :=
  (resolutionData (k:=k) K hK u).complex

def resolutionBasis (p : ℕ) : Module.Basis {F : Face K // F.val.card=p+1}
    (PolynomialRing (k:=k) (X:=X)) ((resolutionComplex (k:=k) K hK u).X p) :=
  chainBasis (k:=k) (X:=X) K (p+1)

theorem resolutionTerm_free (p : ℕ) : Module.Free (PolynomialRing (k:=k) (X:=X))
    ((resolutionComplex (k:=k) K hK u).X p) := Module.Free.of_basis (resolutionBasis (k:=k) K hK u p)

theorem resolutionTerm_finite (p : ℕ) : Module.Finite (PolynomialRing (k:=k) (X:=X))
    ((resolutionComplex (k:=k) K hK u).X p) := Module.Finite.of_basis (resolutionBasis (k:=k) K hK u p)

theorem resolutionTerm_zero_above (N : ℕ) (hN : ∀ F,K F→F.card≤N+1)
    (p : ℕ) (hp : N<p) : Subsingleton ((resolutionComplex (k:=k) K hK u).X p) := by
  have hI : IsEmpty {F : Face K // F.val.card=p+1} :=
    ⟨fun F => by have h := hN F.val.val F.val.property; have hf := F.property; omega⟩
  letI := hI
  exact (resolutionBasis (k:=k) K hK u p).equivFun.injective.subsingleton

theorem resolution_augmentation_comp :
    (augmentation (k:=k) K u).comp ((resolutionData (k:=k) K hK u).differential 0)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact augmentationPolynomial_boundary K hK u z.val

theorem resolution_d_augmentation :
    (resolutionComplex (k:=k) K hK u).d 1 0 ≫
      ModuleCat.ofHom (augmentation (k:=k) K u) = 0 := by
  rw [show (resolutionComplex (k:=k) K hK u).d 1 0 =
      ModuleCat.ofHom ((resolutionData (k:=k) K hK u).differential 0) from
    SubmoduleComplexData.complex_d _ 0]
  exact ModuleCat.hom_ext (resolution_augmentation_comp (k:=k) K hK u)

include contract in
theorem resolution_exact_augmentation :
    (ShortComplex.mk ((resolutionComplex (k:=k) K hK u).d 1 0)
      (ModuleCat.ofHom (augmentation (k:=k) K u))
      (resolution_d_augmentation (k:=k) K hK u)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hdz := (augmentation_cycle_iff K hK u z).mp hz
  obtain ⟨y,hy,hdy⟩ := positive_filling K hK u contract 0 z.val z.property hdz
  refine ⟨⟨y,hy⟩,?_⟩
  change (resolutionData (k:=k) K hK u).complex.d 1 0 ⟨y,hy⟩=z
  rw [SubmoduleComplexData.complex_d]
  exact Subtype.ext hdy

include contract in
theorem resolution_exact_positive (p : ℕ) :
    (resolutionComplex (k:=k) K hK u).ExactAt (p+1) := by
  apply ((resolutionComplex (k:=k) K hK u).exactAt_iff' (p+2) (p+1) p
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hdz : differential K hK u z.val=0 := by
    change (resolutionData (k:=k) K hK u).complex.d (p+1) p z=0 at hz
    rw [SubmoduleComplexData.complex_d] at hz
    exact congrArg Subtype.val hz
  obtain ⟨y,hy,hdy⟩ := positive_filling K hK u contract (p+1) z.val z.property hdz
  refine ⟨⟨y,hy⟩,?_⟩
  change (resolutionData (k:=k) K hK u).complex.d (p+2) (p+1) ⟨y,hy⟩=z
  rw [SubmoduleComplexData.complex_d]
  exact Subtype.ext hdy

/-- A Mathlib projective resolution of the literal monomial ideal,
with the displayed finite free bases and actual labelled differential. -/
def resolution : ProjectiveResolution
    (ModuleCat.of (PolynomialRing (k:=k) (X:=X)) (generatorIdeal (k:=k) K u)) where
  complex := resolutionComplex (k:=k) K hK u
  projective p := ModuleCat.projective_of_free (resolutionBasis (k:=k) K hK u p)
  π := (ChainComplex.toSingle₀Equiv (resolutionComplex (k:=k) K hK u) _).symm
    ⟨ModuleCat.ofHom (augmentation (k:=k) K u),resolution_d_augmentation K hK u⟩
  quasiIso := ⟨fun p => by
    cases p with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
        · dsimp
          simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
          exact ⟨resolution_exact_augmentation K hK u contract,
            (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective K u)⟩
        · exact (resolutionComplex (k:=k) K hK u).shape 0 0 (by simp)
        all_goals rfl
    | succ p =>
        rw [quasiIsoAt_iff_exactAt']
        · exact resolution_exact_positive K hK u contract p
        · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end FourPapers.LabelledSimplicial

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AlcoveResolution -/
section

/-!
# The literal cellular resolution in Theorem 8.1

The vertices are the order-reversing integral points of the dilated
order polytope. Faces are chains contained in one unit cube, and their
labels are the actual products of the row monomials. The complex below
is a Mathlib projective resolution of the actual ideal power. It is
finite free over every commutative ring and has length at most the
number of join-irreducibles of the finite sublattice.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg.Polymatroid

universe u v
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
  {k : Type u} [CommRing k]

/-- The cellular augmentation ideal is exactly the requested power,
not an ideal defined by the conclusion of the resolution theorem. -/
theorem alcove_generatorIdeal (m : ℕ) :
    LabelledSimplicial.generatorIdeal (k:=k) (alcoveFaces hE m)
      (alcoveVertexLabel.{v} hE hne m) =
        (finiteSublatticeIdeal n (k:=k) E)^m := by
  rw [← alcoveVertexLabel_ideal (k:=k) hE hne m]
  unfold LabelledSimplicial.generatorIdeal monomialIdeal
  congr 1
  ext f
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨_,Finset.mem_image.mpr ⟨v,(alcoveSingleton_face_iff hE m v).mp hv,rfl⟩,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨v,(alcoveSingleton_face_iff hE m v).mpr hv,rfl⟩

def alcoveResolutionContraction (m : ℕ) (b : Exponent (FiniteVariable.{v} n))
    (hb : ∃ v,alcoveFaces hE m {v} ∧ alcoveVertexLabel hE hne m v≤b) :
    SimplicialDomination.FaceContraction (k:=k)
      (LabelledSimplicial.divisorFaces (alcoveFaces hE m)
        (alcoveVertexLabel hE hne m) b) := by
  apply alcoveDivisorContraction (k := k) hE hne m b
  obtain ⟨v,hv,hvb⟩ := hb
  exact ⟨v,Finset.mem_filter.mpr ⟨(alcoveSingleton_face_iff hE m v).mp hv,hvb⟩⟩

/-- The actual target ideal is identified by the proved equality above;
the underlying chain complex and its labelled matrices are unchanged. -/
def alcoveResolutionTargetIso (m : ℕ) :
    ModuleCat.of (MvPolynomial (FiniteVariable.{v} n) k)
      (LabelledSimplicial.generatorIdeal (k:=k) (alcoveFaces hE m)
        (alcoveVertexLabel hE hne m)) ≅
    ModuleCat.of (MvPolynomial (FiniteVariable.{v} n) k)
      ↥((finiteSublatticeIdeal n (k:=k) E)^m) :=
  (LinearEquiv.ofEq _ _ (alcove_generatorIdeal (k:=k) hE hne m)).toModuleIso

/-- Theorem 8.1, the cellular resolution, over an arbitrary coefficient
ring. Its faces and incidence numbers do not depend on that ring. -/
def theorem81_cellularResolution (m : ℕ) : ProjectiveResolution
    (ModuleCat.of (MvPolynomial (FiniteVariable.{v} n) k)
      ↥((finiteSublatticeIdeal n (k:=k) E)^m)) where
  complex := LabelledSimplicial.resolutionComplex (k := k) (alcoveFaces hE m)
    (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)
  projective p := (LabelledSimplicial.resolution (k := k)
    (alcoveFaces hE m) (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)
    (alcoveResolutionContraction (k:=k) hE hne m)).projective p
  π := (LabelledSimplicial.resolution (k := k)
      (alcoveFaces hE m) (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)
      (alcoveResolutionContraction (k:=k) hE hne m)).π ≫
    (ChainComplex.single₀ (ModuleCat.{max u v} (MvPolynomial (FiniteVariable.{v} n) k))).map
      (alcoveResolutionTargetIso hE hne m).hom
  quasiIso := by infer_instance

/-- The displayed basis is indexed by genuine p-dimensional simplices. -/
def theorem81_cellularBasis (m p : ℕ) :
    Module.Basis {F : LabelledSimplicial.Face (alcoveFaces hE m) // F.val.card=p+1}
      (MvPolynomial (FiniteVariable.{v} n) k)
      ((theorem81_cellularResolution (k:=k) hE hne m).complex.X p) :=
  LabelledSimplicial.resolutionBasis (k := k) (alcoveFaces hE m) (alcoveFaces_downward hE m)
    (alcoveVertexLabel hE hne m) p

theorem theorem81_cellular_free (m p : ℕ) :
    Module.Free (MvPolynomial (FiniteVariable.{v} n) k)
      ((theorem81_cellularResolution (k:=k) hE hne m).complex.X p) :=
  Module.Free.of_basis (theorem81_cellularBasis hE hne m p)

theorem theorem81_cellular_finite (m p : ℕ) :
    Module.Finite (MvPolynomial (FiniteVariable.{v} n) k)
      ((theorem81_cellularResolution (k:=k) hE hne m).complex.X p) :=
  Module.Finite.of_basis (theorem81_cellularBasis hE hne m p)

/-- The actual chain groups, not merely their homology, vanish above h. -/
theorem theorem81_cellular_length (m p : ℕ) (hp : finiteLatticeHeight hE hne<p) :
    Subsingleton ((theorem81_cellularResolution (k:=k) hE hne m).complex.X p) :=
  LabelledSimplicial.resolutionTerm_zero_above (alcoveFaces hE m)
    (alcoveFaces_downward hE m) (alcoveVertexLabel hE hne m)
    (finiteLatticeHeight hE hne) (fun _ hF => alcoveFaces_card_le hE hne m hF) p hp

theorem theorem81_projectiveDimension_upper (m : ℕ) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{v} n) k)
      ↥((finiteSublatticeIdeal n (k:=k) E)^m)) ≤
        (finiteLatticeHeight hE hne : WithBot ℕ∞) := by
  apply FourPapers.projectiveDimension_le_of_bounded_resolution
    (theorem81_cellularResolution hE hne m) (finiteLatticeHeight hE hne)
  intro p hp
  exact ModuleCat.isZero_iff_subsingleton.mpr (theorem81_cellular_length hE hne m p hp)

/-- The fine shift of a free generator is the least common multiple of
the actual row-monomial labels of its vertices. -/
def theorem81_cellularShift (m : ℕ)
    (F : LabelledSimplicial.Face (alcoveFaces hE m)) : Exponent (FiniteVariable.{v} n) :=
  LabelledSimplicial.faceLabel (alcoveVertexLabel hE hne m) F.val

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BottomChainMap -/
section

/-!
# Multiplication by the minimum in the actual Koszul coordinates

Prepending the minimum leaves the coefficient quotient and exterior face
unchanged. The resulting basis inclusion is therefore the literal monomial
multiplication map, and it commutes with the original Koszul differential.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped BigOperators

universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (μ : E) (hμ : ∀ a : E, μ.val ≤ a.val)

@[simp] theorem bottomPrepend_factorWeight {m : ℕ} (w : FiniteMultichain n E m) :
    finiteChainFactorWeight.{u} (bottomPrepend μ hμ w) =
      reesVariableWeight (finiteTupleImage E) (finiteTupleToNat μ.val) + finiteChainFactorWeight.{u} w := by
  simp only [finiteChainFactorWeight_sum, Fin.sum_univ_succ,
    bottomPrepend_zero, bottomPrepend_succ]

theorem bottomChainFace_erase (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (v : FiniteVariable.{u} n) :
    bottomChainFace μ hμ (chainFaceErase hE a v) =
      chainFaceErase hE (bottomChainFace μ hμ a) v := by
  apply (chainFaceEquiv hE (α + finiteRowExponent n μ.val)).injective
  apply Subtype.ext
  simp only [chainFaceEquiv_val, bottomChainFace_face, chainFaceErase_val]

def bottomChainMap (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    ChainTotalModule n E m α k →ₗ[k]
      ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k :=
  BasisIndexRetraction.inclusion (chainTotalBasis n E m α k)
    (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k)
    (bottomChainFace μ hμ)

def bottomChainRetract (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k →ₗ[k]
      ChainTotalModule n E m α k :=
  BasisIndexRetraction.retraction (chainTotalBasis n E m α k)
    (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k)
    (bottomChainFace μ hμ) (bottomChainFace_injective μ hμ m α)

@[simp] theorem bottomChainMap_basis (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (a : ChainFaceIndex n E m α) :
    bottomChainMap (k := k) μ hμ m α (chainTotalBasis n E m α k a) =
      chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k (bottomChainFace μ hμ a) :=
  BasisIndexRetraction.inclusion_basis _ _ _ a

@[simp] theorem bottomChainRetract_coefficient (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (y : ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k)
    (a : ChainFaceIndex n E m α) :
    (chainTotalBasis n E m α k).repr (bottomChainRetract μ hμ m α y) a =
      (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k).repr y
        (bottomChainFace μ hμ a) :=
  BasisIndexRetraction.retraction_coefficient _ _ _ _ y a

@[simp] theorem bottomChainRetract_map (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (x : ChainTotalModule n E m α k) :
    bottomChainRetract μ hμ m α (bottomChainMap μ hμ m α x) = x :=
  BasisIndexRetraction.retraction_inclusion _ _ _ _ x

/-- The minimum changes neither the coefficient quotient nor the residual
fine exponent, so the two literal exterior submodules agree. -/
theorem bottomAdmissibleChain_totalFaceModule (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (w : AdmissibleChain n E m α) :
    TotalFaceModule (k := k)
        (quotientKoszulFaces
          (finiteChainCoefficientFamily n (bottomAdmissibleChain μ hμ w).val)
          ((α + finiteRowExponent n μ.val) -
            finiteChainShift n (bottomAdmissibleChain μ hμ w).val)) =
      TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α - finiteChainShift n w.val)) := by
  change TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n (bottomPrepend μ hμ w.val))
        ((α + finiteRowExponent n μ.val) - finiteChainShift n (bottomPrepend μ hμ w.val))) = _
  rw [bottomPrepend_coefficientFamily, bottom_residual]

/-- Exterior coordinates of the literal block subtype are ambient basis
coordinates; the proof identifies the canonical subtype module structures. -/
private theorem bottomTotalFaceBasis_repr
    (P : Finset (FiniteVariable.{u} n) → Prop)
    (x : TotalFaceModule (k := k) P) (a : {F // P F}) :
    (totalFaceBasis (k := k) P).repr x a =
      (Simplicial.basis (k := k) (V := FiniteVariable.{u} n)).repr x.val a.val := by
  simpa only [totalFaceBasis] using!
    (FourPapers.restrictedBasis_repr
      (Simplicial.basis (k := k) (V := FiniteVariable.{u} n)) P x a)

/-- The retraction is the literal projection onto the blocks whose first
factor is the minimum. It retains each exterior coordinate unchanged. -/
theorem bottomChainRetract_block (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (y : ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k)
    (w : AdmissibleChain n E m α) :
    (bottomChainRetract μ hμ m α y w).val =
      (y (bottomAdmissibleChain μ hμ w)).val := by
  let z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (α - finiteChainShift n w.val)) :=
    ⟨(y (bottomAdmissibleChain μ hμ w)).val,
      (bottomAdmissibleChain_totalFaceModule (k := k) μ hμ m α w).le
        (y (bottomAdmissibleChain μ hμ w)).property⟩
  have he : bottomChainRetract μ hμ m α y w = z := by
    apply (totalFaceBasis (k := k) _).repr.injective
    apply Finsupp.ext
    intro a
    have hc := bottomChainRetract_coefficient μ hμ m α y ⟨w, a⟩
    simpa only [chainTotalBasis, dfinsuppBasis_repr_apply,
      bottomTotalFaceBasis_repr, bottomChainFace, z] using! hc
  exact congrArg Subtype.val he

theorem bottomChainRetract_special (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (y : ChainTotalModule n E (m+1) (α + finiteRowExponent n μ.val) k) :
    bottomChainRetract μ hμ m α
        (chainTotalSpecialDifferential n E (m+1) (α + finiteRowExponent n μ.val) k y) =
      chainTotalSpecialDifferential n E m α k (bottomChainRetract μ hμ m α y) := by
  apply DFinsupp.ext
  intro w
  apply Subtype.ext
  rw [bottomChainRetract_block]
  change (quotientTotalDifferential _ _ (y (bottomAdmissibleChain μ hμ w))).val =
    (quotientTotalDifferential _ _ (bottomChainRetract μ hμ m α y w)).val
  rw [quotientTotalDifferential_val, quotientTotalDifferential_val, bottomChainRetract_block]
  simp only [bottomAdmissibleChain, bottomPrepend_coefficientFamily, bottom_residual]

theorem bottomChainMap_differential (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    (bottomChainMap (k := k) μ hμ m α).comp (chainTotalOrdinaryDifferential hE m α k) =
      (chainTotalOrdinaryDifferential hE (m+1) (α + finiteRowExponent n μ.val) k).comp
        (bottomChainMap μ hμ m α) := by
  apply (chainTotalBasis n E m α k).ext
  intro a
  simp only [LinearMap.comp_apply, chainTotalOrdinaryDifferential_basis,
    bottomChainMap_basis, map_sum, map_zsmul_unit, bottomChainFace_face,
    bottomChainFace_erase]

/-- In the actual upper Koszul face basis, multiplying a coefficient by
`u_μ` shifts the fine exponent by `deg u_μ` and leaves its exterior coordinate
unchanged. This identifies the constructed map with that multiplication. -/
theorem bottomChainMap_actual_coordinates (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (x : ChainTotalModule n E m α k) :
    (chainTotalEquiv hE (m+1) (α + finiteRowExponent n μ.val) k
      (bottomChainMap μ hμ m α x)).val = (chainTotalEquiv hE m α k x).val := by
  have he :
      (TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) (m+1))
          (α + finiteRowExponent n μ.val))).subtype.comp
        ((chainTotalEquiv hE (m+1) (α + finiteRowExponent n μ.val) k).toLinearMap.comp
          (bottomChainMap μ hμ m α)) =
      (TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)).subtype.comp
        (chainTotalEquiv hE m α k).toLinearMap := by
    apply (chainTotalBasis n E m α k).ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      bottomChainMap_basis, chainTotalEquiv_basis, totalFaceBasis_val,
      chainFaceEquiv_val, bottomChainFace_face]
  exact LinearMap.congr_fun he x

theorem bottomChainMap_preserves (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    FilteredHomology.Preserves
      (Universal.basisFiltration (chainTotalBasis n E m α k)
        (fun a => reesVariableWeight (finiteTupleImage E) (finiteTupleToNat μ.val) + finiteChainFactorWeight.{u} a.1.val))
      (Universal.basisFiltration
        (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k)
        (fun a => finiteChainFactorWeight.{u} a.1.val))
      (bottomChainMap μ hμ m α) :=
  BasisIndexRetraction.inclusion_preserves _ _ _ _ _
    (fun a => bottomPrepend_factorWeight μ hμ a.1.val)

theorem bottomChainRetract_preserves (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    FilteredHomology.Preserves
      (Universal.basisFiltration
        (chainTotalBasis n E (m+1) (α + finiteRowExponent n μ.val) k)
        (fun a => finiteChainFactorWeight.{u} a.1.val))
      (Universal.basisFiltration (chainTotalBasis n E m α k)
        (fun a => reesVariableWeight (finiteTupleImage E) (finiteTupleToNat μ.val) + finiteChainFactorWeight.{u} a.1.val))
      (bottomChainRetract μ hμ m α) :=
  BasisIndexRetraction.retraction_preserves _ _ _ _ _ _
    (fun a => bottomPrepend_factorWeight μ hμ a.1.val)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SignedWeightedMonoid -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-!
# The actual family for a signed weight

Negative weights are realized inside a Laurent polynomial monoid algebra.
The family itself is a free algebra over the polynomial ring in the parameter.
Its multiplication coefficients involve only nonnegative weight defects.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical Polynomial
universe u v
variable {k : Type u} [CommRing k] {M : Type v} [AddCommMonoid M]

def signedWeightedMonomial (w : M → ℤ) (a : M) :
    AddMonoidAlgebra (LaurentPolynomial k) M :=
  AddMonoidAlgebra.single a (LaurentPolynomial.T (w a))

lemma signedWeightedMonomial_linearIndependent (w : M → ℤ) :
    LinearIndependent k[X] (signedWeightedMonomial (k := k) w) := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro a
  change l a = 0
  by_cases ha : l a = 0
  · exact ha
  have hc := congrArg (fun f : AddMonoidAlgebra (LaurentPolynomial k) M => f.coeff a) hl
  have hc' : Polynomial.toLaurent (l a) * LaurentPolynomial.T (w a) = 0 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, signedWeightedMonomial,
      AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul,
      AddMonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, ha, Algebra.smul_def] using hc
  have hh := congrArg (fun f : LaurentPolynomial k => f * LaurentPolynomial.T (-w a)) hc'
  simp only [LaurentPolynomial.mul_T_assoc, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one, zero_mul] at hh
  exact Polynomial.toLaurent_injective (by simpa using hh)

lemma signedWeightedMonomial_mul (w : M → ℤ)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) (a b : M) :
    signedWeightedMonomial (k := k) w a * signedWeightedMonomial w b =
      (X ^ (w a + w b - w (a + b)).toNat : k[X]) •
        signedWeightedMonomial w (a + b) := by
  unfold signedWeightedMonomial
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.smul_single]
  congr 1
  rw [Algebra.smul_def, LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_X_pow, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hsub a b))]
  congr 1
  ring

def signedWeightedSpan (w : M → ℤ) :
    Submodule k[X] (AddMonoidAlgebra (LaurentPolynomial k) M) :=
  Submodule.span k[X] (Set.range (signedWeightedMonomial w))

lemma signedWeightedMonomial_mem (w : M → ℤ) (a : M) :
    signedWeightedMonomial (k := k) w a ∈ signedWeightedSpan w :=
  Submodule.subset_span ⟨a, rfl⟩

lemma signedWeightedSpan_one (w : M → ℤ) (hzero : w 0 = 0) :
    (1 : AddMonoidAlgebra (LaurentPolynomial k) M) ∈ signedWeightedSpan w := by
  have h := signedWeightedMonomial_mem (k := k) w 0
  simpa only [signedWeightedMonomial, hzero, LaurentPolynomial.T_zero,
    ← AddMonoidAlgebra.one_def] using h

lemma signedWeightedSpan_mul (w : M → ℤ)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b)
    {x y : AddMonoidAlgebra (LaurentPolynomial k) M}
    (hx : x ∈ signedWeightedSpan w) (hy : y ∈ signedWeightedSpan w) :
    x * y ∈ signedWeightedSpan w := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          rw [signedWeightedMonomial_mul w hsub]
          exact Submodule.smul_mem _ _ (signedWeightedMonomial_mem w _)
      | zero => simpa using (Submodule.zero_mem (signedWeightedSpan (k := k) w))
      | add y z hy hz ihy ihz =>
          simpa only [mul_add] using Submodule.add_mem (signedWeightedSpan w) ihy ihz
      | smul c y hy ih =>
          simpa only [mul_smul_comm] using Submodule.smul_mem (signedWeightedSpan w) c ih
  | zero => simpa using (Submodule.zero_mem (signedWeightedSpan (k := k) w))
  | add x z hx hz ihx ihz =>
      simpa only [add_mul] using Submodule.add_mem (signedWeightedSpan w) ihx ihz
  | smul c x hx ih =>
      simpa only [smul_mul_assoc] using Submodule.smul_mem (signedWeightedSpan w) c ih

def signedWeightedMonoidAlgebra (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) :
    Subalgebra k[X] (AddMonoidAlgebra (LaurentPolynomial k) M) :=
  (signedWeightedSpan w).toSubalgebra (signedWeightedSpan_one w hzero)
    (fun _ _ => signedWeightedSpan_mul w hsub)

def signedWeightedSpanEquiv (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) :
    signedWeightedSpan (k := k) w ≃ₗ[k[X]]
      signedWeightedMonoidAlgebra (k := k) w hzero hsub where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def signedWeightedMonoidBasis (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) :
    Module.Basis M k[X] (signedWeightedMonoidAlgebra (k := k) w hzero hsub) :=
  (Module.Basis.span (signedWeightedMonomial_linearIndependent (k := k) w)).map
    (signedWeightedSpanEquiv w hzero hsub)

@[simp] lemma signedWeightedMonoidBasis_val (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) (a : M) :
    (signedWeightedMonoidBasis (k := k) w hzero hsub a).val =
      signedWeightedMonomial w a := by
  change (Module.Basis.span (signedWeightedMonomial_linearIndependent (k := k) w) a).val = _
  exact Module.Basis.coe_span_apply _ a

@[simp] lemma signedWeightedMonoidBasis_zero (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) :
    signedWeightedMonoidBasis (k := k) w hzero hsub 0 = 1 := by
  apply Subtype.ext
  simp only [signedWeightedMonoidBasis_val, signedWeightedMonomial, hzero,
    LaurentPolynomial.T_zero, AddMonoidAlgebra.one_def, Subalgebra.coe_one]

lemma signedWeightedMonoidBasis_mul (w : M → ℤ) (hzero : w 0 = 0)
    (hsub : ∀ a b, w (a + b) ≤ w a + w b) (a b : M) :
    signedWeightedMonoidBasis (k := k) w hzero hsub a *
        signedWeightedMonoidBasis w hzero hsub b =
      (X ^ (w a + w b - w (a + b)).toNat : k[X]) •
        signedWeightedMonoidBasis w hzero hsub (a + b) := by
  apply Subtype.ext
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_smul, signedWeightedMonoidBasis_val]
    using signedWeightedMonomial_mul (k := k) w hsub a b

section Equivalence
variable (w : M → ℕ) (hw0 : w 0 = 0) (hws : ∀ a b, w (a + b) ≤ w a + w b)
variable (v : M → ℤ) (hv0 : v 0 = 0) (hvs : ∀ a b, v (a + b) ≤ v a + v b)
variable (hdefect : ∀ a b, w a + w b - w (a + b) = (v a + v b - v (a + b)).toNat)

def signedWeightedBasisEquiv :
    weightedMonoidAlgebra (k := k) w hw0 hws ≃ₗ[k[X]]
      signedWeightedMonoidAlgebra (k := k) v hv0 hvs :=
  (weightedMonoidBasis w hw0 hws).equiv (signedWeightedMonoidBasis v hv0 hvs) (Equiv.refl M)

@[simp] lemma signedWeightedBasisEquiv_basis (a : M) :
    signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs
        (weightedMonoidBasis w hw0 hws a) = signedWeightedMonoidBasis v hv0 hvs a :=
  Module.Basis.equiv_apply _ _ _ _

lemma signedWeightedBasisEquiv_one :
    signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs 1 = 1 := by
  have h0 : weightedMonoidBasis (k := k) w hw0 hws 0 = 1 := by
    apply Subtype.ext
    simp only [weightedMonoidBasis_val, weightedMonomial, hw0, pow_zero,
      AddMonoidAlgebra.one_def, Subalgebra.coe_one]
  rw [← h0, signedWeightedBasisEquiv_basis, signedWeightedMonoidBasis_zero]

include hdefect in
lemma signedWeightedBasisEquiv_mul
    (x y : weightedMonoidAlgebra (k := k) w hw0 hws) :
    signedWeightedBasisEquiv w hw0 hws v hv0 hvs (x * y) =
      signedWeightedBasisEquiv w hw0 hws v hv0 hvs x *
        signedWeightedBasisEquiv w hw0 hws v hv0 hvs y := by
  have hx : x ∈ Submodule.span k[X] (Set.range (weightedMonoidBasis w hw0 hws)) := by
    rw [Module.Basis.span_eq]
    trivial
  have hy : y ∈ Submodule.span k[X] (Set.range (weightedMonoidBasis w hw0 hws)) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          rw [weightedMonoidBasis_mul,
            (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_smul,
            signedWeightedBasisEquiv_basis,
            signedWeightedBasisEquiv_basis, signedWeightedBasisEquiv_basis,
            signedWeightedMonoidBasis_mul, hdefect]
      | zero => simp only [mul_zero,
          (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_zero]
      | add y z hy hz ihy ihz => simp only [mul_add,
          (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_add, ihy, ihz]
      | smul c y hy ih => simp only [mul_smul_comm,
          (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_smul, ih]
  | zero => simp only [zero_mul,
      (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_zero]
  | add x z hx hz ihx ihz => simp only [add_mul,
      (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_add, ihx, ihz]
  | smul c x hx ih => simp only [smul_mul_assoc,
      (signedWeightedBasisEquiv (k := k) w hw0 hws v hv0 hvs).map_smul, ih]

/-- Homogeneous regrading gives an algebra isomorphism with the actual
Laurent realization of the original signed-weight family. -/
def signedWeightedAlgebraEquiv :
    weightedMonoidAlgebra (k := k) w hw0 hws ≃ₐ[k[X]]
      signedWeightedMonoidAlgebra (k := k) v hv0 hvs :=
  AlgEquiv.ofLinearEquiv (signedWeightedBasisEquiv w hw0 hws v hv0 hvs)
    (signedWeightedBasisEquiv_one w hw0 hws v hv0 hvs)
    (signedWeightedBasisEquiv_mul w hw0 hws v hv0 hvs hdefect)

end Equivalence
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.signedWeightedAlgebraEquiv

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.LiteralWeightFamily -/
section

/-!
# The literal image of a weight-homogenized monoid presentation

The parameter algebra is generated by the original presentation variables
with their specified signed powers of the Laurent parameter. The image is
compared with the standard-monomial span by a proved equality, without
assuming that the two constructions agree.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Sublattice.LiteralWeightFamily

open Classical MvPolynomial
open scoped Polynomial

universe uk ut um
variable {k : Type uk} {T : Type ut} {M : Type um} [CommRing k] [AddCommMonoid M]
  (φ : (T →₀ ℕ) →+ M) (ω : T → ℤ)

abbrev Ambient := AddMonoidAlgebra (LaurentPolynomial k) M

def generator (t : T) : Ambient (k := k) (M := M) :=
  AddMonoidAlgebra.single (φ (Finsupp.single t 1)) (LaurentPolynomial.T (ω t))

def presentationMap : MvPolynomial T k[X] →ₐ[k[X]] Ambient (k := k) (M := M) :=
  MvPolynomial.aeval (generator (k := k) φ ω)

def monomialValue (c : T →₀ ℕ) : Ambient (k := k) (M := M) :=
  AddMonoidAlgebra.single (φ c) (LaurentPolynomial.T (Finsupp.weight ω c))

theorem presentationMap_monomial (c : T →₀ ℕ) :
    presentationMap (k := k) φ ω (MvPolynomial.monomial c 1) = monomialValue φ ω c := by
  refine c.induction ?_ ?_
  · change presentationMap (k := k) φ ω (1 : MvPolynomial T k[X]) = _
    simp only [map_one, monomialValue, map_zero, LaurentPolynomial.T_zero]
    rfl
  · intro t r c ht hr ih
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow]
    rw [show presentationMap (k := k) φ ω (MvPolynomial.X t) = generator φ ω t from
      MvPolynomial.aeval_X _ _, ih]
    have hs : (Finsupp.single t r : T →₀ ℕ) = r • Finsupp.single t 1 := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [generator, monomialValue, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single, LaurentPolynomial.T_pow,
      ← LaurentPolynomial.T_add, map_add, Finsupp.weight_single,
      hs, map_nsmul, nsmul_eq_mul, Nat.cast_one, one_mul]

/-- The literal algebra image; its generators are specified before any
normal-form argument or admissibility hypothesis is introduced. -/
def family : Subalgebra k[X] (Ambient (k := k) (M := M)) :=
  (presentationMap (k := k) φ ω).range

theorem monomialValue_eq_parameter_smul {c e : T →₀ ℕ}
    (hφ : φ c = φ e) (hω : Finsupp.weight ω c ≤ Finsupp.weight ω e) :
    monomialValue (k := k) φ ω e =
      (Polynomial.X ^ (Finsupp.weight ω e - Finsupp.weight ω c).toNat : k[X]) •
        monomialValue φ ω c := by
  unfold monomialValue
  rw [AddMonoidAlgebra.smul_single, Algebra.smul_def,
    LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X_pow,
    ← LaurentPolynomial.T_add, Int.toNat_of_nonneg (sub_nonneg.mpr hω), hφ]
  congr 2
  omega

section NormalForm

variable (normal : M → T →₀ ℕ)
  (himage : ∀ a, φ (normal a) = a)
  (hweight : ∀ c, Finsupp.weight ω (normal (φ c)) ≤ Finsupp.weight ω c)

def normalWeight (a : M) : ℤ := Finsupp.weight ω (normal a)

variable (hzero : normalWeight ω normal 0 = 0)
  (hsub : ∀ a b, normalWeight ω normal (a+b) ≤
    normalWeight ω normal a + normalWeight ω normal b)

include himage hweight in
theorem generator_mem_normalSpan (t : T) :
    generator (k := k) φ ω t ∈ signedWeightedSpan (normalWeight ω normal) := by
  have he : generator (k := k) φ ω t =
      monomialValue φ ω (Finsupp.single t 1) := by
    simp only [generator, monomialValue, Finsupp.weight_single, one_nsmul]
  rw [he, monomialValue_eq_parameter_smul φ ω (himage _)
    (hweight (Finsupp.single t 1))]
  apply Submodule.smul_mem
  have hm : monomialValue (k := k) φ ω (normal (φ (Finsupp.single t 1))) =
      signedWeightedMonomial (normalWeight ω normal) (φ (Finsupp.single t 1)) := by
    unfold monomialValue signedWeightedMonomial normalWeight
    rw [himage]
  rw [hm]
  exact signedWeightedMonomial_mem _ _

include himage hweight in
/-- The normal-form span is proved equal to the literal generator image.
No presentation equality is assumed in this statement. -/
theorem family_eq_normalSpan : family (k := k) φ ω =
    signedWeightedMonoidAlgebra (normalWeight ω normal) hzero hsub := by
  apply le_antisymm
  · rintro x ⟨f,rfl⟩
    induction f using MvPolynomial.induction_on with
    | C c =>
        change presentationMap φ ω (MvPolynomial.C c) ∈ _
        rw [presentationMap, MvPolynomial.aeval_C]
        exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg =>
        rw [(presentationMap (k := k) φ ω).map_add]
        exact Subalgebra.add_mem _ hf hg
    | mul_X f t hf =>
        rw [(presentationMap (k := k) φ ω).map_mul]
        change presentationMap (k := k) φ ω f *
          presentationMap (k := k) φ ω (MvPolynomial.X t) ∈ _
        rw [show presentationMap (k := k) φ ω (MvPolynomial.X t) = generator φ ω t from
          MvPolynomial.aeval_X _ _]
        exact Subalgebra.mul_mem _ hf
          (generator_mem_normalSpan φ ω normal himage hweight t)
  · intro x hx
    change x ∈ signedWeightedSpan (normalWeight ω normal) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a,rfl⟩ := hx
        refine ⟨MvPolynomial.monomial (normal a) 1, ?_⟩
        change presentationMap (k := k) φ ω (MvPolynomial.monomial (normal a) 1) = _
        rw [presentationMap_monomial]
        unfold monomialValue signedWeightedMonomial normalWeight
        rw [himage]
    | zero => exact Subalgebra.zero_mem _
    | add x y hx hy ihx ihy => exact Subalgebra.add_mem _ ihx ihy
    | smul c x hx ih => exact (family (k := k) φ ω).toSubmodule.smul_mem c ih

end NormalForm
end FourPapers.Sublattice.LiteralWeightFamily


end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LabelledSimplicialCoefficientChange -/
section

/-!
# Literal coefficient base change of labelled cellular complexes

The same oriented faces index every free module. The coefficient map
commutes with the actual signed lcm differential. Tensor-coordinate
equivalences then identify coefficient base change with that displayed
complex, as polynomial-linear maps, including coefficient rings that are
not flat over the source ring.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.LabelledSimplicial
open Classical CommAlg MvPolynomial PolynomialCoefficientBaseChange
open scoped TensorProduct
variable {R A X : Type*} {V : Type} [CommRing R] [CommRing A]
  [Fintype V] [LinearOrder V] [Fintype X]
  (K : Finset V → Prop) (hK : Simplicial.Downward K) (u : V → X →₀ ℕ)

def coefficientChange (φ : R →+* A) :
    FreeModule (k:=R) (X:=X) K →ₛₗ[(MvPolynomial.map φ : MvPolynomial X R →+* MvPolynomial X A)] FreeModule (k:=A) (X:=X) K where
  toFun z := Finsupp.mapRange (MvPolynomial.map φ) (map_zero _) z
  map_add' z w := by ext F; simp only [Finsupp.mapRange_apply,Finsupp.add_apply,map_add]
  map_smul' p z := by ext F; simp only [Finsupp.mapRange_apply,Finsupp.smul_apply,
    smul_eq_mul,map_mul,RingHom.id_apply]

@[simp] theorem coefficientChange_apply (φ : R →+* A)
    (z : FreeModule (k:=R) (X:=X) K) (F : Face K) :
    coefficientChange K φ z F=MvPolynomial.map φ (z F) := rfl

@[simp] theorem coefficientChange_basis (φ : R →+* A) (F : Face K) :
    coefficientChange (X:=X) K φ (freeBasis (k:=R) (X:=X) K F)=freeBasis (k:=A) (X:=X) K F := by
  apply Finsupp.ext
  intro G
  simp only [coefficientChange_apply,freeBasis_apply,Finsupp.single_apply]
  split_ifs <;> simp

theorem coefficientChange_differential (φ : R →+* A) (z : FreeModule (k:=R) K) :
    coefficientChange K φ (differential K hK u z)=
      differential K hK u (coefficientChange K φ z) := by
  have he : (coefficientChange (X:=X) K φ).comp (differential K hK u)=
      (differential K hK u).comp (coefficientChange K φ) := by
    apply (freeBasis (k:=R) K).ext
    intro F
    simp only [LinearMap.comp_apply,differential_basis,map_sum,map_zsmul_unit,
      map_smulₛₗ,coefficientChange_basis,MvPolynomial.map_monomial,map_one]
  exact LinearMap.congr_fun he z

theorem coefficientChange_chain (φ : R →+* A) (i : ℕ)
    (z : FreeModule (k:=R) (X:=X) K) (hz : z∈chainPiece K i) :
    coefficientChange K φ z∈chainPiece (k:=A) K i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      rw [coefficientChange_basis]
      exact Submodule.subset_span ⟨F,hF,rfl⟩
  | zero => simpa only [map_zero] using (chainPiece (k:=A) (X:=X) K i).zero_mem
  | add z w hz hw ihz ihw =>
      simpa only [map_add] using Submodule.add_mem _ ihz ihw
  | smul p z hz ih =>
      simpa only [map_smulₛₗ] using Submodule.smul_mem _ (MvPolynomial.map φ p) ih

def termCoefficientChange (φ : R →+* A) (i : ℕ) :
    chainPiece (k:=R) (X:=X) K i →ₛₗ[(MvPolynomial.map φ : MvPolynomial X R →+* MvPolynomial X A)]
      chainPiece (k:=A) (X:=X) K i where
  toFun z := ⟨coefficientChange K φ z.val,coefficientChange_chain K φ i z.val z.property⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' p z := Subtype.ext (map_smulₛₗ _ _ _)

theorem coefficientChange_augmentation (φ : R →+* A)
    (z : FreeModule (k:=R) (X:=X) K) (hz : z∈chainPiece K 1) :
    MvPolynomial.map φ (augmentationPolynomial K u z)=
      augmentationPolynomial K u (coefficientChange K φ z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hcard,rfl⟩ := hz
      obtain ⟨v,hF⟩ := Finset.card_eq_one.mp hcard
      have hF' : F=⟨{v},hF ▸ F.property⟩ := Subtype.ext hF
      rw [hF',coefficientChange_basis,augmentationPolynomial_vertex,
        augmentationPolynomial_vertex,MvPolynomial.map_monomial,map_one]
  | zero => simp only [map_zero]
  | add z w hz hw ihz ihw => simp only [map_add,ihz,ihw]
  | smul p z hz ih => simp only [map_smulₛₗ,map_smul,smul_eq_mul,map_mul,ih,RingHom.id_apply]

section Tensor
variable [Algebra R A]

@[simp] theorem chainBasis_repr (i : ℕ)
    (z : chainPiece (k:=R) (X:=X) K i) (F : {F : Face K // F.val.card=i}) :
    (chainBasis (k:=R) (X:=X) K i).repr z F = z.val F.val :=
  restrictedBasis_repr (freeBasis (k:=R) (X:=X) K) (fun F => F.val.card=i) z F

def termBaseChange (i : ℕ) :
    (A ⊗[R] chainPiece (k:=R) (X:=X) K i) ≃ₗ[A] chainPiece (k:=A) (X:=X) K i :=
  (basisCoordinates (R:=R) (V:=X) (F:=↥(chainPiece (k:=R) (X:=X) K i)) A
    (chainBasis (k:=R) (X:=X) K i)).trans
    ((chainBasis (k:=A) (X:=X) K i).repr.symm.restrictScalars A)

theorem termBaseChange_tmul (i : ℕ) (a : A) (z : chainPiece (k:=R) (X:=X) K i) :
    termBaseChange (A:=A) K i (a ⊗ₜ[R] z)=
      a • termCoefficientChange K (algebraMap R A) i z := by
  apply (chainBasis (k:=A) (X:=X) K i).repr.injective
  apply Finsupp.ext
  intro F
  change ((chainBasis (k:=A) (X:=X) K i).repr
    ((chainBasis (k:=A) (X:=X) K i).repr.symm
      (basisCoordinates (R:=R) (V:=X) (F:=↥(chainPiece (k:=R) (X:=X) K i)) A
        (chainBasis (k:=R) (X:=X) K i) (a ⊗ₜ[R] z)))) F = _
  rw [LinearEquiv.apply_symm_apply, basisCoordinates_tmul_apply]
  rw [chainBasis_repr, chainBasis_repr]
  rfl

/-- The displayed tensor equivalence preserves the actual specialized
polynomial action; it is not merely an ungraded module equivalence. -/
def termRealization (i : ℕ) :
    Realization (R:=R) (V:=X) A (chainPiece (k:=R) (X:=X) K i)
      (chainPiece (k:=A) (X:=X) K i) where
  equivalence := termBaseChange K i
  multiply p z := by
    change (chainBasis (k:=A) (X:=X) K i).repr.symm
      (basisCoordinates (R:=R) (V:=X) (F:=↥(chainPiece (k:=R) (X:=X) K i)) A
    (chainBasis (k:=R) (X:=X) K i)
        ((sourceMultiply (chainPiece (k:=R) (X:=X) K i) p).baseChange A z))=_
    rw [basisCoordinates_source_multiply,map_smul]
    rfl

theorem termBaseChange_differential (i : ℕ)
    (z : A ⊗[R] chainPiece (k:=R) (X:=X) K (i+2)) :
    termBaseChange K (i+1)
      ((((resolutionData (k:=R) K hK u).differential i).restrictScalars R).baseChange A z)=
        (resolutionData (k:=A) K hK u).differential i
          (termBaseChange K (i+2) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z =>
      rw [LinearMap.baseChange_tmul,termBaseChange_tmul,termBaseChange_tmul]
      apply Subtype.ext
      change a • coefficientChange K (algebraMap R A)
        (differential (k:=R) K hK u z.val) =
          differential (k:=A) K hK u (a • coefficientChange K (algebraMap R A) z.val)
      rw [LinearMap.map_smul_of_tower,
        coefficientChange_differential K hK u (algebraMap R A) z.val]

/-- The polynomial-linear transported differential is exactly the
literal labelled differential over A. -/
theorem coefficientTransfer_differential (i : ℕ) :
    Realization.transfer A (termRealization K (i+2)) (termRealization K (i+1))
      ((resolutionData (k:=R) K hK u).differential i)=
        (resolutionData (k:=A) K hK u).differential i := by
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := (termBaseChange (R:=R) (A:=A) (X:=X) K (i+2)).surjective z
  change Realization.transfer A (termRealization K (i+2)) (termRealization K (i+1))
    ((resolutionData (k:=R) K hK u).differential i)
    ((termRealization (R:=R) (A:=A) (X:=X) K (i+2)).equivalence x) = _
  rw [Realization.transfer_equivalence A (termRealization K (i+2))
    (termRealization K (i+1)) ((resolutionData (k:=R) K hK u).differential i)]
  exact termBaseChange_differential K hK u i x

/-- The actual augmentation also specializes coefficientwise. Its image
is the literal monomial ideal, independently of any flatness hypothesis. -/
theorem termBaseChange_augmentation
    (z : A ⊗[R] chainPiece (k:=R) (X:=X) K 1) :
    MvPolynomial.algebraTensorAlgEquiv R A
      (LinearMap.baseChange A
        (((augmentationPolynomial (k:=R) K u).domRestrict
          (chainPiece (k:=R) (X:=X) K 1)).restrictScalars R) z)=
      augmentationPolynomial K u (termBaseChange K 1 z).val := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,Submodule.coe_add,hx,hy]
  | tmul a z =>
      rw [LinearMap.baseChange_tmul,MvPolynomial.algebraTensorAlgEquiv_tmul,
        termBaseChange_tmul]
      change a • MvPolynomial.map (algebraMap R A)
        (augmentationPolynomial (k:=R) K u z.val) =
          augmentationPolynomial (k:=A) K u
            (a • coefficientChange K (algebraMap R A) z.val)
      rw [LinearMap.map_smul_of_tower,
        coefficientChange_augmentation K u (algebraMap R A) z.val z.property]

end Tensor
end FourPapers.LabelledSimplicial

end
end
end


end
