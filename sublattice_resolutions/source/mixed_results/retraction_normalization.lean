module
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RetractionNormalization -/
section

/-! # Strong normalization preserving a given projection and inclusion

For a deformation retract onto a zero differential, first replace the
homotopy by `(1-ip) h (1-ip)`, then by `h d h`. All identities hold over
an arbitrary coefficient ring. The actual projection and inclusion are
unchanged, which is useful when the projection is an algebra homomorphism.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.HomologicalPerturbation

section Ring
variable {A : Type*} [Ring A]

def normalizedHomotopy (d h p : A) : A :=
  ((1-p)*h*(1-p))*d*((1-p)*h*(1-p))

theorem normalizedHomotopy_contraction (d h p : A)
    (hdd : d*d=0) (hpp : p*p=p) (hdp : d*p=0) (hpd : p*d=0)
    (hdh : d*h+h*d=1-p) : Contraction d (normalizedHomotopy d h p) p := by
  let q := 1-p
  let t := q*h*q
  have hqq : q*q=q := by
    calc
      q*q = 1-p-p+p*p := by dsimp [q]; noncomm_ring
      _ = q := by rw [hpp]; dsimp [q]; abel
  have hqp : q*p=0 := by dsimp [q]; rw [sub_mul,one_mul,hpp,sub_self]
  have hpq : p*q=0 := by dsimp [q]; rw [mul_sub,mul_one,hpp,sub_self]
  have hdq : d*q=d := by dsimp [q]; rw [mul_sub,mul_one,hdp,sub_zero]
  have hqd : q*d=d := by dsimp [q]; rw [sub_mul,one_mul,hpd,sub_zero]
  have hqt : q*t=t := by dsimp [t]; rw [← mul_assoc,← mul_assoc,hqq]
  have htp : t*p=0 := by dsimp [t]; rw [mul_assoc, hqp, mul_zero]
  have hpt : p*t=0 := by dsimp [t]; rw [← mul_assoc,← mul_assoc,hpq,zero_mul,zero_mul]
  have hdt : d*t+t*d=q := by
    calc
      _ = (d*q)*h*q+q*h*(q*d) := by dsimp [t]; noncomm_ring
      _ = d*h*q+q*h*d := by rw [hdq,hqd]
      _ = (q*d)*h*q+q*h*(d*q) := by rw [hqd,hdq]
      _ = q*(d*h+h*d)*q := by noncomm_ring
      _ = q*q*q := by rw [hdh]
      _ = q := by rw [hqq,hqq]
  have hdtd : d*t*d=d := by
    calc
      _ = (d*t+t*d)*d := by rw [add_mul,mul_assoc t d d,hdd,mul_zero,add_zero]
      _ = q*d := by rw [hdt]
      _ = d := hqd
  have hzero : d*t*t*d=0 := by
    have hh : d*t*t*d+t*d=t*d := by
      calc
        _ = d*t*t*d+t*(d*t*d) := by rw [hdtd]
        _ = (d*t+t*d)*t*d := by noncomm_ring
        _ = q*t*d := by rw [hdt]
        _ = t*d := by rw [hqt]
    exact add_eq_right.mp hh
  refine ⟨hdd,hpp,hdp,hpd,?_,?_,?_,?_⟩
  · change d*(t*d*t)+(t*d*t)*d=1-p
    calc
      _ = (d*t*d)*t+t*(d*t*d) := by noncomm_ring
      _ = d*t+t*d := by rw [hdtd]
      _ = 1-p := hdt
  · change (t*d*t)*(t*d*t)=0
    calc
      _ = t*(d*t*t*d)*t := by noncomm_ring
      _ = 0 := by rw [hzero,mul_zero,zero_mul]
  · change (t*d*t)*p=0
    rw [mul_assoc,htp,mul_zero]
  · change p*(t*d*t)=0
    calc
      _ = (p*t)*d*t := by noncomm_ring
      _ = 0 := by rw [hpt,zero_mul,zero_mul]

end Ring

namespace LinearDeformationRetract
variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearDeformationRetract (R := R) (M := M) (H := H))
  (hzero : C.targetD=0)

include hzero in
theorem inclusion_cycle : C.sourceD.comp C.inclusion=0 := by
  rw [C.inclusion_chain,hzero,LinearMap.comp_zero]

include hzero in
theorem projection_boundary : C.projection.comp C.sourceD=0 := by
  rw [C.projection_chain,hzero,LinearMap.zero_comp]

def normalizedRingContraction : Contraction C.sourceD
    (normalizedHomotopy C.sourceD C.homotopy (C.inclusion.comp C.projection))
    (C.inclusion.comp C.projection) := by
  apply normalizedHomotopy_contraction _ _ _ C.source_square
  · apply LinearMap.ext
    intro x
    change C.inclusion (C.projection (C.inclusion (C.projection x))) =
      C.inclusion (C.projection x)
    rw [C.projection_inclusion]
  · apply LinearMap.ext
    intro x
    change C.sourceD (C.inclusion (C.projection x))=0
    exact LinearMap.congr_fun (C.inclusion_cycle hzero) (C.projection x)
  · apply LinearMap.ext
    intro x
    change C.inclusion (C.projection (C.sourceD x))=0
    have hh := LinearMap.congr_fun (C.projection_boundary hzero) x
    change C.projection (C.sourceD x)=0 at hh
    rw [hh,map_zero]
  · exact C.deformation

/-- Normalize the homotopy while retaining the exact given maps. -/
def normalizeZeroTarget : LinearContraction (R := R) (M := M) (H := H) where
  d := C.sourceD
  h := normalizedHomotopy C.sourceD C.homotopy (C.inclusion.comp C.projection)
  inclusion := C.inclusion
  projection := C.projection
  differential := C.source_square
  retract := C.retract
  inclusion_cycle := C.inclusion_cycle hzero
  projection_boundary := C.projection_boundary hzero
  homotopy := (C.normalizedRingContraction hzero).homotopy
  squareHomotopy := (C.normalizedRingContraction hzero).squareHomotopy
  homotopyInclusion := by
    apply LinearMap.ext
    intro x
    change normalizedHomotopy C.sourceD C.homotopy (C.inclusion.comp C.projection)
      (C.inclusion x)=0
    have hh := LinearMap.congr_fun
      (C.normalizedRingContraction hzero).homotopyProjection (C.inclusion x)
    change normalizedHomotopy C.sourceD C.homotopy (C.inclusion.comp C.projection)
      (C.inclusion (C.projection (C.inclusion x)))=0 at hh
    simpa only [C.projection_inclusion] using hh
  projectionHomotopy := by
    apply LinearMap.ext
    intro x
    change C.projection
      (normalizedHomotopy C.sourceD C.homotopy (C.inclusion.comp C.projection) x)=0
    apply C.inclusion_injective
    rw [map_zero]
    exact LinearMap.congr_fun (C.normalizedRingContraction hzero).projectionHomotopy x

@[simp] theorem normalizeZeroTarget_projection :
    (C.normalizeZeroTarget hzero).projection=C.projection := rfl

@[simp] theorem normalizeZeroTarget_inclusion :
    (C.normalizeZeroTarget hzero).inclusion=C.inclusion := rfl

end LinearDeformationRetract
end FourPapers.HomologicalPerturbation

end
end
end


end
