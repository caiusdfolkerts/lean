module

public import PaperVerification.TensorMultiplicityFunctor
public import Mathlib.RepresentationTheory.Invariants

/-!
# The literal averaging projection onto tensor multiplicities

Multiplicity spaces are images of a concrete idempotent on a genuine
linear-map module.  The idempotent averages the simultaneous conjugation
action of the finite symmetric group.  This construction works whenever
the group order is invertible in the coefficient ring and does not
assume a lower bound on the rank of the original module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace PaperVerification.TensorMultiplicity

universe u v w

variable {R : Type u} [CommRing R] {d : ℕ}
variable {W : Type w} [AddCommGroup W] [Module R W]
  (ρ : Representation R (Equiv.Perm (Fin d)) W)
variable (M : Type v) [AddCommGroup M] [Module R M]
variable [Invertible (Fintype.card (Equiv.Perm (Fin d)) : R)]

/-- The explicit finite average on `Hom(W, M^⊗d)`. -/
def projector : Module.End R (W →ₗ[R] TensorPower R d M) :=
  (Representation.linHom ρ
    (PiTensorProduct.reindexRepresentation R M (Fin d))).averageMap

theorem projector_idempotent : IsIdempotentElem (projector ρ M) :=
  (Representation.isProj_averageMap _).isIdempotentElem

theorem projector_range : LinearMap.range (projector ρ M) =
    (Representation.linHom ρ
      (PiTensorProduct.reindexRepresentation R M (Fin d))).invariants :=
  (Representation.isProj_averageMap _).range

/-- The image of the actual averaging idempotent is canonically the
space of equivariant linear maps defining the multiplicity functor. -/
def projectorRangeEquiv : LinearMap.range (projector ρ M) ≃ₗ[R] Space ρ M :=
  (LinearEquiv.ofEq _ _ (projector_range ρ M)).trans
    (Representation.invariantsEquivIntertwiningMap ρ
      (PiTensorProduct.reindexRepresentation R M (Fin d)))

/-- The averaging retraction onto the actual multiplicity space. -/
def retraction : (W →ₗ[R] TensorPower R d M) →ₗ[R] Space ρ M :=
  (projectorRangeEquiv ρ M).toLinearMap.comp (projector ρ M).rangeRestrict

/-- The underlying linear map is recovered by the canonical inclusion. -/
def inclusion : Space ρ M →ₗ[R] (W →ₗ[R] TensorPower R d M) where
  toFun s := s.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Invertible (Fintype.card (Equiv.Perm (Fin d)) : R)] in
@[simp] theorem inclusion_apply (s : Space ρ M) :
    inclusion ρ M s = s.toLinearMap := rfl

omit [Invertible (Fintype.card (Equiv.Perm (Fin d)) : R)] in
theorem inclusion_injective : Function.Injective (inclusion ρ M) :=
  Representation.IntertwiningMap.toLinearMap_injective _ _

/-- Averaging fixes every actual equivariant map. -/
theorem projector_inclusion (s : Space ρ M) :
    projector ρ M (inclusion ρ M s) = inclusion ρ M s :=
  Representation.averageMap_id _ _
    ((Representation.invariantsEquivIntertwiningMap ρ
      (PiTensorProduct.reindexRepresentation R M (Fin d))).symm s).property

@[simp] theorem inclusion_retraction (f : W →ₗ[R] TensorPower R d M) :
    inclusion ρ M (retraction ρ M f) = projector ρ M f := rfl

@[simp] theorem retraction_inclusion (s : Space ρ M) :
    retraction ρ M (inclusion ρ M s) = s := by
  apply inclusion_injective ρ M
  rw [inclusion_retraction, projector_inclusion]

/-- The multiplicity space is an actual direct summand, exhibited by
linear inclusion and retraction rather than by an assumed decomposition. -/
theorem retraction_comp_inclusion :
    (retraction ρ M).comp (inclusion ρ M) = LinearMap.id := by
  apply LinearMap.ext
  intro s
  exact retraction_inclusion ρ M s

end PaperVerification.TensorMultiplicity
