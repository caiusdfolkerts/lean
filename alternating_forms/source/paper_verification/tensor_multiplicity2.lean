module

public import paper_verification.literal006
import all paper_verification.literal006
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RepresentationTheory.Invariants
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.TensorMultiplicityFunctor -/


/-!
# Tensor multiplicity spaces as functors on all linear maps

The symmetric group acts on an actual tensor power by
`σ (⊗ᵢ vᵢ) = ⊗ᵢ v_(σ⁻¹ i)`.  Applying the same linear map in every
factor intertwines this action.  Consequently the multiplicity space of
any fixed symmetric-group representation is functorial in the original
module, including maps between modules of different ranks.

Specializing the fixed representation to a Specht representation gives
the Schur multiplicity functor.  None of the results below assumes a
stable range, a dimension inequality, or invertibility of the input map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace PaperVerification.TensorMultiplicity

universe u v v₁ v₂ w

variable {R : Type u} [CommRing R] {d : ℕ}
variable {M : Type v} {N : Type v₁} {P : Type v₂} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map applied in every tensor factor, as an actual
intertwiner of the permutation actions. -/
def tensorMap (f : M →ₗ[R] N) :
    Representation.IntertwiningMap
      (PiTensorProduct.reindexRepresentation R M (Fin d))
      (PiTensorProduct.reindexRepresentation R N (Fin d)) where
  toLinearMap := PiTensorProduct.map fun _ : Fin d ↦ f
  isIntertwining' σ := by
    simp only [PiTensorProduct.reindexRepresentation_apply]
    exact PiTensorProduct.map_comp_reindex_eq (fun _ : Fin d ↦ f) σ

@[simp] theorem tensorMap_apply (f : M →ₗ[R] N) (v : TensorPower R d M) :
    tensorMap (d := d) f v = PiTensorProduct.map (fun _ : Fin d ↦ f) v := rfl

@[simp] theorem tensorMap_tprod (f : M →ₗ[R] N) (v : Fin d → M) :
    tensorMap (d := d) f (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i ↦ f (v i)) :=
  PiTensorProduct.map_tprod (fun _ : Fin d ↦ f) v

@[simp] theorem tensorMap_id_apply (v : TensorPower R d M) :
    tensorMap (d := d) (LinearMap.id : M →ₗ[R] M) v = v := by
  simp only [tensorMap_apply, PiTensorProduct.map_id, LinearMap.id_apply]

@[simp] theorem tensorMap_comp_apply (g : N →ₗ[R] P) (f : M →ₗ[R] N)
    (v : TensorPower R d M) :
    tensorMap (d := d) (g.comp f) v = tensorMap g (tensorMap f v) := by
  exact congrArg (fun h : TensorPower R d M →ₗ[R] TensorPower R d P ↦ h v)
    (PiTensorProduct.map_comp (fun _ : Fin d ↦ g) (fun _ : Fin d ↦ f))

variable {W : Type w} [AddCommGroup W] [Module R W]
  (ρ : Representation R (Equiv.Perm (Fin d)) W)

/-- The literal equivariant-linear-map multiplicity space. -/
abbrev Space (M : Type v) [AddCommGroup M] [Module R M] :=
  Representation.IntertwiningMap ρ
    (PiTensorProduct.reindexRepresentation R M (Fin d))

/-- Functoriality on every linear map, by postcomposition with its
tensor power. -/
def map (f : M →ₗ[R] N) : Space ρ M →ₗ[R] Space ρ N :=
  Representation.IntertwiningMap.llcomp ρ _ _ (tensorMap f)

@[simp] theorem map_apply (f : M →ₗ[R] N) (s : Space ρ M) (w : W) :
    map ρ f s w = tensorMap f (s w) := rfl

@[simp] theorem map_id : map ρ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext s w
  exact tensorMap_id_apply (s w)

@[simp] theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map ρ (g.comp f) = (map ρ g).comp (map ρ f) := by
  ext s w
  exact tensorMap_comp_apply g f (s w)

/-- Change of frame on the multiplicity space is an actual linear
equivalence; its inverse comes from the inverse frame. -/
def congr (e : M ≃ₗ[R] N) : Space ρ M ≃ₗ[R] Space ρ N :=
  LinearEquiv.ofLinearMap (map ρ e.toLinearMap) (map ρ e.symm.toLinearMap)
    (by rw [← map_comp, e.comp_symm, map_id])
    (by rw [← map_comp, e.symm_comp, map_id])

@[simp] theorem congr_apply (e : M ≃ₗ[R] N) (s : Space ρ M) :
    congr ρ e s = map ρ e.toLinearMap s := rfl

/-- The multiplicity construction is a functor on the actual category
of modules.  It is polynomial in morphisms, so no additivity of this
functor is asserted. -/
def functor : ModuleCat.{v} R ⥤ ModuleCat.{max v w u} R where
  obj M := ModuleCat.of R (Space ρ M)
  map f := ModuleCat.ofHom (map ρ f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact map_id ρ
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact map_comp ρ g.hom f.hom

end PaperVerification.TensorMultiplicity
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TensorMultiplicityFunctor"

section ComponentSource_1
/- Original module: PaperVerification.TensorMultiplicityProjection -/


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
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TensorMultiplicityProjection"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.TensorMultiplicity.tensorMap, "definition"),
    (`PaperVerification.TensorMultiplicity.Space, "definition"),
    (`PaperVerification.TensorMultiplicity.map, "definition"),
    (`PaperVerification.TensorMultiplicity.map_id, "theorem"),
    (`PaperVerification.TensorMultiplicity.map_comp, "theorem"),
    (`PaperVerification.TensorMultiplicity.congr, "definition"),
    (`PaperVerification.TensorMultiplicity.functor, "definition"),
    (`PaperVerification.TensorMultiplicity.projector, "definition"),
    (`PaperVerification.TensorMultiplicity.projector_idempotent, "theorem"),
    (`PaperVerification.TensorMultiplicity.projector_range, "theorem"),
    (`PaperVerification.TensorMultiplicity.projectorRangeEquiv, "definition"),
    (`PaperVerification.TensorMultiplicity.retraction_comp_inclusion, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "190c0e54c8973a8a2c4ba7de249ab5d8"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:190c0e54c8973a8a2c4ba7de249ab5d8"
