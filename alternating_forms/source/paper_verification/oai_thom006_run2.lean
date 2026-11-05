module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import all Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.RankNullity
import all Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
import all Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Isomorphisms
import all Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
import all Mathlib.LinearAlgebra.Prod
public import paper_verification.oai_thom005_run1
import all paper_verification.oai_thom005_run1
public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
import all Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Topology.Algebra.Module.Equiv
import all Mathlib.Topology.Algebra.Module.Equiv
public import paper_verification.oai_thom003_run1
import all paper_verification.oai_thom003_run1
public import paper_verification.oai_thom004_run1
import all paper_verification.oai_thom004_run1
public import paper_verification.oai_thom001_run1
import all paper_verification.oai_thom001_run1
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import all Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import all Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import all Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Congr
import all Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import all Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import all Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import all Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
public import Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheafify
import all Mathlib.Topology.Sheaves.Sheafify
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq -/

/-! # Complex Normal Eq -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq.Cycles

/-!
# Linear normal spaces of complex coordinate submanifolds

These are concrete local linear models for normal directions to a smooth
complex submanifold. The normal space is the actual quotient of the ambient
complex vector space by its tangent subspace. No cycle class or Thom class is
postulated here.
-/

variable {V W U : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup U] [Module ℂ U]

/-- The complex linear normal space to a complex subspace. -/
abbrev ComplexNormal (S : Submodule ℂ V) := V ⧸ S

/-- Normal vectors are ambient vectors modulo the tangent subspace. -/
abbrev normalProjection (S : Submodule ℂ V) : V →ₗ[ℂ] ComplexNormal S := S.mkQ

@[simp]
theorem normalProjection_eq_zero (S : Submodule ℂ V) (v : V) :
    normalProjection S v = 0 ↔ v ∈ S := by
  exact Submodule.Quotient.mk_eq_zero S

/-- An ambient complex coordinate change carrying tangent spaces to tangent
spaces induces a complex linear change of normal coordinates. -/
def complexNormalEquiv (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) :
    ComplexNormal S ≃ₗ[ℂ] ComplexNormal T :=
  Submodule.Quotient.equiv S T e he

@[simp]
theorem complexNormalEquiv_projection (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) (v : V) :
    complexNormalEquiv S T e he (normalProjection S v) = normalProjection T (e v) := by
  rfl

theorem complexNormalEquiv_trans (S : Submodule ℂ V) (T : Submodule ℂ W)
    (R : Submodule ℂ U) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] U)
    (he : S.map e.toLinearMap = T) (hf : T.map f.toLinearMap = R)
    (hef : S.map (e.trans f).toLinearMap = R) :
    complexNormalEquiv S R (e.trans f) hef =
      (complexNormalEquiv S T e he).trans (complexNormalEquiv T R f hf) := by
  exact Submodule.Quotient.equiv_trans S T R e f he hf hef

/-- The real linear normal quotient agrees with restriction of scalars of the
complex normal quotient. -/
noncomputable def realNormalEquiv (S : Submodule ℂ V) :
    (V ⧸ S.restrictScalars ℝ) ≃ₗ[ℝ] ComplexNormal S :=
  Submodule.Quotient.restrictScalarsEquiv ℝ S

@[simp]
theorem realNormalEquiv_projection (S : Submodule ℂ V) (v : V) :
    realNormalEquiv S ((S.restrictScalars ℝ).mkQ v) = normalProjection S v := by
  rfl

theorem complexNormal_finrank [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Module.finrank ℂ (ComplexNormal S) = Module.finrank ℂ V - Module.finrank ℂ S := by
  exact S.finrank_quotient

/-- A complex normal space of dimension `p` has real dimension `2 * p`. -/
theorem complexNormal_real_finrank (S : Submodule ℂ V) :
    Module.finrank ℝ (ComplexNormal S) = 2 * Module.finrank ℂ (ComplexNormal S) := by
  exact finrank_real_of_complex (ComplexNormal S)

theorem realNormal_finrank [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Module.finrank ℝ (V ⧸ S.restrictScalars ℝ) =
      2 * (Module.finrank ℂ V - Module.finrank ℂ S) := by
  rw [(realNormalEquiv S).finrank_eq, complexNormal_real_finrank, complexNormal_finrank]

theorem complexNormal_finrank_invariant (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) :
    Module.finrank ℂ (ComplexNormal S) = Module.finrank ℂ (ComplexNormal T) :=
  (complexNormalEquiv S T e he).finrank_eq

/-- A complex coordinate change preserving the tangent space induces a
positive real determinant on the normal space. -/
theorem complexNormalEquiv_realDet_pos (S : Submodule ℂ V)
    (e : V ≃ₗ[ℂ] V) (he : S.map e.toLinearMap = S) :
    0 < LinearMap.det (((complexNormalEquiv S S e he).restrictScalars ℝ).toLinearMap) := by
  exact ComplexOrientation.complexLinearEquiv_realDet_pos (complexNormalEquiv S S e he)

/-- The canonical complex orientation of the normal quotient, expressed using
its finite complex basis. Independence of that basis is proved below. -/
noncomputable def complexNormalOrientation [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Orientation ℝ (ComplexNormal S)
      (Fin (Module.finrank ℂ (ComplexNormal S)) × Fin 2) :=
  ComplexOrientation.complexOrientationOfBasis (Module.finBasis ℂ (ComplexNormal S))

theorem complexNormalOrientation_eq_basis [FiniteDimensional ℂ V] (S : Submodule ℂ V)
    (b : Module.Basis (Fin (Module.finrank ℂ (ComplexNormal S))) ℂ (ComplexNormal S)) :
    complexNormalOrientation S = ComplexOrientation.complexOrientationOfBasis b := by
  exact ComplexOrientation.complexOrientationOfBasis_eq (Module.finBasis ℂ (ComplexNormal S)) b

/-- The quotient orientation is preserved by every ambient complex linear
coordinate change preserving the tangent subspace. -/
theorem complexNormalEquiv_preserves_orientation [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (e : V ≃ₗ[ℂ] V) (he : S.map e.toLinearMap = S) :
    Orientation.map (Fin (Module.finrank ℂ (ComplexNormal S)) × Fin 2)
      ((complexNormalEquiv S S e he).restrictScalars ℝ) (complexNormalOrientation S) =
      complexNormalOrientation S := by
  exact ComplexOrientation.complexLinearEquiv_preserves_realBasis_orientation
    (ComplexOrientation.complexRealBasis (Module.finBasis ℂ (ComplexNormal S))) (complexNormalEquiv S S e he)

/-- In local product coordinates, the coordinate submanifold has zero normal
coordinate. -/
def coordinateTangent (n p : ℕ) :
    Submodule ℂ ((Fin n → ℂ) × (Fin p → ℂ)) :=
  LinearMap.ker (LinearMap.snd ℂ (Fin n → ℂ) (Fin p → ℂ))

@[simp]
theorem mem_coordinateTangent (n p : ℕ) (x : (Fin n → ℂ) × (Fin p → ℂ)) :
    x ∈ coordinateTangent n p ↔ x.2 = 0 := by
  rfl

/-- The quotient normal space to a coordinate `n`-plane in `ℂⁿ × ℂᵖ`
is precisely the displayed `ℂᵖ` factor. -/
noncomputable def coordinateNormalEquiv (n p : ℕ) :
    ComplexNormal (coordinateTangent n p) ≃ₗ[ℂ] (Fin p → ℂ) :=
  (LinearMap.snd ℂ (Fin n → ℂ) (Fin p → ℂ)).quotKerEquivOfSurjective
    (fun y => ⟨(0, y), rfl⟩)

@[simp]
theorem coordinateNormalEquiv_projection (n p : ℕ)
    (x : (Fin n → ℂ) × (Fin p → ℂ)) :
    coordinateNormalEquiv n p (normalProjection (coordinateTangent n p) x) = x.2 := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

@[simp]
theorem coordinateNormal_complex_finrank (n p : ℕ) :
    Module.finrank ℂ (ComplexNormal (coordinateTangent n p)) = p := by
  rw [(coordinateNormalEquiv n p).finrank_eq]
  simp

@[simp]
theorem coordinateNormal_real_finrank (n p : ℕ) :
    Module.finrank ℝ (ComplexNormal (coordinateTangent n p)) = 2 * p := by
  rw [complexNormal_real_finrank, coordinateNormal_complex_finrank]

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq.Cycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock -/

/-! # Complex Normal Block -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock.Cycles

noncomputable section

/-!
# The normal block of a tangent-preserving complex linear equivalence

If an ambient continuous linear equivalence and its inverse preserve the
horizontal subspace, its second coordinate descends to a continuous linear
equivalence of the normal factors. No finite-dimensionality or completeness
assumption is needed. The resulting map agrees with the existing construction
of the induced map on the actual quotient by the tangent subspace.
-/

universe uE uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The bottom-right continuous linear block of an ambient equivalence. -/
def normalBlockMap (L : (E × F) ≃L[ℂ] (E × F)) : F →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp
    (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E F))

@[simp]
theorem normalBlockMap_apply (L : (E × F) ≃L[ℂ] (E × F)) (y : F) :
    normalBlockMap L y = (L (0, y)).2 :=
  rfl

/-- Preservation of the horizontal subspace makes the second coordinate
depend only on the normal coordinate. -/
theorem normalBlockMap_projection (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (z : E × F) :
    (L z).2 = normalBlockMap L z.2 := by
  have h := congrArg Prod.snd
    (ContinuousLinearMap.comp_inl_add_comp_inr L.toContinuousLinearMap z)
  change (L (z.1, 0)).2 + (L (0, z.2)).2 = (L z).2 at h
  rw [hL z.1, zero_add] at h
  exact h.symm

/-- The normal block is invertible because the ambient equivalence and its
inverse both preserve the horizontal subspace. Its inverse is the normal
block of the ambient inverse. -/
def normalBlock (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) : F ≃L[ℂ] F where
  toFun := normalBlockMap L
  invFun := normalBlockMap L.symm
  left_inv y := by
    change normalBlockMap L.symm (L (0, y)).2 = y
    rw [← normalBlockMap_projection L.symm hLi (L (0, y))]
    exact congrArg Prod.snd (L.symm_apply_apply (0, y))
  right_inv y := by
    change normalBlockMap L (L.symm (0, y)).2 = y
    rw [← normalBlockMap_projection L hL (L.symm (0, y))]
    exact congrArg Prod.snd (L.apply_symm_apply (0, y))
  map_add' := (normalBlockMap L).map_add
  map_smul' := (normalBlockMap L).map_smul
  continuous_toFun := (normalBlockMap L).continuous
  continuous_invFun := (normalBlockMap L.symm).continuous

@[simp]
theorem normalBlock_apply (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (y : F) :
    normalBlock L hL hLi y = (L (0, y)).2 :=
  rfl

@[simp]
theorem normalBlock_symm_apply (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (y : F) :
    (normalBlock L hL hLi).symm y = (L.symm (0, y)).2 :=
  rfl

@[simp]
theorem normalBlock_toContinuousLinearMap (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).toContinuousLinearMap =
      (ContinuousLinearMap.snd ℂ E F).comp
        (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E F)) :=
  rfl

theorem normalBlock_projection (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (z : E × F) :
    (L z).2 = normalBlock L hL hLi z.2 :=
  normalBlockMap_projection L hL z

/-- The second projection intertwines the ambient and normal equivalences. -/
theorem normalBlock_comp_snd (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ E F) =
      (ContinuousLinearMap.snd ℂ E F).comp L.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  exact (normalBlock_projection L hL hLi z).symm

@[simp]
theorem normalBlock_symm (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).symm = normalBlock L.symm hLi hL := by
  ext y
  rfl

/-- The two preservation hypotheses give exactly the submodule equality
required by the existing induced normal-quotient equivalence. -/
theorem normalBlock_tangent_map (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (LinearMap.ker (LinearMap.snd ℂ E F)).map L.toLinearEquiv.toLinearMap =
      LinearMap.ker (LinearMap.snd ℂ E F) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (L w).2 = 0
    rw [normalBlockMap_projection L hL w]
    change w.2 = 0 at hw
    rw [hw, map_zero]
  · intro hz
    refine ⟨L.symm z, ?_, L.apply_symm_apply z⟩
    change (L.symm z).2 = 0
    rw [normalBlockMap_projection L.symm hLi z]
    change z.2 = 0 at hz
    rw [hz, map_zero]

/-- Under the native quotient identification with the normal factor, the
existing induced quotient equivalence is exactly the normal block. -/
theorem normalBlock_quotient (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (z : ComplexNormalEq.Cycles.ComplexNormal (LinearMap.ker (LinearMap.snd ℂ E F))) :
    let e := (LinearMap.snd ℂ E F).quotKerEquivOfSurjective
      (fun y => ⟨(0, y), rfl⟩)
    e (ComplexNormalEq.Cycles.complexNormalEquiv _ _ L.toLinearEquiv (normalBlock_tangent_map L hL hLi) z) =
      normalBlock L hL hLi (e z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z => exact normalBlock_projection L hL hLi z

/-- The generic quotient comparison specializes to the existing displayed
coordinate-normal equivalence without changing its definition. -/
theorem normalBlock_coordinateNormalEquiv (n p : ℕ)
    (L : ((Fin n → ℂ) × (Fin p → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin p → ℂ)))
    (hL : ∀ x : Fin n → ℂ, (L (x, 0)).2 = 0)
    (hLi : ∀ x : Fin n → ℂ, (L.symm (x, 0)).2 = 0)
    (z : ComplexNormalEq.Cycles.ComplexNormal (ComplexNormalEq.Cycles.coordinateTangent n p)) :
    ComplexNormalEq.Cycles.coordinateNormalEquiv n p
        (ComplexNormalEq.Cycles.complexNormalEquiv _ _ L.toLinearEquiv (normalBlock_tangent_map L hL hLi) z) =
      normalBlock L hL hLi (ComplexNormalEq.Cycles.coordinateNormalEquiv n p z) :=
  normalBlock_quotient L hL hLi z

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock.Cycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction -/

/-! # Normal Slice Local Action -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction.Cycles

noncomputable section

/-!
# Normal slices and actual local normal-class actions

The relative action of a genuine map of product pairs becomes the action of
its normal slice after the actual projection and section equivalences. On
small product neighborhoods this reduces nonlinear coordinate invariance to
the proved comparison of a differentiable germ with its derivative.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open scoped _root_.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeMap_congr {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    {u v : X ⟶ Y} (h : u = v) (hu : Set.MapsTo u A B) (hv : Set.MapsTo v A B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap u hu n = LocalHomology.Cycles.relativeSingularHomologyMap v hv n := by
  subst v
  rfl

section ProductSlice

variable {E F E' F' : Type} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace E'] [TopologicalSpace F']

/-- Restrict a product map to a tangential section and project its normal
coordinate. This is the actual continuous normal slice. -/
def normalSliceMap (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F')) (e : E) :
    TopCat.of F ⟶ TopCat.of F' :=
  NormalProductPair.Cycles.normalProductSection E F e ≫ φ ≫ NormalProductPair.Cycles.normalProductProjection E' F'

@[simp]
theorem normalSliceMap_apply (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (y : F) : normalSliceMap φ e y = (φ (e, y)).2 := rfl

theorem normalSliceMap_mapsTo (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z')) :
    Set.MapsTo (normalSliceMap φ e) ({z}ᶜ : Set F) ({z'}ᶜ : Set F') :=
  fun _ hy => hφ hy

/-- The product-to-slice identity already holds for the genuine relative
chain maps, before passing to homology. -/
theorem normalSlice_relativeChains (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z')) :
    NormalProductPair.Cycles.normalProductRelativeSection E F e z ≫ LocalHomology.Cycles.relativeSingularChainsMap φ hφ ≫
        NormalProductPair.Cycles.normalProductRelativeProjection E' F' z' =
      LocalHomology.Cycles.relativeSingularChainsMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) := by
  simp only [NormalProductPair.Cycles.normalProductRelativeSection, NormalProductPair.Cycles.normalProductRelativeProjection,
    LocalHomology.Cycles.relativeSingularChainsMap_comp]
  rfl

/-- The exact normal-slice action on genuine relative singular homology. -/
theorem normalSlice_relativeHomology (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) n ≫
      LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (NormalProductPair.Cycles.normalProductProjection E' F')
          (NormalProductPair.Cycles.normalProductProjection_mapsTo E' F' z') n =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) n := by
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp, LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  rfl

/-- Conjugating by the actual product equivalences gives precisely the
normal slice, for any displayed genuine tangential contractions. -/
theorem normalProductHomology_conjugate_of_contractions
    (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (e' : E') (z : F) (z' : F')
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (H' : ContinuousMap.Homotopy (ContinuousMap.const E' e') (ContinuousMap.id E'))
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction E F e z H n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
          (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction E' F' e' z' H' n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) n :=
  normalSlice_relativeHomology φ e z z' hφ n

end ProductSlice

section LinearSlice

variable {E E' F F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace F] [TopologicalSpace F']

/-- In linear tangential coordinates the conjugate map is literally
`y ↦ snd (φ (0,y))`, with no linearity condition on the product map. -/
theorem normalProductHomology_conjugate
    (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F')) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    (NormalProductPair.Cycles.normalProductHomologyIso E F z n).inv ≫ LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
        (NormalProductPair.Cycles.normalProductHomologyIso E' F' z' n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ 0) (normalSliceMap_mapsTo φ 0 z z' hφ) n :=
  normalSlice_relativeHomology φ 0 z z' hφ n

end LinearSlice

section BallSlice

variable {E E' F F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [TopologicalSpace F']

/-- For a product of two genuine open balls, normal excision is the only
additional factor in the same exact conjugacy identity. -/
theorem normalOpenProductBallsHomology_conjugate
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶
      TopCat.of (E' × F')) (z' : F')
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E' F' z')) (n : ℕ) :
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E F r s hr hs n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫ (NormalProductPair.Cycles.normalProductHomologyIso E' F' z' n).hom =
      (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of F) (Metric.ball 0 s) 0
        (Metric.mem_ball_self hs) Metric.isOpen_ball n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ (LocalDerivativeHomology.Cycles.ballZero E r hr))
          (normalSliceMap_mapsTo φ (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs) z' hφ) n := by
  change ((LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of F) (Metric.ball 0 s) 0
      (Metric.mem_ball_self hs) Metric.isOpen_ball n).inv ≫
        (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs)
          (NormalProductPair.Cycles.normalConvexContraction E (Metric.ball 0 r) (convex_ball 0 r)
            (Metric.mem_ball_self hr)) n).inv) ≫ _ ≫ _ = _
  rw [Category.assoc]
  congr 1
  exact normalSlice_relativeHomology φ (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs) z' hφ n

end BallSlice

/-- The explicit complex-matrix homotopy of product pairs also proves
complex-linear invariance in all degrees, including dimension zero. -/
theorem complexLinearLocalHomologyMap_eq_id_all {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) :
    LocalDerivativeHomology.Cycles.linearLocalHomologyMap (L.restrictScalars ℝ) n = 𝟙 _ := by
  let A := LinearMap.toMatrix' L.toLinearEquiv.toLinearMap
  have hA : IsUnit A :=
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)
  have h := normalProductHomology_conjugate
    (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 0 (NormalProductPair.Cycles.normalProductComplexChange_mapsTo ℝ A hA) n
  rw [NormalProductPair.Cycles.normalProductComplexChange_homology_eq_id ℝ A hA n, Category.id_comp,
    Iso.inv_hom_id] at h
  have hs : normalSliceMap (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 =
      LocalDerivativeHomology.Cycles.linearNormalMap (L.restrictScalars ℝ) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x
  exact (relativeMap_congr hs
    (normalSliceMap_mapsTo (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 0 0
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo ℝ A hA))
    (LocalDerivativeHomology.Cycles.linearNormalMap_preservesPuncture (L.restrictScalars ℝ)) n).symm.trans h.symm

section BallMaps

variable {E F E' F' : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace E'] [TopologicalSpace F']

/-- Restrict an actual locally continuous product map to a product of open
balls, with its genuine continuous-map structure. -/
def normalProductBallMap (Φ : E × F → E' × F') (r s : ℝ)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s)) :
    TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶ TopCat.of (E' × F') :=
  TopCat.ofHom
    ⟨fun x => Φ (x.1.val, x.2.val), hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun x => ⟨x.1.property, x.2.property⟩)⟩

/-- The local geometric complement condition supplies an actual map of pairs. -/
theorem normalProductBallMap_mapsTo (Φ : E × F → E' × F') (r s : ℝ) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s)) (z' : F')
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s,
      x.2 ≠ 0 → (Φ x).2 ≠ z') :
    Set.MapsTo (normalProductBallMap Φ r s hc)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E' F' z') := by
  intro x hx
  exact hpair _ ⟨x.1.property, x.2.property⟩ (fun h => hx (Subtype.ext h))

end BallMaps

section LocalComplexSlice

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {p : ℕ}

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- When the normal slice fixes the origin, it equals the translated map
used by the actual derivative homotopy. -/
theorem normalProductBallMap_slice_eq_translated
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hzero : (Φ (0, 0)).2 = 0)
    (hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s)) :
    normalSliceMap (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr) =
      LocalDerivativeHomology.Cycles.translatedBallMap (fun y => (Φ (0, y)).2) s hslice := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (Φ (0, x.val)).2 = (Φ (0, x.val)).2 - (Φ (0, 0)).2
  rw [hzero, sub_zero]

/-- A checked derivative remainder bound gives identity normal action on
the actual product-ball pair, in every homology degree. -/
theorem normalProductBallMap_action_eq_id
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s,
      x.2 ≠ 0 → (Φ x).2 ≠ 0)
    (hzero : (Φ (0, 0)).2 = 0) (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s))
    (he : ∀ y, ‖y‖ < s → ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖) (n : ℕ) :
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
          (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) n ≫
            (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 n).hom = 𝟙 _ := by
  rw [normalOpenProductBallsHomology_conjugate]
  have hmap : LocalHomology.Cycles.relativeSingularHomologyMap
      (normalSliceMap (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr))
      (normalSliceMap_mapsTo (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs) 0
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair)) n =
      LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap (fun y => (Φ (0, y)).2)
        (L.restrictScalars ℝ) s hs hslice he n := by
    unfold LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap
    exact relativeMap_congr
      (normalProductBallMap_slice_eq_translated Φ r s hr hc hzero hslice)
      (normalSliceMap_mapsTo (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs) 0
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair))
      (LocalDerivativeHomology.Cycles.translatedBallMap_preservesPuncture (fun y => (Φ (0, y)).2)
        (L.restrictScalars ℝ) s hs hslice he) n
  rw [hmap, LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap_eq_excision_comp,
    complexLinearLocalHomologyMap_eq_id_all, Category.comp_id, Iso.inv_hom_id]

/-- A genuinely defined local product map with invertible complex normal
derivative acts identically on normal local homology after shrinking to
actual product balls. The radii and the derivative remainder bound are proved. -/
theorem exists_normalProductBallMap_action_eq_id
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      ∀ n : ℕ,
        (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs n).inv ≫
          LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
            (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
              (fun x hx => hpair x (hsub hx))) n ≫
            (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 n).hom = 𝟙 _ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) r ⊆ W := by
    rw [ball_prod_same]
    exact hball
  have hsmall : {y | ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖} ∈ 𝓝 (0 : Fin p → ℂ) :=
    DerivativePuncturedHomotopy.Cycles.eventually_derivative_remainder_small (L.restrictScalars ℝ) hderiv
  obtain ⟨s, hs, hsball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Metric.ball_mem_nhds (0 : Fin p → ℂ) hr) hsmall)
  have hnormal : Metric.ball (0 : Fin p → ℂ) s ⊆ Metric.ball 0 r :=
    fun _ hy => (hsball hy).1
  have hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W :=
    (Set.prod_mono Subset.rfl hnormal).trans hprod
  have hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s) :=
    (hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => hsub ⟨Metric.mem_ball_self hr, hy⟩)).snd
  have he : ∀ y, ‖y‖ < s → ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖ := by
    intro y hy
    exact (hsball (by simpa only [Metric.mem_ball, dist_zero_right] using hy)).2
  refine ⟨r, s, hr, hs, hsub, fun n => ?_⟩
  exact normalProductBallMap_action_eq_id Φ r s hr hs (hΦ.mono hsub)
    (fun x hx => hpair x (hsub hx)) hzero L hslice he n

/-- The normalized normal class on a product of coordinate balls, obtained
from the actual product/excision isomorphism and the existing normal generator. -/
def complexNormalOpenProductBallsClass (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    LocalHomology.Cycles.relativeSingularHomology
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) :=
  (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv
    ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- Identity of the actual conjugated normal action implies preservation of
the already normalized normal class, rather than just a rank-one statement. -/
theorem normalProductBallMap_class_of_action
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s,
      x.2 ≠ 0 → (Φ x).2 ≠ 0)
    (hact : (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p) ≫
        (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).hom = 𝟙 _) :
    LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
      (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p := by
  have hm : (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p) =
      (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).inv := by
    apply (cancel_mono (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id]
    exact hact
  exact ConcreteCategory.congr_hom hm ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- A local nonlinear coordinate change with invertible complex normal
derivative preserves the normalized normal class on a proved smaller product. -/
theorem exists_normalProductBallMap_class_invariant
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
        (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p := by
  obtain ⟨r, s, hr, hs, hsub, hact⟩ :=
    exists_normalProductBallMap_action_eq_id Φ W hW hΦ hpair hzero L hderiv
  exact ⟨r, s, hr, hs, hsub, normalProductBallMap_class_of_action Φ r s hr hs
    (hΦ.mono hsub) (fun x hx => hpair x (hsub hx)) (hact (2 * p))⟩

end LocalComplexSlice

section NormalBlockDerivative

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℕ}

/-- The normal slice derivative is the genuine normal block of the ambient
derivative. Its invertibility was proved from both horizontal preservation laws. -/
theorem normalSlice_hasFDerivAt_normalBlock
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    HasFDerivAt (fun y => (Φ (0, y)).2)
      (((ComplexNormalBlock.Cycles.normalBlock L hL hLi).restrictScalars ℝ) : _ →L[ℝ] _) 0 := by
  have h : HasFDerivAt (fun y => (Φ (0, y)).2) (ComplexNormalBlock.Cycles.normalBlock L hL hLi).toContinuousLinearMap 0 := by
    simpa only [ComplexNormalBlock.Cycles.normalBlock_toContinuousLinearMap, ContinuousLinearMap.inr_apply,
      Function.comp_def] using
      (hderiv.comp 0 (ContinuousLinearMap.inr ℂ E (Fin p → ℂ)).hasFDerivAt).snd
  exact h.restrictScalars ℝ

end NormalBlockDerivative

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] {p : ℕ}

/-- An actual nonlinear normal-coordinate change with an invertible
plane-preserving complex ambient derivative preserves the normalized normal
class after a proved product-neighborhood shrinking. -/
theorem exists_normalCoordinate_class_invariant
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
        (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E p :=
  exists_normalProductBallMap_class_invariant Φ W hW hΦ hpair hzero (ComplexNormalBlock.Cycles.normalBlock L hL hLi)
    (normalSlice_hasFDerivAt_normalBlock Φ L hL hLi hderiv)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction.Cycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity -/

/-! # Normal Product Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity

noncomputable section

/-!
# Rational purity and the normalized class of the actual normal product pair

The class is pulled back from the computed punctured complex normal model
along the actual normal projection. The pair contraction proves that this
pullback is an isomorphism. This gives the local product calculation needed
by normal charts, without postulating a global Thom class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual rational relative cohomology of the product with a complex normal space. -/
abbrev complexNormalProductRationalCohomology (p n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (E × (Fin p → ℂ)))
    (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) n

/-- The normalized top-degree coordinate comes from the actual normal projection. -/
def complexNormalProductRationalTopCohomologyEquiv (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) ≃ₗ[ℚ] ℚ :=
  (NormalProductCohomology.Cycles.normalProductCohomologyIso (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) 0 (2 * p)).toLinearEquiv.symm.trans
    (RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv p)

/-- The same genuine product-pair calculation as an isomorphism of rational modules. -/
def complexNormalProductRationalTopCohomologyIso (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  (complexNormalProductRationalTopCohomologyEquiv E p).toModuleIso

/-- The normalized rational relative class of the normal product pair. -/
def complexNormalProductRationalClass (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) :=
  (complexNormalProductRationalTopCohomologyEquiv E p).symm 1

@[simp]
theorem complexNormalProductRationalClass_normalization (p : ℕ) :
    complexNormalProductRationalTopCohomologyEquiv E p
      (complexNormalProductRationalClass E p) = 1 :=
  (complexNormalProductRationalTopCohomologyEquiv E p).apply_symm_apply 1

/-- The normalized class is literally the pullback of the actual normal dual class. -/
theorem complexNormalProductRationalClass_eq_pullback (p : ℕ) :
    complexNormalProductRationalClass E p =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p)).hom
          (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := rfl

/-- Restriction to every constant tangential fiber is the same normalized normal class. -/
theorem complexNormalProductRationalClass_fiber (p : ℕ) (e : E) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalProductPair.Cycles.normalProductSection E (Fin p → ℂ) e)
      (NormalProductPair.Cycles.normalProductSection_mapsTo E (Fin p → ℂ) e 0) (2 * p)).hom
        (complexNormalProductRationalClass E p) = RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  rw [complexNormalProductRationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (NormalProductCohomology.Cycles.normalProductCohomology_fiber (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) e 0 (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- On each normal fiber the class evaluates to one on the actual rationalized
integral local homology generator. -/
theorem complexNormalProductRationalClass_fiber_evaluation (p : ℕ) (e : E) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductSection E (Fin p → ℂ) e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E (Fin p → ℂ) e 0) (2 * p)).hom
          (complexNormalProductRationalClass E p))
      (RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator p) = 1 := by
  rw [complexNormalProductRationalClass_fiber]
  exact RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation p

/-- The computed normal product class is nonzero. -/
theorem complexNormalProductRationalClass_ne_zero (p : ℕ) :
    complexNormalProductRationalClass E p ≠ 0 := by
  intro h
  have hn := complexNormalProductRationalClass_normalization E p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every top-degree product-pair class is a unique rational multiple of this class. -/
theorem complexNormalProductRationalClass_generates (p : ℕ)
    (a : complexNormalProductRationalCohomology E p (2 * p)) :
    ∃! q : ℚ, q • complexNormalProductRationalClass E p = a := by
  have hnorm (q : ℚ) :
      complexNormalProductRationalTopCohomologyEquiv E p
        (q • complexNormalProductRationalClass E p) = q := by
    rw [map_smul, complexNormalProductRationalClass_normalization]
    exact mul_one q
  refine ⟨complexNormalProductRationalTopCohomologyEquiv E p a, ?_, ?_⟩
  · apply (complexNormalProductRationalTopCohomologyEquiv E p).injective
    exact hnorm _
  · intro q hq
    calc
      q = complexNormalProductRationalTopCohomologyEquiv E p
          (q • complexNormalProductRationalClass E p) := (hnorm q).symm
      _ = complexNormalProductRationalTopCohomologyEquiv E p a :=
        congrArg (complexNormalProductRationalTopCohomologyEquiv E p) hq

/-- Actual relative cohomology vanishes outside the normal real dimension. -/
theorem complexNormalProductRationalCohomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (complexNormalProductRationalCohomology E p n) :=
  (RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology_isZero p n hn).of_iso
    (NormalProductCohomology.Cycles.normalProductCohomologyIso (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) 0 n).symm

/-- Top relative cohomology is nonzero, including codimension zero. -/
theorem complexNormalProductRationalTopCohomology_not_isZero (p : ℕ) :
    ¬ IsZero (complexNormalProductRationalCohomology E p (2 * p)) := by
  intro h
  let : Subsingleton (complexNormalProductRationalCohomology E p (2 * p)) :=
    ModuleCat.subsingleton_of_isZero h
  exact complexNormalProductRationalClass_ne_zero E p (Subsingleton.elim _ _)

/-- The precise purity statement for all degrees of the actual normal product pair. -/
theorem complexNormalProductRationalCohomology_isZero_iff (p n : ℕ) :
    IsZero (complexNormalProductRationalCohomology E p n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalProductRationalTopCohomology_not_isZero E p h
  · exact complexNormalProductRationalCohomology_isZero E p n

/-- The normalized class is invariant under every invertible complex normal matrix. -/
theorem complexNormalProductRationalClass_invariant (p : ℕ)
    (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalProductPair.Cycles.normalProductComplexChange E A)
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo E A hA) (2 * p)).hom
        (complexNormalProductRationalClass E p) = complexNormalProductRationalClass E p :=
  NormalProductCohomology.Cycles.normalProductComplexChange_class_invariant (ModuleCat.of ℚ ℚ) E A hA (2 * p)
    (complexNormalProductRationalClass E p)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality -/

/-! # Dual Complex Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality.Cycles

noncomputable section

/-!
# Naturality of dual-complex evaluation and universal coefficients

Precomposition by an actual chain map gives the actual map of linear Hom
cochain complexes. The evaluation pairing descends naturally through both
cycle quotients. Over a field, the canonical universal-coefficient equivalence
therefore intertwines cohomological pullback and precomposition on homology.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

section Evaluation

variable {R : Type} [CommRing R]
variable {C D E : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Linear Hom pullback preserves the identity chain map. -/
@[simp]
theorem linearHomCochainMap_id (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) :
    DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (𝟙 C) M = 𝟙 (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex C M) := by
  ext n φ
  rfl

/-- Linear Hom pullback reverses composition of actual chain maps. -/
@[simp]
theorem linearHomCochainMap_comp (f : C ⟶ D) (g : D ⟶ E)
    (M : ModuleCat.{0} R) :
    DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (f ≫ g) M =
      DualComplexUniversalCoefficient.Cycles.linearHomCochainMap g M ≫ DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M := by
  ext n φ
  rfl

/-- A pulled-back cocycle evaluates on a class by first pushing the class forward. -/
theorem evaluateLinearHomCocycle_naturality (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M) n)
    (z : C.homology n) :
    DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle C M n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n c) z =
      DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle D M n c ((HomologicalComplex.homologyMap f n) z) := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n z
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle_chainClass,
    DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle_chainClass]
  rfl

/-- The canonical pairing on actual cohomology and homology is natural for every
chain map, including degree zero. -/
theorem linearHomHomologyEvaluation_naturality (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M).homology n) (z : C.homology n) :
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation C M n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n) c) z =
      DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation D M n c ((HomologicalComplex.homologyMap f n) z) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M) n c
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n z
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class, DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class]
  rfl

/-- Naturality of canonical evaluation as equality of linear functionals. -/
theorem linearHomHomologyEvaluation_naturality_linearMap (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M).homology n) :
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation C M n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n) c) =
      (DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation D M n c).comp
        (HomologicalComplex.homologyMap f n).hom := by
  ext z
  exact linearHomHomologyEvaluation_naturality f M n c z

end Evaluation

variable {F : Type} [Field F]
variable {C D : ChainComplex (ModuleCat.{0} F) ℕ}

/-- The canonical field universal-coefficient equivalence intertwines actual
cohomological pullback with precomposition by the actual map on homology. -/
theorem dualComplexUniversalCoefficientEquiv_naturality (f : C ⟶ D)
    (n : ℕ) (c : (DualComplexUniversalCoefficient.Cycles.dualCochainComplex D).homology n) :
    DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f (ModuleCat.of F F)) n) c) =
      (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv D n c).comp
        (HomologicalComplex.homologyMap f n).hom :=
  linearHomHomologyEvaluation_naturality_linearMap f (ModuleCat.of F F) n c

/-- The inverse universal-coefficient equivalence is natural as well; extending a
functional introduces no choice into its cohomology class. -/
theorem dualComplexUniversalCoefficientEquiv_symm_naturality (f : C ⟶ D)
    (n : ℕ) (L : Module.Dual F (D.homology n)) :
    (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n).symm
        (L.comp (HomologicalComplex.homologyMap f n).hom) =
      (HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f (ModuleCat.of F F)) n)
        ((DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv D n).symm L) := by
  apply (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n).injective
  rw [LinearEquiv.apply_symm_apply, dualComplexUniversalCoefficientEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality.Cycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality -/

/-! # Relative Universal Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles

noncomputable section

/-!
# Naturality of relative evaluation and universal coefficients

The actual relative cochain kernel and relative chain cokernel have their
canonical maps for continuous maps of pairs. Their degreewise duality and
canonical pairing commute with those maps. Consequently the field
universal-coefficient equivalence and its inverse are natural for pairs.
-/

open _root_.CategoryTheory

section Evaluation

variable {R : Type} [CommRing R]

/-- Relative degreewise evaluation intertwines the actual maps of pair cochains
and pair chains. -/
theorem relativeDegreewiseChainDualEquiv_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y B).X n) :
    RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h).f n c) =
      (RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv M Y B n c).comp
        ((RelativeScalarChains.Cycles.relativeScalarChainsMap R f h).f n).hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective R X A n z
  rw [RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection, LinearMap.comp_apply]
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality R f h) n) z
  change (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h).f n ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n z) =
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y B).f n ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap f).f n z) at hp
  rw [hp, RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection]
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f h) n) c
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h).f n c) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f n c) at hi
  rw [hi]
  exact LinearMap.congr_fun
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map f) n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f n c)) z

/-- The canonical identification of relative cochains with the dual complex
commutes with every continuous map of pairs. -/
theorem relativeCochainDualIso_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h ≫ (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom =
      (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom ≫
        DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M := by
  ext n c
  exact relativeDegreewiseChainDualEquiv_naturality M f h n c

/-- The same canonical square commutes on genuine categorical cohomology. -/
theorem relativeCochainDualIso_homology_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n ≫
        HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n =
      HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n ≫
        HomologicalComplex.homologyMap
          (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M) n := by
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f h) n ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeCochainDualIso_naturality]

/-- Relative cohomological pullback is adjoint to the actual relative homology
pushforward under canonical evaluation, in every degree. -/
theorem relativeHomologyEvaluation_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n) (z : RelativeScalarChains.Cycles.relativeScalarHomology R X A n) :
    RelativeChainD.Cycles.relativeHomologyEvaluation M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) z =
      RelativeChainD.Cycles.relativeHomologyEvaluation M Y B n c
        ((HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) n) z) := by
  have hi := ConcreteCategory.congr_hom
    (relativeCochainDualIso_homology_naturality M f h n) c
  change (HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) =
    (HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M) n)
      ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n) c) at hi
  change DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation (RelativeScalarChains.Cycles.relativeScalarChains R X A) M n
      ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M X A).hom n)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c)) z = _
  rw [hi]
  exact DualComplexNaturality.Cycles.linearHomHomologyEvaluation_naturality (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) M n
    ((HomologicalComplex.homologyMap (RelativeChainD.Cycles.relativeCochainDualIso M Y B).hom n) c) z

/-- Pair-map naturality as equality of linear functionals on relative homology. -/
theorem relativeHomologyEvaluation_naturality_linearMap (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n) :
    RelativeChainD.Cycles.relativeHomologyEvaluation M X A n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f h n) c) =
      (RelativeChainD.Cycles.relativeHomologyEvaluation M Y B n c).comp
        (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap R f h) n).hom := by
  ext z
  exact relativeHomologyEvaluation_naturality M f h n c z

end Evaluation

variable (F : Type) [Field F]

/-- The field universal-coefficient equivalence for actual relative singular
cohomology is natural for all continuous maps of pairs. -/
theorem relativeUniversalCoefficientEquiv_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) Y B n) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of F F) f h n) c) =
      (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F Y B n c).comp
        (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap F f h) n).hom :=
  relativeHomologyEvaluation_naturality_linearMap (ModuleCat.of F F) f h n c

/-- The inverse relative universal-coefficient equivalence also respects maps
of pairs; no choice of extending a functional affects this identity. -/
theorem relativeUniversalCoefficientEquiv_symm_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) (L : Module.Dual F (RelativeScalarChains.Cycles.relativeScalarHomology F Y B n)) :
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n).symm
        (L.comp (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap F f h) n).hom) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of F F) f h n)
        ((RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F Y B n).symm L) := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv F X A n).injective
  rw [LinearEquiv.apply_symm_apply, relativeUniversalCoefficientEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood -/

/-! # Normal Plane Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood.Cycles

/-!
# Normal-plane preservation near the origin of an open chart

The horizontal inclusion `x ↦ (x, 0)` is continuous. Hence an open chart
containing the origin contains this inclusion near the origin, and actual
preservation of the zero normal coordinate gives the corresponding eventual
equality. The same argument applies to the inverse chart. No differentiability
or linear structure is needed for this topological step.
-/

open Filter _root_.Topology

universe uE uF

variable {E : Type uE} [TopologicalSpace E] [Zero E]
variable {F : Type uF} [TopologicalSpace F] [Zero F]

/-- A neighborhood of the product origin contains horizontal points near the
origin of the first factor. -/
theorem normalPlane_eventually_mem {U : Set (E × F)} (hU : IsOpen U)
    (h0 : ((0 : E), (0 : F)) ∈ U) :
    ∀ᶠ x : E in 𝓝 0, (x, (0 : F)) ∈ U := by
  have h : Continuous (fun x : E => (x, (0 : F))) :=
    continuous_id.prodMk continuous_const
  exact h.continuousAt.eventually (hU.eventually_mem h0)

theorem normalPlane_eventually_mem_source (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source) :
    ∀ᶠ x : E in 𝓝 0, (x, (0 : F)) ∈ e.source :=
  normalPlane_eventually_mem e.open_source h0

/-- Actual preservation on the chart source implies preservation on the
horizontal slice near the origin. -/
theorem normalPlane_eventually_map_snd_eq_zero
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (hpres : ∀ z ∈ e.source, z.2 = 0 → (e z).2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e (x, (0 : F))).2 = 0 :=
  (normalPlane_eventually_mem_source e h0).mono fun x hx => hpres (x, 0) hx rfl

/-- A chart carrying the origin to the origin has the origin in its target. -/
theorem normalPlane_zero_mem_target (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) :
    ((0 : E), (0 : F)) ∈ e.target :=
  he0 ▸ e.map_source h0

/-- The actual partial inverse of an origin-fixing chart fixes the origin. -/
theorem normalPlane_symm_apply_zero (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) :
    e.symm (0, 0) = (0, 0) := by
  simpa only [he0] using e.left_inv h0

/-- Actual preservation by the inverse on the chart target implies the
eventual zero-normal equality for the inverse horizontal slice. -/
theorem normalPlane_eventually_symm_snd_eq_zero
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpresInv : ∀ z ∈ e.target, z.2 = 0 → (e.symm z).2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e.symm (x, (0 : F))).2 = 0 :=
  normalPlane_eventually_map_snd_eq_zero e.symm
    (normalPlane_zero_mem_target e h0 he0) hpresInv

/-- Exact preservation of the normal-zero set on the source also proves
preservation by the actual inverse, so no independent inverse assumption is
needed in this formulation. -/
theorem normalPlane_eventually_symm_snd_eq_zero_of_iff
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e.symm (x, (0 : F))).2 = 0 := by
  apply normalPlane_eventually_symm_snd_eq_zero e h0 he0
  intro z hz hz0
  apply (hpres (e.symm z) (e.map_target hz)).mp
  rw [e.right_inv hz]
  exact hz0

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood.Cycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative -/

/-! # Normal Derivative -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative.Cycles

noncomputable section

/-!
# Derivatives of genuine normal coordinate changes

Restricting a differentiable map to the horizontal coordinate plane and
then projecting to its normal coordinate gives a locally zero map when
the original map preserves that plane. Uniqueness of the derivative makes
the lower-left derivative block zero. Applying the same argument to the
actual inverse proves the two preservation hypotheses needed by the
previously constructed complex normal-block equivalence.
-/

open Filter
open scoped _root_.Topology _root_.Manifold

section GeneralDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The lower-left derivative block vanishes when the normal component
of the restriction to the horizontal plane is locally zero. -/
theorem normalDerivative_lowerLeft_eq_zero
    {Φ : E × F → G × H} {D : (E × F) →L[𝕜] (G × H)}
    (hd : HasFDerivAt Φ D (0, 0))
    (hz : ∀ᶠ x : E in 𝓝 0, (Φ (x, 0)).2 = 0) :
    (ContinuousLinearMap.snd 𝕜 G H).comp
      (D.comp (ContinuousLinearMap.inl 𝕜 E F)) = 0 := by
  have hin : HasFDerivAt (fun x : E => (x, (0 : F)))
      (ContinuousLinearMap.inl 𝕜 E F) (0 : E) :=
    (ContinuousLinearMap.inl 𝕜 E F).hasFDerivAt
  have hrestrict : HasFDerivAt (fun x : E => (Φ (x, 0)).2)
      ((ContinuousLinearMap.snd 𝕜 G H).comp
        (D.comp (ContinuousLinearMap.inl 𝕜 E F))) 0 := by
    exact (hd.comp (0 : E) hin).snd
  exact hrestrict.unique
    ((hasFDerivAt_const (𝕜 := 𝕜) (0 : H) (0 : E)).congr_of_eventuallyEq hz)

/-- Consequently the actual derivative maps every horizontal tangent
vector to a horizontal vector. -/
theorem normalDerivative_preserves_horizontal
    {Φ : E × F → G × H} {D : (E × F) →L[𝕜] (G × H)}
    (hd : HasFDerivAt Φ D (0, 0))
    (hz : ∀ᶠ x : E in 𝓝 0, (Φ (x, 0)).2 = 0) (x : E) :
    (D (x, 0)).2 = 0 :=
  congrArg (fun L : E →L[𝕜] H => L x) (normalDerivative_lowerLeft_eq_zero hd hz)

/-- Actual source-plane preservation implies preservation by the
derivative; the neighborhood condition is derived from source openness. -/
theorem normalCoordinateDerivative_preserves_horizontal
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (D : (E × F) →L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (hd : HasFDerivAt e D (0, 0))
    (hpres : ∀ z ∈ e.source, z.2 = 0 → (e z).2 = 0) :
    ∀ x : E, (D (x, 0)).2 = 0 :=
  normalDerivative_preserves_horizontal hd
    (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_map_snd_eq_zero e h0 hpres)

/-- The actual inverse has the inverse derivative at the origin. -/
theorem normalCoordinateInverse_hasFDerivAt
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0)) :
    HasFDerivAt e.symm L.symm.toContinuousLinearMap (0, 0) := by
  apply e.hasFDerivAt_symm (NormalPlaneNeighborhood.Cycles.normalPlane_zero_mem_target e h0 he0)
  simpa only [NormalPlaneNeighborhood.Cycles.normalPlane_symm_apply_zero e h0 he0] using hd

/-- Actual preservation of the horizontal plane by the inverse gives
the corresponding preservation by the inverse derivative. -/
theorem normalCoordinateInverseDerivative_preserves_horizontal
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.target, z.2 = 0 → (e.symm z).2 = 0) :
    ∀ x : E, (L.symm (x, 0)).2 = 0 :=
  normalDerivative_preserves_horizontal
    (normalCoordinateInverse_hasFDerivAt e L h0 he0 hd)
    (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_symm_snd_eq_zero e h0 he0 hpres)

/-- Exact preservation of the zero normal locus supplies both derivative
preservation laws, with no independent linear hypothesis. -/
theorem normalCoordinateDerivative_horizontal_pair
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    (∀ x : E, (L (x, 0)).2 = 0) ∧ (∀ x : E, (L.symm (x, 0)).2 = 0) := by
  constructor
  · exact normalCoordinateDerivative_preserves_horizontal e L.toContinuousLinearMap h0 hd
      (fun z hz => (hpres z hz).mpr)
  · exact normalDerivative_preserves_horizontal
      (normalCoordinateInverse_hasFDerivAt e L h0 he0 hd)
      (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_symm_snd_eq_zero_of_iff e h0 he0 hpres)

end GeneralDerivative

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The genuine normal derivative is invertible, using the preservation
laws proved from the nonlinear map and its actual inverse. -/
def normalCoordinateDerivativeBlock
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) : F ≃L[ℂ] F :=
  Geometric.ComplexNormalBlock.Cycles.normalBlock L (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).1
    (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).2

@[simp]
theorem normalCoordinateDerivativeBlock_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    normalCoordinateDerivativeBlock e L h0 he0 hd hpres y = (L (0, y)).2 := rfl

@[simp]
theorem normalCoordinateDerivativeBlock_symm_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    (normalCoordinateDerivativeBlock e L h0 he0 hd hpres).symm y =
      (L.symm (0, y)).2 := rfl

/-- The ambient derivative commutes with projection to the actual normal
block constructed above. -/
theorem normalCoordinateDerivativeBlock_projection
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (z : E × F) :
    (L z).2 = normalCoordinateDerivativeBlock e L h0 he0 hd hpres z.2 :=
  Geometric.ComplexNormalBlock.Cycles.normalBlock_projection L (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).1
    (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).2 z

/-- The ambient derivative of a genuine differentiable local
homeomorphism, with invertibility derived from its differentiable inverse. -/
def normalDiffeomorphDerivative
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    (E × F) ≃L[ℂ] (E × F) :=
  he.mfderiv h0

theorem normalDiffeomorphDerivative_coe
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    (normalDiffeomorphDerivative e he h0).toContinuousLinearMap = fderiv ℂ e (0, 0) :=
  mfderiv_eq_fderiv

theorem normalDiffeomorphDerivative_hasFDerivAt
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    HasFDerivAt e (normalDiffeomorphDerivative e he h0).toContinuousLinearMap (0, 0) := by
  rw [normalDiffeomorphDerivative_coe]
  exact (he.mdifferentiableAt h0).differentiableAt.hasFDerivAt

/-- A genuine complex local diffeomorphism preserving the normal zero
locus induces an invertible normal derivative, with no chosen derivative
or linear-preservation assumptions. -/
def normalDiffeomorphBlock
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) : F ≃L[ℂ] F :=
  normalCoordinateDerivativeBlock e (normalDiffeomorphDerivative e he h0) h0 he0
    (normalDiffeomorphDerivative_hasFDerivAt e he h0) hpres

theorem normalDiffeomorphBlock_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    normalDiffeomorphBlock e he h0 he0 hpres y = (fderiv ℂ e (0, 0) (0, y)).2 := by
  change ((normalDiffeomorphDerivative e he h0).toContinuousLinearMap (0, y)).2 = _
  rw [normalDiffeomorphDerivative_coe]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative.Cycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction -/

/-! # Rational Normal Slice Action -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction.Cycles

noncomputable section

/-!
# Rational dual normal classes and nonlinear normal-coordinate pullback

The normalized rational class is characterized by actual evaluation on the
rationalized integral generator. Naturality of the proved relative universal
coefficient equivalence transfers preservation of that integral generator
to exact pullback equality of the rational class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section IntegralNormalization

variable (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Rationalize a specified genuine integral relative-homology normalization. -/
def rationalRelativeNormalizationIso
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n ≅ ModuleCat.of ℚ ℚ :=
  RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n ≪≫ RationalScalarExtension.Cycles.rationalizeModules.mapIso e ≪≫ RationalScalarExtension.Cycles.rationalizeUnitIso

/-- The actual rational cohomology class whose evaluation is the rationalized
integral coordinate map. -/
def relativeRationalDualOfIntegralIso
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).symm
    (rationalRelativeNormalizationIso X A n e).hom.hom

@[simp]
theorem relativeRationalDualOfIntegralIso_functional
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n (relativeRationalDualOfIntegralIso X A n e) =
      (rationalRelativeNormalizationIso X A n e).hom.hom :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).apply_symm_apply _

/-- This class evaluates to one on the actual rationalized generator. -/
theorem relativeRationalDualOfIntegralIso_evaluation
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n (relativeRationalDualOfIntegralIso X A n e)
      ((rationalRelativeNormalizationIso X A n e).inv 1) = 1 := by
  rw [relativeRationalDualOfIntegralIso_functional]
  change ((rationalRelativeNormalizationIso X A n e).inv ≫
    (rationalRelativeNormalizationIso X A n e).hom) 1 = 1
  rw [Iso.inv_hom_id]
  rfl

/-- Evaluation one on that generator uniquely determines the rational dual class. -/
theorem relativeRationalDualOfIntegralIso_unique
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n a
      ((rationalRelativeNormalizationIso X A n e).inv 1) = 1) :
    a = relativeRationalDualOfIntegralIso X A n e := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).injective
  rw [relativeRationalDualOfIntegralIso_functional]
  exact (DualNormalization.Cycles.dual_normalization_eq_one_iff
    (rationalRelativeNormalizationIso X A n e).toLinearEquiv
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n a)).mp ha

end IntegralNormalization

section Naturality

variable {X Y : TopCat.{0}} {A : Set X} {B : Set Y}

/-- Preservation of the generating integral class determines the whole
integral coordinate map, since maps out of `ℤ` are determined by one. -/
theorem relativeIntegralNormalization_naturality (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (n : ℕ) (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1) = eY.inv 1) :
    LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom := by
  apply (cancel_epi eX.inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change eY.hom (LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1)) = eX.hom (eX.inv 1)
  rw [hgen]
  change (eY.inv ≫ eY.hom) 1 = (eX.inv ≫ eX.hom) 1
  rw [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Rationalization of the actual integral normalizations respects a genuine
map of pairs whose integral coordinate maps commute. -/
theorem rationalRelativeNormalizationIso_naturality
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (he : LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom) :
    HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n ≫
        (rationalRelativeNormalizationIso Y B n eY).hom =
      (rationalRelativeNormalizationIso X A n eX).hom := by
  calc
    _ = (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n ≫
        (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).hom) ≫
          RationalScalarExtension.Cycles.rationalizeModules.map eY.hom ≫ RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      simp only [rationalRelativeNormalizationIso, Iso.trans_hom,
        Functor.mapIso_hom, Category.assoc]
    _ = ((RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f hf n)) ≫
          RationalScalarExtension.Cycles.rationalizeModules.map eY.hom ≫ RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      rw [RationalRelativeHomology.Cycles.rationalRelativeHomologyIso_hom_naturality]
    _ = (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom) ≫
          RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      rw [RationalScalarExtension.Cycles.rationalizeModules.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [he]
      rfl

/-- Actual relative UCT naturality transfers an integral normalization square
to exact pullback equality of the normalized rational duals. -/
theorem relativeRationalDualOfIntegralIso_pullback
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (he : LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n
      (relativeRationalDualOfIntegralIso Y B n eY) = relativeRationalDualOfIntegralIso X A n eX := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).injective
  rw [RelativeUniversalCoefficientNaturality.Cycles.relativeUniversalCoefficientEquiv_naturality,
    relativeRationalDualOfIntegralIso_functional, relativeRationalDualOfIntegralIso_functional]
  exact congrArg ModuleCat.Hom.hom (rationalRelativeNormalizationIso_naturality f hf n eX eY he)

/-- Preservation of the actual integral generator forces preservation of its
normalized rational dual under the actual cohomological pullback. -/
theorem relativeRationalDualOfIntegralIso_pullback_of_generator
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1) = eY.inv 1) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n
      (relativeRationalDualOfIntegralIso Y B n eY) = relativeRationalDualOfIntegralIso X A n eX :=
  relativeRationalDualOfIntegralIso_pullback f hf n eX eY
    (relativeIntegralNormalization_naturality f hf n eX eY hgen)

end Naturality

/-- The existing punctured-normal rational class has exactly the dual
normalization obtained from the specified integral local generator. -/
theorem complexNormalRationalDualClass_eq_integralDual (p : ℕ) :
    RationalLocalPurity.Cycles.complexNormalRationalDualClass p = relativeRationalDualOfIntegralIso
      (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)
        (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ _).injective
  rw [RationalLocalPurity.Cycles.complexNormalRationalDualClass_functional, relativeRationalDualOfIntegralIso_functional]
  rfl

section ProductNormalization

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The already defined product Thom class agrees with the rational dual of
the actual integral product normalization, by projection naturality. -/
theorem complexNormalProductRationalClass_eq_integralDual (p : ℕ) :
    NormalProductPurity.Cycles.complexNormalProductRationalClass E p = relativeRationalDualOfIntegralIso
      (TopCat.of (E × (Fin p → ℂ))) (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
        (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) := by
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback,
    complexNormalRationalDualClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback
    (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ)) (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0)
    (2 * p) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) rfl

/-- Its value on the actual rationalized integral product generator is one. -/
theorem complexNormalProductRationalClass_integral_evaluation (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (E × (Fin p → ℂ)))
      (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p) (NormalProductPurity.Cycles.complexNormalProductRationalClass E p)
        ((rationalRelativeNormalizationIso (TopCat.of (E × (Fin p → ℂ)))
          (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
          (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p)).inv 1) = 1 := by
  rw [complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_evaluation _ _ _ _

/-- The product rational class is uniquely characterized by this evaluation. -/
theorem complexNormalProductRationalClass_unique_integral (p : ℕ)
    (a : NormalProductPurity.Cycles.complexNormalProductRationalCohomology E p (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (E × (Fin p → ℂ)))
      (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p) a
        ((rationalRelativeNormalizationIso (TopCat.of (E × (Fin p → ℂ)))
          (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
          (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p)).inv 1) = 1) :
    a = NormalProductPurity.Cycles.complexNormalProductRationalClass E p := by
  rw [complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_unique _ _ _ _ a ha

end ProductNormalization

section ProductPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (p : ℕ)

/-- Preservation of the actual integral product normal class gives exact
pullback equality for the already defined rational product Thom class. -/
theorem complexNormalProductRationalClass_pullback_of_integral
    (φ : TopCat.of (E × (Fin p → ℂ)) ⟶ TopCat.of (E' × (Fin p → ℂ)))
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0)
      (NormalProductPair.Cycles.normalProductComplement E' (Fin p → ℂ) 0))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p) (NormalProductPair.Cycles.complexNormalProductClass E p) =
      NormalProductPair.Cycles.complexNormalProductClass E' p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) = NormalProductPurity.Cycles.complexNormalProductRationalClass E p := by
  rw [complexNormalProductRationalClass_eq_integralDual,
    complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E' p) hgen

end ProductPullback

section BallNormalization

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integral top relative homology of the actual product-ball pair,
normalized by normal projection, actual excision, and the fixed normal generator. -/
def complexNormalProductBallIntegralIso (p : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    LocalHomology.Cycles.relativeSingularHomology
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p) ≪≫
    ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The projection used by the cohomology construction is precisely the
projection/excision map of the integral product-ball normalization. -/
theorem normalProductBallProjection_homology (F : Type) [NormedAddCommGroup F]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E F r s)
      (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E F r s hs) n =
        (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E F r s hr hs n).hom := by
  change LocalHomology.Cycles.relativeSingularHomologyMap
    (NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s) ≫
      NormalBallRestriction.Cycles.normalBallInclusion F s) _ n =
    LocalHomology.Cycles.relativeSingularHomologyMap
      (NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s))
      (NormalProductPair.Cycles.normalProductProjection_mapsTo _ _ (NormalBallRestriction.Cycles.normalBallCenter F s hs)) n ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (NormalBallRestriction.Cycles.normalBallInclusion F s)
        (NormalBallRestriction.Cycles.normalBallInclusion_mapsTo F s hs) n
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp]

/-- The rational normal class of a product of balls is the actual pullback
of the normal dual class along projection into the full normal space. -/
def complexNormalProductBallRationalClass (p : ℕ) (r s : ℝ) (_hr : 0 < r) (hs : 0 < s) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) :=
  NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap E (Fin p → ℂ) r s hs (2 * p) (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- This is the same class defined by the actual projection cohomology isomorphism. -/
theorem complexNormalProductBallRationalClass_eq_iso (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    complexNormalProductBallRationalClass E p r s hr hs =
      (NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).hom
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
  rw [NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso_hom]
  rfl

/-- The actual projection class is dual to the integral normal class from
the product-ball excision calculation. No radial normalization is substituted. -/
theorem complexNormalProductBallRationalClass_eq_integralDual (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    complexNormalProductBallRationalClass E p r s hr hs =
      relativeRationalDualOfIntegralIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs) := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
    (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p)
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = _
  rw [complexNormalRationalDualClass_eq_integralDual]
  apply relativeRationalDualOfIntegralIso_pullback
  change LocalHomology.Cycles.relativeSingularHomologyMap (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
      (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom =
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).hom ≫
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom
  rw [normalProductBallProjection_homology E (Fin p → ℂ) r s hr hs (2 * p)]

/-- The ball class evaluates to one on the actual rationalized integral ball generator. -/
theorem complexNormalProductBallRationalClass_evaluation (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ (2 * p)
      (complexNormalProductBallRationalClass E p r s hr hs)
      ((rationalRelativeNormalizationIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs)).inv 1) = 1 := by
  rw [complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_evaluation _ _ _ _

/-- Evaluation on the genuine normal generator uniquely fixes the rational ball class. -/
theorem complexNormalProductBallRationalClass_unique (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ (2 * p) a
      ((rationalRelativeNormalizationIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs)).inv 1) = 1) :
    a = complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_unique _ _ _ _ a ha

omit [NormedSpace ℝ E] in
/-- The rational normal classes agree under actual shrinking of both coordinate balls. -/
theorem complexNormalProductBallRationalClass_restrict (p : ℕ) {r r' s s' : ℝ}
    (hr : 0 < r) (hr' : 0 < r') (hs : 0 < s) (hs' : 0 < s')
    (hrr : r' ≤ r) (hss : s' ≤ s) :
    NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyRestriction E (Fin p → ℂ) hs hs' hrr hss (2 * p)
      (complexNormalProductBallRationalClass E p r s hr hs) =
        complexNormalProductBallRationalClass E p r' s' hr' hs' :=
  ConcreteCategory.congr_hom
    (NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap_restrict E (Fin p → ℂ) hs hs' hrr hss (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end BallNormalization

section BallInclusion

variable (E F : Type) [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The actual inclusion of both coordinate balls into the full product. -/
def normalProductBallsInclusion (r s : ℝ) :
    TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶ TopCat.of (E × F) :=
  TopCat.ofHom ⟨fun z => (z.1.val, z.2.val),
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)⟩

theorem normalProductBallsInclusion_mapsTo (r s : ℝ) (hs : 0 < s) :
    Set.MapsTo (normalProductBallsInclusion E F r s)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E F 0) := by
  intro z hz h
  exact hz (Subtype.ext h)

end BallInclusion

section ProductRestriction

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical ball class is exactly the restriction of the canonical
full-product class along the genuine inclusion of pairs. -/
theorem complexNormalProductRationalClass_restrict_balls (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallsInclusion E (Fin p → ℂ) r s)
      (normalProductBallsInclusion_mapsTo E (Fin p → ℂ) r s hs) (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback]
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
      (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallsInclusion E (Fin p → ℂ) r s)
      (normalProductBallsInclusion_mapsTo E (Fin p → ℂ) r s hs) (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

end ProductRestriction

section BallPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (p : ℕ)

/-- Integral generator preservation for an actual ball-to-product pair map
implies exact rational Thom-class pullback equality. -/
theorem complexNormalProductBallRationalClass_pullback_of_integral
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) ⟶
      TopCat.of (E' × (Fin p → ℂ)))
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (NormalProductPair.Cycles.normalProductComplement E' (Fin p → ℂ) 0))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p)
      (NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductRationalClass_eq_integralDual,
    complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (complexNormalProductBallIntegralIso E p r s hr hs) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E' p) hgen

/-- The same exact duality statement applies between two genuine product-ball pairs. -/
theorem complexNormalProductBallRationalClass_pullback_between_balls
    (r s r' s' : ℝ) (hr : 0 < r) (hs : 0 < s) (hr' : 0 < r') (hs' : 0 < s')
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) ⟶
      TopCat.of (Metric.ball (0 : E') r' × Metric.ball (0 : Fin p → ℂ) s'))
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E') r') (Metric.ball (0 : Fin p → ℂ) s')
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s' hs')))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p)
      (NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E p r s hr hs) =
        NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E' p r' s' hr' hs') :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (complexNormalProductBallRationalClass E' p r' s' hr' hs') =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductBallRationalClass_eq_integralDual,
    complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (complexNormalProductBallIntegralIso E p r s hr hs)
    (complexNormalProductBallIntegralIso E' p r' s' hr' hs') hgen

end BallPullback

section NonlinearPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {p : ℕ}

/-- The actual integral normal-slice invariance theorem implies exact
pullback equality of the normalized rational Thom classes after shrinking. -/
theorem exists_normalSlice_rationalClass_pullback
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) =
          complexNormalProductBallRationalClass E p r s hr hs := by
  obtain ⟨r, s, hr, hs, hsub, hgen⟩ :=
    NormalSliceLocalAction.Cycles.exists_normalProductBallMap_class_invariant Φ W hW hΦ hpair hzero L hderiv
  exact ⟨r, s, hr, hs, hsub,
    complexNormalProductBallRationalClass_pullback_of_integral p r s hr hs
      (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
      (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
        (fun x hx => hpair x (hsub hx))) hgen⟩

end NonlinearPullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] {p : ℕ}

/-- Rational normal-class pullback for a genuine local coordinate map with
its actual complex ambient derivative and proved normal-block invertibility. -/
theorem exists_normalCoordinate_rationalClass_pullback
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
          complexNormalProductBallRationalClass E p r s hr hs :=
  exists_normalSlice_rationalClass_pullback Φ W hW hΦ hpair hzero
    (ComplexNormalBlock.Cycles.normalBlock L hL hLi) (NormalSliceLocalAction.Cycles.normalSlice_hasFDerivAt_normalBlock Φ L hL hLi hderiv)

/-- A genuine complex local diffeomorphism preserving the normal zero locus
has the required rational pullback property. Invertibility and both horizontal
derivative conditions are derived from the map and its actual inverse. -/
theorem exists_normalDiffeomorph_rationalClass_pullback
    (e : OpenPartialHomeomorph (E × (Fin p → ℂ)) (E × (Fin p → ℂ)))
    (he : e.MDifferentiable 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ)))
    (h0 : (0, 0) ∈ e.source) (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ e.source),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap e r s (e.continuousOn.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo e r s hs (e.continuousOn.mono hsub) 0
          (fun x hx hz h => hz ((hpres x (hsub hx)).mp h))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
          complexNormalProductBallRationalClass E p r s hr hs := by
  let L := NormalDerivative.Cycles.normalDiffeomorphDerivative e he h0
  have hd := NormalDerivative.Cycles.normalDiffeomorphDerivative_hasFDerivAt e he h0
  obtain ⟨hL, hLi⟩ := NormalDerivative.Cycles.normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres
  exact exists_normalCoordinate_rationalClass_pullback e e.source
    (e.open_source.mem_nhds h0) e.continuousOn
    (fun x hx hz h => hz ((hpres x hx).mp h))
    (congrArg Prod.snd he0) L hL hLi hd

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction.Cycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairTransition -/

/-! # Normal Pair Transition -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Transitions on verified normal-pair neighborhoods

The ambient chart of a normal pair may extend beyond the neighborhood on
which it describes the full image. We first restrict both charts to those
proved neighborhoods. Their transition then preserves the normal zero
locus on its entire actual source, as does its inverse.
-/

open Set
open scoped _root_.Topology _root_.Manifold

variable {M N : Type*} [TopologicalSpace N] {f : M → N} {x : M}
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup E'] [NormedAddCommGroup F']
  (P : NormalPairRecenter.ImmersionNormalPair E F f x)

/-- Restrict to precisely the neighborhood where the full-image statement
has been proved. -/
def NormalPairRecenter.ImmersionNormalPair.restrictedChart : OpenPartialHomeomorph N (E × F) :=
  P.ambientChart.restrOpen P.neighborhood P.isOpen_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_source : P.restrictedChart.source = P.neighborhood := by
  change P.ambientChart.source ∩ P.neighborhood = P.neighborhood
  exact inter_eq_right.mpr P.neighborhood_subset_source

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_target : P.restrictedChart.target =
    Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius := by
  rw [← P.restrictedChart.image_source_eq_target, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  exact P.ambientChart.image_symm_image_of_subset_target P.product_subset_target

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_apply (y : N) : P.restrictedChart y = P.ambientChart y := rfl

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_symm_apply (z : E × F) :
    P.restrictedChart.symm z = P.ambientChart.symm z := rfl

theorem NormalPairRecenter.ImmersionNormalPair.point_mem_restrictedChart_source : f x ∈ P.restrictedChart.source := by
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  exact P.point_mem_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_point : P.restrictedChart (f x) = (0, 0) :=
  P.point_coordinates

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero : P.ambientChart.symm (0, 0) = f x := by
  rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_restrictedChart_target : (0, 0) ∈ P.restrictedChart.target := by
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_target]
  exact ⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩

variable (Q : NormalPairRecenter.ImmersionNormalPair E' F' f x)

/-- The actual coordinate transition on the overlap of the proved normal
neighborhoods. -/
def NormalPairRecenter.ImmersionNormalPair.transition : OpenPartialHomeomorph (E × F) (E' × F') :=
  P.restrictedChart.symm.trans Q.restrictedChart

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_apply (z : E × F) :
    P.transition Q z = Q.ambientChart (P.ambientChart.symm z) := rfl

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_apply (z : E' × F') :
    (P.transition Q).symm z = P.ambientChart (Q.ambientChart.symm z) := rfl

/-- Membership in the transition source requires both verified neighborhoods. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_source : (P.transition Q).source =
    (Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius) ∩
      P.ambientChart.symm ⁻¹' Q.neighborhood := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_source]
  change P.restrictedChart.target ∩ P.ambientChart.symm ⁻¹' Q.restrictedChart.source = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_target, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]

/-- The source is exactly the first chart's image of the actual overlap. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_source_image : (P.transition Q).source =
    P.ambientChart '' (P.neighborhood ∩ Q.neighborhood) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_source'']
  change P.restrictedChart '' (P.restrictedChart.source ∩ Q.restrictedChart.source) = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  rfl

/-- The target is exactly the second chart's image of the same overlap. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_target_image : (P.transition Q).target =
    Q.ambientChart '' (P.neighborhood ∩ Q.neighborhood) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_target'']
  change Q.restrictedChart '' (Q.restrictedChart.source ∩ P.restrictedChart.source) = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, inter_comm]
  rfl

theorem NormalPairRecenter.ImmersionNormalPair.isOpen_transition_source : IsOpen (P.transition Q).source :=
  (P.transition Q).open_source

theorem NormalPairRecenter.ImmersionNormalPair.isOpen_transition_target : IsOpen (P.transition Q).target :=
  (P.transition Q).open_target

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm : (P.transition Q).symm = Q.transition P := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rfl

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_transition_source : (0, 0) ∈ (P.transition Q).source := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_source]
  refine ⟨⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩, ?_⟩
  change P.ambientChart.symm (0, 0) ∈ Q.neighborhood
  rw [NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero]
  exact Q.point_mem_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_zero : P.transition Q (0, 0) = (0, 0) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_apply, NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero, Q.point_coordinates]

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_transition_target : (0, 0) ∈ (P.transition Q).target := by
  rw [← P.transition_zero Q]
  exact (P.transition Q).map_source (P.zero_mem_transition_source Q)

/-- The transition preserves the zero normal locus everywhere on its
verified source, because both charts describe the same full image. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_preserves_zero (z : E × F) (hz : z ∈ (P.transition Q).source) :
    (P.transition Q z).2 = 0 ↔ z.2 = 0 := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_source] at hz
  have hp : P.ambientChart.symm z ∈ P.neighborhood := ⟨z, hz.1, rfl⟩
  have hP := P.range_iff (P.ambientChart.symm z) hp
  have hQ := Q.range_iff (P.ambientChart.symm z) hz.2
  rw [P.ambientChart.right_inv (P.product_subset_target hz.1)] at hP
  exact hQ.symm.trans hP

theorem NormalPairRecenter.ImmersionNormalPair.transition_preserves_complement (z : E × F) (hz : z ∈ (P.transition Q).source) :
    (P.transition Q z).2 ≠ 0 ↔ z.2 ≠ 0 :=
  not_congr (P.transition_preserves_zero Q z hz)

/-- The inverse transition has the same full zero-locus preservation. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_preserves_zero (z : E' × F')
    (hz : z ∈ (P.transition Q).target) :
    ((P.transition Q).symm z).2 = 0 ↔ z.2 = 0 := by
  have h := P.transition_preserves_zero Q ((P.transition Q).symm z)
    ((P.transition Q).map_target hz)
  rw [(P.transition Q).right_inv hz] at h
  exact h.symm

theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_preserves_complement (z : E' × F')
    (hz : z ∈ (P.transition Q).target) :
    ((P.transition Q).symm z).2 ≠ 0 ↔ z.2 ≠ 0 :=
  not_congr (P.transition_symm_preserves_zero Q z hz)

/-- The actual zero slices in the overlap are homeomorphic. -/
def NormalPairRecenter.ImmersionNormalPair.transitionSupportHomeomorph :
    {z : (P.transition Q).source // z.val.2 = 0} ≃ₜ
      {z : (P.transition Q).target // z.val.2 = 0} :=
  (P.transition Q).toHomeomorphSourceTarget.subtype
    (fun z => (P.transition_preserves_zero Q z.val z.property).symm)

/-- The actual complements of the zero slices in the overlap are homeomorphic. -/
def NormalPairRecenter.ImmersionNormalPair.transitionComplementHomeomorph :
    {z : (P.transition Q).source // z.val.2 ≠ 0} ≃ₜ
      {z : (P.transition Q).target // z.val.2 ≠ 0} :=
  (P.transition Q).toHomeomorphSourceTarget.subtype
    (fun z => (P.transition_preserves_complement Q z.val z.property).symm)

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [ChartedSpace G N]

/-- Restricting a differentiable ambient chart to the verified neighborhood
preserves differentiability of both chart directions. -/
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F)) :
    P.restrictedChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F) := by
  constructor
  · change MDifferentiableOn 𝓘(𝕜, G) 𝓘(𝕜, E × F) P.ambientChart
      (P.ambientChart.source ∩ P.neighborhood)
    exact hP.1.mono inter_subset_left
  · change MDifferentiableOn 𝓘(𝕜, E × F) 𝓘(𝕜, G) P.ambientChart.symm
      (P.ambientChart.target ∩ P.ambientChart.symm ⁻¹' P.neighborhood)
    exact hP.2.mono inter_subset_left

/-- Actual differentiable charts give an actual differentiable transition
on the verified overlap, including a differentiable inverse. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E' × F')) :
    (P.transition Q).MDifferentiable 𝓘(𝕜, E × F) 𝓘(𝕜, E' × F') :=
  (P.restrictedChart_mdifferentiable hP).symm.trans (Q.restrictedChart_mdifferentiable hQ)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairTransition"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition -/

/-! # Immersion Normal Transition -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition

noncomputable section

/-!
# Normal-coordinate transition invariance of actual local rational classes

The genuine transition between two normal pairs preserves their full normal
zero locus. Its proved nonlinear rational-class action gives equality after
shrinking to coordinate balls. Pullback to the corresponding actual ambient
neighborhood then gives equality of the relative-cohomology germs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Analytic.ImmersionNormalPair

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E]
  {f : M → N} {x : M} {p : ℕ}

def normalNeighborhoodBallMap (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) :
    TopCat.of P.neighborhood ⟶
      TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) :=
  (TopCat.isoOfHomeo P.homeomorph).hom ≫
    NormalNeighborhoodRestriction.Cycles.normalProductBallRadiusInclusion E (Fin p → ℂ) hr hs

theorem normalNeighborhoodBallMap_mapsTo
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) (hspos : 0 < s) :
    Set.MapsTo (normalNeighborhoodBallMap P r s hr hs) P.relativeComplement
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hspos)) := by
  intro y hy hzero
  apply (P.mem_complement_iff y).mp hy
  exact congrArg Subtype.val hzero

theorem normalNeighborhoodBallMap_projection
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (r s : ℝ) (hr : P.radius ≤ r) (hs : P.radius ≤ s) :
    normalNeighborhoodBallMap P r s hr hs ≫ NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s =
      P.normalCoordinate := by
  ext y
  rfl

variable [NormedSpace ℝ E] [NormedSpace ℂ E]
variable (P Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- After an actual radius shrinking of the first normal pair, the second
normal-pair class restricts to precisely its normalized rational class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.exists_rationalClassFin_restrict_eq_of_transition
    (he : (P.transition Q).MDifferentiable
      𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ))) :
    ∃ (t : ℝ) (ht : 0 < t) (htP : t ≤ P.radius),
      ∃ (hRQ : (P.restrictRadius t ht htP).neighborhood ⊆ Q.neighborhood),
        RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hRQ (Set.range f) (2 * p)
          Q.rationalClassFin = (P.restrictRadius t ht htP).rationalClassFin := by
  obtain ⟨r, s, hr, hs, hsub, hclass⟩ :=
    RationalNormalSliceAction.Cycles.exists_normalDiffeomorph_rationalClass_pullback (P.transition Q) he
      (P.zero_mem_transition_source Q) (P.transition_zero Q)
      (P.transition_preserves_zero Q)
  let t := min P.radius (min r s)
  have ht : 0 < t := lt_min P.radius_pos (lt_min hr hs)
  have htP : t ≤ P.radius := min_le_left _ _
  have htr : t ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hts : t ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  let T := P.restrictRadius t ht htP
  have hTP : T.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset t ht htP
  have hTQ : T.neighborhood ⊆ Q.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    have hz' := hsub ⟨Metric.ball_subset_ball htr hz.1, Metric.ball_subset_ball hts hz.2⟩
    rw [P.transition_source Q] at hz'
    exact hz'.2
  refine ⟨t, ht, htP, hTQ, ?_⟩
  let b := normalNeighborhoodBallMap T r s htr hts
  have hb := normalNeighborhoodBallMap_mapsTo T r s htr hts hs
  let ψ := NormalSliceLocalAction.Cycles.normalProductBallMap (P.transition Q) r s
    ((P.transition Q).continuousOn.mono hsub)
  have hψ := NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo (P.transition Q) r s hs
    ((P.transition Q).continuousOn.mono hsub) 0
    (fun z hz hne hzero => hne ((P.transition_preserves_zero Q z (hsub hz)).mp hzero))
  let i : TopCat.of T.neighborhood ⟶ TopCat.of Q.neighborhood :=
    LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N)) hTQ
  have hi : Set.MapsTo i T.relativeComplement Q.relativeComplement := fun _ hy => hy
  have hmapQ : (b ≫ ψ) ≫ NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ) = i ≫ Q.normalCoordinate := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change (Q.ambientChart (P.ambientChart.symm (P.ambientChart y.val))).2 =
      (Q.ambientChart y.val).2
    rw [P.ambientChart.left_inv (P.neighborhood_subset_source (hTP y.property))]
  have hcohQ :
      Q.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) ≫
        RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTQ (Set.range f) (2 * p) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
          (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ψ hψ (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p) := by
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Q.normalCoordinate
        Q.normalCoordinate_mapsTo (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i hi (2 * p) = _
    simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    congr 1
    exact hmapQ.symm
  have hcohT :
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
          (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p) =
      T.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
    congr 1
  have hclass' := congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p)) hclass
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback] at hclass'
  change
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ψ hψ (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
        (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) b hb (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) at hclass'
  rw [← hcohQ, hcohT] at hclass'
  rw [Q.rationalClassFin_eq_normalPullback, T.rationalClassFin_eq_normalPullback]
  exact hclass'

/-- Two genuine differentiable normal-coordinate systems at the same
point define the same actual relative-cohomology germ. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_of_transition
    (he : (P.transition Q).MDifferentiable
      𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ))) :
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
      Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin := by
  obtain ⟨t, ht, htP, hTQ, hclass⟩ := P.exists_rationalClassFin_restrict_eq_of_transition Q he
  let T := P.restrictRadius t ht htP
  have hTP : T.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset t ht htP
  calc
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
        T.relativeCohomologyGerm (2 * p)
          (RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTP (Set.range f) (2 * p)
            P.rationalClassFin) :=
      (ConcreteCategory.congr_hom (P.relativeCohomologyGerm_restrict T hTP (2 * p))
        P.rationalClassFin).symm
    _ = T.relativeCohomologyGerm (2 * p) T.rationalClassFin := by
      rw [P.rationalClassFin_restrict T hTP rfl]
    _ = T.relativeCohomologyGerm (2 * p)
        (RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hTQ (Set.range f) (2 * p)
          Q.rationalClassFin) := by rw [hclass]
    _ = Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin :=
      ConcreteCategory.congr_hom (Q.relativeCohomologyGerm_restrict T hTQ (2 * p))
        Q.rationalClassFin

/-- Actual differentiability of both ambient charts supplies the transition
hypothesis of germ invariance. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_of_charts
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ))) :
    P.relativeCohomologyGerm (2 * p) P.rationalClassFin =
      Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin :=
  P.rationalClassFin_germ_eq_of_transition Q (P.transition_mdifferentiable Q hP hQ)

end Analytic.ImmersionNormalPair

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable -/

/-! # Normal Coordinates Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

noncomputable section

/-!
# Differentiability of the constructed normal coordinates

The normal coordinates constructed from a genuine immersion are compositions
of its maximal-atlas charts with a continuous linear equivalence and a
translation. We prove their regularity directly from those constructions.
No regularity is asserted for an arbitrary topological normal-pair structure.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open Set

section

section TangentialTranslations

variable {K E G C N : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup G] [NormedSpace K G]
variable [NormedAddCommGroup C] [NormedSpace K C]
variable [TopologicalSpace N] [ChartedSpace G N]

/-- Translating only the tangential coordinates of an actual differentiable
chart preserves differentiability in both directions. This applies to
recentered normal pairs once the original chart's regularity is proved. -/
theorem mdifferentiable_transHomeomorph_tangentialTranslation
    (c : OpenPartialHomeomorph N (E × C))
    (hc : c.MDifferentiable 𝓘(K, G) 𝓘(K, E × C)) (a : E) :
    (c.transHomeomorph ((Homeomorph.subRight a).prodCongr (Homeomorph.refl C))).MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) := by
  let t : (E × C) ≃ₜ (E × C) :=
    (Homeomorph.subRight a).prodCongr (Homeomorph.refl C)
  have ht : t.toOpenPartialHomeomorph.MDifferentiable 𝓘(K, E × C) 𝓘(K, E × C) := by
    constructor
    · have ht' : ContDiff K 1 (fun z : E × C => (z.1 - a, z.2)) :=
        (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
      exact ht'.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
    · have ht' : ContDiff K 1 (fun z : E × C => (z.1 + a, z.2)) :=
        (contDiff_fst.add contDiff_const).prodMk contDiff_snd
      exact ht'.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact hc.trans ht

namespace ImmersionNormalPair

variable {M : Type*} {f : M → N} {x : M}

/-- Recentering transports a proved ambient-chart differentiability
statement; it does not impose regularity on an arbitrary topological pair. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterChart_mdifferentiable (P : NormalPairRecenter.ImmersionNormalPair E C f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(K, G) 𝓘(K, E × C)) (z : M) :
    (P.recenterChart z).MDifferentiable 𝓘(K, G) 𝓘(K, E × C) :=
  mdifferentiable_transHomeomorph_tangentialTranslation P.ambientChart hP
    (P.ambientChart (f z)).1

/-- The full-image normal pair obtained by recentering and shrinking keeps
the proved differentiability of its ambient coordinates and inverse. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithin_ambientChart_mdifferentiable (P : NormalPairRecenter.ImmersionNormalPair E C f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(K, G) 𝓘(K, E × C))
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) :=
  P.recenterChart_mdifferentiable hP z

end ImmersionNormalPair

end TangentialTranslations

section ConstructedCoordinates

variable {K E G C M N : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup G] [NormedSpace K G]
variable [NormedAddCommGroup C] [NormedSpace K C]
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω} {f : M → N} {x : M}

/-- Centering the immersion's source chart preserves its differentiability
order on the actual source. -/
theorem contMDiffOn_immersionSourceCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E) 𝓘(K, E) n (NormalPairRecenter.immersionSourceCoordinates h)
      (NormalPairRecenter.immersionSourceCoordinates h).source := by
  have ht : ContDiff K n (fun z : E => z - h.domChart x) :=
    contDiff_id.sub contDiff_const
  exact ht.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas)

/-- The inverse centered source chart has the same differentiability order. -/
theorem contMDiffOn_immersionSourceCoordinates_symm
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E) 𝓘(K, E) n (NormalPairRecenter.immersionSourceCoordinates h).symm
      (NormalPairRecenter.immersionSourceCoordinates h).target := by
  have ht : ContDiff K n (fun z : E => z + h.domChart x) :=
    contDiff_id.add contDiff_const
  exact (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
    ht.contMDiff.contMDiffOn (fun _ hz => hz)

/-- The actual split and centered ambient chart is as differentiable as
the genuine immersion chart from which it was constructed. -/
theorem contMDiffOn_immersionNormalCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, G) 𝓘(K, E × C) n (NormalPairRecenter.immersionNormalCoordinates h)
      (NormalPairRecenter.immersionNormalCoordinates h).source := by
  have ht : ContDiff K n (fun z : G =>
      ((h.equiv.symm z).1 - h.domChart x, (h.equiv.symm z).2)) :=
    (h.equiv.symm.contDiff.fst.sub contDiff_const).prodMk h.equiv.symm.contDiff.snd
  exact ht.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)

/-- Its actual inverse is also differentiable on the complete chart target. -/
theorem contMDiffOn_immersionNormalCoordinates_symm
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E × C) 𝓘(K, G) n (NormalPairRecenter.immersionNormalCoordinates h).symm
      (NormalPairRecenter.immersionNormalCoordinates h).target := by
  have ht : ContDiff K n (fun z : E × C => h.equiv (z.1 + h.domChart x, z.2)) :=
    h.equiv.contDiff.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  exact (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
    ht.contMDiff.contMDiffOn (fun _ hz => hz)

/-- A positive-order source chart is a genuine differentiable local
homeomorphism, with differentiable inverse. -/
theorem immersionSourceCoordinates_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hn : n ≠ 0) :
    (NormalPairRecenter.immersionSourceCoordinates h).MDifferentiable 𝓘(K, E) 𝓘(K, E) :=
  ⟨(contMDiffOn_immersionSourceCoordinates h).mdifferentiableOn hn,
    (contMDiffOn_immersionSourceCoordinates_symm h).mdifferentiableOn hn⟩

/-- Positive-order normal coordinates are genuine differentiable local
homeomorphisms in both directions. -/
theorem immersionNormalCoordinates_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hn : n ≠ 0) :
    (NormalPairRecenter.immersionNormalCoordinates h).MDifferentiable 𝓘(K, G) 𝓘(K, E × C) :=
  ⟨(contMDiffOn_immersionNormalCoordinates h).mdifferentiableOn hn,
    (contMDiffOn_immersionNormalCoordinates_symm h).mdifferentiableOn hn⟩

/-- The ambient chart of the actual full-image normal pair inherits the
proved differentiability; the embedding only selects its radius. -/
theorem normalPairOfImmersion_ambientChart_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) :
    (NormalPairRecenter.normalPairOfImmersion h hf).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) :=
  immersionNormalCoordinates_mdifferentiable h hn

/-- The same statement for the actual complement chosen by `IsImmersionAt`. -/
theorem immersionNormalPair_ambientChart_mdifferentiable
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, G) n f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) :
    (NormalPairRecenter.immersionNormalPair h hf).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × h.complement) :=
  normalPairOfImmersion_ambientChart_mdifferentiable
    h.isImmersionAtOfComplement_complement hf hn

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace K D] {m : ℕ∞ω}

/-- The transition on the verified overlap of two actual immersion normal
pairs is differentiable with a differentiable inverse. The two normal
coordinate models may be different. -/
theorem normalPairOfImmersion_transition_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0) :
    ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf)).MDifferentiable
      𝓘(K, E × C) 𝓘(K, E × D) :=
  NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable
    (NormalPairRecenter.normalPairOfImmersion h hf) (NormalPairRecenter.normalPairOfImmersion k hf)
    (normalPairOfImmersion_ambientChart_mdifferentiable h hf hn)
    (normalPairOfImmersion_ambientChart_mdifferentiable k hf hm)

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of the actual transition derivative follows from the
proved differentiability of the actual inverse, with no chosen linear map. -/
theorem normalPairOfImmersion_transition_fderiv_bijective
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0) :
    Function.Bijective
      (fderiv K ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf))
        (0, 0)) := by
  have hd := normalPairOfImmersion_transition_mdifferentiable h k hf hn hm
  let L : (E × C) ≃L[K] (E × D) := hd.mfderiv
    ((NormalPairRecenter.normalPairOfImmersion h hf).zero_mem_transition_source (NormalPairRecenter.normalPairOfImmersion k hf))
  have hL : L.toContinuousLinearMap =
      fderiv K ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf))
        (0, 0) := mfderiv_eq_fderiv
  have hb : Function.Bijective L.toContinuousLinearMap := L.bijective
  rwa [hL] at hb

/-- At an arbitrary shared image point of two genuine normal pairs,
recentering inside the overlap gives a differentiable coordinate transition
with differentiable inverse. All chart regularity comes from the immersion. -/
theorem normalPairOfImmersion_recentered_transition_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    {y : M} (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f y)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0)
    (z : M) (hz : f z ∈ (NormalPairRecenter.normalPairOfImmersion h hf).neighborhood)
    (hz' : f z ∈ (NormalPairRecenter.normalPairOfImmersion k hf).neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (((NormalPairRecenter.normalPairOfImmersion h hf).recenterWithin z hz U hU).transition
      ((NormalPairRecenter.normalPairOfImmersion k hf).recenterWithin z hz' U hU)).MDifferentiable
      𝓘(K, E × C) 𝓘(K, E × D) :=
  NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable _ _
    ((NormalPairRecenter.normalPairOfImmersion h hf).recenterWithin_ambientChart_mdifferentiable
      (normalPairOfImmersion_ambientChart_mdifferentiable h hf hn) z hz U hU)
    ((NormalPairRecenter.normalPairOfImmersion k hf).recenterWithin_ambientChart_mdifferentiable
      (normalPairOfImmersion_ambientChart_mdifferentiable k hf hm) z hz' U hU)

end ConstructedCoordinates

end

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalRecenter -/

/-! # Immersion Normal Recenter -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Normal cohomology classes under genuine recentering

Recentering translates only the tangential coordinate and shrinks the
verified normal neighborhood. Its normal coordinate is unchanged. Actual
relative cohomology pullback therefore identifies the recentered rational
class with restriction of the original class, and the two give the same
germ at the new center.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace Filter
open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The actual recentered neighborhood is contained in the original one. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithin_neighborhood_subset_original
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).neighborhood ⊆ P.neighborhood :=
  (P.recenterWithin_neighborhood_subset z hz U hU).trans Set.inter_subset_left

/-- Inclusion from the genuine recentered neighborhood preserves the
actual normal-coordinate map. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_comp_recenterWithin_inclusion
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N))
        (P.recenterWithin_neighborhood_subset_original z hz U hU) ≫
          P.normalCoordinate = (P.recenterWithin z hz U hU).normalCoordinate := by
  ext y
  change (P.ambientChart y.val).2 =
    ((P.recenterWithin z hz U hU).ambientChart y.val).2
  exact (P.recenterWithin_normalCoordinate z hz U hU y.val).symm

/-- Restriction between the actual relative cohomology groups of the
original and recentered normal neighborhoods. -/
abbrev ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithinCohomologyRestriction
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ⟶
      (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ) n :=
  CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N)
    (P.recenterWithin_neighborhood_subset_original z hz U hU) (Set.range f) n

/-- This restriction is exactly the map of the existing relative
cohomology presheaf, with the complement of the same full image. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithinCohomologyRestriction_eq_presheaf
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.recenterWithinCohomologyRestriction z hz U hU n =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).map
        (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤
          P.openNeighborhood from P.recenterWithin_neighborhood_subset_original z hz U hU)).op :=
  rfl

/-- The actual normal pullback commutes with restriction to the recentered
neighborhood in every cohomological degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
        P.recenterWithinCohomologyRestriction z hz U hU n =
      (P.recenterWithin z hz U hU).normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) P.normalCoordinate
      P.normalCoordinate_mapsTo n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N))
        (P.recenterWithin_neighborhood_subset_original z hz U hU))
      (fun _ hy => hy) n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  congr 1

variable [NormedSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual recentered rational class is restriction of the original
class because both are pullbacks of the same normalized normal class. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    P.recenterWithinCohomologyRestriction z hz U hU (2 * Module.finrank ℂ F)
        P.rationalClass = (P.recenterWithin z hz U hU).rationalClass := by
  rw [P.rationalClass_eq_pullback, (P.recenterWithin z hz U hU).rationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_recenterWithin z hz U hU (2 * Module.finrank ℂ F))
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)

/-- Recentering does not change the actual relative-cohomology germ at
the new center, even when the original pair was centered elsewhere. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_germ_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * Module.finrank ℂ F)).germ P.openNeighborhood (f z) hz P.rationalClass =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * Module.finrank ℂ F)).germ (P.recenterWithin z hz U hU).openNeighborhood
        (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood
          (P.recenterWithin z hz U hU).rationalClass := by
  have h := (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
    (2 * Module.finrank ℂ F)).germ_res_apply
      (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤ P.openNeighborhood
        from P.recenterWithin_neighborhood_subset_original z hz U hU))
      (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood P.rationalClass
  exact h.symm.trans (congrArg
    (fun c : (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ)
        (2 * Module.finrank ℂ F) =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * Module.finrank ℂ F)).germ (P.recenterWithin z hz U hU).openNeighborhood
          (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood c)
    (P.rationalClass_recenterWithin z hz U hU))

end

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- In the explicit degree `2p`, the actual recentered normalized class
is still precisely the restriction of the original normalized class. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    P.recenterWithinCohomologyRestriction z hz U hU (2 * p)
      P.rationalClassFin = (P.recenterWithin z hz U hU).rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback,
    (P.recenterWithin z hz U hU).rationalClassFin_eq_normalPullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_recenterWithin z hz U hU (2 * p))
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- The actual relative-cohomology germ in degree `2p` is unchanged by
recentering at any image point of the verified normal neighborhood. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ P.openNeighborhood (f z) hz P.rationalClassFin =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ (P.recenterWithin z hz U hU).openNeighborhood
        (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood
          (P.recenterWithin z hz U hU).rationalClassFin := by
  have h := (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
    (2 * p)).germ_res_apply
      (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤ P.openNeighborhood
        from P.recenterWithin_neighborhood_subset_original z hz U hU))
      (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood P.rationalClassFin
  exact h.symm.trans (congrArg
    (fun c : (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * p)).germ (P.recenterWithin z hz U hU).openNeighborhood
          (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood c)
    (P.rationalClassFin_recenterWithin z hz U hU))

variable [NormedSpace ℂ E]

/-- At every image point in an actual overlap, two differentiable normal
pairs give the same relative-cohomology germ, even if their original
centers differ. Both are genuinely recentered and shrunk into the overlap
before applying the checked same-center transition theorem. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_on_overlap
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    {y : M} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f y)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (z : M) (hzP : f z ∈ P.neighborhood) (hzQ : f z ∈ Q.neighborhood) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ P.openNeighborhood (f z) hzP P.rationalClassFin =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ Q.openNeighborhood (f z) hzQ Q.rationalClassFin := by
  let W := P.neighborhood ∩ Q.neighborhood
  have hW : W ∈ 𝓝 (f z) :=
    (P.isOpen_neighborhood.inter Q.isOpen_neighborhood).mem_nhds ⟨hzP, hzQ⟩
  let Pz := P.recenterWithin z hzP W hW
  let Qz := Q.recenterWithin z hzQ W hW
  have hPz : Pz.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) :=
    P.recenterWithin_ambientChart_mdifferentiable hP z hzP W hW
  have hQz : Qz.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) :=
    Q.recenterWithin_ambientChart_mdifferentiable hQ z hzQ W hW
  exact (P.rationalClassFin_germ_recenterWithin z hzP W hW).trans
    ((Pz.rationalClassFin_germ_eq_of_charts Qz hPz hQz).trans
      (Q.rationalClassFin_germ_recenterWithin z hzQ W hW).symm)

end

end OAI.AlgebraicGeometry
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalRecenter"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso -/

/-! # Sheaf Quasi Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

noncomputable section

/-!
# Quasi-isomorphisms of module sheaf complexes and stalks

The stalk functors on module sheaves are exact and jointly detect isomorphisms.
Consequently a morphism of complexes of sheaves is a quasi-isomorphism exactly
when it is a quasi-isomorphism on every stalk. The comparison with sheafified
presheaf complexes is induced by the actual sheafification unit in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- Module limits exist in the carrier universe even when the scalars lie in
the smaller universe. -/
local instance sheafQuasiIsoModuleLimits :
    HasLimitsOfSize.{u,u} (ModuleCat.{u,0} R) :=
  ModuleCat.hasLimitsOfSize.{u,u,u,0}

/-- The complex formed by the actual stalks of a complex of module sheaves. -/
def sheafStalkCochainComplex
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ) (x : X) :
    CochainComplex (ModuleCat.{u,0} R) ℕ :=
  (((TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

/-- The morphism on actual stalk complexes induced by a sheaf complex morphism. -/
def sheafStalkCochainMap
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (x : X) :
    sheafStalkCochainComplex K x ⟶ sheafStalkCochainComplex L x :=
  ((TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).map f

/-- Exactness of the sheaf stalk functor gives the canonical homology comparison. -/
def sheafStalkCohomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ) (x : X) (n : ℕ) :
    (sheafStalkCochainComplex K x).homology n ≅
      (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
        stalkFunctor (ModuleCat.{u,0} R) x).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙
    stalkFunctor (ModuleCat.{u,0} R) x)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk--cohomology comparison intertwines the genuine induced maps. -/
@[reassoc]
theorem sheafStalkCohomologyIso_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (x : X) (n : ℕ) :
    HomologicalComplex.homologyMap (sheafStalkCochainMap f x) n ≫
        (sheafStalkCohomologyIso L x n).hom =
      (sheafStalkCohomologyIso K x n).hom ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (HomologicalComplex.homologyMap f n).hom :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (TopCat.Sheaf.forget (ModuleCat.{u,0} R) X ⋙ stalkFunctor (ModuleCat.{u,0} R) x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sheaf complex morphism induces an isomorphism in degree `n` exactly when
it does so on every actual stalk complex. -/
theorem sheaf_quasiIsoAt_iff_stalk
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    QuasiIsoAt f n ↔ ∀ x : X, QuasiIsoAt (sheafStalkCochainMap f x) n := by
  rw [quasiIsoAt_iff_isIso_homologyMap,
    TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  apply forall_congr'
  intro x
  rw [quasiIsoAt_iff_isIso_homologyMap]
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using
    (congrArg IsIso (sheafStalkCohomologyIso_naturality f x n)).to_iff.symm

/-- A morphism of module sheaf complexes is a quasi-isomorphism if and only
if the induced morphism of complexes at every stalk is a quasi-isomorphism. -/
theorem sheaf_quasiIso_iff_stalk
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ}
    (f : K ⟶ L) :
    QuasiIso f ↔ ∀ x : X, QuasiIso (sheafStalkCochainMap f x) := by
  simp only [quasiIso_iff, sheaf_quasiIsoAt_iff_stalk]
  exact forall_comm

/-- Apply the actual sheafification functor in every cochain degree. -/
def sheafifiedCochainComplex
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} R) X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual sheafification unit induces a map from a presheaf stalk complex
to the stalk complex of its sheafification. -/
def sheafificationStalkComplexHom
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ⟶
      sheafStalkCochainComplex (sheafifiedCochainComplex K) x where
  f n := (stalkFunctor (ModuleCat.{u,0} R) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n))
  comm' i j _ := by
    symm
    change (stalkFunctor (ModuleCat.{u,0} R) x).map (K.d i j) ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X j)) =
      (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X i)) ≫
        (stalkFunctor (ModuleCat.{u,0} R) x).map
          (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (K.d i j))
    rw [← Functor.map_comp, ← Functor.map_comp,
      CategoryTheory.toSheafify_naturality]

/-- Sheafification preserves each stalk, so the induced map of stalk complexes
is already an isomorphism of complexes. -/
instance sheafificationStalkComplexHom_isIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    IsIso (sheafificationStalkComplexHom K x) := by
  have : ∀ n : ℕ, IsIso ((sheafificationStalkComplexHom K x).f n) :=
    fun n => stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u,0} R) (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical comparison of presheaf and sheafification stalk complexes,
whose forward map comes from the sheafification unit. -/
def sheafificationStalkComplexIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ≅
      sheafStalkCochainComplex (sheafifiedCochainComplex K) x :=
  asIso (sheafificationStalkComplexHom K x)

@[simp]
theorem sheafificationStalkComplexIso_hom_f
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) (n : ℕ) :
    (sheafificationStalkComplexIso K x).hom.f n =
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk comparison for sheafification is natural in the presheaf complex. -/
@[reassoc]
theorem sheafificationStalkComplexIso_naturality
    {K L : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ}
    (f : K ⟶ L) (x : X) :
    ((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f ≫ (sheafificationStalkComplexIso L x).hom =
      (sheafificationStalkComplexIso K x).hom ≫
        sheafStalkCochainMap
          (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) x := by
  ext n : 1
  change (stalkFunctor (ModuleCat.{u,0} R) x).map (f.f n) ≫
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (L.X n)) =
    (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) ≫
      (stalkFunctor (ModuleCat.{u,0} R) x).map
        (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (f.f n))
  rw [← Functor.map_comp, ← Functor.map_comp, CategoryTheory.toSheafify_naturality]

/-- The comparison sends the germ of a section to the germ of its actual image
under the sheafification unit. -/
theorem sheafificationStalkComplexIso_hom_germ
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ)
    (x : X) (n : ℕ) (U : Opens X) (hx : x ∈ U) (s : (K.X n).obj (op U)) :
    (sheafificationStalkComplexIso K x).hom.f n ((K.X n).germ U x hx s) =
      TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology X) (K.X n)) U x hx
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)).app (op U) s) :=
  stalkFunctor_map_germ_apply U x hx
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n)) s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheafifying a morphism of module presheaf complexes gives a
quasi-isomorphism exactly when the original morphism is one on every stalk. -/
theorem sheafified_quasiIso_iff_stalk
    {K L : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ} (f : K ⟶ L) :
    QuasiIso (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f) ↔
      ∀ x : X, QuasiIso (((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f) := by
  rw [sheaf_quasiIso_iff_stalk]
  apply forall_congr'
  intro x
  rw [← quasiIso_iff_comp_left (sheafificationStalkComplexIso K x).hom,
    ← sheafificationStalkComplexIso_naturality,
    quasiIso_iff_comp_right]

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso"


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
    (`OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafified_quasiIso_iff_stalk, "theorem")
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
    ("nonce", toJson "a9959768a50238327f202c47afbd5cd4"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:a9959768a50238327f202c47afbd5cd4"
