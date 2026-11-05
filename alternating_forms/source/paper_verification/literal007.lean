module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import paper_verification.literal006
public import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import paper_verification.literal002
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import paper_verification.literal003
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import paper_verification.literal005
public import paper_verification.literal001
import Lean.Elab.Tactic.Omega
public import paper_verification.literal000
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import paper_verification.literal004
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.FieldSimp
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Sort

set_option Elab.async false

section TAF_LiteralSource_0409
/- Original module: TauCeti.RepresentationTheory.Continuous.Subrepresentation -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Restricting a continuous representation to an invariant submodule

This file restricts a continuous representation of a monoid to a submodule preserved by every
action operator, the continuous counterpart of Mathlib's `Representation.subrepresentation`, and
descends it to the quotient by such a submodule, the continuous counterpart of
`Representation.quotient`.

## Main definitions

* `ContRepresentation.subrepresentation`: the restriction of a continuous representation to
  an invariant submodule.
* `ContRepresentation.subrepresentationInclusion`: the continuous intertwiner including a
  subrepresentation into its ambient representation.
* `ContRepresentation.quotient`: a continuous representation descended to the quotient by an
  invariant submodule, the continuous counterpart of `Representation.quotient`.

## Main results

* `Subrepresentation.contRepresentation_apply_mem_toSubmodule`: a subrepresentation of the
  underlying representation is stable under the continuous operators.
* `ContRepresentation.mem_invariants_subrepresentation`: a vector of the submodule is
  invariant for the restricted representation exactly when it is invariant for the ambient one.
* `ContRepresentation.toRepresentation_subrepresentation`: the underlying representation of
  a restricted continuous representation is the restriction of the underlying representation.
* `Subrepresentation.toRepresentation_subrepresentation_toSubmodule`: restricting to the
  submodule a subrepresentation carries has that subrepresentation's own representation underneath.
* `ContRepresentation.toRepresentation_quotient`: the underlying representation of a descended
  continuous representation is the descended underlying representation.
* `ContRepresentation.continuous_subrepresentation`: the restriction of a continuous
  representation to an invariant submodule is again continuous.
-/

public section

namespace ContRepresentation

section Restriction

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- The restriction of a continuous representation to an invariant submodule. This is the
continuous counterpart of `Representation.subrepresentation`. -/
def subrepresentation (π : ContRepresentation R G V) (W : Submodule R V)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContRepresentation R G W :=
  .ofMonoidHom
    { toFun g := (π g).restrict (hW g)
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }

variable {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- The restricted action is the ambient action, read on the underlying vectors. -/
@[simp]
theorem coe_subrepresentation_apply (g : G) (v : W) :
    ((subrepresentation π W hW g v : W) : V) = π g (v : V) :=
  (rfl)

/-- A subrepresentation of the underlying representation of `π` is stable under the continuous
operators `π g`. This is `Subrepresentation.apply_mem_toSubmodule` with `π.toRepresentation g`
read as `π g`, in the shape of the stability hypothesis of `ContRepresentation.subrepresentation`;
the two operators agree only after unfolding `ContRepresentation.toRepresentation`, so passing this
lemma, rather than `Subrepresentation.apply_mem_toSubmodule` itself, keeps the restricted
representation type-correct at the transparency at which `rw` and `simp` check their motives. -/
theorem _root_.Subrepresentation.contRepresentation_apply_mem_toSubmodule
    (σ : Subrepresentation π.toRepresentation) (g : G) (v : V) (hv : v ∈ σ.toSubmodule) :
    π g v ∈ σ.toSubmodule :=
  σ.apply_mem_toSubmodule g hv

/-- The inclusion of a subrepresentation into its ambient continuous representation, packaged as a
continuous intertwiner. -/
noncomputable def subrepresentationInclusion
    (π : ContRepresentation R G V) (σ : Subrepresentation π.toRepresentation) :
    ContIntertwiningMap
      (subrepresentation π σ.toSubmodule
        (fun g _ hv ↦ σ.apply_mem_toSubmodule g hv)) π :=
  { toContinuousLinearMap := σ.toSubmodule.subtypeL
    isIntertwining' := fun g ↦ by
      ext v
      rfl }

/-- The subrepresentation inclusion sends a vector to the same vector in the ambient space. -/
@[simp]
theorem subrepresentationInclusion_apply (π : ContRepresentation R G V)
    (σ : Subrepresentation π.toRepresentation) (v : σ.toSubmodule) :
    π.subrepresentationInclusion σ v = (v : V) :=
  (rfl)

-- Not `@[simp]`: Mathlib's `@[simp] ContRepresentation.mem_invariants` already rewrites the
-- left-hand side to `∀ g, subrepresentation π W hW g x = x`, so the attribute would be a `simpNF`
-- violation ("Left-hand side simplifies … using `ContRepresentation.mem_invariants`"). This is the
-- `rw`-usable form of that normalization, as `ContRepresentation.mem_invariants_restrict` is for
-- the restriction along a subgroup.
/-- A vector of an invariant submodule is invariant for the restricted representation exactly when
it is invariant for the ambient one: the restricted action is the ambient action. -/
theorem mem_invariants_subrepresentation {x : W} :
    x ∈ (subrepresentation π W hW).invariants ↔ (x : V) ∈ π.invariants := by
  simp [ContRepresentation.mem_invariants, Subtype.ext_iff]

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
theorem toRepresentation_subrepresentation : (subrepresentation π W hW).toRepresentation
      = π.toRepresentation.subrepresentation W fun g _ hv => hW g _ hv := by
  rfl

-- Not `@[simp]`: `toRepresentation_subrepresentation` already rewrites the left-hand side to
-- `π.toRepresentation.subrepresentation σ.toSubmodule _`, so the attribute would be a `simpNF`
-- violation. This is the one-step form, which is what an argument about a subrepresentation of
-- `π.toRepresentation` needs.
/-- Restricting `π` to the submodule a subrepresentation `σ` of `π.toRepresentation` carries has
`σ.toRepresentation` as its underlying representation: both restrict the ambient action to the
same submodule. -/
theorem _root_.Subrepresentation.toRepresentation_subrepresentation_toSubmodule
    (σ : Subrepresentation π.toRepresentation) :
    (subrepresentation π σ.toSubmodule
      (fun g _ hv ↦ σ.apply_mem_toSubmodule g hv)).toRepresentation = σ.toRepresentation := by
  exact toRepresentation_subrepresentation.trans (by ext g v; rfl)

end Restriction

section Quotient

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- A continuous representation descended to the quotient by an invariant submodule, which
carries the quotient topology. This is the continuous counterpart of `Representation.quotient`. -/
def quotient (π : ContRepresentation R G V) (W : Submodule R V)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContRepresentation R G (V ⧸ W) :=
  .ofMonoidHom
    { toFun g := W.liftQL (W.mkQL ∘L π g) fun v hv ↦ by simpa using hW g v hv
      map_one' := by
        ext v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        simp
      map_mul' g h := by
        ext v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        simp }

variable {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- The descended action on the class of `v` is the class of the ambient action on `v`. -/
@[simp]
theorem quotient_apply_mk (g : G) (v : V) :
    quotient π W hW g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π g v) :=
  (rfl)

/-- The underlying representation of a descended continuous representation is the descended
underlying representation. -/
@[simp]
theorem toRepresentation_quotient : (quotient π W hW).toRepresentation
      = π.toRepresentation.quotient W fun g _ hv => hW g _ hv := by
  ext g v
  rfl

end Quotient

section Continuity

variable {𝕜 G V : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V] [ContinuousConstSMul 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {W : Submodule 𝕜 V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a continuous representation to an invariant submodule preserves continuity: from
continuity of `g ↦ π g` as a map into the continuous linear endomorphisms of `V`, the restricted
action `g ↦ subrepresentation π W hW g` is continuous into those of `W`. This supplies the
continuity argument that `matrixCoeff` and the rest of the continuous-representation API take
explicitly, so a subrepresentation can be used wherever a continuous representation is expected. -/
theorem continuous_subrepresentation (hπ : Continuous π) :
    Continuous (subrepresentation π W hW) := by
  rw [(ContinuousLinearMap.isInducing_postcomp W.subtypeL
    Topology.IsInducing.subtypeVal).continuous_iff]
  exact (ContinuousLinearMap.precomp V W.subtypeL).continuous.comp hπ

end Continuity

end ContRepresentation
end
end TAF_LiteralSource_0409

section TAF_LiteralSource_0410
/- Original module: TauCeti.RepresentationTheory.Continuous.Unitary.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Unitary continuous representations

This file defines when a continuous representation preserves a real or complex inner product. It
characterizes unitarity through norm preservation, isometries, and Mathlib's `unitary` submonoid of
continuous linear operators, and records the basic inner-product identities, the coefficient bound,
and that unitarity passes to restrictions.

The operator characterizations reuse Mathlib's adjoint and unitary-operator theory.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- Applying a continuous group representation at an element and then at its inverse cancels.

This restates `Representation.self_inv_apply` for the continuous action coercion, which `simp` does
not otherwise reach; it is an implementation detail of the inverse-transfer proofs below. -/
private theorem self_inv_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π g (π g⁻¹ v) = v :=
  Representation.self_inv_apply π.toRepresentation g v

section Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- A continuous representation is unitary when every action operator preserves the inner
product. -/
def IsUnitary (π : ContRepresentation 𝕜 G V) : Prop :=
  ∀ g v w, ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜

/-- A representation is unitary exactly when every action map preserves norms. -/
theorem isUnitary_iff_norm_map (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g v, ‖π g v‖ = ‖v‖ := by
  constructor
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mpr (hπ g)
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mp (hπ g)

/-- A representation is unitary exactly when every action map is an isometry. -/
theorem isUnitary_iff_isometry (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g, Isometry (π g) := by
  rw [isUnitary_iff_norm_map]
  exact forall_congr' fun g ↦ (AddMonoidHomClass.isometry_iff_norm (π g)).symm

namespace IsUnitary

variable {π : ContRepresentation 𝕜 G V}

/-- A unitary representation preserves the inner product. -/
@[simp]
theorem inner_map_map (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜 :=
  hπ g v w

/-- Every action map of a unitary representation preserves norms. -/
@[simp]
theorem norm_map (hπ : IsUnitary π) (g : G) (v : V) :
    ‖π g v‖ = ‖v‖ :=
  (isUnitary_iff_norm_map π).mp hπ g v

/-- Every action operator of a unitary representation has operator norm at most `1`. -/
theorem norm_le_one (hπ : IsUnitary π) (g : G) : ‖π g‖ ≤ 1 :=
  (π g).opNorm_le_bound zero_le_one fun v ↦ by simp [hπ.norm_map]

/-- The action operators of a unitary representation are uniformly bounded, in the form taken
by the integrated-form API. -/
theorem exists_norm_le (hπ : IsUnitary π) : ∃ C, ∀ g, ‖π g‖ ≤ C :=
  ⟨1, hπ.norm_le_one⟩

/-- Every action map of a unitary representation is an isometry. -/
theorem isometry (hπ : IsUnitary π) (g : G) : Isometry (π g) :=
  (isUnitary_iff_isometry π).mp hπ g

/-- Every action map of a unitary representation is injective. -/
theorem injective (hπ : IsUnitary π) (g : G) : Function.Injective (π g) :=
  (hπ.isometry g).injective

/-- Restriction along a monoid homomorphism preserves unitarity. -/
theorem restrict {H : Type*} [Monoid H] (hπ : IsUnitary π) (φ : H →* G) :
    IsUnitary (π.restrict φ) :=
  fun h ↦ hπ (φ h)

/-- The restriction of a unitary representation to an invariant submodule is unitary. -/
theorem subrepresentation (hπ : IsUnitary π) {W : Submodule 𝕜 V}
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : IsUnitary (subrepresentation π W hW) :=
  (isUnitary_iff_norm_map _).mpr fun g v => by
    rw [← Submodule.norm_coe, ← Submodule.norm_coe (s := W) v, coe_subrepresentation_apply,
      hπ.norm_map]

/-- A matrix coefficient of a unitary representation is bounded by the product of the vector
norms. -/
theorem norm_inner_map_le (hπ : IsUnitary π) (g : G) (v w : V) :
    ‖⟪π g v, w⟫_𝕜‖ ≤ ‖v‖ * ‖w‖ := by
  calc
    ‖⟪π g v, w⟫_𝕜‖ ≤ ‖π g v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = ‖v‖ * ‖w‖ := by rw [hπ.norm_map]

section

variable [CompleteSpace V]

/-- The adjoint of a unitary action operator is a left inverse. -/
theorem adjoint_comp_self (hπ : IsUnitary π) (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp (π g) = 1 :=
  (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)

end

end IsUnitary

/-- The trivial continuous representation is unitary. -/
theorem isUnitary_trivial :
    IsUnitary (ContRepresentation.trivial 𝕜 G V) := by
  intro _ v w
  simp

end Monoid

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {π : ContRepresentation 𝕜 G V}

/-- For a group representation, inner-product preservation is equivalent to every action operator
belonging to Mathlib's unitary submonoid. -/
theorem isUnitary_iff_mem_unitary (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g, π g ∈ unitary (V →L[𝕜] V) := by
  constructor
  · intro hπ g
    apply ((Group.isUnit g).map π.toMonoidHom).mem_unitary_of_star_mul_self
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)
  · intro hπ g v w
    exact (π g).inner_map_map_of_mem_unitary (hπ g) v w

namespace IsUnitary

/-- Every action operator of a unitary group representation belongs to Mathlib's `unitary`
submonoid. -/
theorem mem_unitary (hπ : IsUnitary π) (g : G) :
    π g ∈ unitary (V →L[𝕜] V) :=
  (isUnitary_iff_mem_unitary π).mp hπ g

/-- The adjoint of a unitary action operator is a right inverse. -/
theorem self_comp_adjoint (hπ : IsUnitary π) (g : G) :
    (π g).comp (ContinuousLinearMap.adjoint (π g)) = 1 := by
  rw [← ContinuousLinearMap.mul_def]
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    Unitary.mul_star_self_of_mem (hπ.mem_unitary g)

omit [CompleteSpace V] in
/-- Moving a unitary action from the first inner-product argument to the second replaces the group
element by its inverse. -/
theorem inner_map_left (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, w⟫_𝕜 = ⟪v, π g⁻¹ w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g v (π g⁻¹ w)

omit [CompleteSpace V] in
/-- Moving a unitary action from the second inner-product argument to the first replaces the group
element by its inverse. -/
theorem inner_map_right (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪v, π g w⟫_𝕜 = ⟪π g⁻¹ v, w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g (π g⁻¹ v) w

/-- The adjoint of a unitary action operator is the action of the inverse group element. -/
@[simp]
theorem adjoint_eq_inv (hπ : IsUnitary π) (g : G) :
    ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simpa using hπ.inner_map_left g⁻¹ v w

end IsUnitary

end Group

end ContRepresentation
end
end TAF_LiteralSource_0410

section TAF_LiteralSource_0411
/- Original module: TauCeti.RepresentationTheory.Compact.Unitarizable -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Weyl's unitarian trick

Averaging the inner product of a Hilbert space over a compact group turns it into a
`G`-invariant inner product. This file carries out that averaging for a continuous representation
`π` of a compact group. Rather than producing a second
`InnerProductSpace` structure on `V` — which would not make the given `π` unitary for the fixed
instance Lean already has — the averaged form is represented by its Gram operator

`gramOperator π hπ = ∫ g, (π g)† ∘ (π g) ∂(haarProb G)`,

a positive-definite self-adjoint operator satisfying `⟪v, S w⟫ = ∫ g, ⟪π g v, π g w⟫`. Invariance
of the averaged form is then the operator identity `(π g)† ∘ S ∘ (π g) = S`.

## Main definitions

* `ContRepresentation.gramOperator`: the Gram operator of the Haar-averaged inner product.

## Main statements

* `ContRepresentation.inner_gramOperator`: the defining property
  `⟪v, S w⟫ = ∫ g, ⟪π g v, π g w⟫`.
* `ContRepresentation.isSelfAdjoint_gramOperator` and
  `ContRepresentation.isPositive_gramOperator`: the Gram operator is self-adjoint and
  positive.
* `ContRepresentation.re_inner_gramOperator_self_pos`: it is positive *definite*; the
  stronger quantitative bound is
  `ContRepresentation.exists_pos_mul_norm_sq_le_re_inner_gramOperator`,
  which bounds the averaged form below by a positive multiple of the original norm square.
* `ContRepresentation.inner_gramOperator_map_map`: the averaged form is `G`-invariant,
  and `ContRepresentation.adjoint_comp_gramOperator_comp` is its operator form.
* `ContRepresentation.isUnitarizable`: the existence of an invariant positive-definite
  self-adjoint operator.
* `ContRepresentation.gramOperator_eq_one`: for an already unitary representation the
  averaging changes nothing.

This is the compact-group replacement for the invertibility of `|G|` in Maschke's theorem. The
invariant-complement and complete-reducibility results of
`TauCeti.RepresentationTheory.Continuous.InvariantComplement` take `IsUnitary` as a hypothesis; this
file does not discharge that hypothesis, but the invariant form built here is the input a
unitarization construction needs. `TauCeti.RepresentationTheory.Compact.UnitaryModel` carries that
construction out in finite dimensions, conjugating `π` into a representation that is unitary for
the inner product `V` was given.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory RCLike TauCeti
open scoped InnerProductSpace

namespace ContRepresentation

section NormedField

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace G]
  [CompactSpace G] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The action operators of a continuous representation of a compact group are uniformly
bounded below: there is a `c > 0` with `c * ‖v‖ ≤ ‖π g v‖` for every `g` and `v`.

The bound comes from applying the inverse operator `π g⁻¹`, whose norm is bounded uniformly in `g`
because `G` is compact and `π` is continuous. Only the seminormed-space structure is involved,
so this is stated before the inner product enters. -/
theorem exists_pos_mul_norm_le_norm_map (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : G) (v : V), c * ‖v‖ ≤ ‖π g v‖ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := fun g : G ↦ π g)
    hπ.continuousOn
  set M' := max M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M'⁻¹, inv_pos.mpr hM'pos, fun g v ↦ ?_⟩
  have hcancel : π g⁻¹ (π g v) = v := Representation.inv_self_apply π.toRepresentation g v
  have hstep : ‖v‖ ≤ M' * ‖π g v‖ :=
    calc ‖v‖ = ‖π g⁻¹ (π g v)‖ := by rw [hcancel]
      _ ≤ ‖π g⁻¹‖ * ‖π g v‖ := (π g⁻¹).le_opNorm _
      _ ≤ M' * ‖π g v‖ :=
        mul_le_mul_of_nonneg_right ((hM g⁻¹ (Set.mem_univ _)).trans (le_max_left _ _))
          (norm_nonneg _)
  rw [inv_mul_le_iff₀ hM'pos]
  exact hstep

end NormedField

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- The family `g ↦ (π g)† ∘ (π g)` of positive operators, as a continuous map on the group.

This is the integrand of the unitarian trick: its value at `g` is the Gram operator of the
pulled-back form `(v, w) ↦ ⟪π g v, π g w⟫`. -/
private noncomputable def gramFamily : C(G, V →L[𝕜] V) where
  toFun g := (ContinuousLinearMap.adjoint (π g)).comp (π g)
  continuous_toFun :=
    (ContinuousLinearMap.compL 𝕜 V V V).continuous₂.comp
      (((ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := V) (F := V)).continuous.comp hπ).prodMk hπ)

/-- The Gram operator of the Haar-averaged inner product
`⟪v, w⟫_G = ∫ g, ⟪π g v, π g w⟫ ∂(haarProb G)` of a continuous representation of a compact group.

The averaged form is recorded through this operator rather than as a second
`InnerProductSpace` structure: Lean fixes one inner product on `V`, and it is the operator identity
`(π g)† ∘ gramOperator π hπ ∘ (π g) = gramOperator π hπ` that expresses `G`-invariance of the
averaged form. The real scalar action needed for integration is the canonical restriction of the
`𝕜`-action, so no additional scalar structure on `V` is required. -/
noncomputable def gramOperator : V →L[𝕜] V :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 V
  letI := IsScalarTower.restrictScalars ℝ 𝕜 V
  haarAverage G (𝕜 := 𝕜) (gramFamily π hπ)

/-- The defining property of the Gram operator: it represents the Haar-averaged inner product. -/
theorem inner_gramOperator (v w : V) :
    ⟪v, gramOperator π hπ w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  let := NormedSpace.restrictScalars ℝ 𝕜 V
  let := IsScalarTower.restrictScalars ℝ 𝕜 V
  have h := ((innerSL 𝕜 v).comp (ContinuousLinearMap.apply 𝕜 V w)).haarAverage_comp_comm
    (G := G) (gramFamily π hπ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  rw [gramOperator, ← innerSL_apply_apply, ← h, haarAverage_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  rw [ContinuousMap.comp_apply]
  dsimp [gramFamily]
  exact ContinuousLinearMap.adjoint_inner_right (π g) v (π g w)

/-- The Gram operator represents the Haar-averaged inner product, written on the left. -/
theorem inner_gramOperator_left (v w : V) :
    ⟪gramOperator π hπ v, w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  rw [← inner_conj_symm, inner_gramOperator, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦ inner_conj_symm _ _)

/-- The averaged form is Hermitian: the Gram operator is symmetric. -/
theorem isSymmetric_gramOperator : (gramOperator π hπ : V →ₗ[𝕜] V).IsSymmetric := fun v w ↦ by
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_gramOperator_left, inner_gramOperator]

/-- The Gram operator of the averaged form is self-adjoint. -/
theorem isSelfAdjoint_gramOperator : IsSelfAdjoint (gramOperator π hπ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (isSymmetric_gramOperator π hπ)

/-! ### Positive definiteness

Nondegeneracy of the averaged form is where compactness of `G` enters a second time: the operator
norms `‖π g‖` are uniformly bounded, so `‖π g v‖` is bounded *below* by a positive multiple of
`‖v‖`, and the average of `‖π g v‖ ^ 2` cannot collapse to zero. -/

omit [CompleteSpace V] in
/-- Integrability of `g ↦ ‖π g v‖ ^ 2`: the integrand is continuous on a compact group carrying a
measure that is finite on compact sets. -/
private theorem integrable_norm_sq (v : V) :
    Integrable (fun g ↦ ‖π g v‖ ^ 2) (haarProb G) :=
  ((continuous_norm.comp (hπ.clm_apply continuous_const)).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The averaged form evaluated on the diagonal is the average of `‖π g v‖ ^ 2`. -/
theorem inner_gramOperator_self (v : V) :
    ⟪gramOperator π hπ v, v⟫_𝕜 = ((∫ g, ‖π g v‖ ^ 2 ∂haarProb G : ℝ) : 𝕜) := by
  rw [inner_gramOperator_left, ← integral_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp [inner_self_eq_norm_sq_to_K]

/-- The Gram operator of the averaged form is a positive operator. -/
theorem isPositive_gramOperator : (gramOperator π hπ).IsPositive := by
  refine ⟨isSymmetric_gramOperator π hπ, fun v ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_gramOperator_self, ofReal_re]
  exact integral_nonneg fun g ↦ by positivity

/-- The Haar-averaged form bounds the original norm square below by a fixed positive
multiple. In particular, its positivity is uniform over all vectors, even in infinite dimensions. -/
theorem exists_pos_mul_norm_sq_le_re_inner_gramOperator :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ re ⟪gramOperator π hπ v, v⟫_𝕜 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_le_norm_map π hπ
  refine ⟨c ^ 2, sq_pos_of_pos hc, fun v ↦ ?_⟩
  rw [inner_gramOperator_self, ofReal_re, ← mul_pow]
  have h := integral_mono (integrable_const ((c * ‖v‖) ^ 2)) (integrable_norm_sq π hπ v)
    fun g ↦ pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg v)) (hbound g v) 2
  simpa using h

/-- **Positive definiteness of the averaged form.** For a nonzero vector the averaged norm square
is strictly positive; this is what makes `⟪v, w⟫_G = ⟪gramOperator π hπ v, w⟫` an inner product
rather than merely a positive semidefinite form. -/
theorem re_inner_gramOperator_self_pos {v : V} (hv : v ≠ 0) :
    0 < re ⟪gramOperator π hπ v, v⟫_𝕜 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_sq_le_re_inner_gramOperator π hπ
  exact (mul_pos hc (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le (hbound v)

/-- The averaged form is nondegenerate, so the Gram operator is injective. -/
theorem gramOperator_injective : Function.Injective (gramOperator π hπ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have := re_inner_gramOperator_self_pos π hπ hne
  rw [hv, inner_zero_left, map_zero] at this
  exact lt_irrefl 0 this

/-! ### Invariance -/

/-- **The averaged form is `G`-invariant.** The original action preserves the averaged inner
product `⟪v, w⟫_G = ⟪v, gramOperator π hπ w⟫`, even when it does not preserve the given one. -/
@[simp]
theorem inner_gramOperator_map_map (g : G) (v w : V) :
    ⟪π g v, gramOperator π hπ (π g w)⟫_𝕜 = ⟪v, gramOperator π hπ w⟫_𝕜 := by
  rw [inner_gramOperator, inner_gramOperator]
  simpa only [map_mul, mul_apply_eq_comp] using
    integral_mul_right_eq_self (μ := haarProb G) (fun h ↦ ⟪π h v, π h w⟫_𝕜) g

/-- **The operator form of `G`-invariance of the averaged form:** `(π g)† ∘ S ∘ (π g) = S`. -/
@[simp]
theorem adjoint_comp_gramOperator_comp (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp ((gramOperator π hπ).comp (π g)) =
      gramOperator π hπ := by
  ext w
  apply ext_inner_left 𝕜
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_gramOperator_map_map]

/-- **Weyl's unitarian trick.** Every continuous representation of a compact group on a Hilbert
space carries a `G`-invariant positive-definite Hermitian form, represented by a positive-definite
self-adjoint operator `S` with `(π g)† ∘ S ∘ (π g) = S`.

This operator is the input to unitarization: retopologizing `V` by `⟪S ·, ·⟫`, or conjugating `π`
by `S ^ (1 / 2)`, makes every `π g` unitary. Neither construction is carried out here, so this file
does not itself produce an `IsUnitary` representation;
`ContRepresentation.exists_isUnitary_congr` does, for a finite-dimensional carrier. -/
theorem isUnitarizable :
    ∃ S : V →L[𝕜] V, IsSelfAdjoint S ∧ (∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) ∧
      ∀ g : G, (ContinuousLinearMap.adjoint (π g)).comp (S.comp (π g)) = S :=
  ⟨gramOperator π hπ, isSelfAdjoint_gramOperator π hπ,
    fun _ hv ↦ re_inner_gramOperator_self_pos π hπ hv, adjoint_comp_gramOperator_comp π hπ⟩

/-- Averaging a form that is already invariant changes nothing: the Gram operator of a unitary
representation is the identity. -/
@[simp]
theorem gramOperator_eq_one (hunitary : ContRepresentation.IsUnitary π) :
    gramOperator π hπ = 1 := by
  let := NormedSpace.restrictScalars ℝ 𝕜 V
  let := IsScalarTower.restrictScalars ℝ 𝕜 V
  have hconst : gramFamily π hπ = ContinuousMap.const G 1 :=
    ContinuousMap.ext fun g ↦ hunitary.adjoint_comp_self g
  rw [gramOperator, hconst, haarAverage_const]

end ContRepresentation
end
end TAF_LiteralSource_0411

section TAF_LiteralSource_0412
/- Original module: TauCeti.Topology.Algebra.Module.Trace -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The trace of a continuous endomorphism as a continuous linear functional

On a finite-dimensional Hausdorff topological vector space `V` over a complete nontrivially
normed field `𝕜`, the trace `T ↦ trace T` of a continuous endomorphism is itself a continuous
linear functional `TauCeti.traceCLM 𝕜 V : (V →L[𝕜] V) →L[𝕜] 𝕜`, where `V →L[𝕜] V` carries its
usual topology of uniform convergence on bounded sets (the operator-norm topology when `V` is
normed). Continuity is not something the algebraic `LinearMap.trace` can see: it holds because
`V →L[𝕜] V` is again a finite-dimensional Hausdorff topological vector space over the complete
field `𝕜`, and every linear map out of such a space is continuous.

This bundled form is what lets the trace commute with limits, continuity and integrals: it is
used, for instance, for the continuity of the character of a continuous representation, to move
the trace through a Bochner integral of operators, and to define the divergence of a vector field
as the trace of its derivative.
-/

public section

namespace TauCeti

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

/-- The trace of a continuous endomorphism of a finite-dimensional Hausdorff topological vector
space, as a continuous linear functional. Continuity is automatic: `V →L[𝕜] V` is a
finite-dimensional Hausdorff topological vector space over the complete field `𝕜`, and every
linear map out of such a space is continuous. -/
noncomputable def traceCLM : (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 V).comp (ContinuousLinearMap.coeLM 𝕜))

variable {𝕜 V}

/-- `TauCeti.traceCLM` evaluates to the trace of the underlying linear map. -/
@[simp]
theorem traceCLM_apply (T : V →L[𝕜] V) :
    traceCLM 𝕜 V T = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) :=
  (rfl)

end TauCeti
end
end TAF_LiteralSource_0412

section TAF_LiteralSource_0413
/- Original module: TauCeti.RepresentationTheory.Continuous.MatrixCoefficient -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Matrix coefficients of continuous representations

This file defines the matrix coefficient
`g ↦ ⟪π g v, w⟫` of a representation whose operator-valued action is continuous, and develops its
algebra: sesquilinearity in the defining vectors, the matrix-multiplication identity at a product
of group elements, the behaviour under left and right translation of the group argument, the
involution coming from inversion, and the uniform bound for unitary representations.

Mathlib's `ContRepresentation` bundles continuous linear action operators but does not require
continuity of the map from the acting topological monoid to those operators. The continuity
hypothesis is therefore explicit in `matrixCoeff` and its API; since it is a `Prop` argument, two
matrix coefficients built from different continuity proofs are equal by proof irrelevance.

## Main definitions

* `ContRepresentation.matrixCoeff`: the matrix coefficient `g ↦ ⟪π g v, w⟫` as an element
  of `C(G, 𝕜)`.
* `ContRepresentation.matrixCoeffₛₗ`: the matrix coefficients of a fixed representation
  bundled as a sesquilinear map `V →ₗ⋆[𝕜] V →ₗ[𝕜] C(G, 𝕜)`, in Mathlib's `innerₛₗ` convention.

## Main statements

* `ContRepresentation.matrixCoeff_apply_mul_eq_sum`: in an orthonormal basis, matrix
  coefficients multiply like matrices, `π_{ik}(g * h) = ∑ j, π_{ij}(g) · π_{jk}(h)`.
* `ContRepresentation.matrixCoeff_comp_mulRight` and
  `ContRepresentation.matrixCoeff_comp_mulLeft`: right and left translates of a matrix
  coefficient of `π` are again matrix coefficients of `π`. This is the `G × G`-action that
  structures the span of the matrix coefficients.
* `ContRepresentation.star_matrixCoeff`: the conjugate of a matrix coefficient of a
  unitary representation is a matrix coefficient composed with inversion.
* `ContRepresentation.matrixCoeff_trivial`: the matrix coefficients of the trivial
  representation are constant.
* `ContRepresentation.norm_matrixCoeff_le`: the uniform bound `‖v‖ * ‖w‖` for a unitary
  representation.

This algebra makes the
span of the matrix coefficients of a fixed representation a translation-stable subspace of `C(G)`,
stable under conjugation followed by inversion of the argument, and it feeds the Schur
orthogonality relations. Conjugation alone leaves that span in general: it produces a
matrix coefficient of the contragredient representation. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

section Coefficients

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The matrix coefficient `g ↦ ⟪π g v, w⟫` of a representation with continuous
operator-valued action. -/
noncomputable def matrixCoeff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : C(G, 𝕜) where
  toFun g := ⟪π g v, w⟫_𝕜
  continuous_toFun := by fun_prop

/-- Evaluation of a matrix coefficient. -/
@[simp]
theorem matrixCoeff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g = ⟪π g v, w⟫_𝕜 :=
  (rfl)

/-- A matrix coefficient at the identity is the inner product of its defining vectors. -/
theorem matrixCoeff_apply_one (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v w : V) :
    matrixCoeff π hπ v w 1 = ⟪v, w⟫_𝕜 := by
  simp

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-! ### Sesquilinearity in the defining vectors

Following Mathlib's inner-product convention, a matrix coefficient is conjugate-linear in its first
vector and linear in its second. -/

@[simp]
theorem matrixCoeff_zero_left (w : V) : matrixCoeff π hπ 0 w = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_zero_right (v : V) : matrixCoeff π hπ v 0 = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_add_left (v₁ v₂ w : V) :
    matrixCoeff π hπ (v₁ + v₂) w = matrixCoeff π hπ v₁ w + matrixCoeff π hπ v₂ w := by
  ext g
  simp [inner_add_left]

@[simp]
theorem matrixCoeff_add_right (v w₁ w₂ : V) :
    matrixCoeff π hπ v (w₁ + w₂) = matrixCoeff π hπ v w₁ + matrixCoeff π hπ v w₂ := by
  ext g
  simp [inner_add_right]

@[simp]
theorem matrixCoeff_smul_left (c : 𝕜) (v w : V) :
    matrixCoeff π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_left]

@[simp]
theorem matrixCoeff_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeff π hπ v (c • w) = c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_right]

/-- The matrix coefficients of a fixed representation, bundled as a sesquilinear map: conjugate
linear in the first vector, linear in the second, exactly as Mathlib's `innerₛₗ`.

Bundling records the sesquilinearity in the form the span of the matrix coefficients is built from,
and supplies the remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the
`LinearMap` API. -/
noncomputable def matrixCoeffₛₗ : V →ₗ⋆[𝕜] V →ₗ[𝕜] C(G, 𝕜) where
  toFun v :=
    { toFun := matrixCoeff π hπ v
      map_add' := matrixCoeff_add_right π hπ v
      map_smul' := matrixCoeff_smul_right π hπ v }
  map_add' v₁ v₂ := LinearMap.ext fun w ↦ matrixCoeff_add_left π hπ v₁ v₂ w
  map_smul' c v := LinearMap.ext fun w ↦ matrixCoeff_smul_left π hπ c v w

@[simp]
theorem matrixCoeffₛₗ_apply_apply (v w : V) :
    matrixCoeffₛₗ π hπ v w = matrixCoeff π hπ v w :=
  (rfl)

/-! ### Translating the group argument -/

/-- Translating the argument of a matrix coefficient on the right moves the action onto the first
vector. The pointwise statement needs no continuity of the multiplication of `G`. -/
theorem matrixCoeff_apply_mul_right (v w : V) (g g₀ : G) :
    matrixCoeff π hπ v w (g * g₀) = matrixCoeff π hπ (π g₀ v) w g := by
  simp [map_mul]

/-- Matrix coefficients multiply like matrices: expanding the intermediate vector `π h v` in an
orthonormal basis writes the coefficient at a product as a sum of products of coefficients. In the
basis notation `π_{ij}(g) = ⟪π g eⱼ, eᵢ⟫` this is `π_{ik}(g * h) = ∑ j, π_{ij}(g) · π_{jk}(h)`. -/
theorem matrixCoeff_apply_mul_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V)
    (v w : V) (g h : G) :
    matrixCoeff π hπ v w (g * h) =
      ∑ i, matrixCoeff π hπ (e i) w g * matrixCoeff π hπ v (e i) h := by
  have hmul : π (g * h) v = π g (π h v) := by simp [map_mul]
  calc
    matrixCoeff π hπ v w (g * h) = ⟪π g (∑ i, ⟪e i, π h v⟫_𝕜 • e i), w⟫_𝕜 := by
      rw [matrixCoeff_apply, hmul, e.sum_repr']
    _ = ∑ i, (starRingEnd 𝕜) ⟪e i, π h v⟫_𝕜 * ⟪π g (e i), w⟫_𝕜 := by
      simp [map_sum, sum_inner, inner_smul_left]
    _ = ∑ i, matrixCoeff π hπ (e i) w g * matrixCoeff π hπ v (e i) h := by
      simp [inner_conj_symm, mul_comm]

/-! ### The trivial representation, and restriction along a homomorphism -/

/-- A matrix coefficient of the trivial representation is the constant function at the inner
product of its defining vectors; the trivial action is constant, so `continuous_const` is its
continuity witness. Which constants arise depends on `V`: they are the values of the inner product,
so all of `𝕜` when some `⟪v, w⟫ ≠ 0`, and only `0` when `V` is trivial. -/
@[simp]
theorem matrixCoeff_trivial (v w : V) :
    matrixCoeff (ContRepresentation.trivial 𝕜 G V) continuous_const v w =
      ContinuousMap.const G ⟪v, w⟫_𝕜 := by
  ext g
  simp
  rfl

/-- A matrix coefficient of an invariant submodule is the matrix coefficient of the ambient
representation at the underlying vectors, so passing to a subrepresentation creates no new
matrix coefficients; `continuous_subrepresentation hπ` is the continuity witness of the restricted
action. -/
@[simp]
theorem matrixCoeff_subrepresentation {W : Submodule 𝕜 V} (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (v w : W) :
    matrixCoeff (subrepresentation π W hW) (continuous_subrepresentation hπ) v w =
      matrixCoeff π hπ (v : V) (w : V) := by
  ext g
  simp [Submodule.coe_inner]

/-- Restricting a representation along a continuous homomorphism precomposes its matrix
coefficients; the restricted action is `π ∘ φ`, so `hπ.comp hφ` is its continuity witness. -/
@[simp]
theorem matrixCoeff_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) (v w : V) :
    matrixCoeff (π.restrict φ) (hπ.comp hφ) v w = (matrixCoeff π hπ v w).comp ⟨φ, hφ⟩ := by
  ext h
  simp

end Coefficients

section TranslationRight

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The right translate of a matrix coefficient of `π` is again a matrix coefficient of `π`: the
translation is absorbed into the first vector. -/
@[simp]
theorem matrixCoeff_comp_mulRight (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulRight g₀) = matrixCoeff π hπ (π g₀ v) w :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_right π hπ v w g g₀

end TranslationRight

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {π : ContRepresentation 𝕜 G V}

/-- Translating the argument of a matrix coefficient of a unitary representation on the left moves
the action of the inverse onto the second vector. -/
theorem matrixCoeff_apply_mul_left (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V)
    (g₀ g : G) :
    matrixCoeff π hπ v w (g₀ * g) = matrixCoeff π hπ v (π g₀⁻¹ w) g := by
  have hmul : π (g₀ * g) v = π g₀ (π g v) := by simp [map_mul]
  rw [matrixCoeff_apply, matrixCoeff_apply, hmul, hunitary.inner_map_left]

/-- Evaluating a matrix coefficient of a unitary representation at an inverse conjugates it and
swaps its defining vectors. This is the involution that the span of the matrix coefficients carries;
see `star_matrixCoeff` for the packaged form. -/
theorem matrixCoeff_apply_inv (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g⁻¹ = (starRingEnd 𝕜) (matrixCoeff π hπ w v g) := by
  rw [matrixCoeff_apply, matrixCoeff_apply, hunitary.inner_map_left, inv_inv, inner_conj_symm]

/-- The left translate of a matrix coefficient of a unitary representation is again a matrix
coefficient: the translation is absorbed into the second vector. -/
@[simp]
theorem matrixCoeff_comp_mulLeft [SeparatelyContinuousMul G] (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulLeft g₀) = matrixCoeff π hπ v (π g₀⁻¹ w) :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_left hπ hunitary v w g₀ g

/-- The conjugate of a matrix coefficient of a unitary representation is the matrix coefficient
with its vectors swapped, precomposed with inversion. So the span of the matrix coefficients of a
unitary representation is stable under the star operation of `C(G, 𝕜)` followed by inversion of the
argument. -/
@[simp]
theorem star_matrixCoeff [ContinuousInv G] (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      (matrixCoeff π hπ w v).comp ⟨Inv.inv, continuous_inv⟩ :=
  ContinuousMap.ext fun g ↦ (matrixCoeff_apply_inv hπ hunitary w v g).symm

end Group

section CompactDomain

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [CompactSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The uniform norm of a matrix coefficient of a unitary representation is at most the product
of the norms of its defining vectors. -/
theorem norm_matrixCoeff_le (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) :
    ‖matrixCoeff π hπ v w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact fun g ↦ hunitary.norm_inner_map_le g v w

end CompactDomain

end ContRepresentation
end
end TAF_LiteralSource_0413

section TAF_LiteralSource_0414
/- Original module: TauCeti.RepresentationTheory.Continuous.Character -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Characters of continuous representations

The character of a finite-dimensional representation is the function `g ↦ trace (π g)`. Mathlib
builds it for a bare `Representation` and proves its algebraic identities; this file packages it
as an element of `C(G, 𝕜)` for a representation with continuous operator-valued action, and links
it to the matrix coefficients of `TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`.

## Main definitions

* `ContRepresentation.character`: the character `g ↦ trace (π g)` as an element of
  `C(G, 𝕜)`.

## Main statements

* `ContRepresentation.character_one`: the character at the identity is the dimension.
* `ContRepresentation.character_conj`: the character is a class function.
* `ContRepresentation.star_character`: the conjugate of the character is the sum of the
  diagonal matrix coefficients `∑ i, ⟪π g eᵢ, eᵢ⟫` in an orthonormal basis. The conjugation is not
  decoration: Mathlib's inner product is conjugate linear in its *first* argument, so the diagonal
  matrix coefficient `matrixCoeff π hπ eᵢ eᵢ` is `⟪π g eᵢ, eᵢ⟫`, whereas the diagonal entry of the
  matrix of `π g` in that basis, which the trace sums, is `⟪eᵢ, π g eᵢ⟫`.
* `ContRepresentation.character_apply_inv`: the character of a unitary representation at an
  inverse is the conjugate of its value.
* `ContRepresentation.norm_character_apply_le`: a unitary character is bounded by the
  dimension.
* `ContRepresentation.continuous_character_mul_self`: the character read along the squaring map
  `g ↦ g * g` is continuous.

## Implementation notes

The underlying function is Mathlib's `Representation.character`, so the identities that are purely
algebraic — the value at `1`, invariance under conjugation, the behaviour under a product of group
elements — are restatements of `Representation.char_one`, `Representation.char_conj` and
`Representation.char_mul_comm` rather than new proofs. What this file adds is continuity, which
`Representation.character` cannot see, and the orthonormal-basis bridge to matrix coefficients.

Continuity of the trace is not automatic from continuity of `π` alone: it is continuity of the
functional `T ↦ trace T` on `V →L[𝕜] V`, which holds because that space is finite-dimensional over
the complete field `𝕜`. That functional is `TauCeti.traceCLM` of
`TauCeti/Topology/Algebra/Module/Trace.lean`, shared with
`TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean`, which uses it to average a trace.

Only the trace is at stake in the sections without an inner product, so they ask no more of the
scalars than that functional does: `𝕜` is a complete nontrivially normed field there, and becomes
`RCLike` only where an orthonormal basis or unitarity enters.

The `L²` theory and the orthogonality relations are in
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`. Nothing here needs a group, a measure,
or compactness, so it is stated over a topological monoid. The mathematical development follows
Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

open TauCeti

namespace ContRepresentation

section Monoid

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The character** `g ↦ trace (π g)` of a finite-dimensional representation with continuous
operator-valued action, as an element of `C(G, 𝕜)`.

The underlying function is Mathlib's `Representation.character`; only the continuity is new, and it
comes from `TauCeti.traceCLM`, the trace as a continuous linear functional. -/
noncomputable def character (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) : C(G, 𝕜) where
  toFun := π.toRepresentation.character
  continuous_toFun := by
    have h : π.toRepresentation.character = fun g ↦ traceCLM 𝕜 V (π g) := by
      funext g
      rw [traceCLM_apply]
      rfl
    rw [h]
    exact (traceCLM 𝕜 V).continuous.comp hπ

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character of a continuous representation is Mathlib's character of the underlying
representation; every algebraic identity about the latter therefore applies verbatim. -/
theorem coe_character : ⇑(character π hπ) = π.toRepresentation.character :=
  (rfl)

/-- Evaluation of the character. -/
@[simp]
theorem character_apply (g : G) :
    character π hπ g = LinearMap.trace 𝕜 V (π g : V →ₗ[𝕜] V) :=
  (rfl)

/-- The character at the identity is the dimension of the representation. -/
theorem character_one : character π hπ 1 = (Module.finrank 𝕜 V : 𝕜) :=
  Representation.char_one π.toRepresentation

/-- The character is unchanged by transposing a product of group elements. -/
theorem character_mul_comm (g h : G) :
    character π hπ (h * g) = character π hπ (g * h) :=
  Representation.char_mul_comm π.toRepresentation g h

/-- The character of the trivial representation is the constant function at the dimension: every
action operator is the identity, whose trace is the dimension. The trivial action is constant, so
`continuous_const` is its continuity witness. -/
@[simp]
theorem character_trivial :
    character (ContRepresentation.trivial 𝕜 G V) continuous_const =
      ContinuousMap.const G (Module.finrank 𝕜 V : 𝕜) := by
  ext g
  have hid : ((ContRepresentation.trivial 𝕜 G V g : V →L[𝕜] V) : V →ₗ[𝕜] V) = LinearMap.id :=
    LinearMap.ext fun v ↦ ContRepresentation.trivial_apply (R := 𝕜) (G := G) (V := V) g v
  -- `character_apply` gets its arguments explicitly: `continuous_const` has the required type only
  -- after unfolding `trivial`, which the matching of `rw` does not do.
  rw [character_apply (ContRepresentation.trivial 𝕜 G V) continuous_const, hid,
    LinearMap.trace_id, ContinuousMap.const_apply]

/-- Restricting a representation along a continuous homomorphism precomposes its character. -/
@[simp]
theorem character_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) :
    character (π.restrict φ) (hπ.comp hφ) = (character π hπ).comp ⟨φ, hφ⟩ := by
  ext h
  rw [character_apply, ContinuousMap.comp_apply, character_apply, ContinuousMap.coe_mk,
    ContRepresentation.restrict_apply]

end Monoid

section MonoidInner

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character read off an orthonormal basis: it is the sum of the diagonal entries
`⟪eᵢ, π g eᵢ⟫` of the matrix of `π g`. -/
theorem character_apply_eq_sum_inner {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) (g : G) :
    character π hπ g = ∑ i, ⟪e i, π g (e i)⟫_𝕜 :=
  LinearMap.trace_eq_sum_inner _ e

/-- **The conjugate of the character is the sum of the diagonal matrix coefficients.** With
`matrixCoeff π hπ v w g = ⟪π g v, w⟫`, conjugate linear in `v`, the diagonal matrix coefficient
`πᵢᵢ(g) = ⟪π g eᵢ, eᵢ⟫` is the *conjugate* of the diagonal entry `⟪eᵢ, π g eᵢ⟫` summed by the
trace; the conjugation on the left is what records that. This is the identity through which the
Schur orthogonality relations compute inner products of characters. -/
theorem star_character {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) :
    star (character π hπ) = ∑ i, matrixCoeff π hπ (e i) (e i) := by
  ext g
  rw [ContinuousMap.star_apply, character_apply_eq_sum_inner π hπ e g]
  simp [inner_conj_symm]

/-- The character of a unitary representation is bounded by the dimension: each of the `dim V`
diagonal entries `⟪eᵢ, π g eᵢ⟫` has modulus at most `‖eᵢ‖ * ‖π g eᵢ‖ = 1`. -/
theorem norm_character_apply_le (hunitary : IsUnitary π) (g : G) :
    ‖character π hπ g‖ ≤ Module.finrank 𝕜 V := by
  classical
  set e := stdOrthonormalBasis 𝕜 V
  calc ‖character π hπ g‖
      = ‖∑ i, ⟪e i, π g (e i)⟫_𝕜‖ := by rw [character_apply_eq_sum_inner π hπ e g]
    _ ≤ ∑ i, ‖⟪e i, π g (e i)⟫_𝕜‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank 𝕜 V), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc ‖⟪e i, π g (e i)⟫_𝕜‖ ≤ ‖e i‖ * ‖π g (e i)‖ := norm_inner_le_norm _ _
          _ = 1 := by rw [hunitary.norm_map, e.orthonormal.1 i, mul_one]
    _ = Module.finrank 𝕜 V := by simp

end MonoidInner

section Group

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The character is a class function.** This is `Representation.char_conj` transported to the
continuous packaging. -/
theorem character_conj (g h : G) :
    character π hπ (h * g * h⁻¹) = character π hπ g :=
  Representation.char_conj π.toRepresentation g h

end Group

section GroupInner

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character of a **unitary** representation at an inverse is the conjugate of its value: the
action of `g⁻¹` is the adjoint of the action of `g`, and taking adjoints conjugates the diagonal
entries in an orthonormal basis. -/
theorem character_apply_inv (hunitary : IsUnitary π) (g : G) :
    character π hπ g⁻¹ = (starRingEnd 𝕜) (character π hπ g) := by
  set e := stdOrthonormalBasis 𝕜 V
  rw [character_apply_eq_sum_inner π hπ e, character_apply_eq_sum_inner π hπ e, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hunitary.inner_map_right g⁻¹ (e i) (e i), inv_inv, inner_conj_symm]

end GroupInner

/-! ### The character along the squaring map -/

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [ContinuousMul G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- The character read along the squaring map `g ↦ g * g` is continuous. -/
theorem continuous_character_mul_self (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    Continuous fun g : G ↦ character π hπ (g * g) :=
  (character π hπ).continuous.comp (continuous_id.mul continuous_id)

end ContRepresentation
end
end TAF_LiteralSource_0414

section TAF_LiteralSource_0415
/- Original module: TauCeti.Analysis.InnerProductSpace.Conjugation -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coordinatewise conjugation in an orthonormal basis

There is no canonical conjugation on an abstract inner product space, so this file attaches one to
an orthonormal basis `e` by conjugating the coordinates in it:
`e.conjugation x = ∑ i, conj ⟪e i, x⟫ • e i`. It is a conjugate-linear isometric involution of `V`
(`OrthonormalBasis.conjugation`, `OrthonormalBasis.conjugation_conjugation`), and conjugating an
operator by it, `A ↦ J ∘ A ∘ J` (`OrthonormalBasis.conjCLM`), is the coordinate-free description
of conjugating the matrix of `A` entrywise.

## Main definitions

* `OrthonormalBasis.conjugation`: the conjugate-linear isometric involution attached to an
  orthonormal basis.
* `OrthonormalBasis.conjCLM`: conjugation of continuous linear operators, `A ↦ J ∘ A ∘ J`, itself
  a conjugate-linear isometric involution of the operators.

## Main statements

* `OrthonormalBasis.conjugation_conjugation` and
  `OrthonormalBasis.inner_conjugation_conjugation`: conjugation is an involution, and reverses
  the inner product.
* `OrthonormalBasis.conjugation_basis`: the basis it is attached to is fixed vector by vector,
  which is what makes it *the* conjugation of that basis.
* `OrthonormalBasis.inner_conjugation_left_basis`: pairing a conjugate against a basis vector
  swaps the two arguments of the inner product.
* `OrthonormalBasis.conjCLM_one`, `OrthonormalBasis.conjCLM_mul` and
  `OrthonormalBasis.conjCLM_conjCLM`: conjugation of operators is a multiplicative involution
  fixing the identity, so with its conjugate-linearity it is a conjugate-linear ring involution of
  the operators.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

section Conjugation

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Coordinatewise conjugation in an orthonormal basis.** A conjugate-linear isometric involution
of `V`, which on coordinates is `x i ↦ conj (x i)`. -/
noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) : V ≃ₗᵢ⋆[𝕜] V :=
  let J : V →ₗ⋆[𝕜] V :=
    { toFun x := ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i
      map_add' x y := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
      map_smul' c x := by simp [inner_smul_right, Finset.smul_sum, smul_smul] }
  have hJ (x : V) (j : ι) : ⟪e j, J x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 :=
    e.orthonormal.inner_right_fintype _ j
  have hJJ : Function.Involutive J := fun x ↦ by
    conv_rhs => rw [← e.sum_repr' x]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hJ, RCLike.conj_conj]
  { LinearEquiv.ofInvolutive J hJJ with
    norm_map' x := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [← e.sum_sq_norm_inner_right, ← e.sum_sq_norm_inner_right]
      simp [hJ, norm_inner_symm] }

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugation, expanded as the coordinate sum defining it. -/
theorem conjugation_apply (x : V) :
    e.conjugation x = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i :=
  (rfl)

/-- The coordinates of a conjugate are the conjugated coordinates. -/
@[simp]
theorem inner_conjugation (x : V) (j : ι) :
    ⟪e j, e.conjugation x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 := by
  rw [conjugation_apply]
  exact e.orthonormal.inner_right_fintype _ j

/-- Conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : V) : e.conjugation (e.conjugation x) = x := by
  conv_rhs => rw [← e.sum_repr' x]
  simp [conjugation_apply (x := e.conjugation x)]

/-- Conjugation is its own inverse. -/
@[simp]
theorem conjugation_symm : e.conjugation.symm = e.conjugation :=
  LinearIsometryEquiv.ext fun x ↦
    e.conjugation.symm_apply_eq.mpr (e.conjugation_conjugation x).symm

/-- **Conjugation fixes the basis it is attached to.** Coordinatewise conjugation is the identity
on the vectors whose coordinates are `0` and `1`. -/
@[simp]
theorem conjugation_basis (j : ι) : e.conjugation (e j) = e j := by
  classical
  conv_rhs => rw [← e.sum_repr' (e j)]
  simp [conjugation_apply, orthonormal_iff_ite.mp e.orthonormal, apply_ite]

/-- Conjugation reverses the inner product: it is conjugate-linear and isometric. -/
@[simp]
theorem inner_conjugation_conjugation (x y : V) :
    ⟪e.conjugation x, e.conjugation y⟫_𝕜 = (starRingEnd 𝕜) ⟪x, y⟫_𝕜 := by
  rw [← e.sum_inner_mul_inner, ← e.sum_inner_mul_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← inner_conj_symm (e.conjugation x) (e i), inner_conjugation, inner_conjugation, map_mul,
    inner_conj_symm]

/-- **Pairing a conjugate against a basis vector swaps the arguments.** Conjugation fixes `e j`, so
the reversal of the inner product turns `⟪J x, e j⟫` into `⟪e j, x⟫`. This is the form in which the
conjugation is contracted against a coordinate. -/
@[simp]
theorem inner_conjugation_left_basis (x : V) (j : ι) :
    ⟪e.conjugation x, e j⟫_𝕜 = ⟪e j, x⟫_𝕜 := by
  conv_lhs => rw [← conjugation_basis e j]
  rw [inner_conjugation_conjugation, inner_conj_symm]

end Conjugation

section ConjugateOperator

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Conjugation of continuous linear operators**, `A ↦ J ∘ A ∘ J` for `J` the conjugation of
`e`. The two conjugate-linearities of `J` cancel, so `J ∘ A ∘ J` is again `𝕜`-linear, and it has the
norm of `A` because `J` is an isometric involution. As a map of operators it is itself a
conjugate-linear isometric involution. -/
noncomputable def conjCLM (e : OrthonormalBasis ι 𝕜 V) : (V →L[𝕜] V) ≃ₗᵢ⋆[𝕜] (V →L[𝕜] V) :=
  let J : V →SL[starRingEnd 𝕜] V := e.conjugation
  let C : (V →L[𝕜] V) →ₗ⋆[𝕜] (V →L[𝕜] V) :=
    { toFun A := J.comp (A.comp J)
      map_add' A B := by ext; simp [J]
      map_smul' c A := by ext; simp [J] }
  { LinearEquiv.ofInvolutive C fun A ↦ by ext; simp [C, J] with
    norm_map' A := (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp _ _).trans
      (A.opNorm_comp_linearIsometryEquiv e.conjugation) }

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Evaluation of a conjugated operator. -/
@[simp]
theorem conjCLM_apply (A : V →L[𝕜] V) (x : V) :
    e.conjCLM A x = e.conjugation (A (e.conjugation x)) :=
  (rfl)

/-- Conjugation fixes the identity, because `J` is an involution. -/
@[simp]
theorem conjCLM_one : e.conjCLM 1 = 1 := by
  ext x
  simp

/-- Conjugation is multiplicative, again because `J` is an involution: the two inner copies of `J`
cancel. -/
@[simp]
theorem conjCLM_mul (A B : V →L[𝕜] V) : e.conjCLM (A * B) = e.conjCLM A * e.conjCLM B := by
  ext x
  simp

/-- Conjugation of operators is an involution, because `J` is. -/
@[simp]
theorem conjCLM_conjCLM (A : V →L[𝕜] V) : e.conjCLM (e.conjCLM A) = A := by
  ext x
  simp

/-- Conjugation of operators is its own inverse. -/
@[simp]
theorem conjCLM_symm : e.conjCLM.symm = e.conjCLM :=
  LinearIsometryEquiv.ext fun A ↦ e.conjCLM.symm_apply_eq.mpr (e.conjCLM_conjCLM A).symm

end ConjugateOperator

end OrthonormalBasis
end
end TAF_LiteralSource_0415

section TAF_LiteralSource_0416
/- Original module: TauCeti.RepresentationTheory.Continuous.Conjugate -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The conjugate of a continuous representation

Complex conjugation of the matrix entries of a representation gives another representation, the
**conjugate** (equivalently, for a unitary representation, the contragredient). It is what the span
of the matrix coefficients needs in order to be closed under the involution of `C(G, 𝕜)`:
conjugating a matrix coefficient of `π` produces a matrix coefficient of the conjugate of `π`, not
of `π` itself.

There is no canonical conjugation on an abstract inner product space, so the construction takes an
orthonormal basis `e` as data and conjugates each action operator by the coordinatewise conjugation
`OrthonormalBasis.conjugation` of that basis, using `OrthonormalBasis.conjCLM`. Different bases
give conjugates that are isomorphic representations, so the choice is immaterial for the uses
downstream, which only need one conjugate to exist.

## Main definitions

* `OrthonormalBasis.conjugate`: the conjugate representation.

## Main statements

* `OrthonormalBasis.continuous_conjugate` and
  `OrthonormalBasis.isUnitary_conjugate`: the conjugate of a continuous representation is
  continuous, and of a unitary one is unitary.
* `OrthonormalBasis.conjugate_conjugate`: conjugating twice returns the original
  representation.
* `OrthonormalBasis.star_matrixCoeff_eq_matrixCoeff_conjugate`: the conjugate of a matrix
  coefficient of `π` is a matrix coefficient of the conjugate of `π`.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open ContRepresentation

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **The conjugate of a continuous representation** with respect to an orthonormal basis: the
action operators are conjugated entrywise in that basis. -/
noncomputable def conjugate (π : ContRepresentation 𝕜 G V) : ContRepresentation 𝕜 G V :=
  .ofMonoidHom
    { toFun g := e.conjCLM (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, conjCLM_mul] }

variable (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in
/-- The action operators of the conjugate representation. -/
@[simp]
theorem conjugate_apply (g : G) : conjugate e π g = e.conjCLM (π g) :=
  (rfl)

omit [TopologicalSpace G] in
/-- **Conjugating twice returns the original representation**, because conjugation of operators is
an involution. -/
@[simp]
theorem conjugate_conjugate : conjugate e (conjugate e π) = π :=
  DFunLike.ext _ _ fun g ↦ by simp

/-- The conjugate of a continuous representation has a continuous operator-valued action. -/
theorem continuous_conjugate (hπ : Continuous π) : Continuous (conjugate e π) :=
  e.conjCLM.continuous.comp hπ

omit [TopologicalSpace G] in
/-- The conjugate of a unitary representation is unitary. -/
theorem isUnitary_conjugate {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π) :
    IsUnitary (OrthonormalBasis.conjugate e π) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by simp [hπ.norm_map]

/-- **The conjugate of a matrix coefficient is a matrix coefficient of the conjugate
representation**, at the conjugated vectors. This is the identity that makes the span of all matrix
coefficients stable under the involution of `C(G, 𝕜)`. -/
theorem star_matrixCoeff_eq_matrixCoeff_conjugate (hπ : Continuous π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      matrixCoeff (conjugate e π) (continuous_conjugate e π hπ)
        (e.conjugation v) (e.conjugation w) := by
  ext g
  simp [inner_conjugation_conjugation, RCLike.star_def]

end OrthonormalBasis
end
end TAF_LiteralSource_0416

section TAF_LiteralSource_0417
/- Original module: TauCeti.Analysis.InnerProductSpace.TensorProduct -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor products of inner product spaces

Mathlib's `ContinuousLinearMap.norm_rTensor_le` and `ContinuousLinearMap.norm_lTensor_le` bound the
norm of `f ⊗ id` and `id ⊗ f` by the norm of `f`. Together with additivity in `f` this says that
`f ↦ f.rTensor H` and `f ↦ f.lTensor H` are contractions, hence continuous in `f`, which is the
form in which the bound is used to make an operator-valued map into a tensor product continuous.

Mathlib's inner product on `E ⊗[𝕜] F` also says that the tensor product of two positive definite
Hermitian forms is positive definite. `TauCeti.apply_self_pos_of_apply_tmul_tmul` states this for
sesquilinear forms on vector spaces carrying no inner product space structure of their own, such as
the Hodge forms of polarized Hodge structures: a sesquilinear form on `W₁ ⊗[𝕜] W₂` whose value on
pure tensors is the product of the values of two positive definite Hermitian forms is positive
definite.

## Main statements

* `TauCeti.lipschitzWith_one_rTensor` and `TauCeti.lipschitzWith_one_lTensor`: tensoring with the
  identity, on either side, is `1`-Lipschitz in the operator.
* `TauCeti.apply_self_pos_of_apply_tmul_tmul`: the tensor product of two positive definite
  Hermitian forms is positive definite.
-/

public section

open scoped TensorProduct ComplexOrder

namespace TauCeti

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Tensoring a continuous linear map with the identity on the right is a contraction, hence
continuous in the map. This is the elementary continuity statement that Mathlib's
`ContinuousLinearMap.norm_rTensor_le` and additivity give together. -/
theorem lipschitzWith_one_rTensor :
    LipschitzWith 1 fun f : E →L[𝕜] F ↦ f.rTensor H :=
  LipschitzWith.of_dist_le_mul fun f f' ↦ by
    simpa [dist_eq_norm, ← ContinuousLinearMap.rTensor_sub] using
      ContinuousLinearMap.norm_rTensor_le (G := H) (f - f')

/-- Tensoring a continuous linear map with the identity on the left is a contraction, hence
continuous in the map. -/
theorem lipschitzWith_one_lTensor :
    LipschitzWith 1 fun f : E →L[𝕜] F ↦ f.lTensor H :=
  LipschitzWith.of_dist_le_mul fun f f' ↦ by
    simpa [dist_eq_norm, ← ContinuousLinearMap.lTensor_sub] using
      ContinuousLinearMap.norm_lTensor_le (G := H) (f - f')

section Sesquilinear

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module 𝕜 W₁] [AddCommGroup W₂] [Module 𝕜 W₂]

/-- The inner product space core of a positive definite Hermitian form. -/
private noncomputable abbrev coreOfPos (h : W₁ →ₗ⋆[𝕜] W₁ →ₗ[𝕜] 𝕜) (hh : h.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) : InnerProductSpace.Core 𝕜 W₁ where
  inner x y := h x y
  conj_inner_symm x y := hh.eq y x
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (RCLike.pos_iff.mp (hpos x hx)).1.le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hne
    exact (hpos x hne).ne' hx

/-- **The tensor product of two positive definite Hermitian forms is positive definite.** A
sesquilinear form `H` on `W₁ ⊗[𝕜] W₂` with `H (a ⊗ b) (c ⊗ d) = h₁ a c * h₂ b d`, for positive
definite Hermitian forms `h₁` and `h₂`, is positive on every nonzero vector. -/
theorem apply_self_pos_of_apply_tmul_tmul {h₁ : W₁ →ₗ⋆[𝕜] W₁ →ₗ[𝕜] 𝕜}
    {h₂ : W₂ →ₗ⋆[𝕜] W₂ →ₗ[𝕜] 𝕜} {H : W₁ ⊗[𝕜] W₂ →ₗ⋆[𝕜] W₁ ⊗[𝕜] W₂ →ₗ[𝕜] 𝕜}
    (hH : ∀ a b c d, H (a ⊗ₜ b) (c ⊗ₜ d) = h₁ a c * h₂ b d) (hh₁ : h₁.IsSymm)
    (hh₂ : h₂.IsSymm) (hpos₁ : ∀ x, x ≠ 0 → 0 < h₁ x x) (hpos₂ : ∀ x, x ≠ 0 → 0 < h₂ x x)
    {x : W₁ ⊗[𝕜] W₂} (hx : x ≠ 0) : 0 < H x x := by
  -- Make `h₁` and `h₂` the inner products of `W₁` and `W₂`; then `H` is Mathlib's inner product
  -- on the tensor product, which is positive definite.
  let c₁ := coreOfPos h₁ hh₁ hpos₁
  let c₂ := coreOfPos h₂ hh₂ hpos₂
  let : NormedAddCommGroup W₁ := c₁.toNormedAddCommGroup
  let : NormedAddCommGroup W₂ := c₂.toNormedAddCommGroup
  let : InnerProductSpace 𝕜 W₁ := InnerProductSpace.ofCore c₁.toCore
  let : InnerProductSpace 𝕜 W₂ := InnerProductSpace.ofCore c₂.toCore
  have hinner : ∀ y z : W₁ ⊗[𝕜] W₂, H y z = inner 𝕜 y z := by
    intro y z
    induction y with
    | tmul a b =>
      induction z with
      | tmul c d =>
        rw [hH, TensorProduct.inner_tmul]
        -- The inner products of the two factors are `h₁` and `h₂` by construction.
        rfl
      | add z z' hz hz' => rw [map_add, hz, hz', inner_add_right]
    | add y y' hy hy' => rw [map_add, LinearMap.add_apply, hy, hy', inner_add_left]
  rw [hinner]
  exact RCLike.pos_iff.2 ⟨re_inner_self_pos.2 hx, inner_self_im x⟩

end Sesquilinear

end TauCeti
end
end TAF_LiteralSource_0417

section TAF_LiteralSource_0418
/- Original module: TauCeti.RepresentationTheory.Continuous.TensorProduct -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The tensor product of continuous representations

The tensor product of two continuous representations of the same monoid acts by
`g ↦ (π g) ⊗ (ρ g)`, that is, by Mathlib's `TensorProduct.mapL`. This file builds it and proves the
three facts its use requires: the operator-valued action stays continuous, unitarity is preserved,
and the matrix coefficients **multiply**,
`(π ⊗ ρ)_{v ⊗ v', w ⊗ w'} = π_{v,w} · ρ_{v',w'}`.

The last identity is the reason the construction is here: it is what makes the span of the matrix
coefficients of all finite-dimensional representations of `G` closed under multiplication, hence a
subalgebra of `C(G, 𝕜)` rather than only a subspace.

Mathlib's inner product on `V ⊗[𝕜] W` (`TensorProduct.instInnerProductSpace`) is the one for which
`⟪v ⊗ₜ v', w ⊗ₜ w'⟫ = ⟪v, w⟫ * ⟪v', w'⟫`, so no choice is being made here; the same file supplies
`TensorProduct.mapL` with its multiplicativity `TensorProduct.mapL_mul` and its norm bound.

## Main definitions

* `ContRepresentation.tprod`: the tensor product `π ⊗ ρ` of two continuous
  representations.

## Main statements

* `ContRepresentation.continuous_tprod` and
  `ContRepresentation.IsUnitary.tprod`: the tensor product of continuous representations is
  continuous, and of unitary ones is unitary.
* `ContRepresentation.matrixCoeff_tprod`: matrix coefficients of a tensor product at pure
  tensors are products of matrix coefficients.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open TauCeti

open scoped InnerProductSpace TensorProduct

namespace ContRepresentation

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The tensor product of two continuous representations**, acting by `g ↦ (π g) ⊗ (ρ g)`. -/
noncomputable def tprod (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    ContRepresentation 𝕜 G (V ⊗[𝕜] W) :=
  .ofMonoidHom
    { toFun g := TensorProduct.mapL (π g) (ρ g)
      map_one' := by simp [ContinuousLinearMap.one_def]
      map_mul' g h := by rw [map_mul, map_mul, TensorProduct.mapL_mul] }

variable (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

omit [TopologicalSpace G] in
/-- The action operators of a tensor product of representations. -/
@[simp]
theorem tprod_apply (g : G) : (tprod π ρ) g = TensorProduct.mapL (π g) (ρ g) :=
  (rfl)

/-- The tensor product of two continuous representations has a continuous operator-valued action:
`mapL` is the composition of two contractions of the separate actions. -/
theorem continuous_tprod (hπ : Continuous π) (hρ : Continuous ρ) :
    Continuous (tprod π ρ) :=
  (lipschitzWith_one_rTensor.continuous.comp hπ).clm_comp
    (lipschitzWith_one_lTensor.continuous.comp hρ)

omit [TopologicalSpace G] in
/-- The tensor product of two unitary representations is unitary: the tensor product of two linear
isometries is a linear isometry. -/
theorem IsUnitary.tprod {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
    (hπ : IsUnitary π) (hρ : IsUnitary ρ) : IsUnitary (tprod π ρ) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by
    simpa using TensorProduct.norm_map
      (((π g) : V →ₗ[𝕜] V).isometryOfInner (hπ.inner_map_map g))
      (((ρ g) : W →ₗ[𝕜] W).isometryOfInner (hρ.inner_map_map g)) x

/-- **Matrix coefficients multiply under tensor product.** The matrix coefficient of `π ⊗ ρ` at a
pair of pure tensors is the product of the matrix coefficients of `π` and of `ρ`. -/
@[simp]
theorem matrixCoeff_tprod (hπ : Continuous π) (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    matrixCoeff (tprod π ρ) (continuous_tprod π ρ hπ hρ) (v ⊗ₜ[𝕜] v') (w ⊗ₜ[𝕜] w') =
      matrixCoeff π hπ v w * matrixCoeff ρ hρ v' w' := by
  ext g
  simp

end ContRepresentation
end
end TAF_LiteralSource_0418

section TAF_LiteralSource_0419
/- Original module: TauCeti.RepresentationTheory.Continuous.Transport -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Transporting a continuous representation along a continuous linear equivalence

A continuous linear equivalence `e : V ≃L[𝕜] W` carries a continuous representation on `V` to one
on `W` by conjugating every action operator, `π g ↦ e ∘ π g ∘ e⁻¹`, that is, by applying Mathlib's
continuous algebra equivalence `ContinuousLinearEquiv.conjContinuousAlgEquiv`. This file builds
that transport and records what it preserves: continuity of the operator-valued action, and — for
an equivalence that is moreover isometric, so that inner products are available — unitarity and,
the point of the construction, the matrix coefficients, which are unchanged once the defining
vectors are moved along `e`.

The transport is what lets a statement about representations on the standard models
`EuclideanSpace 𝕜 (Fin n)` be applied to a representation on an arbitrary finite-dimensional
inner product space: `stdOrthonormalBasis` supplies the isometry `(stdOrthonormalBasis 𝕜 V).repr`,
so nothing is lost by pinning a model.

## Main definitions

* `ContinuousLinearEquiv.congr`: the transported representation `e ∘ π · ∘ e⁻¹`.
* `ContRepresentation.congrEquiv`: the equivalence of continuous representations `π ≃ congr e π`
  witnessed by `e` itself, which is what carries a statement about the transport back to `π`.

## Main statements

* `ContinuousLinearEquiv.continuous_congr`,
  `ContinuousLinearEquiv.isIrreducible_congr` and
  `ContRepresentation.IsUnitary.congr`: the transport preserves continuity,
  irreducibility, and unitarity.
* `ContRepresentation.congr_refl` and `ContinuousLinearEquiv.congr_congr`: the
  transport is functorial, so "transportable onto" is an equivalence relation on representations
  (symmetry is `simp` from these two).
* `LinearIsometryEquiv.matrixCoeff_congr`: the matrix coefficients of the transport at the
  transported vectors are those of the original representation.
* `ContinuousLinearEquiv.matrixCoeff_congr_adjoint`: the same for an equivalence that is not
  isometric, where the second vector moves along the adjoint of `e⁻¹` instead of along `e`.
-/

public section

open ContRepresentation

open scoped InnerProductSpace

namespace ContinuousLinearEquiv

section Congr

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Transport along a continuous linear equivalence.** The representation on `W` obtained from a
representation on `V` by conjugating each action operator with `e : V ≃L[𝕜] W`. -/
noncomputable def congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ContRepresentation 𝕜 G W :=
  .ofMonoidHom
    { toFun g := e.conjContinuousAlgEquiv (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, map_mul] }

omit [TopologicalSpace G] in
/-- The action operators of a transported representation. -/
theorem congr_apply (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) (g : G) (x : W) :
    congr e π g x = e (π g (e.symm x)) :=
  (rfl)

omit [TopologicalSpace G] in
/-- The operator-valued function underlying a transported representation. -/
@[simp]
theorem coe_congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ⇑(congr e π) = fun g ↦ e.conjContinuousAlgEquiv (π g) := by
  funext g
  apply ContinuousLinearMap.ext
  intro x
  exact congr_apply e π g x

/-- Transport preserves continuity of the operator-valued action: conjugation by `e` is the
continuous algebra equivalence `ContinuousLinearEquiv.conjContinuousAlgEquiv`. -/
theorem continuous_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V} (hπ : Continuous π) :
    Continuous (congr e π) :=
  (map_continuous e.conjContinuousAlgEquiv).comp hπ

omit [TopologicalSpace G] in
/-- Transport preserves irreducibility: `e` is an equivariant linear equivalence from `π` to its
transport, and irreducibility is invariant under such an equivalence. -/
theorem isIrreducible_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : π.toRepresentation.IsIrreducible) : (congr e π).toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv (e : V ≃ₗ[𝕜] W)
    (fun g v ↦ by simp [_root_.ContRepresentation.toMonoidHom_apply]) hπ

omit [TopologicalSpace G] in
/-- Transport along the identity changes nothing. -/
@[simp]
theorem _root_.ContRepresentation.congr_refl (π : ContRepresentation 𝕜 G V) :
    congr (ContinuousLinearEquiv.refl 𝕜 V) π = π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

omit [TopologicalSpace G] in
/-- Transporting twice is transporting along the composite. -/
@[simp]
theorem congr_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : V ≃L[𝕜] W)
    (f : W ≃L[𝕜] X) (π : ContRepresentation 𝕜 G V) :
    congr f (congr e π) = congr (e.trans f) π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

end Congr

section CongrIsometry

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

omit [TopologicalSpace G] in
/-- Transport along a linear isometry equivalence preserves unitarity: `e` and `e⁻¹` preserve the
inner product, so the conjugated operators do exactly when the original ones do. -/
theorem _root_.ContRepresentation.IsUnitary.congr {π : ContRepresentation 𝕜 G V}
    (hπ : IsUnitary π) (e : V ≃ₗᵢ[𝕜] W) :
    IsUnitary (ContinuousLinearEquiv.congr e.toContinuousLinearEquiv π) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by simp [hπ.norm_map]

-- The `simp` lemmas below take the continuity of the transported representation, as it occurs on
-- the left-hand side, and derive that of `π` on the right: a hypothesis occurring on the left only
-- inside a proof is not assigned by unification, and `simp` cannot prove it for a symbolic `π`.
/-- **Transport along a linear isometry equivalence does not change matrix coefficients.** The
matrix coefficient of the transported representation at the transported vectors is the matrix
coefficient of the original. -/
@[simp]
theorem _root_.LinearIsometryEquiv.matrixCoeff_congr (e : V ≃ₗᵢ[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous (congr e.toContinuousLinearEquiv π)) (v w : V) :
    matrixCoeff (congr e.toContinuousLinearEquiv π) hπ (e v) (e w) =
      matrixCoeff π (by simpa using continuous_congr e.toContinuousLinearEquiv.symm hπ) v w := by
  ext g
  simp

end CongrIsometry

section CongrAdjoint

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- **Transport along an arbitrary continuous linear equivalence moves matrix coefficients along
`e` and along the adjoint of `e⁻¹`.** For an `e` that is not isometric the second vector has to be
moved by `(e⁻¹)†` rather than by `e`, since it is paired with the transported vector rather than
transported itself.

This is `LinearIsometryEquiv.matrixCoeff_congr` with the isometry hypothesis dropped: for a
linear isometry equivalence `(e⁻¹)† = e`, and the two statements agree. It is what says that being
a matrix coefficient depends only on the *equivalence class* of a representation, so a
representation may be replaced by any conjugate of it — for instance by a unitary one. -/
@[simp]
theorem matrixCoeff_congr_adjoint (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous (congr e π)) (v w : V) :
    matrixCoeff (congr e π) hπ (e v) (ContinuousLinearMap.adjoint (e.symm : W →L[𝕜] V) w) =
      matrixCoeff π (by simpa using continuous_congr e.symm hπ) v w := by
  ext g
  rw [matrixCoeff_apply, matrixCoeff_apply, congr_apply, ContinuousLinearMap.adjoint_inner_right]
  simp

end CongrAdjoint

end ContinuousLinearEquiv

namespace ContRepresentation

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The transport of a representation is equivalent to it**, along `e` itself: `e` intertwines
`π` with `ContinuousLinearEquiv.congr e π` by the very definition of the transported action.

This is the bundled form of that observation, and it is what carries a statement about the
transport back to `π`: an `Equiv` is an isomorphism in the category of continuous representations,
so `π` and `congr e π` have the same subrepresentation lattice, the same irreducible constituents
and the same character. `congrEquiv_apply` and `congrEquiv_symm_apply` evaluate it and its inverse
as `e` and `e.symm`. -/
noncomputable def congrEquiv (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) :
    π.Equiv (ContinuousLinearEquiv.congr e π) :=
  .mk e fun g ↦ ContinuousLinearMap.ext fun v ↦ by simp

@[simp]
theorem congrEquiv_toContinuousLinearEquiv (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) :
    (π.congrEquiv e).toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem congrEquiv_apply (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) (v : V) :
    π.congrEquiv e v = e v :=
  (rfl)

@[simp]
theorem congrEquiv_symm_apply (π : ContRepresentation 𝕜 G V) (e : V ≃L[𝕜] W) (w : W) :
    (π.congrEquiv e).symm w = e.symm w :=
  (rfl)

end ContRepresentation
end
end TAF_LiteralSource_0419

section TAF_LiteralSource_0420
/- Original module: TauCeti.RepresentationTheory.Continuous.Representative -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The representative ring of a monoid with a topology

A **representative function** on a monoid `G` equipped with a topology is a matrix coefficient of a
finite-dimensional continuous representation of `G`. Their span
`TauCeti.representativeSubmodule` is the **representative ring** `𝓡(G) ⊆ C(G, 𝕜)`, and the point of
this file is that the span is far more than a subspace: it is a `*`-subalgebra,
`TauCeti.representativeStarSubalgebra`.

Three constructions supply the three closure properties, and each is a statement about
representations rather than about functions:

* the **trivial** representation on `𝕜` gives the constants
  (`TauCeti.isRepresentative_one`);
* the **tensor product** of two representations multiplies their matrix coefficients
  (`ContRepresentation.matrixCoeff_tprod`), giving closure under multiplication;
* the **conjugate** representation conjugates them
  (`OrthonormalBasis.star_matrixCoeff_eq_matrixCoeff_conjugate`), giving closure under the
  involution of `C(G, 𝕜)`.

Characters are sums of diagonal matrix coefficients, so they lie in `𝓡(G)` as well
(`ContRepresentation.character_mem_representativeSubmodule`).

## Implementation notes

The carrier of a representation cannot be quantified over all types at once, so the *definition*
of a representative function pins the standard models `EuclideanSpace 𝕜 (Fin n)`. Nothing is lost:
`TauCeti.matrixCoeff_mem_representativeSubmodule` says that a matrix coefficient of a continuous
representation on *any* finite-dimensional inner product space is a representative function, by
transporting the representation along the isometry supplied by `stdOrthonormalBasis`
(`ContinuousLinearEquiv.congr`). That transport lemma is what makes the pinned model harmless,
and it is how the closure proofs feed the tensor product `V ⊗ W` and the conjugate back into the
definition. Requiring the carrier to be an inner product space is no restriction on the span
either: over `𝕜` every finite-dimensional space admits an inner product, and every functional on it
is `⟪·, w⟫` for some `w`, so pairing with a functional produces no function beyond these.

No unitarity is required, of `𝓡(G)` or of any lemma about it: none of the three closure properties
uses it, `π ⊗ ρ` and the conjugate of `π` being available for an arbitrary continuous `π`. The
unitary case is used for Schur orthogonality and Peter-Weyl. Preservation of unitarity is recorded
with each of the three constructions
(`ContRepresentation.IsUnitary.tprod`, `OrthonormalBasis.isUnitary_conjugate`,
`ContRepresentation.IsUnitary.congr`); on a *compact* group the distinction is empty
anyway, since Haar averaging unitarizes.

Neither `TauCeti.IsRepresentative` nor `TauCeti.representativeSubmodule` exposes its
implementation. What downstream arguments need of them is supplied by
`TauCeti.isRepresentative_iff`, which produces a representation from a representative function, and
`TauCeti.representativeSubmodule_eq_span`, which is what an induction over the span runs on.

**Point separation is deliberately absent.** That `𝓡(G)` separates the points of a compact `G` is
equivalent to the Peter-Weyl theorem, so it cannot be recorded at this stage without circularity;
it is a corollary of the analytic density theorem, proved in
`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`, not an input to it.

## Main definitions

* `TauCeti.IsRepresentative`: being a matrix coefficient of a finite-dimensional continuous
  representation.
* `TauCeti.representativeSubmodule`: the span of the representative functions.
* `TauCeti.representativeStarSubalgebra`: that span, as a `*`-subalgebra of `C(G, 𝕜)`.

## Main statements

* `TauCeti.isRepresentative_iff` and `TauCeti.representativeSubmodule_eq_span`: the elimination
  principles for the two definitions.
* `TauCeti.matrixCoeff_mem_representativeSubmodule`: every matrix coefficient of a
  finite-dimensional continuous representation lies in `𝓡(G)`.
* `TauCeti.IsRepresentative.mul`, `TauCeti.IsRepresentative.star`,
  `TauCeti.isRepresentative_one`, `TauCeti.isRepresentative_zero`: the representative functions
  themselves are closed under multiplication and conjugation and contain the constants and `0`.
* `TauCeti.mul_mem_representativeSubmodule`, `TauCeti.star_mem_representativeSubmodule`: the same
  closure properties for their span.
* `ContRepresentation.character_mem_representativeSubmodule`: characters lie in `𝓡(G)`.

The uniform density of this algebra in `C(G)` is the analytic core of Peter-Weyl. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and
T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Chapter III.
-/

public section

open _root_.ContRepresentation

open scoped InnerProductSpace

namespace TauCeti

section Defs

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

/-- **A representative function** on `G`: a matrix coefficient of a finite-dimensional continuous
representation. The carrier is pinned to a standard model `EuclideanSpace 𝕜 (Fin n)`, which by
`TauCeti.isRepresentative_matrixCoeff` is no restriction. -/
def IsRepresentative (f : C(G, 𝕜)) : Prop :=
  ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))) (hπ : Continuous π)
    (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w

/-- Being a representative function is exhibiting the function as a matrix coefficient of a
continuous representation on a standard model. -/
theorem isRepresentative_iff {f : C(G, 𝕜)} :
    IsRepresentative f ↔ ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
      (hπ : Continuous π) (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w :=
  (Iff.rfl)

variable (𝕜 G) in
/-- **The representative ring `𝓡(G)`**, as a submodule of `C(G, 𝕜)`: the span of the matrix
coefficients of the finite-dimensional continuous representations of `G`. -/
def representativeSubmodule : Submodule 𝕜 C(G, 𝕜) :=
  Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f}

variable (𝕜 G) in
/-- The representative ring is the span of the representative functions. -/
theorem representativeSubmodule_eq_span :
    representativeSubmodule 𝕜 G = Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f} :=
  (rfl)

/-- A representative function lies in the representative ring. -/
theorem mem_representativeSubmodule_of_isRepresentative {f : C(G, 𝕜)} (hf : IsRepresentative f) :
    f ∈ representativeSubmodule 𝕜 G :=
  Submodule.subset_span hf

end Defs

section Membership

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Every matrix coefficient is representative.** A matrix coefficient of a continuous
representation on an arbitrary finite-dimensional inner product space is a representative function:
transporting the representation along `(stdOrthonormalBasis 𝕜 V).repr` puts it on a standard model
without changing its matrix coefficients. -/
theorem isRepresentative_matrixCoeff (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (v w : V) :
    IsRepresentative (matrixCoeff π hπ v w) :=
  ⟨Module.finrank 𝕜 V,
    ContinuousLinearEquiv.congr (stdOrthonormalBasis 𝕜 V).repr.toContinuousLinearEquiv π,
    ContinuousLinearEquiv.continuous_congr _ hπ, _, _,
    (LinearIsometryEquiv.matrixCoeff_congr (stdOrthonormalBasis 𝕜 V).repr
        (ContinuousLinearEquiv.continuous_congr _ hπ) v w).symm⟩

/-- Every matrix coefficient of a finite-dimensional continuous representation lies in `𝓡(G)`. -/
theorem matrixCoeff_mem_representativeSubmodule (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (v w : V) :
    matrixCoeff π hπ v w ∈ representativeSubmodule 𝕜 G :=
  mem_representativeSubmodule_of_isRepresentative (isRepresentative_matrixCoeff π hπ v w)

end Membership

section Algebra

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

variable (𝕜 G) in
/-- **The constants are representative.** The constant function `1` is the matrix coefficient of the
trivial one-dimensional representation at the unit vector `1 : 𝕜`. -/
theorem isRepresentative_one : IsRepresentative (1 : C(G, 𝕜)) := by
  have h : (1 : C(G, 𝕜)) =
      matrixCoeff (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const (1 : 𝕜) (1 : 𝕜) := by
    rw [matrixCoeff_trivial]
    ext g
    simp
  rw [h]
  exact isRepresentative_matrixCoeff _ _ _ _

variable (𝕜 G) in
/-- **The zero function is representative.** It is the matrix coefficient of the trivial
one-dimensional representation at the zero vector. -/
theorem isRepresentative_zero : IsRepresentative (0 : C(G, 𝕜)) := by
  simpa only [matrixCoeff_zero_left (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const] using
    isRepresentative_matrixCoeff (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const
      (0 : 𝕜) (0 : 𝕜)

variable (𝕜 G) in
/-- The constant function `1` lies in `𝓡(G)`. -/
theorem one_mem_representativeSubmodule : (1 : C(G, 𝕜)) ∈ representativeSubmodule 𝕜 G :=
  mem_representativeSubmodule_of_isRepresentative (isRepresentative_one 𝕜 G)

/-- **A product of representative functions is representative**: the product of a matrix coefficient
of `π` and one of `ρ` is a matrix coefficient of `π ⊗ ρ`. -/
theorem IsRepresentative.mul {a b : C(G, 𝕜)} (ha : IsRepresentative a)
    (hb : IsRepresentative b) : IsRepresentative (a * b) := by
  obtain ⟨n, π, hπ, v, w, rfl⟩ := ha
  obtain ⟨m, ρ, hρ, v', w', rfl⟩ := hb
  rw [← matrixCoeff_tprod π ρ hπ hρ v w v' w']
  exact isRepresentative_matrixCoeff _ _ _ _

/-- **The conjugate of a representative function is representative**: the conjugate of a matrix
coefficient of `π` is a matrix coefficient of the conjugate of `π`. -/
theorem IsRepresentative.star {a : C(G, 𝕜)} (ha : IsRepresentative a) :
    IsRepresentative (star a) := by
  obtain ⟨n, π, hπ, v, w, rfl⟩ := ha
  rw [OrthonormalBasis.star_matrixCoeff_eq_matrixCoeff_conjugate (EuclideanSpace.basisFun (Fin n)
      𝕜) π hπ v w]
  exact isRepresentative_matrixCoeff _ _ _ _

/-- **`𝓡(G)` is closed under multiplication.** -/
theorem mul_mem_representativeSubmodule {a b : C(G, 𝕜)} (ha : a ∈ representativeSubmodule 𝕜 G)
    (hb : b ∈ representativeSubmodule 𝕜 G) : a * b ∈ representativeSubmodule 𝕜 G := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact mem_representativeSubmodule_of_isRepresentative (hx.mul hy)
  | zero_left y _ => simp
  | zero_right x _ => simp
  | add_left x y z _ _ _ ihx ihy => rw [add_mul]; exact add_mem ihx ihy
  | add_right x y z _ _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul_left c x y _ _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih
  | smul_right c x y _ _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih

/-- **`𝓡(G)` is closed under the involution of `C(G, 𝕜)`.** -/
theorem star_mem_representativeSubmodule {a : C(G, 𝕜)} (ha : a ∈ representativeSubmodule 𝕜 G) :
    star a ∈ representativeSubmodule 𝕜 G := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact mem_representativeSubmodule_of_isRepresentative hx.star
  | zero => simp
  | add x y _ _ ihx ihy => rw [star_add]; exact add_mem ihx ihy
  | smul c x _ ih => rw [star_smul]; exact Submodule.smul_mem _ _ ih

variable (𝕜 G) in
/-- **The representative ring as a `*`-subalgebra of `C(G, 𝕜)`.** The span of the matrix
coefficients of the finite-dimensional continuous representations of `G` contains the constants,
and is closed under multiplication and under conjugation. -/
def representativeStarSubalgebra : StarSubalgebra 𝕜 C(G, 𝕜) where
  carrier := representativeSubmodule 𝕜 G
  mul_mem' := mul_mem_representativeSubmodule
  add_mem' := add_mem
  zero_mem' := zero_mem _
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (one_mem_representativeSubmodule 𝕜 G)
  star_mem' := star_mem_representativeSubmodule

/-- Membership in the representative `*`-subalgebra is membership in its underlying span. -/
@[simp]
theorem mem_representativeStarSubalgebra_iff {f : C(G, 𝕜)} :
    f ∈ representativeStarSubalgebra 𝕜 G ↔ f ∈ representativeSubmodule 𝕜 G :=
  Iff.rfl

end Algebra

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The character of a finite-dimensional continuous representation lies in `𝓡(G)`.** Its
conjugate is the sum of the diagonal matrix coefficients, and `𝓡(G)` is closed under
conjugation. -/
theorem _root_.ContRepresentation.character_mem_representativeSubmodule
    (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    character π hπ ∈ representativeSubmodule 𝕜 G := by
  have h : character π hπ =
      star (∑ i, matrixCoeff π hπ (stdOrthonormalBasis 𝕜 V i) (stdOrthonormalBasis 𝕜 V i)) := by
    rw [← star_character π hπ (stdOrthonormalBasis 𝕜 V), star_star]
  rw [h]
  exact star_mem_representativeSubmodule
    (Submodule.sum_mem _ fun i _ ↦ matrixCoeff_mem_representativeSubmodule π hπ _ _)

end ContRepresentation

end TauCeti
end
end TAF_LiteralSource_0420

section TAF_LiteralSource_0421
/- Original module: TauCeti.RepresentationTheory.Compact.UnitaryModel -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The unitary model of a finite-dimensional representation of a compact group

Weyl's unitarian trick, in `TauCeti/RepresentationTheory/Compact/Unitarizable.lean`, averages the
inner product of a continuous representation `π` of a compact group over Haar measure and records
the averaged form through its Gram operator `S`, a positive-definite self-adjoint operator with
`(π g)† ∘ S ∘ (π g) = S`. That is an invariant form, not yet a unitary representation: Lean fixes
one `InnerProductSpace` structure on the carrier, and `π` is in general not unitary for it.

This file closes the gap in finite dimensions. Changing coordinates by the automorphism `A` that
standardizes the invariant form
(`TauCeti.exists_continuousLinearEquiv_inner_map_map`, morally `A = S ^ (-1 / 2)`) conjugates `π`
into a representation that *is* unitary for the given inner product:

`ContRepresentation.exists_isUnitary_congr` produces `e : V ≃L[𝕜] V` with
`IsUnitary (congr e π)`.

What this buys is a replacement of `π` by an equivalent representation, not by `π` itself, so a
property may be proved for unitary representations alone exactly when it is invariant under
conjugation by a continuous linear automorphism. The two consequences recorded here are the form
that fact is consumed in, and both are of that kind: a matrix coefficient of an arbitrary
finite-dimensional continuous representation is a matrix coefficient of a unitary one, and hence
the representative ring `𝓡(G)` is spanned by the matrix coefficients of the **unitary**
finite-dimensional continuous representations alone.

## Main statements

* `ContRepresentation.exists_isUnitary_congr`: a finite-dimensional continuous
  representation of a compact group is conjugate to a unitary one.
* `ContRepresentation.exists_isUnitary_matrixCoeff_eq`: its matrix coefficients are matrix
  coefficients of a unitary representation.
* `TauCeti.isRepresentative_iff_exists_isUnitary`: a representative function is a matrix
  coefficient of a unitary representation on a standard model.

## Implementation notes

The conjugating automorphism is not asked to be canonical:
`TauCeti.exists_continuousLinearEquiv_inner_map_map` chooses an eigenbasis of the Gram operator,
and only its existence is exported. Nothing downstream needs more, since the unitary structure it
produces is unique up to a unitary equivalence anyway.

Finite dimensionality enters only through that standardization, which is proved by the spectral
theorem; the Gram operator itself is built for an arbitrary Hilbert-space carrier.

Unitarization allows the matrix coefficients of arbitrary representations to be expanded in those
of unitary irreducible representations. The mathematical development follows Daniel Bump,
*Lie Groups*, second edition, Chapter 2.
-/

public section

open _root_.ContRepresentation

open MeasureTheory RCLike TauCeti TauCeti.ContRepresentation
open scoped InnerProductSpace

namespace ContRepresentation

section Unitarization

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

private local instance instCompleteSpaceUnitaryModel : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

/-- **A finite-dimensional continuous representation of a compact group is conjugate to a unitary
one.** There is a continuous linear automorphism `e` of the carrier for which the transported
representation `ContinuousLinearEquiv.congr e π` preserves the inner product.

This is the unitarian trick in its usable form. Haar averaging supplies the invariant
positive-definite form `⟪S ·, ·⟫`; the automorphism `A` carrying the standard inner product to
that form (`TauCeti.exists_continuousLinearEquiv_inner_map_map`) conjugates the invariance of the
form into unitarity of `A⁻¹ ∘ π · ∘ A`. -/
theorem exists_isUnitary_congr (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ e : V ≃L[𝕜] V, IsUnitary (ContinuousLinearEquiv.congr e π) := by
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_inner_map_map (π.gramOperator hπ)
    (π.isSymmetric_gramOperator hπ) fun _ hv ↦ π.re_inner_gramOperator_self_pos hπ hv
  -- The same standardization with the Gram operator on the second argument, which is the side
  -- `inner_gramOperator_map_map` states invariance of the averaged form on.
  have hA' : ∀ x y : V, ⟪A x, π.gramOperator hπ (A y)⟫_𝕜 = ⟪x, y⟫_𝕜 := fun x y ↦ by
    rw [← inner_conj_symm, hA, inner_conj_symm]
  have hunitary : ∀ (g : G) (x y : V), ⟪ContinuousLinearEquiv.congr A.symm π g x,
      ContinuousLinearEquiv.congr A.symm π g y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
    intro g x y
    rw [ContinuousLinearEquiv.congr_apply, ContinuousLinearEquiv.congr_apply,
        ContinuousLinearEquiv.symm_symm,
      ← hA' (A.symm (π g (A x))) (A.symm (π g (A y))), ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, π.inner_gramOperator_map_map hπ, hA']
  exact ⟨A.symm, (isUnitary_iff_norm_map _).mpr fun g ↦
    (LinearMap.norm_map_iff_inner_map_map _).mpr (hunitary g)⟩

/-- **A matrix coefficient of a finite-dimensional continuous representation of a compact group is
a matrix coefficient of a unitary one**, on the same carrier and at suitably moved vectors.

Matrix coefficients depend only on the equivalence class of a representation
(`ContinuousLinearEquiv.matrixCoeff_congr_adjoint`), so the conjugate unitary model produced
by `ContRepresentation.exists_isUnitary_congr` produces every matrix coefficient of the
original. -/
theorem exists_isUnitary_matrixCoeff_eq (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) :
    ∃ (ρ : ContRepresentation 𝕜 G V) (hρ : Continuous ρ), IsUnitary ρ ∧
      ∃ v' w' : V, matrixCoeff π hπ v w = matrixCoeff ρ hρ v' w' :=
  let ⟨e, he⟩ := exists_isUnitary_congr π hπ
  ⟨ContinuousLinearEquiv.congr e π, ContinuousLinearEquiv.continuous_congr e hπ, he, e v,
      ContinuousLinearMap.adjoint (e.symm : V →L[𝕜] V) w,
    (ContinuousLinearEquiv.matrixCoeff_congr_adjoint e (ContinuousLinearEquiv.continuous_congr e
        hπ) v w).symm⟩

end Unitarization

end ContRepresentation

namespace TauCeti

section Representative

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **The representative functions of a compact group are the matrix coefficients of its unitary
finite-dimensional continuous representations.** Restricting the representations allowed in the
definition of `TauCeti.IsRepresentative` to the unitary ones changes nothing.

The forward direction is unitarization; the reverse is the definition. Consequently the
representative ring `𝓡(G)`, whose uniform density in `C(G, 𝕜)` is the analytic core of the
Peter-Weyl theorem, is spanned by the matrix coefficients of unitary representations, which are
the ones Schur orthogonality applies to. -/
theorem isRepresentative_iff_exists_isUnitary {f : C(G, 𝕜)} :
    IsRepresentative f ↔ ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
      (hπ : Continuous π), ContRepresentation.IsUnitary π ∧
        ∃ v w : EuclideanSpace 𝕜 (Fin n), f = ContRepresentation.matrixCoeff π hπ v w := by
  rw [isRepresentative_iff]
  constructor
  · rintro ⟨n, π, hπ, v, w, rfl⟩
    obtain ⟨ρ, hρ, hunitary, v', w', hvw⟩ :=
      π.exists_isUnitary_matrixCoeff_eq hπ v w
    exact ⟨n, ρ, hρ, hunitary, v', w', hvw⟩
  · rintro ⟨n, π, hπ, -, v, w, rfl⟩
    exact ⟨n, π, hπ, v, w, rfl⟩

end Representative

end TauCeti
end
end TAF_LiteralSource_0421

section TAF_LiteralSource_0422
/- Original module: TauCeti.RepresentationTheory.Continuous.InvariantComplement -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Invariant complements of unitary continuous representations

For a unitary representation of a *group* the orthogonal complement of an invariant subspace is
again invariant, so an invariant subspace admitting an orthogonal projection has an invariant
complement. This is the averaging-free half of complete reducibility: it needs no measure, only
that every action operator preserves the inner product.

Invariance of a submodule is Mathlib's `Representation.invtSubmodule`, the sublattice of submodules
invariant under every action operator, and semisimplicity is Mathlib's
`Representation.IsSemisimpleRepresentation`, the statement that the lattice of subrepresentations is
complemented.

## Main definitions

* `ContRepresentation.IsUnitary.orthogonalSubrepresentation`: the orthogonal complement of
  a subrepresentation of a unitary representation, as a subrepresentation.
* `ContRepresentation.IsUnitary.starProjectionIntertwiner`: the orthogonal projection onto
  an invariant subspace, as a continuous intertwining map.

## Main results

* `ContRepresentation.IsUnitary.orthogonal_mem_invtSubmodule`: for a unitary representation
  of a group, the orthogonal complement of an invariant submodule is invariant. The element form is
  `ContRepresentation.IsUnitary.apply_mem_orthogonal`.
* `ContRepresentation.IsUnitary.isCompl_orthogonalSubrepresentation`: a subrepresentation
  admitting an orthogonal projection is complemented by its orthogonal complement.
* `ContRepresentation.IsUnitary.sup_orthogonalSubrepresentation_inf`: a subrepresentation
  together with its orthogonal complement inside a larger one recovers the larger one.
* `ContRepresentation.IsUnitary.starProjection_apply_comm`: the orthogonal projection onto
  an invariant subspace commutes with the action.
* `ContRepresentation.IsUnitary.isSemisimpleRepresentation` and
  `ContRepresentation.IsUnitary.isSemisimpleModule_asModule`: complete reducibility of a
  finite-dimensional unitary continuous representation, in the subrepresentation-lattice form and
  as semisimplicity of the group-algebra module.

## Implementation notes

The hypothesis that `G` is a group is essential and is not a convenience: the unilateral shift is a
unitary representation of the monoid `ℕ` on `ℓ²` for which the orthogonal complement of an
invariant subspace need not be invariant. What the proof uses is that the action of `g⁻¹` carries
the invariant subspace back into itself.

Nothing here assumes `V` complete. Mathlib's `ContinuousLinearMap.orthogonal_mem_invtSubmodule`
draws the same conclusion for a single operator `T`, from invariance under `T.adjoint`, but
`ContinuousLinearMap.adjoint` is available only on a complete space, so that route would force
`[CompleteSpace V]` on every statement below. Instead `IsUnitary.inner_map_right` moves the action
across the inner product by inverting the group element, which needs no completeness. Mathlib keeps
a completeness-free counterpart of the same result for symmetric operators, namely
`LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule`.

Complementation of a single subrepresentation asks only for an orthogonal projection onto it. The
semisimplicity statement, which asks it of *every* subrepresentation, is stated in finite
dimensions, where every subspace is complete and hence has one. It is false for a general
infinite-dimensional unitary representation, whose invariant subspaces decompose it as a Hilbert
direct sum but not as an algebraic one.

## References

The mathematical development follows Daniel
Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

/-! ### The orthogonal complement of an invariant subspace -/

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

namespace IsUnitary

variable {W : Submodule 𝕜 V}

/-- For a unitary representation of a group, the action carries the orthogonal complement of an
invariant subspace into itself. -/
theorem apply_mem_orthogonal (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (g : G) {v : V}
    (hv : v ∈ Wᗮ) : π g v ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [hπ.inner_map_right]
  exact hv _ (hW g⁻¹ u hu)

/-- **Invariant complements.** For a unitary representation of a group, the orthogonal complement
of an invariant submodule is again invariant. -/
theorem orthogonal_mem_invtSubmodule (hπ : IsUnitary π)
    (hW : W ∈ π.toRepresentation.invtSubmodule) : Wᗮ ∈ π.toRepresentation.invtSubmodule := by
  rw [Representation.mem_invtSubmodule] at hW ⊢
  exact fun g _ hv => hπ.apply_mem_orthogonal (fun g' _ hu => hW g' hu) g hv

/-- The orthogonal complement of a subrepresentation of a unitary representation, as a
subrepresentation. -/
def orthogonalSubrepresentation (hπ : IsUnitary π) (σ : Subrepresentation π.toRepresentation) :
    Subrepresentation π.toRepresentation where
  toSubmodule := σ.toSubmoduleᗮ
  apply_mem_toSubmodule g _ hv :=
    hπ.apply_mem_orthogonal (fun g' _ hu => σ.apply_mem_toSubmodule g' hu) g hv

@[simp]
theorem toSubmodule_orthogonalSubrepresentation (hπ : IsUnitary π)
    (σ : Subrepresentation π.toRepresentation) :
    (hπ.orthogonalSubrepresentation σ).toSubmodule = σ.toSubmoduleᗮ :=
  (rfl)

section Projection

variable [W.HasOrthogonalProjection]

/-- The orthogonal projection onto an invariant subspace of a unitary representation commutes with
the action. -/
theorem starProjection_apply_comm (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (g : G)
    (v : V) : W.starProjection (π g v) = π g (W.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal' (z := π g (v - W.starProjection v))
    (hW g _ (W.starProjection_apply_mem v))
    (hπ.apply_mem_orthogonal hW g (W.sub_starProjection_mem_orthogonal v)) ?_
  rw [← map_add, add_sub_cancel]

/-- The orthogonal projection onto an invariant subspace of a unitary representation, as a
continuous intertwining map. -/
noncomputable def starProjectionIntertwiner (hπ : IsUnitary π)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContIntertwiningMap π π where
  __ := W.starProjection
  isIntertwining' g := by
    ext v
    exact hπ.starProjection_apply_comm hW g v

@[simp]
theorem toContinuousLinearMap_starProjectionIntertwiner (hπ : IsUnitary π)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) :
    (hπ.starProjectionIntertwiner hW).toContinuousLinearMap = W.starProjection :=
  (rfl)

@[simp]
theorem starProjectionIntertwiner_apply (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (v : V) :
    hπ.starProjectionIntertwiner hW v = W.starProjection v :=
  (rfl)

end Projection

/-- A subrepresentation of a unitary representation is complemented by its orthogonal complement,
as soon as it admits an orthogonal projection. -/
theorem isCompl_orthogonalSubrepresentation (hπ : IsUnitary π)
    (σ : Subrepresentation π.toRepresentation) [σ.toSubmodule.HasOrthogonalProjection] :
    IsCompl σ (hπ.orthogonalSubrepresentation σ) := by
  have h : IsCompl σ.toSubmodule σ.toSubmoduleᗮ := σ.toSubmodule.isCompl_orthogonal
  exact Subrepresentation.isCompl_toSubmodule.mp h

/-- A subrepresentation, together with its orthogonal complement taken inside a larger
subrepresentation, recovers that larger subrepresentation. This is
`Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection` read in the lattice of
subrepresentations, which is legitimate because unitarity makes the orthogonal complement
invariant. -/
theorem sup_orthogonalSubrepresentation_inf (hπ : IsUnitary π)
    {σ τ : Subrepresentation π.toRepresentation} (h : σ ≤ τ)
    [σ.toSubmodule.HasOrthogonalProjection] :
    σ ⊔ hπ.orthogonalSubrepresentation σ ⊓ τ = τ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
    toSubmodule_orthogonalSubrepresentation]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (Subrepresentation.toSubmodule_le_toSubmodule.mpr h)

/-! ### Complete reducibility in finite dimensions -/

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

/-- **Complete reducibility.** A finite-dimensional unitary continuous representation of a group is
semisimple: every subrepresentation has a complement. -/
theorem isSemisimpleRepresentation (hπ : IsUnitary π) :
    Representation.IsSemisimpleRepresentation π.toRepresentation :=
  ⟨fun σ => ⟨_, hπ.isCompl_orthogonalSubrepresentation σ⟩⟩

/-- **Complete reducibility, algebraic form.** The group-algebra module of a finite-dimensional
unitary continuous representation of a group is semisimple. -/
theorem isSemisimpleModule_asModule (hπ : IsUnitary π) :
    IsSemisimpleModule (MonoidAlgebra 𝕜 G) π.toRepresentation.asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
    π.toRepresentation).mp hπ.isSemisimpleRepresentation

end FiniteDimensional

end IsUnitary

end Unitary

end ContRepresentation
end
end TAF_LiteralSource_0422

section TAF_LiteralSource_0423
/- Original module: TauCeti.RepresentationTheory.Compact.Semisimple -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Complete reducibility for compact groups

A finite-dimensional representation of a compact group over `ℝ` or `ℂ` whose matrix coefficients
are continuous is semisimple: every subrepresentation has an invariant complement. This is
Maschke's theorem with Haar averaging in place of the average over a finite group.

The statement is about a plain `Representation` on a vector space without any chosen topology or
inner product, so that it applies to representations built algebraically, such as the restriction
of a rational representation of `GL n ℂ` to the unitary group. The continuity hypothesis is
stated through linear functionals: `g ↦ f (ρ g v)` is continuous for every vector `v` and every
linear functional `f`.

The proof transports the representation, along a basis, to a continuous representation on the
Euclidean space `EuclideanSpace 𝕜 (Fin d)`. The unitarian trick
(`ContRepresentation.exists_isUnitary_congr`) conjugates that one into a unitary representation,
in which the orthogonal complement of a subrepresentation is invariant
(`ContRepresentation.IsUnitary.isCompl_orthogonalSubrepresentation`); pulling that complement back
along the composite equivalence gives the complement in the original representation.

## Main results

* `Representation.isSemisimpleRepresentation_of_continuous`: a finite-dimensional representation
  of a compact group with continuous matrix coefficients is semisimple.

## References

* D. Bump, *Lie Groups*, second edition, Springer GTM 225 (2013), Chapter 2, Proposition 2.1.
-/

public section

open ContRepresentation

namespace Representation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Complete reducibility for compact groups.** A finite-dimensional representation of a compact
group whose matrix coefficients `g ↦ f (ρ g v)` are continuous is semisimple: every
subrepresentation has an invariant complement. -/
theorem isSemisimpleRepresentation_of_continuous (ρ : Representation 𝕜 G V)
    (hρ : ∀ (f : Module.Dual 𝕜 V) (v : V), Continuous fun g => f (ρ g v)) :
    ρ.IsSemisimpleRepresentation := by
  borelize G
  let b := Module.finBasis 𝕜 V
  -- Transport `ρ` to a continuous representation on a Euclidean space along the basis `b`.
  let T : V ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V)) :=
    b.equivFun.trans (EuclideanSpace.equiv _ 𝕜).symm.toLinearEquiv
  let π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V))) := .ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap (T.conj (ρ g))
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
  have hπT (g : G) (v : V) : π g (T v) = T (ρ g v) :=
    -- `π g` is `T ∘ ρ g ∘ T⁻¹` by definition.
    congrArg (fun w => T (ρ g w)) (T.symm_apply_apply v)
  have hπ : Continuous π := by
    refine continuous_clm_apply.mpr fun y => ?_
    refine (EuclideanSpace.equiv _ 𝕜).symm.continuous.comp (continuous_pi fun i => ?_)
    exact hρ (b.coord i) (T.symm y)
  obtain ⟨e, he⟩ := exists_isUnitary_congr π hπ
  -- The composite equivalence intertwines `ρ` with the unitary model `e.congr π`.
  let T' := T.trans (e : _ ≃L[𝕜] _).toLinearEquiv
  have hT' (g : G) (v : V) : e.congr π g (T' v) = T' (ρ g v) := by
    rw [ContinuousLinearEquiv.congr_apply]
    simp [T', hπT]
  refine ⟨fun p => ?_⟩
  let S : Subrepresentation (e.congr π).toRepresentation :=
    { toSubmodule := p.toSubmodule.map T'
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨ρ g v, p.apply_mem_toSubmodule g hv, ?_⟩
        exact (hT' g v).symm }
  let q : Subrepresentation ρ :=
    { toSubmodule := (he.orthogonalSubrepresentation S).toSubmodule.comap (T' : V →ₗ[𝕜] _)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [← hT']
        exact (he.orthogonalSubrepresentation S).apply_mem_toSubmodule g hv }
  refine ⟨q, Subrepresentation.isCompl_toSubmodule.mp ?_⟩
  have hc := Subrepresentation.isCompl_toSubmodule.mpr (he.isCompl_orthogonalSubrepresentation S)
  simpa [S, q, Submodule.comap_map_eq_of_injective T'.injective] using
    (Submodule.orderIsoMapComap T').symm.isCompl hc

end Representation
end
end TAF_LiteralSource_0423

section TAF_LiteralSource_0424
/- Original module: TauCeti.Data.Fintype.BigOperators -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sums over finite types

A sum of values that are all equal to `d` on the indices satisfying `p`, and zero elsewhere, is
the number of such indices times `d` (`Fintype.sum_ite_eq_card_nsmul`).

For a finite type `ι` and finite coordinate sets `s i`, a sum over maps taking their `i`th value
in `s i` of a quantity depending only on two distinct coordinates is a sum over the pairs of
values, with each pair counted once for every choice of the remaining coordinates.
Counting arguments use
this to reduce a sum over labelled copies of a pattern to a sum over one pair of its vertices.

More generally, any sum over such a box splits at two distinct coordinates `i` and `j`: sum over
the maps with prescribed values at `i` and `j`, and then over all values of the two coordinates,
substituted with `Function.update`. Telescoping arguments use this to test one pair of
coordinates while the others stay fixed.
-/

public section

open Finset

namespace Fintype

/-- A sum of values `f i` over the indices satisfying `p`, all of which are equal to `d`, is the
number of such indices times `d`. -/
theorem sum_ite_eq_card_nsmul {ι M : Type*} [Fintype ι] [AddCommMonoid M] {p : ι → Prop}
    [DecidablePred p] {f : ι → M} {d : M} (hf : ∀ i, p i → f i = d) :
    (∑ i, if p i then f i else 0) = Fintype.card {i // p i} • d := by
  rw [Fintype.card_subtype, ← sum_filter]
  exact sum_eq_card_nsmul fun i hi ↦ hf i (mem_filter.1 hi).2

/-- A sum of a function of two distinct coordinates over a finite box counts each pair
of values once for every choice of the remaining coordinates. -/
theorem sum_piFinset_apply_apply {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) (F : κ → κ → M) :
    ∑ g ∈ piFinset s, F (g i) (g j) =
      (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
  classical
  have hfib (p : κ × κ) (hp : p ∈ s i ×ˢ s j) :
      #{g ∈ piFinset s | (g i, g j) = p} = ∏ k ∈ univ \ {i, j}, #(s k) := by
    rw [mem_product] at hp
    have hj : p.2 ∈ Function.update s i {p.1} j := by
      simpa [Function.update_of_ne hij.symm] using hp.2
    simp only [Prod.ext_iff, ← filter_filter]
    rw [← piFinset_update_singleton_eq_filter_piFinset_eq s i hp.1,
      ← piFinset_update_singleton_eq_filter_piFinset_eq _ j hj, card_piFinset]
    simp_rw [Function.apply_update (fun _ ↦ Finset.card (α := κ))]
    rw [prod_update_of_mem (mem_univ j), prod_update_of_mem (by simpa using hij)]
    simp only [card_singleton, one_mul]
    congr 1
    ext k
    simp [and_comm]
  rw [← sum_fiberwise_of_maps_to (g := fun g : ι → κ ↦ (g i, g j)) (t := s i ×ˢ s j)
    fun g hg ↦ mem_product.2 ⟨mem_piFinset.1 hg i, mem_piFinset.1 hg j⟩]
  calc ∑ p ∈ s i ×ˢ s j, ∑ g ∈ piFinset s with (g i, g j) = p, F (g i) (g j)
      = ∑ p ∈ s i ×ˢ s j, (∏ k ∈ univ \ {i, j}, #(s k)) • F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← hfib p hp, ← sum_const]
        exact Finset.sum_congr rfl fun g hg ↦ by rw [← (mem_filter.1 hg).2]
    _ = (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
        rw [sum_nsmul, sum_product]

/-- A sum over a finite box splits at two distinct coordinates `i` and `j`: for values
`a ∈ s i` and `b ∈ s j`, each map in the box arises exactly once by overwriting the `i`th and `j`th
values of a map in the box taking the values `a` at `i` and `b` at `j`. -/
theorem sum_piFinset_eq_sum_filter_sum_sum_update {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [AddCommMonoid M] {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) {a b : κ}
    (ha : a ∈ s i) (hb : b ∈ s j) (F : (ι → κ) → M) :
    ∑ g ∈ piFinset s, F g =
      ∑ h ∈ piFinset s with h i = a ∧ h j = b, ∑ x ∈ s i, ∑ y ∈ s j,
        F (Function.update (Function.update h i x) j y) := by
  simp_rw [← sum_product']
  refine sum_nbij' (fun g ↦ (Function.update (Function.update g i a) j b, g i, g j))
    (fun q ↦ Function.update (Function.update q.1 i q.2.1) j q.2.2) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_piFinset, mem_product, mem_filter] at hg ⊢
    refine ⟨⟨fun l ↦ ?_, by simp [hij]⟩, hg i, hg j⟩
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq ⊢
    intro l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro g _
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq
    obtain ⟨⟨-, rfl, rfl⟩, -, -⟩ := hq
    ext l <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all
  · intro g _
    congr 1
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end Fintype
end
end TAF_LiteralSource_0424

section TAF_LiteralSource_0425
/- Original module: TauCeti.RingTheory.SimpleModule.Isotypic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Hom spaces and direct sums of isotypic components

Mathlib shows that the isotypic components of a module are independent
(`sSupIndep_isotypicComponents`) and, for a semisimple module, span it
(`sSup_isotypicComponents`); it reads off the consequence for endomorphisms
(`IsSemisimpleModule.endAlgEquiv`). This file records the consequence for the module itself: a
semisimple module is the internal direct sum of its isotypic components. When there are finitely
many components, for instance when the module is Noetherian, composing with
`DFinsupp.linearEquivFunOnFintype` presents it as their product.

Maps from a simple module `S` into `M` land in its `S`-isotypic component. Restricting the
codomain therefore gives an equivalence of hom spaces, without any semisimplicity or
finiteness assumption on `M`. A map from a simple module into an isotypic module of a different
type is zero (`IsIsotypicOfType.linearMap_eq_zero`). The isotypic components of pairwise
non-isomorphic simple modules are independent (`TauCeti.iSupIndep_isotypicComponent`); this is the
indexed form of Mathlib's `sSupIndep_isotypicComponents`, allowing types that do not occur in the
module.

## Main definitions

* `TauCeti.linearMapIsotypicComponentEquiv`: the hom space from `S` into its isotypic component
  is linearly equivalent to the hom space from `S` into the ambient module.

* `IsSemisimpleModule.linearEquivIsotypicComponents`: a semisimple module is linearly
  equivalent to the direct sum of its isotypic components.

## Main statements

* `TauCeti.finrank_linearMap_isotypicComponent`: restricting the target to its isotypic
  component preserves the `finrank` of the hom space out of the simple module.

* `IsSemisimpleModule.linearEquivIsotypicComponents_apply_coe` and
  `IsSemisimpleModule.linearEquivIsotypicComponents_symm_single`: the equivalence and its
  inverse on a single isotypic component.

* `IsSemisimpleModule.isCompl_isotypicComponent_sSup_sdiff`: an isotypic component is
  complementary to the sum of the other isotypic components.

* `IsSemisimpleModule.exists_forall_smul_eq_ite`: for a semisimple module finite over its
  endomorphism ring, an element of the ring acts as the identity on the simple submodules of a
  given type and as zero on all the others, by Jacobson density.
-/

public section

namespace TauCeti

section Hom

variable {R M S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup S] [Module R S]

/-- A module is its own isotypic component: the top submodule is isomorphic to the module. -/
@[simp]
theorem isotypicComponent_self_eq_top : isotypicComponent R S S = ⊤ :=
  eq_top_iff.mpr <| (Submodule.le_isotypicComponent ⊤).trans_eq
    Submodule.topEquiv.isotypicComponent_eq

variable [IsSimpleModule R S]

/-- A map out of a simple module takes its values in the isotypic component of that type. -/
theorem _root_.LinearMap.apply_mem_isotypicComponent (f : S →ₗ[R] M) (s : S) :
    f s ∈ isotypicComponent R M S := by
  have h := LinearMap.le_comap_isotypicComponent (M := S) (N := M) S f
  rw [isotypicComponent_self_eq_top] at h
  exact h Submodule.mem_top

variable (k : Type*) [CommSemiring k] [Algebra k R] [Module k M] [IsScalarTower k R M]

/-- Composition with the inclusion of the `S`-isotypic component is an equivalence of hom
spaces out of the simple module `S`. Its inverse corestricts a map to that component.
The equivalence is linear over the scalar semiring acting on the target. -/
def linearMapIsotypicComponentEquiv :
    (S →ₗ[R] isotypicComponent R M S) ≃ₗ[k] (S →ₗ[R] M) where
  toFun g := (isotypicComponent R M S).subtype ∘ₗ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.codRestrict _ f.apply_mem_isotypicComponent
  left_inv _ := by ext s; rfl
  right_inv _ := by ext s; rfl

/-- The forward equivalence composes a map into the isotypic component with its inclusion
into the ambient module. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_apply
    (f : S →ₗ[R] isotypicComponent R M S) (s : S) :
    linearMapIsotypicComponentEquiv k f s = f s := (rfl)

/-- The inverse equivalence corestricts a map into the ambient module to its isotypic
component, preserving its values. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_symm_apply (f : S →ₗ[R] M) (s : S) :
    (linearMapIsotypicComponentEquiv k).symm f s =
      ⟨f s, f.apply_mem_isotypicComponent s⟩ := (rfl)

variable {k} in
/-- The `finrank` of a hom space out of `S` is unchanged by restricting the target to its
`S`-isotypic component, because every map out of `S` lands there. The scalar semiring acts only
on the target; no field or scalar action on `S` is needed. -/
@[simp]
theorem finrank_linearMap_isotypicComponent :
    Module.finrank k (S →ₗ[R] isotypicComponent R M S) = Module.finrank k (S →ₗ[R] M) :=
  (linearMapIsotypicComponentEquiv k).finrank_eq

end Hom

end TauCeti

namespace IsIsotypicOfType

variable {R M N S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup S] [Module R S]
  [IsSimpleModule R S]

/-- A map from a simple module into an isotypic module of a different type is zero. -/
theorem linearMap_eq_zero (h : IsIsotypicOfType R M N)
    (hne : ¬ Nonempty (S ≃ₗ[R] N)) (f : S →ₗ[R] M) : f = 0 := by
  obtain hinj | hzero := f.injective_or_eq_zero
  · let e := LinearEquiv.ofInjective f hinj
    have : IsSimpleModule R (LinearMap.range f) := .congr e.symm
    exact False.elim (hne ⟨e.trans (h (LinearMap.range f)).some⟩)
  · exact hzero

end IsIsotypicOfType

namespace IsSemisimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]

/-- **A semisimple module is the direct sum of its isotypic components.** The equivalence sends
an element to its family of components, and its inverse adds the components up. This is the
module-level counterpart of `IsSemisimpleModule.endAlgEquiv`. -/
noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M

variable {R M}

/-- The inverse of `linearEquivIsotypicComponents` sends the family that is `x` at the isotypic
component `c` and zero elsewhere to `x`, viewed as an element of `M`. -/
@[simp]
theorem linearEquivIsotypicComponents_symm_single (c : isotypicComponents R M) (x : c.1) :
    (linearEquivIsotypicComponents R M).symm (DFinsupp.single c x) = x := by
  simp [linearEquivIsotypicComponents]

/-- `linearEquivIsotypicComponents` sends an element `x` of an isotypic component `c`, viewed as an
element of `M`, to the family that is `x` at `c` and zero elsewhere. -/
@[simp]
theorem linearEquivIsotypicComponents_apply_coe {c : isotypicComponents R M} (x : c.1) :
    linearEquivIsotypicComponents R M x = DFinsupp.single c x := by
  rw [← linearEquivIsotypicComponents_symm_single, LinearEquiv.apply_symm_apply]

-- Not `@[simp]`: the component `c` does not occur in the left-hand side, so `simp` could only
-- find it by solving `x ∈ c.1` for `c`. The simp form is
-- `linearEquivIsotypicComponents_apply_coe`, as with `DirectSum.decompose_coe` and
-- `DirectSum.decompose_of_mem`.
/-- An element `x` of `M` lying in an isotypic component `c` is sent by
`linearEquivIsotypicComponents` to the family that is `x` at `c` and zero elsewhere. -/
theorem linearEquivIsotypicComponents_apply_of_mem {c : isotypicComponents R M} {x : M}
    (hx : x ∈ c.1) : linearEquivIsotypicComponents R M x = DFinsupp.single c ⟨x, hx⟩ :=
  linearEquivIsotypicComponents_apply_coe ⟨x, hx⟩

end IsSemisimpleModule

namespace IsSemisimpleModule

section Projection

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **An isotypic component and the other isotypic components are complementary.** In a
semisimple module, the `S`-isotypic component and the sum of all the other isotypic components are
complements. This holds also when `S` does not occur, the component then being zero. -/
theorem isCompl_isotypicComponent_sSup_sdiff [IsSemisimpleModule R M]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsCompl (isotypicComponent R M S)
      (sSup (isotypicComponents R M \ {isotypicComponent R M S})) := by
  constructor
  · by_cases hc : isotypicComponent R M S ∈ isotypicComponents R M
    · exact sSupIndep_isotypicComponents R M hc
    · -- No submodule is isomorphic to `S`, so the isotypic component is zero.
      have hbot : isotypicComponent R M S = ⊥ := sSup_eq_bot.mpr fun m ⟨e⟩ =>
        absurd ⟨m, IsSimpleModule.congr e, e.isotypicComponent_eq.symm⟩ hc
      rw [hbot]
      exact disjoint_bot_left
  · rw [codisjoint_iff, eq_top_iff, ← sSup_isotypicComponents R M]
    refine sSup_le fun d hd => ?_
    by_cases h : d = isotypicComponent R M S
    · exact h ▸ le_sup_left
    · exact (le_sSup (Set.mem_sdiff_of_mem hd h)).trans le_sup_right

open scoped Classical in
/-- **Isotypic projections are actions of ring elements.** For a semisimple module `M` finite over
its endomorphism ring and a simple module `S`, some `a : R` acts as the identity on every simple
submodule of `M` isomorphic to `S` and as zero on every other simple submodule. Its action on `M`
is the projection onto the `S`-isotypic component along the sum of the other isotypic
components. -/
theorem exists_forall_smul_eq_ite [IsSemisimpleModule R M] [Module.Finite (Module.End R M) M]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ a : R, ∀ T : Submodule R M, IsSimpleModule R T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[R] S) then x else 0 := by
  classical
  set c := isotypicComponent R M S
  set c' := sSup (isotypicComponents R M \ {c})
  -- A simple submodule lies in `c` or in `c'`, according to whether it is isomorphic to `S`.
  have hle (T : Submodule R M) (hT : IsSimpleModule R T) :
      (Nonempty (T ≃ₗ[R] S) → T ≤ c) ∧ (¬ Nonempty (T ≃ₗ[R] S) → T ≤ c') := by
    refine ⟨fun h => le_sSup h, fun h => T.le_isotypicComponent.trans (le_sSup ⟨⟨T, hT, rfl⟩, ?_⟩)⟩
    intro hTc
    exact h (isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M S) T
      (T.le_isotypicComponent.trans (Set.mem_singleton_iff.mp hTc).le))
  have hcompl : IsCompl c c' := isCompl_isotypicComponent_sSup_sdiff S
  -- Both summands are fully invariant, so the projection commutes with every endomorphism.
  have hc : c.IsFullyInvariant := .isotypicComponent R M S
  have hc' : c'.IsFullyInvariant :=
    isFullyInvariant_iff_sSup_isotypicComponents.mpr ⟨_, Set.sdiff_subset, rfl⟩
  let π := c.projection c' hcompl
  have hcomm (f : Module.End R M) (x : M) : π (f x) = f (π x) := by
    have hker : x - π x ∈ c' := by
      rw [← Submodule.projection_apply_eq_zero_iff hcompl, map_sub,
        Submodule.projection_apply_of_mem_left hcompl (Submodule.projection_apply_mem hcompl x),
        sub_self]
    have hx : f x = f (π x) + f (x - π x) := by rw [← map_add, add_sub_cancel]
    rw [hx, map_add, Submodule.projection_apply_of_mem_left hcompl
      (hc f (Submodule.projection_apply_mem hcompl x)),
      Submodule.projection_apply_of_mem_right hcompl (hc' f hker), add_zero]
  let F : Module.End (Module.End R M) M :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := fun f x => hcomm f x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := M) F
  refine ⟨a, fun T hT x hx => ?_⟩
  have hax : a • x = π x := congrArg (fun t : Module.End (Module.End R M) M => t x) ha
  rw [hax]
  split_ifs with h
  · exact Submodule.projection_apply_of_mem_left hcompl ((hle T hT).1 h hx)
  · exact Submodule.projection_apply_of_mem_right hcompl ((hle T hT).2 h hx)

end Projection

end IsSemisimpleModule

namespace TauCeti

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The isotypic components of a family of pairwise non-isomorphic simple modules are
independent. -/
theorem iSupIndep_isotypicComponent {κ : Type*} (S : κ → Type*) [∀ j, AddCommGroup (S j)]
    [∀ j, Module R (S j)] [∀ j, IsSimpleModule R (S j)]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) :
    iSupIndep fun j => isotypicComponent R M (S j) := by
  -- Restricted to the nonzero components, the family is an injective reindexing of
  -- `isotypicComponents R M`.
  have hmem (j : κ) (hj : isotypicComponent R M (S j) ≠ ⊥) :
      isotypicComponent R M (S j) ∈ isotypicComponents R M := by
    obtain ⟨N, hN, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hj
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent R M (S j)) N hN
    exact ⟨N, ‹_›, e.isotypicComponent_eq.symm⟩
  rw [← iSupIndep_ne_bot]
  refine ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)).comp
    (f := fun j : {j // isotypicComponent R M (S j) ≠ ⊥} => ⟨_, hmem j.1 j.2⟩) ?_
  intro ⟨i, hi⟩ ⟨j, _⟩ hij
  -- A simple submodule of the common component is a copy of both `S i` and `S j`.
  obtain ⟨N, hN, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hi
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (S i)) N hN
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (S j)) N (hN.trans (congrArg Subtype.val hij).le)
  exact Subtype.ext (hS i j ⟨e.symm.trans e'⟩)

end TauCeti
end
end TAF_LiteralSource_0425

section TAF_LiteralSource_0426
/- Original module: TauCeti.Algebra.Module.Submodule.Quotient -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/


/-!
# Submodule intervals and quotients

This file records the generic order correspondence between a submodule interval and submodules of
the associated quotient, and the identifications of *subquotients* `↥B ⧸ A` that a linear map
induces when it is injective or surjective.

## Main declarations

* `TauCeti.mapIic_symm_apply`: the inverse of `Submodule.mapIic` takes inverse images
  along the inclusion.
* `TauCeti.iccOrderIsoQuotientOfMapEq`: the interval/quotient correspondence for a
  specified copy of the lower endpoint inside the upper endpoint.
* `TauCeti.mapSubquotientEquivOfInjective`: an injective linear map identifies the subquotient of
  the images of two submodules with the subquotient of the two submodules themselves.
* `TauCeti.comapSubquotientEquivOfSurjective`: a surjective linear map identifies the subquotient
  of the preimages of two submodules with the subquotient of the two submodules themselves.
* `LinearMap.quotientEquivRangeQuotientMap`: a linear map whose kernel lies below a submodule
  identifies the quotient by that submodule with the corresponding quotient of its range, and
  `LinearMap.ker_mkQ_comp_rangeRestrict` is the kernel computation behind it.
* `Submodule.quotientEquivPiZModOfBasis`: a quotient by a submodule with a specified diagonal
  basis is a product of cyclic groups with the specified diagonal orders.

## References

The diagonal quotient construction follows Mathlib's
`Submodule.quotientEquivPiSpan` and `Submodule.quotientEquivPiZMod`, with the bases and diagonal
coefficients made explicit so an externally normalized Smith form can be retained.
-/

public section

namespace Submodule

/-- Transport a subquotient across equalities of its ambient and denominator submodules. -/
noncomputable def subquotientEquivOfEq
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') :
    (↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R]
      (↥B' ⧸ Submodule.comap B'.subtype A') := by
  subst A'
  subst B'
  exact LinearEquiv.refl R _

/-- Forward transport preserves the ambient representative. -/
@[simp] theorem subquotientEquivOfEq_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') (x : B) :
    subquotientEquivOfEq A B A' B' hA hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (show B' from ⟨x, by rw [← hB]; exact x.property⟩) := by
  subst A'
  subst B'
  rfl

/-- The inverse transport takes quotient representatives to the same ambient vector. -/
@[simp] theorem subquotientEquivOfEq_symm_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') (x : B') :
    (subquotientEquivOfEq A B A' B' hA hB).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (show B from ⟨x, by rw [hB]; exact x.property⟩) := by
  -- The right representative transports `x : B'` back across `hB : B = B'`.
  subst A'
  subst B'
  rfl

end Submodule

namespace TauCeti

section QuotientInterval

section Order

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The inverse of `Submodule.mapIic` takes the inverse image along the inclusion.  This is the
`symm`-side counterpart of Mathlib's `Submodule.coe_mapIic_apply`. -/
@[simp]
theorem mapIic_symm_apply (p : Submodule R M) (N : Set.Iic p) :
    p.mapIic.symm N = (N : Submodule R M).comap p.subtype :=
  rfl

/-- Submodules of `q` containing a submodule whose ambient image is `p` are the same as ambient
submodules in the interval from `p` to `q`. -/
private def iciSubmoduleOrderIsoIcc {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Ici r ≃o Set.Icc p q where
  toFun N := ⟨(q.mapIic N.1 : Submodule R M), by
    refine ⟨?_, (q.mapIic N.1).2⟩
    rw [Submodule.coe_mapIic_apply, ← hr]
    exact Submodule.map_mono N.2⟩
  invFun N := ⟨q.mapIic.symm ⟨N.1, N.2.2⟩, by
    rw [mapIic_symm_apply]
    exact (Submodule.le_comap_map q.subtype r).trans
      (Submodule.comap_mono (hr.le.trans N.2.1))⟩
  left_inv N := Subtype.ext (q.mapIic.symm_apply_apply N.1)
  right_inv N := by
    apply Subtype.ext
    exact congrArg (fun P : Set.Iic q => (P : Submodule R M))
      (q.mapIic.apply_symm_apply ⟨N.1, N.2.2⟩)
  map_rel_iff' := by
    intro N₁ N₂
    exact Subtype.coe_le_coe.trans q.mapIic.le_iff_le

private theorem coe_iciSubmoduleOrderIsoIcc_symm_apply {p q : Submodule R M}
    (r : Submodule R q) (hr : r.map q.subtype = p) (N : Set.Icc p q) :
    (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) =
      N.1.comap q.subtype :=
  mapIic_symm_apply q ⟨N.1, N.2.2⟩

end Order

section Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The interval correspondence for a specified copy `r` of the lower endpoint inside `q`. -/
def iccOrderIsoQuotientOfMapEq {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Icc p q ≃o Submodule R (q ⧸ r) :=
  (iciSubmoduleOrderIsoIcc r hr).symm.trans (Submodule.comapMkQRelIso r).symm

/-- A representative belongs to the quotient submodule in the interval correspondence exactly
when its underlying ambient element belongs to the corresponding interval submodule. -/
@[simp]
theorem mk_mem_iccOrderIsoQuotientOfMapEq_iff {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) (N : Set.Icc p q) (x : q) :
    Submodule.Quotient.mk x ∈ iccOrderIsoQuotientOfMapEq r hr N ↔
      (x : M) ∈ N.1 := by
  have happly : iccOrderIsoQuotientOfMapEq r hr N =
      (Submodule.comapMkQRelIso r).symm ((iciSubmoduleOrderIsoIcc r hr).symm N) :=
    OrderIso.trans_apply _ _ N
  have hcomap : ((Submodule.comapMkQRelIso r).symm
      ((iciSubmoduleOrderIsoIcc r hr).symm N)).comap r.mkQ =
      (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) :=
    congrArg Subtype.val
      ((Submodule.comapMkQRelIso r).apply_symm_apply ((iciSubmoduleOrderIsoIcc r hr).symm N))
  rw [happly, ← r.mkQ_apply, ← Submodule.mem_comap, hcomap,
    coe_iciSubmoduleOrderIsoIcc_symm_apply, Submodule.mem_comap, Submodule.subtype_apply]

/-- An ambient representative belongs to the interval submodule corresponding to `Q` exactly
when its quotient class belongs to `Q`. -/
@[simp]
theorem mem_iccOrderIsoQuotientOfMapEq_symm_apply_iff {p q : Submodule R M}
    (r : Submodule R q)
    (hr : r.map q.subtype = p) (Q : Submodule R (q ⧸ r)) (x : q) :
    (x : M) ∈ ((iccOrderIsoQuotientOfMapEq r hr).symm Q).1 ↔
      Submodule.Quotient.mk x ∈ Q := by
  simpa only [OrderIso.apply_symm_apply] using
    (mk_mem_iccOrderIsoQuotientOfMapEq_iff r hr
      ((iccOrderIsoQuotientOfMapEq r hr).symm Q) x).symm

end Quotient

end QuotientInterval

section Subquotient

section Map

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- An injective linear map carries the trace of `A` in `B` onto the trace of `A.map f` in
`B.map f`, so it descends to the subquotients. -/
@[simp]
theorem map_equivMapOfInjective_comap_subtype (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) :
    Submodule.map ((Submodule.equivMapOfInjective f hf B : ↥B ≃ₗ[R] ↥(B.map f)) :
        ↥B →ₗ[R] ↥(B.map f)) (Submodule.comap B.subtype A)
      = Submodule.comap (B.map f).subtype (A.map f) := by
  refine Submodule.map_injective_of_injective (B.map f).injective_subtype ?_
  have hcomp : (B.map f).subtype ∘ₗ
      ((Submodule.equivMapOfInjective f hf B : ↥B ≃ₗ[R] ↥(B.map f)) : ↥B →ₗ[R] ↥(B.map f))
        = f ∘ₗ B.subtype :=
    LinearMap.ext fun x => Submodule.coe_equivMapOfInjective_apply f hf B x
  rw [← Submodule.map_comp, hcomp, Submodule.map_comp, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, Submodule.map_inf f hf]

end Map

section Quotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **An injective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `M`
the subquotient cut out by the images `A.map f`, `B.map f` is the subquotient cut out by `A` and
`B` themselves; for `A ≤ B` this reads `B.map f ⧸ A.map f ≃ₗ[R] B ⧸ A`. -/
noncomputable def mapSubquotientEquivOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) :
    (↥(B.map f) ⧸ Submodule.comap (B.map f).subtype (A.map f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf B)
    (map_equivMapOfInjective_comap_subtype f hf A B)).symm

/-- `TauCeti.mapSubquotientEquivOfInjective` read on representatives: its inverse is induced by
the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    (mapSubquotientEquivOfInjective f hf A B).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x) := by
  rw [mapSubquotientEquivOfInjective, LinearEquiv.symm_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- `TauCeti.mapSubquotientEquivOfInjective` read on representatives, in the forward direction:
it undoes the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    mapSubquotientEquivOfInjective f hf A B
        (Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x)) =
      Submodule.Quotient.mk x := by
  rw [← mapSubquotientEquivOfInjective_symm_apply f hf A B x,
    LinearEquiv.apply_symm_apply]

/-- The kernel of `x ↦ f x mod A`, on the preimage of `B`, is the trace of the preimage of `A`. -/
theorem ker_mkQ_comp_submoduleComap (f : M →ₗ[R] N) (A B : Submodule R N) :
    LinearMap.ker ((Submodule.comap B.subtype A).mkQ ∘ₗ f.submoduleComap B)
      = Submodule.comap (B.comap f).subtype (A.comap f) := by
  ext x
  simp

/-- **A surjective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `N`
the subquotient cut out by the preimages `A.comap f`, `B.comap f` is the subquotient cut out by `A`
and `B` themselves; for `A ≤ B` this reads `B.comap f ⧸ A.comap f ≃ₗ[R] B ⧸ A`. -/
noncomputable def comapSubquotientEquivOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) :
    (↥(B.comap f) ⧸ Submodule.comap (B.comap f).subtype (A.comap f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_submoduleComap f A B).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp
        (LinearMap.submoduleComap_surjective_of_surjective f B hf)))

/-- `TauCeti.comapSubquotientEquivOfSurjective` read on representatives: it is induced by the
restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    comapSubquotientEquivOfSurjective f hf A B (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.submoduleComap B x) := by
  rw [comapSubquotientEquivOfSurjective, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- `TauCeti.comapSubquotientEquivOfSurjective` read on representatives, in the inverse direction:
it undoes the restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    (comapSubquotientEquivOfSurjective f hf A B).symm
        (Submodule.Quotient.mk (f.submoduleComap B x)) = Submodule.Quotient.mk x := by
  rw [← comapSubquotientEquivOfSurjective_apply f hf A B x,
    LinearEquiv.symm_apply_apply]

/-- The kernel of the map from `M` to the quotient of the range of `f` by the image of `I` is
exactly `I`, provided that `I` contains the kernel of `f`. -/
theorem _root_.LinearMap.ker_mkQ_comp_rangeRestrict (f : M →ₗ[R] N) (I : Submodule R M)
    (hker : LinearMap.ker f ≤ I) :
    LinearMap.ker ((I.map f.rangeRestrict).mkQ.comp f.rangeRestrict) = I := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  exact Submodule.comap_map_eq_self (by simpa using hker)

/-- **A quotient above the kernel is the corresponding quotient of the range.**

If `ker f ≤ I`, the map `x ↦ f x` identifies `M / I` with the range of `f` modulo the
image of `I`. This form of the first isomorphism theorem is useful when `f` is a representation
with a controlled kernel. -/
noncomputable def _root_.LinearMap.quotientEquivRangeQuotientMap (f : M →ₗ[R] N)
    (I : Submodule R M)
    (hker : LinearMap.ker f ≤ I) :
    (M ⧸ I) ≃ₗ[R] (LinearMap.range f ⧸ I.map f.rangeRestrict) :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.ker_mkQ_comp_rangeRestrict f I hker).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp f.surjective_rangeRestrict))

/-- `LinearMap.quotientEquivRangeQuotientMap` sends the class of `x` to the class of `f x` in the
range quotient. -/
@[simp]
theorem _root_.LinearMap.quotientEquivRangeQuotientMap_apply_mk (f : M →ₗ[R] N)
    (I : Submodule R M) (hker : LinearMap.ker f ≤ I) (x : M) :
    f.quotientEquivRangeQuotientMap I hker (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.rangeRestrict x) := by
  rw [LinearMap.quotientEquivRangeQuotientMap, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearMap.comp_apply, Submodule.mkQ_apply]

/-- `LinearMap.quotientEquivRangeQuotientMap` read in the inverse direction: the class of
`f.rangeRestrict x` in the range quotient comes from the class of `x`. -/
@[simp]
theorem _root_.LinearMap.quotientEquivRangeQuotientMap_symm_apply_mk (f : M →ₗ[R] N)
    (I : Submodule R M) (hker : LinearMap.ker f ≤ I) (x : M) :
    (f.quotientEquivRangeQuotientMap I hker).symm (Submodule.Quotient.mk (f.rangeRestrict x)) =
      Submodule.Quotient.mk x := by
  rw [← LinearMap.quotientEquivRangeQuotientMap_apply_mk f I hker x,
    LinearEquiv.symm_apply_apply]

end Quotient

end Subquotient

section DiagonalQuotient

open Module

variable {M ι : Type*} [AddCommGroup M] [Finite ι]

/-- A submodule with a diagonal basis relative to an ambient basis is cut out by divisibility
of the ambient coordinates. -/
private theorem mem_iff_dvd_repr_of_diagonal_basis {N : Submodule ℤ M}
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) {a : ι → ℤ}
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) :
    x ∈ N ↔ ∀ i, a i ∣ b.repr x i := by
  let _ := Fintype.ofFinite ι
  rw [bN.mem_submodule_iff' (x := x)]
  simp_rw [hdiag]
  have hrepr : ∀ (c : ι → ℤ) (i),
      b.repr (∑ j, c j • a j • b j) i = a i * c i := by
    intro c i
    simp only [← mul_smul, b.repr_sum_self, mul_comm]
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, hrepr c i⟩
  · rintro ha
    choose c hc using ha
    exact ⟨c, b.ext_elem fun i ↦ Eq.trans (hc i) (hrepr c i).symm⟩

/-- The coordinate isomorphism of an ambient basis carries a submodule with a diagonal basis onto
the product of the principal ideals generated by the diagonal coefficients. -/
private theorem map_equivFun_eq_pi_span (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    Submodule.map (b.equivFun : M →ₗ[ℤ] ι → ℤ) N =
      Submodule.pi Set.univ fun i ↦ Ideal.span ({a i} : Set ℤ) := by
  let _ := Fintype.ofFinite ι
  ext x
  simp only [Submodule.mem_map, Submodule.mem_pi, mem_iff_dvd_repr_of_diagonal_basis b bN hdiag,
    Set.mem_univ, Ideal.mem_span_singleton, forall_true_left, LinearEquiv.coe_coe,
    Basis.equivFun_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i
  · rintro hdvd
    refine ⟨∑ i, x i • b i, fun i ↦ ?_, ?_⟩
    · rw [b.repr_sum_self x]
      exact hdvd i
    · exact b.repr_sum_self x

private noncomputable def coordinateQuotientEquiv (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    M ⧸ N ≃+ ((ι → ℤ) ⧸ (Submodule.pi Set.univ fun i ↦ Ideal.span ({a i} : Set ℤ))) :=
  (Submodule.Quotient.equiv N _ b.equivFun
    (map_equivFun_eq_pi_span N b bN a hdiag)).toAddEquiv

private theorem coordinateQuotientEquiv_mk (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) :
    coordinateQuotientEquiv N b bN a hdiag (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (b.equivFun x) :=
  rfl

private noncomputable def quotientPiZModEquiv (a : ι → ℤ) :
    ((ι → ℤ) ⧸ (Submodule.pi Set.univ fun i ↦ Ideal.span ({a i} : Set ℤ))) ≃+
      ∀ i, ZMod (a i).natAbs :=
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  (Submodule.quotientPi fun i ↦ Ideal.span ({a i} : Set ℤ)).toAddEquiv.trans
    (AddEquiv.piCongrRight fun i ↦ (Int.quotientSpanEquivZMod (a i) : _ ≃+ _))

private theorem quotientPiZModEquiv_mk_apply (a : ι → ℤ) (x : ι → ℤ) (i : ι) :
    quotientPiZModEquiv a (Submodule.Quotient.mk x) i =
      ((x i : ℤ) : ZMod (a i).natAbs) :=
  rfl

/-- A quotient by a submodule with a specified diagonal basis is a product of cyclic groups.

Unlike `Submodule.quotientEquivPiZMod`, this construction takes both bases and their diagonal
coefficients as input. This lets a caller retain a normalized choice of Smith invariant factors
rather than using the coefficients selected internally by Mathlib's basis-level Smith form. -/
noncomputable def _root_.Submodule.quotientEquivPiZModOfBasis (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) :
    M ⧸ N ≃+ ∀ i, ZMod (a i).natAbs :=
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  (coordinateQuotientEquiv N b bN a hdiag).trans (quotientPiZModEquiv a)

/-- The diagonal quotient equivalence sends a representative to its coordinates modulo the
corresponding diagonal coefficients. -/
@[simp]
theorem _root_.Submodule.quotientEquivPiZModOfBasis_mk_apply (N : Submodule ℤ M)
    (b : Basis ι ℤ M) (bN : Basis ι ℤ N) (a : ι → ℤ)
    (hdiag : ∀ i, (bN i : M) = a i • b i) (x : M) (i : ι) :
    N.quotientEquivPiZModOfBasis b bN a hdiag (Submodule.Quotient.mk x) i =
      ((b.repr x i : ℤ) : ZMod (a i).natAbs) := by
  rw [Submodule.quotientEquivPiZModOfBasis, AddEquiv.trans_apply,
    coordinateQuotientEquiv_mk, quotientPiZModEquiv_mk_apply]
  rfl

end DiagonalQuotient

end TauCeti
end
end TAF_LiteralSource_0426

section TAF_LiteralSource_0427
/- Original module: TauCeti.RingTheory.CompositionSeries.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Transporting a composition series along a semilinear map

Let `σ : R →+* R₂` be a surjective ring homomorphism (`[RingHomSurjective σ]`). An injective
semilinear map `f : M →ₛₗ[σ] N` carries the submodules of `M` to submodules of `N` and preserves
coverings (`Submodule.map_covBy_of_injective`), so it carries a composition series of
`R`-submodules of `M` to one of `R₂`-submodules of `N`: `TauCeti.mapCompositionSeriesOfInjective`.
A surjective one pulls the submodules of `N` back to submodules of `M` and preserves coverings
(`Submodule.comap_covBy_of_surjective`), so it carries a composition series of `R₂`-submodules of
`N` back to one of `R`-submodules of `M`: `TauCeti.comapCompositionSeriesOfSurjective`.
This file records only how the transported series is built (its length, terms and endpoints).

For a linear map `f : M →ₗ[R] N` over a single ring (the case `σ = RingHom.id R`), the transported
series also keeps the *factors* themselves, and not just their number: this is the identification
of subquotients `TauCeti.mapSubquotientEquivOfInjective`, respectively
`TauCeti.comapSubquotientEquivOfSurjective`, of `TauCeti.Algebra.Module.Submodule.Quotient`, which
are stated only for such linear maps.

Taking `f` to be a linear equivalence, this is what makes an invariant read off a composition
series an invariant of the isomorphism class of the ambient module; the Jordan-Hölder
multiplicities of `TauCeti.RingTheory.CompositionSeries.Multiplicity` are the consumer this was
written for, and `TauCeti.RingTheory.CompositionSeries.Additivity` is the consumer that needs the
two one-sided forms, for the inclusion of a submodule and the projection onto a quotient.

## Main definitions

* `TauCeti.mapCompositionSeriesOfInjective`: the image of a composition series under an injective
  semilinear map.
* `TauCeti.comapCompositionSeriesOfSurjective`: the preimage of a composition series under a
  surjective semilinear map.

## References

The two transports are exactly the anonymous `let`s inside the proof of Mathlib's
`Module.length_eq_add_of_exact` (`Mathlib/RingTheory/Length.lean`, by Andrew Yang), packaged here
as named definitions with an API so that, for linear maps, they can be shown to preserve the
factors themselves and not just their number.
-/

public section

namespace TauCeti

variable {R R₂ M N : Type*} [Ring R] [Ring R₂] {σ : R →+* R₂} [RingHomSurjective σ]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R₂ N]

/-- The image of a composition series of `M` under an injective semilinear map
`f : M →ₛₗ[σ] N`. -/
def mapCompositionSeriesOfInjective (f : M →ₛₗ[σ] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) : CompositionSeries (Submodule R₂ N) :=
  s.map ⟨fun A => A.map f, Submodule.map_covBy_of_injective hf⟩

@[simp]
theorem mapCompositionSeriesOfInjective_length (f : M →ₛₗ[σ] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).length = s.length :=
  (rfl)

/-- The term of the transported series at an index is the image of the term of `s` at that same
index, transported along `TauCeti.mapCompositionSeriesOfInjective_length`. -/
@[simp]
theorem mapCompositionSeriesOfInjective_apply (f : M →ₛₗ[σ] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M))
    (i : Fin ((mapCompositionSeriesOfInjective f hf s).length + 1)) :
    mapCompositionSeriesOfInjective f hf s i =
      (s (i.cast (by rw [mapCompositionSeriesOfInjective_length]))).map f :=
  (rfl)

@[simp]
theorem head_mapCompositionSeriesOfInjective (f : M →ₛₗ[σ] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).head = s.head.map f :=
  (rfl)

@[simp]
theorem last_mapCompositionSeriesOfInjective (f : M →ₛₗ[σ] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).last = s.last.map f :=
  (rfl)

/-- The preimage of a composition series of `N` under a surjective semilinear map
`f : M →ₛₗ[σ] N`. -/
def comapCompositionSeriesOfSurjective (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R₂ N)) : CompositionSeries (Submodule R M) :=
  s.map ⟨fun A => A.comap f, Submodule.comap_covBy_of_surjective hf⟩

@[simp]
theorem comapCompositionSeriesOfSurjective_length (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R₂ N)) :
    (comapCompositionSeriesOfSurjective f hf s).length = s.length :=
  (rfl)

/-- The term of the transported series at an index is the preimage of the term of `s` at that same
index, transported along `TauCeti.comapCompositionSeriesOfSurjective_length`. -/
@[simp]
theorem comapCompositionSeriesOfSurjective_apply (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R₂ N))
    (i : Fin ((comapCompositionSeriesOfSurjective f hf s).length + 1)) :
    comapCompositionSeriesOfSurjective f hf s i =
      (s (i.cast (by rw [comapCompositionSeriesOfSurjective_length]))).comap f :=
  (rfl)

@[simp]
theorem head_comapCompositionSeriesOfSurjective (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R₂ N)) :
    (comapCompositionSeriesOfSurjective f hf s).head = s.head.comap f :=
  (rfl)

@[simp]
theorem last_comapCompositionSeriesOfSurjective (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R₂ N)) :
    (comapCompositionSeriesOfSurjective f hf s).last = s.last.comap f :=
  (rfl)

end TauCeti
end
end TAF_LiteralSource_0427

section TAF_LiteralSource_0428
/- Original module: TauCeti.RingTheory.CompositionSeries.Multiplicity -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Jordan-Hölder multiplicities of a simple module

A composition series of a module `M` cuts `M` into simple subquotients, its *factors*, and the
Jordan-Hölder theorem says that two composition series with the same endpoints have the same
factors up to a permutation.  Counting how often a fixed simple module `S` occurs among them is
therefore an invariant of `M` alone: the **multiplicity** `[M : S]` of `S` in `M`.  This file
builds that count.

Mathlib has everything the construction rests on and nothing built on it: the Jordan-Hölder
theorem `CompositionSeries.jordan_holder` in the abstract lattice form, the recognition
`isFiniteLength_iff_exists_compositionSeries` of the modules that admit a composition series from
`⊥` to `⊤`, the identification `JordanHolderLattice.Iso.linearEquiv` of the abstract interval
isomorphism with a linear equivalence of subquotients, and `Module.length`, which records only the
*number* of factors — and, with it, `Module.length_compositionSeries`, which is what pins down the
length of a composition series of a subsingleton or a simple module below.  The multiplicity of an
individual simple module is not there.

The count is taken with `Nat.card`, over the subtype of indices whose factor is a copy of `S`, so
no decidability of "is a copy of `S`" is needed.  The factor at an index `i` is spelled out as the
subquotient `↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)`, in the exact form
that `JordanHolderLattice.Iso.linearEquiv` produces, rather than being wrapped in a definition of
its own; that keeps the interface between this file and Mathlib's Jordan-Hölder machinery a
definitional identity.

## Main definitions

* `TauCeti.IsCompositionFactorAt`: the factor of a composition series at an index is a copy of a
  given module.
* `TauCeti.compositionMultiplicity`: the number of indices of a composition series whose factor is
  a copy of a given module.
* `TauCeti.jordanHolderMultiplicity`: the multiplicity `[M : S]`, the same count for a composition
  series of `M` running from `⊥` to `⊤`.

## Main results

* `TauCeti.compositionMultiplicity_eq_of_head_eq_of_last_eq`: **the multiplicity is a
  Jordan-Hölder invariant** — two composition series with the same endpoints count every module
  the same number of times.  This is what makes `TauCeti.jordanHolderMultiplicity` well defined,
  and `TauCeti.compositionMultiplicity_eq_jordanHolderMultiplicity` says that *every* composition
  series from `⊥` to `⊤` computes it.
* `TauCeti.IsCompositionFactorAt.isSimpleModule`: the factors are simple, so the multiplicity of a
  module that is not simple vanishes
  (`TauCeti.jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule`).
* `TauCeti.jordanHolderMultiplicity_eq_of_linearEquiv`: **the multiplicity is an invariant of the
  isomorphism class of the ambient module**, which is what makes `[Pᵢ : Sⱼ]` well posed for a
  projective cover, an object defined only up to isomorphism.  The transport of a composition
  series along an injective or a surjective linear map that this rests on is
  `TauCeti.RingTheory.CompositionSeries.Basic`.
* `TauCeti.jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv` and
  `TauCeti.jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule`: a simple
  module contains itself once and nothing else, the anti-vacuity check on the count.
* `TauCeti.jordanHolderMultiplicity_congr`: the multiplicity depends on `S` only through its
  isomorphism class.

## References

The Jordan-Hölder multiplicities `[Pᵢ : Sⱼ]` are what the Cartan matrix of a finite-dimensional
algebra is defined by, in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` ("The Cartan matrix of an
algebra", *"defined primarily by the Jordan-Hölder multiplicities `Cᵢⱼ = [Pᵢ : Sⱼ]` of `Sⱼ` in the
projective cover `Pᵢ`, well-defined by Jordan-Hölder"*); this file supplies that multiplicity and
its well-definedness.

* Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  §I.4 and §III.3.
-/

public section

open JordanHolderLattice

namespace TauCeti

universe u v v' w w'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### The factors of a composition series -/

/-- The factor of the composition series `s` at the index `i` is a copy of `S`: the subquotient
`s i.succ / s i.castSucc` is linearly equivalent to `S`. -/
def IsCompositionFactorAt (s : CompositionSeries (Submodule R M)) (i : Fin s.length)
    (S : Type w) [AddCommGroup S] [Module R S] : Prop :=
  Nonempty ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R] S)

variable {s : CompositionSeries (Submodule R M)} {i : Fin s.length}
variable {S : Type w} [AddCommGroup S] [Module R S] {T : Type w'} [AddCommGroup T] [Module R T]

/-- The defining property of `TauCeti.IsCompositionFactorAt`: it is the existence of a linear
equivalence between the subquotient at the index and the given module.  This is what introduces and
eliminates the predicate. -/
theorem isCompositionFactorAt_iff :
    IsCompositionFactorAt s i S ↔
      Nonempty ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R] S) :=
  (Iff.rfl)

/-- Being a factor at a given index only depends on the isomorphism class of the module. -/
theorem IsCompositionFactorAt.congr (h : IsCompositionFactorAt s i S) (e : S ≃ₗ[R] T) :
    IsCompositionFactorAt s i T :=
  h.elim fun f => ⟨f.trans e⟩

/-- Being a factor at a given index only depends on the isomorphism class of the module. -/
theorem isCompositionFactorAt_congr (e : S ≃ₗ[R] T) :
    IsCompositionFactorAt s i S ↔ IsCompositionFactorAt s i T :=
  ⟨fun h => h.congr e, fun h => h.congr e.symm⟩

/-- Two composition series with the same two submodules at an index have the same factor there.
The equalities are enough: the subquotient is built from the two submodules alone. -/
theorem isCompositionFactorAt_congr_of_eq {s t : CompositionSeries (Submodule R M)}
    {i : Fin s.length} {j : Fin t.length} (hsucc : s i.succ = t j.succ)
    (hcast : s i.castSucc = t j.castSucc) :
    IsCompositionFactorAt s i S ↔ IsCompositionFactorAt t j S := by
  rw [isCompositionFactorAt_iff, isCompositionFactorAt_iff, hcast, hsucc]

/-- **The factors of a composition series are simple**: each step of a composition series is a
covering, and a covering pair of submodules has simple quotient. -/
theorem isSimpleModule_subquotient (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
  have cov := s.step i
  (covBy_iff_quot_is_simple cov.le).mp cov

/-- A module that occurs as a factor of a composition series is simple. -/
@[grind →]
theorem IsCompositionFactorAt.isSimpleModule (h : IsCompositionFactorAt s i S) :
    IsSimpleModule R S :=
  have := isSimpleModule_subquotient s i
  h.elim fun e => _root_.IsSimpleModule.congr e.symm

/-! ### The multiplicity along a fixed composition series -/

/-- The number of indices at which the composition series `s` has a factor isomorphic to `S`. -/
noncomputable def compositionMultiplicity (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] : ℕ :=
  Nat.card {i : Fin s.length // IsCompositionFactorAt s i S}

/-- The defining formula for `TauCeti.compositionMultiplicity`, so that it can be evaluated on a
concrete composition series. -/
theorem compositionMultiplicity_def (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = Nat.card {i : Fin s.length // IsCompositionFactorAt s i S} :=
  (rfl)

/-- The multiplicity along a fixed composition series as a sum of indicators, the form in which it
splits along a decomposition of the index set. -/
theorem compositionMultiplicity_eq_sum_ite (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] [∀ i, Decidable (IsCompositionFactorAt s i S)] :
    compositionMultiplicity s S =
      ∑ i : Fin s.length, if IsCompositionFactorAt s i S then 1 else 0 := by
  rw [compositionMultiplicity_def, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]

/-- `S` occurs in `s` — the multiplicity is nonzero — exactly when some index carries a copy of
`S`. -/
theorem compositionMultiplicity_ne_zero_iff (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S ≠ 0 ↔ ∃ i, IsCompositionFactorAt s i S := by
  rw [compositionMultiplicity_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun i => ⟨i.1, i.2⟩, fun ⟨i, hi⟩ => ⟨⟨⟨i, hi⟩⟩, inferInstance⟩⟩

theorem compositionMultiplicity_le_length (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] : compositionMultiplicity s S ≤ s.length :=
  (Finite.card_subtype_le _).trans_eq (Nat.card_eq_fintype_card.trans (Fintype.card_fin _))

/-- Only simple modules occur as factors, so everything else has multiplicity zero. -/
theorem compositionMultiplicity_eq_zero_of_not_isSimpleModule
    (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] (hS : ¬ IsSimpleModule R S) :
    compositionMultiplicity s S = 0 := by
  have : IsEmpty {i : Fin s.length // IsCompositionFactorAt s i S} :=
    ⟨fun i => hS i.2.isSimpleModule⟩
  simp [compositionMultiplicity_def]

/-- The multiplicity along a fixed composition series depends on `S` only through its isomorphism
class. -/
theorem compositionMultiplicity_congr (s : CompositionSeries (Submodule R M)) (e : S ≃ₗ[R] T) :
    compositionMultiplicity s S = compositionMultiplicity s T :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => isCompositionFactorAt_congr e)

/-- **Equivalent composition series have the same multiplicities.** The bijection of indices
underlying the equivalence matches the factors up to isomorphism, so it restricts to a bijection
between the indices carrying a copy of `S`. -/
theorem compositionMultiplicity_eq_of_equivalent {s₁ s₂ : CompositionSeries (Submodule R M)}
    (h : s₁.Equivalent s₂) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s₁ S = compositionMultiplicity s₂ S := by
  obtain ⟨f, hf⟩ := h
  refine Nat.card_congr (Equiv.subtypeEquiv f fun i => ?_)
  have e := (hf i).linearEquiv
  exact ⟨fun ⟨g⟩ => ⟨e.symm.trans g⟩, fun ⟨g⟩ => ⟨e.trans g⟩⟩

/-- **The multiplicity is a Jordan-Hölder invariant.** Two composition series with the same first
and last term count every module the same number of times. -/
theorem compositionMultiplicity_eq_of_head_eq_of_last_eq {s₁ s₂ : CompositionSeries (Submodule R M)}
    (hhead : s₁.head = s₂.head) (hlast : s₁.last = s₂.last)
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s₁ S = compositionMultiplicity s₂ S :=
  compositionMultiplicity_eq_of_equivalent (CompositionSeries.jordan_holder s₁ s₂ hhead hlast) S

/-! ### The multiplicity of a simple module in a module of finite length -/

variable (R M) in
/-- **The Jordan-Hölder multiplicity `[M : S]`**: the number of factors isomorphic to `S` in a
composition series of `M` running from `⊥` to `⊤`.  By
`TauCeti.compositionMultiplicity_eq_jordanHolderMultiplicity` any such series computes it, so the
choice of series below is immaterial. -/
noncomputable def jordanHolderMultiplicity [IsNoetherian R M] [IsArtinian R M]
    (S : Type w) [AddCommGroup S] [Module R S] : ℕ :=
  compositionMultiplicity (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose S

/-- **Every composition series from `⊥` to `⊤` computes the multiplicity.** -/
theorem compositionMultiplicity_eq_jordanHolderMultiplicity [IsNoetherian R M] [IsArtinian R M]
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = jordanHolderMultiplicity R M S :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_of_head_eq_of_last_eq (hbot.trans h.1.symm) (htop.trans h.2.symm) S

/-- `S` is a composition factor of `M` — the multiplicity `[M : S]` is nonzero — exactly when some
index of a composition series from `⊥` to `⊤` carries a copy of `S`. -/
theorem jordanHolderMultiplicity_ne_zero_iff [IsNoetherian R M] [IsArtinian R M]
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S ≠ 0 ↔ ∃ i, IsCompositionFactorAt s i S := by
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop,
    compositionMultiplicity_ne_zero_iff]

/-- The multiplicity `[M : S]` depends on `S` only through its isomorphism class. -/
theorem jordanHolderMultiplicity_congr [IsNoetherian R M] [IsArtinian R M] (e : S ≃ₗ[R] T) :
    jordanHolderMultiplicity R M S = jordanHolderMultiplicity R M T :=
  compositionMultiplicity_congr _ e

/-- Only simple modules occur as composition factors. -/
theorem jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule [IsNoetherian R M] [IsArtinian R M]
    (S : Type w) [AddCommGroup S] [Module R S] (hS : ¬ IsSimpleModule R S) :
    jordanHolderMultiplicity R M S = 0 :=
  compositionMultiplicity_eq_zero_of_not_isSimpleModule _ S hS

/-! ### Transport along an injective or a surjective linear map -/

section Transport

variable {N : Type v'} [AddCommGroup N] [Module R N]

/-- Transporting a composition series along an injective linear map does not change which module
sits at an index; the index is transported along
`TauCeti.mapCompositionSeriesOfInjective_length`. -/
@[simp]
theorem isCompositionFactorAt_mapCompositionSeriesOfInjective_iff (f : M →ₗ[R] N)
    (hf : Function.Injective f) (s : CompositionSeries (Submodule R M))
    (i : Fin (mapCompositionSeriesOfInjective f hf s).length)
    (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt (mapCompositionSeriesOfInjective f hf s) i S ↔
      IsCompositionFactorAt s (i.cast (mapCompositionSeriesOfInjective_length f hf s)) S := by
  rw [isCompositionFactorAt_iff, isCompositionFactorAt_iff,
    mapCompositionSeriesOfInjective_apply, mapCompositionSeriesOfInjective_apply]
  exact ⟨fun ⟨g⟩ => ⟨(mapSubquotientEquivOfInjective f hf _ _).symm.trans g⟩,
    fun ⟨g⟩ => ⟨(mapSubquotientEquivOfInjective f hf _ _).trans g⟩⟩

/-- Transporting a composition series along a surjective linear map does not change which module
sits at an index; the index is transported along
`TauCeti.comapCompositionSeriesOfSurjective_length`. -/
@[simp]
theorem isCompositionFactorAt_comapCompositionSeriesOfSurjective_iff (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (s : CompositionSeries (Submodule R N))
    (i : Fin (comapCompositionSeriesOfSurjective f hf s).length)
    (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt (comapCompositionSeriesOfSurjective f hf s) i S ↔
      IsCompositionFactorAt s (i.cast (comapCompositionSeriesOfSurjective_length f hf s)) S := by
  rw [isCompositionFactorAt_iff, isCompositionFactorAt_iff,
    comapCompositionSeriesOfSurjective_apply, comapCompositionSeriesOfSurjective_apply]
  exact ⟨fun ⟨g⟩ => ⟨(comapSubquotientEquivOfSurjective f hf _ _).symm.trans g⟩,
    fun ⟨g⟩ => ⟨(comapSubquotientEquivOfSurjective f hf _ _).trans g⟩⟩

/-- **An injective map preserves multiplicities**: the image of a composition series counts every
module the same number of times as the series itself. -/
@[simp]
theorem compositionMultiplicity_mapCompositionSeriesOfInjective (f : M →ₗ[R] N)
    (hf : Function.Injective f) (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity (mapCompositionSeriesOfInjective f hf s) S =
      compositionMultiplicity s S :=
  Nat.card_congr (Equiv.subtypeEquiv (finCongr (mapCompositionSeriesOfInjective_length f hf s))
    fun i => isCompositionFactorAt_mapCompositionSeriesOfInjective_iff f hf s i S)

/-- **A surjective map preserves multiplicities**: the preimage of a composition series counts
every module the same number of times as the series itself. -/
@[simp]
theorem compositionMultiplicity_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (s : CompositionSeries (Submodule R N))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity (comapCompositionSeriesOfSurjective f hf s) S =
      compositionMultiplicity s S :=
  Nat.card_congr
    (Equiv.subtypeEquiv (finCongr (comapCompositionSeriesOfSurjective_length f hf s))
      fun i => isCompositionFactorAt_comapCompositionSeriesOfSurjective_iff f hf s i S)

/-- **The multiplicity only depends on the isomorphism class of the ambient module.** -/
theorem jordanHolderMultiplicity_eq_of_linearEquiv [IsNoetherian R M] [IsArtinian R M]
    [IsNoetherian R N] [IsArtinian R N] (e : M ≃ₗ[R] N)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S := by
  obtain ⟨s, hbot, htop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R M
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop S,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity
      (mapCompositionSeriesOfInjective (e : M →ₗ[R] N) e.injective s)
      (by simp [hbot]) (by simp [htop, e.range]) S,
    compositionMultiplicity_mapCompositionSeriesOfInjective]

end Transport

/-! ### Modules of length zero and one -/

/-- A composition series of a subsingleton module is a single point. -/
theorem compositionSeries_length_eq_zero_of_subsingleton [Subsingleton M]
    (s : CompositionSeries (Submodule R M)) : s.length = 0 := by
  simpa using Module.length_compositionSeries s (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- A subsingleton module has no composition factors at all. -/
theorem compositionMultiplicity_eq_zero_of_subsingleton [Subsingleton M]
    (s : CompositionSeries (Submodule R M)) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = 0 :=
  Nat.le_zero.mp ((compositionMultiplicity_le_length s S).trans_eq
    (compositionSeries_length_eq_zero_of_subsingleton s))

/-- Every multiplicity `[M : S]` in a subsingleton module `M` vanishes. -/
theorem jordanHolderMultiplicity_eq_zero_of_subsingleton [Subsingleton M]
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = 0 :=
  compositionMultiplicity_eq_zero_of_subsingleton _ S

/-- The bottom-to-top subquotient of a module is the module itself. -/
theorem nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top {A B : Submodule R M} (hA : A = ⊥)
    (hB : B = ⊤) : Nonempty ((↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R] M) := by
  subst hA hB
  refine ⟨(Submodule.quotEquivOfEqBot _ ?_).trans Submodule.topEquiv⟩
  rw [Submodule.comap_bot, Submodule.ker_subtype]

/-- A composition series of a simple module from `⊥` to `⊤` has a single step. -/
theorem compositionSeries_length_eq_one_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    s.length = 1 := by
  simpa using Module.length_compositionSeries s hbot htop

/-- **The single factor of a simple module is that module.** Every index of a composition series
of a simple module running from `⊥` to `⊤` carries the module itself. -/
theorem isCompositionFactorAt_iff_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (i : Fin s.length) (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt s i S ↔ Nonempty (M ≃ₗ[R] S) := by
  have hbot' : s 0 = ⊥ := s.apply_zero.trans hbot
  have htop' : s (Fin.last s.length) = ⊤ := s.apply_last.trans htop
  have hlen := compositionSeries_length_eq_one_of_isSimpleModule hbot htop
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  have h0 : s i.castSucc = ⊥ := by
    rw [← hbot']
    exact congrArg s (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero, hi]))
  have h1 : s i.succ = ⊤ := by
    rw [← htop']
    exact congrArg s (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))
  obtain ⟨g⟩ := nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top h0 h1
  exact ⟨fun ⟨f⟩ => ⟨g.symm.trans f⟩, fun ⟨f⟩ => ⟨g.trans f⟩⟩

/-- **A simple module contains exactly one copy of itself**, counted along a fixed composition
series of it running from `⊥` to `⊤`. -/
theorem compositionMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    compositionMultiplicity s S = 1 := by
  have hall : ∀ i : Fin s.length, IsCompositionFactorAt s i S := fun i =>
    (isCompositionFactorAt_iff_of_isSimpleModule hbot htop i S).mpr ⟨e⟩
  rw [compositionMultiplicity_def, Nat.card_congr (Equiv.subtypeUnivEquiv hall),
    Nat.card_eq_fintype_card, Fintype.card_fin,
    compositionSeries_length_eq_one_of_isSimpleModule hbot htop]

/-- **A simple module contains no copy of a module it is not isomorphic to**, counted along a fixed
composition series of it running from `⊥` to `⊤`. -/
theorem compositionMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule
    [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    compositionMultiplicity s S = 0 := by
  have : IsEmpty {i : Fin s.length // IsCompositionFactorAt s i S} :=
    ⟨fun i => he.elim'
      ((isCompositionFactorAt_iff_of_isSimpleModule hbot htop i.1 S).mp i.2).some⟩
  simp [compositionMultiplicity_def]

/-- **A simple module contains exactly one copy of itself**: the multiplicity `[M : S]` of a simple
module `M` in itself is `1`. -/
theorem jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv [IsSimpleModule R M]
    (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    jordanHolderMultiplicity R M S = 1 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv h.1 h.2 S e

/-- **A simple module contains no copy of a module it is not isomorphic to**: the multiplicity
`[M : S]` vanishes for a simple `M` admitting no linear equivalence with `S`. -/
theorem jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule
    [IsSimpleModule R M] (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    jordanHolderMultiplicity R M S = 0 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule h.1 h.2 S he

end TauCeti
end
end TAF_LiteralSource_0428

section TAF_LiteralSource_0429
/- Original module: TauCeti.RingTheory.CompositionSeries.Additivity -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Additivity of the Jordan-Hölder multiplicities

The Jordan-Hölder multiplicity `[M : S]` counts the factors isomorphic to `S` in a composition
series of `M`.  This file proves that it is **additive in a short exact sequence**: for a submodule
`p` of a module `M` of finite length,

`[M : S] = [p : S] + [M ⧸ p : S]`.

Both the composition factors of `p` and those of `M ⧸ p` are composition factors of `M`, and no
others are, so a single count splits in two.

The proof glues a composition series of `p` and a composition series of `M ⧸ p` into one series of
`M`: the lower half is carried along the *injective* map `p.subtype` by
`TauCeti.mapCompositionSeriesOfInjective` and the upper half along the *surjective* map `p.mkQ` by
`TauCeti.comapCompositionSeriesOfSurjective`, both of
`TauCeti/RingTheory/CompositionSeries/Basic.lean`; that these transports preserve every
multiplicity is `TauCeti.compositionMultiplicity_mapCompositionSeriesOfInjective` and
`TauCeti.compositionMultiplicity_comapCompositionSeriesOfSurjective`, of
`TauCeti/RingTheory/CompositionSeries/Multiplicity.lean`.  The two resulting series meet at `p` and
are glued with `RelSeries.smash`, whose `castAdd`/`natAdd` index lemmas split the count of factors
isomorphic to `S` into the two halves.

## Main results

* `TauCeti.compositionMultiplicity_smash`: the multiplicities of two composition series glued end
  to end add.
* `TauCeti.jordanHolderMultiplicity_eq_submodule_add_quotient`: **additivity**,
  `[M : S] = [p : S] + [M ⧸ p : S]`.
* `TauCeti.jordanHolderMultiplicity_eq_add_of_exact`: the same statement for a short exact sequence
  `0 → A → M → B → 0`.
* `TauCeti.jordanHolderMultiplicity_le_of_injective` and
  `TauCeti.jordanHolderMultiplicity_le_of_surjective`: a submodule and a quotient — more generally
  the source of an injective map into `M` and the target of a surjective map out of `M` — each
  contribute at most `M`'s multiplicity.
* `TauCeti.jordanHolderMultiplicity_prod`: `[M × N : S] = [M : S] + [N : S]`.
* `TauCeti.jordanHolderMultiplicity_pi`: additivity on a finite product of modules.

## References

This file refines Mathlib's `Module.length_eq_add_of_exact` (`Mathlib/RingTheory/Length.lean`, by
Andrew Yang) from counting the factors of a composition series to counting those isomorphic to a
fixed simple module `S`, and follows its proof plan: the same two transports along an injective and
a surjective map, the same `RelSeries.smash` gluing, and the same `map_bot`/`comap_top` endpoint
bookkeeping.  The monotonicity and product corollaries below are likewise the multiplicity
analogues of `Module.length_le_of_injective`, `Module.length_le_of_surjective` and
`Module.length_prod`.  What is new is that the transports are shown to preserve each factor's
isomorphism class and not merely the number of factors: the identification of the subquotients is
`TauCeti.mapSubquotientEquivOfInjective` and `TauCeti.comapSubquotientEquivOfSurjective` of
`TauCeti/Algebra/Module/Submodule/Quotient.lean`, and the resulting factor-by-factor comparison is
`TauCeti.isCompositionFactorAt_mapCompositionSeriesOfInjective_iff` and its surjective counterpart
in `TauCeti/RingTheory/CompositionSeries/Multiplicity.lean`;
`TauCeti/RingTheory/CompositionSeries/Basic.lean` supplies the transports themselves.

The additivity of `[Pᵢ : Sⱼ]` is what makes the Cartan matrix of a finite-dimensional algebra
computable, in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` ("The Cartan matrix of an
algebra"); `TauCeti/RingTheory/CompositionSeries/Multiplicity.lean` supplies the multiplicity
itself.

* Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  §I.4.
-/

public section

namespace TauCeti

universe u v v' v'' w w'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v'} [AddCommGroup N] [Module R N]
variable {S : Type v''} [AddCommGroup S] [Module R S]

/-! ### Gluing two composition series -/

section Smash

variable (p q : CompositionSeries (Submodule R M)) (h : p.last = q.head)

/-- The factors of the first half of a glued series are the factors of the first series. -/
@[simp]
theorem isCompositionFactorAt_smash_castAdd_iff (i : Fin p.length) :
    IsCompositionFactorAt (p.smash q h) (i.castAdd q.length) S ↔ IsCompositionFactorAt p i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_castAdd h i)
    (RelSeries.smash_castAdd h i)

/-- The factors of the second half of a glued series are the factors of the second series. -/
@[simp]
theorem isCompositionFactorAt_smash_natAdd_iff (i : Fin q.length) :
    IsCompositionFactorAt (p.smash q h) (i.natAdd p.length) S ↔ IsCompositionFactorAt q i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_natAdd h i)
    (RelSeries.smash_natAdd h i)

/-- **Gluing adds multiplicities.**  Two composition series joined end to end count every module as
often as the two of them together. -/
@[simp]
theorem compositionMultiplicity_smash :
    compositionMultiplicity (p.smash q h) S =
      compositionMultiplicity p S + compositionMultiplicity q S := by
  classical
  rw [compositionMultiplicity_eq_sum_ite, compositionMultiplicity_eq_sum_ite,
    compositionMultiplicity_eq_sum_ite]
  exact (Fin.sum_univ_add _).trans (by simp)

end Smash

/-! ### Additivity of the Jordan-Hölder multiplicity -/

/-- **The Jordan-Hölder multiplicity is additive.**  For a submodule `p` of a module of finite
length, `[M : S] = [p : S] + [M ⧸ p : S]`: a composition series of `p`, pushed into `M` along
`p.subtype`, and one of `M ⧸ p`, pulled back along `p.mkQ`, meet at `p` and glue to a composition
series of `M`. -/
theorem jordanHolderMultiplicity_eq_submodule_add_quotient [IsNoetherian R M] [IsArtinian R M]
    (p : Submodule R M) :
    jordanHolderMultiplicity R M S =
      jordanHolderMultiplicity R p S + jordanHolderMultiplicity R (M ⧸ p) S := by
  obtain ⟨t, htbot, httop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R p
  obtain ⟨u, hubot, hutop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R (M ⧸ p)
  have hconnect :
      (mapCompositionSeriesOfInjective p.subtype p.injective_subtype t).last =
        (comapCompositionSeriesOfSurjective p.mkQ p.mkQ_surjective u).head := by
    simp [httop, hubot]
  refine (compositionMultiplicity_eq_jordanHolderMultiplicity
    ((mapCompositionSeriesOfInjective p.subtype p.injective_subtype t).smash
      (comapCompositionSeriesOfSurjective p.mkQ p.mkQ_surjective u) hconnect)
    (by simp [RelSeries.head_smash, htbot]) (by simp [RelSeries.last_smash, hutop])
    S).symm.trans ?_
  rw [compositionMultiplicity_smash, compositionMultiplicity_mapCompositionSeriesOfInjective,
    compositionMultiplicity_comapCompositionSeriesOfSurjective,
    compositionMultiplicity_eq_jordanHolderMultiplicity t htbot httop S,
    compositionMultiplicity_eq_jordanHolderMultiplicity u hubot hutop S]

/-- **Additivity in a short exact sequence** `0 → A → M → B → 0`: the multiplicity of `S` in the
middle term is the sum of its multiplicities in the two ends.

Mathematically the finiteness of `A` and of `B` follows from that of `M`, through `A ≃ₗ[R] range f`
and `M ⧸ ker g ≃ₗ[R] B`.  The assumptions are nevertheless binders here rather than facts derived
in the proof, because `jordanHolderMultiplicity R A S` and `jordanHolderMultiplicity R B S` carry
them in their own signatures: the conclusion does not elaborate without them, so a caller holds
them already in order to state it. -/
theorem jordanHolderMultiplicity_eq_add_of_exact [IsNoetherian R M] [IsArtinian R M]
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    jordanHolderMultiplicity R M S =
      jordanHolderMultiplicity R A S + jordanHolderMultiplicity R B S := by
  rw [jordanHolderMultiplicity_eq_submodule_add_quotient (LinearMap.range f),
    jordanHolderMultiplicity_eq_of_linearEquiv (LinearEquiv.ofInjective f hf) S,
    ← jordanHolderMultiplicity_eq_of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hfg).symm).trans
        (g.quotKerEquivOfSurjective hg)) S]

/-- A module that embeds in `M` contributes at most `M`'s multiplicity.  As for
`TauCeti.jordanHolderMultiplicity_eq_add_of_exact`, the finiteness of `A` follows from that of `M`
and is a binder only because `jordanHolderMultiplicity R A S` — which already occurs in the
statement a caller is trying to prove — does not elaborate without it. -/
theorem jordanHolderMultiplicity_le_of_injective [IsNoetherian R M] [IsArtinian R M]
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    (f : A →ₗ[R] M) (hf : Function.Injective f) :
    jordanHolderMultiplicity R A S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact Nat.le_add_right _ _

/-- A quotient of `M` contributes at most `M`'s multiplicity.  As for
`TauCeti.jordanHolderMultiplicity_eq_add_of_exact`, the finiteness of `B` follows from that of `M`
and is a binder only because `jordanHolderMultiplicity R B S` — which already occurs in the
statement a caller is trying to prove — does not elaborate without it. -/
theorem jordanHolderMultiplicity_le_of_surjective [IsNoetherian R M] [IsArtinian R M]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (g : M →ₗ[R] B) (hg : Function.Surjective g) :
    jordanHolderMultiplicity R B S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
  exact Nat.le_add_left _ _

/-- **Additivity on a binary product**: `[M × N : S] = [M : S] + [N : S]`. -/
@[simp]
theorem jordanHolderMultiplicity_prod [IsNoetherian R M] [IsArtinian R M] [IsNoetherian R N]
    [IsArtinian R N] :
    jordanHolderMultiplicity R (M × N) S =
      jordanHolderMultiplicity R M S + jordanHolderMultiplicity R N S :=
  jordanHolderMultiplicity_eq_add_of_exact (LinearMap.inl R M N) (LinearMap.snd R M N)
    (LinearMap.inl_injective) (LinearMap.snd_surjective) Function.Exact.inl_snd

/-- The Jordan-Hölder multiplicity in a finite product is the sum of the multiplicities in
its factors. This is the multiplicity analogue of `Module.length_pi_of_fintype`. -/
@[simp]
theorem jordanHolderMultiplicity_pi : ∀ {ι : Type*} [Fintype ι]
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, IsNoetherian R (N i)] [∀ i, IsArtinian R (N i)],
    jordanHolderMultiplicity R (∀ i, N i) S = ∑ i, jordanHolderMultiplicity R (N i) S := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH N _ _ _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← jordanHolderMultiplicity_eq_of_linearEquiv (LinearEquiv.piCongrLeft R N e) S,
      IH, e.sum_comp (fun i ↦ jordanHolderMultiplicity R (N i) S)]
  · intro N _ _ _ _
    simp [jordanHolderMultiplicity_eq_zero_of_subsingleton]
  · intro ι _ IH N _ _ _ _
    rw [jordanHolderMultiplicity_eq_of_linearEquiv (LinearEquiv.piOptionEquivProd R) S,
      jordanHolderMultiplicity_prod, IH, Fintype.sum_option]

end TauCeti
end
end TAF_LiteralSource_0429

section TAF_LiteralSource_0430
/- Original module: TauCeti.RingTheory.Semisimple.RegularIsotypicComponent -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Mathlib.RingTheory.FiniteLength` is imported for the instance chain that makes a semisimple
-- ring Noetherian over itself, which is what supplies `Finite (isotypicComponents R R)` in
-- `TauCeti.finite_of_pairwise_not_linearEquiv`.

/-!
# Isotypic components of the regular module as an invariant of abstract simple modules

Mathlib's `isotypicComponent R N S` is the sum of all submodules of `N` isomorphic to `S`, and
`isotypicComponents R N` is the set of its nontrivial values as `S` ranges over the simple
*submodules* of `N`. For `N = R` the latter is a set of left ideals, and it is what indexes the
Artin-Wedderburn decomposition of a semisimple ring. Calling those indices the isomorphism classes
of simple `R`-modules is a theorem, not a rename: an abstract simple module carries no relation to
`R` beyond its action.

Mathlib supplies the input, `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`: every
simple module over a semisimple ring is isomorphic to a left ideal, necessarily a minimal one. This
file turns that realization into the statement that `M ↦ isotypicComponent R R M`, which Mathlib
already defines for an abstract `M`, is a complete isomorphism invariant of simple modules whose
values are exactly `isotypicComponents R R`.

## Main results

* `TauCeti.le_isotypicComponent_iff_nonempty_linearEquiv`: a simple submodule lies in the
  `S`-isotypic component exactly when it is a copy of the simple module `S`. The isotypic component
  therefore sees no simple module other than `S`; this holds in any ambient module, with no
  hypothesis on the ring.
* `TauCeti.isotypicComponent_eq_iff`: **the block ⇆ simple-module dictionary.** Two simple modules
  over a semisimple ring cut out the same isotypic component of `R` if and only if they are
  isomorphic — the injectivity half.
* `TauCeti.isotypicComponent_mem_isotypicComponents`: the isotypic component cut out by an abstract
  simple module is one of the isotypic components of the regular module, so the map above is
  well defined into `isotypicComponents R R`. Surjectivity needs no lemma: by definition every
  element of `isotypicComponents R R` is `isotypicComponent R R I` for a simple left ideal `I`.
* `TauCeti.simpleSubmoduleClassesEquiv`: **the bijection.** The isomorphism classes of simple
  submodules of `M`, as the quotient type `TauCeti.SimpleSubmoduleClasses R M`, correspond to the
  isotypic components of `M`, the class of `N` going to the `N`-isotypic component. This needs no
  hypothesis on the ring; for `M = R` it is the bijection with the Artin-Wedderburn blocks.
* `TauCeti.simpleModuleClass`: over a semisimple ring, the class in `SimpleSubmoduleClasses R R`
  of the simple left ideals realizing an abstract simple module. Its fibres are the isomorphism
  classes (`TauCeti.simpleModuleClass_eq_iff`) and it hits every class
  (`TauCeti.simpleModuleClass_coe`), so `SimpleSubmoduleClasses R R` is a universe-safe type of
  isomorphism classes of simple `R`-modules.
* `TauCeti.finite_of_pairwise_not_linearEquiv`: a semisimple ring has only finitely many
  isomorphism classes of simple modules.

## Implementation notes

Isomorphism classes of *abstract* simple modules cannot be a type: they range over every universe.
They are therefore handled in two ways here. The relational lemmas
`TauCeti.isotypicComponent_eq_iff` and `TauCeti.isotypicComponent_mem_isotypicComponents` state
injectivity and well-definedness of `M ↦ isotypicComponent R R M` without naming a type of classes
at all. The bundled bijection instead uses `TauCeti.SimpleSubmoduleClasses R R`, the classes of
simple *left ideals*, which is a type in `Type u`; over a semisimple ring
`TauCeti.simpleModuleClass` identifies it with the classes of abstract simple modules. It is used
through `TauCeti.SimpleSubmoduleClasses.mk`, `TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff` and the
eliminators `TauCeti.SimpleSubmoduleClasses.lift` (into `Sort`, with its defining equation
`TauCeti.SimpleSubmoduleClasses.lift_mk`) and `TauCeti.SimpleSubmoduleClasses.ind` (into `Prop`),
which is a complete API: nothing downstream has to know it is a quotient.

Each proof over a semisimple ring realizes the abstract module as a left ideal and transports along
that realization; nothing here redoes the isotypic theory.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, and C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R]

section IsotypicComponent

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A simple submodule lies in the `S`-isotypic component of `M` exactly when it is a copy of the
simple module `S`. Unlike Mathlib's `Submodule.le_isotypicComponent`, the module `S` cutting out
the component is an arbitrary simple `R`-module rather than a submodule of `M`. -/
theorem le_isotypicComponent_iff_nonempty_linearEquiv {S : Type w} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (N : Submodule R M) [IsSimpleModule R N] :
    N ≤ isotypicComponent R M S ↔ Nonempty (N ≃ₗ[R] S) :=
  ⟨fun h ↦ isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S) N h, fun e ↦ le_sSup e⟩

variable (R M) in
/-- The isomorphism classes of simple submodules of `M`. Unlike the isomorphism classes of abstract
simple modules, which range over every universe, this is a type; over a semisimple ring the two
agree for `M = R`, by `TauCeti.simpleModuleClass`.

That this is a quotient of the simple submodules by linear isomorphism is an implementation
detail: build a class with `TauCeti.SimpleSubmoduleClasses.mk`, compare classes with
`TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff`, and eliminate with
`TauCeti.SimpleSubmoduleClasses.lift` into `Sort` or `TauCeti.SimpleSubmoduleClasses.ind` into
`Prop`. The bodies stay unexposed: the defining equations
`TauCeti.SimpleSubmoduleClasses.lift_mk` and `TauCeti.coe_simpleSubmoduleClassesEquiv_mk` are
stated as ordinary theorems, so nothing downstream depends on the quotient by definitional
unfolding. -/
def SimpleSubmoduleClasses : Type _ :=
  Quot fun N N' : {N : Submodule R M // IsSimpleModule R N} ↦ Nonempty (N.1 ≃ₗ[R] N'.1)

namespace SimpleSubmoduleClasses

/-- The isomorphism class of a simple submodule of `M`. -/
def mk (N : Submodule R M) [IsSimpleModule R N] : SimpleSubmoduleClasses R M := Quot.mk _ ⟨N, ‹_›⟩

/-- Two simple submodules have the same isomorphism class exactly when they are isomorphic. -/
theorem mk_eq_mk_iff {N N' : Submodule R M} [IsSimpleModule R N] [IsSimpleModule R N'] :
    mk N = mk N' ↔ Nonempty (N ≃ₗ[R] N') :=
  Quot.eq.trans <| Equivalence.eqvGen_iff
    ⟨fun _ ↦ ⟨.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- Every isomorphism class is the class of a simple submodule: the eliminator into `Prop`. -/
@[elab_as_elim]
theorem ind {motive : SimpleSubmoduleClasses R M → Prop}
    (mk : ∀ (N : Submodule R M) (_ : IsSimpleModule R N), motive (.mk N))
    (c : SimpleSubmoduleClasses R M) : motive c :=
  Quot.ind (fun N ↦ mk N.1 N.2) c

/-- **The eliminator into `Sort`.** To define data on the isomorphism classes of simple submodules
of `M` it suffices to give a value on each simple submodule and to check that isomorphic simple
submodules get the same value; the value on a class is then read off by
`TauCeti.SimpleSubmoduleClasses.lift_mk`. -/
def lift {α : Sort*} (f : ∀ (N : Submodule R M) [IsSimpleModule R N], α)
    (hf : ∀ (N N' : Submodule R M) [IsSimpleModule R N] [IsSimpleModule R N'],
      Nonempty (N ≃ₗ[R] N') → f N = f N')
    (c : SimpleSubmoduleClasses R M) : α :=
  Quot.lift (fun N ↦ @f N.1 N.2) (fun N N' h ↦ @hf N.1 N'.1 N.2 N'.2 h) c

/-- The defining equation of `TauCeti.SimpleSubmoduleClasses.lift`. -/
@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (N : Submodule R M) [IsSimpleModule R N], α} {hf}
    (N : Submodule R M) [IsSimpleModule R N] : lift f hf (mk N) = f N := (rfl)

end SimpleSubmoduleClasses

variable (R M) in
/-- **Isomorphism classes of simple submodules biject with isotypic components.** The class of a
simple submodule `N` of `M` corresponds to the `N`-isotypic component of `M`. -/
noncomputable def simpleSubmoduleClassesEquiv :
    SimpleSubmoduleClasses R M ≃ isotypicComponents R M :=
  Equiv.ofBijective
    (SimpleSubmoduleClasses.lift
      (fun N hN ↦ (⟨isotypicComponent R M N, N, hN, rfl⟩ : isotypicComponents R M))
      fun _ _ _ _ ⟨e⟩ ↦ Subtype.ext e.isotypicComponent_eq)
    ⟨by
      refine SimpleSubmoduleClasses.ind fun N _ ↦ SimpleSubmoduleClasses.ind fun N' _ h ↦ ?_
      have h' : isotypicComponent R M N = isotypicComponent R M N' := congrArg Subtype.val h
      exact SimpleSubmoduleClasses.mk_eq_mk_iff.mpr <|
        (le_isotypicComponent_iff_nonempty_linearEquiv N).mp (h' ▸ N.le_isotypicComponent),
     by rintro ⟨_, N, _, rfl⟩; exact ⟨.mk N, rfl⟩⟩

@[simp]
theorem coe_simpleSubmoduleClassesEquiv_mk (N : Submodule R M) [IsSimpleModule R N] :
    (simpleSubmoduleClassesEquiv R M (.mk N) : Submodule R M) = isotypicComponent R M N := (rfl)

/-- A Noetherian module has only finitely many isomorphism classes of simple submodules. -/
instance [IsNoetherian R M] : Finite (SimpleSubmoduleClasses R M) :=
  .of_equiv _ (simpleSubmoduleClassesEquiv R M).symm

variable (R M)

/-- Over a semisimple ring, the isotypic component of the regular module cut out by an abstract
simple module really is one of the isotypic components of `R`, which are indexed by the simple
*left ideals*. -/
theorem isotypicComponent_mem_isotypicComponents [IsSemisimpleRing R] [IsSimpleModule R M] :
    isotypicComponent R R M ∈ isotypicComponents R R := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  exact ⟨I, .congr e.symm, e.isotypicComponent_eq⟩

variable {R M}

/-- **The isotypic component of the regular module is a complete isomorphism invariant of a simple
module.** Over a semisimple ring, two simple modules cut out the same isotypic component of `R` if
and only if they are isomorphic.

Together with `TauCeti.isotypicComponent_mem_isotypicComponents` and the fact that every element of
`isotypicComponents R R` is by definition an isotypic component of a simple left ideal, this is the
bijection between isomorphism classes of simple `R`-modules and the isotypic components of `R`; the
latter index the blocks of an Artin-Wedderburn decomposition. -/
theorem isotypicComponent_eq_iff [IsSemisimpleRing R] {N : Type w} [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] :
    isotypicComponent R R M = isotypicComponent R R N ↔ Nonempty (M ≃ₗ[R] N) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.isotypicComponent_eq⟩
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  have : IsSimpleModule R I := .congr f.symm
  obtain ⟨e⟩ := (le_isotypicComponent_iff_nonempty_linearEquiv I).mp <|
    (Submodule.le_isotypicComponent I).trans_eq (f.isotypicComponent_eq.symm.trans h.symm)
  exact ⟨e.symm.trans f.symm⟩

variable (R M) in
/-- Over a semisimple ring, the isomorphism class of the simple left ideals realizing an abstract
simple module `M`; see `TauCeti.simpleModuleClass_eq_mk_iff`. -/
noncomputable def simpleModuleClass [IsSemisimpleRing R] [IsSimpleModule R M] :
    SimpleSubmoduleClasses R R :=
  (simpleSubmoduleClassesEquiv R R).symm
    ⟨isotypicComponent R R M, isotypicComponent_mem_isotypicComponents R M⟩

@[simp]
theorem coe_simpleSubmoduleClassesEquiv_simpleModuleClass [IsSemisimpleRing R]
    [IsSimpleModule R M] :
    (simpleSubmoduleClassesEquiv R R (simpleModuleClass R M) : Submodule R R) =
      isotypicComponent R R M :=
  congrArg Subtype.val ((simpleSubmoduleClassesEquiv R R).apply_symm_apply _)

/-- **The dictionary as a map to a type of classes.** Over a semisimple ring, two simple modules
have the same class of realizing left ideals if and only if they are isomorphic.

With `TauCeti.simpleModuleClass_coe` this says that `SimpleSubmoduleClasses R R`, which
`TauCeti.simpleSubmoduleClassesEquiv` identifies with the isotypic components of `R`, is a type of
isomorphism classes of simple `R`-modules. -/
theorem simpleModuleClass_eq_iff [IsSemisimpleRing R] {N : Type w} [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] :
    simpleModuleClass R M = simpleModuleClass R N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← (simpleSubmoduleClassesEquiv R R).apply_eq_iff_eq, ← Subtype.coe_inj,
    coe_simpleSubmoduleClassesEquiv_simpleModuleClass,
    coe_simpleSubmoduleClassesEquiv_simpleModuleClass]
  exact isotypicComponent_eq_iff

/-- Every isomorphism class of simple left ideals is the class of an abstract simple module, namely
of the ideal itself: `TauCeti.simpleModuleClass` is surjective. -/
@[simp]
theorem simpleModuleClass_coe [IsSemisimpleRing R] (I : Submodule R R) [IsSimpleModule R I] :
    simpleModuleClass R I = .mk I :=
  (simpleSubmoduleClassesEquiv R R).injective <| Subtype.ext <| by simp

/-- The class of an abstract simple module is the class of a simple left ideal exactly when the two
are isomorphic, which is what makes `TauCeti.simpleModuleClass` a realization of `M`. -/
theorem simpleModuleClass_eq_mk_iff [IsSemisimpleRing R] [IsSimpleModule R M]
    (I : Submodule R R) [IsSimpleModule R I] :
    simpleModuleClass R M = .mk I ↔ Nonempty (M ≃ₗ[R] I) := by
  rw [← simpleModuleClass_coe, simpleModuleClass_eq_iff]

/-- A semisimple ring has only finitely many isomorphism classes of simple modules: a family of
pairwise non-isomorphic simple `R`-modules is indexed by a finite type. -/
theorem finite_of_pairwise_not_linearEquiv [IsSemisimpleRing R] {ι : Type*} (S : ι → Type v)
    [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (h : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) : Finite ι :=
  Finite.of_injective (fun i ↦ simpleModuleClass R (S i)) fun i j hij ↦
    h i j (simpleModuleClass_eq_iff.mp hij)

end IsotypicComponent

end TauCeti
end
end TAF_LiteralSource_0430

section TAF_LiteralSource_0431
/- Original module: TauCeti.RingTheory.Semisimple.Multiplicity -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The multiplicity of a simple module, as the dimension of a hom space

Let `A` be an algebra over a field `k` and let `S` be a simple `A`-module, finite-dimensional over
`k`. If a module `M` is written as a finite direct sum of simple
modules, the number of summands isomorphic to `S` is the **multiplicity** of `S` in `M`.  Written
that way the multiplicity refers to a chosen decomposition. Over an algebraically closed field
this file identifies it with the manifestly choice-free number

`Module.finrank k (S →ₗ[A] M)`,

so that the multiplicity is an invariant of `M` and needs no decomposition to be defined.

The proof is Schur's lemma plus additivity.  A hom space out of `S` into a finite product splits
as the product of the hom spaces into the factors, and each factor contributes `1` or `0`
according as it is or is not isomorphic to `S`.  Those two values are the dimension forms of
Schur's lemma, `LinearEquiv.finrank_linearMap_eq_one` and
`TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`, proved in
`TauCeti/RingTheory/Semisimple/Schur.lean`. Transport of a hom space along an isomorphism of its
target uses `LinearEquiv.homCongrRight`, defined in `TauCeti/Algebra/Module/Equiv/Basic.lean`.

Over an arbitrary field, an isomorphic factor instead contributes
`finrank k (Module.End A S)`.  The corresponding scaled multiplicity formula is enough to recover
the number of factors, since this endomorphism algebra has positive dimension. Constituent
detection and hom-space reconstruction therefore need no algebraic closure. Multiplicity
invariance is proved over arbitrary rings by identifying the factor count with the
Jordan-Hölder multiplicity.

The hom-space dimension results are stated for a `k`-algebra `A` and `A`-modules that are
`k`-modules compatibly. For `A = k[G]`, the hom space is the space of intertwiners. The
reconstruction result from simple-module classes needs only a semisimple ring, while
reconstruction from hom-space dimensions returns to the finite-dimensional `k`-algebra setting.

## Main results

* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`: **the multiplicity theorem.**  If
  `M ≃ₗ[A] ∀ i, N i` with every `N i` simple, then `finrank k (S →ₗ[A] M)` is the number of
  indices `i` with `N i ≅ S`.
* `LinearEquiv.finrank_linearMap_eq_natCard_mul_finrank_end`: over an arbitrary field, the same
  count is multiplied by the dimension of the division algebra `End_A(S)`; the literal product
  form is `TauCeti.finrank_linearMap_pi_eq_natCard_mul_finrank_end`.
* `TauCeti.jordanHolderMultiplicity_pi_eq_natCard`: over any ring, the count of simple factors
  is the Jordan-Hölder multiplicity.
* `TauCeti.natCard_eq_natCard_of_linearEquiv_pi`: equivalent finite products of simple modules
  over any ring have equally many factors isomorphic to `S`; applied to two decompositions of
  one module, this says that the multiplicity is well defined.
* `TauCeti.nonempty_linearEquiv_pi_of_natCard_eq`: conversely, two finite products of simple
  modules are linearly equivalent when their numbers of factors in every simple-module class
  agree.
* `TauCeti.nonempty_linearEquiv_of_finrank_linearMap_eq`: finite modules over a finite-dimensional
  semisimple algebra are linearly equivalent when every simple left ideal has the same hom-space
  dimension into them.
* `TauCeti.natCard_linearMap_eq_pow_jordanHolderMultiplicity`: over any ring, maps from a
  finitely generated semisimple module `M` to a simple module `S` number `#End(S) ^ [M : S]`.
* `TauCeti.natCard_linearMap_pi_eq_prod_pow`: maps from `M` into a finite product of simple
  modules `N i` number `∏ i, #End(N i) ^ [M : N i]`.
* `IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq`: over any ring,
  finitely generated semisimple modules with the same Jordan-Hölder multiplicities are isomorphic.
* `IsSemisimpleModule.nonempty_linearEquiv_of_natCard_linearMap_mul_eq`: over any ring,
  finite semisimple modules `M` and `N` with `#Hom(M, N) · #Hom(N, M) = #End(M) · #End(N)` are
  isomorphic.
* `TauCeti.finrank_linearMap_pos_iff_exists_nonempty_linearEquiv`: the multiplicity is positive
  exactly when `S` occurs among the factors, so the hom space detects the constituents.
* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const`: the isotypic case, where `M` is
  a power of `S` itself and the multiplicity is the number of copies.
* `TauCeti.nonempty_linearEquiv_isotypicComponent`: **the isotypic component is the power of its
  type with exponent the multiplicity**, `isotypicComponent A M S ≃ₗ[A] Fin m → S` for
  `m = finrank k (S →ₗ[A] M)`, and
  `TauCeti.finrank_isotypicComponent`: consequently `dim (isotypicComponent A M S) = m · dim S`.
* `TauCeti.finrank_linearMap_pos_of_ne_bot`: for a finite-dimensional `M`, the hom space out of
  any nonzero submodule is positive-dimensional.  This asks for neither simplicity nor an
  algebraically closed field, so it lives apart from the results above.
* `TauCeti.range_isotypicEval`: **the range of evaluation is the isotypic component**, where
  `TauCeti.isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M` is `s ⊗ f ↦ f s`.  Evaluation and its
  naturality in the target (`TauCeti.isotypicEval_comp`) are stated over a commutative semiring, no
  finiteness and no field operations being involved.

## The isotypic component

Mathlib's `isotypicComponent A M S` is the sum of the submodules of `M` isomorphic to `S`, and
`IsIsotypicOfType.linearEquiv_fun` writes it as a finite power of `S` once `S` is simple and `M` is
finite-dimensional.  What the multiplicity theorem adds is the value of the exponent: every
`A`-linear map out of `S` lands in the isotypic component
(`LinearMap.apply_mem_isotypicComponent`), so `TauCeti.linearMapIsotypicComponentEquiv` identifies
their hom spaces out of `S`, and the count above identifies the exponent with
`finrank k (S →ₗ[A] M)`. This is the decomposition-free description of the component that a
multiplicity computation needs.

The same fact says that evaluation `S ⊗[k] (S →ₗ[A] M) →ₗ[A] M` has the isotypic component as its
range: a map out of `S` lands there, and every submodule isomorphic to `S` is the range of such a
map. This half of the uncounted decomposition needs only a commutative semiring of scalars; that
evaluation is moreover injective, and hence an isomorphism onto the component, is proved over an
algebraically closed field in `TauCeti/RingTheory/Semisimple/IsotypicTensor.lean`.

## Implementation notes

The index set of a decomposition is counted with `Nat.card` of a subtype rather than with a
`Finset.filter`, so that no `DecidablePred` instance enters the statements; the proofs introduce
classical decidability and a `Fintype` structure locally.

The semisimple-ring reconstruction theorem counts factors by `simpleModuleClass`; the hom-space
reconstruction theorem converts those class fibres to the `Nonempty (S ≃ₗ[A] N i)` convention of
the multiplicity theorem using `simpleModuleClass_eq_mk_iff`.

Over an arbitrary ring, where simple modules need not embed in the ring, the factors of a
finitely generated semisimple module are instead taken to be quotients `R ⧸ m` by maximal left
ideals, and are matched up to isomorphism directly; maps out of such a module into a simple module
are counted with `Nat.card`, which needs no base field.

The dimension formulas assume simplicity of `S` and finite dimensionality over `k`. The
multiplicity theorem takes the decomposition of `M` as data; existence of a decomposition is the
separate semisimplicity input. The ring-general factor-count statements need neither a base field
nor simplicity of the module whose occurrences are counted.

## References

See C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
§25, or J.-P. Serre, *Linear Representations of Finite Groups*, §2.
-/

public section

namespace TauCeti

/-! ### The multiplicity of a simple module in a finite direct sum -/

section Multiplicity

section ArbitraryField

variable {k A S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity formula over an arbitrary field.** The dimension of the space of maps from
a simple module `S` into a finite product of simple modules is the number of factors isomorphic
to `S`, multiplied by the dimension of the division algebra `End_A(S)`. -/
theorem finrank_linearMap_pi_eq_natCard_mul_finrank_end :
    Module.finrank k (S →ₗ[A] ∀ i, N i) =
      Nat.card {i // Nonempty (S ≃ₗ[A] N i)} * Module.finrank k (Module.End A S) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : Module.finrank k (S →ₗ[A] ∀ i, N i) =
      ∑ i, Module.finrank k (S →ₗ[A] N i) := by
    rw [← (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k).finrank_eq]
    exact Module.finrank_pi_fintype k
  have hval : ∀ i, Module.finrank k (S →ₗ[A] N i) =
      if Nonempty (S ≃ₗ[A] N i) then Module.finrank k (Module.End A S) else 0 := by
    intro i
    split_ifs with hi
    · exact (LinearEquiv.homCongrRight k (S := S) hi.some).finrank_eq.symm
    · exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp hi)
  rw [hpi, Finset.sum_congr rfl fun i _ ↦ hval i]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite]

/-- The multiplicity formula over an arbitrary field, for a module given with a finite
simple decomposition. Each copy of `S` contributes the dimension of `End_A(S)`. -/
theorem _root_.LinearEquiv.finrank_linearMap_eq_natCard_mul_finrank_end {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) =
      Nat.card {i // Nonempty (S ≃ₗ[A] N i)} * Module.finrank k (Module.End A S) := by
  rw [(LinearEquiv.homCongrRight k (S := S) e).finrank_eq,
    finrank_linearMap_pi_eq_natCard_mul_finrank_end (k := k)]

end ArbitraryField

section SimpleTarget

variable {k A S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- A module with a finite decomposition into simple modules has a finite-dimensional space of
maps from any finite-dimensional module into it. -/
theorem _root_.LinearEquiv.finiteDimensional_linearMap_of_pi {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    FiniteDimensional k (S →ₗ[A] M) := by
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : FiniteDimensional k (S →ₗ[A] ∀ i, N i) :=
    Module.Finite.equiv (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k)
  exact Module.Finite.equiv (LinearEquiv.homCongrRight k (S := S) e).symm

end SimpleTarget

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity theorem for a product of simple modules.**  The dimension of the space of
`A`-linear maps from a simple module `S` into a finite product of simple modules counts the
factors isomorphic to `S`. -/
theorem finrank_linearMap_pi_eq_natCard :
    Module.finrank k (S →ₗ[A] ∀ i, N i) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [finrank_linearMap_pi_eq_natCard_mul_finrank_end (k := k),
    LinearEquiv.finrank_linearMap_eq_one (LinearEquiv.refl A S), mul_one]

/-- **The multiplicity theorem.**  If `M` decomposes as a finite direct sum of simple modules
`N i`, then the dimension of the space of `A`-linear maps from a simple module `S` into `M` is
the number of factors isomorphic to `S`.

Only the right-hand side mentions the decomposition, so this is the statement that the
multiplicity of `S` in `M` is an invariant of `M`; see
`TauCeti.natCard_eq_natCard_of_linearEquiv_pi`. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [e.finrank_linearMap_eq_natCard_mul_finrank_end (k := k),
    LinearEquiv.finrank_linearMap_eq_one (LinearEquiv.refl A S), mul_one]

omit [IsAlgClosed k] in
/-- **A hom space detects a constituent.**  There is a nonzero `A`-linear map from the simple
module `S` into `M` exactly when `S` occurs among the simple factors of `M`. -/
theorem finrank_linearMap_pos_iff_exists_nonempty_linearEquiv {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    0 < Module.finrank k (S →ₗ[A] M) ↔ ∃ i, Nonempty (S ≃ₗ[A] N i) := by
  have : Module.Finite k (Module.End A S) :=
    finiteDimensional_linearMap_of_isSimpleModule
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  rw [e.finrank_linearMap_eq_natCard_mul_finrank_end (k := k),
    mul_pos_iff_of_pos_right
      (Module.finrank_pos : 0 < Module.finrank k (Module.End A S)), Nat.card_pos_iff,
    nonempty_subtype]
  exact and_iff_left inferInstance

end Multiplicity

/-! ### Multiplicity invariance over arbitrary rings -/

section RingMultiplicity

variable {A S : Type*} [Ring A] [AddCommGroup S] [Module A S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- The Jordan-Hölder multiplicity in a finite product of simple modules counts the factors
isomorphic to the given module. -/
theorem jordanHolderMultiplicity_pi_eq_natCard :
    jordanHolderMultiplicity A (∀ i, N i) S = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [jordanHolderMultiplicity_pi]
  have hval (i : ι) : jordanHolderMultiplicity A (N i) S =
      if Nonempty (S ≃ₗ[A] N i) then 1 else 0 := by
    split_ifs with h
    · exact jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S h.some.symm
    · exact jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule S
        ⟨fun e ↦ h ⟨e.symm⟩⟩
  simp_rw [hval]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Equivalent finite products of simple modules contain equally many copies of every module.
This is Jordan-Hölder invariance over an arbitrary ring, without a choice of base field. -/
theorem natCard_eq_natCard_of_linearEquiv_pi {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module A (P j)] [∀ j, IsSimpleModule A (P j)]
    (e : (∀ i, N i) ≃ₗ[A] ∀ j, P j) :
    Nat.card {i // Nonempty (S ≃ₗ[A] N i)} = Nat.card {j // Nonempty (S ≃ₗ[A] P j)} := by
  rw [← jordanHolderMultiplicity_pi_eq_natCard, ← jordanHolderMultiplicity_pi_eq_natCard]
  exact jordanHolderMultiplicity_eq_of_linearEquiv e S

end RingMultiplicity

/-! ### Reconstructing a finite sum from its multiplicities -/

section Reconstruction

variable {R : Type*} [Ring R] [IsSemisimpleRing R]
variable {ι κ : Type*} [Finite ι] [Finite κ]
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, IsSimpleModule R (N i)]
variable {P : κ → Type*} [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
  [∀ j, IsSimpleModule R (P j)]

/-- **Finite sums of simple modules are determined by their multiplicities.** If two finite
families contain equally many modules in every simple-module isomorphism class, their products are
linearly equivalent. -/
theorem nonempty_linearEquiv_pi_of_natCard_eq
    (h : ∀ c : SimpleSubmoduleClasses R R,
      Nat.card {i // simpleModuleClass R (N i) = c} =
        Nat.card {j // simpleModuleClass R (P j) = c}) :
    Nonempty ((∀ i, N i) ≃ₗ[R] ∀ j, P j) := by
  have efiber : ∀ c, {i // simpleModuleClass R (N i) = c} ≃
      {j // simpleModuleClass R (P j) = c} := fun c ↦ (Finite.card_eq.mp (h c)).some
  let σ : ι ≃ κ := Equiv.ofFiberEquiv efiber
  have hclass (i : ι) : simpleModuleClass R (N i) = simpleModuleClass R (P (σ i)) :=
    (Equiv.ofFiberEquiv_map efiber i).symm
  have hiso (i : ι) : Nonempty (N i ≃ₗ[R] P (σ i)) :=
    simpleModuleClass_eq_iff.mp (hclass i)
  exact ⟨(LinearEquiv.piCongrRight fun i ↦ (hiso i).some).trans
    (LinearEquiv.piCongrLeft R P σ)⟩

end Reconstruction

/-! ### Semisimple modules over an arbitrary ring -/

section ArbitraryRing

universe u v w

variable {R : Type u} [Ring R]

/-- A finitely generated semisimple module is a finite product of quotients of the ring by maximal
left ideals. This is `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp` with each simple summand
replaced by an isomorphic cyclic module, so that all the factors live in the universe of `R`. -/
theorem _root_.IsSemisimpleModule.exists_linearEquiv_pi_quotient (M : Type v) [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] [Module.Finite R M] :
    ∃ (n : ℕ) (m : Fin n → Ideal R), (∀ i, (m i).IsMaximal) ∧
      Nonempty (M ≃ₗ[R] ∀ i, R ⧸ m i) := by
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  choose m hm e' using fun i ↦ isSimpleModule_iff_quot_maximal.mp (hS i)
  exact ⟨n, m, hm, ⟨e.trans DFinsupp.linearEquivFunOnFintype |>.trans
    (LinearEquiv.piCongrRight fun i ↦ (e' i).some)⟩⟩

/-- **Maps from a finite product of simple modules into a simple module `S`.** Their number is
the number of endomorphisms of `S`, raised to the number of factors isomorphic to `S`: by Schur's
lemma a factor isomorphic to `S` contributes a copy of `End_R(S)`, and any other factor
contributes only the zero map. No base field is involved, and the formula holds even when
`End_R(S)` is infinite, both sides then being `0` or `1` together. -/
theorem natCard_linearMap_pi_eq_pow {ι : Type*} [Finite ι] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, IsSimpleModule R (N i)]
    (S : Type w) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nat.card ((∀ i, N i) →ₗ[R] S) =
      Nat.card (Module.End R S) ^ Nat.card {i // Nonempty (S ≃ₗ[R] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hval (i : ι) : Nat.card (N i →ₗ[R] S) =
      if Nonempty (S ≃ₗ[R] N i) then Nat.card (Module.End R S) else 1 := by
    split_ifs with h
    · exact Nat.card_congr (h.some.symm.arrowCongrAddEquiv (LinearEquiv.refl R S)).toEquiv
    · have : Subsingleton (N i →ₗ[R] S) :=
        subsingleton_linearMap_of_isEmpty_linearEquiv ⟨fun e ↦ h ⟨e.symm⟩⟩
      exact Nat.card_unique
  rw [Nat.card_congr (LinearMap.lsum R N ℕ).symm.toEquiv, Nat.card_pi,
    Finset.prod_congr rfl fun i _ ↦ hval i, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

/-- **Maps from a semisimple module into a simple module count its multiplicity.** For a finitely
generated semisimple module `M` and a simple module `S`,
`#Hom_R(M, S) = #End_R(S) ^ [M : S]`, where `[M : S]` is the Jordan-Hölder multiplicity. When
`End_R(S)` is finite with at least two elements, the number of maps therefore determines the
multiplicity. -/
theorem natCard_linearMap_eq_pow_jordanHolderMultiplicity (M : Type v) [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] [Module.Finite R M]
    (S : Type w) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nat.card (M →ₗ[R] S) = Nat.card (Module.End R S) ^ jordanHolderMultiplicity R M S := by
  obtain ⟨n, m, hm, ⟨e⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) M
  have (i : Fin n) : IsSimpleModule R (R ⧸ m i) := isSimpleModule_iff_isCoatom.mpr (hm i).out
  rw [Nat.card_congr (e.arrowCongrAddEquiv (LinearEquiv.refl R S)).toEquiv,
    natCard_linearMap_pi_eq_pow, jordanHolderMultiplicity_eq_of_linearEquiv e,
    jordanHolderMultiplicity_pi_eq_natCard]

/-- **Maps from a semisimple module into a finite product of simple modules.** For a finitely
generated semisimple module `M`, `#Hom_R(M, ∏ i, N i) = ∏ i, #End_R(N i) ^ [M : N i]`: maps into a
product are families of maps into the factors, counted by
`TauCeti.natCard_linearMap_eq_pow_jordanHolderMultiplicity`. -/
theorem natCard_linearMap_pi_eq_prod_pow {ι : Type*} [Fintype ι] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, IsSimpleModule R (N i)]
    (M : Type v) [AddCommGroup M] [Module R M] [IsSemisimpleModule R M] [Module.Finite R M] :
    Nat.card (M →ₗ[R] ∀ i, N i) =
      ∏ i, Nat.card (Module.End R (N i)) ^ jordanHolderMultiplicity R M (N i) := by
  let e : (M →ₗ[R] ∀ i, N i) ≃ ∀ i, M →ₗ[R] N i :=
    { toFun f i := LinearMap.proj i ∘ₗ f
      invFun := LinearMap.pi
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ natCard_linearMap_eq_pow_jordanHolderMultiplicity M (N i)

/-- **Semisimple modules are determined by their Jordan-Hölder multiplicities**, over an arbitrary
ring. Two finitely generated semisimple modules which contain every simple module equally often
are isomorphic. It suffices to test the simple modules in the universe of `R`, since every simple
module is isomorphic to a quotient of `R`.

Over a semisimple ring this is `TauCeti.nonempty_linearEquiv_pi_of_natCard_eq`, where the simple
modules are indexed by the simple left ideals of `R`; in general a simple module need not embed in
`R`, and the factors are matched by isomorphism directly. -/
theorem _root_.IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq
    (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [IsSemisimpleModule R N]
    [Module.Finite R N]
    (h : ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
      jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S) :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨n, a, ha, ⟨eM⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) M
  obtain ⟨m, b, hb, ⟨eN⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) N
  -- Index the simple factors of `M` and of `N` together, and group the indices by the isomorphism
  -- class of their factor. The hypothesis says each class has equally many indices on both sides.
  let c : Fin n ⊕ Fin m → Ideal R := Sum.elim a b
  have hc : ∀ x, IsSimpleModule R (R ⧸ c x) := by
    rintro (i | j)
    exacts [isSimpleModule_iff_isCoatom.mpr (ha i).out, isSimpleModule_iff_isCoatom.mpr (hb j).out]
  have (i : Fin n) : IsSimpleModule R (R ⧸ a i) := hc (.inl i)
  have (j : Fin m) : IsSimpleModule R (R ⧸ b j) := hc (.inr j)
  let s : Setoid (Fin n ⊕ Fin m) :=
    { r x y := Nonempty ((R ⧸ c y) ≃ₗ[R] R ⧸ c x)
      iseqv := ⟨fun _ ↦ ⟨LinearEquiv.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
        fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e'.trans e⟩⟩ }
  have hcount (x : Fin n ⊕ Fin m) :
      Nat.card {i // Quotient.mk s (.inl i) = Quotient.mk s x} =
        Nat.card {j // Quotient.mk s (.inr j) = Quotient.mk s x} := by
    have := hc x
    simp only [Quotient.eq]
    exact ((jordanHolderMultiplicity_eq_of_linearEquiv eM _).trans
      jordanHolderMultiplicity_pi_eq_natCard).symm.trans <| (h (R ⧸ c x)).trans <|
        (jordanHolderMultiplicity_eq_of_linearEquiv eN _).trans
          jordanHolderMultiplicity_pi_eq_natCard
  let e (q : Quotient s) : {i // Quotient.mk s (.inl i) = q} ≃ {j // Quotient.mk s (.inr j) = q} :=
    (Finite.card_eq.mp <| by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact hcount x).some
  let σ : Fin n ≃ Fin m := Equiv.ofFiberEquiv e
  have hσ (i : Fin n) : Nonempty ((R ⧸ a i) ≃ₗ[R] R ⧸ b (σ i)) :=
    Quotient.exact (Equiv.ofFiberEquiv_map e i)
  exact ⟨eM.trans <| (LinearEquiv.piCongrRight fun i ↦ (hσ i).some).trans <|
    (LinearEquiv.piCongrLeft R (fun j ↦ R ⧸ b j) σ).trans eN.symm⟩

/-- **Finite semisimple modules are determined by the numbers of maps between them**, over an
arbitrary ring. Two finite semisimple modules `M` and `N` with
`#Hom(M, N) · #Hom(N, M) = #End(M) · #End(N)` are isomorphic.

Writing `a_S` and `b_S` for the multiplicities of a simple module `S` in `M` and `N`, and
`q_S = #End(S) ≥ 2`, the four numbers of maps are `∏ q_S ^ (a_S b_S)`, `∏ q_S ^ (b_S a_S)`,
`∏ q_S ^ (a_S ^ 2)` and `∏ q_S ^ (b_S ^ 2)`, so the hypothesis says `∏ q_S ^ ((a_S - b_S) ^ 2) = 1`.
This form of the comparison applies when only maps between `M` and `N` themselves can be counted,
for instance when `M` and `N` are reductions of lattices whose hom modules are known. -/
theorem _root_.IsSemisimpleModule.nonempty_linearEquiv_of_natCard_linearMap_mul_eq
    (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    [Finite M] [AddCommGroup N] [Module R N] [IsSemisimpleModule R N] [Finite N]
    (h : Nat.card (M →ₗ[R] N) * Nat.card (N →ₗ[R] M) =
      Nat.card (Module.End R M) * Nat.card (Module.End R N)) :
    Nonempty (M ≃ₗ[R] N) := by
  classical
  obtain ⟨n, a, ha, ⟨eM⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) M
  obtain ⟨m, b, hb, ⟨eN⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) N
  -- Index the simple factors of `M` and of `N` together, and group them by isomorphism class.
  let c : Fin n ⊕ Fin m → Ideal R := Sum.elim a b
  have hc : ∀ x, IsSimpleModule R (R ⧸ c x) := by
    rintro (i | j)
    exacts [isSimpleModule_iff_isCoatom.mpr (ha i).out, isSimpleModule_iff_isCoatom.mpr (hb j).out]
  have (i : Fin n) : IsSimpleModule R (R ⧸ a i) := hc (.inl i)
  have (j : Fin m) : IsSimpleModule R (R ⧸ b j) := hc (.inr j)
  let eM' : M ≃ₗ[R] ∀ i, R ⧸ c (.inl i) := eM
  let eN' : N ≃ₗ[R] ∀ j, R ⧸ c (.inr j) := eN
  have hfin : ∀ x, Finite (R ⧸ c x) := by
    rintro (i | j)
    · exact Finite.of_surjective (fun y : M ↦ eM' y i) fun z ↦ ⟨eM'.symm (Pi.single i z), by simp⟩
    · exact Finite.of_surjective (fun y : N ↦ eN' y j) fun z ↦ ⟨eN'.symm (Pi.single j z), by simp⟩
  let s : Setoid (Fin n ⊕ Fin m) :=
    { r x y := Nonempty ((R ⧸ c y) ≃ₗ[R] R ⧸ c x)
      iseqv := ⟨fun _ ↦ ⟨LinearEquiv.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
        fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e'.trans e⟩⟩ }
  let κ : Fin n ⊕ Fin m → Quotient s := Quotient.mk s
  -- The size of the endomorphism ring of a class of simple factors, and the numbers `A q` and
  -- `B q` of factors of `M` and of `N` in the class `q`.
  let C : Quotient s → ℕ := Quotient.lift (fun x ↦ Nat.card (Module.End R (R ⧸ c x)))
    fun x y ⟨e⟩ ↦ (Nat.card_congr (e.arrowCongrAddEquiv e).toEquiv).symm
  -- `C` is defined by `Quotient.lift`, so it computes on classes by definition.
  have hC_mk (x) : C (κ x) = Nat.card (Module.End R (R ⧸ c x)) := rfl
  let A (q : Quotient s) : ℕ := Nat.card {i // κ (.inl i) = q}
  let B (q : Quotient s) : ℕ := Nat.card {j // κ (.inr j) = q}
  -- `κ y = κ x` unfolds to `Nonempty ((R ⧸ c x) ≃ₗ[R] R ⧸ c y)`, the condition counted by
  -- `jordanHolderMultiplicity_pi_eq_natCard`.
  have hA (x) : jordanHolderMultiplicity R M (R ⧸ c x) = A (κ x) := by
    have := hc x
    rw [jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard]
    simp only [A, κ, Quotient.eq]
    rfl
  have hB (x) : jordanHolderMultiplicity R N (R ⧸ c x) = B (κ x) := by
    have := hc x
    rw [jordanHolderMultiplicity_eq_of_linearEquiv eN, jordanHolderMultiplicity_pi_eq_natCard]
    simp only [B, κ, Quotient.eq]
    rfl
  -- Counting maps into a product of simple factors, grouped by class.
  have hfib {k : ℕ} (g : Fin k → Fin n ⊕ Fin m) (F : Quotient s → ℕ) :
      ∏ j, C (κ (g j)) ^ F (κ (g j)) = ∏ q, C q ^ (Nat.card {j // κ (g j) = q} * F q) := by
    rw [← Finset.prod_fiberwise' Finset.univ (fun j ↦ κ (g j)) fun q ↦ C q ^ F q]
    refine Finset.prod_congr rfl fun q _ ↦ ?_
    rw [Finset.prod_const, ← pow_mul, mul_comm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardM {k : ℕ} (g : Fin k → Fin n ⊕ Fin m) :
      Nat.card (M →ₗ[R] ∀ j, R ⧸ c (g j)) = ∏ q, C q ^ (Nat.card {j // κ (g j) = q} * A q) := by
    have := fun j ↦ hc (g j)
    rw [natCard_linearMap_pi_eq_prod_pow, ← hfib]
    simp only [hA, hC_mk]
  have hcardN {k : ℕ} (g : Fin k → Fin n ⊕ Fin m) :
      Nat.card (N →ₗ[R] ∀ j, R ⧸ c (g j)) = ∏ q, C q ^ (Nat.card {j // κ (g j) = q} * B q) := by
    have := fun j ↦ hc (g j)
    rw [natCard_linearMap_pi_eq_prod_pow, ← hfib]
    simp only [hB, hC_mk]
  rw [Nat.card_congr ((LinearEquiv.refl R M).arrowCongrAddEquiv eN').toEquiv,
    Nat.card_congr ((LinearEquiv.refl R N).arrowCongrAddEquiv eM').toEquiv,
    Nat.card_congr ((LinearEquiv.refl R M).arrowCongrAddEquiv eM').toEquiv,
    Nat.card_congr ((LinearEquiv.refl R N).arrowCongrAddEquiv eN').toEquiv,
    hcardM Sum.inr, hcardN Sum.inl, hcardM Sum.inl, hcardN Sum.inr,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib] at h
  simp only [← pow_add] at h
  -- Since `a * a + b * b = (b * a + a * b) + ((a - b) ^ 2 + (b - a) ^ 2)`, the hypothesis forces
  -- `∏ q, C q ^ ((A q - B q) ^ 2 + (B q - A q) ^ 2) = 1`.
  have hsq (a b : ℕ) : a * a + b * b = (b * a + a * b) + ((a - b) ^ 2 + (b - a) ^ 2) := by
    rcases le_total a b with hab | hab <;>
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      simp only [Nat.sub_eq_zero_of_le hab, add_tsub_cancel_left]
      ring
  have hC (q : Quotient s) : 1 < C q := by
    induction q using Quotient.ind with | _ x
    have := hc x
    have := hfin x
    have : Finite (Module.End R (R ⧸ c x)) := Finite.of_injective _ DFunLike.coe_injective
    have := IsSimpleModule.nontrivial R (R ⧸ c x)
    exact Finite.one_lt_card (α := Module.End R (R ⧸ c x))
  have hone : ∏ q, C q ^ ((A q - B q) ^ 2 + (B q - A q) ^ 2) = 1 := by
    have h' : ∏ q, C q ^ (B q * A q + A q * B q) = ∏ q, C q ^ (A q * A q + B q * B q) := h
    have h2 : ∏ q, C q ^ (A q * A q + B q * B q) = (∏ q, C q ^ (B q * A q + A q * B q)) *
        ∏ q, C q ^ ((A q - B q) ^ 2 + (B q - A q) ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun q _ ↦ by rw [← pow_add, ← hsq]
    rw [h2] at h'
    exact (mul_eq_left₀ (Finset.prod_ne_zero_iff.mpr fun q _ ↦
      pow_ne_zero _ (zero_lt_one.trans (hC q)).ne')).mp h'.symm
  have hAB (q : Quotient s) : A q = B q := by
    have := Nat.dvd_one.mp (hone ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
    rw [Nat.pow_eq_one] at this
    have := this.resolve_left (hC q).ne'
    simp only [Nat.add_eq_zero_iff, pow_eq_zero_iff two_ne_zero, Nat.sub_eq_zero_iff_le] at this
    omega
  -- Hence `M` and `N` have the same Jordan-Hölder multiplicities.
  refine IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N
    fun S _ _ _ ↦ ?_
  by_cases hx : ∃ x, Nonempty (S ≃ₗ[R] R ⧸ c x)
  · obtain ⟨x, ⟨e⟩⟩ := hx
    rw [jordanHolderMultiplicity_congr e, jordanHolderMultiplicity_congr e, hA, hB, hAB]
  · push Not at hx
    rw [jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard,
      jordanHolderMultiplicity_eq_of_linearEquiv eN, jordanHolderMultiplicity_pi_eq_natCard]
    have : IsEmpty {i // Nonempty (S ≃ₗ[R] R ⧸ a i)} := ⟨fun i ↦ (hx (.inl i.1)).false i.2.some⟩
    have : IsEmpty {j // Nonempty (S ≃ₗ[R] R ⧸ b j)} := ⟨fun j ↦ (hx (.inr j.1)).false j.2.some⟩
    simp

end ArbitraryRing

/-! ### Reconstructing finite modules from hom-space dimensions -/

section ReconstructionFromHom

variable {k A M P : Type*} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsSemisimpleRing A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module.Finite A M]
variable [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] [Module.Finite A P]

/-- **Finite modules over a semisimple algebra are determined by their simple multiplicities.**
If every simple left ideal has hom spaces of the same dimension into `M` and `P`, then `M` and
`P` are linearly equivalent. -/
theorem nonempty_linearEquiv_of_finrank_linearMap_eq
    (h : ∀ (S : Submodule A A) [IsSimpleModule A S],
      Module.finrank k (S →ₗ[A] M) = Module.finrank k (S →ₗ[A] P)) :
    Nonempty (M ≃ₗ[A] P) := by
  obtain ⟨n, SM, eM, hSM⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨m, SP, eP, hSP⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A P
  let _ (i : Fin n) : IsSimpleModule A (SM i) := hSM i
  let _ (i : Fin m) : IsSimpleModule A (SP i) := hSP i
  let epM : M ≃ₗ[A] ∀ i, SM i := eM.trans DFinsupp.linearEquivFunOnFintype
  let epP : P ≃ₗ[A] ∀ i, SP i := eP.trans DFinsupp.linearEquivFunOnFintype
  have hfiber : ∀ c,
      Nat.card {i // simpleModuleClass A (SM i) = c} =
        Nat.card {j // simpleModuleClass A (SP j) = c} := by
    intro c
    induction c using SimpleSubmoduleClasses.ind with
    | mk S hS =>
      let _ : IsSimpleModule A S := hS
      let _ : Module.Finite k S :=
        Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
      let _ : Module.Finite k (Module.End A S) :=
        .of_injective (LinearMap.restrictScalarsₗ k A S S k) (LinearMap.restrictScalars_injective k)
      have hendpos : 0 < Module.finrank k (Module.End A S) := by
        let _ : Nontrivial S := IsSimpleModule.nontrivial A S
        let _ : Nontrivial (Module.End A S) := inferInstance
        exact Module.finrank_pos
      have hpredM (i : Fin n) : simpleModuleClass A (SM i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SM i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      have hpredP (i : Fin m) : simpleModuleClass A (SP i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SP i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      rw [Nat.card_congr (Equiv.subtypeEquivRight hpredM),
        Nat.card_congr (Equiv.subtypeEquivRight hpredP)]
      apply Nat.eq_of_mul_eq_mul_right hendpos
      rw [← epM.finrank_linearMap_eq_natCard_mul_finrank_end (k := k) (S := S),
        ← epP.finrank_linearMap_eq_natCard_mul_finrank_end (k := k) (S := S), h S]
  exact ⟨epM |>.trans (nonempty_linearEquiv_pi_of_natCard_eq hfiber).some |>.trans epP.symm⟩

end ReconstructionFromHom

/-! ### The isotypic case -/

section Isotypic

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **The multiplicity of `S` in a power of `S`.**  If `M` is a finite power of the simple module
`S`, the dimension of the space of `A`-linear maps `S → M` is the number of copies.

This is the form Clifford theory uses: an isotypic component of a restriction is a power of a
single constituent, and its multiplicity is read off as a dimension. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi_const {ι : Type*} [Finite ι] {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] (ι → S)) :
    Module.finrank k (S →ₗ[A] M) = Nat.card ι := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) (N := fun _ : ι ↦ S) e]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ ⟨LinearEquiv.refl A S⟩)

end Isotypic

/-! ### The isotypic component -/

section IsotypicComponent

variable {k A M S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [IsAlgClosed k] [FiniteDimensional k S] [FiniteDimensional k M]

/-- **The isotypic component is the power of its type with exponent the multiplicity.**  Mathlib's
`IsIsotypicOfType.linearEquiv_fun` writes the component as a finite power of `S`; what is proved
here is that the exponent is the multiplicity `finrank k (S →ₗ[A] M)`, which is the form that
identifies it without reference to the decomposition. -/
theorem nonempty_linearEquiv_isotypicComponent :
    Nonempty (isotypicComponent A M S ≃ₗ[A] (Fin (Module.finrank k (S →ₗ[A] M)) → S)) := by
  have : Module.Finite k ↥(isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  have : Module.Finite A ↥(isotypicComponent A M S) :=
    Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent A M S).linearEquiv_fun
  have hn : Module.finrank k (S →ₗ[A] M) = n := by
    rw [← finrank_linearMap_isotypicComponent (k := k),
      finrank_linearMap_eq_natCard_of_linearEquiv_pi_const (k := k) e]
    simp
  rw [hn]
  exact ⟨e⟩

/-- **The dimension of an isotypic component is the multiplicity times the dimension of its
type.**  This is the counted form of the isotypic decomposition: the `S`-isotypic component of `M`
is `S^{⊕ m}` with `m` the multiplicity `finrank k (S →ₗ[A] M)`. -/
theorem finrank_isotypicComponent :
    Module.finrank k ↥(isotypicComponent A M S)
      = Module.finrank k (S →ₗ[A] M) * Module.finrank k S := by
  obtain ⟨e⟩ := nonempty_linearEquiv_isotypicComponent (k := k) (A := A) (M := M) (S := S)
  rw [(e.restrictScalars k).finrank_eq]
  simp [Module.finrank_pi_fintype]

end IsotypicComponent

/-! ### Evaluation of the multiplicity space -/

section Evaluation

open TensorProduct

variable (k : Type*) {A S M N : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommMonoid N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- **Evaluation** `S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`.  Only the left factor carries an
`A`-action, so this is a map of `A`-modules for the `TensorProduct.leftModule` structure.
The construction works over semirings and needs no additive inverses. -/
def isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M :=
  AlgebraTensorModule.lift (LinearMap.id (R := k) (M := S →ₗ[A] M)).flip

@[simp]
theorem isotypicEval_tmul (s : S) (f : S →ₗ[A] M) : isotypicEval k (s ⊗ₜ f) = f s :=
  (rfl)

/-- **Naturality of evaluation in the target.**  Postcomposition with an `A`-linear map
`g : M →ₗ[A] N` is, on the tensor factorization, the map `g` induces on multiplicity spaces; the
left factor is untouched.  So an operator commuting with `A` acts through the multiplicity space
alone, which is what makes the second factor a module over the commutant. -/
theorem isotypicEval_comp (g : M →ₗ[A] N) :
    g ∘ₗ isotypicEval k (S := S) =
      isotypicEval k ∘ₗ
        AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) := by
  refine AlgebraTensorModule.curry_injective ?_
  ext s f
  rfl

/-- The value form of `TauCeti.isotypicEval_comp`. -/
@[simp]
theorem isotypicEval_map_apply (g : M →ₗ[A] N) (x : S ⊗[k] (S →ₗ[A] M)) :
    isotypicEval k
        (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) x) = g (isotypicEval k x) :=
  (LinearMap.congr_fun (isotypicEval_comp k g) x).symm

end Evaluation

section EvaluationRange

open TensorProduct

variable (k : Type*) {A S M : Type*} [CommSemiring k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [IsSimpleModule A S]

/-- **The range of evaluation is the `S`-isotypic component of `M`.**  A map out of `S` lands in
the component, and every submodule of `M` isomorphic to `S` is the range of such a map.  This
needs no finiteness and no field hypothesis: a commutative semiring of scalars suffices. -/
@[simp]
theorem range_isotypicEval :
    LinearMap.range (isotypicEval k (S := S) (M := M)) = isotypicComponent A M S := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s f => simpa using f.apply_mem_isotypicComponent s
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  · refine sSup_le ?_
    rintro m ⟨e⟩ x hx
    refine ⟨e ⟨x, hx⟩ ⊗ₜ (m.subtype ∘ₗ (e.symm : S →ₗ[A] m)), ?_⟩
    simp

end EvaluationRange

/-! ### Positivity for an arbitrary nonzero submodule -/

section Positivity

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]

/-- **A nonzero submodule has a positive-dimensional hom space.**  The inclusion of a nonzero
`A`-submodule `S` of `M` is a nonzero element of `S →ₗ[A] M`, and that hom space is
finite-dimensional over `k` because `S` and `M` are.  For a simple `S` over a splitting field this
is the statement that a constituent occurs with positive multiplicity.

`A` is a ring rather than a semiring because the finite-dimensionality of the hom space is
`LinearMap.finiteDimensional'`, which needs one; over a semiring `↥S` carries no `AddCommGroup`
instance and `Module.Finite.linearMap` does not apply. -/
theorem finrank_linearMap_pos_of_ne_bot {S : Submodule A M} (hS : S ≠ ⊥) :
    0 < Module.finrank k (S →ₗ[A] M) := by
  have : Module.Finite k ↥S :=
    .of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hS
  have : Nontrivial (S →ₗ[A] M) :=
    ⟨S.subtype, 0, fun hzero => hv0 (by simpa using DFunLike.congr_fun hzero ⟨v, hv⟩)⟩
  exact Module.finrank_pos

end Positivity

end TauCeti
end
end TAF_LiteralSource_0431

section TAF_LiteralSource_0432
/- Original module: TauCeti.RingTheory.Semisimple.Trace -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semisimple modules are determined by their traces

Let `A` be an algebra over a field `k` of characteristic zero. A finite-dimensional semisimple
`A`-module `M` gives the trace function `a ↦ tr_k (a • · : M → M)` on `A`. This file proves that
the trace function determines `M` up to isomorphism
(`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`). No finiteness is asked of `A`,
which is the point: for the group algebra of an infinite group, such as `GL n ℂ`, it is what lets
characters determine semisimple representations.

The argument isolates one isotypic type at a time by an element of `A`. For a semisimple module
`X` finite over its endomorphism ring and a simple module `S`, the projection of `X` onto its
`S`-isotypic component along the sum of the other isotypic components commutes with every
endomorphism, because isotypic components are fully invariant. Jacobson density then writes it
as the action of some `a : A` (`IsSemisimpleModule.exists_forall_smul_eq_ite`): `a` acts
as the identity on every simple submodule of `X` isomorphic to `S`, and as zero on every other
simple submodule. Applied to `X = M × N`, the trace of `a` on `M` is the multiplicity of `S` in
`M` times the dimension of `S`, and likewise on `N`. In characteristic zero equal traces therefore
give equal multiplicities, and finite semisimple modules with equal multiplicities are isomorphic
(`IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq`).

## Main results

* `IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`: **finite-dimensional semisimple
  modules over an algebra in characteristic zero with the same traces are isomorphic.**

## References

* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open Module TauCeti

universe u

namespace IsSemisimpleModule

section Trace

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]

open scoped Classical in
/-- An element acting as in `IsSemisimpleModule.exists_forall_smul_eq_ite` on the simple
submodules of `X` acts in the same way on every simple module embedded in `X`. -/
private theorem smul_eq_ite_of_injective {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {Y : Type*} [AddCommGroup Y] [Module A Y] [IsSimpleModule A Y]
    (f : Y →ₗ[A] X) (hf : Function.Injective f) (y : Y) :
    a • y = if Nonempty (S ≃ₗ[A] Y) then y else 0 := by
  let e := LinearEquiv.ofInjective f hf
  have hT : IsSimpleModule A (LinearMap.range f) := IsSimpleModule.congr e.symm
  have hiff : Nonempty (LinearMap.range f ≃ₗ[A] S) ↔ Nonempty (S ≃ₗ[A] Y) :=
    ⟨fun ⟨e'⟩ => ⟨e'.symm.trans e.symm⟩, fun ⟨e'⟩ => ⟨(e'.trans e).symm⟩⟩
  have hy := ha _ hT (f y) (LinearMap.mem_range_self f y)
  rw [← map_smul, hiff] at hy
  apply hf
  split_ifs at hy ⊢ <;> simpa using hy

open scoped Classical in
/-- The trace of such an element on a module embedded in `X`, computed on a decomposition into
simple submodules, adds up the dimensions of the summands isomorphic to `S`. -/
private theorem trace_lsmul_eq_sum_ite {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [FiniteDimensional k P] {n : ℕ} (Q : Fin n → Submodule A P) (e : P ≃ₗ[A] ∀ i, Q i)
    (hQ : ∀ i, IsSimpleModule A (Q i)) (j : P →ₗ[A] X) (hj : Function.Injective j) :
    LinearMap.trace k P (Algebra.lsmul k k P a) =
      ∑ i, if Nonempty (S ≃ₗ[A] Q i) then (finrank k (Q i) : k) else 0 := by
  have (i : Fin n) : Module.Finite k (Q i) :=
    .of_injective ((Q i).subtype.restrictScalars k) Subtype.val_injective
  rw [← LinearMap.trace_conj' _ (e.restrictScalars k), LinearMap.trace_pi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hQa (y : Q i) : a • y = if Nonempty (S ≃ₗ[A] Q i) then y else 0 :=
    have := hQ i
    smul_eq_ite_of_injective ha (j ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.single A (fun i => Q i) i)
      (hj.comp (e.symm.injective.comp fun _ _ h => Pi.single_injective i h)) y
  have hblock : LinearMap.proj i ∘ₗ (e.restrictScalars k).conj (Algebra.lsmul k k P a) ∘ₗ
      LinearMap.single k (fun i => Q i) i =
        if Nonempty (S ≃ₗ[A] Q i) then LinearMap.id else 0 := by
    ext y
    simp only [LinearMap.comp_apply, LinearEquiv.conj_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, Algebra.lsmul_coe, map_smul, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.smul_apply, hQa]
    split_ifs <;> simp
  rw [hblock]
  split_ifs <;> simp

/-- **Semisimple modules are determined by their traces.** Over an algebra `A` over a field of
characteristic zero, two finite-dimensional semisimple `A`-modules on which every element of `A`
acts with the same trace are isomorphic. No finiteness is asked of `A`. -/
theorem nonempty_linearEquiv_of_trace_eq [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [FiniteDimensional k M] [IsSemisimpleModule A M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [FiniteDimensional k N] [IsSemisimpleModule A N]
    (h : ∀ a : A, LinearMap.trace k M (Algebra.lsmul k k M a) =
      LinearMap.trace k N (Algebra.lsmul k k N a)) :
    Nonempty (M ≃ₗ[A] N) := by
  classical
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  have : Module.Finite (Module.End A (M × N)) (M × N) :=
    Module.Finite.of_restrictScalars_finite k _ _
  refine nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N fun S _ _ _ => ?_
  obtain ⟨a, ha⟩ := exists_forall_smul_eq_ite (R := A) (M := M × N) S
  obtain ⟨n, P, eP, hP⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨m, Q, eQ, hQ⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A N
  let _ (i : Fin n) : IsSimpleModule A (P i) := hP i
  let _ (i : Fin m) : IsSimpleModule A (Q i) := hQ i
  let eM : M ≃ₗ[A] ∀ i, P i := eP.trans DFinsupp.linearEquivFunOnFintype
  let eN : N ≃ₗ[A] ∀ i, Q i := eQ.trans DFinsupp.linearEquivFunOnFintype
  rw [jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard,
    jordanHolderMultiplicity_eq_of_linearEquiv eN, jordanHolderMultiplicity_pi_eq_natCard]
  have htM :=
    trace_lsmul_eq_sum_ite (k := k) ha P eM hP (LinearMap.inl A M N) LinearMap.inl_injective
  have htN :=
    trace_lsmul_eq_sum_ite (k := k) ha Q eN hQ (LinearMap.inr A M N) LinearMap.inr_injective
  by_cases hS : (∃ i, Nonempty (S ≃ₗ[A] P i)) ∨ ∃ j, Nonempty (S ≃ₗ[A] Q j)
  · -- All the summands of type `S`, in `M` and in `N`, have one common positive dimension `d`.
    obtain ⟨d, hd, hdP, hdQ⟩ : ∃ d : ℕ, 0 < d ∧
        (∀ i, Nonempty (S ≃ₗ[A] P i) → finrank k (P i) = d) ∧
        ∀ j, Nonempty (S ≃ₗ[A] Q j) → finrank k (Q j) = d := by
      rcases hS with ⟨i₀, ⟨e₀⟩⟩ | ⟨j₀, ⟨e₀⟩⟩
      · have : Module.Finite k (P i₀) :=
          .of_injective ((P i₀).subtype.restrictScalars k) Subtype.val_injective
        have : Nontrivial (P i₀) := IsSimpleModule.nontrivial A _
        exact ⟨_, finrank_pos, fun i ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq,
          fun j ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩
      · have : Module.Finite k (Q j₀) :=
          .of_injective ((Q j₀).subtype.restrictScalars k) Subtype.val_injective
        have : Nontrivial (Q j₀) := IsSimpleModule.nontrivial A _
        exact ⟨_, finrank_pos, fun i ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq,
          fun j ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩
    have heq := (htM.symm.trans (h a)).trans htN
    rw [Fintype.sum_ite_eq_card_nsmul fun i hi ↦ congrArg Nat.cast (hdP i hi),
      Fintype.sum_ite_eq_card_nsmul fun j hj ↦ congrArg Nat.cast (hdQ j hj), nsmul_eq_mul,
      nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul] at heq
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.cast_injective heq)
  · -- If `S` occurs in neither module, both counts vanish.
    push Not at hS
    have : IsEmpty {i // Nonempty (S ≃ₗ[A] P i)} := ⟨fun i => (hS.1 i.1).false i.2.some⟩
    have : IsEmpty {j // Nonempty (S ≃ₗ[A] Q j)} := ⟨fun j => (hS.2 j.1).false j.2.some⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

end Trace

end IsSemisimpleModule
end
end TAF_LiteralSource_0432

section TAF_LiteralSource_0433
/- Original module: TauCeti.RepresentationTheory.Semisimple -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Semisimple representations are determined by their characters

Over a field of characteristic zero, two finite-dimensional semisimple representations of a monoid
with the same character are equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). The monoid need
not be finite: for a finite group in characteristic zero every representation is semisimple by
Maschke's theorem, but the statement here is what applies to an infinite group such as `GL n ℂ`,
once complete reducibility is known by other means.

The character determines the trace of every element `a = ∑ a_g g` of the monoid algebra `k[G]`
acting on the representation, namely `∑ a_g χ(g)`. So the `k[G]`-modules of the two
representations are semisimple with equal trace functions, and
`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq` identifies them.

## Main results

* `Representation.trace_asAlgebraHom_eq_of_character_eq`: representations with the same character
  have the same trace function on `k[G]`.
* `Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`: **semisimple
  representations with the same character are equivalent.**

## References

* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **The character determines the trace on the monoid algebra.** If two representations have the
same character, then every element of `k[G]` acts on them with the same trace. -/
theorem trace_asAlgebraHom_eq_of_character_eq {ρ : Representation k G V}
    {σ : Representation k G W} (h : ρ.character = σ.character) (a : k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom a) = LinearMap.trace k W (σ.asAlgebraHom a) := by
  have hlin : (LinearMap.trace k V).comp ρ.asAlgebraHom.toLinearMap =
      (LinearMap.trace k W).comp σ.asAlgebraHom.toLinearMap :=
    MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring <| by
      simpa [character] using congrFun h g
  exact LinearMap.congr_fun hlin a

/-- **Semisimple representations are determined by their characters.** Over a field of
characteristic zero, two finite-dimensional semisimple representations of a monoid with the same
character are equivalent. The monoid need not be finite. -/
theorem nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation [CharZero k]
    [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) _ _ fun a => ?_
  rw [← LinearMap.trace_conj' _ ρ.asModuleEquiv, ← LinearMap.trace_conj' _ σ.asModuleEquiv]
  exact trace_asAlgebraHom_eq_of_character_eq h a

end Representation
end
end TAF_LiteralSource_0433

section TAF_LiteralSource_0434
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The special unitary subgroup of the general linear group

Mathlib's `Matrix.specialUnitaryGroup n 𝕜` is a `Submonoid (Matrix n n 𝕜)`: the unitary matrices
of determinant one, carrying its own `Group` structure because a unitary matrix is inverted by its
adjoint.  The constructions that see a matrix group as a group of *units* — the general linear Lie
group and its Lie algebra above all — need the same object as a `Subgroup (GL n 𝕜)` instead, and
that is `TauCeti.GLSpecialUnitary n 𝕜`.

It is defined as the intersection of two subgroups already present: `unitarySubgroup (GL n 𝕜)`,
Mathlib's unitary elements of a group with involution, and the kernel of the determinant
`Matrix.GeneralLinearGroup.det`.  Defining it this way rather than by transporting the submonoid
is what makes it usable: a property of the special unitary group that is the conjunction of a
unitary and a determinant property can be proved one factor at a time, each factor being a group
whose theory is already available.  `TauCeti.GLSpecialUnitary.mem_iff` identifies the carrier with
Mathlib's submonoid, so nothing is lost.

This mirrors `TauCeti.GLSymplectic`, the units-level avatar of `Matrix.symplecticGroup`.

## Main definitions

* `TauCeti.GLSpecialUnitary`: the special unitary group as a subgroup of `GL n 𝕜`.

## Main results

* `TauCeti.GLSpecialUnitary.eq_unitarySubgroup_inf_ker_det`: the defining decomposition into a
  unitary and a determinant condition.
* `TauCeti.GLSpecialUnitary.mem_iff`: its elements are the units whose matrix is special unitary.
* `TauCeti.GLSpecialUnitary.le_unitarySubgroup`: it is contained in the unitary subgroup.
-/

public section

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [CommRing 𝕜] [StarRing 𝕜]

/-- **The special unitary subgroup of the general linear group**: the invertible matrices that are
unitary and have determinant one, as a subgroup of `GL n 𝕜`.  It is `Matrix.specialUnitaryGroup`
read on units, and is presented as the intersection of the unitary subgroup with the kernel of the
determinant. -/
def GLSpecialUnitary : Subgroup (GL n 𝕜) :=
  unitarySubgroup (GL n 𝕜) ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det

namespace GLSpecialUnitary

/-- The special unitary subgroup is by definition cut out by two independent conditions: being
unitary, and having determinant one. -/
theorem eq_unitarySubgroup_inf_ker_det :
    GLSpecialUnitary n 𝕜 =
      unitarySubgroup (GL n 𝕜) ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det :=
  (rfl)

variable {n 𝕜}

/-- An invertible matrix lies in the special unitary subgroup exactly when its underlying matrix
lies in Mathlib's `Matrix.specialUnitaryGroup`. -/
@[simp]
theorem mem_iff {M : GL n 𝕜} :
    M ∈ GLSpecialUnitary n 𝕜 ↔ (M : Matrix n n 𝕜) ∈ Matrix.specialUnitaryGroup n 𝕜 := by
  rw [eq_unitarySubgroup_inf_ker_det, Matrix.mem_specialUnitaryGroup_iff]
  -- Both sides are now a conjunction of a unitary and a determinant condition; what remains is
  -- transporting each across the coercion of units.
  simp [Units.unitary_eq, Units.ext_iff]

/-- The special unitary subgroup is contained in the unitary subgroup. -/
theorem le_unitarySubgroup : GLSpecialUnitary n 𝕜 ≤ unitarySubgroup (GL n 𝕜) :=
  eq_unitarySubgroup_inf_ker_det n 𝕜 ▸ inf_le_left

/-- The carrier of the special unitary subgroup is the preimage of Mathlib's special unitary
submonoid under the coercion of units.  This is the form the closedness of the subgroup is read
from. -/
theorem coe_eq_preimage :
    (GLSpecialUnitary n 𝕜 : Set (GL n 𝕜)) =
      Units.val ⁻¹' (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  Set.ext fun _ => mem_iff

end GLSpecialUnitary

end TauCeti
end
end TAF_LiteralSource_0434

section TAF_LiteralSource_0435
/- Original module: TauCeti.Topology.Algebra.Star.Unitary -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The unitary subgroup of the units is closed, and compact when `unitary M` is

Mathlib's `isClosed_unitary` says that the unitary elements of a topological star monoid `M` are
a closed subset of `M`.  This file transfers that to the group of units: `unitarySubgroup Mˣ`,
the unitary elements of `Mˣ` packaged as a subgroup, is closed in `Mˣ`.  It also shows that
`unitarySubgroup Mˣ` is compact whenever `unitary M` is.

Closedness is immediate once Mathlib's `Units.unitary_eq` exhibits the subgroup as the
preimage of `unitary M` under `Units.val`, which is continuous.  No hypothesis beyond the ones
`isClosed_unitary` already needs is required.

Compactness does not follow from the preimage description.  Instead, the subgroup is the image
of `unitary M` under `Unitary.toUnits`, which is continuous into `Mˣ` because the star operation
is continuous; this needs only `ContinuousStar M`, and no `T1Space` or `ContinuousMul`.

This is the closedness hypothesis that the Lie algebra of a closed subgroup of `Mˣ` is computed
from; see `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `TauCeti.mem_unitary_units_iff`: a unit is unitary exactly when its underlying element is.
* `TauCeti.isClosed_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is closed.
* `TauCeti.isCompact_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is compact when
  `unitary M` is.
-/

public section

namespace TauCeti

/-- A unit of a star monoid is unitary exactly when its underlying element is unitary. -/
@[simp]
theorem mem_unitary_units_iff {M : Type*} [Monoid M] [StarMul M] {g : Mˣ} :
    g ∈ unitary Mˣ ↔ (g : M) ∈ unitary M := by
  rw [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply]

variable (M : Type*) [Monoid M] [StarMul M] [TopologicalSpace M] [T1Space M] [ContinuousStar M]
  [ContinuousMul M]

/-- **The unitary subgroup of the units of a topological star monoid is closed.**  It is the
preimage of the closed set `unitary M` under the continuous coercion `Units.val`. -/
theorem isClosed_unitarySubgroup_units :
    IsClosed ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  have hpre : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Units.val ⁻¹' (unitary M : Set M) :=
    Set.ext fun _ => mem_unitary_units_iff
  rw [hpre]
  exact isClosed_unitary.preimage Units.continuous_val

/-- **The unitary subgroup of the units of a topological star monoid is compact when `unitary M`
is.**  It is the image of `unitary M` under the continuous map sending a unitary element to the
unit it defines. -/
theorem isCompact_unitarySubgroup_units {M : Type*} [Monoid M] [StarMul M] [TopologicalSpace M]
    [ContinuousStar M] (h : IsCompact (unitary M : Set M)) :
    IsCompact ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  have : CompactSpace (unitary M) := isCompact_iff_compactSpace.mp h
  have hrange : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Set.range fun U : unitary M ↦ Unitary.toUnits U := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, mem_unitary_units_iff.mp hg⟩, Units.ext rfl⟩, ?_⟩
    rintro ⟨U, rfl⟩
    exact mem_unitary_units_iff.mpr U.property
  rw [hrange]
  exact isCompact_range <| Units.continuous_iff.mpr
    ⟨continuous_subtype_val, continuous_subtype_val.star⟩

end TauCeti
end
end TAF_LiteralSource_0435

section TAF_LiteralSource_0436
/- Original module: TauCeti.Topology.Algebra.UnitaryGroup -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The unitary and special unitary matrix groups are compact

For a finite index type `n` and `𝕜 = ℝ` or `ℂ` (any `RCLike` field), the unitary group
`Matrix.unitaryGroup n 𝕜` and the special unitary group `Matrix.specialUnitaryGroup n 𝕜` are
compact subsets of `Matrix n n 𝕜` in the entrywise topology, hence compact topological groups.

The argument is the classical one. A unitary matrix has unit rows, so all its entries lie in the
closed unit ball (Mathlib's `entry_norm_bound_of_unitary`); the unitary group is therefore contained
in the compact set of matrices with entries in that ball, and it is closed because it is cut out by
the equations `star A * A = 1` and `A * star A = 1`. The special unitary group adds the closed
condition `det A = 1`.

Mathlib already supplies the topological group structure on `unitary R` for a topological star
monoid `R` (`isClosed_unitary` and the `IsTopologicalGroup (unitary R)` instance), so for the
unitary group only compactness is new. The special unitary group is a different submonoid, carrying
its own `Group` instance in `Mathlib/LinearAlgebra/UnitaryGroup.lean`, so its `ContinuousInv` and
`IsTopologicalGroup` instances are recorded here too. Those instances and its closedness need no
`RCLike` hypothesis, and are stated over a topological commutative star ring instead; only
compactness is `RCLike`-specific. Hausdorffness is not proved here: it
is inherited from the ambient matrix topology whenever `𝕜` is Hausdorff.

Closedness is also recorded one level up, for `TauCeti.GLSpecialUnitary`, the same group seen as
a subgroup of the general linear group of units: its carrier is the preimage of the matrix special
unitary group under the continuous coercion `Units.val`.  That is the form in which the
closed-subgroup theorem consumes it.  Over `ℝ` or `ℂ`, compactness of the matrix unitary group
likewise passes to the unitary subgroup `unitarySubgroup (GL n 𝕜)`.

This is the setup the compact-group representation theory of `SU(2)` runs on; see
`TauCeti/RepresentationTheory/SU2/Basic.lean`.

## Main results

* `TauCeti.Matrix.isClosed_specialUnitaryGroup`: the special unitary matrix group is closed.
* `TauCeti.Matrix.isCompact_unitaryGroup` and `TauCeti.Matrix.isCompact_specialUnitaryGroup`: the
  unitary and special unitary matrix groups over `ℝ` or `ℂ` are compact.
* `TauCeti.isClosed_GLSpecialUnitary`: the special unitary subgroup of the general linear group is
  closed.
* `Matrix.GeneralLinearGroup.isCompact_unitarySubgroup`: the unitary subgroup of the general linear
  group over `ℝ` or `ℂ` is compact.
-/

public section

open Metric Set

namespace TauCeti

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing 𝕜] [StarRing 𝕜]

variable [TopologicalSpace 𝕜] [ContinuousStar 𝕜]

instance : ContinuousInv (Matrix.specialUnitaryGroup n 𝕜) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

section TopologicalSemiring

variable [IsTopologicalSemiring 𝕜]

instance : IsTopologicalGroup (Matrix.specialUnitaryGroup n 𝕜) where

end TopologicalSemiring

variable [IsTopologicalRing 𝕜]

/-- The special unitary group of `n × n` matrices is a closed subset of `Matrix n n 𝕜`: it is cut
out of the closed unitary group by the closed condition `det A = 1`. -/
theorem isClosed_specialUnitaryGroup [T1Space 𝕜] :
    IsClosed (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hinter : (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜))
      = (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) ∩ {A | A.det = 1} := by
    ext A
    simpa using Matrix.mem_specialUnitaryGroup_iff
  rw [hinter]
  exact isClosed_unitary.inter
    (isClosed_singleton.preimage (Continuous.matrix_det continuous_id))

end CommRing

section RCLike

variable [RCLike 𝕜]

/-- The unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of `Matrix n n 𝕜`. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact ((isCompact_closedBall (0 : 𝕜) 1).matrix).of_isClosed_subset isClosed_unitary
    fun _ hA _ _ => mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hA _ _)

instance : CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

/-- The special unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of
`Matrix n n 𝕜`. -/
theorem isCompact_specialUnitaryGroup :
    IsCompact (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  isCompact_unitaryGroup.of_isClosed_subset isClosed_specialUnitaryGroup
    fun _ hA => Matrix.specialUnitaryGroup_le_unitaryGroup hA

instance : CompactSpace (Matrix.specialUnitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end RCLike

end Matrix

section GeneralLinear

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [CommRing 𝕜] [StarRing 𝕜]
  [TopologicalSpace 𝕜] [ContinuousStar 𝕜] [IsTopologicalRing 𝕜] [T1Space 𝕜]

/-- **The special unitary subgroup of the general linear group is closed.**  Its carrier is the
preimage of the closed matrix special unitary group under the continuous coercion of units.  This
is the hypothesis the closed-subgroup theorem needs in order to promote it to an embedded Lie
subgroup. -/
theorem isClosed_GLSpecialUnitary :
    IsClosed ((GLSpecialUnitary n 𝕜 : Subgroup (GL n 𝕜)) : Set (GL n 𝕜)) := by
  rw [GLSpecialUnitary.coe_eq_preimage]
  exact (Matrix.isClosed_specialUnitaryGroup (n := n) (𝕜 := 𝕜)).preimage Units.continuous_val

end GeneralLinear

end TauCeti

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- **The unitary subgroup of `GL n 𝕜` is compact** over `ℝ` or `ℂ`: the matrix unitary group is
compact. -/
theorem isCompact_unitarySubgroup :
    IsCompact ((unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) : Set (GL n 𝕜)) :=
  TauCeti.isCompact_unitarySubgroup_units TauCeti.Matrix.isCompact_unitaryGroup

end Matrix.GeneralLinearGroup
end
end TAF_LiteralSource_0436

section TAF_LiteralSource_0437
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Weyl's unitarian trick for the rational representations of `GL n ℂ`

A rational representation `ρ` of `GL n ℂ` restricts, along the inclusion
`Unitary.toUnits : U(n) →* GL n ℂ` of the unitary group, to a representation of the compact group
`U(n)`. **Weyl's unitarian trick** is that nothing is lost in this restriction: a subspace is
`GL n ℂ`-invariant exactly when it is `U(n)`-invariant, and a linear map between two rational
representations intertwines the `GL n ℂ`-actions exactly when it intertwines the `U(n)`-actions.
Consequently a rational representation is irreducible exactly when its restriction to `U(n)` is,
and, since every finite-dimensional continuous representation of a compact group is completely
reducible, every rational representation of `GL n ℂ` is completely reducible.

The bridge between the two groups is that `U(n)` is Zariski dense in `GL n ℂ`
(`TauCeti.Matrix.GeneralLinearGroup.eq_of_mem_rationalFunctions_of_forall_unitary`), together with
the fact that every matrix coefficient `g ↦ f (ρ g w)` of a rational representation is a rational
function on `GL n ℂ` (`TauCeti.IsRationalRep.dual_apply_mem_rationalFunctions`). If `p` is
`U(n)`-invariant, `w ∈ p`, and `f` is a linear functional vanishing on `p`, the rational function
`g ↦ f (ρ g w)` vanishes on `U(n)`, hence everywhere, so `ρ g w ∈ p` for every `g`.

These are the inputs that let the compact-group theory of `U(n)` (Haar averaging, Schur
orthogonality, the Weyl integration formula) be applied to the rational representations of
`GL n ℂ`. Complete reducibility in particular means that a rational representation is a direct
sum of irreducible ones, so that it is described by the multiplicities of its irreducible
constituents rather than by a composition series alone.

## Main results

* `TauCeti.IsRationalRep.apply_mem_of_forall_unitary`: a subspace invariant under the unitary
  group is invariant under `GL n ℂ`.
* `TauCeti.IsRationalRep.subrepresentationOrderIso`: the subrepresentations of `ρ` are those of
  its restriction to `U(n)`.
* `TauCeti.IsRationalRep.isIrreducible_comp_toUnits_iff`: `ρ` is irreducible exactly when its
  restriction to `U(n)` is.
* `TauCeti.IsRationalRep.isIntertwiningMap_of_comp_toUnits` and
  `TauCeti.IsRationalRep.intertwiningMapEquiv`: the intertwining maps between two rational
  representations are those between their restrictions to `U(n)`.
* `TauCeti.IsRationalRep.continuous_dual_apply_toUnits`: the restriction of a rational
  representation to `U(n)` has continuous matrix coefficients.
* `TauCeti.IsRationalRep.isSemisimpleRepresentation`: **every rational representation of
  `GL n ℂ` is completely reducible.**
* `TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq`: rational representations
  whose characters agree on the diagonal torus are equivalent.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 2.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 9.3.
-/

public section

open TauCeti.Matrix.GeneralLinearGroup

namespace TauCeti

namespace IsRationalRep

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **A subspace invariant under the unitary group is invariant under `GL n ℂ`.** If `ρ` is
rational and `p` is preserved by every unitary matrix, then it is preserved by every invertible
matrix: for `w ∈ p` and a linear functional `f` vanishing on `p`, the rational function
`g ↦ f (ρ g w)` vanishes on the unitary group, hence everywhere. -/
theorem apply_mem_of_forall_unitary (h : IsRationalRep ρ) {p : Submodule ℂ W}
    (hp : ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ∀ v ∈ p, ρ (Unitary.toUnits u) v ∈ p)
    (g : GL (Fin n) ℂ) {v : W} (hv : v ∈ p) : ρ g v ∈ p := by
  by_contra hgv
  obtain ⟨f, hf, hpf⟩ := p.exists_le_ker_of_notMem hgv
  refine hf (congrFun (eq_of_mem_rationalFunctions_of_forall_unitary
    (h.dual_apply_mem_rationalFunctions f v) (zero_mem _) fun u => ?_) g)
  exact hpf (hp u v hv)

/-- **The subrepresentations of a rational representation are those of its restriction to the
unitary group.** Restriction along `Unitary.toUnits` keeps the underlying submodule, and every
subspace invariant under the unitary group is already invariant under `GL n ℂ`
(`TauCeti.IsRationalRep.apply_mem_of_forall_unitary`). -/
def subrepresentationOrderIso (h : IsRationalRep ρ) :
    Subrepresentation (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g _ hv :=
        h.apply_mem_of_forall_unitary (fun u _ hw => S.apply_mem_toSubmodule u hw) g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule u _ hv := S.apply_mem_toSubmodule (Unitary.toUnits u) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

/-- The correspondence `TauCeti.IsRationalRep.subrepresentationOrderIso` keeps the underlying
submodule. -/
@[simp]
theorem subrepresentationOrderIso_apply_toSubmodule (h : IsRationalRep ρ)
    (S : Subrepresentation
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))) :
    (h.subrepresentationOrderIso S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- The inverse correspondence `TauCeti.IsRationalRep.subrepresentationOrderIso` keeps the
underlying submodule. -/
@[simp]
theorem subrepresentationOrderIso_symm_apply_toSubmodule (h : IsRationalRep ρ)
    (S : Subrepresentation ρ) :
    (h.subrepresentationOrderIso.symm S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- **A rational representation is irreducible exactly when its restriction to the unitary group
is.** -/
theorem isIrreducible_comp_toUnits_iff (h : IsRationalRep ρ) :
    Representation.IsIrreducible
        (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ)) ↔
      ρ.IsIrreducible :=
  h.subrepresentationOrderIso.isSimpleOrder_iff

section Intertwining

variable {W' : Type*} [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **A linear map between rational representations intertwining the unitary group intertwines
`GL n ℂ`.** For `w` and a linear functional `f`, the two rational functions `g ↦ f (φ (ρ g w))`
and `g ↦ f (σ g (φ w))` agree on the unitary group, hence everywhere. -/
theorem isIntertwiningMap_of_comp_toUnits (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    {φ : W →ₗ[ℂ] W'}
    (hφ : Representation.IsIntertwiningMap
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      (σ.comp Unitary.toUnits) φ) :
    ρ.IsIntertwiningMap σ φ := by
  refine ⟨fun g w => ?_⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  rw [map_sub, sub_eq_zero]
  refine congrFun (eq_of_mem_rationalFunctions_of_forall_unitary
    (hρ.dual_apply_mem_rationalFunctions (f ∘ₗ φ) w)
    (hσ.dual_apply_mem_rationalFunctions f (φ w)) fun u => ?_) g
  simpa using congrArg f (hφ.isIntertwining u w)

/-- **The intertwining maps between two rational representations are those between their
restrictions to the unitary group**, as a linear equivalence keeping the underlying linear map
(`TauCeti.IsRationalRep.isIntertwiningMap_of_comp_toUnits`). -/
noncomputable def intertwiningMapEquiv (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    Representation.IntertwiningMap
        (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
        (σ.comp Unitary.toUnits) ≃ₗ[ℂ] Representation.IntertwiningMap ρ σ where
  toFun φ := φ.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
    (hρ.isIntertwiningMap_of_comp_toUnits hσ
      ⟨fun u w => by simpa using Representation.IntertwiningMap.isIntertwining _ _ φ u w⟩
      ).isIntertwining
  invFun φ := φ.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ fun u w => by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ φ (Unitary.toUnits u) w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence `TauCeti.IsRationalRep.intertwiningMapEquiv` keeps the underlying function. -/
@[simp]
theorem coe_intertwiningMapEquiv_apply (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (φ : Representation.IntertwiningMap
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      (σ.comp Unitary.toUnits)) :
    ⇑(hρ.intertwiningMapEquiv hσ φ) = ⇑φ :=
  (rfl)

/-- The inverse of `TauCeti.IsRationalRep.intertwiningMapEquiv` keeps the underlying function. -/
@[simp]
theorem coe_intertwiningMapEquiv_symm_apply (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (φ : Representation.IntertwiningMap ρ σ) :
    ⇑((hρ.intertwiningMapEquiv hσ).symm φ) = ⇑φ :=
  (rfl)

end Intertwining

/-- **The restriction of a rational representation to the unitary group is continuous**: its
matrix coefficients `u ↦ f (ρ u w)` are continuous functions on `U(n)`, being polynomials in the
entries of `u` divided by a power of the nonvanishing `det u`. -/
theorem continuous_dual_apply_toUnits (h : IsRationalRep ρ) (f : Module.Dual ℂ W) (w : W) :
    Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => f (ρ (Unitary.toUnits u) w) := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions_iff_inv.mp (h.dual_apply_mem_rationalFunctions f w)
  have hU : Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      (u : Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val
  simp only [hP, Unitary.val_toUnits_apply]
  refine ((hU.matrix_det.pow m).inv₀ fun u => pow_ne_zero m ?_).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun ij => hU.matrix_elem ij.1 ij.2))
  simpa using _root_.Matrix.GeneralLinearGroup.det_ne_zero (Unitary.toUnits u)

/-- **Every rational representation of `GL n ℂ` is completely reducible.** Its restriction to the
compact group `U(n)` is continuous, hence completely reducible by Haar averaging
(`Representation.isSemisimpleRepresentation_of_continuous`), and it has the same
subrepresentations (`TauCeti.IsRationalRep.subrepresentationOrderIso`). -/
theorem isSemisimpleRepresentation (h : IsRationalRep ρ) : ρ.IsSemisimpleRepresentation := by
  have := h.finite
  exact h.subrepresentationOrderIso.complementedLattice_iff.mp
    (Representation.isSemisimpleRepresentation_of_continuous _ h.continuous_dual_apply_toUnits)

section Character

variable {W' : Type*} [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **Rational representations are determined by their characters on the diagonal torus.** Two
rational representations of `GL n ℂ` whose characters agree at every invertible diagonal matrix
are equivalent.

Every unitary matrix is unitarily conjugate to a diagonal one
(`TauCeti.exists_isConj_unitaryTorusHom`), so the restrictions to `U(n)` have the same character.
They are semisimple, hence equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`), and an
equivalence of the restrictions intertwines `GL n ℂ`
(`TauCeti.IsRationalRep.intertwiningMapEquiv`). -/
theorem nonempty_equiv_of_forall_character_diagGL_eq (hρ : IsRationalRep ρ)
    (hσ : IsRationalRep σ)
    (h : ∀ t : Fin n → ℂˣ, ρ.character (diagGL t) = σ.character (diagGL t)) :
    Nonempty (ρ.Equiv σ) := by
  have := hρ.finite
  have := hσ.finite
  let ρu : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W := ρ.comp Unitary.toUnits
  let σu : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W' := σ.comp Unitary.toUnits
  have : ρu.IsSemisimpleRepresentation :=
    Representation.isSemisimpleRepresentation_of_continuous _ hρ.continuous_dual_apply_toUnits
  have : σu.IsSemisimpleRepresentation :=
    Representation.isSemisimpleRepresentation_of_continuous _ hσ.continuous_dual_apply_toUnits
  have hchar : ρu.character = σu.character := funext fun u => by
    obtain ⟨z, hz⟩ := exists_isConj_unitaryTorusHom u
    obtain ⟨c, hc⟩ := isConj_iff.mp hz
    rw [← Representation.char_conj ρu u c, hc, ← Representation.char_conj σu u c, hc]
    simpa [ρu, σu, Representation.character, toUnits_unitaryTorusHom] using h _
  obtain ⟨e⟩ :=
    Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation ρu σu hchar
  exact ⟨.mk e.toLinearEquiv (hρ.intertwiningMapEquiv hσ e.toIntertwiningMap).isIntertwining'⟩

end Character

end IsRationalRep

end TauCeti
end
end TAF_LiteralSource_0437

section TAF_LiteralSource_0438
/- Original module: PaperVerification.AlternatingFormsRationalRepresentation -/


/-!
# Rationality of the actual quotient representation

The two closure operations needed in addition to Tau Ceti's existing API
are duals and subrepresentations.  Matrix inversion is proved rational by
the ordinary adjugate formula.  Subrepresentations use extension of linear
functionals, so no invariant complement or reductivity is assumed here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Matrix

namespace PaperVerification.AlternatingForms.RationalRepresentation

open TauCeti TauCeti.Matrix.GeneralLinearGroup

theorem adjugateEntry_polynomial (n : ℕ) (i j : Fin n) :
    (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).adjugate i j) ∈
      polynomialFunctions ℂ n := by
  refine mem_polynomialFunctions.mpr
    ⟨(Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate i j, fun g => ?_⟩
  have h := (MvPolynomial.eval
    (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)).map_adjugate
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have he : (MvPolynomial.eval
      (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)).mapMatrix
        (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) =
      (g : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    simp [Matrix.mvPolynomialX]
  rw [he] at h
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) h).symm

theorem rational_pointwise_add {n : ℕ} {f g : GL (Fin n) ℂ → ℂ}
    (hf : f∈rationalFunctions ℂ n) (hg : g∈rationalFunctions ℂ n) :
    (fun x => f x+g x)∈rationalFunctions ℂ n := by
  have he : f+g=(fun x => f x+g x) := by funext x; rfl
  rw [←he]
  exact (rationalFunctions ℂ n).add_mem hf hg

theorem rational_pointwise_mul {n : ℕ} {f g : GL (Fin n) ℂ → ℂ}
    (hf : f∈rationalFunctions ℂ n) (hg : g∈rationalFunctions ℂ n) :
    (fun x => f x*g x)∈rationalFunctions ℂ n := by
  have he : f*g=(fun x => f x*g x) := by funext x; rfl
  rw [←he]
  exact (rationalFunctions ℂ n).mul_mem hf hg

theorem inverseEntry_rational (n : ℕ) (i j : Fin n) :
    (fun g : GL (Fin n) ℂ => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) i j) ∈
      rationalFunctions ℂ n := by
  have hd : (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det⁻¹) ∈
      rationalFunctions ℂ n := by
    simpa only [_root_.zpow_neg_one, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply] using det_zpow_mem_rationalFunctions (k := ℂ) (n := n) (-1)
  have ha := polynomialFunctions_le_rationalFunctions (adjugateEntry_polynomial n i j)
  have h := rational_pointwise_mul hd ha
  simpa only [Pi.mul_apply, Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using h

theorem rational_comp_inverse (n : ℕ) (f : GL (Fin n) ℂ → ℂ)
    (hf : f ∈ rationalFunctions ℂ n) :
    (fun g => f g⁻¹) ∈ rationalFunctions ℂ n := by
  have hpoly (P : MvPolynomial (Fin n × Fin n) ℂ) :
      (fun g : GL (Fin n) ℂ => MvPolynomial.eval
        (fun p => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P) ∈
          rationalFunctions ℂ n := by
    induction P using MvPolynomial.induction_on with
    | C a =>
        simp only [MvPolynomial.eval_C]
        exact (rationalFunctions ℂ n).algebraMap_mem a
    | add P Q hP hQ =>
        simpa only [map_add] using rational_pointwise_add hP hQ
    | mul_X P i hP =>
        simpa only [map_mul, MvPolynomial.eval_X] using
          rational_pointwise_mul hP (inverseEntry_rational n i.1 i.2)
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions_iff_inv.mp hf
  have he : (fun g : GL (Fin n) ℂ => f g⁻¹) =
      (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det^m) *
        (fun g : GL (Fin n) ℂ => MvPolynomial.eval
          (fun p => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P) := by
    funext g
    rw [Pi.mul_apply, hP]
    congr 1
    · rw [← Matrix.GeneralLinearGroup.val_det_apply,
        map_inv, Units.val_inv_eq_inv_val, inv_pow, inv_inv,
        Matrix.GeneralLinearGroup.val_det_apply]
    · simp only [Matrix.GeneralLinearGroup.coe_inv]
  rw [he]
  exact (rationalFunctions ℂ n).mul_mem
    (polynomialFunctions_le_rationalFunctions
      ((polynomialFunctions ℂ n).pow_mem det_mem_polynomialFunctions m)) (hpoly P)

section Closure

variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) V}
  {σ : Representation ℂ (GL (Fin n) ℂ) W}

theorem dual (hρ : IsRationalRep ρ) : IsRationalRep ρ.dual := by
  letI := hρ.finite
  let b := Module.finBasis ℂ V
  apply (isRationalRep_iff_forall_mem_rationalFunctions b.dualBasis).mpr
  intro i j
  have h := rational_comp_inverse n
    (fun g => b.dualBasis j (ρ g (b i))) (hρ.dual_apply_mem_rationalFunctions _ _)
  simpa only [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] using h

theorem prod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.prod σ) := by
  letI := hρ.finite
  letI := hσ.finite
  apply isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
  intro f v
  have he : (fun g => f (ρ.prod σ g v)) =
      (fun g => (f ∘ₗ LinearMap.inl ℂ V W) (ρ g v.1)) +
        (fun g => (f ∘ₗ LinearMap.inr ℂ V W) (σ g v.2)) := by
    funext g
    change f (ρ g v.1, σ g v.2) = f (ρ g v.1, 0) + f (0, σ g v.2)
    rw [← map_add]
    congr 1
    simp
  rw [he]
  exact (rationalFunctions ℂ n).add_mem
    (hρ.dual_apply_mem_rationalFunctions _ _) (hσ.dual_apply_mem_rationalFunctions _ _)

theorem subrepresentation (hρ : IsRationalRep ρ) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) :
    IsRationalRep (ρ.subrepresentation S hS) := by
  letI := hρ.finite
  apply isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
  intro f v
  have h := hρ.dual_apply_mem_rationalFunctions (Subspace.dualLift S f) v.val
  have he : (fun g => f (ρ.subrepresentation S hS g v)) =
      (fun g => Subspace.dualLift S f (ρ g v.val)) := by
    funext g
    exact (Subspace.dualLift_of_subtype (W := S) (φ := f)
      (ρ.subrepresentation S hS g v)).symm
  rw [he]
  exact h

theorem transport (hρ : IsRationalRep ρ) (e : ρ.Equiv σ) : IsRationalRep σ :=
  hρ.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective

end Closure

open SymmetricPencil

theorem model_rational (t : ℕ) : IsRationalRep (modelRepresentation ℂ t) :=
  prod (dual (TauCeti.isPolynomialRep_symPowerRep 2 t).isRationalRep)
    (TauCeti.isPolynomialRep_symPowerRep 2 (t+1)).isRationalRep

theorem coordinate_rational (t : ℕ) : IsRationalRep (coordinateRepresentation ℂ t) :=
  transport (model_rational t) (coordinateRepresentationEquiv ℂ t).symm

theorem quotient_rational (t s : ℕ) : IsRationalRep (quotientRepresentation ℂ t s) := by
  let S := exteriorDegreeRelations (K := ℂ)
    (oddPathFirstQuadratic (K := ℂ) (Pi.basisFun ℂ (Fin (2*(t+1)+1))))
    (oddPathSecondQuadratic (K := ℂ) (Pi.basisFun ℂ (Fin (2*(t+1)+1)))) s
  let f : ((coordinateRepresentation ℂ t).exteriorPower s).IntertwiningMap
      (quotientRepresentation ℂ t s) :=
    .mk S.mkQ (by
      intro g
      apply LinearMap.ext
      intro x
      change S.mkQ ((coordinateRepresentation ℂ t).exteriorPower s g x) =
        quotientRepresentation ℂ t s g (S.mkQ x)
      rw [Representation.exteriorPower_apply]
      exact (quotientRepresentation_mk ℂ t s g x).symm)
  exact ((coordinate_rational t).exteriorPower s).of_surjective f S.mkQ_surjective

theorem bigraded_rational (t p q : ℕ) : IsRationalRep (bigradedRepresentation ℂ t p q) :=
  subrepresentation (quotient_rational t (p+q)) _ (bigradedPiece_invariant ℂ t p q)

end PaperVerification.AlternatingForms.RationalRepresentation
end
end
end TAF_LiteralSource_0438

section TAF_LiteralSource_0439
/- Original module: PaperVerification.AlternatingFormsTopSelection -/


/-!
# The original good words are exactly the interlacing selections

The `a`-set is selected and the `c`-set is the complement of the selected
`b`-set.  The strip inequalities are equivalent to the two prefix-count
inequalities below.  Sorting then recovers the interlacing inequalities.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open BooleanWalks

theorem prefix_compl_add {n : ℕ} (C : Finset (Fin n)) (r : ℕ) (hr : r≤n) :
    prefixCount C r + prefixCount Cᶜ r = r := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin n => i.val<r)) (fun i => i∈C)
  have h₁ : (Finset.univ.filter (fun i : Fin n => i.val<r)).filter (fun i => i∈C) =
      C.filter (fun i => i.val<r) := by
    ext i
    simp [and_comm]
  have h₂ : (Finset.univ.filter (fun i : Fin n => i.val<r)).filter (fun i => ¬i∈C) =
      Cᶜ.filter (fun i => i.val<r) := by
    ext i
    simp [and_comm]
  rw [h₁, h₂, Fin.card_filter_val_lt, Nat.min_eq_right hr] at h
  exact h

theorem prefixCount_mono {n : ℕ} (C : Finset (Fin n)) : Monotone (prefixCount C) := by
  intro a b hab
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi,hia⟩
  exact Finset.mem_filter.mpr ⟨hi, hia.trans_le hab⟩

theorem index_lt_prefix_iff {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m)
    (i : Fin m) (r : ℕ) :
    i.val < prefixCount S r ↔ (S.orderEmbOfFin hS i).val < r := by
  have he : prefixCount S r =
      (Finset.univ.filter (fun j : Fin m => (S.orderEmbOfFin hS j).val<r)).card := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S hS]
    rw [prefixCount, Finset.filter_image,
      Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective]
  rw [he]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hb : (S.orderEmbOfFin hS b).val ≤ (S.orderEmbOfFin hS a).val :=
    (S.orderEmbOfFin hS).monotone hba
  omega

theorem prefix_at_index {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m) (i : Fin m) :
    prefixCount S (S.orderEmbOfFin hS i).val=i.val := by
  have he' (r : ℕ) : prefixCount S r =
      (Finset.univ.filter (fun j : Fin m => (S.orderEmbOfFin hS j).val < r)).card := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S hS]
    rw [prefixCount, Finset.filter_image,
      Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective]
  have he : prefixCount S (S.orderEmbOfFin hS i).val =
      (Finset.univ.filter (fun j : Fin m => j < i)).card := by
    rw [he']
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (S.orderEmbOfFin hS).lt_iff_lt
  rw [he]
  have hf : (Finset.univ.filter (fun j : Fin m => j < i))=Finset.Iio i := by
    ext j
    simp
  rw [hf, Fin.card_Iio]

theorem prefix_after_index {m n : ℕ} (S : Finset (Fin n)) (hS : S.card=m) (i : Fin m) :
    prefixCount S ((S.orderEmbOfFin hS i).val+1)=i.val+1 := by
  rw [prefixCount_succ, prefix_at_index, selectedAt_position,
    if_pos (S.orderEmbOfFin_mem hS i)]

def GoodPair (p q : ℕ) :=
  {AC : Finset (Fin (p+q)) × Finset (Fin (p+q+1)) //
    AC.1.card=p ∧ AC.2.card=p+1 ∧ ∀ r, r≤p+q →
      prefixCount AC.1 r ≤ prefixCount AC.2 r ∧
        prefixCount AC.2 (r+1) ≤ prefixCount AC.1 r+1}

instance (p q : ℕ) : Fintype (GoodPair p q) := by
  unfold GoodPair
  infer_instance

def goodPairToInterlacing {p q : ℕ} (P : GoodPair p q) : Interlacing p q :=
  ⟨(P.val.1.orderEmbOfFin P.property.1, P.val.2.orderEmbOfFin P.property.2.1),
    (P.val.1.orderEmbOfFin P.property.1).strictMono,
    (P.val.2.orderEmbOfFin P.property.2.1).strictMono, by
      intro i
      change (P.val.2.orderEmbOfFin P.property.2.1 i.castSucc).val ≤
          (P.val.1.orderEmbOfFin P.property.1 i).val ∧
        (P.val.1.orderEmbOfFin P.property.1 i).val <
          (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val
      constructor
      · have hi := (P.val.1.orderEmbOfFin P.property.1 i).isLt
        have hp := (P.property.2.2 ((P.val.1.orderEmbOfFin P.property.1 i).val+1)
          (by omega)).1
        rw [prefix_after_index] at hp
        have hc := (index_lt_prefix_iff P.val.2 P.property.2.1 i.castSucc
          ((P.val.1.orderEmbOfFin P.property.1 i).val+1)).mp (by simpa using hp)
        omega
      · have hi := (P.val.2.orderEmbOfFin P.property.2.1 i.succ).isLt
        have hp := (P.property.2.2 (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val
          (by omega)).2
        rw [prefix_after_index] at hp
        have ha := (index_lt_prefix_iff P.val.1 P.property.1 i
          (P.val.2.orderEmbOfFin P.property.2.1 i.succ).val).mp (by
            simp only [Fin.val_succ] at hp
            omega)
        exact ha⟩

def interlacingToGoodPair {p q : ℕ} (I : Interlacing p q) : GoodPair p q := by
  let A := GoodPaths.selectedSet I.val.1
  let C := GoodPaths.selectedSet I.val.2
  have ha : A.card=p := GoodPaths.selectedSet_card I.property.1
  have hc : C.card=p+1 := GoodPaths.selectedSet_card I.property.2.1
  have hea : A.orderEmbOfFin ha=I.val.1 :=
    (Finset.orderEmbOfFin_unique ha
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.1).symm
  have hec : C.orderEmbOfFin hc=I.val.2 :=
    (Finset.orderEmbOfFin_unique hc
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.2.1).symm
  refine ⟨(A,C), ha, hc, ?_⟩
  intro r hr
  change prefixCount A r ≤ prefixCount C r ∧
    prefixCount C (r+1) ≤ prefixCount A r+1
  constructor
  · by_contra h
    have hA := (prefixCount_le A r).trans_eq ha
    let i : Fin p := ⟨prefixCount C r, by omega⟩
    have hai := (index_lt_prefix_iff A ha i r).mp (by dsimp [i]; omega)
    have hci := (index_lt_prefix_iff C hc i.castSucc r).not.mp (by dsimp [i]; omega)
    rw [hea] at hai
    rw [hec] at hci
    have hb := (I.property.2.2 i).1
    omega
  · by_contra h
    have hC := (prefixCount_le C (r+1)).trans_eq hc
    let i : Fin p := ⟨prefixCount A r, by omega⟩
    have hci := (index_lt_prefix_iff C hc i.succ (r+1)).mp (by dsimp [i]; omega)
    have hai := (index_lt_prefix_iff A ha i r).not.mp (by dsimp [i]; omega)
    rw [hea] at hai
    rw [hec] at hci
    have hb := (I.property.2.2 i).2
    omega

def goodPairInterlacingEquiv (p q : ℕ) : GoodPair p q ≃ Interlacing p q where
  toFun := goodPairToInterlacing
  invFun := interlacingToGoodPair
  left_inv P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Finset.image_orderEmbOfFin_univ P.val.1 P.property.1
    · exact Finset.image_orderEmbOfFin_univ P.val.2 P.property.2.1
  right_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.orderEmbOfFin_unique (GoodPaths.selectedSet_card I.property.1)
        (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.1).symm
    · exact (Finset.orderEmbOfFin_unique (GoodPaths.selectedSet_card I.property.2.1)
        (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property.2.1).symm

def selectedAB {k : ℕ} (A : Finset (Fin k)) (B : Finset (Fin (k+1))) :
    Finset (Fin (2*k+1)) := (A.disjSum B).map (abIndex k).toEmbedding

def originalPrefix {k : ℕ} (S : Finset (Fin (2*k+1))) (r : ℕ) : ℕ :=
  (S.filter (fun i => i.val+1<r)).card

theorem originalPrefix_selectedAB {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) r =
      (A.filter (fun i => 2*i.val+2<r)).card +
        (B.filter (fun i => 2*i.val+1<r)).card := by
  rw [originalPrefix, selectedAB, Finset.filter_map, Finset.card_map]
  have he : (A.disjSum B).filter (fun x => (abIndex k x).val+1<r) =
      (A.filter (fun i => 2*i.val+2<r)).disjSum
        (B.filter (fun i => 2*i.val+1<r)) := by
    ext x
    cases x with
    | inl i =>
        simp only [Finset.mem_filter, Finset.inl_mem_disjSum]
        change (i∈A ∧ (2*i.val+1)+1<r) ↔ (i∈A ∧ 2*i.val+2<r)
        exact and_congr_right (fun _ => by omega)
    | inr i =>
        simp only [Finset.mem_filter, Finset.inr_mem_disjSum]
        rfl
  change ((A.disjSum B).filter (fun x => (abIndex k x).val+1<r)).card = _
  rw [he, Finset.card_disjSum]

theorem originalPrefix_odd {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) (2*r+1) = prefixCount A r+prefixCount B r := by
  rw [originalPrefix_selectedAB]
  have ha : A.filter (fun i => 2*i.val+2<2*r+1)=A.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  have hb : B.filter (fun i => 2*i.val+1<2*r+1)=B.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  rw [ha,hb]
  rfl

theorem originalPrefix_even {k : ℕ} (A : Finset (Fin k))
    (B : Finset (Fin (k+1))) (r : ℕ) :
    originalPrefix (selectedAB A B) (2*r+2) = prefixCount A r+prefixCount B (r+1) := by
  rw [originalPrefix_selectedAB]
  have ha : A.filter (fun i => 2*i.val+2<2*r+2)=A.filter (fun i => i.val<r) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  have hb : B.filter (fun i => 2*i.val+1<2*r+2)=B.filter (fun i => i.val<r+1) := by
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => by omega)
  rw [ha,hb]
  rfl

theorem selectedAB_strip_iff {p q : ℕ} (A : Finset (Fin (p+q)))
    (C : Finset (Fin (p+q+1))) (hA : A.card=p) (hC : C.card=p+1) :
    (∀ r, r≤2*(p+q)+3 →
      2*originalPrefix (selectedAB A Cᶜ) r≤r ∧
        r+2*(p+q)≤2*(p+q)+3+2*originalPrefix (selectedAB A Cᶜ) r) ↔
    (∀ r, r≤p+q → prefixCount A r≤prefixCount C r ∧
      prefixCount C (r+1)≤prefixCount A r+1) := by
  constructor
  · intro h r hr
    have ho := h (2*r+1) (by omega)
    have he := h (2*r+2) (by omega)
    rw [originalPrefix_odd] at ho
    rw [originalPrefix_even] at he
    have hc₁ := prefix_compl_add C r (by omega)
    have hc₂ := prefix_compl_add C (r+1) (by omega)
    constructor <;> omega
  · intro h r hr
    by_cases hz : r=0
    · subst r
      simp [originalPrefix]
    · by_cases hpar : r%2=1
      · let j := r/2
        have he : r=2*j+1 := by dsimp [j]; omega
        rw [he, originalPrefix_odd]
        by_cases hj : j≤p+q
        · have hp := h j hj
          have hc := prefix_compl_add C j (by omega)
          have hm : prefixCount C j ≤ prefixCount C (j+1) :=
            prefixCount_mono C (Nat.le_succ j)
          constructor <;> omega
        · have hj' : j=p+q+1 := by omega
          rw [hj', prefixCount_all A _ (by omega), prefixCount_all Cᶜ _ le_rfl,
            hA, Finset.card_compl, Fintype.card_fin, hC]
          constructor <;> omega
      · let j := r/2-1
        have he : r=2*j+2 := by dsimp [j]; omega
        have hj : j≤p+q := by omega
        rw [he, originalPrefix_even]
        have hp := h j hj
        have hc := prefix_compl_add C (j+1) (by omega)
        have hm : prefixCount C j ≤ prefixCount C (j+1) :=
          prefixCount_mono C (Nat.le_succ j)
        constructor <;> omega

end PaperVerification.AlternatingForms.TopInterlacing
end
end
end TAF_LiteralSource_0439

section TAF_LiteralSource_0440
/- Original module: PaperVerification.AlternatingFormsTopGoodWords -/


/-!
# The actual top bidegree basis and its interlacing indexing equivalence

All three index sets below are independently defined.  The source consists
of the original good exterior words of total degree `p+q` and `a`-degree
`p`; the intermediate set records the selected `a` indices and omitted
`b` indices; the target is the symmetric-power monomial indexing set.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open BooleanWalks

def TopWord (p q : ℕ) :=
  {I : GoodOddIndex (p+q) (p+q) // Bidegree.goodADegree I=p}

instance (p q : ℕ) : Fintype (TopWord p q) := by
  unfold TopWord
  infer_instance

theorem selectedAB_injective {k : ℕ} {A A' : Finset (Fin k)}
    {B B' : Finset (Fin (k+1))} (h : selectedAB A B=selectedAB A' B') :
    A=A' ∧ B=B' :=
  Finset.disjSum_inj.mp (Finset.map_injective (abIndex k).toEmbedding h)

theorem aDegree_of_selectedAB {k s : ℕ} (I : Fin s → Fin (2*k+1))
    (hI : StrictMono I) (A : Finset (Fin k)) (B : Finset (Fin (k+1)))
    (hS : GoodPaths.selectedSet I=selectedAB A B) :
    Bidegree.aWordDegree I=A.card := by
  have hsum : Bidegree.aWordDegree I =
      ∑ j ∈ GoodPaths.selectedSet I, Bidegree.aIndexDegree j := by
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro a ha b hb hab
      exact hI.injective hab
  rw [hsum, hS, selectedAB, Finset.sum_map, Finset.sum_disjSum]
  have ha (i : Fin k) : Bidegree.aIndexDegree ((abIndex k) (.inl i))=1 := by
    have h : (2*i.val+1)%2=1 := by omega
    simp [Bidegree.aIndexDegree, abIndex, h]
  have hb (i : Fin (k+1)) : Bidegree.aIndexDegree ((abIndex k) (.inr i))=0 := by
    have h : (2*i.val)%2≠1 := by omega
    simp [Bidegree.aIndexDegree, abIndex, h]
  change (∑ i∈A, Bidegree.aIndexDegree (abIndex k (.inl i))) +
    (∑ j∈B, Bidegree.aIndexDegree (abIndex k (.inr j))) = A.card
  simp only [ha, hb, Finset.sum_const, Finset.sum_const_zero, Nat.nsmul_eq_mul,
    Nat.mul_one, Nat.mul_zero, Nat.add_zero]

theorem goodPair_selected_card {p q : ℕ} (P : GoodPair p q) :
    (selectedAB P.val.1 P.val.2ᶜ).card=p+q := by
  rw [selectedAB, Finset.card_map, Finset.card_disjSum, P.property.1,
    Finset.card_compl, Fintype.card_fin, P.property.2.1]
  omega

def goodPairToTopWord {p q : ℕ} (P : GoodPair p q) : TopWord p q := by
  let S := selectedAB P.val.1 P.val.2ᶜ
  have hS : S.card=p+q := goodPair_selected_card P
  let I := S.orderEmbOfFin hS
  have hi : GoodPaths.selectedSet I=S := Finset.image_orderEmbOfFin_univ S hS
  have hg : ∀ j, 2*j.val≤(I j).val ∧ (I j).val+2*(p+q)≤2*(p+q)+2+2*j.val := by
    apply (GoodPaths.good_bounds_iff_prefix_strip (p+q) (p+q) I I.strictMono).mpr
    intro r hr
    rw [GoodPaths.selectedBefore_eq_filter_card I.strictMono, hi]
    exact (selectedAB_strip_iff P.val.1 P.val.2 P.property.1 P.property.2.1).mpr
      P.property.2.2 r hr
  refine ⟨⟨⟨I,I.strictMono⟩,hg⟩, ?_⟩
  change Bidegree.aWordDegree I=p
  exact (aDegree_of_selectedAB I I.strictMono P.val.1 P.val.2ᶜ hi).trans P.property.1

theorem goodPairToTopWord_selected {p q : ℕ} (P : GoodPair p q) :
    GoodPaths.selectedSet (goodPairToTopWord P).val.val.val = selectedAB P.val.1 P.val.2ᶜ :=
  Finset.image_orderEmbOfFin_univ _ (goodPair_selected_card P)

theorem goodPairToTopWord_injective (p q : ℕ) :
    Function.Injective (goodPairToTopWord (p := p) (q := q)) := by
  intro P Q h
  have hs := congrArg (fun I : TopWord p q => GoodPaths.selectedSet I.val.val.val) h
  rw [goodPairToTopWord_selected, goodPairToTopWord_selected] at hs
  obtain ⟨ha,hb⟩ := selectedAB_injective hs
  apply Subtype.ext
  exact Prod.ext ha (by simpa only [compl_compl] using congrArg (fun C => Cᶜ) hb)

theorem goodPairToTopWord_surjective (p q : ℕ) :
    Function.Surjective (goodPairToTopWord (p := p) (q := q)) := by
  intro I
  let S := GoodPaths.selectedSet I.val.val.val
  let T := S.map (abIndex (p+q)).symm.toEmbedding
  let A := T.toLeft
  let B := T.toRight
  let C := Bᶜ
  have hs : selectedAB A B=S := by
    rw [selectedAB]
    change (T.toLeft.disjSum T.toRight).map _=S
    rw [Finset.toLeft_disjSum_toRight]
    simp [T, Finset.map_map]
  have ha : A.card=p := by
    have h := aDegree_of_selectedAB I.val.val.val I.val.val.property A B hs.symm
    exact h.symm.trans I.property
  have hc : C.card=p+1 := by
    have htotal : A.card+B.card=p+q := by
      have hcard := congrArg Finset.card hs
      rw [selectedAB, Finset.card_map, Finset.card_disjSum] at hcard
      exact hcard.trans (GoodPaths.selectedSet_card I.val.val.property)
    change (Bᶜ).card=p+1
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hgood : ∀ r, r≤p+q → prefixCount A r≤prefixCount C r ∧
      prefixCount C (r+1)≤prefixCount A r+1 := by
    apply (selectedAB_strip_iff A C ha hc).mp
    intro r hr
    have hp := (GoodPaths.good_bounds_iff_prefix_strip (p+q) (p+q)
      I.val.val.val I.val.val.property).mp I.val.property r hr
    rw [GoodPaths.selectedBefore_eq_filter_card I.val.val.property] at hp
    simpa only [C, compl_compl, hs, S, originalPrefix] using hp
  let P : GoodPair p q := ⟨(A,C),ha,hc,hgood⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply (GoodPaths.increasingSelectionEquiv (p+q) (2*(p+q)+1)).injective
  apply Subtype.ext
  change GoodPaths.selectedSet (goodPairToTopWord P).val.val.val=S
  rw [goodPairToTopWord_selected]
  simpa only [P, C, compl_compl] using hs

def topWordGoodPairEquiv (p q : ℕ) : TopWord p q ≃ GoodPair p q :=
  (Equiv.ofBijective goodPairToTopWord
    ⟨goodPairToTopWord_injective p q, goodPairToTopWord_surjective p q⟩).symm

def topWordInterlacingEquiv (p q : ℕ) : TopWord p q ≃ Interlacing p q :=
  (topWordGoodPairEquiv p q).trans (goodPairInterlacingEquiv p q)

/-- Every actual good word in the original top bidegree corresponds to
exactly one symmetric monomial, in the full parameter range. -/
def topWordSymEquiv (p q : ℕ) : TopWord p q ≃ Sym (Fin (q+1)) (2*p+1) :=
  (topWordInterlacingEquiv p q).trans (interlacingSymEquiv p q)

theorem topWord_card (p q : ℕ) : Fintype.card (TopWord p q)=(2*p+q+1).choose q := by
  rw [Fintype.card_congr (topWordInterlacingEquiv p q), interlacing_card]

/-- The dimension clause of Corollary 5.2 for the actual exterior quotient. -/
theorem actual_top_bigraded_dimension {K : Type*} [Field K] [CharZero K] (p q : ℕ) :
    Module.finrank K (Bidegree.actualBigradedPiece (K := K) (p+q) p q) =
      (2*p+q+1).choose q := by
  rw [Bidegree.finrank_actualBigradedPiece]
  change Nat.card (TopWord p q)=_
  rw [Nat.card_eq_fintype_card]
  exact topWord_card p q

end PaperVerification.AlternatingForms.TopInterlacing
end
end
end TAF_LiteralSource_0440

section TAF_LiteralSource_0441
/- Original module: PaperVerification.AlternatingFormsSymmetricPencilWeights -/


/-!
# Torus characters of the actual quotient pieces

Weights are computed on the original vector representation and then on its
actual exterior quotient.  The good basis is used only to compute the trace
of that already constructed action.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct Classical

namespace PaperVerification.AlternatingForms.SymmetricPencil

open TopInterlacing

variable (K : Type) [Field K]

def aWeight (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin k) : Kˣ :=
  u 0^((i.val : ℤ)+1-k) * u 1^(-(i.val : ℤ))

def bWeight (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin (k+1)) : Kˣ :=
  u 0^((k : ℤ)-i.val) * u 1^(i.val : ℤ)

def indexWeight (k : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*k+1)) : Kˣ :=
  Sum.elim (aWeight K k u) (bWeight K k u) ((abIndex k).symm j)

def wordWeight {k s : ℕ} (u : Fin 2 → Kˣ) (I : Fin s → Fin (2*k+1)) : Kˣ :=
  ∏ i, indexWeight K k u (I i)

@[simp] theorem indexWeight_a (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin k) :
    indexWeight K k u (abIndex k (.inl i))=aWeight K k u i := by
  simp [indexWeight]

@[simp] theorem indexWeight_b (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin (k+1)) :
    indexWeight K k u (abIndex k (.inr i))=bWeight K k u i := by
  simp [indexWeight]

theorem binaryBasis_diagonal (d : ℕ) (u : Fin 2 → Kˣ) (i : Fin (d+1)) :
    TauCeti.symPowerRep K 2 d (TauCeti.diagGL u) (binaryBasis K d i) =
      (bWeight K d u i : K) • binaryBasis K d i := by
  have h := (Pi.basisFun K (Fin 2)).map_symmetricPower_of_apply
    (TauCeti.stdRep K 2 (TauCeti.diagGL u)) (fun j => (u j : K))
    (TauCeti.stdRep_diagGL_apply_basisFun u) ((binaryIndex d).symm i)
  rw [TauCeti.symPowerRep, Representation.symmetricPower_apply]
  simp only [binaryBasis,Module.Basis.reindex_apply]
  change SymmetricPower.map (ι := Fin d) (TauCeti.stdRep K 2 (TauCeti.diagGL u))
      ((Pi.basisFun K (Fin 2)).symmetricPower d ((binaryIndex d).symm i)) = _
  rw [h]
  congr 1
  have hi : i.val≤d := by have := i.isLt; omega
  simp only [binaryIndex, Equiv.symm_trans_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, TauCeti.coe_symFinTwoEquiv_symm_apply,
    Multiset.map_add, Multiset.map_replicate, Multiset.prod_add, Multiset.prod_replicate,
    Fin.val_rev, bWeight, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [show d+1-(i.val+1)=d-i.val by omega,Nat.sub_sub_self hi,
    show (d : ℤ)-(i.val : ℤ)=((d-i.val : ℕ) : ℤ) by omega,
    zpow_natCast, zpow_natCast]

theorem binaryDualBasis_diagonal (d : ℕ) (u : Fin 2 → Kˣ) (i : Fin (d+1)) :
    (TauCeti.symPowerRep K 2 d).dual (TauCeti.diagGL u) ((binaryBasis K d).dualBasis i) =
      (aWeight K (d+1) u i : K) • (binaryBasis K d).dualBasis i := by
  apply (binaryBasis K d).ext
  intro j
  change (binaryBasis K d).dualBasis i
      (TauCeti.symPowerRep K 2 d (TauCeti.diagGL u)⁻¹ (binaryBasis K d j)) = _
  rw [← map_inv TauCeti.diagGL u, binaryBasis_diagonal, map_smul,
    LinearMap.smul_apply, Module.Basis.dualBasis_apply_self]
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl, smul_eq_mul, mul_one]
    congr 1
    simp only [bWeight, aWeight, Pi.inv_apply, inv_zpow, inv_inv, Nat.cast_add, Nat.cast_one]
    rw [show ((i.val : ℤ)+1-(d+1)) = -((d : ℤ)-i.val) by omega,
      zpow_neg, zpow_neg]
  · simp only [hij, Ne.symm hij, if_false, smul_eq_mul, mul_zero]

theorem modelBasis_diagonal (t : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*(t+1)+1)) :
    modelRepresentation K t (TauCeti.diagGL u) (modelBasis K t j) =
      (indexWeight K (t+1) u j : K) • modelBasis K t j := by
  obtain ⟨j,rfl⟩ := (abIndex (t+1)).surjective j
  cases j with
  | inl i =>
      have hi : abIndex (t+1) (.inl i)=oddPathMiddle i := by
        apply Fin.ext
        rfl
      rw [hi, modelBasis_middle]
      change ((TauCeti.symPowerRep K 2 t).dual (TauCeti.diagGL u)
          ((binaryBasis K t).dualBasis i),
        TauCeti.symPowerRep K 2 (t+1) (TauCeti.diagGL u) 0) = _
      rw [← hi, indexWeight_a]
      simp only [map_zero, Prod.smul_mk, smul_zero, binaryDualBasis_diagonal]
  | inr i =>
      have hb : modelBasis K t (abIndex (t+1) (.inr i)) =
          (0, binaryBasis K (t+1) i) := by
        change modelBasis K t ((TopInterlacing.abIndex (t+1)) (.inr i)) = _
        simp [modelBasis, Module.Basis.prod_apply]
      rw [hb, indexWeight_b]
      change ((TauCeti.symPowerRep K 2 t).dual (TauCeti.diagGL u) 0,
        TauCeti.symPowerRep K 2 (t+1) (TauCeti.diagGL u) (binaryBasis K (t+1) i)) = _
      simp only [map_zero, Prod.smul_mk, smul_zero, binaryBasis_diagonal]

theorem coordinateBasis_diagonal (t : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*(t+1)+1)) :
    coordinateRepresentation K t (TauCeti.diagGL u)
      (Pi.basisFun K (Fin (2*(t+1)+1)) j) =
      (indexWeight K (t+1) u j : K) • Pi.basisFun K (Fin (2*(t+1)+1)) j := by
  apply (coordinateEquiv K t).injective
  rw [coordinateRepresentation_equiv, map_smul]
  simpa only [coordinateEquiv, standardBasisEquiv_basisFun] using modelBasis_diagonal K t u j

variable [CharZero K]

theorem quotient_goodBasis_diagonal (t s : ℕ) (u : Fin 2 → Kˣ)
    (I : GoodOddIndex (t+1) s) :
    quotientRepresentation K t s (TauCeti.diagGL u) (oddExteriorBasis (t+1) s I) =
      (wordWeight K u I.val.val : K) • oddExteriorBasis (t+1) s I := by
  rw [oddExteriorBasis_apply, exteriorPluckerBasis_apply, quotientRepresentation_mk,
    exteriorPower.map_apply_ιMulti]
  have he : coordinateRepresentation K t (TauCeti.diagGL u) ∘
      (fun i => Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i)) =
    fun i => (indexWeight K (t+1) u (I.val.val i) : K) •
      Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i) := by
    funext i
    exact coordinateBasis_diagonal K t u _
  rw [he, AlternatingMap.map_smul_univ]
  have hw : (∏ i, (indexWeight K (t+1) u (I.val.val i) : K)) =
      (wordWeight K u I.val.val : K) := by
    exact (Units.coe_prod (fun i => indexWeight K (t+1) u (I.val.val i)) Finset.univ).symm
  rw [hw]
  exact Submodule.Quotient.mk_smul (R := K) (S := K)
    (p := exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*(t+1)+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*(t+1)+1)))) s)
    (wordWeight K u I.val.val : K)
    (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i)))

/-- In the exceptional case `k=0`, the only vector span is `Sym⁰ U`, on
which the induced action is the identity. -/
def naturalQuotientRepresentation : (k s : ℕ) →
    Representation K (GL (Fin 2) K) (OddExteriorQuotientDegree (K := K) k s)
  | 0, s => Representation.trivial K (GL (Fin 2) K) _
  | t+1, s => quotientRepresentation K t s

def naturalBigradedRepresentation : (k p q : ℕ) →
    Representation K (GL (Fin 2) K) (Bidegree.actualBigradedPiece (K := K) k p q)
  | 0, p, q => Representation.trivial K (GL (Fin 2) K) _
  | t+1, p, q => bigradedRepresentation K t p q

theorem indexWeight_zero (u : Fin 2 → Kˣ) (j : Fin 1) : indexWeight K 0 u j=1 := by
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  have hzero : abIndex 0 (.inr (0 : Fin 1)) = (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [← hzero, indexWeight_b]
  simp [bWeight]

theorem natural_goodBasis_diagonal (k s : ℕ) (u : Fin 2 → Kˣ)
    (I : GoodOddIndex k s) :
    naturalQuotientRepresentation K k s (TauCeti.diagGL u) (oddExteriorBasis k s I) =
      (wordWeight K u I.val.val : K) • oddExteriorBasis k s I := by
  cases k with
  | zero => simp [naturalQuotientRepresentation, wordWeight, indexWeight_zero]
  | succ t => exact quotient_goodBasis_diagonal K t s u I

def bigradedBasis (k p q : ℕ) :
    Module.Basis {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p} K
      (Bidegree.actualBigradedPiece (K := K) k p q) :=
  (PaperVerification.GradedComponentBasis.componentBasis
    (Bidegree.quotientAGrading k (p+q)) (oddExteriorBasis k (p+q)) Bidegree.goodADegree
    (BasisDegree.basis_mem_piece (oddExteriorBasis k (p+q)) Bidegree.goodADegree) p).map
      (LinearEquiv.ofEq _ _ (Bidegree.quotientAGrading_piece k (p+q) p))

theorem bigradedBasis_coe (k p q : ℕ)
    (I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p}) :
    (bigradedBasis K k p q I : OddExteriorQuotientDegree (K := K) k (p+q)) =
      oddExteriorBasis k (p+q) I.val := by
  simp only [bigradedBasis, PaperVerification.GradedComponentBasis.componentBasis,
    Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply,
    Function.comp_apply]

theorem bigradedBasis_diagonal (k p q : ℕ) (u : Fin 2 → Kˣ)
    (I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p}) :
    naturalBigradedRepresentation K k p q (TauCeti.diagGL u) (bigradedBasis K k p q I) =
      (wordWeight K u I.val.val.val : K) • bigradedBasis K k p q I := by
  apply Subtype.ext
  have h := natural_goodBasis_diagonal K k (p+q) u I.val
  rw [← bigradedBasis_coe K k p q I] at h
  cases k <;> exact h

/-- The character is the trace of the actual quotient action, evaluated in
the proved original good-monomial basis. -/
theorem bigraded_character (k p q : ℕ) (u : Fin 2 → Kˣ) :
    (naturalBigradedRepresentation K k p q).character (TauCeti.diagGL u) =
      ∑ I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p},
        (wordWeight K u I.val.val.val : K) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K (bigradedBasis K k p q),
    Matrix.trace]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, bigradedBasis_diagonal,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

end PaperVerification.AlternatingForms.SymmetricPencil
end
end
end TAF_LiteralSource_0441

section TAF_LiteralSource_0442
/- Original module: PaperVerification.AlternatingFormsTopWeightIdentity -/


/-!
# The complete torus-weight identity, with its determinant twist

The exterior quotient and the plethysm have different central characters
as representations of `GL₂`.  The explicit integer `determinantTwist`
corrects this difference.  Its disappearance on `SL₂` is used only in the
final representation theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

open SymmetricPencil

def finIndexSum (n : ℕ) : ℤ := ∑ i : Fin n, (i.val : ℤ)

theorem finIndexSum_succ (n : ℕ) : finIndexSum (n+1)=finIndexSum n+n := by
  rw [finIndexSum, Fin.sum_univ_castSucc]
  rfl

theorem twice_finIndexSum_succ (n : ℕ) :
    2*finIndexSum (n+1)=(n : ℤ)*(n+1) := by
  induction n with
  | zero => simp [finIndexSum]
  | succ n ih =>
      rw [finIndexSum_succ (n+1)]
      push_cast
      nlinarith

theorem finIndexSum_pair (p : ℕ) : finIndexSum p+finIndexSum (p+1)=(p : ℤ)^2 := by
  have h := twice_finIndexSum_succ p
  rw [finIndexSum_succ] at h ⊢
  nlinarith

def weakSum {p q : ℕ} (I : Interlacing p q) : ℤ :=
  ∑ j : Fin (2*p+1), ((toWeakWord I).val j).val

def aSum {p q : ℕ} (I : Interlacing p q) : ℤ := ∑ i : Fin p, (I.val.1 i).val
def cSum {p q : ℕ} (I : Interlacing p q) : ℤ := ∑ i : Fin (p+1), (I.val.2 i).val

theorem weakSum_add_square {p q : ℕ} (I : Interlacing p q) :
    weakSum I+(p : ℤ)^2=aSum I+cSum I := by
  have he : weakSum I =
      (∑ i : Fin p, (((I.val.1 i).val : ℤ)-i.val)) +
        (∑ i : Fin (p+1), (((I.val.2 i).val : ℤ)-i.val)) := by
    rw [weakSum, ← Equiv.sum_comp (abIndex p), Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      change (weakValue I (abIndex p (.inl i)) : ℤ)=_
      rw [weakValue_a, Nat.cast_sub (strictMonoFin_lower _ I.property.1 i)]
    · apply Finset.sum_congr rfl
      intro i hi
      change (weakValue I (abIndex p (.inr i)) : ℤ)=_
      rw [weakValue_c, Nat.cast_sub (strictMonoFin_lower _ I.property.2.1 i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at he
  change weakSum I=aSum I-finIndexSum p+(cSum I-finIndexSum (p+1)) at he
  have h := finIndexSum_pair p
  omega

/-- The integral determinant power required before restricting to `SL₂`. -/
def determinantTwist (p q : ℕ) : ℤ :=
  (p : ℤ)^2-finIndexSum (p+q+1)+((p : ℤ)+q)*q-(p : ℤ)*(p+q-1 : ℤ)

theorem determinantTwist_central (p q : ℕ) :
    2*determinantTwist p q =
      -(p : ℤ)*(p+q-1 : ℤ)+(q : ℤ)*(p+q)-q*(2*p+1) := by
  have hs := twice_finIndexSum_succ (p+q)
  unfold determinantTwist
  push_cast at hs ⊢
  nlinarith

theorem prod_zpow_sum {G ι : Type*} [CommGroup G] (S : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ i ∈ S, a^(f i) = a^(∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih, zpow_add]

def symmetricWeight {K : Type*} [Field K] (q r : ℕ) (u : Fin 2 → Kˣ)
    (S : Sym (Fin (q+1)) r) : Kˣ :=
  ((S : Multiset (Fin (q+1))).map
    (fun i => u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val))).prod

theorem symmetricWeight_interlacing {K : Type*} [Field K] {p q : ℕ}
    (u : Fin 2 → Kˣ) (I : Interlacing p q) :
    symmetricWeight q (2*p+1) u (interlacingSymEquiv p q I) =
      u 0^(weakSum I)*u 1^((q : ℤ)*(2*p+1)-weakSum I) := by
  change ((TauCeti.Sym.ofFn (toWeakWord I).val : Multiset (Fin (q+1))).map _).prod=_
  rw [TauCeti.Sym.coe_ofFn, Multiset.map_coe, Multiset.prod_coe,
    List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]
  rw [Finset.prod_mul_distrib,
    prod_zpow_sum, prod_zpow_sum]
  congr 1
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change ((2*p+1 : ℕ) : ℤ)*q-weakSum I=(q : ℤ)*(2*p+1)-weakSum I
  push_cast
  ring

theorem wordWeight_of_selectedAB {K : Type} [Field K] {k s : ℕ}
    (u : Fin 2 → Kˣ) (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (A : Finset (Fin k)) (B : Finset (Fin (k+1)))
    (hS : GoodPaths.selectedSet I=selectedAB A B) :
    wordWeight K u I = (∏ i ∈ A, aWeight K k u i)*(∏ i ∈ B, bWeight K k u i) := by
  have he : wordWeight K u I = ∏ j ∈ GoodPaths.selectedSet I, indexWeight K k u j := by
    rw [GoodPaths.selectedSet, Finset.prod_image]
    · rfl
    · intro a ha b hb hab
      exact hI.injective hab
  rw [he, hS, selectedAB, Finset.prod_map, Finset.prod_disjSum]
  change (∏ i ∈ A, indexWeight K k u (abIndex k (.inl i))) *
      (∏ i ∈ B, indexWeight K k u (abIndex k (.inr i))) = _
  simp only [indexWeight_a, indexWeight_b]

theorem pairWeight_formula {K : Type} [Field K] {k : ℕ} (u : Fin 2 → Kˣ)
    (A : Finset (Fin k)) (B : Finset (Fin (k+1))) :
    (∏ i ∈ A, aWeight K k u i)*(∏ i ∈ B, bWeight K k u i) =
      u 0^((∑ i ∈ A, (i.val : ℤ))-(A.card : ℤ)*(k-1)+(B.card : ℤ)*k-
        ∑ i ∈ B, (i.val : ℤ)) *
      u 1^((∑ i ∈ B, (i.val : ℤ))-∑ i ∈ A, (i.val : ℤ)) := by
  simp only [aWeight, bWeight, Finset.prod_mul_distrib, prod_zpow_sum]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 1
  · congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
    ring
  · congr 1
    rw [Finset.sum_neg_distrib]
    ring

theorem interlacing_wordWeight {K : Type} [Field K] {p q : ℕ}
    (u : Fin 2 → Kˣ) (I : Interlacing p q) :
    wordWeight K u (goodPairToTopWord (interlacingToGoodPair I)).val.val.val =
      (u 0*u 1)^(determinantTwist p q) *
        symmetricWeight q (2*p+1) u (interlacingSymEquiv p q I) := by
  let P := interlacingToGoodPair I
  let A := P.val.1
  let C := P.val.2
  let B := Cᶜ
  have ha : A.card=p := P.property.1
  have hc : C.card=p+1 := P.property.2.1
  have hb : B.card=q := by
    dsimp only [B]
    rw [Finset.card_compl, Fintype.card_fin, hc]
    omega
  have hsa : (∑ i ∈ A, (i.val : ℤ))=aSum I := by
    change (∑ i ∈ GoodPaths.selectedSet I.val.1, (i.val : ℤ))=aSum I
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      exact I.property.1.injective hij
  have hsc : (∑ i ∈ C, (i.val : ℤ))=cSum I := by
    change (∑ i ∈ GoodPaths.selectedSet I.val.2, (i.val : ℤ))=cSum I
    rw [GoodPaths.selectedSet, Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      exact I.property.2.1.injective hij
  have hsb : (∑ i ∈ B, (i.val : ℤ))=finIndexSum (p+q+1)-cSum I := by
    have h := C.sum_add_sum_compl (fun i => (i.val : ℤ))
    rw [hsc] at h
    change cSum I+(∑ i ∈ B, (i.val : ℤ))=finIndexSum (p+q+1) at h
    omega
  have hz := weakSum_add_square I
  have hs := twice_finIndexSum_succ (p+q)
  rw [wordWeight_of_selectedAB u _ (goodPairToTopWord P).val.val.property A B
      (goodPairToTopWord_selected P), pairWeight_formula, ha, hb, hsa, hsb,
    symmetricWeight_interlacing, mul_zpow, mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 1
  · congr 1
    unfold determinantTwist
    push_cast at *
    nlinarith
  · congr 1
    unfold determinantTwist
    push_cast at *
    nlinarith

/-- The full torus character identity on the exact actual good-word index
set, with the indispensable determinant factor retained. -/
theorem topWord_weight_sum {K : Type} [Field K] (p q : ℕ) (u : Fin 2 → Kˣ) :
    (∑ W : TopWord p q, (wordWeight K u W.val.val.val : K)) =
      (((u 0*u 1)^(determinantTwist p q) : Kˣ) : K) *
        ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  rw [← Equiv.sum_comp (topWordInterlacingEquiv p q).symm]
  have hw (I : Interlacing p q) :
      (topWordInterlacingEquiv p q).symm I=goodPairToTopWord (interlacingToGoodPair I) := rfl
  simp_rw [hw, interlacing_wordWeight, Units.val_mul]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (interlacingSymEquiv p q)
    (fun S : Sym (Fin (q+1)) (2*p+1) => (symmetricWeight q (2*p+1) u S : K))

end PaperVerification.AlternatingForms.TopInterlacing
end
end
end TAF_LiteralSource_0442

section TAF_LiteralSource_0443
/- Original module: PaperVerification.AlternatingFormsTopRepresentation -/


/-!
# The full representation statement of Corollary 5.2

The source representation acts on the literal bidegree of the quotient of
the exterior algebra by the two original quadrics.  Its construction,
including invariance of the ideal, is in `SymmetricPencilAction`.

The proof first identifies rational `GL₂` representations after the
necessary integral determinant twist.  It then restricts the actual
intertwining equivalence to `SL₂`, where that twist becomes trivial.
The case `p=q=0` is included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct
open Matrix

namespace PaperVerification.AlternatingForms.TopRepresentation

open SymmetricPencil TopInterlacing TauCeti

variable (K : Type) [Field K]

/-- The genuine iterated symmetric-power representation appearing in the
paper, before restriction from `GL₂` to `SL₂`. -/
def plethysmRepresentation (p q : ℕ) :
    Representation K (GL (Fin 2) K) (Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K))) :=
  (TauCeti.symPowerRep K 2 q).symmetricPower (2*p+1)

/-- Reversing the binary monomial basis makes its eigenvalues agree
directly with the interlacing coordinates.  This is a basis change within
the actual symmetric power. -/
def reversedBinaryBasis (q : ℕ) :
    Module.Basis (Fin (q+1)) K (Sym[K]^q (Fin 2 → K)) :=
  (binaryBasis K q).reindex (Fin.revPerm : Equiv.Perm (Fin (q+1)))

theorem reversedBinaryBasis_diagonal (q : ℕ) (u : Fin 2 → Kˣ) (i : Fin (q+1)) :
    TauCeti.symPowerRep K 2 q (TauCeti.diagGL u) (reversedBinaryBasis K q i) =
      ((u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val) : Kˣ) : K) •
        reversedBinaryBasis K q i := by
  simp only [reversedBinaryBasis,Module.Basis.reindex_apply,
    Fin.revPerm_symm,Fin.revPerm_apply]
  rw [binaryBasis_diagonal]
  congr 1
  have hi : i.val≤q := by have := i.isLt; omega
  have hrev : i.rev.val=q-i.val := by rw [Fin.val_rev]; omega
  simp only [bWeight,hrev]
  rw [Nat.cast_sub hi,show (q : ℤ)-((q : ℤ)-i.val)=i.val by ring]

theorem plethysm_character (p q : ℕ) (u : Fin 2 → Kˣ) :
    Representation.character (V := Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))
      (plethysmRepresentation K p q) (TauCeti.diagGL u) =
      ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  rw [Representation.character, plethysmRepresentation,
    Representation.symmetricPower_apply,
    Module.Basis.trace_map_symmetricPower_of_apply (reversedBinaryBasis K q)
      (TauCeti.symPowerRep K 2 q (TauCeti.diagGL u))
      (fun i => ((u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val) : Kˣ) : K)) (2*p+1)
      (reversedBinaryBasis_diagonal K q u)]
  apply Finset.sum_congr rfl
  intro S hS
  change _ = (Units.coeHom K)
    (((S : Multiset (Fin (q+1))).map
      (fun i => u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val))).prod)
  rw [map_multiset_prod, Multiset.map_map]
  rfl

/-- The `GL₂` target with the determinant power required by the central
character.  The untwisted assertion is only an `SL₂` assertion. -/
def twistedPlethysmRepresentation (p q : ℕ) :
    Representation K (GL (Fin 2) K)
      (K ⊗[K] (Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))) :=
  (TauCeti.detPowerRep K 2 (determinantTwist p q)).tprod
    (plethysmRepresentation K p q)

theorem twistedPlethysm_character (p q : ℕ) (u : Fin 2 → Kˣ) :
    (twistedPlethysmRepresentation K p q).character (TauCeti.diagGL u) =
      (((u 0*u 1)^(determinantTwist p q) : Kˣ) : K) *
        ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  have hc := congrFun
    (Representation.char_tensor (V := K)
      (W := Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))
      (TauCeti.detPowerRep K 2 (determinantTwist p q))
      (plethysmRepresentation K p q)) (TauCeti.diagGL u)
  rw [Pi.mul_apply,TauCeti.char_detPowerRep,TauCeti.det_diagGL,Fin.prod_univ_two,
    plethysm_character] at hc
  exact hc

variable [CharZero K]

set_option maxHeartbeats 800000 in
theorem top_character_eq_twisted (p q : ℕ) (u : Fin 2 → Kˣ) :
    (naturalBigradedRepresentation K (p+q) p q).character (TauCeti.diagGL u) =
      (twistedPlethysmRepresentation K p q).character (TauCeti.diagGL u) := by
  rw [bigraded_character, twistedPlethysm_character]
  exact topWord_weight_sum p q u

theorem naturalBigraded_rational (k p q : ℕ) :
    TauCeti.IsRationalRep (naturalBigradedRepresentation ℂ k p q) := by
  cases k with
  | zero =>
      letI : Module.Finite ℂ (Bidegree.actualBigradedPiece (K := ℂ) 0 p q) :=
        Module.Finite.of_basis (bigradedBasis ℂ 0 p q)
      apply TauCeti.isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
      intro f v
      change (fun _ : GL (Fin 2) ℂ => f v) ∈
        TauCeti.Matrix.GeneralLinearGroup.rationalFunctions ℂ 2
      exact (TauCeti.Matrix.GeneralLinearGroup.rationalFunctions ℂ 2).algebraMap_mem (f v)
  | succ t => exact RationalRepresentation.bigraded_rational t p q

theorem plethysm_rational (p q : ℕ) :
    TauCeti.IsRationalRep (plethysmRepresentation ℂ p q) :=
  ((TauCeti.isPolynomialRep_symPowerRep 2 q).symmetricPower (2*p+1)).isRationalRep

theorem twistedPlethysm_rational (p q : ℕ) :
    TauCeti.IsRationalRep (twistedPlethysmRepresentation ℂ p q) :=
  (TauCeti.isRationalRep_detPowerRep (determinantTwist p q)).tprod (plethysm_rational p q)

/-- The full auxiliary `GL₂` equivalence, with its essential determinant
twist.  It is obtained from proved rationality and equality of actual
characters, using rational complete reducibility over `ℂ`. -/
theorem top_gl2_equivalence (p q : ℕ) :
    Nonempty ((naturalBigradedRepresentation ℂ (p+q) p q).Equiv
      (twistedPlethysmRepresentation ℂ p q)) :=
  (naturalBigraded_rational (p+q) p q).nonempty_equiv_of_forall_character_diagGL_eq
    (twistedPlethysm_rational p q) (top_character_eq_twisted ℂ p q)

/-- Corollary 5.2's representation isomorphism for every `p,q ≥ 0`, on
the actual quotient piece `A_{p,q}` and the actual iterated symmetric
power.  No determinant twist remains after restriction to `SL₂`. -/
theorem paper_corollary_5_2_representation (p q : ℕ) :
    Nonempty
      (Representation.Equiv
        ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
        ((plethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL)) := by
  obtain ⟨e⟩ := top_gl2_equivalence p q
  let eSL :
      Representation.Equiv
      ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
      ((twistedPlethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL) :=
    .mk e.toLinearEquiv (fun g => e.isIntertwining' (Matrix.SpecialLinearGroup.toGL g))
  exact ⟨eSL.trans
    (TauCeti.tprodDetPowerSLEquiv ℂ 2 (determinantTwist p q) (plethysmRepresentation ℂ p q))⟩

/-- Both clauses of Corollary 5.2, with the complete parameter range. -/
theorem paper_corollary_5_2 (p q : ℕ) :
    Nonempty
      (Representation.Equiv
        ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
        ((plethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL)) ∧
      Module.finrank ℂ (Bidegree.actualBigradedPiece (K := ℂ) (p+q) p q) =
        (2*p+q+1).choose q :=
  ⟨paper_corollary_5_2_representation p q, actual_top_bigraded_dimension p q⟩

end PaperVerification.AlternatingForms.TopRepresentation
end
end
end TAF_LiteralSource_0443

section TAF_LiteralSource_0444
/- Original module: PaperVerification.AlternatingFormsCubicInjectivity -/


/-!
# The actual cubic multiplication map in every dimension at least six

The degree-three determinant in Theorem 1.1 is exactly choose(n,3)-2n.
Rank-nullity therefore proves injectivity of the original exterior
multiplication map, on the same principal open, for every n≥6.  There is
no restriction to an even dimension or to a six-dimensional subspace.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped Matrix

theorem twice_choose_two_int (n : ℕ) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      linear_combination ih

theorem paperMatrix_three_det (w : ℕ) :
    (PathDeterminant.paperMatrix (w+2) 3).det =
      (w+2 : ℤ)^3 - 2*(w+2 : ℤ)*((w+1).choose 2 : ℤ) + (w.choose 3 : ℤ) := by
  have hm : PathDeterminant.paperMatrix (w+2) 3 =
      !![(w+2 : ℤ), ((w+1).choose 2 : ℤ), (w.choose 3 : ℤ);
         1, (w+2 : ℤ), ((w+1).choose 2 : ℤ);
         0, 1, (w+2 : ℤ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PathDeterminant.paperMatrix, Nat.choose_one_right]
  rw [hm, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

theorem paperWalkCount_three (n : ℕ) (hn : 6 ≤ n) :
    StripWalks.paperWalkCount n 3 + 2*n = n.choose 3 := by
  obtain ⟨w, rfl⟩ : ∃ w, n=w+6 := ⟨n-6, by omega⟩
  have hd := PathDeterminant.paperWalkCount_determinant (w+6) 3 (by omega)
  rw [show w+6+2-2*3=w+2 by omega, paperMatrix_three_det] at hd
  have htwo := twice_choose_two_int w
  have hshift : ((w+6).choose 3 : ℤ) =
      (w.choose 3 : ℤ)+6*(w.choose 2 : ℤ)+15*(w : ℤ)+20 := by
    simp only [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_one]
    ring
  have hnext : ((w+1).choose 2 : ℤ) = (w.choose 2 : ℤ)+(w : ℤ) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
    ring
  have he : (StripWalks.paperWalkCount (w+6) 3 : ℤ)+2*(w+6 : ℤ) =
      ((w+6).choose 3 : ℤ) := by
    rw [hd, hnext, hshift]
    linear_combination -(w+5 : ℤ)*htwo
  exact_mod_cast he

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The cubic dimension equality implies injectivity of the actual map
`(u,v) ↦ f∧u+g∧v`; it is not an assumed presentation of the relation space. -/
theorem cubic_wedge_injective_of_hilbert (n : ℕ) (hn : 6 ≤ n)
    (hdim : Module.finrank K M=n) (f g : ⋀[K]^2 M)
    (h3 : Module.finrank K (ExteriorQuotientDegree f g 3) =
      StripWalks.paperWalkCount n 3) :
    Function.Injective (orbitExteriorRelationMap f g 1) := by
  have hr := exteriorQuotientDegree_finrank_add_orbitRange f g 1
  change Module.finrank K (ExteriorQuotientDegree f g 3) +
    Module.finrank K (LinearMap.range (orbitExteriorRelationMap f g 1)) =
      Module.finrank K (⋀[K]^3 M) at hr
  rw [exteriorPower.finrank_eq, hdim, h3] at hr
  have hc := paperWalkCount_three n hn
  have hnull := (orbitExteriorRelationMap f g 1).finrank_range_add_finrank_ker
  simp only [Module.finrank_prod, exteriorPower.finrank_eq, Nat.choose_one_right, hdim] at hnull
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- One genuine nonzero coefficient polynomial controls cubic injectivity
throughout the full space of alternating-form pairs, in every n≥6. -/
theorem generic_cubic_wedge_injective (n : ℕ) (hn : 6 ≤ n)
    (hdim : Module.finrank K M=n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q ≠ 0 →
            Function.Injective (orbitExteriorRelationMap
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 1) := by
  classical
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  exact cubic_wedge_injective_of_hilbert n hn hdim _ _
    (((h y hy).2.1 3 (by decide) (by omega)).1)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0444

section TAF_LiteralSource_0445
/- Original module: PaperVerification.TwoStepCentralLie -/


/-!
# The genuine central two-step Lie algebra and its universal maps

An alternating bilinear map `B : V × V → Z` defines the ordinary Lie
algebra `V ⊕ Z`, with `Z` central and `[v,w]=B(v,w)`.  No Lie superalgebra
convention is used.  The universal maps below go to Mathlib's actual
universal enveloping algebra, not to a separately defined surrogate.

This supporting source is a proof candidate until checked with its complete
dependency closure.  It does not assert Proposition 5.3 by itself.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.TwoStepCentralLie

variable {K V Z : Type*} [CommRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]

/-- The actual alternating bilinear bracket data. -/
structure Data where
  bilinear : V →ₗ[K] V →ₗ[K] Z
  alternating : ∀ v, bilinear v v=0

/-- The underlying vector space is the literal direct sum of generators
and central directions.  The data parameter keeps distinct Lie brackets
on this vector space distinct at the type level. -/
def LieSpace (D : Data (K := K) (V := V) (Z := Z)) := V × Z

variable (D : Data (K := K) (V := V) (Z := Z))

instance : AddCommGroup (LieSpace D) := inferInstanceAs (AddCommGroup (V × Z))
instance : Module K (LieSpace D) := inferInstanceAs (Module K (V × Z))

def coordinates : LieSpace D ≃ₗ[K] V × Z := LinearEquiv.refl K _

def generator : V →ₗ[K] LieSpace D := LinearMap.inl K V Z
def central : Z →ₗ[K] LieSpace D := LinearMap.inr K V Z

@[simp] theorem coordinates_generator (v : V) : coordinates D (generator D v)=(v,0) := rfl
@[simp] theorem coordinates_central (z : Z) : coordinates D (central D z)=(0,z) := rfl

instance : Bracket (LieSpace D) (LieSpace D) where
  bracket x y := ((0 : V),D.bilinear x.1 y.1)

@[simp] theorem bracket_coordinates (x y : LieSpace D) :
    coordinates D ⁅x,y⁆=((0 : V),D.bilinear x.1 y.1) := rfl

instance : LieRing (LieSpace D) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (LieSpace D))
  toBracket := inferInstanceAs (Bracket (LieSpace D) (LieSpace D))
  add_lie x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear (x.1+y.1) z.1) =
      ((0 : V),D.bilinear x.1 z.1)+((0 : V),D.bilinear y.1 z.1)
    simp only [map_add, LinearMap.add_apply, Prod.mk_add_mk, zero_add]
  lie_add x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 (y.1+z.1)) =
      ((0 : V),D.bilinear x.1 y.1)+((0 : V),D.bilinear x.1 z.1)
    simp only [map_add, Prod.mk_add_mk, zero_add]
  lie_self x := by
    change ((0 : V),D.bilinear x.1 x.1)=((0 : V),(0 : Z))
    rw [D.alternating]
  leibniz_lie x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 0)=((0 : V),D.bilinear 0 z.1)+((0 : V),D.bilinear y.1 0)
    simp

instance : LieAlgebra K (LieSpace D) where
  toModule := inferInstanceAs (Module K (LieSpace D))
  lie_smul t x y := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 (t • y.1))=t • ((0 : V),D.bilinear x.1 y.1)
    simp

@[simp] theorem generator_bracket (v w : V) :
    ⁅generator D v,generator D w⁆=central D (D.bilinear v w) := rfl

@[simp] theorem central_bracket (z : Z) (x : LieSpace D) : ⁅central D z,x⁆=0 := by
  change ((0 : V),D.bilinear 0 x.1)=((0 : V),(0 : Z))
  simp

@[simp] theorem bracket_central (x : LieSpace D) (z : Z) : ⁅x,central D z⁆=0 := by
  change ((0 : V),D.bilinear x.1 0)=((0 : V),(0 : Z))
  simp

/-- Every threefold bracket vanishes in the actual Lie algebra. -/
theorem bracket_bracket_eq_zero (x y z : LieSpace D) : ⁅⁅x,y⁆,z⁆=0 := by
  change ((0 : V),D.bilinear 0 z.1)=((0 : V),(0 : Z))
  simp

@[simp] theorem bracket_nested_eq_zero (x y z : LieSpace D) : ⁅x,⁅y,z⁆⁆=0 := by
  change ((0 : V),D.bilinear x.1 0)=((0 : V),(0 : Z))
  simp

theorem generator_injective : Function.Injective (generator D) := by
  intro v w h
  exact congrArg Prod.fst h

theorem central_injective : Function.Injective (central D) := by
  intro v w h
  exact congrArg Prod.snd h

@[simp] theorem generator_add_central (x : LieSpace D) :
    generator D x.1+central D x.2=x := by
  apply (coordinates D).injective
  change (x.1,0)+(0,x.2)=(x.1,x.2)
  simp

/-- The two homogeneous generator subspaces are literal linear-map ranges. -/
def degreeOne : Submodule K (LieSpace D) := LinearMap.range (generator D)
def degreeTwo : Submodule K (LieSpace D) := LinearMap.range (central D)

def degreeOneEquiv : V ≃ₗ[K] degreeOne D :=
  LinearEquiv.ofInjective (generator D) (generator_injective D)

def degreeTwoEquiv : Z ≃ₗ[K] degreeTwo D :=
  LinearEquiv.ofInjective (central D) (central_injective D)

theorem degree_subspaces_disjoint : Disjoint (degreeOne D) (degreeTwo D) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨v,rfl⟩ ⟨z,hz⟩
  have hv : v=0 := (congrArg Prod.fst hz).symm
  rw [hv,map_zero]

theorem degree_subspaces_span : degreeOne D ⊔ degreeTwo D=⊤ := by
  apply top_unique
  intro x hx
  rw [← generator_add_central D x]
  exact Submodule.add_mem_sup ⟨x.1,rfl⟩ ⟨x.2,rfl⟩

section FiniteDimensions

theorem finrank_degreeOne : Module.finrank K (degreeOne D)=Module.finrank K V :=
  (degreeOneEquiv D).finrank_eq.symm

theorem finrank_degreeTwo : Module.finrank K (degreeTwo D)=Module.finrank K Z :=
  (degreeTwoEquiv D).finrank_eq.symm

end FiniteDimensions

section UniversalProperty

variable {A : Type*} [Ring A] [Algebra K A]
attribute [local instance 100] LieRing.ofAssociativeRing

theorem lie_eq_zero_of_commute {x y : A} (h : Commute x y) : ⁅x,y⁆=0 :=
  sub_eq_zero.mpr h.eq

/-- A linear assignment of generators and central directions satisfying
the displayed commutator equations gives an actual Lie homomorphism. -/
def liftLie (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) :
    LieSpace D →ₗ⁅K⁆ A where
  toLinearMap := X.coprod C
  map_lie' {x y} := by
    change X 0+C (D.bilinear x.1 y.1)=⁅X x.1+C x.2,X y.1+C y.2⁆
    rw [map_zero,zero_add,add_lie,lie_add,lie_add,hXX,
      lie_eq_zero_of_commute (hXC x.1 y.2),
      lie_eq_zero_of_commute (hXC y.1 x.2).symm,
      lie_eq_zero_of_commute (hCC x.2 y.2)]
    simp

@[simp] theorem liftLie_generator (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (v : V) :
    liftLie D X C hXX hXC hCC (generator D v)=X v := by
  change X v+C 0=X v
  simp

@[simp] theorem liftLie_central (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (z : Z) :
    liftLie D X C hXX hXC hCC (central D z)=C z := by
  change X 0+C z=C z
  simp

/-- The standard enveloping-algebra map supplied by that Lie homomorphism. -/
def lift (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) :
    UniversalEnvelopingAlgebra K (LieSpace D) →ₐ[K] A :=
  UniversalEnvelopingAlgebra.lift K (liftLie D X C hXX hXC hCC)

@[simp] theorem lift_generator (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (v : V) :
    lift D X C hXX hXC hCC (UniversalEnvelopingAlgebra.ι K (generator D v))=X v := by
  rw [lift,UniversalEnvelopingAlgebra.lift_ι_apply,liftLie_generator]

@[simp] theorem lift_central (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (z : Z) :
    lift D X C hXX hXC hCC (UniversalEnvelopingAlgebra.ι K (central D z))=C z := by
  rw [lift,UniversalEnvelopingAlgebra.lift_ι_apply,liftLie_central]

end UniversalProperty
end PaperVerification.TwoStepCentralLie
end
end
end TAF_LiteralSource_0445

section TAF_LiteralSource_0446
/- Original module: PaperVerification.QuadraticCommutatorQuotient -/


/-!
# A commutator presentation and the genuine enveloping algebra

The source here is the actual quotient of the free associative algebra by
quadratic commutator relations in the kernel of a specified bracket map.
It is not defined as an enveloping algebra.  If its two commutator directions
are proved central, universal properties construct inverse algebra maps to
Mathlib's enveloping algebra of the actual central Lie algebra.

The centrality hypothesis is an intermediate algebraic condition; the
exterior cubic-injectivity argument must prove it before this theorem can
be used for Proposition 5.3.  The ordinary quadratic-dual annihilator
identification is also a separate required comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticCommutatorQuotient

open TwoStepCentralLie

variable {K ν Z : Type*} [Field K] [Fintype ν] [DecidableEq ν]
  [AddCommGroup Z] [Module K Z]

abbrev V := ν → K
abbrev PairCoordinates := (ν × ν) → K

variable (D : Data (K := K) (V := V (K := K) (ν := ν)) (Z := Z))

/-- The bracket on a formal linear combination of ordered pairs. -/
def bracketMap : PairCoordinates (K := K) (ν := ν) →ₗ[K] Z :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => D.bilinear (Pi.basisFun K ν p.1) (Pi.basisFun K ν p.2))

/-- Surjectivity of the actual bracket coefficients identifies the second
degree with brackets of the original degree-one generators. -/
theorem degreeTwo_eq_span_generator_brackets
    (hD : Function.Surjective (bracketMap D)) :
    degreeTwo D=Submodule.span K (Set.range (fun p : ν × ν =>
      ⁅generator D (Pi.basisFun K ν p.1),generator D (Pi.basisFun K ν p.2)⁆)) := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    obtain ⟨a,rfl⟩ := hD z
    rw [←(Pi.basisFun K (ν × ν)).sum_repr a]
    simp only [map_sum,map_smul]
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    rw [bracketMap,Module.Basis.constr_basis]
    exact Submodule.subset_span ⟨p,rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨p,rfl⟩
    exact ⟨D.bilinear (Pi.basisFun K ν p.1) (Pi.basisFun K ν p.2),rfl⟩

section Commutators

variable {A : Type*} [Ring A] [Algebra K A]

def commutator (x y : A) : A := x*y-y*x

def commutatorMap (X : ν → A) : PairCoordinates (K := K) (ν := ν) →ₗ[K] A :=
  (Pi.basisFun K (ν × ν)).constr K (fun p => commutator (X p.1) (X p.2))

@[simp] theorem commutatorMap_basis (X : ν → A) (p : ν × ν) :
    commutatorMap X (Pi.basisFun K (ν × ν) p)=commutator (X p.1) (X p.2) := by
  simp [commutatorMap]

def commutatorBilinear (X : V (K := K) (ν := ν) →ₗ[K] A) :
    V (K := K) (ν := ν) →ₗ[K] V (K := K) (ν := ν) →ₗ[K] A :=
  LinearMap.mk₂ K (fun v w => commutator (X v) (X w))
    (by intros; simp only [commutator,map_add,add_mul,mul_add]; abel)
    (by intros; simp only [commutator,map_smul,smul_mul_assoc,mul_smul_comm,smul_sub])
    (by intros; simp only [commutator,map_add,add_mul,mul_add]; abel)
    (by intros; simp only [commutator,map_smul,smul_mul_assoc,mul_smul_comm,smul_sub])

@[simp] theorem commutatorBilinear_apply (X : V (K := K) (ν := ν) →ₗ[K] A) (v w) :
    commutatorBilinear X v w=commutator (X v) (X w) := rfl

end Commutators

/-- Relations are imposed in the free associative algebra itself. -/
inductive Relation : FreeAlgebra K ν → FreeAlgebra K ν → Prop
  | kernel (a : PairCoordinates (K := K) (ν := ν)) (ha : bracketMap D a=0) :
      Relation (commutatorMap (FreeAlgebra.ι K) a) 0

abbrev Algebra := RingQuot (Relation D)

def quotientMap : FreeAlgebra K ν →ₐ[K] Algebra D := RingQuot.mkAlgHom K (Relation D)

def X (i : ν) : Algebra D := quotientMap D (FreeAlgebra.ι K i)

def XLinear : V (K := K) (ν := ν) →ₗ[K] Algebra D :=
  (Pi.basisFun K ν).constr K (X D)

@[simp] theorem XLinear_basis (i : ν) : XLinear D (Pi.basisFun K ν i)=X D i := by
  simp [XLinear]

theorem quotientMap_commutator (a : PairCoordinates (K := K) (ν := ν)) :
    quotientMap D (commutatorMap (FreeAlgebra.ι K) a)=commutatorMap (X D) a := by
  have h : (quotientMap D).toLinearMap.comp (commutatorMap (FreeAlgebra.ι K))=
      commutatorMap (X D) := by
    apply (Pi.basisFun K (ν × ν)).ext
    intro p
    rw [LinearMap.comp_apply,commutatorMap_basis,commutatorMap_basis]
    simp only [AlgHom.toLinearMap_apply,commutator,map_sub,map_mul,X]
  exact LinearMap.congr_fun h a

theorem bracket_ker_le_commutator_ker :
    LinearMap.ker (bracketMap D) ≤ LinearMap.ker (commutatorMap (X D)) := by
  intro a ha
  change bracketMap D a=0 at ha
  change commutatorMap (X D) a=0
  rw [← quotientMap_commutator]
  exact (RingQuot.mkAlgHom_rel K (Relation.kernel a ha)).trans (map_zero _)

variable (hD : Function.Surjective (bracketMap D))

/-- The central-coordinate map is obtained by factoring the actual
commutator map through its proved kernel inclusion. -/
def centralMap : Z →ₗ[K] Algebra D :=
  (bracketMap D).liftOfSurjective hD
    ⟨commutatorMap (X D),bracket_ker_le_commutator_ker D⟩

@[simp] theorem centralMap_bracketMap (a : PairCoordinates (K := K) (ν := ν)) :
    centralMap D hD (bracketMap D a)=commutatorMap (X D) a := by
  simp [centralMap]

theorem X_commutator (i j : ν) :
    commutator (X D i) (X D j)=
      centralMap D hD (D.bilinear (Pi.basisFun K ν i) (Pi.basisFun K ν j)) := by
  have h := centralMap_bracketMap D hD (Pi.basisFun K (ν × ν) (i,j))
  rw [commutatorMap_basis] at h
  simpa only [bracketMap,Module.Basis.constr_basis] using h.symm

theorem XLinear_commutator (v w : V (K := K) (ν := ν)) :
    commutator (XLinear D v) (XLinear D w)=centralMap D hD (D.bilinear v w) := by
  have h : commutatorBilinear (XLinear D)=D.bilinear.compr₂ (centralMap D hD) := by
    apply (Pi.basisFun K ν).ext
    intro i
    apply (Pi.basisFun K ν).ext
    intro j
    simpa only [commutatorBilinear_apply,XLinear_basis,LinearMap.compr₂_apply]
      using X_commutator D hD i j
  exact LinearMap.congr_fun (LinearMap.congr_fun h v) w

/-- Commuting with each original generator implies commuting with every
element of the actual free-algebra quotient. -/
theorem commute_all_of_generators (z : Algebra D) (hz : ∀ i, Commute (X D i) z) :
    ∀ a : Algebra D, Commute a z := by
  intro a
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (Relation D) a
  change Commute (quotientMap D a) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
      rw [AlgHom.commutes]
      exact Algebra.commutes c z
  | grade1 i => exact hz i
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb
  | add a b ha hb => simpa only [map_add] using ha.add_left hb

section EnvelopingComparison

attribute [local instance 100] LieRing.ofAssociativeRing

variable (hcentral : ∀ i z, Commute (X D i) (centralMap D hD z))

def toEnvelopingFree : FreeAlgebra K ν →ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  FreeAlgebra.lift K (fun i =>
    UniversalEnvelopingAlgebra.ι K (generator D (Pi.basisFun K ν i)))

theorem toEnvelopingFree_commutator (a : PairCoordinates (K := K) (ν := ν)) :
    toEnvelopingFree D (commutatorMap (FreeAlgebra.ι K) a)=
      UniversalEnvelopingAlgebra.ι K (central D (bracketMap D a)) := by
  have h : (toEnvelopingFree D).toLinearMap.comp (commutatorMap (FreeAlgebra.ι K))=
      (UniversalEnvelopingAlgebra.ι K).toLinearMap.comp
        ((central D).comp (bracketMap D)) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,commutatorMap_basis,commutator,map_sub,map_mul,
      toEnvelopingFree,FreeAlgebra.lift_ι_apply,bracketMap,Module.Basis.constr_basis]
    exact ((UniversalEnvelopingAlgebra.ι K).map_lie
      (generator D (Pi.basisFun K ν i)) (generator D (Pi.basisFun K ν j))).symm
  exact LinearMap.congr_fun h a

def toEnveloping : Algebra D →ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  RingQuot.liftAlgHom K ⟨toEnvelopingFree D,by
    intro a b h
    cases h with
    | kernel a ha =>
        rw [toEnvelopingFree_commutator,ha,map_zero,map_zero,map_zero]⟩

@[simp] theorem toEnveloping_X (i : ν) :
    toEnveloping D (X D i)=UniversalEnvelopingAlgebra.ι K
      (generator D (Pi.basisFun K ν i)) := by
  simp [toEnveloping,X,quotientMap,RingQuot.liftAlgHom_mkAlgHom_apply,toEnvelopingFree]

theorem toEnveloping_central (z : Z) :
    toEnveloping D (centralMap D hD z)=UniversalEnvelopingAlgebra.ι K (central D z) := by
  obtain ⟨a,rfl⟩ := hD z
  rw [centralMap_bracketMap,← quotientMap_commutator]
  rw [toEnveloping,quotientMap,RingQuot.liftAlgHom_mkAlgHom_apply,
    toEnvelopingFree_commutator]

def fromEnveloping : UniversalEnvelopingAlgebra K (LieSpace D) →ₐ[K] Algebra D :=
  TwoStepCentralLie.lift D (XLinear D) (centralMap D hD)
    (XLinear_commutator D hD)
    (fun v z => commute_all_of_generators D _ (fun i => hcentral i z) (XLinear D v))
    (fun z z' => commute_all_of_generators D _ (fun i => hcentral i z') (centralMap D hD z))

@[simp] theorem fromEnveloping_generator (v : V (K := K) (ν := ν)) :
    fromEnveloping D hD hcentral (UniversalEnvelopingAlgebra.ι K (generator D v))=
      XLinear D v := by
  unfold fromEnveloping
  exact TwoStepCentralLie.lift_generator D _ _ _ _ _ v

@[simp] theorem fromEnveloping_central (z : Z) :
    fromEnveloping D hD hcentral (UniversalEnvelopingAlgebra.ι K (central D z))=
      centralMap D hD z := by
  unfold fromEnveloping
  exact TwoStepCentralLie.lift_central D _ _ _ _ _ z

theorem from_toEnveloping :
    (fromEnveloping D hD hcentral).comp (toEnveloping D)=AlgHom.id K (Algebra D) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  change fromEnveloping D hD hcentral (toEnveloping D (X D i))=X D i
  rw [toEnveloping_X,fromEnveloping_generator,XLinear_basis]

theorem to_fromEnveloping :
    (toEnveloping D).comp (fromEnveloping D hD hcentral)=
      AlgHom.id K (UniversalEnvelopingAlgebra K (LieSpace D)) := by
  have hX (v : V (K := K) (ν := ν)) :
      toEnveloping D (XLinear D v)=UniversalEnvelopingAlgebra.ι K (generator D v) := by
    have h : (toEnveloping D).toLinearMap.comp (XLinear D)=
        (UniversalEnvelopingAlgebra.ι K).toLinearMap.comp (generator D) := by
      apply (Pi.basisFun K ν).ext
      intro i
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,LieHom.coe_toLinearMap,
      XLinear_basis,toEnveloping_X]
    exact LinearMap.congr_fun h v
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  rw [← generator_add_central D x]
  simp only [LieHom.coe_comp,AlgHom.coe_toLieHom,Function.comp_apply,
    AlgHom.comp_apply,AlgHom.id_apply,map_add,fromEnveloping_generator,
    fromEnveloping_central,hX,toEnveloping_central]

/-- The two explicitly constructed maps are inverses.  This theorem uses
the actual free quotient and Mathlib's ordinary universal enveloping algebra. -/
def envelopingEquiv : Algebra D ≃ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  AlgEquiv.ofAlgHom (toEnveloping D) (fromEnveloping D hD hcentral)
    (to_fromEnveloping D hD hcentral) (from_toEnveloping D hD hcentral)

end EnvelopingComparison
end PaperVerification.QuadraticCommutatorQuotient
end
end
end TAF_LiteralSource_0446

section TAF_LiteralSource_0447
/- Original module: PaperVerification.AlternatingFormsCubicJacobi -/


/-!
# The actual cubic wedge map forces central commutators

This is the linear-algebra step in Proposition 5.3.  The hypothesis is
injectivity of the literal map `(u,v) ↦ f∧u+g∧v`, rather than a statement
about an abstract expected Hilbert function.  The conclusion applies to
any associative algebra whose generator commutators have coefficients
given by the actual two exterior forms.  Jacobi and separation by linear
functionals prove that the two commutator directions are central.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.CubicJacobi

variable {K : Type*} [Field K] {ν : Type*}

def coefficient (i j k : ν) : (⋀[K]^3 (ν → K)) →ₗ[K] K :=
  exteriorPower.alternatingMapToDual K (ν → K) 3
    ![LinearMap.proj i, LinearMap.proj j, LinearMap.proj k]

theorem coefficient_word (i j k : ν) (w : Fin 3 → ν → K) :
    coefficient i j k (exteriorPower.ιMulti K 3 w) =
      w 0 i*w 1 j*w 2 k-w 0 i*w 1 k*w 2 j-
        w 0 j*w 1 i*w 2 k+w 0 j*w 1 k*w 2 i+
        w 0 k*w 1 i*w 2 j-w 0 k*w 1 j*w 2 i := by
  simp only [coefficient, exteriorPower.alternatingMapToDual_apply_ιMulti,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, LinearMap.proj_apply]

theorem wedge_word_one (w : Fin 2 → ν → K) (v : ν → K) :
    exteriorPower.wedge K (ν → K) 2 1 (exteriorPower.ιMulti K 2 w)
      ((exteriorPower.oneEquiv K (ν → K)).symm v) =
        exteriorPower.ιMulti K 3 ![w 0,w 1,v] := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Function.comp_def, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, mul_one]
  rw [mul_assoc]

/-- The six-term coefficient formula is obtained from the actual exterior
pairing, with every sign fixed by that pairing. -/
theorem coefficient_wedge_one (f : ⋀[K]^2 (ν → K)) (v : ν → K) (i j k : ν) :
    coefficient i j k
      (exteriorPower.wedge K (ν → K) 2 1 f
        ((exteriorPower.oneEquiv K (ν → K)).symm v)) =
      orbitExteriorCoefficientMatrix f i j*v k-
        orbitExteriorCoefficientMatrix f i k*v j+
        orbitExteriorCoefficientMatrix f j k*v i := by
  have h : coefficient (K := K) i j k ∘ₗ
        (exteriorPower.wedge K (ν → K) 2 1).flip
          ((exteriorPower.oneEquiv K (ν → K)).symm v) =
      v k • orbitExteriorCoefficient i j-v j • orbitExteriorCoefficient i k+
        v i • orbitExteriorCoefficient j k := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, wedge_word_one, coefficient_word,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      orbitExteriorCoefficient_word, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,Matrix.cons_val_succ,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    ring
  have he := LinearMap.congr_fun h f
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    orbitExteriorCoefficientMatrix, mul_comm] using he

variable [Fintype ν] [DecidableEq ν]

theorem eq_zero_of_coefficients (z : ⋀[K]^3 (ν → K))
    (hz : ∀ i j k, coefficient (K := K) i j k z=0) : z=0 := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  let b := Pi.basisFun K ν
  apply (b.exteriorPower 3).repr.injective
  ext s
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have hd : exteriorPower.ιMultiDual K 3 b s =
      coefficient (K := K) (a 0) (a 1) (a 2) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, coefficient_word,
      Matrix.det_fin_three, Matrix.of_apply, b, Module.Basis.coord_apply,
      Pi.basisFun_repr, a]
  rw [hd]
  exact hz _ _ _

def vectorRelationMap (f g : ⋀[K]^2 (ν → K)) :
    ((ν → K) × (ν → K)) →ₗ[K] (⋀[K]^3 (ν → K)) :=
  (orbitExteriorRelationMap f g 1).comp
    (((exteriorPower.oneEquiv K (ν → K)).symm).prodCongr
      (exteriorPower.oneEquiv K (ν → K)).symm).toLinearMap

theorem vectorRelationMap_injective (f g : ⋀[K]^2 (ν → K))
    (h : Function.Injective (orbitExteriorRelationMap f g 1)) :
    Function.Injective (vectorRelationMap f g) :=
  h.comp (((exteriorPower.oneEquiv K (ν → K)).symm).prodCongr
    (exteriorPower.oneEquiv K (ν → K)).symm).injective

theorem coefficient_vectorRelationMap (f g : ⋀[K]^2 (ν → K))
    (v w : ν → K) (i j k : ν) :
    coefficient i j k (vectorRelationMap f g (v,w)) =
      orbitExteriorCoefficientMatrix f i j*v k-
        orbitExteriorCoefficientMatrix f i k*v j+
        orbitExteriorCoefficientMatrix f j k*v i+
      (orbitExteriorCoefficientMatrix g i j*w k-
        orbitExteriorCoefficientMatrix g i k*w j+
        orbitExteriorCoefficientMatrix g j k*w i) := by
  simp only [vectorRelationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, orbitExteriorRelationMap, LinearMap.coprod_apply,
    map_add, coefficient_wedge_one]

section Centrality

variable {A : Type*} [Ring A] [Algebra K A]

def commutator (x y : A) : A := x*y-y*x

theorem commutator_jacobi (x y z : A) :
    commutator x (commutator y z)-commutator y (commutator x z)+
      commutator z (commutator x y)=0 := by
  unfold commutator
  noncomm_ring

theorem commutator_linear (x z₁ z₂ : A) (a b : K) :
    commutator x (a • z₁+b • z₂) =
      a • commutator x z₁+b • commutator x z₂ := by
  simp only [commutator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_sub]
  abel

/-- Injectivity of the actual cubic wedge map proves the two commutator
directions commute with every original generator, in any associative
algebra satisfying the displayed quadratic commutator equations. -/
theorem generator_commutes_of_cubic_injective
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (X : ν → A) (z₁ z₂ : A)
    (hcomm : ∀ i j, commutator (X i) (X j) =
      orbitExteriorCoefficientMatrix f i j • z₁+
        orbitExteriorCoefficientMatrix g i j • z₂) :
    ∀ i, Commute (X i) z₁ ∧ Commute (X i) z₂ := by
  have hdual (φ : Module.Dual K A) :
      (fun i => φ (commutator (X i) z₁))=0 ∧
        (fun i => φ (commutator (X i) z₂))=0 := by
    let v : ν → K := fun i => φ (commutator (X i) z₁)
    let w : ν → K := fun i => φ (commutator (X i) z₂)
    have hz : vectorRelationMap f g (v,w)=0 := by
      apply eq_zero_of_coefficients
      intro i j k
      rw [coefficient_vectorRelationMap]
      have hj := commutator_jacobi (X i) (X j) (X k)
      rw [hcomm j k, hcomm i k, hcomm i j, commutator_linear,
        commutator_linear, commutator_linear] at hj
      have hh := congrArg φ hj
      simp only [map_add, map_sub, map_smul, map_zero, smul_eq_mul] at hh
      change _=0
      dsimp [v,w]
      linear_combination hh
    have he : (v,w)=(0,0) := vectorRelationMap_injective f g hinj
      (hz.trans (map_zero _).symm)
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  intro i
  constructor
  · apply sub_eq_zero.mp
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    exact congrFun (hdual φ).1 i
  · apply sub_eq_zero.mp
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    exact congrFun (hdual φ).2 i

end Centrality
end PaperVerification.AlternatingForms.CubicJacobi
end
end
end TAF_LiteralSource_0447

section TAF_LiteralSource_0448
/- Original module: PaperVerification.AlternatingFormsTwoStepDual -/


/-!
# The two actual exterior forms define the central enveloping comparison

Injectivity of the literal cubic wedge map proves both independence of the
two bracket directions and their centrality in the actual associative
commutator quotient.  The comparison with Mathlib's ordinary enveloping
algebra therefore has no centrality or rank hypothesis left over.

The additional comparison with the conventional tensor-annihilator
definition of a quadratic dual is required separately; this module does
not label the commutator presentation as that dual by definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TwoStepDual

open TwoStepCentralLie
open QuadraticCommutatorQuotient

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

def formBilinear (f : ⋀[K]^2 (ν → K)) :
    (ν → K) →ₗ[K] (ν → K) →ₗ[K] K :=
  Matrix.toBilin' (orbitExteriorCoefficientMatrix f)

theorem formBilinear_self (f : ⋀[K]^2 (ν → K)) (v : ν → K) : formBilinear f v v=0 := by
  have h : formBilinear f v v= -formBilinear f v v := by
    simp only [formBilinear,Matrix.toBilin'_apply]
    calc
      (∑ i,∑ j,v i*orbitExteriorCoefficientMatrix f i j*v j)=
          ∑ i,∑ j,v j*orbitExteriorCoefficientMatrix f j i*v i := Finset.sum_comm
      _ = -(∑ i,∑ j,v i*orbitExteriorCoefficientMatrix f i j*v j) := by
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [orbitExteriorCoefficientMatrix_skew f i j]
        ring
  have htwo : (2 : K)*formBilinear f v v=0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

set_option maxHeartbeats 800000 in
@[simp] theorem formBilinear_basis (f : ⋀[K]^2 (ν → K)) (i j : ν) :
    formBilinear f (Pi.basisFun K ν i) (Pi.basisFun K ν j)=
      orbitExteriorCoefficientMatrix f i j := by
  rw [formBilinear,Pi.basisFun_apply,Pi.basisFun_apply]
  exact Matrix.toBilin'_single _ i j

def bracketData (f g : ⋀[K]^2 (ν → K)) :
    TwoStepCentralLie.Data (K := K) (V := ν → K) (Z := K × K) where
  bilinear := LinearMap.mk₂ K (fun v w => (formBilinear f v w,formBilinear g v w))
    (by intros; simp only [map_add,LinearMap.add_apply,Prod.mk_add_mk])
    (by intros; simp only [map_smul,LinearMap.smul_apply,Prod.smul_mk])
    (by intros; simp only [map_add,Prod.mk_add_mk])
    (by intros; simp only [map_smul,Prod.smul_mk])
  alternating v := by
    change (formBilinear f v v,formBilinear g v v)=(0,0)
    rw [formBilinear_self,formBilinear_self]

@[simp] theorem bracketData_basis (f g : ⋀[K]^2 (ν → K)) (i j : ν) :
    (bracketData f g).bilinear (Pi.basisFun K ν i) (Pi.basisFun K ν j)=
      (orbitExteriorCoefficientMatrix f i j,orbitExteriorCoefficientMatrix g i j) := by
  change (formBilinear f (Pi.basisFun K ν i) (Pi.basisFun K ν j),
    formBilinear g (Pi.basisFun K ν i) (Pi.basisFun K ν j))=_
  rw [formBilinear_basis,formBilinear_basis]

theorem pair_linear_expansion {A : Type*} [AddCommGroup A] [Module K A]
    (L : (K × K) →ₗ[K] A) (a b : K) :
    L (a,b)=a • L (1,0)+b • L (0,1) := by
  have h : (a,b)=a • (1,0)+b • (0,1) := by simp
  rw [h,map_add,map_smul,map_smul]

variable [Nonempty ν]

/-- Cubic injectivity already forces independence of the two original
forms.  No separate generic independence hypothesis is needed. -/
theorem scalar_relation_trivial (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (a b : K) (hab : a • f+b • g=0) : a=0 ∧ b=0 := by
  let i : ν := Classical.choice inferInstance
  let v : ⋀[K]^1 (ν → K) :=
    (exteriorPower.oneEquiv K (ν → K)).symm (Pi.basisFun K ν i)
  have hv : (orbitExteriorRelationMap f g 1) (a • v,b • v)=0 := by
    have h := congrArg (fun F : ⋀[K]^2 (ν → K) => exteriorPower.wedge K (ν → K) 2 1 F v) hab
    simpa only [orbitExteriorRelationMap,LinearMap.coprod_apply,map_add,map_smul,
      LinearMap.add_apply,LinearMap.smul_apply,map_zero,LinearMap.zero_apply] using h
  have he : (a • v,b • v)=(0,0) := hinj (hv.trans (map_zero _).symm)
  have ha := congrArg
    (fun x : ⋀[K]^1 (ν → K) => (exteriorPower.oneEquiv K (ν → K) x) i)
    (congrArg Prod.fst he)
  have hb := congrArg
    (fun x : ⋀[K]^1 (ν → K) => (exteriorPower.oneEquiv K (ν → K) x) i)
    (congrArg Prod.snd he)
  constructor
  · simpa [v,Pi.basisFun_apply] using ha
  · simpa [v,Pi.basisFun_apply] using hb

/-- The actual ordered-pair bracket map has both central directions in
its range, as a consequence of the cubic map alone. -/
theorem bracketMap_surjective (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    Function.Surjective (bracketMap (bracketData f g)) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro φ hφ
  change (bracketMap (bracketData f g)).dualMap φ=0 at hφ
  change φ=0
  let a := φ (1,0)
  let b := φ (0,1)
  have hrel : a • f+b • g=0 := by
    apply orbitExteriorCoefficientMatrix_injective
    funext i j
    have he := LinearMap.congr_fun hφ (Pi.basisFun K (ν × ν) (i,j))
    simp only [LinearMap.dualMap_apply,LinearMap.comp_apply,
      bracketMap,Module.Basis.constr_basis,bracketData_basis,LinearMap.zero_apply] at he
    rw [pair_linear_expansion] at he
    change _=orbitExteriorCoefficient i j 0
    simp only [orbitExteriorCoefficientMatrix,map_add,map_smul,map_zero,smul_eq_mul]
    dsimp only [a,b]
    simpa only [orbitExteriorCoefficientMatrix,smul_eq_mul,mul_comm] using he
  obtain ⟨ha,hb⟩ := scalar_relation_trivial f g hinj a b hrel
  apply LinearMap.ext
  rintro ⟨x,y⟩
  rw [pair_linear_expansion]
  change x • a+y • b=0
  rw [ha,hb,smul_zero,smul_zero,add_zero]

def actualCentralMap (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    (K × K) →ₗ[K] QuadraticCommutatorQuotient.Algebra (bracketData f g) :=
  centralMap (bracketData f g) (bracketMap_surjective f g hinj)

/-- Jacobi proves centrality in the actual free-associative quotient,
using the coefficients of the two literal exterior forms. -/
theorem actual_generator_central (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    ∀ i z, Commute (QuadraticCommutatorQuotient.X (bracketData f g) i)
      (actualCentralMap f g hinj z) := by
  let D := bracketData f g
  let C := actualCentralMap f g hinj
  have hc := CubicJacobi.generator_commutes_of_cubic_injective f g hinj
    (QuadraticCommutatorQuotient.X D) (C (1,0)) (C (0,1)) (by
      intro i j
      change commutator (QuadraticCommutatorQuotient.X D i)
        (QuadraticCommutatorQuotient.X D j)=_
      rw [X_commutator D (bracketMap_surjective f g hinj),bracketData_basis]
      exact pair_linear_expansion C _ _)
  intro i z
  rcases z with ⟨a,b⟩
  change Commute (QuadraticCommutatorQuotient.X D i) (C (a,b))
  rw [pair_linear_expansion]
  change _*_=_*_
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,(hc i).1.eq,(hc i).2.eq]

/-- For the original forms with injective cubic wedge map, the
commutator presentation is the actual enveloping algebra of the literal
two-step Lie algebra.  Centrality and bracket surjectivity have been
proved and are not hypotheses of this result. -/
def actualCommutatorEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    QuadraticCommutatorQuotient.Algebra (bracketData f g) ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (bracketData f g)) :=
  envelopingEquiv (bracketData f g) (bracketMap_surjective f g hinj)
    (actual_generator_central f g hinj)

end PaperVerification.AlternatingForms.TwoStepDual
end
end
end TAF_LiteralSource_0448

section TAF_LiteralSource_0449
/- Original module: PaperVerification.AlternatingFormsQuadraticDual -/


/-!
# The ordinary quadratic dual and its commutator presentation

Ordered-pair coordinates are the tensor-square coordinates in the standard
basis.  The original quadratic relation space is the inverse image of
`span{f,g}` under the literal wedge map.  The dual relation space is its
ordinary coefficient-pairing annihilator.  This file compares that
annihilator with the kernel-commutator presentation; neither algebra is
defined to make the comparison automatic.

The source remains a proof candidate until its complete closure is checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

open QuadraticCommutatorQuotient TwoStepDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

abbrev Coordinates := (ν × ν) → K

/-- The coefficient space is rigorously identified with the actual
tensor square, through its usual tensor-product basis. -/
def tensorCoordinates : ((ν → K) ⊗[K] (ν → K)) ≃ₗ[K]
    Coordinates (K := K) (ν := ν) :=
  ((Pi.basisFun K ν).tensorProduct (Pi.basisFun K ν)).equivFun

@[simp] theorem tensorCoordinates_tmul (v w : ν → K) (i j : ν) :
    tensorCoordinates (v ⊗ₜ[K] w) (i,j)=v i*w j := by
  simp [tensorCoordinates,Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply,mul_comm]

def wordMap : Coordinates (K := K) (ν := ν) →ₗ[K] FreeAlgebra K ν :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => FreeAlgebra.ι K p.1*FreeAlgebra.ι K p.2)

def wedgeMap : Coordinates (K := K) (ν := ν) →ₗ[K] (⋀[K]^2 (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => exteriorPower.ιMulti K 2 ![Pi.basisFun K ν p.1,Pi.basisFun K ν p.2])

def dotDual : Coordinates (K := K) (ν := ν) →ₗ[K]
    Module.Dual K (Coordinates (K := K) (ν := ν)) :=
  (Pi.basisFun K (ν × ν)).constr K (fun p => LinearMap.proj p)

def coefficientDual : Coordinates (K := K) (ν := ν) →ₗ[K]
    Module.Dual K (⋀[K]^2 (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => orbitExteriorCoefficient p.1 p.2)

def skew : Coordinates (K := K) (ν := ν) →ₗ[K] Coordinates (K := K) (ν := ν) where
  toFun a p := a p-a (p.2,p.1)
  map_add' a b := by ext p; simp; ring
  map_smul' c a := by ext p; simp; ring

@[simp] theorem skew_apply (a : Coordinates (K := K) (ν := ν)) (i j : ν) :
    skew a (i,j)=a (i,j)-a (j,i) := rfl

@[simp] theorem dotDual_basis_right (a : Coordinates (K := K) (ν := ν)) (p : ν × ν) :
    dotDual a (Pi.basisFun K (ν × ν) p)=a p := by
  simp [dotDual,Module.Basis.constr_apply_fintype,Pi.basisFun_equivFun,
    Pi.basisFun_apply,Pi.single_apply]

@[simp] theorem wedgeMap_basis (i j : ν) :
    wedgeMap (Pi.basisFun K (ν × ν) (i,j))=
      exteriorPower.ιMulti K 2 ![Pi.basisFun K ν i,Pi.basisFun K ν j] := by
  simp [wedgeMap]

theorem wedgeMap_surjective : Function.Surjective (wedgeMap (K := K) (ν := ν)) := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  let b := (Pi.basisFun K ν).exteriorPower 2
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro z ⟨s,rfl⟩
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  refine ⟨Pi.basisFun K (ν × ν) (a 0,a 1),?_⟩
  rw [wedgeMap_basis]
  change exteriorPower.ιMulti K 2 ![Pi.basisFun K ν (a 0),Pi.basisFun K ν (a 1)]=_
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedgeMap_symmetric (i j : ν) :
    wedgeMap (Pi.basisFun K (ν × ν) (i,j)+Pi.basisFun K (ν × ν) (j,i))=0 := by
  apply orbitExteriorCoefficientMatrix_injective
  funext u v
  simp only [map_add,wedgeMap_basis,orbitExteriorCoefficientMatrix,
    orbitExteriorCoefficient_word,map_zero,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- This identity is the actual adjoint relation between the exterior
wedge map and antisymmetrization of tensor coefficients. -/
theorem coefficientDual_wedge (a t : Coordinates (K := K) (ν := ν)) :
    coefficientDual a (wedgeMap t)=dotDual (skew a) t := by
  have H : (LinearMap.lcomp K _ (wedgeMap (K := K) (ν := ν))).comp coefficientDual=
      dotDual.comp skew := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨u,v⟩
    simp only [LinearMap.comp_apply,LinearMap.lcomp_apply,coefficientDual,
      Module.Basis.constr_basis,wedgeMap_basis,orbitExteriorCoefficient_word,
      dotDual_basis_right,skew_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq]
    by_cases hiu : i=u <;> by_cases hiv : i=v <;>
      by_cases hju : j=u <;> by_cases hjv : j=v <;>
      simp [hiu,hiv,hju,hjv,eq_comm]
  exact LinearMap.congr_fun (LinearMap.congr_fun H a) t

theorem bracketMap_eq_coefficientDual (f g : ⋀[K]^2 (ν → K))
    (a : Coordinates (K := K) (ν := ν)) :
    bracketMap (bracketData f g) a=(coefficientDual a f,coefficientDual a g) := by
  have h : bracketMap (bracketData f g)=
      ((LinearMap.applyₗ (R := K) (M₂ := K) f).comp coefficientDual).prod
        ((LinearMap.applyₗ (R := K) (M₂ := K) g).comp coefficientDual) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    simp only [bracketMap,coefficientDual,Module.Basis.constr_basis,bracketData_basis,
      LinearMap.prod_apply,LinearMap.comp_apply,Function.prod_apply,
      LinearMap.coe_comp,Function.comp_apply,LinearMap.applyₗ_apply_apply,
      orbitExteriorCoefficientMatrix]
  exact LinearMap.congr_fun h a

/-- The original quadratic relations, before taking their annihilator. -/
def originalRelations (f g : ⋀[K]^2 (ν → K)) :
    Submodule K (Coordinates (K := K) (ν := ν)) :=
  (Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K)))).comap wedgeMap

theorem wedge_zero_degree (f : ⋀[K]^2 (ν → K)) :
    exteriorPower.wedge K (ν → K) 2 0 f=
      (exteriorPower.zeroEquiv K (ν → K)).toLinearMap.smulRight f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  apply Subtype.ext
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.smulRight_apply,
    LinearEquiv.coe_coe,exteriorPower.zeroEquiv_ιMulti,one_smul,
    exteriorPower.wedge,DirectSum.gMulLHom_apply_apply,SetLike.coe_gMul,
    exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_zero_apply,mul_one]

/-- In degree two, the actual generated exterior ideal contains exactly
the linear span of the original forms. -/
theorem exterior_degree_two_relations (f g : ⋀[K]^2 (ν → K)) :
    exteriorDegreeRelations f g 2=Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) := by
  apply le_antisymm ?_ (quadraticSpan_le_exteriorDegreeRelations f g)
  change exteriorDegreeRelations f g (2+0) ≤ _
  rw [exteriorDegreeRelations_eq_images]
  apply sup_le
  · rintro z ⟨v,rfl⟩
    rw [wedge_zero_degree]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rintro z ⟨v,rfl⟩
    rw [wedge_zero_degree]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The original tensor relation space is the kernel of projection to
the actual degree-two quotient, not a postulated presentation. -/
theorem originalRelations_eq_actualKernel (f g : ⋀[K]^2 (ν → K)) :
    originalRelations f g=
      LinearMap.ker ((exteriorDegreeRelations f g 2).mkQ.comp wedgeMap) := by
  rw [LinearMap.ker_comp,Submodule.ker_mkQ,exterior_degree_two_relations]
  rfl

/-- The ordinary tensor coefficient pairing defines the dual relation
space.  It includes the annihilator of the exterior square relations and
of the two specified forms. -/
def dualRelations (f g : ⋀[K]^2 (ν → K)) :
    Submodule K (Coordinates (K := K) (ν := ν)) :=
  (originalRelations f g).dualAnnihilator.comap dotDual

theorem mem_dualRelations (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔ ∀ t,
      wedgeMap t∈Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) → dotDual q t=0 := by
  simp only [dualRelations,Submodule.mem_comap,Submodule.mem_dualAnnihilator,
    originalRelations]

theorem skew_mem_dualRelations (f g : ⋀[K]^2 (ν → K))
    (a : Coordinates (K := K) (ν := ν))
    (ha : bracketMap (bracketData f g) a=0) : skew a∈dualRelations f g := by
  rw [bracketMap_eq_coefficientDual] at ha
  have hf : coefficientDual a f=0 := congrArg Prod.fst ha
  have hg : coefficientDual a g=0 := congrArg Prod.snd ha
  apply (mem_dualRelations f g _).mpr
  intro t ht
  rw [← coefficientDual_wedge]
  have hker : Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) ≤
      LinearMap.ker (coefficientDual a) := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact hf
    · exact hg
  exact hker ht

/-- Every ordinary dual quadratic relation is an actual commutator
coefficient vector whose bracket direction vanishes. -/
theorem mem_dualRelations_iff (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔ ∃ a, bracketMap (bracketData f g) a=0 ∧ skew a=q := by
  constructor
  · intro hq
    have hq' := (mem_dualRelations f g q).mp hq
    have hskew (i j : ν) : q (i,j)+q (j,i)=0 := by
      have h := hq' (Pi.basisFun K (ν × ν) (i,j)+Pi.basisFun K (ν × ν) (j,i))
        (by rw [wedgeMap_symmetric]; exact Submodule.zero_mem _)
      simpa only [map_add,dotDual_basis_right] using h
    let a : Coordinates (K := K) (ν := ν) := (2 : K)⁻¹ • q
    have haq : skew a=q := by
      funext p
      rcases p with ⟨i,j⟩
      change (2 : K)⁻¹*q (i,j)-(2 : K)⁻¹*q (j,i)=q (i,j)
      have hs := hskew i j
      field_simp
      linear_combination -hs
    refine ⟨a,?_,haq⟩
    rw [bracketMap_eq_coefficientDual]
    apply Prod.ext
    · obtain ⟨t,ht⟩ := wedgeMap_surjective (K := K) (ν := ν) f
      have h := hq' t (by rw [ht]; exact Submodule.subset_span (by simp))
      rw [← haq,← coefficientDual_wedge,ht] at h
      exact h
    · obtain ⟨t,ht⟩ := wedgeMap_surjective (K := K) (ν := ν) g
      have h := hq' t (by rw [ht]; exact Submodule.subset_span (by simp))
      rw [← haq,← coefficientDual_wedge,ht] at h
      exact h
  · rintro ⟨a,ha,rfl⟩
    exact skew_mem_dualRelations f g a ha

theorem wordMap_skew (a : Coordinates (K := K) (ν := ν)) :
    wordMap (skew a)=commutatorMap (FreeAlgebra.ι K) a := by
  have h : (wordMap (K := K) (ν := ν)).comp (skew (K := K) (ν := ν))=
      commutatorMap (FreeAlgebra.ι K : ν → FreeAlgebra K ν) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    have hs : skew (Pi.basisFun K (ν × ν) (i,j))=
        Pi.basisFun K (ν × ν) (i,j)-Pi.basisFun K (ν × ν) (j,i) := by
      funext p
      rcases p with ⟨u,v⟩
      simp [skew_apply,Pi.basisFun_apply,Pi.single_apply,Prod.mk.injEq,and_comm]
    rw [LinearMap.comp_apply,hs,map_sub]
    simp only [wordMap,commutatorMap,Module.Basis.constr_basis,
      QuadraticCommutatorQuotient.commutator]
  exact LinearMap.congr_fun h a

inductive DualRelation (f g : ⋀[K]^2 (ν → K)) : FreeAlgebra K ν → FreeAlgebra K ν → Prop
  | annihilator (q : Coordinates (K := K) (ν := ν)) (hq : q∈dualRelations f g) :
      DualRelation f g (wordMap q) 0

/-- The ordinary quadratic dual in tensor-square coordinates. -/
abbrev QuadraticDual (f g : ⋀[K]^2 (ν → K)) := RingQuot (DualRelation f g)

theorem definingRelations_eq (f g : ⋀[K]^2 (ν → K)) :
    QuadraticCommutatorQuotient.Relation (bracketData f g)=DualRelation f g := by
  funext x y
  apply propext
  constructor
  · intro h
    cases h with
    | kernel a ha =>
        rw [← wordMap_skew]
        exact DualRelation.annihilator (skew a) (skew_mem_dualRelations f g a ha)
  · intro h
    cases h with
    | annihilator q hq =>
        obtain ⟨a,ha,rfl⟩ := (mem_dualRelations_iff f g q).mp hq
        rw [wordMap_skew]
        exact QuadraticCommutatorQuotient.Relation.kernel a ha

def quotientRelEquiv
    {r s : FreeAlgebra K ν → FreeAlgebra K ν → Prop} (h : r=s) :
    RingQuot r ≃ₐ[K] RingQuot s := by
  cases h
  exact AlgEquiv.refl

theorem quotientRelEquiv_mk
    {r s : FreeAlgebra K ν → FreeAlgebra K ν → Prop} (h : r=s)
    (x : FreeAlgebra K ν) :
    quotientRelEquiv h (RingQuot.mkAlgHom K r x)=RingQuot.mkAlgHom K s x := by
  cases h
  rfl

def commutatorEquiv (f g : ⋀[K]^2 (ν → K)) :
    QuadraticDual f g ≃ₐ[K] QuadraticCommutatorQuotient.Algebra (bracketData f g) :=
  quotientRelEquiv (definingRelations_eq f g).symm

@[simp] theorem commutatorEquiv_mk (f g : ⋀[K]^2 (ν → K))
    (x : FreeAlgebra K ν) :
    commutatorEquiv f g (RingQuot.mkAlgHom K (DualRelation f g) x)=
      QuadraticCommutatorQuotient.quotientMap (bracketData f g) x :=
  quotientRelEquiv_mk (definingRelations_eq f g).symm x

variable [Nonempty ν]

/-- The conventional annihilator-defined quadratic dual is isomorphic to
the genuine enveloping algebra of the actual ordinary two-step Lie
algebra, whenever the actual cubic wedge map is injective. -/
def quadraticDualEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    QuadraticDual f g ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (bracketData f g)) :=
  (commutatorEquiv f g).trans (actualCommutatorEnvelopingEquiv f g hinj)

@[simp] theorem quadraticDualEnvelopingEquiv_generator
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) (i : ν) :
    quadraticDualEnvelopingEquiv f g hinj
      (RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i))=
      UniversalEnvelopingAlgebra.ι K
        (TwoStepCentralLie.generator (bracketData f g) (Pi.basisFun K ν i)) := by
  rw [quadraticDualEnvelopingEquiv,AlgEquiv.trans_apply,commutatorEquiv_mk]
  exact QuadraticCommutatorQuotient.toEnveloping_X (bracketData f g) i

end PaperVerification.AlternatingForms.QuadraticDual
end
end
end TAF_LiteralSource_0449

section TAF_LiteralSource_0450
/- Original module: PaperVerification.AlternatingFormsQuadraticDualTensor -/


/-!
# The coordinate quadratic dual is the literal tensor-algebra quotient

The algebra used in the dual calculation is presented in free-generator
coordinates.  This file supplies the actual comparison with Mathlib's
tensor algebra on the actual dual of the original generator vector space.  The two maps descend the
genuine tensor/free-algebra equivalence, and their inverse laws are proved
on the original quotient maps.  The displayed quadratic tensors become
the literal products of the two tensor-algebra inclusions.

This is a candidate until checked with its complete closure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.AlternatingForms.QuadraticDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

/-- Coordinates in the tensor square of the actual dual space. -/
def dualTensorCoordinates :
    (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) ≃ₗ[K]
      Coordinates (K := K) (ν := ν) :=
  ((Pi.basisFun K ν).dualBasis.tensorProduct (Pi.basisFun K ν).dualBasis).equivFun

/-- The coefficient pairing is exactly the canonical tensor evaluation pairing. -/
theorem actual_tensor_pairing (q t : Coordinates (K := K) (ν := ν)) :
    TensorProduct.dualDistrib K (ν → K) (ν → K)
      (dualTensorCoordinates.symm q) (tensorCoordinates.symm t)=dotDual q t := by
  have h :
      (LinearMap.lcomp K K (tensorCoordinates (K := K) (ν := ν)).symm.toLinearMap).comp
        ((TensorProduct.dualDistrib K (ν → K) (ν → K)).comp
          (dualTensorCoordinates (K := K) (ν := ν)).symm.toLinearMap)=dotDual := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨u,v⟩
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, dotDual_basis_right]
    simp [LinearMap.lcomp_apply,dualTensorCoordinates,tensorCoordinates,
      Module.Basis.equivFun_symm_apply,Module.Basis.tensorProduct_apply,
      Pi.basisFun_apply,Pi.single_apply,TensorProduct.dualDistrib_apply,
      Module.Basis.dualBasis_apply,dotDual_basis_right,Prod.mk.injEq]
    split_ifs <;> simp_all
  exact LinearMap.congr_fun (LinearMap.congr_fun h q) t

/-- No self-duality convention is assumed: these are precisely the tensors
in the actual dual tensor square annihilating the original quadratic relations. -/
theorem mem_dualRelations_actual (f g : ⋀[K]^2 (ν → K))
    (q : Coordinates (K := K) (ν := ν)) :
    q∈dualRelations f g ↔
      ∀ z : (ν → K) ⊗[K] (ν → K),
        wedgeMap (tensorCoordinates z)∈
          Submodule.span K ({f,g} : Set (⋀[K]^2 (ν → K))) →
        TensorProduct.dualDistrib K (ν → K) (ν → K) (dualTensorCoordinates.symm q) z=0 := by
  rw [mem_dualRelations]
  constructor
  · intro h z hz
    have hh := h (tensorCoordinates z) hz
    rw [←actual_tensor_pairing] at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro h t ht
    have hh := h (tensorCoordinates.symm t) (by
      simpa only [LinearEquiv.apply_symm_apply] using ht)
    rw [actual_tensor_pairing] at hh
    exact hh

def tensorFreeEquiv : TensorAlgebra K (Module.Dual K (ν → K)) ≃ₐ[K] FreeAlgebra K ν :=
  TensorAlgebra.equivFreeAlgebra (Pi.basisFun K ν).dualBasis

def tensorWordMap : Coordinates (K := K) (ν := ν) →ₗ[K]
    TensorAlgebra K (Module.Dual K (ν → K)) :=
  (Pi.basisFun K (ν × ν)).constr K (fun p =>
    TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis p.1)*
      TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis p.2))

@[simp] theorem tensorWordMap_basis (i j : ν) :
    tensorWordMap (Pi.basisFun K (ν × ν) (i,j))=
      TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)*
        TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis j) := by
  simp only [tensorWordMap,Module.Basis.constr_basis]

def tensorQuadraticInclusion :
    (Module.Dual K (ν → K) ⊗[K] Module.Dual K (ν → K)) →ₗ[K]
      TensorAlgebra K (Module.Dual K (ν → K)) :=
  TensorProduct.lift ((LinearMap.mul K (TensorAlgebra K (Module.Dual K (ν → K)))).compl₁₂
    (TensorAlgebra.ι K) (TensorAlgebra.ι K))

/-- The quadratic relation element is the genuine degree-two tensor inclusion. -/
theorem tensorWordMap_eq_actual_inclusion :
    tensorWordMap (K := K) (ν := ν)=
      tensorQuadraticInclusion.comp dualTensorCoordinates.symm.toLinearMap := by
  apply (Pi.basisFun K (ν × ν)).ext
  rintro ⟨i,j⟩
  rw [LinearMap.comp_apply,tensorWordMap_basis]
  simp [tensorQuadraticInclusion,dualTensorCoordinates,
    Module.Basis.equivFun_symm_apply,Module.Basis.tensorProduct_apply,
    Pi.basisFun_apply,Pi.single_apply]

theorem tensorFreeEquiv_word (q : Coordinates (K := K) (ν := ν)) :
    tensorFreeEquiv (tensorWordMap q)=wordMap q := by
  have h : (tensorFreeEquiv (K := K) (ν := ν)).toLinearMap.comp tensorWordMap=wordMap := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    change tensorFreeEquiv (tensorWordMap (Pi.basisFun K (ν × ν) (i,j)))=
      wordMap (Pi.basisFun K (ν × ν) (i,j))
    rw [tensorWordMap_basis,map_mul]
    simp only [tensorFreeEquiv,TensorAlgebra.equivFreeAlgebra_ι_apply,
      wordMap,Module.Basis.constr_basis]
  exact LinearMap.congr_fun h q

theorem tensorFreeEquiv_symm_word (q : Coordinates (K := K) (ν := ν)) :
    tensorFreeEquiv.symm (wordMap q)=tensorWordMap q := by
  apply tensorFreeEquiv.injective
  rw [AlgEquiv.apply_symm_apply,tensorFreeEquiv_word]

inductive TensorDualRelation (f g : ⋀[K]^2 (ν → K)) :
    TensorAlgebra K (Module.Dual K (ν → K)) →
      TensorAlgebra K (Module.Dual K (ν → K)) → Prop
  | annihilator (q : Coordinates (K := K) (ν := ν)) (hq : q∈dualRelations f g) :
      TensorDualRelation f g (tensorWordMap q) 0

/-- The ordinary tensor-algebra quotient by the actual annihilator relations. -/
abbrev TensorQuadraticDual (f g : ⋀[K]^2 (ν → K)) := RingQuot (TensorDualRelation f g)

def tensorDualToCoordinates (f g : ⋀[K]^2 (ν → K)) :
    TensorQuadraticDual f g →ₐ[K] QuadraticDual f g :=
  RingQuot.liftAlgHom K
    ⟨(RingQuot.mkAlgHom K (DualRelation f g)).comp tensorFreeEquiv.toAlgHom,by
      intro x y h
      cases h with
      | annihilator q hq =>
          simp only [AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,tensorFreeEquiv_word,map_zero]
          exact (RingQuot.mkAlgHom_rel K (DualRelation.annihilator q hq)).trans (map_zero _)⟩

def coordinatesToTensorDual (f g : ⋀[K]^2 (ν → K)) :
    QuadraticDual f g →ₐ[K] TensorQuadraticDual f g :=
  RingQuot.liftAlgHom K
    ⟨(RingQuot.mkAlgHom K (TensorDualRelation f g)).comp tensorFreeEquiv.symm.toAlgHom,by
      intro x y h
      cases h with
      | annihilator q hq =>
          simp only [AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,tensorFreeEquiv_symm_word,map_zero]
          exact (RingQuot.mkAlgHom_rel K
            (TensorDualRelation.annihilator q hq)).trans (map_zero _)⟩

@[simp] theorem tensorDualToCoordinates_mk (f g : ⋀[K]^2 (ν → K))
    (x : TensorAlgebra K (Module.Dual K (ν → K))) :
    tensorDualToCoordinates f g (RingQuot.mkAlgHom K (TensorDualRelation f g) x)=
      RingQuot.mkAlgHom K (DualRelation f g) (tensorFreeEquiv x) := by
  simp only [tensorDualToCoordinates,RingQuot.liftAlgHom_mkAlgHom_apply,
    AlgHom.comp_apply,AlgEquiv.toAlgHom_apply]

@[simp] theorem coordinatesToTensorDual_mk (f g : ⋀[K]^2 (ν → K))
    (x : FreeAlgebra K ν) :
    coordinatesToTensorDual f g (RingQuot.mkAlgHom K (DualRelation f g) x)=
      RingQuot.mkAlgHom K (TensorDualRelation f g) (tensorFreeEquiv.symm x) := by
  simp only [coordinatesToTensorDual,RingQuot.liftAlgHom_mkAlgHom_apply,
    AlgHom.comp_apply,AlgEquiv.toAlgHom_apply]

/-- A proved equivalence of the actual quotients, preserving the original generators. -/
def tensorDualEquiv (f g : ⋀[K]^2 (ν → K)) :
    TensorQuadraticDual f g ≃ₐ[K] QuadraticDual f g :=
  AlgEquiv.ofAlgHom (tensorDualToCoordinates f g) (coordinatesToTensorDual f g)
    (by
      apply RingQuot.ringQuot_ext'
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply,coordinatesToTensorDual_mk,tensorDualToCoordinates_mk,
        AlgEquiv.apply_symm_apply,AlgHom.id_apply])
    (by
      apply RingQuot.ringQuot_ext'
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply,tensorDualToCoordinates_mk,coordinatesToTensorDual_mk,
        AlgEquiv.symm_apply_apply,AlgHom.id_apply])

@[simp] theorem tensorDualEquiv_generator (f g : ⋀[K]^2 (ν → K)) (i : ν) :
    tensorDualEquiv f g
      (RingQuot.mkAlgHom K (TensorDualRelation f g)
        (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=
      RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i) := by
  change tensorDualToCoordinates f g
    (RingQuot.mkAlgHom K (TensorDualRelation f g)
      (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=_
  rw [tensorDualToCoordinates_mk,tensorFreeEquiv,
    TensorAlgebra.equivFreeAlgebra_ι_apply]

variable [Nonempty ν]

def tensorQuadraticDualEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    TensorQuadraticDual f g ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (TwoStepDual.bracketData f g)) :=
  (tensorDualEquiv f g).trans (quadraticDualEnvelopingEquiv f g hinj)

end PaperVerification.AlternatingForms.QuadraticDual
end
end
end TAF_LiteralSource_0450

section TAF_LiteralSource_0451
/- Original module: PaperVerification.EigenBasisGrading -/


/-!
# Coordinate support of a diagonal eigenspace

If a linear endomorphism acts diagonally on a genuine basis, with distinct
eigenvalues assigned to the natural-number degrees, its eigenspaces are
exactly the subspaces supported in those degrees.  The index set of the
basis can be infinite; no finite-dimensionality assumption is introduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.EigenBasisGrading

open AlternatingForms.BasisDegree

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : Module.Basis I K V) (δ : I → ℕ) (eigenScalar : ℕ → K)
  (F : V →ₗ[K] V) (hF : ∀ i,F (B i)=eigenScalar (δ i) • B i)

include hF in
theorem coordinate_map (i : I) (x : V) :
    B.repr (F x) i=eigenScalar (δ i)*B.repr x i := by
  have h : (B.coord i).comp F=eigenScalar (δ i) • B.coord i := by
    apply B.ext
    intro j
    simp only [LinearMap.comp_apply,hF,map_smul,LinearMap.smul_apply,
      Module.Basis.coord_apply,Module.Basis.repr_self]
    classical
    by_cases hji : j=i
    · subst j
      simp
    · simp [Finsupp.single_apply,hji,Ne.symm hji]
  exact LinearMap.congr_fun h x

include hF in
theorem eigenvector_iff_degree_support (hEigen : Function.Injective eigenScalar)
    (d : ℕ) (x : V) :
    F x=eigenScalar d • x ↔ x∈piece B δ d := by
  rw [mem_piece]
  constructor
  · intro hx i hi
    by_contra hc
    have he := congrArg (fun y => B.repr y i) hx
    rw [coordinate_map B δ eigenScalar F hF,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
    exact hi (hEigen (mul_right_cancel₀ hc he))
  · intro hx
    apply B.repr.injective
    apply Finsupp.ext
    intro i
    rw [coordinate_map B δ eigenScalar F hF,map_smul,Finsupp.smul_apply,smul_eq_mul]
    by_cases hi : δ i=d
    · rw [hi]
    · rw [hx i hi,mul_zero,mul_zero]

include hF in
theorem eigenspace_eq_piece (hEigen : Function.Injective eigenScalar) (d : ℕ) :
    Module.End.eigenspace F (eigenScalar d)=piece B δ d := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  exact eigenvector_iff_degree_support B δ eigenScalar F hF hEigen d x

theorem span_degree_eq_piece (d : ℕ) :
    Submodule.span K (Set.range (fun i : {i // δ i=d} => B i))=piece B δ d := by
  rw [piece_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

/-- Restricting a genuine basis gives a basis of every exact degree piece. -/
def degreeBasis (d : ℕ) : Module.Basis {i // δ i=d} K (piece B δ d) :=
  (Module.Basis.span (B.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_eq_piece B δ d))

theorem finrank_piece (d : ℕ) :
    Module.finrank K (piece B δ d)=Nat.card {i // δ i=d} :=
  Module.finrank_eq_nat_card_basis (degreeBasis B δ d)

end PaperVerification.EigenBasisGrading
end
end
end TAF_LiteralSource_0451

section TAF_LiteralSource_0452
/- Original module: TauCeti.Data.Finsupp.Multiset -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Multisets of exponent vectors

Mathlib's `Finsupp.toMultiset` sends an exponent vector `e : α →₀ ℕ` to the multiset in which
each `a` occurs `e a` times. Its cardinality is the total degree of `e`. This file also computes it
on exponent vectors built from unit steps `Finsupp.single a 1`: adding one unit step conses its
index, and a sum of unit steps along a finite family is the multiset of values of the family.

## Main results

* `Finsupp.card_toMultiset_eq_degree`: `card (toMultiset e) = e.degree`.
* `Finsupp.toMultiset_add_single_one`: `toMultiset (e + single a 1) = a ::ₘ toMultiset e`.
* `Finsupp.toMultiset_sum_single_one`: `toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p`.

The same unit steps summed along a list, with coefficients in any additive commutative monoid
with one, count the occurrences of each letter; in characteristic zero these counts determine a
constant list.

* `List.sum_map_single_one_apply`: `(l.map fun k ↦ single k 1).sum a = l.count a`.
* `List.eq_replicate_of_sum_map_single_one_eq`: a list whose letter counts are those of `m`
  copies of `i` is `m` copies of `i`.
-/

public section

namespace Finsupp

/-- The number of letters of the monomial with exponent vector `d` is its total degree. This is
not a `simp` lemma: `Finsupp.card_toMultiset` already rewrites the left-hand side to
`d.sum fun _ => id`, so tagging it would leave it out of simp-normal form. -/
theorem card_toMultiset_eq_degree {α : Type*} (d : α →₀ ℕ) :
    Multiset.card d.toMultiset = d.degree := by
  rw [card_toMultiset, degree_apply]
  rfl

/-- Adding one unit step at `a` to an exponent vector conses `a` onto its multiset. -/
theorem toMultiset_add_single_one {α : Type*} (e : α →₀ ℕ) (a : α) :
    toMultiset (e + single a 1) = a ::ₘ toMultiset e := by
  simp [toMultiset_add, add_comm]

/-- The multiset of a sum of unit steps along a family `p` indexed by a finset `s` is the
multiset of the values of `p` on `s`. -/
theorem toMultiset_sum_single_one {α ι : Type*} (s : Finset ι) (p : ι → α) :
    toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p := by
  simpa [toMultiset_sum, one_nsmul, Finset.sum_map_val] using
    Multiset.sum_map_singleton (s.val.map p)

end Finsupp

namespace List

variable {α R : Type*} [AddCommMonoidWithOne R]

/-- Summing the unit steps `single k 1` along a list counts the occurrences of each letter. -/
theorem sum_map_single_one_apply [DecidableEq α] (l : List α) (a : α) :
    (l.map fun k => Finsupp.single k (1 : R)).sum a = l.count a := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [map_cons, sum_cons, Finsupp.add_apply, ih, count_cons, Finsupp.single_apply]
    split_ifs <;> simp_all [add_comm]

/-- In characteristic zero, a list whose sum of unit steps is `m` times the unit step at `i` is
the list of `m` copies of `i`. -/
theorem eq_replicate_of_sum_map_single_one_eq [CharZero R] {l : List α} {i : α} {m : ℕ}
    (hl : (l.map fun k => Finsupp.single k (1 : R)).sum = Finsupp.single i (m : R)) :
    l = replicate m i := by
  classical
  have hcount : ∀ j, (l.count j : R) = Finsupp.single i (m : R) j := fun j => by
    rw [← hl, sum_map_single_one_apply]
  have hall : ∀ j ∈ l, j = i := by
    intro j hj
    by_contra hji
    have := hcount j
    rw [Finsupp.single_eq_of_ne hji, Nat.cast_eq_zero] at this
    exact (count_pos_iff.2 hj).ne' this
  have hi := hcount i
  rw [Finsupp.single_eq_same, Nat.cast_inj, count_eq_length.2 fun j hj => (hall j hj).symm] at hi
  exact eq_replicate_iff.2 ⟨hi, hall⟩

end List
end
end TAF_LiteralSource_0452

section TAF_LiteralSource_0453
/- Original module: TauCeti.Data.Finsupp.Order -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Decompositions of finitely supported functions on linear orders

A finitely supported function splits into its coordinates below a chosen index, its value at
that index, and its coordinates above it.

A natural-valued finitely supported function with an index below `l` in its support splits as
`single i 1 + g`, where `i < l` and every index in the support of `g` is at least `i`.
This decomposition supports induction on ordered monomials by removing one occurrence of
their least variable.
-/

public section

namespace Finsupp

variable {ι : Type*} [LinearOrder ι]

/-- A finitely supported function splits into its values before `i`, at `i`, and after `i`. -/
theorem filter_lt_add_single_add_filter_gt {M : Type*} [AddZeroClass M] (f : ι →₀ M) (i : ι) :
    f.filter (· < i) + single i (f i) + f.filter (i < ·) = f := by
  ext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne]
  · simp
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne']

/-- If the support of `f` is not bounded below by `l`, split off one occurrence of its least
index `i < l`. Every index in the remaining support is at least `i`. -/
theorem exists_eq_single_add_of_not_forall_le (f : ι →₀ ℕ) {l : ι}
    (h : ¬ ∀ i ∈ f.support, l ≤ i) :
    ∃ (i : ι) (g : ι →₀ ℕ), i < l ∧ (∀ j ∈ g.support, i ≤ j) ∧ f = single i 1 + g := by
  simp only [not_forall, not_le] at h
  obtain ⟨j, hj, hjl⟩ := h
  have hne : f.support.Nonempty := ⟨j, hj⟩
  let i := f.support.min' hne
  have hi : i ∈ f.support := f.support.min'_mem hne
  refine ⟨i, f - single i 1, (f.support.min'_le j hj).trans_lt hjl, fun k hk ↦ ?_, ?_⟩
  · exact f.support.min'_le k (support_tsub hk)
  · simpa only [add_comm] using (sub_add_single_one_cancel (mem_support_iff.1 hi)).symm

end Finsupp
end
end TAF_LiteralSource_0453

section TAF_LiteralSource_0454
/- Original module: TauCeti.Data.Finsupp.Weight -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Weights of finitely supported functions

If every variable occurring in a monomial `f : σ →₀ ℕ` has weight at most `c`, then the weight
of `f` is at most `degree f • c`. With `c = -1` over `ℤ`, this says that a monomial all of whose
variables have negative weight has weight at most minus its total degree, which is how
negatively graded variables bound the degree of elements of powers of the ideal of the
variables.

The weight of a multiset multiplicity function is the sum of the weights of its entries.

Weights also respect scaling of the weight vector and decompose into contributions before, at,
and after a chosen coordinate in a linear order. These identities support comparisons between
lexicographic order and weighted degree.

On a product `ι × κ` of blocks indexed by `ι`, the weight given by the indicator of block `b`
sums the coefficients in that block. For natural-valued exponents, this is the degree in block `b`.
More generally, for a block map `b : σ → τ`, the indicator weight of the fibre over `h` is the value
at `h` of the pushforward `Finsupp.mapDomain b`.

## Main results

* `Finsupp.weight_toFinsupp`: multiset multiplicities recover the sum of entry weights.
* `Finsupp.prod_pow_eq_pow_degree`: `∏ a ^ tᵢ = a ^ degree t`.
* `Finsupp.degree_optionElim`: extending by `y` at `none` adds `y` to the degree.
* `Finsupp.prod_pow_optionElim`, `Finsupp.sum_nsmul_optionElim`: extending by `n` at `none`
  splits off the factor `c none ^ n` from the weighted product `∏ c i ^ (f.optionElim n) i`, and
  the summand `n • c none` from the weighted sum.
* `Finsupp.pow_degree_le_pow_degree_optionElim`: `a ^ degree f ≤ b ^ degree (f.optionElim m)`
  for `0 ≤ a ≤ b` and `1 ≤ b`.
* `Finsupp.weight_le_degree_nsmul`: if `w s ≤ c` for all `s`, then `weight w f ≤ degree f • c`.
* `Finsupp.weight_le_degree_nsmul_of_mem_support`: the same bound, assuming `w s ≤ c` only for
  the variables `s` occurring in `f`.
* `Finsupp.weight_le_degree_nsmul_of_monotone`: for monotone weights `w`, if every variable
  occurring in `f` is at most `i`, then `weight w f ≤ degree f • w i`.
* `Finsupp.weight_filter_lt_add_smul_add_weight_filter_gt`: split a weight at a coordinate.
* `Finsupp.weight_smul_left`: scaling the weight vector scales the weight.
* `Finsupp.weight_ite_fst_eq_sum`: the indicator weight of a block sums its coefficients; for
  natural-valued exponents, this is the degree in that block.
* `Finsupp.weight_ite_eq_mapDomain_apply`: the indicator weight of a fibre of `b : σ → τ` is the
  corresponding value of `Finsupp.mapDomain b`.
* `Finsupp.weight_ite_sumElim_eq_add_mapDomain_apply`: for the block map `Sum.elim id b` on
  `τ ⊕ σ`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`.
* `Finsupp.natCast_weight_eq_of_support_subset`: on monomials supported in a finite set `s`, the
  weight `weight w` agrees with any additive functional on `s → ℤ` taking the value `w i` on the
  `i`-th coordinate vector.
* `Finsupp.finite_degree_eq`, `Finsupp.finite_degree_le`: in finitely many variables there are
  finitely many exponent vectors of each degree, and of degree at most `n`.
* `Finsupp.fintypeDegreeEq`: for a fintype of variables with decidable equality, the exponent
  vectors of degree `n` form a fintype, enumerated by `Finset.finsuppAntidiag`.
-/

public section

namespace Finsupp

/-- The weight of the multiplicity function of a multiset is the sum of its entry weights. -/
@[simp]
theorem weight_toFinsupp {σ M : Type*} [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (s : Multiset σ) :
    weight w s.toFinsupp = (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, map_add, weight_single]
    simpa using congrArg (w i + ·) ih

/-- A product of powers of one fixed element `a`, with exponents given by `t`, is `a` raised to
the degree of `t`. -/
theorem prod_pow_eq_pow_degree {σ M : Type*} [CommMonoid M] (t : σ →₀ ℕ) (a : M) :
    (t.prod fun _ n ↦ a ^ n) = a ^ t.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, degree_apply]

/-- Extending `f` to `Option σ` by the value `y` at `none` adds `y` to the degree. -/
@[simp]
theorem degree_optionElim {σ R : Type*} [AddCommMonoid R] (f : σ →₀ R) (y : R) :
    (f.optionElim y).degree = y + f.degree := by
  have h (g : Option σ →₀ R) : g.degree = g.sum fun _ e ↦ e := degree_apply g
  rw [h, sum_option_index _ _ (fun _ ↦ rfl) fun _ _ _ ↦ rfl, optionElim_apply_none,
    some_optionElim, degree_apply, Finsupp.sum]

/-- The weighted product of `f.optionElim n` splits off the factor `c none ^ n`. This is the
form of Mathlib's `Finsupp.prod_option_index` used to separate one variable from the monomial
weights of multivariate series. -/
@[to_additive /-- The weighted sum of `f.optionElim n` splits off the summand `n • c none`. -/]
theorem prod_pow_optionElim {α N : Type*} [CommMonoid N] (c : Option α → N) (n : ℕ)
    (f : α →₀ ℕ) :
    (f.optionElim n).prod (c · ^ ·) = c none ^ n * f.prod (fun i k ↦ c (Option.some i) ^ k) := by
  rw [prod_option_index _ _ (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _,
    optionElim_apply_none, some_optionElim]

/-- A power `a ^ degree f` is bounded by the power `b ^ degree (f.optionElim m)` of a larger
base `b ≥ 1`, for any value `m` at `none`. -/
theorem pow_degree_le_pow_degree_optionElim {σ R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 ≤ b) (f : σ →₀ ℕ) (m : ℕ) :
    a ^ f.degree ≤ b ^ (f.optionElim m).degree := by
  rw [degree_optionElim, pow_add]
  exact (pow_le_pow_left₀ ha hab _).trans (le_mul_of_one_le_left (pow_nonneg (ha.trans hab) _)
    (one_le_pow₀ hb))

end Finsupp

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- If every variable occurring in `f` has weight at most `c`, then the weight of `f` is at most
its degree times `c`. -/
theorem weight_le_degree_nsmul_of_mem_support (f : σ →₀ ℕ) {w : σ → M} {c : M}
    (hw : ∀ s ∈ f.support, w s ≤ c) : weight w f ≤ degree f • c := by
  rw [weight_apply, degree_apply, Finsupp.sum, ← Finset.sum_nsmul_assoc]
  gcongr with s hs
  exact hw s hs

/-- If every variable has weight at most `c`, then the weight of `f` is at most its degree times
`c`. -/
theorem weight_le_degree_nsmul (f : σ →₀ ℕ) {w : σ → M} {c : M} (hw : ∀ s, w s ≤ c) :
    weight w f ≤ degree f • c :=
  weight_le_degree_nsmul_of_mem_support f fun s _ ↦ hw s

/-- If the weights `w` are monotone and every variable occurring in `f` is at most `i`, then the
weight of `f` is at most its degree times `w i`. -/
theorem weight_le_degree_nsmul_of_monotone [Preorder σ] (f : σ →₀ ℕ) {w : σ → M}
    (hw : Monotone w) {i : σ} (hf : ∀ s ∈ f.support, s ≤ i) : weight w f ≤ degree f • w i :=
  weight_le_degree_nsmul_of_mem_support f fun s hs ↦ hw (hf s hs)

end Finsupp

namespace Finsupp

variable {σ M : Type*}

/-- The `c`-weight of a finitely supported function `w` splits into the weights before `i`, at
`i`, and after `i`. -/
theorem weight_filter_lt_add_smul_add_weight_filter_gt [LinearOrder σ] {R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (c : σ → M) (w : σ →₀ R) (i : σ) :
    weight c (w.filter (· < i)) + w i • c i + weight c (w.filter (i < ·)) = weight c w := by
  conv_rhs => rw [← filter_lt_add_single_add_filter_gt w i]
  rw [map_add, map_add, weight_single]

/-- Scaling the weight vector scales the weight. -/
theorem weight_smul_left {R S : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DistribSMul S M] [SMulCommClass R S M] (s : S) (c : σ → M) (w : σ →₀ R) :
    weight (s • c) w = s • weight c w := by
  simp only [weight_apply, smul_sum, Pi.smul_apply]
  exact sum_congr fun _ _ ↦ smul_comm _ s _

end Finsupp

namespace Finsupp

/-- The indicator weight of block `b` of a finitely supported function on `ι × κ` is the sum of
its coefficients in block `b`. -/
theorem weight_ite_fst_eq_sum {ι κ R : Type*} [Fintype κ] [DecidableEq ι] [Semiring R]
    (e : ι × κ →₀ R) (b : ι) :
    weight (fun p : ι × κ ↦ if p.1 = b then (1 : R) else 0) e = ∑ l, e (b, l) := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, Finsupp.add_apply, Finset.sum_add_distrib]
  | single p n =>
    obtain ⟨h, l⟩ := p
    by_cases hb : h = b
    · subst hb
      classical
      simp [Finsupp.weight_single, Finsupp.single_apply]
    · simp [Finsupp.weight_single, hb]

end Finsupp

namespace Finsupp

/-- The indicator weight of the fibre of `b` over `h` is the value at `h` of the pushforward of
`e` along `b`, that is, the sum of the coefficients of `e` at the indices lying over `h`. -/
theorem weight_ite_eq_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (e : σ →₀ R) (h : τ) :
    weight (fun j ↦ if b j = h then (1 : R) else 0) e = e.mapDomain b h := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, mapDomain_add, Finsupp.add_apply]
  | single j n => by_cases hj : b j = h <;> simp [weight_single, mapDomain_single, hj]

end Finsupp

namespace Finsupp

/-- On `τ ⊕ σ`, with the block map `Sum.elim id b` that puts the coordinate `.inl h` into block
`h`, the indicator weight of block `h` of `a.sumElim e` is `a h + e.mapDomain b h`. -/
theorem weight_ite_sumElim_eq_add_mapDomain_apply {σ τ R : Type*} [DecidableEq τ] [Semiring R]
    (b : σ → τ) (a : τ →₀ R) (e : σ →₀ R) (h : τ) :
    weight (fun v ↦ if Sum.elim id b v = h then (1 : R) else 0) (a.sumElim e) =
      a h + e.mapDomain b h := by
  rw [weight_ite_eq_mapDomain_apply, sumElim_eq_add, mapDomain_add, ← mapDomain_comp,
    ← mapDomain_comp]
  simp

end Finsupp

namespace Finsupp

/-- If an additive functional `μ` on the integer vectors indexed by a finite set `s` takes the
value `w i` on the `i`-th coordinate vector, then `μ` agrees with the weight `weight w` on every
monomial supported in `s`. -/
theorem natCast_weight_eq_of_support_subset {σ : Type*} [DecidableEq σ] {s : Finset σ}
    (μ : (s → ℤ) →+ ℤ) {w : σ → ℕ} (hμ : ∀ i : s, μ (Pi.single i 1) = w i) {a : σ →₀ ℕ}
    (ha : a.support ⊆ s) : (weight w a : ℤ) = μ fun i ↦ (a i : ℤ) := by
  rw [weight_apply, Finsupp.sum_of_support_subset a ha _ (by simp), Nat.cast_sum,
    ← Finset.sum_coe_sort s]
  conv_rhs => rw [← Finset.univ_sum_single fun i : s ↦ (a i : ℤ)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (Pi.single i (a i : ℤ) : s → ℤ) = a i • Pi.single i 1 := by
    rw [← Pi.single_smul', Nat.smul_one_eq_cast]
  rw [hc, map_nsmul, hμ]
  simp

end Finsupp

namespace Finsupp

/-- In finitely many variables there are finitely many exponent vectors of each degree. -/
instance finite_degree_eq {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree = n} :=
  (finite_of_degree_eq n).to_subtype

/-- In finitely many variables there are finitely many exponent vectors of degree at most `n`. -/
instance finite_degree_le {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree ≤ n} :=
  (finite_of_degree_le n).to_subtype

/-- For a fintype of variables with decidable equality, the exponent vectors of degree `n` form a
fintype, enumerated by `Finset.finsuppAntidiag`. -/
instance fintypeDegreeEq {σ : Type*} [Fintype σ] [DecidableEq σ] (n : ℕ) :
    Fintype {s : σ →₀ ℕ // s.degree = n} :=
  Fintype.ofFinset (p := {s : σ →₀ ℕ | s.degree = n}) ((Finset.univ : Finset σ).finsuppAntidiag n)
    fun s ↦ by simp [Finset.mem_finsuppAntidiag, degree_eq_sum]

end Finsupp
end
end TAF_LiteralSource_0454

section TAF_LiteralSource_0455
/- Original module: TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The submodules of polynomials of bounded total degree

Mathlib's `MvPolynomial.restrictTotalDegree σ R m` is the submodule of polynomials of total degree
at most `m`. This file records that these submodules increase with `m`, that a monomial of degree
at most `m` lies in the `m`-th one, and that the `m`-th one is spanned by those monomials, so that
a linear statement about polynomials of bounded degree reduces to monomials. These monomials form
a basis whose coordinates are the coefficients, giving finite coordinates on tuples of
bounded-degree polynomials; evaluating such tuples is faithful over an infinite integral domain,
by Mathlib's `MvPolynomial.funext`. Raising the degree bound leaves the evaluation unchanged and
zero-pads the coordinates. As a spanning family, the monomials may be
replaced by products `∏ᵢ Sₖᵢ(Xᵢ)` of the members of a polynomial sequence `S` in the separate
variables, for instance the integer-valued binomial polynomials.

## Main results

* `MvPolynomial.restrictTotalDegree_mono`: the submodules increase with the degree bound.
* `MvPolynomial.monomial_mem_restrictTotalDegree`: a monomial of degree at most `m` has total
  degree at most `m`.
* `MvPolynomial.restrictTotalDegree_eq_span`: the monomials of degree at most `m` span the
  polynomials of total degree at most `m`.
* `MvPolynomial.basisRestrictTotalDegree`: the monomial basis of the polynomials of total degree
  at most `m`, whose coordinates are the coefficients.
* `MvPolynomial.boundedCoefficientEquiv`: monomial coefficients as finite coordinates on tuples of
  bounded-degree polynomials.
* `MvPolynomial.boundedEvaluation`, `MvPolynomial.boundedEvaluation_injective`: evaluation of such
  tuples as vector-valued functions is linear, and injective over an infinite integral domain.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp`: raising the degree bound extends the
  finite coefficient coordinates by zero.
* `MvPolynomial.span_prod_aeval_X_le`: products of a triangular family of one-variable polynomials
  in the separate variables lie in the span of the products of the original family.
* `Polynomial.Sequence.span_prod_aeval_X_eq_restrictTotalDegree`: the products `∏ᵢ Sₖᵢ(Xᵢ)` of
  a polynomial sequence with unit leading coefficients span the polynomials of bounded degree.
* `Module.Basis.apply_mem_of_monomial_degree_le`: a bilinear map takes values in a submodule on
  bounded-degree polynomials if it does so on basis vectors and bounded-degree monomials.
* `Module.Basis.constr_X_mul_mem_restrictTotalDegree`: multiplication by a linear form raises
  total degree by at most one.
-/

public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

variable (σ R) in
/-- The polynomials of total degree at most `m` increase with `m`. -/
theorem restrictTotalDegree_mono : Monotone (restrictTotalDegree σ R) :=
  fun _ _ h p hp ↦
    (mem_restrictTotalDegree σ _ p).2 (((mem_restrictTotalDegree σ _ p).1 hp).trans h)

/-- A monomial whose exponent has degree at most `m` has total degree at most `m`. -/
theorem monomial_mem_restrictTotalDegree {s : σ →₀ ℕ} {m : ℕ} (h : s.degree ≤ m) (r : R) :
    monomial s r ∈ restrictTotalDegree σ R m :=
  (mem_restrictTotalDegree σ m _).2 <| (totalDegree_monomial_le s r).trans <| by
    simpa [Finsupp.sum, Finsupp.degree_apply] using h

variable (σ R) in
/-- The polynomials of total degree at most `m` are those supported on exponents of degree at
most `m`. -/
theorem restrictTotalDegree_eq_restrictSupport (m : ℕ) :
    restrictTotalDegree σ R m = restrictSupport R {s : σ →₀ ℕ | s.degree ≤ m} := by
  have hs : {s : σ →₀ ℕ | (s.sum fun _ e ↦ e) ≤ m} = {s | s.degree ≤ m} := by
    ext s
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [restrictTotalDegree, hs]

variable (σ R) in
/-- The polynomials of total degree at most `m` are spanned by the monomials of degree at most
`m`. -/
theorem restrictTotalDegree_eq_span (m : ℕ) :
    restrictTotalDegree σ R m =
      Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ m}) := by
  rw [restrictTotalDegree_eq_restrictSupport, restrictSupport_eq_span]

variable (σ R) in
/-- The monomial basis of the polynomials of total degree at most `m`, indexed by exponents of
degree at most `m`. -/
noncomputable def basisRestrictTotalDegree (m : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree ≤ m} R (restrictTotalDegree σ R m) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm)

/-- The coordinate of a bounded-degree polynomial in the monomial basis is its coefficient. -/
@[simp]
theorem basisRestrictTotalDegree_repr_apply (m : ℕ) (p : restrictTotalDegree σ R m)
    (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m).repr p s = (p : MvPolynomial σ R).coeff s := (rfl)

/-- A monomial basis vector of the bounded-degree polynomials is the corresponding monomial. -/
@[simp]
theorem coe_basisRestrictTotalDegree (m : ℕ) (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m s : MvPolynomial σ R) = monomial s.1 1 := by
  classical
  have h : basisRestrictTotalDegree σ R m s =
      ⟨monomial s.1 1, monomial_mem_restrictTotalDegree s.2 1⟩ := by
    refine (basisRestrictTotalDegree σ R m).repr.injective (Finsupp.ext fun t ↦ ?_)
    simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  rw [h]

section Coordinates

variable {J : Type*}

variable (σ R J) in
/-- Monomial coefficients identify `J`-indexed tuples of polynomials of total degree at most `d`
with functions on the pairs of an index and an exponent of degree at most `d`. For finitely many
variables and indices this index type is finite, so these are finite coordinates. -/
noncomputable def boundedCoefficientEquiv [Finite σ] (d : ℕ) :
    (J → restrictTotalDegree σ R d) ≃ₗ[R] (J × {s : σ →₀ ℕ // s.degree ≤ d} → R) :=
  (LinearEquiv.piCongrRight fun _ => (basisRestrictTotalDegree σ R d).equivFun).trans
    (LinearEquiv.curry R R J {s : σ →₀ ℕ // s.degree ≤ d}).symm

/-- A finite coefficient coordinate is the corresponding monomial coefficient of an entry. -/
@[simp] theorem boundedCoefficientEquiv_apply [Finite σ] {d : ℕ}
    (v : J → restrictTotalDegree σ R d) (i : J × {s : σ →₀ ℕ // s.degree ≤ d}) :
    boundedCoefficientEquiv σ R J d v i = (v i.1 : MvPolynomial σ R).coeff i.2 := by
  simp [boundedCoefficientEquiv, Function.uncurry]

/-- The tuple with prescribed finite coefficient coordinates has those monomial coefficients. -/
@[simp] theorem coeff_boundedCoefficientEquiv_symm_apply [Finite σ] {d : ℕ}
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R) (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (((boundedCoefficientEquiv σ R J d).symm a j : restrictTotalDegree σ R d) :
      MvPolynomial σ R).coeff s = a (j, s) := by
  have h := boundedCoefficientEquiv_apply ((boundedCoefficientEquiv σ R J d).symm a) (j, s)
  rwa [LinearEquiv.apply_symm_apply, eq_comm] at h

variable (σ R J) in
/-- Evaluation of a tuple of bounded-degree polynomials as a vector-valued function on points.
It is linear in the tuple. -/
noncomputable def boundedEvaluation (d : ℕ) :
    (J → restrictTotalDegree σ R d) →ₗ[R] (σ → R) → J → R where
  toFun v x j := eval x (v j : MvPolynomial σ R)
  map_add' v w := by
    funext x j
    simp
  map_smul' a v := by
    funext x j
    simp

/-- Coordinate evaluation of a tuple of bounded-degree polynomials. -/
@[simp] theorem boundedEvaluation_apply {d : ℕ} (v : J → restrictTotalDegree σ R d)
    (x : σ → R) (j : J) :
    boundedEvaluation σ R J d v x j = eval x (v j : MvPolynomial σ R) := (rfl)

/-- Over an infinite integral domain, bounded-degree polynomial tuples are determined by the
functions they define: the evaluation map is faithful. -/
theorem boundedEvaluation_injective {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (d : ℕ) : Function.Injective (boundedEvaluation σ R J d) := fun _ _ h =>
  _root_.funext fun j => Subtype.ext <| MvPolynomial.funext fun x => congrFun (congrFun h x) j

/-- Raising the degree bound from `d` to `d'` does not change the function defined by a tuple of
bounded-degree polynomials. -/
@[simp] theorem boundedEvaluation_inclusion_comp {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedEvaluation σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      boundedEvaluation σ R J d v := (rfl)

/-- Raising the degree bound from `d` to `d'` zero-pads the finite coefficient coordinates: they
are extended by zero along the inclusion of index types, so the new coordinates at exponents of
degree above `d` vanish. -/
theorem boundedCoefficientEquiv_inclusion_comp [Finite σ] {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedCoefficientEquiv σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
            fun _ hs => hs.trans h))
        (boundedCoefficientEquiv σ R J d v) := by
  have hinj : Function.Injective (Prod.map (id : J → J)
      (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
        fun _ hs => hs.trans h)) :=
    Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective
  ext ⟨j, s, hs'⟩
  by_cases hs : s.degree ≤ d
  · convert (hinj.extend_apply (boundedCoefficientEquiv σ R J d v)
      (0 : J × {s : σ →₀ ℕ // s.degree ≤ d'} → R) (j, ⟨s, hs⟩)).symm using 1
    · simp
    · -- The index `(j, ⟨s, hs'⟩)` is the image of `(j, ⟨s, hs⟩)` by definition.
      rw [Function.ExtendByZero.linearMap_apply]
      rfl
  · rw [Function.ExtendByZero.linearMap_apply, Function.extend_apply' _ _ _ ?_, Pi.zero_apply,
      boundedCoefficientEquiv_apply, Function.comp_apply, Submodule.coe_inclusion]
    · refine coeff_eq_zero_of_totalDegree_lt ?_
      rw [← Finsupp.degree_apply]
      exact ((mem_restrictTotalDegree σ d _).1 (v j).2).trans_lt (not_le.1 hs)
    · rintro ⟨⟨j', s', hs''⟩, he⟩
      exact hs (by cases he; exact hs'')

end Coordinates

open Polynomial in
/-- If each `q k` with `k ≤ m` is a combination of the `p j` with `j ≤ k`, then the products
`∏ᵢ q_{τ i}(Xᵢ)` with `τ.degree ≤ m` lie in the span of the products `∏ᵢ p_{τ i}(Xᵢ)` with
`τ.degree ≤ m`. -/
theorem span_prod_aeval_X_le {σ R : Type*} [Fintype σ] [CommSemiring R] {p q : ℕ → R[X]} {m : ℕ}
    (h : ∀ k ≤ m, q k ∈ Submodule.span R (p '' Set.Iic k)) :
    Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i))) ''
        {τ | τ.degree ≤ m}) ≤
      Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (p (τ i))) ''
        {τ | τ.degree ≤ m}) := by
  classical
  rw [Submodule.span_le]
  rintro _ ⟨τ, hτ, rfl⟩
  -- Each factor lies in the span of the `p j (Xᵢ)` with `j ≤ τ i`.
  have hmem (i : σ) : Polynomial.aeval (X (R := R) i) (q (τ i)) ∈
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (h _ ((Finsupp.le_degree i τ).trans hτ))
  have hprod : ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i)) ∈ ∏ i,
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    induction (Finset.univ : Finset σ) using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact Submodule.one_le.1 le_rfl
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Submodule.mul_mem_mul (hmem i) ih
  rw [Submodule.prod_span] at hprod
  refine Submodule.span_mono ?_ hprod
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hx
  simp only [Finset.mem_univ, forall_const, Set.image_image] at hg
  choose j hj hgj using fun i ↦ @hg i
  refine ⟨Finsupp.equivFunOnFinite.symm j, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_le_sum fun i _ ↦ Set.mem_Iic.1 (hj i)).trans
      ((Finsupp.degree_eq_sum τ).symm.le.trans hτ)
  · simp [← hgj]

end MvPolynomial

namespace Polynomial.Sequence

open Submodule

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- **Change of basis to products of a polynomial sequence.** If the leading coefficients of
`S₀, …, Sₘ` are units, then the products `∏ᵢ S_{τ i}(Xᵢ)` over the exponents `τ` of degree at
most `m` span the polynomials of total degree at most `m`, exactly as the monomials `X^τ` do. -/
theorem span_prod_aeval_X_eq_restrictTotalDegree (S : Sequence R) {m : ℕ}
    (hS : ∀ k ≤ m, IsUnit (S k).leadingCoeff) :
    span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) (S (τ i))) ''
        {τ | τ.degree ≤ m}) = MvPolynomial.restrictTotalDegree σ R m := by
  classical
  have hmon : MvPolynomial.restrictTotalDegree σ R m =
      span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) ((X : R[X]) ^ (τ i))) ''
        {τ | τ.degree ≤ m}) := by
    rw [MvPolynomial.restrictTotalDegree_eq_span]
    congr! with τ
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  rw [hmon]
  refine le_antisymm (MvPolynomial.span_prod_aeval_X_le fun k _ ↦ ?_)
    (MvPolynomial.span_prod_aeval_X_le fun k hk ↦ ?_)
  · have : S k ∈ degreeLE R k := mem_degreeLE.2 (S.degree_eq k).le
    rwa [degreeLE_eq_span_X_pow, Finset.coe_image, Finset.coe_range,
      Set.Iio_add_one_eq_Iic] at this
  · rw [S.span_degreeLE fun i hi ↦ hS i (hi.trans hk), mem_degreeLE]
    exact degree_X_pow_le k

end Polynomial.Sequence

namespace Module.Basis

open MvPolynomial

section Bilinear

variable {σ κ R L M : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]
  [AddCommMonoid M] [Module R M]

/-- A bilinear map out of a module and a polynomial algebra takes values in a submodule on
polynomials of total degree at most `d` if it does so on basis vectors and monomials of degree at
most `d`. -/
theorem apply_mem_of_monomial_degree_le (b : Basis κ R L)
    (Φ : L →ₗ[R] MvPolynomial σ R →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : κ) (s : σ →₀ ℕ), s.degree ≤ d → Φ (b l) (monomial s 1) ∈ N)
    (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h l s hs
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

end Bilinear

variable {ι R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- Multiplying by the linear form attached to `x` in the basis `b` raises total degree by at
most one. -/
theorem constr_X_mul_mem_restrictTotalDegree (b : Basis ι R L) {d : ℕ} (x : L)
    {p : MvPolynomial ι R} (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  refine b.apply_mem_of_monomial_degree_le
    ((LinearMap.mul R _).comp (b.constr R X)) _ d (fun l σ hσ ↦ ?_) x hp
  have hm : (monomial (Finsupp.single l 1 + σ) 1 : MvPolynomial ι R) ∈
      restrictTotalDegree ι R (d + 1) :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  simpa [monomial_single_add] using hm

end Module.Basis
end
end TAF_LiteralSource_0455

section TAF_LiteralSource_0456
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.PolynomialRep -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The PBW representation of a Lie algebra on a polynomial algebra

Let `L` be a Lie algebra over a commutative ring `R`, free with a basis `b` indexed by a linearly
ordered type `ι`, and let `S = R[zᵢ | i ∈ ι]` be the polynomial algebra on the same index set.
This file constructs the representation of `L` on `S` that proves the linear-independence half
of the Poincaré--Birkhoff--Witt theorem: a Lie algebra homomorphism

`b.pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R S`

such that

* `bᵢ` acts on a monomial `z^σ` all of whose variables are at least `i` by multiplication by
  `zᵢ`;
* every `x : L` acts on a polynomial of total degree at most `d` as multiplication by the linear
  form `zₓ = ∑ᵢ (b.repr x i) zᵢ`, up to an error of total degree at most `d`.

Given a word `x₁ ⋯ xₙ` in `L`, the induced action of `U(L)` therefore sends `1` to `zₓ₁ ⋯ zₓₙ`
up to lower-degree terms, and sends an ordered monomial `bᵢ₁ ⋯ bᵢₙ` (`i₁ ≤ ⋯ ≤ iₙ`) to the monomial
`zᵢ₁ ⋯ zᵢₙ` exactly. This is what separates the graded pieces of the PBW filtration from each
other.

## The construction

The action of `bₗ` on a monomial `z^σ` is defined by induction on the degree of `σ`. If every
variable of `σ` is at least `l`, it is multiplication by `zₗ`. Otherwise `σ = eμ + τ` where `μ` is
the least variable of `σ` and `μ < l`, and the value is forced by the commutator relation that the
representation must satisfy:

`bₗ · z^σ = zμ zₗ z^τ + bμ · (bₗ · z^τ - zₗ z^τ) + ⁅bₗ, bμ⁆ · z^τ`,

where all actions on the right are on polynomials of degree less than that of `σ`. The induction
is carried out by iterating a single step on bilinear maps `L → S → S`; the iterates agree on
polynomials of degree at most `n` from the `n`-th one onwards, and their limit is the action.
Verifying that the result is a Lie algebra homomorphism is again an induction on degree, whose
only nontrivial case uses the Jacobi identity. The recursive construction and its degree estimates
use only a module with a bracket; the Lie identities enter when proving the representation law.

## Main definitions and results

* `Module.Basis.pbwPolynomialRep`: the representation.
* `Module.Basis.pbwPolynomialRep_basis_monomial_of_le`: the action of `bₗ` on a monomial in
  variables at least `l` is multiplication by `zₗ`.
* `Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`: up to terms of total degree at
  most `d`, the action on a polynomial of total degree at most `d` is multiplication by the
  corresponding linear form.
* `Module.Basis.pbwPolynomialRep_mem_restrictTotalDegree`: the action raises total degree by at
  most one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4,
  Lemma A, whose proof this file follows.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

open MvPolynomial

universe u v w

namespace Module.Basis

variable {R : Type u} {L : Type v} {ι : Type w}

local notation "S" => MvPolynomial ι R

local notation "S≤" => MvPolynomial.restrictTotalDegree ι R

attribute [local instance 100] LieRing.ofAssociativeRing

namespace PBWPolynomialRep

/-! ### Monomial bookkeeping -/

-- Keep the split-off variable first so Mathlib normalizes its monomial directly.
attribute [local simp] monomial_single_add

/-! ### Multiplication by the linear form -/

section Semiring

variable [CommSemiring R] [AddCommMonoid L] [Module R L] (b : Basis ι R L)

/-- Multiplication by the linear form `zₓ = b.constr R X x`. -/
private noncomputable def naive : L →ₗ[R] S →ₗ[R] S :=
  (LinearMap.mul R S).comp (b.constr R X)

private theorem naive_apply (x : L) (p : S) : naive b x p = b.constr R X x * p :=
  rfl

end Semiring

section DegreeBound

variable [CommRing R] [AddCommGroup L] [Module R L] (b : Basis ι R L)

/-- The degree estimate `g x p - zₓ p ∈ S≤ d` for `p ∈ S≤ d`, in every degree. -/
private def DegreeBound (g : L →ₗ[R] S →ₗ[R] S) : Prop :=
  ∀ (d : ℕ) (x : L) (p : S), p ∈ (S≤ d) → g x p - b.constr R X x * p ∈ S≤ d

private theorem DegreeBound.mem {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ} (x : L)
    {p : S} (hp : p ∈ S≤ d) : g x p ∈ S≤ (d + 1) := by
  have := Submodule.add_mem _ (restrictTotalDegree_mono ι R (Nat.le_succ d) (hg d x p hp))
    (b.constr_X_mul_mem_restrictTotalDegree x hp)
  rwa [sub_add_cancel] at this

end DegreeBound

variable [CommRing R] [LinearOrder ι]

/-! ### The inductive step -/

section Construction

variable [AddCommGroup L] [Module R L] (b : Basis ι R L) [Bracket L L]

/-- One step of the inductive construction: from an action `g`, valid in degrees below that of
`σ`, define the action of `bₗ` on `z^σ`. -/
private noncomputable def step (g : L →ₗ[R] S →ₗ[R] S) : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦
    if h : ∀ i ∈ σ.support, l ≤ i then X l * monomial σ 1
    else
      let μ := σ.support.min' (by
        push Not at h
        obtain ⟨i, hi, -⟩ := h
        exact ⟨i, hi⟩)
      let τ := σ - Finsupp.single μ 1
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1)

private theorem step_of_le (g : L →ₗ[R] S →ₗ[R] S) {l : ι} {σ : ι →₀ ℕ}
    (h : ∀ i ∈ σ.support, l ≤ i) : step b g (b l) (monomial σ 1) = X l * monomial σ 1 := by
  have hσ : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis, dite_eq_left_of_eq_true (eq_true h), hσ]

private theorem step_of_lt (g : L →ₗ[R] S →ₗ[R] S) {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    step b g (b l) (monomial (Finsupp.single μ 1 + τ) 1) =
      X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : μ ∈ (Finsupp.single μ 1 + τ).support := by simp
  have h : ¬ ∀ i ∈ (Finsupp.single μ 1 + τ).support, l ≤ i :=
    fun h ↦ (h μ hμ).not_gt hμl
  have hσ : (monomial (Finsupp.single μ 1 + τ) 1 : S) =
      basisMonomials ι R (Finsupp.single μ 1 + τ) := by simp
  rw [step, Basis.constr_basis, hσ, Basis.constr_basis,
    dite_eq_right_of_eq_false (eq_false h)]
  have hmin : (Finsupp.single μ 1 + τ).support.min' ⟨μ, hμ⟩ = μ :=
    le_antisymm (Finset.min'_le _ _ hμ)
      (Finset.le_min' _ _ _ (by simpa [Finsupp.support_add_eq_union] using hμτ))
  simp only [hmin, add_tsub_cancel_left]

private theorem degreeBound_step {g : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) :
    DegreeBound b (step b g) := by
  intro d x p hp
  refine b.apply_mem_of_monomial_degree_le (step b g - naive b) _ d (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, naive_apply, Basis.constr_basis]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := σ.exists_eq_single_add_of_not_forall_le h
  have hτ : τ.degree + 1 ≤ d := by simpa [Nat.one_add] using hσ
  have hX : X μ * X l * monomial τ 1 + g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) +
        g ⁅b l, b μ⁆ (monomial τ 1) - X l * (X μ * monomial τ 1) =
      g (b μ) (g (b l) (monomial τ 1) - X l * monomial τ 1) + g ⁅b l, b μ⁆ (monomial τ 1) := by
    ring
  rw [step_of_lt b g hμl hμτ]
  simp only [monomial_single_add, pow_one]
  rw [hX]
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  refine restrictTotalDegree_mono ι R hτ
    (Submodule.add_mem _ (DegreeBound.mem b hg _ ?_) (DegreeBound.mem b hg _ hτmem))
  have := hg _ (b l) _ hτmem
  rwa [Basis.constr_basis] at this

/-- `step` only looks one degree down: actions agreeing in degree at most `d` give the same next
step in degree at most `d + 1`. -/
private theorem step_congr {g g' : L →ₗ[R] S →ₗ[R] S} (hg : DegreeBound b g) {d : ℕ}
    (hgg' : ∀ (x : L) (p : S), p ∈ (S≤ d) → g x p = g' x p) (x : L) {p : S}
    (hp : p ∈ S≤ (d + 1)) : step b g x p = step b g' x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine b.apply_mem_of_monomial_degree_le (step b g - step b g') ⊥ (d + 1)
    (fun l σ hσ ↦ ?_) x hp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
  by_cases h : ∀ i ∈ σ.support, l ≤ i
  · rw [step_of_le b g h, step_of_le b g' h]
  obtain ⟨μ, τ, hμl, hμτ, rfl⟩ := σ.exists_eq_single_add_of_not_forall_le h
  have hτmem : (monomial τ 1 : S) ∈ S≤ d :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  have hq : g (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ d := by
    have := hg d (b l) _ hτmem
    rwa [Basis.constr_basis] at this
  rw [step_of_lt b g hμl hμτ, step_of_lt b g' hμl hμτ, hgg' _ _ hq, hgg' _ _ hτmem,
    hgg' _ _ hτmem]

/-- The iterates of `step`, starting from multiplication by the linear form. -/
private noncomputable def approx : ℕ → L →ₗ[R] S →ₗ[R] S
  | 0 => naive b
  | n + 1 => step b (approx n)

private theorem degreeBound_approx (n : ℕ) : DegreeBound b (approx b n) := by
  induction n with
  | zero =>
      intro d x p _
      rw [approx, naive_apply, sub_self]
      exact Submodule.zero_mem _
  | succ n ih => exact degreeBound_step b ih

private theorem approx_succ_eq (n : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + 1) x p = approx b n x p := by
  induction n generalizing x p with
  | zero =>
      rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
      refine b.apply_mem_of_monomial_degree_le (approx b 1 - approx b 0) ⊥ 0
        (fun l σ hσ ↦ ?_) x hp
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero]
      have hσ : σ = 0 := (Finsupp.degree_eq_zero_iff σ).1 (Nat.le_zero.1 hσ)
      subst hσ
      rw [approx, approx, step_of_le b _ (by simp), naive_apply, Basis.constr_basis]
  | succ n ih => exact step_congr b (degreeBound_approx b (n + 1)) ih x hp

private theorem approx_add_eq (n k : ℕ) (x : L) {p : S} (hp : p ∈ S≤ n) :
    approx b (n + k) x p = approx b n x p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← add_assoc,
        approx_succ_eq b _ x (restrictTotalDegree_mono ι R (Nat.le_add_right n k) hp), ih]

/-! ### The limit action -/

/-- The limit of the iterates: on monomials of degree `n`, the `n`-th iterate. -/
private noncomputable def act : L →ₗ[R] S →ₗ[R] S :=
  b.constr R fun l ↦ (basisMonomials ι R).constr R fun σ ↦ approx b σ.degree (b l) (monomial σ 1)

private theorem act_eq_approx {d n : ℕ} (hdn : d ≤ n) (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p = approx b n x p := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← LinearMap.sub_apply, ← Submodule.mem_bot R]
  refine b.apply_mem_of_monomial_degree_le (act b - approx b n) ⊥ d (fun l σ hσ ↦ ?_) x hp
  have hσb : (monomial σ 1 : S) = basisMonomials ι R σ := by simp
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.mem_bot, sub_eq_zero, act,
    Basis.constr_basis, hσb, Basis.constr_basis, ← hσb]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hσ.trans hdn)
  exact (approx_add_eq b _ k _ (monomial_mem_restrictTotalDegree le_rfl 1)).symm

private theorem act_sub_mem {d : ℕ} (x : L) {p : S} (hp : p ∈ S≤ d) :
    act b x p - b.constr R X x * p ∈ S≤ d := by
  rw [act_eq_approx b le_rfl x hp]
  exact degreeBound_approx b d d x p hp

private theorem degreeBound_act : DegreeBound b (act b) :=
  fun _ x _ hp ↦ act_sub_mem b x hp

private theorem act_of_le {l : ι} {σ : ι →₀ ℕ} (h : ∀ i ∈ σ.support, l ≤ i) :
    act b (b l) (monomial σ 1) = X l * monomial σ 1 := by
  rw [act_eq_approx b (Nat.le_succ _) _ (monomial_mem_restrictTotalDegree le_rfl 1), approx,
    step_of_le b _ h]

private theorem act_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l) (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (monomial (Finsupp.single μ 1 + τ) 1) =
      X μ * X l * monomial τ 1 + act b (b μ) (act b (b l) (monomial τ 1) - X l * monomial τ 1) +
        act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hτmem : (monomial τ 1 : S) ∈ S≤ τ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  have hq : approx b τ.degree (b l) (monomial τ 1) - X l * monomial τ 1 ∈ S≤ τ.degree := by
    have := degreeBound_approx b τ.degree τ.degree (b l) _ hτmem
    rwa [Basis.constr_basis] at this
  rw [act_eq_approx b le_rfl _
      (monomial_mem_restrictTotalDegree (s := Finsupp.single μ 1 + τ) le_rfl 1), map_add,
    Finsupp.degree_single, add_comm 1 τ.degree, approx, step_of_lt b _ hμl hμτ,
    act_eq_approx b le_rfl _ hτmem,
    act_eq_approx b le_rfl _ hτmem, act_eq_approx b le_rfl _ hq]

/-- The defining case of the commutator relation: `μ < l` and `μ` is at most every variable
of `τ`. -/
private theorem act_comm_of_lt {l μ : ι} {τ : ι →₀ ℕ} (hμl : μ < l)
    (hμτ : ∀ i ∈ τ.support, μ ≤ i) :
    act b (b l) (act b (b μ) (monomial τ 1)) =
      act b (b μ) (act b (b l) (monomial τ 1)) + act b ⁅b l, b μ⁆ (monomial τ 1) := by
  have hμ : act b (b μ) (X l * monomial τ 1) = X μ * X l * monomial τ 1 := by
    have h := act_of_le b (l := μ) (σ := Finsupp.single l 1 + τ)
      (by simpa [Finsupp.support_add_eq_union] using And.intro hμl.le hμτ)
    simpa [mul_assoc] using h
  have h := act_of_lt b hμl hμτ
  simp only [monomial_single_add, pow_one] at h
  rw [act_of_le b hμτ, h, map_sub, hμ]
  abel

/-! ### The commutator relation -/

/-- The commutator relation for the action, in total degree at most `d`. -/
private def CommRel (d : ℕ) : Prop :=
  ∀ (x y : L) (p : S), p ∈ (S≤ d) → act b x (act b y p) = act b y (act b x p) + act b ⁅x, y⁆ p

/-- The expansion of `bₗ bₘ z^τ` when the least variable `ν` of `τ` is less than both `l` and `m`,
assuming the commutator relation one degree down. -/
private theorem act_act_eq_of_lt {l m ν : ι} {Ψ : ι →₀ ℕ} (hνl : ν < l) (hνm : ν < m)
    (hνΨ : ∀ i ∈ Ψ.support, ν ≤ i) (ih : CommRel b Ψ.degree) :
    act b (b l) (act b (b m) (monomial (Finsupp.single ν 1 + Ψ) 1)) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) +
        act b ⁅b m, b ν⁆ (act b (b l) (monomial Ψ 1)) +
        act b ⁅b l, ⁅b m, b ν⁆⁆ (monomial Ψ 1) := by
  have hΨ : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
  -- `bₘ z^Ψ` is the monomial `zₘ z^Ψ` up to an error `w` of degree at most that of `Ψ`.
  set w := act b (b m) (monomial Ψ 1) - monomial (Finsupp.single m 1 + Ψ) 1 with hw
  have hwmem : w ∈ S≤ Ψ.degree := by
    rw [hw]
    simpa [Basis.constr_basis] using act_sub_mem b (b m) hΨ
  have hνΨm : ∀ i ∈ (Finsupp.single m 1 + Ψ).support, ν ≤ i :=
    by simpa [Finsupp.support_add_eq_union] using And.intro hνm.le hνΨ
  have hsplit : act b (b m) (monomial Ψ 1) = monomial (Finsupp.single m 1 + Ψ) 1 + w := by
    rw [hw, add_sub_cancel]
  -- The commutator relation for `bₗ` and `bν` on `bₘ z^Ψ`.
  have hlν : act b (b l) (act b (b ν) (act b (b m) (monomial Ψ 1))) =
      act b (b ν) (act b (b l) (act b (b m) (monomial Ψ 1))) +
        act b ⁅b l, b ν⁆ (act b (b m) (monomial Ψ 1)) := by
    rw [hsplit]
    simp only [map_add]
    rw [act_comm_of_lt b hνl hνΨm, ih _ _ _ hwmem]
    abel
  simp only [monomial_single_add, pow_one]
  rw [← act_of_le b hνΨ,
    ih (b m) (b ν) _ hΨ, map_add, hlν, ih (b l) ⁅b m, b ν⁆ _ hΨ]
  abel

end Construction

variable [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

/-- The defect `x ↦ y ↦ [act x, act y] - act ⁅x, y⁆`, as a bilinear map. -/
private noncomputable def defect : L →ₗ[R] L →ₗ[R] Module.End R S :=
  LinearMap.mk₂ R (fun x y ↦ act b x * act b y - act b y * act b x - act b ⁅x, y⁆)
    (fun x₁ x₂ y ↦ by simp only [map_add, add_lie, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, smul_lie, smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun x y₁ y₂ ↦ by simp only [map_add, lie_add, add_mul, mul_add]; abel)
    (fun c x y ↦ by
      simp only [map_smul, lie_smul, smul_mul_assoc, mul_smul_comm, smul_sub])

private theorem commRel_of_basis {d : ℕ}
    (h : ∀ (l m : ι) (τ : ι →₀ ℕ), τ.degree ≤ d →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1)) :
    CommRel b d := by
  have key : ∀ (l : ι) (y : L) (p : S), p ∈ (S≤ d) → defect b (b l) y p = 0 := by
    intro l y p hp
    rw [← Submodule.mem_bot R]
    refine b.apply_mem_of_monomial_degree_le (defect b (b l)) ⊥ d
      (fun m τ hτ ↦ ?_) y hp
    simp [defect, h l m τ hτ]
  intro x y p hp
  have hx : ((defect b).flip y).flip p = 0 := b.ext fun l ↦ by simpa using key l y p hp
  have := LinearMap.congr_fun hx x
  simp only [defect, LinearMap.flip_apply, LinearMap.mk₂_apply, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← sub_eq_zero, ← this]
  abel

/-- The commutator relation in total degree at most `d`, by strong induction on `d`. -/
private theorem commRel (d : ℕ) : CommRel b d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  refine commRel_of_basis b fun l m τ hτ ↦ ?_
  -- the hard case: the least variable `ν` of `τ` is less than both `l` and `m`
  have hard : ∀ {l m : ι}, (¬ ∀ i ∈ τ.support, m ≤ i) → m < l →
      act b (b l) (act b (b m) (monomial τ 1)) =
        act b (b m) (act b (b l) (monomial τ 1)) + act b ⁅b l, b m⁆ (monomial τ 1) := by
    intro l m hm hml
    obtain ⟨ν, Ψ, hνm, hνΨ, rfl⟩ := τ.exists_eq_single_add_of_not_forall_le hm
    have hΨ : Ψ.degree < d := by simp at hτ; omega
    have hνl := hνm.trans hml
    have ihΨ := ih _ hΨ
    have hΨmem : (monomial Ψ 1 : S) ∈ S≤ Ψ.degree := monomial_mem_restrictTotalDegree le_rfl 1
    -- Expand both `bₗ bₘ z^τ` and `bₘ bₗ z^τ`; the cross terms `⁅bₗ, bν⁆ bₘ z^Ψ` and
    -- `⁅bₘ, bν⁆ bₗ z^Ψ` cancel. Writing `z^τ = bν z^Ψ`, the commutator relation one degree down
    -- turns the right-hand side into `bν ⁅bₗ, bₘ⁆ z^Ψ + ⁅⁅bₗ, bₘ⁆, bν⁆ z^Ψ`, and the Jacobi
    -- identity matches the remaining double brackets.
    rw [act_act_eq_of_lt b hνl hνm hνΨ ihΨ, act_act_eq_of_lt b hνm hνl hνΨ ihΨ,
      monomial_single_add, pow_one, ← act_of_le b hνΨ,
      ihΨ ⁅b l, b m⁆ (b ν) _ hΨmem,
      ihΨ (b l) (b m) _ hΨmem, map_add, leibniz_lie (b l) (b m) (b ν), map_add,
      LinearMap.add_apply]
    abel
  rcases lt_trichotomy m l with hml | rfl | hlm
  · by_cases hm : ∀ i ∈ τ.support, m ≤ i
    · exact act_comm_of_lt b hml hm
    · exact hard hm hml
  · rw [lie_self, map_zero, LinearMap.zero_apply, add_zero]
  · by_cases hl : ∀ i ∈ τ.support, l ≤ i
    · rw [act_comm_of_lt b hlm hl, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel
    · rw [hard hl hlm, ← lie_skew, map_neg, LinearMap.neg_apply]
      abel

end PBWPolynomialRep

open PBWPolynomialRep

variable [CommRing R] [LinearOrder ι] [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

/-- **The PBW representation.** For a Lie algebra `L` with a basis `b` indexed by a linearly
ordered type `ι`, the representation of `L` on the polynomial algebra `R[zᵢ | i ∈ ι]` in which
`bₗ` acts on a monomial in variables at least `l` by multiplication by `zₗ`
(`Module.Basis.pbwPolynomialRep_basis_monomial_of_le`), and every element acts as multiplication
by its linear form up to lower-degree terms
(`Module.Basis.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree`). -/
noncomputable def pbwPolynomialRep : L →ₗ⁅R⁆ Module.End R (MvPolynomial ι R) where
  toLinearMap := act b
  map_lie' {x y} := by
    refine LinearMap.ext fun p ↦ ?_
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LieRing.of_associative_ring_bracket,
      LinearMap.sub_apply, Module.End.mul_apply,
      commRel b p.totalDegree x y p ((mem_restrictTotalDegree ι _ p).2 le_rfl)]
    abel

/-- A basis vector `bₗ` acts on a monomial with any coefficient, all of whose variables are at
least `l`, as multiplication by the variable `zₗ`. -/
@[simp↓]
theorem pbwPolynomialRep_basis_monomial_of_le {l : ι} {σ : ι →₀ ℕ} (r : R)
    (h : ∀ i ∈ σ.support, l ≤ i) :
    b.pbwPolynomialRep (b l) (monomial σ r) = X l * monomial σ r := by
  have hr : (monomial σ r : S) = r • monomial σ 1 := by simp [smul_monomial]
  have h1 : b.pbwPolynomialRep (b l) (monomial σ 1) = X l * monomial σ 1 :=
    act_of_le b h
  rw [hr, map_smul, h1, mul_smul_comm]

/-- On polynomials of total degree at most `d`, the action of `x` is multiplication by the linear
form `zₓ = b.constr R X x`, up to an error of total degree at most `d`. -/
theorem pbwPolynomialRep_sub_mul_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p - b.constr R X x * p ∈ restrictTotalDegree ι R d :=
  act_sub_mem b x hp

/-- The action raises total degree by at most one. -/
theorem pbwPolynomialRep_mem_restrictTotalDegree {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.pbwPolynomialRep x p ∈ restrictTotalDegree ι R (d + 1) :=
  DegreeBound.mem b (degreeBound_act b) x hp

end Module.Basis
end
end TAF_LiteralSource_0456

section TAF_LiteralSource_0457
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic results on universal enveloping algebras

This file records general results about universal enveloping algebras that do not depend on
additional structures such as filtrations, bialgebras, or antipodes.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`: a universal enveloping algebra is
  generated, as an algebra, by its canonical Lie generators.
* `TauCeti.UniversalEnvelopingAlgebra.induction_ι`: the induction principle on the canonical Lie
  generators that the previous statement supplies.
* `TauCeti.UniversalEnvelopingAlgebra.instFiniteType`: a universal enveloping algebra is an algebra
  of finite type over the base ring as soon as the Lie algebra is finite as a module.
* `TauCeti.UniversalEnvelopingAlgebra.representation`: the algebra homomorphism `U(L) → End M`
  attached to a Lie module `M`, in particular the adjoint action of `U(L)` on `L` at `M = L`.
* `TauCeti.UniversalEnvelopingAlgebra.representation_lie_of_mem_center`: a central element of
  `U(L)` acts on a Lie module by a map commuting with the Lie action.
* `TauCeti.UniversalEnvelopingAlgebra.mem_center_iff_forall_lie_ι`: centrality in `U(L)` is
  detected on the canonical Lie generators alone.
* `TauCeti.UniversalEnvelopingAlgebra.ad_ι_pow_apply_ι`: iterating the commutator with a Lie
  generator reproduces, on the Lie generators, the iterated adjoint action of `L`.
* `TauCeti.UniversalEnvelopingAlgebra.lie_map_ι`: an algebra representation maps the bracket of
  canonical Lie generators to the bracket of their images.
* `TauCeti.UniversalEnvelopingAlgebra.lie_map_ι_eq_smul`: a Lie-bracket eigenvector remains one
  under an algebra representation.
* `TauCeti.UniversalEnvelopingAlgebra.mul_sub_mul_eq_map_ι_lie`: the image of a Lie bracket
  under an algebra homomorphism is the ring commutator of the images.
* `TauCeti.UniversalEnvelopingAlgebra.commute_of_lie_eq_zero`: images of Lie-commuting elements
  commute.
* `TauCeti.UniversalEnvelopingAlgebra.zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq`: a scaled
  Lie-bracket relation gives the corresponding scaled ring-commutator relation.
* `TauCeti.UniversalEnvelopingAlgebra.mul_eq_mul_add_zsmul_of_lie_eq`: an integral Lie-bracket
  structure constant gives the corresponding ring-commutator relation.
-/

public section

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The enveloping algebra is generated by the canonical Lie generators.** This is the `U(L)`
analogue of `TensorAlgebra.adjoin_range_ι`, obtained by pushing that statement along the surjective
quotient map `UniversalEnvelopingAlgebra.mkAlgHom R L`. -/
theorem adjoin_range_ι :
    _root_.Algebra.adjoin R (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R)) =
      (⊤ : Subalgebra R U) := by
  have hcomp : (⇑(_root_.UniversalEnvelopingAlgebra.ι R) : L → U) =
      ⇑(_root_.UniversalEnvelopingAlgebra.mkAlgHom R L) ∘ ⇑(TensorAlgebra.ι R) :=
    funext fun x => _root_.UniversalEnvelopingAlgebra.ι_apply R x
  rw [hcomp, Set.range_comp, ← AlgHom.map_adjoin, TensorAlgebra.adjoin_range_ι,
    _root_.Algebra.map_top]
  -- `mkAlgHom R L` is by definition the quotient map `RingCon.mkₐ R (ringCon R L)`.
  exact (AlgHom.range_eq_top _).2 (RingCon.mkₐ_surjective _)

/-- **Induction on the canonical Lie generators.** A property of elements of `U(L)` that holds for
the canonical Lie generators and the scalars, and is stable under sums and products, holds
everywhere, since those generate `U(L)` as an `R`-algebra. -/
@[elab_as_elim]
theorem induction_ι {p : U → Prop}
    (ι : ∀ x : L, p (_root_.UniversalEnvelopingAlgebra.ι R x))
    (algebraMap : ∀ r : R, p (_root_.Algebra.algebraMap R U r))
    (add : ∀ a b, p a → p b → p (a + b)) (mul : ∀ a b, p a → p b → p (a * b)) (u : U) : p u := by
  have hu : u ∈ _root_.Algebra.adjoin R (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R)) := by
    rw [adjoin_range_ι R L]; exact _root_.Algebra.mem_top
  induction hu using _root_.Algebra.adjoin_induction with
  | mem u hu => obtain ⟨x, rfl⟩ := hu; exact ι x
  | algebraMap r => exact algebraMap r
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

variable {R L} in
/-- **The enveloping algebra of a Lie algebra which is finite as a module is an `R`-algebra of
finite type**: a finite spanning set of `L` generates `U(L)` as an algebra, the canonical Lie
generators of `U(L)` generating it
(`TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`). -/
instance instFiniteType [Module.Finite R L] : Algebra.FiniteType R U := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := L)
  -- the span of the image of a spanning set of `L` is the whole of the image of `L`
  have hrange : ((Submodule.span R
      (⇑((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U) ''
        (S : Set L)) : Submodule R U) : Set U) =
      Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R (L := L)) := by
    rw [← Submodule.map_span, hS, ← LinearMap.range_eq_map, LinearMap.coe_range,
      LieHom.coe_toLinearMap]
  exact ⟨S.image ⇑((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U), by
    rw [Finset.coe_image, ← _root_.Algebra.adjoin_span, hrange, adjoin_range_ι R L]⟩

variable (M : Type w) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The representation of a universal enveloping algebra on a Lie module**: the algebra
homomorphism obtained from `LieModule.toEnd` by the universal property of `U(L)`. At `M = L` this
is the adjoint action, since `LieAlgebra.ad R L` is `LieModule.toEnd R L L`. -/
noncomputable def representation : U →ₐ[R] Module.End R M :=
  _root_.UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)

-- Neither this lemma nor its pointwise form below is a `simp` lemma: `simp` unfolds `ι` through
-- Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so a left-hand side mentioning `ι` is not in
-- simp-normal form. This is why Mathlib's own `lift_ι_apply` is not a `simp` lemma either;
-- `representation_ι'` is the corresponding simp-normal form.
/-- The representation acts on a canonical Lie generator by the Lie action. -/
theorem representation_ι (x : L) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) = LieModule.toEnd R L M x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The representation on the Lie algebra itself acts on a canonical generator by the adjoint
action. -/
theorem representation_ι_ad (x : L) :
    representation R L L (_root_.UniversalEnvelopingAlgebra.ι R x) = LieAlgebra.ad R L x :=
  representation_ι R L L x

/-- The `simp`-normal form of `TauCeti.UniversalEnvelopingAlgebra.representation_ι`, stated for
the canonical generators as `simp` writes them. -/
@[simp]
theorem representation_ι' (x : L) :
    representation R L M
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      LieModule.toEnd R L M x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply' R _ x

/-- The pointwise form of `TauCeti.UniversalEnvelopingAlgebra.representation_ι`: a Lie generator
acts by the Lie bracket. -/
theorem representation_ι_apply (x : L) (m : M) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  rw [representation_ι, LieModule.toEnd_apply_apply]

/-- **A central element of `U(L)` acts on a Lie module by a map commuting with the Lie action.**
Equivalently, `TauCeti.UniversalEnvelopingAlgebra.representation R L M u` is `L`-equivariant, that
is, a homomorphism of Lie modules. Centrality is used only against the canonical Lie generators,
which is what the Lie action is read off. -/
theorem representation_lie_of_mem_center {u : U} (hu : u ∈ Subalgebra.center R U) (x : L) (m : M) :
    representation R L M u ⁅x, m⁆ = ⁅x, representation R L M u m⁆ := by
  have h := congrArg (representation R L M)
    (Subalgebra.mem_center_iff.mp hu (_root_.UniversalEnvelopingAlgebra.ι R x))
  rw [map_mul, map_mul, representation_ι] at h
  have h₁ := congrArg (fun g : Module.End R M ↦ g m) h
  simpa only [Module.End.mul_apply, LieModule.toEnd_apply_apply] using h₁.symm

variable {R L}
variable {B : Type w} [Ring B] [Algebra R B]

/-- An algebra representation of the universal enveloping algebra maps the Lie bracket to the
commutator in its target algebra. -/
theorem lie_map_ι (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) (x y : L) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι R x), ρ (_root_.UniversalEnvelopingAlgebra.ι R y)⁆ =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) := by
  have hlie := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) x y
  rw [LieRing.of_associative_ring_bracket] at hlie
  rw [LieRing.of_associative_ring_bracket, hlie, map_sub, map_mul, map_mul]

/-- A Lie-bracket eigenvector remains one under an algebra representation of the universal
enveloping algebra. -/
theorem lie_map_ι_eq_smul (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {x y : L} {a : R}
    (hxy : ⁅x, y⁆ = a • y) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι R x), ρ (_root_.UniversalEnvelopingAlgebra.ι R y)⁆ =
      a • ρ (_root_.UniversalEnvelopingAlgebra.ι R y) := by
  rw [lie_map_ι ρ, hxy, map_smul, map_smul]

/-- The image of a Lie bracket under an algebra homomorphism from a universal enveloping algebra
is the ring commutator of the images. -/
theorem mul_sub_mul_eq_map_ι_lie
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) (a b : L) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι R a) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R b) -
        ρ (_root_.UniversalEnvelopingAlgebra.ι R b) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R a) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R ⁅a, b⁆) := by
  rw [LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) a b,
    LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul]

/-- Images of Lie-commuting elements commute under every algebra homomorphism from the universal
enveloping algebra. -/
theorem commute_of_lie_eq_zero
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b : L} (hab : ⁅a, b⁆ = 0) :
    Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι R a))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) := by
  have h := mul_sub_mul_eq_map_ι_lie ρ a b
  rw [hab, map_zero, map_zero] at h
  exact sub_eq_zero.mp h

/-- A scaled Lie-bracket relation becomes the corresponding scaled ring-commutator relation under
every algebra homomorphism from the universal enveloping algebra. -/
theorem zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b b' : L} {p q r : ℤ} {n : ℕ}
    (hab : (p * q) • ⁅a, b⁆ = ((n : ℤ) * r) • b') :
    (p • ρ (_root_.UniversalEnvelopingAlgebra.ι R a)) *
        (q • ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) =
      (q • ρ (_root_.UniversalEnvelopingAlgebra.ι R b)) *
          (p • ρ (_root_.UniversalEnvelopingAlgebra.ι R a)) +
        n • (r • ρ (_root_.UniversalEnvelopingAlgebra.ι R b')) := by
  have hbracket := congrArg ((p * q) • ·) (mul_sub_mul_eq_map_ι_lie ρ a b)
  rw [← map_zsmul, ← map_zsmul, hab, map_zsmul, map_zsmul] at hbracket
  rw [← sub_eq_iff_eq_add']
  have hcoeff : n • (r • ρ (_root_.UniversalEnvelopingAlgebra.ι R b')) =
      ((n : ℤ) * r) • ρ (_root_.UniversalEnvelopingAlgebra.ι R b') := by
    rw [← natCast_zsmul, ← mul_zsmul]
  rw [hcoeff]
  simpa only [smul_sub, mul_smul_comm, smul_mul_assoc, mul_zsmul, smul_comm p q] using
    hbracket

/-- A bracket relation with an integral structure constant becomes the corresponding commutator
relation under every algebra homomorphism from the universal enveloping algebra. -/
theorem mul_eq_mul_add_zsmul_of_lie_eq
    (ρ : _root_.UniversalEnvelopingAlgebra R L →ₐ[R] B) {a b b' : L} {c : ℤ}
    (hab : ⁅a, b⁆ = c • b') :
    ρ (_root_.UniversalEnvelopingAlgebra.ι R a) *
        ρ (_root_.UniversalEnvelopingAlgebra.ι R b) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι R b) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι R a) +
        c • ρ (_root_.UniversalEnvelopingAlgebra.ι R b') := by
  simpa using
    (zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := 1) (r := c) (n := 1) (by simpa using hab))


section Center

variable (R L)

/-- **Centrality in `U(L)` is detected on the canonical Lie generators.**  An element of `U(L)`
is central exactly when it brackets to zero against every canonical Lie generator, because those
generators generate `U(L)` as an algebra and the elements commuting with a fixed element form a
subalgebra. -/
theorem mem_center_iff_forall_lie_ι {u : U} :
    u ∈ Subalgebra.center R U ↔
      ∀ x : L, ⁅u, _root_.UniversalEnvelopingAlgebra.ι R x⁆ = 0 := by
  refine ⟨fun hu x => ?_, fun h => ?_⟩
  · rw [LieRing.of_associative_ring_bracket,
      ← Subalgebra.mem_center_iff.mp hu (_root_.UniversalEnvelopingAlgebra.ι R x), sub_self]
  · -- The centralizer of `u` is a subalgebra containing every Lie generator, hence everything.
    have hgen : (⊤ : Subalgebra R U) ≤ Subalgebra.centralizer R {u} := by
      rw [← adjoin_range_ι R L]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      refine (Subalgebra.mem_centralizer_iff R).mpr fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hx := h x
      rw [LieRing.of_associative_ring_bracket] at hx
      exact sub_eq_zero.mp hx
    exact Subalgebra.mem_center_iff.mpr fun b =>
      ((Subalgebra.mem_centralizer_iff R).mp (hgen (Set.mem_univ b)) u rfl).symm

variable {R L}

/-- **The iterated commutator with a Lie generator, read on the Lie generators.**  Bracketing
`n` times with `ι x` inside `U(L)` sends `ι y` to the image of the `n`-fold adjoint action of `x`
on `y`; that is, `ι` intertwines `LieAlgebra.ad R L x` with the inner derivation of `U(L)`
attached to `ι x`. -/
theorem ad_ι_pow_apply_ι (x y : L) (n : ℕ) :
    (LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n)
        (_root_.UniversalEnvelopingAlgebra.ι R y) =
      _root_.UniversalEnvelopingAlgebra.ι R ((LieAlgebra.ad R L x ^ n) y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply,
      ← LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R), ih, pow_succ,
      Module.End.mul_apply, LieAlgebra.ad_apply]

end Center

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0457

section TAF_LiteralSource_0458
/- Original module: TauCeti.Algebra.WordFiltration.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The word filtration generated by a linear map

Let `A` be an associative algebra and let `f : M →ₗ[R] A` be a linear family of elements of `A`.
This file defines `TauCeti.Algebra.wordFiltration f k`, the submodule spanned by products of at most
`k` elements in the range of `f`. This is the canonical increasing filtration on any algebra
generated by a linear family.

The construction is factored out of the Clifford and universal-enveloping-algebra filtrations. In
both cases the defining relations can lower word length, so the quotient is filtered rather than
graded by length. The generic construction records the properties independent of those relations:
monotonicity, multiplicativity, the first two steps, comparison with powers of the range of `f`,
and exhaustivity onto the subalgebra generated by `f`.

## Main definitions and results

* `TauCeti.Algebra.wordFiltration`: powers of the scalar-and-generator submodule.
* `TauCeti.Algebra.wordFiltration.previousRestricted`: the preceding step inside the current step.
* `TauCeti.Algebra.wordFiltration_eq_pow`: its defining equation as that power.
* `TauCeti.Algebra.wordFiltration_mul`: multiplication adds filtration degrees.
* `TauCeti.Algebra.span_prod_map_eq_wordFiltration`: words in a spanning family span each
  filtration step.
* `TauCeti.Algebra.span_prod_map_eq_range_pow`: words of length exactly `n` span the `n`-th power
  of the generator range.
* `TauCeti.Algebra.map_wordFiltration_le`: algebra maps sending generators into degree one preserve
  every filtration step.
* `TauCeti.Algebra.map_wordFiltration_eq`: an algebra map carrying the scalar-and-generator
  submodule exactly onto another does the same in every filtration degree.
* `TauCeti.Algebra.map_wordFiltration_eq_of_surjective`: a compatible algebra map carries every
  filtration step onto the corresponding target step when the map between generators is
  surjective.
* `TauCeti.Algebra.wordFiltration_eq_iSup_pow`: comparison with powers of `LinearMap.range f`.
* `TauCeti.Algebra.iSup_wordFiltration_eq_adjoin`: the filtration exhausts precisely the subalgebra
  generated by `f`.
* `TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top` and
  `TauCeti.Algebra.exists_mem_notMem_wordFiltrationPrevious`: elementwise consequences of
  exhaustivity, the second producing the leading degree of a nonzero element.
* `TauCeti.Algebra.wordFiltration.instGradedMonoid` and
  `TauCeti.Algebra.wordFiltration.instIsRingFiltration`: the bundled multiplicativity and
  filtration instances.
-/

public section

universe u v w

namespace TauCeti.Algebra

variable {R : Type u} {M : Type v} {A : Type w}
variable [CommSemiring R] [Semiring A] [_root_.Algebra R A] [AddCommMonoid M] [Module R M]

/-- The degree filtration generated by a linear map `f : M →ₗ[R] A`.

The `k`-th step is the `k`-th submodule power of the scalars together with the range of `f`. It is
equivalently the `R`-span of products of at most `k` elements in the range of `f`, including the
empty product; see `wordFiltration_le_iff`. -/
def wordFiltration (f : M →ₗ[R] A) (k : ℕ) : Submodule R A :=
  (1 ⊔ LinearMap.range f) ^ k

/-- The defining equation of the word filtration: degree `k` is the `k`-th submodule power of the
scalars together with the range of `f`. -/
theorem wordFiltration_eq_pow (f : M →ₗ[R] A) (k : ℕ) :
    wordFiltration f k = (1 ⊔ LinearMap.range f) ^ k :=
  (rfl)

/-- The step preceding degree `k`, with bottom in degree zero. -/
def wordFiltrationPrevious (f : M →ₗ[R] A) : ℕ → Submodule R A
  | 0 => ⊥
  | k + 1 => wordFiltration f k

/-- The preceding word filtration is trivial in degree zero. -/
@[simp]
theorem wordFiltrationPrevious_zero (f : M →ₗ[R] A) : wordFiltrationPrevious f 0 = ⊥ :=
  (rfl)

/-- In successor degree, the preceding word filtration is the previous filtration step. -/
@[simp]
theorem wordFiltrationPrevious_succ (f : M →ₗ[R] A) (k : ℕ) :
    wordFiltrationPrevious f (k + 1) = wordFiltration f k :=
  (rfl)

variable (f : M →ₗ[R] A)

/-- A word of length `n` lies in the `n`-th power of the range of the generators. -/
theorem prod_map_mem_range_pow (l : List M) :
    (l.map f).prod ∈ LinearMap.range f ^ l.length := by
  induction l with
  | nil => exact Submodule.one_le.1 le_rfl
  | cons m l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self f m) ih

open Pointwise in
/-- Words of length exactly `n` in a spanning family span the `n`-th power of the generator
range. -/
theorem span_prod_map_eq_range_pow_of_span {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (n : ℕ) :
    Submodule.span R {a | ∃ l : List ι, l.length = n ∧
      (l.map fun i ↦ f (e i)).prod = a} = LinearMap.range f ^ n := by
  have hrange : LinearMap.range f = Submodule.span R (Set.range fun i ↦ f (e i)) := by
    rw [LinearMap.range_eq_map, ← he, Submodule.map_span]
    congr 2
    ext a
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, ⟨i, rfl⟩, rfl⟩
  rw [hrange, Submodule.span_pow]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_pow]
  constructor
  · rintro ⟨l, rfl, rfl⟩
    exact ⟨fun i ↦ ⟨f (e l[(i : ℕ)]), Set.mem_range_self _⟩, congrArg List.prod
      (List.ofFn_getElem_eq_map l fun i ↦ f (e i))⟩
  · rintro ⟨g, rfl⟩
    choose i hi using fun j ↦ (Set.mem_range.mp (g j).2)
    exact ⟨List.ofFn i, List.length_ofFn, by
      rw [List.map_ofFn]
      simp [Function.comp_def, hi]⟩

/-- Words of length exactly `n` span the `n`-th power of the generator range. -/
theorem span_prod_map_eq_range_pow (n : ℕ) :
    Submodule.span R {a | ∃ l : List M, l.length = n ∧ (l.map f).prod = a} =
      LinearMap.range f ^ n := by
  have hid : Submodule.span R (Set.range (id : M → M)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  simpa only [id_eq] using span_prod_map_eq_range_pow_of_span f id hid n

/-- A word of length at most `k` belongs to the `k`-th word-filtration step. -/
theorem prod_map_mem_wordFiltration {k : ℕ} {l : List M} (hl : l.length ≤ k) :
    (l.map f).prod ∈ wordFiltration f k := by
  rw [wordFiltration]
  have hpow : LinearMap.range f ^ l.length ≤ (1 ⊔ LinearMap.range f) ^ k :=
    (pow_le_pow_left' le_sup_right l.length).trans (pow_le_pow_right' le_sup_left hl)
  exact hpow (prod_map_mem_range_pow f l)

/-- A submodule contains the `k`-th filtration step exactly when it contains every word of length
at most `k`. -/
theorem wordFiltration_le_iff {k : ℕ} {p : Submodule R A} :
    wordFiltration f k ≤ p ↔ ∀ l : List M, l.length ≤ k → (l.map f).prod ∈ p := by
  constructor
  · intro h l hl
    exact h (prod_map_mem_wordFiltration f hl)
  · intro h
    induction k generalizing p with
    | zero =>
        rw [wordFiltration, pow_zero]
        exact Submodule.one_le.2 (by simpa using h [] le_rfl)
    | succ k ih =>
        rw [wordFiltration, pow_succ', Submodule.sup_mul, Submodule.one_mul]
        refine sup_le (ih fun l hl => h l (hl.trans (Nat.le_succ k))) ?_
        rw [Submodule.mul_le]
        rintro _ ⟨m, rfl⟩ y hy
        apply ih (p := p.comap (LinearMap.mulLeft R (f m))) _ hy
        intro l hl
        rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
        rw [← List.prod_cons, ← List.map_cons]
        exact h (m :: l) (by simpa using Nat.succ_le_succ hl)

/-- Products of at most `k` images of a spanning family span the `k`-th word-filtration step. -/
theorem span_prod_map_eq_wordFiltration {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (k : ℕ) :
    Submodule.span R {a | ∃ word : List ι, word.length ≤ k ∧
      (word.map fun i ↦ f (e i)).prod = a} = wordFiltration f k := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro a ⟨word, hword, rfl⟩
    have h := prod_map_mem_wordFiltration f (l := word.map e) (by simpa using hword)
    simpa only [List.map_map, Function.comp_def, SetLike.mem_coe] using h
  · rw [wordFiltration_le_iff]
    intro word hword
    induction word generalizing k with
    | nil => exact Submodule.subset_span ⟨[], Nat.zero_le k, by simp⟩
    | cons x word ih =>
        cases k with
        | zero => simp at hword
        | succ k =>
            have htail : word.length ≤ k := by simpa using hword
            have ih := ih k htail
            have hx : x ∈ Submodule.span R (Set.range e) := by rw [he]; exact Submodule.mem_top
            refine Submodule.span_induction (p := fun y _ ↦
              f y * (word.map f).prod ∈ Submodule.span R
                {a | ∃ familyWord : List ι, familyWord.length ≤ k + 1 ∧
                  (familyWord.map fun i ↦ f (e i)).prod = a}) ?_ ?_ ?_ ?_ hx
            · intro y hy
              obtain ⟨i, rfl⟩ := hy
              have hcomap : (word.map f).prod ∈
                  (Submodule.span R {a | ∃ familyWord : List ι, familyWord.length ≤ k + 1 ∧
                    (familyWord.map fun i ↦ f (e i)).prod = a}).comap
                      (LinearMap.mulLeft R (f (e i))) := by
                refine (Submodule.span_le.mpr ?_) ih
                rintro a ⟨tail, htail, rfl⟩
                exact Submodule.subset_span
                  ⟨i :: tail, by simpa using Nat.succ_le_succ htail, by simp⟩
              simpa only [LinearMap.mulLeft_apply] using Submodule.mem_comap.mp hcomap
            · simp
            · intro y z _ _ hy hz
              simpa only [map_add, add_mul] using Submodule.add_mem _ hy hz
            · intro r y _ hy
              simpa only [map_smul, smul_mul_assoc] using Submodule.smul_mem _ r hy

section Map

variable {N : Type*} {B : Type*}
variable [Semiring B] [_root_.Algebra R B] [AddCommMonoid N] [Module R N]

/-- An algebra homomorphism that sends each source generator into target filtration degree one
preserves word-filtration degree. -/
theorem map_wordFiltration_le (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap ≤ wordFiltration f' k := by
  rw [wordFiltration_eq_pow, wordFiltration_eq_pow, Submodule.map_pow, Submodule.map_sup,
    Submodule.map_one]
  apply pow_le_pow_left'
  refine sup_le le_sup_left ?_
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  simpa only [wordFiltration, pow_one, AlgHom.toLinearMap_apply] using h m

/-- The membership form of `map_wordFiltration_le`: an algebra homomorphism that sends source
generators into target filtration degree one preserves every filtration step. -/
theorem map_mem_wordFiltration (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) {k : ℕ} {x : A}
    (hx : x ∈ wordFiltration f k) : g x ∈ wordFiltration f' k :=
  map_wordFiltration_le f g f' h k ⟨x, hx, rfl⟩

/-- An algebra homomorphism that maps one scalar-and-generator submodule exactly onto another
maps every corresponding word-filtration step exactly onto the other. -/
theorem map_wordFiltration_eq (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : (1 ⊔ LinearMap.range f).map g.toLinearMap = 1 ⊔ LinearMap.range f') (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap = wordFiltration f' k := by
  rw [wordFiltration_eq_pow, wordFiltration_eq_pow, Submodule.map_pow, h]

/-- A compatible algebra homomorphism maps every word-filtration step onto the corresponding
target step when its map on the generating modules is surjective. -/
theorem map_wordFiltration_eq_of_surjective (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (g : A →ₐ[R] B) (f' : N →ₗ[R] B)
    (h : g.toLinearMap.comp f = f'.comp q) (k : ℕ) :
    (wordFiltration f k).map g.toLinearMap = wordFiltration f' k := by
  apply map_wordFiltration_eq f g f' _ k
  rw [Submodule.map_sup, Submodule.map_one, ← LinearMap.range_comp, h,
    LinearMap.range_comp, LinearMap.range_eq_top_of_surjective q hq, Submodule.map_top]

end Map

/-- The word filtration is increasing. -/
theorem wordFiltration_mono : Monotone (wordFiltration f) := fun _ _ hij =>
  pow_le_pow_right' le_sup_left hij

/-- The zeroth word-filtration step consists of the scalars. -/
@[simp]
theorem wordFiltration_zero : wordFiltration f 0 = 1 := by
  simp [wordFiltration]

/-- The empty word puts `1` in every filtration step. -/
theorem one_mem_wordFiltration (k : ℕ) : (1 : A) ∈ wordFiltration f k := by
  simpa using prod_map_mem_wordFiltration f (l := []) (Nat.zero_le k)

/-- Every scalar belongs to every filtration step. -/
theorem algebraMap_mem_wordFiltration (r : R) (k : ℕ) :
    algebraMap R A r ∈ wordFiltration f k := by
  rw [_root_.Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (one_mem_wordFiltration f k)

/-- Each generator belongs to the first filtration step. -/
theorem apply_mem_wordFiltration_one (m : M) : f m ∈ wordFiltration f 1 := by
  simpa using prod_map_mem_wordFiltration f (l := [m]) le_rfl

/-- The range of the generating linear map lies in the first filtration step. -/
theorem range_le_wordFiltration_one : LinearMap.range f ≤ wordFiltration f 1 := by
  rintro _ ⟨m, rfl⟩
  exact apply_mem_wordFiltration_one f m

/-- Multiplication adds word-filtration degrees. In fact the product of the two filtration steps
equals the step in the sum degree. -/
theorem wordFiltration_mul (i j : ℕ) :
    wordFiltration f i * wordFiltration f j = wordFiltration f (i + j) := by
  rw [wordFiltration, wordFiltration, wordFiltration, pow_add]

/-- The elementwise multiplicativity of the word filtration. -/
theorem mul_mem_wordFiltration {i j : ℕ} {x y : A} (hx : x ∈ wordFiltration f i)
    (hy : y ∈ wordFiltration f j) : x * y ∈ wordFiltration f (i + j) := by
  rw [← wordFiltration_mul f i j]
  exact Submodule.mul_mem_mul hx hy

/-- Multiplying an element of degree strictly below `i` by an element of degree at most `j`
produces an element of degree strictly below `i + j`. -/
theorem mul_mem_wordFiltrationPrevious_left {i j : ℕ} {x y : A}
    (hx : x ∈ wordFiltrationPrevious f i) (hy : y ∈ wordFiltration f j) :
    x * y ∈ wordFiltrationPrevious f (i + j) := by
  cases i with
  | zero =>
      simp only [wordFiltrationPrevious_zero, Submodule.mem_bot] at hx
      subst x
      simp
  | succ i =>
      rw [wordFiltrationPrevious_succ] at hx
      rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc,
        wordFiltrationPrevious_succ]
      exact mul_mem_wordFiltration f hx hy

/-- Multiplying an element of degree at most `i` by an element of degree strictly below `j`
produces an element of degree strictly below `i + j`. -/
theorem mul_mem_wordFiltrationPrevious_right {i j : ℕ} {x y : A}
    (hx : x ∈ wordFiltration f i) (hy : y ∈ wordFiltrationPrevious f j) :
    x * y ∈ wordFiltrationPrevious f (i + j) := by
  cases j with
  | zero =>
      simp only [wordFiltrationPrevious_zero, Submodule.mem_bot] at hy
      subst y
      simp
  | succ j =>
      rw [wordFiltrationPrevious_succ] at hy
      rw [← Nat.add_assoc, wordFiltrationPrevious_succ]
      exact mul_mem_wordFiltration f hx hy

/-- The `n`-th power of the generator range lies in filtration degree `n`. -/
theorem range_pow_le_wordFiltration (n : ℕ) : LinearMap.range f ^ n ≤ wordFiltration f n :=
  pow_le_pow_left' le_sup_right n

/-- The `k`-th word-filtration step is the supremum of the powers of the generator range of degree
at most `k`. -/
theorem wordFiltration_eq_iSup_pow (k : ℕ) :
    wordFiltration f k = ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range f ^ (i : ℕ) := by
  refine le_antisymm ((wordFiltration_le_iff f).2 fun l hl => ?_) (iSup_le fun i => ?_)
  · exact Submodule.mem_iSup_of_mem ⟨l.length, hl⟩ (prod_map_mem_range_pow f l)
  · exact (range_pow_le_wordFiltration f i).trans (wordFiltration_mono f i.2)

/-- The successor filtration step adjoins words of exactly the new degree. -/
theorem wordFiltration_succ_eq_sup (k : ℕ) :
    wordFiltration f (k + 1) = wordFiltration f k ⊔ LinearMap.range f ^ (k + 1) := by
  refine le_antisymm ((wordFiltration_le_iff f).2 fun l hl => ?_)
    (sup_le (wordFiltration_mono f (Nat.le_succ k)) (range_pow_le_wordFiltration f (k + 1)))
  rcases eq_or_lt_of_le hl with h | h
  · exact Submodule.mem_sup_right (h ▸ prod_map_mem_range_pow f l)
  · exact Submodule.mem_sup_left (prod_map_mem_wordFiltration f (Nat.lt_succ_iff.1 h))

/-- The first filtration step consists of the scalars and the generator range. -/
@[simp]
theorem wordFiltration_one : wordFiltration f 1 = 1 ⊔ LinearMap.range f := by
  simp [wordFiltration]

/-- Powers of a filtration step multiply its degree. -/
theorem wordFiltration_pow (i n : ℕ) : wordFiltration f i ^ n = wordFiltration f (i * n) := by
  rw [wordFiltration, wordFiltration, pow_mul]

/-- The word filtration exhausts exactly the subalgebra generated by the range of `f`. -/
theorem iSup_wordFiltration_eq_adjoin :
    ⨆ k, wordFiltration f k = (_root_.Algebra.adjoin R (Set.range f)).toSubmodule := by
  refine le_antisymm (iSup_le fun _ => (wordFiltration_le_iff f).2 ?_) ?_
  · intro l hl
    clear hl
    induction l with
    | nil => simp
    | cons m l ih =>
      rw [List.map_cons, List.prod_cons]
      exact (_root_.Algebra.adjoin R (Set.range f)).mul_mem
        (_root_.Algebra.subset_adjoin (Set.mem_range_self m)) ih
  · rintro x hx
    refine _root_.Algebra.adjoin_induction (p := fun x _ => x ∈ ⨆ k, wordFiltration f k)
      (fun _ hx => ?_) (fun r => ?_) (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy)
      (fun _ _ _ _ hx hy => ?_) hx
    · obtain ⟨m, rfl⟩ := hx
      exact Submodule.mem_iSup_of_mem 1 (apply_mem_wordFiltration_one f m)
    · exact Submodule.mem_iSup_of_mem 0 (algebraMap_mem_wordFiltration f r 0)
    · rw [Submodule.mem_iSup_of_directed _ (wordFiltration_mono f).directed_le] at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      exact Submodule.mem_iSup_of_mem (i + j) (mul_mem_wordFiltration f hi hj)

/-- **An exhaustive word filtration covers the algebra elementwise**: if the filtration steps
supremum to `⊤`, every element lies in one of them. -/
theorem exists_mem_wordFiltration_of_iSup_eq_top (h : ⨆ k, wordFiltration f k = ⊤) (a : A) :
    ∃ k, a ∈ wordFiltration f k := by
  have hmem : a ∈ ⨆ k, wordFiltration f k := by
    rw [h]
    exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (wordFiltration_mono f).directed_le] at hmem

/-- **A nonzero element of an exhaustive word filtration has a leading degree**: a degree it
belongs to but whose preceding step it misses. -/
theorem exists_mem_notMem_wordFiltrationPrevious {a : A} (ha : a ≠ 0)
    (hex : ∃ k, a ∈ wordFiltration f k) :
    ∃ k, a ∈ wordFiltration f k ∧ a ∉ wordFiltrationPrevious f k := by
  classical
  obtain ⟨k, hk, hmin⟩ :
      ∃ k, a ∈ wordFiltration f k ∧ ∀ m, m < k → a ∉ wordFiltration f m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨k, hk, ?_⟩
  cases k with
  | zero => simpa using ha
  | succ m =>
      rw [wordFiltrationPrevious_succ]
      exact hmin m (Nat.lt_succ_self m)

namespace wordFiltration

/-- The preceding word-filtration step, viewed as a submodule of the current step. -/
abbrev previousRestricted (k : ℕ) :
    Submodule R (wordFiltration f k) :=
  (wordFiltrationPrevious f k).submoduleOf (wordFiltration f k)

/-- Membership in the restricted preceding step is ambient membership in the preceding step. -/
@[simp]
theorem mem_previousRestricted_iff (k : ℕ)
    (x : wordFiltration f k) :
    x ∈ previousRestricted f k ↔ (x : A) ∈ wordFiltrationPrevious f k :=
  Iff.rfl

/-- The restricted preceding word filtration is trivial in degree zero. -/
@[simp]
theorem previousRestricted_zero : previousRestricted f 0 = ⊥ := by
  ext x
  simp

/-- In successor degree, the restricted preceding word filtration is the previous step viewed
inside the current step. -/
@[simp]
theorem previousRestricted_succ (k : ℕ) :
    previousRestricted f (k + 1) =
      Submodule.comap (wordFiltration f (k + 1)).subtype (wordFiltration f k) := by
  simp only [previousRestricted, wordFiltrationPrevious_succ, Submodule.submoduleOf]

/-- Casting a filtered element between equal degrees does not change its value in the ambient
algebra. -/
@[simp]
theorem wordFiltration_coe_cast {i j : ℕ}
    (h : i = j) (x : wordFiltration f i) :
    ((cast (congrArg (fun k => ↥(wordFiltration f k)) h) x : wordFiltration f j) :
      A) = x := by
  subst j
  rfl

/-- Word filtrations are multiplicative families of submodules. -/
instance instGradedMonoid : SetLike.GradedMonoid (wordFiltration f) where
  one_mem := by simpa using one_mem_wordFiltration f 0
  mul_mem := fun {i j} {x y} hx hy =>
    mul_mem_wordFiltration (i := i) (j := j) (x := x) (y := y) f hx hy

/-- The word filtration, with the preceding step at each degree, is a ring filtration. -/
instance instIsRingFiltration :
    IsRingFiltration (wordFiltration f) (wordFiltrationPrevious f) where
  mono := wordFiltration_mono f
  is_le := by
    intro i j hij
    cases j with
    | zero => simp at hij
    | succ j =>
        exact wordFiltration_mono f (Nat.le_of_lt_succ hij)
  is_sup := by
    intro B j hB
    cases j with
    | zero => exact bot_le
    | succ j => exact hB j (Nat.lt_succ_self j)

end wordFiltration

end TauCeti.Algebra
end
end TAF_LiteralSource_0458

section TAF_LiteralSource_0459
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The PBW filtration of a universal enveloping algebra

This file constructs the Poincaré--Birkhoff--Witt filtration: the increasing filtration of
`UniversalEnvelopingAlgebra R L` by word length in the image of the canonical Lie map
`UniversalEnvelopingAlgebra.ι R`.

The defining relation

```text
ι(x) * ι(y) = ι(y) * ι(x) + ι([x,y])
```

replaces a degree-two commutator by a degree-one term. Thus word length gives a filtration, not a
grading. In the associated graded this degree drop makes the leading symbols commute; the comparison
with `SymmetricAlgebra R L` is not treated here.

Nothing in the construction is special to the enveloping algebra: `pbwFiltration` and
`pbwFiltrationPrevious` are `TauCeti.Algebra.wordFiltration` and
`TauCeti.Algebra.wordFiltrationPrevious` of `TauCeti/Algebra/WordFiltration/Basic.lean`,
specialized to `UniversalEnvelopingAlgebra.ι R`, exactly as `CliffordAlgebra.filtration` is that
same construction for `CliffordAlgebra.ι`. What is special to `U(L)` is the exhaustivity, which
comes from the tensor-algebra presentation.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration`: words of length at most `k` in the range of
  `UniversalEnvelopingAlgebra.ι R`.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_eq_pow`: its defining equation as the power of
  the scalar-and-generator submodule.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_mul`: multiplication adds degrees.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_zero` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_one`: the scalar and generator steps.
* `TauCeti.UniversalEnvelopingAlgebra.adjoin_image_ι_eq_top`: the image of any Lie generating set
  generates `U(L)` as an `R`-algebra.
* `TauCeti.UniversalEnvelopingAlgebra.iSup_pbwFiltration_eq_top`: the filtration is exhaustive.
* `TauCeti.UniversalEnvelopingAlgebra.exists_mem_pbwFiltration`: exhaustivity read elementwise.
* `TauCeti.UniversalEnvelopingAlgebra.instIsRingFiltration`: the bundled `IsRingFiltration`
  structure on `pbwFiltration`, with `pbwFiltrationPrevious` as its preceding-step family.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The PBW filtration on `U(L)`: its `k`-th step is spanned by products of at most `k` canonical
Lie generators.

This is `TauCeti.Algebra.wordFiltration` specialized to `UniversalEnvelopingAlgebra.ι R`; the
shared API is in `TauCeti/Algebra/WordFiltration/Basic.lean`. -/
def pbwFiltration (k : ℕ) : Submodule R U :=
  TauCeti.Algebra.wordFiltration (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k

/-- The PBW filtration is the word filtration generated by the canonical Lie map. -/
theorem pbwFiltration_def (k : ℕ) :
    pbwFiltration R L k =
      TauCeti.Algebra.wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k := (rfl)

/-- PBW filtration degree `k` is the `k`-th power of the scalars and canonical Lie generators. -/
theorem pbwFiltration_eq_pow (k : ℕ) :
    pbwFiltration R L k =
      (1 ⊔ LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap) ^ k :=
  TauCeti.Algebra.wordFiltration_eq_pow _ k

/-- The step preceding degree `k` in the PBW filtration, that is
`TauCeti.Algebra.wordFiltrationPrevious` specialized to `UniversalEnvelopingAlgebra.ι R`, with
bottom in degree zero. -/
def pbwFiltrationPrevious : ℕ → Submodule R U :=
  TauCeti.Algebra.wordFiltrationPrevious (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap

/-- The preceding PBW filtration is the preceding word filtration of the canonical Lie map. -/
theorem pbwFiltrationPrevious_def (k : ℕ) :
    pbwFiltrationPrevious R L k =
      TauCeti.Algebra.wordFiltrationPrevious
        (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k := (rfl)

/-- The preceding PBW filtration is trivial in degree zero. -/
@[simp]
theorem pbwFiltrationPrevious_zero : pbwFiltrationPrevious R L 0 = ⊥ :=
  TauCeti.Algebra.wordFiltrationPrevious_zero _

/-- In successor degree, the preceding PBW filtration is the previous filtration step. -/
@[simp]
theorem pbwFiltrationPrevious_succ (k : ℕ) :
    pbwFiltrationPrevious R L (k + 1) = pbwFiltration R L k :=
  TauCeti.Algebra.wordFiltrationPrevious_succ _ k

/-- A word of at most `k` canonical Lie generators lies in PBW filtration degree `k`. -/
theorem prod_map_ι_mem_pbwFiltration {k : ℕ} {l : List L} (hl : l.length ≤ k) :
    (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈ pbwFiltration R L k := by
  -- The generic lemma is about the underlying linear map, so name the coercion explicitly.
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.prod_map_mem_wordFiltration _ hl

/-- A submodule contains the `k`-th PBW filtration step exactly when it contains every word of
length at most `k` in the canonical Lie generators. -/
theorem pbwFiltration_le_iff {k : ℕ} {p : Submodule R U} :
    pbwFiltration R L k ≤ p ↔
      ∀ l : List L, l.length ≤ k → (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈ p := by
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.wordFiltration_le_iff _

/-- The PBW filtration is increasing. -/
theorem pbwFiltration_mono : Monotone (pbwFiltration R L) :=
  TauCeti.Algebra.wordFiltration_mono _

/-- PBW filtration degree zero consists of scalars. -/
@[simp]
theorem pbwFiltration_zero : pbwFiltration R L 0 = 1 :=
  TauCeti.Algebra.wordFiltration_zero _

/-- The empty word puts `1` in every PBW filtration step. -/
theorem one_mem_pbwFiltration (k : ℕ) : (1 : U) ∈ pbwFiltration R L k :=
  TauCeti.Algebra.one_mem_wordFiltration _ k

/-- Scalars belong to every PBW filtration step. -/
theorem algebraMap_mem_pbwFiltration (r : R) (k : ℕ) :
    algebraMap R U r ∈ pbwFiltration R L k :=
  TauCeti.Algebra.algebraMap_mem_wordFiltration _ r k

/-- A canonical Lie generator has PBW filtration degree at most one. -/
theorem ι_mem_pbwFiltration_one (x : L) :
    _root_.UniversalEnvelopingAlgebra.ι R x ∈ pbwFiltration R L 1 := by
  rw [← LieHom.coe_toLinearMap]
  exact TauCeti.Algebra.apply_mem_wordFiltration_one _ x

/-- The range of the canonical Lie map lies in the first PBW filtration step. -/
theorem ι_range_le_pbwFiltration_one :
    LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ≤ pbwFiltration R L 1 :=
  TauCeti.Algebra.range_le_wordFiltration_one _

/-- Multiplication adds PBW filtration degrees. -/
theorem pbwFiltration_mul (i j : ℕ) :
    pbwFiltration R L i * pbwFiltration R L j = pbwFiltration R L (i + j) :=
  TauCeti.Algebra.wordFiltration_mul _ i j

/-- The elementwise multiplicativity of the PBW filtration. -/
theorem mul_mem_pbwFiltration {i j : ℕ} {x y : U} (hx : x ∈ pbwFiltration R L i)
    (hy : y ∈ pbwFiltration R L j) : x * y ∈ pbwFiltration R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltration _ hx hy

/-- Multiplication preserves a strict degree drop in the left factor of the PBW filtration. -/
theorem mul_mem_pbwFiltrationPrevious_left {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltrationPrevious R L i) (hy : y ∈ pbwFiltration R L j) :
    x * y ∈ pbwFiltrationPrevious R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_left _ hx hy

/-- Multiplication preserves a strict degree drop in the right factor of the PBW filtration. -/
theorem mul_mem_pbwFiltrationPrevious_right {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltration R L i) (hy : y ∈ pbwFiltrationPrevious R L j) :
    x * y ∈ pbwFiltrationPrevious R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_right _ hx hy

/-- Iterating `pbwFiltration_mul`: the `n`-th submodule power of the `i`-th step is the `i * n`-th
step. -/
theorem pbwFiltration_pow (i n : ℕ) :
    pbwFiltration R L i ^ n = pbwFiltration R L (i * n) :=
  TauCeti.Algebra.wordFiltration_pow _ i n

/-- The `k`-th PBW filtration step is the supremum of the powers of the canonical generator range
of degree at most `k`. -/
theorem pbwFiltration_eq_iSup_pow (k : ℕ) :
    pbwFiltration R L k =
      ⨆ i : {i : ℕ // i ≤ k},
        LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ^ (i : ℕ) :=
  TauCeti.Algebra.wordFiltration_eq_iSup_pow _ k

/-- The successor PBW step adjoins words of exactly the new degree. -/
theorem pbwFiltration_succ_eq_sup (k : ℕ) :
    pbwFiltration R L (k + 1) =
      pbwFiltration R L k ⊔
        LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap ^ (k + 1) :=
  TauCeti.Algebra.wordFiltration_succ_eq_sup _ k

/-- PBW filtration degree one consists of the scalars and the canonical Lie generators. -/
@[simp]
theorem pbwFiltration_one :
    pbwFiltration R L 1 = 1 ⊔ LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap :=
  TauCeti.Algebra.wordFiltration_one _

/-- **A Lie generating set generates the enveloping algebra.** If `S` generates `L` as a Lie
algebra, then the image of `S` under the canonical map generates `U(L)` as an `R`-algebra.

Only the associative subalgebra generated by the image is involved, so no linear independence or
finiteness of `S` is needed. -/
theorem adjoin_image_ι_eq_top {S : Set L} (hS : LieSubalgebra.lieSpan R L S = ⊤) :
    _root_.Algebra.adjoin R (⇑(_root_.UniversalEnvelopingAlgebra.ι R) '' S) =
      (⊤ : Subalgebra R U) := by
  have hle : LieSubalgebra.lieSpan R L S ≤
      (lieSubalgebraOfSubalgebra R U (_root_.Algebra.adjoin R
        (⇑(_root_.UniversalEnvelopingAlgebra.ι R) '' S))).comap
          (_root_.UniversalEnvelopingAlgebra.ι R) :=
    LieSubalgebra.lieSpan_le.2 fun y hy =>
      (LieSubalgebra.mem_comap _ _).2 (_root_.Algebra.subset_adjoin ⟨y, hy, rfl⟩)
  rw [hS] at hle
  rw [eq_top_iff, ← adjoin_range_ι R L]
  refine _root_.Algebra.adjoin_le ?_
  rintro _ ⟨x, rfl⟩
  exact (LieSubalgebra.mem_comap _ _).1 (hle (LieSubalgebra.mem_top x))

/-- **The PBW filtration is exhaustive.** The canonical generators generate `U(L)` as an algebra,
so every element is a combination of words of some finite length. -/
theorem iSup_pbwFiltration_eq_top : ⨆ k, pbwFiltration R L k = ⊤ := by
  have h : ⨆ k, pbwFiltration R L k =
      (_root_.Algebra.adjoin R
        (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap)).toSubmodule :=
    TauCeti.Algebra.iSup_wordFiltration_eq_adjoin _
  rw [h, LieHom.coe_toLinearMap, adjoin_range_ι, _root_.Algebra.top_toSubmodule]

/-- **Every element of the enveloping algebra lies in some PBW filtration step**, the elementwise
form of `TauCeti.UniversalEnvelopingAlgebra.iSup_pbwFiltration_eq_top`. -/
theorem exists_mem_pbwFiltration (a : U) : ∃ k, a ∈ pbwFiltration R L k :=
  TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top _ (iSup_pbwFiltration_eq_top R L) a

/-- The PBW filtration carries Mathlib's bundled ring-filtration structure. -/
instance instIsRingFiltration :
    IsRingFiltration (pbwFiltration R L) (pbwFiltrationPrevious R L) :=
  TauCeti.Algebra.wordFiltration.instIsRingFiltration _

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0459

section TAF_LiteralSource_0460
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Functoriality of universal enveloping algebras

A homomorphism of Lie algebras induces an algebra homomorphism of their universal enveloping
algebras. This file constructs that map directly from Mathlib's universal property and proves its
characteristic equation on the canonical Lie generators, its identity and composition laws, and
its behaviour on split monomorphisms and split epimorphisms. A Lie algebra equivalence consequently
induces an algebra equivalence of universal enveloping algebras.

The split-morphism results avoid any freeness or Poincare--Birkhoff--Witt hypothesis: a chosen
one-sided inverse of a Lie homomorphism lifts to the same one-sided inverse on enveloping algebras.
In particular, the equivalence construction is available over an arbitrary commutative ring. No
Poincare--Birkhoff--Witt theorem or injectivity of the canonical Lie map is asserted here.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.map`: the algebra homomorphism induced by a Lie algebra
  homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.mapEquiv`: the algebra equivalence induced by a Lie algebra
  equivalence.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_ι`: the induced map agrees with the original Lie
  homomorphism on the canonical generators.
* `TauCeti.UniversalEnvelopingAlgebra.map_id` and
  `TauCeti.UniversalEnvelopingAlgebra.map_comp`: enveloping-algebra maps are functorial.
* `TauCeti.UniversalEnvelopingAlgebra.map_surjective_of_surjective`: surjective Lie maps induce
  surjective enveloping-algebra maps.
* `TauCeti.UniversalEnvelopingAlgebra.map_injective_of_leftInverse` and
  `TauCeti.UniversalEnvelopingAlgebra.map_surjective_of_rightInverse`: split morphisms remain split
  after passing to enveloping algebras.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The algebra homomorphism of universal enveloping algebras induced by a Lie algebra
homomorphism.

It is the unique algebra homomorphism sending the canonical generator `ι R x` to `ι R (f x)`;
`map_ι` is the corresponding computation rule and `map_unique` is the universal property in that
form. -/
noncomputable def map (f : LieHom R L M) :
    _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  _root_.UniversalEnvelopingAlgebra.lift R
    ((_root_.UniversalEnvelopingAlgebra.ι R).comp f)

/-- An enveloping-algebra map acts on the canonical Lie generators by the original Lie
homomorphism. -/
-- `simp`-normal form is `map_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem map_ι (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x) := by
  rw [map, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact LieHom.comp_apply _ _ _

/-- The `simp`-normal form of `map_ι`, stated for the canonical generators as `simp` writes them:
`ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem map_ι' (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (f x)) := by
  simpa using map_ι R f x

/-- An algebra homomorphism out of an enveloping algebra is the map induced by `f` exactly when
it sends every canonical generator to the image prescribed by `f`. -/
theorem map_unique (f : LieHom R L M)
    (g : _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M) :
    (∀ x, g (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x)) ↔ g = map R f := by
  rw [map]
  refine Iff.trans ?_
    (_root_.UniversalEnvelopingAlgebra.lift_unique R
      ((_root_.UniversalEnvelopingAlgebra.ι R).comp f) g)
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- The identity Lie homomorphism induces the identity algebra homomorphism. -/
@[simp]
theorem map_id :
    map R (LieHom.id : LieHom R L L) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.id_apply, AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.id_apply]

/-- Composition of Lie homomorphisms becomes composition of the induced algebra homomorphisms. -/
@[simp]
theorem map_comp (f : LieHom R L M) (g : LieHom R M N) :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply]

/-- For Lie subalgebras `A ≤ B` of `L`, mapping `U(A)` into `U(B)` and then into `U(L)` is the map
induced by the inclusion of `A` in `L`. -/
@[simp]
theorem map_incl_comp_map_inclusion {A B : LieSubalgebra R L} (h : A ≤ B) :
    (map R B.incl).comp (map R (LieSubalgebra.inclusion h)) = map R A.incl := by
  rw [← map_comp]
  -- `B.incl ∘ inclusion h` and `A.incl` are both the coercion `A → L`
  rfl

/-- A left inverse of Lie homomorphisms induces a left inverse of the corresponding
enveloping-algebra maps. -/
theorem map_leftInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : g.comp f = LieHom.id) : Function.LeftInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R g).comp (map R f) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A right inverse of Lie homomorphisms induces a right inverse of the corresponding
enveloping-algebra maps. -/
theorem map_rightInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : f.comp g = LieHom.id) : Function.RightInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R f).comp (map R g) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R M) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A split monomorphism of Lie algebras induces an injective homomorphism of enveloping
algebras. -/
theorem map_injective_of_leftInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : g.comp f = LieHom.id) : Function.Injective (map R f) :=
  (map_leftInverse R h).injective

/-- A surjective Lie homomorphism induces a surjective homomorphism of universal enveloping
algebras. -/
theorem map_surjective_of_surjective (f : LieHom R L M) (hf : Function.Surjective f) :
    Function.Surjective (map R f) := by
  intro y
  induction y using induction_ι R M with
  | ι y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨_root_.UniversalEnvelopingAlgebra.ι R x, map_ι R f x⟩
  | algebraMap r =>
      exact ⟨algebraMap R (_root_.UniversalEnvelopingAlgebra R L) r, (map R f).commutes r⟩
  | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, map_add (map R f) x y⟩
  | mul a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x * y, map_mul (map R f) x y⟩

/-- A split epimorphism of Lie algebras induces a surjective homomorphism of enveloping
algebras. -/
theorem map_surjective_of_rightInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : f.comp g = LieHom.id) : Function.Surjective (map R f) :=
  map_surjective_of_surjective R f fun y ↦
    ⟨g y, by
      simpa only [LieHom.comp_apply, LieHom.id_apply] using
        DFunLike.congr_fun h y⟩

/-- A Lie algebra equivalence induces an algebra equivalence of universal enveloping algebras. -/
noncomputable def mapEquiv (e : LieEquiv R L M) :
    _root_.UniversalEnvelopingAlgebra R L ≃ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  AlgEquiv.ofAlgHom (map R e.toLieHom) (map R e.symm.toLieHom)
    (by
      rw [← map_comp]
      have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.apply_symm_apply
      rw [h, map_id])
    (by
      rw [← map_comp]
      have h : e.symm.toLieHom.comp e.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.symm_apply_apply
      rw [h, map_id])

/-- The algebra homomorphism underlying `mapEquiv` is the map induced by the underlying Lie
homomorphism. -/
@[simp]
theorem mapEquiv_toAlgHom (e : LieEquiv R L M) :
    (mapEquiv R e).toAlgHom = map R e.toLieHom :=
  by rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The algebra equivalence induced by a Lie equivalence acts on canonical generators by that Lie
equivalence. -/
-- `simp`-normal form is `mapEquiv_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem mapEquiv_ι (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (e x) := by
  rw [← AlgEquiv.toAlgHom_apply, mapEquiv_toAlgHom, map_ι, LieEquiv.coe_coe]

/-- The `simp`-normal form of `mapEquiv_ι`, stated for the canonical generators as `simp` writes
them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem mapEquiv_ι' (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (e x)) := by
  simpa using mapEquiv_ι R e x

/-- Passing the inverse Lie equivalence to enveloping algebras gives the inverse algebra
equivalence. -/
@[simp]
theorem mapEquiv_symm (e : LieEquiv R L M) :
    (mapEquiv R e).symm = mapEquiv R e.symm :=
  by
    apply AlgEquiv.ext
    intro a
    rw [mapEquiv, AlgEquiv.ofAlgHom_symm]
    simp only [AlgEquiv.ofAlgHom_apply, mapEquiv, LieEquiv.symm_symm]

/-- The identity Lie equivalence induces the identity algebra equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv R (LieEquiv.refl : LieEquiv R L L) = AlgEquiv.refl :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have hrefl : (LieEquiv.refl : LieEquiv R L L).toLieHom = LieHom.id := by
      apply LieHom.ext
      intro x
      rfl
    rw [hrefl, map_id, AlgEquiv.refl_toAlgHom]

/-- Composition of Lie equivalences becomes composition of the induced algebra equivalences. -/
@[simp]
theorem mapEquiv_trans (e : LieEquiv R L M) (d : LieEquiv R M N) :
    (mapEquiv R e).trans (mapEquiv R d) = mapEquiv R (e.trans d) :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have htrans : ((mapEquiv R e).trans (mapEquiv R d)).toAlgHom =
        (mapEquiv R d).toAlgHom.comp (mapEquiv R e).toAlgHom := by
      apply AlgHom.ext
      intro a
      simp only [AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply, AlgHom.comp_apply]
    rw [htrans, mapEquiv_toAlgHom, mapEquiv_toAlgHom]
    have hLie : (e.trans d).toLieHom = d.toLieHom.comp e.toLieHom := by
      apply LieHom.ext
      intro x
      simp only [LieEquiv.trans_apply, LieHom.comp_apply, LieEquiv.coe_coe]
    rw [hLie, map_comp]

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0460

section TAF_LiteralSource_0461
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Permuting PBW words modulo lower filtration

This file proves the first consequence of the defining relation of a universal enveloping algebra
for its associated graded. If two words in the canonical generators differ only by a permutation,
then their difference has filtration degree strictly below their common word length. In particular,
the leading term of a word is unchanged when the word is sorted.

An adjacent exchange is the mathematical heart of the proof:

```text
ι(x) * ι(y) - ι(y) * ι(x) = ι([x,y]).
```

The left side has word length two while the right side has word length one. Multiplying by the
unchanged suffix preserves this one-degree drop. Induction on `List.Perm` then gives the result for
an arbitrary permutation.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial`: the product of a word in a chosen family of
  Lie-algebra elements.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwMonomial`: induced maps act factorwise on PBW
  monomials.
* `TauCeti.UniversalEnvelopingAlgebra.prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm`:
  permuted words in canonical generators differ by a lower-filtration term.
* `pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm`:
  the same statement for words in an indexed family.
* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`:
  every word has the same leading term as its ordered version.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Exchanging the two leading generators of a word lowers the PBW filtration degree of the
difference by one. -/
private theorem prod_map_ι_sub_swap_mem_pbwFiltrationPrevious (x y : L) (l : List L) :
    ((x :: y :: l).map ⇑ι).prod - ((y :: x :: l).map ⇑ι).prod ∈
      pbwFiltrationPrevious R L (x :: y :: l).length := by
  simp only [List.length_cons, pbwFiltrationPrevious_succ, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← mul_assoc, ← sub_mul,
    ← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]
  simpa only [Nat.add_comm] using
    mul_mem_pbwFiltration (R := R) (L := L) (ι_mem_pbwFiltration_one R L ⁅x, y⁆)
      (prod_map_ι_mem_pbwFiltration R L le_rfl)

/-- **Permuting a word does not change its leading PBW term.** The products of two permuted lists
of canonical generators differ by an element of degree strictly below their common length. -/
theorem prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm {l₁ l₂ : List L}
    (h : l₁.Perm l₂) :
    (l₁.map ⇑ι).prod - (l₂.map ⇑ι).prod ∈ pbwFiltrationPrevious R L l₁.length := by
  induction h with
  | nil => simp
  | cons x h ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [← mul_sub]
      simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
        mul_mem_pbwFiltrationPrevious_right (R := R) (L := L)
          (ι_mem_pbwFiltration_one R L x) ih
  | swap x y l => exact prod_map_ι_sub_swap_mem_pbwFiltrationPrevious R L y x l
  | trans h₁ _ ih₁ ih₂ =>
      rw [← h₁.length_eq] at ih₂
      simpa only [sub_add_sub_cancel] using
        (pbwFiltrationPrevious R L _).add_mem ih₁ ih₂

variable {ιIndex : Type w}

/-- The PBW monomial attached to a word of indices in a family `e : ιIndex → L`. No ordering or
linear-independence hypothesis on the family is needed. -/
def pbwMonomial (e : ιIndex → L) (word : List ιIndex) :
    _root_.UniversalEnvelopingAlgebra R L :=
  ((word.map e).map ⇑ι).prod

@[simp]
theorem pbwMonomial_nil (e : ιIndex → L) : pbwMonomial R L e [] = 1 := by
  simp [pbwMonomial]

@[simp]
theorem pbwMonomial_cons (e : ιIndex → L) (i : ιIndex) (word : List ιIndex) :
    pbwMonomial R L e (i :: word) = ι (e i) * pbwMonomial R L e word := by
  simp [pbwMonomial]

/-- A PBW monomial is the product of the corresponding canonical Lie generators. -/
theorem pbwMonomial_def (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word = ((word.map e).map ⇑ι).prod := by
  induction word with
  | nil => exact pbwMonomial_nil R L e
  | cons i word ih => simp only [pbwMonomial_cons, List.map_cons, List.prod_cons, ih]

section Map

variable (S : Type u) [CommRing S]
variable {A : Type v} {B : Type x}
variable [LieRing A] [LieAlgebra S A]
variable [LieRing B] [LieAlgebra S B]

/-- An induced enveloping-algebra map applies the Lie homomorphism to every factor of a PBW
monomial. -/
@[simp]
theorem map_pbwMonomial (f : LieHom S A B) (e : ιIndex → A) (word : List ιIndex) :
    map S f (pbwMonomial S A e word) = pbwMonomial S B (fun i ↦ f (e i)) word := by
  rw [pbwMonomial_def, pbwMonomial_def, map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  exact map_ι S f (e i)

end Map

@[simp]
theorem pbwMonomial_append (e : ιIndex → L) (word₁ word₂ : List ιIndex) :
    pbwMonomial R L e (word₁ ++ word₂) =
      pbwMonomial R L e word₁ * pbwMonomial R L e word₂ := by
  simp [pbwMonomial]

/-- A PBW monomial belongs to the filtration step given by the length of its word. -/
theorem pbwMonomial_mem_pbwFiltration (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word ∈ pbwFiltration R L word.length := by
  rw [pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_mem_pbwFiltration R L (l := word.map e) (by simp)

/-- Permuted words in any indexed family give PBW monomials with the same leading term. -/
theorem pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm
    (e : ιIndex → L) {word₁ word₂ : List ιIndex} (h : word₁.Perm word₂) :
    pbwMonomial R L e word₁ - pbwMonomial R L e word₂ ∈
      pbwFiltrationPrevious R L word₁.length := by
  rw [pbwMonomial_def, pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L (h.map e)

/-- Sorting the indices of a PBW monomial by a decidable relation preserves its leading term. This
is the form used to span the associated graded by ordered monomials. -/
theorem pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
    (r : ιIndex → ιIndex → Prop) [DecidableRel r] (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word - pbwMonomial R L e (word.insertionSort r) ∈
      pbwFiltrationPrevious R L word.length :=
  pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm R L e
    (List.perm_insertionSort r word).symm

/-- Relabelling the indices of an exponent vector along an order embedding relabels its ordered
PBW monomial. -/
theorem pbwMonomial_sort_toMultiset_mapDomain {ι₁ ι₂ : Type*} [LinearOrder ι₁]
    [LinearOrder ι₂] (g : ι₁ ↪o ι₂) (e : ι₂ → L) (n : ι₁ →₀ ℕ) :
    pbwMonomial R L e ((n.mapDomain g).toMultiset.sort (· ≤ ·)) =
      pbwMonomial R L (e ∘ g) (n.toMultiset.sort (· ≤ ·)) := by
  rw [← Finsupp.toMultiset_map, ← Multiset.map_sort g n.toMultiset (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ ↦ g.le_iff_le.symm)]
  simp only [pbwMonomial_def, List.map_map, Function.comp_def]

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0461

section TAF_LiteralSource_0462
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Evaluation -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Evaluation of the PBW polynomial representation

The polynomial representation attached to an ordered basis of a Lie algebra gives a linear map
from its enveloping algebra to polynomials by applying an operator to `1`. An ordered word of
basis vectors evaluates to the monomial with exactly those multiplicities. This normalization
identifies the ordered PBW basis with the usual polynomial monomials as modules.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace Module.Basis

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Apply the PBW polynomial representation of the enveloping algebra to the constant `1`. -/
noncomputable def pbwEval : _root_.UniversalEnvelopingAlgebra R L →ₗ[R] MvPolynomial ι R :=
  LinearMap.applyₗ (1 : MvPolynomial ι R) ∘ₗ
    (_root_.UniversalEnvelopingAlgebra.lift R b.pbwPolynomialRep).toLinearMap

@[simp]
theorem pbwEval_one : b.pbwEval 1 = 1 := by
  simp [pbwEval]

/-- Left multiplication by a generator becomes its action on polynomials. -/
theorem pbwEval_ι_mul (x : L) (a : _root_.UniversalEnvelopingAlgebra R L) :
    b.pbwEval (_root_.UniversalEnvelopingAlgebra.ι R x * a) =
      b.pbwPolynomialRep x (b.pbwEval a) := by
  simp [pbwEval]

/-- An ordered word evaluates to the polynomial monomial with the same multiplicities. -/
theorem pbwEval_pbwMonomial {word : List ι} (hword : word.Pairwise (· ≤ ·)) :
    b.pbwEval (pbwMonomial R L b word) = monomial (Multiset.toFinsupp (word : Multiset ι)) 1 := by
  induction word with
  | nil => simp [Multiset.toFinsupp_zero]
  | cons i word ih =>
      obtain ⟨hle, htail⟩ := List.pairwise_cons.1 hword
      rw [pbwMonomial_cons, pbwEval_ι_mul, ih htail,
        pbwPolynomialRep_basis_monomial_of_le b 1 (fun j hj ↦ hle j (by simpa using hj))]
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton, X, monomial_mul_monomial, one_mul]

end Module.Basis
end
end TAF_LiteralSource_0462

section TAF_LiteralSource_0463
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Ordered monomials span the PBW filtration

Let `e : ι → L` be a linearly ordered spanning family of a Lie algebra. This file proves that the
degree-`k` Poincaré--Birkhoff--Witt filtration of `UniversalEnvelopingAlgebra R L` is spanned by the
monomials

```text
ι(e(i₁)) ⋯ ι(e(iₙ)),    i₁ ≤ ⋯ ≤ iₙ,    n ≤ k.
```

There are two steps. First, `span_prod_map_eq_wordFiltration` expands arbitrary Lie-algebra words in
the spanning family. Second, sorting a word in that family changes it only by a term in the
preceding filtration step, by
`pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`. Induction on the filtration degree then
absorbs this error into shorter ordered monomials.

For an arbitrary Lie homomorphism, the induced enveloping-algebra map sends the ordered monomials
in a family, and their span, exactly onto those for the image family.

This is the spanning half of the PBW basis theorem; linear independence of the ordered monomials is
not proved here.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.orderedPBWMonomials`: the ordered monomials of length at
  most a specified degree.
* `TauCeti.UniversalEnvelopingAlgebra.map_span_orderedPBWMonomials`: induced maps carry their
  spans onto the spans of the corresponding image-family monomials.
* `TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`: these monomials
  span exactly the corresponding PBW filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.span_iUnion_orderedPBWMonomials_eq_top`: all ordered monomials
  span the universal enveloping algebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section OrderedWords

variable {ι : Type w} [LE ι] (e : ι → L)

/-- Ordered PBW monomials in a family indexed by an ordered type, of word length at most `k`. -/
def orderedPBWMonomials (k : ℕ) : Set U :=
  {a | ∃ word : List ι,
    word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a}

/-- Membership in `orderedPBWMonomials`, in terms of an ordered word of family indices. -/
@[simp]
theorem mem_orderedPBWMonomials_iff {k : ℕ} {a : U} :
    a ∈ orderedPBWMonomials R L e k ↔
      ∃ word : List ι,
        word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a :=
  Iff.rfl

/-- An ordered family word of length at most `k` gives an ordered PBW monomial of degree at most
`k`. -/
theorem pbwMonomial_mem_orderedPBWMonomials {k : ℕ} {word : List ι}
    (hsorted : word.Pairwise (· ≤ ·)) (hword : word.length ≤ k) :
    pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
  ⟨word, hsorted, hword, rfl⟩

/-- Increasing the degree bound enlarges the set of ordered PBW monomials. -/
theorem orderedPBWMonomials_mono : Monotone (orderedPBWMonomials R L e) := by
  intro i j hij a
  rintro ⟨word, hsorted, hlength, rfl⟩
  exact ⟨word, hsorted, hlength.trans hij, rfl⟩

/-- Every ordered PBW monomial of degree at most `k` lies in the `k`-th PBW filtration step. -/
theorem orderedPBWMonomials_subset_pbwFiltration (k : ℕ) :
    orderedPBWMonomials R L e k ⊆ pbwFiltration R L k := by
  rintro a ⟨word, -, hword, rfl⟩
  exact (pbwFiltration_mono R L hword) (pbwMonomial_mem_pbwFiltration R L e word)

/-- The only ordered PBW monomial of degree zero is the empty monomial `1`. -/
@[simp]
theorem orderedPBWMonomials_zero : orderedPBWMonomials R L e 0 = {1} := by
  ext a
  constructor
  · rintro ⟨word, -, hword, rfl⟩
    rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hword), pbwMonomial_nil]
    exact Set.mem_singleton 1
  · rintro rfl
    exact ⟨[], List.Pairwise.nil, le_rfl, pbwMonomial_nil R L e⟩

end OrderedWords

section Map

variable {M : Type x} [LieRing M] [LieAlgebra R M]
variable {ι : Type w} [LE ι]

/-- An induced enveloping-algebra map sends the ordered monomials in a family exactly to the
ordered monomials in its image family. This statement does not require the Lie map or the family
to be surjective. -/
@[simp]
theorem image_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    map R f '' orderedPBWMonomials R L e k =
      orderedPBWMonomials R M (fun i ↦ f (e i)) k := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [mem_orderedPBWMonomials_iff] at hb ⊢
    obtain ⟨word, hordered, hlength, rfl⟩ := hb
    exact ⟨word, hordered, hlength, (map_pbwMonomial R f e word).symm⟩
  · rw [mem_orderedPBWMonomials_iff]
    rintro ⟨word, hordered, hlength, rfl⟩
    have hsource : pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
      (mem_orderedPBWMonomials_iff R L e).2 ⟨word, hordered, hlength, rfl⟩
    exact ⟨pbwMonomial R L e word, hsource, map_pbwMonomial R f e word⟩

/-- The induced enveloping-algebra map carries the span of the ordered monomials in a family
onto the span of the corresponding ordered monomials in its image family. -/
@[simp]
theorem map_span_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    (Submodule.span R (orderedPBWMonomials R L e k)).map (map R f).toLinearMap =
      Submodule.span R (orderedPBWMonomials R M (fun i ↦ f (e i)) k) := by
  rw [Submodule.map_span, AlgHom.coe_toLinearMap, image_orderedPBWMonomials R L f e k]

end Map

section Spanning

variable {ι : Type w} [LinearOrder ι] (e : ι → L)

/-- **Ordered PBW monomials span the PBW filtration.** For a linearly ordered spanning family `e`
in `L`, the monomials in nondecreasing family elements of length at most `k` span precisely
filtration degree `k` of `UniversalEnvelopingAlgebra R L`.

This is the spanning half of PBW. The reverse information needed for a basis is linear independence,
which comes from identifying the associated graded algebra with `SymmetricAlgebra R L`. -/
theorem span_orderedPBWMonomials_eq_pbwFiltration
    (he : Submodule.span R (Set.range e) = ⊤) (k : ℕ) :
    Submodule.span R (orderedPBWMonomials R L e k) = pbwFiltration R L k := by
  refine le_antisymm (Submodule.span_le.mpr
    (orderedPBWMonomials_subset_pbwFiltration R L e k)) ?_
  induction k with
  | zero =>
      rw [pbwFiltration_zero, orderedPBWMonomials_zero, Submodule.one_le]
      exact Submodule.subset_span (Set.mem_singleton 1)
  | succ k ih =>
      -- Expand arbitrary generator words in the spanning family, then sort the resulting words.
      have hfiltration : TauCeti.Algebra.wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (k + 1) =
          pbwFiltration R L (k + 1) := by
        rw [TauCeti.Algebra.wordFiltration_eq_pow, pbwFiltration_eq_pow]
      rw [← hfiltration, ← TauCeti.Algebra.span_prod_map_eq_wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap e he (k + 1),
        Submodule.span_le]
      rintro a ⟨word, hword, rfl⟩
      have hp :
          (word.map fun i ↦
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (e i)).prod =
            pbwMonomial R L e word := by
        rw [pbwMonomial_def]
        simp only [List.map_map, Function.comp_def, LieHom.coe_toLinearMap]
      rw [hp]
      let sorted := word.insertionSort (· ≤ ·)
      have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
      have hlength : sorted.length ≤ k + 1 := by
        simpa [sorted] using hword
      have hsorted_mem : pbwMonomial R L e sorted ∈
          Submodule.span R (orderedPBWMonomials R L e (k + 1)) :=
        Submodule.subset_span
          (pbwMonomial_mem_orderedPBWMonomials R L e hsorted hlength)
      cases word with
      | nil =>
          simpa [sorted] using hsorted_mem
      | cons head tail =>
          have htail : tail.length ≤ k := by simpa using hword
          have hdiff :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                pbwFiltration R L tail.length := by
            have h := pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
              R L (· ≤ ·) e (head :: tail)
            rw [List.length_cons, pbwFiltrationPrevious_succ] at h
            exact h
          have hdiff' :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                Submodule.span R (orderedPBWMonomials R L e (k + 1)) := by
            have hdiffk := pbwFiltration_mono R L htail hdiff
            exact Submodule.span_mono (orderedPBWMonomials_mono R L e (Nat.le_succ k))
              (ih hdiffk)
          rw [← sub_add_cancel (pbwMonomial R L e (head :: tail))
            (pbwMonomial R L e sorted)]
          exact Submodule.add_mem _ hdiff' hsorted_mem

/-- The ordered PBW monomials in a linearly ordered spanning family span the whole universal
enveloping algebra. -/
theorem span_iUnion_orderedPBWMonomials_eq_top
    (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R (⋃ k, orderedPBWMonomials R L e k) = ⊤ := by
  rw [Submodule.span_iUnion]
  simp_rw [span_orderedPBWMonomials_eq_pbwFiltration R L e he]
  exact iSup_pbwFiltration_eq_top R L

end Spanning

end TauCeti.UniversalEnvelopingAlgebra
end
end TAF_LiteralSource_0463

