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

