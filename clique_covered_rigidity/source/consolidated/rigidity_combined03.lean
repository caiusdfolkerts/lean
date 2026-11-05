module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Minimal
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityLaman_RigidityMatroid.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/RigidityMatroid.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/














/-!
# The rigidity matroid: row-independent edge sets

An edge set is *row-independent* at a placement when its rows of the rigidity matrix are
linearly independent (`EdgeSetRowIndependent`); Jordán (2016, p. 39) calls these sets the
independent sets of the framework's rigidity matroid. This file proves what the rigidity matroid
in the plane and in 3-space rests on, with no `Matroid` structure: transport along
isomorphisms and injective vertex maps, openness in the placement, the rank bounds at a
generically rigid and at an affinely-spanning placement, the perturbation to an
affinely-spanning placement, the counts that row-independence forces (`(2, 3)`-sparsity in the
plane, one half of Pollaczek-Geiringer's and Laman's characterization, which
`IsGenericallyRigid.exists_isLaman_le` uses, and the Laman condition `IsLaman3` in 3-space), and
the `0`-extension lift in 3-space.

The matroids are built elsewhere: the planar one in `MatroidIdentification.lean` and
`LinearRigidityMatroid.lean`, the generic one in `GenericRigidityMatroid.lean`. The blueprint
presents this file in `sec:laman-theorem` (its `(⇒)` direction), `sec:rigidity-matroid`,
`sec:jacobs-easy` and `sec:jacobs-zero-extension`.
-/

public section

open Module

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- An edge set `I ⊆ G.edgeSet` is **row-independent at a placement `p`** when the family
of edge-rows `(motion ↦ G.RigidityMap p motion e)_{e ∈ I}` — viewed as linear functionals
on `Framework V d` — is linearly independent over `ℝ`.

Equivalently (in finite dimension), the composition of `G.RigidityMap p` with the column
projection `(G.edgeSet → ℝ) → (I → ℝ)` has full rank `|I|`. Jordán (2016, p. 39) calls such
`I` the *independent sets* of the rigidity matroid of `(G, p)`; the matroid itself is
`linearRigidityMatroid` (`LinearRigidityMatroid.lean`). -/
def EdgeSetRowIndependent (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) : Prop :=
  LinearIndepOn ℝ
    (fun e : G.edgeSet => fun motion : Framework V d => G.RigidityMap p motion e) I

/-- Row-independence at `p` is inherited by edge subsets: dropping rows from a linearly
independent family leaves a linearly independent family. -/
theorem EdgeSetRowIndependent.mono {G : SimpleGraph V} {p : Framework V d}
    {I J : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) (h : J ⊆ I) :
    G.EdgeSetRowIndependent p J :=
  LinearIndepOn.mono hI h

/-- The empty edge set is row-independent at every placement. -/
theorem edgeSetRowIndependent_empty (G : SimpleGraph V) (p : Framework V d) :
    G.EdgeSetRowIndependent p ∅ :=
  linearIndepOn_empty ℝ _

/-- The `e`-th row of the rigidity matrix at placement `p`, viewed as a linear functional
`Framework V d →ₗ[ℝ] ℝ`. As a function, it sends `motion ↦ G.RigidityMap p motion e`. -/
@[expose] noncomputable def rigidityRow (G : SimpleGraph V) (p : Framework V d) :
    G.edgeSet → Module.Dual ℝ (Framework V d) :=
  fun e => (LinearMap.proj e).comp (G.RigidityMap p)

@[simp]
theorem rigidityRow_apply (G : SimpleGraph V) (p : Framework V d) (e : G.edgeSet)
    (motion : Framework V d) : G.rigidityRow p e motion = G.RigidityMap p motion e := rfl

/-- The `e`-th rigidity row is linear in the placement: shifting `p₀` by `t • r` shifts the row
by `t • G.rigidityRow r e`. Used by the linear-interpolation perturbation argument for the
uniform-genericity lemma in `LinearRigidityMatroid.lean`. -/
theorem rigidityRow_add_smul (G : SimpleGraph V) (p₀ r : Framework V d) (t : ℝ)
    (e : G.edgeSet) :
    G.rigidityRow (p₀ + t • r) e =
      G.rigidityRow p₀ e + t • G.rigidityRow r e := by
  ext motion
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | h u v =>
    have h_diff : (p₀ + t • r) u - (p₀ + t • r) v =
        (p₀ u - p₀ v) + t • (r u - r v) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_sub]; abel
    simp only [rigidityRow_apply, rigidityMap_apply, h_diff, inner_add_left,
      inner_smul_left, RCLike.conj_to_real, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]

/-- **The rigidity row of an edge does not depend on which graph's edge set packages it.** The
formula `motion ↦ ⟪p u - p v, motion u - motion v⟫_ℝ` reads off `e.val : Sym2 V` alone, so `G` and
`H`'s rows at the same underlying edge and placement agree. Used to reconcile a subgraph's own
`rigidityRow` family with the ambient `(⊤ : SimpleGraph V)`'s, restricted to the subgraph's edges
(e.g. `finrank_range_rigidityMap_le_genericRank`, `GenericRigidityMatroid.lean`). -/
theorem rigidityRow_congr (G H : SimpleGraph V) (p : Framework V d) {e : Sym2 V}
    (heG : e ∈ G.edgeSet) (heH : e ∈ H.edgeSet) :
    G.rigidityRow p ⟨e, heG⟩ = H.rigidityRow p ⟨e, heH⟩ := by
  induction e using Sym2.ind with
  | h u v => ext motion; simp only [rigidityRow_apply, rigidityMap_apply]

/-- Row-independence in the function module is equivalent to linear independence in the dual
module: the bridge between the blueprint's set-of-functions formulation and the linear-functional
`rigidityRow` family. -/
theorem edgeSetRowIndependent_iff_linearIndepOn_rigidityRow
    (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) :
    G.EdgeSetRowIndependent p I ↔ LinearIndepOn ℝ (G.rigidityRow p) I := by
  change LinearIndepOn ℝ
      (fun e : G.edgeSet => LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ (G.rigidityRow p e)) I ↔ _
  exact (LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ).linearIndepOn_iff_of_injOn
    DFunLike.coe_injective.injOn

/-- **Full row-independence transports between a graph's own edge set and the ambient
`(⊤ : SimpleGraph V)`'s.** All of `G`'s edges are row-independent at `p` iff the corresponding
subset of `(⊤ : SimpleGraph V)`'s edges is. Reconciles the graph-relative `EdgeSetRowIndependent`
predicate with the `Set (⊤ : SimpleGraph V).edgeSet`-indexed form `genericRigidityMatroid_indep_iff`
needs, via the graph-independence of `rigidityRow` (`rigidityRow_congr`): reindexing along the
evident bijection `G.edgeSet ≃ (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet)`
carries a `LinearIndependent` family to the other, in each direction. -/
theorem edgeSetRowIndependent_univ_iff_top {G : SimpleGraph V} {p : Framework V d} :
    G.EdgeSetRowIndependent p Set.univ ↔
      (⊤ : SimpleGraph V).EdgeSetRowIndependent p (Subtype.val ⁻¹' G.edgeSet) := by
  have hGE : G.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  set e : G.edgeSet ≃ (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) :=
    { toFun := fun x => ⟨⟨x.val, hGE x.property⟩, x.property⟩
      invFun := fun y => ⟨y.val.val, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } with he_def
  have hpt : ∀ x : G.edgeSet, G.rigidityRow p x = (⊤ : SimpleGraph V).rigidityRow p (e x).val :=
    fun x => rigidityRow_congr G (⊤ : SimpleGraph V) p x.property (hGE x.property)
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff,
    edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  change LinearIndependent ℝ (G.rigidityRow p) ↔
      LinearIndependent ℝ (fun y : (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) =>
        (⊤ : SimpleGraph V).rigidityRow p y.val)
  constructor
  · intro h
    have heq : (fun y : (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) =>
        (⊤ : SimpleGraph V).rigidityRow p y.val) = G.rigidityRow p ∘ e.symm := by
      funext y
      rw [Function.comp_apply, hpt (e.symm y), e.apply_symm_apply]
    rw [heq]
    exact h.comp e.symm e.symm.injective
  · intro h
    have heq : G.rigidityRow p = (fun y : (Subtype.val ⁻¹' G.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet) => (⊤ : SimpleGraph V).rigidityRow p y.val) ∘ e := by
      funext x; exact hpt x
    rw [heq]
    exact h.comp e e.injective

/-- **Iso transport for row-independence.** A graph iso `φ : G ≃g H` carries a row-independent
placement `q` of `H` to the placement `q ∘ φ` of `G`, which is row-independent on `Set.univ`.

Row-LI analogue of `IsInfinitesimallyRigid.iso` in `Framework.lean`. The G-rows at `q ∘ φ`
factor as `Lφ.toLinearMap.dualMap ∘ H.rigidityRow q ∘ φ.mapEdgeSet`, where
`Lφ : Framework V d ≃ₗ[ℝ] Framework W d` is precomposition with `φ.symm` (motion ↦ motion ∘
φ.symm). LI of the H-rows transports through the bijection `φ.mapEdgeSet` and the injective
linear map `Lφ.toLinearMap.dualMap` (dualMap of a linear equiv). Used at each Henneberg branch
of the induction on `|V|` in `IsSparse.exists_rowIndependent_placement`
(`MatroidIdentification.lean`). -/
theorem EdgeSetRowIndependent.iso {V W : Type*} {d : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    {q : Framework W d} (h : H.EdgeSetRowIndependent q Set.univ) :
    G.EdgeSetRowIndependent (q ∘ φ) Set.univ := by
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff] at h ⊢
  -- Precomposition linear equiv `Framework V d ≃ₗ[ℝ] Framework W d`, `motion ↦ motion ∘ φ.symm`.
  let Lφ : Framework V d ≃ₗ[ℝ] Framework W d :=
    { toFun := fun motion => motion ∘ φ.symm
      invFun := fun motion' => motion' ∘ φ
      left_inv := fun motion => by ext v; simp
      right_inv := fun motion' => by ext w; simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- G-rows at `q ∘ φ` factor through `Lφ.dualMap` and the edge-set bijection.
  have h_factor : ∀ e : G.edgeSet,
      G.rigidityRow (q ∘ φ) e =
        Lφ.toLinearMap.dualMap (H.rigidityRow q (φ.mapEdgeSet e)) := by
    rintro ⟨e, he⟩
    induction e with
    | h u w =>
      refine LinearMap.ext fun motion => ?_
      have hH : s(φ u, φ w) ∈ H.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.map_adj_iff.mpr he
      change G.RigidityMap (q ∘ φ) motion ⟨s(u, w), he⟩ =
        H.RigidityMap q (motion ∘ φ.symm) ⟨s(φ u, φ w), hH⟩
      rw [rigidityMap_apply _ _ _ u w he, rigidityMap_apply _ _ _ (φ u) (φ w) hH]
      simp
  -- Conclude: LI transports along the dualMap of a linear equiv (injective) and the edge-set
  -- bijection (injective reindexing).
  have h_reindex : LinearIndependent ℝ (H.rigidityRow q ∘ φ.mapEdgeSet) :=
    h.comp _ φ.mapEdgeSet.injective
  have h_inj : LinearMap.ker (Lφ.toLinearMap.dualMap) = ⊥ :=
    LinearMap.ker_eq_bot.mpr Lφ.dualMap.injective
  have h_compose : LinearIndependent ℝ
      (Lφ.toLinearMap.dualMap ∘ (H.rigidityRow q ∘ φ.mapEdgeSet)) :=
    h_reindex.map' _ h_inj
  convert h_compose using 1
  funext e
  exact h_factor e

/-! ### Rigidity-row factoring through an injective vertex embedding

The factoring identity and its two LI consequences (forward / reverse) shared by every
"lift placement along an injective vertex map" proof. Specialisations:
`some : V → Option V` (typeI / typeII / pendant Henneberg lifts in `MatroidIdentification.lean`)
and `Subtype.val : ↥S → V` (the restriction to an induced subgraph in
`isSparse_of_edgeSetRowIndependent_dim_two` and `isLaman3_of_edgeSetRowIndependent_dim_three`).
Generalises the iso-only `EdgeSetRowIndependent.iso` above. -/

/-- **Rigidity-row factoring through `LinearMap.funLeft φ`.** For an injective vertex map
`φ : V → W` and a placement `p_ext : Framework W d` compatible with `p' : Framework V d`
(`p_ext (φ v) = p' v`), the row of `H` at the lifted edge `Sym2.map φ e'` factors as the
`dualMap` of `LinearMap.funLeft ℝ _ φ : Framework W d →ₗ Framework V d` applied to the
`G'`-row at `e'`. -/
theorem rigidityRow_lift_eq_funLeft_dualMap
    {V W : Type*} {d : ℕ} (φ : V → W)
    {G' : SimpleGraph V} {H : SimpleGraph W}
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    (e' : G'.edgeSet) (hlift : Sym2.map φ e'.val ∈ H.edgeSet) :
    H.rigidityRow p_ext ⟨Sym2.map φ e'.val, hlift⟩ =
      (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap
        (G'.rigidityRow p' e') := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨e, he⟩ := e'
  induction e with
  | h u v => simp [rigidityRow_apply, rigidityMap_apply, hcompat]

/-- **Forward transport of row independence along an injective vertex embedding.** If
`G'.EdgeSetRowIndependent p' Set.univ` and every `G'`-edge lifts (along `Sym2.map φ`) to an
`H`-edge with `p_ext` compatible (`p_ext (φ v) = p' v`), then the family of `H`-rows at
`p_ext` indexed via any injective re-indexing `s : ι → G'.edgeSet` of (a subset of) the
lifted edges is linearly independent. Used by the `oldSet` branches of the typeI/typeII/pendant
Henneberg row-LI lifts (`MatroidIdentification.lean`); the `s = Subtype.val` instance handles
the typeII subtype `{e' // e'.val ≠ s(a, b)}`. -/
theorem linearIndependent_rigidityRow_lift_of_injective
    {V W : Type*} {d : ℕ}
    {G' : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    (hφ : Function.Injective φ)
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    {ι : Type*} (s : ι → G'.edgeSet) (hs : Function.Injective s)
    (hlift : ∀ i : ι, Sym2.map φ (s i).val ∈ H.edgeSet)
    (h : G'.EdgeSetRowIndependent p' Set.univ) :
    LinearIndependent ℝ
      (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet)) := by
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
      linearIndepOn_univ_iff] at h
  have h_eq : (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet)) =
      (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap ∘
        (fun i => G'.rigidityRow p' (s i)) :=
    funext fun i =>
      rigidityRow_lift_eq_funLeft_dualMap φ hcompat (s i) (hlift i)
  rw [h_eq]
  exact LinearIndependent.dualMap_of_surjective
    (LinearMap.funLeft_surjective_of_injective _ _ _ hφ) (h.comp _ hs)

/-- **Reverse transport of row independence along an injective vertex embedding.** If the
family of `H`-rows at `p_ext` indexed via `s : ι → G'.edgeSet` (with each `Sym2.map φ (s i)`
landing in `H.edgeSet`) is linearly independent, then so is the underlying family of
`G'`-rows at `p'`. Used by `isSparse_of_edgeSetRowIndependent_dim_two` and
`isLaman3_of_edgeSetRowIndependent_dim_three`, where the V-side row-LI on `I` pulls back to
row-LI of the induced subgraph at the restricted placement. -/
theorem linearIndependent_rigidityRow_of_lift
    {V W : Type*} {d : ℕ}
    {G' : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    {ι : Type*} {s : ι → G'.edgeSet}
    (hlift : ∀ i : ι, Sym2.map φ (s i).val ∈ H.edgeSet)
    (h : LinearIndependent ℝ
      (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet))) :
    LinearIndependent ℝ (fun i : ι => G'.rigidityRow p' (s i)) := by
  refine LinearIndependent.of_comp
    (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap ?_
  convert h using 1
  funext i
  exact (rigidityRow_lift_eq_funLeft_dualMap φ hcompat (s i) (hlift i)).symm

/-! ### Henneberg-lift elim-motion glue

Two facts shared verbatim by the three Henneberg row-LI lifts
(`typeI_edgeSetRowIndependent_extend`, its pendant `b = a` degeneracy, and
`typeII_edgeSetRowIndependent_extend` in `MatroidIdentification.lean`), which all place the new
vertex `none` at `q` (`p_ext = fun w => w.elim q p'`) and probe the extended rows with the
coordinate *elim-motions* `fun w => w.elim α 0` (zero on every `some`-vertex). -/

/-- **New-vertex rigidity row at an elim-motion.** With the new vertex `none` placed at `q`
(`p_ext = fun w => w.elim q p'`), the row of a new edge `s(none, some x)` evaluated at the
coordinate elim-motion `fun w => w.elim α 0` (zero on every `some`-vertex) is the scalar inner
product `⟪q - p' x, α⟫_ℝ`. Collapses the recurring `rigidityRow_apply, rigidityMap_apply,
Option.elim_*, sub_zero` micro-idiom in the new-row branches of the typeI/typeII/pendant lifts. -/
theorem rigidityRow_none_some_elim {V : Type*} {d : ℕ} {H : SimpleGraph (Option V)}
    (q : EuclideanSpace ℝ (Fin d)) (p' : Framework V d) (α : EuclideanSpace ℝ (Fin d)) {x : V}
    (hmem : s((none : Option V), some x) ∈ H.edgeSet) :
    H.rigidityRow (fun w : Option V => w.elim q p') ⟨s(none, some x), hmem⟩
        (fun w : Option V => w.elim α (fun _ => 0)) = ⟪q - p' x, α⟫_ℝ := by
  simp only [rigidityRow_apply, rigidityMap_apply, Option.elim_none, Option.elim_some, sub_zero]

/-- **The lifted old-row span vanishes at an elim-motion.** In a Henneberg lift
(`p_ext = fun w => w.elim q p'`), every rigidity row of an edge lifted from `V` via
`Sym2.map some` vanishes at the coordinate elim-motion `fun w => w.elim α 0`; hence the span of
any set `S` of such lifted rows lies in the kernel of evaluation at that motion. The three row-LI
lifts use this to show a joint element of the old span vanishes at the test motion. -/
theorem oldSpan_le_ker_eval_elim {V : Type*} {d : ℕ} {H : SimpleGraph (Option V)}
    (q : EuclideanSpace ℝ (Fin d)) (p' : Framework V d) (α : EuclideanSpace ℝ (Fin d))
    {S : Set H.edgeSet} (hS : ∀ e ∈ S, ∃ e0 : Sym2 V, e.val = Sym2.map some e0) :
    Submodule.span ℝ (H.rigidityRow (fun w : Option V => w.elim q p') '' S) ≤
      LinearMap.ker (Module.Dual.eval ℝ (Framework (Option V) d)
        (fun w : Option V => w.elim α (fun _ => 0))) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨e0, he0⟩ := hS e he
  rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, rigidityRow_apply]
  obtain ⟨e, he_mem⟩ := e
  subst he0
  induction e0 with
  | h u v => simp [rigidityMap_apply]

/-- **Openness of row-independence in the placement.** If `p₀` makes an edge subset `I`
row-independent, then so does every placement in some neighborhood of `p₀`.

Row-LI analogue of `IsInfinitesimallyRigid.eventually` (in `Framework.lean`). The proof
transports the LI assertion from `Module.Dual ℝ (Framework V d)` — which carries no canonical
norm — to the normed space `Fin n → ℝ` (`n = finrank ℝ (Framework V d)`) along the basis
isomorphism `b.dualBasis.equivFun : Module.Dual ℝ (Framework V d) ≃ₗ[ℝ] Fin n → ℝ` (which sends
`l ↦ fun i => l (b i)` by `Basis.dualBasis_equivFun`). The matrix family
`p ↦ (i, k) ↦ G.rigidityRow p i.val (b k)` is continuous in `p` (each entry is an inner product,
already tagged `@[fun_prop]` via `continuous_rigidityMap_apply`); equals an LI family at `p₀`
under the transport; `LinearIndependent.eventually` preserves LI on a neighborhood; transport
back. -/
theorem EdgeSetRowIndependent.eventually [Finite V] {G : SimpleGraph V}
    {p₀ : Framework V d} {I : Set G.edgeSet}
    (h₀ : G.EdgeSetRowIndependent p₀ I) :
    ∀ᶠ p in 𝓝 p₀, G.EdgeSetRowIndependent p I := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  have : Fintype I := Fintype.ofFinite _
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow] at h₀
  set n := Module.finrank ℝ (Framework V d)
  set b := Module.finBasis ℝ (Framework V d) with hb_def
  set ψ : Module.Dual ℝ (Framework V d) ≃ₗ[ℝ] Fin n → ℝ := b.dualBasis.equivFun
  set M : Framework V d → I → Fin n → ℝ := fun p i k => G.rigidityRow p i.val (b k) with hM_def
  have h_cont : Continuous M := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    change Continuous fun p : Framework V d => G.RigidityMap p (b k) i.val
    fun_prop
  have h_M_eq_ψ : ∀ p : Framework V d,
      (fun i : I => M p i) = (ψ : _ →ₗ[ℝ] _) ∘ (fun i : I => G.rigidityRow p i.val) := by
    intro p
    funext i k
    exact (Basis.dualBasis_equivFun b _ _).symm
  have h_iff : ∀ p : Framework V d,
      LinearIndependent ℝ (fun i : I => M p i) ↔
      LinearIndependent ℝ (fun i : I => G.rigidityRow p i.val) := by
    intro p
    rw [h_M_eq_ψ p, LinearMap.linearIndependent_iff _ (LinearEquiv.ker _)]
  have hM₀_li : LinearIndependent ℝ (M p₀) := (h_iff p₀).mpr h₀
  have h_event : ∀ᶠ p in 𝓝 p₀, LinearIndependent ℝ (M p) :=
    h_cont.continuousAt.tendsto.eventually hM₀_li.eventually
  filter_upwards [h_event] with p hp_li
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  exact (h_iff p).mp hp_li

/-- The rigidity rows span the range of the transpose map. Combined with
`LinearMap.finrank_range_dualMap_eq_finrank_range` this is the row-rank-equals-column-rank
identity for the rigidity matrix; in span form, it is
`LinearMap.range_dualMap_eq_span_image_dualBasis` applied to `Pi.basisFun ℝ G.edgeSet`. -/
theorem span_range_rigidityRow (G : SimpleGraph V) [Finite G.edgeSet] (p : Framework V d) :
    Submodule.span ℝ (Set.range (G.rigidityRow p)) =
      LinearMap.range (G.RigidityMap p).dualMap := by
  classical
  have h_row : G.rigidityRow p =
      (G.RigidityMap p).dualMap ∘ (Pi.basisFun ℝ G.edgeSet).dualBasis := by
    funext e; ext _; simp [rigidityRow]
  rw [h_row]
  exact (LinearMap.range_dualMap_eq_span_image_dualBasis (Pi.basisFun ℝ G.edgeSet) _).symm

/-- **Rank lower bound at a generically rigid placement, d-general.** If `G` is generically
rigid in dimension `d`, some framework `p` realises
`d * #V ≤ finrank (range (G.RigidityMap p)) + d (d + 1) / 2`.

This is the rank half of `IsGenericallyRigid.card_mul_le`: the same rank-nullity argument that
gives `d * #V ≤ #E + d (d + 1) / 2`, stopping one step earlier (before replacing `rank` by
`#E` via `rigidityMap_finrank_range_le`). `exists_edgeSetRowIndependent_basis_dim_two` uses it
at `d = 2`, where `2 * (2 + 1) / 2 = 3` reduces by `rfl`, so no `d = 2` form is needed. -/
theorem rigidityMap_finrank_range_ge_of_isGenericallyRigid [Fintype V] {d : ℕ}
    {G : SimpleGraph V} (hG : G.IsGenericallyRigid d) :
    ∃ p : Framework V d,
      d * Fintype.card V ≤
        Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + d * (d + 1) / 2 := by
  obtain ⟨p, h_ker⟩ := hG
  refine ⟨p, ?_⟩
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2 := h_ker
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

/-- **Rank upper bound at an affinely-spanning placement, d-general.** If `p : Framework V d`
affinely spans `EuclideanSpace ℝ (Fin d)`, then
`finrank (range (G.RigidityMap p)) + d (d + 1) / 2 ≤ d * #V`.

Combine the d-general kernel bound `rigidityMap_ker_finrank_ge_of_affinelySpanning`
(`d (d + 1) / 2 ≤ finrank ker`) with rank-nullity and `Framework.finrank`. Companion to
`rigidityMap_finrank_range_ge_of_isGenericallyRigid`; at a placement that is both
infinitesimally rigid and affinely spanning the two bounds pin the row rank to exactly
`d * #V - d (d + 1) / 2`. -/
theorem rigidityMap_finrank_range_le_of_affinelySpanning [Fintype V] {d : ℕ}
    (G : SimpleGraph V) {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + d * (d + 1) / 2 ≤
      d * Fintype.card V := by
  have h_ker : d * (d + 1) / 2 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
    G.rigidityMap_ker_finrank_ge_of_affinelySpanning hp
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

/-- **Row-independent edge basis at a fixed rank-realising placement, dim 2.** If `p : Framework
V 2` realises the rank lower bound `2 * #V ≤ finrank (range R) + 3` (e.g. at an infinitesimally
rigid placement, via rank-nullity), then `G` has a row-independent edge set at `p` of size exactly
`2 * #V - 3`. The placement is supplied externally, so the lemma composes with
`exists_affinelySpanning_of_eventually` (at `IsInfinitesimallyRigid.eventually`) in
`IsGenericallyRigid.exists_isLaman_le`; `exists_edgeSetRowIndependent_basis_dim_two` applies it
at the placement of the rank lower bound. -/
theorem exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two [Fintype V]
    {G : SimpleGraph V} {p : Framework V 2}
    (hp : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3) :
    ∃ I : Set G.edgeSet,
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  -- Extend ∅ to a row-LI subset `b ⊆ univ` whose image spans the whole row family.
  obtain ⟨b, _hb_sub, _, h_range_sub, hb_li⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ (G.rigidityRow p))
      (Set.empty_subset (Set.univ : Set G.edgeSet))
  have : Fintype ↥b := Fintype.ofFinite _
  -- The span of `rigidityRow '' b` equals `range R.dualMap`: forward inclusion is monotonicity
  -- of `span` (from `rigidityRow '' b ⊆ Set.range rigidityRow`) plus `span_range_rigidityRow`;
  -- reverse uses the `rigidityRow '' univ ⊆ span ...` output of `exists_linearIndepOn_extension`.
  have h_span_b : Submodule.span ℝ (G.rigidityRow p '' b) =
      LinearMap.range (G.RigidityMap p).dualMap := by
    rw [← G.span_range_rigidityRow p]
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_
    rw [Submodule.span_le, ← Set.image_univ]
    exact h_range_sub
  -- `b` is an LI family spanning that submodule, so its cardinality is the finrank.
  have h_card_b : Fintype.card ↥b =
      finrank ℝ (Submodule.span ℝ (G.rigidityRow p '' b)) := by
    have h :=
      (linearIndependent_iff_card_eq_finrank_span
        (b := fun e : ↥b => G.rigidityRow p e.val)).mp hb_li
    rwa [Set.finrank, ← Set.image_eq_range] at h
  -- Chain `Fintype.card ↥b = finrank (range R.dualMap) = finrank (range R) ≥ 2 * #V - 3`.
  have h_le_card : 2 * Fintype.card V - 3 ≤ b.ncard := by
    have h1 := h_card_b
    rw [h_span_b, LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
    rw [Set.ncard_eq_card_coe]
    omega
  -- Truncate `b` to a subset `I ⊆ b` with `|I| = 2 * #V - 3`.
  obtain ⟨I, hI_sub, hI_card⟩ := Set.exists_subset_card_eq h_le_card
  exact ⟨I, hI_card,
    (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mpr (hb_li.mono hI_sub)⟩

/-- **Row-independent edge basis at a generically rigid placement, dim 2.** If `G` is generically
rigid in dimension 2, there is a placement `p` and a row-independent edge set `I ⊆ G.edgeSet` of
size exactly `2 * #V - 3`.

Composition of `rigidityMap_finrank_range_ge_of_isGenericallyRigid` (extracting an IR witness `p`
and its rank lower bound) with `exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two` (basis-
pick at any placement realising the rank lower bound). -/
theorem exists_edgeSetRowIndependent_basis_dim_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) :
    ∃ (p : Framework V 2) (I : Set G.edgeSet),
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  obtain ⟨p, hp⟩ := rigidityMap_finrank_range_ge_of_isGenericallyRigid hG
  exact ⟨p, exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two hp⟩

/-! ### Affinely-spanning rigid placement, d-general

The `(⇒)` direction of Laman's theorem needs a placement that is both infinitesimally rigid
for `G` *and* affinely spanning on every size-`≥ d + 1` subset. Openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) supplies the IR half; for the affinely-spanning half we
perturb the IR witness along the *moment curve* `w v = (φ(v)^1, …, φ(v)^d)` (with `φ : V → ℝ`
injective via `Fintype.equivFin`). For each ordered `(d+1)`-tuple of distinct vertices, the
affine-dependence determinant of the perturbed difference matrix is a polynomial in `t` of
degree at most `d`, whose top coefficient is the Vandermonde-difference determinant
`∏_{0 ≤ i < j ≤ d} (φ vⱼ − φ vᵢ)`, nonzero by injectivity. Each per-tuple bad set is therefore
finite (`Polynomial.finite_setOf_isRoot`), the finite union of bad sets is finite, and any open
interval avoids it. -/

/-- **Affine independence from a nonzero difference-matrix determinant, d-general.** If `q : Fin
(d + 1) → EuclideanSpace ℝ (Fin d)` and the `d × d` matrix of differences `q i.succ - q 0` has
nonzero determinant, then `q` is affinely independent.

Proof: row-LI of the matrix in `Fin d → ℝ` follows from
`Matrix.linearIndependent_rows_of_det_ne_zero`; transport along `WithLp.linearEquiv` to LI of the
EuclideanSpace differences; conclude `AffineIndependent` via
`affineIndependent_iff_linearIndependent_vsub` and the reindex
`finSuccAboveEquiv (0 : Fin (d + 1))`. -/
private lemma affineIndependent_of_difference_det_ne_zero {d : ℕ}
    (q : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (h : (Matrix.of fun i j : Fin d => q i.succ j - q 0 j).det ≠ 0) :
    AffineIndependent ℝ q := by
  have h_LI_rows : LinearIndependent ℝ
      (fun i : Fin d => Matrix.of (fun i' j : Fin d => q i'.succ j - q 0 j) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero h
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0,
    ← linearIndependent_equiv (finSuccAboveEquiv 0),
    ← (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)]
  exact h_LI_rows

/-- **Affinely-spanning perturbation under an eventually-true placement property, d-general.**
Given any property `P : Framework V d → Prop` that holds on a neighborhood of some placement
`p₀`, there exists a placement satisfying `P` and affinely spanning `EuclideanSpace ℝ (Fin d)`
when restricted to every size-`≥ d + 1` subset of `V`.

Specialised twice in the planar files: at `P = G.IsInfinitesimallyRigid` (the `(⇒)` direction
of Laman's theorem, in `LamanTheorem.lean`, where `hP` comes from
`IsInfinitesimallyRigid.eventually`), and at `P = G.EdgeSetRowIndependent · I` in dimension 2
(the iff `edgeSet_rowIndependent_iff_isSparse_dim_two`, in `MatroidIdentification.lean`,
where `hP` comes from `EdgeSetRowIndependent.eventually`). The moment-curve perturbation does
not depend on the property; only the openness premise differs between the two callers.

The proof perturbs `p₀` along the moment-curve direction `w v = (φ(v)^1, …, φ(v)^d)` with
`φ : V → ℝ` injective. The openness premise `hP` gives `ε > 0` such that `P (p₀ + t • w)` holds
for `|t| < ε`. For each ordered `(d+1)`-tuple of distinct vertices, the difference-matrix
determinant `det(M₀ + t · M₁)` is a polynomial in `t` of degree at most `d`
(`Polynomial.natDegree_det_X_add_C_le`) whose `t^d` coefficient is `det M₁`
(`Polynomial.coeff_det_X_add_C_card`), the Vandermonde-difference determinant
`∏_{0 ≤ i < j ≤ d} (φ vⱼ − φ vᵢ)` (`Matrix.det_powerDifferences`), nonzero by injectivity. The
bad-`t` set per tuple is therefore finite (`Polynomial.finite_setOf_isRoot`); the finite union over
tuples is finite; and the open interval `(0, ε)` is infinite, so it has a point avoiding the bad
set. -/
theorem exists_affinelySpanning_of_eventually [Finite V] {d : ℕ}
    {P : Framework V d → Prop} {p₀ : Framework V d}
    (hP : ∀ᶠ p in 𝓝 p₀, P p) :
    ∃ p : Framework V d, P p ∧
      ∀ S : Set V, d + 1 ≤ S.ncard →
        affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  -- Step 1: pick `φ : V → ℝ` injective.
  let ψ : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let φ : V → ℝ := fun v => ((ψ v).val : ℝ)
  have hφ_inj : Function.Injective φ := by
    intro a b h
    apply ψ.injective
    apply Fin.ext
    have h' : ((ψ a).val : ℝ) = ((ψ b).val : ℝ) := h
    exact_mod_cast h'
  -- Step 2: moment-curve direction `w v = (φ(v)^1, …, φ(v)^d)`.
  let w : V → EuclideanSpace ℝ (Fin d) :=
    fun v => WithLp.toLp 2 (fun j : Fin d => (φ v) ^ (j.val + 1))
  have hw : ∀ (v : V) (j : Fin d), (w v) j = (φ v) ^ (j.val + 1) := fun _ _ => rfl
  -- Step 3: perturbed placement `pt t = p₀ + t • w`.
  let pt : ℝ → Framework V d := fun t v => p₀ v + t • w v
  have h_pt_zero : pt 0 = p₀ := by ext v i; simp [pt]
  have h_pt_cont : Continuous pt := by
    refine continuous_pi fun v => ?_
    exact continuous_const.add (continuous_id'.smul continuous_const)
  -- Step 4: pull the openness premise back to `t`.
  have h_event_P : ∀ᶠ t in 𝓝 (0 : ℝ), P (pt t) := by
    have h_tendsto : Filter.Tendsto pt (𝓝 0) (𝓝 p₀) :=
      h_pt_zero ▸ h_pt_cont.tendsto 0
    exact h_tendsto.eventually hP
  rw [Metric.eventually_nhds_iff] at h_event_P
  obtain ⟨ε, hε_pos, hε_P⟩ := h_event_P
  -- Coordinate identity: `(pt t v) j = (p₀ v) j + t * φ(v)^(j+1)`.
  have h_pt_coord : ∀ (t : ℝ) (v : V) (j : Fin d),
      (pt t v) j = (p₀ v) j + t * (φ v) ^ (j.val + 1) := by
    intros t v j
    simp [pt, hw, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- Step 5: for each injective `q : Fin (d + 1) → V`, the per-tuple bad-`t` set is finite.
  have h_per_tuple : ∀ q : Fin (d + 1) → V, Function.Injective q →
      {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}.Finite := by
    intros q hq_inj
    -- Difference matrices: `M₀` from `p₀`, `M₁` from the moment curve.
    set M₀ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => p₀ (q i.succ) j - p₀ (q 0) j) with hM₀_def
    set M₁ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => (φ (q i.succ)) ^ (j.val + 1) - (φ (q 0)) ^ (j.val + 1))
      with hM₁_def
    -- `det M₁ = ∏_{i<j} (φ(qⱼ) - φ(qᵢ)) ≠ 0` by injectivity of `φ ∘ q`.
    have h_det_M₁_ne : M₁.det ≠ 0 := by
      rw [hM₁_def, Matrix.det_powerDifferences (fun k : Fin (d + 1) => φ (q k))]
      refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr ?_)
      intros j hij
      rw [Finset.mem_Ioi] at hij
      refine sub_ne_zero.mpr ?_
      intro h
      exact (Fin.ne_of_lt hij).symm (hq_inj (hφ_inj h))
    -- The polynomial `P(X) = det (X • M₁.map C + M₀.map C) ∈ ℝ[X]`.
    set P : Polynomial ℝ :=
      ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C + M₀.map Polynomial.C).det
      with hP_def
    -- `coeff P d = det M₁ ≠ 0`, so `P ≠ 0`.
    have hP_ne : P ≠ 0 := by
      intro h
      apply h_det_M₁_ne
      have := Polynomial.coeff_det_X_add_C_card M₁ M₀
      rw [show Fintype.card (Fin d) = d from Fintype.card_fin d, ← hP_def, h] at this
      simpa using this.symm
    -- `P.eval t = (t • M₁ + M₀).det` via `Polynomial.eval_det_X_add_C`.
    have hP_eval : ∀ t : ℝ, P.eval t = (t • M₁ + M₀).det := fun t => by
      rw [hP_def, Polynomial.eval_det_X_add_C]
    -- The rows of `t • M₁ + M₀` are `(pt t (q i.succ) - pt t (q 0))` coordinatewise.
    have h_rows : ∀ t : ℝ,
        (t • M₁ + M₀ : Matrix (Fin d) (Fin d) ℝ) =
        Matrix.of (fun i j : Fin d => (pt t (q i.succ)) j - (pt t (q 0)) j) := by
      intro t
      ext i j
      simp [Matrix.add_apply, smul_eq_mul, hM₀_def, hM₁_def, h_pt_coord]
      ring
    -- The bad-`t` set is contained in the zero set of `P`.
    have h_bad_sub : {t : ℝ | ¬ AffineIndependent ℝ (fun i => pt t (q i))} ⊆
        {t : ℝ | P.IsRoot t} := by
      intros t ht
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hP_eval] at *
      by_contra h_det_ne
      exact ht (affineIndependent_of_difference_det_ne_zero (fun i => pt t (q i))
        (by rw [← h_rows t]; exact h_det_ne))
    exact (Polynomial.finite_setOfPred_isRoot hP_ne).subset h_bad_sub
  -- Step 6: assemble the global bad set as a finite union over injective `(d+1)`-tuples.
  let tuples : Finset (Fin (d + 1) → V) :=
    (Finset.univ : Finset (Fin (d + 1) → V)).filter Function.Injective
  let bad : Set ℝ :=
    ⋃ q ∈ tuples, {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}
  have h_bad_finite : bad.Finite := by
    apply (Finset.finite_toSet tuples).biUnion
    intros q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    exact h_per_tuple q hq.2
  -- Step 7: pick `t ∈ (0, ε) \ bad`.
  have h_nonempty : ((Set.Ioo (0 : ℝ) ε) \ bad).Nonempty :=
    ((Set.Ioo_infinite hε_pos).sdiff h_bad_finite).nonempty
  obtain ⟨t, ⟨ht_pos, ht_lt⟩, ht_good⟩ := h_nonempty
  -- Step 8: assemble the witness.
  refine ⟨pt t, ?_, ?_⟩
  · -- `P (pt t)` since `t` is in the openness neighborhood.
    apply hε_P
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact ht_lt
  · -- Affinely spans on every size-`≥ d + 1` subset.
    intros S hS
    -- Pick `d + 1` distinct elements in `S` as an injective `q : Fin (d + 1) → V`.
    obtain ⟨q, hq_inj, hq_S⟩ := Set.exists_injective_fin_of_le_ncard hS
    -- The `(d+1)`-tuple at `pt t` is affinely independent.
    have h_AI : AffineIndependent ℝ (fun i => pt t (q i)) := by
      by_contra h
      apply ht_good
      simp only [bad, Set.mem_iUnion]
      refine ⟨q, ?_, h⟩
      simp [tuples, hq_inj]
    -- The affine span of these `d + 1` points is `⊤` in `EuclideanSpace ℝ (Fin d)`.
    have h_span_tuple : affineSpan ℝ (Set.range (fun i => pt t (q i))) = ⊤ := by
      rw [h_AI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp [finrank_euclideanSpace]
    -- The tuple is included in the image of `p|_S`.
    have h_incl : Set.range (fun i => pt t (q i)) ⊆
        Set.range (fun v : S => pt t v.val) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨q i, hq_S i⟩, rfl⟩
    -- Hence the larger affine span is `⊤`.
    apply top_le_iff.mp
    calc ⊤ = affineSpan ℝ (Set.range (fun i => pt t (q i))) := h_span_tuple.symm
      _ ≤ affineSpan ℝ (Set.range (fun v : S => pt t v.val)) :=
          affineSpan_mono ℝ h_incl

/-! ### Sparsity from row-independence

The half of Pollaczek-Geiringer's and Laman's characterization of row-independence in the plane
(Jordán 2016, Theorem 2.2.1) that needs no construction: a row-independent edge set at a
placement with no three points collinear is `(2, 3)`-sparse. Jordán derives it from his rank
bound (Lemmas 1.2.1 and 1.3.1), as we do. -/

/-- **`(2, 3)`-sparsity from row-independence, dim 2** (one half of Pollaczek-Geiringer's and
Laman's characterization, Jordán's Theorem 2.2.1). Let
`p : Framework V 2` affinely span on every size-`≥ 3` subset of `V`; then any spanning subgraph
whose edge set is row-independent at `p` is `(2, 3)`-sparse.

Proof: fix a vertex subset `s : Finset V` satisfying the sparsity proviso `3 ≤ 2 * #s`. Bridge to
the induced subgraph via `ncard_edgesIn_eq_ncard_induce_edgeSet`. For `#s = 2` the conclusion is
a one-edge combinatorial bound (`card_edgeFinset_le_card_choose_two`); for `#s ≥ 3` it comes from
the d-general rank upper bound at affinely-spanning placements
(`rigidityMap_finrank_range_le_of_affinelySpanning`) applied to the induced subgraph at the
restricted placement, after transporting row-independence through the framework-restriction map
`Framework V 2 → Framework ↥s 2`. The transport uses `LinearIndependent.of_comp` on the dual-map
direction; the factoring identity says the rigidity row in `G` at the lifted edge equals the
rigidity row in the induced subgraph composed with the restriction.

**Blueprint:** the $(\Rightarrow)$ direction's sparsity step, `lem:isSparse-of-rowIndependent-two`.
The hypothesis `hp` is supplied at dimension `2` by `exists_affinelySpanning_of_eventually`
(specialised at infinitesimal rigidity in `IsGenericallyRigid.exists_isLaman_le`, at
row-independence in `edgeSet_rowIndependent_iff_isSparse_dim_two`). -/
theorem isSparse_of_edgeSetRowIndependent_dim_two {V : Type*} {G : SimpleGraph V}
    {p : Framework V 2}
    (hp : ∀ S : Set V, 3 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤)
    {I : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) :
    (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsSparse 2 3 := by
  classical
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  -- `H.edgeSet = Subtype.val '' I`: the `fromEdgeSet \ diagSet` reduces because every
  -- edge in the image is already a non-loop (it came from `G.edgeSet`).
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  -- `H ≤ G` (the spanning subgraph is contained in `G`).
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  intro s hs
  -- Bridge `(H.edgesIn ↑s).ncard` to `(H.induce ↑s).edgeSet.ncard` via the
  -- `Sym2.map Subtype.val` bijection.
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet]
  set S : Set V := (↑s : Set V) with hS_def
  have hS_ncard : S.ncard = s.card := by rw [hS_def]; exact Set.ncard_coe_finset s
  have hS_card : Fintype.card ↥S = s.card := (Set.ncard_eq_card_coe _).symm.trans hS_ncard
  -- Case split: `hs : 3 ≤ 2 * s.card` forces `s.card = 2 ∨ 3 ≤ s.card`.
  obtain hs_two | hs_ge : s.card = 2 ∨ 3 ≤ s.card := by omega
  · -- `s.card = 2`: simple-graph combinatorics gives ≤ 1 edge in the induced subgraph.
    have h_card_le : (H.induce S).edgeFinset.card ≤ (Fintype.card ↥S).choose 2 :=
      card_edgeFinset_le_card_choose_two
    rw [hS_card, hs_two, Nat.choose_self] at h_card_le
    have h_ncard_eq : (H.induce S).edgeSet.ncard = (H.induce S).edgeFinset.card := by
      rw [Set.ncard_eq_card_coe, ← SimpleGraph.edgeFinset_card]
    omega
  · -- `s.card ≥ 3`: row factoring + rank upper bound at affinely-spanning placement.
    set p_s : Framework ↥S 2 := fun v => p v.val with hp_s_def
    -- The hypothesis supplies affine spanning for the restricted placement.
    have h_affineSpan : affineSpan ℝ (Set.range p_s) = ⊤ :=
      hp S (by rw [hS_ncard]; exact hs_ge)
    -- Rank upper bound at the induced subgraph.
    have h_rank_le : Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) + 3 ≤
        2 * s.card := by
      have h := rigidityMap_finrank_range_le_of_affinelySpanning (H.induce S) h_affineSpan
      rwa [hS_card] at h
    -- V-side lift of an induced-subgraph edge, landing in `H.edgeSet ⊆ G.edgeSet`.
    have hlift_mem_H : ∀ e' : (H.induce S).edgeSet,
        Sym2.map (Subtype.val : ↥S → V) e'.val ∈ H.edgeSet := by
      intro e'
      obtain ⟨e, he⟩ := e'
      induction e with | h u v =>
        rw [mem_edgeSet, induce_adj] at he
        rw [Sym2.map_mk, mem_edgeSet]
        exact he
    let liftEdge : (H.induce S).edgeSet → G.edgeSet :=
      fun e' => ⟨Sym2.map (Subtype.val : ↥S → V) e'.val,
        edgeSet_mono hHG (hlift_mem_H e')⟩
    -- The lift lands in `I`: `(liftEdge e').val ∈ H.edgeSet = Subtype.val '' I`.
    have hlift_in_I : ∀ e' : (H.induce S).edgeSet, liftEdge e' ∈ I := by
      intro e'
      have h_in_H : (liftEdge e').val ∈ H.edgeSet := hlift_mem_H e'
      rw [hH_edgeSet] at h_in_H
      obtain ⟨e₀, he₀_in_I, he₀_eq⟩ := h_in_H
      have : liftEdge e' = e₀ := Subtype.ext he₀_eq.symm
      rw [this]; exact he₀_in_I
    -- `liftEdge` is injective.
    have hlift_inj : Function.Injective liftEdge := fun _ _ h =>
      Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h))
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via the reverse-direction helper (factoring + `of_comp`).
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') :=
      linearIndependent_rigidityRow_of_lift (Subtype.val : ↥S → V) (fun _ => rfl)
        (fun i => edgeSet_mono hHG (hlift_mem_H i)) h_li_V
    -- Convert LI to a finrank identity, then chain through the dualMap rank equality.
    have h_card_eq : Fintype.card (H.induce S).edgeSet =
        Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) := by
      have h := (linearIndependent_iff_card_eq_finrank_span
        (b := fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e')).mp h_li_s
      rw [Set.finrank] at h
      rw [h, (H.induce S).span_range_rigidityRow p_s]
      exact LinearMap.finrank_range_dualMap_eq_finrank_range _
    rw [Set.ncard_eq_card_coe]
    omega

/-! ### The Laman condition from row-independence, dimension three (Jacobs' conjecture, easy
direction) -/

/-- **The Laman condition from row independence, dimension three** (Jacobs' conjecture, easy
direction). Let `p : Framework V 3` affinely span on every size-`≥ 4` subset of `V`; then any
spanning subgraph whose edge set is row-independent at `p` is Laman (`IsLaman3`).

Proof: the same argument as `isSparse_of_edgeSetRowIndependent_dim_two`, one dimension up. Fix
`s : Finset V` with `3 ≤ s.card`. For `s.card = 3` the bound is the trivial combinatorial count
(`card_edgeFinset_le_card_choose_two`, `Nat.choose 3 2 = 3`); for `s.card ≥ 4` it comes from the
`d`-general rank upper bound at affinely-spanning placements
(`rigidityMap_finrank_range_le_of_affinelySpanning`) applied to the induced subgraph at the
restricted placement, after transporting row-independence through the framework-restriction map
`Framework V 3 → Framework ↥s 3` exactly as in the planar case.

**Blueprint:** the easy direction of Jacobs' conjecture, `lem:isLaman3-of-rowIndependent`. The
hypothesis `hp` is supplied at dimension `3` by a general-position placement
(`cor:genericMatroid-indep-isLaman3`, `GeneralPositionPlacement.lean`). -/
theorem isLaman3_of_edgeSetRowIndependent_dim_three {V : Type*} {G : SimpleGraph V}
    {p : Framework V 3}
    (hp : ∀ S : Set V, 4 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤)
    {I : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) :
    (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsLaman3 := by
  classical
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  -- `H.edgeSet = Subtype.val '' I`: the `fromEdgeSet \ diagSet` reduces because every
  -- edge in the image is already a non-loop (it came from `G.edgeSet`).
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  -- `H ≤ G` (the spanning subgraph is contained in `G`).
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  intro s hs
  -- Bridge `(H.edgesIn ↑s).ncard` to `(H.induce ↑s).edgeSet.ncard` via the
  -- `Sym2.map Subtype.val` bijection.
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet]
  set S : Set V := (↑s : Set V) with hS_def
  have hS_ncard : S.ncard = s.card := by rw [hS_def]; exact Set.ncard_coe_finset s
  have hS_card : Fintype.card ↥S = s.card := (Set.ncard_eq_card_coe _).symm.trans hS_ncard
  -- Case split: `hs : 3 ≤ s.card` forces `s.card = 3 ∨ 4 ≤ s.card`.
  obtain hs_three | hs_ge : s.card = 3 ∨ 4 ≤ s.card := by omega
  · -- `s.card = 3`: simple-graph combinatorics gives ≤ 3 edges in the induced subgraph.
    have h_card_le : (H.induce S).edgeFinset.card ≤ (Fintype.card ↥S).choose 2 :=
      card_edgeFinset_le_card_choose_two
    rw [hS_card, hs_three, show Nat.choose 3 2 = 3 from rfl] at h_card_le
    have h_ncard_eq : (H.induce S).edgeSet.ncard = (H.induce S).edgeFinset.card := by
      rw [Set.ncard_eq_card_coe, ← SimpleGraph.edgeFinset_card]
    omega
  · -- `s.card ≥ 4`: row factoring + rank upper bound at affinely-spanning placement.
    set p_s : Framework ↥S 3 := fun v => p v.val with hp_s_def
    -- The hypothesis supplies affine spanning for the restricted placement.
    have h_affineSpan : affineSpan ℝ (Set.range p_s) = ⊤ :=
      hp S (by rw [hS_ncard]; exact hs_ge)
    -- Rank upper bound at the induced subgraph.
    have h_rank_le : Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) + 6 ≤
        3 * s.card := by
      have h := rigidityMap_finrank_range_le_of_affinelySpanning (H.induce S) h_affineSpan
      rwa [hS_card] at h
    -- V-side lift of an induced-subgraph edge, landing in `H.edgeSet ⊆ G.edgeSet`.
    have hlift_mem_H : ∀ e' : (H.induce S).edgeSet,
        Sym2.map (Subtype.val : ↥S → V) e'.val ∈ H.edgeSet := by
      intro e'
      obtain ⟨e, he⟩ := e'
      induction e with | h u v =>
        rw [mem_edgeSet, induce_adj] at he
        rw [Sym2.map_mk, mem_edgeSet]
        exact he
    let liftEdge : (H.induce S).edgeSet → G.edgeSet :=
      fun e' => ⟨Sym2.map (Subtype.val : ↥S → V) e'.val,
        edgeSet_mono hHG (hlift_mem_H e')⟩
    -- The lift lands in `I`: `(liftEdge e').val ∈ H.edgeSet = Subtype.val '' I`.
    have hlift_in_I : ∀ e' : (H.induce S).edgeSet, liftEdge e' ∈ I := by
      intro e'
      have h_in_H : (liftEdge e').val ∈ H.edgeSet := hlift_mem_H e'
      rw [hH_edgeSet] at h_in_H
      obtain ⟨e₀, he₀_in_I, he₀_eq⟩ := h_in_H
      have : liftEdge e' = e₀ := Subtype.ext he₀_eq.symm
      rw [this]; exact he₀_in_I
    -- `liftEdge` is injective.
    have hlift_inj : Function.Injective liftEdge := fun _ _ h =>
      Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h))
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via the reverse-direction helper (factoring + `of_comp`).
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') :=
      linearIndependent_rigidityRow_of_lift (Subtype.val : ↥S → V) (fun _ => rfl)
        (fun i => edgeSet_mono hHG (hlift_mem_H i)) h_li_V
    -- Convert LI to a finrank identity, then chain through the dualMap rank equality.
    have h_card_eq : Fintype.card (H.induce S).edgeSet =
        Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) := by
      have h := (linearIndependent_iff_card_eq_finrank_span
        (b := fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e')).mp h_li_s
      rw [Set.finrank] at h
      rw [h, (H.induce S).span_range_rigidityRow p_s]
      exact LinearMap.finrank_range_dualMap_eq_finrank_range _
    rw [Set.ncard_eq_card_coe]
    omega

/-! ### Zero-extension (vertex-addition) row-independence lift, dimension three

The conditional core of `lem:zero-extension-rowIndependent`, the `0`-extension lemma
(Jackson–Jordán 2008, Lemma 3.3, citing Whiteley's Vertex 3-Addition Lemma 9.1.3, 1996) that
the reduction of Jacobs' conjecture to minimum degree at least two and the degree-one rank
formula both use. On a *fixed* vertex set, re-placing a single vertex `v` off the affine hull of
its neighbors keeps every edge of `H` row-independent, provided the edges *not* incident to `v`
were already row-independent: the untouched rows stay independent, and the star rows at
`v` are independent from them and from each other because the displacement vectors `p v - p' uᵢ`
are linearly independent. This is the fixed-`V` analogue of
`typeI_edgeSetRowIndependent_extend` (which instead adjoins a fresh `Option V` vertex). -/

/-- **Zero-extension row-independence lift (conditional core), dimension three.** Let `H` be a
graph on `V`, `v` a vertex, and `H - E_H(v) = H.deleteIncidenceSet v` the graph with the edges at
`v` removed. Suppose the edges of `H.deleteIncidenceSet v` are row-independent at `p'`, and `p`
agrees with `p'` away from `v`. If the displacement vectors `p v - p' u` at the neighbors `u` of
`v` are linearly independent, then the edges of `H` are row-independent at `p`.

The conditional form of the blueprint's `lem:zero-extension-rowIndependent`: the
linear-independence hypothesis on the displacements is exactly what the unconditional lift
supplies by placing `v` off the affine hull of its (at most three) neighbors. The proof mirrors
`typeI_edgeSetRowIndependent_extend`: `H.edgeSet` splits into the block of edges not incident to
`v` (whose rows agree with those of `H.deleteIncidenceSet v` at `p'`, since `p` and `p'` agree on
their endpoints) and the star at `v`. Both the independence of the star rows and their
span-disjointness from the first block are read off the test-motion detector `Ψ` — evaluation of
a row at motions supported at `v` — which annihilates every non-incident row and sends each star
row to `innerₗ` of its displacement vector. -/
theorem zero_extension_edgeSetRowIndependent_extend {V : Type*} {H : SimpleGraph V} {v : V}
    {p' p : Framework V 3} (hagree : ∀ w, w ≠ v → p w = p' w)
    (h : (H.deleteIncidenceSet v).EdgeSetRowIndependent p' Set.univ)
    (hLI : LinearIndependent ℝ (fun u : H.neighborSet v => p v - p' u.val)) :
    H.EdgeSetRowIndependent p Set.univ := by
  classical
  -- The inclusion `(H - E_H(v)).edgeSet ↪ H.edgeSet` and the star map `neighborSet v → H.edgeSet`.
  have hH'le : H.deleteIncidenceSet v ≤ H := deleteIncidenceSet_le H v
  set inclOld : (H.deleteIncidenceSet v).edgeSet → H.edgeSet :=
    fun e' => ⟨e'.val, edgeSet_mono hH'le e'.property⟩ with hinclOld_def
  have hinclOld_inj : Function.Injective inclOld := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext h1
  -- `mem_edgeSet` / `mem_neighborSet` are `Iff.rfl`, so membership of `s(v, u)` in `H.edgeSet`
  -- and adjacency `H.Adj v u` are definitionally the neighbor-set membership (avoid `.mpr`/`.mp`
  -- dot notation on these, which hits the `Iff.rfl` "unknown constant" trap).
  have hstar_mem : ∀ u : H.neighborSet v, s(v, u.val) ∈ H.edgeSet := fun u => u.2
  set star : H.neighborSet v → H.edgeSet := fun u => ⟨s(v, u.val), hstar_mem u⟩ with hstar_def
  have hstar_ne : ∀ u : H.neighborSet v, u.val ≠ v :=
    fun u => (u.2 : H.Adj v u.val).ne'
  have hstar_inj : Function.Injective star := fun u₁ u₂ heq =>
    Subtype.ext (Sym2.congr_right.mp (congrArg Subtype.val heq))
  -- The test-motion detector `Ψ`: evaluate a dual functional at motions supported at `v`.
  set X : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Framework V 3 :=
    LinearMap.single ℝ (fun _ : V => EuclideanSpace ℝ (Fin 3)) v with hX_def
  set Ψ : Module.Dual ℝ (Framework V 3) →ₗ[ℝ] Module.Dual ℝ (EuclideanSpace ℝ (Fin 3)) :=
    X.dualMap with hΨ_def
  -- `Ψ` sends each star row to `innerₗ` of its displacement vector.
  have hΨstar : ∀ u : H.neighborSet v,
      Ψ (H.rigidityRow p (star u)) = innerₗ (EuclideanSpace ℝ (Fin 3)) (p v - p' u.val) := by
    intro u
    ext α
    simp only [hΨ_def, LinearMap.dualMap_apply, hX_def, LinearMap.single_apply, hstar_def,
      rigidityRow_apply, rigidityMap_apply, Pi.single_eq_same, Pi.single_eq_of_ne (hstar_ne u),
      sub_zero, hagree u.val (hstar_ne u), innerₗ_apply_apply]
  -- `innerₗ` is injective, so `Ψ ∘ star-rows` is independent (from `hLI`).
  have hinnerₗ_ker : LinearMap.ker (innerₗ (EuclideanSpace ℝ (Fin 3))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have hmm := LinearMap.congr_fun hm m
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at hmm
    exact inner_self_eq_zero.mp hmm
  have hΨstar_li : LinearIndependent ℝ (Ψ ∘ (H.rigidityRow p ∘ star)) := by
    have heq : (Ψ ∘ (H.rigidityRow p ∘ star)) =
        (innerₗ (EuclideanSpace ℝ (Fin 3))) ∘ (fun u : H.neighborSet v => p v - p' u.val) := by
      funext u; exact hΨstar u
    rw [heq]
    exact hLI.map' _ hinnerₗ_ker
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  set oldSet : Set H.edgeSet := Set.range inclOld with holdSet_def
  set newSet : Set H.edgeSet := Set.range star with hnewSet_def
  -- Every edge either avoids `v` (old block) or is a star edge at `v` (new block).
  have h_cover : (Set.univ : Set H.edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    induction e with
    | h x y =>
      have hadj : H.Adj x y := he
      rcases eq_or_ne x v with hx | hx
      · subst hx
        exact Or.inr ⟨⟨y, hadj⟩, Subtype.ext rfl⟩
      · rcases eq_or_ne y v with hy | hy
        · subst hy
          exact Or.inr ⟨⟨x, hadj.symm⟩, Subtype.ext Sym2.eq_swap⟩
        · exact Or.inl ⟨⟨s(x, y), deleteIncidenceSet_adj.mpr ⟨hadj, hx, hy⟩⟩,
            Subtype.ext rfl⟩
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- Independence of the old block: its rows agree with `H.deleteIncidenceSet v`'s at `p'`.
    rw [holdSet_def, linearIndepOn_range_iff hinclOld_inj]
    have hrow_old : (H.rigidityRow p ∘ inclOld) = (H.deleteIncidenceSet v).rigidityRow p' := by
      funext e'
      obtain ⟨e, he⟩ := e'
      induction e with
      | h x y =>
        obtain ⟨-, hxv, hyv⟩ := deleteIncidenceSet_adj.mp he
        ext motion
        simp only [Function.comp_apply, hinclOld_def, rigidityRow_apply, rigidityMap_apply,
          hagree x hxv, hagree y hyv]
    rw [hrow_old]
    exact linearIndepOn_univ_iff.mp
      ((edgeSetRowIndependent_iff_linearIndepOn_rigidityRow _ _ _).mp h)
  · -- Independence of the star rows: `Ψ ∘ star-rows` is independent, so star-rows are too.
    rw [hnewSet_def, linearIndepOn_range_iff hstar_inj]
    exact LinearIndependent.of_comp Ψ hΨstar_li
  · -- Disjoint spans: `Ψ` kills the old block and is injective on the star span.
    have hold_ker : Submodule.span ℝ (H.rigidityRow p '' oldSet) ≤ LinearMap.ker Ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, he_old, rfl⟩
      rw [holdSet_def] at he_old
      obtain ⟨e', rfl⟩ := he_old
      obtain ⟨e, he⟩ := e'
      induction e with
      | h x y =>
        obtain ⟨-, hxv, hyv⟩ := deleteIncidenceSet_adj.mp he
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        ext α
        simp only [hΨ_def, LinearMap.dualMap_apply, hX_def, LinearMap.single_apply, hinclOld_def,
          rigidityRow_apply, rigidityMap_apply, Pi.single_eq_of_ne hxv,
          Pi.single_eq_of_ne hyv, sub_self, inner_zero_right, LinearMap.zero_apply]
    have hnew_disj : Disjoint (Submodule.span ℝ (H.rigidityRow p '' newSet)) (LinearMap.ker Ψ) := by
      rw [hnewSet_def, ← Set.range_comp]
      exact hΨstar_li.disjoint_span_range_ker
    exact hnew_disj.symm.mono_left hold_ker

/-- **Zero-extension row-independence lift (unconditional), dimension three** — the blueprint's
`lem:zero-extension-rowIndependent`. Let `H` be a graph on `V` and `v` a vertex of degree at most
three whose neighbors have affinely independent images under a placement `p'` at which the edges
of `H - E_H(v) = H.deleteIncidenceSet v` are row-independent. Then there is a placement `p`,
agreeing with `p'` away from `v`, at which the edges of `H` are row-independent.

Since the neighbor images are affinely independent and number at most three, their affine hull is
a proper affine subspace of `ℝ³`, so some point `q` lies off it; placing `v` there
(`Function.update p' v q`) makes the displacement vectors `q - p' uᵢ` linearly independent (a
vanishing combination with nonzero weight-sum would exhibit `q` as an affine combination of the
`p' uᵢ`, and one with zero weight-sum vanishes by affine independence), so
`zero_extension_edgeSetRowIndependent_extend` applies. The affine-independence and degree
hypotheses are discharged at a generic placement in general position by
`zero_extension_genericRank_add_degree` (`cor:zero-extension-degree-le-three`,
`JacobsZeroExtension.lean`). -/
theorem zero_extension_edgeSetRowIndependent_lift {V : Type*} {H : SimpleGraph V} {v : V}
    [Fintype ↥(H.neighborSet v)] {p' : Framework V 3}
    (h : (H.deleteIncidenceSet v).EdgeSetRowIndependent p' Set.univ)
    (hdeg : Fintype.card ↥(H.neighborSet v) ≤ 3)
    (hAI : AffineIndependent ℝ (fun u : H.neighborSet v => p' u.val)) :
    ∃ p : Framework V 3, (∀ w, w ≠ v → p w = p' w) ∧ H.EdgeSetRowIndependent p Set.univ := by
  classical
  set w : H.neighborSet v → EuclideanSpace ℝ (Fin 3) := fun u => p' u.val with hw_def
  -- The affine hull of at most three affinely independent points is a proper subspace of `ℝ³`.
  have hspan_ne_top : affineSpan ℝ (Set.range w) ≠ ⊤ := by
    intro htop
    have hcard := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop
    rw [finrank_euclideanSpace, Fintype.card_fin] at hcard
    omega
  obtain ⟨q, hq⟩ : ∃ q, q ∉ affineSpan ℝ (Set.range w) := by
    by_contra hcon
    exact hspan_ne_top (top_unique fun x _ => not_not.mp fun hx => hcon ⟨x, hx⟩)
  -- Placing `v` at `q` makes the displacement vectors linearly independent.
  have hLI : LinearIndependent ℝ (fun u : H.neighborSet v => q - w u) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have key : (∑ u, c u) • q = ∑ u, c u • w u := by
      have h2 : ∑ u, (c u • q - c u • w u) = 0 := by
        rw [← hc]; exact Finset.sum_congr rfl fun u _ => (smul_sub (c u) q (w u)).symm
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, sub_eq_zero] at h2
      exact h2
    by_cases hC : (∑ u, c u) = 0
    · have hsum0 : ∑ u, c u • w u = 0 := by rw [← key, hC, zero_smul]
      exact fun u => hAI.eq_zero_of_sum_eq_zero hC hsum0 u (Finset.mem_univ u)
    · exfalso
      apply hq
      have hsum1 : ∑ u, c u / (∑ u', c u') = 1 := by rw [← Finset.sum_div, div_self hC]
      have hqcomb : q = ∑ u, (c u / (∑ u', c u')) • w u := by
        rw [← inv_smul_smul₀ hC q, key, Finset.smul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [smul_smul, div_eq_inv_mul]
      rw [hqcomb, ← Finset.affineCombination_eq_linear_combination Finset.univ w
        (fun u => c u / (∑ u', c u')) hsum1]
      exact affineCombination_mem_affineSpan hsum1 w
  -- Assemble via the conditional core at `p = Function.update p' v q`.
  refine ⟨Function.update p' v q, fun x hx => Function.update_of_ne hx q p', ?_⟩
  refine zero_extension_edgeSetRowIndependent_extend ?_ h ?_
  · exact fun x hx => Function.update_of_ne hx q p'
  · simpa only [Function.update_self, hw_def] using hLI

end SimpleGraph


end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0001/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityLaman_LamanTheorem.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/LamanTheorem.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/








/-!
# Laman's theorem

Laman's theorem (Pollaczek-Geiringer 1927, Laman 1970): for `n ≥ 2` vertices, a simple graph is
generically rigid in the plane iff it contains a Laman spanning subgraph (a `(2, 3)`-tight
subgraph on the same vertex set):

```
G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

* `IsLaman.isGenericallyRigid_two` — the (⇐) direction, by Henneberg induction
  on `Fintype.card V`.
* `IsGenericallyRigid.exists_isLaman_le` — the (⇒) direction: a basis of the rows of the rigidity
  matrix at a suitable placement spans a `(2, 3)`-sparse, hence Laman, subgraph.
* `isGenericallyRigid_two_iff_exists_isLaman_le` — the iff, composed from
  the two directional theorems above.

`IsGenericallyRigid.card_mul_le_two` is the edge count `IsGenericallyRigid.card_mul_le`
(`Framework.lean`) at `d = 2`. The blueprint's `sec:laman-theorem` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Edge-count corollary for generic rigidity in dimension 2: every generically
rigid graph in the plane has at least `2 * #V − 3` edges. Phrased additively
per the no-`ℕ`-subtraction rule.

The `d = 2` specialization of `IsGenericallyRigid.card_mul_le`. -/
theorem IsGenericallyRigid.card_mul_le_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) : 2 * Fintype.card V ≤ G.edgeSet.ncard + 3 :=
  hG.card_mul_le

/-- **Strong-form (⇐) Laman, internal helper.** Strong induction on
`Fintype.card V`: every Laman graph admits an *injective* rigid placement in
dim 2 (`IsGenericallyRigidInj 2`).

Both inductive moves (Type I and Type II) are handled by the unconditional
per-move preservation theorems in `HennebergRigidity.lean`; the Type II step's
non-collinearity gap is discharged inside
`typeII_isGenericallyRigidInj_two` via openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) and a perturbation of one neighbor of the
new vertex off the line through the other two. Base case `n = 2` reduces to `K₂` via
`eq_top_of_card_eq_two` plus iso transport. -/
private theorem IsLaman.isGenericallyRigidInj_two_of_card :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {G : SimpleGraph V}, G.IsLaman → G.IsGenericallyRigidInj 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV G h
    classical
    by_cases hV3 : 3 ≤ Fintype.card V
    · -- Inductive step: apply the flat-form `exists_typeI_or_typeII_reverse`, reconstruct the
      -- iso to `typeI G' a b` / `typeII G' x y c` at this callsite (the flat form describes the
      -- smaller graph directly via `comap` and `fromEdgeSet`), then IH + operation-form forward
      -- preservation + iso transport.
      obtain ⟨v, hbranch⟩ := Henneberg.IsLaman.exists_typeI_or_typeII_reverse h hV3
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_hdeg, a, b, hab, hN_iff, hG'_lam⟩ |
        ⟨_hdeg, x, y, c, hxy, hcx, hcy, hN_iff, hnxy, hG'_lam⟩
      · -- Type I: build `G ≃g typeI (G.comap _) a b` and transport.
        have ih_G' : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V)) a b :=
          Henneberg.isoTypeIOfTwoNeighbors a.property.symm b.property.symm hN_iff
        exact (Henneberg.typeI_isGenericallyRigidInj_two ih_G' hab).iso φ.symm
      · -- Type II: build `G ≃g typeII (G.comap _ ⊔ fromEdgeSet {s(x, y)}) x y c` and transport.
        have ih_G' :
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeII
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)) x y c :=
          Henneberg.isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm
            hN_iff hnxy
        exact (Henneberg.typeII_isGenericallyRigidInj_two ih_G' hxy hcx.symm hcy.symm).iso φ.symm
    · -- Base case: `Fintype.card V ≤ 2`. The `≤ 1` sub-cases contradict Laman
      -- tightness (a Laman graph has `#E + 3 = 2 * #V`, infeasible for #V ≤ 1
      -- in `ℕ`); `n = 2` reduces to K₂ via `eq_top_of_card_eq_two` + iso transport.
      have hE := h.edgeSet_ncard
      rw [Nat.card_eq_fintype_card] at hE
      have hcard2 : Fintype.card V = 2 := by omega
      have h_top : G = ⊤ := h.eq_top_of_card_eq_two hcard2
      rw [h_top]
      have e : V ≃ Fin 2 := Fintype.equivFinOfCardEq hcard2
      exact (top_fin_two_isGenericallyRigidInj 1).iso (Iso.completeGraph e.symm)

/-- Every Laman graph is generically rigid in dimension 2.

Proved by Henneberg induction on `Fintype.card V`: the K₂ base case is
`top_fin_two_isGenericallyRigidInj 1` (dimension `1 + 1`); the inductive step uses
`IsLaman.exists_typeI_or_typeII_reverse` plus per-move rigidity preservation
plus iso transport (`IsGenericallyRigidInj.iso`). The induction maintains the
strong predicate `IsGenericallyRigidInj` (existence of an *injective* rigid
placement) — see `IsLaman.isGenericallyRigidInj_two_of_card`. -/
theorem IsLaman.isGenericallyRigid_two [Finite V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 := by
  have : Fintype V := Fintype.ofFinite V
  exact (IsLaman.isGenericallyRigidInj_two_of_card _ rfl h).toIsGenericallyRigid

/-- Every graph that is generically rigid in dimension 2 contains a Laman
spanning subgraph.

Proved by one half of Pollaczek-Geiringer's and Laman's characterization of
row-independence in the plane (Jordán 2016, Theorem 2.2.1): an edge set
row-independent at a placement with no three points collinear is
`(2, 3)`-sparse, so a basis of the rows (size `2n − 3`) spans a Laman subgraph.

Proof: pick a placement `p` that is both infinitesimally rigid for `G`
*and* affinely-spanning on every size-`≥ 3` subset, via the
property-polymorphic perturbation `exists_affinelySpanning_of_eventually`
specialised at `IsInfinitesimallyRigid.eventually` and `d = 2`. At `p`, the rank
lower bound from IR + rank-nullity feeds
`exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`, which extracts
a row-independent edge set `I ⊆ G.edgeSet` of size `2|V| - 3`. The spanning
subgraph `H = fromEdgeSet (Subtype.val '' I)` is `(2, 3)`-sparse by
`isSparse_of_edgeSetRowIndependent_dim_two` (using affine spanning of `p`)
and has exactly `2|V| - 3` edges by construction, hence is `(2, 3)`-tight,
i.e.\ Laman. -/
theorem IsGenericallyRigid.exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigid 2) (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  -- Step 1: pick an IR + affinely-spanning placement.
  obtain ⟨p₀, hp₀⟩ := h
  obtain ⟨p, hp_IR, hp_aff⟩ := exists_affinelySpanning_of_eventually hp₀.eventually
  -- Step 2: rank lower bound at `p` (from IR + rank-nullity).
  have h_rank_ge : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3 := by
    have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ 3 := hp_IR
    have h_total : Module.finrank ℝ (Framework V 2) = 2 * Fintype.card V := by
      rw [Framework.finrank, mul_comm]
    have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
    omega
  -- Step 3: basis-pick at `p`.
  obtain ⟨I, hI_card, hI⟩ :=
    exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two h_rank_ge
  -- Step 4: assemble the spanning subgraph and verify Laman.
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  have hH_ncard : H.edgeSet.ncard = 2 * Fintype.card V - 3 := by
    rw [hH_edgeSet, Set.ncard_image_of_injective _ Subtype.val_injective, hI_card]
  refine ⟨H, hHG, isSparse_of_edgeSetRowIndependent_dim_two hp_aff hI, ?_⟩
  rw [hH_ncard, Nat.card_eq_fintype_card]
  omega

/-- **Laman's theorem** (Pollaczek-Geiringer 1927, Laman 1970). A simple graph on `n ≥ 2`
vertices is generically rigid in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` and `IsGenericallyRigid.exists_isLaman_le`. -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (hV : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman :=
  ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph


end
end BundleSource0002

section BundleSource0003
/- Source: Papers/RigidityDefinitions.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Rigidity/BarJoint.lean at commit
 e457fde9100c9b7226bd4d81af6860f210a531ab.
-/







@[expose] public section

/-!
# Real bar--joint infinitesimal rigidity

This file gives the actual linearized bar constraints over `ℝ`.  Generic rank
is defined as the attained maximum rank among all placements, not as a desired
combinatorial formula.  A graph is generically rigid when its maximum rank
agrees with the complete graph on the same vertex type; this convention also
handles vertex sets of size smaller than the ambient affine dimension.
-/

namespace Papers.Rigidity
namespace BarJoint

open scoped BigOperators

/-- A point in real coordinate dimension `d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- A placement of the vertices in real coordinate dimension `d`. -/
abbrev Placement (V : Type) (d : ℕ) := V → Point d

/-- An infinitesimal velocity assignment. -/
abbrev Velocity (V : Type) (d : ℕ) := V → Point d

/-- The linearized squared-length constraint for the ordered pair `(v,w)`. -/
def edgeConstraint {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) : ℝ :=
  ∑ i : Fin d, (p v i - p w i) * (u v i - u w i)

theorem edgeConstraint_comm {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) :
    edgeConstraint p u v w = edgeConstraint p u w v := by
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One bar constraint as a real linear functional of the velocity. -/
def edgeFunctional {V : Type} {d : ℕ}
    (p : Placement V d) (v w : V) : Velocity V d →ₗ[ℝ] ℝ where
  toFun u := edgeConstraint p u v w
  map_add' u z := by
    simp only [edgeConstraint, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c u := by
    simp only [edgeConstraint, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem edgeFunctional_apply {V : Type} {d : ℕ}
    (p : Placement V d) (u : Velocity V d) (v w : V) :
    edgeFunctional p v w u = edgeConstraint p u v w :=
  rfl

/--
The real rigidity operator.  Its target uses all ordered vertex pairs; nonedges
and diagonal pairs receive zero.  Doubling an undirected row does not alter
rank, while this fixed target makes ranks of different graphs directly
comparable.
-/
noncomputable def rigidityOperator {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    Velocity V d →ₗ[ℝ] (V × V → ℝ) := by
  classical
  exact LinearMap.pi fun vw ↦
    if G.Adj vw.1 vw.2 then edgeFunctional p vw.1 vw.2 else 0

@[simp] theorem rigidityOperator_apply_of_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) (v w : V)
    (h : G.Adj v w) :
    rigidityOperator G p u (v, w) = edgeConstraint p u v w := by
  classical
  simp [rigidityOperator, h]

@[simp] theorem rigidityOperator_apply_of_not_adj {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) (v w : V)
    (h : ¬ G.Adj v w) :
    rigidityOperator G p u (v, w) = 0 := by
  classical
  simp [rigidityOperator, h]

/-- A velocity is an infinitesimal motion precisely when every bar row vanishes. -/
def IsInfinitesimalMotion {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) : Prop :=
  u ∈ (rigidityOperator G p).ker

theorem isInfinitesimalMotion_iff {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (u : Velocity V d) :
    IsInfinitesimalMotion G p u ↔
      ∀ v w : V, G.Adj v w → edgeConstraint p u v w = 0 := by
  classical
  constructor
  · intro hu v w hvw
    have hZero : rigidityOperator G p u = 0 := LinearMap.mem_ker.mp hu
    have hAt := congrFun hZero (v, w)
    simpa [rigidityOperator, hvw] using hAt
  · intro hu
    rw [IsInfinitesimalMotion, LinearMap.mem_ker]
    funext vw
    by_cases h : G.Adj vw.1 vw.2
    · simpa [rigidityOperator, h] using hu vw.1 vw.2 h
    · simp [rigidityOperator, h]

/-- Every constant velocity field is a translational infinitesimal motion. -/
theorem translation_isInfinitesimalMotion {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) (a : Point d) :
    IsInfinitesimalMotion G p (fun _ ↦ a) := by
  rw [isInfinitesimalMotion_iff]
  intro v w _
  simp [edgeConstraint]

theorem finrank_velocity {V : Type} [Fintype V] (d : ℕ) :
    Module.finrank ℝ (Velocity V d) = Fintype.card V * d := by
  rw [Module.finrank_pi_fintype]
  simp

theorem rigidityOperator_bot {V : Type} {d : ℕ} (p : Placement V d) :
    rigidityOperator (⊥ : SimpleGraph V) p = 0 := by
  classical
  ext u vw
  simp [rigidityOperator]

/-- The rank of the actual rigidity operator at one placement. -/
noncomputable def rigidityRank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : ℕ :=
  Module.finrank ℝ (LinearMap.range (rigidityOperator G p))

@[simp] theorem rigidityRank_bot {V : Type} [Fintype V] {d : ℕ}
    (p : Placement V d) :
    rigidityRank (⊥ : SimpleGraph V) p = 0 := by
  rw [rigidityRank, rigidityOperator_bot, LinearMap.range_zero]
  simp

theorem rigidityRank_le_velocityFinrank {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) :
    rigidityRank G p ≤ Module.finrank ℝ (Velocity V d) := by
  exact LinearMap.finrank_range_le (rigidityOperator G p)

/-- The proposition that a specified operator rank occurs at a real placement. -/
def RankIsAttained {V : Type} [Fintype V] (G : SimpleGraph V) (d r : ℕ) : Prop :=
  ∃ p : Placement V d, rigidityRank G p = r

/--
The generic rigidity rank, defined as the greatest rank actually attained by a
real placement.  The search bound is the dimension of the velocity space, and
`rigidityRank_le_velocityFinrank` proves that no placement is omitted.
-/
noncomputable def genericRigidityRank {V : Type} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (RankIsAttained G d)
    (Module.finrank ℝ (Velocity V d))

theorem rigidityRank_le_genericRigidityRank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (p : Placement V d) :
    rigidityRank G p ≤ genericRigidityRank G d := by
  classical
  simpa [genericRigidityRank] using
    (Nat.le_findGreatest (P := RankIsAttained G d)
      (rigidityRank_le_velocityFinrank G p) (show RankIsAttained G d (rigidityRank G p) from ⟨p, rfl⟩))

theorem genericRigidityRank_le_velocityFinrank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    genericRigidityRank G d ≤ Module.finrank ℝ (Velocity V d) := by
  classical
  simpa [genericRigidityRank] using
    (Nat.findGreatest_le (P := RankIsAttained G d)
      (Module.finrank ℝ (Velocity V d)))

/-- The maximum rank is attained by at least one real placement. -/
theorem exists_rigidityRank_eq_genericRigidityRank {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) :
    ∃ p : Placement V d, rigidityRank G p = genericRigidityRank G d := by
  classical
  let p₀ : Placement V d := 0
  have h := Nat.findGreatest_spec (P := RankIsAttained G d)
    (rigidityRank_le_velocityFinrank G p₀)
    (show RankIsAttained G d (rigidityRank G p₀) from ⟨p₀, rfl⟩)
  simpa [genericRigidityRank, RankIsAttained] using h

@[simp] theorem genericRigidityRank_bot {V : Type} [Fintype V] (d : ℕ) :
    genericRigidityRank (⊥ : SimpleGraph V) d = 0 := by
  rcases exists_rigidityRank_eq_genericRigidityRank (⊥ : SimpleGraph V) d with ⟨p, hp⟩
  rw [← hp, rigidityRank_bot]

theorem eq_bot_of_subsingleton {V : Type} [Subsingleton V] (G : SimpleGraph V) :
    G = ⊥ := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  constructor
  · intro h
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact (G.loopless.irrefl v h).elim
  · intro h
    exact (SimpleGraph.bot_adj v w).mp h |>.elim

/-- On zero or one vertex, every simple graph has actual generic rank zero. -/
theorem genericRigidityRank_eq_zero_of_subsingleton
    {V : Type} [Fintype V] [Subsingleton V] (G : SimpleGraph V) (d : ℕ) :
    genericRigidityRank G d = 0 := by
  rw [eq_bot_of_subsingleton G, genericRigidityRank_bot]

/--
Maximum-rank semantics of generic infinitesimal rigidity.  Comparison with the
complete graph is valid uniformly, including when `Fintype.card V < d + 1`.
-/
def IsGenericallyRigidInDimension {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  genericRigidityRank G d =
    genericRigidityRank (SimpleGraph.completeGraph V) d

/-- The dimension-three specialization used by the body--pin theorem. -/
def IsGenericallyRigidInR3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsGenericallyRigidInDimension G 3

@[simp] theorem completeGraph_isGenericallyRigidInDimension
    (V : Type) [Fintype V] (d : ℕ) :
    IsGenericallyRigidInDimension (SimpleGraph.completeGraph V) d :=
  rfl

@[simp] theorem completeGraph_isGenericallyRigidInR3
    (V : Type) [Fintype V] :
    IsGenericallyRigidInR3 (SimpleGraph.completeGraph V) :=
  rfl


end BarJoint
end Papers.Rigidity


end
end BundleSource0003

section BundleSource0004
/- Source: Papers/RigidityConing.lean -/




@[expose] public section

/-!
# The actual planar-to-spatial coning motion equivalence

The cone apex is placed at the origin and a planar vertex `q v` at
`(q v 0, q v 1, 1)`. After subtracting the apex translation, its spoke
equation determines the third velocity coordinate. The remaining bar
equations are precisely the original planar equations.

This is a necessary coning dependency of the overlap/Laman argument in
Section 3. It is outside the frozen pair-pin closure and remains uncompiled.
-/

namespace Papers.Rigidity.Coning

noncomputable section

open BarJoint Matrix
open scoped Matrix BigOperators

variable {V : Type}

/-- Add one actual vertex adjacent to every old vertex. -/
def cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | none, none => False
    | some v, some w => G.Adj v w
    | _, _ => True
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm
  loopless := by
    constructor
    intro a
    cases a with
    | none => exact id
    | some v => exact G.loopless.irrefl v

/-- The height-one coned placement; its nongeneric nature is harmless
for establishing a lower bound on the attained maximum rank. -/
def placement (q : Placement V 2) : Placement (Option V) 3
  | none => 0
  | some v => ![q v 0, q v 1, 1]

/-- A planar motion and an arbitrary apex translation give this literal
spatial velocity assignment. -/
def liftVelocity (q : Placement V 2) (a : Point 3) (w : Velocity V 2) :
    Velocity (Option V) 3
  | none => a
  | some v => a + ![w v 0, w v 1, -(q v 0 * w v 0 + q v 1 * w v 1)]

/-- Remove the apex translation and retain the two planar coordinates. -/
def extractVelocity : Velocity (Option V) 3 →ₗ[ℝ] Velocity V 2 where
  toFun u v := ![u (some v) 0 - u none 0, u (some v) 1 - u none 1]
  map_add' u w := by
    funext v i
    fin_cases i <;> simp <;> ring
  map_smul' a u := by
    funext v i
    fin_cases i <;> simp <;> ring

theorem extract_liftVelocity (q : Placement V 2) (a : Point 3) (w : Velocity V 2) :
    extractVelocity (liftVelocity q a w) = w := by
  funext v i
  fin_cases i <;> simp [extractVelocity, liftVelocity]

theorem liftVelocity_spoke (q : Placement V 2) (a : Point 3) (w : Velocity V 2)
    (v : V) : edgeConstraint (placement q) (liftVelocity q a w) none (some v) = 0 := by
  simp [edgeConstraint, placement, liftVelocity, Fin.sum_univ_succ]
    <;> ring

theorem liftVelocity_old_edge (q : Placement V 2) (a : Point 3) (w : Velocity V 2)
    (v v' : V) :
    edgeConstraint (placement q) (liftVelocity q a w) (some v) (some v') =
      edgeConstraint q w v v' := by
  simp [edgeConstraint, placement, liftVelocity, Fin.sum_univ_succ]
    <;> ring

theorem old_edge_eq_extract (q : Placement V 2) (u : Velocity (Option V) 3)
    (v v' : V) :
    edgeConstraint (placement q) u (some v) (some v') =
      edgeConstraint q (extractVelocity u) v v' := by
  simp [edgeConstraint, placement, extractVelocity, Fin.sum_univ_succ]
    <;> ring

theorem spoke_eq (q : Placement V 2) (u : Velocity (Option V) 3) (v : V) :
    edgeConstraint (placement q) u none (some v) =
      q v 0 * (u (some v) 0 - u none 0) +
      q v 1 * (u (some v) 1 - u none 1) + u (some v) 2 - u none 2 := by
  simp [edgeConstraint, placement, Fin.sum_univ_succ]
    <;> ring

theorem lift_isMotion (G : SimpleGraph V) (q : Placement V 2)
    (a : Point 3) (w : Velocity V 2) (hw : IsInfinitesimalMotion G q w) :
    IsInfinitesimalMotion (cone G) (placement q) (liftVelocity q a w) := by
  rw [isInfinitesimalMotion_iff] at hw ⊢
  intro v v' h
  cases v with
  | none =>
      cases v' with
      | none => exact False.elim h
      | some v' => exact liftVelocity_spoke q a w v'
  | some v =>
      cases v' with
      | none =>
          rw [edgeConstraint_comm]
          exact liftVelocity_spoke q a w v
      | some v' =>
          rw [liftVelocity_old_edge]
          exact hw v v' h

theorem extract_isMotion (G : SimpleGraph V) (q : Placement V 2)
    (u : Velocity (Option V) 3)
    (hu : IsInfinitesimalMotion (cone G) (placement q) u) :
    IsInfinitesimalMotion G q (extractVelocity u) := by
  rw [isInfinitesimalMotion_iff] at hu ⊢
  intro v w hvw
  rw [← old_edge_eq_extract]
  exact hu (some v) (some w) hvw

/-- The spoke equations make the reconstruction exact at every vertex. -/
theorem lift_extract_eq (G : SimpleGraph V) (q : Placement V 2)
    (u : Velocity (Option V) 3)
    (hu : IsInfinitesimalMotion (cone G) (placement q) u) :
    liftVelocity q (u none) (extractVelocity u) = u := by
  funext v i
  cases v with
  | none => rfl
  | some v =>
      have h := (isInfinitesimalMotion_iff (cone G) (placement q) u).mp hu
        none (some v) trivial
      rw [spoke_eq] at h
      fin_cases i
      · simp [liftVelocity, extractVelocity]
      · simp [liftVelocity, extractVelocity]
      · change u none 2 +
          -(q v 0 * (u (some v) 0 - u none 0) +
            q v 1 * (u (some v) 1 - u none 1)) = u (some v) 2
        linarith only [h]

def motionToPlanar (G : SimpleGraph V) (q : Placement V 2) :
    (rigidityOperator (cone G) (placement q)).ker →ₗ[ℝ]
      (Point 3 × (rigidityOperator G q).ker) where
  toFun u := (u.val none, ⟨extractVelocity u.val, extract_isMotion G q u.val u.property⟩)
  map_add' u w := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_add extractVelocity u.val w.val)
  map_smul' a u := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_smul extractVelocity a u.val)

theorem motionToPlanar_bijective (G : SimpleGraph V) (q : Placement V 2) :
    Function.Bijective (motionToPlanar G q) := by
  constructor
  · intro u w h
    have ha : u.val none = w.val none := congrArg Prod.fst h
    have hw : extractVelocity u.val = extractVelocity w.val :=
      congrArg (fun z : Point 3 × (rigidityOperator G q).ker => z.2.val) h
    apply Subtype.ext
    rw [← lift_extract_eq G q u.val u.property,
      ← lift_extract_eq G q w.val w.property, ha, hw]
  · rintro ⟨a, w⟩
    refine ⟨⟨liftVelocity q a w.val, lift_isMotion G q a w.val w.property⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact Subtype.ext (extract_liftVelocity q a w.val)

/-- The exact ordinary motion-kernel isomorphism, including the apex
translation and every original planar velocity coordinate. -/
def motionEquiv (G : SimpleGraph V) (q : Placement V 2) :
    (rigidityOperator (cone G) (placement q)).ker ≃ₗ[ℝ]
      (Point 3 × (rigidityOperator G q).ker) :=
  LinearEquiv.ofBijective (motionToPlanar G q) (motionToPlanar_bijective G q)

theorem finrank_motion [Fintype V] (G : SimpleGraph V) (q : Placement V 2) :
    Module.finrank ℝ (rigidityOperator (cone G) (placement q)).ker =
      3 + Module.finrank ℝ (rigidityOperator G q).ker := by
  rw [(motionEquiv G q).finrank_eq, Module.finrank_prod]
  simp [Point]

/-- At this literal coned placement, every spoke pays one rank in addition
to the full actual planar rigidity rank. No genericity premise is used. -/
theorem rigidityRank_cone_placement [Fintype V]
    (G : SimpleGraph V) (q : Placement V 2) :
    rigidityRank (cone G) (placement q) = Fintype.card V + rigidityRank G q := by
  have hcone := (rigidityOperator (cone G) (placement q)).finrank_range_add_finrank_ker
  have hbase := (rigidityOperator G q).finrank_range_add_finrank_ker
  rw [finrank_motion, finrank_velocity] at hcone
  rw [finrank_velocity] at hbase
  simp only [Fintype.card_option] at hcone
  change rigidityRank (cone G) (placement q) + _ = _ at hcone
  change rigidityRank G q + _ = _ at hbase
  omega

end

end Papers.Rigidity.Coning

end
end BundleSource0004

section BundleSource0005
/- Source: Papers/RigidityLamanBridge.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31BryanInterop/RealizedRank.lean, commit
e457fde9100c9b7226bd4d81af6860f210a531ab.
-/



@[expose] public section

/-!
# Comparing the realized bar--joint rigidity ranks

This module imports both projects' actual rigidity operators. The coordinate
conversion is linear, and the edge-indexed constraints determine the same
kernel as the ordered-pair constraints.
-/

namespace Papers.Rigidity.LamanInterop

open scoped InnerProductSpace

/-- The coordinatewise linear equivalence between the two placement spaces. -/
noncomputable def frameworkEquiv (V : Type) (d : ℕ) :
    BarJoint.Placement V d ≃ₗ[ℝ] SimpleGraph.Framework V d :=
  LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm

@[simp]
theorem frameworkEquiv_apply {V : Type} {d : ℕ}
    (p : BarJoint.Placement V d) (v : V) (i : Fin d) :
    frameworkEquiv V d p v i = p v i := rfl

@[simp]
theorem frameworkEquiv_symm_apply {V : Type} {d : ℕ}
    (p : SimpleGraph.Framework V d) (v : V) (i : Fin d) :
    (frameworkEquiv V d).symm p v i = p v i := rfl

/-- Each Euclidean inner-product constraint is the original coordinate sum. -/
theorem inner_edge_eq {V : Type} {d : ℕ}
    (p : BarJoint.Placement V d) (u : BarJoint.Velocity V d) (v w : V) :
    ⟪frameworkEquiv V d p v - frameworkEquiv V d p w,
      frameworkEquiv V d u v - frameworkEquiv V d u w⟫_ℝ =
      BarJoint.edgeConstraint p u v w := by
  simp [PiLp.inner_apply, BarJoint.edgeConstraint, mul_comm]

/-- The two operators have exactly the same motions after coordinate conversion. -/
theorem mem_ker_rigidityMap_iff {V : Type} {d : ℕ}
    (G : SimpleGraph V) (p : BarJoint.Placement V d) (u : BarJoint.Velocity V d) :
    frameworkEquiv V d u ∈ (G.RigidityMap (frameworkEquiv V d p)).ker ↔
      u ∈ (BarJoint.rigidityOperator G p).ker := by
  change _ ↔ BarJoint.IsInfinitesimalMotion G p u
  rw [BarJoint.isInfinitesimalMotion_iff]
  constructor
  · intro hu v w hvw
    have h := congrFun (LinearMap.mem_ker.mp hu) ⟨s(v, w), hvw⟩
    rw [G.rigidityMap_apply (frameworkEquiv V d p) (frameworkEquiv V d u) v w hvw,
      inner_edge_eq] at h
    exact h
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext e
    obtain ⟨e, he⟩ := e
    induction e with
    | h v w =>
      simpa only [SimpleGraph.rigidityMap_apply, inner_edge_eq, Pi.zero_apply] using
        hu v w he

/-- Equality of the realized ranks, for every finite graph and every placement. -/
theorem rigidityRank_eq_finrank_range {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : BarJoint.Placement V d) :
    BarJoint.rigidityRank G p =
      Module.finrank ℝ (LinearMap.range (G.RigidityMap (frameworkEquiv V d p))) := by
  let E := frameworkEquiv V d
  let B := G.RigidityMap (E p)
  have hk : (B.comp E.toLinearMap).ker = (BarJoint.rigidityOperator G p).ker := by
    ext u
    exact mem_ker_rigidityMap_iff G p u
  have hB := (B.comp E.toLinearMap).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp_of_range_eq_top B E.range, hk] at hB
  have hA := (BarJoint.rigidityOperator G p).finrank_range_add_finrank_ker
  change Module.finrank ℝ (BarJoint.rigidityOperator G p).range = _
  exact Nat.add_right_cancel (hA.trans hB.symm)

/-- Equality of motion-space dimensions, including all degenerate placements
and all finite orders. -/
theorem finrank_ker_eq {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : BarJoint.Placement V d) :
    Module.finrank ℝ (BarJoint.rigidityOperator G p).ker =
      Module.finrank ℝ (G.RigidityMap (frameworkEquiv V d p)).ker := by
  have hA := (BarJoint.rigidityOperator G p).finrank_range_add_finrank_ker
  have hB := (G.RigidityMap (frameworkEquiv V d p)).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (BarJoint.Velocity V d) =
      Module.finrank ℝ (SimpleGraph.Framework V d) := (frameworkEquiv V d).finrank_eq
  have hr := rigidityRank_eq_finrank_range G p
  unfold BarJoint.rigidityRank at hr
  omega

end Papers.Rigidity.LamanInterop


end
end BundleSource0005

section BundleSource0006
/- Source: Papers/RigidityTriangle.lean -/





@[expose] public section

/-!
# The actual infinitesimal motions of a noncollinear triangle

The three ordinary bar rows have rank three.  Evaluation of the six
Euclidean twist coordinates is injective on the three vertices and its
image is exactly their bar-motion kernel.  This supplies the surviving
triangle of a tetrahedral body after a vertex is deleted; no rigidity
or body representation is assumed in the conclusion.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix BigOperators

/-- The usual noncollinearity condition, expressed by two differences. -/
def NoncollinearTriangle (q : Fin 3 → Vec3) : Prop :=
  LinearIndependent ℝ ![q 1 - q 0, q 2 - q 0]

/-- The three literal bar rows, in the order `01`, `02`, `12`. -/
def triangleBarMatrix (q : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3 × Fin 3) ℝ :=
  ![fun a => if a.1 = 0 then q 0 a.2 - q 1 a.2
      else if a.1 = 1 then q 1 a.2 - q 0 a.2 else 0,
    fun a => if a.1 = 0 then q 0 a.2 - q 2 a.2
      else if a.1 = 2 then q 2 a.2 - q 0 a.2 else 0,
    fun a => if a.1 = 1 then q 1 a.2 - q 2 a.2
      else if a.1 = 2 then q 2 a.2 - q 1 a.2 else 0]

theorem triangleBarMatrix_mulVec (q : Fin 3 → Vec3)
    (u : Fin 3 × Fin 3 → ℝ) :
    (triangleBarMatrix q) *ᵥ u =
      ![BarJoint.edgeConstraint q (fun i j => u (i, j)) 0 1,
        BarJoint.edgeConstraint q (fun i j => u (i, j)) 0 2,
        BarJoint.edgeConstraint q (fun i j => u (i, j)) 1 2] := by
  ext i
  fin_cases i <;>
    simp [triangleBarMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_three, BarJoint.edgeConstraint] <;> ring

theorem triangleBarMatrix_rows_independent (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) :
    LinearIndependent ℝ (triangleBarMatrix q).row := by
  rw [Matrix.row_def, Fintype.linearIndependent_iff]
  intro c hc
  have h01 : c 0 • (q 1 - q 0) + c 1 • (q 2 - q 0) = 0 := by
    ext j
    have hj := congrFun hc (0, j)
    simp [triangleBarMatrix, Fin.sum_univ_three] at hj
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    linarith
  have hcoeff := LinearIndependent.pair_iff.mp hq (c 0) (c 1) h01
  have h12 : q 1 - q 2 ≠ 0 := by
    intro hz
    have heq : q 1 - q 0 = q 2 - q 0 := by rw [sub_eq_zero.mp hz]
    have hind : (0 : Fin 2) = 1 := hq.injective heq
    exact (by decide : (0 : Fin 2) ≠ 1) hind
  have hlast : c 2 • (q 1 - q 2) = 0 := by
    ext j
    have hj := congrFun hc (1, j)
    simpa [triangleBarMatrix, Fin.sum_univ_three, hcoeff.1, hcoeff.2] using hj
  have hc2 : c 2 = 0 := (smul_eq_zero.mp hlast).resolve_right h12
  intro i
  fin_cases i <;> simp [hcoeff.1, hcoeff.2, hc2]

theorem triangleBarMatrix_rank (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) : (triangleBarMatrix q).rank = 3 := by
  simpa using (triangleBarMatrix_rows_independent q hq).rank_matrix

/-- A Euclidean twist preserves each actual squared-distance differential. -/
theorem twist_preserves_bar (X : Twist) (x y : Vec3) :
    ∑ i : Fin 3, (x i - y i) *
      (evaluateTwist x X i - evaluateTwist y X i) = 0 := by
  simp [evaluateTwist_apply, cross_apply, Fin.sum_univ_three]
  ring

/-- A twist fixing a noncollinear triangle is the zero twist. -/
theorem twist_eq_zero_of_fixing_triangle (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) (X : Twist)
    (hX : ∀ i, evaluateTwist (q i) X = 0) : X = 0 := by
  have hv : X.1 ⨯₃ (q 1 - q 0) = 0 := by
    ext i
    have h0 := congrFun (hX 0) i
    have h1 := congrFun (hX 1) i
    fin_cases i <;>
      simp [evaluateTwist_apply, cross_apply] at h0 h1 ⊢ <;> linarith
  have hw : X.1 ⨯₃ (q 2 - q 0) = 0 := by
    ext i
    have h0 := congrFun (hX 0) i
    have h2 := congrFun (hX 2) i
    fin_cases i <;>
      simp [evaluateTwist_apply, cross_apply] at h0 h2 ⊢ <;> linarith
  have hω : X.1 = 0 := by
    by_contra hne
    have hdepv : ¬ LinearIndependent ℝ ![X.1, q 1 - q 0] := by
      intro h
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr h) hv
    have hdepw : ¬ LinearIndependent ℝ ![X.1, q 2 - q 0] := by
      intro h
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr h) hw
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a • X.1 = q 1 - q 0 := by
      simpa only [LinearIndependent.pair_iff' hne, not_forall_not] using hdepv
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b • X.1 = q 2 - q 0 := by
      simpa only [LinearIndependent.pair_iff' hne, not_forall_not] using hdepw
    apply (crossProduct_ne_zero_iff_linearIndependent.mpr hq)
    rw [← ha, ← hb]
    simp
  apply Prod.ext hω
  simpa [evaluateTwist_apply, hω] using hX 0

/-- Evaluation on the nine literal vertex coordinates of the triangle. -/
def triangleTwistOperator (q : Fin 3 → Vec3) :
    Twist →ₗ[ℝ] (Fin 3 × Fin 3 → ℝ) :=
  LinearMap.pi fun a => (LinearMap.proj a.2).comp (evaluateTwist (q a.1))

@[simp] theorem triangleTwistOperator_apply (q : Fin 3 → Vec3)
    (X : Twist) (a : Fin 3 × Fin 3) :
    triangleTwistOperator q X a = evaluateTwist (q a.1) X a.2 := rfl

theorem triangleTwistOperator_injective (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) : Function.Injective (triangleTwistOperator q) := by
  intro X Y h
  apply sub_eq_zero.mp
  apply twist_eq_zero_of_fixing_triangle q hq (X - Y)
  intro i
  ext j
  have hij := congrFun h (i, j)
  simpa only [triangleTwistOperator_apply, map_sub, Pi.sub_apply, Pi.zero_apply,
    sub_eq_zero] using hij

theorem triangleTwistOperator_range_eq_ker (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) :
    (triangleTwistOperator q).range = (triangleBarMatrix q).mulVecLin.ker := by
  have hle : (triangleTwistOperator q).range ≤
      (triangleBarMatrix q).mulVecLin.ker := by
    rintro _ ⟨X, rfl⟩
    rw [LinearMap.mem_ker]
    change (triangleBarMatrix q) *ᵥ (triangleTwistOperator q X) = 0
    rw [triangleBarMatrix_mulVec]
    ext i
    fin_cases i <;>
      simpa [BarJoint.edgeConstraint] using twist_preserves_bar X _ _
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (triangleTwistOperator_injective q hq), finrank_twist]
  have hnull := (triangleBarMatrix q).mulVecLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (triangleBarMatrix q).mulVecLin.range = 3 :=
    triangleBarMatrix_rank q hq
  rw [hrange] at hnull
  norm_num at hnull
  omega

/-- The actual isomorphism, so extracting a body's twist is a linear
operation on its surviving triangle velocities. -/
def triangleTwistEquiv (q : Fin 3 → Vec3) (hq : NoncollinearTriangle q) :
    Twist ≃ₗ[ℝ] (triangleBarMatrix q).mulVecLin.ker := by
  let F : Twist →ₗ[ℝ] (triangleBarMatrix q).mulVecLin.ker :=
    (triangleTwistOperator q).codRestrict _ (fun X => by
      rw [← triangleTwistOperator_range_eq_ker q hq]
      exact ⟨X, rfl⟩)
  apply LinearEquiv.ofBijective F
  constructor
  · intro X Y h
    apply triangleTwistOperator_injective q hq
    exact congrArg Subtype.val h
  · intro u
    have hu : (u : Fin 3 × Fin 3 → ℝ) ∈ (triangleTwistOperator q).range :=
      (triangleTwistOperator_range_eq_ker q hq).ge u.property
    obtain ⟨X, hX⟩ := hu
    exact ⟨X, Subtype.ext hX⟩

@[simp] theorem triangleTwistEquiv_apply (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) (X : Twist) (a : Fin 3 × Fin 3) :
    (triangleTwistEquiv q hq X).1 a = evaluateTwist (q a.1) X a.2 := rfl

theorem triangleTwistEquiv_symm_fit (q : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q) (u : (triangleBarMatrix q).mulVecLin.ker)
    (i j : Fin 3) :
    evaluateTwist (q i) ((triangleTwistEquiv q hq).symm u) j = u.1 (i, j) := by
  exact congrFun (congrArg Subtype.val ((triangleTwistEquiv q hq).apply_symm_apply u)) (i, j)

/-- Every actual triangle bar motion has a unique Euclidean twist. -/
theorem exists_unique_twist_of_triangleMotion (q u : Fin 3 → Vec3)
    (hq : NoncollinearTriangle q)
    (hu : ∀ i j : Fin 3, i ≠ j → BarJoint.edgeConstraint q u i j = 0) :
    ∃! X : Twist, ∀ i, u i = evaluateTwist (q i) X := by
  let uf : Fin 3 × Fin 3 → ℝ := fun a => u a.1 a.2
  have huf : uf ∈ (triangleBarMatrix q).mulVecLin.ker := by
    rw [LinearMap.mem_ker]
    change (triangleBarMatrix q) *ᵥ uf = 0
    rw [triangleBarMatrix_mulVec]
    simp [uf, hu 0 1 (by decide), hu 0 2 (by decide), hu 1 2 (by decide)]
  rw [← triangleTwistOperator_range_eq_ker q hq] at huf
  obtain ⟨X, hX⟩ := huf
  have hfit (i : Fin 3) : u i = evaluateTwist (q i) X := by
    ext j
    exact (congrFun hX (i, j)).symm
  refine ⟨X, hfit, ?_⟩
  intro Y hY
  apply triangleTwistOperator_injective q hq
  ext a
  exact (congrFun (hY a.1) a.2).symm.trans (congrFun (hfit a.1) a.2)

end

end Papers.Rigidity

end
end BundleSource0006

section BundleSource0007
/- Source: Papers/RigidityStatements.lean -/





@[expose] public section

/-!
# Exact targets for the clique-covered rigidity paper

This module records propositions to be proved.  A declaration with a name ending
in `Claim` is a definition of the intended proposition, not an asserted theorem.
No principal claim is claimed to be established merely by this module compiling.
-/

namespace Papers.Rigidity

open BarJoint
open scoped Classical

/-- Vertex connectivity, including the usual strict lower bound on the order. -/
def VertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- Every edge is contained in a complete subgraph on four vertices. -/
def K4Covered {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w →
    ∃ S : Finset V, S.card = 4 ∧ v ∈ S ∧ w ∈ S ∧ G.IsClique (S : Set V)

/-- The complete mathematical assertion of Theorem 1.1. -/
def SixConnectedK4RigidityClaim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    VertexConnected G 6 → K4Covered G → IsGenericallyRigidInR3 G

/-- A vertex set spanning a generically rigid induced subgraph. -/
def RigidInducedSubgraph {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsGenericallyRigidInR3 (G.induce (S : Set V))

/-- Every edge lies in an actual generically rigid subgraph on at least four
vertices. The witnessing graph may omit edges of the ambient induced graph. -/
def RigidSubgraphCovered {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w → ∃ S : Finset V, 4 ≤ S.card ∧
    ∃ (hv : v ∈ S) (hw : w ∈ S) (H : SimpleGraph {x : V // x ∈ S}),
      H ≤ G.induce (S : Set V) ∧ H.Adj ⟨v, hv⟩ ⟨w, hw⟩ ∧
        IsGenericallyRigidInR3 H

/-- The equivalent induced-subgraph formulation, proved equivalent in
`RigidityClosure` rather than taken as an additional hypothesis. -/
def RigidInducedCovered {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w → ∃ S : Finset V,
    4 ≤ S.card ∧ v ∈ S ∧ w ∈ S ∧ RigidInducedSubgraph G S

/-- The first assertion of Corollary 1.2, with the same generality as the paper. -/
def RigidClusterCoveredRigidityClaim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    VertexConnected G 6 → RigidSubgraphCovered G →
    IsGenericallyRigidInR3 G

/-- Complete each member of a family of vertex sets, keeping the same vertices. -/
def clusterCompletion {V I : Type} (C : I → Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ i, v ∈ C i ∧ w ∈ C i
  symm := by
    constructor
    rintro v w ⟨hvw, i, hv, hw⟩
    exact ⟨Ne.symm hvw, i, hw, hv⟩
  loopless := by constructor; intro v; simp

/-- All pairs of vertices in the set belong to the rigidity closure of the
ambient graph. Unlike `RigidInducedSubgraph`, the rigidity may be transmitted
through vertices outside the set. -/
def RigidCluster {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  genericRigidityRank (G ⊔ clusterCompletion (fun _ : Unit => S)) 3 =
    genericRigidityRank G 3

/-- The more general spanning-completion assertion in Corollary 1.2. -/
def RigidClusterCompletionRigidityClaim : Prop :=
  ∀ (V I : Type) [Fintype V] (G : SimpleGraph V) (C : I → Finset V),
    (∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i)) →
    VertexConnected (clusterCompletion C) 6 → IsGenericallyRigidInR3 G

end Papers.Rigidity

end
end BundleSource0007

section BundleSource0008
/- Source: Papers/RigidityVertexPin.lean -/





@[expose] public section

/-!
# Exact elimination of the three coordinates of a deleted vertex

An incident tetrahedron leaves a noncollinear triangle after deleting the
vertex.  The triangle's actual bar motion determines a unique twist.  All
bars at the deleted vertex are equivalent to equality of those twists'
evaluated velocities there.  The resulting isomorphism is between actual
operator kernels, and gives the rank identity used in Lemma 3.1.
-/

namespace Papers.Rigidity.VertexPin

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix BigOperators

variable {V B : Type}

abbrev DeletedVertex (v : V) := {w : V // w ≠ v}

def deletedGraph (G : SimpleGraph V) (v : V) : SimpleGraph (DeletedVertex v) :=
  G.induce {w | w ≠ v}

def deletedPlacement (p : Placement V 3) (v : V) : Placement (DeletedVertex v) 3 :=
  fun w => p w.1

abbrev DeletedMotions (G : SimpleGraph V) (p : Placement V 3) (v : V) :=
  (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).ker

/-- A family of actual tetrahedra at `v` covering every incident edge.
It is constructed from K4 coverage separately; no motion or rank condition
is part of the combinatorial data. -/
structure IncidentTetrahedra (G : SimpleGraph V) (v : V) (B : Type) where
  triangle : B → Fin 3 → DeletedVertex v
  injective : ∀ b, Function.Injective (triangle b)
  clique : ∀ b (i j : Fin 3), i ≠ j →
    G.Adj (triangle b i).1 (triangle b j).1
  spoke : ∀ b (i : Fin 3), G.Adj v (triangle b i).1
  covers : ∀ w, G.Adj v w → ∃ b i, (triangle b i).1 = w

/-- All actual four-cliques containing `v`; duplicate descriptions and
pairwise overlap are allowed and impose no new combinatorial assumption. -/
def IncidentK4 (G : SimpleGraph V) (v : V) :=
  {S : Finset V // S.card = 4 ∧ v ∈ S ∧ G.IsClique (S : Set V)}

instance [Fintype V] (G : SimpleGraph V) (v : V) : Fintype (IncidentK4 G v) := by
  unfold IncidentK4
  infer_instance

private theorem erased_incidentK4_card (G : SimpleGraph V) (v : V)
    (S : IncidentK4 G v) : (S.1.erase v).card = 3 := by
  rw [Finset.card_erase_of_mem S.2.2.1, S.2.1]

private def incidentTriangleEquiv (G : SimpleGraph V) (v : V) (S : IncidentK4 G v) :
    Fin 3 ≃ {w : V // w ∈ S.1.erase v} :=
  (Finset.equivFinOfCardEq (erased_incidentK4_card G v S)).symm

private def incidentTriangle (G : SimpleGraph V) (v : V) (S : IncidentK4 G v) :
    Fin 3 → DeletedVertex v := fun i =>
  ⟨(incidentTriangleEquiv G v S i).1,
    (Finset.mem_erase.mp (incidentTriangleEquiv G v S i).2).1⟩

private theorem incidentTriangle_mem (G : SimpleGraph V) (v : V)
    (S : IncidentK4 G v) (i : Fin 3) : (incidentTriangle G v S i).1 ∈ S.1 :=
  (Finset.mem_erase.mp (incidentTriangleEquiv G v S i).2).2

private theorem incidentTriangle_injective (G : SimpleGraph V) (v : V)
    (S : IncidentK4 G v) : Function.Injective (incidentTriangle G v S) := by
  intro i j hij
  apply (incidentTriangleEquiv G v S).injective
  exact Subtype.ext (congrArg (fun w : DeletedVertex v => w.val) hij)

/-- The incident-tetrahedron family is supplied by the paper's literal
K4-coverage hypothesis. -/
@[no_expose] def tetrahedraOfK4Covered (G : SimpleGraph V) (v : V) (hG : K4Covered G) :
    IncidentTetrahedra G v (IncidentK4 G v) where
  triangle := incidentTriangle G v
  injective := incidentTriangle_injective G v
  clique := by
    intro S i j hij
    exact S.2.2.2 (incidentTriangle_mem G v S i) (incidentTriangle_mem G v S j)
      (fun heq => hij (incidentTriangle_injective G v S (Subtype.ext heq)))
  spoke := by
    intro S i
    exact S.2.2.2 S.2.2.1 (incidentTriangle_mem G v S i)
      (Ne.symm (incidentTriangle G v S i).2)
  covers := by
    intro w hvw
    obtain ⟨S, hc, hv, hw, hclique⟩ := hG v w hvw
    let S' : IncidentK4 G v := ⟨S, hc, hv, hclique⟩
    have hwe : w ∈ S.erase v := Finset.mem_erase.mpr ⟨Ne.symm hvw.ne, hw⟩
    let w' : {z : V // z ∈ S.erase v} := ⟨w, hwe⟩
    refine ⟨S', (incidentTriangleEquiv G v S').symm w', ?_⟩
    exact congrArg Subtype.val ((incidentTriangleEquiv G v S').apply_symm_apply w')

theorem incidentK4_nonempty_of_neighbor (G : SimpleGraph V) (v : V)
    (hG : K4Covered G) (w : V) (hvw : G.Adj v w) : Nonempty (IncidentK4 G v) := by
  obtain ⟨S, hc, hv, _, hclique⟩ := hG v w hvw
  exact ⟨S, hc, hv, hclique⟩

namespace IncidentTetrahedra

variable {G : SimpleGraph V} {v : V}

def trianglePoints (T : IncidentTetrahedra G v B) (p : Placement V 3) (b : B) :
    Fin 3 → Vec3 := fun i => p (T.triangle b i).1

def NoncollinearAt (T : IncidentTetrahedra G v B) (p : Placement V 3) : Prop :=
  ∀ b, NoncollinearTriangle (T.trianglePoints p b)

/-- The three star directions form a basis at each incident tetrahedron.
This is ordinary affine independence of its four points. -/
def TransverseAt (T : IncidentTetrahedra G v B) (p : Placement V 3) : Prop :=
  ∀ b, LinearIndependent ℝ (fun i : Fin 3 => p v - T.trianglePoints p b i)

def restrictTriangle (T : IncidentTetrahedra G v B) (p : Placement V 3) (b : B) :
    DeletedMotions G p v →ₗ[ℝ] (Fin 3 × Fin 3 → ℝ) where
  toFun u a := u.1 (T.triangle b a.1) a.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictTriangle_mem_ker (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (b : B) (u : DeletedMotions G p v) :
    T.restrictTriangle p b u ∈ (triangleBarMatrix (T.trianglePoints p b)).mulVecLin.ker := by
  have hmotion := (isInfinitesimalMotion_iff
    (deletedGraph G v) (deletedPlacement p v) u.1).mp u.2
  have hbar (i j : Fin 3) (hij : i ≠ j) :
      edgeConstraint (T.trianglePoints p b)
        (fun i => u.1 (T.triangle b i)) i j = 0 := by
    exact hmotion (T.triangle b i) (T.triangle b j) (T.clique b i j hij)
  rw [LinearMap.mem_ker]
  change (triangleBarMatrix (T.trianglePoints p b)) *ᵥ (T.restrictTriangle p b u) = 0
  rw [triangleBarMatrix_mulVec]
  simpa [restrictTriangle] using
    show ![edgeConstraint (T.trianglePoints p b) (fun i => u.1 (T.triangle b i)) 0 1,
      edgeConstraint (T.trianglePoints p b) (fun i => u.1 (T.triangle b i)) 0 2,
      edgeConstraint (T.trianglePoints p b) (fun i => u.1 (T.triangle b i)) 1 2] = 0 by
      simp [hbar 0 1 (by decide), hbar 0 2 (by decide), hbar 1 2 (by decide)]

/-- The twist extracted by the proved triangle isomorphism. -/
def bodyTwist (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (b : B) : DeletedMotions G p v →ₗ[ℝ] Twist :=
  (triangleTwistEquiv (T.trianglePoints p b) (hp b)).symm.toLinearMap.comp
    ((T.restrictTriangle p b).codRestrict _ (T.restrictTriangle_mem_ker p b))

theorem bodyTwist_fit (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (b : B) (u : DeletedMotions G p v) (i : Fin 3) :
    evaluateTwist (T.trianglePoints p b i) (T.bodyTwist p hp b u) =
      u.1 (T.triangle b i) := by
  ext j
  exact triangleTwistEquiv_symm_fit (T.trianglePoints p b) (hp b)
    ⟨T.restrictTriangle p b u, T.restrictTriangle_mem_ker p b u⟩ i j

/-- The literal common-pin equations, using one incident body as reference. -/
def commonPinOperator (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) :
    DeletedMotions G p v →ₗ[ℝ] (B → Vec3) :=
  LinearMap.pi fun b => (evaluateTwist (p v)).comp
    (T.bodyTwist p hp b - T.bodyTwist p hp base)

@[simp] theorem commonPinOperator_apply (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base b : B)
    (u : DeletedMotions G p v) :
    T.commonPinOperator p hp base u b =
      evaluateTwist (p v) (T.bodyTwist p hp b u) -
        evaluateTwist (p v) (T.bodyTwist p hp base u) := by
  change evaluateTwist (p v) (T.bodyTwist p hp b u - T.bodyTwist p hp base u) = _
  exact map_sub (evaluateTwist (p v)) _ _

def restrictFullMotion (T : IncidentTetrahedra G v B) (p : Placement V 3) :
    (rigidityOperator G p).ker →ₗ[ℝ] DeletedMotions G p v where
  toFun u := ⟨fun w => u.1 w.1, by
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b hab
    exact (isInfinitesimalMotion_iff G p u.1).mp u.2 a.1 b.1 hab⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem velocity_eq_of_three_bars (q : Fin 3 → Vec3) (x y : Vec3)
    (X : Twist) (hq : LinearIndependent ℝ (fun i => x - q i))
    (hbar : ∀ i : Fin 3, (x - q i) ⬝ᵥ (y - evaluateTwist (q i) X) = 0) :
    y = evaluateTwist x X := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i => x - q i
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.linearIndependent_row_iff_isUnit.mp hq)
  have hzero : A *ᵥ (y - evaluateTwist x X) = 0 := by
    ext i
    have hi := hbar i
    have ht := twist_preserves_bar X x (q i)
    change (x - q i) ⬝ᵥ (y - evaluateTwist x X) = 0
    simp only [dotProduct, Pi.sub_apply, Fin.sum_univ_three] at hi ht ⊢
    linear_combination hi - ht
  apply sub_eq_zero.mp
  apply hinj
  simpa using hzero

/-- Each full graph motion assigns to `v` the velocity of every incident
body.  The proof uses its three actual bars, not a body-motion hypothesis. -/
theorem fullMotion_at_vertex (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (ht : T.TransverseAt p)
    (u : (rigidityOperator G p).ker) (b : B) :
    u.1 v = evaluateTwist (p v) (T.bodyTwist p hp b (T.restrictFullMotion p u)) := by
  apply velocity_eq_of_three_bars (T.trianglePoints p b) (p v) (u.1 v) _ (ht b)
  intro i
  rw [T.bodyTwist_fit]
  exact (isInfinitesimalMotion_iff G p u.1).mp u.2 v (T.triangle b i).1 (T.spoke b i)

theorem restrictFullMotion_mem_commonPin_ker (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (ht : T.TransverseAt p)
    (base : B) (u : (rigidityOperator G p).ker) :
    T.restrictFullMotion p u ∈ (T.commonPinOperator p hp base).ker := by
  rw [LinearMap.mem_ker]
  ext b j
  rw [T.commonPinOperator_apply, ← T.fullMotion_at_vertex p hp ht u b,
    ← T.fullMotion_at_vertex p hp ht u base]
  simp

/-- Extend a deleted motion by the velocity predicted by the reference
triangle.  Compatibility is checked separately below. -/
def extendDeletedMotion (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) :
    DeletedMotions G p v →ₗ[ℝ] Velocity V 3 where
  toFun u w := if hw : w = v then evaluateTwist (p v) (T.bodyTwist p hp base u)
    else u.1 ⟨w, hw⟩
  map_add' u z := by
    ext w j
    by_cases hw : w = v <;> simp [hw] <;> abel
  map_smul' c u := by
    ext w j
    by_cases hw : w = v <;> simp [hw]

@[simp] theorem extendDeletedMotion_vertex (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B)
    (u : DeletedMotions G p v) :
    T.extendDeletedMotion p hp base u v = evaluateTwist (p v) (T.bodyTwist p hp base u) := by
  simp [extendDeletedMotion]

@[simp] theorem extendDeletedMotion_other (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B)
    (u : DeletedMotions G p v) (w : DeletedVertex v) :
    T.extendDeletedMotion p hp base u w.1 = u.1 w := by
  simp [extendDeletedMotion, w.2]

theorem extendDeletedMotion_is_motion (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (base : B)
    (u : (T.commonPinOperator p hp base).ker) :
    IsInfinitesimalMotion G p (T.extendDeletedMotion p hp base u.1) := by
  have hpin (b : B) : evaluateTwist (p v) (T.bodyTwist p hp b u.1) =
      evaluateTwist (p v) (T.bodyTwist p hp base u.1) := by
    have hb := congrFun (LinearMap.mem_ker.mp u.2) b
    simpa only [commonPinOperator_apply, Pi.zero_apply, sub_eq_zero] using hb
  have hspoke (w : V) (hvw : G.Adj v w) :
      edgeConstraint p (T.extendDeletedMotion p hp base u.1) v w = 0 := by
    obtain ⟨b, i, rfl⟩ := T.covers w hvw
    change ∑ j : Fin 3, (p v j - p (T.triangle b i).1 j) *
      (T.extendDeletedMotion p hp base u.1 v j -
        T.extendDeletedMotion p hp base u.1 (T.triangle b i).1 j) = 0
    rw [T.extendDeletedMotion_vertex, T.extendDeletedMotion_other, ← hpin b,
      ← T.bodyTwist_fit p hp b u.1 i]
    exact twist_preserves_bar _ _ _
  rw [isInfinitesimalMotion_iff]
  intro a b hab
  by_cases ha : a = v
  · subst a
    exact hspoke b hab
  by_cases hb : b = v
  · subst b
    rw [edgeConstraint_comm]
    exact hspoke a hab.symm
  have hdeleted := (isInfinitesimalMotion_iff (deletedGraph G v)
    (deletedPlacement p v) u.1.1).mp u.1.2 ⟨a, ha⟩ ⟨b, hb⟩ hab
  simpa [edgeConstraint, deletedPlacement, extendDeletedMotion, ha, hb] using hdeleted

/-- The exact kernel isomorphism that eliminates the three velocity
coordinates at `v`. -/
def fullMotionEquivCommonPinKernel (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (ht : T.TransverseAt p)
    (base : B) :
    (rigidityOperator G p).ker ≃ₗ[ℝ] (T.commonPinOperator p hp base).ker where
  toFun u := ⟨T.restrictFullMotion p u,
    T.restrictFullMotion_mem_commonPin_ker p hp ht base u⟩
  invFun u := ⟨T.extendDeletedMotion p hp base u.1,
    T.extendDeletedMotion_is_motion p hp base u⟩
  left_inv u := by
    apply Subtype.ext
    ext w j
    by_cases hw : w = v
    · subst w
      change T.extendDeletedMotion p hp base (T.restrictFullMotion p u) v j = u.val v j
      rw [T.extendDeletedMotion_vertex]
      exact congrFun (T.fullMotion_at_vertex p hp ht u base).symm j
    · simp [restrictFullMotion, extendDeletedMotion, hw]
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    ext w j
    simp [restrictFullMotion, extendDeletedMotion, w.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Rank loss under literal vertex deletion equals three plus the rank
of the actual common-pin compatibility operator. -/
theorem rigidityRank_deletion_identity [Fintype V] [Fintype B]
    (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (ht : T.TransverseAt p) (base : B) :
    rigidityRank G p = rigidityRank (deletedGraph G v) (deletedPlacement p v) + 3 +
      Module.finrank ℝ (T.commonPinOperator p hp base).range := by
  have hker := (T.fullMotionEquivCommonPinKernel p hp ht base).finrank_eq
  have hfull := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hdeleted := (rigidityOperator (deletedGraph G v)
    (deletedPlacement p v)).finrank_range_add_finrank_ker
  have hpin := (T.commonPinOperator p hp base).finrank_range_add_finrank_ker
  have hcard : Fintype.card (DeletedVertex v) + 1 = Fintype.card V := by
    have h := Fintype.card_subtype_compl (fun w : V => w = v)
    have hpositive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    simp only [Fintype.card_subtype_eq] at h
    change Fintype.card (DeletedVertex v) = Fintype.card V - 1 at h
    omega
  rw [finrank_velocity] at hfull hdeleted
  change Module.finrank ℝ (T.commonPinOperator p hp base).range +
      Module.finrank ℝ (T.commonPinOperator p hp base).ker =
      Module.finrank ℝ (rigidityOperator (deletedGraph G v)
        (deletedPlacement p v)).ker at hpin
  unfold rigidityRank
  omega

end IncidentTetrahedra

end

end Papers.Rigidity.VertexPin

end
end BundleSource0008

section BundleSource0009
/- Source: Papers/RigidityGenericRank.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from Rigidity/GraphNecessity.lean and Rigidity/RegularPlacement.lean,
Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture commit
e457fde9100c9b7226bd4d81af6860f210a531ab.
-/










@[expose] public section

/-!
# Open dense simultaneous maximum-rank placements

These are statements about the actual real bar-constraint operators. Their
proofs use determinant polynomials and the finite intersection of open dense
sets, rather than assuming the existence of generic realizations.
-/

namespace Papers.Rigidity.BarJoint

/-- With the velocity held fixed, the rigidity operator is linear in the
placement coordinates. -/
noncomputable def rigidityOperatorLinearInPlacement
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) :
    Placement V d →ₗ[ℝ] (Velocity V d →ₗ[ℝ] (V × V → ℝ)) where
  toFun := rigidityOperator G
  map_add' p q := by
    apply LinearMap.ext
    intro u
    funext vw
    classical
    by_cases h : G.Adj vw.1 vw.2
    · simp only [LinearMap.add_apply, Pi.add_apply,
        rigidityOperator_apply_of_adj G _ _ _ _ h, edgeConstraint]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp [rigidityOperator_apply_of_not_adj G _ _ _ _ h]
  map_smul' a p := by
    apply LinearMap.ext
    intro u
    funext vw
    classical
    by_cases h : G.Adj vw.1 vw.2
    · simp only [LinearMap.smul_apply, Pi.smul_apply,
        rigidityOperator_apply_of_adj G _ _ _ _ h, edgeConstraint,
        smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp [rigidityOperator_apply_of_not_adj G _ _ _ _ h]

/-- The rigidity operator as a continuous map from placements to continuous
linear maps on velocities.  Both conversions are legitimate because the
source spaces are finite-dimensional. -/
noncomputable def continuousRigidityOperatorMap
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) :
    Placement V d →L[ℝ] (Velocity V d →L[ℝ] (V × V → ℝ)) := by
  let inner : (Velocity V d →ₗ[ℝ] (V × V → ℝ)) ≃ₗ[ℝ]
      (Velocity V d →L[ℝ] (V × V → ℝ)) :=
    LinearMap.toContinuousLinearMap
  exact LinearMap.toContinuousLinearMap
    (inner.toLinearMap.comp (rigidityOperatorLinearInPlacement G))

@[simp] theorem continuousRigidityOperatorMap_apply
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (p : Placement V d) (u : Velocity V d) (vw : V × V) :
    continuousRigidityOperatorMap G p u vw = rigidityOperator G p u vw :=
  rfl

/-- A fixed lower bound on rigidity rank is an open condition on placements. -/
theorem isOpen_setOf_le_rigidityRank
    {V : Type} [Fintype V] {d : ℕ} (G : SimpleGraph V) (r : ℕ) :
    IsOpen {p : Placement V d | r ≤ rigidityRank G p} := by
  let F := continuousRigidityOperatorMap (d := d) G
  have hopen : IsOpen
      (F ⁻¹' {L : Velocity V d →L[ℝ] (V × V → ℝ) |
        (r : Cardinal) ≤ (L : Velocity V d →ₗ[ℝ] (V × V → ℝ)).rank}) :=
    (isOpen_setOf_nat_le_rank (E := Velocity V d) (F := V × V → ℝ) r).preimage
      F.continuous
  convert hopen using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  change r ≤ Module.finrank ℝ (rigidityOperator G p).range ↔
    (r : Cardinal) ≤ Module.rank ℝ (rigidityOperator G p).range
  rw [← Module.finrank_eq_rank]
  norm_cast


open Module
open scoped BigOperators

/-- A placement is regular for `G` when the rigidity operator has its maximum
attained rank there. -/
def IsRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) (p : Placement V d) : Prop :=
  rigidityRank G p = genericRigidityRank G d

/-- A placement is generic when it is regular for every simple graph on the
same labelled vertex set. -/
def IsGenericPlacement {V : Type} [Fintype V] {d : ℕ}
    (p : Placement V d) : Prop :=
  ∀ G : SimpleGraph V, IsRegularPlacement G p

/-- The regular placements of a fixed graph form an open set. -/
theorem isOpen_isRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) :
    IsOpen {p : Placement V d | IsRegularPlacement G p} := by
  have hopen :=
    isOpen_setOf_le_rigidityRank (d := d) G (genericRigidityRank G d)
  convert hopen using 1
  ext p
  simp only [Set.mem_setOf_eq, IsRegularPlacement]
  constructor
  · intro h
    exact h.ge
  · intro h
    exact le_antisymm (rigidityRank_le_genericRigidityRank G d p) h

/-- The regular placements of a fixed graph are dense. -/
theorem dense_isRegularPlacement {V : Type} [Fintype V] {d : ℕ}
    (G : SimpleGraph V) :
    Dense {p : Placement V d | IsRegularPlacement G p} := by
  classical
  let r := genericRigidityRank G d
  obtain ⟨w, hw⟩ := exists_rigidityRank_eq_genericRigidityRank G d
  have hfin : Module.finrank ℝ
      (LinearMap.range (rigidityOperator G w)) = r := by
    simpa [rigidityRank, r] using hw
  let b : Basis (Fin r) ℝ (LinearMap.range (rigidityOperator G w)) :=
    Module.finBasisOfFinrankEq ℝ _ hfin
  obtain ⟨lift, hlift⟩ :=
    (rigidityOperator G w).rangeRestrict.exists_rightInverse_of_surjective
      (rigidityOperator G w).range_rangeRestrict
  let U₀ : (Fin r → ℝ) →ₗ[ℝ] Velocity V d :=
    lift.comp b.equivFun.symm.toLinearMap
  let T₀ : (Fin r → ℝ) →ₗ[ℝ] (V × V → ℝ) :=
    (LinearMap.range (rigidityOperator G w)).subtype.comp
      b.equivFun.symm.toLinearMap
  have hRwU : (rigidityOperator G w).comp U₀ = T₀ := by
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun hlift (b.equivFun.symm a)
    exact congrArg Subtype.val h
  have hT₀inj : Function.Injective T₀ := by
    intro x y hxy
    apply b.equivFun.symm.injective
    exact Subtype.ext hxy
  have hT₀ker : LinearMap.ker T₀ = ⊥ :=
    LinearMap.ker_eq_bot.mpr hT₀inj
  let φ : (V × V → ℝ) →ₗ[ℝ] (Fin r → ℝ) := T₀.leftInverse
  have hφT₀ : φ.comp T₀ = LinearMap.id := by
    exact T₀.leftInverse_comp_of_inj hT₀ker

  refine dense_iff_inter_open.mpr ?_
  intro O hO ⟨p, hpO⟩
  let q : ℝ → Placement V d := fun t ↦ p + t • (w - p)
  have hq_cont : Continuous q :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hq_zero : q 0 = p := by simp [q]
  have hq_preimage_open : IsOpen (q ⁻¹' O) := hO.preimage hq_cont
  have hzero_preimage : (0 : ℝ) ∈ q ⁻¹' O := by
    simpa [hq_zero] using hpO
  have hpreimage_nhds : q ⁻¹' O ∈ nhds (0 : ℝ) :=
    hq_preimage_open.mem_nhds hzero_preimage
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hpreimage_nhds

  let A₀ : Module.End ℝ (Fin r → ℝ) :=
    φ.comp ((rigidityOperator G p).comp U₀)
  let A₁ : Module.End ℝ (Fin r → ℝ) :=
    φ.comp ((rigidityOperator G (w - p)).comp U₀)
  let e : Basis (Fin r) ℝ (Fin r → ℝ) := Pi.basisFun ℝ (Fin r)
  let M₀ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₀
  let M₁ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₁
  let P : Polynomial ℝ :=
    Matrix.det
      ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C +
        M₀.map Polynomial.C)

  have hoperator_line (t : ℝ) :
      rigidityOperator G (q t) =
        rigidityOperator G p + t • rigidityOperator G (w - p) := by
    change (rigidityOperatorLinearInPlacement G) (p + t • (w - p)) =
      (rigidityOperatorLinearInPlacement G) p +
        t • (rigidityOperatorLinearInPlacement G) (w - p)
    rw [map_add, map_smul]
  have hA_line (t : ℝ) :
      A₀ + t • A₁ = φ.comp ((rigidityOperator G (q t)).comp U₀) := by
    rw [hoperator_line]
    ext a
    simp [A₀, A₁]
  have hP_eval (t : ℝ) :
      P.eval t = LinearMap.det (A₀ + t • A₁) := by
    dsimp only [P]
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    rw [← LinearMap.det_toMatrix e]
    congr 1
    ext i j
    simp [M₀, M₁]
    ring
  have hA_one : A₀ + (1 : ℝ) • A₁ = LinearMap.id := by
    rw [hA_line 1, show q 1 = w by simp [q], hRwU, hφT₀]
  have hP_one : P.eval 1 = 1 := by
    rw [hP_eval, hA_one]
    simp
  have hP_ne : P ≠ 0 := by
    intro hP
    simp [hP] at hP_one

  let Z : Set ℝ := {t | Polynomial.IsRoot P t}
  have hZfinite : Z.Finite := by
    simpa [Z] using Polynomial.finite_setOf_isRoot hP_ne
  have hintervalInfinite : (Set.Ioo (0 : ℝ) ε).Infinite :=
    Set.Ioo_infinite hεpos
  have hnotSubset : ¬ Set.Ioo (0 : ℝ) ε ⊆ Z := by
    intro hsubset
    exact hintervalInfinite (hZfinite.subset hsubset)
  obtain ⟨t, htInterval, htNotRoot⟩ := Set.not_subset.mp hnotSubset
  have hP_t : P.eval t ≠ 0 := by
    simpa [Z, Polynomial.IsRoot] using htNotRoot
  have hA_t_det : LinearMap.det (A₀ + t • A₁) ≠ 0 := by
    simpa [hP_eval t] using hP_t
  have hA_t_ker : LinearMap.ker (A₀ + t • A₁) = ⊥ := by
    by_contra hker
    exact hA_t_det (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  have hA_t_inj : Function.Injective (A₀ + t • A₁) :=
    LinearMap.ker_eq_bot.mp hA_t_ker
  let RqU : (Fin r → ℝ) →ₗ[ℝ] (V × V → ℝ) :=
    (rigidityOperator G (q t)).comp U₀
  have hRqU_inj : Function.Injective RqU := by
    intro x y hxy
    apply hA_t_inj
    rw [hA_line]
    exact congrArg φ hxy
  have hrank_lower : r ≤ rigidityRank G (q t) := by
    rw [rigidityRank]
    calc
      r = Module.finrank ℝ (Fin r → ℝ) := by simp
      _ = Module.finrank ℝ (LinearMap.range RqU) :=
        (LinearMap.finrank_range_of_inj hRqU_inj).symm
      _ ≤ Module.finrank ℝ (LinearMap.range (rigidityOperator G (q t))) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hq_regular : IsRegularPlacement G (q t) := by
    exact le_antisymm (rigidityRank_le_genericRigidityRank G d (q t)) hrank_lower
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos htInterval.1]
    exact htInterval.2
  exact ⟨q t, hball ht_ball, hq_regular⟩

/-- Placements regular for every graph form an open set. -/
theorem isOpen_isGenericPlacement {V : Type} [Fintype V] {d : ℕ} :
    IsOpen {p : Placement V d | IsGenericPlacement p} := by
  rw [show {p : Placement V d | IsGenericPlacement p} =
      ⋂ G : SimpleGraph V, {p : Placement V d | IsRegularPlacement G p} by
    ext p
    simp [IsGenericPlacement]]
  exact isOpen_iInter_of_finite fun G ↦ isOpen_isRegularPlacement G

/-- Placements regular for every graph are dense. -/
theorem dense_isGenericPlacement {V : Type} [Fintype V] {d : ℕ} :
    Dense {p : Placement V d | IsGenericPlacement p} := by
  rw [show {p : Placement V d | IsGenericPlacement p} =
      ⋂ G : SimpleGraph V, {p : Placement V d | IsRegularPlacement G p} by
    ext p
    simp [IsGenericPlacement]]
  exact dense_iInter_of_isOpen
    (fun G ↦ isOpen_isRegularPlacement G)
    (fun G ↦ dense_isRegularPlacement G)

/-- A finite labelled vertex set admits a placement regular for every simple
graph on that set. -/
theorem exists_isGenericPlacement {V : Type} [Fintype V] (d : ℕ) :
    ∃ p : Placement V d, IsGenericPlacement p := by
  have hdense := dense_isGenericPlacement (V := V) (d := d)
  obtain ⟨p, hp, -⟩ := hdense.exists_mem_open isOpen_univ
    (Set.univ_nonempty : (Set.univ : Set (Placement V d)).Nonempty)
  exact ⟨p, hp⟩

theorem infinitesimalMotion_of_le {V : Type} {d : ℕ}
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (p : Placement V d) (u : Velocity V d)
    (hu : IsInfinitesimalMotion H p u) : IsInfinitesimalMotion G p u := by
  rw [isInfinitesimalMotion_iff] at hu ⊢
  intro v w hvw
  exact hu v w (hGH hvw)

theorem rigidityRank_le_of_ker_le {V : Type} [Fintype V] {d : ℕ}
    (G H : SimpleGraph V) (p : Placement V d)
    (hker : (rigidityOperator H p).ker ≤ (rigidityOperator G p).ker) :
    rigidityRank G p ≤ rigidityRank H p := by
  have hdim := Submodule.finrank_mono hker
  have hG := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hH := (rigidityOperator H p).finrank_range_add_finrank_ker
  change Module.finrank ℝ (rigidityOperator G p).range ≤
    Module.finrank ℝ (rigidityOperator H p).range
  omega

theorem rigidityRank_mono {V : Type} [Fintype V] {d : ℕ}
    {G H : SimpleGraph V} (hGH : G ≤ H) (p : Placement V d) :
    rigidityRank G p ≤ rigidityRank H p := by
  apply rigidityRank_le_of_ker_le
  intro u hu
  exact infinitesimalMotion_of_le hGH p u hu

theorem genericRigidityRank_mono {V : Type} [Fintype V] {d : ℕ}
    {G H : SimpleGraph V} (hGH : G ≤ H) :
    genericRigidityRank G d ≤ genericRigidityRank H d := by
  obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank G d
  rw [← hp]
  exact (rigidityRank_mono hGH p).trans (rigidityRank_le_genericRigidityRank H d p)

theorem IsGenericallyRigidInDimension.mono {V : Type} [Fintype V] {d : ℕ}
    {G H : SimpleGraph V} (hG : IsGenericallyRigidInDimension G d)
    (hGH : G ≤ H) : IsGenericallyRigidInDimension H d := by
  have hlow := genericRigidityRank_mono (d := d) hGH
  have hupp := genericRigidityRank_mono (d := d)
    (show H ≤ SimpleGraph.completeGraph V from le_top)
  change genericRigidityRank G d = genericRigidityRank (SimpleGraph.completeGraph V) d at hG
  change genericRigidityRank H d = genericRigidityRank (SimpleGraph.completeGraph V) d
  exact le_antisymm hupp (hG ▸ hlow)

theorem IsGenericallyRigidInR3.mono {V : Type} [Fintype V]
    {G H : SimpleGraph V} (hG : IsGenericallyRigidInR3 G) (hGH : G ≤ H) :
    IsGenericallyRigidInR3 H :=
  IsGenericallyRigidInDimension.mono hG hGH

theorem ker_eq_of_le_of_genericRigidityRank_eq
    {V : Type} [Fintype V] {d : ℕ} {G H : SimpleGraph V}
    (hGH : G ≤ H) (hr : genericRigidityRank G d = genericRigidityRank H d)
    (p : Placement V d) (hp : IsGenericPlacement p) :
    (rigidityOperator H p).ker = (rigidityOperator G p).ker := by
  have hle : (rigidityOperator H p).ker ≤ (rigidityOperator G p).ker :=
    fun u hu => infinitesimalMotion_of_le hGH p u hu
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hG := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hH := (rigidityOperator H p).finrank_range_add_finrank_ker
  have hrank : rigidityRank G p = rigidityRank H p :=
    (hp G).trans (hr.trans (hp H).symm)
  unfold rigidityRank at hrank
  omega

theorem rigidityOperator_sup_ker {V : Type} {d : ℕ}
    (G H : SimpleGraph V) (p : Placement V d) :
    (rigidityOperator (G ⊔ H) p).ker =
      (rigidityOperator G p).ker ⊓ (rigidityOperator H p).ker := by
  ext u
  change IsInfinitesimalMotion (G ⊔ H) p u ↔
    IsInfinitesimalMotion G p u ∧ IsInfinitesimalMotion H p u
  simp only [isInfinitesimalMotion_iff, SimpleGraph.sup_adj]
  constructor
  · intro hu
    exact ⟨fun v w hvw => hu v w (Or.inl hvw), fun v w hvw => hu v w (Or.inr hvw)⟩
  · rintro ⟨hG, hH⟩ v w (hvw | hvw)
    · exact hG v w hvw
    · exact hH v w hvw

end Papers.Rigidity.BarJoint

end
end BundleSource0009

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0009/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0009.json"

section BundleSource0010
/- Source: Papers/RigidityAffineRank.lean -/



@[expose] public section

/-!
# Open dense rank bounds in an affine family of actual linear operators

The determinant-on-a-line argument used for generic frameworks applies
equally to a new pin while all old coordinates are fixed.  This version
keeps those parameters fixed and uses an ordinary real affine family;
no algebraic-independence assumption or unproved generic point is needed.
-/

namespace Papers.Rigidity.AffineRank

noncomputable section

open Module
open scoped BigOperators

variable {P M N : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

def family (A : M →ₗ[ℝ] N) (L : P →ₗ[ℝ] (M →ₗ[ℝ] N)) (p : P) : M →ₗ[ℝ] N :=
  A + L p

def rankAt (A : M →ₗ[ℝ] N) (L : P →ₗ[ℝ] (M →ₗ[ℝ] N)) (p : P) : ℕ :=
  Module.finrank ℝ (family A L p).range

theorem isOpen_setOf_le_rankAt (A : M →ₗ[ℝ] N)
    (L : P →ₗ[ℝ] (M →ₗ[ℝ] N)) (r : ℕ) :
    IsOpen {p : P | r ≤ rankAt A L p} := by
  let inner : (M →ₗ[ℝ] N) ≃ₗ[ℝ] (M →L[ℝ] N) := LinearMap.toContinuousLinearMap
  let D : P →L[ℝ] (M →L[ℝ] N) :=
    LinearMap.toContinuousLinearMap (inner.toLinearMap.comp L)
  have hcont : Continuous (fun p : P => inner A + D p) :=
    continuous_const.add D.continuous
  have hopen := (isOpen_setOfPred_nat_le_rank
    (𝕜 := ℝ) (E := M) (F := N) r).preimage hcont
  convert hopen using 1
  ext p
  change r ≤ Module.finrank ℝ (family A L p).range ↔
    (r : Cardinal) ≤ Module.rank ℝ (family A L p).range
  rw [← Module.finrank_eq_rank]
  norm_cast

/-- Every rank that occurs anywhere in an affine family occurs as a
lower bound on an open dense set of parameters. -/
theorem dense_setOf_rankAt_le (A : M →ₗ[ℝ] N)
    (L : P →ₗ[ℝ] (M →ₗ[ℝ] N)) (w : P) :
    Dense {p : P | rankAt A L w ≤ rankAt A L p} := by
  classical
  let r := rankAt A L w
  let F := family A L
  let b : Basis (Fin r) ℝ (F w).range := Module.finBasisOfFinrankEq ℝ _ rfl
  obtain ⟨lift, hlift⟩ :=
    (F w).rangeRestrict.exists_rightInverse_of_surjective (F w).range_rangeRestrict
  let U₀ : (Fin r → ℝ) →ₗ[ℝ] M := lift.comp b.equivFun.symm.toLinearMap
  let T₀ : (Fin r → ℝ) →ₗ[ℝ] N :=
    (F w).range.subtype.comp b.equivFun.symm.toLinearMap
  have hFwU : (F w).comp U₀ = T₀ := by
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun hlift (b.equivFun.symm a)
    exact congrArg (fun y : (F w).range => y.val) h
  have hT₀inj : Function.Injective T₀ := by
    intro x y hxy
    apply b.equivFun.symm.injective
    exact Subtype.ext hxy
  let φ : N →ₗ[ℝ] (Fin r → ℝ) := T₀.leftInverse
  have hφT₀ : φ.comp T₀ = LinearMap.id :=
    T₀.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hT₀inj)
  refine dense_iff_inter_open.mpr ?_
  intro O hO ⟨p, hpO⟩
  let q : ℝ → P := fun t => p + t • (w - p)
  have hq_cont : Continuous q := continuous_const.add (continuous_id.smul continuous_const)
  have hq_zero : q 0 = p := by simp [q]
  have hpreimage_nhds : q ⁻¹' O ∈ nhds (0 : ℝ) :=
    (hO.preimage hq_cont).mem_nhds (by simpa [hq_zero] using hpO)
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hpreimage_nhds
  let A₀ : Module.End ℝ (Fin r → ℝ) := φ.comp ((F p).comp U₀)
  let A₁ : Module.End ℝ (Fin r → ℝ) := φ.comp ((L (w - p)).comp U₀)
  let e : Basis (Fin r) ℝ (Fin r → ℝ) := Pi.basisFun ℝ (Fin r)
  let M₀ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₀
  let M₁ : Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix e e A₁
  let Q : Polynomial ℝ :=
    Matrix.det ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C + M₀.map Polynomial.C)
  have hoperator_line (t : ℝ) : F (q t) = F p + t • L (w - p) := by
    simp only [F, family, q, map_add, map_smul]
    rw [add_assoc]
  have hA_line (t : ℝ) : A₀ + t • A₁ = φ.comp ((F (q t)).comp U₀) := by
    rw [hoperator_line]
    ext a
    simp [A₀, A₁]
  have hQ_eval (t : ℝ) : Q.eval t = LinearMap.det (A₀ + t • A₁) := by
    dsimp only [Q]
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det, ← LinearMap.det_toMatrix e]
    congr 1
    ext i j
    simp [M₀, M₁]
    ring
  have hA_one : A₀ + (1 : ℝ) • A₁ = LinearMap.id := by
    rw [hA_line 1, show q 1 = w by simp [q], hFwU, hφT₀]
  have hQ_one : Q.eval 1 = 1 := by rw [hQ_eval, hA_one]; simp
  have hQ_ne : Q ≠ 0 := by
    intro hQ
    simp [hQ] at hQ_one
  let Z : Set ℝ := {t | Polynomial.IsRoot Q t}
  have hZfinite : Z.Finite := by simpa [Z] using Polynomial.finite_setOf_isRoot hQ_ne
  have hintervalInfinite : (Set.Ioo (0 : ℝ) ε).Infinite := Set.Ioo_infinite hεpos
  have hnotSubset : ¬ Set.Ioo (0 : ℝ) ε ⊆ Z := by
    intro hsubset
    exact hintervalInfinite (hZfinite.subset hsubset)
  obtain ⟨t, htInterval, htNotRoot⟩ := Set.not_subset.mp hnotSubset
  have hQ_t : Q.eval t ≠ 0 := by simpa [Z, Polynomial.IsRoot] using htNotRoot
  have hA_t_det : LinearMap.det (A₀ + t • A₁) ≠ 0 := by simpa [hQ_eval t] using hQ_t
  have hA_t_ker : LinearMap.ker (A₀ + t • A₁) = ⊥ := by
    by_contra hker
    exact hA_t_det (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  have hA_t_inj : Function.Injective (A₀ + t • A₁) := LinearMap.ker_eq_bot.mp hA_t_ker
  let FqU : (Fin r → ℝ) →ₗ[ℝ] N := (F (q t)).comp U₀
  have hFqU_inj : Function.Injective FqU := by
    intro x y hxy
    apply hA_t_inj
    rw [hA_line]
    exact congrArg φ hxy
  have hrank_lower : r ≤ rankAt A L (q t) := by
    unfold rankAt
    calc
      r = Module.finrank ℝ (Fin r → ℝ) := by simp
      _ = Module.finrank ℝ FqU.range := (LinearMap.finrank_range_of_inj hFqU_inj).symm
      _ ≤ Module.finrank ℝ (family A L (q t)).range :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos htInterval.1]
    exact htInterval.2
  exact ⟨q t, hball ht_ball, hrank_lower⟩

/-- A lower bound witnessed at one parameter holds densely. -/
theorem dense_setOf_le_rankAt (A : M →ₗ[ℝ] N)
    (L : P →ₗ[ℝ] (M →ₗ[ℝ] N)) (r : ℕ)
    (hw : ∃ w, r ≤ rankAt A L w) : Dense {p : P | r ≤ rankAt A L p} := by
  obtain ⟨w, hw⟩ := hw
  exact (dense_setOf_rankAt_le A L w).mono (fun _ hp => hw.trans hp)

end

end Papers.Rigidity.AffineRank

end
end BundleSource0010

section BundleSource0011
/- Source: Papers/RigidityAlgebra.lean -/



@[expose] public section

/-!
# Algebraic integrability constraints for three-dimensional rigid motions

These results verify the linear-algebra steps occurring in Lemmas 4.2 and 4.3
of `35_clique_covered_rigidity(6).pdf`.  They do not assert the global rigidity
theorem, nor do they assume any unproved geometric theorem.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- The algebraic consequence of differentiating `dt = -dR b` in Lemma 4.2.
All matrices satisfying the resulting identity are zero. -/
theorem matrix_eq_zero_of_cross_integrability (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ u v : Vec3, u ⨯₃ (A *ᵥ v) = v ⨯₃ (A *ᵥ u)) : A = 0 := by
  have h01 := h ![1, 0, 0] ![0, 1, 0]
  have h02 := h ![1, 0, 0] ![0, 0, 1]
  have h12 := h ![0, 1, 0] ![0, 0, 1]
  have h010 := congrFun h01 0
  have h011 := congrFun h01 1
  have h012 := congrFun h01 2
  have h020 := congrFun h02 0
  have h021 := congrFun h02 1
  have h022 := congrFun h02 2
  have h120 := congrFun h12 0
  have h121 := congrFun h12 1
  have h122 := congrFun h12 2
  simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h010 h011 h012 h020 h021 h022 h120 h121 h122
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- Coordinate-free version of the same algebraic integrability calculation. -/
theorem linearMap_eq_zero_of_cross_integrability (A : Vec3 →ₗ[ℝ] Vec3)
    (h : ∀ u v : Vec3, u ⨯₃ A v = v ⨯₃ A u) : A = 0 := by
  have hm : LinearMap.toMatrix' A = 0 := by
    apply matrix_eq_zero_of_cross_integrability
    intro u v
    simpa only [LinearMap.toMatrix'_mulVec] using h u v
  apply LinearMap.ext
  intro v
  rw [← LinearMap.toMatrix'_mulVec A v, hm]
  simp

/-- Matrix of a scalar multiple of the identity plus cross product with `g`. -/
def scalarCrossMatrix (c : ℝ) (g : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c, -g 2, g 1; g 2, c, -g 0; -g 1, g 0, c]

theorem scalarCrossMatrix_mulVec (c : ℝ) (g v : Vec3) :
    scalarCrossMatrix c g *ᵥ v = c • v + g ⨯₃ v := by
  ext i
  fin_cases i <;>
    simp [scalarCrossMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cross_apply] <;>
    ring

/-- Over the reals, a scalar identity plus a skew matrix cannot have rank one
unless both its scalar and skew parts vanish. This is the rank calculation in
the proof of Lemma 4.3. -/
theorem scalarCrossMatrix_eq_zero_of_rank_le_one (c : ℝ) (g : Vec3)
    (hr : (scalarCrossMatrix c g).rank ≤ 1) : c = 0 ∧ g = 0 := by
  have hminor (k : Fin 2 → Fin 3) :
      ((scalarCrossMatrix c g).submatrix k k).det = 0 := by
    by_contra hd
    have hl := (Matrix.rank_submatrix_le (scalarCrossMatrix c g) k k).trans hr
    rw [Matrix.rank_of_det_ne_zero hd] at hl
    norm_num at hl
  have h01 := hminor ![0, 1]
  have h02 := hminor ![0, 2]
  have h12 := hminor ![1, 2]
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply] at h01 h02 h12
  simp [scalarCrossMatrix] at h01 h02 h12
  have hc : c = 0 := by nlinarith [sq_nonneg (g 2)]
  refine ⟨hc, ?_⟩
  ext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2)]

/-- The nonzero proportionality factor forced by the angular
Maurer--Cartan rank calculation is exactly one. -/
theorem proportionality_eq_one (a : ℝ) (g : Vec3) (ha : a ≠ 0)
    (hr : (scalarCrossMatrix (a ^ 2 - a) g).rank ≤ 1) : a = 1 := by
  have hc := (scalarCrossMatrix_eq_zero_of_rank_le_one (a ^ 2 - a) g hr).1
  have hf : a * (a - 1) = 0 := by nlinarith
  have := (mul_eq_zero.mp hf).resolve_left ha
  linarith

/-- If a three-dimensional twist space projects isomorphically to angular
velocity, write its translational part as `B *ᵥ ω`.  The new-pin evaluation is
`B - cross(p)`. Vanishing of its determinant forces `B` to be skew. -/
theorem transpose_eq_neg_of_pin_determinants
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ p : Vec3, (B - scalarCrossMatrix 0 p).det = 0) : Bᵀ = -B := by
  have h0 := h ![0, 0, 0]
  have hp0 := h ![1, 0, 0]
  have hm0 := h ![-1, 0, 0]
  have hp1 := h ![0, 1, 0]
  have hm1 := h ![0, -1, 0]
  have hp2 := h ![0, 0, 1]
  have hm2 := h ![0, 0, -1]
  have hp01 := h ![1, 1, 0]
  have hp02 := h ![1, 0, 1]
  have hp12 := h ![0, 1, 1]
  simp [scalarCrossMatrix, Matrix.det_fin_three] at h0 hp0 hm0 hp1 hm1 hp2 hm2 hp01 hp02 hp12
  have hd0 : B 0 0 = 0 := by linear_combination (1 / 2 : ℝ) * hp0 + (1 / 2 : ℝ) * hm0 - h0
  have hd1 : B 1 1 = 0 := by linear_combination (1 / 2 : ℝ) * hp1 + (1 / 2 : ℝ) * hm1 - h0
  have hd2 : B 2 2 = 0 := by linear_combination (1 / 2 : ℝ) * hp2 + (1 / 2 : ℝ) * hm2 - h0
  have hs01 : B 0 1 + B 1 0 = 0 := by linear_combination hp01 - hp0 - hp1 + h0
  have hs02 : B 0 2 + B 2 0 = 0 := by linear_combination hp02 - hp0 - hp2 + h0
  have hs12 : B 1 2 + B 2 1 = 0 := by linear_combination hp12 - hp1 - hp2 + h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- Every real skew matrix of order three is cross product with one unique
vector. This identifies the finite virtual center explicitly. -/
theorem existsUnique_cross_center
    (B : Matrix (Fin 3) (Fin 3) ℝ) (h : Bᵀ = -B) :
    ∃! a : Vec3, B = scalarCrossMatrix 0 a := by
  have hentry (i j : Fin 3) : B j i = -B i j := by
    simpa using congrFun (congrFun h i) j
  have hd0 := hentry 0 0
  have hd1 := hentry 1 1
  have hd2 := hentry 2 2
  have h01 := hentry 0 1
  have h02 := hentry 0 2
  have h12 := hentry 1 2
  refine ⟨![-B 1 2, B 0 2, -B 0 1], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarCrossMatrix] <;> linarith
  · intro a ha
    have ha0 := congrFun (congrFun ha 1) 2
    have ha1 := congrFun (congrFun ha 0) 2
    have ha2 := congrFun (congrFun ha 0) 1
    simp [scalarCrossMatrix] at ha0 ha1 ha2
    ext i
    fin_cases i <;> simp <;> linarith

/-- The finite-center case of the alternating-form classification in Lemma
3.4, proved directly from the new-pin determinant identity. -/
theorem unique_finite_center_of_pin_determinants
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ p : Vec3, (B - scalarCrossMatrix 0 p).det = 0) :
    ∃! a : Vec3, B = scalarCrossMatrix 0 a :=
  existsUnique_cross_center B (transpose_eq_neg_of_pin_determinants B h)

/-- A nonzero translational twist in a space with singular evaluation at
every new pin forces every two angular velocities to be dependent.  This is
the other case needed for a direct elementary proof of Lemma 3.4. -/
theorem angular_cross_eq_zero_of_translation
    (t a b u v : Vec3) (ht : t ≠ 0)
    (h : ∀ p : Vec3, t ⬝ᵥ ((a + u ⨯₃ p) ⨯₃ (b + v ⨯₃ p)) = 0) :
    u ⨯₃ v = 0 := by
  have hq (p : Vec3) : (t ⬝ᵥ p) * (p ⬝ᵥ (u ⨯₃ v)) = 0 := by
    have hp := h p
    have hm := h (-p)
    have h0 := h 0
    simp [cross_apply, dotProduct, Fin.sum_univ_succ, -mul_eq_zero] at hp hm h0 ⊢
    linear_combination (1 / 2 : ℝ) * hp + (1 / 2 : ℝ) * hm - h0
  have htt : t ⬝ᵥ t ≠ 0 := by
    intro hzero
    exact ht (dotProduct_self_eq_zero.mp hzero)
  have htw : t ⬝ᵥ (u ⨯₃ v) = 0 := (mul_eq_zero.mp (hq t)).resolve_left htt
  have hw := hq (t + u ⨯₃ v)
  simp only [dotProduct_add, add_dotProduct, htw, add_zero, zero_add] at hw
  exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left htt)

/-- The angular conclusion also gives the exact scalar dependence. -/
theorem angular_is_scalar_of_translation
    (t a b u v : Vec3) (ht : t ≠ 0) (hu : u ≠ 0)
    (h : ∀ p : Vec3, t ⬝ᵥ ((a + u ⨯₃ p) ⨯₃ (b + v ⨯₃ p)) = 0) :
    ∃ c : ℝ, c • u = v := by
  have hc := angular_cross_eq_zero_of_translation t a b u v ht h
  have hn : ¬ LinearIndependent ℝ ![u, v] := by
    intro hi
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr hi) hc
  simpa only [LinearIndependent.pair_iff' hu, not_forall_not] using hn

end Papers.Rigidity

end
end BundleSource0011

section BundleSource0012
/- Source: Papers/RigidityTwistClassification.lean -/




@[expose] public section

/-!
# Singular evaluation of three-dimensional body twists

The ambient space is the actual six-dimensional space of Euclidean twists,
not an abstract matroid specified by the desired rigidity conclusions.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- Every finite-center rotation space has singular evaluation at each pin. -/
theorem finiteCenterSpace_singular (a : Vec3) : SingularPinSpace (finiteCenterSpace a) := by
  intro p
  by_cases hpa : p = a
  · subst p
    have hz : restrictEvaluation (finiteCenterSpace a) a = 0 := by
      apply LinearMap.ext
      intro X
      exact X.property
    rw [hz, LinearMap.range_zero]
    simp
  · let r : Vec3 := p - a
    have hr : r ≠ 0 := sub_ne_zero.mpr hpa
    let X : finiteCenterSpace a :=
      ⟨(r, -(r ⨯₃ a)), by simp [finiteCenterSpace, LinearMap.mem_ker]⟩
    have hX : X ≠ 0 := by
      intro hx
      have hf := congrArg (fun x : finiteCenterSpace a => x.val.1) hx
      exact hr hf
    have hk : X ∈ (restrictEvaluation (finiteCenterSpace a) p).ker := by
      rw [LinearMap.mem_ker]
      change -(r ⨯₃ a) + r ⨯₃ p = 0
      rw [neg_add_eq_sub, ← map_sub]
      exact cross_self r
    have hkne : (restrictEvaluation (finiteCenterSpace a) p).ker ≠ ⊥ := by
      intro he
      rw [he] at hk
      exact hX (by simpa using hk)
    have hdim : 1 ≤ Module.finrank ℝ (restrictEvaluation (finiteCenterSpace a) p).ker :=
      Submodule.one_le_finrank_iff.mpr hkne
    have hrank := (restrictEvaluation (finiteCenterSpace a) p).finrank_range_add_finrank_ker
    rw [finrank_finiteCenterSpace] at hrank
    omega

/-- A threefold scalar product vanishes inside every subspace of dimension
at most two. -/
theorem triple_product_eq_zero_of_finrank_le_two
    (U : Submodule ℝ Vec3) (hU : Module.finrank ℝ U ≤ 2) (x y z : U) :
    (x : Vec3) ⬝ᵥ ((y : Vec3) ⨯₃ (z : Vec3)) = 0 := by
  by_contra hd
  rw [triple_product_eq_det] at hd
  let A : Matrix (Fin 3) (Fin 3) ℝ := ![x.val, y.val, z.val]
  have hunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd)
  have hi : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_row_iff_isUnit.mpr hunit
  have hcomp : U.subtype ∘ ![x, y, z] = A.row := by
    funext i
    fin_cases i <;> rfl
  have hiU : LinearIndependent ℝ ![x, y, z] :=
    LinearIndependent.of_comp U.subtype (by rw [hcomp]; exact hi)
  have hdim := hiU.fintype_card_le_finrank
  norm_num at hdim
  omega

theorem finrank_le_two_of_triple_product_eq_zero
    (U : Submodule ℝ Vec3)
    (hU : ∀ x y z : U, (x : Vec3) ⬝ᵥ ((y : Vec3) ⨯₃ (z : Vec3)) = 0) :
    Module.finrank ℝ U ≤ 2 := by
  by_contra hn
  have hu : Module.finrank ℝ U ≤ 3 := by
    simpa [Vec3] using Submodule.finrank_le U
  have he : Module.finrank ℝ U = Module.finrank ℝ Vec3 := by
    have hU3 : Module.finrank ℝ U = 3 := by omega
    simpa [Vec3] using hU3
  have ht : U = ⊤ := Submodule.eq_top_of_finrank_eq he
  have hm (v : Vec3) : v ∈ U := by rw [ht]; trivial
  have h := hU ⟨![1, 0, 0], hm _⟩ ⟨![0, 1, 0], hm _⟩ ⟨![0, 0, 1], hm _⟩
  norm_num [cross_apply, dotProduct, Fin.sum_univ_succ] at h

theorem singularPinSpace_triple_product
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (X Y Z : W) (p : Vec3) :
    evaluateTwist p X.val ⬝ᵥ
      (evaluateTwist p Y.val ⨯₃ evaluateTwist p Z.val) = 0 := by
  let E := restrictEvaluation W p
  let x : E.range := ⟨E X, X, rfl⟩
  let y : E.range := ⟨E Y, Y, rfl⟩
  let z : E.range := ⟨E Z, Z, rfl⟩
  exact triple_product_eq_zero_of_finrank_le_two E.range (hW p) x y z

/-- If the twist space contains a nonzero pure translation, all angular
velocities are pairwise dependent. -/
theorem angular_cross_eq_zero_in_singularPinSpace
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (t : Vec3) (ht : t ≠ 0) (htW : (0, t) ∈ W) (X Y : W) :
    X.val.1 ⨯₃ Y.val.1 = 0 := by
  apply angular_cross_eq_zero_of_translation t X.val.2 Y.val.2 X.val.1 Y.val.1 ht
  intro p
  have h := singularPinSpace_triple_product W hW ⟨(0, t), htW⟩ X Y p
  simpa using h

/-- The actual angular projection of a twist subspace. -/
def angularProjection (W : Submodule ℝ Twist) : W →ₗ[ℝ] Vec3 :=
  (LinearMap.fst ℝ Vec3 Vec3).comp W.subtype

@[simp] theorem angularProjection_apply (W : Submodule ℝ Twist) (X : W) :
    angularProjection W X = X.val.1 := rfl

theorem ker_crossProduct_eq_span (d : Vec3) (hd : d ≠ 0) :
    (crossProduct d).ker = Submodule.span ℝ {d} := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have hn : ¬ LinearIndependent ℝ ![d, v] := by
      intro hi
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr hi) hv
    simpa only [LinearIndependent.pair_iff' hd, not_forall_not] using hn
  · rintro ⟨c, rfl⟩
    simp

theorem finrank_range_crossProduct (d : Vec3) (hd : d ≠ 0) :
    Module.finrank ℝ (crossProduct d).range = 2 := by
  have hr := (crossProduct d).finrank_range_add_finrank_ker
  rw [ker_crossProduct_eq_span d hd, finrank_span_singleton hd] at hr
  norm_num [Vec3] at hr
  omega

theorem mem_range_crossProduct_iff (d v : Vec3) (hd : d ≠ 0) :
    v ∈ (crossProduct d).range ↔ v ⬝ᵥ d = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [dotProduct_comm]
    exact dot_self_cross d p
  · intro hv
    have hv' : d ⬝ᵥ v = 0 := by simpa only [dotProduct_comm] using hv
    have hdd : d ⬝ᵥ d ≠ 0 := fun h => hd (dotProduct_self_eq_zero.mp h)
    refine ⟨(-(d ⬝ᵥ d)⁻¹) • (d ⨯₃ v), ?_⟩
    rw [map_smul, cross_cross_eq_smul_sub_smul']
    simp [hv', smul_smul, hdd]

theorem angular_cross_eq_zero_of_parallel_evaluations
    (a b u v : Vec3)
    (h : ∀ p : Vec3, (a + u ⨯₃ p) ⨯₃ (b + v ⨯₃ p) = 0) :
    u ⨯₃ v = 0 := by
  have hquadratic (p : Vec3) : (u ⨯₃ p) ⨯₃ (v ⨯₃ p) = 0 := by
    ext i
    have hp := congrFun (h p) i
    have hm := congrFun (h (-p)) i
    have hzero := congrFun (h 0) i
    fin_cases i <;>
      simp [cross_apply] at hp hm hzero ⊢ <;>
      linear_combination (1 / 2 : ℝ) * hp + (1 / 2 : ℝ) * hm - hzero
  have hidentity (p : Vec3) :
      (u ⨯₃ p) ⨯₃ (v ⨯₃ p) = (p ⬝ᵥ (u ⨯₃ v)) • p := by
    ext i
    fin_cases i <;>
      simp [cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring
  have hz : ((u ⨯₃ v) ⬝ᵥ (u ⨯₃ v)) • (u ⨯₃ v) = 0 :=
    (hidentity (u ⨯₃ v)).symm.trans (hquadratic (u ⨯₃ v))
  rcases smul_eq_zero.mp hz with hh | hh
  · exact dotProduct_self_eq_zero.mp hh
  · exact hh

theorem angular_eq_zero_of_translation_parallel
    (t b v : Vec3) (ht : t ≠ 0)
    (h : ∀ p : Vec3, t ⨯₃ (b + v ⨯₃ p) = 0) : v = 0 := by
  by_contra hv
  have htb : t ⨯₃ b = 0 := by simpa using h 0
  have hle : (crossProduct v).range ≤ Submodule.span ℝ {t} := by
    rintro w ⟨p, rfl⟩
    rw [← ker_crossProduct_eq_span t ht]
    have hp := h p
    simpa only [LinearMap.mem_ker, map_add, htb, zero_add] using hp
  have hdim := Submodule.finrank_mono hle
  rw [finrank_range_crossProduct v hv, finrank_span_singleton ht] at hdim
  omega

/-- Two twists with parallel evaluated velocities at every point must be
proportional as twists. This supplies the small-dimensional part of the
generic-pin classification after polynomial propagation. -/
theorem scalar_of_pointwise_parallel_twists (X Y : Twist) (hX : X ≠ 0)
    (h : ∀ p : Vec3, evaluateTwist p X ⨯₃ evaluateTwist p Y = 0) :
    ∃ c : ℝ, c • X = Y := by
  classical
  by_cases hω : X.1 = 0
  · have ht : X.2 ≠ 0 := fun hz => hX (Prod.ext hω hz)
    have hYω : Y.1 = 0 := angular_eq_zero_of_translation_parallel X.2 Y.2 Y.1 ht
      (by intro p; simpa [evaluateTwist_apply, hω] using h p)
    have hcross : X.2 ⨯₃ Y.2 = 0 := by simpa using h 0
    have hm : Y.2 ∈ Submodule.span ℝ {X.2} := by
      rw [← ker_crossProduct_eq_span X.2 ht]
      exact LinearMap.mem_ker.mpr hcross
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨c, Prod.ext ?_ hc⟩
    simp [hω, hYω]
  · have hcross : X.1 ⨯₃ Y.1 = 0 :=
      angular_cross_eq_zero_of_parallel_evaluations X.2 Y.2 X.1 Y.1 h
    have hm : Y.1 ∈ Submodule.span ℝ {X.1} := by
      rw [← ker_crossProduct_eq_span X.1 hω]
      exact LinearMap.mem_ker.mpr hcross
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    let Z : Twist := Y - c • X
    have hZω : Z.1 = 0 := by simpa [Z, hc]
    have hparallel (p : Vec3) : evaluateTwist p Z ⨯₃ evaluateTwist p X = 0 := by
      have he : evaluateTwist p Z = evaluateTwist p Y - c • evaluateTwist p X := by
        simp only [Z, map_sub, map_smul]
      rw [he, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        cross_self, smul_zero, sub_zero,
        ← cross_anticomm (evaluateTwist p X) (evaluateTwist p Y), h p, neg_zero]
    have hZt : Z.2 = 0 := by
      by_contra hn
      exact hω (angular_eq_zero_of_translation_parallel Z.2 X.2 X.1 hn
        (by intro p; simpa [evaluateTwist_apply, hZω] using hparallel p))
    refine ⟨c, ?_⟩
    have hz : Z = 0 := Prod.ext hZω hZt
    exact (sub_eq_zero.mp hz).symm

theorem exists_pin_separating_independent_twists (X Y : Twist)
    (hXY : LinearIndependent ℝ ![X, Y]) :
    ∃ p : Vec3, evaluateTwist p X ⨯₃ evaluateTwist p Y ≠ 0 := by
  by_contra hn
  have hz : ∀ p : Vec3, evaluateTwist p X ⨯₃ evaluateTwist p Y = 0 := by
    simpa only [not_exists, not_not] using hn
  have hX : X ≠ 0 := hXY.ne_zero 0
  obtain ⟨c, hc⟩ := scalar_of_pointwise_parallel_twists X Y hX hz
  exact (LinearIndependent.pair_iff' hX).mp hXY c hc

theorem exists_pin_detecting_nonzero_twist (X : Twist) (hX : X ≠ 0) :
    ∃ p : Vec3, evaluateTwist p X ≠ 0 := by
  by_contra hn
  have hz : ∀ p : Vec3, evaluateTwist p X = 0 := by
    simpa only [not_exists, not_not] using hn
  have ht : X.2 = 0 := by simpa using hz 0
  have hω : X.1 ≠ 0 := fun h => hX (Prod.ext h ht)
  have hm : crossProduct X.1 = 0 := by
    apply LinearMap.ext
    intro p
    change X.1 ⨯₃ p = 0
    simpa [ht] using hz p
  have hr := finrank_range_crossProduct X.1 hω
  rw [hm, LinearMap.range_zero] at hr
  simp at hr

theorem exists_pure_translation_of_not_injective_angular
    (W : Submodule ℝ Twist) (h : ¬ Function.Injective (angularProjection W)) :
    ∃ t : Vec3, t ≠ 0 ∧ (0, t) ∈ W := by
  classical
  obtain ⟨X, Y, heq, hne⟩ := Function.not_injective_iff.mp h
  let Z : W := X - Y
  have hZ : Z ≠ 0 := sub_ne_zero.mpr hne
  have hang : Z.val.1 = 0 := by
    change X.val.1 - Y.val.1 = 0
    exact sub_eq_zero.mpr heq
  have ht : Z.val.2 ≠ 0 := by
    intro hzero
    apply hZ
    apply Subtype.ext
    exact Prod.ext hang hzero
  refine ⟨Z.val.2, ht, ?_⟩
  have hm := Z.property
  simpa only [← hang] using hm

theorem exists_nonzero_angular_in_singularPinSpace
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W) : ∃ X : W, X.val.1 ≠ 0 := by
  by_contra hn
  have hz : ∀ X : W, X.val.1 = 0 := by simpa only [not_exists, not_not] using hn
  have hi : Function.Injective (restrictEvaluation W 0) := by
    intro X Y hXY
    apply Subtype.ext
    apply Prod.ext
    · rw [hz X, hz Y]
    · simpa [restrictEvaluation, evaluateTwist_apply] using hXY
  have he := LinearMap.finrank_range_of_inj hi
  have hb := hW 0
  rw [he] at hb
  omega

/-- The complementary case of Lemma 3.4: a singular twist space of dimension
at least three with a translation has a common projective center at infinity. -/
theorem exists_infiniteCenter_of_not_injective_angular
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W)
    (hnot : ¬ Function.Injective (angularProjection W)) :
    ∃ d : Vec3, d ≠ 0 ∧ W = infiniteCenterSpace d := by
  classical
  obtain ⟨t, ht, htW⟩ := exists_pure_translation_of_not_injective_angular W hnot
  obtain ⟨X, hd⟩ := exists_nonzero_angular_in_singularPinSpace W hW hdim
  let d : Vec3 := X.val.1
  let A := angularProjection W
  let K := A.ker
  have hcross (Y : W) : d ⨯₃ Y.val.1 = 0 :=
    angular_cross_eq_zero_in_singularPinSpace W hW t ht htW X Y
  have har : A.range ≤ Submodule.span ℝ {d} := by
    rintro v ⟨Y, rfl⟩
    rw [← ker_crossProduct_eq_span d hd]
    exact LinearMap.mem_ker.mpr (hcross Y)
  have harank : Module.finrank ℝ A.range ≤ 1 := by
    have hh := Submodule.finrank_mono har
    rwa [finrank_span_singleton hd] at hh
  have hnull := A.finrank_range_add_finrank_ker
  have hkge : 2 ≤ Module.finrank ℝ K := by
    change 2 ≤ Module.finrank ℝ A.ker
    omega
  let Tmap : K →ₗ[ℝ] Vec3 := (restrictEvaluation W 0).comp K.subtype
  let T : Submodule ℝ Vec3 := Tmap.range
  have hkfirst (Z : K) : Z.val.val.1 = 0 := Z.property
  have hTinj : Function.Injective Tmap := by
    intro Y Z heq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rw [hkfirst Y, hkfirst Z]
    · simpa [Tmap, restrictEvaluation, evaluateTwist_apply] using heq
  have hTdim : Module.finrank ℝ T = Module.finrank ℝ K :=
    LinearMap.finrank_range_of_inj hTinj
  have hTle (p : Vec3) : T ≤ (restrictEvaluation W p).range := by
    rintro u ⟨Z, hZ⟩
    refine ⟨Z.val, ?_⟩
    have heq : restrictEvaluation W p Z.val = Tmap Z := by
      simp [Tmap, restrictEvaluation, evaluateTwist_apply, hkfirst Z]
    exact heq.trans hZ
  have hTtwo : Module.finrank ℝ T = 2 := by
    have hu := (Submodule.finrank_mono (hTle 0)).trans (hW 0)
    omega
  have hrange (p : Vec3) : T = (restrictEvaluation W p).range := by
    apply Submodule.eq_of_le_of_finrank_eq (hTle p)
    have hl := Submodule.finrank_mono (hTle p)
    have hu := hW p
    omega
  have hevalmem (p : Vec3) (Y : W) : restrictEvaluation W p Y ∈ T := by
    rw [hrange p]
    exact ⟨Y, rfl⟩
  have hcle : (crossProduct d).range ≤ T := by
    rintro v ⟨p, rfl⟩
    have heq : d ⨯₃ p = restrictEvaluation W p X - restrictEvaluation W 0 X := by
      simp [d, restrictEvaluation, evaluateTwist_apply]
    rw [heq]
    exact T.sub_mem (hevalmem p X) (hevalmem 0 X)
  have hcT : (crossProduct d).range = T :=
    Submodule.eq_of_le_of_finrank_eq hcle ((finrank_range_crossProduct d hd).trans hTtwo.symm)
  have hsecond (Y : W) : Y.val.2 ∈ T := by
    simpa [restrictEvaluation, evaluateTwist_apply] using hevalmem 0 Y
  have htrans (v : Vec3) (hv : v ∈ T) : (0, v) ∈ W := by
    obtain ⟨Z, hZ⟩ := hv
    have hsec : Z.val.val.2 = v := by
      simpa [Tmap, restrictEvaluation, evaluateTwist_apply] using hZ
    have hm := Z.val.property
    simpa only [← hkfirst Z, ← hsec] using hm
  have hangular : (d, (0 : Vec3)) ∈ W := by
    have hm := W.sub_mem X.property (htrans X.val.2 (hsecond X))
    have he : X.val - (0, X.val.2) = (d, (0 : Vec3)) := by
      apply Prod.ext
      · change X.val.1 - 0 = d
        exact sub_zero _
      · change X.val.2 - X.val.2 = 0
        exact sub_self _
    rwa [he] at hm
  refine ⟨d, hd, ?_⟩
  apply le_antisymm
  · intro Y hY
    constructor
    · rw [← cross_anticomm d Y.1, hcross ⟨Y, hY⟩, neg_zero]
    · apply (mem_range_crossProduct_iff d Y.2 hd).mp
      rw [hcT]
      exact hsecond ⟨Y, hY⟩
  · intro Y hY
    have hDY : d ⨯₃ Y.1 = 0 := by
      rw [← cross_anticomm Y.1 d, hY.1, neg_zero]
    have hm : Y.1 ∈ Submodule.span ℝ {d} := by
      rw [← ker_crossProduct_eq_span d hd]
      exact LinearMap.mem_ker.mpr hDY
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have htmem : Y.2 ∈ T := by
      rw [← hcT]
      exact (mem_range_crossProduct_iff d Y.2 hd).mpr hY.2
    have hsum := W.add_mem (W.smul_mem c hangular) (htrans Y.2 htmem)
    simpa [hc] using hsum

theorem finiteCenterSpace_injective : Function.Injective finiteCenterSpace := by
  intro a b hab
  have hcross (w : Vec3) : w ⨯₃ (b - a) = 0 := by
    have hm : (w, -(w ⨯₃ a)) ∈ finiteCenterSpace a := by
      simp [finiteCenterSpace, LinearMap.mem_ker]
    rw [hab] at hm
    change -(w ⨯₃ a) + w ⨯₃ b = 0 at hm
    rw [map_sub]
    simpa only [sub_eq_add_neg, add_comm] using hm
  have hx := hcross ![1, 0, 0]
  have hy := hcross ![0, 1, 0]
  have hx1 := congrFun hx 1
  have hx2 := congrFun hx 2
  have hy2 := congrFun hy 2
  simp [cross_apply] at hx1 hx2 hy2
  ext i
  fin_cases i
  · change a 0 = b 0
    exact sub_eq_zero.mp hy2
  · change a 1 = b 1
    exact (sub_eq_zero.mp hx2).symm
  · change a 2 = b 2
    exact sub_eq_zero.mp hx1

/-- Full classification in the case where the angular projection is
injective. No chosen basis or virtual center is assumed in the statement. -/
theorem existsUnique_finiteCenter_of_injective_angular
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W)
    (hinj : Function.Injective (angularProjection W)) :
    ∃! a : Vec3, W = finiteCenterSpace a := by
  have hu := LinearMap.finrank_le_finrank_of_injective hinj
  have hd : Module.finrank ℝ W = 3 := by
    have hu3 : Module.finrank ℝ W ≤ 3 := by simpa [Vec3] using hu
    omega
  have hd' : Module.finrank ℝ W = Module.finrank ℝ Vec3 := by simpa [Vec3] using hd
  let e : W ≃ₗ[ℝ] Vec3 :=
    LinearMap.linearEquivOfInjective (angularProjection W) hinj hd'
  let T : Vec3 →ₗ[ℝ] Vec3 :=
    (LinearMap.snd ℝ Vec3 Vec3).comp (W.subtype.comp e.symm.toLinearMap)
  let B : Matrix (Fin 3) (Fin 3) ℝ := LinearMap.toMatrix' T
  have hang (v : Vec3) : (e.symm v).val.1 = v := e.apply_symm_apply v
  have htrans (v : Vec3) : B *ᵥ v = (e.symm v).val.2 :=
    LinearMap.toMatrix'_mulVec T v
  have heval (p v : Vec3) :
      (B - scalarCrossMatrix 0 p) *ᵥ v = evaluateTwist p (e.symm v).val := by
    rw [Matrix.sub_mulVec, htrans, scalarCrossMatrix_mulVec]
    simp only [zero_smul, zero_add, evaluateTwist_apply, hang]
    rw [← cross_anticomm p v]
    rfl
  have hdet (p : Vec3) : (B - scalarCrossMatrix 0 p).det = 0 := by
    by_contra hne
    have hunit : IsUnit (B - scalarCrossMatrix 0 p) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
    have hsur := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
    have hE : Function.Surjective (restrictEvaluation W p) := by
      intro q
      obtain ⟨v, hv⟩ := hsur q
      exact ⟨e.symm v, (heval p v).symm.trans hv⟩
    have hr := hW p
    rw [LinearMap.range_eq_top.mpr hE] at hr
    norm_num [Vec3] at hr
  obtain ⟨a, hBa, _⟩ := unique_finite_center_of_pin_determinants B hdet
  have hle : W ≤ finiteCenterSpace a := by
    intro X hX
    let x : W := ⟨X, hX⟩
    have ht := htrans (e x)
    rw [e.symm_apply_apply] at ht
    change B *ᵥ X.1 = X.2 at ht
    rw [hBa, scalarCrossMatrix_mulVec] at ht
    have hx : X.2 = a ⨯₃ X.1 := by simpa using ht.symm
    change X.2 + X.1 ⨯₃ a = 0
    rw [hx]
    exact cross_anticomm' a X.1
  have heq : W = finiteCenterSpace a :=
    Submodule.eq_of_le_of_finrank_eq hle (hd.trans (finrank_finiteCenterSpace a).symm)
  refine ⟨a, heq, ?_⟩
  intro b hb
  exact finiteCenterSpace_injective (hb.symm.trans heq)

/-- The ordinary plane perpendicular to `d`. -/
def normalPlane (d : Vec3) : Submodule ℝ Vec3 :=
  (dotProductBilin ℝ ℝ d).ker

theorem finrank_normalPlane (d : Vec3) (hd : d ≠ 0) :
    Module.finrank ℝ (normalPlane d) = 2 := by
  have hdd : d ⬝ᵥ d ≠ 0 := fun h => hd (dotProduct_self_eq_zero.mp h)
  have hs : Function.Surjective (dotProductBilin ℝ ℝ d) := by
    intro c
    refine ⟨(c / (d ⬝ᵥ d)) • d, ?_⟩
    change d ⬝ᵥ ((c / (d ⬝ᵥ d)) • d) = c
    rw [dotProduct_smul]
    change c / (d ⬝ᵥ d) * (d ⬝ᵥ d) = c
    exact div_mul_cancel₀ c hdd
  have h := (dotProductBilin ℝ ℝ d).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self, hdim] at h
  change 1 + Module.finrank ℝ (normalPlane d) = 3 at h
  omega

def infinityParameters (d : Vec3) : (ℝ × normalPlane d) →ₗ[ℝ] Twist :=
  ((LinearMap.fst ℝ ℝ (normalPlane d)).smulRight d).prod
    ((normalPlane d).subtype.comp (LinearMap.snd ℝ ℝ (normalPlane d)))

@[simp] theorem infinityParameters_apply (d : Vec3) (x : ℝ × normalPlane d) :
    infinityParameters d x = (x.1 • d, x.2.val) := rfl

theorem infinityParameters_injective (d : Vec3) (hd : d ≠ 0) :
    Function.Injective (infinityParameters d) := by
  intro x y hxy
  have hc := congrArg Prod.fst hxy
  have ht := congrArg Prod.snd hxy
  apply Prod.ext
  · exact smul_left_injective ℝ hd hc
  · exact Subtype.ext ht

theorem infinityParameters_range (d : Vec3) (hd : d ≠ 0) :
    (infinityParameters d).range = infiniteCenterSpace d := by
  ext X
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · change (x.1 • d) ⨯₃ d = 0
      simp
    · change x.2.val ⬝ᵥ d = 0
      have ht : d ⬝ᵥ x.2.val = 0 := x.2.property
      simpa only [dotProduct_comm] using ht
  · intro hX
    have hc : d ⨯₃ X.1 = 0 := by
      rw [← cross_anticomm X.1 d, hX.1, neg_zero]
    have hm : X.1 ∈ Submodule.span ℝ {d} := by
      rw [← ker_crossProduct_eq_span d hd]
      exact hc
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    let v : normalPlane d := ⟨X.2, by
      change d ⬝ᵥ X.2 = 0
      simpa only [dotProduct_comm] using hX.2⟩
    refine ⟨(c, v), ?_⟩
    exact Prod.ext hc rfl

theorem finrank_infiniteCenterSpace (d : Vec3) (hd : d ≠ 0) :
    Module.finrank ℝ (infiniteCenterSpace d) = 3 := by
  have h := LinearMap.finrank_range_of_inj (infinityParameters_injective d hd)
  rw [infinityParameters_range d hd] at h
  simpa [finrank_normalPlane d hd] using h

/-- The projective centers at infinity really have singular evaluation, too. -/
theorem infiniteCenterSpace_singular (d : Vec3) (hd : d ≠ 0) :
    SingularPinSpace (infiniteCenterSpace d) := by
  intro p
  have hle : (restrictEvaluation (infiniteCenterSpace d) p).range ≤ normalPlane d := by
    rintro v ⟨X, rfl⟩
    have hcross : d ⨯₃ X.val.1 = 0 := by
      rw [← cross_anticomm X.val.1 d, X.property.1, neg_zero]
    have hm : X.val.1 ∈ Submodule.span ℝ {d} := by
      rw [← ker_crossProduct_eq_span d hd]
      exact hcross
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    change d ⬝ᵥ (X.val.2 + X.val.1 ⨯₃ p) = 0
    rw [← hc, dotProduct_add]
    have ht : d ⬝ᵥ X.val.2 = 0 := by
      simpa only [dotProduct_comm] using X.property.2
    simp [ht]
  exact (Submodule.finrank_mono hle).trans_eq (finrank_normalPlane d hd)

/-- A finite center and a projective center at infinity are distinct. -/
theorem finiteCenterSpace_ne_infiniteCenterSpace (a d : Vec3) (hd : d ≠ 0) :
    finiteCenterSpace a ≠ infiniteCenterSpace d := by
  intro heq
  have hz : normalPlane d = ⊥ := by
    apply le_antisymm
    · intro t ht
      have hm : ((0 : Vec3), t) ∈ infiniteCenterSpace d := by
        constructor
        · simp
        · have htd : d ⬝ᵥ t = 0 := ht
          simpa only [dotProduct_comm] using htd
      rw [← heq] at hm
      have ht0 : t = 0 := by
        simpa [finiteCenterSpace, LinearMap.mem_ker, evaluateTwist_apply] using hm
      simpa using ht0
    · exact bot_le
  have hdim := finrank_normalPlane d hd
  rw [hz] at hdim
  simp at hdim

/-- The complete real twist-space classification used by the paper's
alternating-form lemma: finite or infinite common projective center. -/
theorem singularPinSpace_classification
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W) :
    (∃! a : Vec3, W = finiteCenterSpace a) ∨
      ∃ d : Vec3, d ≠ 0 ∧ W = infiniteCenterSpace d := by
  by_cases hi : Function.Injective (angularProjection W)
  · exact Or.inl (existsUnique_finiteCenter_of_injective_angular W hW hdim hi)
  · exact Or.inr (exists_infiniteCenter_of_not_injective_angular W hW hdim hi)

theorem finrank_eq_three_of_singularPinSpace
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W) : Module.finrank ℝ W = 3 := by
  rcases singularPinSpace_classification W hW hdim with ha | ⟨d, hd, he⟩
  · obtain ⟨a, he, _⟩ := ha
    rw [he]
    exact finrank_finiteCenterSpace a
  · rw [he]
    exact finrank_infiniteCenterSpace d hd

/-- Infinite centers giving the same space represent the same projective
point; their direction vectors differ by a nonzero scalar. -/
theorem infiniteCenters_scalar_equivalent (d e : Vec3) (hd : d ≠ 0) (he : e ≠ 0)
    (h : infiniteCenterSpace d = infiniteCenterSpace e) :
    ∃ c : ℝ, c ≠ 0 ∧ c • e = d := by
  have hm : (d, (0 : Vec3)) ∈ infiniteCenterSpace d := by constructor <;> simp
  rw [h] at hm
  have hc : e ⨯₃ d = 0 := by
    rw [← cross_anticomm d e, hm.1, neg_zero]
  have hmem : d ∈ Submodule.span ℝ {e} := by
    rw [← ker_crossProduct_eq_span e he]
    exact hc
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_, hc⟩
  intro hz
  apply hd
  simpa [hz] using hc.symm

end Papers.Rigidity

end
end BundleSource0012

section BundleSource0013
/- Source: Papers/RigidityCommonPinLowRank.lean -/




@[expose] public section

/-!
# Common-pin constraints of rank at most one force body merger

The rank bound is required on a nonempty open set of ordinary real pins.
The conclusion provides a pin in that same open set where every relative
twist evaluation is injective.  Together with the exact graph deletion
identity this proves the low-rank contradiction in the alternative
proof of Lemma 3.1.  All relative spaces are actual images of linear maps.
-/

namespace Papers.Rigidity.CommonPinLowRank

noncomputable section

open Matrix Module
open scoped Matrix

variable {U B : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype B]

def pointEvaluation : Vec3 →ₗ[ℝ] (Twist →ₗ[ℝ] Vec3) where
  toFun p := ((crossProduct (R := ℝ)).flip p).comp (LinearMap.fst ℝ Vec3 Vec3)
  map_add' p q := by
    apply LinearMap.ext
    intro X
    change X.1 ⨯₃ (p + q) = X.1 ⨯₃ p + X.1 ⨯₃ q
    exact map_add (crossProduct X.1) p q
  map_smul' c p := by
    apply LinearMap.ext
    intro X
    change X.1 ⨯₃ (c • p) = c • (X.1 ⨯₃ p)
    exact map_smul (crossProduct X.1) c p

@[simp] theorem pointEvaluation_apply (p : Vec3) (X : Twist) :
    pointEvaluation p X = X.1 ⨯₃ p := rfl

def operator (R : B → U →ₗ[ℝ] Twist) (p : Vec3) : U →ₗ[ℝ] (B → Vec3) :=
  LinearMap.pi fun b => (evaluateTwist p).comp (R b)

def linearPart (R : B → U →ₗ[ℝ] Twist) :
    Vec3 →ₗ[ℝ] (U →ₗ[ℝ] (B → Vec3)) where
  toFun p := LinearMap.pi fun b => (pointEvaluation p).comp (R b)
  map_add' p q := by
    ext u b i
    simp
  map_smul' c p := by
    ext u b i
    simp

theorem operator_eq_affineFamily (R : B → U →ₗ[ℝ] Twist) (p : Vec3) :
    operator R p = AffineRank.family (operator R 0) (linearPart R) p := by
  ext u b i
  simp [operator, linearPart, AffineRank.family, evaluateTwist_apply]

theorem exists_operator_rank_ge_two (R : B → U →ₗ[ℝ] Twist) (b : B)
    (hdim : 2 ≤ Module.finrank ℝ (R b).range) :
    ∃ p : Vec3, 2 ≤ Module.finrank ℝ (operator R p).range := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hdim
  have hxy : LinearIndependent ℝ ![(f 0 : Twist), (f 1 : Twist)] := by
    have hmap := hf.map' (R b).range.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    convert hmap using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨p, hp⟩ := exists_pin_separating_independent_twists (f 0) (f 1) hxy
  have heval : LinearIndependent ℝ ![evaluateTwist p (f 0), evaluateTwist p (f 1)] :=
    crossProduct_ne_zero_iff_linearIndependent.mp hp
  obtain ⟨x, hx⟩ := (f 0).2
  obtain ⟨y, hy⟩ := (f 1).2
  let z : Fin 2 → (operator R p).range :=
    ![⟨operator R p x, x, rfl⟩, ⟨operator R p y, y, rfl⟩]
  let proj : (operator R p).range →ₗ[ℝ] Vec3 :=
    (LinearMap.proj b).comp (operator R p).range.subtype
  have hproj : LinearIndependent ℝ (proj ∘ z) := by
    have heq : proj ∘ z = ![evaluateTwist p (f 0), evaluateTwist p (f 1)] := by
      funext i
      fin_cases i
      · change evaluateTwist p (R b x) = evaluateTwist p (f 0)
        rw [hx]
      · change evaluateTwist p (R b y) = evaluateTwist p (f 1)
        rw [hy]
    rw [heq]
    exact heval
  have hz : LinearIndependent ℝ z := LinearIndependent.of_comp proj hproj
  exact ⟨p, by simpa using hz.fintype_card_le_finrank⟩

/-- A rank-one common-pin family on an open set has no two-dimensional
relative twist image. -/
theorem relative_finrank_le_one_of_rank_le_one_on_open
    (R : B → U →ₗ[ℝ] Twist) (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hrank : ∀ p ∈ O, Module.finrank ℝ (operator R p).range ≤ 1) (b : B) :
    Module.finrank ℝ (R b).range ≤ 1 := by
  by_contra hdim
  obtain ⟨w, hw⟩ := exists_operator_rank_ge_two R b (by omega)
  have hdense := AffineRank.dense_setOf_le_rankAt (operator R 0) (linearPart R) 2
    ⟨w, by
      unfold AffineRank.rankAt
      rw [← operator_eq_affineFamily R w]
      exact hw⟩
  obtain ⟨p, hp, hpO⟩ := hdense.exists_mem_open hO hne
  have hlower : 2 ≤ Module.finrank ℝ (operator R p).range := by
    change 2 ≤ Module.finrank ℝ
      (AffineRank.family (operator R 0) (linearPart R) p).range at hp
    rwa [← operator_eq_affineFamily R p] at hp
  have hupper := hrank p hpO
  omega

private def restrictedLinearPart (W : Submodule ℝ Twist) :
    Vec3 →ₗ[ℝ] (W →ₗ[ℝ] Vec3) where
  toFun p := (pointEvaluation p).comp W.subtype
  map_add' p q := by ext X i; simp
  map_smul' c p := by ext X i; simp

private theorem restricted_eq_family (W : Submodule ℝ Twist) (p : Vec3) :
    restrictEvaluation W p =
      AffineRank.family (restrictEvaluation W 0) (restrictedLinearPart W) p := by
  ext X i
  simp [restrictEvaluation, restrictedLinearPart, AffineRank.family, evaluateTwist_apply]

theorem exists_injective_evaluation_of_finrank_le_one (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W ≤ 1) :
    ∃ p : Vec3, Function.Injective (restrictEvaluation W p) := by
  by_cases hzero : Module.finrank ℝ W = 0
  · have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp hzero
    subst W
    exact ⟨0, fun X Y _ => Subsingleton.elim X Y⟩
  have hone : Module.finrank ℝ W = 1 := by omega
  obtain ⟨X, hX⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank ℝ W)
  have hval : (X : Twist) ≠ 0 := fun h => hX (Subtype.ext h)
  obtain ⟨p, hp⟩ := exists_pin_detecting_nonzero_twist X hval
  have hrange : (restrictEvaluation W p).range ≠ ⊥ := by
    intro hbot
    have hm : evaluateTwist p X ∈ (restrictEvaluation W p).range := ⟨X, rfl⟩
    rw [hbot] at hm
    exact hp hm
  have hlower := Submodule.one_le_finrank_iff.mpr hrange
  have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
  rw [hone] at hnull
  have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
  exact ⟨p, LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)⟩

theorem dense_injective_evaluation_of_finrank_le_one (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W ≤ 1) :
    Dense {p : Vec3 | Function.Injective (restrictEvaluation W p)} := by
  obtain ⟨w, hw⟩ := exists_injective_evaluation_of_finrank_le_one W hW
  have hwRank := LinearMap.finrank_range_of_inj hw
  have hdense := AffineRank.dense_setOf_le_rankAt
    (restrictEvaluation W 0) (restrictedLinearPart W) (Module.finrank ℝ W)
    ⟨w, by
      unfold AffineRank.rankAt
      rw [← restricted_eq_family W w]
      exact hwRank.ge⟩
  apply hdense.mono
  intro p hp
  have hlower : Module.finrank ℝ W ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    change _ ≤ Module.finrank ℝ
      (AffineRank.family (restrictEvaluation W 0) (restrictedLinearPart W) p).range at hp
    rwa [← restricted_eq_family W p] at hp
  have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
  have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

/-- The elementary two-twist separation lemma gives an injective pin for
every actual twist space of dimension at most two. -/
theorem exists_injective_evaluation_of_finrank_le_two (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W ≤ 2) :
    ∃ p : Vec3, Function.Injective (restrictEvaluation W p) := by
  by_cases hsmall : Module.finrank ℝ W ≤ 1
  · exact exists_injective_evaluation_of_finrank_le_one W hsmall
  have hdim : Module.finrank ℝ W = 2 := by omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank
    (show 2 ≤ Module.finrank ℝ W by omega)
  have hxy : LinearIndependent ℝ ![(f 0 : Twist), (f 1 : Twist)] := by
    have hmap := hf.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    convert hmap using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨p, hp⟩ := exists_pin_separating_independent_twists (f 0) (f 1) hxy
  have heval : LinearIndependent ℝ (fun i : Fin 2 => evaluateTwist p (f i)) := by
    have h := crossProduct_ne_zero_iff_linearIndependent.mp hp
    convert h using 1
    funext i
    fin_cases i <;> rfl
  let z : Fin 2 → (restrictEvaluation W p).range :=
    fun i => ⟨restrictEvaluation W p (f i), f i, rfl⟩
  have hz : LinearIndependent ℝ z :=
    LinearIndependent.of_comp (restrictEvaluation W p).range.subtype heval
  have hlower : 2 ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    simpa only [Fintype.card_fin] using hz.fintype_card_le_finrank
  have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
  have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
  exact ⟨p, LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)⟩

theorem dense_injective_evaluation_of_finrank_le_two (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W ≤ 2) :
    Dense {p : Vec3 | Function.Injective (restrictEvaluation W p)} := by
  obtain ⟨w, hw⟩ := exists_injective_evaluation_of_finrank_le_two W hW
  have hwRank := LinearMap.finrank_range_of_inj hw
  have hdense := AffineRank.dense_setOf_le_rankAt
    (restrictEvaluation W 0) (restrictedLinearPart W) (Module.finrank ℝ W)
    ⟨w, by
      unfold AffineRank.rankAt
      rw [← restricted_eq_family W w]
      exact hwRank.ge⟩
  apply hdense.mono
  intro p hp
  have hlower : Module.finrank ℝ W ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    change _ ≤ Module.finrank ℝ
      (AffineRank.family (restrictEvaluation W 0) (restrictedLinearPart W) p).range at hp
    rwa [← restricted_eq_family W p] at hp
  have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
  have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

/-- A nonzero stationary vector in a fixed twist subspace at every pin
of an open set forces that subspace to have dimension at least three. -/
theorem three_le_finrank_of_stationary_family_on_open
    (W : Submodule ℝ Twist) (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hstationary : ∀ p ∈ O, ∃ X : W, X ≠ 0 ∧ evaluateTwist p X.val = 0) :
    3 ≤ Module.finrank ℝ W := by
  by_contra hsmall
  have hdense := dense_injective_evaluation_of_finrank_le_two W (by omega)
  obtain ⟨p, hp, hpO⟩ := hdense.exists_mem_open hO hne
  obtain ⟨X, hX, hXp⟩ := hstationary p hpO
  apply hX
  apply hp
  simpa [restrictEvaluation] using hXp

/-- If a three-dimensional actual twist space has a stationary member
at every pin in a nonempty open set, its evaluation is singular at every
pin. The affine matrix rank loci, not a closure assumption, give this
extension from the open set. -/
theorem singularPinSpace_of_stationary_family_on_open
    (W : Submodule ℝ Twist) (hW : Module.finrank ℝ W = 3)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hstationary : ∀ p ∈ O, ∃ X : W, X ≠ 0 ∧ evaluateTwist p X.val = 0) :
    SingularPinSpace W := by
  intro q
  by_contra hlarge
  have hlower : 3 ≤ Module.finrank ℝ (restrictEvaluation W q).range := by omega
  have hdense := AffineRank.dense_setOf_le_rankAt
    (restrictEvaluation W 0) (restrictedLinearPart W) 3
    ⟨q, by
      unfold AffineRank.rankAt
      rw [← restricted_eq_family W q]
      exact hlower⟩
  obtain ⟨p, hp, hpO⟩ := hdense.exists_mem_open hO hne
  have hrank : 3 ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    change _ ≤ Module.finrank ℝ
      (AffineRank.family (restrictEvaluation W 0) (restrictedLinearPart W) p).range at hp
    rwa [← restricted_eq_family W p] at hp
  have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
  have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
  have hinj := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  obtain ⟨X, hX, hXp⟩ := hstationary p hpO
  apply hX
  apply hinj
  simpa [restrictEvaluation] using hXp

theorem isOpen_injective_evaluation (W : Submodule ℝ Twist) :
    IsOpen {p : Vec3 | Function.Injective (restrictEvaluation W p)} := by
  have hopen := AffineRank.isOpen_setOf_le_rankAt
    (restrictEvaluation W 0) (restrictedLinearPart W) (Module.finrank ℝ W)
  convert hopen using 1
  ext p
  simp only [Set.mem_setOf_eq, AffineRank.rankAt]
  rw [← restricted_eq_family W p]
  constructor
  · intro h
    exact (LinearMap.finrank_range_of_inj h).ge
  · intro h
    have hnull := (restrictEvaluation W p).finrank_range_add_finrank_ker
    have hker : Module.finrank ℝ (restrictEvaluation W p).ker = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

/-- The same open set contains a pin at which zero common-pin velocity
forces every relative twist itself to vanish. -/
theorem exists_pin_detecting_all_relative_twists
    (R : B → U →ₗ[ℝ] Twist) (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hrank : ∀ p ∈ O, Module.finrank ℝ (operator R p).range ≤ 1) :
    ∃ p ∈ O, ∀ u : U, operator R p u = 0 → ∀ b, R b u = 0 := by
  have hdim (b : B) : Module.finrank ℝ (R b).range ≤ 1 :=
    relative_finrank_le_one_of_rank_le_one_on_open R O hO hne hrank b
  have hdense : Dense (⋂ b : B,
      {p : Vec3 | Function.Injective (restrictEvaluation (R b).range p)}) :=
    dense_iInter_of_isOpen (fun b => isOpen_injective_evaluation (R b).range)
      (fun b => dense_injective_evaluation_of_finrank_le_one (R b).range (hdim b))
  obtain ⟨p, hp, hpO⟩ := hdense.exists_mem_open hO hne
  refine ⟨p, hpO, ?_⟩
  intro u hu b
  have hinj := Set.mem_iInter.mp hp b
  have hzero : restrictEvaluation (R b).range p ⟨R b u, u, rfl⟩ =
      restrictEvaluation (R b).range p 0 := by
    simpa [operator, restrictEvaluation] using congrFun hu b
  exact congrArg Subtype.val (hinj hzero)

end

end Papers.Rigidity.CommonPinLowRank

end
end BundleSource0013

section BundleSource0014
/- Source: Papers/RigidityVertexPinVariation.lean -/




@[expose] public section

/-!
# Varying the deleted vertex while keeping the old framework fixed

The old motion kernel and the extracted triangle twists are identified
explicitly under replacement of the new pin.  Consequently the actual
graph rank identity becomes an affine family on one fixed vector space.
-/

namespace Papers.Rigidity.VertexPin

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V B : Type} [Fintype V] [Fintype B]

def replacePlacement (p : Placement V 3) (v : V) (q : Vec3) : Placement V 3 :=
  fun w => if w = v then q else p w

@[simp] theorem replacePlacement_vertex (p : Placement V 3) (v : V) (q : Vec3) :
    replacePlacement p v q v = q := by simp [replacePlacement]

@[simp] theorem replacePlacement_other (p : Placement V 3) (v : V) (q : Vec3)
    (w : DeletedVertex v) : replacePlacement p v q w.1 = p w.1 := by
  simp [replacePlacement, w.2]

@[simp] theorem replacePlacement_self (p : Placement V 3) (v : V) :
    replacePlacement p v (p v) = p := by
  ext w j
  by_cases hw : w = v <;> simp [replacePlacement, hw]

theorem continuous_replacePlacement (p : Placement V 3) (v : V) :
    Continuous (replacePlacement p v) := by
  apply continuous_pi
  intro w
  apply continuous_pi
  intro j
  by_cases hw : w = v
  · simpa only [replacePlacement, if_pos hw] using
      (continuous_apply j : Continuous (fun q : Vec3 => q j))
  · simpa only [replacePlacement, if_neg hw] using
      (continuous_const : Continuous (fun _ : Vec3 => p w j))

@[simp] theorem deletedPlacement_replace (p : Placement V 3) (v : V) (q : Vec3) :
    deletedPlacement (replacePlacement p v q) v = deletedPlacement p v := by
  ext w j
  simp [deletedPlacement]

def deletedMotionEquivReplace (G : SimpleGraph V) (p : Placement V 3) (v : V) (q : Vec3) :
    DeletedMotions G (replacePlacement p v q) v ≃ₗ[ℝ] DeletedMotions G p v :=
  LinearEquiv.ofEq
    (DeletedMotions G (replacePlacement p v q) v) (DeletedMotions G p v) (by
      change (rigidityOperator (deletedGraph G v)
        (deletedPlacement (replacePlacement p v q) v)).ker =
          (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).ker
      rw [deletedPlacement_replace])

@[simp] theorem deletedMotionEquivReplace_apply (G : SimpleGraph V)
    (p : Placement V 3) (v : V) (q : Vec3)
    (u : DeletedMotions G (replacePlacement p v q) v) :
    (deletedMotionEquivReplace G p v q u).1 = u.1 := rfl

namespace IncidentTetrahedra

variable {G : SimpleGraph V} {v : V}

@[simp] theorem trianglePoints_replace (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (q : Vec3) (b : B) :
    T.trianglePoints (replacePlacement p v q) b = T.trianglePoints p b := by
  ext i j
  simp [trianglePoints]

theorem noncollinear_replace (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) :
    T.NoncollinearAt (replacePlacement p v q) := by
  intro b
  simpa only [trianglePoints_replace] using hp b

theorem bodyTwist_replace (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) (b : B)
    (u : DeletedMotions G (replacePlacement p v q) v) :
    T.bodyTwist (replacePlacement p v q) (T.noncollinear_replace p hp q) b u =
      T.bodyTwist p hp b (deletedMotionEquivReplace G p v q u) := by
  apply triangleTwistOperator_injective (T.trianglePoints p b) (hp b)
  ext a
  have hnew := congrFun (T.bodyTwist_fit (replacePlacement p v q)
    (T.noncollinear_replace p hp q) b u a.1) a.2
  have hold := congrFun (T.bodyTwist_fit p hp b
    (deletedMotionEquivReplace G p v q u) a.1) a.2
  simpa only [trianglePoints_replace, deletedMotionEquivReplace_apply,
    triangleTwistOperator_apply] using hnew.trans hold.symm

def relativeTwists (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) (b : B) : DeletedMotions G p v →ₗ[ℝ] Twist :=
  T.bodyTwist p hp b - T.bodyTwist p hp base

def commonPinAt (T : IncidentTetrahedra G v B) (p : Placement V 3)
    (hp : T.NoncollinearAt p) (base : B) (q : Vec3) :
    DeletedMotions G p v →ₗ[ℝ] (B → Vec3) :=
  CommonPinLowRank.operator (T.relativeTwists p hp base) q

theorem commonPinOperator_replace (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) (base : B) :
    T.commonPinOperator (replacePlacement p v q) (T.noncollinear_replace p hp q) base =
      (T.commonPinAt p hp base q).comp (deletedMotionEquivReplace G p v q).toLinearMap := by
  ext u b j
  simp [commonPinOperator_apply, commonPinAt, CommonPinLowRank.operator,
    relativeTwists, T.bodyTwist_replace p hp q] <;> abel

theorem commonPinRank_replace (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3) (base : B) :
    Module.finrank ℝ
      (T.commonPinOperator (replacePlacement p v q) (T.noncollinear_replace p hp q) base).range =
      Module.finrank ℝ (T.commonPinAt p hp base q).range := by
  rw [commonPinOperator_replace, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (deletedMotionEquivReplace G p v q).surjective,
    Submodule.map_top]

/-- The deletion identity on one fixed old motion space, uniformly in
every transverse new pin. -/
theorem rigidityRank_replace_identity (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : T.NoncollinearAt p) (q : Vec3)
    (ht : T.TransverseAt (replacePlacement p v q)) (base : B) :
    rigidityRank G (replacePlacement p v q) =
      rigidityRank (deletedGraph G v) (deletedPlacement p v) + 3 +
        Module.finrank ℝ (T.commonPinAt p hp base q).range := by
  have h := T.rigidityRank_deletion_identity (replacePlacement p v q)
    (T.noncollinear_replace p hp q) ht base
  rw [deletedPlacement_replace, T.commonPinRank_replace p hp q base] at h
  exact h

theorem isOpen_transverse_pins (T : IncidentTetrahedra G v B) (p : Placement V 3) :
    IsOpen {q : Vec3 | T.TransverseAt (replacePlacement p v q)} := by
  have heq : {q : Vec3 | T.TransverseAt (replacePlacement p v q)} =
      ⋂ b : B, {q : Vec3 | LinearIndependent ℝ
        (fun i : Fin 3 => q - T.trianglePoints p b i)} := by
    ext q
    simp [TransverseAt]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro b
  have hc : Continuous (fun q : Vec3 => fun i : Fin 3 => q - T.trianglePoints p b i) :=
    continuous_pi fun i => continuous_id.sub continuous_const
  exact isOpen_setOfPred_linearIndependent.preimage hc

/-- Around a generic transverse placement, varying only `v` preserves
every graph's maximum rank and every incident tetrahedron's transversality. -/
theorem exists_open_generic_pin_window (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hp : IsGenericPlacement p) (ht : T.TransverseAt p) :
    ∃ O : Set Vec3, IsOpen O ∧ p v ∈ O ∧
      ∀ q ∈ O, IsGenericPlacement (replacePlacement p v q) ∧
        T.TransverseAt (replacePlacement p v q) := by
  let O := {q : Vec3 | IsGenericPlacement (replacePlacement p v q)} ∩
    {q : Vec3 | T.TransverseAt (replacePlacement p v q)}
  refine ⟨O, ?_, ?_, fun _ h => h⟩
  · exact (isOpen_isGenericPlacement.preimage (continuous_replacePlacement p v)).inter
      (T.isOpen_transverse_pins p)
  · simpa [O] using And.intro hp ht

end IncidentTetrahedra

end

end Papers.Rigidity.VertexPin

end
end BundleSource0014

section BundleSource0015
/- Source: Papers/RigidityGeneralPosition.lean -/






@[expose] public section

/-!
# Simultaneous genuine generic rank and geometric general position

Every finite graph has real placements which simultaneously attain all
graph ranks, have no repeated points, have no collinear triples, and have
no coplanar quadruples.  Each condition is proved open and dense from an
explicit full-rank specialization.  No generic point is postulated.
-/

namespace Papers.Rigidity.GeneralPosition

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V B : Type} [Fintype V]

def displacementMatrix {n : ℕ} (f : Fin (n + 1) ↪ V) (p : Placement V 3) :
    Matrix (Fin n) (Fin 3) ℝ := fun i => p (f i.succ) - p (f 0)

def displacementFamily {n : ℕ} (f : Fin (n + 1) ↪ V) :
    Placement V 3 →ₗ[ℝ] (Vec3 →ₗ[ℝ] (Fin n → ℝ)) where
  toFun p := (displacementMatrix f p).mulVecLin
  map_add' p q := by
    apply LinearMap.ext
    intro z
    funext i
    simp [displacementMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro z
    funext i
    simp [displacementMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem displacement_independent_iff_rank {n : ℕ} (f : Fin (n + 1) ↪ V)
    (p : Placement V 3) :
    LinearIndependent ℝ (displacementMatrix f p).row ↔
      (displacementMatrix f p).rank = n := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    ← (displacementMatrix f p).rank_eq_finrank_span_row]
  simp only [Fintype.card_fin, eq_comm]

/-- Assign zero to the distinguished point and independent coordinate
vectors to the other labelled points. -/
theorem exists_displacement_independent {n : ℕ} (hn : n ≤ 3)
    (f : Fin (n + 1) ↪ V) :
    ∃ p : Placement V 3, LinearIndependent ℝ (displacementMatrix f p).row := by
  let e : Fin n ↪ Fin 3 := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  let g : Fin (n + 1) → Vec3 :=
    Fin.cases 0 (fun i => Pi.basisFun ℝ (Fin 3) (e i))
  let p : Placement V 3 := Function.extend f g 0
  have hp (i : Fin (n + 1)) : p (f i) = g i := f.injective.extend_apply g 0 i
  have heq : (displacementMatrix f p).row =
      fun i : Fin n => Pi.basisFun ℝ (Fin 3) (e i) := by
    rw [Matrix.row_def]
    ext i j
    simp [displacementMatrix, hp, g]
  refine ⟨p, ?_⟩
  rw [heq]
  exact (Pi.basisFun ℝ (Fin 3)).linearIndependent.comp e e.injective

theorem isOpen_displacement_independent {n : ℕ} (f : Fin (n + 1) ↪ V) :
    IsOpen {p : Placement V 3 | LinearIndependent ℝ (displacementMatrix f p).row} := by
  have hc : Continuous (fun p : Placement V 3 => (displacementMatrix f p).row) := by
    apply continuous_pi
    intro i
    exact (continuous_apply (f i.succ)).sub (continuous_apply (f 0))
  exact isOpen_setOfPred_linearIndependent.preimage hc

theorem dense_displacement_independent {n : ℕ} (hn : n ≤ 3)
    (f : Fin (n + 1) ↪ V) :
    Dense {p : Placement V 3 | LinearIndependent ℝ (displacementMatrix f p).row} := by
  obtain ⟨w, hw⟩ := exists_displacement_independent hn f
  have hwrank := (displacement_independent_iff_rank f w).mp hw
  have hrank (q : Placement V 3) :
      AffineRank.rankAt 0 (displacementFamily f) q = (displacementMatrix f q).rank := by
    unfold AffineRank.rankAt AffineRank.family
    rw [zero_add]
    rfl
  have hdense := AffineRank.dense_setOf_le_rankAt 0 (displacementFamily f) n
    ⟨w, by rw [hrank]; exact hwrank.ge⟩
  apply hdense.mono
  intro p hp
  apply (displacement_independent_iff_rank f p).mpr
  have hlower : n ≤ (displacementMatrix f p).rank := by
    change n ≤ AffineRank.rankAt 0 (displacementFamily f) p at hp
    rw [hrank] at hp
    exact hp
  exact le_antisymm (by simpa using Matrix.rank_le_card_height (displacementMatrix f p)) hlower

/-- Every ordered selection of at most four distinct vertices is affinely
independent, recorded as independence of its actual displacement vectors. -/
def InGeneralPosition (p : Placement V 3) : Prop :=
  ∀ n : Fin 4, ∀ f : Fin (n.val + 1) ↪ V,
    LinearIndependent ℝ (displacementMatrix f p).row

theorem isOpen_generalPosition : IsOpen {p : Placement V 3 | InGeneralPosition p} := by
  have heq : {p : Placement V 3 | InGeneralPosition p} =
      ⋂ n : Fin 4, ⋂ f : Fin (n.val + 1) ↪ V,
        {p : Placement V 3 | LinearIndependent ℝ (displacementMatrix f p).row} := by
    ext p
    simp [InGeneralPosition]
  rw [heq]
  exact isOpen_iInter_of_finite fun n => isOpen_iInter_of_finite fun f =>
    isOpen_displacement_independent f

theorem dense_generalPosition : Dense {p : Placement V 3 | InGeneralPosition p} := by
  have heq : {p : Placement V 3 | InGeneralPosition p} =
      ⋂ n : Fin 4, ⋂ f : Fin (n.val + 1) ↪ V,
        {p : Placement V 3 | LinearIndependent ℝ (displacementMatrix f p).row} := by
    ext p
    simp [InGeneralPosition]
  rw [heq]
  apply dense_iInter_of_isOpen
  · intro n
    exact isOpen_iInter_of_finite fun f => isOpen_displacement_independent f
  · intro n
    exact dense_iInter_of_isOpen (fun f => isOpen_displacement_independent f)
      (fun f => dense_displacement_independent (by omega : n.val ≤ 3) f)

/-- Generic rank and geometric nondegeneracy are achieved together. -/
theorem exists_generic_generalPosition :
    ∃ p : Placement V 3, IsGenericPlacement p ∧ InGeneralPosition p := by
  have hgen : ({p : Placement V 3 | IsGenericPlacement p}).Nonempty :=
    exists_isGenericPlacement 3
  obtain ⟨p, hpGeom, hpGeneric⟩ :=
    dense_generalPosition.exists_mem_open isOpen_isGenericPlacement hgen
  exact ⟨p, hpGeneric, hpGeom⟩

theorem InGeneralPosition.comp_embedding {W : Type} [Fintype W]
    (p : Placement V 3) (hp : InGeneralPosition p) (e : W ↪ V) :
    InGeneralPosition (p ∘ e) := by
  intro n f
  exact hp n (f.trans e)

theorem InGeneralPosition.triangle (p : Placement V 3) (hp : InGeneralPosition p)
    (f : Fin 3 ↪ V) : NoncollinearTriangle (p ∘ f) := by
  change LinearIndependent ℝ ![p (f 1) - p (f 0), p (f 2) - p (f 0)]
  have heq : (displacementMatrix f p).row =
      ![p (f 1) - p (f 0), p (f 2) - p (f 0)] := by
    funext i
    fin_cases i <;> rfl
  rw [← heq]
  exact hp (2 : Fin 4) f

theorem InGeneralPosition.star (p : Placement V 3) (hp : InGeneralPosition p)
    (v : V) (f : Fin 3 ↪ {w : V // w ≠ v}) :
    LinearIndependent ℝ (fun i : Fin 3 => p v - p (f i).1) := by
  let g : Fin 4 ↪ V :=
    { toFun := Fin.cases v (fun i => (f i).1)
      inj' := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => rfl
          | succ j => exact False.elim ((f j).2 hij.symm)
        | succ i =>
          cases j using Fin.cases with
          | zero => exact False.elim ((f i).2 hij)
          | succ j => exact congrArg Fin.succ (f.injective (Subtype.ext hij)) }
  have h := (hp (3 : Fin 4) g).neg
  change LinearIndependent ℝ (fun i : Fin 3 => -(p (f i).1 - p v)) at h
  simpa only [neg_sub] using h

theorem InGeneralPosition.incident_noncollinear (p : Placement V 3)
    (hp : InGeneralPosition p) {G : SimpleGraph V} {v : V}
    (T : VertexPin.IncidentTetrahedra G v B) : T.NoncollinearAt p := by
  intro b
  let f : Fin 3 ↪ V :=
    ⟨fun i => (T.triangle b i).1, fun _ _ h => T.injective b (Subtype.ext h)⟩
  exact InGeneralPosition.triangle p hp f

theorem InGeneralPosition.incident_transverse (p : Placement V 3)
    (hp : InGeneralPosition p) {G : SimpleGraph V} {v : V}
    (T : VertexPin.IncidentTetrahedra G v B) : T.TransverseAt p := by
  intro b
  exact InGeneralPosition.star p hp v ⟨T.triangle b, T.injective b⟩

end

end Papers.Rigidity.GeneralPosition

end
end BundleSource0015

section BundleSource0016
/- Source: Papers/RigidityRestriction.lean -/



@[expose] public section

/-!
# Restricting a generic placement to a vertex set

An induced framework has the same rank as its extension by isolated vertices.
This proves that the simultaneous maximum-rank semantics commute with taking
vertex subsets, including empty and small subsets.
-/

namespace Papers.Rigidity.BarJoint

open scoped Classical

def liftGraph {V : Type} (S : Finset V) (H : SimpleGraph {v : V // v ∈ S}) :
    SimpleGraph V where
  Adj v w := ∃ hv : v ∈ S, ∃ hw : w ∈ S, H.Adj ⟨v, hv⟩ ⟨w, hw⟩
  symm := by
    constructor
    rintro v w ⟨hv, hw, h⟩
    exact ⟨hw, hv, h.symm⟩
  loopless := by
    constructor
    intro v
    rintro ⟨hv, hw, h⟩
    exact H.loopless.irrefl ⟨v, hv⟩ h

def restrictVelocity {V : Type} (S : Finset V) (d : ℕ) :
    Velocity V d →ₗ[ℝ] Velocity {v : V // v ∈ S} d where
  toFun u v := u v.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def extendVelocity {V : Type} (S : Finset V) (d : ℕ)
    (u : Velocity {v : V // v ∈ S} d) : Velocity V d :=
  fun v => if hv : v ∈ S then u ⟨v, hv⟩ else 0

@[simp] theorem restrict_extendVelocity {V : Type} (S : Finset V) (d : ℕ)
    (u : Velocity {v : V // v ∈ S} d) :
    restrictVelocity S d (extendVelocity S d u) = u := by
  ext v i
  simp [restrictVelocity, extendVelocity, v.property]

theorem restrictVelocity_surjective {V : Type} (S : Finset V) (d : ℕ) :
    Function.Surjective (restrictVelocity S d) :=
  fun u => ⟨extendVelocity S d u, restrict_extendVelocity S d u⟩

noncomputable def extendConstraint {V : Type} (S : Finset V) :
    ({v : V // v ∈ S} × {v : V // v ∈ S} → ℝ) →ₗ[ℝ] (V × V → ℝ) where
  toFun f vw := if h : vw.1 ∈ S ∧ vw.2 ∈ S then
      f (⟨vw.1, h.1⟩, ⟨vw.2, h.2⟩) else 0
  map_add' f g := by
    ext vw
    split_ifs with h <;> simp [h]
  map_smul' c f := by
    ext vw
    split_ifs with h <;> simp [h]

theorem extendConstraint_injective {V : Type} (S : Finset V) :
    Function.Injective (extendConstraint S) := by
  intro f g h
  ext vw
  have he := congrFun h (vw.1.val, vw.2.val)
  simpa [extendConstraint, vw.1.property, vw.2.property] using he

theorem rigidityOperator_liftGraph {V : Type} (S : Finset V)
    (H : SimpleGraph {v : V // v ∈ S}) {d : ℕ} (p : Placement V d) :
    rigidityOperator (liftGraph S H) p =
      (extendConstraint S).comp
        ((rigidityOperator H (restrictVelocity S d p)).comp (restrictVelocity S d)) := by
  ext u vw
  rcases vw with ⟨v, w⟩
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
  · by_cases he : H.Adj ⟨v, hv⟩ ⟨w, hw⟩ <;>
      simp [rigidityOperator, liftGraph, restrictVelocity, extendConstraint,
        hv, hw, he, edgeConstraint]
  · simp [rigidityOperator, liftGraph, extendConstraint, hv, hw]
  · simp [rigidityOperator, liftGraph, extendConstraint, hv, hw]
  · simp [rigidityOperator, liftGraph, extendConstraint, hv, hw]

theorem rigidityRank_liftGraph {V : Type} [Fintype V] (S : Finset V)
    (H : SimpleGraph {v : V // v ∈ S}) {d : ℕ} (p : Placement V d) :
    rigidityRank (liftGraph S H) p = rigidityRank H (restrictVelocity S d p) := by
  let R := rigidityOperator H (restrictVelocity S d p)
  have hr : (R.comp (restrictVelocity S d)).range = R.range := by
    rw [LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (restrictVelocity_surjective S d), Submodule.map_top]
  rw [rigidityRank, rigidityOperator_liftGraph, LinearMap.range_comp, hr]
  exact (Submodule.equivMapOfInjective (extendConstraint S)
    (extendConstraint_injective S) R.range).finrank_eq.symm

theorem genericRigidityRank_liftGraph {V : Type} [Fintype V] (S : Finset V)
    (H : SimpleGraph {v : V // v ∈ S}) (d : ℕ) :
    genericRigidityRank (liftGraph S H) d = genericRigidityRank H d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank (liftGraph S H) d
    rw [← hp, rigidityRank_liftGraph]
    exact rigidityRank_le_genericRigidityRank H d _
  · obtain ⟨q, hq⟩ := exists_rigidityRank_eq_genericRigidityRank H d
    have hr := rigidityRank_le_genericRigidityRank (liftGraph S H) d (extendVelocity S d q)
    rw [rigidityRank_liftGraph, restrict_extendVelocity, hq] at hr
    exact hr

theorem isGenericPlacement_restrict {V : Type} [Fintype V] {d : ℕ}
    (p : Placement V d) (hp : IsGenericPlacement p) (S : Finset V) :
    IsGenericPlacement (restrictVelocity S d p) := by
  intro H
  have he := hp (liftGraph S H)
  change rigidityRank (liftGraph S H) p = genericRigidityRank (liftGraph S H) d at he
  rwa [rigidityRank_liftGraph, genericRigidityRank_liftGraph] at he

end Papers.Rigidity.BarJoint

end
end BundleSource0016

section BundleSource0017
/- Source: Papers/RigidityRelabelling.lean -/



@[expose] public section

/-!
# Relabelling actual rigidity operators

This transports the full motion kernel and attained generic rank across a
vertex equivalence. It permits finite labelled models to be used for arbitrary
finite vertex types without restricting any graph in the principal claims.
-/

namespace Papers.Rigidity.BarJoint

variable {V W : Type} [Fintype V] [Fintype W]

noncomputable def relabelMotionKernel (e : V ≃ W) (G : SimpleGraph V)
    {d : ℕ} (p : Placement V d) :
    (rigidityOperator G p).ker ≃ₗ[ℝ]
      (rigidityOperator (G.comap e.symm) (p ∘ e.symm)).ker where
  toFun u := ⟨u.val ∘ e.symm, by
    change IsInfinitesimalMotion (G.comap e.symm) (p ∘ e.symm) (u.val ∘ e.symm)
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    exact (isInfinitesimalMotion_iff G p u.val).mp u.property
      (e.symm a) (e.symm b) hab⟩
  invFun u := ⟨u.val ∘ e, by
    change IsInfinitesimalMotion G p (u.val ∘ e)
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    have h := (isInfinitesimalMotion_iff (G.comap e.symm) (p ∘ e.symm) u.val).mp
      u.property (e a) (e b) (by simpa using hab)
    simpa [edgeConstraint] using h⟩
  left_inv u := by
    apply Subtype.ext
    funext v
    simp
  right_inv u := by
    apply Subtype.ext
    funext v
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rigidityRank_relabel (e : V ≃ W) (G : SimpleGraph V)
    {d : ℕ} (p : Placement V d) :
    rigidityRank (G.comap e.symm) (p ∘ e.symm) = rigidityRank G p := by
  have hk := (relabelMotionKernel e G p).finrank_eq
  have hV := (rigidityOperator G p).finrank_range_add_finrank_ker
  have hW := (rigidityOperator (G.comap e.symm) (p ∘ e.symm)).finrank_range_add_finrank_ker
  have hd : Module.finrank ℝ (Velocity V d) = Module.finrank ℝ (Velocity W d) := by
    rw [finrank_velocity, finrank_velocity, Fintype.card_congr e]
  change Module.finrank ℝ (rigidityOperator (G.comap e.symm) (p ∘ e.symm)).range =
    Module.finrank ℝ (rigidityOperator G p).range
  omega

theorem genericRigidityRank_relabel (e : V ≃ W) (G : SimpleGraph V) (d : ℕ) :
    genericRigidityRank (G.comap e.symm) d = genericRigidityRank G d := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank (G.comap e.symm) d
    have hr := rigidityRank_relabel e G (p ∘ e)
    have he : (p ∘ e) ∘ e.symm = p := by funext v; simp
    rw [he, hp] at hr
    exact hr.le.trans (rigidityRank_le_genericRigidityRank G d (p ∘ e))
  · obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank G d
    have h := rigidityRank_le_genericRigidityRank (G.comap e.symm) d (p ∘ e.symm)
    rwa [rigidityRank_relabel, hp] at h

theorem isGenericallyRigid_relabel_iff (e : V ≃ W) (G : SimpleGraph V) (d : ℕ) :
    IsGenericallyRigidInDimension (G.comap e.symm) d ↔ IsGenericallyRigidInDimension G d := by
  have htop : (SimpleGraph.completeGraph V).comap e.symm =
      SimpleGraph.completeGraph W := by
    ext a b
    simp only [SimpleGraph.comap_adj, SimpleGraph.completeGraph_eq_top,
      SimpleGraph.top_adj, e.symm.injective.ne_iff]
  have hc := genericRigidityRank_relabel e (SimpleGraph.completeGraph V) d
  rw [htop] at hc
  unfold IsGenericallyRigidInDimension
  rw [genericRigidityRank_relabel, hc]

end Papers.Rigidity.BarJoint

end
end BundleSource0017

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0017/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0017.json"

section BundleSource0018
/- Source: Papers/RigidityClosure.lean -/





@[expose] public section

/-!
# Completing rigid clusters and the implication in Corollary 1.2

Completing a family of clusters does not increase actual generic rigidity
rank. The corollary is then reduced to Theorem 1.1 by a proved implication;
Theorem 1.1 is not supplied as an axiom or declared proved here.
-/

namespace Papers.Rigidity

open BarJoint
open scoped Classical

/-- Passing from an arbitrary rigid covering subgraph to its ambient
induced graph preserves precisely the edge-cover hypothesis of Corollary 1.2. -/
theorem rigidSubgraphCovered_iff_rigidInducedCovered
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    RigidSubgraphCovered G ↔ RigidInducedCovered G := by
  constructor
  · intro h v w hvw
    obtain ⟨S, hcard, hv, hw, H, hle, _, hrigid⟩ := h v w hvw
    exact ⟨S, hcard, hv, hw, hrigid.mono hle⟩
  · intro h v w hvw
    obtain ⟨S, hcard, hv, hw, hrigid⟩ := h v w hvw
    exact ⟨S, hcard, hv, hw, G.induce (S : Set V), le_rfl, hvw, hrigid⟩

theorem VertexConnected.mono {V : Type} [Fintype V] {G H : SimpleGraph V} {k : ℕ}
    (hG : VertexConnected G k) (hGH : G ≤ H) : VertexConnected H k := by
  refine ⟨hG.1, ?_⟩
  intro S hS
  apply SimpleGraph.Connected.mono (G := G.induce ((S : Set V)ᶜ)) _ (hG.2 S hS)
  intro v w hvw
  exact hGH hvw

/-- An induced rigid subgraph is an ambient rigid cluster, proved by
restricting generic placements and actual infinitesimal motions. -/
theorem RigidInducedSubgraph.rigidCluster {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (hS : RigidInducedSubgraph G S) :
    RigidCluster G S := by
  obtain ⟨p, hp⟩ := exists_isGenericPlacement (V := V) 3
  let H := clusterCompletion (fun _ : Unit => S)
  let pS := restrictVelocity S 3 p
  have hpS : IsGenericPlacement pS := isGenericPlacement_restrict p hp S
  have hrankS : genericRigidityRank (G.induce (S : Set V)) 3 =
      genericRigidityRank (SimpleGraph.completeGraph {v : V // v ∈ S}) 3 := hS
  have he := ker_eq_of_le_of_genericRigidityRank_eq le_top hrankS pS hpS
  have hker : (rigidityOperator G p).ker ≤ (rigidityOperator (G ⊔ H) p).ker := by
    intro u hu
    have huS : IsInfinitesimalMotion (G.induce (S : Set V)) pS (restrictVelocity S 3 u) := by
      rw [isInfinitesimalMotion_iff]
      intro v w hvw
      exact (isInfinitesimalMotion_iff G p u).mp hu v.val w.val hvw
    have hucomplete : IsInfinitesimalMotion
        (SimpleGraph.completeGraph {v : V // v ∈ S}) pS (restrictVelocity S 3 u) := by
      change restrictVelocity S 3 u ∈ (rigidityOperator _ pS).ker
      rw [he]
      exact huS
    change IsInfinitesimalMotion (G ⊔ H) p u
    rw [isInfinitesimalMotion_iff]
    intro v w hvw
    rcases hvw with hG | ⟨hne, _, hv, hw⟩
    · exact (isInfinitesimalMotion_iff G p u).mp hu v w hG
    · have hneS : (⟨v, hv⟩ : {v : V // v ∈ S}) ≠ ⟨w, hw⟩ := by
        intro heq
        exact hne (congrArg Subtype.val heq)
      exact (isInfinitesimalMotion_iff _ pS (restrictVelocity S 3 u)).mp hucomplete
        ⟨v, hv⟩ ⟨w, hw⟩ hneS
  have hr := rigidityRank_le_of_ker_le (G ⊔ H) G p hker
  change genericRigidityRank (G ⊔ H) 3 = genericRigidityRank G 3
  apply le_antisymm
  · exact (hp (G ⊔ H)).symm.le.trans (hr.trans (hp G).le)
  · exact genericRigidityRank_mono le_sup_left

theorem clusterCompletion_k4Covered {V I : Type} (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card) : K4Covered (clusterCompletion C) := by
  classical
  intro v w hvw
  obtain ⟨hne, i, hv, hw⟩ := hvw
  have hpair : ({v, w} : Finset V) ⊆ C i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hw
  obtain ⟨S, hsmall, hlarge, hcard⟩ :=
    Finset.exists_subsuperset_card_eq hpair (n := 4) (by simp [hne]) (hC i)
  refine ⟨S, hcard, hsmall (by simp), hsmall (by simp), ?_⟩
  intro x hx y hy hxy
  exact ⟨hxy, i, hlarge hx, hlarge hy⟩

/-- The rank of a completed family of ambient rigid clusters is bounded by
the rank of the original graph, with arbitrary overlap and family size. -/
theorem clusterCompletion_genericRigidityRank_le
    {V I : Type} [Fintype V] (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, RigidCluster G (C i)) :
    genericRigidityRank (clusterCompletion C) 3 ≤ genericRigidityRank G 3 := by
  obtain ⟨p, hp⟩ := exists_isGenericPlacement (V := V) 3
  have hker : (rigidityOperator G p).ker ≤
      (rigidityOperator (clusterCompletion C) p).ker := by
    intro u hu
    change IsInfinitesimalMotion (clusterCompletion C) p u
    rw [isInfinitesimalMotion_iff]
    intro v w hvw
    obtain ⟨hne, i, hv, hw⟩ := hvw
    let H := clusterCompletion (fun _ : Unit => C i)
    have he : (rigidityOperator (G ⊔ H) p).ker = (rigidityOperator G p).ker :=
      ker_eq_of_le_of_genericRigidityRank_eq le_sup_left (hC i).symm p hp
    have hu' : IsInfinitesimalMotion (G ⊔ H) p u := by
      change u ∈ (rigidityOperator (G ⊔ H) p).ker
      rw [he]
      exact hu
    apply (isInfinitesimalMotion_iff (G ⊔ H) p u).mp hu' v w
    exact Or.inr ⟨hne, (), hv, hw⟩
  have hr := rigidityRank_le_of_ker_le (clusterCompletion C) G p hker
  exact (hp (clusterCompletion C)).symm.le.trans (hr.trans (hp G).le)

/-- The general form of Corollary 1.2 follows from the exact principal
Theorem 1.1, with no new rigidity or genericity assumptions. -/
theorem rigidClusterCompletionRigidity_of_sixConnectedK4Rigidity
    (hmain : SixConnectedK4RigidityClaim) : RigidClusterCompletionRigidityClaim := by
  intro V I _ G C hC hconn
  have hcover := clusterCompletion_k4Covered C (fun i => (hC i).1)
  have hrigid := hmain V (clusterCompletion C) hconn hcover
  have hrank := clusterCompletion_genericRigidityRank_le G C (fun i => (hC i).2)
  have hupper : genericRigidityRank G 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph V) 3 :=
    genericRigidityRank_mono le_top
  change genericRigidityRank (clusterCompletion C) 3 =
    genericRigidityRank (SimpleGraph.completeGraph V) 3 at hrigid
  change genericRigidityRank G 3 = genericRigidityRank (SimpleGraph.completeGraph V) 3
  exact le_antisymm hupper (hrigid ▸ hrank)

/-- The edge-cover formulation of Corollary 1.2 follows from the exact
principal theorem, through the proved ambient-cluster completion result. -/
theorem rigidClusterCoveredRigidity_of_sixConnectedK4Rigidity
    (hmain : SixConnectedK4RigidityClaim) : RigidClusterCoveredRigidityClaim := by
  intro V _ G hconn hcover
  have hcover' := (rigidSubgraphCovered_iff_rigidInducedCovered G).mp hcover
  let I := {S : Finset V // 4 ≤ S.card ∧ RigidInducedSubgraph G S}
  let C : I → Finset V := Subtype.val
  have hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i) := by
    intro i
    exact ⟨i.property.1, RigidInducedSubgraph.rigidCluster G i.val i.property.2⟩
  have hle : G ≤ clusterCompletion C := by
    intro v w hvw
    obtain ⟨S, hcard, hv, hw, hrigid⟩ := hcover' v w hvw
    exact ⟨hvw.ne, ⟨S, hcard, hrigid⟩, hv, hw⟩
  exact rigidClusterCompletionRigidity_of_sixConnectedK4Rigidity hmain
    V I G C hC (hconn.mono hle)

end Papers.Rigidity

end
end BundleSource0018

section BundleSource0019
/- Source: Papers/RigidityMinimalCounterexample.lean -/




@[expose] public section

/-!
# The actual extremal graph and rigidity closure

Failure of Theorem 1.1 produces a graph of least order and, within that
order, greatest number of actual edges. The selection uses finite graphs
and the actual generic rigidity operator. Vertex connectivity gives the
degree bound directly, and edge maximality forces every ambient rigid
cluster of order at least four to induce a clique.

These are the initial reductions of Lemma 3.1. They do not assert that the
remaining minimal counterexample is impossible.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint
open scoped Classical

/-- The counterexamples being minimized are exactly the failures of the
paper's principal assertion. -/
def IsCounterexample {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  VertexConnected G 6 ∧ K4Covered G ∧ ¬ IsGenericallyRigidInR3 G

def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- All extremal properties are proved by selection. No rigidity
conclusion or local structural assertion is stored as an assumption. -/
structure MinimalCounterexample (V : Type) [Fintype V] where
  graph : SimpleGraph V
  connected : VertexConnected graph 6
  covered : K4Covered graph
  flexible : ¬ IsGenericallyRigidInR3 graph
  vertexMinimal : ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
    Fintype.card W < Fintype.card V → VertexConnected H 6 → K4Covered H →
      IsGenericallyRigidInR3 H
  edgeMaximal : ∀ H : SimpleGraph V, VertexConnected H 6 → K4Covered H →
    ¬ IsGenericallyRigidInR3 H → edgeCount H ≤ edgeCount graph

def CounterexampleOrder (n : ℕ) : Prop :=
  ∃ (V : Type) (hV : Fintype V), @Fintype.card V hV = n ∧
    ∃ G : SimpleGraph V, @IsCounterexample V hV G

/-- The lexicographic minimal-counterexample reduction is valid for all
finite vertex types, without a restriction to a fixed finite universe. -/
theorem exists_minimalCounterexample (hfalse : ¬ SixConnectedK4RigidityClaim) :
    ∃ (V : Type) (hV : Fintype V), Nonempty (@MinimalCounterexample V hV) := by
  classical
  have hex : ∃ n, CounterexampleOrder n := by
    by_contra hnone
    apply hfalse
    intro V hV G hconn hcover
    by_contra hflex
    exact hnone ⟨Fintype.card V, V, hV, rfl, G, hconn, hcover, hflex⟩
  obtain ⟨V, hV, hcard, G, hG⟩ := Nat.find_spec hex
  letI : Fintype V := hV
  let candidates : Finset (SimpleGraph V) := Finset.univ.filter IsCounterexample
  have hmem : G ∈ candidates := by simpa [candidates] using hG
  obtain ⟨Gmax, hmaxmem, hmax⟩ :=
    Finset.exists_max_image candidates edgeCount ⟨G, hmem⟩
  have hGmax : IsCounterexample Gmax := by simpa [candidates] using hmaxmem
  refine ⟨V, hV, ⟨{
    graph := Gmax
    connected := hGmax.1
    covered := hGmax.2.1
    flexible := hGmax.2.2
    vertexMinimal := ?_
    edgeMaximal := ?_ }⟩⟩
  · intro W hW H hsmall hconn hcover
    by_contra hflex
    have hwitness : CounterexampleOrder (Fintype.card W) :=
      ⟨W, hW, rfl, H, hconn, hcover, hflex⟩
    have hmin := Nat.find_min' hex hwitness
    rw [← hcard] at hmin
    exact (Nat.not_le_of_lt hsmall) hmin
  · intro H hconn hcover hflex
    apply hmax H
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hconn, hcover, hflex⟩

/-- Each edge of a union retains a covering tetrahedron from one of its
two original graphs. -/
theorem K4Covered.sup {V : Type} {G H : SimpleGraph V}
    (hG : K4Covered G) (hH : K4Covered H) : K4Covered (G ⊔ H) := by
  intro v w hvw
  rcases hvw with hvw | hvw
  · obtain ⟨S, hcard, hv, hw, hclique⟩ := hG v w hvw
    exact ⟨S, hcard, hv, hw, SimpleGraph.IsClique.mono le_sup_left hclique⟩
  · obtain ⟨S, hcard, hv, hw, hclique⟩ := hH v w hvw
    exact ⟨S, hcard, hv, hw, SimpleGraph.IsClique.mono le_sup_right hclique⟩

/-- The stated vertex-connectivity condition implies the full minimum
degree bound, including the cardinality condition on the vertex set. -/
theorem VertexConnected.degree_ge {V : Type} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hconn : VertexConnected G k) (v : V) :
    k ≤ G.degree v := by
  classical
  by_contra hk
  have hdegree : G.degree v < k := Nat.lt_of_not_ge hk
  have horder := hconn.1
  let S := G.neighborFinset v
  have hv : v ∉ S := G.notMem_neighborFinset_self v
  have hS : S.card < k := hdegree
  have hsize : (insert v S).card < Fintype.card V := by
    rw [Finset.card_insert_of_notMem hv]
    change G.degree v + 1 < Fintype.card V
    omega
  have hex : ∃ w : V, w ∉ insert v S := by
    by_contra h
    have hsub : (Finset.univ : Finset V) ⊆ insert v S := by
      intro w hw
      by_contra hw'
      exact h ⟨w, hw'⟩
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ] at hcard
    omega
  obtain ⟨w, hw⟩ := hex
  have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
  let v' : {x : V // x ∉ S} := ⟨v, hv⟩
  let w' : {x : V // x ∉ S} := ⟨w, hwS⟩
  have hne : v' ≠ w' := by
    intro h
    exact hw (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val h).symm))
  have hisolated : (G.induce ((S : Set V)ᶜ)).neighborSet v' = ∅ := by
    ext z
    change G.Adj v z.1 ↔ False
    exact ⟨fun hz => z.2 ((G.mem_neighborFinset v z.1).mpr hz), False.elim⟩
  exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hne hisolated)
    (hconn.2 S hS v' w')

/-- The order-seven boundary case is the complete graph, so every
counterexample has enough vertices for the one-vertex deletion arguments. -/
theorem MinimalCounterexample.eight_le_card
    {V : Type} [Fintype V] (C : MinimalCounterexample V) :
    8 ≤ Fintype.card V := by
  classical
  have horder := C.connected.1
  by_contra hsmall
  have hseven : Fintype.card V = 7 := by omega
  have htop : C.graph = ⊤ := by
    apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    intro v
    apply (C.graph.degree_eq_card_sub_one v).mp
    have hlower := C.connected.degree_ge v
    have hupper := C.graph.degree_lt_card_verts v
    omega
  apply C.flexible
  rw [htop]
  simpa only [SimpleGraph.completeGraph_eq_top] using
    completeGraph_isGenericallyRigidInR3 V

/-- Edge maximality completes every ambient rigidity cluster. This
retains the full ambient meaning of closure: a cluster need not be rigid
using only its induced edges. -/
theorem MinimalCounterexample.rigidCluster_isClique
    {V : Type} [Fintype V] (C : MinimalCounterexample V)
    (S : Finset V) (hcard : 4 ≤ S.card) (hcluster : RigidCluster C.graph S) :
    C.graph.IsClique (S : Set V) := by
  classical
  let H := C.graph ⊔ clusterCompletion (fun _ : Unit => S)
  have hconn : VertexConnected H 6 := C.connected.mono le_sup_left
  have hcover : K4Covered H := C.covered.sup
    (clusterCompletion_k4Covered (fun _ : Unit => S) (fun _ => hcard))
  have hrank : genericRigidityRank H 3 = genericRigidityRank C.graph 3 := hcluster
  have hflex : ¬ IsGenericallyRigidInR3 H := by
    intro h
    apply C.flexible
    change genericRigidityRank C.graph 3 =
      genericRigidityRank (SimpleGraph.completeGraph V) 3
    exact hrank.symm.trans h
  have hcount : H.edgeFinset.card ≤ C.graph.edgeFinset.card := by
    simpa only [edgeCount, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      using C.edgeMaximal H hconn hcover hflex
  have hsub : C.graph.edgeFinset ⊆ H.edgeFinset :=
    SimpleGraph.edgeFinset_mono le_sup_left
  have heq : C.graph = H := SimpleGraph.edgeFinset_inj.mp
    (Finset.eq_of_subset_of_card_le hsub hcount)
  intro v hv w hw hvw
  have h : H.Adj v w := Or.inr ⟨hvw, (), hv, hw⟩
  rwa [← heq] at h

end

end Papers.Rigidity

end
end BundleSource0019

section BundleSource0020
/- Source: Papers/RigidityDeletionLowerBound.lean -/







@[expose] public section

/-!
# The deletion bound from actual common-pin ranks

If deleting a vertex of a K4-covered graph loses at most four generic
bar-rank dimensions, its closed neighborhood is an ambient rigid cluster.
The proof constructs a regular, geometrically nondegenerate real placement,
uses the exact graph-kernel elimination theorem, varies only the deleted
vertex, and invokes the proved common-pin low-rank lemma.

For the edge-maximal minimal counterexample, a nonsimplicial vertex
therefore has deletion rank loss at least five.  No theorem from the
cited external three-dimensional rigidity literature is assumed here.
-/

namespace Papers.Rigidity.VertexPin

noncomputable section

open BarJoint
open scoped Classical

variable {V : Type} [Fintype V]

def deletionRankDrop (G : SimpleGraph V) (v : V) : ℕ :=
  genericRigidityRank G 3 - genericRigidityRank (deletedGraph G v) 3

def closedNeighborhood (G : SimpleGraph V) (v : V) : Finset V :=
  insert v (G.neighborFinset v)

@[simp] theorem mem_closedNeighborhood (G : SimpleGraph V) (v w : V) :
    w ∈ closedNeighborhood G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighborhood]

/-- Generic rank on the whole vertex set remains generic after deleting
one vertex.  The subtype relabelling is explicit. -/
theorem generic_deletedPlacement (p : Placement V 3) (hp : IsGenericPlacement p) (v : V) :
    IsGenericPlacement (deletedPlacement p v) := by
  let S : Finset V := Finset.univ.erase v
  let e : DeletedVertex v ≃ {w : V // w ∈ S} :=
    { toFun := fun w => ⟨w.1, by simp [S, w.2]⟩
      invFun := fun w => ⟨w.1, (Finset.mem_erase.mp w.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpS := isGenericPlacement_restrict p hp S
  intro H
  have h := hpS (H.comap e.symm)
  change rigidityRank (H.comap e.symm) ((deletedPlacement p v) ∘ e.symm) =
    genericRigidityRank (H.comap e.symm) 3 at h
  rwa [rigidityRank_relabel, genericRigidityRank_relabel] at h

/-- Low deletion rank forces the entire closed neighborhood into the
actual ambient rigidity closure. -/
theorem closedNeighborhood_rigidCluster_of_drop_le_four
    (G : SimpleGraph V) (v : V) (hG : K4Covered G)
    (hneigh : ∃ w, G.Adj v w) (hdrop : deletionRankDrop G v ≤ 4) :
    RigidCluster G (closedNeighborhood G v) := by
  obtain ⟨p, hpGeneric, hpGeom⟩ :=
    GeneralPosition.exists_generic_generalPosition (V := V)
  let T := tetrahedraOfK4Covered G v hG
  obtain ⟨w, hw⟩ := hneigh
  let base : IncidentK4 G v :=
    Classical.choice (incidentK4_nonempty_of_neighbor G v hG w hw)
  have hp : T.NoncollinearAt p :=
    GeneralPosition.InGeneralPosition.incident_noncollinear p hpGeom T
  have ht : T.TransverseAt p :=
    GeneralPosition.InGeneralPosition.incident_transverse p hpGeom T
  have hpDeleted := generic_deletedPlacement p hpGeneric v
  obtain ⟨O, hO, hpO, hwindow⟩ := T.exists_open_generic_pin_window p hpGeneric ht
  have hrank (q : Vec3) (hq : q ∈ O) :
      Module.finrank ℝ (T.commonPinAt p hp base q).range ≤ 1 := by
    have hid := T.rigidityRank_replace_identity p hp q (hwindow q hq).2 base
    have hrG := (hwindow q hq).1 G
    have hrD := hpDeleted (deletedGraph G v)
    change rigidityRank G (replacePlacement p v q) = genericRigidityRank G 3 at hrG
    change rigidityRank (deletedGraph G v) (deletedPlacement p v) =
      genericRigidityRank (deletedGraph G v) 3 at hrD
    rw [hrG, hrD] at hid
    unfold deletionRankDrop at hdrop
    omega
  obtain ⟨q, hqO, hdetect⟩ := CommonPinLowRank.exists_pin_detecting_all_relative_twists
    (T.relativeTwists p hp base) O hO ⟨p v, hpO⟩ hrank
  let p' := replacePlacement p v q
  have hp' : T.NoncollinearAt p' := T.noncollinear_replace p hp q
  have ht' : T.TransverseAt p' := (hwindow q hqO).2
  have hgen' : IsGenericPlacement p' := (hwindow q hqO).1
  have hrepresentation (u : (rigidityOperator G p').ker) :
      ∃ X : Twist, ∀ w ∈ closedNeighborhood G v, u.1 w = evaluateTwist (p' w) X := by
    let u' := T.restrictFullMotion p' u
    let u₀ := deletedMotionEquivReplace G p v q u'
    have hpin' : T.commonPinOperator p' hp' base u' = 0 :=
      LinearMap.mem_ker.mp (T.restrictFullMotion_mem_commonPin_ker p' hp' ht' base u)
    have hpin : T.commonPinAt p hp base q u₀ = 0 := by
      rw [T.commonPinOperator_replace p hp q base] at hpin'
      exact hpin'
    have hequal (b : IncidentK4 G v) : T.bodyTwist p hp b u₀ = T.bodyTwist p hp base u₀ := by
      have h := hdetect u₀ hpin b
      change T.bodyTwist p hp b u₀ - T.bodyTwist p hp base u₀ = 0 at h
      exact sub_eq_zero.mp h
    let X := T.bodyTwist p hp base u₀
    have hbody (b : IncidentK4 G v) : T.bodyTwist p' hp' b u' = X := by
      rw [T.bodyTwist_replace p hp q b u']
      exact hequal b
    refine ⟨X, ?_⟩
    intro z hz
    rcases (mem_closedNeighborhood G v z).mp hz with rfl | hz
    · rw [T.fullMotion_at_vertex p' hp' ht' u base, hbody]
    · obtain ⟨b, i, rfl⟩ := T.covers z hz
      have hfit := T.bodyTwist_fit p' hp' b u' i
      rw [hbody] at hfit
      exact hfit.symm
  let H := clusterCompletion (fun _ : Unit => closedNeighborhood G v)
  have hker : (rigidityOperator G p').ker ≤ (rigidityOperator (G ⊔ H) p').ker := by
    intro u hu
    obtain ⟨X, hX⟩ := hrepresentation ⟨u, hu⟩
    change ∀ w ∈ closedNeighborhood G v, u w = evaluateTwist (p' w) X at hX
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b hab
    rcases hab with hab | ⟨_, _, ha, hb⟩
    · exact (isInfinitesimalMotion_iff G p' u).mp hu a b hab
    · change ∑ i : Fin 3, (p' a i - p' b i) * (u a i - u b i) = 0
      rw [hX a ha, hX b hb]
      exact twist_preserves_bar X _ _
  have hr := rigidityRank_le_of_ker_le (G ⊔ H) G p' hker
  change genericRigidityRank (G ⊔ H) 3 = genericRigidityRank G 3
  apply le_antisymm
  · exact (hgen' (G ⊔ H)).symm.le.trans (hr.trans (hgen' G).le)
  · exact genericRigidityRank_mono le_sup_left

/-- The actual closed neighborhood has the expected cardinality. -/
theorem card_closedNeighborhood (G : SimpleGraph V) (v : V) :
    (closedNeighborhood G v).card = G.degree v + 1 := by
  rw [closedNeighborhood, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
  exact congrArg (· + 1) (G.card_neighborFinset_eq_degree v)

/-- In the selected edge-maximal counterexample, the only remaining
input for `δ(v) ≥ 5` is nonsimpliciality, proved by vertex elimination. -/
theorem MinimalCounterexample.five_le_deletionRankDrop_of_nonsimplicial
    (C : MinimalCounterexample V) (v : V)
    (hns : ¬ C.graph.IsClique (C.graph.neighborSet v)) :
    5 ≤ deletionRankDrop C.graph v := by
  by_contra hsmall
  have hdegree := C.connected.degree_ge v
  have hpos : 0 < (C.graph.neighborFinset v).card := by
    rw [C.graph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hneigh : ∃ w, C.graph.Adj v w := ⟨w, (C.graph.mem_neighborFinset v w).mp hw⟩
  have hcluster := closedNeighborhood_rigidCluster_of_drop_le_four C.graph v C.covered
    hneigh (by omega)
  have hcard : 4 ≤ (closedNeighborhood C.graph v).card := by
    rw [card_closedNeighborhood]
    omega
  have hclique := C.rigidCluster_isClique (closedNeighborhood C.graph v) hcard hcluster
  apply hns
  intro a ha b hb hab
  exact hclique ((mem_closedNeighborhood C.graph v a).mpr (Or.inr ha))
    ((mem_closedNeighborhood C.graph v b).mpr (Or.inr hb)) hab

end

end Papers.Rigidity.VertexPin

end
end BundleSource0020

section BundleSource0021
/- Source: Papers/RigidityElimination.lean -/



@[expose] public section

/-!
# Deleting a vertex and completing its neighbors

The graph `G-v+K(N(v))` is constructed literally. Connectivity is proved
by mapping walks after replacing the deleted vertex by a surviving
neighbor. Tetrahedral edge covers are transported or replaced inside the
completed neighborhood. Minimality then proves the actual generic
rigidity of this graph in a minimal counterexample.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint
open scoped Classical

abbrev DeletedVertex {V : Type} (v : V) := {w : V // w ≠ v}

def deletedNeighbors {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    Finset (DeletedVertex v) :=
  (G.neighborFinset v).subtype (· ≠ v)

@[simp] theorem mem_deletedNeighbors {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) (w : DeletedVertex v) :
    w ∈ deletedNeighbors G v ↔ G.Adj v w.1 := by
  simp [deletedNeighbors]

@[simp] theorem card_deletedNeighbors {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) : (deletedNeighbors G v).card = G.degree v := by
  rw [deletedNeighbors, Finset.card_subtype]
  have hfilter : (G.neighborFinset v).filter (· ≠ v) = G.neighborFinset v := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact ((G.mem_neighborFinset v w).mp hw).ne.symm
  rw [hfilter, G.card_neighborFinset_eq_degree]

/-- The actual neighborhood completion on the remaining vertex set. -/
def neighborCompletion {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    SimpleGraph (DeletedVertex v) :=
  G.induce {w | w ≠ v} ⊔ clusterCompletion (fun _ : Unit => deletedNeighbors G v)

@[simp] theorem neighborCompletion_adj {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) (x y : DeletedVertex v) :
    (neighborCompletion G v).Adj x y ↔
      G.Adj x.1 y.1 ∨ (x ≠ y ∧ G.Adj v x.1 ∧ G.Adj v y.1) := by
  simp [neighborCompletion, clusterCompletion]

/-- A map taking every edge to a walk also takes every walk to a walk;
contracted edges are allowed to map to a length-zero walk. -/
theorem reachable_map_of_edgeReachable
    {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
    (hf : ∀ {u v}, G.Adj u v → H.Reachable (f u) (f v))
    {u v : V} (h : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons hadj p ih => exact (hf hadj).trans ih

/-- Filling the neighborhood preserves vertex connectivity when the
remaining order satisfies its required strict size condition. -/
theorem VertexConnected.neighborCompletion
    {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hconn : VertexConnected G k) (hcard : k + 2 ≤ Fintype.card V) (v : V) :
    VertexConnected (Papers.Rigidity.neighborCompletion G v) k := by
  classical
  have hdeletedCard : Fintype.card (DeletedVertex v) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun w : V => w = v)]
    simp
  refine ⟨by rw [hdeletedCard]; omega, ?_⟩
  intro S hS
  let T : Finset V := S.image Subtype.val
  have hTcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hTmem (x : DeletedVertex v) : x.1 ∈ T ↔ x ∈ S := by
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      have hyx : y = x := Subtype.ext heq
      simpa [hyx] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hvT : v ∉ T := by
    intro hv
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hv
    exact x.2 hxeq
  have hTlt : T.card < k := by rwa [hTcard]
  have hremaining := hconn.2 T hTlt
  have hnotSubset : ¬ G.neighborFinset v ⊆ T := by
    intro hsub
    have hcount := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree] at hcount
    have hdegree := hconn.degree_ge v
    omega
  obtain ⟨z, hzNeighbor, hzT⟩ := Finset.not_subset.mp hnotSubset
  have hzAdj : G.Adj v z := (G.mem_neighborFinset v z).mp hzNeighbor
  let z₀ : DeletedVertex v := ⟨z, hzAdj.ne.symm⟩
  let z' : {x : DeletedVertex v // x ∉ S} :=
    ⟨z₀, fun hzS => hzT ((hTmem z₀).mpr hzS)⟩
  let f : {x : V // x ∉ T} → {x : DeletedVertex v // x ∉ S} := fun x =>
    if hx : x.1 = v then z' else
      ⟨⟨x.1, hx⟩, fun hxS => x.2 ((hTmem ⟨x.1, hx⟩).mpr hxS)⟩
  have hfromDeleted (x y : {w : V // w ∉ T})
      (hx : x.1 = v) (hy : y.1 ≠ v)
      (hxy : (G.induce ((T : Set V)ᶜ)).Adj x y) :
      ((Papers.Rigidity.neighborCompletion G v).induce ((S : Set (DeletedVertex v))ᶜ)).Reachable
        (f x) (f y) := by
    simp only [f, dif_pos hx, dif_neg hy]
    by_cases hzy : z = y.1
    · have heq : z' =
          (⟨⟨y.1, hy⟩, fun hyS => y.2 ((hTmem ⟨y.1, hy⟩).mpr hyS)⟩ :
            {x : DeletedVertex v // x ∉ S}) :=
        Subtype.ext (Subtype.ext hzy)
      rw [heq]
    · apply SimpleGraph.Adj.reachable
      change (Papers.Rigidity.neighborCompletion G v).Adj z₀ ⟨y.1, hy⟩
      apply (neighborCompletion_adj G v _ _).mpr
      refine Or.inr ⟨?_, hzAdj, ?_⟩
      · intro heq
        exact hzy (congrArg Subtype.val heq)
      · simpa [hx] using hxy
  have hmap : ∀ {x y}, (G.induce ((T : Set V)ᶜ)).Adj x y →
      ((Papers.Rigidity.neighborCompletion G v).induce ((S : Set (DeletedVertex v))ᶜ)).Reachable
        (f x) (f y) := by
    intro x y hxy
    by_cases hx : x.1 = v
    · by_cases hy : y.1 = v
      · have hloop : G.Adj v v := by simpa [hx, hy] using hxy
        exact False.elim (G.loopless.irrefl v hloop)
      · exact hfromDeleted x y hx hy hxy
    · by_cases hy : y.1 = v
      · exact (hfromDeleted y x hy hx hxy.symm).symm
      · simp only [f, dif_neg hx, dif_neg hy]
        apply SimpleGraph.Adj.reachable
        exact Or.inl hxy
  refine { preconnected := ?_, nonempty := ⟨z'⟩ }
  intro a b
  let a₀ : {x : V // x ∉ T} := ⟨a.1.1, fun haT => a.2 ((hTmem a.1).mp haT)⟩
  let b₀ : {x : V // x ∉ T} := ⟨b.1.1, fun hbT => b.2 ((hTmem b.1).mp hbT)⟩
  have h := reachable_map_of_edgeReachable f hmap (hremaining a₀ b₀)
  simpa [f, a₀, b₀, a.1.2, b.1.2] using h

/-- A tetrahedron using the removed vertex is replaced by a tetrahedron
inside its completed neighborhood. Every original edge is retained. -/
theorem K4Covered.neighborCompletion {V : Type} [Fintype V]
    {G : SimpleGraph V} (hcover : K4Covered G) (v : V) (hdegree : 4 ≤ G.degree v) :
    K4Covered (Papers.Rigidity.neighborCompletion G v) := by
  classical
  let N := deletedNeighbors G v
  let K := clusterCompletion (fun _ : Unit => N)
  have hK : K4Covered K := clusterCompletion_k4Covered _ (by
    intro i
    simpa [N] using hdegree)
  have hfromK {x y : DeletedVertex v} (hxy : K.Adj x y) :
      ∃ A : Finset (DeletedVertex v), A.card = 4 ∧ x ∈ A ∧ y ∈ A ∧
        (Papers.Rigidity.neighborCompletion G v).IsClique (A : Set (DeletedVertex v)) := by
    obtain ⟨A, hcard, hx, hy, hclique⟩ := hK x y hxy
    exact ⟨A, hcard, hx, hy, SimpleGraph.IsClique.mono le_sup_right hclique⟩
  intro x y hxy
  rcases hxy with hold | hnew
  · obtain ⟨A, hAcard, hxA, hyA, hAclique⟩ := hcover x.1 y.1 hold
    by_cases hvA : v ∈ A
    · apply hfromK
      refine ⟨?_, (), ?_, ?_⟩
      · exact hold.ne
      · apply (mem_deletedNeighbors G v x).mpr
        exact hAclique hvA hxA x.2.symm
      · apply (mem_deletedNeighbors G v y).mpr
        exact hAclique hvA hyA y.2.symm
    · let A' := A.subtype (· ≠ v)
      have hcard : A'.card = 4 := by
        rw [Finset.card_subtype]
        have hfilter : A.filter (· ≠ v) = A := by
          apply Finset.filter_eq_self.mpr
          intro w hw hweq
          exact hvA (hweq ▸ hw)
        rw [hfilter, hAcard]
      refine ⟨A', hcard, Finset.mem_subtype.mpr hxA,
        Finset.mem_subtype.mpr hyA, ?_⟩
      intro a ha b hb hab
      refine Or.inl (hAclique (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb) ?_)
      exact fun heq => hab (Subtype.ext heq)
  · exact hfromK hnew

/-- The graph denoted `H_v` in Lemma 3.1 is generically rigid, by genuine
vertex minimality after both combinatorial hypotheses have been proved. -/
theorem MinimalCounterexample.neighborCompletion_isGenericallyRigid
    {V : Type} [Fintype V] (C : MinimalCounterexample V) (v : V) :
    IsGenericallyRigidInR3 (Papers.Rigidity.neighborCompletion C.graph v) := by
  have hcard := C.eight_le_card
  have hdegree := C.connected.degree_ge v
  have hsmall : Fintype.card (DeletedVertex v) < Fintype.card V := by
    rw [Fintype.card_subtype_compl (fun w : V => w = v)]
    simp only [Fintype.card_unique, Fintype.card_subtype_eq]
    omega
  exact C.vertexMinimal (DeletedVertex v) (Papers.Rigidity.neighborCompletion C.graph v) hsmall
    (C.connected.neighborCompletion (by omega) v)
    (C.covered.neighborCompletion v (by omega))

end

end Papers.Rigidity

end
end BundleSource0021

section BundleSource0022
/- Source: Papers/RigidityZeroExtension.lean -/




@[expose] public section

/-!
# Three-bar vertex extension and the unconditional deletion bound

The ordinary three-dimensional vertex-extension theorem is proved from
the actual complete-graph motion kernel and the triangle twist theorem.
It excludes simplicial vertices in the minimal counterexample.  The
previous low-rank neighborhood-closure argument then establishes
`δ(v) ≥ 5` with no remaining local structural hypothesis.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V : Type} [Fintype V]

/-- A motion preserving every bar of a general-position complete graph
is an actual Euclidean twist, as soon as a triangle is present. -/
theorem exists_twist_of_completeMotion (p u : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (f : Fin 3 ↪ V)
    (hu : IsInfinitesimalMotion (SimpleGraph.completeGraph V) p u) :
    ∃ X : Twist, ∀ w, u w = evaluateTwist (p w) X := by
  have hbars := (isInfinitesimalMotion_iff (SimpleGraph.completeGraph V) p u).mp hu
  have htriangle : ∀ i j : Fin 3, i ≠ j →
      edgeConstraint (p ∘ f) (u ∘ f) i j = 0 := by
    intro i j hij
    exact hbars (f i) (f j) (f.injective.ne hij)
  obtain ⟨X, hX, _⟩ := exists_unique_twist_of_triangleMotion
    (p ∘ f) (u ∘ f) (GeneralPosition.InGeneralPosition.triangle p hp f) htriangle
  refine ⟨X, ?_⟩
  intro w
  by_cases hw : w ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hw
    exact hX i
  let f' : Fin 3 ↪ {z : V // z ≠ w} :=
    { toFun := fun i => ⟨f i, fun h => hw ⟨i, h⟩⟩
      inj' := fun _ _ h => f.injective (congrArg Subtype.val h) }
  apply VertexPin.IncidentTetrahedra.velocity_eq_of_three_bars
    (p ∘ f) (p w) (u w) X (GeneralPosition.InGeneralPosition.star p hp w f')
  intro i
  rw [← hX i]
  exact hbars w (f i) (fun h => hw ⟨i, h.symm⟩)

namespace VertexPin

private def neighborTriple (G : SimpleGraph V) (v : V) (hdegree : 3 ≤ G.degree v) :
    Fin 3 ↪ DeletedVertex v := by
  let e : (G.neighborFinset v) ≃ Fin (G.degree v) :=
    Finset.equivFinOfCardEq (G.card_neighborFinset_eq_degree v)
  let g : Fin 3 ↪ (G.neighborFinset v) := (Fin.castLEEmb hdegree).trans e.symm.toEmbedding
  exact
    { toFun := fun i => ⟨(g i).1, ((G.mem_neighborFinset v (g i).1).mp (g i).2).ne.symm⟩
      inj' := fun _ _ h => g.injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h)) }

private theorem neighborTriple_adj (G : SimpleGraph V) (v : V)
    (hdegree : 3 ≤ G.degree v) (i : Fin 3) :
    G.Adj v (neighborTriple G v hdegree i).1 := by
  exact (G.mem_neighborFinset v _).mp
    (((Fin.castLEEmb hdegree).trans
      (Finset.equivFinOfCardEq (G.card_neighborFinset_eq_degree v)).symm.toEmbedding i).2)

/-- A generically rigid deleted graph and three actual incident bars
give generic rigidity after inserting the vertex. -/
theorem isGenericallyRigid_of_deleted (G : SimpleGraph V) (v : V)
    (hdegree : 3 ≤ G.degree v)
    (hdeleted : IsGenericallyRigidInR3 (deletedGraph G v)) :
    IsGenericallyRigidInR3 G := by
  obtain ⟨p, hpGeneric, hpGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  let f := neighborTriple G v hdegree
  have hpDeleted := generic_deletedPlacement p hpGeneric v
  have hpGeomDeleted : GeneralPosition.InGeneralPosition (deletedPlacement p v) :=
    GeneralPosition.InGeneralPosition.comp_embedding p hpGeom
      (⟨Subtype.val, Subtype.val_injective⟩ : DeletedVertex v ↪ V)
  have hclosed : (rigidityOperator (SimpleGraph.completeGraph (DeletedVertex v))
      (deletedPlacement p v)).ker =
      (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).ker :=
    ker_eq_of_le_of_genericRigidityRank_eq le_top hdeleted
      (deletedPlacement p v) hpDeleted
  have hker : (rigidityOperator G p).ker ≤
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
    intro u hu
    let uold : Velocity (DeletedVertex v) 3 := fun w => u w.1
    have huold : IsInfinitesimalMotion (deletedGraph G v) (deletedPlacement p v) uold := by
      rw [isInfinitesimalMotion_iff]
      intro a b hab
      exact (isInfinitesimalMotion_iff G p u).mp hu a.1 b.1 hab
    have hucomplete : IsInfinitesimalMotion (SimpleGraph.completeGraph (DeletedVertex v))
        (deletedPlacement p v) uold := by
      change uold ∈ (rigidityOperator _ _).ker
      rw [hclosed]
      exact huold
    obtain ⟨X, hX⟩ := exists_twist_of_completeMotion
      (deletedPlacement p v) uold hpGeomDeleted f hucomplete
    change ∀ w : DeletedVertex v, u w.val = evaluateTwist (p w.val) X at hX
    have huv : u v = evaluateTwist (p v) X := by
      apply IncidentTetrahedra.velocity_eq_of_three_bars
        (fun i => p (f i).1) (p v) (u v) X
        (GeneralPosition.InGeneralPosition.star p hpGeom v f)
      intro i
      rw [← hX (f i)]
      exact (isInfinitesimalMotion_iff G p u).mp hu v (f i).1
        (neighborTriple_adj G v hdegree i)
    have hfull (w : V) : u w = evaluateTwist (p w) X := by
      by_cases hw : w = v
      · simpa [hw] using huv
      · exact hX ⟨w, hw⟩
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b _
    change ∑ i : Fin 3, (p a i - p b i) * (u a i - u b i) = 0
    rw [hfull a, hfull b]
    exact twist_preserves_bar X _ _
  have hr := rigidityRank_le_of_ker_le (SimpleGraph.completeGraph V) G p hker
  change genericRigidityRank G 3 = genericRigidityRank (SimpleGraph.completeGraph V) 3
  apply le_antisymm (genericRigidityRank_mono le_top)
  exact (hpGeneric (SimpleGraph.completeGraph V)).symm.le.trans (hr.trans (hpGeneric G).le)

end VertexPin

/-- A simplicial neighborhood makes the literal neighbor completion
equal to the deleted graph. -/
theorem neighborCompletion_eq_deleted_of_simplicial (G : SimpleGraph V) (v : V)
    (hclique : G.IsClique (G.neighborSet v)) :
    neighborCompletion G v = VertexPin.deletedGraph G v := by
  apply le_antisymm
  · intro x y hxy
    rcases (neighborCompletion_adj G v x y).mp hxy with hold | ⟨hne, hx, hy⟩
    · exact hold
    · exact hclique hx hy (fun h => hne (Subtype.ext h))
  · intro x y hxy
    exact Or.inl hxy

/-- The simplicial-vertex reduction of Lemma 3.1, including the actual
three-bar extension argument. -/
theorem MinimalCounterexample.not_simplicial (C : MinimalCounterexample V) (v : V) :
    ¬ C.graph.IsClique (C.graph.neighborSet v) := by
  intro hclique
  have hdeleted := C.neighborCompletion_isGenericallyRigid v
  rw [neighborCompletion_eq_deleted_of_simplicial C.graph v hclique] at hdeleted
  apply C.flexible
  exact VertexPin.isGenericallyRigid_of_deleted C.graph v
    (by have h := C.connected.degree_ge v; omega) hdeleted

/-- The full deletion-rank bound in Lemma 3.1, with all its local
structural prerequisites proved from the selected counterexample. -/
theorem MinimalCounterexample.five_le_deletionRankDrop
    (C : MinimalCounterexample V) (v : V) :
    5 ≤ VertexPin.deletionRankDrop C.graph v :=
  VertexPin.MinimalCounterexample.five_le_deletionRankDrop_of_nonsimplicial C v
    (C.not_simplicial v)

end

end Papers.Rigidity

end
end BundleSource0022

section BundleSource0023
/- Source: Papers/RigidityCompleteRank.lean -/




@[expose] public section

/-!
# Complete-graph rank and the actual common-motion subspace

The six-dimensional trivial-motion term is derived from Euclidean twists
and actual bar kernels.  This identifies the paper's flexibility count
with the ordinary generic rigidity rank for all relevant graph orders.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint
open scoped Classical

variable {V : Type} [Fintype V]

def globalTwistOperator (p : Placement V 3) : Twist →ₗ[ℝ] Velocity V 3 :=
  LinearMap.pi fun v => evaluateTwist (p v)

@[simp] theorem globalTwistOperator_apply (p : Placement V 3) (X : Twist) (v : V) :
    globalTwistOperator p X v = evaluateTwist (p v) X := rfl

theorem globalTwist_isMotion (G : SimpleGraph V) (p : Placement V 3) (X : Twist) :
    IsInfinitesimalMotion G p (globalTwistOperator p X) := by
  rw [isInfinitesimalMotion_iff]
  intro a b _
  exact twist_preserves_bar X (p a) (p b)

def globalTwistMotion (G : SimpleGraph V) (p : Placement V 3) :
    Twist →ₗ[ℝ] (rigidityOperator G p).ker :=
  (globalTwistOperator p).codRestrict _ (globalTwist_isMotion G p)

theorem globalTwistOperator_injective (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (hcard : 3 ≤ Fintype.card V) :
    Function.Injective (globalTwistOperator p) := by
  obtain ⟨f : Fin 3 ↪ V⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := V) (by simpa using hcard)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro X hX
    apply twist_eq_zero_of_fixing_triangle (p ∘ f)
      (GeneralPosition.InGeneralPosition.triangle p hp f) X
    intro i
    exact congrFun (LinearMap.mem_ker.mp hX) (f i)
  · exact bot_le

theorem globalTwistMotion_injective (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (hcard : 3 ≤ Fintype.card V) :
    Function.Injective (globalTwistMotion G p) := by
  intro X Y h
  exact globalTwistOperator_injective p hp hcard (congrArg Subtype.val h)

def completeMotionEquiv (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (hcard : 3 ≤ Fintype.card V) :
    Twist ≃ₗ[ℝ] (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  apply LinearEquiv.ofBijective (globalTwistMotion (SimpleGraph.completeGraph V) p)
  refine ⟨globalTwistMotion_injective _ p hp hcard, ?_⟩
  intro u
  obtain ⟨f : Fin 3 ↪ V⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := V) (by simpa using hcard)
  obtain ⟨X, hX⟩ := exists_twist_of_completeMotion p u.val hp f u.property
  exact ⟨X, Subtype.ext (funext fun v => (hX v).symm)⟩

theorem completeMotion_finrank (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (hcard : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (rigidityOperator (SimpleGraph.completeGraph V) p).ker = 6 := by
  rw [← (completeMotionEquiv p hp hcard).finrank_eq, finrank_twist]

/-- The usual complete-graph generic rank follows from the actual
six-dimensional Euclidean motion kernel. -/
theorem genericCompleteRank_add_six (hcard : 3 ≤ Fintype.card V) :
    genericRigidityRank (SimpleGraph.completeGraph V) 3 + 6 = 3 * Fintype.card V := by
  obtain ⟨p, hpGeneric, hpGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  have h := (rigidityOperator (SimpleGraph.completeGraph V) p).finrank_range_add_finrank_ker
  rw [completeMotion_finrank p hpGeom hcard] at h
  change rigidityRank (SimpleGraph.completeGraph V) p + 6 = _ at h
  rw [hpGeneric] at h
  simpa [Velocity, Point, Module.finrank_pi_fintype, Nat.mul_comm] using h

theorem genericCompleteRank_eq (hcard : 3 ≤ Fintype.card V) :
    genericRigidityRank (SimpleGraph.completeGraph V) 3 = 3 * Fintype.card V - 6 := by
  have h := genericCompleteRank_add_six (V := V) hcard
  omega

def MinimalCounterexample.flexibility (C : MinimalCounterexample V) : ℕ :=
  3 * Fintype.card V - 6 - genericRigidityRank C.graph 3

theorem MinimalCounterexample.flexibility_pos (C : MinimalCounterexample V) :
    0 < C.flexibility := by
  have hc := C.eight_le_card
  have hr := genericCompleteRank_add_six (V := V) (by omega)
  have hle : genericRigidityRank C.graph 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph V) 3 := genericRigidityRank_mono le_top
  have hne : genericRigidityRank C.graph 3 ≠
      genericRigidityRank (SimpleGraph.completeGraph V) 3 := C.flexible
  unfold flexibility
  omega

theorem MinimalCounterexample.rank_add_flexibility (C : MinimalCounterexample V) :
    genericRigidityRank C.graph 3 + C.flexibility + 6 = 3 * Fintype.card V := by
  have hc := C.eight_le_card
  have hr := genericCompleteRank_add_six (V := V) (by omega)
  have hle : genericRigidityRank C.graph 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph V) 3 := genericRigidityRank_mono le_top
  unfold flexibility
  omega

end

end Papers.Rigidity

end
end BundleSource0023

section BundleSource0024
/- Source: Papers/RigidityConingLaman.lean -/






@[expose] public section

/-!
# Planar rigidity supplies actual spatial rigidity of the cone

The Laman library's Euclidean framework and this project's coordinate
operator are related by the proved kernel equivalence. Coning then uses
the literal motion equivalence at a height-one realization. This is the
required forward coning theorem in the overlap argument, with no assumed
matroid identification or projective-rank assertion.

The coning equivalence connects planar independence to spatial rigidity.
-/

namespace Papers.Rigidity.Coning

noncomputable section

open BarJoint

variable {V : Type} [Fintype V]

/-- A planar infinitesimally rigid witness produces a spatial cone whose
actual generic rank agrees with its complete graph, for all relevant orders. -/
theorem isGenericallyRigidInR3_of_planar
    (G : SimpleGraph V) (hcard : 2 ≤ Fintype.card V)
    (hG : G.IsGenericallyRigid 2) : IsGenericallyRigidInR3 (cone G) := by
  obtain ⟨q, hq⟩ := hG
  change Module.finrank ℝ (G.RigidityMap q).ker ≤ 3 at hq
  let p : Placement V 2 := (LamanInterop.frameworkEquiv V 2).symm q
  have he : LamanInterop.frameworkEquiv V 2 p = q :=
    (LamanInterop.frameworkEquiv V 2).apply_symm_apply q
  have hp : Module.finrank ℝ (rigidityOperator G p).ker ≤ 3 := by
    rw [LamanInterop.finrank_ker_eq, he]
    exact hq
  have hcone : Module.finrank ℝ (rigidityOperator (cone G) (placement p)).ker ≤ 6 := by
    rw [finrank_motion]
    omega
  have htotal := (rigidityOperator (cone G) (placement p)).finrank_range_add_finrank_ker
  rw [finrank_velocity] at htotal
  change rigidityRank (cone G) (placement p) + _ = _ at htotal
  have hcardCone : 3 ≤ Fintype.card (Option V) := by
    simpa only [Fintype.card_option] using Nat.add_le_add_right hcard 1
  have hcomplete := genericCompleteRank_add_six (V := Option V) hcardCone
  have hlower := rigidityRank_le_genericRigidityRank (cone G) 3 (placement p)
  have hupper : genericRigidityRank (cone G) 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph (Option V)) 3 :=
    genericRigidityRank_mono le_top
  change genericRigidityRank (cone G) 3 =
    genericRigidityRank (SimpleGraph.completeGraph (Option V)) 3
  omega

/-- The coning consequence of the complete Laman theorem, connected to
the original three-dimensional rigidity definition. -/
theorem isGenericallyRigidInR3_of_isLaman
    (G : SimpleGraph V) (hG : G.IsLaman) : IsGenericallyRigidInR3 (cone G) := by
  have hcard : 2 ≤ Fintype.card V := by
    have h := hG.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at h
    omega
  exact isGenericallyRigidInR3_of_planar G hcard hG.isGenericallyRigid_two

end

end Papers.Rigidity.Coning

end
end BundleSource0024

section BundleSource0025
/- Source: Papers/RigidityBodies.lean -/




@[expose] public section

/-!
# Maximal rigid cliques and their actual motion gluing

Every clique is rigid as a complete subgraph.  A body is therefore a
maximal clique with at least four vertices, exactly as in Section 3.
Three common generic vertices force two Euclidean twists to agree.  The
resulting union is proved to lie in the ambient rigidity closure through
the literal bar-motion kernel.
-/

namespace Papers.Rigidity

noncomputable section

open BarJoint
open scoped Classical

variable {V : Type} [Fintype V]

def IsBody (G : SimpleGraph V) (S : Finset V) : Prop :=
  4 ≤ S.card ∧ G.IsClique (S : Set V) ∧
    ∀ T : Finset V, S ⊆ T → G.IsClique (T : Set V) → T ⊆ S

/-- Every four-clique lies in a maximal clique, by maximizing its actual
finite vertex cardinality. -/
theorem exists_body_containing (G : SimpleGraph V) (S : Finset V)
    (hcard : 4 ≤ S.card) (hclique : G.IsClique (S : Set V)) :
    ∃ T : Finset V, S ⊆ T ∧ IsBody G T := by
  let candidates : Finset (Finset V) :=
    Finset.univ.filter fun T => S ⊆ T ∧ G.IsClique (T : Set V)
  have hS : S ∈ candidates := by simp [candidates, hclique]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨S, hS⟩
  have hT' : S ⊆ T ∧ G.IsClique (T : Set V) := by simpa [candidates] using hT
  refine ⟨T, hT'.1, hcard.trans (Finset.card_le_card hT'.1), hT'.2, ?_⟩
  intro U hTU hU
  have hUm : U ∈ candidates := by simp [candidates, hT'.1.trans hTU, hU]
  exact (Finset.eq_of_subset_of_card_le hTU (hmax U hUm)).symm.subset

theorem K4Covered.edge_in_body {G : SimpleGraph V} (hG : K4Covered G)
    {v w : V} (hvw : G.Adj v w) :
    ∃ S : Finset V, IsBody G S ∧ v ∈ S ∧ w ∈ S := by
  obtain ⟨T, hcard, hv, hw, hclique⟩ := hG v w hvw
  obtain ⟨S, hTS, hS⟩ := exists_body_containing G T (by omega) hclique
  exact ⟨S, hS, hTS hv, hTS hw⟩

/-- A motion on a graph restricts to one unique Euclidean twist on a
clique containing at least three general-position vertices. -/
theorem exists_twist_on_clique (G : SimpleGraph V) (p u : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (hu : IsInfinitesimalMotion G p u)
    (S : Finset V) (hcard : 3 ≤ S.card) (hclique : G.IsClique (S : Set V)) :
    ∃ X : Twist, ∀ w ∈ S, u w = evaluateTwist (p w) X := by
  let e : S ↪ V := Function.Embedding.subtype _
  obtain ⟨f : Fin 3 ↪ S⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := ↥S) (by simpa using hcard)
  have hpS := GeneralPosition.InGeneralPosition.comp_embedding p hp e
  have huS : IsInfinitesimalMotion (SimpleGraph.completeGraph S) (p ∘ e) (u ∘ e) := by
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    exact (isInfinitesimalMotion_iff G p u).mp hu a.val b.val
      (hclique a.property b.property (fun h => hab (Subtype.ext h)))
  obtain ⟨X, hX⟩ := exists_twist_of_completeMotion (p ∘ e) (u ∘ e) hpS f huS
  exact ⟨X, fun w hw => hX ⟨w, hw⟩⟩

/-- Actual twist representation of every ambient motion implies the
rank-defined ambient closure property. -/
theorem rigidCluster_of_motionRepresentation (G : SimpleGraph V) (S : Finset V)
    (p : Placement V 3) (hp : IsGenericPlacement p)
    (hrep : ∀ u : (rigidityOperator G p).ker,
      ∃ X : Twist, ∀ w ∈ S, u.val w = evaluateTwist (p w) X) :
    RigidCluster G S := by
  let H := clusterCompletion (fun _ : Unit => S)
  have hker : (rigidityOperator G p).ker ≤ (rigidityOperator (G ⊔ H) p).ker := by
    intro u hu
    obtain ⟨X, hX⟩ := hrep ⟨u, hu⟩
    change ∀ w ∈ S, u w = evaluateTwist (p w) X at hX
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b hab
    rcases hab with hab | ⟨_, _, ha, hb⟩
    · exact (isInfinitesimalMotion_iff G p u).mp hu a b hab
    · change ∑ i : Fin 3, (p a i - p b i) * (u a i - u b i) = 0
      rw [hX a ha, hX b hb]
      exact twist_preserves_bar X _ _
  have hr := rigidityRank_le_of_ker_le (G ⊔ H) G p hker
  change genericRigidityRank (G ⊔ H) 3 = genericRigidityRank G 3
  apply le_antisymm
  · exact (hp (G ⊔ H)).symm.le.trans (hr.trans (hp G).le)
  · exact genericRigidityRank_mono le_sup_left

/-- Three common generic vertices glue the actual motions of two cliques. -/
theorem rigidCluster_union_of_cliques (G : SimpleGraph V) (S T : Finset V)
    (hS : G.IsClique (S : Set V)) (hT : G.IsClique (T : Set V))
    (hcommon : 3 ≤ (S ∩ T).card) : RigidCluster G (S ∪ T) := by
  obtain ⟨p, hpGeneric, hpGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  obtain ⟨f : Fin 3 ↪ V, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S ∩ T) (by simpa using hcommon)
  have hfS (i : Fin 3) : f i ∈ S := (Finset.mem_inter.mp (hf ⟨i, rfl⟩)).1
  have hfT (i : Fin 3) : f i ∈ T := (Finset.mem_inter.mp (hf ⟨i, rfl⟩)).2
  apply rigidCluster_of_motionRepresentation G (S ∪ T) p hpGeneric
  intro u
  obtain ⟨X, hX⟩ := exists_twist_on_clique G p u.val hpGeom u.property S
    (hcommon.trans (Finset.card_le_card Finset.inter_subset_left)) hS
  obtain ⟨Y, hY⟩ := exists_twist_on_clique G p u.val hpGeom u.property T
    (hcommon.trans (Finset.card_le_card Finset.inter_subset_right)) hT
  have hXY : X = Y := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (p ∘ f)
      (GeneralPosition.InGeneralPosition.triangle p hpGeom f) (X - Y)
    intro i
    change evaluateTwist (p (f i)) (X - Y) = 0
    rw [map_sub, ← hX (f i) (hfS i), ← hY (f i) (hfT i), sub_self]
  refine ⟨X, ?_⟩
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact hX w hw
  · rw [hXY]
    exact hY w hw

/-- Distinct maximal bodies in the selected counterexample have at most
two common actual vertices. -/
theorem MinimalCounterexample.body_intersection_le_two (C : MinimalCounterexample V)
    (S T : Finset V) (hS : IsBody C.graph S) (hT : IsBody C.graph T) (hne : S ≠ T) :
    (S ∩ T).card ≤ 2 := by
  by_contra hlarge
  have hcommon : 3 ≤ (S ∩ T).card := by omega
  have hcluster := rigidCluster_union_of_cliques C.graph S T hS.2.1 hT.2.1 hcommon
  have hcard : 4 ≤ (S ∪ T).card := hS.1.trans (Finset.card_le_card Finset.subset_union_left)
  have hclique := C.rigidCluster_isClique (S ∪ T) hcard hcluster
  have hST := hS.2.2 (S ∪ T) Finset.subset_union_left hclique
  have hTS := hT.2.2 (S ∪ T) Finset.subset_union_right hclique
  apply hne
  exact Finset.Subset.antisymm (Finset.subset_union_left.trans hTS)
    (Finset.subset_union_right.trans hST)

/-- Every vertex belongs to at least two distinct actual bodies. -/
theorem MinimalCounterexample.exists_two_bodies (C : MinimalCounterexample V) (v : V) :
    ∃ S T : Finset V, IsBody C.graph S ∧ IsBody C.graph T ∧
      v ∈ S ∧ v ∈ T ∧ S ≠ T := by
  have hdegree := C.connected.degree_ge v
  have hpos : 0 < (C.graph.neighborFinset v).card := by
    rw [C.graph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  obtain ⟨S, hS, hvS, _⟩ := C.covered.edge_in_body
    ((C.graph.mem_neighborFinset v w).mp hw)
  by_contra hnone
  have heq (T : Finset V) (hT : IsBody C.graph T) (hvT : v ∈ T) : T = S := by
    by_contra hne
    exact hnone ⟨S, T, hS, hT, hvS, hvT, Ne.symm hne⟩
  apply C.not_simplicial v
  intro a ha b hb hab
  obtain ⟨T, hT, hvT, haT⟩ := C.covered.edge_in_body ha
  obtain ⟨U, hU, hvU, hbU⟩ := C.covered.edge_in_body hb
  have haS : a ∈ S := by rwa [heq T hT hvT] at haT
  have hbS : b ∈ S := by rwa [heq U hU hvU] at hbU
  exact hS.2.1 haS hbS hab

/-- All structural assertions of Lemma 3.1 are combined without any
additional geometric premise. -/
theorem MinimalCounterexample.lemma_three_one (C : MinimalCounterexample V) :
    (∀ S : Finset V, 4 ≤ S.card → RigidCluster C.graph S → C.graph.IsClique (S : Set V)) ∧
    (∀ v, ¬ C.graph.IsClique (C.graph.neighborSet v)) ∧
    (∀ v, IsGenericallyRigidInR3 (neighborCompletion C.graph v)) ∧
    (∀ v, 5 ≤ VertexPin.deletionRankDrop C.graph v) ∧
    (∀ v, ∃ S T : Finset V, IsBody C.graph S ∧ IsBody C.graph T ∧
      v ∈ S ∧ v ∈ T ∧ S ≠ T) ∧
    (∀ S T : Finset V, IsBody C.graph S → IsBody C.graph T → S ≠ T →
      (S ∩ T).card ≤ 2) :=
  ⟨C.rigidCluster_isClique, C.not_simplicial, C.neighborCompletion_isGenericallyRigid,
    C.five_le_deletionRankDrop, C.exists_two_bodies, C.body_intersection_le_two⟩

end

end Papers.Rigidity

end
end BundleSource0025

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0025/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0025.json"

section BundleSource0026
/- Source: Papers/RigidityConingAmbient.lean -/





@[expose] public section

/-!
# Coning a planar neighborhood component inside the original graph

This file transports the literal cone across its actual vertex labels,
then uses the already defined ambient rigidity closure. It supplies the
maximal-component implication in Lemma 3.2 without presuming that the
neighborhood itself has already been completed.

These coning calculations apply inside the original ambient graph.
-/

namespace Papers.Rigidity.Coning

noncomputable section

open BarJoint
open scoped Classical

variable {V : Type} [Fintype V]

def vertexMap (v : V) (S : Finset V) :
    Option {w : V // w ∈ S} → {w : V // w ∈ insert v S}
  | none => ⟨v, Finset.mem_insert_self v S⟩
  | some w => ⟨w.val, Finset.mem_insert_of_mem w.property⟩

theorem vertexMap_bijective (v : V) (S : Finset V) (hv : v ∉ S) :
    Function.Bijective (vertexMap v S) := by
  constructor
  · intro a b hab
    have he := congrArg Subtype.val hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            have hb : v = b.val := he
            exact False.elim (hv (hb.symm ▸ b.property))
    | some a =>
        cases b with
        | none =>
            have ha : a.val = v := he
            exact False.elim (hv (ha ▸ a.property))
        | some b => exact congrArg some (Subtype.ext he)
  · intro w
    by_cases hw : w.val = v
    · exact ⟨none, Subtype.ext hw.symm⟩
    · have hmem : w.val ∈ S :=
        (Finset.mem_insert.mp w.property).resolve_left hw
      exact ⟨some ⟨w.val, hmem⟩, rfl⟩

def vertexEquiv (v : V) (S : Finset V) (hv : v ∉ S) :
    Option {w : V // w ∈ S} ≃ {w : V // w ∈ insert v S} :=
  Equiv.ofBijective (vertexMap v S) (vertexMap_bijective v S hv)

theorem mapped_cone_le (G : SimpleGraph V) (v : V) (S : Finset V) (hv : v ∉ S)
    (hstar : ∀ w ∈ S, G.Adj v w) :
    (cone (G.induce (S : Set V))).comap (vertexEquiv v S hv).symm ≤
      G.induce ((insert v S : Finset V) : Set V) := by
  have hmap (a b : Option {w : V // w ∈ S})
      (hab : (cone (G.induce (S : Set V))).Adj a b) :
      G.Adj (vertexMap v S a).val (vertexMap v S b).val := by
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some b => exact hstar b.val b.property
    | some a =>
        cases b with
        | none => exact (hstar a.val a.property).symm
        | some b => exact hab
  intro a b hab
  have h := hmap ((vertexEquiv v S hv).symm a) ((vertexEquiv v S hv).symm b) hab
  change G.Adj ((vertexEquiv v S hv) ((vertexEquiv v S hv).symm a)).val
    ((vertexEquiv v S hv) ((vertexEquiv v S hv).symm b)).val at h
  change G.Adj a.val b.val
  simpa only [Equiv.apply_symm_apply] using h

/-- A planar rigid induced neighborhood set cones to a rigid induced
subgraph on the actual labels `insert v S`. Additional edges are allowed. -/
theorem rigidInduced_insert_of_planar (G : SimpleGraph V) (v : V) (S : Finset V)
    (hv : v ∉ S) (hstar : ∀ w ∈ S, G.Adj v w) (hcard : 2 ≤ S.card)
    (hplanar : (G.induce (S : Set V)).IsGenericallyRigid 2) :
    RigidInducedSubgraph G (insert v S) := by
  have hcone := isGenericallyRigidInR3_of_planar
    (G.induce (S : Set V)) (by simpa using hcard) hplanar
  have hrel : IsGenericallyRigidInR3
      ((cone (G.induce (S : Set V))).comap (vertexEquiv v S hv).symm) :=
    (isGenericallyRigid_relabel_iff (vertexEquiv v S hv)
      (cone (G.induce (S : Set V))) 3).mpr hcone
  exact hrel.mono (mapped_cone_le G v S hv hstar)

theorem rigidCluster_insert_of_planar (G : SimpleGraph V) (v : V) (S : Finset V)
    (hv : v ∉ S) (hstar : ∀ w ∈ S, G.Adj v w) (hcard : 2 ≤ S.card)
    (hplanar : (G.induce (S : Set V)).IsGenericallyRigid 2) :
    RigidCluster G (insert v S) :=
  RigidInducedSubgraph.rigidCluster G (insert v S)
    (rigidInduced_insert_of_planar G v S hv hstar hcard hplanar)

/-- In the selected counterexample every planar rigid neighborhood set
of at least three vertices already cones to an actual clique. -/
theorem planar_neighborhood_cone_isClique (C : MinimalCounterexample V)
    (v : V) (S : Finset V) (hS : S ⊆ C.graph.neighborFinset v)
    (hcard : 3 ≤ S.card)
    (hplanar : (C.graph.induce (S : Set V)).IsGenericallyRigid 2) :
    C.graph.IsClique ((insert v S : Finset V) : Set V) := by
  have hstar (w : V) (hw : w ∈ S) : C.graph.Adj v w :=
    (C.graph.mem_neighborFinset v w).mp (hS hw)
  have hv : v ∉ S := fun h => C.graph.loopless.irrefl v (hstar v h)
  apply C.rigidCluster_isClique (insert v S)
  · rw [Finset.card_insert_of_notMem hv]
    omega
  · exact rigidCluster_insert_of_planar C.graph v S hv hstar (by omega) hplanar

/-- No planar rigid component of the neighborhood can properly contain
the deletion of an incident maximal body. This is the first assertion
used in the proof of Lemma 3.2. -/
theorem incident_body_planar_maximal (C : MinimalCounterexample V)
    (v : V) (T S : Finset V) (hT : IsBody C.graph T) (hvT : v ∈ T)
    (hTS : T.erase v ⊆ S) (hS : S ⊆ C.graph.neighborFinset v)
    (hplanar : (C.graph.induce (S : Set V)).IsGenericallyRigid 2) :
    S ⊆ T.erase v := by
  have hc : 3 ≤ S.card := by
    have he := Finset.card_le_card hTS
    rw [Finset.card_erase_of_mem hvT] at he
    have ht := hT.1
    omega
  have hclique := planar_neighborhood_cone_isClique C v S hS hc hplanar
  have hTsub : T ⊆ insert v S := by
    intro w hw
    by_cases hwv : w = v
    · exact Finset.mem_insert.mpr (Or.inl hwv)
    · exact Finset.mem_insert.mpr (Or.inr (hTS (Finset.mem_erase.mpr ⟨hwv, hw⟩)))
  have hsub := hT.2.2 (insert v S) hTsub hclique
  intro w hw
  refine Finset.mem_erase.mpr ⟨?_, hsub (Finset.mem_insert_of_mem hw)⟩
  exact ((C.graph.mem_neighborFinset v w).mp (hS hw)).ne.symm

end

end Papers.Rigidity.Coning

end
end BundleSource0026

section BundleSource0027
/- Source: Papers/RigidityPlanarCircuit.lean -/





@[expose] public section

/-!
# The rigid support of a minimal planar dependence

This supplies the circuit step used in Lemma 3.2. A minimally non-sparse
graph is supported on a vertex set on which deletion of any one edge
leaves a Laman graph. Its induced graph is therefore actually generically
rigid in the plane. The conclusion can then be coned inside the original
neighborhood, using the literal cone rigidity equivalence.

The planar circuit supplies the neighborhood completion step.
-/

namespace Papers.Rigidity.PlanarCircuit

noncomputable section

open scoped Classical

variable {V : Type} [Fintype V]

/-- Every non-sparse finite graph has a minimal non-sparse edge subset.
This is a finite-poset choice, with no matroid assertion assumed. -/
theorem exists_minimal_nonSparse (G : SimpleGraph V) (hG : ¬ G.IsSparse 2 3) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ¬ H.IsSparse 2 3 ∧
      ∀ K : SimpleGraph V, K < H → K.IsSparse 2 3 := by
  classical
  obtain ⟨H, hHG, hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : SimpleGraph V => ¬ H.IsSparse 2 3) G hG
  refine ⟨H, hHG, hH.1, ?_⟩
  intro K hKH
  by_contra hK
  exact (not_le_of_gt hKH) (hH.2 hK hKH.le)

/-- A minimally non-sparse edge set has a planar rigid support. Isolated
vertices of the ambient type need not be included in that support. -/
theorem exists_rigid_support (G : SimpleGraph V)
    (hnot : ¬ G.IsSparse 2 3)
    (hminimal : ∀ H : SimpleGraph V, H < G → H.IsSparse 2 3) :
    ∃ S : Finset V, 3 ≤ S.card ∧ G.edgesIn (S : Set V) = G.edgeSet ∧
      (G.induce (S : Set V)).IsGenericallyRigid 2 := by
  classical
  obtain ⟨S, hS, hbad⟩ : ∃ S : Finset V,
      3 ≤ 2 * S.card ∧ 2 * S.card < (G.edgesIn (S : Set V)).ncard + 3 := by
    have h := hnot
    unfold SimpleGraph.IsSparse at h
    push_neg at h
    exact h
  have hcardS : Fintype.card (S : Set V) = S.card :=
    @Fintype.card_coe V S (inferInstance : Fintype (S : Set V))
  let H := SimpleGraph.fromEdgeSet (G.edgesIn (S : Set V))
  have hHedge : H.edgeSet = G.edgesIn (S : Set V) :=
    SimpleGraph.edgeSet_fromEdgeSet_of_off_diag
      ((G.edgesIn_subset_edgeSet _).trans (SimpleGraph.edgeSet_mono le_top))
  have hHle : H ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp (by
    rw [hHedge]
    exact G.edgesIn_subset_edgeSet _)
  have hHinside : H.edgesIn (S : Set V) = G.edgesIn (S : Set V) := by
    change H.edgeSet ∩ (S : Set V).sym2 = _
    rw [hHedge]
    exact Set.inter_eq_left.mpr Set.inter_subset_right
  have hHeq : H = G := by
    by_contra hne
    have hsparse := hminimal H (lt_of_le_of_ne hHle hne)
    have hbound := hsparse S hS
    rw [hHinside] at hbound
    omega
  have hsupport : G.edgesIn (S : Set V) = G.edgeSet := by
    simpa only [hHeq] using hHedge.symm
  have hcap : (G.edgesIn (S : Set V)).ncard ≤ S.card.choose 2 := by
    rw [SimpleGraph.ncard_edgesIn_eq_ncard_induce_edgeSet]
    have h := Set.ncard_le_ncard
      (SimpleGraph.edgeSet_mono
        (show G.induce (S : Set V) ≤ ⊤ from le_top))
    simpa only [SimpleGraph.ncard_edgeSet_top_eq_card_choose_two, hcardS] using h
  have hcard : 3 ≤ S.card := by
    by_contra h
    have htwo : S.card = 2 := by omega
    norm_num only [htwo, Nat.choose_self] at hcap
    omega
  have hpos : 0 < G.edgeSet.ncard := by
    rw [hsupport] at hbad
    omega
  obtain ⟨e, he⟩ := (Set.ncard_pos G.edgeSet.toFinite).mp hpos
  let K := SimpleGraph.fromEdgeSet (G.edgeSet \ {e})
  have hKedge : K.edgeSet = G.edgeSet \ {e} :=
    SimpleGraph.edgeSet_fromEdgeSet_of_off_diag
      (Set.sdiff_subset.trans (SimpleGraph.edgeSet_mono le_top))
  have hKle : K ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp (by
    rw [hKedge]
    exact Set.sdiff_subset)
  have hKne : K ≠ G := by
    intro h
    have hke : e ∈ K.edgeSet := h.symm ▸ he
    rw [hKedge] at hke
    exact hke.2 (Set.mem_singleton e)
  have hKsparse := hminimal K (lt_of_le_of_ne hKle hKne)
  have hKinside : K.edgesIn (S : Set V) = K.edgeSet := by
    apply Set.inter_eq_left.mpr
    intro a ha
    have hGa : a ∈ G.edgeSet := (SimpleGraph.edgeSet_mono hKle) ha
    rw [← hsupport] at hGa
    exact hGa.2
  have hcounts : K.edgeSet.ncard + 1 = G.edgeSet.ncard := by
    rw [hKedge]
    exact Set.ncard_sdiff_singleton_add_one he
  have hbound := hKsparse S hS
  rw [hKinside] at hbound
  rw [hsupport] at hbad
  have hexact : K.edgeSet.ncard + 3 = 2 * S.card := by omega
  have hlaman : (K.induce (S : Set V)).IsLaman := by
    refine ⟨hKsparse.comap Subtype.val_injective, ?_⟩
    rw [← SimpleGraph.ncard_edgesIn_eq_ncard_induce_edgeSet, hKinside,
      Nat.card_eq_fintype_card, hcardS]
    exact hexact
  refine ⟨S, hcard, hsupport, ?_⟩
  apply SimpleGraph.IsGenericallyRigid.mono (G := K.induce (S : Set V))
    (G' := G.induce (S : Set V))
  · intro a b hab
    exact hKle hab
  · exact hlaman.isGenericallyRigid_two

/-- In the selected counterexample a minimal planar dependence inside a
neighborhood has a support whose cone is already an actual clique. -/
theorem exists_clique_cone_support (C : MinimalCounterexample V) (v : V)
    (H : SimpleGraph V) (hHG : H ≤ C.graph)
    (hHN : H.support ⊆ (C.graph.neighborFinset v : Set V))
    (hnot : ¬ H.IsSparse 2 3)
    (hminimal : ∀ K : SimpleGraph V, K < H → K.IsSparse 2 3) :
    ∃ S : Finset V, 3 ≤ S.card ∧ H.edgesIn (S : Set V) = H.edgeSet ∧
      C.graph.IsClique ((insert v S : Finset V) : Set V) := by
  classical
  obtain ⟨S, hcard, hsupport, hrigid⟩ := exists_rigid_support H hnot hminimal
  /- Remove any isolated ambient labels before coning: the sparse
  equality shows that a rigid support of at least three vertices has
  positive degree at each vertex. -/
  obtain ⟨K, hKH, hKlaman⟩ := hrigid.exists_isLaman_le (by simpa using (show 2 ≤ S.card by omega))
  have hS : S ⊆ C.graph.neighborFinset v := by
    intro w hw
    let wS : (S : Set V) := ⟨w, hw⟩
    have hdegree := hKlaman.two_le_degree (by simpa using hcard) wS
    have hnonempty : (K.neighborFinset wS).Nonempty := by
      apply Finset.card_pos.mp
      rw [K.card_neighborFinset_eq_degree]
      omega
    obtain ⟨z, hz⟩ := hnonempty
    have hadj : H.Adj w z.val := hKH ((K.mem_neighborFinset wS z).mp hz)
    exact hHN hadj.left_mem_support
  have hrigidG : (C.graph.induce (S : Set V)).IsGenericallyRigid 2 :=
    SimpleGraph.IsGenericallyRigid.mono (fun _ _ h => hHG h) hrigid
  exact ⟨S, hcard, hsupport,
    Coning.planar_neighborhood_cone_isClique C v S hS hcard hrigidG⟩

end

end Papers.Rigidity.PlanarCircuit

end
end BundleSource0027

section BundleSource0028
/- Source: Papers/RigidityLaman_RowIndependence.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted from the proved row-independence prefix of Bryan Gin-ge Chen's
MatroidIdentification.lean, commit021c2284bc387efee3c3b20a18eb5f769638b578.
The unrelated downstream count-matroid packaging is omitted; no used
mathematical theorem or proof is replaced by an assumption. Public import
paths are adapted to this project.
-/






/-!
# Matroid identification of the planar rigidity matroid

The harder half of the characterization of row-independence in the plane, due to
Pollaczek-Geiringer and Laman (Jordán 2016, Theorem 2.2.1; Pollaczek-Geiringer proves this half
in her §8, p. 70): in dimension 2, every `(2, 3)`-sparse edge set is row-independent at some
placement. Combined with the other half (`isSparse_of_edgeSetRowIndependent_dim_two` in
`RigidityMatroid.lean`), this gives the row-LI ↔ sparse iff and packages the planar rigidity
matroid as a `Mathlib.Combinatorics.Matroid` instance.

The proof follows Jordán's proof of his Theorem 2.2.1 (p. 45): induction with reverse Henneberg
moves, each move lifting row-independence to a placement of the larger graph by placing the new
vertex suitably. It inducts on `|V|`, where Jordán inducts on `|E|`. This file holds the
Henneberg row-LI lifts (pendant, Type I and Type II, in operation form), the inductive existence
theorem, the iff and the matroid identification.

The blueprint's `sec:rigidity-matroid` presents this file.
-/

public section

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- Internal helper for the Type I row-LI lift. If a linear combination
`c * ⟪q - p' a, α⟫_ℝ + d * ⟪q - p' b, α⟫_ℝ` vanishes for every `α : EuclideanSpace ℝ (Fin 2)`,
then under `LinearIndependent ℝ ![q - p' a, q - p' b]` we have `c = d = 0`. -/
private lemma typeI_new_rows_coeff_zero
    {V : Type*} {p' : Framework V 2} {a b : V} {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' b]) {c d : ℝ}
    (heval : ∀ α : EuclideanSpace ℝ (Fin 2),
        c * ⟪q - p' a, α⟫_ℝ + d * ⟪q - p' b, α⟫_ℝ = 0) :
    c = 0 ∧ d = 0 := by
  have h_inner : ∀ α : EuclideanSpace ℝ (Fin 2),
      ⟪c • (q - p' a) + d • (q - p' b), α⟫_ℝ = 0 := fun α => by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    linarith [heval α]
  exact LinearIndependent.pair_iff.mp hLI c d
    (inner_self_eq_zero.mp (h_inner _))

/-- **Conditional Type I row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent, and `q : EuclideanSpace ℝ (Fin 2)` places the new vertex so that the two
displacements `q - p' a` and `q - p' b` are linearly independent, then every edge of
`typeI G' a b` is row-independent at the extended placement `fun w : Option V => w.elim q p'`.

Row-LI analogue of `typeI_isInfinitesimallyRigid_extend`. The proof uses
`LinearIndepOn.union` to partition `(typeI G' a b).edgeSet` into the image of `G'.edgeSet`
under `Sym2.map some` and the two new edges `s(none, some a)`, `s(none, some b)`. LI on the
old part comes by factoring through the restriction map `(· ∘ some) : Framework (Option V) 2 →ₗ
Framework V 2` whose dual is injective (since the restriction is surjective). LI on the new
part is direct from `hLI`. Disjointness of spans follows by evaluating any joint element at
motions with `x ∘ some = 0`: old rows vanish, and the resulting new-row equation pins both new
coefficients to zero via `hLI` again. -/
theorem typeI_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b : V} {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' b]) :
    (typeI G' a b).EdgeSetRowIndependent (fun w : Option V => w.elim q p') Set.univ := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  -- `hLI` implies `a ≠ b` (otherwise `![v, v]` is dependent).
  have hab : a ≠ b := by
    intro hab_eq
    have : (![q - p' a, q - p' b] : Fin 2 → EuclideanSpace ℝ (Fin 2)) 0 =
        ![q - p' a, q - p' b] 1 := by simp [hab_eq]
    exact (by decide : (0 : Fin 2) ≠ 1) (hLI.injective this)
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G' edges to typeI edges via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet,
      Sym2.map (some : V → Option V) e'.val ∈ (typeI G' a b).edgeSet := by
    rintro ⟨e, he⟩
    induction e with
    | h u v => rw [Sym2.map_mk, mem_edgeSet]; exact he
  set lift_some : G'.edgeSet → (typeI G' a b).edgeSet := fun e' =>
    ⟨Sym2.map some e'.val, hlift_mem e'⟩ with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq))
  -- New edges in `(typeI _).edgeSet`.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeI G' a b).edgeSet := by simp
  have hnewB_mem : s((none : Option V), some b) ∈ (typeI G' a b).edgeSet := by simp
  set newEdgeA : (typeI G' a b).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  set newEdgeB : (typeI G' a b).edgeSet := ⟨s(none, some b), hnewB_mem⟩ with hB_def
  have hAB_ne : newEdgeA ≠ newEdgeB := fun heq =>
    hab (Sym2.mk_none_some_eq_iff.mp (congrArg Subtype.val heq))
  -- The two pieces of the cover.
  set oldSet : Set (typeI G' a b).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeI G' a b).edgeSet := {newEdgeA, newEdgeB} with hnewSet_def
  -- `Set.univ ⊆ oldSet ∪ newSet`.
  have h_cover : (Set.univ : Set (typeI G' a b).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeI_edgeSet] at he
    rcases he with ⟨e0, he0_mem, h_some⟩ | h_new
    · left
      exact ⟨⟨e0, he0_mem⟩, Subtype.ext h_some⟩
    · right
      rcases h_new with h_eq | h_eq
      · exact Or.inl (Subtype.ext h_eq)
      · exact Or.inr (Subtype.ext h_eq)
  refine LinearIndepOn.mono ?_ h_cover
  -- Three pieces: LI on old, LI on new, disjoint spans.
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`.
    rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      id Function.injective_id hlift_mem h
  · -- LI on `newSet = {newEdgeA, newEdgeB}`: derive coefficients zero via `hLI`.
    rw [hnewSet_def, LinearIndepOn.pair_iff _ hAB_ne]
    intro c d hcd
    refine typeI_new_rows_coeff_zero hLI ?_
    intro α
    have key := DFunLike.congr_fun hcd (fun w : Option V => w.elim α (fun _ => 0))
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      smul_eq_mul, hp_ext_def, hA_def, hB_def, rigidityRow_none_some_elim] at key
    exact key
  · -- Disjoint spans: any joint element evaluates to zero at "x ∘ some = 0" motions.
    rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    -- `row '' newSet = {row newEdgeA, row newEdgeB}`; pick coefficients `c, d`.
    rw [hnewSet_def, Set.image_pair, Submodule.mem_span_pair] at hf_new
    obtain ⟨c, d, hcd⟩ := hf_new
    -- Show `f = 0` by showing `c • row newEdgeA + d • row newEdgeB = 0`, via `c = d = 0`.
    rw [← hcd]
    -- Evaluate at the test motion `elim α 0`; `f` vanishes there (since `f` is in the old span
    -- and every old row vanishes there, `oldSpan_le_ker_eval_elim`), so the new-row
    -- contribution vanishes too.
    suffices h_cd : c = 0 ∧ d = 0 by simp [h_cd.1, h_cd.2]
    refine typeI_new_rows_coeff_zero hLI ?_
    intro α
    have hf_zero_at_x : f (fun w : Option V => w.elim α (fun _ => 0)) = 0 := by
      have h_le := oldSpan_le_ker_eval_elim (H := typeI G' a b) q p' α (S := oldSet)
        (by rintro _ ⟨e', rfl⟩; exact ⟨e'.val, rfl⟩)
      simpa using h_le hf_old
    have hcd_eval := DFunLike.congr_fun hcd (fun w : Option V => w.elim α (fun _ => 0))
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hp_ext_def, hA_def, hB_def, rigidityRow_none_some_elim] at hcd_eval
    -- `hcd_eval : c * ⟪q - p' a, α⟫ + d * ⟪q - p' b, α⟫ = f (elim α 0)`; combine.
    linarith [hcd_eval, hf_zero_at_x]

/-- **Unconditional Type I row-LI lift in dim 2.** Given a placement `p'` of `G'` at which every
edge of `G'` is row-independent, and two old vertices `a, b` with distinct images
`p' a ≠ p' b`, there exists an extended placement `p : Framework (Option V) 2` with
`p ∘ some = p'` at which every edge of `typeI G' a b` is row-independent.

Row-LI analogue of `typeI_isGenericallyRigidInj_two`. The proof uses
`exists_off_line_off_finite_dim_two` (with empty avoidance set, since the sufficiency half
needs *some* placement, not an *injective* one) to pick `q` so that `q - p' a` and
`q - p' b` are linearly independent, then applies `typeI_edgeSetRowIndependent_extend`. -/
theorem typeI_edgeSetRowIndependent_lift {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b : V} (hab : p' a ≠ p' b) :
    ∃ p : Framework (Option V) 2, p ∘ some = p' ∧
      (typeI G' a b).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨q, hLI, _⟩ :=
    exists_off_line_off_finite_dim_two (p' a) (p' b) hab ∅ Set.finite_empty
  exact ⟨fun w : Option V => w.elim q p', funext fun _ => rfl,
    typeI_edgeSetRowIndependent_extend h hLI⟩

/-! ### Pendant row-LI lift

The pendant case is the `b = a` degeneracy of the Type I lift: `typeI G' a a` joins the new
vertex to a single old vertex `a` (the parallel edges collapse), so the lift consumes only
`q ≠ p' a` (no linear-independence condition between two displacements). The conditional core
mirrors `typeI_edgeSetRowIndependent_extend` with the `newSet = {newA}` singleton in place of
the pair `{newA, newB}`. -/

/-- **Conditional pendant row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent and `q ≠ p' a`, then every edge of `typeI G' a a` is row-independent at
the extended placement `fun w : Option V => w.elim q p'`.

Degenerate `b = a` case of `typeI_edgeSetRowIndependent_extend`: the parallel edges of
`typeI G' a a` collapse to the single new edge `s(none, some a)`, so the LI condition
`![q - p' a, q - p' b]` (impossible at `b = a`) is replaced by `q ≠ p' a`. Used, through
`typeI_pendant_edgeSetRowIndependent_lift`, by the pendant branch (degree-1 reverse) of the
induction on `|V|` in `IsSparse.exists_rowIndependent_placement`. -/
theorem typeI_pendant_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a : V} {q : EuclideanSpace ℝ (Fin 2)} (hq : q ≠ p' a) :
    (typeI G' a a).EdgeSetRowIndependent (fun w : Option V => w.elim q p') Set.univ := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G' edges to typeI edges via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet,
      Sym2.map (some : V → Option V) e'.val ∈ (typeI G' a a).edgeSet := by
    rintro ⟨e, he⟩
    induction e with
    | h u v => rw [Sym2.map_mk, mem_edgeSet]; exact he
  set lift_some : G'.edgeSet → (typeI G' a a).edgeSet := fun e' =>
    ⟨Sym2.map some e'.val, hlift_mem e'⟩ with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq))
  -- The single new edge.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeI G' a a).edgeSet := by simp
  set newEdgeA : (typeI G' a a).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  -- Cover: typeI.edgeSet ⊆ oldSet ∪ {newA}.
  set oldSet : Set (typeI G' a a).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeI G' a a).edgeSet := {newEdgeA} with hnewSet_def
  have h_cover : (Set.univ : Set (typeI G' a a).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeI_edgeSet] at he
    rcases he with ⟨e0, he0_mem, h_some⟩ | h_new
    · left; exact ⟨⟨e0, he0_mem⟩, Subtype.ext h_some⟩
    · right
      rcases h_new with h_eq | h_eq <;> exact Subtype.ext h_eq
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`.
    rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      id Function.injective_id hlift_mem h
  · -- LI on the singleton `{newA}`: `row newA ≠ 0` via the motion
    -- `none ↦ q - p' a, some _ ↦ 0` evaluating the row to `‖q - p' a‖² > 0`.
    rw [hnewSet_def, linearIndepOn_singleton_iff]
    intro h_zero
    have h_apply := DFunLike.congr_fun h_zero
        (fun w : Option V => w.elim (q - p' a) (fun _ => 0))
    simp only [LinearMap.zero_apply, hp_ext_def, hA_def, rigidityRow_none_some_elim] at h_apply
    exact (sub_ne_zero.mpr hq) (inner_self_eq_zero.mp h_apply)
  · -- Disjoint spans: standard test-motion argument.
    rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    rw [hnewSet_def, Set.image_singleton, Submodule.mem_span_singleton] at hf_new
    obtain ⟨c, hc⟩ := hf_new
    rw [← hc]
    suffices h_c : c = 0 by simp [h_c]
    -- Apply at `elim (q - p' a) 0`: old span vanishes; new row gives `c * ‖q - p' a‖²`.
    have hf_zero_at_x : f (fun w : Option V => w.elim (q - p' a) (fun _ => 0)) = 0 := by
      have h_le := oldSpan_le_ker_eval_elim (H := typeI G' a a) q p' (q - p' a) (S := oldSet)
        (by rintro _ ⟨e', rfl⟩; exact ⟨e'.val, rfl⟩)
      simpa using h_le hf_old
    have hc_eval := DFunLike.congr_fun hc (fun w : Option V => w.elim (q - p' a) (fun _ => 0))
    simp only [LinearMap.smul_apply, smul_eq_mul, hp_ext_def, hA_def,
      rigidityRow_none_some_elim] at hc_eval
    have hqa_ne : ⟪q - p' a, q - p' a⟫_ℝ ≠ 0 :=
      fun h => sub_ne_zero.mpr hq (inner_self_eq_zero.mp h)
    have h_prod : c * ⟪q - p' a, q - p' a⟫_ℝ = 0 := by linarith [hf_zero_at_x]
    exact (mul_eq_zero.mp h_prod).resolve_right hqa_ne

/-- **Unconditional pendant row-LI lift in dim 2.** Given a placement `p'` of `G'` at which
every edge of `G'` is row-independent and an old vertex `a : V`, there exists an extended
placement `p : Framework (Option V) 2` with `p ∘ some = p'` at which every edge of
`typeI G' a a` is row-independent.

The blueprint statement `lem:pendant-rowIndependent-lift`: picks any `q ≠ p' a` (exists since
`EuclideanSpace ℝ (Fin 2)` is nontrivial) and applies
`typeI_pendant_edgeSetRowIndependent_extend`. Used by the pendant branch of the induction on
`|V|` in `IsSparse.exists_rowIndependent_placement`, alongside the canonical iso
`isoTypeIOfTwoNeighbors` at `a = b` (the unique neighbour of the degree-1 vertex). -/
theorem typeI_pendant_edgeSetRowIndependent_lift {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ) (a : V) :
    ∃ p : Framework (Option V) 2, p ∘ some = p' ∧
      (typeI G' a a).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨q, hq⟩ := exists_ne (p' a)
  exact ⟨fun w : Option V => w.elim q p', funext fun _ => rfl,
    typeI_pendant_edgeSetRowIndependent_extend h hq⟩

/-! ### Type II row-LI lift, conditional core

Row-LI analogue of `typeII_isInfinitesimallyRigid_extend`. The new vertex `q` is
placed on the line through `p' a, p' b` (collinearity scalar `s ≠ 0, 1`) so that a linear
combination of the two new rows for `s(none, some a)` and `s(none, some b)` is a multiple of
the deleted G'-row for `s(a, b)` (`typeII_collinear_inner_combo`); the third new row
`s(none, some c)` is independent by `(q - p' a, q - p' c)` linear independence. Whiteley's
argument (his proof of the Edge `d`-Split Theorem 11.1.7, 1996), adapted to row-LI. -/

/-- Internal helper for the Type II row-LI lift. Under the collinearity hypothesis
`q - p' a = s • (p' b - p' a)` with `s ≠ 0`, the evaluation
`β_a · ⟪q - p' a, α⟫ + β_b · ⟪q - p' b, α⟫ + β_c · ⟪q - p' c, α⟫ = 0` for every `α`
together with `LinearIndependent ℝ ![q - p' a, q - p' c]` pins
`s β_a + (s - 1) β_b = 0` and `β_c = 0`. The hypothesis `s ≠ 0` lets us rescale the
`q - p' a, q - p' b` evaluations into a Type I shape (scalar multiples of `q - p' a`)
and invoke `typeI_new_rows_coeff_zero`. -/
private lemma typeII_new_rows_coeff_zero
    {V : Type*} {p' : Framework V 2} {a b c : V}
    {q : EuclideanSpace ℝ (Fin 2)} {s : ℝ} (hs0 : s ≠ 0)
    (hcoll : q - p' a = s • (p' b - p' a))
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' c])
    {β_a β_b β_c : ℝ}
    (heval : ∀ α : EuclideanSpace ℝ (Fin 2),
        β_a * ⟪q - p' a, α⟫_ℝ + β_b * ⟪q - p' b, α⟫_ℝ +
          β_c * ⟪q - p' c, α⟫_ℝ = 0) :
    s * β_a + (s - 1) * β_b = 0 ∧ β_c = 0 := by
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have h1 : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    simp only [h1, hcoll, sub_smul, one_smul]
  -- Reformulate as a Type I-style evaluation in `q - p' a, q - p' c` only.
  have heval' : ∀ α : EuclideanSpace ℝ (Fin 2),
      ((s * β_a + (s - 1) * β_b) / s) * ⟪q - p' a, α⟫_ℝ +
        β_c * ⟪q - p' c, α⟫_ℝ = 0 := by
    intro α
    have h := heval α
    rw [hcoll, hcoll_b, real_inner_smul_left, real_inner_smul_left] at h
    have hs_inner : ⟪q - p' a, α⟫_ℝ = s * ⟪p' b - p' a, α⟫_ℝ := by
      rw [hcoll, real_inner_smul_left]
    rw [hs_inner]
    field_simp
    linarith
  obtain ⟨h1, h2⟩ := typeI_new_rows_coeff_zero hLI heval'
  refine ⟨?_, h2⟩
  have := (div_eq_zero_iff.mp h1).resolve_right hs0
  exact this

/-- **Conditional Type II row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent, `G'.Adj a b` (so `s(a, b)` is the deleted G'-edge), and
`q : EuclideanSpace ℝ (Fin 2)` is placed on the line through `p' a, p' b` with collinearity
scalar `s ≠ 0, 1` (i.e. `q - p' a = s • (p' b - p' a)`) AND the linear-independence condition
`LinearIndependent ℝ ![q - p' a, q - p' c]` (the new vertex's displacement to `p' c` is off
the line through `p' a, p' b`), then every edge of `typeII G' a b c` is row-independent at the
extended placement `fun w : Option V => w.elim q p'`.

Row-LI analogue of `typeII_isInfinitesimallyRigid_extend`. Whiteley's argument adapted to the
dual side: the two new rows `s(none, some a)` and `s(none, some b)` have displacements parallel
to `p' b - p' a`, and a single linear combination
`s · row_b - (s-1) · row_a = -s(s-1) · T(rowG'(s(a, b)))` recovers the deleted `G'`-row
`s(a, b)`; the third new row
`s(none, some c)` is independent of the first two by linear independence of `![q - p' a,
q - p' c]`, and the entire new-row span is disjoint from the lifted old-row span (whose
G'-row for `s(a, b)` is *not* in the lifted typeII old-row family, but is in the new-row
span by the same identity). -/
theorem typeII_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b c : V} (h_ab : G'.Adj a b)
    {q : EuclideanSpace ℝ (Fin 2)} {s : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hcoll : q - p' a = s • (p' b - p' a))
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' c]) :
    (typeII G' a b c).EdgeSetRowIndependent
        (fun w : Option V => w.elim q p') Set.univ := by
  classical
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have h1 : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    simp only [h1, hcoll, sub_smul, one_smul]
  have hab_ne : a ≠ b := G'.ne_of_adj h_ab
  -- `a ≠ c` from hLI (else `![v, v]` not LI).
  have hac_ne : a ≠ c := by
    intro hac_eq
    have : (![q - p' a, q - p' c] : Fin 2 → EuclideanSpace ℝ (Fin 2)) 0 =
        ![q - p' a, q - p' c] 1 := by simp [hac_eq]
    exact (by decide : (0 : Fin 2) ≠ 1) (hLI.injective this)
  -- `b ≠ c` from hcoll + hLI (else `q - p' a = (s/(s-1)) • (q - p' c)`, against LI).
  have hbc_ne : b ≠ c := by
    intro hbc_eq
    rw [linearIndependent_fin2] at hLI
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI
    obtain ⟨_, h_LI⟩ := hLI
    refine h_LI (s / (s - 1)) ?_
    rw [← hbc_eq, hcoll, hcoll_b, ← smul_assoc, smul_eq_mul]
    congr 1
    field_simp
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G'-edges `e' ≠ s(a, b)` via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet, e'.val ≠ s(a, b) →
      Sym2.map (some : V → Option V) e'.val ∈ (typeII G' a b c).edgeSet := by
    rintro ⟨e, he⟩ hne
    induction e with
    | h u v =>
      simp only [Sym2.map_mk, mem_edgeSet, typeII_adj_some_some]
      exact ⟨he, by simpa using hne⟩
  set lift_some : {e' : G'.edgeSet // e'.val ≠ s(a, b)} →
      (typeII G' a b c).edgeSet :=
    fun e' => ⟨Sym2.map some e'.val.val, hlift_mem e'.val e'.property⟩
    with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Subtype.ext
      (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq)))
  -- Restriction map, used by the disjoint-spans branch below; its `dualMap` factors the
  -- lifted-old typeII rows via `rigidityRow_lift_eq_funLeft_dualMap`.
  set restrictMap : Framework (Option V) 2 →ₗ[ℝ] Framework V 2 :=
    LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)
  have h_restrict_surj : Function.Surjective restrictMap :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (Option.some_injective V)
  have h_factor : ∀ e' : {e' : G'.edgeSet // e'.val ≠ s(a, b)},
      (typeII G' a b c).rigidityRow p_ext (lift_some e') =
        restrictMap.dualMap (G'.rigidityRow p' e'.val) :=
    fun e' => rigidityRow_lift_eq_funLeft_dualMap (some : V → Option V)
      (fun _ => rfl) e'.val (hlift_mem e'.val e'.property)
  -- The three new edges in `(typeII G' a b c).edgeSet`.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeII G' a b c).edgeSet := by simp
  have hnewB_mem : s((none : Option V), some b) ∈ (typeII G' a b c).edgeSet := by simp
  have hnewC_mem : s((none : Option V), some c) ∈ (typeII G' a b c).edgeSet := by simp
  set newEdgeA : (typeII G' a b c).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  set newEdgeB : (typeII G' a b c).edgeSet := ⟨s(none, some b), hnewB_mem⟩ with hB_def
  set newEdgeC : (typeII G' a b c).edgeSet := ⟨s(none, some c), hnewC_mem⟩ with hC_def
  -- The three new edges are pairwise distinct.
  have hAB_ne : newEdgeA ≠ newEdgeB := fun heq =>
    hab_ne (Sym2.mk_none_some_eq_iff.mp (congrArg Subtype.val heq))
  have hAC_ne : newEdgeA ≠ newEdgeC := fun heq =>
    hac_ne (Sym2.mk_none_some_eq_iff.mp (congrArg Subtype.val heq))
  have hBC_ne : newEdgeB ≠ newEdgeC := fun heq =>
    hbc_ne (Sym2.mk_none_some_eq_iff.mp (congrArg Subtype.val heq))
  -- Cover: typeII.edgeSet ⊆ oldSet ∪ newSet.
  set oldSet : Set (typeII G' a b c).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeII G' a b c).edgeSet := {newEdgeA, newEdgeB, newEdgeC}
    with hnewSet_def
  have h_cover : (Set.univ : Set (typeII G' a b c).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeII_edgeSet] at he
    rcases he with ⟨e0, ⟨he0_mem, he0_ne⟩, h_some⟩ | h_new
    · left
      refine ⟨⟨⟨e0, he0_mem⟩, ?_⟩, ?_⟩
      · simpa using he0_ne
      · exact Subtype.ext h_some
    · right
      rcases h_new with h_eqA | h_eqB | h_eqC
      · exact Or.inl (Subtype.ext h_eqA)
      · exact Or.inr (Or.inl (Subtype.ext h_eqB))
      · exact Or.inr (Or.inr (Subtype.ext h_eqC))
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`, restricted to
  -- the subtype `≠ s(a, b)` (the deleted G'-edge).
  · rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      Subtype.val Subtype.val_injective (fun i => hlift_mem i.val i.property) h
  -- LI on `newSet = {newEdgeA, newEdgeB, newEdgeC}`: peel via `LinearIndepOn.insert`.
  · -- `{newA, newB, newC} = insert newA (insert newB (insert newC ∅))`: convert the
    -- inner `{newC}` to `insert newC ∅` so the chain of three `.insert` calls elaborates.
    rw [hnewSet_def, ← LawfulSingleton.insert_empty_eq newEdgeC]
    refine (((linearIndepOn_empty ℝ
      ((typeII G' a b c).rigidityRow p_ext)).insert ?_).insert ?_).insert ?_
    · -- `row newEdgeC ∉ span(row '' ∅) = ⊥`; i.e., `row newEdgeC ≠ 0`. Witnessed by
      -- applying the row at the motion `none ↦ q - p' c, some _ ↦ 0`.
      rw [Set.image_empty, Submodule.span_empty, Submodule.mem_bot]
      intro h_zero
      have h_apply := DFunLike.congr_fun h_zero
          (fun w : Option V => w.elim (q - p' c) (fun _ => 0))
      simp only [LinearMap.zero_apply, hp_ext_def, hC_def, rigidityRow_none_some_elim] at h_apply
      have hqc_ne := hLI.ne_zero 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hqc_ne
      exact hqc_ne (inner_self_eq_zero.mp h_apply)
    · -- `row newEdgeB ∉ span {row newEdgeC}`. Assume `c_c • row newC = row newB`; evaluate
      -- at `x_α`; the helper forces `s - 1 = 0`, contradicting `hs1`.
      simp only [Set.image_singleton, LawfulSingleton.insert_empty_eq,
        Submodule.mem_span_singleton]
      rintro ⟨c_c, hc_c⟩
      have h_motion : ∀ α : EuclideanSpace ℝ (Fin 2),
          (0 : ℝ) * ⟪q - p' a, α⟫_ℝ + 1 * ⟪q - p' b, α⟫_ℝ +
            (-c_c) * ⟪q - p' c, α⟫_ℝ = 0 := by
        intro α
        have key := DFunLike.congr_fun hc_c (fun w : Option V => w.elim α (fun _ => 0))
        simp only [LinearMap.smul_apply, smul_eq_mul, hp_ext_def, hB_def, hC_def,
          rigidityRow_none_some_elim] at key
        linarith
      obtain ⟨h1, _⟩ := typeII_new_rows_coeff_zero hs0 hcoll hLI h_motion
      apply hs1; linarith
    · -- `row newEdgeA ∉ span {row newEdgeB, row newEdgeC}`. Assume `c_b • row newB +
      -- c_c • row newC = row newA`. Apply at `x_α`: `s + (s-1)(-c_b) = 0` (so `c_b = s/(s-1)`)
      -- and `c_c = 0`. Then apply at `y` with `y(some a) = q - p' a` else `0`: LHS = 0
      -- (since `b ≠ a, c ≠ a` make the inner products vanish), RHS = `-‖q - p' a‖²`. The
      -- norm vanishing contradicts `q - p' a ≠ 0` from `hLI`.
      simp only [Set.image_insert_eq, Set.image_singleton,
        LawfulSingleton.insert_empty_eq, Submodule.mem_span_pair]
      rintro ⟨c_b, c_c, hcd⟩
      have h_motion : ∀ α : EuclideanSpace ℝ (Fin 2),
          (1 : ℝ) * ⟪q - p' a, α⟫_ℝ + (-c_b) * ⟪q - p' b, α⟫_ℝ +
            (-c_c) * ⟪q - p' c, α⟫_ℝ = 0 := by
        intro α
        have key := DFunLike.congr_fun hcd.symm
          (fun w : Option V => w.elim α (fun _ => 0))
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hp_ext_def, hA_def, hB_def, hC_def, rigidityRow_none_some_elim] at key
        linarith
      obtain ⟨_, h2⟩ := typeII_new_rows_coeff_zero hs0 hcoll hLI h_motion
      -- h2 : -c_c = 0
      have hc_c_zero : c_c = 0 := by linarith
      -- Test motion y with y(some a) = q - p' a, others 0.
      set y : Framework (Option V) 2 :=
        Function.update (0 : Framework (Option V) 2) (some a) (q - p' a) with hy_def
      have h_y_a : y (some a) = q - p' a := Function.update_self _ _ _
      have h_y_b : y (some b) = 0 := by
        rw [hy_def, Function.update_of_ne ((Option.some_injective V).ne hab_ne.symm)]
        rfl
      have h_y_c : y (some c) = 0 := by
        rw [hy_def, Function.update_of_ne ((Option.some_injective V).ne hac_ne.symm)]
        rfl
      have h_y_none : y none = 0 := by
        rw [hy_def, Function.update_of_ne (Option.some_ne_none a).symm]
        rfl
      have h_at_y := DFunLike.congr_fun hcd y
      simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hp_ext_def, hA_def, hB_def, hC_def, smul_eq_mul,
        h_y_a, h_y_b, h_y_c, h_y_none, Option.elim_none, Option.elim_some,
        zero_sub, sub_self, inner_zero_right, mul_zero,
        inner_neg_right] at h_at_y
      -- h_at_y : 0 + 0 = -⟪q - p' a, q - p' a⟫_ℝ
      have hqa_norm_zero : ⟪q - p' a, q - p' a⟫_ℝ = 0 := by linarith
      have hqa_zero : q - p' a = 0 := inner_self_eq_zero.mp hqa_norm_zero
      have hqa_ne := hLI.ne_zero 0
      simp only [Matrix.cons_val_zero] at hqa_ne
      exact hqa_ne hqa_zero
  -- Disjoint spans: any joint element vanishes at `x_α` motions, pinning `c_c = 0` and
  -- `s c_a + (s-1) c_b = 0`. Then `f = (s c_a) • restrictMap.dualMap(rowG'(s(a, b)))`
  -- (Whiteley row identity in dual form). G'-LI + `dualMap` injective then force `s c_a = 0`,
  -- hence `c_a = c_b = 0`.
  · rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    -- Decompose f along {newA, newB, newC}.
    rw [hnewSet_def, Set.image_insert_eq, Submodule.mem_span_insert] at hf_new
    obtain ⟨c_a, f_a, hf_a_mem, hf_eq_a⟩ := hf_new
    rw [Set.image_insert_eq, Submodule.mem_span_insert] at hf_a_mem
    obtain ⟨c_b, f_b, hf_b_mem, hf_eq_b⟩ := hf_a_mem
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hf_b_mem
    obtain ⟨c_c, hf_eq_c⟩ := hf_b_mem
    -- f = c_a • row newA + c_b • row newB + c_c • row newC.
    have hf_decomp : f = c_a • (typeII G' a b c).rigidityRow p_ext newEdgeA +
        c_b • (typeII G' a b c).rigidityRow p_ext newEdgeB +
        c_c • (typeII G' a b c).rigidityRow p_ext newEdgeC := by
      rw [hf_eq_a, hf_eq_b, ← hf_eq_c]; abel
    -- Old span vanishes at `x_α` motions; f does too.
    have h_zero_at_x : ∀ α : EuclideanSpace ℝ (Fin 2),
        f (fun w : Option V => w.elim α (fun _ => 0)) = 0 := by
      intro α
      have h_le := oldSpan_le_ker_eval_elim (H := typeII G' a b c) q p' α (S := oldSet)
        (by rintro _ ⟨e', rfl⟩; exact ⟨e'.val.val, rfl⟩)
      simpa using h_le hf_old
    have h_helper_eq : ∀ α : EuclideanSpace ℝ (Fin 2),
        c_a * ⟪q - p' a, α⟫_ℝ + c_b * ⟪q - p' b, α⟫_ℝ +
          c_c * ⟪q - p' c, α⟫_ℝ = 0 := by
      intro α
      have h_zero := h_zero_at_x α
      rw [hf_decomp] at h_zero
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hp_ext_def, hA_def, hB_def, hC_def, rigidityRow_none_some_elim] at h_zero
      linarith
    obtain ⟨h_ab_coeff, h_cc⟩ :=
      typeII_new_rows_coeff_zero hs0 hcoll hLI h_helper_eq
    -- f = (s * c_a) • restrictMap.dualMap (G'.rigidityRow p' ⟨s(a,b), h_ab⟩).
    -- The algebraic backbone is the row identity (`typeII_collinear_inner_combo`):
    -- `(s−1)·⟪q−p'a, ·⟫ − s·⟪q−p'b, ·⟫ = s(s−1)·⟪p'a−p'b, ·⟫`, applied with the c_a-c_b
    -- pin from `h_ab_coeff` (rewritten as `h_cb_rel : (s−1) c_b = −(s c_a)`).
    set eAB : G'.edgeSet := ⟨s(a, b), h_ab⟩ with heAB_def
    have h_cb_rel : (s - 1) * c_b = -(s * c_a) := by linarith
    have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have h_f_eq : f = (s * c_a) • restrictMap.dualMap (G'.rigidityRow p' eAB) := by
      rw [hf_decomp, h_cc, zero_smul, add_zero]
      apply LinearMap.ext
      intro x
      have h_combo := typeII_collinear_inner_combo (a := a) (b := b) hcoll x
      have h_rowAB : restrictMap.dualMap (G'.rigidityRow p' eAB) x =
          ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
        simp [rigidityRow_apply, heAB_def]
        rfl
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        rigidityRow_apply, rigidityMap_apply, hp_ext_def, hA_def, hB_def,
        Option.elim_none, Option.elim_some, h_rowAB]
      linear_combination (norm := (field_simp; ring))
        (c_a / (s - 1)) * h_combo +
          (⟪q - p' b, x none - x (some b)⟫_ℝ / (s - 1)) * h_cb_rel
    -- f ∈ span(row '' oldSet) ⊆ Submodule.map T.dualMap (span of G'-rows on subset).
    -- Show: T.dualMap(rowG'(eAB)) ∈ same map; then T-injectivity + G'-LI ⟹ s c_a = 0.
    have h_old_le : Submodule.span ℝ ((typeII G' a b c).rigidityRow p_ext '' oldSet) ≤
        Submodule.map restrictMap.dualMap
          (Submodule.span ℝ
            (G'.rigidityRow p' '' {e : G'.edgeSet | e.val ≠ s(a, b)})) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨e', rfl⟩, rfl⟩
      rw [h_factor]
      refine Submodule.mem_map.mpr ⟨G'.rigidityRow p' e'.val, ?_, rfl⟩
      exact Submodule.subset_span ⟨e'.val, e'.property, rfl⟩
    by_cases h_s_ca_zero : s * c_a = 0
    · have h_ca_zero : c_a = 0 :=
        (mul_eq_zero.mp h_s_ca_zero).resolve_left hs0
      have h_cb_zero : c_b = 0 := by
        have : (s - 1) * c_b = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hs1)
      simp [hf_decomp, h_ca_zero, h_cb_zero, h_cc]
    · exfalso
      -- T(rowG'(eAB)) = (s c_a)⁻¹ • f ∈ old span.
      have h_T_eAB_in : restrictMap.dualMap (G'.rigidityRow p' eAB) ∈
          Submodule.span ℝ ((typeII G' a b c).rigidityRow p_ext '' oldSet) := by
        have h_scalar :
            restrictMap.dualMap (G'.rigidityRow p' eAB) = (s * c_a)⁻¹ • f := by
          simp only [h_f_eq, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ h_s_ca_zero, one_smul]
        rw [h_scalar]
        exact Submodule.smul_mem _ _ hf_old
      -- ... ⊆ T-image of subset span. Extract g_inner.
      obtain ⟨g_inner, hg_inner_mem, hg_inner_eq⟩ :=
        Submodule.mem_map.mp (h_old_le h_T_eAB_in)
      have h_dualMap_inj : Function.Injective restrictMap.dualMap :=
        LinearMap.dualMap_injective_of_surjective h_restrict_surj
      have h_g_eq : g_inner = G'.rigidityRow p' eAB :=
        h_dualMap_inj hg_inner_eq
      rw [h_g_eq] at hg_inner_mem
      have h_li_G' : LinearIndependent ℝ (G'.rigidityRow p') := by
        rw [← linearIndepOn_univ_iff,
            ← edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
        exact h
      have h_eAB_notin : eAB ∉ {e : G'.edgeSet | e.val ≠ s(a, b)} := by
        simp [heAB_def]
      exact h_li_G'.notMem_span_image h_eAB_notin hg_inner_mem

/-! ### Type II row-LI lift, unconditional wrapper

Row-LI analogue of `typeII_isGenericallyRigidInj_two` minus the
injectivity-preservation half. The non-collinearity gap on `(p' a, p' b, p' c)` is discharged
by moving `p' c` off the line through `p' a, p' b` (preserving row-LI of `G'` via
`EdgeSetRowIndependent.eventually`), after which the collinearity scalar `s = 1/2` recovers
the conditional core. -/

/-- **Existence of a non-collinear row-independent placement in dim 2.** Given a placement `p₀`
of `G'` at which every edge of `G'` is row-independent, an edge `G'.Adj a b`, and a third vertex
`c` with `a ≠ c, b ≠ c`, there exists a placement `p` of `V` with `G'`-row-LI at `p` and
`(p a, p b, p c)` non-collinear, i.e. `LinearIndependent ℝ ![p b - p a, p c - p a]`.

Row-LI analogue of `exists_nonCollinear_rigid_placement_dim_two`. The non-zero
direction `p₀ b - p₀ a ≠ 0` is supplied by `h_ab` plus row-LI (a zero row at the edge `s(a, b)`
would contradict LI), and row-LI of `G'` is preserved on a neighborhood of `t = 0` by
`EdgeSetRowIndependent.eventually` pulled back through continuity of the perturbation; the
shared core `exists_nonCollinear_update_perturbation_dim_two` selects a `t ≠ 0` that also gives
non-collinearity. -/
private lemma exists_nonCollinear_rowIndependent_placement_dim_two [Finite V]
    {G' : SimpleGraph V} {p₀ : Framework V 2}
    (h : G'.EdgeSetRowIndependent p₀ Set.univ)
    {a b c : V} (h_ab : G'.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework V 2, G'.EdgeSetRowIndependent p Set.univ ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  classical
  -- `p₀ a ≠ p₀ b` from row-LI: the row at `s(a, b)` would be zero, contradicting LI.
  have h_row_ab_ne : G'.rigidityRow p₀ ⟨s(a, b), h_ab⟩ ≠ 0 := by
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow] at h
    exact h.ne_zero (Set.mem_univ _)
  have hab_distinct : p₀ a ≠ p₀ b := by
    intro heq
    apply h_row_ab_ne
    refine LinearMap.ext fun motion => ?_
    exact (rigidityMap_apply G' p₀ motion a b h_ab).trans (by simp [heq])
  have hd_ne_zero : p₀ b - p₀ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab_distinct)
  obtain ⟨w, hw_outside⟩ := exists_not_mem_span_singleton_dim_two hd_ne_zero
  -- Row-LI preservation along the `Function.update`-perturbation, by continuity.
  have h_p_t_cont : Continuous
      (fun t : ℝ => Function.update p₀ c (p₀ c + t • w)) := by fun_prop
  have h_p_t_zero : Function.update p₀ c (p₀ c + (0 : ℝ) • w) = p₀ := by
    simp
  have h_rowLI_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      G'.EdgeSetRowIndependent (Function.update p₀ c (p₀ c + t • w)) Set.univ := by
    have h_ev_p := h.eventually
    rw [← h_p_t_zero] at h_ev_p
    exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
  exact exists_nonCollinear_update_perturbation_dim_two
    (P := fun p => G'.EdgeSetRowIndependent p Set.univ)
    hac hbc hd_ne_zero w hw_outside h_rowLI_ev

/-- **Unconditional Type II row-LI lift in dim 2.** Given a placement `p'` of `G'` at which every
edge of `G'` is row-independent, an edge `G'.Adj a b`, and a third vertex `c` with `a ≠ c, b ≠ c`,
there exists an extended placement `p : Framework (Option V) 2` at which every edge of
`typeII G' a b c` is row-independent.

Row-LI analogue of `typeII_isGenericallyRigidInj_two` minus the injectivity. The proof
passes the input through `exists_nonCollinear_rowIndependent_placement_dim_two` to obtain a
placement `p''` at which `(p'' a, p'' b, p'' c)` is non-collinear (moving `p' c` off the line
through `p' a, p' b` if needed; row-LI openness via `EdgeSetRowIndependent.eventually`
preserves row-LI through the perturbation). With the non-collinear placement in hand, pick
`s = 1/2` and set `q := p'' a + s • (p'' b - p'' a)`; the conditional core
`typeII_edgeSetRowIndependent_extend` then applies. Unlike the Type I lift, the conclusion does
*not* state `p ∘ some = p'`, because the helper may have perturbed `p'` itself. -/
theorem typeII_edgeSetRowIndependent_lift [Finite V] {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b c : V} (h_ab : G'.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework (Option V) 2,
      (typeII G' a b c).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨p'', hp''_rowLI, hp''_LI⟩ :=
    exists_nonCollinear_rowIndependent_placement_dim_two h h_ab hac hbc
  set s : ℝ := 1 / 2 with hs_def
  set q : EuclideanSpace ℝ (Fin 2) := p'' a + s • (p'' b - p'' a) with hq_def
  have hs0 : s ≠ 0 := by norm_num [hs_def]
  have hs1 : s ≠ 1 := by norm_num [hs_def]
  have hcoll : q - p'' a = s • (p'' b - p'' a) := by simp [hq_def]
  have hLI : LinearIndependent ℝ ![q - p'' a, q - p'' c] := by
    have h_form :
        (![q - p'' a, q - p'' c] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![s • (p'' b - p'' a) + (0 : ℝ) • (p'' c - p'' a),
            s • (p'' b - p'' a) + (-1 : ℝ) • (p'' c - p'' a)] := by
      funext i
      fin_cases i
      · change q - p'' a = s • (p'' b - p'' a) + (0 : ℝ) • (p'' c - p'' a)
        rw [hcoll, zero_smul, add_zero]
      · change q - p'' c = s • (p'' b - p'' a) + (-1 : ℝ) • (p'' c - p'' a)
        have hqc : q - p'' c = (q - p'' a) - (p'' c - p'' a) := by abel
        simp only [hqc, hcoll, neg_smul, one_smul, sub_eq_add_neg]
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨hp''_LI, ?_⟩
    simp [hs0]
  exact ⟨fun w : Option V => w.elim q p'',
    typeII_edgeSetRowIndependent_extend hp''_rowLI h_ab hs0 hs1 hcoll hLI⟩

/-- **Existence of a row-independent placement separating two vertices in dim 2.** Given a
placement `p₀` of `G'` at which every edge of `G'` is row-independent and two distinct vertices
`a, b`, there exists a row-LI placement `p` with `p a ≠ p b`. If `p₀ a ≠ p₀ b` already, return
`p₀`; otherwise perturb `p₀ a` by `t • v` for `v ≠ 0` and small `t ≠ 0`, preserving row-LI via
`EdgeSetRowIndependent.eventually`. The Type I branch of the induction on `|V|`
(`IsSparse.exists_rowIndependent_placement`) feeds this to `typeI_edgeSetRowIndependent_lift`
(which requires `p' a ≠ p' b`). -/
private lemma exists_distinct_rowIndependent_placement_dim_two [Finite V]
    {G' : SimpleGraph V} {p₀ : Framework V 2}
    (h : G'.EdgeSetRowIndependent p₀ Set.univ) {a b : V} (hab : a ≠ b) :
    ∃ p : Framework V 2, G'.EdgeSetRowIndependent p Set.univ ∧ p a ≠ p b := by
  classical
  by_cases hab_p : p₀ a = p₀ b
  · -- Collapsed branch: perturb `p₀ a` by `t • v` with `v ≠ 0` and small `t ≠ 0`.
    obtain ⟨v, hv_ne⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
    set p_t : ℝ → Framework V 2 := fun t => Function.update p₀ a (p₀ a + t • v)
      with hp_t_def
    have h_p_t_a : ∀ t, p_t t a = p₀ a + t • v := fun _ => Function.update_self a _ p₀
    have h_p_t_b : ∀ t, p_t t b = p₀ b :=
      fun _ => Function.update_of_ne hab.symm _ p₀
    have h_p_t_cont : Continuous p_t := by fun_prop
    have h_p_t_zero : p_t 0 = p₀ := by
      funext x
      change Function.update p₀ a (p₀ a + (0 : ℝ) • v) x = p₀ x
      by_cases hxa : x = a
      · rw [hxa, Function.update_self]; simp
      · rw [Function.update_of_ne hxa]
    have h_rowLI_ev : ∀ᶠ t in 𝓝 (0 : ℝ), G'.EdgeSetRowIndependent (p_t t) Set.univ := by
      have h_ev_p := h.eventually
      rw [← h_p_t_zero] at h_ev_p
      exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
    have h_diff : ∀ t : ℝ, t ≠ 0 → p_t t a ≠ p_t t b := by
      intro t ht_ne hp_eq
      rw [h_p_t_a, h_p_t_b, ← hab_p, add_eq_left, smul_eq_zero] at hp_eq
      exact hp_eq.elim ht_ne hv_ne
    have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        G'.EdgeSetRowIndependent (p_t t) Set.univ ∧ t ≠ 0 := by
      filter_upwards [h_rowLI_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with t hrow ht_ne
      exact ⟨hrow, ht_ne⟩
    obtain ⟨t, hrow, ht_ne⟩ := h_combined.exists
    exact ⟨p_t t, hrow, h_diff t ht_ne⟩
  · exact ⟨p₀, h, hab_p⟩

end Henneberg

/-! ### Induction on `|V|`: every sparse graph has a row-independent placement

The harder half of Pollaczek-Geiringer's and Laman's characterization (Jordán 2016, Theorem
2.2.1): in dimension 2, every `(2, 3)`-sparse graph admits a placement at which its edge set is
row-independent. The proof is strong induction on `Fintype.card V`: each Henneberg reverse
strictly decreases `card V`, and the corresponding row-LI lift (pendant / Type I / Type II)
reconstructs a placement of the larger graph. -/

/-- **Sparse ⇒ row-independent at some placement, dim 2.** Every `(2, 3)`-sparse graph `H` on a
finite vertex set admits a placement `p : Framework V 2` at which the entire edge set of `H` is
row-independent.

The harder half of Pollaczek-Geiringer's and Laman's characterization (Jordán 2016, Theorem
2.2.1), by Jordán's induction (p. 45), here on `Fintype.card V` rather than on `|E|`. Base
case: when `H.edgeSet` is empty (in particular when `card V ≤ 1`), the empty family of rows is
linearly independent at any placement. Inductive step: apply
`IsSparse.exists_typeI_or_typeII_reverse` to obtain a vertex `v` with `H.degree v ∈ {1, 2, 3}`
and a smaller sparse graph `H'` on `{w // w ≠ v}` via one of three Henneberg
reverses (pendant / Type I / Type II). The IH gives a row-LI placement `p'` of `H'`; in each
branch, the corresponding row-LI lift (`typeI_pendant_edgeSetRowIndependent_lift` /
`typeI_edgeSetRowIndependent_lift` / `typeII_edgeSetRowIndependent_lift`) reconstructs a
row-LI placement of the Henneberg extension `typeI H' a a` (or `typeI H' a b`, or
`typeII H' x y c`), and `EdgeSetRowIndependent.iso` transports back to `H` via the iso from
`Henneberg.isoTypeIOfTwoNeighbors` / `Henneberg.isoTypeIIOfThreeNeighbors`. The Type I
branch additionally feeds `p'` through `exists_distinct_rowIndependent_placement_dim_two` to
ensure `p' a ≠ p' b` (the LI hypothesis of `typeI_edgeSetRowIndependent_lift`). -/
theorem IsSparse.exists_rowIndependent_placement :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {H : SimpleGraph V}, H.IsSparse 2 3 →
        ∃ p : Framework V 2, H.EdgeSetRowIndependent p Set.univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV H h
    classical
    by_cases hE : H.edgeSet.Nonempty
    · -- Inductive step: apply the flat-form sparse reverse, reconstruct the iso to
      -- `typeI H' a b` / `typeI H' a a` / `typeII H' x y c` via the iso constructors in
      -- `HennebergReverse.lean`, then apply IH + row-LI lift + iso transport.
      obtain ⟨v, hbranch⟩ := h.exists_typeI_or_typeII_reverse hE
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_hdeg, a, hN_iff, hG'sparse⟩ |
        ⟨_hdeg, a, b, hab, hN_iff, hG'sparse⟩ |
        ⟨_hdeg, x, y, c, hxy, hcx, hcy, hN_iff, hnxy, hG'sparse⟩
      · -- Pendant branch (degree 1): the unique neighbour `a` of `v` is exposed.
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        obtain ⟨p_lift, _hp_lift_some, hp_lift_LI⟩ :=
          Henneberg.typeI_pendant_edgeSetRowIndependent_lift hp' a
        have ha_adj : H.Adj v a.val := (hN_iff a.val).mpr rfl
        have hN_iff_aa : ∀ w : V, H.Adj v w ↔ w = a.val ∨ w = a.val := fun w => by
          rw [hN_iff]; tauto
        have φ : H ≃g Henneberg.typeI (H.comap (Subtype.val : {w : V // w ≠ v} → V)) a a :=
          Henneberg.isoTypeIOfTwoNeighbors (H.ne_of_adj ha_adj) (H.ne_of_adj ha_adj)
            hN_iff_aa
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
      · -- Type I branch (degree 2): two distinct neighbours `a ≠ b` of `v`.
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        obtain ⟨p'', hp'', hp''_ne⟩ :=
          Henneberg.exists_distinct_rowIndependent_placement_dim_two hp' hab
        obtain ⟨p_lift, _hp_lift_some, hp_lift_LI⟩ :=
          Henneberg.typeI_edgeSetRowIndependent_lift hp'' hp''_ne
        have ha_adj : H.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
        have hb_adj : H.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
        have φ : H ≃g Henneberg.typeI (H.comap (Subtype.val : {w : V // w ≠ v} → V)) a b :=
          Henneberg.isoTypeIOfTwoNeighbors (H.ne_of_adj ha_adj) (H.ne_of_adj hb_adj)
            hN_iff
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
      · -- Type II branch (degree 3): three neighbours `x, y, c` with non-adj `(x, y)`.
        set H' : SimpleGraph {w : V // w ≠ v} :=
          H.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _) with hH'_def
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        have h_bridge : H'.Adj x y := by
          rw [hH'_def, sup_adj]
          exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
        obtain ⟨p_lift, hp_lift_LI⟩ :=
          Henneberg.typeII_edgeSetRowIndependent_lift hp' h_bridge hcx.symm hcy.symm
        have φ : H ≃g Henneberg.typeII H' x y c :=
          Henneberg.isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm
            hN_iff hnxy
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
    · -- Base case: `H.edgeSet = ∅`, the empty family of rows is LI.
      rw [Set.not_nonempty_iff_eq_empty] at hE
      have : IsEmpty (H.edgeSet : Type _) := Set.isEmpty_coe_sort.mpr hE
      refine ⟨0, ?_⟩
      rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff]
      exact linearIndependent_empty_type

/-! ### Row-independent iff `(2, 3)`-sparse, dim 2

Combining the necessity half `isSparse_of_edgeSetRowIndependent_dim_two` with the
sufficiency half `IsSparse.exists_rowIndependent_placement` yields the characterization of
Pollaczek-Geiringer and Laman in dimension 2 (Jordán 2016, Theorem 2.2.1): an edge subset of
`G` is row-independent at some placement iff its spanning subgraph is `(2, 3)`-sparse. -/

/-- **Row-LI iff `(2, 3)`-sparse, dim 2** (Pollaczek-Geiringer, Laman). Let `V` be finite and
`G : SimpleGraph V`. An edge set `I ⊆ G.edgeSet` is row-independent at some placement
`p : Framework V 2` iff the spanning subgraph of `G` with edge set `I` (i.e.
`fromEdgeSet (Subtype.val '' I)`) is `(2, 3)`-sparse.

The matroid identification of the planar rigidity matroid with the `(2, 3)`-count matroid on
`E(K_V)`. The `(⇒)` direction perturbs the row-LI witness to an affinely-spanning placement via
`exists_affinelySpanning_of_eventually` (at row-LI's openness, `EdgeSetRowIndependent.eventually`),
then applies the necessity half `isSparse_of_edgeSetRowIndependent_dim_two`. The `(⇐)`
direction is `IsSparse.exists_rowIndependent_placement` on the spanning subgraph
`H := fromEdgeSet (Subtype.val '' I)`, followed by a bridge from
`H.EdgeSetRowIndependent p Set.univ` to `G.EdgeSetRowIndependent p I`: the natural reindex
`I → H.edgeSet`, `e_I ↦ ⟨e_I.val.val, …⟩`, is injective, and the rigidity rows at corresponding
edges coincide (both reduce to `⟪p u - p v, motion u - motion v⟫_ℝ` on the same `Sym2`-value), so
LI transports via `LinearIndependent.comp`. -/
theorem edgeSet_rowIndependent_iff_isSparse_dim_two {V : Type*} [Finite V]
    (G : SimpleGraph V) (I : Set G.edgeSet) :
    (∃ p : Framework V 2, G.EdgeSetRowIndependent p I) ↔
      (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsSparse 2 3 := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨?_, ?_⟩
  · -- (⇒) Perturb the row-LI witness to be affinely-spanning, then apply the easy direction.
    rintro ⟨p, hp⟩
    obtain ⟨p', hp'_LI, hp'_aff⟩ := exists_affinelySpanning_of_eventually hp.eventually
    exact isSparse_of_edgeSetRowIndependent_dim_two hp'_aff hp'_LI
  · -- (⇐) Apply the hard direction on the spanning subgraph, then bridge LI back to `G` on `I`.
    intro hSparse
    set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
    have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
      rw [hH_def, edgeSet_fromEdgeSet]
      refine sdiff_eq_left.mpr ?_
      rw [Set.disjoint_left]
      rintro e ⟨e', _, rfl⟩ he_diag
      exact not_isDiag_of_mem_edgeSet G e'.property he_diag
    obtain ⟨p, hp⟩ := IsSparse.exists_rowIndependent_placement _ rfl hSparse
    refine ⟨p, ?_⟩
    -- Reindex `I → H.edgeSet`, `e_I ↦ e_I.val.val`, injective.
    let toH : I → H.edgeSet := fun e_I =>
      ⟨e_I.val.val, by rw [hH_edgeSet]; exact ⟨e_I.val, e_I.property, rfl⟩⟩
    have htoH_inj : Function.Injective toH := by
      intro a b hab
      have h1 : (toH a).val = (toH b).val := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
        linearIndepOn_univ_iff] at hp
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
    -- `LinearIndepOn ℝ (G.rigidityRow p) I` unfolds to subtype LI; `G`- and `H`-rows at
    -- corresponding edges are definitionally equal (both reduce through `Sym2.lift` to the
    -- same `edgeRow p (u, v)` on the same `Sym2`-value), so `hp.comp toH htoH_inj` closes the
    -- goal up to that defeq.
    exact hp.comp toH htoH_inj


end SimpleGraph

end
end BundleSource0028

section BundleSource0029
/- Source: Papers/RigidityNeighborhoodBases.lean -/





@[expose] public section

/-!
# Independence of neighborhood bases on distinct incident bodies

The proof uses a literal minimal non-sparse subgraph, its Laman rigid
support, coning, and maximality of actual rigid cliques. No decomposition
of the planar rigidity matroid is assumed. This is the independence step
of Lemma 3.2; the input graphs may be any sparse graphs on the respective
body deletions, so in particular they may be planar rigidity bases.

The construction retains the original graph and its body deletions.
-/

namespace Papers.Rigidity.NeighborhoodBases

noncomputable section

open scoped Classical BigOperators

variable {V : Type} [Fintype V]

theorem body_absorbs_clique (C : MinimalCounterexample V) (T U : Finset V)
    (hT : IsBody C.graph T) (hU : C.graph.IsClique (U : Set V))
    (hcommon : 3 ≤ (T ∩ U).card) : U ⊆ T := by
  have hcluster := rigidCluster_union_of_cliques C.graph T U hT.2.1 hU hcommon
  have hcard : 4 ≤ (T ∪ U).card :=
    hT.1.trans (Finset.card_le_card Finset.subset_union_left)
  have hclique := C.rigidCluster_isClique (T ∪ U) hcard hcluster
  exact Finset.subset_union_right.trans (hT.2.2 (T ∪ U) Finset.subset_union_left hclique)

theorem three_common_of_members {T U : Finset V} {v x y : V}
    (hvT : v ∈ T) (hxT : x ∈ T) (hyT : y ∈ T)
    (hvU : v ∈ U) (hxU : x ∈ U) (hyU : y ∈ U)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    3 ≤ (T ∩ U).card := by
  have hsub : ({v, x, y} : Finset V) ⊆ T ∩ U := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hvT, hvU⟩
    · exact Finset.mem_inter.mpr ⟨hxT, hxU⟩
    · exact Finset.mem_inter.mpr ⟨hyT, hyU⟩
  have hc : ({v, x, y} : Finset V).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hvx, hvy, hxy⟩
  simpa only [hc] using Finset.card_le_card hsub

/-- The union of sparse graphs supported on distinct body deletions is
sparse. Every support and every edge here belongs to the actual graph. -/
theorem union_isSparse (C : MinimalCounterexample V) (v : V)
    {ι : Type} [Fintype ι] (T : ι → Finset V) (B : ι → SimpleGraph V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody C.graph (T i)) (hv : ∀ i, v ∈ T i)
    (hB : ∀ i, (B i).IsSparse 2 3)
    (hedges : ∀ i, (B i).edgeSet ⊆ C.graph.edgesIn ((T i).erase v : Set V)) :
    (⨆ i, B i).IsSparse 2 3 := by
  classical
  let U : SimpleGraph V := ⨆ i, B i
  have hUG : U ≤ C.graph := by
    intro x y hxy
    obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hxy
    exact (hedges i ((SimpleGraph.mem_edgeSet (B i)).mpr hi)).1
  have hUN : U.support ⊆ (C.graph.neighborFinset v : Set V) := by
    intro x hx
    obtain ⟨y, hxy⟩ := U.mem_support.mp hx
    obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hxy
    have hinside := (SimpleGraph.mem_edgesIn.mp (hedges i ((SimpleGraph.mem_edgeSet (B i)).mpr hi))).2
    have hxTi : x ∈ (T i).erase v := hinside (Sym2.mem_mk_left x y)
    apply (C.graph.mem_neighborFinset v x).mpr
    exact (hT i).2.1 (hv i) (Finset.mem_erase.mp hxTi).2
      (Finset.mem_erase.mp hxTi).1.symm
  by_contra hnon
  obtain ⟨H, hHU, hHnon, hHmin⟩ := PlanarCircuit.exists_minimal_nonSparse U hnon
  obtain ⟨S, hScard, hSedges, hSclique⟩ :=
    PlanarCircuit.exists_clique_cone_support C v H (hHU.trans hUG)
      ((SimpleGraph.support_mono hHU).trans hUN) hHnon hHmin
  have hHne : H ≠ ⊥ := by
    intro h
    exact hHnon (h.symm ▸ SimpleGraph.bot_isSparse 2 3)
  obtain ⟨x, y, hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hHne
  obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp (hHU hxy)
  have hxyIn := SimpleGraph.mem_edgesIn.mp (hedges i ((SimpleGraph.mem_edgeSet (B i)).mpr hi))
  have hxTi := Finset.mem_erase.mp (hxyIn.2 (Sym2.mem_mk_left x y))
  have hyTi := Finset.mem_erase.mp (hxyIn.2 (Sym2.mem_mk_right x y))
  have hxyS : s(x, y) ∈ H.edgesIn (S : Set V) := by
    rw [hSedges]
    exact hxy
  have hxS : x ∈ S := (SimpleGraph.mem_edgesIn.mp hxyS).2 (Sym2.mem_mk_left x y)
  have hyS : y ∈ S := (SimpleGraph.mem_edgesIn.mp hxyS).2 (Sym2.mem_mk_right x y)
  have hSi : S ⊆ T i := by
    apply Finset.Subset.trans (Finset.subset_insert v S)
    apply body_absorbs_clique C (T i) (insert v S) (hT i) hSclique
    exact three_common_of_members (hv i) hxTi.2 hyTi.2
      (Finset.mem_insert_self v S) (Finset.mem_insert_of_mem hxS)
      (Finset.mem_insert_of_mem hyS) hxTi.1.symm hyTi.1.symm hxy.ne
  have hHBi : H ≤ B i := by
    intro a b hab
    obtain ⟨j, hj⟩ := SimpleGraph.iSup_adj.mp (hHU hab)
    have hjinside := SimpleGraph.mem_edgesIn.mp (hedges j ((SimpleGraph.mem_edgeSet (B j)).mpr hj))
    have haTj := Finset.mem_erase.mp (hjinside.2 (Sym2.mem_mk_left a b))
    have hbTj := Finset.mem_erase.mp (hjinside.2 (Sym2.mem_mk_right a b))
    have habS : s(a, b) ∈ H.edgesIn (S : Set V) := by
      rw [hSedges]
      exact hab
    have haS : a ∈ S := (SimpleGraph.mem_edgesIn.mp habS).2 (Sym2.mem_mk_left a b)
    have hbS : b ∈ S := (SimpleGraph.mem_edgesIn.mp habS).2 (Sym2.mem_mk_right a b)
    have hcommon : 3 ≤ (T i ∩ T j).card :=
      three_common_of_members (hv i) (hSi haS) (hSi hbS)
        (hv j) haTj.2 hbTj.2 haTj.1.symm hbTj.1.symm hab.ne
    have hTij : T i = T j := by
      by_contra hne
      have hsmall := C.body_intersection_le_two (T i) (T j) (hT i) (hT j) hne
      omega
    have hij : i = j := hTinj hTij
    simpa only [← hij] using hj
  exact hHnon (SimpleGraph.IsSparse.mono_left hHBi (hB i))

/-- Literal simultaneous independence of the union's rigidity rows. The
complete planar sparse/row-independence theorem supplies the placement. -/
theorem union_rows_independent (C : MinimalCounterexample V) (v : V)
    {ι : Type} [Fintype ι] (T : ι → Finset V) (B : ι → SimpleGraph V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody C.graph (T i)) (hv : ∀ i, v ∈ T i)
    (hB : ∀ i, (B i).IsSparse 2 3)
    (hedges : ∀ i, (B i).edgeSet ⊆ C.graph.edgesIn ((T i).erase v : Set V)) :
    ∃ p : SimpleGraph.Framework V 2,
      (⨆ i, B i).EdgeSetRowIndependent p Set.univ :=
  SimpleGraph.IsSparse.exists_rowIndependent_placement (Fintype.card V) rfl
    (union_isSparse C v T B hTinj hT hv hB hedges)

/-- Distinct incident bodies have disjoint sets of edges avoiding the
common vertex. This is about edge occurrences, not disjoint vertices. -/
theorem pairwise_disjoint_edges (C : MinimalCounterexample V) (v : V)
    {ι : Type} (T : ι → Finset V) (B : ι → SimpleGraph V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody C.graph (T i)) (hv : ∀ i, v ∈ T i)
    (hedges : ∀ i, (B i).edgeSet ⊆ C.graph.edgesIn ((T i).erase v : Set V)) :
    Pairwise (fun i j => Disjoint (B i).edgeSet (B j).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e with
  | h x y =>
    have hi := SimpleGraph.mem_edgesIn.mp (hedges i hei)
    have hj := SimpleGraph.mem_edgesIn.mp (hedges j hej)
    have hxi := Finset.mem_erase.mp (hi.2 (Sym2.mem_mk_left x y))
    have hyi := Finset.mem_erase.mp (hi.2 (Sym2.mem_mk_right x y))
    have hxj := Finset.mem_erase.mp (hj.2 (Sym2.mem_mk_left x y))
    have hyj := Finset.mem_erase.mp (hj.2 (Sym2.mem_mk_right x y))
    have hcommon : 3 ≤ (T i ∩ T j).card :=
      three_common_of_members (hv i) hxi.2 hyi.2 (hv j) hxj.2 hyj.2
        hxi.1.symm hyi.1.symm ((SimpleGraph.mem_edgeSet C.graph).mp hi.1).ne
    have hsmall := C.body_intersection_le_two (T i) (T j) (hT i) (hT j)
      (fun h => hij (hTinj h))
    omega

/-- The numerical assertion of Lemma 3.2 for any actual selected planar
bases. `hcount` is their literal Laman basis cardinality, not a surrogate
for the desired overlap inequality. -/
theorem basis_overlap_inequality (C : MinimalCounterexample V) (v : V)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (T : ι → Finset V) (B : ι → SimpleGraph V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody C.graph (T i)) (hv : ∀ i, v ∈ T i)
    (hB : ∀ i, (B i).IsSparse 2 3)
    (hedges : ∀ i, (B i).edgeSet ⊆ C.graph.edgesIn ((T i).erase v : Set V))
    (hcount : ∀ i, (B i).edgeSet.ncard + 3 = 2 * ((T i).erase v).card) :
    2 * ((∑ i, ((T i).erase v).card) -
      (Finset.univ.biUnion (fun i => (T i).erase v)).card) ≤
        3 * Fintype.card ι - 3 := by
  classical
  let U : SimpleGraph V := ⨆ i, B i
  let N : Finset V := Finset.univ.biUnion (fun i => (T i).erase v)
  have hsparse := union_isSparse C v T B hTinj hT hv hB hedges
  have hNinside : U.edgesIn (N : Set V) = U.edgeSet := by
    apply Set.inter_eq_left.mpr
    intro e he
    rw [SimpleGraph.edgeSet_iSup] at he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    apply Set.mem_sym2_iff_subset.mpr
    intro w hw
    have hwTi := (SimpleGraph.mem_edgesIn.mp (hedges i hi)).2 hw
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hwTi⟩
  have hNcard : 3 ≤ N.card := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    have hsub : (T i).erase v ⊆ N := by
      intro w hw
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hw⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (hv i)] at hc
    have ht := (hT i).1
    omega
  have hbound := hsparse N (by omega)
  change (U.edgesIn (N : Set V)).ncard + 3 ≤ 2 * N.card at hbound
  rw [hNinside] at hbound
  have hsumEdges : U.edgeSet.ncard = ∑ i, (B i).edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_iSup]
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun i => (B i).edgeSet.toFinite)
        (pairwise_disjoint_edges C v T B hTinj hT hv hedges)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hcount i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  change (∑ i, (B i).edgeSet.ncard) + Fintype.card ι * 3 =
    2 * (∑ i, ((T i).erase v).card) at hsum
  rw [hsumEdges] at hbound
  have hpositive : 0 < Fintype.card ι := Fintype.card_pos
  change 2 * ((∑ i, ((T i).erase v).card) - N.card) ≤ 3 * Fintype.card ι - 3
  omega

end

end Papers.Rigidity.NeighborhoodBases

end
end BundleSource0029

section BundleSource0030
/- Source: Papers/RigidityPlanarBasisExistence.lean -/



@[expose] public section

/-!
# Actual planar bases in the incident cliques

Henneberg type-I extensions construct a Laman graph on every finite
vertex set of cardinality at least two. Mapping it into a clique keeps
its literal edge set, sparsity, and cardinality. Thus no existence of a
neighborhood rigidity basis is left as an extra premise in Lemma 3.2.

The basis is constructed from the actual neighborhood graph.
-/

namespace Papers.Rigidity.NeighborhoodBases

noncomputable section

open scoped Classical BigOperators

theorem exists_laman_fin_add_two : ∀ m : ℕ,
    ∃ H : SimpleGraph (Fin (m + 2)), H.IsLaman := by
  intro m
  induction m with
  | zero => exact ⟨⊤, SimpleGraph.top_fin_two_isLaman⟩
  | succ m ih =>
    obtain ⟨H, hH⟩ := ih
    let a : Fin (m + 2) := ⟨0, by omega⟩
    let b : Fin (m + 2) := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = 1 at hv
      omega
    let J := SimpleGraph.Henneberg.typeI H a b
    have hJ : J.IsLaman := SimpleGraph.Henneberg.typeI_isLaman hH hab
    let e : Option (Fin (m + 2)) ≃ Fin (m + 1 + 2) :=
      Fintype.equivOfCardEq (by simp <;> omega)
    exact ⟨J.map e.toEmbedding, SimpleGraph.IsLaman.iso (SimpleGraph.Iso.map e J) hJ⟩

theorem exists_laman (V : Type) [Fintype V] (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H.IsLaman := by
  classical
  obtain ⟨H, hH⟩ := exists_laman_fin_add_two (Fintype.card V - 2)
  let e : Fin (Fintype.card V - 2 + 2) ≃ V :=
    Fintype.equivOfCardEq (by simp <;> omega)
  exact ⟨H.map e.toEmbedding, SimpleGraph.IsLaman.iso (SimpleGraph.Iso.map e H) hH⟩

/-- Isolated ambient vertices do not affect planar sparsity. This is
proved from actual edge selectors and their injective image cardinality. -/
theorem sparse_map_embedding {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (hH : H.IsSparse 2 3) (f : W ↪ V) :
    (H.map f).IsSparse 2 3 := by
  classical
  intro U hU
  let T : Finset W := Finset.univ.filter (fun w => f w ∈ U)
  have hcardT : Fintype.card (T : Set W) = T.card :=
    @Fintype.card_coe W T (inferInstance : Fintype (T : Set W))
  have himage : T.image f ⊆ U := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hw).2
  have hcard : T.card ≤ U.card := by
    rw [← Finset.card_image_of_injective T f.injective]
    exact Finset.card_le_card himage
  have hedge : (H.map f).edgesIn (U : Set V) =
      (H.map f).edgesIn ((T.image f : Finset V) : Set V) := by
    apply Set.Subset.antisymm
    · intro e he
      induction e with
      | h x y =>
        have hxy := SimpleGraph.mem_edgesIn.mp he
        obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj f H _ _).mp hxy.1
        have haT : a ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ a, hxy.2 (Sym2.mem_mk_left (f a) (f b))⟩
        have hbT : b ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ b, hxy.2 (Sym2.mem_mk_right (f a) (f b))⟩
        exact SimpleGraph.mk_mem_edgesIn hxy.1
          (Finset.mem_image.mpr ⟨a, haT, rfl⟩)
          (Finset.mem_image.mpr ⟨b, hbT, rfl⟩)
    · exact SimpleGraph.edgesIn_mono himage
  have hcount : (H.edgesIn (T : Set W)).ncard =
      ((H.map f).edgesIn ((T.image f : Finset V) : Set V)).ncard := by
    simpa only [SimpleGraph.comap_map_eq] using
      (H.map f).ncard_edgesIn_comap f.injective T
  rw [hedge, ← hcount]
  by_cases hT : 3 ≤ 2 * T.card
  · exact (hH T hT).trans (Nat.mul_le_mul_left 2 hcard)
  · have hsmall : T.card < 2 := by omega
    have hcap : (H.edgesIn (T : Set W)).ncard ≤ T.card.choose 2 := by
      rw [SimpleGraph.ncard_edgesIn_eq_ncard_induce_edgeSet]
      have h := Set.ncard_le_ncard
        (SimpleGraph.edgeSet_mono
          (show H.induce (T : Set W) ≤ ⊤ from le_top))
      simpa only [SimpleGraph.ncard_edgeSet_top_eq_card_choose_two, hcardT] using h
    rw [Nat.choose_eq_zero_of_lt hsmall] at hcap
    omega

/-- A clique has a literal sparse spanning edge basis of the planar
rigidity matrix, with exactly `2 |S| - 3` edges. -/
theorem exists_basis_on_clique {V : Type} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hS : 2 ≤ S.card) (hclique : G.IsClique (S : Set V)) :
    ∃ B : SimpleGraph V, B.IsSparse 2 3 ∧ B.edgeSet ⊆ G.edgesIn (S : Set V) ∧
      B.edgeSet.ncard + 3 = 2 * S.card := by
  classical
  have hcardS : Fintype.card (S : Set V) = S.card :=
    @Fintype.card_coe V S (inferInstance : Fintype (S : Set V))
  obtain ⟨H, hH⟩ := exists_laman (S : Set V) (by rw [hcardS]; exact hS)
  let e : (S : Set V) ↪ V := Function.Embedding.subtype _
  refine ⟨H.map e, sparse_map_embedding H hH.1 e, ?_, ?_⟩
  · intro a ha
    induction a with
    | h x y =>
      obtain ⟨xS, yS, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj e H _ _).mp ha
      exact SimpleGraph.mk_mem_edgesIn
        (hclique xS.property yS.property (e.injective.ne hxy.ne)) xS.property yS.property
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ e.sym2Map.injective]
    simpa only [Nat.card_eq_fintype_card, hcardS] using hH.2

/-- Full numerical Lemma 3.2: there is no supplied basis or sparsity
hypothesis. A nonempty finite family of distinct bodies through `v`
satisfies the paper's exact overlap bound. -/
theorem lemma_three_two {V : Type} [Fintype V] (C : MinimalCounterexample V) (v : V)
    {ι : Type} [Fintype ι] [Nonempty ι] (T : ι → Finset V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody C.graph (T i)) (hv : ∀ i, v ∈ T i) :
    2 * ((∑ i, ((T i).erase v).card) -
      (Finset.univ.biUnion (fun i => (T i).erase v)).card) ≤
        3 * Fintype.card ι - 3 := by
  classical
  have hex (i : ι) : ∃ B : SimpleGraph V,
      B.IsSparse 2 3 ∧ B.edgeSet ⊆ C.graph.edgesIn ((T i).erase v : Set V) ∧
        B.edgeSet.ncard + 3 = 2 * ((T i).erase v).card := by
    apply exists_basis_on_clique C.graph ((T i).erase v)
    · rw [Finset.card_erase_of_mem (hv i)]
      have h := (hT i).1
      omega
    · intro x hx y hy hxy
      exact (hT i).2.1 (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hy).2 hxy
  choose B hBsparse hBedges hBcount using hex
  exact basis_overlap_inequality C v T B hTinj hT hv hBsparse hBedges hBcount

end

end Papers.Rigidity.NeighborhoodBases

end
end BundleSource0030

section BundleSource0031
/- Source: Papers/RigidityStress.lean -/





@[expose] public section

/-!
# Ordinary undirected bar stresses

The generic-rank definition uses the fixed target of ordered pairs. This
file proves that deleting the repeated rows and all nonedge rows preserves
the actual kernel and rank. Stresses then have one coefficient per genuine
undirected edge, as in the paper, and the usual rank/stress identity is
derived from duality and rank-nullity.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint

open scoped BigOperators
open scoped Classical

variable {V : Type} [Fintype V] {d : ℕ}

/-- One coefficient for each actual unordered graph edge. -/
abbrev Edge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}

def unorderedFunctional (p : Placement V d) : Sym2 V → (Velocity V d →ₗ[ℝ] ℝ) :=
  Sym2.lift ⟨edgeFunctional p, by
    intro v w
    apply LinearMap.ext
    intro u
    exact edgeConstraint_comm p u v w⟩

@[simp] theorem unorderedFunctional_mk (p : Placement V d) (v w : V)
    (u : Velocity V d) :
    unorderedFunctional p s(v,w) u = edgeConstraint p u v w := rfl

theorem unorderedFunctional_out (p : Placement V d) (e : Sym2 V)
    (u : Velocity V d) :
    unorderedFunctional p e u = edgeConstraint p u e.out.1 e.out.2 := by
  have h := congrArg (fun q : Sym2 V => unorderedFunctional p q u) e.out_eq
  exact h.symm

def undirectedRigidityOperator (G : SimpleGraph V) (p : Placement V d) :
    Velocity V d →ₗ[ℝ] (Edge G → ℝ) :=
  LinearMap.pi fun e => unorderedFunctional p e.val

@[simp] theorem undirectedRigidityOperator_apply (G : SimpleGraph V)
    (p : Placement V d) (u : Velocity V d) (e : Edge G) :
    undirectedRigidityOperator G p u e = unorderedFunctional p e.val u := rfl

theorem ker_undirectedRigidityOperator (G : SimpleGraph V) (p : Placement V d) :
    (undirectedRigidityOperator G p).ker = (rigidityOperator G p).ker := by
  classical
  ext u
  constructor
  · intro h
    change IsInfinitesimalMotion G p u
    rw [isInfinitesimalMotion_iff]
    intro v w hvw
    have hz := congrFun (LinearMap.mem_ker.mp h) (⟨s(v,w), hvw⟩ : Edge G)
    simpa using hz
  · intro h
    have hm : IsInfinitesimalMotion G p u := h
    rw [isInfinitesimalMotion_iff] at hm
    rw [LinearMap.mem_ker]
    ext e
    have hadj : G.Adj e.val.out.1 e.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.val.out_eq]
      exact e.property
    simpa only [undirectedRigidityOperator_apply, unorderedFunctional_out,
      Pi.zero_apply] using hm _ _ hadj

/-- Ordered-pair bookkeeping does not change the rank of ordinary bar rows. -/
theorem undirectedRigidityRank_eq (G : SimpleGraph V) (p : Placement V d) :
    Module.finrank ℝ (undirectedRigidityOperator G p).range = rigidityRank G p := by
  classical
  have hu := (undirectedRigidityOperator G p).finrank_range_add_finrank_ker
  have ho := (rigidityOperator G p).finrank_range_add_finrank_ker
  rw [ker_undirectedRigidityOperator] at hu
  unfold rigidityRank
  omega

/-- The virtual-work functional of an ordinary edge-coefficient vector. -/
def stressOperator (G : SimpleGraph V) (p : Placement V d) :
    (Edge G → ℝ) →ₗ[ℝ] Module.Dual ℝ (Velocity V d) := by
  classical
  exact (undirectedRigidityOperator G p).dualMap.comp
    (dotProductEquiv ℝ (Edge G)).toLinearMap

@[simp] theorem stressOperator_apply (G : SimpleGraph V) (p : Placement V d)
    (ω : Edge G → ℝ) (u : Velocity V d) :
    stressOperator G p ω u =
      ∑ e : Edge G, ω e * edgeConstraint p u e.val.out.1 e.val.out.2 := by
  classical
  change (∑ e : Edge G, ω e * unorderedFunctional p e.val u) = _
  simp only [unorderedFunctional_out]

/-- Self-stresses are exactly the bar coefficients annihilating every
velocity field under the actual Euclidean virtual-work pairing. -/
def StressSpace (G : SimpleGraph V) (p : Placement V d) :
    Submodule ℝ (Edge G → ℝ) := (stressOperator G p).ker

theorem mem_StressSpace_iff (G : SimpleGraph V) (p : Placement V d)
    (ω : Edge G → ℝ) :
    ω ∈ StressSpace G p ↔ ∀ u : Velocity V d,
      ∑ e : Edge G, ω e * edgeConstraint p u e.val.out.1 e.val.out.2 = 0 := by
  classical
  simp only [StressSpace, LinearMap.mem_ker, LinearMap.ext_iff,
    stressOperator_apply, LinearMap.zero_apply]

theorem stressOperator_rank (G : SimpleGraph V) (p : Placement V d) :
    Module.finrank ℝ (stressOperator G p).range = rigidityRank G p := by
  classical
  rw [stressOperator, LinearMap.range_comp_of_range_eq_top _
    (dotProductEquiv ℝ (Edge G)).range,
    LinearMap.finrank_range_dualMap_eq_finrank_range,
    undirectedRigidityRank_eq]

/-- The exact identity used throughout the stress count. -/
theorem rigidityRank_add_stress_dimension (G : SimpleGraph V) (p : Placement V d) :
    rigidityRank G p + Module.finrank ℝ (StressSpace G p) = Fintype.card (Edge G) := by
  classical
  have h := (stressOperator G p).finrank_range_add_finrank_ker
  rw [stressOperator_rank] at h
  rw [← Module.finrank_fintype_fun_eq_card ℝ]
  exact h

end Papers.Rigidity.BarJoint

end
end
end BundleSource0031

section BundleSource0032
/- Source: Papers/RigiditySupportedCode.lean -/







@[expose] public section

/-!
# Actual supported linear codes and shortening

These are the linear-algebra ingredients of the finite-order proof of
Lemma 2.1.  Codewords are actual coordinate vectors over an arbitrary
field.  Shortening sets the deleted coordinate equal to zero; it is not
puncturing an arbitrary codeword.  The Singleton bound is proved directly
by an injective coordinate projection.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical

variable {K I : Type*} [Field K] [Fintype I]

def support (w : I → K) : Finset I := Finset.univ.filter (fun i => w i ≠ 0)

@[simp] theorem mem_support (w : I → K) (i : I) :
    i ∈ support w ↔ w i ≠ 0 := by simp [support]

def MinimumSupport (W : Submodule K (I → K)) (s : ℕ) : Prop :=
  ∀ w ∈ W, w ≠ 0 → s ≤ (support w).card

def activeCoordinates (W : Submodule K (I → K)) : Finset I :=
  Finset.univ.filter (fun i => ∃ w ∈ W, w i ≠ 0)

@[simp] theorem mem_activeCoordinates (W : Submodule K (I → K)) (i : I) :
    i ∈ activeCoordinates W ↔ ∃ w ∈ W, w i ≠ 0 := by
  simp [activeCoordinates]

theorem support_subset_active {W : Submodule K (I → K)} {w : I → K} (hw : w ∈ W) :
    support w ⊆ activeCoordinates W := by
  intro i hi
  exact (mem_activeCoordinates W i).mpr ⟨w, hw, (mem_support w i).mp hi⟩

/-- The code dimension plus its minimum support is at most one more
than its number of active coordinates.  The nonzero-code hypothesis is
necessary: the zero code satisfies every minimum-support condition. -/
theorem singleton_bound (W : Submodule K (I → K)) (s : ℕ)
    (hs : 1 ≤ s) (hmin : MinimumSupport W s) (hW : W ≠ ⊥) :
    Module.finrank K W + s ≤ (activeCoordinates W).card + 1 := by
  obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hsg : s ≤ (activeCoordinates W).card :=
    (hmin w hw hwne).trans (Finset.card_le_card (support_subset_active hw))
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show (activeCoordinates W).card + 1 - s ≤ (activeCoordinates W).card by omega)
  let F : W →ₗ[K] (A → K) :=
    LinearMap.pi fun i => (LinearMap.proj i.val).comp W.subtype
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hxzero : ∀ i ∈ A, x.val i = 0 := by
        intro i hi
        exact congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      have hsub : support x.val ⊆ activeCoordinates W \ A := by
        intro i hi
        refine Finset.mem_sdiff.mpr ⟨support_subset_active x.property hi, ?_⟩
        intro hiA
        exact (mem_support x.val i).mp hi (hxzero i hiA)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset hA, hAc] at hc
      have hxv : x.val = 0 := by
        by_contra hne
        have h := hmin x.val x.property hne
        omega
      exact Subtype.ext hxv
    · exact bot_le
  have hr := LinearMap.finrank_le_finrank_of_injective hF
  have hr' : Module.finrank K W ≤ A.card := by
    simpa using hr
  omega

/-- Inserting a zero coordinate is a genuine injective linear map. -/
def insertZero {n : ℕ} (i : Fin (n + 1)) : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun w := Fin.insertNth i 0 w
  map_add' u v := by
    funext j
    cases j using Fin.succAboveCases i with
    | x => simp
    | p j => simp
  map_smul' a w := by
    funext j
    cases j using Fin.succAboveCases i with
    | x => simp
    | p j => simp

@[simp] theorem insertZero_same {n : ℕ} (i : Fin (n + 1)) (w : Fin n → K) :
    insertZero i w i = 0 := by simp [insertZero]

@[simp] theorem insertZero_succAbove {n : ℕ} (i : Fin (n + 1))
    (w : Fin n → K) (j : Fin n) : insertZero i w (i.succAbove j) = w j := by
  simp [insertZero]

theorem insertZero_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (insertZero (K := K) i) :=
  Fin.insertNth_right_injective (α := fun _ : Fin (n + 1) => K) (p := i) 0

def shorten {n : ℕ} (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1)) :
    Submodule K (Fin n → K) := W.comap (insertZero i)

@[simp] theorem mem_shorten {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (i : Fin (n + 1)) (w : Fin n → K) :
    w ∈ shorten W i ↔ insertZero i w ∈ W := Iff.rfl

theorem support_insertZero {n : ℕ} (i : Fin (n + 1)) (w : Fin n → K) :
    support (insertZero i w) = (support w).map ⟨i.succAbove, Fin.succAbove_right_injective⟩ := by
  ext j
  cases j using Fin.succAboveCases i with
  | x => simp
  | p j => simp

theorem minimumSupport_shorten {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (i : Fin (n + 1)) {s : ℕ} (hmin : MinimumSupport W s) :
    MinimumSupport (shorten W i) s := by
  intro w hw hne
  have hi : insertZero i w ≠ 0 := by
    intro h
    exact hne (insertZero_injective i (by simpa using h))
  have h := hmin (insertZero i w) hw hi
  simpa [support_insertZero] using h

def coordinate (W : Submodule K (I → K)) (i : I) : W →ₗ[K] K :=
  (LinearMap.proj i).comp W.subtype

@[simp] theorem coordinate_apply (W : Submodule K (I → K)) (i : I) (w : W) :
    coordinate W i w = w.val i := rfl

theorem coordinate_ne_zero_iff (W : Submodule K (I → K)) (i : I) :
    coordinate W i ≠ 0 ↔ i ∈ activeCoordinates W := by
  rw [mem_activeCoordinates]
  constructor
  · intro h
    by_contra hnone
    apply h
    ext w
    by_contra hne
    exact hnone ⟨w.val, w.property, hne⟩
  · rintro ⟨w, hw, hne⟩ hz
    exact hne (congrArg (fun f : W →ₗ[K] K => f ⟨w, hw⟩) hz)

/-- Shortening is linearly equivalent to the kernel of the selected
coordinate functional on the original code. -/
def shortenEquivKernel {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (i : Fin (n + 1)) : shorten W i ≃ₗ[K] (coordinate W i).ker where
  toFun w := ⟨⟨insertZero i w.val, w.property⟩, by simp⟩
  invFun w := ⟨Fin.removeNth i w.val.val, by
    have hi : w.val.val i = 0 := w.property
    change Fin.insertNth i 0 (Fin.removeNth i w.val.val) ∈ W
    rw [← hi, Fin.insertNth_self_removeNth]
    exact w.val.property⟩
  left_inv w := by ext j; simp [insertZero, Fin.removeNth]
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    have hi : w.val.val i = 0 := w.property
    change Fin.insertNth i 0 (Fin.removeNth i w.val.val) = w.val.val
    rw [← hi, Fin.insertNth_self_removeNth]
  map_add' u v := by ext j; exact congrFun (map_add (insertZero i) u.val v.val) j
  map_smul' a w := by ext j; exact congrFun (map_smul (insertZero i) a w.val) j

theorem finrank_shorten_of_active {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (i : Fin (n + 1)) (hi : i ∈ activeCoordinates W) :
    Module.finrank K (shorten W i) + 1 = Module.finrank K W := by
  rw [(shortenEquivKernel W i).finrank_eq]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero ((coordinate_ne_zero_iff W i).mpr hi)

theorem finrank_shorten_of_inactive {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (i : Fin (n + 1)) (hi : i ∉ activeCoordinates W) :
    Module.finrank K (shorten W i) = Module.finrank K W := by
  rw [(shortenEquivKernel W i).finrank_eq]
  have hz : coordinate W i = 0 := by
    by_contra hne
    exact hi ((coordinate_ne_zero_iff W i).mp hne)
  change Module.finrank K (coordinate W i).ker = Module.finrank K W
  rw [hz, LinearMap.ker_zero, finrank_top]

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0032

section BundleSource0033
/- Source: Papers/RigidityStressEquilibrium.lean -/





@[expose] public section

/-!
# Actual equilibrium and minimum support of a stress star

The force balance at a vertex is derived from the virtual-work definition
of ordinary unordered-edge stresses.  Restricting any actual stress
subspace to a vertex star then gives a code whose nonzero words have at
least four coordinates at a three-dimensional general-position placement.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix BarJoint
open scoped Classical BigOperators Matrix

namespace GeneralPosition

theorem InGeneralPosition.small_star
    {V I : Type} [Fintype V] [Fintype I]
    (p : Placement V 3) (hp : InGeneralPosition p) (v : V)
    (f : I ↪ {w : V // w ≠ v}) (hI : Fintype.card I ≤ 3) :
    LinearIndependent ℝ (fun i => p v - p (f i).val) := by
  let e := Fintype.equivFin I
  let g : Fin (Fintype.card I + 1) ↪ V :=
    { toFun := Fin.cases v (fun i => (f (e.symm i)).val)
      inj' := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => rfl
          | succ j => exact False.elim ((f (e.symm j)).property hij.symm)
        | succ i =>
          cases j using Fin.cases with
          | zero => exact False.elim ((f (e.symm i)).property hij)
          | succ j =>
            apply congrArg Fin.succ
            exact e.symm.injective (f.injective (Subtype.ext hij)) }
  have h := (hp ⟨Fintype.card I, by omega⟩ g).neg
  have h' := h.comp e e.injective
  change LinearIndependent ℝ
    (fun i : I => -(p ((f (e.symm (e i))).val) - p v)) at h'
  simpa only [Equiv.symm_apply_apply, neg_sub] using h'

end GeneralPosition

namespace BarJoint

variable {V : Type} [Fintype V] {d : ℕ}

abbrev IncidentEdge (G : SimpleGraph V) (v : V) := {e : Edge G // v ∈ e.val}

def incidentOther (G : SimpleGraph V) (v : V) (e : IncidentEdge G v) : V :=
  Sym2.Mem.other e.property

theorem incidentOther_ne (G : SimpleGraph V) (v : V) (e : IncidentEdge G v) :
    incidentOther G v e ≠ v := G.edge_other_ne e.val.property e.property

theorem incidentOther_injective (G : SimpleGraph V) (v : V) :
    Function.Injective (incidentOther G v) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  exact (Sym2.other_spec e.property).symm.trans
    ((congrArg (fun w => s(v, w)) h).trans (Sym2.other_spec f.property))

def starRestriction (G : SimpleGraph V) (v : V) :
    (Edge G → ℝ) →ₗ[ℝ] (IncidentEdge G v → ℝ) :=
  LinearMap.pi fun e => LinearMap.proj e.val

@[simp] theorem starRestriction_apply (G : SimpleGraph V) (v : V)
    (ω : Edge G → ℝ) (e : IncidentEdge G v) : starRestriction G v ω e = ω e.val := rfl

theorem unorderedFunctional_impulse_of_incident (G : SimpleGraph V)
    (p : Placement V d) (v : V) (z : Point d) (e : IncidentEdge G v) :
    unorderedFunctional p e.val.val (Pi.single v z) =
      (p v - p (incidentOther G v e)) ⬝ᵥ z := by
  have hn := incidentOther_ne G v e
  rw [← Sym2.other_spec e.property, unorderedFunctional_mk]
  change edgeConstraint p (Pi.single v z) v (incidentOther G v e) = _
  simp [edgeConstraint, Pi.single_apply, hn, hn.symm, dotProduct]

theorem unorderedFunctional_impulse_of_not_incident (G : SimpleGraph V)
    (p : Placement V d) (v : V) (z : Point d) (e : Edge G) (he : v ∉ e.val) :
    unorderedFunctional p e.val (Pi.single v z) = 0 := by
  have h₁ : e.val.out.1 ≠ v := by intro h; exact he (h ▸ e.val.out_fst_mem)
  have h₂ : e.val.out.2 ≠ v := by intro h; exact he (h ▸ e.val.out_snd_mem)
  simp [unorderedFunctional_out, edgeConstraint, Pi.single_apply, h₁, h₂]

/-- Equilibrium at an actual graph vertex, derived by testing arbitrary
velocity impulses at that vertex. -/
theorem stress_force_balance (G : SimpleGraph V) (p : Placement V d)
    (ω : Edge G → ℝ) (hω : ω ∈ StressSpace G p) (v : V) :
    ∑ e : IncidentEdge G v, ω e.val • (p v - p (incidentOther G v e)) = 0 := by
  have hwork (z : Point d) :
      (∑ e : IncidentEdge G v, ω e.val • (p v - p (incidentOther G v e))) ⬝ᵥ z = 0 := by
    have h := congrArg (fun f : Module.Dual ℝ (Velocity V d) => f (Pi.single v z))
      (LinearMap.mem_ker.mp hω)
    change (∑ e : Edge G, ω e * unorderedFunctional p e.val (Pi.single v z)) = 0 at h
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun e : Edge G => v ∈ e.val)
      (fun e : Edge G => ω e * unorderedFunctional p e.val (Pi.single v z))
    have houtside : (∑ e : {e : Edge G // v ∉ e.val},
        ω e.val * unorderedFunctional p e.val.val (Pi.single v z)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [unorderedFunctional_impulse_of_not_incident G p v z e.val e.property, mul_zero]
    rw [houtside, add_zero, h] at hsplit
    rw [sum_dotProduct]
    simpa only [smul_dotProduct, smul_eq_mul,
      unorderedFunctional_impulse_of_incident G p v z] using hsplit
  ext i
  have h := hwork (Pi.single i 1)
  simpa using h

/-- The actual star image of an arbitrary subspace of edge coefficients. -/
def stressStarCode (G : SimpleGraph V) (v : V)
    (W : Submodule ℝ (Edge G → ℝ)) : Submodule ℝ (IncidentEdge G v → ℝ) :=
  W.map (starRestriction G v)

/-- Every nonzero word in an actual stress-star image uses at least four
distinct incident bars at a general-position placement. -/
theorem stressStarCode_minimumSupport_four
    (G : SimpleGraph V) (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (W : Submodule ℝ (Edge G → ℝ)) (hW : W ≤ StressSpace G p) :
    SupportedCode.MinimumSupport (stressStarCode G v W) 4 := by
  intro a ha hane
  obtain ⟨ω, hω, rfl⟩ := Submodule.mem_map.mp ha
  let S := SupportedCode.support (starRestriction G v ω)
  by_contra hcard
  have hc : Fintype.card S ≤ 3 := by
    rw [Fintype.card_coe S]
    change (SupportedCode.support (starRestriction G v ω)).card ≤ 3
    omega
  let f : S ↪ {w : V // w ≠ v} :=
    { toFun := fun e => ⟨incidentOther G v e.val, incidentOther_ne G v e.val⟩
      inj' := by
        intro e f h
        exact Subtype.ext (incidentOther_injective G v (congrArg Subtype.val h)) }
  have hlin := hp.small_star p v f hc
  have hfull := stress_force_balance G p ω (hW hω) v
  have hsum : (∑ e : S, ω e.val.val • (p v - p (incidentOther G v e.val))) = 0 := by
    rw [Finset.sum_coe_sort S
      (fun e : IncidentEdge G v => ω e.val • (p v - p (incidentOther G v e)))]
    rw [Finset.sum_subset (Finset.subset_univ S)]
    · exact hfull
    · intro e he hne
      have hz : ω e.val = 0 := by
        simpa only [S, SupportedCode.mem_support, starRestriction_apply, not_not] using hne
      rw [hz, zero_smul]
  have hzero := (Fintype.linearIndependent_iff.mp hlin)
    (fun e : S => ω e.val.val) hsum
  apply hane
  ext e
  change ω e.val = 0
  by_cases he : e ∈ S
  · exact hzero ⟨e, he⟩
  · simpa only [S, SupportedCode.mem_support, starRestriction_apply, not_not] using he

end BarJoint
end

end Papers.Rigidity

end
end BundleSource0033

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0033/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0033.json"

section BundleSource0034
/- Source: Papers/RigidityCopiedStars.lean -/





@[expose] public section

/-!
# Independence of the actual copied body stars

The coefficients are attached to literal copies of the edges at a fixed
vertex, one copy in each incident maximal body.  They vanish outside that
body.  Their cancellation on each actual edge and their separate force
balances imply that every copied coefficient is zero.  This is Lemma 6.1;
the overlap estimate is derived from the selected counterexample, not
assumed as a numerical premise.

The copied stars supply the local rank bounds for the global argument.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint
open scoped Classical BigOperators

namespace BodyLoads

variable {V : Type} [Fintype V]

/-- A nonzero balanced star has at least four actual nonzero bars. -/
theorem balanced_star_support_four
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (a : V → ℝ) (hav : a v = 0)
    (hbalance : ∑ w, a w • (p v - p w) = 0) (ha : a ≠ 0) :
    4 ≤ (SupportedCode.support a).card := by
  let S := SupportedCode.support a
  by_contra hsmall
  have hS : Fintype.card S ≤ 3 := by
    rw [Fintype.card_coe S]
    change (SupportedCode.support a).card ≤ 3
    omega
  let f : S ↪ {w : V // w ≠ v} :=
    { toFun := fun w => ⟨w.val, by
        intro hw
        have hn : a w.val ≠ 0 := (SupportedCode.mem_support a w.val).mp w.property
        exact hn (by simpa only [hw] using hav)⟩
      inj' := fun _ _ h => Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h) }
  have hlin := GeneralPosition.InGeneralPosition.small_star p hp v f hS
  have hsum : ∑ w : S, a w.val • (p v - p w.val) = 0 := by
    rw [Finset.sum_coe_sort S (fun w : V => a w • (p v - p w))]
    rw [Finset.sum_subset (Finset.subset_univ S)]
    · exact hbalance
    · intro w _ hw
      have hz : a w = 0 := by
        simpa only [S, SupportedCode.mem_support, not_not] using hw
      rw [hz, zero_smul]
  have hz := (Fintype.linearIndependent_iff.mp hlin) (fun w : S => a w.val) hsum
  apply ha
  ext w
  change a w = 0
  by_cases hw : w ∈ S
  · exact hz ⟨w, hw⟩
  · simpa only [S, SupportedCode.mem_support, not_not] using hw

/-- Count the same finite incidence relation by its two coordinates. -/
theorem sum_card_eq_sum_multiplicity
    {I : Type} [Fintype I] (S : I → Finset V) :
    (∑ i, (S i).card) =
      ∑ w : V, (Finset.univ.filter fun i => w ∈ S i).card := by
  calc
    (∑ i, (S i).card) = ∑ i, ∑ w : V, if w ∈ S i then 1 else 0 := by simp
    _ = ∑ w : V, ∑ i, if w ∈ S i then 1 else 0 := Finset.sum_comm
    _ = ∑ w : V, (Finset.univ.filter fun i => w ∈ S i).card := by simp

/-- A sum of scalar coefficients that vanishes has either no nonzero
summands or at least two of them. -/
theorem cancelling_coefficients_support
    {I : Type} [Fintype I] (a : I → ℝ) (h : ∑ i, a i = 0) :
    (SupportedCode.support a).card = 0 ∨ 2 ≤ (SupportedCode.support a).card := by
  by_cases hz : (SupportedCode.support a).card = 0
  · exact Or.inl hz
  · right
    by_contra hsmall
    have hc : (SupportedCode.support a).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hni : a i ≠ 0 := (SupportedCode.mem_support a i).mp (by simp [hi])
    have hsum : (∑ j, a j) = a i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hj : j ∉ SupportedCode.support a := by simp [hi, hji]
        simpa only [SupportedCode.mem_support, not_not] using hj
      · simp
    exact hni (hsum.symm.trans h)

/-- The incidence part of the copied-star argument.  The full body
overlap estimate is supplied separately by its already stated theorem. -/
theorem copied_support_count
    {I : Type} [Fintype I] (S : I → Finset V) (a : I → V → ℝ)
    (hsupport : ∀ i w, a i w ≠ 0 → w ∈ S i)
    (hcancel : ∀ w, ∑ i, a i w = 0) :
    (∑ i, (SupportedCode.support (a i)).card) +
        2 * (Finset.univ.biUnion S).card ≤ 2 * ∑ i, (S i).card := by
  let N := Finset.univ.biUnion S
  let m (w : V) := (Finset.univ.filter fun i => w ∈ S i).card
  let n (w : V) := (SupportedCode.support (fun i => a i w)).card
  have hnm (w : V) : n w ≤ m w := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsupport i w ((SupportedCode.mem_support (fun i => a i w) i).mp hi)⟩
  have hlocal (w : V) : n w + 2 * (if w ∈ N then 1 else 0) ≤ 2 * m w := by
    by_cases hw : w ∈ N
    · have hm : 1 ≤ m w := by
        apply Nat.succ_le_iff.mpr
        apply Finset.card_pos.mpr
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have hcases := cancelling_coefficients_support (fun i => a i w) (hcancel w)
      change n w = 0 ∨ 2 ≤ n w at hcases
      rw [if_pos hw]
      rcases hcases with hn | hn <;> have := hnm w <;> omega
    · rw [if_neg hw, mul_zero, add_zero]
      exact (hnm w).trans (by omega)
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hlocal w)
  have hn : (∑ w, n w) = ∑ i, (SupportedCode.support (a i)).card := by
    calc
      (∑ w, n w) = ∑ w : V,
          (Finset.univ.filter fun i => w ∈ SupportedCode.support (a i)).card := by
        apply Finset.sum_congr rfl
        intro w _
        change (SupportedCode.support (fun i => a i w)).card = _
        apply congrArg Finset.card
        ext i
        simp only [SupportedCode.mem_support, Finset.mem_filter,
          Finset.mem_univ, true_and]
      _ = ∑ i, (SupportedCode.support (a i)).card :=
        (sum_card_eq_sum_multiplicity (fun i => SupportedCode.support (a i))).symm
  have hm : (∑ w, m w) = ∑ i, (S i).card :=
    (sum_card_eq_sum_multiplicity S).symm
  have hN : (∑ w : V, if w ∈ N then 1 else 0) = N.card := by simp
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hn, hm, hN] using hsum

/-- Lemma 6.1 for any finite family of distinct actual bodies through
the vertex.  There is no nonemptiness premise on the original family. -/
theorem copied_star_coefficients_eq_zero
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (v : V)
    {I : Type} [Fintype I] (T : I → Finset V)
    (hTinj : Function.Injective T) (hT : ∀ i, IsBody M.graph (T i))
    (hv : ∀ i, v ∈ T i) (a : I → V → ℝ)
    (hsupport : ∀ i w, a i w ≠ 0 → w ∈ (T i).erase v)
    (hcancel : ∀ w, ∑ i, a i w = 0)
    (hbalance : ∀ i, ∑ w, a i w • (p v - p w) = 0) :
    ∀ i w, a i w = 0 := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨i₀, w₀, hi₀⟩ := hnot
  let A : Finset I := Finset.univ.filter fun i => a i ≠ 0
  have hiA : i₀ ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hi
    exact hi₀ (congrFun hi w₀)
  letI : Nonempty A := ⟨⟨i₀, hiA⟩⟩
  let S : A → Finset V := fun i => (T i.val).erase v
  let b : A → V → ℝ := fun i => a i.val
  have hbne (i : A) : b i ≠ 0 := (Finset.mem_filter.mp i.property).2
  have hbself (i : A) : b i v = 0 := by
    by_contra hn
    exact Finset.notMem_erase v (T i.val) (hsupport i.val v hn)
  have hbcount (i : A) : 4 ≤ (SupportedCode.support (b i)).card :=
    balanced_star_support_four p hp v (b i) (hbself i) (hbalance i.val) (hbne i)
  have hbcancel (w : V) : ∑ i : A, b i w = 0 := by
    change (∑ i : A, a i.val w) = 0
    rw [Finset.sum_coe_sort A (fun i : I => a i w)]
    rw [Finset.sum_subset (Finset.subset_univ A)]
    · exact hcancel w
    · intro i _ hi
      have hai : a i = 0 := by
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
      exact congrFun hai w
  have hupper := copied_support_count S b (fun i w => hsupport i.val w) hbcancel
  have hoverlap := NeighborhoodBases.lemma_three_two M v (fun i : A => T i.val)
    (hTinj.comp Subtype.val_injective) (fun i => hT i.val) (fun i => hv i.val)
  have hNle : (Finset.univ.biUnion S).card ≤ ∑ i : A, (S i).card :=
    Finset.card_biUnion_le
  have hlower : 4 * Fintype.card A ≤ ∑ i : A, (SupportedCode.support (b i)).card := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] using
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbcount i))
  have hpositive : 0 < Fintype.card A := Fintype.card_pos
  change 2 * ((∑ i : A, (S i).card) - (Finset.univ.biUnion S).card) ≤
    3 * Fintype.card A - 3 at hoverlap
  omega

end BodyLoads
end Papers.Rigidity

end
end
end BundleSource0034

section BundleSource0035
/- Source: Papers/RigidityStarCoordinates.lean -/



@[expose] public section

/-!
# Actual vertex-indexed coordinates of a stress star

The unordered-edge coefficient is reindexed by its other endpoint and
extended by zero on nonneighbors.  The ordinary force balance is proved
under this exact coordinate change, for use on copied body stars.

The coordinate maps retain the original incident-edge coefficients.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint

open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def starCoordinates (G : SimpleGraph V) (v : V) :
    (Edge G → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.pi fun w => if h : G.Adj v w then LinearMap.proj ⟨s(v,w), h⟩ else 0

theorem starCoordinates_of_adj (G : SimpleGraph V) (v w : V)
    (a : Edge G → ℝ) (h : G.Adj v w) :
    starCoordinates G v a w = a ⟨s(v,w), h⟩ := by
  simp [starCoordinates, h]

theorem starCoordinates_of_not_adj (G : SimpleGraph V) (v w : V)
    (a : Edge G → ℝ) (h : ¬ G.Adj v w) :
    starCoordinates G v a w = 0 := by
  simp [starCoordinates, h]

@[simp] theorem starCoordinates_self (G : SimpleGraph V) (v : V)
    (a : Edge G → ℝ) : starCoordinates G v a v = 0 := by
  exact starCoordinates_of_not_adj G v v a (G.loopless.irrefl v)

theorem incidentOther_adj (G : SimpleGraph V) (v : V) (e : IncidentEdge G v) :
    G.Adj v (incidentOther G v e) := by
  have h := e.val.property
  rw [← Sym2.other_spec e.property] at h
  exact h

def incidentNeighborEquiv (G : SimpleGraph V) (v : V) :
    IncidentEdge G v ≃ {w : V // G.Adj v w} :=
  Equiv.ofBijective (fun e => ⟨incidentOther G v e, incidentOther_adj G v e⟩) (by
    constructor
    · intro e f hef
      exact incidentOther_injective G v (congrArg Subtype.val hef)
    · intro w
      let e : IncidentEdge G v :=
        ⟨⟨s(v,w.val), w.property⟩, Sym2.mem_mk_left v w.val⟩
      refine ⟨e, Subtype.ext ?_⟩
      exact Sym2.congr_right.mp (Sym2.other_spec e.property))

theorem starCoordinates_incidentOther
    (G : SimpleGraph V) (v : V) (a : Edge G → ℝ) (e : IncidentEdge G v) :
    starCoordinates G v a (incidentOther G v e) = a e.val := by
  rw [starCoordinates_of_adj G v _ a (incidentOther_adj G v e)]
  congr 1
  exact Subtype.ext (Sym2.other_spec e.property)

theorem sum_starCoordinates_eq_incident
    (G : SimpleGraph V) (p : Placement V 3) (v : V) (a : Edge G → ℝ) :
    (∑ w, starCoordinates G v a w • (p v - p w)) =
      ∑ e : IncidentEdge G v, a e.val • (p v - p (incidentOther G v e)) := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun w => G.Adj v w)
    (fun w => starCoordinates G v a w • (p v - p w))
  have hout : (∑ w : {w : V // ¬ G.Adj v w},
      starCoordinates G v a w.val • (p v - p w.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [starCoordinates_of_not_adj G v _ a w.property, zero_smul]
  rw [hout, add_zero] at hsplit
  rw [← hsplit]
  have hsum := Equiv.sum_comp (incidentNeighborEquiv G v)
    (fun w : {w : V // G.Adj v w} =>
      starCoordinates G v a w.val • (p v - p w.val))
  simpa only [incidentNeighborEquiv, Equiv.ofBijective_apply,
    starCoordinates_incidentOther] using hsum.symm

theorem stress_starCoordinates_balance
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ)
    (ha : a ∈ StressSpace G p) (v : V) :
    ∑ w, starCoordinates G v a w • (p v - p w) = 0 := by
  rw [sum_starCoordinates_eq_incident]
  exact stress_force_balance G p a ha v

end Papers.Rigidity.BarJoint

end
end
end BundleSource0035

section BundleSource0036
/- Source: Papers/RigiditySupportedPrefix.lean -/




@[expose] public section

/-!
# The actual new-stress quotient embeds in its supported star image

The coordinate-set statement below applies to each induced graph prefix.
It identifies the kernel of restriction to the new star with the old
supported space, and derives the dimension inequality by rank-nullity.
The code is an arbitrary linear subspace; no equality with the full
stress space is required.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical

variable {K E I : Type*} [Field K] [Fintype E] [Fintype I]

def supportedOn (W : Submodule K (E → K)) (A : Set E) : Submodule K (E → K) where
  carrier := {w | w ∈ W ∧ ∀ e, e ∉ A → w e = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun e he => by simp [hu' e he, hv' e he]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun e he => by simp [hw' e he]⟩

@[simp] theorem mem_supportedOn (W : Submodule K (E → K)) (A : Set E) (w : E → K) :
    w ∈ supportedOn W A ↔ w ∈ W ∧ ∀ e, e ∉ A → w e = 0 := Iff.rfl

theorem supportedOn_mono (W : Submodule K (E → K)) {A B : Set E} (hAB : A ⊆ B) :
    supportedOn W A ≤ supportedOn W B := by
  intro w hw
  exact ⟨hw.1, fun e he => hw.2 e (fun h => he (hAB h))⟩

def coordinateRestriction (e : I ↪ E) : (E → K) →ₗ[K] (I → K) :=
  LinearMap.pi fun i => LinearMap.proj (e i)

@[simp] theorem coordinateRestriction_apply (e : I ↪ E) (w : E → K) (i : I) :
    coordinateRestriction e w i = w (e i) := rfl

/-- Exact kernel identification for the new-coordinate map.  The old
coordinate set is disjoint from the new star, and every newly allowed
coordinate belongs to that star. -/
def supportedPrefixKernelEquiv (W : Submodule K (E → K)) (A B : Set E)
    (e : I ↪ E) (hAB : A ⊆ B) (hold : ∀ i, e i ∉ A)
    (hnew : ∀ a ∈ B, a ∉ A → a ∈ Set.range e) :
    ((coordinateRestriction e).domRestrict (supportedOn W B)).ker ≃ₗ[K]
      supportedOn W A where
  toFun w := ⟨w.val.val, w.val.property.1, by
    intro a ha
    by_cases hb : a ∈ B
    · obtain ⟨i, rfl⟩ := hnew a hb ha
      exact congrFun (LinearMap.mem_ker.mp w.property) i
    · exact w.val.property.2 a hb⟩
  invFun w := ⟨⟨w.val, supportedOn_mono W hAB w.property⟩, by
    rw [LinearMap.mem_ker]
    ext i
    exact w.property.2 (e i) (hold i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem supportedPrefix_range_le (W : Submodule K (E → K)) (B : Set E)
    (e : I ↪ E) :
    ((coordinateRestriction e).domRestrict (supportedOn W B)).range ≤
      supportedOn (W.map (coordinateRestriction e)) (e ⁻¹' B) := by
  rintro a ⟨w, rfl⟩
  refine ⟨⟨w.val, w.property.1, rfl⟩, ?_⟩
  intro i hi
  exact w.property.2 (e i) hi

/-- The full new supported dimension, minus the old dimension, is at
most the dimension of the supported part of the actual global star
image.  This is the injection used in Corollary 2.2. -/
theorem supportedPrefix_finrank_le (W : Submodule K (E → K)) (A B : Set E)
    (e : I ↪ E) (hAB : A ⊆ B) (hold : ∀ i, e i ∉ A)
    (hnew : ∀ a ∈ B, a ∉ A → a ∈ Set.range e) :
    Module.finrank K (supportedOn W B) ≤
      Module.finrank K (supportedOn W A) +
        Module.finrank K (supportedOn (W.map (coordinateRestriction e)) (e ⁻¹' B)) := by
  have hdim :=
    ((coordinateRestriction e).domRestrict (supportedOn W B)).finrank_range_add_finrank_ker
  rw [(supportedPrefixKernelEquiv W A B e hAB hold hnew).finrank_eq] at hdim
  have hle := Submodule.finrank_mono (supportedPrefix_range_le W B e)
  omega

end
end Papers.Rigidity.SupportedCode

end
end BundleSource0036

section BundleSource0037
/- Source: Papers/RigiditySubgraphStress.lean -/





@[expose] public section

/-!
# Zero extension identifies subgraph stresses exactly

For an actual subgraph on the same vertex set, zero extension is a
linear equivalence from its stress space onto the parent stress vectors
supported on its edges.  Thus the induced-prefix spaces in the stress
count are literally stresses of the induced subframeworks, and their
dimensions obey the ordinary rank/stress identity.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V] {d : ℕ}
variable {G H : SimpleGraph V}

def edgeInclusion (h : H ≤ G) : Edge H ↪ Edge G where
  toFun e := ⟨e.val, SimpleGraph.edgeSet_mono h e.property⟩
  inj' := by intro e f hef; exact Subtype.ext (congrArg (fun e : Edge G => e.val) hef)

def subgraphEdgeSet (G H : SimpleGraph V) : Set (Edge G) :=
  {e | e.val ∈ H.edgeSet}

def subgraphEdgeEquiv (h : H ≤ G) : Edge H ≃ subgraphEdgeSet G H where
  toFun e := ⟨edgeInclusion h e, e.property⟩
  invFun e := ⟨e.val.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def extendEdgeCoefficients (h : H ≤ G) : (Edge H → ℝ) →ₗ[ℝ] (Edge G → ℝ) where
  toFun ω e := if he : e.val ∈ H.edgeSet then ω ⟨e.val, he⟩ else 0
  map_add' ω η := by ext e; split_ifs with he <;> simp [he]
  map_smul' a ω := by ext e; split_ifs with he <;> simp [he]

def restrictEdgeCoefficients (h : H ≤ G) : (Edge G → ℝ) →ₗ[ℝ] (Edge H → ℝ) :=
  LinearMap.pi fun e => LinearMap.proj (edgeInclusion h e)

@[simp] theorem extendEdgeCoefficients_inside (h : H ≤ G) (ω : Edge H → ℝ)
    (e : Edge H) : extendEdgeCoefficients h ω (edgeInclusion h e) = ω e := by
  simp [extendEdgeCoefficients, edgeInclusion, e.property]

@[simp] theorem extendEdgeCoefficients_outside (h : H ≤ G) (ω : Edge H → ℝ)
    (e : Edge G) (he : e.val ∉ H.edgeSet) : extendEdgeCoefficients h ω e = 0 := by
  simp [extendEdgeCoefficients, he]

@[simp] theorem restrict_extendEdgeCoefficients (h : H ≤ G) (ω : Edge H → ℝ) :
    restrictEdgeCoefficients h (extendEdgeCoefficients h ω) = ω := by
  ext e
  exact extendEdgeCoefficients_inside h ω e

theorem extend_restrictEdgeCoefficients (h : H ≤ G) (ω : Edge G → ℝ)
    (hω : ∀ e, e.val ∉ H.edgeSet → ω e = 0) :
    extendEdgeCoefficients h (restrictEdgeCoefficients h ω) = ω := by
  ext e
  by_cases he : e.val ∈ H.edgeSet
  · simp [extendEdgeCoefficients, restrictEdgeCoefficients, edgeInclusion, he]
  · simp [extendEdgeCoefficients, he, hω e he]

theorem sum_extendEdgeCoefficients (h : H ≤ G) (ω : Edge H → ℝ)
    (f : Edge G → ℝ) :
    (∑ e : Edge G, extendEdgeCoefficients h ω e * f e) =
      ∑ e : Edge H, ω e * f (edgeInclusion h e) := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun e : Edge G => e ∈ subgraphEdgeSet G H)
    (fun e => extendEdgeCoefficients h ω e * f e)
  have hout : (∑ e : {e : Edge G // e ∉ subgraphEdgeSet G H},
      extendEdgeCoefficients h ω e.val * f e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [extendEdgeCoefficients_outside h ω e.val e.property, zero_mul]
  rw [hout, add_zero] at hsplit
  rw [← hsplit]
  have hreindex := Equiv.sum_comp (subgraphEdgeEquiv h)
    (fun e : subgraphEdgeSet G H => extendEdgeCoefficients h ω e.val * f e.val)
  change (∑ e : Edge H,
      extendEdgeCoefficients h ω (edgeInclusion h e) * f (edgeInclusion h e)) =
    ∑ e : subgraphEdgeSet G H, extendEdgeCoefficients h ω e.val * f e.val at hreindex
  simpa only [extendEdgeCoefficients_inside] using hreindex.symm

/-- Zero extension preserves the literal virtual-work functional. -/
theorem stressOperator_extendEdgeCoefficients (h : H ≤ G) (p : Placement V d)
    (ω : Edge H → ℝ) :
    stressOperator G p (extendEdgeCoefficients h ω) = stressOperator H p ω := by
  apply LinearMap.ext
  intro u
  rw [stressOperator_apply, stressOperator_apply, sum_extendEdgeCoefficients]
  rfl

/-- The actual subgraph stress space is exactly the parent stress space
supported on the subgraph edges. -/
def subgraphStressEquiv (h : H ≤ G) (p : Placement V d) :
    StressSpace H p ≃ₗ[ℝ] supportedOn (StressSpace G p) (subgraphEdgeSet G H) where
  toFun ω := ⟨extendEdgeCoefficients h ω.val, by
    constructor
    · rw [StressSpace, LinearMap.mem_ker, stressOperator_extendEdgeCoefficients]
      exact LinearMap.mem_ker.mp ω.property
    · intro e he
      exact extendEdgeCoefficients_outside h ω.val e he⟩
  invFun ω := ⟨restrictEdgeCoefficients h ω.val, by
    rw [StressSpace, LinearMap.mem_ker]
    rw [← stressOperator_extendEdgeCoefficients h p,
      extend_restrictEdgeCoefficients h ω.val ω.property.2]
    exact LinearMap.mem_ker.mp ω.property.1⟩
  left_inv ω := Subtype.ext (restrict_extendEdgeCoefficients h ω.val)
  right_inv ω := Subtype.ext (extend_restrictEdgeCoefficients h ω.val ω.property.2)
  map_add' ω η := Subtype.ext (map_add (extendEdgeCoefficients h) ω.val η.val)
  map_smul' a ω := Subtype.ext (map_smul (extendEdgeCoefficients h) a ω.val)

/-- The rank/stress identity for the actual supported subgraph space. -/
theorem rigidityRank_add_supportedStress_dimension (h : H ≤ G) (p : Placement V d) :
    rigidityRank H p +
      Module.finrank ℝ (supportedOn (StressSpace G p) (subgraphEdgeSet G H)) =
        Fintype.card (Edge H) := by
  rw [← (subgraphStressEquiv h p).finrank_eq]
  exact rigidityRank_add_stress_dimension H p

end
end Papers.Rigidity.BarJoint

end
end BundleSource0037

section BundleSource0038
/- Source: Papers/RigidityLocalStressSum.lean -/





@[expose] public section

/-!
# The actual direct sum of local body stresses

Each local space consists of ordinary graph stresses supported on the
complete graph of one maximal body.  The copied-star theorem proves
both injectivity of their finite sum and its compatibility with every
induced vertex set.  No dimension count substitutes for this support
identity.

These local stress spaces supply the denominator in Proposition 6.2.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

abbrev Body (G : SimpleGraph V) := {S : Finset V // IsBody G S}

/-- The actual edges having both endpoints in the displayed vertex set. -/
def vertexEdgeSet (G : SimpleGraph V) (T : Finset V) : Set (Edge G) :=
  {e | ∀ v, v ∈ e.val → v ∈ T}

def localStressSpace (G : SimpleGraph V) (p : Placement V 3) (C : Body G) :
    Submodule ℝ (Edge G → ℝ) :=
  supportedOn (StressSpace G p) (vertexEdgeSet G C.val)

def localStressSum (G : SimpleGraph V) (p : Placement V 3) :
    (∀ C : Body G, localStressSpace G p C) →ₗ[ℝ] (Edge G → ℝ) :=
  ∑ C : Body G, (localStressSpace G p C).subtype.comp (LinearMap.proj C)

@[simp] theorem localStressSum_apply
    (G : SimpleGraph V) (p : Placement V 3)
    (a : ∀ C : Body G, localStressSpace G p C) :
    localStressSum G p a = ∑ C : Body G, (a C).val := by
  simp [localStressSum]

theorem localStressSum_mem
    (G : SimpleGraph V) (p : Placement V 3)
    (a : ∀ C : Body G, localStressSpace G p C) :
    localStressSum G p a ∈ StressSpace G p := by
  rw [localStressSum_apply]
  exact Submodule.sum_mem _ (fun C _ => (a C).property.1)

theorem local_star_nonzero_endpoints
    (G : SimpleGraph V) (p : Placement V 3) (C : Body G)
    (a : localStressSpace G p C) (v w : V)
    (ha : starCoordinates G v a.val w ≠ 0) :
    v ∈ C.val ∧ w ∈ C.val ∧ w ≠ v := by
  by_cases hvw : G.Adj v w
  · rw [starCoordinates_of_adj G v w a.val hvw] at ha
    have he : (⟨s(v,w), hvw⟩ : Edge G) ∈ vertexEdgeSet G C.val := by
      by_contra hne
      exact ha (a.property.2 _ hne)
    exact ⟨he v (Sym2.mem_mk_left v w), he w (Sym2.mem_mk_right v w), hvw.ne.symm⟩
  · exact False.elim (ha (starCoordinates_of_not_adj G v w a.val hvw))

theorem local_star_zero_of_not_mem
    (G : SimpleGraph V) (p : Placement V 3) (C : Body G)
    (a : localStressSpace G p C) (v : V) (hv : v ∉ C.val) (w : V) :
    starCoordinates G v a.val w = 0 := by
  by_contra hn
  exact hv (local_star_nonzero_endpoints G p C a v w hn).1

/-- At an omitted vertex, support of the aggregate makes all actual
copied body-star coefficients vanish separately. -/
theorem omitted_vertex_local_stars_zero
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : ∀ C : Body M.graph, localStressSpace M.graph p C)
    (ha : ∀ e, e ∉ vertexEdgeSet M.graph T → localStressSum M.graph p a e = 0)
    (v : V) (hv : v ∉ T) :
    ∀ C : Body M.graph, ∀ w, starCoordinates M.graph v (a C).val w = 0 := by
  let I := {C : Body M.graph // v ∈ C.val}
  let b : I → V → ℝ := fun i => starCoordinates M.graph v (a i.val).val
  have hfull (w : V) :
      (∑ C : Body M.graph, starCoordinates M.graph v (a C).val w) = 0 := by
    have hmap := congrFun (map_sum (starCoordinates M.graph v)
      (fun C : Body M.graph => (a C).val) Finset.univ) w
    rw [← localStressSum_apply] at hmap
    simp only [Finset.sum_apply] at hmap
    rw [← hmap]
    by_cases h : M.graph.Adj v w
    · rw [starCoordinates_of_adj _ _ _ _ h]
      apply ha
      intro he
      exact hv (he v (Sym2.mem_mk_left v w))
    · exact starCoordinates_of_not_adj _ _ _ _ h
  have hcancel (w : V) : ∑ i : I, b i w = 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun C : Body M.graph => v ∈ C.val)
      (fun C => starCoordinates M.graph v (a C).val w)
    have hout : (∑ C : {C : Body M.graph // v ∉ C.val},
        starCoordinates M.graph v (a C.val).val w) = 0 := by
      apply Finset.sum_eq_zero
      intro C _
      exact local_star_zero_of_not_mem M.graph p C.val (a C.val) v C.property w
    rw [hout, add_zero, hfull] at hsplit
    exact hsplit
  have hsupport (i : I) (w : V) (hi : b i w ≠ 0) : w ∈ i.val.val.erase v := by
    have hw := local_star_nonzero_endpoints M.graph p i.val (a i.val) v w hi
    exact Finset.mem_erase.mpr ⟨hw.2.2, hw.2.1⟩
  have hz := copied_star_coefficients_eq_zero M p hp v (fun i : I => i.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => i.val.property) (fun i => i.property) b hsupport hcancel
    (fun i => stress_starCoordinates_balance M.graph p (a i.val).val
      (a i.val).property.1 v)
  intro C w
  by_cases hC : v ∈ C.val
  · exact hz ⟨C, hC⟩ w
  · exact local_star_zero_of_not_mem M.graph p C (a C) v hC w

/-- The literal induced-prefix support equality for the finite sum of
local stresses.  This is the support assertion in Proposition 6.2. -/
theorem localStressSum_supported_iff
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : ∀ C : Body M.graph, localStressSpace M.graph p C) :
    (∀ e, e ∉ vertexEdgeSet M.graph T → localStressSum M.graph p a e = 0) ↔
      ∀ C e, e ∉ vertexEdgeSet M.graph T → (a C).val e = 0 := by
  constructor
  · intro ha C e he
    change ¬∀ v, v ∈ e.val → v ∈ T at he
    push_neg at he
    obtain ⟨v, hve, hv⟩ := he
    have hz := omitted_vertex_local_stars_zero M p hp T a ha v hv C
      (incidentOther M.graph v ⟨e, hve⟩)
    simpa only [starCoordinates_incidentOther] using hz
  · intro ha e he
    rw [localStressSum_apply, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun C _ => ha C e he)

/-- Ordinary stresses on the distinct maximal bodies have a genuine
direct sum inside the ambient graph stress space. -/
theorem localStressSum_injective
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) :
    Function.Injective (localStressSum M.graph p) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro a ha
    have hz : localStressSum M.graph p a = 0 := LinearMap.mem_ker.mp ha
    have hlocal := (localStressSum_supported_iff M p hp ∅ a).mp
      (fun e _ => congrFun hz e)
    change a = 0
    funext C
    apply Subtype.ext
    funext e
    apply hlocal C e
    intro he
    exact Finset.notMem_empty e.val.out.1
      (he e.val.out.1 (Sym2.out_fst_mem e.val))
  · exact bot_le

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0038

section BundleSource0039
/- Source: Papers/RigidityCompleteFragmentMotions.lean -/




@[expose] public section

/-!
# Complete fragments of every cardinality

The body-load exact sequences use fragments with zero, one, or two
vertices.  This file proves that their actual complete-graph motion
kernels still consist of restrictions of Euclidean twists.  In the
two-point case the angular velocity is constructed by the ordinary
vector triple-product identity; no six-dimensional-motion assumption
is made at small cardinalities.

The construction includes complete fragments of every finite size.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint Matrix
open scoped Classical Matrix BigOperators

variable {V : Type} [Fintype V]

theorem exists_twist_fitting_two_points
    (p q u v : Vec3) (hpq : p ≠ q)
    (hbar : (q - p) ⬝ᵥ (v - u) = 0) :
    ∃ X : Twist, evaluateTwist p X = u ∧ evaluateTwist q X = v := by
  let d := q - p
  let e := v - u
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdd : d ⬝ᵥ d ≠ 0 := by
    intro hz
    exact hd (dotProduct_self_eq_zero.mp hz)
  have hed : e ⬝ᵥ d = 0 := by
    rw [dotProduct_comm]
    exact hbar
  let ω := (d ⬝ᵥ d)⁻¹ • (d ⨯₃ e)
  have hω : ω ⨯₃ d = e := by
    dsimp only [ω]
    rw [map_smul, LinearMap.smul_apply, cross_cross_eq_smul_sub_smul,
      hed, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ hdd, one_smul]
  refine ⟨(ω, u - ω ⨯₃ p), ?_, ?_⟩
  · simp only [evaluateTwist_apply, sub_add_cancel]
  · rw [evaluateTwist_apply]
    have hcross : ω ⨯₃ q - ω ⨯₃ p = e := by
      rw [← map_sub]
      exact hω
    ext i
    have hi := congrFun hcross i
    change u i - (ω ⨯₃ p) i + (ω ⨯₃ q) i = v i
    change (ω ⨯₃ q) i - (ω ⨯₃ p) i = v i - u i at hi
    linarith

theorem GeneralPosition.InGeneralPosition.injective
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    Function.Injective p := by
  intro v w hpvw
  by_contra hvw
  let f : Fin 2 ↪ V := ⟨![v, w], Matrix.injective_pair_iff_ne.mpr hvw⟩
  have hlin := hp (1 : Fin 4) f
  have hn := hlin.ne_zero (0 : Fin 1)
  apply hn
  change p w - p v = 0
  rw [hpvw, sub_self]

/-- Every infinitesimal motion of a complete fragment is an actual
Euclidean twist restriction, including the empty and tiny fragments. -/
theorem exists_twist_of_completeMotion_all
    (p u : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (hu : IsInfinitesimalMotion (SimpleGraph.completeGraph V) p u) :
    ∃ X : Twist, ∀ v, u v = evaluateTwist (p v) X := by
  by_cases hlarge : 3 ≤ Fintype.card V
  · obtain ⟨f : Fin 3 ↪ V⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin 3) (β := V) (by simpa using hlarge)
    exact exists_twist_of_completeMotion p u hp f hu
  · have hsmall : Fintype.card V ≤ 2 := by omega
    by_cases htwo : Fintype.card V = 2
    · have hc : (Finset.univ : Finset V).card = 2 := by simpa using htwo
      obtain ⟨v, w, hvw, hVW⟩ := Finset.card_eq_two.mp hc
      have hpvw : p v ≠ p w := (GeneralPosition.InGeneralPosition.injective p hp).ne hvw
      have hbar : (p w - p v) ⬝ᵥ (u w - u v) = 0 :=
        (isInfinitesimalMotion_iff (SimpleGraph.completeGraph V) p u).mp hu
          w v (Ne.symm hvw)
      obtain ⟨X, hXv, hXw⟩ := exists_twist_fitting_two_points (p v) (p w) (u v) (u w)
        hpvw hbar
      refine ⟨X, ?_⟩
      intro x
      have hx : x = v ∨ x = w := by
        simpa only [hVW, Finset.mem_insert, Finset.mem_singleton] using
          (Finset.mem_univ x : x ∈ (Finset.univ : Finset V))
      rcases hx with rfl | rfl
      · exact hXv.symm
      · exact hXw.symm
    · by_cases hone : Fintype.card V = 1
      · have hc : (Finset.univ : Finset V).card = 1 := by simpa using hone
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
        refine ⟨(0, u v), ?_⟩
        intro w
        have hw : w = v := by simpa only [hv, Finset.mem_singleton] using Finset.mem_univ w
        subst w
        simp [evaluateTwist_apply]
      · have hz : Fintype.card V = 0 := by omega
        letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
        exact ⟨0, fun v => isEmptyElim v⟩

theorem complete_kernel_eq_twist_range_all
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    (rigidityOperator (SimpleGraph.completeGraph V) p).ker =
      (globalTwistOperator p).range := by
  apply le_antisymm
  · intro u hu
    obtain ⟨X, hX⟩ := exists_twist_of_completeMotion_all p u hp hu
    exact ⟨X, funext fun v => (hX v).symm⟩
  · rintro u ⟨X, rfl⟩
    exact globalTwist_isMotion (SimpleGraph.completeGraph V) p X

end Papers.Rigidity

end
end
end BundleSource0039

section BundleSource0040
/- Source: Papers/RigidityFragmentLoads.lean -/






@[expose] public section

/-!
# Literal balanced loads and complete-fragment resolution

Loads are ordinary vectors on the actual vertices.  Their force and
moment equations are proved equivalent to annihilating Euclidean twist
restrictions.  Duality then resolves every balanced load by bar
coefficients on the complete fragment, at every fragment size.

The definition of balanced loads does not encode representability as
an assumption.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint Matrix
open scoped Classical BigOperators Matrix

variable {V : Type} [Fintype V]

/-- The ordinary Euclidean virtual-work pairing, with no quotient or
equilibrium condition imposed on either argument. -/
def loadWorkEquiv : Velocity V 3 ≃ₗ[ℝ] Module.Dual ℝ (Velocity V 3) :=
  let e := (LinearEquiv.curry ℝ ℝ V (Fin 3)).symm
  (e.trans (dotProductEquiv ℝ (V × Fin 3))).trans e.dualMap

@[simp] theorem loadWorkEquiv_apply (F u : Velocity V 3) :
    loadWorkEquiv F u = ∑ v, F v ⬝ᵥ u v := by
  change (∑ x : V × Fin 3, F x.1 x.2 * u x.1 x.2) = ∑ v, F v ⬝ᵥ u v
  rw [Fintype.sum_prod_type]
  rfl

theorem loadWorkEquiv_comm (F u : Velocity V 3) :
    loadWorkEquiv F u = loadWorkEquiv u F := by
  rw [loadWorkEquiv_apply, loadWorkEquiv_apply]
  exact Finset.sum_congr rfl (fun v _ => dotProduct_comm _ _)

theorem stressOperator_single
    (G : SimpleGraph V) (p u : Placement V 3) (e : Edge G) :
    stressOperator G p (Pi.single e 1) u = unorderedFunctional p e.val u := by
  change (Pi.single e (1 : ℝ) : Edge G → ℝ) ⬝ᵥ
    (fun f : Edge G => unorderedFunctional p f.val u) = _
  exact single_one_dotProduct e _

/-- Actual forces exerted by an unordered-edge coefficient vector. -/
def forceOperator (G : SimpleGraph V) (p : Placement V 3) :
    (Edge G → ℝ) →ₗ[ℝ] Velocity V 3 :=
  loadWorkEquiv.symm.toLinearMap.comp (stressOperator G p)

@[simp] theorem loadWork_forceOperator
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    loadWorkEquiv (forceOperator G p a) = stressOperator G p a := by
  exact loadWorkEquiv.apply_symm_apply _

theorem forceOperator_eq_zero_iff
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    forceOperator G p a = 0 ↔ a ∈ StressSpace G p := by
  rw [StressSpace, LinearMap.mem_ker]
  constructor
  · intro ha
    rw [← loadWork_forceOperator, ha, map_zero]
  · intro ha
    apply loadWorkEquiv.injective
    rw [loadWork_forceOperator, ha, map_zero]

theorem forceOperator_vertex
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) (v : V) :
    forceOperator G p a v =
      ∑ e : IncidentEdge G v, a e.val • (p v - p (incidentOther G v e)) := by
  have hwork (z : Vec3) :
      forceOperator G p a v ⬝ᵥ z =
        (∑ e : IncidentEdge G v, a e.val • (p v - p (incidentOther G v e))) ⬝ᵥ z := by
    have h := congrArg (fun f : Module.Dual ℝ (Velocity V 3) => f (Pi.single v z))
      (loadWork_forceOperator G p a)
    simp only [loadWorkEquiv_apply] at h
    have hleft : (∑ w, forceOperator G p a w ⬝ᵥ (Pi.single v z : Velocity V 3) w) =
        forceOperator G p a v ⬝ᵥ z := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        simp [Pi.single_apply, hw, Ne.symm hw]
      · simp
    rw [hleft] at h
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun e : Edge G => v ∈ e.val)
      (fun e : Edge G => a e * unorderedFunctional p e.val (Pi.single v z))
    have hout : (∑ e : {e : Edge G // v ∉ e.val},
        a e.val * unorderedFunctional p e.val.val (Pi.single v z)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [unorderedFunctional_impulse_of_not_incident G p v z e.val e.property, mul_zero]
    rw [hout, add_zero] at hsplit
    have hstress : stressOperator G p a (Pi.single v z) =
        ∑ e : Edge G, a e * unorderedFunctional p e.val (Pi.single v z) := by
      simp only [stressOperator_apply, unorderedFunctional_out]
    rw [hstress, ← hsplit] at h
    rw [h, sum_dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    simp only [smul_dotProduct, smul_eq_mul,
      unorderedFunctional_impulse_of_incident G p v z]
  ext i
  simpa using hwork (Pi.single i 1)

theorem work_on_globalTwist (p F : Placement V 3) (X : Twist) :
    loadWorkEquiv F (globalTwistOperator p X) =
      (∑ v, F v) ⬝ᵥ X.2 + (∑ v, p v ⨯₃ F v) ⬝ᵥ X.1 := by
  rw [loadWorkEquiv_apply]
  simp only [globalTwistOperator_apply, evaluateTwist_apply, dotProduct_add,
    Finset.sum_add_distrib]
  rw [← sum_dotProduct]
  congr 1
  calc
    (∑ v, F v ⬝ᵥ X.1 ⨯₃ p v) = ∑ v, X.1 ⬝ᵥ p v ⨯₃ F v := by
      apply Finset.sum_congr rfl
      intro v _
      exact triple_product_permutation _ _ _
    _ = X.1 ⬝ᵥ (∑ v, p v ⨯₃ F v) := (dotProduct_sum _ _ _).symm
    _ = (∑ v, p v ⨯₃ F v) ⬝ᵥ X.1 := dotProduct_comm _ _

/-- A load is balanced precisely when its total force and total moment
are zero.  The annihilator presentation only supplies its linear space. -/
def balancedLoads (p : Placement V 3) : Submodule ℝ (Velocity V 3) :=
  (globalTwistOperator p).range.dualAnnihilator.comap loadWorkEquiv.toLinearMap

theorem mem_balancedLoads_iff (p F : Placement V 3) :
    F ∈ balancedLoads p ↔ (∑ v, F v = 0) ∧ (∑ v, p v ⨯₃ F v = 0) := by
  have hmem : F ∈ balancedLoads p ↔
      ∀ X : Twist, loadWorkEquiv F (globalTwistOperator p X) = 0 := by
    simp only [balancedLoads, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
      LinearMap.mem_range, forall_exists_index]
    constructor
    · intro h X
      exact h _ X rfl
    · intro h u X hX
      subst u
      exact h X
  rw [hmem]
  constructor
  · intro h
    constructor
    · ext i
      have hi := h (0, Pi.single i 1)
      simpa only [work_on_globalTwist, dotProduct_zero, add_zero, dotProduct_single,
        mul_one, Pi.zero_apply] using hi
    · ext i
      have hi := h (Pi.single i 1, 0)
      simpa only [work_on_globalTwist, dotProduct_zero, zero_add, dotProduct_single,
        mul_one, Pi.zero_apply] using hi
  · rintro ⟨hF, hM⟩ X
    rw [work_on_globalTwist, hF, hM, zero_dotProduct, zero_dotProduct, add_zero]

theorem stressOperator_range_eq_annihilator (G : SimpleGraph V) (p : Placement V 3) :
    (stressOperator G p).range =
      (undirectedRigidityOperator G p).ker.dualAnnihilator := by
  rw [stressOperator, LinearMap.range_comp_of_range_eq_top _
    (dotProductEquiv ℝ (Edge G)).range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- Every literal balanced load is resolved by ordinary bar coefficients
on the complete fragment.  Empty, singleton and two-point fragments are
included by the preceding complete-kernel theorem. -/
theorem balanced_iff_complete_bar_load
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (F : Placement V 3) :
    F ∈ balancedLoads p ↔
      ∃ a : Edge (SimpleGraph.completeGraph V) → ℝ,
        forceOperator (SimpleGraph.completeGraph V) p a = F := by
  change loadWorkEquiv F ∈ (globalTwistOperator p).range.dualAnnihilator ↔ _
  rw [← complete_kernel_eq_twist_range_all p hp,
    ← ker_undirectedRigidityOperator,
    ← stressOperator_range_eq_annihilator]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, loadWorkEquiv.injective ?_⟩
    rw [loadWork_forceOperator, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨a, (loadWork_forceOperator _ _ _).symm⟩

/-- A complete graph on the displayed subset, with the other ambient
vertices isolated.  This keeps all prefix spaces in common coordinates. -/
def cliqueOn (S : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ v ∈ S ∧ w ∈ S
  symm := by
    constructor
    rintro v w ⟨hvw, hv, hw⟩
    exact ⟨Ne.symm hvw, hw, hv⟩
  loopless := by constructor; intro v; simp

theorem cliqueOn_le {G : SimpleGraph V} (S : Finset V)
    (hS : G.IsClique (S : Set V)) : cliqueOn S ≤ G := by
  intro v w h
  exact hS h.2.1 h.2.2 h.1

def balancedLoadsOn (p : Placement V 3) (S : Finset V) :
    Submodule ℝ (Velocity V 3) where
  carrier := {F | F ∈ balancedLoads p ∧ ∀ v, v ∉ S → F v = 0}
  zero_mem' := ⟨(balancedLoads p).zero_mem, by simp⟩
  add_mem' := by
    rintro F H ⟨hF, hFS⟩ ⟨hH, hHS⟩
    exact ⟨(balancedLoads p).add_mem hF hH, fun v hv => by simp [hFS v hv, hHS v hv]⟩
  smul_mem' := by
    rintro c F ⟨hF, hFS⟩
    exact ⟨(balancedLoads p).smul_mem c hF, fun v hv => by simp [hFS v hv]⟩

theorem balanced_load_annihilates_twist
    (p F : Placement V 3) (hF : F ∈ balancedLoads p) (X : Twist) :
    loadWorkEquiv F (globalTwistOperator p X) = 0 := by
  change loadWorkEquiv F ∈ (globalTwistOperator p).range.dualAnnihilator at hF
  exact (Submodule.mem_dualAnnihilator (loadWorkEquiv F)).mp hF _ ⟨X, rfl⟩

theorem forceOperator_balanced
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    forceOperator G p a ∈ balancedLoads p := by
  have htwist : (globalTwistOperator p).range ≤ (undirectedRigidityOperator G p).ker := by
    rw [ker_undirectedRigidityOperator]
    rintro u ⟨X, rfl⟩
    exact globalTwist_isMotion G p X
  have hstress : stressOperator G p a ∈
      (undirectedRigidityOperator G p).ker.dualAnnihilator := by
    rw [← stressOperator_range_eq_annihilator]
    exact ⟨a, rfl⟩
  change loadWorkEquiv (forceOperator G p a) ∈
    (globalTwistOperator p).range.dualAnnihilator
  rw [loadWork_forceOperator]
  exact Submodule.dualAnnihilator_anti htwist hstress

theorem clique_force_zero_outside
    (p : Placement V 3) (S : Finset V) (a : Edge (cliqueOn S) → ℝ)
    (v : V) (hv : v ∉ S) : forceOperator (cliqueOn S) p a v = 0 := by
  letI : IsEmpty (IncidentEdge (cliqueOn S) v) :=
    ⟨fun e => hv (incidentOther_adj (cliqueOn S) v e).2.1⟩
  rw [forceOperator_vertex]
  simp

/-- Complete-fragment surjectivity in fixed ambient coordinates.  The
right side is the actual force/moment space with literal support in S. -/
theorem range_clique_forceOperator
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (S : Finset V) :
    (forceOperator (cliqueOn S) p).range = balancedLoadsOn p S := by
  apply le_antisymm
  · rintro F ⟨a, rfl⟩
    exact ⟨forceOperator_balanced _ p a, clique_force_zero_outside p S a⟩
  · intro F hF
    have hwork : loadWorkEquiv F ∈ (undirectedRigidityOperator (cliqueOn S) p).ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      rw [ker_undirectedRigidityOperator] at hu
      let e : S ↪ V := Function.Embedding.subtype _
      have hpS := GeneralPosition.InGeneralPosition.comp_embedding p hp e
      have huS : IsInfinitesimalMotion (SimpleGraph.completeGraph S) (p ∘ e) (u ∘ e) := by
        rw [isInfinitesimalMotion_iff]
        intro v w hvw
        exact (isInfinitesimalMotion_iff (cliqueOn S) p u).mp hu v.val w.val
          ⟨fun h => hvw (Subtype.ext h), v.property, w.property⟩
      obtain ⟨X, hX⟩ := exists_twist_of_completeMotion_all (p ∘ e) (u ∘ e) hpS huS
      have heq : loadWorkEquiv F u = loadWorkEquiv F (globalTwistOperator p X) := by
        rw [loadWorkEquiv_apply, loadWorkEquiv_apply]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ S
        · rw [show u v = evaluateTwist (p v) X from hX ⟨v, hv⟩]
          rfl
        · rw [hF.2 v hv, zero_dotProduct, zero_dotProduct]
      rw [heq]
      exact balanced_load_annihilates_twist p F hF.1 X
    rw [← stressOperator_range_eq_annihilator] at hwork
    obtain ⟨a, ha⟩ := hwork
    refine ⟨a, loadWorkEquiv.injective ?_⟩
    rw [loadWork_forceOperator, ha]

theorem forceOperator_rank (G : SimpleGraph V) (p : Placement V 3) :
    Module.finrank ℝ (forceOperator G p).range = rigidityRank G p := by
  have hker : (forceOperator G p).ker = StressSpace G p := by
    ext a
    exact forceOperator_eq_zero_iff G p a
  have hF := (forceOperator G p).finrank_range_add_finrank_ker
  have hS := (stressOperator G p).finrank_range_add_finrank_ker
  rw [hker] at hF
  rw [stressOperator_rank] at hS
  change rigidityRank G p + Module.finrank ℝ (StressSpace G p) = _ at hS
  omega

theorem balancedLoadsOn_finrank
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (S : Finset V) :
    Module.finrank ℝ (balancedLoadsOn p S) = rigidityRank (cliqueOn S) p := by
  rw [← range_clique_forceOperator p hp S, forceOperator_rank]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0040

section BundleSource0041
/- Source: Papers/RigidityBodyLoadRank.lean -/





@[expose] public section

/-!
# Actual compatible body loads and the full prefix rank formula

Each member of the body-load family is an ordinary balanced vector load
supported on its complete fragment.  Compatibility is cancellation at
each actual vertex.  The dual test map has exactly the induced graph's
ordinary motion kernel.  Rank-nullity therefore yields Proposition 6.2's
rank identity for every induced vertex set, including empty and tiny
fragments.  The family is not defined in terms of the desired rank.

The rank calculation uses the actual force-balance maps of Proposition 6.2.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint Matrix
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def maskedGraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ T ∧ w ∈ T
  symm := by constructor; rintro v w ⟨h, hv, hw⟩; exact ⟨h.symm, hw, hv⟩
  loopless := by constructor; intro v; rintro ⟨h, _⟩; exact G.loopless.irrefl v h

theorem maskedGraph_eq_liftInduce (G : SimpleGraph V) (T : Finset V) :
    maskedGraph G T = liftGraph T (G.induce (T : Set V)) := by
  ext v w
  simp only [maskedGraph, liftGraph, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨h, hv, hw⟩
    exact ⟨hv, hw, h⟩
  · rintro ⟨hv, hw, h⟩
    exact ⟨h, hv, hw⟩

theorem cliqueOn_eq_liftComplete (T : Finset V) :
    cliqueOn T = liftGraph T (SimpleGraph.completeGraph T) := by
  ext v w
  constructor
  · rintro ⟨hne, hv, hw⟩
    exact ⟨hv, hw, fun h => hne (congrArg Subtype.val h)⟩
  · rintro ⟨hv, hw, hne⟩
    exact ⟨fun h => hne (Subtype.ext h), hv, hw⟩

abbrev BodyBalancedFamily (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :=
  ∀ C : Body G, balancedLoadsOn p (C.val ∩ T)

/-- Add all load copies at their actual vertex coordinates. -/
def totalBodyLoad (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyBalancedFamily G p T →ₗ[ℝ] Velocity V 3 :=
  ∑ C : Body G, (balancedLoadsOn p (C.val ∩ T)).subtype.comp (LinearMap.proj C)

@[simp] theorem totalBodyLoad_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) :
    totalBodyLoad G p T F = ∑ C : Body G, (F C).val := by
  simp [totalBodyLoad]

@[simp] theorem totalBodyLoad_single
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (C : Body G) (F : balancedLoadsOn p (C.val ∩ T)) :
    totalBodyLoad G p T (Pi.single C F) = F.val := by
  rw [totalBodyLoad_apply, Finset.sum_eq_single C]
  · simp
  · intro D _ hDC
    simp [Pi.single_eq_of_ne hDC]
  · simp

/-- The literal compatible load space of Section 6 at the prefix T. -/
def compatibleBodyLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (BodyBalancedFamily G p T) :=
  (totalBodyLoad G p T).ker

theorem mem_compatibleBodyLoads_iff
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) :
    F ∈ compatibleBodyLoads G p T ↔ ∀ v, ∑ C : Body G, (F C).val v = 0 := by
  simp only [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_apply,
    funext_iff, Finset.sum_apply, Pi.zero_apply]

/-- The constraints tested against actual balanced body loads. -/
def bodyLoadTest (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Velocity V 3 →ₗ[ℝ] Module.Dual ℝ (BodyBalancedFamily G p T) :=
  (totalBodyLoad G p T).dualMap.comp loadWorkEquiv.toLinearMap

theorem fragment_le_masked (G : SimpleGraph V) (T : Finset V) (C : Body G) :
    cliqueOn (C.val ∩ T) ≤ maskedGraph G T := by
  intro v w h
  exact ⟨C.property.2.1 (Finset.mem_inter.mp h.2.1).1
    (Finset.mem_inter.mp h.2.2).1 h.1,
    (Finset.mem_inter.mp h.2.1).2, (Finset.mem_inter.mp h.2.2).2⟩

/-- This is the ordinary graph-motion kernel, proved by testing actual
single-bar loads in bodies containing the edge. -/
theorem ker_bodyLoadTest
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    (bodyLoadTest G p T).ker = (rigidityOperator (maskedGraph G T) p).ker := by
  ext u
  constructor
  · intro hu
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro v w h
    obtain ⟨S, hS, hv, hw⟩ := hG.edge_in_body h.1
    let C : Body G := ⟨S, hS⟩
    have hadj : (cliqueOn (C.val ∩ T)).Adj v w :=
      ⟨h.1.ne, Finset.mem_inter.mpr ⟨hv, h.2.1⟩,
        Finset.mem_inter.mpr ⟨hw, h.2.2⟩⟩
    let e : Edge (cliqueOn (C.val ∩ T)) := ⟨s(v,w), hadj⟩
    let a : Edge (cliqueOn (C.val ∩ T)) → ℝ := Pi.single e 1
    have hF : forceOperator (cliqueOn (C.val ∩ T)) p a ∈
        balancedLoadsOn p (C.val ∩ T) := by
      rw [← range_clique_forceOperator p hp (C.val ∩ T)]
      exact ⟨a, rfl⟩
    let F : balancedLoadsOn p (C.val ∩ T) := ⟨_, hF⟩
    have hz := congrArg (fun f : Module.Dual ℝ (BodyBalancedFamily G p T) =>
      f (Pi.single C F)) (LinearMap.mem_ker.mp hu)
    change loadWorkEquiv u (totalBodyLoad G p T (Pi.single C F)) = 0 at hz
    rw [totalBodyLoad_single, loadWorkEquiv_comm] at hz
    change loadWorkEquiv (forceOperator (cliqueOn (C.val ∩ T)) p a) u = 0 at hz
    rw [loadWork_forceOperator, stressOperator_single] at hz
    exact hz
  · intro hu
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro F
    change loadWorkEquiv u (totalBodyLoad G p T F) = 0
    rw [totalBodyLoad_apply, map_sum]
    apply Finset.sum_eq_zero
    intro C _
    rw [loadWorkEquiv_comm]
    have huC : u ∈ (undirectedRigidityOperator (cliqueOn (C.val ∩ T)) p).ker := by
      rw [ker_undirectedRigidityOperator]
      rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
      intro v w h
      exact (isInfinitesimalMotion_iff (maskedGraph G T) p u).mp hu v w
        (fragment_le_masked G T C h)
    obtain ⟨a, ha⟩ : (F C).val ∈ (forceOperator (cliqueOn (C.val ∩ T)) p).range :=
      (range_clique_forceOperator p hp (C.val ∩ T)).ge (F C).property
    rw [← ha, loadWork_forceOperator]
    have hstress : stressOperator (cliqueOn (C.val ∩ T)) p a ∈
        (undirectedRigidityOperator (cliqueOn (C.val ∩ T)) p).ker.dualAnnihilator := by
      rw [← stressOperator_range_eq_annihilator]
      exact ⟨a, rfl⟩
    exact (Submodule.mem_dualAnnihilator
      (stressOperator (cliqueOn (C.val ∩ T)) p a)).mp hstress u huC

theorem totalBodyLoad_rank
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ (totalBodyLoad G p T).range = rigidityRank (maskedGraph G T) p := by
  have htest : Module.finrank ℝ (bodyLoadTest G p T).range =
      Module.finrank ℝ (totalBodyLoad G p T).range := by
    rw [bodyLoadTest, LinearMap.range_comp_of_range_eq_top _ loadWorkEquiv.range,
      LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h₁ := (bodyLoadTest G p T).finrank_range_add_finrank_ker
  have h₂ := (rigidityOperator (maskedGraph G T) p).finrank_range_add_finrank_ker
  rw [htest, ker_bodyLoadTest G hG p hp T] at h₁
  unfold rigidityRank
  omega

/-- Proposition 6.2's rank formula, as an exact addition identity. -/
theorem body_load_rank_identity
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    rigidityRank (maskedGraph G T) p +
        Module.finrank ℝ (compatibleBodyLoads G p T) =
      ∑ C : Body G, rigidityRank (cliqueOn (C.val ∩ T)) p := by
  have h := (totalBodyLoad G p T).finrank_range_add_finrank_ker
  rw [totalBodyLoad_rank G hG p hp T] at h
  change rigidityRank (maskedGraph G T) p +
    Module.finrank ℝ (compatibleBodyLoads G p T) =
    Module.finrank ℝ (BodyBalancedFamily G p T) at h
  rw [Module.finrank_pi_fintype] at h
  simpa only [balancedLoadsOn_finrank p hp] using h

/-- The same identity on the literal induced subtype graph and complete
fragment graphs, with their actual generic ranks. -/
theorem generic_body_load_rank_identity
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    genericRigidityRank (G.induce (T : Set V)) 3 +
        Module.finrank ℝ (compatibleBodyLoads G p T) =
      ∑ C : Body G, genericRigidityRank (SimpleGraph.completeGraph ↥(C.val ∩ T)) 3 := by
  have h := body_load_rank_identity G hG p hp T
  change ∀ H : SimpleGraph V, rigidityRank H p = genericRigidityRank H 3 at hgen
  simp only [hgen] at h
  rw [maskedGraph_eq_liftInduce, genericRigidityRank_liftGraph] at h
  simpa only [cliqueOn_eq_liftComplete, genericRigidityRank_liftGraph] using h

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0041

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0041/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0041.json"

section BundleSource0042
/- Source: Papers/RigidityUniformOrders.lean -/










@[expose] public section

/-!
# Restricting an actual uniform vertex order

An outcome records the position of every label.  Restriction sorts the
positions of a specified embedded set of labels.  Its uniform law is
proved by extending permutations of these labels to the whole vertex
set and double-counting a finite sum.  Thus later star estimates need
no independent assumption about the relative order of a neighborhood.
-/

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The position of every label in a total ordering. -/
abbrev Outcome (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

instance outcome_nonempty (V : Type*) [Fintype V] : Nonempty (Outcome V) :=
  ⟨Fintype.equivFin V⟩

/-- Sort exactly the positions occupied by the selected labels. -/
def restrict (e : I ↪ V) (σ : Outcome V) : Outcome I := by
  letI : LinearOrder I := LinearOrder.lift' (fun i => σ (e i))
    (σ.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq I rfl).symm.toEquiv

theorem restrict_lt_iff (e : I ↪ V) (σ : Outcome V) (i j : I) :
    restrict e σ i < restrict e σ j ↔ σ (e i) < σ (e j) := by
  letI : LinearOrder I := LinearOrder.lift' (fun i => σ (e i))
    (σ.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq I rfl).symm.lt_iff_lt

theorem outcome_eq_of_lt_iff (σ τ : Outcome I)
    (h : ∀ i j, σ i < σ j ↔ τ i < τ j) : σ = τ := by
  have hm : StrictMono (fun k => τ (σ.symm k)) := by
    intro a b hab
    exact (h (σ.symm a) (σ.symm b)).mp (by simpa using hab)
  apply Equiv.ext
  intro i
  have hi := congrFun hm.eq_id (σ i)
  simpa using hi.symm

/-- Relabeling only the selected vertices permutes their induced order
by precisely the same relabeling. -/
theorem restrict_relabel (e : I ↪ V) (σ : Outcome V) (τ : Equiv.Perm I) :
    restrict e ((τ.viaEmbedding e).trans σ) = τ.trans (restrict e σ) := by
  apply outcome_eq_of_lt_iff
  intro i j
  simp only [restrict_lt_iff, Equiv.trans_apply,
    Equiv.Perm.viaEmbedding_apply]

def relabelEquiv (e : I ↪ V) (τ : Equiv.Perm I) : Outcome V ≃ Outcome V where
  toFun σ := (τ.viaEmbedding e).trans σ
  invFun σ := (τ.viaEmbedding e).symm.trans σ
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

def permOutcomeEquiv (ρ : Outcome I) : Equiv.Perm I ≃ Outcome I where
  toFun τ := τ.trans ρ
  invFun ω := ω.trans ρ.symm
  left_inv τ := by ext i; simp
  right_inv ω := by ext i; simp

def mean (f : Outcome V → ℝ) : ℝ :=
  (∑ σ : Outcome V, f σ) / Fintype.card (Outcome V)

/-- The exact pushforward law of a uniformly chosen total order under
restriction to any embedded finite set of labels. -/
theorem mean_restrict (e : I ↪ V) (f : Outcome I → ℝ) :
    mean (fun σ : Outcome V => f (restrict e σ)) = mean f := by
  have hglobal (τ : Equiv.Perm I) :
      (∑ σ : Outcome V, f (τ.trans (restrict e σ))) =
        ∑ σ : Outcome V, f (restrict e σ) := by
    simpa only [relabelEquiv, Equiv.coe_fn_mk, restrict_relabel] using
      (Equiv.sum_comp (relabelEquiv e τ) (fun σ => f (restrict e σ)))
  have hlocal (σ : Outcome V) :
      (∑ τ : Equiv.Perm I, f (τ.trans (restrict e σ))) =
        ∑ ρ : Outcome I, f ρ :=
    Equiv.sum_comp (permOutcomeEquiv (restrict e σ)) f
  have hdouble :
      (Fintype.card (Equiv.Perm I) : ℝ) *
          (∑ σ : Outcome V, f (restrict e σ)) =
        (Fintype.card (Outcome V) : ℝ) * (∑ ρ : Outcome I, f ρ) := by
    calc
      _ = ∑ τ : Equiv.Perm I, ∑ σ : Outcome V,
          f (τ.trans (restrict e σ)) := by
            simp only [hglobal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ σ : Outcome V, ∑ τ : Equiv.Perm I,
          f (τ.trans (restrict e σ)) := Finset.sum_comm
      _ = _ := by
        simp only [hlocal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (Equiv.Perm I) = Fintype.card (Outcome I) :=
    Fintype.card_congr (permOutcomeEquiv (Fintype.equivFin I))
  rw [hcard] at hdouble
  have hV : (Fintype.card (Outcome V) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hI : (Fintype.card (Outcome I) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  unfold mean
  apply (div_eq_div_iff hV hI).mpr
  simpa only [mul_comm] using hdouble

theorem mean_congr (f g : Outcome V → ℝ) (h : ∀ σ, f σ = g σ) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => h σ)

theorem mean_mono (f g : Outcome V → ℝ) (h : ∀ σ, f σ ≤ g σ) :
    mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => h σ))
    (Nat.cast_nonneg _)

theorem mean_add (f g : Outcome V → ℝ) :
    mean (fun σ => f σ + g σ) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_sub (f g : Outcome V → ℝ) :
    mean (fun σ => f σ - g σ) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_const (a : ℝ) : mean (fun _ : Outcome V => a) = a := by
  have hV : (Fintype.card (Outcome V) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hV

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0042

section BundleSource0043
/- Source: Papers/RigidityStressPrefix.lean -/





@[expose] public section

/-!
# Induced graph prefixes and their actual stress stars

Both prefix spaces are subspaces of the original unordered-edge
coefficient space, supported precisely on the induced graph before or
after the specified vertex enters.  The new-star kernel is the old
space, so its dimension increase is bounded by the supported part of
the actual global star image.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical

variable {V : Type} [Fintype V]

def edgesBefore (G : SimpleGraph V) (σ : Outcome V) (v : V) : Set (Edge G) :=
  {e | ∀ w, w ∈ e.val → σ w < σ v}

def edgesThrough (G : SimpleGraph V) (σ : Outcome V) (v : V) : Set (Edge G) :=
  {e | ∀ w, w ∈ e.val → σ w ≤ σ v}

def incidentEdgeEmbedding (G : SimpleGraph V) (v : V) : IncidentEdge G v ↪ Edge G :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgesBefore_subset_edgesThrough (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    edgesBefore G σ v ⊆ edgesThrough G σ v := by
  intro e he w hw
  exact (he w hw).le

theorem incident_not_edgesBefore (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : IncidentEdge G v) : e.val ∉ edgesBefore G σ v := by
  intro he
  exact (lt_irrefl (σ v)) (he v e.property)

theorem new_edge_incident (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : Edge G) (he : e ∈ edgesThrough G σ v) (hold : e ∉ edgesBefore G σ v) :
    e ∈ Set.range (incidentEdgeEmbedding G v) := by
  change ¬ ∀ w, w ∈ e.val → σ w < σ v at hold
  push_neg at hold
  obtain ⟨w, hw, hnot⟩ := hold
  have hwv : w = v := σ.injective (le_antisymm (he w hw) hnot)
  exact ⟨⟨e, hwv ▸ hw⟩, rfl⟩

theorem incident_edgesThrough_iff (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : IncidentEdge G v) :
    e.val ∈ edgesThrough G σ v ↔ σ (incidentOther G v e) < σ v := by
  constructor
  · intro he
    have hle := he (incidentOther G v e) (Sym2.other_mem e.property)
    exact lt_of_le_of_ne hle (fun h => incidentOther_ne G v e (σ.injective h))
  · intro he w hw
    rw [← Sym2.other_spec e.property] at hw
    rcases Sym2.mem_iff.mp hw with h | h
    · subst w
      exact le_rfl
    · subst w
      exact he.le

/-- The old and new actual induced-prefix stress subspaces. -/
def stressBefore (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (Edge G → ℝ) :=
  supportedOn W (edgesBefore G σ v)

def stressThrough (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (Edge G → ℝ) :=
  supportedOn W (edgesThrough G σ v)

def precedingStarCode (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (IncidentEdge G v → ℝ) :=
  supportedOn (stressStarCode G v W)
    {e | σ (incidentOther G v e) < σ v}

/-- An actual induced-prefix dimension increase injects into the global
star image supported on the preceding neighbors.  This applies equally
to proper subspaces of the full stress space. -/
theorem stressPrefix_finrank_le (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V) :
    Module.finrank ℝ (stressThrough G W σ v) ≤
      Module.finrank ℝ (stressBefore G W σ v) +
        Module.finrank ℝ (precedingStarCode G W σ v) := by
  have h := supportedPrefix_finrank_le W (edgesBefore G σ v) (edgesThrough G σ v)
    (incidentEdgeEmbedding G v) (edgesBefore_subset_edgesThrough G σ v)
    (incident_not_edgesBefore G σ v) (new_edge_incident G σ v)
  have hsets : (incidentEdgeEmbedding G v) ⁻¹' edgesThrough G σ v =
      {e | σ (incidentOther G v e) < σ v} := by
    ext e
    exact incident_edgesThrough_iff G σ v e
  rw [hsets] at h
  exact h

theorem stressPrefix_dimension_increase_le (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V) :
    (Module.finrank ℝ (stressThrough G W σ v) : ℤ) -
        Module.finrank ℝ (stressBefore G W σ v) ≤
      Module.finrank ℝ (precedingStarCode G W σ v) := by
  have h := stressPrefix_finrank_le G W σ v
  omega

end
end Papers.Rigidity.BarJoint

end
end BundleSource0043

section BundleSource0044
/- Source: Papers/RigiditySupportedOrder.lean -/









@[expose] public section

/-!
# Uniform finite orders with a marker

An outcome is a literal permutation of the coordinates and one distinct
marker.  Its probability is the reciprocal of the factorial of the
number of labels.  We first use the coordinates following the marker;
reversing the permutation gives exactly the preceding-coordinate model.
The recursion conditions on the first label and shortens the actual
code whenever this label is a coordinate.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

variable {K : Type*} [Field K]

def remainingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    σ.symm i.castSucc < σ.symm (Fin.last n) → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

@[simp] theorem mem_remainingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin n → K) :
    w ∈ remainingCode W σ ↔ w ∈ W ∧ ∀ i : Fin n,
      σ.symm i.castSucc < σ.symm (Fin.last n) → w i = 0 := Iff.rfl

theorem remainingCode_le {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : remainingCode W σ ≤ W := fun _ h => h.1

/-- Literal expectation under the uniform finite ordering law. -/
def orderMean {n : ℕ} (W : Submodule K (Fin n → K)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K (remainingCode W σ) : ℝ)) /
    (n + 1).factorial

/-- The literal subspace supported on coordinates preceding the marker. -/
def precedingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    σ.symm (Fin.last n) < σ.symm i.castSucc → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

def precedingMean {n : ℕ} (W : Submodule K (Fin n → K)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K (precedingCode W σ) : ℝ)) /
    (n + 1).factorial

private def reversePositions (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Reversal is a probability-preserving bijection of the finite order
space because all outcomes have the same factorial weight. -/
private def reverseOrder (n : ℕ) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := (reversePositions n).trans σ
  invFun σ := (reversePositions n).trans σ
  left_inv σ := by ext i; simp [reversePositions]
  right_inv σ := by ext i; simp [reversePositions]

private theorem remainingCode_reverse {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) :
    remainingCode W (reverseOrder (n + 1) σ) = precedingCode W σ := by
  ext w
  simp [remainingCode, precedingCode, reverseOrder, reversePositions, Fin.rev_lt_rev]

theorem orderMean_eq_precedingMean {n : ℕ} (W : Submodule K (Fin n → K)) :
    orderMean W = precedingMean W := by
  unfold orderMean precedingMean
  apply congrArg (fun x : ℝ => x / (n + 1).factorial)
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W (reverseOrder (n + 1) σ)) : ℝ) :=
      (Equiv.sum_comp (reverseOrder (n + 1))
        (fun σ => (Module.finrank K (remainingCode W σ) : ℝ))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [remainingCode_reverse]

private theorem first_marker {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (σ : Equiv.Perm (Fin (n + 1))) :
    remainingCode W (Equiv.Perm.decomposeFin'Symm (Fin.last (n + 1)) σ) = W := by
  ext w
  simp [mem_remainingCode]

private theorem first_coordinate_position {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (Equiv.Perm.decomposeFin'Symm i.castSucc σ).symm (i.succAbove j).castSucc =
      (σ.symm j.castSucc).succ := by
  have h := Equiv.Perm.decomposeFin'Symm_symm_succAbove i.castSucc σ
    (σ.symm j.castSucc)
  simpa only [Equiv.apply_symm_apply, Fin.castSucc_succAbove_castSucc] using h

private theorem marker_position {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin'Symm i.castSucc σ).symm (Fin.last (n + 1)) =
      (σ.symm (Fin.last n)).succ := by
  have h := Equiv.Perm.decomposeFin'Symm_symm_succAbove i.castSucc σ
    (σ.symm (Fin.last n))
  simpa only [Equiv.apply_symm_apply,
    Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)] using h

private theorem first_coordinate_inactive {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    i ∉ activeCoordinates (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) := by
  rintro hi
  obtain ⟨w, hw, hwi⟩ := (mem_activeCoordinates _ i).mp hi
  apply hwi
  apply hw.2 i
  rw [Equiv.Perm.decomposeFin'Symm_symm_eq_zero, marker_position]
  exact Fin.succ_pos _

private theorem shorten_remainingCode {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    shorten (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) i =
      remainingCode (shorten W i) σ := by
  ext w
  simp only [mem_shorten, mem_remainingCode]
  constructor
  · rintro ⟨hw, hz⟩
    refine ⟨hw, ?_⟩
    intro j hj
    have h := hz (i.succAbove j)
    rw [first_coordinate_position, marker_position] at h
    simpa only [insertZero_succAbove] using h (Fin.succ_lt_succ_iff.mpr hj)
  · rintro ⟨hw, hz⟩
    refine ⟨hw, ?_⟩
    intro j hj
    cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      rw [first_coordinate_position, marker_position] at hj
      simpa only [insertZero_succAbove] using hz j (Fin.succ_lt_succ_iff.mp hj)

private theorem first_coordinate_finrank {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Module.finrank K (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) =
      Module.finrank K (remainingCode (shorten W i) σ) := by
  rw [← shorten_remainingCode]
  exact (finrank_shorten_of_inactive _ i (first_coordinate_inactive W i σ)).symm

/-- Conditioning on the first label gives the exact finite-order
recursion, with the marker term equal to the whole code dimension. -/
theorem orderMean_recursion {n : ℕ} (W : Submodule K (Fin (n + 1) → K)) :
    orderMean W =
      ((Module.finrank K W : ℝ) + ∑ i : Fin (n + 1), orderMean (shorten W i)) /
        (n + 2) := by
  have hsum :
      (∑ τ : Equiv.Perm (Fin (n + 2)), (Module.finrank K (remainingCode W τ) : ℝ)) =
      (n + 1).factorial * (Module.finrank K W : ℝ) +
        ∑ i : Fin (n + 1),
          ∑ σ : Equiv.Perm (Fin (n + 1)),
            (Module.finrank K (remainingCode (shorten W i) σ) : ℝ) := by
    rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin' (n := n)).symm]
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    simp only [Equiv.Perm.decomposeFin'_symm]
    change
      (∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W
          (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) : ℝ)) +
      (∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W
          (Equiv.Perm.decomposeFin'Symm (Fin.last (n + 1)) σ)) : ℝ)) = _
    calc
      _ = (∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
          (Module.finrank K (remainingCode (shorten W i) σ) : ℝ)) +
          (n + 1).factorial * (Module.finrank K W : ℝ) := by
        apply congrArg₂ (fun x y : ℝ => x + y)
        · apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro σ _
          exact congrArg (fun r : ℕ => (r : ℝ)) (first_coordinate_finrank W i σ)
        · calc
            _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K W : ℝ) := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [first_marker W σ]
            _ = _ := by
              simp only [Finset.sum_const, Finset.card_univ,
                Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := add_comm _ _
  unfold orderMean
  rw [hsum, Nat.factorial_succ (n + 1)]
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hn' : (n + 1 + 1 : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [← Finset.sum_div]
  field_simp [hfac, hn, hn']
  <;> ring

theorem orderMean_eq_zero_of_finrank_eq_zero {n : ℕ}
    (W : Submodule K (Fin n → K)) (hW : Module.finrank K W = 0) :
    orderMean W = 0 := by
  have hz (σ : Equiv.Perm (Fin (n + 1))) :
      Module.finrank K (remainingCode W σ) = 0 := by
    have h := Submodule.finrank_mono (remainingCode_le W σ)
    omega
  simp [orderMean, hz]

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0044

section BundleSource0045
/- Source: Papers/RigiditySupportedBound.lean -/




@[expose] public section

/-!
# The supported-code inequality for every field and finite length

This is the full inequality needed for the random-order stress argument.
Its expectation is the uniform average of the actual supported subspace
dimensions over all coordinate-and-marker permutations.  The proof uses
no coding-theoretic axiom, probabilistic memorylessness assertion, or
additional hypothesis on the code.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

def bound (s r : ℕ) : ℝ := (r : ℝ) * (r + 1) / (2 * (r + s))

@[simp] theorem bound_zero (s : ℕ) : bound s 0 = 0 := by simp [bound]

theorem bound_succ_mono (s r : ℕ) (hs : 1 ≤ s) : bound s r ≤ bound s (r + 1) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (r : ℝ) + s ≠ 0 := by positivity
  have hden' : (r : ℝ) + 1 + s ≠ 0 := by positivity
  have hdiff : bound s (r + 1) - bound s r =
      ((r : ℝ) + 1) * (r + 2 * s) /
        (2 * (r + s) * (r + 1 + s)) := by
    unfold bound
    push_cast
    field_simp
    <;> ring
  apply sub_nonneg.mp
  rw [hdiff]
  positivity

private theorem bound_step (s r d g : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (hg : g ≤ d) (hsingle : r + s ≤ g + 1) :
    ((r : ℝ) + ((d - g : ℕ) : ℝ) * bound s r + (g : ℝ) * bound s (r - 1)) /
        (d + 1) ≤ bound s r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (k : ℝ) + s ≠ 0 := by positivity
  have hden' : (k : ℝ) + 1 + s ≠ 0 := by positivity
  have hidentity : ((k : ℝ) + 1 + s) * bound s (k + 1) =
      (k + 1) + (k + s) * bound s k := by
    unfold bound
    push_cast
    field_simp
    <;> ring
  have hmono := bound_succ_mono s k hs
  have hg' : (k : ℝ) + s ≤ g := by exact_mod_cast (show k + s ≤ g by omega)
  have hmul := mul_nonneg (sub_nonneg.mpr hg') (sub_nonneg.mpr hmono)
  have hmain : (k : ℝ) + 1 + (g : ℝ) * bound s k ≤
      ((g : ℝ) + 1) * bound s (k + 1) := by
    nlinarith [hidentity]
  have hd : (0 : ℝ) < d + 1 := by positivity
  apply (div_le_iff₀ hd).mpr
  rw [Nat.cast_sub hg]
  norm_num only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  nlinarith [hmain]

/-- Lemma 2.1's supported-subspace upper bound, under the exact uniform
finite order law.  The length and support threshold are unrestricted,
and the coefficient field is arbitrary. -/
theorem orderMean_le_bound {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s) :
    orderMean W ≤ bound s (Module.finrank K W) := by
  induction n with
  | zero =>
    have hzero : Module.finrank K W = 0 := by
      have h := W.finrank_le
      simpa using h
    rw [orderMean_eq_zero_of_finrank_eq_zero W hzero, hzero, bound_zero]
  | succ n ih =>
    by_cases hrzero : Module.finrank K W = 0
    · rw [orderMean_eq_zero_of_finrank_eq_zero W hrzero, hrzero, bound_zero]
    · let r := Module.finrank K W
      let g := (activeCoordinates W).card
      have hr : 1 ≤ r := by omega
      have hg : g ≤ n + 1 := by
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
      have hW : W ≠ ⊥ := by intro hz; simp [hz] at hrzero
      have hsingle : r + s ≤ g + 1 := singleton_bound W s hs hmin hW
      have hterm (i : Fin (n + 1)) : orderMean (shorten W i) ≤
          if i ∈ activeCoordinates W then bound s (r - 1) else bound s r := by
        have h := ih (shorten W i) (minimumSupport_shorten W i hmin)
        by_cases hi : i ∈ activeCoordinates W
        · have hd := finrank_shorten_of_active W i hi
          have hd' : Module.finrank K (shorten W i) = r - 1 := by omega
          simpa [hi, hd'] using h
        · have hd := finrank_shorten_of_inactive W i hi
          simpa [hi, hd, r] using h
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
      have hite :
          (∑ i : Fin (n + 1), if i ∈ activeCoordinates W then bound s (r - 1) else bound s r) =
            (g : ℝ) * bound s (r - 1) + ((n + 1 - g : ℕ) : ℝ) * bound s r := by
        rw [Finset.sum_ite]
        have hpos : (Finset.univ.filter fun i => i ∈ activeCoordinates W) =
            activeCoordinates W := by ext i; simp
        have hneg : (Finset.univ.filter fun i => i ∉ activeCoordinates W) =
            Finset.univ \ activeCoordinates W := by ext i; simp
        rw [hpos, hneg]
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, g]
      rw [hite] at hsum
      rw [orderMean_recursion]
      calc
        ((Module.finrank K W : ℝ) + ∑ i : Fin (n + 1), orderMean (shorten W i)) /
            (n + 2) ≤
            ((r : ℝ) + (g : ℝ) * bound s (r - 1) +
              ((n + 1 - g : ℕ) : ℝ) * bound s r) / (n + 2) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                dsimp [r] at *
                linarith
        _ ≤ bound s r := by
          have h := bound_step s r (n + 1) g hs hr hg hsingle
          convert h using 1 <;> push_cast <;> ring

/-- The same bound in the paper's preceding-coordinate convention. -/
theorem precedingMean_le_bound {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s) :
    precedingMean W ≤ bound s (Module.finrank K W) := by
  rw [← orderMean_eq_precedingMean]
  exact orderMean_le_bound W hs hmin

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0045

section BundleSource0046
/- Source: Papers/RigiditySupportedRelabel.lean -/





@[expose] public section

/-!
# Supported codes under actual vertex orders

Coordinate relabeling preserves support, dimension and each supported
subspace.  The preceding-code estimate is then transported from its
finite permutation model to the restriction of a genuinely uniform
order on an arbitrary finite ambient vertex set.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open UniformOrders
open scoped Classical BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def reindexCode (W : Submodule K (I → K)) (e : J ≃ I) : Submodule K (J → K) :=
  W.map (LinearEquiv.funCongrLeft K K e).toLinearMap

theorem support_reindex (w : I → K) (e : J ≃ I) :
    support (fun j => w (e j)) = (support w).map e.symm.toEmbedding := by
  ext j
  simp only [mem_support, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e j, h, e.symm_apply_apply j⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi

theorem minimumSupport_reindex (W : Submodule K (I → K)) (e : J ≃ I)
    {s : ℕ} (hW : MinimumSupport W s) : MinimumSupport (reindexCode W e) s := by
  rintro a ⟨w, hw, rfl⟩ hne
  have hwn : w ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have h := hW w hw hwn
  change s ≤ (support (fun j => w (e j))).card
  simpa only [support_reindex, Finset.card_map] using h

theorem finrank_reindex (W : Submodule K (I → K)) (e : J ≃ I) :
    Module.finrank K (reindexCode W e) = Module.finrank K W :=
  (LinearEquiv.funCongrLeft K K e).finrank_map_eq W

theorem reindex_supportedOn (W : Submodule K (I → K)) (e : J ≃ I) (A : Set I) :
    reindexCode (supportedOn W A) e = supportedOn (reindexCode W e) (e ⁻¹' A) := by
  ext a
  constructor
  · rintro ⟨w, ⟨hw, hs⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, fun j hj => hs (e j) hj⟩
  · rintro ⟨⟨w, hw, rfl⟩, hs⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    intro i hi
    have h := hs (e.symm i)
    simpa using h (by simpa using hi)

theorem finrank_supportedOn_reindex (W : Submodule K (I → K))
    (e : J ≃ I) (A : Set I) :
    Module.finrank K (supportedOn (reindexCode W e) (e ⁻¹' A)) =
      Module.finrank K (supportedOn W A) := by
  rw [← reindex_supportedOn]
  exact finrank_reindex _ _

theorem precedingCode_eq_supportedOn {n : ℕ}
    (W : Submodule K (Fin n → K)) (σ : Equiv.Perm (Fin (n + 1))) :
    precedingCode W σ = supportedOn W
      {i | σ.symm i.castSucc < σ.symm (Fin.last n)} := by
  ext w
  constructor
  · rintro ⟨hw, hs⟩
    refine ⟨hw, ?_⟩
    intro i hi
    apply hs i
    exact lt_of_le_of_ne (le_of_not_gt hi)
      (fun h => (Fin.castSucc_ne_last i) (σ.symm.injective h).symm)
  · rintro ⟨hw, hs⟩
    refine ⟨hw, ?_⟩
    intro i hi
    exact hs i (not_lt_of_gt hi)

end
end Papers.Rigidity.SupportedCode

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

def finOutcomeEquiv (n : ℕ) : Outcome (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun ρ := (ρ.trans (finCongr (Fintype.card_fin n))).symm
  invFun σ := σ.symm.trans (finCongr (Fintype.card_fin n)).symm
  left_inv ρ := by ext i; simp
  right_inv σ := by ext i; simp

theorem mean_finOutcome (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) :
    mean (fun ρ : Outcome (Fin n) => f (finOutcomeEquiv n ρ)) =
      (∑ σ : Equiv.Perm (Fin n), f σ) / n.factorial := by
  have hcard : Fintype.card (Outcome (Fin n)) = n.factorial := by
    calc
      _ = Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr (finOutcomeEquiv n)
      _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  unfold mean
  apply congrArg₂ (fun x y : ℝ => x / y)
  · apply Finset.sum_equiv (finOutcomeEquiv n)
    · intro ρ
      simp only [Finset.mem_univ]
    · intro ρ _
      rfl
  · simpa only [← Nat.card_eq_fintype_card] using
      congrArg (fun k : ℕ => (k : ℝ)) hcard

variable {V : Type*} [Fintype V]

def restrictPermutation {n : ℕ} (e : Fin n ↪ V) (σ : Outcome V) :
    Equiv.Perm (Fin n) := finOutcomeEquiv n (restrict e σ)

theorem restrictPermutation_lt_iff {n : ℕ} (e : Fin n ↪ V)
    (σ : Outcome V) (i j : Fin n) :
    (restrictPermutation e σ).symm i < (restrictPermutation e σ).symm j ↔
      σ (e i) < σ (e j) := by
  simpa only [restrictPermutation, finOutcomeEquiv, Equiv.coe_fn_mk, Equiv.symm_symm,
    Equiv.trans_apply, finCongr_apply, Fin.cast_lt_cast] using restrict_lt_iff e σ i j

theorem mean_restrictPermutation {n : ℕ} (e : Fin n ↪ V)
    (f : Equiv.Perm (Fin n) → ℝ) :
    mean (fun σ : Outcome V => f (restrictPermutation e σ)) =
      (∑ τ : Equiv.Perm (Fin n), f τ) / n.factorial := by
  unfold restrictPermutation
  exact (mean_restrict e (fun ρ => f (finOutcomeEquiv n ρ))).trans
    (mean_finOutcome n f)

/-- The supported-code bound for the labels of a fixed embedded
coordinate-and-marker set inside an actual global vertex permutation. -/
theorem mean_supported_preceding_le {K : Type*} [Field K] {n s : ℕ}
    (e : Fin (n + 1) ↪ V) (W : Submodule K (Fin n → K))
    (hs : 1 ≤ s) (hW : SupportedCode.MinimumSupport W s) :
    mean (fun σ : Outcome V =>
      (Module.finrank K (SupportedCode.supportedOn W
        {i | σ (e i.castSucc) < σ (e (Fin.last n))}) : ℝ)) ≤
      SupportedCode.bound s (Module.finrank K W) := by
  have hcode (σ : Outcome V) :
      SupportedCode.supportedOn W
        {i | σ (e i.castSucc) < σ (e (Fin.last n))} =
      SupportedCode.precedingCode W (restrictPermutation e σ) := by
    rw [SupportedCode.precedingCode_eq_supportedOn]
    congr 1
    ext i
    exact (restrictPermutation_lt_iff e σ i.castSucc (Fin.last n)).symm
  calc
    _ = mean (fun σ : Outcome V =>
        (Module.finrank K (SupportedCode.precedingCode W
          (restrictPermutation e σ)) : ℝ)) := by
      apply congrArg mean
      funext σ
      exact congrArg (fun S : Submodule K (Fin n → K) =>
        (Module.finrank K S : ℝ)) (hcode σ)
    _ = SupportedCode.precedingMean W :=
      mean_restrictPermutation e
        (fun τ => (Module.finrank K (SupportedCode.precedingCode W τ) : ℝ))
    _ ≤ SupportedCode.bound s (Module.finrank K W) :=
      SupportedCode.precedingMean_le_bound W hs hW

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0046

section BundleSource0047
/- Source: Papers/RigidityStressExpectation.lean -/




@[expose] public section

/-!
# The supported-stress expectation in Corollary 2.2

The expectation here is taken over the actual uniformly chosen global
vertex order.  The proof combines the previously established local-order
pushforward law, force equilibrium at the given general-position
placement, and the actual prefix-kernel injection.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical

variable {V : Type} [Fintype V]

def starEnumeration (G : SimpleGraph V) (v : V) :
    Fin (Fintype.card (IncidentEdge G v)) ≃ IncidentEdge G v :=
  (Fintype.equivFin (IncidentEdge G v)).symm

/-- The coordinates are the distinct neighboring vertices; the final
marker is the vertex whose insertion is being studied. -/
def starMarkerEmbedding (G : SimpleGraph V) (v : V) :
    Fin (Fintype.card (IncidentEdge G v) + 1) ↪ V where
  toFun := Fin.lastCases v (fun i => incidentOther G v (starEnumeration G v i))
  inj' := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact False.elim (incidentOther_ne G v (starEnumeration G v j) hij.symm)
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact False.elim (incidentOther_ne G v (starEnumeration G v i) hij)
      | cast j =>
        simp only [Fin.lastCases_castSucc] at hij
        exact congrArg Fin.castSucc
          ((starEnumeration G v).injective (incidentOther_injective G v hij))

@[simp] theorem starMarkerEmbedding_coordinate (G : SimpleGraph V) (v : V)
    (i : Fin (Fintype.card (IncidentEdge G v))) :
    starMarkerEmbedding G v i.castSucc = incidentOther G v (starEnumeration G v i) := by
  simp [starMarkerEmbedding]

@[simp] theorem starMarkerEmbedding_marker (G : SimpleGraph V) (v : V) :
    starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))) = v := by
  simp [starMarkerEmbedding]

/-- Expected supported dimension in the actual global star image, with
no independence law for local positions assumed in the hypotheses. -/
theorem mean_precedingStarCode_le
    (G : SimpleGraph V) (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (W : Submodule ℝ (Edge G → ℝ)) (hW : W ≤ StressSpace G p) :
    mean (fun σ : Outcome V => (Module.finrank ℝ (precedingStarCode G W σ v) : ℝ)) ≤
      bound 4 (Module.finrank ℝ (stressStarCode G v W)) := by
  let e := starEnumeration G v
  let C := reindexCode (stressStarCode G v W) e
  have hC : MinimumSupport C 4 :=
    minimumSupport_reindex _ e (stressStarCode_minimumSupport_four G p hp v W hW)
  have hmean := mean_supported_preceding_le (starMarkerEmbedding G v) C (by decide) hC
  have hdim (σ : Outcome V) :
      Module.finrank ℝ (supportedOn C
        {i | σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))))}) =
      Module.finrank ℝ (precedingStarCode G W σ v) := by
    have hset :
        {i | σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))))} =
        e ⁻¹' {a | σ (incidentOther G v a) < σ v} := by
      ext i
      change σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v)))) ↔
        σ (incidentOther G v (e i)) < σ v
      rw [starMarkerEmbedding_coordinate G v i, starMarkerEmbedding_marker G v]
    calc
      _ = Module.finrank ℝ (supportedOn C
          (e ⁻¹' {a | σ (incidentOther G v a) < σ v})) :=
        congrArg (fun S : Set (Fin (Fintype.card (IncidentEdge G v))) =>
          Module.finrank ℝ (supportedOn C S)) hset
      _ = _ := finrank_supportedOn_reindex (stressStarCode G v W) e
        {a | σ (incidentOther G v a) < σ v}
  have hCd : Module.finrank ℝ C = Module.finrank ℝ (stressStarCode G v W) :=
    finrank_reindex _ e
  calc
    _ = mean (fun σ : Outcome V =>
        (Module.finrank ℝ (supportedOn C
          {i | σ (starMarkerEmbedding G v i.castSucc) <
            σ (starMarkerEmbedding G v
              (Fin.last (Fintype.card (IncidentEdge G v))))}) : ℝ)) := by
      apply congrArg mean
      funext σ
      exact congrArg (fun k : ℕ => (k : ℝ)) (hdim σ).symm
    _ ≤ bound 4 (Module.finrank ℝ C) := hmean
    _ = bound 4 (Module.finrank ℝ (stressStarCode G v W)) :=
      congrArg (bound 4) hCd

/-- The actual expected induced-prefix increase of a fixed stress
subspace.  The integer-valued dimensions are embedded in `ℝ` before
subtraction, so this definition involves no truncated natural subtraction. -/
def stressDimensionContribution (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (v : V) : ℝ :=
  mean fun σ : Outcome V =>
    (Module.finrank ℝ (stressThrough G W σ v) : ℝ) -
      Module.finrank ℝ (stressBefore G W σ v)

/-- The full subspace assertion of Corollary 2.2, for every finite graph,
every general-position placement, and every actual stress subspace. -/
theorem corollary_two_two_subspace
    (G : SimpleGraph V) (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (W : Submodule ℝ (Edge G → ℝ)) (hW : W ≤ StressSpace G p) :
    stressDimensionContribution G W v ≤
      bound 4 (Module.finrank ℝ (stressStarCode G v W)) := by
  apply le_trans (mean_mono _ _ ?_) (mean_precedingStarCode_le G p hp v W hW)
  intro σ
  have h := stressPrefix_finrank_le G W σ v
  have hreal :
      (Module.finrank ℝ (stressThrough G W σ v) : ℝ) ≤
        (Module.finrank ℝ (stressBefore G W σ v) : ℝ) +
          Module.finrank ℝ (precedingStarCode G W σ v) := by exact_mod_cast h
  linarith

end
end Papers.Rigidity.BarJoint

end
end BundleSource0047

section BundleSource0048
/- Source: Papers/RigidityRankContributions.lean -/






@[expose] public section

/-!
# Actual vertex-order rigidity-rank contributions

The graph at each stage is the induced prefix with the remaining labels
isolated.  Rank contributions are literal uniform averages of successive
generic ranks.  Their sum is the rank of the original graph.  The
expected number of newly inserted edges is proved by swapping the two
endpoint labels in the uniform order space.
-/

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

theorem mean_sum (f : I → Outcome V → ℝ) :
    mean (fun σ => ∑ i, f i σ) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_indicator_precedes (v w : V) (hne : v ≠ w) :
    mean (fun σ : Outcome V => if σ v < σ w then (1 : ℝ) else 0) = 1 / 2 := by
  let F : Outcome V → ℝ := fun σ => if σ v < σ w then 1 else 0
  let H : Outcome V → ℝ := fun σ => if σ w < σ v then 1 else 0
  let swap : Outcome V ≃ Outcome V :=
    { toFun := fun σ => (Equiv.swap v w).trans σ
      invFun := fun σ => (Equiv.swap v w).trans σ
      left_inv := by intro σ; ext a; simp
      right_inv := by intro σ; ext a; simp }
  have hsum : (∑ σ : Outcome V, F σ) = ∑ σ : Outcome V, H σ := by
    have h := Equiv.sum_comp swap F
    simpa [F, H, swap] using h.symm
  have hmean : mean F = mean H := by unfold mean; rw [hsum]
  have hone (σ : Outcome V) : F σ + H σ = 1 := by
    have hneq : σ v ≠ σ w := σ.injective.ne hne
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simp [F, H, hlt, not_lt_of_gt hlt]
    · simp [F, H, hgt, not_lt_of_gt hgt]
  have htotal : mean F + mean H = 1 := by
    rw [← mean_add, mean_congr _ _ hone, mean_const]
  change mean F = 1 / 2
  linarith

end
end Papers.Rigidity.UniformOrders

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The actual graph induced by the first `k` labels; all remaining
labels are isolated and contribute no bar row. -/
def prefixGraph (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (σ v).val < k ∧ (σ w).val < k
  symm := by constructor; rintro v w ⟨h, hv, hw⟩; exact ⟨h.symm, hw, hv⟩
  loopless := by constructor; intro v; rintro ⟨h, _⟩; exact G.loopless.irrefl v h

theorem prefixGraph_le (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) :
    prefixGraph G σ k ≤ G := fun _ _ h => h.1

@[simp] theorem prefixGraph_zero (G : SimpleGraph V) (σ : Outcome V) :
    prefixGraph G σ 0 = ⊥ := by ext v w; simp [prefixGraph]

@[simp] theorem prefixGraph_card (G : SimpleGraph V) (σ : Outcome V) :
    prefixGraph G σ (Fintype.card V) = G := by
  ext v w
  simp only [prefixGraph, and_iff_left_iff_imp]
  exact fun _ => ⟨(σ v).isLt, (σ w).isLt⟩

theorem subgraphEdgeSet_prefixGraph (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) :
    subgraphEdgeSet G (prefixGraph G σ k) =
      {e : Edge G | ∀ w, w ∈ e.val → (σ w).val < k} := by
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      change (G.Adj a b ∧ (σ a).val < k ∧ (σ b).val < k) ↔ _
      have hab : G.Adj a b := he
      simp [Sym2.mem_iff, hab]

theorem subgraphEdgeSet_prefix_before (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    subgraphEdgeSet G (prefixGraph G σ (σ v).val) = edgesBefore G σ v := by
  rw [subgraphEdgeSet_prefixGraph]
  rfl

theorem subgraphEdgeSet_prefix_through (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    subgraphEdgeSet G (prefixGraph G σ ((σ v).val + 1)) = edgesThrough G σ v := by
  rw [subgraphEdgeSet_prefixGraph]
  ext e
  simp only [Set.mem_setOf_eq, edgesThrough, Nat.lt_add_one_iff, Fin.le_def]

/-- A rank contribution is the expected change in actual generic
rigidity rank at the moment the named vertex enters. -/
def rankContribution (G : SimpleGraph V) (v : V) : ℝ :=
  mean fun σ : Outcome V =>
    (genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
      genericRigidityRank (prefixGraph G σ (σ v).val) 3

/-- No rank is lost in the bookkeeping: the contributions add to the
full graph rank, for every finite graph including the empty graph. -/
theorem sum_rankContribution (G : SimpleGraph V) :
    (∑ v : V, rankContribution G v) = (genericRigidityRank G 3 : ℝ) := by
  have htel (σ : Outcome V) :
      (∑ v : V, ((genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
        genericRigidityRank (prefixGraph G σ (σ v).val) 3)) =
      (genericRigidityRank G 3 : ℝ) := by
    let f : ℕ → ℝ := fun k => genericRigidityRank (prefixGraph G σ k) 3
    have heq := Equiv.sum_comp σ (fun k : Fin (Fintype.card V) => f (k.val + 1) - f k.val)
    rw [heq, Fin.sum_univ_eq_sum_range
      (fun k => f (k + 1) - f k) (Fintype.card V), Finset.sum_range_sub f]
    simp [f, genericRigidityRank_bot]
  simp only [rankContribution]
  rw [← mean_sum]
  rw [mean_congr _ _ htel, mean_const]

def precedingIncidentCount (G : SimpleGraph V) (σ : Outcome V) (v : V) : ℕ :=
  (Finset.univ.filter (fun e : IncidentEdge G v => σ (incidentOther G v e) < σ v)).card

/-- The expected number of preceding incident edges is half the literal
number of incident edges.  This follows from the actual global order,
with no probabilistic assumption about neighboring labels. -/
theorem mean_precedingIncidentCount (G : SimpleGraph V) (v : V) :
    mean (fun σ : Outcome V => (precedingIncidentCount G σ v : ℝ)) =
      (Fintype.card (IncidentEdge G v) : ℝ) / 2 := by
  have hcount (σ : Outcome V) : (precedingIncidentCount G σ v : ℝ) =
      ∑ e : IncidentEdge G v, if σ (incidentOther G v e) < σ v then (1 : ℝ) else 0 := by
    simp [precedingIncidentCount, Finset.sum_boole]
  rw [mean_congr _ _ hcount, mean_sum]
  simp_rw [mean_indicator_precedes _ _ (incidentOther_ne G v _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The two supported spaces appearing in the prefix injection have
exactly the ordinary induced-subgraph stress dimensions. -/
theorem prefix_rank_stress_identities (G : SimpleGraph V) (p : Placement V 3)
    (σ : Outcome V) (v : V) :
    rigidityRank (prefixGraph G σ (σ v).val) p +
        Module.finrank ℝ (stressBefore G (StressSpace G p) σ v) =
      Fintype.card (Edge (prefixGraph G σ (σ v).val)) ∧
    rigidityRank (prefixGraph G σ ((σ v).val + 1)) p +
        Module.finrank ℝ (stressThrough G (StressSpace G p) σ v) =
      Fintype.card (Edge (prefixGraph G σ ((σ v).val + 1))) := by
  constructor
  · exact (congrArg (fun S : Set (Edge G) =>
        rigidityRank (prefixGraph G σ (σ v).val) p +
          Module.finrank ℝ (SupportedCode.supportedOn (StressSpace G p) S))
        (subgraphEdgeSet_prefix_before G σ v)).symm.trans
      (rigidityRank_add_supportedStress_dimension (prefixGraph_le G σ (σ v).val) p)
  · exact (congrArg (fun S : Set (Edge G) =>
        rigidityRank (prefixGraph G σ ((σ v).val + 1)) p +
          Module.finrank ℝ (SupportedCode.supportedOn (StressSpace G p) S))
        (subgraphEdgeSet_prefix_through G σ v)).symm.trans
      (rigidityRank_add_supportedStress_dimension
        (prefixGraph_le G σ ((σ v).val + 1)) p)

end
end Papers.Rigidity.BarJoint

end
end BundleSource0048

section BundleSource0049
/- Source: Papers/RigidityRankContributionBound.lean -/




@[expose] public section

/-!
# The actual rank-contribution bound from stress support

The change in the number of prefix edges is identified with the actual
preceding incident edges.  Together with the exact rank/stress identities,
this gives the rank-contribution bound in terms of the dimension of the
full star image.  No generic-rank increment is defined by the desired
inequality.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def incidentEdgeEquivIncidenceSet (G : SimpleGraph V) (v : V) :
    IncidentEdge G v ≃ G.incidenceSet v where
  toFun e := ⟨e.val.val, e.val.property, e.property⟩
  invFun e := ⟨⟨e.val, e.property.1⟩, e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_incidentEdge_eq_degree (G : SimpleGraph V) (v : V) :
    Fintype.card (IncidentEdge G v) = G.degree v := by
  rw [Fintype.card_congr (incidentEdgeEquivIncidenceSet G v),
    G.card_incidenceSet_eq_degree]

def newPrefixEdgeEquiv (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    ↥(edgesThrough G σ v \ edgesBefore G σ v) ≃
      {e : IncidentEdge G v // σ (incidentOther G v e) < σ v} where
  toFun e := by
    have hv : v ∈ e.val.val := by
      obtain ⟨f, hf⟩ := new_edge_incident G σ v e.val e.property.1 e.property.2
      change f.val = e.val at hf
      exact hf ▸ f.property
    let f : IncidentEdge G v := ⟨e.val, hv⟩
    exact ⟨f, (incident_edgesThrough_iff G σ v f).mp e.property.1⟩
  invFun e := ⟨e.val.val,
    (incident_edgesThrough_iff G σ v e.val).mpr e.property,
    incident_not_edgesBefore G σ v e.val⟩
  left_inv e := rfl
  right_inv e := rfl

/-- Every edge appearing at this step is an actual star edge to a
preceding neighbor, and every such edge appears at this step. -/
theorem card_prefixEdges_step (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    Fintype.card (Edge (prefixGraph G σ ((σ v).val + 1))) =
      Fintype.card (Edge (prefixGraph G σ (σ v).val)) + precedingIncidentCount G σ v := by
  have hbefore := Fintype.card_congr
    (subgraphEdgeEquiv (prefixGraph_le G σ (σ v).val))
  rw [subgraphEdgeSet_prefix_before] at hbefore
  have hthrough := Fintype.card_congr
    (subgraphEdgeEquiv (prefixGraph_le G σ ((σ v).val + 1)))
  rw [subgraphEdgeSet_prefix_through] at hthrough
  have hsplit := Fintype.card_congr
    (Equiv.Set.sumDiffSubset (edgesBefore_subset_edgesThrough G σ v))
  rw [Fintype.card_sum] at hsplit
  have hnew := Fintype.card_congr (newPrefixEdgeEquiv G σ v)
  have hnew' : Fintype.card ↥(edgesThrough G σ v \ edgesBefore G σ v) =
      precedingIncidentCount G σ v := by
    exact hnew.trans (Fintype.card_subtype
      (fun e : IncidentEdge G v => σ (incidentOther G v e) < σ v))
  omega

/-- Exact decomposition of a rank contribution into the expected new
edges and the expected dimension of the actual new stresses. -/
theorem rankContribution_eq_degree_half_sub_stress
    (G : SimpleGraph V) (p : Placement V 3) (hp : IsGenericPlacement p) (v : V) :
    rankContribution G v = (G.degree v : ℝ) / 2 -
      stressDimensionContribution G (StressSpace G p) v := by
  have hpoint (σ : Outcome V) :
      ((genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
        genericRigidityRank (prefixGraph G σ (σ v).val) 3) =
      (precedingIncidentCount G σ v : ℝ) -
        ((Module.finrank ℝ (stressThrough G (StressSpace G p) σ v) : ℝ) -
          Module.finrank ℝ (stressBefore G (StressSpace G p) σ v)) := by
    obtain ⟨hbefore, hthrough⟩ := prefix_rank_stress_identities G p σ v
    have hcard := card_prefixEdges_step G σ v
    rw [hp] at hbefore hthrough
    have hbefore' := congrArg (fun n : ℕ => (n : ℝ)) hbefore
    have hthrough' := congrArg (fun n : ℕ => (n : ℝ)) hthrough
    have hcard' := congrArg (fun n : ℕ => (n : ℝ)) hcard
    push_cast at hbefore' hthrough' hcard'
    linarith
  unfold rankContribution
  rw [mean_congr _ _ hpoint, mean_sub, mean_precedingIncidentCount,
    card_incidentEdge_eq_degree]
  rfl

/-- Corollary 2.2's numerical bound, first stated with the literal full
star-image dimension.  Its identification with `degree - deletionRankDrop`
is a separate exact-sequence calculation. -/
theorem rankContribution_ge_degree_half_sub_bound_star
    (G : SimpleGraph V) (p : Placement V 3) (hp : IsGenericPlacement p)
    (hgeom : GeneralPosition.InGeneralPosition p) (v : V) :
    (G.degree v : ℝ) / 2 - bound 4 (Module.finrank ℝ (stressStarCode G v (StressSpace G p))) ≤
      rankContribution G v := by
  rw [rankContribution_eq_degree_half_sub_stress G p hp v]
  exact sub_le_sub_left
    (corollary_two_two_subspace G p hgeom v (StressSpace G p) le_rfl) _

end
end Papers.Rigidity.BarJoint

end
end BundleSource0049

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0049/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0049.json"
