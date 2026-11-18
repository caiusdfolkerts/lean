module
import verification.internal.checkpoint
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityLaman_Framework.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Framework.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/






/-!
# Frameworks and infinitesimal rigidity

A `d`-dimensional **framework** on a vertex set `V` is a placement
`p : V → EuclideanSpace ℝ (Fin d)`. Given a graph `G : SimpleGraph V`, the
**rigidity map** at `p` sends an infinitesimal motion `p' : Framework V d`
to the family of edge-length derivatives `e ↦ ⟪p u - p v, p' u - p' v⟫`
indexed by the edges `e = s(u, v) ∈ G.edgeSet`. Geometrically, this is the
differential at `p` of the squared-edge-length map (modulo a factor of two);
we define it directly via the explicit entry formula to avoid `fderiv` and
the differentiability machinery — none of which the rank/kernel arguments
downstream need.

A framework is **infinitesimally rigid** when the kernel of the rigidity
map has dimension at most `d (d+1) / 2`, the dimension of the space of trivial
Euclidean motions (translations and infinitesimal rotations). It is **generically
rigid** when *some* placement is infinitesimally rigid. We follow Jordán (2016, §1.2);
the definition of infinitesimal rigidity agrees with his when `|V| ≥ d` or `|V| ≤ 1`, so
always in the plane, and is weaker otherwise (`IsInfinitesimallyRigid`).

These definitions are stated for general dimension `d`; Laman's theorem
(`LamanTheorem.lean`) takes `d = 2`.

## Main definitions

* `Framework V d` — placement type, `abbrev` for `V → EuclideanSpace ℝ (Fin d)`.
* `SimpleGraph.RigidityMap G p` — the rigidity map as an `ℝ`-linear map.
* `SimpleGraph.IsInfinitesimallyRigid G p` — kernel-dimension bound.
* `SimpleGraph.IsGenericallyRigid G d` — existence of a rigid placement.
* `SimpleGraph.IsGenericallyRigidInj G d` — existence of a rigid *injective*
  placement; the predicate the Henneberg induction of Laman's theorem maintains.

The blueprint's `sec:frameworks` presents this file.
-/

@[expose] public section

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- A `d`-dimensional **framework** on a vertex set `V` is a placement of `V`
into `EuclideanSpace ℝ (Fin d)`.

`abbrev` so that the Pi-`Module ℝ`, `AddCommGroup`, and finite-dimensional
instances on `V → EuclideanSpace ℝ (Fin d)` apply transparently. -/
abbrev Framework (V : Type*) (d : ℕ) : Type _ := V → EuclideanSpace ℝ (Fin d)

/-- The dimension of the framework space: `#V` copies of `EuclideanSpace ℝ (Fin d)`. -/
@[simp]
theorem Framework.finrank [Fintype V] :
    Module.finrank ℝ (Framework V d) = Fintype.card V * d := by
  simp [Module.finrank_pi_fintype]

/-- The `(u, v)`-row of the rigidity matrix as a linear functional on framework
motions: `x ↦ ⟪p u - p v, x u - x v⟫_ℝ`. Internal building block for
`RigidityMap`; consumers go through `rigidityMap_apply` instead. -/
-- Non-`private` because `RigidityMap`'s exposed body references `edgeRow` / `edgeRow_symm`
-- through `Sym2.lift`, which trips the module system's private-in-public check.
noncomputable def edgeRow (p : Framework V d) (u v : V) :
    Framework V d →ₗ[ℝ] ℝ :=
  ((innerSL ℝ (p u - p v)).toLinearMap).comp
    ((LinearMap.proj u : Framework V d →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) -
      LinearMap.proj v)

@[simp]
theorem edgeRow_apply (p : Framework V d) (u v : V) (x : Framework V d) :
    edgeRow p u v x = ⟪p u - p v, x u - x v⟫_ℝ := rfl

theorem edgeRow_symm (p : Framework V d) (u v : V) :
    edgeRow p u v = edgeRow p v u := by
  ext x
  rw [edgeRow_apply, edgeRow_apply, ← neg_sub (p u) (p v), ← neg_sub (x u) (x v),
      inner_neg_neg]

/-- The **rigidity map** of a framework `p`: an `ℝ`-linear map sending an
infinitesimal motion `p' : Framework V d` to the family
`e ↦ ⟪p u - p v, p' u - p' v⟫_ℝ` indexed by the edges `e = s(u, v) ∈ G.edgeSet`.

Built compositionally as `LinearMap.pi` over the per-edge `edgeRow`s, so
linearity in `p'` is inherited from the existing `LinearMap` API. -/
noncomputable def RigidityMap (G : SimpleGraph V) (p : Framework V d) :
    Framework V d →ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearMap.pi fun e : G.edgeSet =>
    Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩ e.val

/-- The rigidity map evaluated at an explicit edge `s(u, v)` is the inner product
`⟪p u - p v, p' u - p' v⟫_ℝ`. -/
@[simp]
theorem rigidityMap_apply (G : SimpleGraph V) (p p' : Framework V d) (u v : V)
    (huv : s(u, v) ∈ G.edgeSet) :
    G.RigidityMap p p' ⟨s(u, v), huv⟩ = ⟪p u - p v, p' u - p' v⟫_ℝ := by
  simp [RigidityMap]

/-- Continuity of `RigidityMap` in its placement: for a fixed motion `x` and edge `e`, the entry
`G.RigidityMap p x e` is a continuous function of `p`. The entry expands to the inner product
`⟪p u - p v, x u - x v⟫`, jointly continuous in `(p, x)` and *a fortiori* continuous in `p` alone
with `x` fixed; the proof inducts on `e : Sym2 V` to expose `s(u, v)`.

Building block for `IsInfinitesimallyRigid.eventually`. Tagged `@[fun_prop]` so downstream
continuity goals involving `RigidityMap` close via the `fun_prop` tactic. -/
@[fun_prop]
theorem continuous_rigidityMap_apply (G : SimpleGraph V) (x : Framework V d)
    (e : G.edgeSet) : Continuous (fun p : Framework V d => G.RigidityMap p x e) := by
  obtain ⟨e, he⟩ := e
  induction e with
  | h u v => simp only [rigidityMap_apply G _ x u v he]; fun_prop

/-- The rigidity map's kernel shrinks under graph inclusion: adding edges can only
add constraints, never remove them. -/
theorem rigidityMap_ker_mono {G G' : SimpleGraph V} (h : G ≤ G') (p : Framework V d) :
    LinearMap.ker (G'.RigidityMap p) ≤ LinearMap.ker (G.RigidityMap p) := by
  intro p' hp'
  rw [LinearMap.mem_ker] at hp' ⊢
  funext ⟨e, he⟩
  exact congr_fun hp' ⟨e, edgeSet_mono h he⟩

/-- The rank of the rigidity map is bounded by the number of edges. -/
theorem rigidityMap_finrank_range_le [Finite V] (G : SimpleGraph V) (p : Framework V d) :
    Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) ≤ G.edgeSet.ncard := by
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  calc Module.finrank ℝ (LinearMap.range (G.RigidityMap p))
      ≤ Module.finrank ℝ (G.edgeSet → ℝ) := Submodule.finrank_le _
    _ = Fintype.card G.edgeSet := Module.finrank_pi ℝ
    _ = G.edgeSet.ncard := (Set.ncard_eq_card_coe _).symm

/-- A framework `p` is **infinitesimally rigid** for `G` if the kernel of the
rigidity map has dimension at most `d (d+1) / 2`, the dimension of the space of trivial
Euclidean motions (translations and infinitesimal rotations).

When the points `p v` affinely span `ℝ^d`, the trivial infinitesimal motions of `p` lie in the
kernel and have that dimension, so the bound says that every infinitesimal motion is trivial,
Jordán's definition (2016, p. 36). In general it says that the rigidity map has rank at least
`d|V| − d(d+1)/2`, where Jordán's equivalent rank form (pp. 36–37) asks for his bound
`S(|V|, d)`. The two agree when `|V| ≥ d` or `|V| ≤ 1`, so always at `d = 2`; when
`2 ≤ |V| ≤ d − 1` this definition is weaker (two vertices with no edge, anywhere in `ℝ³`,
satisfy it). The blueprint's `fmlnote:infinitesimal-rigidity` gives the comparison. The kernel
bound is the form the rank–nullity arguments downstream use. -/
-- The `[Finite V]` instance is semantically required (otherwise `Module.finrank`
-- of the kernel is vacuously `0` and the definition is meaningless), but is not
-- consumed by elaboration of the body. The instance acts as a contract guard so
-- callers cannot accidentally apply this with infinite `V`. The
-- `unusedFintypeInType` syntax linter does not yet extend to `def`s
-- (planned upstream improvement, per Thomas Murrills's Dec-2025 Zulip message),
-- so the env-linter's `unusedArguments` rule is what fires today; once the
-- syntax linter extends, this site would migrate to
-- `set_option linter.unusedFintypeInType false` instead.
@[nolint unusedArguments]
def IsInfinitesimallyRigid [Finite V] (G : SimpleGraph V) (p : Framework V d) : Prop :=
  Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2

/-- A graph `G` is **generically rigid** in dimension `d` if some placement is
infinitesimally rigid.

Defining it through a single placement avoids generic placements (those whose coordinates are
algebraically independent over `ℚ`), which neither direction of Laman's theorem
(`LamanTheorem.lean`) needs. No declaration relates it to rigidity at generic placements; the
blueprint's remark after `def:isGenericallyRigid` compares it with Jordán's definition. -/
def IsGenericallyRigid [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p

/-- Adding edges preserves infinitesimal rigidity at the same placement. -/
theorem IsInfinitesimallyRigid.mono [Finite V] {G G' : SimpleGraph V} (h : G ≤ G')
    {p : Framework V d} (hG : G.IsInfinitesimallyRigid p) : G'.IsInfinitesimallyRigid p :=
  (Submodule.finrank_mono (rigidityMap_ker_mono h p)).trans hG

/-- Adding edges preserves generic rigidity. -/
theorem IsGenericallyRigid.mono [Finite V] {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.IsGenericallyRigid d) : G'.IsGenericallyRigid d :=
  hG.imp fun _ => IsInfinitesimallyRigid.mono h

/-- Iso transport for infinitesimal rigidity: a graph iso `φ : G ≃g H` carries
an infinitesimally rigid placement `p` of `G` to the placement `p ∘ φ.symm` of
`H`, which is also infinitesimally rigid.

The proof builds a linear equivalence between the two rigidity-map kernels by
precomposition with `φ` and uses `LinearEquiv.finrank_eq` to transport the
kernel-dimension bound. -/
theorem IsInfinitesimallyRigid.iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {p : Framework V d}
    (h : G.IsInfinitesimallyRigid p) : H.IsInfinitesimallyRigid (p ∘ φ.symm) := by
  -- Per-edge correspondence: `q' ∈ ker H ↔ q' ∘ φ ∈ ker G`.
  have hH_to_G : ∀ q' : Framework W d,
      (H.RigidityMap (p ∘ φ.symm)) q' = 0 → (G.RigidityMap p) (q' ∘ φ.toEquiv) = 0 := by
    intro q' hq'
    ext ⟨e, he⟩
    induction e with
    | h a b =>
      have hH : s(φ a, φ b) ∈ H.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.map_adj_iff.mpr he
      have key := congr_fun hq' ⟨s(φ a, φ b), hH⟩
      simpa using key
  have hG_to_H : ∀ p' : Framework V d,
      (G.RigidityMap p) p' = 0 →
        (H.RigidityMap (p ∘ φ.symm)) (p' ∘ φ.symm.toEquiv) = 0 := by
    intro p' hp'
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have hG : s(φ.symm u, φ.symm v) ∈ G.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.symm.map_adj_iff.mpr he
      have key := congr_fun hp' ⟨s(φ.symm u, φ.symm v), hG⟩
      simpa using key
  -- Linear equiv between the two kernels.
  let kerEquiv : LinearMap.ker (H.RigidityMap (p ∘ φ.symm)) ≃ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    { toFun := fun q' => ⟨q'.1 ∘ φ.toEquiv,
        LinearMap.mem_ker.mpr (hH_to_G q'.1 (LinearMap.mem_ker.mp q'.2))⟩
      invFun := fun p' => ⟨p'.1 ∘ φ.symm.toEquiv,
        LinearMap.mem_ker.mpr (hG_to_H p'.1 (LinearMap.mem_ker.mp p'.2))⟩
      left_inv := fun _ => Subtype.ext <| funext fun _ => by simp
      right_inv := fun _ => Subtype.ext <| funext fun _ => by simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact kerEquiv.finrank_eq.le.trans h

/-- Iso transport for generic rigidity: a graph iso preserves generic rigidity. -/
theorem IsGenericallyRigid.iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (h : G.IsGenericallyRigid d) : H.IsGenericallyRigid d := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p ∘ φ.symm, hp.iso φ⟩

/-- **Openness of infinitesimal rigidity in the placement.** If `p₀` is infinitesimally rigid for
`G`, then every placement `p` in some neighborhood of `p₀` is also infinitesimally rigid.

The proof picks a basis of `LinearMap.range (G.RigidityMap p₀)` of size `r = rank (G.RigidityMap
p₀)`, lifts each basis vector to a preimage in `Framework V d`, and uses
`LinearIndependent.eventually` plus continuity of `p ↦ G.RigidityMap p (preimg i)` to conclude that
the lifted images stay linearly independent in a neighborhood of `p₀`. Combined with rank-nullity
on both `p₀` and the nearby `p`, this gives the kernel-dim bound. -/
theorem IsInfinitesimallyRigid.eventually [Finite V] {G : SimpleGraph V}
    {p₀ : Framework V d} (h₀ : G.IsInfinitesimallyRigid p₀) :
    ∀ᶠ p in 𝓝 p₀, G.IsInfinitesimallyRigid p := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  set r := Module.finrank ℝ (LinearMap.range (G.RigidityMap p₀)) with hr_def
  -- Lift a basis of `LinearMap.range (G.RigidityMap p₀)` to preimages.
  let e := Module.finBasis ℝ (LinearMap.range (G.RigidityMap p₀))
  let preimg : Fin r → Framework V d := fun i =>
    Classical.choose (LinearMap.mem_range.mp (e i).property)
  have h_preimg_eq : ∀ i, G.RigidityMap p₀ (preimg i) = (e i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (e i).property)
  -- LI of the basis ⇒ LI of `(e i).val` in the ambient space (subtype injective)
  --                  ⇒ LI of `G.RigidityMap p₀ ∘ preimg`.
  have h_subtype_li : LinearIndependent ℝ (fun i => (e i).val) :=
    e.linearIndependent.map' (LinearMap.range (G.RigidityMap p₀)).subtype
      (Submodule.ker_subtype _)
  have h_preimg_li : LinearIndependent ℝ (fun i => G.RigidityMap p₀ (preimg i)) := by
    convert h_subtype_li using 1
    funext i; exact h_preimg_eq i
  -- Continuity of `p ↦ (G.RigidityMap p (preimg i))_i` into `Fin r → (G.edgeSet → ℝ)`.
  have h_cont : Continuous
      (fun p : Framework V d => fun i => G.RigidityMap p (preimg i)) := by fun_prop
  -- Filter pullback of `LinearIndependent.eventually`.
  have h_event_li : ∀ᶠ p in 𝓝 p₀,
      LinearIndependent ℝ (fun i => G.RigidityMap p (preimg i)) :=
    h_cont.continuousAt.tendsto.eventually h_preimg_li.eventually
  filter_upwards [h_event_li] with p hp_li
  -- Lift LI back to the range submodule of `RigidityMap p`, then apply
  -- `LinearIndependent.fintypeCard_le_finrank` to get `r ≤ rank (RigidityMap p)`.
  let lift : Fin r → LinearMap.range (G.RigidityMap p) :=
    fun i => ⟨G.RigidityMap p (preimg i), LinearMap.mem_range_self _ _⟩
  have h_lift_li : LinearIndependent ℝ lift := by
    have h_eq : (fun i => G.RigidityMap p (preimg i)) =
        (LinearMap.range (G.RigidityMap p)).subtype ∘ lift := rfl
    rw [h_eq] at hp_li
    exact hp_li.of_comp _
  have h_card_le := h_lift_li.fintype_card_le_finrank
  rw [Fintype.card_fin] at h_card_le
  -- Combine with rank-nullity on both `p₀` and `p`.
  unfold IsInfinitesimallyRigid
  have h_rn₀ := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p₀)
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  have h₀_unfold : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p₀)) ≤ d * (d + 1) / 2 := h₀
  omega

/-- A graph `G` is **generically rigid with an injective placement** in dimension `d` if some
infinitesimally rigid placement is also injective. It implies `IsGenericallyRigid`
(`IsGenericallyRigidInj.toIsGenericallyRigid`), strictly at `d = 0`, where `K₂` has no injective
placement; the blueprint's remark after `def:isGenericallyRigidInj` compares the two. The
Henneberg induction of Laman's theorem (`LamanTheorem.lean`) maintains the injective placement at
each step (the per-move arguments of `HennebergRigidity.lean` need `p a ≠ p b`, which
`IsGenericallyRigid` does not supply) and weakens to `IsGenericallyRigid` at the end. -/
def IsGenericallyRigidInj [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p ∧ Function.Injective p

/-- An injectively-generic-rigid graph is generically rigid. -/
theorem IsGenericallyRigidInj.toIsGenericallyRigid [Finite V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigidInj d) : G.IsGenericallyRigid d :=
  h.imp fun _ hp => hp.1

/-- Adding edges preserves injective generic rigidity at the same placement. -/
theorem IsGenericallyRigidInj.mono [Finite V] {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.IsGenericallyRigidInj d) : G'.IsGenericallyRigidInj d :=
  hG.imp fun _ hp => ⟨hp.1.mono h, hp.2⟩

/-- Iso transport for injective generic rigidity: a graph iso preserves injective generic
rigidity. Injectivity of `p ∘ φ.symm` follows from injectivity of `p` since `φ.symm` is a
bijection. -/
theorem IsGenericallyRigidInj.iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (h : G.IsGenericallyRigidInj d) : H.IsGenericallyRigidInj d := by
  obtain ⟨p, hp_rig, hp_inj⟩ := h
  exact ⟨p ∘ φ.symm, hp_rig.iso φ, hp_inj.comp φ.symm.toEquiv.injective⟩

/-- A generically rigid graph in dimension `d` on `n` vertices has at least
`d * n − d(d+1)/2` edges. Phrased additively, to avoid `ℕ` subtraction.

The proof is rank-nullity: pick an infinitesimally rigid placement `p`; then
`d * n = dim Framework = dim range + dim ker ≤ #E + d(d+1)/2`. -/
theorem IsGenericallyRigid.card_mul_le [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid d) :
    d * Fintype.card V ≤ G.edgeSet.ncard + d * (d + 1) / 2 := by
  obtain ⟨p, h_ker⟩ := hG
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2 := h_ker
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  have h_range := G.rigidityMap_finrank_range_le p
  omega

/-- The K₂ worked example, *injective* form: the complete graph on two vertices is generically
rigid with an injective placement in every positive dimension `d + 1`. Witnessed by `p 0 = 0`,
`p 1 = e₀` (first standard basis vector). -/
theorem top_fin_two_isGenericallyRigidInj (d : ℕ) :
    (⊤ : SimpleGraph (Fin 2)).IsGenericallyRigidInj (d + 1) := by
  set p : Framework (Fin 2) (d + 1) := ![0, EuclideanSpace.single 0 1] with hp_def
  refine ⟨p, ?_, ?_⟩
  · -- Infinitesimal rigidity.
    change Module.finrank ℝ (LinearMap.ker
      ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) ≤ (d + 1) * (d + 2) / 2
    have h_edge : s((0 : Fin 2), 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet := by simp
    have h_total : Module.finrank ℝ (Framework (Fin 2) (d + 1)) = 2 * (d + 1) := by
      rw [Framework.finrank]; simp
    have h_rn :=
      LinearMap.finrank_range_add_finrank_ker ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)
    have h_range_pos :
        1 ≤ Module.finrank ℝ (LinearMap.range
          ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) := by
      rw [Submodule.one_le_finrank_iff, Ne, LinearMap.range_eq_bot]
      intro h_eq
      have h_val :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = -1 := by
        simp [rigidityMap_apply, hp_def, inner_neg_left]
      have h_zero :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = 0 := by rw [h_eq]; rfl
      linarith
    -- Bound: `2*(d+1) - 1 = 2d+1 ≤ (d+1)(d+2)/2` for all `d ≥ 0`.
    have h_quadratic : 4 * d + 2 ≤ (d + 1) * (d + 2) := by nlinarith [Nat.le_mul_self d]
    omega
  · -- Injectivity: `p 0 = 0` has norm 0; `p 1 = e₀` has norm 1.
    intro i j hij
    have h_norm : ‖p i‖ = ‖p j‖ := congrArg _ hij
    fin_cases i <;> fin_cases j <;> revert h_norm <;> simp [hp_def]

/-- The K₂ worked example: the complete graph on two vertices is generically
rigid in any dimension `d`. For `d ≥ 1`, weakened from the injective form
`top_fin_two_isGenericallyRigidInj`; for `d = 0` the framework space is
zero-dimensional, so the kernel is, and any placement is rigid. -/
theorem top_fin_two_isGenericallyRigid (d : ℕ) :
    (⊤ : SimpleGraph (Fin 2)).IsGenericallyRigid d := by
  rcases d with _ | d
  · -- d = 0: framework space is zero-dimensional, so any placement is rigid.
    refine ⟨0, ?_⟩
    have h_total : Module.finrank ℝ (Framework (Fin 2) 0) = 0 := by
      rw [Framework.finrank]; simp
    exact (Submodule.finrank_le _).trans_eq h_total
  · exact (top_fin_two_isGenericallyRigidInj d).toIsGenericallyRigid

end SimpleGraph


end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0001/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityLaman_Mathlib_Data_Finset_BooleanAlgebra.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Finset/BooleanAlgebra.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidate: coercion of the complement of a singleton finset

Mathlib's `Finset.coe_compl` and `Finset.coe_singleton` give the two ingredient
rewrites; this file packages their composition as a single `simp`/`norm_cast`
lemma.

The companion `card_compl_singleton` belongs beside `Finset.card_compl` in
`Mathlib/Data/Fintype/Card.lean` (mirrored at
`CombinatorialRigidity/Mathlib/Data/Fintype/Card.lean`).

The Lean namespace is the upstream one (`Finset`), not the project's, so
promotion is a copy-paste alongside `Finset.coe_compl`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Finset/BooleanAlgebra.lean`)

* `Finset.coe_compl_singleton` — `(({a} : Finset α)ᶜ : Set α) = ({a} : Set α)ᶜ`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[norm_cast]
theorem coe_compl_singleton (a : α) :
    ((({a} : Finset α)ᶜ : Finset α) : Set α) = ({a} : Set α)ᶜ := by
  rw [coe_compl, coe_singleton]

end Finset


end
end BundleSource0002

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0002/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0002.json"

section BundleSource0003
/- Source: Papers/RigidityLaman_Mathlib_Data_Fintype_Card.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Fintype/Card.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/








/-!
# Upstream candidates: cardinality of the complement of a singleton finset, and of ordered pairs

Companion of `Finset.coe_compl_singleton` in
`CombinatorialRigidity/Mathlib/Data/Finset/BooleanAlgebra.lean`. The
`card` form lands next to `Finset.card_compl` in `Mathlib/Data/Fintype/Card.lean`.

`Fintype.card_subtype_fst_lt_snd` counts the strictly-increasing ordered pairs of a linearly-ordered
fintype as `(Fintype.card α).choose 2`, via the bijection with two-element subsets
(`Fintype.card_finset_len`). It belongs alongside `Sym2.card` / `Fintype.card_finset_len`.

The Lean namespaces are the upstream ones (`Finset`, `Fintype`), not the project's, so
promotion is a copy-paste alongside `Finset.card_compl` / `Fintype.card_finset_len`. See
`DESIGN.md` "Mirror directory".

## Contents (target files: `Mathlib/Data/Fintype/Card.lean`, `Mathlib/Data/Fintype/Powerset.lean`)

* `Finset.card_compl_singleton` — `(({a} : Finset α)ᶜ).card = Fintype.card α - 1`.
* `Fintype.card_subtype_fst_lt_snd` —
  `Fintype.card {q : α × α // q.1 < q.2} = (Fintype.card α).choose 2`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp]
theorem card_compl_singleton (a : α) :
    (({a} : Finset α)ᶜ).card = Fintype.card α - 1 := by
  rw [card_compl, card_singleton]

end Finset

namespace Fintype

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- **The strictly-increasing ordered pairs of a linearly-ordered fintype number
`(Fintype.card α).choose 2`.** The subtype `{q : α × α // q.1 < q.2}` of ordered pairs is in
bijection with the two-element subsets `{s : Finset α // s.card = 2}` — a pair `(i, j)` with
`i < j` maps to `{i, j}`, and a two-element set maps to its increasing enumeration
`(orderEmbOfFin 0, orderEmbOfFin 1)` — so the count is `(Fintype.card α).choose 2`
(`Fintype.card_finset_len`). -/
theorem card_subtype_fst_lt_snd :
    Fintype.card {q : α × α // q.1 < q.2} = (Fintype.card α).choose 2 := by
  classical
  -- The increasing enumeration of the pair `{i, j}` (with `i < j`) is `![i, j]`.
  have hemb : ∀ {i j : α} (hij : i < j),
      (({i, j} : Finset α).orderEmbOfFin
        (Finset.card_pair (ne_of_lt hij)) : Fin 2 → α) = ![i, j] :=
    fun {i j} hij => (Finset.orderEmbOfFin_unique _
      (fun x => by fin_cases x <;> simp)
      (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)).symm
  rw [← Fintype.card_finset_len (α := α) 2]
  apply Fintype.card_congr
  refine
    { toFun := fun q => ⟨{q.1.1, q.1.2}, by rw [Finset.card_pair (ne_of_lt q.2)]⟩
      invFun := fun s =>
        ⟨(s.1.orderEmbOfFin s.2 0, s.1.orderEmbOfFin s.2 1), by
          exact (s.1.orderEmbOfFin s.2).strictMono (by decide)⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨i, j⟩, hij⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    rw [hemb hij]
    exact ⟨rfl, rfl⟩
  · rintro ⟨s, hs⟩
    -- `orderEmbOfFin 0`, `orderEmbOfFin 1` are exactly the two elements of `s` (its range), so
    -- `{orderEmbOfFin 0, orderEmbOfFin 1} = s`.
    refine Subtype.ext ?_
    rw [← Finset.coe_inj, Finset.coe_insert, Finset.coe_singleton,
      ← Finset.range_orderEmbOfFin s hs]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    · rintro ⟨y, rfl⟩; fin_cases y <;> simp

end Fintype


end
end BundleSource0003

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0003/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0003.json"

section BundleSource0004
/- Source: Papers/RigidityLaman_Laman.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Laman.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/







/-!
# Laman graphs

A simple graph is **Laman** (or *minimally rigid in the plane*) if it is
`(2, 3)`-tight: every set of `k ≥ 2` vertices spans at most `2k − 3`
edges, with equality globally.

Laman's theorem (Pollaczek-Geiringer 1927, Laman 1970) identifies these
graphs with the generically minimally rigid graphs in the plane;
`LamanTheorem.lean` proves it in the form "generically rigid iff some
spanning subgraph is Laman". This file proves the facts about Laman graphs
that its induction rests on.

## Main definitions

* `SimpleGraph.IsLaman G` — `G.IsTight 2 3`.

## Main lemmas

* `SimpleGraph.IsLaman.isSparse`, `IsLaman.edgeSet_ncard` — accessor
  lemmas for the two components.
* `SimpleGraph.isLaman_iff` — unfolds `IsLaman` to the explicit
  conjunction `IsSparse 2 3 ∧ #E + 3 = 2 * #V`.
* `SimpleGraph.IsLaman.two_le_degree` — every vertex of a Laman graph
  on `n ≥ 3` vertices has degree at least 2.
* `SimpleGraph.IsLaman.exists_two_le_degree_le_three` — every Laman graph
  on `n ≥ 3` vertices contains a vertex of degree exactly 2 or 3. The
  degree-≤-3 half is the general `IsSparse.exists_degree_le_three`.
* `SimpleGraph.top_fin_two_isLaman` — `K₂` is Laman. The base case for
  the Henneberg construction.
* `SimpleGraph.IsLaman.iso` — Laman is preserved under graph isomorphism.

## Implementation notes

`IsLaman` is a non-reducible `def` (= `IsTight 2 3`); `grind` will not
unfold it. Use `refine ⟨?_, ?_⟩` or pattern-match to break the
And-structure inherited from `IsTight`. See `TACTICS-GOLF.md` §4.

The blueprint's `sec:laman` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- A simple graph is **Laman** (or *minimally rigid in the plane*) if it is `(2, 3)`-tight. -/
@[expose] def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

/-- A Laman graph on `n` vertices has exactly `2n − 3` edges. -/
theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

/-- Unfolding of `IsLaman`: a graph is Laman iff it is `(2, 3)`-sparse and globally meets the
`2n − 3` edge count. -/
theorem isLaman_iff {G : SimpleGraph V} :
    G.IsLaman ↔ G.IsSparse 2 3 ∧ G.edgeSet.ncard + 3 = 2 * Nat.card V := Iff.rfl

/-! ### Minimum degree

In a Laman graph on `n ≥ 3` vertices, every vertex has degree at least 2. Apply sparsity to the
vertex set `{v}ᶜ`: the edges spanned there are exactly the edges of `G` not incident to `v`, so
`#E − G.degree v + 3 ≤ 2 * (n − 1)`; combined with tightness `#E + 3 = 2n`, this forces
`G.degree v ≥ 2`. -/
theorem IsLaman.two_le_degree [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ G.degree v := by
  classical
  -- Apply sparsity to the Finset `{v}ᶜ`; combine with the vertex-deletion partition + tightness.
  have hsparse := h.isSparse ({v} : Finset V)ᶜ (by simp; omega)
  have hpart := G.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet v
  have hE := h.edgeSet_ncard
  grind only [Finset.coe_compl_singleton, Finset.card_compl_singleton,
    G.ncard_incidenceSet_eq_degree, Nat.card_eq_fintype_card]

/-! ### A vertex of low degree

By `IsSparse.exists_degree_le_three` (handshake + the global edge bound), any `(2, 3)`-sparse
graph on `n ≥ 2` vertices has a vertex of degree at most 3. Combined with
`IsLaman.two_le_degree`, when `n ≥ 3` this yields a vertex of degree exactly 2 or 3: the
vertex that a reverse Henneberg move removes. -/

/-- In a Laman graph on `n ≥ 3` vertices there is a vertex of degree exactly 2 or 3.
A reverse Henneberg move removes such a vertex; the reverse decomposition
`Henneberg.IsLaman.exists_typeI_or_typeII_reverse` finds it through the sparse one,
`IsSparse.exists_typeI_or_typeII_reverse`, rather than through this lemma. -/
theorem IsLaman.exists_two_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  obtain ⟨v, hv⟩ := h.isSparse.exists_degree_le_three (by omega)
  exact ⟨v, h.two_le_degree hV v, hv⟩

/-- A graph isomorphism preserves the Laman property. Specialization of `IsTight.iso` at
`(k, ℓ) = (2, 3)`. -/
theorem IsLaman.iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : G.IsLaman) : H.IsLaman :=
  IsTight.iso φ h

/-! ### Base case for Henneberg: `K₂` is Laman -/

/-- A Laman graph on exactly two vertices is the complete graph K₂. The proof reads off
`#G.edgeSet = 1` from tightness and matches with `#(⊤ : SimpleGraph V).edgeSet = 1`;
since `G ≤ ⊤` automatically, equal cardinalities force the edge sets equal, hence
`G = ⊤`. The (⇐) direction of Laman's theorem uses this for the base case of the
Henneberg induction on `Fintype.card V`. -/
theorem IsLaman.eq_top_of_card_eq_two [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) (hV : Fintype.card V = 2) : G = ⊤ := by
  rw [← edgeSet_inj]
  have hG_card : G.edgeSet.ncard = 1 := by
    grind only [h.edgeSet_ncard, Nat.card_eq_fintype_card]
  have hTop_card : ((⊤ : SimpleGraph V).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two, hV]; rfl
  refine Set.eq_of_subset_of_ncard_le (edgeSet_subset_edgeSet.mpr le_top) ?_ ?_
  · rw [hTop_card, hG_card]
  · classical
    exact (Set.toFinite _)

/-- The complete graph on two vertices is Laman: it has one edge, matching `2 · 2 − 3 = 1`.
This is the base case of the Henneberg construction. -/
theorem top_fin_two_isLaman : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  -- Sparsity. Only the case `s = Finset.univ` is non-vacuous.
  obtain rfl : s = Finset.univ :=
    s.eq_univ_of_card (by have := s.card_le_univ; grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

end SimpleGraph


end
end BundleSource0004

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0004/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0004.json"

section BundleSource0005
/- Source: Papers/RigidityLaman_Mathlib_Data_Finset_Option.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Finset/Option.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidate: addition-form cardinality lemma for `Finset.eraseNone`

Mathlib has `Finset.card_eraseNone_of_mem`:
```
(h : none ∈ s) : #s.eraseNone = #s - 1
```
in `ℕ`-subtraction form. This project uniformly avoids `ℕ`-subtraction (see
`ROADMAP.md` "Engineering conventions"), so consumers of the lemma have to
re-derive `s.eraseNone.card + 1 = s.card` via `Nat.sub_add_cancel` plus a
positivity witness — three extra tokens at every call site.

The Lean namespace is the upstream one (`Finset`), so promotion to mathlib is
a copy-paste alongside `Finset.card_eraseNone_of_mem`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Finset/Option.lean`)

* `Finset.card_eraseNone_add_one_of_mem` — `none ∈ s → #s.eraseNone + 1 = #s`.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

/-- Addition-form companion to `Finset.card_eraseNone_of_mem`: when `none ∈ s`,
the some-elements of `s` plus the `none` itself recover `#s`. Phrased without
`ℕ`-subtraction so that `omega` and `grind` can chain it directly. -/
theorem card_eraseNone_add_one_of_mem {s : Finset (Option α)} (h : none ∈ s) :
    s.eraseNone.card + 1 = s.card := by
  rw [card_eraseNone_of_mem h, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, h⟩)]

end Finset


end
end BundleSource0005

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0005/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0005.json"

section BundleSource0006
/- Source: Papers/RigidityLaman_Henneberg.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Henneberg.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/










/-!
# Henneberg moves

Two vertex-extension operations on simple graphs. The Laman graphs are exactly the graphs
built from `K₂` by them, a characterization due to Henneberg (1911), Pollaczek-Geiringer (1927)
and Laman (1970). The project proves its two inductive steps, not the characterization itself:
the moves preserve the Laman property (this file), and every Laman graph on at least three
vertices is, up to isomorphism, a move applied to a smaller Laman graph
(`HennebergReverse.lean`).

* **Type I** joins a fresh vertex to two existing vertices `a` and `b` (degree 2 when
  `a ≠ b`).
* **Type II** deletes the edge `s(a, b)`, if present, and joins a fresh vertex to `a`, `b` and a
  third existing vertex `c` (degree 3 when the three are distinct).

The fresh vertex is represented as `none : Option V`, with old vertices
embedded via `some`. This is mathlib's canonical "add one element" idiom
(cf. `Equiv.optionEquivSumPUnit`); it avoids a freshness side-condition on
every move and keeps the type signatures readable.

## Main definitions

* `SimpleGraph.Henneberg.typeI G a b : SimpleGraph (Option V)`.
* `SimpleGraph.Henneberg.typeII G a b c : SimpleGraph (Option V)`.

The blueprint's `sec:henneberg` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- The **Type I Henneberg move**: extend `G : SimpleGraph V` by a fresh vertex
of degree 2 joined to two existing vertices `a` and `b`. The output graph lives
on `Option V`, with the new vertex represented as `none`.

When `a = b`, the new vertex has degree 1 (the parallel edges collapse); the
move preserves the Laman property only under `a ≠ b`. -/
@[expose] def typeI (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | some u, none => u = a ∨ u = b
    | none, some v => v = a ∨ v = b
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun
    | none => id
    | some u => G.loopless.irrefl u⟩

/-- The **Type II Henneberg move**: extend `G : SimpleGraph V` by deleting the
edge `s(a, b)` and adding a fresh vertex of degree 3 joined to `a`, `b`, and a
third vertex `c`. The output graph lives on `Option V`.

The move is well-defined for any `a b c : V`. It preserves the Laman property when
`G.Adj a b` (so `a ≠ b`) and `c` is neither `a` nor `b` (`typeII_isLaman`); at `a = b` it is
the Type I move at `a` and `c`. -/
@[expose] def typeII (G : SimpleGraph V) (a b c : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v ∧ s(u, v) ≠ s(a, b)
    | some u, none => u = a ∨ u = b ∨ u = c
    | none, some v => v = a ∨ v = b ∨ v = c
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, fun heq => h.2 (Sym2.eq_swap.trans heq)⟩⟩
  loopless := ⟨fun
    | none => id
    | some u => fun h => G.loopless.irrefl u h.1⟩

/-! ### Adjacency unfolding -/

variable {G : SimpleGraph V} {a b c u v : V}

@[simp] lemma typeI_adj_some_some : (typeI G a b).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma typeI_adj_some_none : (typeI G a b).Adj (some u) none ↔ u = a ∨ u = b := Iff.rfl

@[simp] lemma typeI_adj_none_some : (typeI G a b).Adj none (some v) ↔ v = a ∨ v = b := Iff.rfl

lemma typeI_not_adj_none_none : ¬ (typeI G a b).Adj none none := id

@[simp] lemma typeII_adj_some_some :
    (typeII G a b c).Adj (some u) (some v) ↔ G.Adj u v ∧ s(u, v) ≠ s(a, b) := Iff.rfl

@[simp] lemma typeII_adj_some_none :
    (typeII G a b c).Adj (some u) none ↔ u = a ∨ u = b ∨ u = c := Iff.rfl

@[simp] lemma typeII_adj_none_some :
    (typeII G a b c).Adj none (some v) ↔ v = a ∨ v = b ∨ v = c := Iff.rfl

lemma typeII_not_adj_none_none : ¬ (typeII G a b c).Adj none none := id

instance instDecidableTypeIAdj [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : DecidableRel (typeI G a b).Adj := fun u v =>
  match u, v with
  | some u, some v => (inferInstance : Decidable (G.Adj u v))
  | some u, none => (inferInstance : Decidable (u = a ∨ u = b))
  | none, some v => (inferInstance : Decidable (v = a ∨ v = b))
  | none, none => instDecidableFalse

instance instDecidableTypeIIAdj [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (typeII G a b c).Adj := fun u v =>
  match u, v with
  | some u, some v => (inferInstance : Decidable (G.Adj u v ∧ s(u, v) ≠ s(a, b)))
  | some u, none => (inferInstance : Decidable (u = a ∨ u = b ∨ u = c))
  | none, some v => (inferInstance : Decidable (v = a ∨ v = b ∨ v = c))
  | none, none => instDecidableFalse

/-! ### Sparsity helpers for the `_isLaman` proofs

`typeI_isLaman` and `typeII_isLaman` decompose `(typeI/II _).edgesIn ↑s` into "old" edges (image
under `some`) plus the subset of fresh edges (each of the form `s(none, some _)`) that lie in
`s.sym2`. The three helpers below isolate the recurring set-cardinality steps used in the
sparsity case analysis. The last two are stated against `s.eraseNone` (mathlib's name for the
some-preimage of a `Finset (Option V)`) so callers can pass the produced equalities /
non-memberships directly. -/

/-- If `none ∉ s`, no fresh edge `s(none, some _)` lies in `s.sym2`, so any subset of fresh edges
intersected with `s.sym2` has cardinality `0`. -/
private lemma fresh_sym2_ncard_eq_zero_of_none_notMem [Finite V] {s : Finset (Option V)}
    (hnone : none ∉ s) (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, none ∈ e) :
    (xs ∩ ((↑s : Set (Option V)).sym2)).ncard = 0 := by
  rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro e ⟨he, hsub⟩
  exact hnone (Set.mem_sym2_iff_subset.mp hsub (h_xs e he))

/-- If `s.eraseNone = {w}`, every fresh edge `s(none, some x)` that lies in `s.sym2` satisfies
`x = w`, so the intersection with `s.sym2` is contained in `{s(none, some w)}`. -/
private lemma fresh_sym2_subset_singleton {s : Finset (Option V)} {w : V}
    (hw : s.eraseNone = {w})
    (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, ∃ x : V, e = s(none, some x)) :
    xs ∩ ((↑s : Set (Option V)).sym2) ⊆ ({s(none, some w)} : Set _) := by
  rintro e ⟨he, hsub⟩
  obtain ⟨x, rfl⟩ := h_xs e he
  rw [Set.mem_sym2_iff_subset, Sym2.coe_mk] at hsub
  have hx : x ∈ s.eraseNone := Finset.mem_eraseNone.mpr (hsub (Or.inr rfl))
  rw [hw, Finset.mem_singleton] at hx
  exact hx ▸ rfl

/-- The triple-fresh-edges intersection is bounded by `2` when at least one of the three vertices
sits outside `s.eraseNone`: that vertex's edge fails the `s.sym2` membership, leaving at most the
other two. -/
private lemma fresh_sym2_triple_inter_ncard_le_two {s : Finset (Option V)}
    {x y z : V} (hx : x ∉ s.eraseNone) :
    (({s(none, some x), s(none, some y), s(none, some z)} : Set _) ∩
        ((↑s : Set (Option V)).sym2)).ncard ≤ 2 := by
  refine (Set.ncard_le_ncard (?_ : _ ⊆
      ({s(none, some y), s(none, some z)} : Set _))).trans (Set.ncard_pair_le _ _)
  rintro e ⟨hpair, hsub⟩
  have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
  rcases hpair with rfl | rfl | rfl
  · exact (hx (Finset.mem_eraseNone.mpr (hsubV (by simp)))).elim
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

/-! ### Edge set of `typeI`

The edge set of `typeI G a b` decomposes into the image of `G.edgeSet` under `some` plus the two
new edges joining `none` to `some a` and `some b`. -/

/-- Edge set of `typeI G a b`: the old edges (image of `G.edgeSet` under `some`) together with the
two new edges joining `none` to `some a` and `some b`. -/
lemma typeI_edgeSet (G : SimpleGraph V) (a b : V) :
    (typeI G a b).edgeSet =
      (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

/-- Cardinality of `typeI G a b`'s edge set: under `a ≠ b`, two new edges are added. -/
lemma typeI_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    ((typeI G a b).edgeSet).ncard = G.edgeSet.ncard + 2 := by
  have hDisj : Disjoint (Sym2.map some '' G.edgeSet)
      ({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl) <;> simp)
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective, Set.ncard_pair (by simp [hab])]

/-- Cardinality decomposition of `(typeI G a b).edgesIn ↑s`: the old `G`-edges with both endpoints
in `s.eraseNone`, plus the fresh edges `{s(none, some a), s(none, some b)}` that lie in `↑s`. The
two summands are disjoint by `Sym2.disjoint_image_map_some`. -/
private lemma typeI_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b : V)
    (s : Finset (Option V)) :
    ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V)).ncard +
      (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeI G a b).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V) ∪ T := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;> simp [edgesIn, T]
  have h_disj : Disjoint (Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V)) T :=
    Sym2.disjoint_image_map_some fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

/-! ### Type I preserves the Laman property -/

/-- The Type I Henneberg move preserves the Laman property: if `G` is Laman and `a ≠ b`, then
`typeI G a b` is Laman. Tightness follows from `typeI_edgeSet_ncard` and `Finite.card_option`;
sparsity is by case analysis on `none ∈ s` and on the cardinality of `s.eraseNone` (the
some-preimage `s'`). -/
theorem typeI_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman)
    {a b : V} (hab : a ≠ b) : (typeI G a b).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · -- Sparsity. `s' := s.eraseNone` is the some-preimage; `T` is the fresh edges in `↑s`.
    set s' : Finset V := s.eraseNone
    set T : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
    have h_ncard : ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V)).ncard + T.ncard :=
      typeI_edgesIn_ncard_decomp G a b s
    have hT_le_2 : T.ncard ≤ 2 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_pair_le _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s.card = s'.card + 1`.
      have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      -- Sub-case on `s'.card`: 0 (vacuous), 1 (singleton), ≥ 2 (use sparsity).
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · -- s'.card = 0: precondition fails (`s.card = 1`).
        omega
      · -- s'.card = 1: `s' = {w}`. Then `(G.edgesIn ↑s').ncard = 0` and `T.ncard ≤ 1`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V)).ncard = 0 := by rw [hw]; simp
        have hT_sub : T ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT_le_1 : T.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: apply `G`'s sparsity on `s'`.
        have hG := h.isSparse s' (by omega)
        omega
    · -- Case `none ∉ s`. Then `T.ncard = 0` and `s.card = s'.card`.
      have hsc : s.card = s'.card := (Finset.card_eraseNone_of_notMem hnone).symm
      have hT_empty : T.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      omega
  · -- Tightness.
    grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

/-- Inverse of `typeI_isLaman`: if a Type I move on `G` produces a Laman graph (with the two
existing endpoints `a ≠ b` distinct), then `G` itself is Laman. The two facts together give
`typeI_isLaman_iff` below.

The proof is dual to `typeI_isLaman` and reuses `typeI_edgesIn_ncard_decomp`: an arbitrary
`s' : Finset V` lifts to `s := s'.image some : Finset (Option V)`, where `none ∉ s` collapses the
fresh-edge contribution to zero and the edges-in count of `(typeI G a b)` on `s` equals that of `G`
on `s'`. -/
theorem typeI_reverse_isLaman [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (h : (typeI G a b).IsLaman) : G.IsLaman := by
  classical
  refine ⟨fun s' hs' => ?_, ?_⟩
  · -- Sparsity. Lift `s'` to `s := s'.image some` and apply `(typeI G a b)`'s sparsity there.
    set s : Finset (Option V) := s'.image some
    have hs_card : s.card = s'.card :=
      Finset.card_image_of_injective s' (Option.some_injective _)
    have hnone : none ∉ s := by simp [s]
    have hT_zero : (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard = 0 :=
      fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
    have h_decomp := typeI_edgesIn_ncard_decomp G a b s
    rw [Finset.eraseNone_image_some, hT_zero, add_zero] at h_decomp
    have hsparse := h.isSparse s (by rw [hs_card]; exact hs')
    rw [h_decomp, hs_card] at hsparse
    exact hsparse
  · -- Tightness.
    grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

/-- The Type I Henneberg move and its underlying graph are simultaneously Laman: under `a ≠ b`,
`(typeI G a b).IsLaman ↔ G.IsLaman`. -/
theorem typeI_isLaman_iff [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsLaman ↔ G.IsLaman :=
  ⟨typeI_reverse_isLaman hab, fun h => typeI_isLaman h hab⟩

/-! ### Edge set of `typeII`

The edge set of `typeII G a b c` decomposes into the image of `G.edgeSet \ {s(a, b)}` under `some`
plus the three new edges joining `none` to `some a`, `some b`, and `some c`. -/

/-- Edge set of `typeII G a b c`: the old edges other than `s(a, b)` (image under `some`) together
with the three new edges joining `none` to `some a`, `some b`, and `some c`. -/
lemma typeII_edgeSet (G : SimpleGraph V) (a b c : V) :
    (typeII G a b c).edgeSet =
      (Sym2.map some '' (G.edgeSet \ {s(a, b)})) ∪
        {s(none, some a), s(none, some b), s(none, some c)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

/-- Cardinality of `typeII G a b c`'s edge set: the deletion-then-`+3-new-edges` arithmetic. The
hypotheses force the three new edges to be pairwise distinct; the deletion is recorded in the
right-hand side as `G.edgeSet \ {s(a, b)}`, so this lemma does not assume `G.Adj a b`. -/
lemma typeII_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b c : V}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ((typeII G a b c).edgeSet).ncard = (G.edgeSet \ {s(a, b)}).ncard + 3 := by
  have hDisj : Disjoint (Sym2.map some '' (G.edgeSet \ {s(a, b)}))
      ({s(none, some a), s(none, some b), s(none, some c)} :
        Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl | rfl) <;> simp)
  rw [typeII_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective,
    Set.ncard_insert_of_notMem (by simp [hab, hca.symm]) (by simp),
    Set.ncard_pair (by simp [hcb.symm])]

/-- Cardinality decomposition of `(typeII G a b c).edgesIn ↑s`: the old `G`-edges (less `s(a, b)`)
with both endpoints in `s.eraseNone`, plus the fresh edges
`{s(none, some a), s(none, some b), s(none, some c)}` that lie in `↑s`. The two summands are
disjoint by `Sym2.disjoint_image_map_some`. -/
private lemma typeII_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b c : V)
    (s : Finset (Option V)) :
    ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}).ncard +
      (({s(none, some a), s(none, some b), s(none, some c)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T' : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
      ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeII G a b c).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}) ∪ T' := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;>
      (simp [edgesIn, T']; try tauto)
  have h_disj : Disjoint (Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)})) T' :=
    Sym2.disjoint_image_map_some
      fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

/-! ### Type II preserves the Laman property -/

/-- The Type II Henneberg move preserves the Laman property: if `G` is Laman, `G.Adj a b` (so
`a ≠ b`) and `c` differs from `a` and `b`, then `typeII G a b c` is Laman. The proof structure
mirrors `typeI_isLaman`; the main wrinkle is that the deletion of `s(a, b)` interacts with the new
edges, but a uniform `+ 2` bound holds: either `s(a, b)` was inside `G.edgesIn ↑s'` (loses 1, gains
up to 3), or it wasn't (loses 0, but then one of `a, b` is outside `s'` so gains at most 2). -/
theorem typeII_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {a b c : V}
    (hca : c ≠ a) (hcb : c ≠ b) (hG_ab : G.Adj a b) :
    (typeII G a b c).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · -- Sparsity. `s' := s.eraseNone` is the some-preimage; `T'` is the fresh edges in `↑s`.
    set s' : Finset V := s.eraseNone
    set T' : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
        ((↑s : Set (Option V)).sym2) with hT'_def
    have h_ncard : ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard + T'.ncard :=
      typeII_edgesIn_ncard_decomp G a b c s
    have hT'_le_3 : T'.ncard ≤ 3 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_triple_le _ _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s.card = s'.card + 1`.
      have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      -- Sub-case on `s'.card`.
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · omega -- vacuous: precondition fails
      · -- s'.card = 1: `s' = {w}`. Singleton means no `G`-edges; `T' ⊆ {s(none, some w)}`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard = 0 := by
          rw [hw]; simp
        have hT'_sub : T' ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT'_le_1 : T'.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT'_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: case-split on whether `s(a, b) ∈ G.edgesIn ↑s'`.
        have hG := h.isSparse s' (by omega)
        by_cases h_ab_in : s(a, b) ∈ G.edgesIn (↑s' : Set V)
        · -- `s(a, b) ∈ G.edgesIn ↑s'`: deletion removes one, `T'.ncard ≤ 3` works.
          have hdiff := Set.ncard_sdiff_singleton_of_mem h_ab_in (s := G.edgesIn (↑s' : Set V))
          have hG_ne_zero : (G.edgesIn (↑s' : Set V)).ncard ≠ 0 :=
            Set.ncard_ne_zero_of_mem h_ab_in
          omega
        · -- `s(a, b) ∉ G.edgesIn ↑s'`: deletion is a no-op, but `a ∉ s'` or `b ∉ s'`, so the
          -- corresponding new edge `s(none, some a)` or `s(none, some b)` is also missing.
          -- Hence `T'.ncard ≤ 2`.
          have hdiff : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard =
              (G.edgesIn (↑s' : Set V)).ncard := by
            rw [Set.sdiff_singleton_eq_self h_ab_in]
          -- Since `s(a, b) ∈ G.edgeSet` (from `hG_ab`) but not in `G.edgesIn ↑s'`,
          -- it must fail the subset condition: `a ∉ s'` or `b ∉ s'`.
          have h_or : a ∉ s' ∨ b ∉ s' := by
            by_contra h_both
            push Not at h_both
            exact h_ab_in (G.mk_mem_edgesIn hG_ab h_both.1 h_both.2)
          -- Then T'.ncard ≤ 2: whichever of `a, b` is not in `s'` contributes no edge to `T'`.
          -- For the `b ∉ s'` arm, reorder T' as `{s(none, some b), s(none, some a), …} ∩ s.sym2`
          -- (the underlying `Set` is unchanged) so the helper applies with `x = b`.
          have hT'_le_2 : T'.ncard ≤ 2 := by
            rcases h_or with ha | hb
            · exact fresh_sym2_triple_inter_ncard_le_two ha
            · rw [hT'_def, Set.insert_comm s(none, some a) s(none, some b)]
              exact fresh_sym2_triple_inter_ncard_le_two hb
          omega
    · -- Case `none ∉ s`. Then `T'.ncard = 0` and `s.card = s'.card`.
      have hsc : s.card = s'.card := (Finset.card_eraseNone_of_notMem hnone).symm
      have hT'_empty : T'.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      have hdiff_le : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard ≤
          (G.edgesIn (↑s' : Set V)).ncard :=
        Set.ncard_sdiff_singleton_le _ _
      omega
  · -- Tightness.
    have hab : a ≠ b := hG_ab.ne
    have hab_in : s(a, b) ∈ G.edgeSet := hG_ab
    grind only [!typeII_edgeSet_ncard, !Finite.card_option,
      !Set.ncard_sdiff_singleton_of_mem, h.edgeSet_ncard]

end Henneberg

end SimpleGraph

-- The iso constructors (`isoTypeIOfTwoNeighbors`, `isoTypeIIOfThreeNeighbors`), the Laman
-- reverse decomposition (`IsLaman.exists_typeI_or_typeII_reverse`) and the example of `K₄`
-- minus an edge are in `HennebergReverse.lean`.


end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0006/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityLaman_HennebergReverse.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/HennebergReverse.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Henneberg moves — reverse decomposition and worked example

The *reverse* half of the Henneberg moves of `Henneberg.lean`: the iso constructors that
bridge flat-form reverse decompositions to operation-form forward-preservation theorems, the
flat-form Henneberg reverse decomposition for Laman graphs
(`IsLaman.exists_typeI_or_typeII_reverse`), and the K₄-minus-one-edge worked example.
`HennebergRigidity.lean` imports `Henneberg.lean` alone; `LamanTheorem.lean` and
`MatroidIdentification.lean`, which use its iso constructors, import this file.

## Main definitions / theorems

* `SimpleGraph.Henneberg.isoTypeIOfTwoNeighbors`,
  `SimpleGraph.Henneberg.isoTypeIIOfThreeNeighbors` — canonical iso
  constructors from neighbourhood data at a chosen vertex.
* `SimpleGraph.Henneberg.IsLaman.exists_typeI_or_typeII_reverse` — every
  Laman graph on `n ≥ 3` vertices admits a Henneberg reverse.
* `SimpleGraph.top_fin_four_minus_edge_isLaman` — `K₄ \ {s(2, 3)}` is Laman.

The blueprint's `sec:henneberg` presents this file, in its reverse decomposition
(`sec:henneberg-decomp`) and its closing example.
-/

public section

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-! ### Decomposition iso constructors

`isoTypeIOfTwoNeighbors` and `isoTypeIIOfThreeNeighbors` package, given neighborhood
data at a chosen vertex `v`, the canonical iso `G ≃g typeI G' a b` (resp.
`G ≃g typeII G' a b c`) along the equivalence `(Equiv.optionSubtypeNe v).symm`. They are the
bridge between flat-form reverse decomposition theorems (which describe the smaller graph
`G'` directly via `G.comap Subtype.val` and `fromEdgeSet`) and operation-form forward-
preservation theorems, which operate on `typeI G' a b` / `typeII G' a b c`: the rigidity steps
`typeI_isGenericallyRigidInj_two` / `typeII_isGenericallyRigidInj_two` of `LamanTheorem.lean`'s
induction, and the row-independence lifts of `MatroidIdentification.lean`'s. The forward =
operation / reverse = flat split is documented in `DESIGN.md` *Statement-form conventions*. -/

/-- Build a graph iso `G ≃g H` along the canonical `V ≃ Option {w : V // w ≠ v}` equivalence,
given the adjacency-equivalence at the `(u, w)` cases w.r.t. `v`. The `(none, none)` case needs
nothing, as neither graph has a loop; the `(none, some)` and `(some, none)` cases are related by
adjacency-symmetry, so only one of them is asked for. The `(some, some)` case carries any
move-specific bridging-edge logic. -/
def isoOfOptionSubtypeNe [DecidableEq V] {G : SimpleGraph V} (v : V)
    {H : SimpleGraph (Option {w : V // w ≠ v})}
    (hns : ∀ w (hw : w ≠ v), H.Adj none (some ⟨w, hw⟩) ↔ G.Adj v w)
    (hss : ∀ {u w} (hu : u ≠ v) (hw : w ≠ v),
        H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔ G.Adj u w) :
    G ≃g H where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      -- `simp` closes it: neither graph has a loop (`SimpleGraph.irrefl`).
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hns w hw
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        H.adj_comm, G.adj_comm]
      exact hns u hu
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hss hu hw

/-- Iso from `G` to a Type I move applied to its induced subgraph on `{w // w ≠ v}`, when the
neighbors of `v` are exactly `a` and `b`: the membership-style hypothesis `hN` says
`N(v) = {a, b}`. The statement does not ask `a ≠ b`; at `a = b` the vertex `v` has degree 1,
the case `MatroidIdentification.lean`'s induction applies it to. -/
def isoTypeIOfTwoNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun _ _ => Iff.rfl)

/-- Iso from `G` to a Type II move applied to (induced subgraph + bridging edge `s(a, b)`), when
the neighbors of `v` are exactly `a`, `b` and `c` (`hN`) and `a, b` are non-adjacent in `G`. The
statement asks neither `a ≠ b` nor that `c` differ from `a` and `b`; `v` has degree 3 when the
three are distinct. -/
def isoTypeIIOfThreeNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c) (hnab : ¬ G.Adj a b) :
    G ≃g typeII (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set (Sym2 _)))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun {u w} _ _ => by
      rw [typeII_adj_some_some, sup_adj, comap_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
      -- Forward: contradiction from the deletion clause. Backward: lift the subtype-level Sym2
      -- equality through `Subtype.val` to `s(u, w) = s(a, b)`, then case-split to hit `¬G.Adj a b`.
      refine ⟨fun h => h.1.elim id (fun ⟨hL, _⟩ => absurd hL h.2),
        fun hadj => ⟨Or.inl hadj, fun heq => ?_⟩⟩
      have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> grind [G.adj_symm])

/-! ### Flat-form Henneberg reverse decomposition for Laman graphs

Every Laman graph on `n ≥ 3` vertices admits a Henneberg reverse to another Laman graph on
one fewer vertex. Thin shell over `IsSparse.exists_typeI_or_typeII_reverse`: it applies the
sparse flat-form decomposition to `h.isSparse` and discards its pendant branch
(`G.degree v = 1`) by `IsLaman.two_le_degree`. In the Type I branch `G'` is Laman by
`typeI_isLaman_iff` along the typeI iso; in the Type II branch the sparse decomposition's
`G'.IsSparse 2 3` and the edge count from the typeII iso, `typeII_edgeSet_ncard` and the bridge
edge make `G'` Laman.

`LamanTheorem.lean`'s induction rebuilds the iso to `typeI G' a b` / `typeII G' a b c` at the
call site, by `isoTypeIOfTwoNeighbors` / `isoTypeIIOfThreeNeighbors`, before applying the
operation-form steps `typeI_isGenericallyRigidInj_two` / `typeII_isGenericallyRigidInj_two` and
transporting along the iso. -/

/-- **Laman reverse decomposition (flat form).** Every Laman graph `G` on `n ≥ 3`
vertices admits a Henneberg reverse to another Laman graph on the subtype `{w // w ≠ v}`:
either some vertex `v` has degree exactly 2 with two distinct neighbors `a, b` such that the
induced subgraph `G.comap Subtype.val` is Laman (Type I reverse), or some vertex `v` has
degree exactly 3 with three distinct neighbors `x, y, c` and a non-adjacent pair `(x, y)` such
that the induced subgraph augmented with the bridging edge `s(x, y)` is Laman (Type II reverse).

The Laman analogue of `IsSparse.exists_typeI_or_typeII_reverse`. Proof: apply the sparse
3-way version to `h.isSparse` (`G.edgeSet` is nonempty since Laman tight gives
`|E| = 2|V| - 3 ≥ 3` under `|V| ≥ 3`). The pendant branch (`deg v = 1`) is impossible since
`IsLaman.two_le_degree` forces `2 ≤ deg v`; dispatch via `absurd`. The Type I branch
(`deg v = 2`) feeds directly into `typeI_isLaman_iff` after iso transport. In the Type II
branch, the typeII iso transports `G`'s Laman to `(typeII G' x y c).IsLaman`, and
`typeII_edgeSet_ncard` plus the bridge-edge presence pins down `G'`'s tight edge count. -/
theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v : V,
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsLaman) := by
  classical
  -- `G` has at least one edge: Laman tightness + `|V| ≥ 3` gives `|E| = 2|V| - 3 ≥ 3 ≥ 1`.
  have hE : G.edgeSet.Nonempty := by
    have h_eq := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at h_eq
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hbranch⟩ := h.isSparse.exists_typeI_or_typeII_reverse hE
  refine ⟨v, ?_⟩
  rcases hbranch with
    ⟨hdeg1, _, _, _⟩ |
    ⟨hdeg2, a, b, hab, hN_iff, hG'sparse⟩ |
    ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, hG'sparse⟩
  · -- Pendant branch: impossible since `IsLaman.two_le_degree` forces `2 ≤ deg v`.
    exact absurd hdeg1 (by have := h.two_le_degree hV v; omega)
  · -- Type I branch. Extract the two neighbours from `hN_iff` and
    -- bump `G'.IsSparse` to `G'.IsLaman` via `typeI_isLaman_iff` and the typeI iso.
    have ha_adj : G.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
    have hG'_laman : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman :=
      (typeI_isLaman_iff hab).mp
        (IsLaman.iso (isoTypeIOfTwoNeighbors (G.ne_of_adj ha_adj) (G.ne_of_adj hb_adj)
          hN_iff) h)
    exact Or.inl ⟨hdeg2, a, b, hab, hN_iff, hG'_laman⟩
  · -- Type II branch. Build the typeII iso, transport `G.IsLaman` to `(typeII G' x y c).IsLaman`,
    -- and reconstruct `G'`'s tight edge count from `typeII_edgeSet_ncard` plus the bridge.
    refine Or.inr ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, ?_⟩
    set G' : SimpleGraph {w : V // w ≠ v} :=
      G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _) with hG'_def
    have h_iso : G ≃g typeII G' x y c :=
      isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm hN hnxy
    have h_typeII_laman : (typeII G' x y c).IsLaman := IsLaman.iso h_iso h
    have h_count := h_typeII_laman.edgeSet_ncard
    rw [typeII_edgeSet_ncard G' hxy hcx hcy, Finite.card_option] at h_count
    have hbridge : s(x, y) ∈ G'.edgeSet := by
      change G'.Adj x y
      rw [hG'_def, sup_adj]
      exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
    have h_diff : (G'.edgeSet \ {s(x, y)}).ncard + 1 = G'.edgeSet.ncard :=
      Set.ncard_sdiff_singleton_add_one hbridge (Set.toFinite _)
    exact ⟨hG'sparse, by omega⟩

end Henneberg

/-! ### K₄ minus one edge is Laman

A worked example: `(⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}` is Laman. The proof
applies `typeI_isLaman` twice from `top_fin_two_isLaman` to get a Laman graph on
`Option (Option (Fin 2))`, then transports it to `Fin 4` via `IsLaman.iso`. -/

private def Henneberg.fin4equiv : Option (Option (Fin 2)) ≃ Fin 4 where
  toFun
    | none => 3
    | some none => 2
    | some (some 0) => 0
    | some (some 1) => 1
  invFun
    | 0 => some (some 0)
    | 1 => some (some 1)
    | 2 => some none
    | 3 => none
  left_inv := by decide
  right_inv := by decide

/-- Graph isomorphism from the iterated Type I extension of `K₂` to `K₄ \ {s(2, 3)}`. -/
private def Henneberg.fin4iso :
    (Henneberg.typeI (Henneberg.typeI (⊤ : SimpleGraph (Fin 2)) 0 1) (some 0) (some 1))
      ≃g ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}) where
  toEquiv := Henneberg.fin4equiv
  map_rel_iff' := by
    rintro (_ | _ | a) (_ | _ | b) <;> first
      | decide
      | (fin_cases a <;> decide)
      | (fin_cases b <;> decide)
      | (fin_cases a <;> fin_cases b <;> decide)

/-- The complete graph on four vertices minus one edge is Laman. The witness construction is
two iterated Type I Henneberg moves applied to `K₂`. -/
theorem top_fin_four_minus_edge_isLaman :
    ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}).IsLaman :=
  IsLaman.iso Henneberg.fin4iso <|
    Henneberg.typeI_isLaman
      (Henneberg.typeI_isLaman top_fin_two_isLaman (by decide))
      (by decide)

end SimpleGraph


end
end BundleSource0007

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0007/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0007.json"

section BundleSource0008
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_AffineSpace_AffineSubspace_Cover.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Cover.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/





/-!
# Upstream candidate: affine version of `Subspace.biUnion_ne_univ_of_top_notMem`

Mathlib's `Mathlib.GroupTheory.CosetCover` proves that a vector space over an infinite
division ring cannot be covered by finitely many proper linear subspaces
(`Subspace.biUnion_ne_univ_of_top_notMem`). The same statement holds for proper *affine*
subspaces, with essentially the same proof: each non-empty affine subspace is a coset
of its direction submodule, so an affine cover lifts to an additive-coset cover, and the
general `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` finishes via the usual
finite-quotient / infinite-base contradiction.

The affine version subsumes the "finite union of points plus proper linear subspaces"
shape that arises in generic-position arguments, since each point is a 0-dim affine
subspace.

Upstream target: a new file `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Cover.lean`
(parallel to `Mathlib/GroupTheory/CosetCover.lean` but in the affine-space hierarchy,
importing `GroupTheory.CosetCover` for the underlying `AddSubgroup` machinery and
`AffineSubspace.Basic` and `AffineSpace.FiniteDimensional` for the affine API).

## Main results

* `AffineSubspace.biUnion_ne_univ_of_top_notMem` — a vector space over an infinite
  division ring is not a finite union of proper affine subspaces.
* `AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank` — a finite set in a
  vector space whose cardinality is at most `finrank` has an affine span that is
  not the whole space. Natural upstream home is
  `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean` (alongside
  `finrank_vectorSpan_image_finset_le`).
-/

@[expose] public section

open scoped Pointwise

namespace AffineSubspace

variable {k V : Type*} [DivisionRing k] [Infinite k]
    [AddCommGroup V] [Module k V]
    {s : Finset (AffineSubspace k V)}

/-- A vector space over an infinite division ring cannot be a finite union of proper
affine subspaces. -/
theorem biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) :
    ⋃ p ∈ s, (p : Set V) ≠ Set.univ := by
  intro hcovers
  classical
  -- Drop empty affine subspaces from the cover; they contribute nothing.
  set s' : Finset (AffineSubspace k V) :=
    s.filter (fun p : AffineSubspace k V => (p : Set V).Nonempty) with hs'_def
  have hs'_sub : s' ⊆ s := Finset.filter_subset _ _
  have h_top_notmem' : ⊤ ∉ s' := fun h => hs (hs'_sub h)
  have hs'_cov : ⋃ p ∈ s', (p : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s, (p : Set V) := hcovers ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hp, ⟨x, hxp⟩⟩, hxp⟩
  -- Choose a basepoint for each non-empty subspace.
  choose b hb using fun p (hp : p ∈ s') => (Finset.mem_filter.mp hp).2
  -- Each non-empty `p ∈ s'` is the coset `b p hp +ᵥ p.direction.toAddSubgroup`.
  have hcoset : ∀ p (hp : p ∈ s'),
      (p : Set V) = b p hp +ᵥ (p.direction.toAddSubgroup : Set V) := by
    intro p hp
    ext x
    rw [Set.mem_vadd_set]
    refine ⟨fun hx => ⟨x - b p hp, ?_, by simp⟩, ?_⟩
    · have := AffineSubspace.vsub_mem_direction hx (hb p hp)
      simpa using this
    · rintro ⟨d, hd, rfl⟩
      have : d +ᵥ b p hp ∈ p :=
        AffineSubspace.vadd_mem_of_mem_direction (by simpa using hd) (hb p hp)
      simpa [add_comm] using this
  -- Re-express the cover with cosets of direction submodules, indexed by `s'.attach`.
  have h_addcov : ⋃ q ∈ s'.attach, b q.1 q.2 +ᵥ
      (q.1.direction.toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s', (p : Set V) := hs'_cov ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
    rw [hcoset p hp] at hxp
    exact hxp
  -- Apply the additive coset-cover theorem and contradict.
  obtain ⟨q, _hq_mem, _hq_fi⟩ :=
    AddSubgroup.exists_finiteIndex_of_leftCoset_cover h_addcov
  set p := q.1 with hp_def
  have hp_in_s' : p ∈ s' := q.2
  have hp_ne_top : p ≠ ⊤ := fun h => h_top_notmem' (h ▸ hp_in_s')
  have hdir_ne_top : p.direction ≠ ⊤ := by
    intro hdir
    apply hp_ne_top
    rw [← AffineSubspace.mk'_eq (hb p hp_in_s'), hdir]
    simp
  have : Finite (V ⧸ p.direction) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (V ⧸ p.direction) :=
    Submodule.Quotient.nontrivial_iff.mpr hdir_ne_top
  have : Infinite (V ⧸ p.direction) := Module.Free.infinite k (V ⧸ p.direction)
  exact not_finite (V ⧸ p.direction)

end AffineSubspace

section ProperAffineSpan

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

open Module in
/-- A finite set in a vector space whose cardinality does not exceed `finrank` has an affine
span that is not the whole space (in infinite dimension `finrank` is `0`, so the set is
empty). Generalizes "a single point spans no more than itself" and "two points span at most a
line" — useful for ruling out `affineSpan k s = ⊤` from a cardinality bound, e.g., the
proper-affine-subspaces side-condition of `AffineSubspace.biUnion_ne_univ_of_top_notMem`. -/
theorem AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
    {s : Set V} (hsf : s.Finite) (hs : s.ncard ≤ finrank k V) :
    affineSpan k s ≠ ⊤ := by
  intro h_top
  rcases s.eq_empty_or_nonempty with rfl | hs_ne
  · -- `s = ∅`: `affineSpan = ⊥ ≠ ⊤`.
    exact AffineSubspace.bot_ne_top _ _ _ ((AffineSubspace.span_empty k V V) ▸ h_top)
  · -- `s` nonempty: `finrank (vectorSpan k s) + 1 ≤ s.ncard`, but `vectorSpan = ⊤` from
    -- `h_top` would force `finrank V + 1 ≤ s.ncard ≤ finrank V`, contradiction.
    have : Fintype s := hsf.fintype
    have : Nonempty s := hs_ne.to_subtype
    have h_le : finrank k (vectorSpan k s) + 1 ≤ s.ncard := by
      have h := finrank_vectorSpan_range_add_one_le k (Subtype.val : s → V)
      rw [Subtype.range_val] at h
      rwa [Set.ncard_eq_toFinset_card s hsf, hsf.card_toFinset]
    rw [(AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top _ _ _ h_top), finrank_top] at h_le
    omega

end ProperAffineSpan


end
end BundleSource0008

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0008/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0008.json"

section BundleSource0009
/- Source: Papers/RigidityLaman_Mathlib_Topology_Separation_Hausdorff.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Topology/Separation/Hausdorff.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidates: openness of injectivity for finite-domain perturbations

Let `V` be a finite type and `α` a Hausdorff topological space. If a continuous family
`F : X → V → α` of `V`-tuples is *injective at one base point* `x₀`, then it is
*injective on a neighborhood* of `x₀`. In other words, `Injective (F ·)` is an open
property of the parameter `x` under componentwise continuity in `x`, provided the index
type is finite and the target is T2.

Mathlib already has `Set.InjOn.exists_mem_nhdsSet` (here, in
`Mathlib.Topology.Separation.Hausdorff`), but that lemma asks for `f : X → Y` injective
on a compact set `s ⊆ X` and produces a *neighborhood of `s`*. The shape needed in
continuous-deformation arguments — a one-parameter family `F : X → V → α` evaluated at
`V`-many points, injective in the second slot at the basepoint — is dual to that, and
does not seem to have a direct upstream form.

## Main results

* `Function.Injective.eventually_of_continuousAt` — the general lemma: a `Finite`-
  indexed family that is componentwise continuous at `x₀` and injective at `x₀` is
  eventually injective.
* `Function.Injective.eventually_update_of_continuousAt` — the `Function.update`
  corollary: if `p₀ : V → α` is injective and `f : X → α` is a continuous deformation
  through `f x₀ = p₀ c` of the `c`-th coordinate, then `update p₀ c (f x)` is injective
  for `x` in a neighborhood of `x₀`. This is the form Henneberg-move generic-placement
  arguments use (cf. `exists_nonCollinear_rigid_placement_dim_two`).

The Lean namespace is the upstream one (`Function.Injective`); promotion to mathlib is
a copy-paste alongside `Set.InjOn.exists_mem_nhdsSet`. See `DESIGN.md`
"Mirror directory".
-/

@[expose] public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {x₀ : X}
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {V : Type*} [Finite V]

/-- If a family `F : X → V → α` of `V`-tuples (with `V` a finite type and `α` Hausdorff)
is *componentwise continuous* at a base point `x₀` and *injective* at `x₀`, then it is
injective on a neighborhood of `x₀`.

Each pair `(u, v)` with `u ≠ v` contributes a `ContinuousAt.prodMk`-driven eventuality
that `(F x u, F x v)` stays off the diagonal (closed in `α × α` by Hausdorffness);
`Finset.eventually_all` aggregates the finitely many pair-eventualities into a single
neighborhood. -/
theorem Injective.eventually_of_continuousAt {F : X → V → α}
    (hcont : ∀ v, ContinuousAt (fun x => F x v) x₀) (hinj : Injective (F x₀)) :
    ∀ᶠ x in 𝓝 x₀, Injective (F x) := by
  have : Fintype V := Fintype.ofFinite V
  have h_each : ∀ uv ∈ (Finset.univ : Finset (V × V)),
      ∀ᶠ x in 𝓝 x₀, uv.1 ≠ uv.2 → F x uv.1 ≠ F x uv.2 := by
    rintro ⟨u, v⟩ _
    by_cases huv : u = v
    · exact .of_forall (fun _ h => absurd huv h)
    have h_ne : F x₀ u ≠ F x₀ v := fun h => huv (hinj h)
    have h_prod : ContinuousAt (fun x => (F x u, F x v)) x₀ :=
      (hcont u).prodMk (hcont v)
    have h_compl : (Set.diagonal α)ᶜ ∈ 𝓝 (F x₀ u, F x₀ v) :=
      isClosed_diagonal.isOpen_compl.mem_nhds h_ne
    filter_upwards [h_prod h_compl] with x hx _ using hx
  filter_upwards [Finset.univ.eventually_all.mpr h_each] with x hx u v heq
  by_contra h_uv
  exact hx (u, v) (Finset.mem_univ _) h_uv heq

/-- One-coordinate perturbation form of `Function.Injective.eventually_of_continuousAt`.
If `p₀ : V → α` is injective on a finite type `V` (with `α` Hausdorff) and `f : X → α`
is a continuous deformation through `f x₀ = p₀ c` of the `c`-th coordinate, then
`Function.update p₀ c (f x)` is injective for `x` in a neighborhood of `x₀`.

Used to lift "injective at the base placement" through a one-vertex `Function.update`
perturbation in Henneberg-move generic-placement arguments. -/
theorem Injective.eventually_update_of_continuousAt [DecidableEq V] {p₀ : V → α}
    (hp₀ : Injective p₀) {c : V} {f : X → α}
    (hf : ContinuousAt f x₀) (hf0 : f x₀ = p₀ c) :
    ∀ᶠ x in 𝓝 x₀, Injective (update p₀ c (f x)) := by
  have h_eq0 : update p₀ c (f x₀) = p₀ := by
    funext v
    by_cases hvc : v = c
    · subst hvc; simp [hf0]
    · simp [update_of_ne hvc]
  have hcont : ∀ v, ContinuousAt (fun x => update p₀ c (f x) v) x₀ := by
    intro v
    by_cases hvc : v = c
    · subst hvc; simpa using hf
    · simpa [update_of_ne hvc] using (continuousAt_const : ContinuousAt (fun _ : X => p₀ v) x₀)
  have hinj₀ : Injective (update p₀ c (f x₀)) := by rw [h_eq0]; exact hp₀
  exact Injective.eventually_of_continuousAt (F := fun x => update p₀ c (f x)) hcont hinj₀

end Function


end
end BundleSource0009

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0009/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0009.json"

section BundleSource0010
/- Source: Papers/RigidityLaman_HennebergRigidity.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/HennebergRigidity.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/






/-!
# Rigidity preservation under Henneberg moves (dim 2)

The Type I and Type II Henneberg moves both preserve injective generic
rigidity in dimension 2. The proofs are rank-nullity arguments on the rigidity map: a `restrict :
ker ((typeI/II _).RigidityMap p_ext) →ₗ[ℝ] ker (G.RigidityMap p)` map `x ↦ x ∘ some` is built per
move, shown to be injective via the new edges through `none`, and the kernel-dim bound transports
via `LinearMap.finrank_le_finrank_of_injective`.

The Type II move's "place `q` on the line through `p a, p b`" construction requires the
*non-collinear* hypothesis `LinearIndependent ℝ ![p b - p a, p c - p a]`; the unconditional
wrapper `typeII_isGenericallyRigidInj_two` discharges this gap by moving the placement of `c`
off the line through `p a` and `p b`, justified by openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`). Jordán (2016, Lemmas 1.2.2 and 1.2.3, p. 38) states
the two moves' rank increase in general position, citing Whiteley (1996, Lemma 11.1.1 and
Theorem 11.1.7); the Type II placement on the line is Whiteley's proof of his Theorem 11.1.7.

## Main theorems

* `SimpleGraph.Henneberg.typeI_isInfinitesimallyRigid_extend` — rank-nullity conditional core for
  Type I.
* `SimpleGraph.Henneberg.typeI_isGenericallyRigidInj_two` — unconditional Type I preservation.
* `SimpleGraph.Henneberg.typeII_isInfinitesimallyRigid_extend` — rank-nullity conditional core for
  Type II (input: `q` collinear with `(p a, p b)`; `(q - p a, q - p c)` LI).
* `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two_of_nonCollinear` — Type II preservation
  conditional on non-collinearity.
* `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two` — unconditional Type II preservation;
  composes the perturbation helper with the conditional theorem.

## Implementation notes

The moves themselves are in `Henneberg.lean`, which this file keeps free of the analysis and
linear-algebra imports needed here. The blueprint's `sec:henneberg-rigidity` presents this file.
-/

public section

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- Injectivity of an `Option`-extended placement: if `p` is injective and the new value `q`
sits outside `Set.range p`, the function `fun w : Option V => w.elim q p` is injective.

The `Option`-extension shape comes from the Henneberg moves: `none` represents the fresh vertex,
placed at `q`; `some _` keeps the old placement. The 4-way `rintro` proof recurs in every
unconditional rigidity-preservation theorem (`typeI`/`typeII_isGenericallyRigidInj_two`); this
helper factors it. -/
private lemma injective_option_elim {V α : Type*}
    {p : V → α} (hp : Function.Injective p) {q : α} (hq : q ∉ Set.range p) :
    Function.Injective (fun w : Option V => w.elim q p) := by
  rintro (_ | u) (_ | v) h
  · rfl
  · exact (hq ⟨v, h.symm⟩).elim
  · exact (hq ⟨u, h⟩).elim
  · exact congrArg some (hp h)

/-- In `EuclideanSpace ℝ (Fin 2)`, every line `Submodule.span ℝ {v}` (with `v ≠ 0`) is a proper
subspace, so admits a non-member. The off-line construction in `exists_off_line_off_finite_dim_two`
and the perturbation direction in `exists_nonCollinear_rigid_placement_dim_two` both
need this; the helper consolidates the `finrank_span_singleton` / `finrank_euclideanSpace_fin` /
`SetLike.exists_not_mem_of_ne_top` chain. -/
lemma exists_not_mem_span_singleton_dim_two
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin 2),
      w ∉ Submodule.span ℝ ({v} : Set _) := by
  refine SetLike.exists_notMem_of_ne_top _ ?_
  intro h_top
  have h1 := finrank_span_singleton (K := ℝ) hv
  rw [h_top, finrank_top] at h1
  have h2 := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)
  omega

/-- Inner-product perpendicularity transports across a shared "target". If `sx = sy` and the
displacement `xn - sx` is `⟪v, ·⟫`-perpendicular and similarly for `yn - sy`, then `xn - yn` is
too. Used in the Henneberg move-rigidity injectivity steps to recover
`⟪direction, x none - y none⟫ = 0` from the two new-edge constraints together with the on-`some`
agreement `x ∘ some = y ∘ some`. -/
private lemma inner_sub_perp_of_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v xn yn sx sy : E} (hs : sx = sy)
    (hx : ⟪v, xn - sx⟫_ℝ = 0) (hy : ⟪v, yn - sy⟫_ℝ = 0) : ⟪v, xn - yn⟫_ℝ = 0 := by
  subst hs
  simp only [show xn - yn = (xn - sx) - (yn - sx) by abel, inner_sub_right, hx, hy, sub_zero]

/-- In `EuclideanSpace ℝ (Fin 2)`, a vector `u` orthogonal to two linearly independent vectors is
zero. The size-2 LI family spans (`Fin 2`'s cardinality matches `finrank`), so the orthogonal
complement is `⊥`. -/
private lemma eq_zero_of_orthogonal_dim_two
    {v₁ v₂ u : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : ⟪v₁, u⟫_ℝ = 0) (h₂ : ⟪v₂, u⟫_ℝ = 0) : u = 0 := by
  have h_span_top : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (by simp)
  have h_ortho : Submodule.span ℝ (Set.range ![v₁, v₂]) ⟂ Submodule.span ℝ ({u} : Set _) := by
    rw [Submodule.isOrtho_span]
    rintro w ⟨i, rfl⟩ v rfl
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  rwa [h_span_top, Submodule.isOrtho_top_left, Submodule.span_singleton_eq_bot] at h_ortho

/-- **Conditional Type I rigidity preservation in dim 2.** If `p : Framework V 2` is
infinitesimally rigid for `G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex
for which the displacements `q - p a` and `q - p b` are linearly independent, then the extended
placement `fun w => w.elim q p` is infinitesimally rigid for `typeI G a b`.

The rank-nullity heart of `typeI_isGenericallyRigidInj_two`. The proof builds a linear injection
from `ker ((typeI G a b).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via the restriction
`x ↦ x ∘ some`: it lands in the right kernel because every `G`-edge lifts to a `typeI G a b`-edge
with the same rigidity-row formula, and it is injective because the two new edges through `none`
pin down `x none` completely whenever `q - p a` and `q - p b` are linearly independent. -/
theorem typeI_isInfinitesimallyRigid_extend [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b : V}
    {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p a, q - p b]) :
    (typeI G a b).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- The restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`: every `G`-edge `s(u, v)`
  -- lifts to `s(some u, some v) ∈ (typeI G a b).edgeSet` with the same rigidity-row formula.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeI G a b).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := he
      have key := congr_fun hx ⟨s(some u, some v), h_some⟩
      simp only [rigidityMap_apply, Pi.zero_apply] at key
      simpa [rigidityMap_apply, hp_ext_def] using key
  -- Kernel-to-kernel linear map: precomposition by `some`, restricted to send `ker (typeI _)`
  -- into `ker G`.
  let restrict : LinearMap.ker ((typeI G a b).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    ((LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)).comp
        (LinearMap.ker ((typeI G a b).RigidityMap p_ext)).subtype).codRestrict
      (LinearMap.ker (G.RigidityMap p)) (fun x => h_into x.1 x.2)
  -- Injectivity: any two kernel elements agreeing on `some _` agree at `none` too, because the
  -- two new edges through `none` orthogonalize `x.1 none - y.1 none` against the LI pair
  -- `(q - p a, q - p b)`, forcing the difference to vanish.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Extract the two new-edge constraints for both `x` and `y`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeI G a b).edgeSet := by simp
    have h_b_edge : s((none : Option V), some b) ∈ (typeI G a b).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxb := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some b), h_b_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyb := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some b), h_b_edge⟩
    -- Unfold `p_ext` (`none ↦ q`, `some _ ↦ p _`) inside the inner products.
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxb hya hyb
    have h_perp_a := inner_sub_perp_of_eq (h_some a) hxa hya
    have h_perp_b := inner_sub_perp_of_eq (h_some b) hxb hyb
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_b)
  -- Rank-nullity: `finrank (ker (typeI _)) ≤ finrank (ker G) ≤ 3`.
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given two distinct points `pa, pb` and a finite "to-avoid" set
`S`, there is a point `q ∉ S` with `q - pa` and `q - pb` linearly independent. The geometric
content is "off the line through `pa` and `pb`, and off `S`".

The argument routes through `AffineSubspace.biUnion_ne_univ_of_top_notMem`
(mirrored under `CombinatorialRigidity/Mathlib/.../Cover.lean`, the affine analogue of
mathlib's `Subspace.biUnion_ne_univ_of_top_notMem`): a vector space over an infinite
division ring is not covered by finitely many proper affine subspaces, applied to the
cover `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}`. The LI condition
`(q - pa, q - pb)` then follows from `q` being off the line via a single row-op on
`(q - pa, pb - pa)`.

Used by `typeI_isGenericallyRigidInj_two` with `S = Set.range p` to get a `q` outside
the image of `p`, and by `typeI_edgeSetRowIndependent_lift` (`MatroidIdentification.lean`) with
`S = ∅` (row-independence does not need an injective extended placement). -/
lemma exists_off_line_off_finite_dim_two
    (pa pb : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      LinearIndependent ℝ ![q - pa, q - pb] ∧ q ∉ S := by
  classical
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Build the cover `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}` of proper affine
  -- subspaces, and apply the affine analogue of `Subspace.biUnion_ne_univ_of_top_notMem`.
  set L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    affineSpan ℝ ({pa, pb} : Set _) with hL_def
  set s_cover : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    insert L (hS.toFinset.image (fun s => affineSpan ℝ ({s} : Set _)))
  have hno_top : ⊤ ∉ s_cover := by
    have h_fr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
    rw [Finset.mem_insert]
    rintro (h_L | h_sing)
    · -- Pair: `({pa, pb} : Set _).ncard = 2 ≤ 2 = finrank`.
      exact AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
        (Set.toFinite _) (by rw [Set.ncard_pair hab, h_fr]) h_L.symm
    · rcases Finset.mem_image.mp h_sing with ⟨s, _, hs_eq⟩
      exact AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
        (Set.toFinite _) (by rw [Set.ncard_singleton s, h_fr]; omega) hs_eq
  have h_cover := AffineSubspace.biUnion_ne_univ_of_top_notMem hno_top
  rw [Set.ne_univ_iff_exists_notMem] at h_cover
  obtain ⟨q, hq⟩ := h_cover
  rw [Set.mem_iUnion₂] at hq
  push Not at hq
  have hqL : q ∉ L := hq L (Finset.mem_insert_self _ _)
  have hqS : q ∉ S := fun h_in =>
    hq (affineSpan ℝ ({q} : Set _))
      (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨q, hS.mem_toFinset.mpr h_in, rfl⟩))
      ((AffineSubspace.mem_affineSpan_singleton _ _).mpr rfl)
  refine ⟨q, ?_, hqS⟩
  -- LI of `![q - pa, q - pb]`: from off-line, get `q - pa ∉ ℝ ∙ (pb - pa)`,
  -- then row-op via `LinearIndependent.pair_add_smul_add_smul_iff`.
  have hq_off : (q - pa) ∉ Submodule.span ℝ ({pb - pa} : Set _) := by
    intro h_in
    rw [Submodule.mem_span_singleton] at h_in
    obtain ⟨r, hr⟩ := h_in
    apply hqL
    rw [hL_def, show q = (q - pa) +ᵥ pa from by simp, vadd_left_mem_affineSpan_pair]
    exact ⟨r, hr⟩
  have hLI_qpa_d :
      LinearIndependent ℝ (![q - pa, pb - pa] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd, fun a h_eq => hq_off ?_⟩
    rw [Submodule.mem_span_singleton]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h_eq
    exact ⟨a, h_eq⟩
  have h_form :
      (![q - pa, q - pb] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ![(1 : ℝ) • (q - pa) + (0 : ℝ) • (pb - pa),
          (1 : ℝ) • (q - pa) + (-1 : ℝ) • (pb - pa)] := by
    ext i
    fin_cases i <;> simp
  rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
  exact ⟨hLI_qpa_d, by norm_num⟩

/-- **Type I preserves injective generic rigidity in dim 2.** Given an injectively generically
rigid `G` in dim 2 and `a ≠ b` in `V`, the Henneberg Type I extension `typeI G a b` is again
injectively generically rigid in dim 2. The proof picks a `q : EuclideanSpace ℝ (Fin 2)` off both
the line through `p a, p b` (via `exists_off_line_off_finite_dim_two`) and the image of `p`, then
appeals to `typeI_isInfinitesimallyRigid_extend` for rigidity of the extended placement
`fun w => w.elim q p` and to the off-image condition for its injectivity. -/
theorem typeI_isGenericallyRigidInj_two [Finite V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj⟩ := hG
  have hpab : p a ≠ p b := fun h => hab (hp_inj h)
  obtain ⟨q, hLI, hq_notmem⟩ :=
    exists_off_line_off_finite_dim_two (p a) (p b) hpab (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p, typeI_isInfinitesimallyRigid_extend hp_rig hLI,
    injective_option_elim hp_inj hq_notmem⟩

/-! ### Type II preservation of rigidity in dim 2

Whiteley's argument (his proof of the Edge `d`-Split Theorem 11.1.7, 1996; Jordán 2016, Lemma
1.2.3, cites it): place the new vertex `q` on the *line* through `p a` and `p b`. The three new
edges' constraints then split into a "deleted-edge recovery" (the constraint
`⟪p a - p b, x (some a) - x (some b)⟫ = 0` falls out of the new edges at `none ↔ some a` and
`none ↔ some b`, both lying along the common direction `p b - p a`) and an "injectivity" piece
(the new edge at `none ↔ some c`, in an independent direction, pins `x none`).

The argument requires `p a, p b, p c` to be **non-collinear** — otherwise `q - p c` also lies in
the `p b - p a` direction, the LI condition fails, and the extended placement is not
rigid (a 1-parameter family of "vertical" infinitesimal motions of `none` is unconstrained).
The conditional theorem below takes the appropriate `q` as input; the unconditional wrapper
strengthens the input rigid placement to one with non-collinear `(p a, p b, p c)` via the
perturbation helper `exists_nonCollinear_rigid_placement_dim_two`, which uses openness of
infinitesimal rigidity (`IsInfinitesimallyRigid.eventually` in `Framework.lean`). -/

/-- **Algebraic backbone of the typeII conditional cores.** Given the collinear extension
condition `q - p' a = s • (p' b - p' a)` for the typeII new vertex, the two new-edge inner
products at `none ↔ some a` and `none ↔ some b` combine linearly to recover the deleted-edge
inner product at `s(a, b)`:

  `(s − 1) · ⟪q − p' a, x none − x (some a)⟫_ℝ − s · ⟪q − p' b, x none − x (some b)⟫_ℝ
   = s(s − 1) · ⟪p' a − p' b, x (some a) − x (some b)⟫_ℝ`

valid for any motion `x : Framework (Option V) d`. This is the algebraic content shared by
`typeII_isInfinitesimallyRigid_extend` (kernel / IR side) and
`typeII_edgeSetRowIndependent_extend` (`MatroidIdentification.lean`; dual / row-LI side): in the
IR setting both new-edge inner products vanish at a kernel element, and dividing by
`s(s − 1) ≠ 0` recovers the deleted-edge G'-constraint; in the row-LI setting the equation is
the row identity
`(s−1)·rigidityRow newA − s·rigidityRow newB = s(s−1) · restrictMap.dualMap (rigidityRow eAB)`
applied at `x`, which combined with G'-row LI and `dualMap` injectivity forces the
typeII coefficients to vanish.

Proof: derive `q - p' b = (s − 1) • (p' b - p' a)` from `hcoll` by `q − p' b = (q − p' a) −
(p' b − p' a)`, factor both inner-product scalars via `real_inner_smul_left`, and finish by
`linear_combination` over the `⟪p' b − p' a, ·⟫`-linearity identity that pulls the inner
arguments together and flips the sign once. -/
lemma typeII_collinear_inner_combo {V : Type*} {d : ℕ}
    {p' : Framework V d} {q : EuclideanSpace ℝ (Fin d)} {s : ℝ} {a b : V}
    (hcoll : q - p' a = s • (p' b - p' a))
    (x : Framework (Option V) d) :
    (s - 1) * ⟪q - p' a, x none - x (some a)⟫_ℝ
        - s * ⟪q - p' b, x none - x (some b)⟫_ℝ
      = s * (s - 1) * ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have heq : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    simp only [heq, hcoll, sub_smul, one_smul]
  rw [hcoll, hcoll_b, real_inner_smul_left, real_inner_smul_left]
  have h_eq :
      ⟪p' b - p' a, x none - x (some a)⟫_ℝ - ⟪p' b - p' a, x none - x (some b)⟫_ℝ
        = ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
    simp only [← inner_sub_right,
        show (x none - x (some a)) - (x none - x (some b))
          = x (some b) - x (some a) from by abel,
        show (p' b - p' a) = -(p' a - p' b) from by abel,
        show (x (some b) - x (some a)) = -(x (some a) - x (some b)) from by abel,
        inner_neg_neg]
  linear_combination s * (s - 1) * h_eq

/-- **Conditional Type II rigidity preservation in dim 2.** If `p` is infinitesimally rigid for
`G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex satisfying
the collinearity condition `q - p a = α • (p b - p a)` with `α ≠ 0, 1` (so `q` is on the line
through `p a, p b`, distinct from both) AND the linear-independence condition
`LinearIndependent ℝ ![q - p a, q - p c]` (the new vertex's direction to `p c` is off the line),
then the extended placement `fun w => w.elim q p` is infinitesimally rigid for `typeII G a b c`.

The rank-nullity heart of `typeII_isGenericallyRigidInj_two_of_nonCollinear`. The proof builds a
linear injection from `ker ((typeII G a b c).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via
the restriction `x ↦ x ∘ some`. The new ingredient over typeI is that for the deleted edge
`s(a, b)` (no corresponding typeII edge), the kernel constraint is recovered from the two
collinear-direction new edges at `none ↔ some a` and `none ↔ some b`. The statement does not
ask `G.Adj a b`: when `ab` is not an edge of `G` there is no such constraint to recover. -/
theorem typeII_isInfinitesimallyRigid_extend [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b c : V}
    {q : EuclideanSpace ℝ (Fin 2)} {α : ℝ}
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hcoll : q - p a = α • (p b - p a))
    (hLI : LinearIndependent ℝ ![q - p a, q - p c]) :
    (typeII G a b c).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- Restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    -- Kernel constraints at the two collinear-direction new edges `none ↔ some a` and
    -- `none ↔ some b`; plug into `typeII_collinear_inner_combo` to recover the deleted-edge
    -- constraint at `s(a, b)` via `α(α - 1) ≠ 0`.
    have hxa := congr_fun hx ⟨s(none, some a), by simp⟩
    have hxb := congr_fun hx ⟨s(none, some b), by simp⟩
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxb
    have h_combo := typeII_collinear_inner_combo hcoll x
    rw [hxa, hxb] at h_combo
    simp only [mul_zero, sub_zero] at h_combo
    have h_deleted : ⟪p a - p b, x (some a) - x (some b)⟫_ℝ = 0 :=
      (mul_eq_zero.mp h_combo.symm).resolve_left
        (mul_ne_zero hα0 (sub_ne_zero.mpr hα1))
    -- Edge-membership check.
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_uv : G.Adj u v := he
      by_cases h_eq : s(u, v) = s(a, b)
      · -- Deleted edge. `RigidityMap` is built via `Sym2.lift` (`Framework.lean`), so it's
        -- already Sym2-invariant in the edge: rewriting the edge subtype `⟨s(u, v), he⟩ =
        -- ⟨s(a, b), _⟩` via `Subtype.ext h_eq` replaces what would otherwise be a two-way
        -- `Sym2.eq_iff` orientation case split in the unfolded inner-product form.
        rw [show (⟨s(u, v), he⟩ : G.edgeSet) = ⟨s(a, b), h_eq ▸ he⟩ from Subtype.ext h_eq]
        simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
        exact h_deleted
      · -- Non-deleted edge: lift to typeII edge.
        have h_typeII : s(some u, some v) ∈ (typeII G a b c).edgeSet :=
          show (typeII G a b c).Adj (some u) (some v) from ⟨h_uv, h_eq⟩
        have key := congr_fun hx ⟨s(some u, some v), h_typeII⟩
        simp only [rigidityMap_apply, Pi.zero_apply] at key
        simpa [rigidityMap_apply, Function.comp_apply, hp_ext_def] using key
  -- Kernel-to-kernel linear map: precomposition by `some`, restricted to send
  -- `ker (typeII _)` into `ker G`.
  let restrict : LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    ((LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)).comp
        (LinearMap.ker ((typeII G a b c).RigidityMap p_ext)).subtype).codRestrict
      (LinearMap.ker (G.RigidityMap p)) (fun x => h_into x.1 x.2)
  -- Injectivity: the new edges at `none ↔ some a` and `none ↔ some c` orthogonalize
  -- `x.1 none - y.1 none` against the LI pair `(q - p a, q - p c)`.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Use new-edge constraints at `none ↔ some a` and `none ↔ some c`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeII G a b c).edgeSet := by simp
    have h_c_edge : s((none : Option V), some c) ∈ (typeII G a b c).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxc := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some c), h_c_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyc := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some c), h_c_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxc hya hyc
    have h_perp_a := inner_sub_perp_of_eq (h_some a) hxa hya
    have h_perp_c := inner_sub_perp_of_eq (h_some c) hxc hyc
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_c)
  -- Rank-nullity: `finrank (ker (typeII _)) ≤ finrank (ker G) ≤ 3`.
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given distinct points `pa, pb`, a third point `pc` with
`(pa, pb, pc)` non-collinear, and a finite "to-avoid" set `S`, there is a `q := pa + α • (pb - pa)`
on the line through `pa, pb` (with `α ≠ 0, 1`) such that `q ∉ S` and
`LinearIndependent ℝ ![q - pa, q - pc]`. The geometric content is: parametrize the line through
`pa, pb` by `α`; the LI condition is automatic from `(pa, pb, pc)` non-collinearity for any
`α ≠ 0`; the off-set and `α ≠ 1` conditions are each violated by at most finitely many `α`. -/
private lemma exists_typeII_q_on_line_dim_two
    (pa pb pc : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (hLI_abc : LinearIndependent ℝ ![pb - pa, pc - pa])
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ (α : ℝ) (q : EuclideanSpace ℝ (Fin 2)),
      α ≠ 0 ∧ α ≠ 1 ∧ q - pa = α • (pb - pa) ∧
      LinearIndependent ℝ ![q - pa, q - pc] ∧ q ∉ S := by
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Parametrize the line: `f α := pa + α • (pb - pa)`.
  set f : ℝ → EuclideanSpace ℝ (Fin 2) := fun α => pa + α • (pb - pa) with hf_def
  have hf_inj : Function.Injective f := fun _ _ h =>
    smul_left_injective ℝ hd (add_left_cancel h)
  -- The "bad" `α`-set: `{0, 1} ∪ f⁻¹(S)`.
  set bad : Set ℝ := ({0, 1} : Set ℝ) ∪ (f ⁻¹' S) with hbad_def
  have hbad_fin : bad.Finite :=
    ((Set.finite_singleton _).insert _).union (hS.preimage hf_inj.injOn)
  obtain ⟨α, hα⟩ := hbad_fin.exists_notMem
  have hα0 : α ≠ 0 := fun h => hα (by simp [hbad_def, h])
  have hα1 : α ≠ 1 := fun h => hα (by simp [hbad_def, h])
  have hq_notmem : f α ∉ S := fun h_mem => hα (by simp [hbad_def, h_mem])
  refine ⟨α, f α, hα0, hα1, ?_, ?_, hq_notmem⟩
  · -- `f α - pa = α • (pb - pa)` by definition.
    simp [hf_def]
  · -- LI of `![q - pa, q - pc]`: stage as a row-op on `![pb - pa, pc - pa]`.
    have h_form :
        (![f α - pa, f α - pc] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![α • (pb - pa) + (0 : ℝ) • (pc - pa),
            α • (pb - pa) + (-1 : ℝ) • (pc - pa)] := by
      ext i
      fin_cases i <;> simp [hf_def]
      abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨hLI_abc, ?_⟩
    intro h_eq
    apply hα0
    linarith

/-- **Type II preserves injective generic rigidity in dim 2, given non-collinear neighbors.**
Given an injectively generically rigid `G` in dim 2 *witnessed by a placement* `p` *for which*
`(p a, p b, p c)` *is non-collinear*, the Type II extension `typeII G a b c` is again
injectively generically rigid in dim 2.

The non-collinearity hypothesis is essential — see the section docstring above. Removing it
requires an openness-of-rigidity argument (any rigid placement can be perturbed to a non-collinear
one while preserving rigidity); the perturbation is packaged in
`exists_nonCollinear_rigid_placement_dim_two`, which the unconditional
`typeII_isGenericallyRigidInj_two` below uses. -/
theorem typeII_isGenericallyRigidInj_two_of_nonCollinear [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp_rig : G.IsInfinitesimallyRigid p) (hp_inj : Function.Injective p)
    {a b c : V} (hLI_abc : LinearIndependent ℝ ![p b - p a, p c - p a]) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  have hpab : p a ≠ p b := fun h => hLI_abc.ne_zero 0 (by simp [h])
  obtain ⟨α, q, hα0, hα1, hcoll, hLI, hq_notmem⟩ :=
    exists_typeII_q_on_line_dim_two (p a) (p b) (p c) hpab hLI_abc (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p,
    typeII_isInfinitesimallyRigid_extend hp_rig hα0 hα1 hcoll hLI,
    injective_option_elim hp_inj hq_notmem⟩

/-- **Non-collinear placement via `Function.update`-perturbation in dim 2.** Shared core of
`exists_nonCollinear_rigid_placement_dim_two` (rigidity and injectivity) and
`exists_nonCollinear_rowIndependent_placement_dim_two` (row-independence,
`MatroidIdentification.lean`). Given a
placement `p₀` with `p₀ b - p₀ a ≠ 0`, a property `P` preserved on a neighborhood of `t = 0`
along the one-vertex perturbation `t ↦ Function.update p₀ c (p₀ c + t • w)` for a direction
`w` outside `span {p₀ b - p₀ a}`, produce a placement `p` with `P p` and the non-collinearity
`LinearIndependent ℝ ![p b - p a, p c - p a]`.

If `p₀` is itself non-collinear, return it (with `P p₀` extracted from `hP_ev` via
`Filter.Eventually.self_of_nhds` at `t = 0`). Otherwise `p₀ c - p₀ a = δ • (p₀ b - p₀ a)` for some
`δ` (via `LinearIndependent.pair_iff'` at the non-zero direction); LI of the perturbed pair for
any `t ≠ 0` follows from `pair_add_smul_add_smul_iff` against the auxiliary
`![w, p₀ b - p₀ a]` LI. A witness `t ≠ 0` in the `P`-preservation neighborhood exists because
`𝓝[≠] 0` is `NeBot` in `ℝ`.

Callers supply `hP_ev` per their preservation property: row-LI / IR pull back
`EdgeSetRowIndependent.eventually` / `IsInfinitesimallyRigid.eventually` through continuity of
the update, and IR + injectivity additionally `.and`-conjoins
`Function.Injective.eventually_update_of_continuousAt` (whose `Function.update` shape is what
forces the eventually-on-`t` rather than eventually-on-`p` form here). -/
lemma exists_nonCollinear_update_perturbation_dim_two {V : Type*} [DecidableEq V]
    {P : Framework V 2 → Prop} {p₀ : Framework V 2}
    {a b c : V} (hac : a ≠ c) (hbc : b ≠ c)
    (hd_ne_zero : p₀ b - p₀ a ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2))
    (hw_outside : w ∉ Submodule.span ℝ ({p₀ b - p₀ a} : Set _))
    (hP_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
        P (Function.update p₀ c (p₀ c + t • w))) :
    ∃ p : Framework V 2, P p ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  -- Auxiliary LI `![w, p₀ b - p₀ a]`, used to invoke `pair_add_smul_add_smul_iff`.
  have h_LI_w_d : LinearIndependent ℝ
      (![w, p₀ b - p₀ a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd_ne_zero, fun s heq => hw_outside ?_⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨s, heq⟩
  -- Name the perturbation; record its pointwise identities.
  let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
  have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w := fun _ => Function.update_self c _ p₀
  have h_p_t_ne : ∀ t (v : V), v ≠ c → p_t t v = p₀ v :=
    fun _ v hvc => Function.update_of_ne hvc _ p₀
  have h_p_t_a : ∀ t, p_t t a = p₀ a := fun t => h_p_t_ne t a hac
  have h_p_t_b : ∀ t, p_t t b = p₀ b := fun t => h_p_t_ne t b hbc
  have h_p_t_zero : p_t 0 = p₀ := by
    funext v
    by_cases hvc : v = c
    · rw [hvc, h_p_t_c]; simp
    · rw [h_p_t_ne 0 v hvc]
  -- LI branch: `p₀` already non-collinear, return it (extract `P p₀` at `t = 0`).
  by_cases hLI₀ : LinearIndependent ℝ ![p₀ b - p₀ a, p₀ c - p₀ a]
  · exact ⟨p₀, h_p_t_zero ▸ hP_ev.self_of_nhds, hLI₀⟩
  -- Collinear branch: factor `p₀ c - p₀ a = δ • (p₀ b - p₀ a)` via `pair_iff'`.
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, p₀ c - p₀ a = δ • (p₀ b - p₀ a) := by
    rw [LinearIndependent.pair_iff' hd_ne_zero] at hLI₀
    push Not at hLI₀
    exact hLI₀.imp fun _ h => h.symm
  -- LI of the perturbed pair for any `t ≠ 0`.
  have h_LI_perturbed : ∀ t : ℝ, t ≠ 0 →
      LinearIndependent ℝ ![p_t t b - p_t t a, p_t t c - p_t t a] := by
    intro t ht_ne
    have h_form :
        (![p_t t b - p_t t a, p_t t c - p_t t a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![(0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a),
            t • w + δ • (p₀ b - p₀ a)] := by
      funext i
      fin_cases i
      · change p_t t b - p_t t a = (0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a)
        simp [h_p_t_a t, h_p_t_b t]
      · change p_t t c - p_t t a = t • w + δ • (p₀ b - p₀ a)
        simp only [h_p_t_a t, h_p_t_c t,
          show (p₀ c + t • w) - p₀ a = (p₀ c - p₀ a) + t • w from by abel, hδ]
        abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨h_LI_w_d, ?_⟩
    simp [ht_ne.symm]
  -- Pick a `t ≠ 0` in the `P`-neighborhood.
  have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ), P (p_t t) ∧ t ≠ 0 := by
    filter_upwards [hP_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hP_t ht_ne
    exact ⟨hP_t, ht_ne⟩
  obtain ⟨t, hP_t, ht_ne⟩ := h_combined.exists
  exact ⟨p_t t, hP_t, h_LI_perturbed t ht_ne⟩

/-- **Openness-of-rigidity helper: produce a non-collinear rigid placement.** Given any injective
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, there is an injective rigid
placement `p` for which `(p a, p b, p c)` is non-collinear (i.e.,
`LinearIndependent ℝ ![p b - p a, p c - p a]`).

The proof: if the IH placement `p₀` already has the LI condition, use it. Otherwise, pick a
direction `w ∉ span (p₀ b - p₀ a)` and perturb `p₀ c` to `p₀ c + t • w`. By
`IsInfinitesimallyRigid.eventually` and `Function.Injective.eventually_update_of_continuousAt`,
the perturbed placement stays rigid and injective on an open neighborhood of `t = 0`; the
shared core `exists_nonCollinear_update_perturbation_dim_two` selects a `t ≠ 0` that also gives
non-collinearity.

By openness of infinitesimal rigidity it closes the collinearity gap: it lifts
`typeII_isGenericallyRigidInj_two_of_nonCollinear` to the unconditional
`typeII_isGenericallyRigidInj_two` below. -/
private lemma exists_nonCollinear_rigid_placement_dim_two [Finite V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigidInj 2) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework V 2, G.IsInfinitesimallyRigid p ∧ Function.Injective p ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  classical
  obtain ⟨p₀, hp₀_rig, hp₀_inj⟩ := h
  have hd_ne_zero : p₀ b - p₀ a ≠ 0 :=
    sub_ne_zero.mpr fun heq => hab (hp₀_inj heq.symm)
  obtain ⟨w, hw_outside⟩ := exists_not_mem_span_singleton_dim_two hd_ne_zero
  -- Continuity of the perturbation; the `t = 0` instance reduces to `p₀`.
  have h_p_t_cont : Continuous
      (fun t : ℝ => Function.update p₀ c (p₀ c + t • w)) := by fun_prop
  have h_p_t_zero : Function.update p₀ c (p₀ c + (0 : ℝ) • w) = p₀ := by
    simp
  -- Rigidity preservation along the update (pull back `IsInfinitesimallyRigid.eventually`).
  have h_rig_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      G.IsInfinitesimallyRigid (Function.update p₀ c (p₀ c + t • w)) := by
    have h_ev_p := hp₀_rig.eventually
    rw [← h_p_t_zero] at h_ev_p
    exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
  -- Injectivity preservation along the update.
  have h_inj_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      Function.Injective (Function.update p₀ c (p₀ c + t • w)) :=
    hp₀_inj.eventually_update_of_continuousAt (f := fun t => p₀ c + t • w)
      (by fun_prop) (by simp)
  obtain ⟨p, ⟨hrig, hinj⟩, hLI⟩ :=
    exists_nonCollinear_update_perturbation_dim_two
      (P := fun p => G.IsInfinitesimallyRigid p ∧ Function.Injective p)
      hac hbc hd_ne_zero w hw_outside (h_rig_ev.and h_inj_ev)
  exact ⟨p, hrig, hinj, hLI⟩

/-- **Type II preserves injective generic rigidity in dim 2 (unconditional).** Given an injectively
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, the Type II Henneberg
extension `typeII G a b c` is again injectively generically rigid in dim 2.

The proof passes the IH through `exists_nonCollinear_rigid_placement_dim_two` to obtain a placement
on which `(p a, p b, p c)` is non-collinear (the original IH placement may have a collinear
triple, in which case we move the placement of `c` in a direction off the line through `p a, p b`
to break collinearity while preserving rigidity, by openness of infinitesimal rigidity), then
invokes the conditional `typeII_isGenericallyRigidInj_two_of_nonCollinear`. -/
theorem typeII_isGenericallyRigidInj_two [Finite V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj, hLI⟩ :=
    exists_nonCollinear_rigid_placement_dim_two hG hab hac hbc
  exact typeII_isGenericallyRigidInj_two_of_nonCollinear hp_rig hp_inj hLI

end Henneberg

end SimpleGraph


end
end BundleSource0010

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0010/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0010.json"

section BundleSource0011
/- Source: Papers/RigidityLaman_SquareGraph.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/SquareGraph.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/





/-!
# The square of a graph

The **square** `G.square` of a graph `G = (V, E)` is `G` together with an edge for every pair of
vertices at distance exactly two: the graph `G² = (V, E²)` that Katoh–Tanigawa 2011 define on
p. 650, where a molecule whose atoms and bonds form `G` is modelled as a bar-joint framework on
`G²`, and also as a body-hinge framework on `G` with the hinges at each body meeting in one
point, because in `G²` a vertex and its neighbors form a complete graph (the equivalence of the
two models is Whiteley's; `sec:molecule-modelling`). This file supplies the square, the fact
that a closed neighborhood `N[v] = {v} ∪ N(v)` induces a complete subgraph of `G²`, every edge of
`G²` lying in one, and what squaring does under the deletion of the edges at a vertex of degree
at most one and under the restriction to a set containing the support. The blueprint presents
the file in `sec:molecule-modelling-defs` (`def:square-graph`, `lem:square-cliques`), with the
clique at a singleton part in `sec:jacobs-counting` and the rest in `sec:jacobs-zero-extension`.

## Main definitions

* `SimpleGraph.square G` — the square graph `G²`.
* `SimpleGraph.closedNeighborSet G v` — the closed neighborhood `N[v] = {v} ∪ N(v)`.

## Main results

* `SimpleGraph.le_square` — `G` is a subgraph of `G.square`.
* `SimpleGraph.isClique_closedNeighborSet_square` — every closed neighborhood is a clique
  of the square.
* `SimpleGraph.isClique_neighborSet_square` — the open neighborhood is also a clique
  (`lem:singleton-part-neighborhood`).
* `SimpleGraph.exists_mem_closedNeighborSet_of_square_adj` — every edge of `G.square` lies
  inside the closed neighborhood of some vertex of `G`.
* `SimpleGraph.square_deleteIncidenceSet_of_degree_le_one`,
  `SimpleGraph.neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.ncard_neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.isClique_neighborSet_square_of_degree_eq_one` (`lem:square-delete-degree-le-one`,
  `lem:square-leaf-neighborhood`): deleting the edges at a vertex of degree at most one commutes
  with squaring, and the neighborhood in `G²` of a degree-one vertex is the closed neighborhood of
  its neighbor `u` without itself, a clique of `G²` with `d_G(u)` elements.
* `SimpleGraph.square_support_subset`, `SimpleGraph.square_induce_of_support_subset`
  (`lem:square-induce-support`): the support of the square lies inside `G`'s, and squaring
  commutes with the restriction to any set containing the support.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## The square graph -/

/-- The **square** of a graph `G`: distinct vertices `u, v` are adjacent in `G.square` when
they are already adjacent in `G`, or when they share a common neighbor in `G` (i.e. are at
graph distance exactly two). `def:square-graph`; Katoh–Tanigawa 2011, p. 650. -/
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty)
  symm := ⟨fun u v => by
    rintro ⟨hne, hc | hc⟩
    · exact ⟨hne.symm, Or.inl hc.symm⟩
    · exact ⟨hne.symm, Or.inr (by rwa [commonNeighbors_symm])⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

@[simp]
theorem square_adj {u v : V} :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty) := Iff.rfl

/-- `G` is a subgraph of its own square: every original edge survives. -/
theorem le_square (G : SimpleGraph V) : G ≤ G.square := fun _ _ h => ⟨h.ne, Or.inl h⟩

/-! ## Closed neighborhoods -/

/-- The **closed neighborhood** of a vertex: itself together with its neighbors,
`N[v] = {v} ∪ N(v)`. -/
def closedNeighborSet (G : SimpleGraph V) (v : V) : Set V := insert v (G.neighborSet v)

@[simp]
theorem mem_closedNeighborSet {u v : V} :
    u ∈ G.closedNeighborSet v ↔ u = v ∨ G.Adj v u := Iff.rfl

theorem self_mem_closedNeighborSet (G : SimpleGraph V) (v : V) : v ∈ G.closedNeighborSet v :=
  Or.inl rfl

/-- Closed neighborhoods induce complete subgraphs of the square (`lem:square-cliques`): any two
distinct vertices of `N[v]` are within distance two of each other, through `v` if neither is `v`
itself. -/
theorem isClique_closedNeighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.closedNeighborSet v) := by
  intro x hx y hy hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact absurd rfl hxy
  · exact ⟨hxy, Or.inl hy⟩
  · exact ⟨hxy, Or.inl hx.symm⟩
  · exact ⟨hxy, Or.inr ⟨v, hx.symm, hy.symm⟩⟩

/-- The **open neighborhood** is also a clique of the square (`lem:singleton-part-neighborhood`,
the clique): a special case of `isClique_closedNeighborSet_square`, restricting from `N[v]` to
`N(v) ⊆ N[v]`. This is the form the counting bound uses at a singleton part. -/
theorem isClique_neighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.neighborSet v) :=
  (isClique_closedNeighborSet_square G v).subset (Set.subset_insert v _)

/-- Every edge of `G.square` lies inside the closed neighborhood of some vertex of `G`
(`lem:square-cliques`): an original edge `uv` inside `N[u]`, a distance-two edge `uv` through a
common neighbor `w` inside `N[w]`. -/
theorem exists_mem_closedNeighborSet_of_square_adj {u v : V} (h : G.square.Adj u v) :
    ∃ w, u ∈ G.closedNeighborSet w ∧ v ∈ G.closedNeighborSet w := by
  obtain ⟨-, hadj | hcn⟩ := h
  · exact ⟨u, G.self_mem_closedNeighborSet u, Or.inr hadj⟩
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact ⟨w, Or.inr hw.1.symm, Or.inr hw.2.symm⟩

/-- A closed neighborhood has cardinality one more than the vertex's degree. -/
theorem ncard_closedNeighborSet (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.closedNeighborSet v).ncard = G.degree v + 1 := by
  rw [closedNeighborSet, Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
    ncard_neighborSet_eq_degree]

/-! ## Degree-one vertices

The proof of Jacobs' conjecture (`thm:jacobs`) and the degree-one rank formulas (JJ Lemma 4.2)
both delete the edge at a degree-one vertex `v` and pass to `G' = G - E_G(v)`. The lemmas below
say what squaring does under that deletion (`sec:jacobs-zero-extension`): it commutes with it,
and in `G²` the vertex `v` has the `d_G(u)` neighbors `N_G[u] \ {v}`, `u` its neighbor, which
form a clique. -/

/-- **Deleting the edges at a vertex of degree at most one commutes with squaring**
(`lem:square-delete-degree-le-one`). A path of length two between vertices `x, y ≠ v` cannot
pass through `v`, which has at most one neighbor, so the squares agree away from `v`; and
neither side has an edge at `v`. -/
theorem square_deleteIncidenceSet_of_degree_le_one {G : SimpleGraph V} {v : V}
    [Fintype (G.neighborSet v)] (hv : G.degree v ≤ 1) :
    (G.deleteIncidenceSet v).square = G.square.deleteIncidenceSet v := by
  ext x y
  simp only [square_adj, deleteIncidenceSet_adj]
  constructor
  · rintro ⟨hxy, ⟨hadj, hxv, hyv⟩ | hcn⟩
    · exact ⟨⟨hxy, Or.inl hadj⟩, hxv, hyv⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors, deleteIncidenceSet_adj, deleteIncidenceSet_adj] at hw
      exact ⟨⟨hxy, Or.inr ⟨w, ⟨hw.1.1, hw.2.1⟩⟩⟩, hw.1.2.1, hw.2.2.1⟩
  · rintro ⟨⟨hxy, hadj | hcn⟩, hxv, hyv⟩
    · exact ⟨hxy, Or.inl ⟨hadj, hxv, hyv⟩⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors] at hw
      rcases eq_or_ne w v with rfl | hwv
      · exact absurd (eq_of_adj_of_degree_le_one hv hw.1.symm hw.2.symm) hxy
      · exact ⟨hxy, Or.inr ⟨w,
          deleteIncidenceSet_adj.mpr ⟨hw.1, hxv, hwv⟩,
            deleteIncidenceSet_adj.mpr ⟨hw.2, hyv, hwv⟩⟩⟩

/-- **The neighborhood in the square of a degree-one vertex** (`lem:square-leaf-neighborhood`).
If `v` has degree one in `G` with neighbor `u`, its neighborhood in `G.square` is the closed
neighborhood of `u` without `v`: every neighbor of `v` in `G.square` is `u` (`v`'s only edge) or
a neighbor of `u` (`u` being the only possible common neighbor). -/
theorem neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.neighborSet v = G.closedNeighborSet u \ {v} := by
  ext w
  simp only [mem_neighborSet, square_adj, Set.mem_sdiff, mem_closedNeighborSet,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hvw, hadj | hcn⟩
    · exact ⟨Or.inl (eq_of_adj_of_degree_le_one hdeg.le hu hadj).symm, hvw.symm⟩
    · obtain ⟨c, hc⟩ := hcn
      rw [mem_commonNeighbors] at hc
      obtain rfl : c = u := eq_of_adj_of_degree_le_one hdeg.le hc.1 hu
      exact ⟨Or.inr hc.2.symm, hvw.symm⟩
  · rintro ⟨rfl | hadj, hwv⟩
    · exact ⟨fun h => hwv h.symm, Or.inl hu⟩
    · exact ⟨fun h => hwv h.symm, Or.inr ⟨u, hu, hadj.symm⟩⟩

/-- **The degree in the square of a degree-one vertex** (`lem:square-leaf-neighborhood`). A
degree-one vertex `v` has `G.square`-degree the `G`-degree of its neighbor `u`: the closed
neighborhood of `u` has `d_G(u) + 1` elements, and removing `v` (which lies in it) drops exactly
one. -/
theorem ncard_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] [Fintype (G.neighborSet u)]
    (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    (G.square.neighborSet v).ncard = G.degree u := by
  classical
  rw [neighborSet_square_of_degree_eq_one hdeg hu,
    Set.ncard_sdiff_singleton_of_mem (mem_closedNeighborSet.mpr (Or.inr hu.symm)),
    ncard_closedNeighborSet]
  omega

/-- **The neighborhood in the square of a degree-one vertex is a clique**
(`lem:square-leaf-neighborhood`): it is a subset of the clique `N_G[u]`
(`isClique_closedNeighborSet_square`). -/
theorem isClique_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.IsClique (G.square.neighborSet v) := by
  rw [neighborSet_square_of_degree_eq_one hdeg hu]
  exact (isClique_closedNeighborSet_square G u).subset Set.sdiff_subset

/-! ## Restriction to a set containing the support

When no vertex has degree one, the proof of Jacobs' conjecture (`thm:jacobs`) restricts `G` to its
support, the set of its non-isolated vertices; squaring commutes with that restriction
(`lem:square-induce-support`). -/

/-- **Squaring does not grow the support** (`lem:square-induce-support`). Every edge of `G.square`
has both endpoints in `G`'s support: an edge or a common neighbor in `G` puts each endpoint in
`G.support`. -/
theorem square_support_subset (G : SimpleGraph V) : G.square.support ⊆ G.support := by
  rintro x ⟨y, -, hadj | hcn⟩
  · exact hadj.left_mem_support
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact hw.1.left_mem_support

/-- **Squaring commutes with the restriction to a set containing the support**
(`lem:square-induce-support`). If `S` contains every non-isolated vertex of `G`, the square of
the induced subgraph `G[S]` is the induced subgraph of `G.square` on `S`: a length-two path
between vertices of `S` has its middle vertex non-isolated (`square_support_subset`), hence in
`S`, so adjacency in `G.square` and in `G[S].square` agree on `S`. -/
theorem square_induce_of_support_subset {G : SimpleGraph V} {S : Set V} (hS : G.support ⊆ S) :
    (G.induce S).square = G.square.induce S := by
  ext u v
  simp only [square_adj, induce_adj]
  constructor
  · rintro ⟨hne, hadj | hcn⟩
    · exact ⟨fun h => hne (Subtype.coe_injective h), Or.inl hadj⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors, induce_adj, induce_adj] at hw
      exact ⟨fun h => hne (Subtype.coe_injective h), Or.inr ⟨w, hw⟩⟩
  · rintro ⟨hne, hadj | hcn⟩
    · exact ⟨fun h => hne (congrArg _ h), Or.inl hadj⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors] at hw
      exact ⟨fun h => hne (congrArg _ h), Or.inr ⟨⟨w, hS hw.1.right_mem_support⟩, hw⟩⟩

end SimpleGraph


end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0011/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigidityLaman_Jacobs.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Jacobs.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/




/-!
# The three-dimensional Laman condition

Jackson–Jordán 2008 (*On the rigidity of molecular graphs*, Combinatorica **28**) state a
three-dimensional counting condition on graphs (their §5) that is *not* an instance of the
`(k, ℓ)`-sparsity family `IsSparse` at `(3, 6)`: `IsSparse` quantifies over every `s` with
`6 ≤ 3 * #s`, which includes `#s = 2`, where the bound `3 * 2 - 6 = 0` fails on every graph with
an edge, while Jackson–Jordán's condition constrains only `#s ≥ 3` and holds vacuously on `K₂`
(`fmlnote:isLaman3-guard`). This file supplies the predicate `SimpleGraph.IsLaman3`, its
monotonicity and restriction to induced subgraphs, and its first consequence for squares: a graph
whose square is Laman has maximum degree at most three (Jackson–Jordán Lemma 5.2). The blueprint
presents the file in `sec:jacobs-laman3`, with the count at a vertex in `sec:jacobs-counting`
and the restriction in `sec:jacobs-zero-extension`.

## Main definitions

* `SimpleGraph.IsLaman3 G` — every `s : Finset V` with `3 ≤ s.card` spans at most
  `3 * s.card - 6` edges, phrased additively (`(G.edgesIn ↑s).ncard + 6 ≤ 3 * s.card`) to
  avoid `ℕ`-subtraction, as with `IsSparse`.

## Main results

* `SimpleGraph.IsLaman3.mono_left` — a subgraph of a Laman graph is Laman.
* `SimpleGraph.IsLaman3.ncard_edgesIn_le` — the Laman bound restated for a finite `Set V`
  rather than a `Finset V` (applied to a part `{x | f x = a}` of a tight partition in the proof
  of `thm:laman-square-count`).
* `SimpleGraph.IsLaman3.degree_le_three` — Jackson–Jordán Lemma 5.2: if `G²` is Laman,
  every vertex of `G` has degree at most three.
* `SimpleGraph.ncard_edgesIn_neighborSet_square` — the count of
  `lem:singleton-part-neighborhood`: if `G²` is Laman, then at a vertex of degree at least two
  the edges of `G²` inside `N_G(v)` number `2 * d_G(v) - 3`. It assumes no partition.
* `SimpleGraph.IsLaman3.induce` — `lem:isLaman3-induce`: the Laman condition restricts to
  induced subgraphs.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- The **three-dimensional Laman condition** (`def:isLaman3`; Jackson–Jordán 2008 §5): every subset
of at least three vertices spans at most `3|X| - 6` edges. Not an instance of `IsSparse` at
`(3, 6)`: that predicate's guard `ℓ ≤ k * #s` also admits `#s = 2`, where the bound `3 * 2 - 6 = 0`
fails on every graph with an edge, while this condition constrains only `#s ≥ 3` and holds vacuously
on `K₂`. Phrased additively to avoid `ℕ`-subtraction. -/
def IsLaman3 (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, 3 ≤ s.card → (G.edgesIn ↑s).ncard + 6 ≤ 3 * s.card

/-- **Monotonicity** (`lem:isLaman3-mono`). A subgraph of a Laman graph is Laman: the edge
counts inside any `s : Finset V` only decrease. -/
theorem IsLaman3.mono_left {H H' : SimpleGraph V} (h : H ≤ H') (hH' : H'.IsLaman3) :
    H.IsLaman3 := by
  intro s hs
  refine (Nat.add_le_add_right ?_ 6).trans (hH' s hs)
  exact Set.ncard_le_ncard (fun _ ⟨he₁, he₂⟩ ↦ ⟨edgeSet_subset_edgeSet.mpr h he₁, he₂⟩)
    (H'.edgesIn_finite s)

/-- **The Laman bound restated for a `Set V`.** If `G` is Laman and `X` is a finite set of at
least three vertices, `X` spans at most `3|X| - 6` edges of `G` (additive form, as in
`IsLaman3`). Passes from the `Finset`-quantified definition to the `Set` form of the proof of
`thm:laman-square-count`, where a part of a partition is `{x | f x = a} : Set V`. -/
theorem IsLaman3.ncard_edgesIn_le {G : SimpleGraph V} (hd : G.IsLaman3) {X : Set V}
    (hXfin : X.Finite) (h3 : 3 ≤ X.ncard) :
    (G.edgesIn X).ncard + 6 ≤ 3 * X.ncard := by
  have hcard := Set.ncard_eq_toFinset_card X hXfin
  have h := hd hXfin.toFinset (by rw [← hcard]; exact h3)
  rwa [hXfin.coe_toFinset, ← hcard] at h

/-- **Maximum degree three** (`lem:isLaman3-degree-le-three`; Jackson–Jordán Lemma 5.2). If `G²` is
Laman, every vertex of `G` has degree at most three. The closed neighborhood `N_G[v]` is a clique of
`G²` (`isClique_closedNeighborSet_square`) on `d_G(v) + 1` vertices; a clique on five (or more)
vertices already violates the Laman condition, since `C(5, 2) = 10 > 3 * 5 - 6 = 9`
(`IsClique.ncard_edgesIn`). -/
theorem IsLaman3.degree_le_three {G : SimpleGraph V} (hd : G.square.IsLaman3) (v : V)
    [Fintype (G.neighborSet v)] : G.degree v ≤ 3 := by
  classical
  by_contra hlt
  have h4 : 4 ≤ G.degree v := by omega
  set s : Finset V := insert v (G.neighborFinset v) with hs_def
  have hs_coe : (↑s : Set V) = G.closedNeighborSet v := by
    simp only [hs_def, Finset.coe_insert, coe_neighborFinset, closedNeighborSet]
  have hs_card : s.card = G.degree v + 1 := by
    rw [hs_def, Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  obtain ⟨t, hts, htc⟩ := s.exists_subset_card_eq (n := 5) (by omega)
  have hclique : G.square.IsClique (↑t : Set V) :=
    (isClique_closedNeighborSet_square G v).subset (hs_coe ▸ (Finset.coe_subset.mpr hts))
  have hcount := IsClique.ncard_edgesIn hclique
  rw [htc] at hcount
  have hLaman := hd t (by omega)
  rw [hcount, htc, show Nat.choose 5 2 = 10 from rfl] at hLaman
  omega

/-- **The edges of the square inside a neighborhood** (`lem:singleton-part-neighborhood`, the
count; JJ eq. (5)). If `G²` is Laman and `v` has degree at least two, `N_G(v)` (always a clique
of `G²`, `isClique_neighborSet_square`) has exactly `2 * d_G(v) - 3` edges of `G²` inside it
(additive form to avoid `ℕ`-subtraction). It assumes no partition: the degree bound
(`degree_le_three`) gives `d_G(v) ∈ {2, 3}`, and `C(2, 2) = 1 = 2·2 - 3`,
`C(3, 2) = 3 = 2·3 - 3`. The singleton part of `lem:singleton-part-neighborhood` is needed only
to show that every edge counted is a *special cross* edge, not for the count itself. -/
theorem ncard_edgesIn_neighborSet_square {G : SimpleGraph V} (hd : G.square.IsLaman3)
    {v : V} [Fintype (G.neighborSet v)] (hmindeg : 2 ≤ G.degree v) :
    (G.square.edgesIn (G.neighborSet v)).ncard + 3 = 2 * G.degree v := by
  classical
  have hclique_finset : G.square.IsClique (↑(G.neighborFinset v) : Set V) := by
    rw [coe_neighborFinset]; exact isClique_neighborSet_square G v
  have hcount := IsClique.ncard_edgesIn hclique_finset
  rw [coe_neighborFinset, card_neighborFinset_eq_degree] at hcount
  have hle : G.degree v ≤ 3 := hd.degree_le_three v
  obtain hd2 | hd3 : G.degree v = 2 ∨ G.degree v = 3 := by omega
  · rw [hd2] at hcount ⊢; rw [hcount]; decide
  · rw [hd3] at hcount ⊢; rw [hcount]; decide

/-- **The Laman condition restricts to induced subgraphs** (`lem:isLaman3-induce`). If `G` is
Laman and `S ⊆ V`, the induced subgraph `G[S]` is Laman: a set `t` of at least three vertices
of `S` spans in `G[S]` exactly the edges its image spans in `G`, whose count is bounded by the
Laman condition on `G`. -/
theorem IsLaman3.induce {G : SimpleGraph V} (hd : G.IsLaman3) (S : Set V) :
    (G.induce S).IsLaman3 := by
  classical
  intro t ht
  set Y : Finset V := t.map (Function.Embedding.subtype (· ∈ S)) with hY
  have hcard : Y.card = t.card := Finset.card_map _
  have hsub : Sym2.map (Subtype.val : ↥S → V) '' ((G.induce S).edgesIn (↑t : Set ↥S)) ⊆
      G.edgesIn (↑Y : Set V) := by
    rintro e ⟨e', he', rfl⟩
    obtain ⟨hadj, hsub⟩ := mem_edgesIn.mp he'
    induction e' with
    | h a b =>
      rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff] at hsub
      refine mem_edgesIn.mpr ⟨hadj, ?_⟩
      simp only [Sym2.map_mk, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hsub.1),
        Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hsub.2)⟩
  have hle : ((G.induce S).edgesIn (↑t : Set ↥S)).ncard ≤ (G.edgesIn (↑Y : Set V)).ncard :=
    calc ((G.induce S).edgesIn (↑t : Set ↥S)).ncard
        = (Sym2.map (Subtype.val : ↥S → V) '' ((G.induce S).edgesIn (↑t : Set ↥S))).ncard :=
          (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
      _ ≤ (G.edgesIn (↑Y : Set V)).ncard := Set.ncard_le_ncard hsub (G.edgesIn_finite Y)
  have hY3 : 3 ≤ Y.card := by rw [hcard]; exact ht
  have hlam := hd Y hY3
  omega

end SimpleGraph


end
end BundleSource0012

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0012/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0012.json"

section BundleSource0013
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_Dual_Basis.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/Dual/Basis.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/




/-!
# Upstream candidates: standard-basis-dual lemmas and the row space as a span

Two facts adjacent to `Module.Basis.dualBasis` and `LinearMap.dualMap` that
mathlib does not ship:

1. **`Pi.basisFun_toDual_apply`** evaluates the self-pairing
   `(Pi.basisFun R η).toDual x y` as the coordinate sum `∑ i, x i * y i` (the
   dot product). `Module.Basis.toDual_apply_left` handles a single basis
   argument; the bilinear evaluation against two arbitrary vectors of `η → R` is
   not packaged.

2. **`LinearMap.range_dualMap_eq_span_image_dualBasis`** says that the row
   space is spanned by the rows: for any basis `b` on the codomain, the range
   of `f.dualMap` is the `R`-linear span of `f.dualMap '' (range b.dualBasis)`.
   Mathlib's `LinearMap.finrank_range_dualMap_eq_finrank_range` (row rank
   equals column rank) is a statement about dimensions only; this span
   identity is missing.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Dual/Basis.lean`,
adding the `import Mathlib.LinearAlgebra.StdBasis` line. The Lean namespaces
(`Pi`, `LinearMap`) match upstream conventions.

See `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

namespace Pi

variable {R η : Type*} [CommSemiring R] [Finite η] [DecidableEq η]

variable [Fintype η]

/-- The self-pairing of the standard basis's `Basis.toDual` against two vectors
of `η → R` is the coordinate sum `∑ i, x i * y i` (the dot product `x ⬝ᵥ y`). -/
theorem basisFun_toDual_apply (x y : η → R) :
    (Pi.basisFun R η).toDual x y = ∑ i, x i * y i := by
  conv_lhs => rw [← (Pi.basisFun R η).sum_repr y, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, Module.Basis.toDual_apply_left, Pi.basisFun_repr,
    Pi.basisFun_repr, mul_comm]

end Pi

namespace LinearMap

variable {ι R M N : Type*} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Finite ι] [DecidableEq ι]

/-- **The row space is spanned by the rows.** The range of the dual map
`f.dualMap` is the `R`-linear span of the family
`fun i ↦ f.dualMap (b.dualBasis i)` for any basis `b` on the codomain. -/
theorem range_dualMap_eq_span_image_dualBasis (b : Module.Basis ι R N)
    (f : M →ₗ[R] N) :
    LinearMap.range f.dualMap =
      Submodule.span R (Set.range (f.dualMap ∘ b.dualBasis)) := by
  rw [Set.range_comp, Submodule.span_image, b.dualBasis.span_eq, Submodule.map_top]

end LinearMap


end
end BundleSource0013

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0013/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0013.json"

section BundleSource0014
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_Dual_Lemmas.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/Dual/Lemmas.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/




/-!
# Upstream candidate: surjective pullback preserves dual linear independence

`LinearIndependent.map'` plus `LinearMap.dualMap_injective_of_surjective` plus
`LinearMap.ker_eq_bot` is a three-line chain, packaged here. The combinatorial-rigidity
project meets it when it restricts a placement along an injective vertex map: the
restriction is `LinearMap.funLeft`, surjective by injectivity of the vertex map, so its
dual is injective and keeps linearly independent rows independent
(`linearIndependent_rigidityRow_lift_of_injective`, `RigidityMatroid.lean`).

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Dual/Lemmas.lean`
(or any file that imports both `Dual.Defs` and `LinearIndependent.Basic`); the
namespace (`LinearIndependent`) matches upstream conventions.

See `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

namespace LinearIndependent

variable {R M N ι : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjective linear map `f : M →ₗ[R] N` pulls a linearly independent family of
dual vectors on `N` back to a linearly independent family of dual vectors on `M`
through `f.dualMap`. -/
theorem dualMap_of_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f)
    {v : ι → Module.Dual R N} (hv : LinearIndependent R v) :
    LinearIndependent R (f.dualMap ∘ v) :=
  hv.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hf))

end LinearIndependent


end
end BundleSource0014

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0014/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0014.json"

section BundleSource0015
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_LinearIndependent_Basic.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/LinearIndependent/Basic.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/








/-!
# Upstream candidates: independent-family facts

Six facts about linearly independent families, all upstream-eligible.

`LinearIndependent.disjoint_span_range_ker` is the converse companion of mathlib's
`LinearIndependent.map`: if the composite `f ∘ v` is linearly independent, then the span of
`v` meets `ker f` trivially (`Disjoint (span R (range v)) (ker f)`). `LinearIndependent.map`
supplies the forward direction (span-disjoint-from-kernel makes `f ∘ v` independent when `v`
is); this reads the disjointness back off the composite's independence. The rigidity project's
zero-extension lift (`RigidityMatroid.lean`) uses it to discharge the span-disjointness of the
`LinearIndepOn.union` splitting the square's edge rows into the non-incident block and the star
at the new vertex — the star rows survive a test-motion detector `Ψ` whose kernel contains the
non-incident block, so `Ψ ∘ (star rows)` is independent and this lemma turns that into the
required disjointness.

`linearIndependent_sumElim_unit_iff` is the row-space criterion for appending a
single vector to a linearly independent family: over a division ring, augmenting
an independent `v` with one more vector `x` (packaged as `Sum.elim v (fun _ : Unit
=> x)`) stays independent **iff** `x` is not already in the span of `v`. It is the
`Sum.elim … (fun _ : Unit => x)` companion of mathlib's `LinearIndepOn.notMem_span_iff`
(which is phrased for `insert a s`); the `Sum.elim`-of-a-`Unit`-singleton shape is the
one the rigidity project's block-assembly functionals come in (the new block plus one
augmenting candidate row, `linearIndependent_sumElim_candidateRow_iff` in
`Molecular/RigidityMatrix/Claim612.lean`).

The proof is `linearIndependent_sum` (the iff splitting an `ι ⊕ ι'` family into the two
sub-families plus span-disjointness) specialised to `ι' = Unit`, where the second
sub-family is the singleton `{x}` and span-disjointness `Disjoint (span (range v)) (K ∙ x)`
collapses to `x ∉ span (range v)` by `Submodule.disjoint_span_singleton'`.

`linearIndependent_sum_smul_ne_zero` is the elementary fact that a finite linear
combination `∑ j, c j • v j` of a linearly independent family with at least one
nonzero coefficient `c i ≠ 0` is nonzero (the contrapositive of
`Fintype.linearIndependent_iff`: a vanishing combination forces all coefficients to
vanish, in particular `c i`).

`exists_smul_combination_eq_sub_of_mem_span_image_compl` turns a membership
`w ∈ span (v '' {j ≠ i})` into the explicit unit-normalized vanishing combination it
witnesses: over a nontrivial ring, for an independent family `v` and an index `i`, if
`w` lies in the span of the other vectors `{v j : j ≠ i}` then there is a coefficient
family `lam` with `lam i = 1` and `∑ j, lam j • v j = v i - w` — and this combination is
nonzero (the unit coefficient at `i`, via `linearIndependent_sum_smul_ne_zero`). It is
the coefficient-extraction (`Fintype.mem_span_image_iff_exists_fun` to get the `j ≠ i`
coefficients, extended by `lam i = 1`) the rigidity project's redundant-row decomposition
consumes (KT eqs. (6.24)/(6.25): the redundant row `v i` minus its expansion `w` over the
others is the candidate vector `r̂`, with the redundant index's coefficient pinned to `1`).

`LinearIndepOn.units_smul` is the `LinearIndepOn` companion of mathlib's own
`LinearIndependent.units_smul`/`units_smul_iff` (stated only for the unrestricted
`LinearIndependent`): rescaling each member of an independent-on-`s` family `v` by a
per-index unit `w i` keeps it independent on `s`. Immediate from the mathlib lemma applied
to the restricted family `s.restrict v`, since `LinearIndepOn` unfolds to exactly that. The
rigidity project uses it to transport independence along a pointwise nonzero rescaling
(`linearIndepOn_of_forall_smul`, `Molecular/Molecule/Pencil/MainComponent/GenericBase.lean`).

`LinearIndependent.pair_map` completes mathlib's `pair_iff`/`pair_symm_iff`/`pair_iff'` family
with the missing functoriality step: an injective linear map carries an independent *pair* to an
independent pair. Mathlib has the general-family form (`LinearIndependent.map'`, kernel-trivial
`f`), but only for `f ∘ v`, and there is no `f ∘ ![x, y] = ![f x, f y]` bridge in
`Data/Fin/VecNotation.lean`, so the general form cannot be used on a `![·, ·]` goal without
hand-rolling that step — which is exactly the friction this lemma removes. The rigidity
project's cut arm (`Molecular/Molecule/Pencil/Arms.lean`) uses it to push one side's
adjacent-point distinctness through the repositioning automorphism.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`
(it imports `linearIndependent_sum` there, `disjoint_span_singleton'` from `Span.Basic`,
`Fintype.linearIndependent_iff`, and `Fintype.mem_span_image_iff_exists_fun` from
`Finsupp.LinearCombination`). `LinearIndepOn.units_smul` needs only
`LinearIndependent.units_smul` itself, already in the same file.

See `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

/-- **A linear combination of an independent family with a nonzero coefficient is
nonzero.** Over a ring, for a linearly independent family `v : ι → M` indexed by a
`Fintype` and coefficients `c : ι → R` with some `c i ≠ 0`, the combination
`∑ j, c j • v j` is nonzero. (Contrapositive of `Fintype.linearIndependent_iff`: a
vanishing combination forces every coefficient — in particular `c i` — to be `0`.) -/
theorem linearIndependent_sum_smul_ne_zero {R M ι : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype ι] {v : ι → M} (hv : LinearIndependent R v) {c : ι → R} {i : ι}
    (hci : c i ≠ 0) : ∑ j, c j • v j ≠ 0 :=
  fun h => hci (Fintype.linearIndependent_iff.1 hv c h i)

/-- **The unit-normalized vanishing combination witnessed by a span-of-the-others
membership.** Over a nontrivial ring, for a linearly independent family `v : ι → M`
(indexed by a `Fintype`), an index `i`, and a vector `w` in the span of the *other*
vectors `{v j : j ≠ i}`, there is a coefficient family `lam : ι → R` with `lam i = 1`
whose combination `∑ j, lam j • v j` equals `v i - w` — and is nonzero (it carries the
unit coefficient `1` at the independent index `i`,
`linearIndependent_sum_smul_ne_zero`). The coefficients on `{j ≠ i}` come from
`Fintype.mem_span_image_iff_exists_fun` (negated), extended by `lam i = 1`. -/
theorem exists_smul_combination_eq_sub_of_mem_span_image_compl {R M ι : Type*} [Ring R]
    [Nontrivial R] [AddCommGroup M] [Module R M] [Fintype ι] {v : ι → M}
    (hv : LinearIndependent R v) {i : ι} {w : M}
    (hw : w ∈ Submodule.span R (v '' {j | j ≠ i})) :
    ∃ lam : ι → R, lam i = 1 ∧ (∑ j, lam j • v j) = v i - w ∧ (∑ j, lam j • v j) ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun R).1 hw
  set c' : ι → R := fun j => if hj : j = i then 0 else c ⟨j, hj⟩ with hc'def
  have hc'sum : ∑ j, c' j • v j = w := by
    have key : ∑ j ∈ Finset.univ.filter (· ≠ i), c' j • v j = w := by
      rw [Finset.sum_subtype (p := fun j => j ≠ i) (Finset.univ.filter (· ≠ i))
        (fun x => by simp) (fun j => c' j • v j), ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [hc'def, dite_eq_right a.2, Subtype.coe_eta]
    rw [← key]
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => ?_)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    simp [hc'def, hj]
  set lam : ι → R := fun j => if j = i then 1 else -c' j with hlamdef
  have hlam_i : lam i = 1 := by simp [hlamdef]
  refine ⟨lam, hlam_i, ?_, linearIndependent_sum_smul_ne_zero hv (hlam_i ▸ one_ne_zero)⟩
  rw [eq_sub_iff_add_eq, ← hc'sum, ← Finset.sum_add_distrib,
    show v i = ∑ j, (if j = i then (1 : R) else 0) • v j by simp [Finset.sum_ite_eq']]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← add_smul]
  by_cases hj : j = i <;> simp [hlamdef, hj, hc'def]

/-- **The span of a family meets a linear map's kernel trivially when the composite is
independent.** Over a ring, if `f ∘ v` is linearly independent then
`Disjoint (span R (range v)) (ker f)`. Converse companion of `LinearIndependent.map` (which
proves `f ∘ v` independent from `v` independent and this disjointness); here the disjointness
is read back off the composite's independence: an element of the intersection is a finite
combination `∑ cᵢ • v i` sent to `0` by `f`, so `∑ cᵢ • f (v i) = 0`, forcing every `cᵢ = 0`
by independence of `f ∘ v`, hence the element is `0`. -/
theorem LinearIndependent.disjoint_span_range_ker {R M M' ι : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {v : ι → M} {f : M →ₗ[R] M'} (h : LinearIndependent R (f ∘ v)) :
    Disjoint (Submodule.span R (Set.range v)) (LinearMap.ker f) := by
  rw [Submodule.disjoint_def]
  intro x hx hxk
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker, ← Finsupp.linearCombination_apply,
    Finsupp.apply_linearCombination] at hxk
  rw [linearIndependent_iff] at h
  rw [h c hxk]; simp

variable {K M ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- **Appending one vector to an independent family stays independent iff the vector is
fresh.** Over a division ring, for a linearly independent family `v : ι → M` and a vector
`x : M`, the augmented family `Sum.elim v (fun _ : Unit => x)` is linearly independent iff
`x ∉ Submodule.span K (Set.range v)`. -/
theorem linearIndependent_sumElim_unit_iff {v : ι → M} (hv : LinearIndependent K v) (x : M) :
    LinearIndependent K (Sum.elim v (fun _ : Unit => x)) ↔
      x ∉ Submodule.span K (Set.range v) := by
  rw [linearIndependent_sum]
  -- The `inr`-side range span is `K ∙ x`; the `inl`-side range span is `span (range v)`.
  have hspan : Submodule.span K (Set.range ((Sum.elim v fun _ : Unit => x) ∘ Sum.inr))
      = K ∙ x := by simp [Set.range_const]
  have hcomp : Submodule.span K (Set.range ((Sum.elim v fun _ : Unit => x) ∘ Sum.inl))
      = Submodule.span K (Set.range v) := by congr 1
  constructor
  · rintro ⟨_, hr, hdisj⟩
    have hx : x ≠ 0 := by simpa using hr.ne_zero (default : Unit)
    rw [hspan, hcomp] at hdisj
    exact (Submodule.disjoint_span_singleton' hx).1 hdisj
  · intro hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ Submodule.zero_mem _)
    refine ⟨by simpa using hv,
      LinearIndependent.of_subsingleton (default : Unit) (by simpa using hx0), ?_⟩
    rw [hspan, hcomp]
    exact (Submodule.disjoint_span_singleton' hx0).2 hx

/-- **An injective linear map preserves independence of a pair.** Over a ring, if
`![x, y]` is linearly independent and `f` is an injective linear map, then `![f x, f y]` is
too. The `![·, ·]` form of `LinearIndependent.map'`, which mathlib states only for `f ∘ v`
(and `Data/Fin/VecNotation.lean` carries no `f ∘ ![x, y] = ![f x, f y]` bridge); proved
directly through `LinearIndependent.pair_iff`, pulling a vanishing combination of the images
back along injectivity. -/
theorem LinearIndependent.pair_map {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] {x y : M} (h : LinearIndependent R ![x, y])
    (f : M →ₗ[R] M') (hf : Function.Injective f) :
    LinearIndependent R ![f x, f y] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  refine h s t (hf ?_)
  rw [map_add, map_smul, map_smul, map_zero]
  exact hst

/-- **A unit-rescaling congruence for `LinearIndepOn`.** Over a ring, for a family `v : ι → M`
independent on a set `s` and a per-index unit rescaling `w : ι → Rˣ`, the rescaled family `w • v`
is again independent on `s`. The `LinearIndepOn` companion of mathlib's own
`LinearIndependent.units_smul` (stated only for the unrestricted `LinearIndependent`); immediate
from that lemma applied to the restricted family `s.restrict v`, since `LinearIndepOn R v s`
unfolds to exactly `LinearIndependent R (s.restrict v)` and restriction commutes with the
pointwise `•`. -/
theorem LinearIndepOn.units_smul {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι → M} {s : Set ι} (hv : LinearIndepOn R v s) (w : ι → Rˣ) :
    LinearIndepOn R (w • v) s :=
  LinearIndependent.units_smul hv fun x : s => w x


end
end BundleSource0015

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0015/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0015.json"

section BundleSource0016
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_Matrix_Polynomial.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/Matrix/Polynomial.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidate: evaluating `det (X • A.map C + B.map C)` at a scalar.

The matrix polynomial `(X • A.map C + B.map C : Matrix n n α[X]).det ∈ α[X]`
already has its `natDegree` and its `0`- and `card`-coefficients pinned down in
`Mathlib.LinearAlgebra.Matrix.Polynomial`
(`natDegree_det_X_add_C_le`, `coeff_det_X_add_C_zero`, `coeff_det_X_add_C_card`).
The companion `eval`-at-a-scalar identity

  `eval t (det (X • A.map C + B.map C)) = (t • A + B).det`

is not in mathlib. It is the direct consequence of `RingHom.map_det` applied to
`evalRingHom t : α[X] →+* α`, plus a pointwise simplification of the entries of
`(evalRingHom t).mapMatrix (X • A.map C + B.map C)` back to `t • A + B`.

The combinatorial-rigidity project uses this to perturb a placement in dimension
`d` until every `d + 1` of its points affinely span
(`exists_affinelySpanning_of_eventually`, `RigidityMatroid.lean`, over the
coordinate field `ℝ` of that file; the lemma itself holds over any `CommRing α`):
the polynomial
`P := det (X • M₁.map C + M₀.map C) ∈ α[X]` has leading coefficient
`det M₁ ≠ 0` and per-tuple bad-`t` set `{t | P.IsRoot t}`, identified via
`eval_det_X_add_C` with `{t | det (t • M₁ + M₀) = 0}` — i.e. the difference
matrix `t • M₁ + M₀` is singular for only finitely many `t`.

Mirror path: `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`. Promotion to mathlib
is copy-paste into the upstream file, alongside the existing `coeff_*` and
`natDegree_*` siblings.
-/

@[expose] public section

namespace Polynomial

open Matrix

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

/-- Evaluating the matrix-polynomial determinant `det (X • A.map C + B.map C)`
at a scalar `t` yields the scalar determinant `det (t • A + B)`. Companion to
`Polynomial.coeff_det_X_add_C_zero` / `Polynomial.coeff_det_X_add_C_card`. -/
theorem eval_det_X_add_C (A B : Matrix n n α) (t : α) :
    eval t (det ((X : α[X]) • A.map C + B.map C)) = (t • A + B).det := by
  rw [show eval t (det ((X : α[X]) • A.map C + B.map C)) =
        evalRingHom t (det ((X : α[X]) • A.map C + B.map C)) from rfl,
      (evalRingHom t).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, coe_evalRingHom, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, eval_add, eval_mul,
    eval_X, eval_C]

end Polynomial


end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0016/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0016.json"

section BundleSource0017
/- Source: Papers/RigidityLaman_Mathlib_LinearAlgebra_Vandermonde.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/LinearAlgebra/Vandermonde.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidate: the row-0-subtracted Vandermonde minor

If `v : Fin (n + 1) → R` and we form the `n × n` matrix whose `(i, j)`-entry is
`v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)`, then its determinant equals the
full `(n + 1) × (n + 1)` Vandermonde determinant `∏_{0 ≤ i < j ≤ n} (v j - v i)`.

This is the classical row-reduction identity: in the Vandermonde matrix
`V i j = v i ^ j`, subtracting row 0 from each other row preserves the
determinant and turns column 0 into `(1, 0, …, 0)`; cofactor-expansion along
column 0 then collapses the `(n + 1) × (n + 1)` determinant to the `n × n`
minor of `power-difference` entries. The combinatorial-rigidity project uses
the identity when it perturbs a placement in dimension `d` along the moment
curve until every `d + 1` of its points affinely span
(`exists_affinelySpanning_of_eventually`, `RigidityMatroid.lean`): the perturbed
difference matrix `M(t) = M_0 + t · M_1` has `det M_1` equal to the
power-difference determinant on the perturbation parameters, so injectivity of
the parameters implies `det M_1 ≠ 0`, hence the polynomial `t ↦ det M(t)` has
finitely many roots. It also gives the affine independence of points on the
moment curve in 3-space (`affineIndependent_momentCurve3_of_injective`,
`GeneralPositionPlacement.lean`).

The lemma is upstream-eligible: pure linear algebra over a `CommRing` with no
project-specific concepts. The proof uses the polynomial-evaluation identity
`Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` already in mathlib,
plus a one-step Laplace expansion along the sparse top row.

Mirror path: `Mathlib/LinearAlgebra/Vandermonde.lean`. (Naming: the matrix is
the `(Fin.succ, Fin.succ)`-submatrix obtained after the row-0-subtraction
reduction, so `det_powerDiff_succAbove_zero` would be the wordy alternative;
`det_powerDifferences` is the project-internal call site name.)
-/

@[expose] public section

namespace Matrix

open Polynomial Finset

/-- The `n × n` matrix `M i j = v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)` has
determinant equal to the `(n + 1) × (n + 1)` Vandermonde determinant
`∏_{0 ≤ i < j ≤ n} (v j - v i)`.

Geometrically, row `i` of `M` is the difference `p i.succ - p 0` of points on the
moment curve, `p i = (v i, v i ^ 2, …, v i ^ n) ∈ Rⁿ`. -/
theorem det_powerDifferences {n : ℕ} {R : Type*} [CommRing R] (v : Fin (n + 1) → R) :
    (Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1))).det =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  -- Trivial ring: both sides are `0`.
  nontriviality R
  -- Strategy: realize `M` as the `(Fin.succ, Fin.succ)`-minor of the
  -- `(n+1) × (n+1)` evaluation matrix `A i j = (p j).eval (v i)` where
  -- `p 0 = 1` and `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))`. Then
  -- `det A = det (vandermonde v)` by
  -- `det_eval_matrixOfPolynomials_eq_det_vandermonde`, and `det A = det M`
  -- by cofactor-expansion along row 0 (only the `(0, 0)`-entry is nonzero).
  set p : Fin (n + 1) → R[X] :=
    Fin.cases 1 (fun k : Fin n => X ^ (k.val + 1) - C (v 0 ^ (k.val + 1))) with hp
  have h_p_zero : p 0 = 1 := by simp [p]
  have h_p_succ : ∀ k : Fin n, p k.succ = X ^ (k.val + 1) - C (v 0 ^ (k.val + 1)) := by
    intro k; simp [p]
  have h_deg : ∀ i, (p i).natDegree = (i : ℕ) := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero, Fin.val_zero, natDegree_one]
    · intro k
      rw [h_p_succ, natDegree_X_pow_sub_C, Fin.val_succ]
  have h_monic : ∀ i, (p i).Monic := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero]; exact monic_one
    · intro k
      rw [h_p_succ]
      exact monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  -- The (n+1) × (n+1) evaluation matrix and its identification with `vandermonde v`.
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of (fun i j : Fin (n + 1) => (p j).eval (v i)) with hA
  have h_vand : (Matrix.vandermonde v).det = A.det :=
    det_eval_matrixOfPolynomials_eq_det_vandermonde v p h_deg h_monic
  rw [det_vandermonde] at h_vand
  -- Row 0 of `A`: only the `(0, 0)`-entry is nonzero (= 1).
  have h_A_row_zero : ∀ j : Fin (n + 1), j ≠ 0 → A 0 j = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp [A, h_p_succ]
  have h_A_zero_zero : A 0 0 = 1 := by simp [A, h_p_zero]
  -- Cofactor-expand along row 0.
  have h_det_A : A.det = (A.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_row_zero A]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [h_A_zero_zero, Fin.succAbove_zero]
    · intros j _ hj
      rw [h_A_row_zero j hj]; ring
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- The submatrix `A.submatrix Fin.succ Fin.succ` is our target.
  have h_submatrix :
      A.submatrix Fin.succ Fin.succ =
        Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)) := by
    ext i j
    simp [A, h_p_succ, eval_sub, eval_pow, eval_X, eval_C]
  rw [← h_submatrix, ← h_det_A, ← h_vand]

end Matrix


end
end BundleSource0017

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0017/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0017.json"

section BundleSource0018
/- Source: Papers/RigidityLaman_TrivialMotions.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/TrivialMotions.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/





/-!
# Trivial infinitesimal motions

The space of **trivial infinitesimal motions** of a framework `p : Framework V d` is the linear
span of (i) all translations `motion v = t` for `t : EuclideanSpace ℝ (Fin d)` constant, and
(ii) all infinitesimal rotations `motion v = A (p v)` where `A` is "skew-adjoint" in the sense
`⟪x, A x⟫_ℝ = 0` for every `x : EuclideanSpace ℝ (Fin d)`. This submodule lies in the kernel of
`G.RigidityMap p` for every graph `G` (`trivialMotions_le_ker`). At an affinely-spanning
placement it has dimension `d (d + 1) / 2`, the dimension of the infinitesimal rigid motions;
the file proves the lower bound (`trivialMotions_finrank_ge_of_affinelySpanning`), the half that
the rank bound of the rigidity map needs.

All API is `d`-general. The `(⇒)` direction of Laman's theorem uses
`rigidityMap_ker_finrank_ge_of_affinelySpanning` at `d = 2` (through
`rigidityMap_finrank_range_le_of_affinelySpanning`, `RigidityMatroid.lean`), where
`d (d + 1) / 2 = 3` reduces by `rfl` on `Nat` literals, so no `d = 2` form is needed.

## Main definitions

* `SimpleGraph.translationMotion (t)` — the constant motion sending every vertex to `t`.
* `SimpleGraph.infinitesimalRotation A p` — the motion `v ↦ A (p v)`.
* `SimpleGraph.trivialMotions p` — the span of all translations and skew-adjoint rotations.

## Main results

* `SimpleGraph.translationMotion_mem_ker`, `SimpleGraph.infinitesimalRotation_mem_ker`,
  `SimpleGraph.trivialMotions_le_ker` — trivial motions lie in the rigidity-map kernel.
* `SimpleGraph.trivialMotions_finrank_ge_of_affinelySpanning` — at any affinely-spanning
  placement, the trivial-motions submodule has dimension at least `d (d + 1) / 2`.
* `SimpleGraph.rigidityMap_ker_finrank_ge_of_affinelySpanning` — corresponding kernel bound.

The blueprint's `sec:trivial-motions` presents this file.
-/

public section

open scoped InnerProductSpace

open Module

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-! ### Translations -/

/-- The constant motion translating every vertex by `t`. Every translation lies in the kernel of
`G.RigidityMap p` (`translationMotion_mem_ker`): edge-length derivatives all vanish because
`p'_u - p'_v = t - t = 0` for any edge `s(u, v)`. -/
@[expose] def translationMotion (t : EuclideanSpace ℝ (Fin d)) : Framework V d :=
  fun _ => t

@[simp]
theorem translationMotion_apply (t : EuclideanSpace ℝ (Fin d)) (v : V) :
    (translationMotion t : Framework V d) v = t := rfl

theorem translationMotion_mem_ker (G : SimpleGraph V) (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v => simp [rigidityMap_apply]

/-! ### Infinitesimal rotations -/

/-- The infinitesimal-rotation motion at placement `p` driven by a linear map `A`. For the motion
to lie in the rigidity-map kernel (cf.\ `infinitesimalRotation_mem_ker`), `A` must satisfy the
"skew-adjoint" condition `⟪x, A x⟫_ℝ = 0` for every `x`; in dimension `d` such `A`'s form a
`d (d − 1) / 2`-dimensional space (skew-symmetric matrices), recovering the textbook count
$d + d(d - 1)/2 = d(d+1)/2$ for the trivial-motions dimension. -/
@[expose] def infinitesimalRotation
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (p : Framework V d) :
    Framework V d := fun v => A (p v)

@[simp]
theorem infinitesimalRotation_apply
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (p : Framework V d) (v : V) :
    infinitesimalRotation A p v = A (p v) := rfl

theorem infinitesimalRotation_mem_ker (G : SimpleGraph V) (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v =>
    simp only [rigidityMap_apply, Pi.zero_apply, infinitesimalRotation]
    rw [← map_sub A]
    exact hA _

/-! ### The submodule of trivial motions -/

/-- The submodule of **trivial infinitesimal motions** at placement `p`: the span of all
translations together with all infinitesimal rotations by skew-adjoint linear maps.

For every graph `G` this submodule lies in the kernel of `G.RigidityMap p`
(`trivialMotions_le_ker`). At a placement that affinely spans `EuclideanSpace ℝ (Fin d)` it has
dimension at least `d (d + 1) / 2` (`trivialMotions_finrank_ge_of_affinelySpanning`), the
dimension of the Euclidean rigid motions; the matching upper bound is not proved here. -/
def trivialMotions (p : Framework V d) : Submodule ℝ (Framework V d) :=
  Submodule.span ℝ <|
    Set.range (translationMotion (V := V) : EuclideanSpace ℝ (Fin d) → Framework V d) ∪
    {m | ∃ A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ x, ⟪x, A x⟫_ℝ = 0) ∧ m = infinitesimalRotation A p}

theorem translationMotion_mem_trivialMotions (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ trivialMotions p :=
  Submodule.subset_span (Or.inl ⟨t, rfl⟩)

theorem infinitesimalRotation_mem_trivialMotions (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ trivialMotions p :=
  Submodule.subset_span (Or.inr ⟨A, hA, rfl⟩)

/-- **Trivial motions lie in the rigidity-map kernel** for any graph `G` and any placement `p`. -/
theorem trivialMotions_le_ker (G : SimpleGraph V) (p : Framework V d) :
    trivialMotions p ≤ LinearMap.ker (G.RigidityMap p) := by
  rw [trivialMotions, Submodule.span_le]
  rintro m (⟨t, rfl⟩ | ⟨A, hA, rfl⟩)
  · exact translationMotion_mem_ker G p t
  · exact infinitesimalRotation_mem_ker G p hA

/-! ### The d-general finrank lower bound at an affinely-spanning placement

This section proves `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at an affinely-spanning
placement, via an explicit family of `d` translations (the coordinate translations) and
`d (d - 1) / 2` elementary skew-symmetric rotations (one per ordered pair `(i, j)` with `j < i`).
The planar case is its instance at `d = 2`, where the bound is `3`. -/

/-- The "elementary skew-adjoint" linear map indexed by a pair `i, j : Fin d`, sending
`x ↦ x_j • e_i - x_i • e_j` (where `e_k = EuclideanSpace.single k 1`). Skew-adjoint:
`⟪x, elemSkewMap i j x⟫_ℝ = 0` (`inner_elemSkewMap_self`). For `i = j` it is the zero map; for
`i ≠ j` it corresponds to the elementary skew-symmetric matrix `E_{i, j} - E_{j, i}`. The
collection of `elemSkewMap i j` for `j < i` spans the `d (d - 1) / 2`-dim space of skew-symmetric
linear maps and supplies the rotation generators of `trivialMotions`. -/
def elemSkewMap (i j : Fin d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := x j • PiLp.single 2 i (1 : ℝ) - x i • PiLp.single 2 j (1 : ℝ)
  map_add' u v := by
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.ofLp_single, Pi.single_apply]
    split_ifs <;> ring
  map_smul' c v := by
    ext k
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.ofLp_single,
      Pi.single_apply, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem elemSkewMap_apply (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    (elemSkewMap i j x) k = (if k = i then x j else 0) - (if k = j then x i else 0) := by
  simp only [elemSkewMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.ofLp_single, Pi.single_apply]
  split_ifs <;> ring

/-- **`elemSkewMap i j` is skew-adjoint.** The inner product `⟪x, elemSkewMap i j x⟫_ℝ` vanishes
for every `x`, so `infinitesimalRotation (elemSkewMap i j) p` lies in the rigidity-map kernel
(`infinitesimalRotation_mem_ker`). -/
theorem inner_elemSkewMap_self (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, elemSkewMap i j x⟫_ℝ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · suffices h : elemSkewMap i i x = 0 by simp [h]
    ext k
    simp [elemSkewMap_apply]
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, elemSkewMap_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
    grind

/-! ### The d-general motion family and linear independence

The d-general trivial-motion family is indexed by `Fin d ⊕ Σ i : Fin d, Fin i.val`: the left half
contributes the `d` coordinate translations, and the right half contributes one elementary skew
rotation per ordered pair `(i, j)` with `j < i` (so `j : Fin i.val`). Linear independence holds
whenever the placement `p` affinely spans `EuclideanSpace ℝ (Fin d)`; the joint LI argument
combines:

1. *Translation/rotation split.* The combination at vertex `v` decomposes as `t + S(p v)` in
   `EuclideanSpace ℝ (Fin d)`, where `t = ∑ i, c.inl i • e_i` is the translation vector and
   `S = ∑ ⟨i, j⟩, c.inr ⟨i, j⟩ • elemSkewMap i j'` is the rotation linear map (`j' : Fin d` is the
   embedding of `j : Fin i.val`).
2. *Rotation kill via affine spanning.* Subtracting `t + S(p v) = 0` and `t + S(p w) = 0` gives
   `S(p v - p w) = 0`; affine spanning implies the vector span of `{p v - p w}` is `⊤`, so `S = 0`
   as a linear map (`LinearMap.eqOn_span`).
3. *Coefficient extraction.* From `S = 0`, evaluating `S` at the standard basis vectors picks out
   each rotation coefficient. With those gone, the surviving equation `t = 0` then yields the
   translation coefficients via the standard-basis coord-read. -/

/-- **Cross-term vanishing for the ordered-pair indexing.** Evaluating
`elemSkewMap s.1 ⟨s.2.val, _⟩` (the generator at ordered-pair index `s : Σ x : Fin d, Fin x.val`)
at the standard basis vector `e_{⟨j.val, _⟩}` and reading off coordinate `i` produces `1` exactly
when `s = ⟨i, j⟩` and `0` for every other index.

The strict inequalities `s.2.val < s.1.val` and `j.val < i.val` baked into the ordered-pair type
rule out the symmetric cross-term in `elemSkewMap_apply`: that term would require both
`i.val = s.2.val < s.1.val` and `s.1.val = j.val < i.val`, giving `i.val < s.1.val < i.val`. This
lemma is the substantive content of *"the other cross-terms vanish for the ordered-pair index
range"* used in `trivialMotionFamily_linearIndependent`. -/
theorem elemSkewMap_ofLp_inr_apply (i : Fin d) (j : Fin i.val)
    (s : Σ x : Fin d, Fin x.val) :
    (elemSkewMap s.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩
        (PiLp.single 2 (⟨j.val, j.isLt.trans i.isLt⟩ : Fin d) (1 : ℝ))).ofLp i
      = if s = ⟨i, j⟩ then 1 else 0 := by
  obtain ⟨a, b⟩ := s
  -- Case-split on `i = a`; `grind` then dispatches the nested `if`s plus the sigma-equality
  -- RHS using `b.isLt` / `j.isLt` to rule out the symmetric cross-term in `elemSkewMap_apply`.
  rcases eq_or_ne i a with rfl | hia <;> simp [elemSkewMap_apply] <;> grind

/-- The d-general trivial-motion family at a placement `p`. The left summand of the index type
contributes the `d` coordinate translations (one per `i : Fin d`); the right summand contributes
one elementary skew rotation per ordered pair `⟨i, j⟩` with `j : Fin i.val` (so `j.val < i.val`),
using `elemSkewMap i ⟨j.val, _⟩` for the skew generator. Each value lies in `trivialMotions p`
(`trivialMotionFamily_mem_trivialMotions`). -/
@[expose] def trivialMotionFamily (p : Framework V d) :
    (Fin d ⊕ Σ i : Fin d, Fin i.val) → Framework V d
  | .inl i => translationMotion (PiLp.single 2 i (1 : ℝ))
  | .inr ⟨i, j⟩ =>
      infinitesimalRotation (elemSkewMap i ⟨j.val, j.isLt.trans i.isLt⟩) p

@[simp] theorem trivialMotionFamily_inl (p : Framework V d) (i : Fin d) :
    trivialMotionFamily p (.inl i) = translationMotion (PiLp.single 2 i (1 : ℝ)) := rfl

@[simp] theorem trivialMotionFamily_inr (p : Framework V d) (i : Fin d) (j : Fin i.val) :
    trivialMotionFamily p (.inr ⟨i, j⟩) =
      infinitesimalRotation (elemSkewMap i ⟨j.val, j.isLt.trans i.isLt⟩) p := rfl

theorem trivialMotionFamily_mem_trivialMotions (p : Framework V d)
    (s : Fin d ⊕ Σ i : Fin d, Fin i.val) :
    trivialMotionFamily p s ∈ trivialMotions p := by
  rcases s with i | ⟨i, j⟩
  · exact translationMotion_mem_trivialMotions p _
  · exact infinitesimalRotation_mem_trivialMotions p (inner_elemSkewMap_self _ _)

/-- **Joint linear independence** of the d-general trivial-motion family at an affinely-spanning
placement. The translation/rotation split combined with affine spanning kills the rotation part,
leaving the translation part identifiable coord-by-coord. -/
theorem trivialMotionFamily_linearIndependent {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    LinearIndependent ℝ (trivialMotionFamily p) := by
  obtain ⟨_, v₀, rfl⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- The "skew sum" linear map and "translation vector" assembled from coefficients.
  set S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    ∑ s : Σ i : Fin d, Fin i.val,
      c (.inr s) • elemSkewMap s.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩ with hS_def
  set t : EuclideanSpace ℝ (Fin d) :=
    ∑ i : Fin d, c (.inl i) • PiLp.single 2 i (1 : ℝ) with ht_def
  -- Coordinate `m` of `t` is the translation coefficient `c (.inl m)`.
  have ht_coord : ∀ m : Fin d, t.ofLp m = c (.inl m) := fun m => by
    simp [ht_def, Pi.single_apply]
  -- Step 1: at every `v`, `t + S (p v) = 0`. Evaluate `hc` at `v` and split the index sum.
  have h_combine : ∀ v : V, t + S (p v) = 0 := fun v => by
    simpa [hS_def, ht_def, trivialMotionFamily, Fintype.sum_sum_type,
      LinearMap.sum_apply] using congrFun hc v
  -- Step 2: `S` vanishes on differences `p v - p w`.
  have h_S_diff : ∀ v w : V, S (p v - p w) = 0 := fun v w => by
    rw [map_sub, eq_neg_of_add_eq_zero_right (h_combine v),
      eq_neg_of_add_eq_zero_right (h_combine w), sub_self]
  -- Step 3: `S = 0` as a linear map (vanishes on the vector span of `Set.range p`).
  have : Nonempty V := ⟨v₀⟩
  have h_S_zero : S = 0 := by
    have hvspan : Submodule.span ℝ ((Set.range p) -ᵥ (Set.range p)) = ⊤ := by
      rw [← vectorSpan_def]
      exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _
        (Set.range_nonempty p)).mp hp
    refine LinearMap.ext_on hvspan ?_
    rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
    simpa [vsub_eq_sub] using h_S_diff v w
  -- Step 4: `t = 0`.
  have h_t_zero : t = 0 := by simpa [h_S_zero] using h_combine v₀
  -- Step 5: extract coefficients.
  intro s
  rcases s with i | ⟨i, j⟩
  · -- Translation coefficient: from `t = 0`, read coordinate `i`.
    simpa [ht_coord i] using congrArg (·.ofLp i) h_t_zero
  · -- Rotation coefficient: from `S = 0`, apply at `e_{j'}` and read coord `i`.
    -- The sum collapses via `elemSkewMap_ofLp_inr_apply` (cross-term vanishing) + `sum_ite_eq'`.
    have h_extract : (S (PiLp.single 2 (⟨j.val, j.isLt.trans i.isLt⟩ : Fin d) (1 : ℝ))).ofLp i
        = c (.inr ⟨i, j⟩) := by
      rw [hS_def, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [elemSkewMap_ofLp_inr_apply i j, mul_ite, mul_one, mul_zero]
      simp
    rw [h_S_zero] at h_extract
    simpa using h_extract.symm

/-- Cardinality of the d-general trivial-motion index: `d` coordinate translations plus
`d * (d - 1) / 2 = ∑_{i < d} i` skew rotations gives `d * (d + 1) / 2`. -/
theorem fintype_card_trivialMotionFamilyIndex :
    Fintype.card (Fin d ⊕ Σ i : Fin d, Fin i.val) = d * (d + 1) / 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ i : Fin d, i.val) = ∑ i ∈ Finset.range d, i from Fin.sum_univ_eq_sum_range id d]
  rw [show d + ∑ i ∈ Finset.range d, i = ∑ i ∈ Finset.range (d + 1), i by
    rw [Finset.sum_range_succ]; ring]
  rw [Finset.sum_range_id]
  rw [Nat.add_sub_cancel, Nat.mul_comm]

/-- **The d-general finrank lower bound for trivial motions at an affinely-spanning placement.**
At any placement `p : Framework V d` whose image affinely spans `EuclideanSpace ℝ (Fin d)`, the
trivial-motions submodule has dimension at least `d (d + 1) / 2` (the textbook dimension of
Euclidean rigid motions). The argument exhibits an explicit family of `d` coordinate translations
and `d (d - 1) / 2` elementary skew rotations and shows it is linearly independent. -/
theorem trivialMotions_finrank_ge_of_affinelySpanning [Finite V]
    {p : Framework V d} (hp : affineSpan ℝ (Set.range p) = ⊤) :
    d * (d + 1) / 2 ≤ Module.finrank ℝ (trivialMotions p) := by
  have : Fintype V := Fintype.ofFinite V
  -- Lift the trivial-motion family into the `trivialMotions p` submodule.
  let f : (Fin d ⊕ Σ i : Fin d, Fin i.val) → (trivialMotions p) :=
    fun s => ⟨trivialMotionFamily p s, trivialMotionFamily_mem_trivialMotions p s⟩
  have h_LI : LinearIndependent ℝ f := by
    have h_amb : LinearIndependent ℝ (trivialMotionFamily p) :=
      trivialMotionFamily_linearIndependent hp
    have h_eq : (fun s => (f s).val) = trivialMotionFamily p := by
      funext s; rfl
    rw [← h_eq] at h_amb
    exact h_amb.of_comp (trivialMotions p).subtype
  have h_card := h_LI.fintype_card_le_finrank
  rw [fintype_card_trivialMotionFamilyIndex] at h_card
  exact h_card

/-- **d-general finrank lower bound for the rigidity-map kernel at an affinely-spanning placement.**
For any graph `G`, any dimension `d`, and any placement `p` whose image affinely spans
`EuclideanSpace ℝ (Fin d)`, the kernel of `G.RigidityMap p` has dimension at least
`d (d + 1) / 2`, the dimension of the infinitesimal rigid motions (Jordán 2016, p. 36; the
generators are Whiteley's, 1996, §11.1).

Combines the d-general `trivialMotions_finrank_ge_of_affinelySpanning` with the unconditional
inclusion `trivialMotions_le_ker`. Plugs into rank-nullity to give the d-general rank upper
bound `rigidityMap_finrank_range_le_of_affinelySpanning` on `G.RigidityMap p`'s range. -/
theorem rigidityMap_ker_finrank_ge_of_affinelySpanning [Finite V]
    (G : SimpleGraph V) {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    d * (d + 1) / 2 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
  (trivialMotions_finrank_ge_of_affinelySpanning hp).trans
    (Submodule.finrank_mono (trivialMotions_le_ker G p))

end SimpleGraph


end
end BundleSource0018

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations02/block_0018/Consolidated/RigidityFoundations02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations02/checkpoint_0018.json"
