module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

public import verified.parts.part026
import all verified.parts.part026

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart381
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Subarc.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

/-- The affine map carrying `[0, 1]` onto the parameter interval between `a` and `b`,
running from `a` to `b`. -/
def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

/-- The reparametrisation is injective as soon as it is not constant. -/
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

/-- `reparam a b` carries the unit interval exactly onto `uIcc a b`. This is `segment_eq_image'`
read through the identification of a real segment with an unordered closed interval. -/
theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  change (fun θ : ℝ => a + θ * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b
  simpa only [smul_eq_mul] using h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

/-- A subinterval of the unit interval stays inside it: `uIcc` is the convex hull of its two
endpoints, and the unit interval is convex. -/
theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

/-! ### Subarcs -/

/-- The subarc of `f` between the parameters `a` and `b`: the arc traversed from `f a` to
`f b`, reparametrised so that it is again a map on `[0, 1]`. -/
def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

/-- The image of a subarc is the arc restricted to the subinterval — which is what "sub"
means, and the form every consumer wants. -/
theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem subarc_image_subset (ha : a ∈ I) (hb : b ∈ I) : subarc f a b '' I ⊆ f '' I := by
  rw [subarc_image]
  exact image_mono (uIcc_subset_I ha hb)

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

/-- Injectivity of the subarc needs injectivity of `f` only where the subarc runs. -/
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

/-- A subarc between two distinct parameters is an arc between the two values there. The
injectivity hypothesis is confined to the traversed interval, so this applies to a piece of a
Jordan curve as well as to a piece of an arc. -/
theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

theorem isArc_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : IsArc (f '' uIcc a b) :=
  (isArcBetween_subarc hc hi ha hb hab).isArc

/-- The version for an arc, whose parametrisation is injective everywhere. -/
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

/-- Any two distinct points of an arc are the endpoints of a subarc of it. The set-level
form, for the consumers that never see a parametrisation. -/
theorem IsArc.exists_isArcBetween_subset {A : Set Plane} (h : IsArc A) {p q : Plane}
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) : ∃ B ⊆ A, IsArcBetween B p q := by
  obtain ⟨f, hc, hi, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  refine ⟨f '' uIcc s t, image_mono (uIcc_subset_I hs ht), ?_⟩
  exact isArcBetween_subarc_of_injOn_I hc hi hs ht (fun h => hpq (by rw [h]))

/-! ### The arc without its endpoints -/

/-- The open arc — the blueprint's `P°`: an arc with its two endpoints removed.

Taken on the parameter side, as the image of the open unit interval, because that is the form
the subarc basis argument needs: an open subarc is the image of an open subinterval.
Injectivity then says it is also the arc minus the two endpoint *values*, which is how the
blueprint reads it (`openArc_eq_diff`). -/
def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

theorem openArc_subset : openArc f ⊆ f '' I := image_mono Ioo_subset_I

/-- On an arc the two readings of "without its endpoints" agree: dropping the endpoints of the
parameter interval drops exactly the two endpoint values, since injectivity means no other
parameter shares them. -/
theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

/-- The open arc of a subarc is the arc restricted to the *open* subinterval. -/
theorem openArc_subarc (hab : a ≠ b) : openArc (subarc f a b) = f '' uIoo a b := by
  have h : reparam a b '' Ioo 0 1 = uIoo a b := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · -- Increasing: the witness for `x` is the fraction of the way from `a` to `b`.
      rw [uIoo_of_lt hlt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(x - a) / (b - a), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.1]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.2])
    · exact absurd rfl hab
    · -- Decreasing: the same fraction, written with both signs flipped.
      rw [uIoo_of_gt hgt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(a - x) / (a - b), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.2]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.1])
  rw [openArc, show subarc f a b = f ∘ reparam a b from rfl, image_comp, h]

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- **The interior of an arc is the image of the open parameter interval.** The bridge from
`IsArcBetween`, which is about the set, to `openArc`, which is about a parametrisation. -/
theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

/-- **The interior of an arc is connected.** It is the continuous image of `Ioo 0 1`. -/
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

/-- The interior of an arc is nonempty: `Ioo 0 1` is. -/
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- The interior of an arc is connected in the nonempty sense. -/
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

/-- **An endpoint of an arc is a limit of its interior.** This is what turns "the closure of a
cell meets the curve in one arc only" into a statement about the *endpoints* of a crosscut, and
it is what says an ear's two ends lie on the boundary of the face its interior lies in. -/
theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  -- The endpoint is the limit of the interior as the parameter tends to `0`.
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

/-! ### A parametrisation is an open map onto its arc -/

/-- **The parametrisation is an open map onto its arc.** The image of a relatively open piece
of the parameter interval is relatively open in the arc.

No inverse is constructed. The complement piece `I \ U` is compact, so its image is compact,
so it is closed; and by injectivity the image of `U ∩ I` is exactly the arc minus that closed
set. Stated for a relatively open *piece* `U ∩ I` rather than for a subarc, because at an
endpoint the basic neighbourhood is half-open — `openArc` of a subarc is the interior case,
and this covers both. -/
theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · -- The discarded piece is compact, hence closed, so its complement is open.
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · -- Injectivity turns "remove the image" into "image of the removal".
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

/-- The pointwise reading of the previous theorem, and the one consumers use: around every
point of the image of a relatively open piece there is a ball meeting the arc only inside that
image. This is precisely the continuity of the inverse parametrisation. -/
theorem exists_ball_inter_subset_image (hc : ContinuousOn f I) (hi : InjOn f I)
    {U : Set ℝ} (hU : IsOpen U) {x : Plane} (hx : x ∈ f '' (U ∩ I)) :
    ∃ ε > 0, Metric.ball x ε ∩ f '' I ⊆ f '' (U ∩ I) := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi hU
  have hxV : x ∈ V := (hV ▸ hx).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen x hxV
  exact ⟨ε, hε, fun y hy => hV ▸ ⟨hball hy.1, hy.2⟩⟩

/-- The open arc is relatively open in the arc: the blueprint's `P°` is a relatively open
subarc. -/
theorem openArc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) :
    ∃ V : Set Plane, IsOpen V ∧ openArc f = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
  exact ⟨V, hVopen, by rwa [inter_eq_self_of_subset_left Ioo_subset_I] at hV⟩

/-- A subarc without its endpoints is relatively open in the arc. These are the "relatively
open subarcs" the blueprint speaks of. -/
theorem openArc_subarc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) :
    ∃ V : Set Plane, IsOpen V ∧ f '' uIoo a b = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (U := uIoo a b) isOpen_Ioo
  refine ⟨V, hVopen, ?_⟩
  rwa [inter_eq_self_of_subset_left
    (uIoo_subset_uIcc_self.trans (uIcc_subset_I ha hb))] at hV

/-! ### The subarc basis -/

/-- **Every neighbourhood of a point of the arc contains the image of an open subinterval
around its parameter.** With `image_isRelOpen`, which says those images are relatively open,
this makes them a basis of the arc's subspace topology.

The piece is the parameter interval cut by an interval around the parameter, which is
half-open exactly when the point is an endpoint. -/
theorem basic_piece_inside_ball (hc : ContinuousOn f I) {x : Plane} (hx : x ∈ f '' I)
    {r : ℝ} (hr : 0 < r) :
    ∃ c d : ℝ, x ∈ f '' (Ioo c d ∩ I) ∧ f '' (Ioo c d ∩ I) ⊆ Metric.ball x r := by
  obtain ⟨s, hs, rfl⟩ := hx
  -- Continuity at the parameter turns the prescribed radius into a parameter radius.
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc s hs) r hr
  refine ⟨s - δ, s + δ, ⟨s, ⟨⟨by linarith, by linarith⟩, hs⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht, htI⟩, rfl⟩
  have : dist t s < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact Metric.mem_ball.mpr (hclose htI this)

end Schoenflies

end BundlePart381

section BundlePart382
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/VertexSquares.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The vertex squares, the last parameter inside a closed set, and the cores

Three of the ordinary bricks of the polygonal redrawing of a finite plane graph.

**The vertex squares.** Around each vertex of a finite plane graph sits a closed axis-parallel
square which meets no other vertex and no edge arc of an edge not incident with that vertex.
One compact separation per other vertex and per non-incident arc, then the single-`ε`-for-all
lemma of `Schoenflies/UniformBound.lean`. Squares rather than disks because the assembly needs
the boundary to be made of segments; convexity, which the radial segments of the last step
want, both shapes have.

Because the choice is made once for all vertices rather than vertex by vertex, halving the
common radius also makes *distinct squares disjoint* — which the cores of the next brick need
and which the per-vertex statement does not give. That is why `exists_vertexSquares` is the
form to consume and `exists_square_at` only its ingredient.

**The last parameter inside a closed set.** The parameters at which an arc lies in a closed
set form a compact subset of the parameter interval; if it is nonempty its supremum is
attained, and past that supremum the arc has left the set for good. The mirror statement about
the infimum is what the far end of an edge wants: the arc leaves the square at `v` for the last
time and enters the square at `w` for the first time.

**The cores.** The subarc of an edge between those two parameters. It meets the square at `v`
in its own first endpoint only, the square at `w` in its own last endpoint only, and — the
clause the assembly really uses — it contains no vertex, which makes distinct cores disjoint
without any further estimate.

## Blueprint

Bricks B2, B3 and B4 of `lem:polygonal-redrawing`.

* `Plane.closedBall_subset_closedSquare`, `Plane.closedSquare_subset_ball` — a square sits
  inside a ball and vice versa, the comparison every separation argument passes through.
* `Plane.supDist_triangle`, `Plane.closedSquare_mono_center`, `Plane.mem_closedSquare_self` —
  square arithmetic missing from `Schoenflies/Square.lean`.
* `exists_last_mem_Icc`, `exists_first_mem_Icc`, `exists_last_mem`, `exists_first_mem` — B3,
  with `isCompact_parameters_mem` behind them.
* `Graph.IsDrawing.exists_square_at` — B2 at one vertex.
* `Graph.IsDrawing.exists_vertexSquares` — B2 as consumed: one radius for every vertex, with
  distinct squares disjoint.
* `Graph.IsDrawing.exists_core` — B4, the core of one edge.
* `Graph.IsDrawing.disjoint_of_subset_edgeArc` — B4's "distinct cores are disjoint".
* `Graph.IsDrawing.closedSquare_disjoint_edgeArc_of_ne` — B4's "meets no other vertex square",
  which is a property of the whole arc.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-! ### Square arithmetic

`Schoenflies/Square.lean` has convexity, openness and closedness of `closedSquare` but no
triangle inequality for `supDist` and no monotonicity at a general centre; both are needed
here. -/

/-- Squares about a common centre grow with the radius. `Bounded.closedSquare_mono` says this
only about the origin. -/
theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

/-- The centre lies in its own square. -/
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

/-- The inscribed ball: a ball is inside the square of the same radius, since the sup norm is
at most the Euclidean norm. -/
theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

/-- The circumscribed ball, in the form the separations want: a square of *half* a given
radius sits inside the open ball of that radius, because `√2 < 2`. -/
theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

/-! ### B3 — the last point of an arc inside a closed set -/

/-- The parameters at which a curve lies in a closed set form a compact subset of the
parameter interval: the parametrisation is continuous there and the interval is compact.

Stated over an arbitrary `Icc` and not only over `[0, 1]`, because the *second* use of B3 —
the first entry into the far vertex's square — has to happen after the last exit from the near
one, i.e. on the interval `[a, 1]`. -/
theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

/-- The last parameter inside a closed set. Given one parameter whose point lies in `C`, there
is a largest one: the curve is in `C` there, and at every larger parameter of the interval it
has left `C` for good.

This is the supremum of a nonempty compact set of parameters, which is therefore attained. -/
theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  -- A parameter past the supremum that still lands in `C` would be a member above it.
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

/-- The mirror of `exists_last_mem_Icc`: the first parameter inside a closed set. Before it the
curve has not yet reached `C`. -/
theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

/-- B3 on the unit interval: the last parameter at which an arc is inside a closed set. -/
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

/-- B3 on the unit interval, at the other end: the first parameter at which an arc is inside a
closed set. -/
theorem exists_first_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ I, t < s → f t ∉ C :=
  exists_first_mem_Icc hf hC ht₀ hmem

end Schoenflies

/-! ### B2 — the vertex squares -/

open Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A vertex lies on no arc of an edge it is not incident with: the arc meets the vertex set
only at its own two ends, and those are the vertices it is incident with. -/
theorem IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

/-- B2 at a single vertex: a closed square about `v` meeting no other vertex and no arc of an
edge not incident with `v`.

The two families are separated the same way — one compact separation each, then the common
positive bound of `exists_pos_forall_of_finite` — and the two radii are then merged by taking
the smaller, which is legitimate because shrinking a square preserves "meets nothing". -/
theorem IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  -- The other vertices.
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · -- `w` is at positive Euclidean distance from `v`, and a square of half that radius
        -- sits inside the ball of that radius.
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  -- The non-incident edges.
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

/-- B2 as its consumers want it: **one** radius serving every vertex at once, with the squares
about distinct vertices disjoint.

Disjointness is not a consequence of the per-vertex statement — a square about `v` avoiding
`w` says nothing about a square about `w` reaching towards `v`. It comes from choosing the
radius once for all vertices and then halving it: two squares of radius `r` that met would put
their centres within `2r` in the sup metric, i.e. each centre in the other's square of radius
`2r`, which the unhalved choice forbids. -/
theorem IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  -- One radius for all vertices, by the same monotone-downward bound.
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · -- Both centres are within `r/2` of `x`, hence within `r` of each other.
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

/-! ### B4 — the cores -/

/-- An edge is incident only with its own two ends. -/
theorem not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

/-- "The core meets no other vertex square" is really a statement about the whole arc: the
square about a vertex which is neither end of the edge misses the edge's arc entirely, by B2.
The hypothesis is exactly the second clause of `exists_vertexSquares`. -/
theorem IsDrawing.closedSquare_disjoint_edgeArc_of_ne {e : β} {v w u : Plane} {r : ℝ}
    (hsq : ∀ e ∈ E(G), ¬ G.Inc e u → Disjoint (Plane.closedSquare u r) (edgeArc drawing e))
    (hlink : G.IsLink e v w) (huv : u ≠ v) (huw : u ≠ w) :
    Disjoint (Plane.closedSquare u r) (edgeArc drawing e) :=
  hsq e hlink.edge_mem (not_inc_of_ne hlink huv huw)

/-- **Distinct cores are disjoint.** A subset of one edge's arc containing no vertex meets no
other edge's arc at all, because distinct edges meet only at vertices. Stated for arbitrary
subsets rather than for cores, since that is all the argument uses — and it is why
`exists_core` carries `Disjoint K V(G)` rather than a clause about other edges. -/
theorem IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

/-- **The core of an edge.** Between the last parameter at which the edge's arc is inside the
square about `v` and the first parameter after that at which it is inside the square about `w`
sits a subarc `K` — the core — which meets the square at `v` in its first endpoint only, meets
the square at `w` in its last endpoint only, and contains no vertex at all.

The two squares must be disjoint, which is what the uniform choice of `exists_vertexSquares`
provides; disjointness in particular forces `v ≠ w`, so **this says nothing about a loop
edge** — see the module report.

The "first entry after the last exit" is not the same as "first entry": nothing forbids the
arc from dipping into the far square and coming back, so the second application of B3 is over
`[a, 1]` and not over `[0, 1]`.

That the endpoints of the core are *not* the vertices themselves is where the positivity of
the radius is used: the arc starts at the centre of the square about `v`, so it is still
inside the square just after leaving it, and the last exit therefore happens at a positive
parameter. That fact is what makes `Disjoint K V(G)` true and hence distinct cores disjoint. -/
theorem IsDrawing.exists_core (h : IsDrawing G drawing) {e : β} {v w : Plane} {r : ℝ}
    (hr : 0 < r) (hlink : G.IsLink e v w)
    (hdisj : Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r)) :
    ∃ (K : Set Plane) (p q : Plane),
      K ⊆ edgeArc drawing e ∧ IsCompact K ∧ IsArcBetween K p q ∧
      K ∩ Plane.closedSquare v r = {p} ∧ K ∩ Plane.closedSquare w r = {q} ∧
      Disjoint K V(G) := by
  obtain ⟨f, hcont, hinj, himg, hf0, hf1⟩ := h.edge_isArcBetween hlink
  have hv0 : f 0 ∈ Plane.closedSquare v r := by
    rw [hf0]; exact Plane.mem_closedSquare_self v hr.le
  have hw1 : f 1 ∈ Plane.closedSquare w r := by
    rw [hf1]; exact Plane.mem_closedSquare_self w hr.le
  -- The last exit from the square at `v` …
  obtain ⟨a, haI, -, haD, hafter⟩ :=
    exists_last_mem hcont (Plane.isClosed_closedSquare v r) zero_mem_I hv0
  have hsub : Icc a 1 ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, ht.2⟩
  -- … and the first entry into the square at `w` after it.
  obtain ⟨b, hbmem, -, hbD, hbefore⟩ :=
    exists_first_mem_Icc (hcont.mono hsub) (Plane.isClosed_closedSquare w r)
      (right_mem_Icc.2 haI.2) hw1
  have hbI : b ∈ I := hsub hbmem
  have hne : a ≠ b := by
    intro hEq
    rw [hEq] at haD
    exact Set.disjoint_left.1 hdisj haD hbD
  have hIccI : Icc a b ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, le_trans ht.2 hbmem.2⟩
  -- The core does not reach back to `v`: just after `0` the arc is still inside the square.
  have hpv : f a ≠ v := by
    intro hEq
    have ha0 : a = 0 := hinj haI zero_mem_I (by rw [hEq, hf0])
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 zero_mem_I) r hr
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have htI : min (δ / 2) 1 ∈ I := ⟨ht0.le, min_le_right _ _⟩
    have hdist : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine hafter _ htI (by rw [ha0]; exact ht0) (Plane.closedBall_subset_closedSquare v r ?_)
    rw [mem_closedBall, ← hf0]
    exact (hclose htI hdist).le
  -- Symmetrically, the core does not reach forward to `w`.
  have hqw : f b ≠ w := by
    intro hEq
    have hb1 : b = 1 := hinj hbI one_mem_I (by rw [hEq, hf1])
    have halt1 : a < 1 := by rw [← hb1]; exact lt_of_le_of_ne hbmem.1 hne
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 1 one_mem_I) r hr
    have hmax1 : max (1 - δ / 2) ((a + 1) / 2) < 1 := max_lt (by linarith) (by linarith)
    have hmaxa : a ≤ max (1 - δ / 2) ((a + 1) / 2) :=
      le_trans (by linarith) (le_max_right _ _)
    have htmem : max (1 - δ / 2) ((a + 1) / 2) ∈ Icc a 1 := ⟨hmaxa, hmax1.le⟩
    have hdist : dist (max (1 - δ / 2) ((a + 1) / 2)) 1 < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have := le_max_left (1 - δ / 2) ((a + 1) / 2)
      linarith
    refine hbefore _ htmem (by rw [hb1]; exact hmax1)
      (Plane.closedBall_subset_closedSquare w r ?_)
    rw [mem_closedBall, ← hf1]
    exact (hclose (hsub htmem) hdist).le
  -- The core itself.
  have harc : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    have hsubarc := isArcBetween_subarc_of_injOn_I hcont hinj haI hbI hne
    rwa [uIcc_of_le hbmem.1] at hsubarc
  have hKsub : f '' Icc a b ⊆ edgeArc drawing e := by
    rw [← himg]; exact image_mono hIccI
  have hKv : f '' Icc a b ∩ Plane.closedSquare v r = {f a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hafter t (hIccI ht) hlt)
    · rintro rfl
      exact ⟨⟨a, ⟨le_refl a, hbmem.1⟩, rfl⟩, haD⟩
  have hKw : f '' Icc a b ∩ Plane.closedSquare w r = {f b} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.2 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hbefore t ⟨ht.1, le_trans ht.2 hbmem.2⟩ hlt)
    · rintro rfl
      exact ⟨⟨b, ⟨hbmem.1, le_refl b⟩, rfl⟩, hbD⟩
  refine ⟨f '' Icc a b, f a, f b, hKsub, harc.isArc.isCompact, harc, hKv, hKw,
    Set.disjoint_left.2 fun x hxK hxV => ?_⟩
  -- A vertex on the core is an end of the edge, and each end is excluded by the two facts
  -- above together with the descriptions of `K ∩ D_v` and `K ∩ D_w`.
  rcases h.vertex_mem_edgeArc hlink hxV (hKsub hxK) with heq | heq
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare v r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self v hr.le⟩
    rw [hKv, mem_singleton_iff] at hmem
    exact hpv (hmem ▸ heq)
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare w r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self w hr.le⟩
    rw [hKw, mem_singleton_iff] at hmem
    exact hqw (hmem ▸ heq)

end Graph

end BundlePart382

section BundlePart383
/- Source: dev/planar_search/schoenflies_port/Schoenflies/LocallyPolygonal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# The plane minus finitely many open squares is locally polygonally connected

This is brick B5 of the polygonal-redrawing argument. The redrawing cuts an open axis-parallel
square out of the plane around each vertex of the graph; what the rest of the argument needs of
the leftover set `M` is that it is *locally polygonally connected* — every point of `M` has a
relatively open neighbourhood all of whose points are joined to each other by polygonal paths
running inside `M`. That is what feeds the clopen argument one level up (brick B6), where the
basic open piece is no longer a ball.

The informal description of the three basic shapes — a disk away from every square, a half-disk
against one side, a three-quarter disk at a corner — suggests an angular case analysis. There is
none here. Both the squares and the basic neighbourhoods are axis-parallel, so each shape is an
intersection of a small square with the complement of an open square, and

* the complement of an open square is the union of the four closed coordinate half-planes that
  bound it (`Plane.compl_openSquare_subset_iUnion`);
* intersecting with a small square gives four *rectangles*, each convex;
* if the small square is small enough, each of those rectangles is either empty or contains the
  centre `p` (`Plane.exists_radius_sides`).

A union of convex sets with a common point is polygonally connected by two segments through that
point, which is `isLocallyPolyConnAt_of_star`. The three shapes are then just the three ways the
list of nonempty pieces can come out (one, two adjacent, or two adjacent again with `p` on the
corner) and none of them has to be named.

The passage from one square to finitely many is a shrinking step: since the closed squares are
pairwise disjoint, a point lies in at most one of them, and a small enough neighbourhood of any
point misses all the others outright, so `M` looks locally exactly like the one-square case.

## Blueprint

* `PolyConnIn` — "joined by a polygonal path inside `S`"; the relation Lemma 1.1 produces.
* `IsLocallyPolyConn` — the local form of polygonal connectedness, brick B5's conclusion.
* `polyConnIn_of_convex`, `polyConnIn_union_of_convex` — a rectangle, and two rectangles that
  meet, are polygonally connected.
* `Plane.sideHalfPlane`, `Plane.sideGap` — the four half-planes bounding a square and the room
  between a point and each of them.
* `isLocallyPolyConnAt_compl_openSquare` — the one-square case: the complement of any open
  square is locally polygonally connected, at every point of the plane.
* `isLocallyPolyConn_compl_biUnion` — brick B5: the plane minus finitely many open squares with
  pairwise disjoint closures is locally polygonally connected.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T : Set Plane} {x y z : Plane}

/-! ### Two list lemmas about `poly`

`PolyPath.lean` has `poly_concat`, which extends a vertex list by a single vertex. Transitivity
and symmetry of polygonal connectedness need the two-list versions; both are general facts about
`poly` and belong beside `poly_concat` rather than here. -/

/-- Reversing a vertex list does not move its carrier. -/
theorem poly_reverse : ∀ vs : List Plane, poly vs.reverse = poly vs
  | [] => by simp
  | [v] => by simp
  | u :: v :: tl => by
    rw [List.reverse_cons, poly_concat (by simp) u, poly_reverse (v :: tl),
      List.getLast_reverse (by simp), List.head_cons, poly_cons_cons, segment_symm]
    exact union_comm _ _

/-! ### Polygonal connectedness inside a set -/

/-- `x` and `y` are joined by a polygonal path lying inside `S`.

This is the relation `exists_poly_of_isPreconnected` produces; naming it lets the local statement
below be phrased without repeating the vertex-list existential. -/
def PolyConnIn (S : Set Plane) (x y : Plane) : Prop :=
  ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ S ∧ vs.head h = x ∧ vs.getLast h = y

theorem PolyConnIn.refl (hx : x ∈ S) : PolyConnIn S x x :=
  ⟨[x], by simp, by simpa using hx, rfl, rfl⟩

/-- A point joined to anything lies in the set: the carrier contains the head. -/
theorem PolyConnIn.left_mem (h : PolyConnIn S x y) : x ∈ S := by
  obtain ⟨vs, hne, hsub, hhead, -⟩ := h
  exact hhead ▸ hsub (head_mem_poly hne)

theorem PolyConnIn.right_mem (h : PolyConnIn S x y) : y ∈ S := by
  obtain ⟨vs, hne, hsub, -, hlast⟩ := h
  exact hlast ▸ hsub (getLast_mem_poly hne)

theorem PolyConnIn.mono (h : PolyConnIn S x y) (hST : S ⊆ T) : PolyConnIn T x y := by
  obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h
  exact ⟨vs, hne, hsub.trans hST, hhead, hlast⟩

theorem PolyConnIn.trans (hxy : PolyConnIn S x y) (hyz : PolyConnIn S y z) :
    PolyConnIn S x z := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := hxy
  obtain ⟨ws, hw, hwS, hwh, hwl⟩ := hyz
  obtain ⟨w, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.head_cons] at hwh
  subst hwh
  refine ⟨vs ++ w :: rest, by simp, ?_, ?_, ?_⟩
  · rw [poly_append hv w rest hvl]; exact union_subset hvS hwS
  · rw [List.head_append_of_ne_nil hv]; exact hvh
  · rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil w rest)]; exact hwl

theorem PolyConnIn.symm (h : PolyConnIn S x y) : PolyConnIn S y x := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := h
  refine ⟨vs.reverse, by simpa using hv, ?_, ?_, ?_⟩
  · rw [poly_reverse]; exact hvS
  · rw [List.head_reverse]; exact hvl
  · rw [List.getLast_reverse]; exact hvh

/-- Convexity is the base case: the segment is already a polygonal path. -/
theorem polyConnIn_of_convex {C : Set Plane} (hC : Convex ℝ C) (hCS : C ⊆ S)
    (hx : x ∈ C) (hy : y ∈ C) : PolyConnIn S x y :=
  ⟨[x, y], by simp, by
    rw [poly_cons_cons, poly_singleton]
    exact union_subset ((hC.segment_subset hx hy).trans hCS)
      (singleton_subset_iff.2 (hCS hy)), rfl, rfl⟩

/-- Two convex pieces that meet are polygonally connected in their union — two segments through
a common point. This is the "two rectangles meeting in a rectangle" step, with the shape of the
overlap irrelevant: only that it is inhabited. -/
theorem polyConnIn_union_of_convex {C D : Set Plane} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hmeet : (C ∩ D).Nonempty) (hx : x ∈ C ∪ D) (hy : y ∈ C ∪ D) : PolyConnIn (C ∪ D) x y := by
  obtain ⟨w, hwC, hwD⟩ := hmeet
  have hxw : PolyConnIn (C ∪ D) x w := by
    rcases hx with hx | hx
    · exact polyConnIn_of_convex hC subset_union_left hx hwC
    · exact polyConnIn_of_convex hD subset_union_right hx hwD
  have hwy : PolyConnIn (C ∪ D) w y := by
    rcases hy with hy | hy
    · exact polyConnIn_of_convex hC subset_union_left hwC hy
    · exact polyConnIn_of_convex hD subset_union_right hwD hy
  exact hxw.trans hwy

/-! ### The local statement -/

/-- `S` is polygonally connected near `p`: some open `U` containing `p` has all the points of
`U ∩ S` joined to each other by polygonal paths *inside `S`*.

`U ∩ S` is the relative neighbourhood; stating it through an ambient open set avoids carrying a
subtype topology. Note the paths are required to lie in `S`, not in the neighbourhood — that is
the form brick B6's clopen argument consumes. -/
def IsLocallyPolyConnAt (S : Set Plane) (p : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyConnIn S x y

/-- `S` is locally polygonally connected: polygonally connected near each of its points. -/
def IsLocallyPolyConn (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt S p

/-- If the relative neighbourhood is itself convex there is nothing to do. -/
theorem isLocallyPolyConnAt_of_convex {U : Set Plane} {p : Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hUS : U ⊆ S) (hconv : Convex ℝ U) : IsLocallyPolyConnAt S p :=
  ⟨U, hU, hpU, fun _ hx _ hy => polyConnIn_of_convex hconv hUS hx.1 hy.1⟩

/-- The gluing step, and the whole geometric content of the three shapes: if the relative
neighbourhood is covered by convex pieces each of which is either empty or contains `p`, then
any two of its points are joined by two segments through `p`.

No piece is required to be nonempty and no piece is named, so the same statement covers the
disk, the half-disk and the three-quarter disk at once. -/
theorem isLocallyPolyConnAt_of_star {U : Set Plane} {p : Plane} {ι : Type*} {C : ι → Set Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hcover : U ∩ S ⊆ ⋃ i, C i) (hsub : ∀ i, C i ⊆ S)
    (hconv : ∀ i, Convex ℝ (C i)) (hstar : ∀ i, ∀ z ∈ C i, p ∈ C i) :
    IsLocallyPolyConnAt S p := by
  refine ⟨U, hU, hpU, fun x hx y hy => ?_⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover hx)
  obtain ⟨j, hyj⟩ := mem_iUnion.1 (hcover hy)
  exact (polyConnIn_of_convex (hconv i) (hsub i) hxi (hstar i x hxi)).trans
    (polyConnIn_of_convex (hconv j) (hsub j) (hstar j y hyj) hyj)

/-! ### The four sides of a square -/

namespace Plane

/-- A coordinate description of the open square: it is the set of points within `r` of the
centre in each coordinate separately. -/
theorem mem_openSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ openSquare c r ↔ ∀ i, |x i - c i| < r := by
  simp only [openSquare, mem_setOf_eq, supDist, supNorm, sub_apply, max_lt_iff,
    Fin.forall_fin_two]

/-- The centre of a square of positive radius is in it. -/
theorem mem_openSquare_self {p : Plane} {s : ℝ} (hs : 0 < s) : p ∈ openSquare p s := by
  simpa [openSquare] using hs

/-- Squares about a point grow with the radius. -/
theorem openSquare_mono {p : Plane} {s t : ℝ} (h : s ≤ t) : openSquare p s ⊆ openSquare p t :=
  fun _ hx => lt_of_lt_of_le hx h

/-- The closed half-plane on the far side of the `i`-th pair of sides of the square about `c` of
radius `r`; `b = true` picks the upper one. The four of them cover the complement of the square,
and each is convex, which is all the argument uses them for. -/
def sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) : Set Plane :=
  cond b {x | c i + r ≤ x i} {x | x i ≤ c i - r}

/-- How much room there is between `p` and the half-plane `sideHalfPlane c r i b`: positive
exactly when `p` is outside it, and an upper bound on a square radius that keeps a neighbourhood
of `p` clear of it. -/
noncomputable def sideGap (c : Plane) (r : ℝ) (p : Plane) (i : Fin 2) (b : Bool) : ℝ :=
  cond b ((c i + r) - p i) (p i - (c i - r))

theorem convex_sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    Convex ℝ (sideHalfPlane c r i b) := by
  cases b
  · exact convex_coord_le i _
  · exact convex_coord_ge i _

/-- Each of the four half-planes misses the open square. -/
theorem sideHalfPlane_subset_compl (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    sideHalfPlane c r i b ⊆ (openSquare c r)ᶜ := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff c r x).1 hmem i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hx) (by linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hx) (by linarith [hlt.2])

/-- The complement of an open square is covered by the four closed half-planes bounding it. -/
theorem compl_openSquare_subset_iUnion (c : Plane) (r : ℝ) :
    (openSquare c r)ᶜ ⊆ ⋃ ib : Fin 2 × Bool, sideHalfPlane c r ib.1 ib.2 := by
  intro x hx
  rw [mem_compl_iff, mem_openSquare_iff] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  rcases le_abs.1 hi with h | h
  · exact mem_iUnion.2 ⟨(i, true), show c i + r ≤ x i by linarith⟩
  · exact mem_iUnion.2 ⟨(i, false), show x i ≤ c i - r by linarith⟩

/-- If the radius is at most the room between `p` and a half-plane, the square about `p` of that
radius misses the half-plane. No sign condition on the gap: when it is nonpositive the radius is
too, and the square is empty. -/
theorem openSquare_disjoint_sideHalfPlane {c : Plane} {r s : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (hs : s ≤ sideGap c r p i b) :
    ∀ x ∈ openSquare p s, x ∉ sideHalfPlane c r i b := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff p s x).1 hx i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hmem) (by
      simp only [sideGap, cond_false] at hs; linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hmem) (by
      simp only [sideGap, cond_true] at hs; linarith [hlt.2])

/-- If there is no room between `p` and a half-plane, `p` is in it. -/
theorem mem_sideHalfPlane_of_sideGap_nonpos {c : Plane} {r : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (h : sideGap c r p i b ≤ 0) : p ∈ sideHalfPlane c r i b := by
  cases b
  · simp only [sideGap, cond_false] at h
    exact show p i ≤ c i - r by linarith
  · simp only [sideGap, cond_true] at h
    exact show c i + r ≤ p i by linarith

/-- Each piece the sides of one square cut a small square into is an axis-parallel rectangle —
an intersection of four coordinate strips with one more coordinate half-plane — and is therefore
convex. This is the only property of the three basic shapes the argument uses. -/
theorem convex_openSquare_inter_sideHalfPlane (p : Plane) (s : ℝ) (c : Plane) (r : ℝ)
    (i : Fin 2) (b : Bool) : Convex ℝ (openSquare p s ∩ sideHalfPlane c r i b) :=
  (convex_openSquare p s).inter (convex_sideHalfPlane c r i b)

end Plane

/-! ### Choosing one radius for finitely many constraints -/

/-- A positive lower bound for whichever members of a finite family happen to be positive.
This is `exists_pos_le_of_finite` with the selection built in; the members that are nonpositive
impose nothing. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (d : ι → ℝ) :
    ∃ s > 0, ∀ i, 0 < d i → s ≤ d i := by
  obtain ⟨s, hs, hle⟩ :=
    exists_pos_le_of_finite (S := {i : ι | 0 < d i}) (Set.toFinite _) (f := d) fun _ hi => hi
  exact ⟨s, hs, fun i hi => hle i hi⟩

/-- A radius small enough that the square about `p` misses every side half-plane of the square
about `c` that `p` itself is outside of. -/
theorem Plane.exists_radius_sides (c : Plane) (r : ℝ) (p : Plane) :
    ∃ s > 0, ∀ ib : Fin 2 × Bool,
      ∀ z ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2,
        p ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2 := by
  obtain ⟨s, hs, hle⟩ := exists_pos_le_of_pos fun ib : Fin 2 × Bool => sideGap c r p ib.1 ib.2
  refine ⟨s, hs, fun ib z hz => ⟨?_, ?_⟩⟩
  · -- `p` is the centre of its own square, which is nonempty because `s > 0`.
    exact mem_openSquare_self hs
  · -- If there were room, the square about `p` would already miss this half-plane, and `z`
    -- could not be in it.
    by_contra hp
    exact openSquare_disjoint_sideHalfPlane
      (hle ib (lt_of_not_ge fun hcon => hp (mem_sideHalfPlane_of_sideGap_nonpos hcon))) z hz.1 hz.2

/-! ### The one-square case -/

/-- **The one-square case of brick B5.** The complement of an open axis-parallel square is
polygonally connected near every point of the plane.

The neighbourhood is a small square about `p`; intersected with the complement it becomes the
union of the four rectangles cut off by the sides of the big square, each convex and each either
empty or containing `p`. That is the disk / half-disk / three-quarter-disk trichotomy, with the
cases never distinguished. -/
theorem isLocallyPolyConnAt_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
      openSquare p s ∩ sideHalfPlane c r ib.1 ib.2)
    (isOpen_openSquare p s) (mem_openSquare_self hs) ?_ ?_ ?_ hstar
  · rintro x ⟨hxU, hxM⟩
    obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c r hxM)
    exact mem_iUnion.2 ⟨ib, hxU, hib⟩
  · exact fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2)
  · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c r ib.1 ib.2

/-! ### Finitely many squares -/

/-- **Brick B5.** The plane minus finitely many open axis-parallel squares whose closed squares
are pairwise disjoint is locally polygonally connected.

Two steps. Away from all the closed squares a small square about `p` is convex and already
inside `M`. Otherwise `p` lies in exactly one closed square — exactly one, by disjointness — and
a small enough square about `p` misses all the others, so near `p` the set `M` *is* the
complement of that one open square and the previous theorem's decomposition applies verbatim. -/
theorem isLocallyPolyConn_compl_biUnion {A : Set Plane} (hA : A.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ A, ∀ c' ∈ A, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ A, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ρ c < supDist p c → ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c _ s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ A, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀A, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ A \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcA, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀A c hcA fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s₁, hs₁, hs₁le⟩ := exists_pos_le_of_finite (hA.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    obtain ⟨s₂, hs₂, hstar⟩ := Plane.exists_radius_sides c₀ (ρ c₀) p
    set s := min s₁ s₂ with hsdef
    have hs : 0 < s := lt_min hs₁ hs₂
    have hpU : p ∈ openSquare p s := mem_openSquare_self hs
    -- Near `p`, the set `M` is exactly the complement of the one open square about `c₀`.
    have hloc : openSquare p s ∩ (⋃ c ∈ A, openSquare c (ρ c))ᶜ
        ⊆ openSquare p s ∩ (openSquare c₀ (ρ c₀))ᶜ := by
      rintro x ⟨hxU, hxM⟩
      exact ⟨hxU, fun hcon => hxM (mem_biUnion hc₀A hcon)⟩
    have hback : ∀ x ∈ openSquare p s, x ∉ openSquare c₀ (ρ c₀) →
        x ∈ (⋃ c ∈ A, openSquare c (ρ c))ᶜ := by
      intro x hxU hx₀ hcon
      obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c (by linarith [hfar c ⟨hcA, hcne⟩]) s
          (le_trans (min_le_left _ _) (hs₁le c ⟨hcA, hcne⟩)) x hxU hxc
    refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
        openSquare p s ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2)
      (isOpen_openSquare p s) hpU ?_ ?_ ?_ ?_
    · rintro x hx
      obtain ⟨hxU, hx₀⟩ := hloc hx
      obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c₀ (ρ c₀) hx₀)
      exact mem_iUnion.2 ⟨ib, hxU, hib⟩
    · rintro ib x ⟨hxU, hxH⟩
      exact hback x hxU (sideHalfPlane_subset_compl c₀ (ρ c₀) ib.1 ib.2 hxH)
    · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c₀ (ρ c₀) ib.1 ib.2
    · -- Shrinking the radius from `s₂` to `s` keeps every nonempty piece through `p`.
      rintro ib z ⟨hzU, hzH⟩
      refine ⟨hpU, ?_⟩
      have : z ∈ openSquare p s₂ ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2 :=
        ⟨openSquare_mono (min_le_right s₁ s₂) hzU, hzH⟩
      exact (hstar ib z this).2
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ A, 0 < supDist p c - ρ c := by
      intro c hcA
      have := hnear c hcA
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hA (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt_of_convex (isOpen_openSquare p s)
      (mem_openSquare_self hs) ?_ (convex_openSquare p s)
    intro x hx hcon
    obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c (by linarith [hfar c hcA]) s (hsle c hcA) x hx hxc

end Schoenflies

end BundlePart383

section BundlePart384
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolygonalCarrier.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Polygonal connectedness over a carrier

`Schoenflies.exists_poly_of_isPreconnected` joins two points of an *open* connected subset
of the plane by a polygonal path. The redrawing argument needs the same conclusion for a
carrier that is **not** open in the plane: the ambient set there is the plane minus finitely
many open squares, and the basic neighbourhood of a point on a square's boundary is a
half-disk or a three-quarter disk rather than a ball.

This module restates the clopen argument over an arbitrary carrier `C`. The only hypothesis
on `C` is that it is *locally polygonally connected*: every point has a relatively open
neighbourhood all of whose points it reaches by a polygonal path inside `C`. Openness of `C`
is used nowhere; the ball of the classical proof appears only in
`isLocallyPolyConnected_of_isOpen`, which is what recovers the old statement.

## Blueprint

Brick B6 of `lem:polygonal-redrawing` (H6): polygonal connectivity one level up.

* `PolyReaches` — "joined by a polygonal path inside `C`", as an inductive relation.
  **Note for the integrator:** `Schoenflies/LocallyPolygonal.lean` is being written
  concurrently and defines a relation of the same meaning; the two want unifying.
* `IsLocallyPolyConnected` — the hypothesis replacing openness.
* `PolyReaches.of_isPreconnected` — Lemma 1.1 (polygonal connectedness) over a carrier.
* `exists_poly_of_isPreconnected'` — the old `exists_poly_of_isPreconnected` re-derived from
  it, verbatim; the `example` below it is a machine check that the statements agree.
-/

open Metric Set

namespace Schoenflies

variable {C D : Set Plane} {x y z : Plane}

/-! ### Joined by a polygonal path inside a carrier -/

/-- `PolyReaches C x y`: there is a polygonal path from `x` to `y` all of whose segments lie
in `C`. Built at the far end — a path is extended by one segment at a time — because that is
the shape both halves of the clopen argument use. `refl` carries `x ∈ C` so that a constant
path witnesses membership, matching `poly [x] = {x}`. -/
inductive PolyReaches (C : Set Plane) (x : Plane) : Plane → Prop
  | refl (hx : x ∈ C) : PolyReaches C x x
  | step {y z : Plane} (h : PolyReaches C x y) (hseg : segment ℝ y z ⊆ C) : PolyReaches C x z

namespace PolyReaches

/-- A single segment inside `C` is already a polygonal path. -/
theorem of_segment (hseg : segment ℝ x y ⊆ C) : PolyReaches C x y :=
  (PolyReaches.refl (hseg (left_mem_segment ℝ x y))).step hseg

theorem left_mem (h : PolyReaches C x y) : x ∈ C := by
  induction h with
  | refl hx => exact hx
  | step _ _ ih => exact ih

theorem right_mem (h : PolyReaches C x y) : y ∈ C := by
  induction h with
  | refl hx => exact hx
  | @step _ z _ hseg _ => exact hseg (right_mem_segment ℝ _ z)

theorem trans (h₁ : PolyReaches C x y) (h₂ : PolyReaches C y z) : PolyReaches C x z := by
  induction h₂ with
  | refl _ => exact h₁
  | step _ hseg ih => exact ih.step hseg

/-- Symmetry: a path is run backwards one segment at a time, each reversed segment being the
same set. -/
theorem symm (h : PolyReaches C x y) : PolyReaches C y x := by
  induction h with
  | refl hx => exact PolyReaches.refl hx
  | @step y z _ hseg ih =>
    -- The last segment, reversed, joins `z` back to `y`; then follow the shorter path back.
    exact (of_segment (by rwa [segment_symm])).trans ih

theorem mono (hCD : C ⊆ D) (h : PolyReaches C x y) : PolyReaches D x y := by
  induction h with
  | refl hx => exact PolyReaches.refl (hCD hx)
  | step _ hseg ih => exact ih.step (hseg.trans hCD)

end PolyReaches

/-! ### The relation and the vertex-list representation agree -/

/-- A polygonal path in the sense of `PolyReaches` yields a vertex list with the carrier of
its polygon inside `C`. This is `poly_concat` used once per `step`. -/
theorem PolyReaches.exists_poly (h : PolyReaches C x y) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y := by
  induction h with
  | refl hx => exact ⟨[x], by simp, by simpa using hx, rfl, rfl⟩
  | @step _ z _ hseg ih =>
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := ih
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub hseg
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp

/-- Conversely a vertex list whose polygon lies in `C` joins its ends. -/
theorem polyReaches_of_poly_subset : ∀ {vs : List Plane} (hne : vs ≠ []), poly vs ⊆ C →
    PolyReaches C (vs.head hne) (vs.getLast hne)
  | [], hne, _ => absurd rfl hne
  | [v], _, hsub => PolyReaches.refl (hsub (by simp))
  | u :: v :: rest, _, hsub => by
    rw [poly_cons_cons] at hsub
    have hstep : PolyReaches C u v :=
      PolyReaches.of_segment (subset_union_left.trans hsub)
    have hrest := polyReaches_of_poly_subset (List.cons_ne_nil v rest)
      (subset_union_right.trans hsub)
    rw [List.getLast_cons (List.cons_ne_nil v rest)]
    exact hstep.trans hrest

/-! ### Local polygonal connectedness -/

/-- `C` is locally polygonally connected when every point of `C` has a relatively open
neighbourhood in `C` each of whose points it reaches by a polygonal path inside `C`.

The neighbourhood is presented as `V ∩ C` for an ambient open `V`, which is exactly what a
relatively open neighbourhood is; the paths are only required to stay inside `C`, not inside
the neighbourhood, since that is all the clopen argument uses and it is the weaker demand on
a producer. Ball, half-disk and three-quarter disk all qualify. -/
def IsLocallyPolyConnected (C : Set Plane) : Prop :=
  ∀ w ∈ C, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ V ∩ C, PolyReaches C w z

/-- The relative-openness step, stated once because the clopen argument uses it twice — for
the reachable set and, run backwards, for its relative complement.

A subset of `C` closed under "reach one more point of `C` by a polygonal path" is relatively
open in `C`. The witness is the union of all ambient open sets that are polygonally attached
to a point of `S`; no choice is needed to assemble it. -/
theorem isRelOpen_of_polyReaches_stable (hloc : IsLocallyPolyConnected C) {S : Set Plane}
    (hS : S ⊆ C) (hstable : ∀ w ∈ S, ∀ z ∈ C, PolyReaches C w z → z ∈ S) :
    ∃ U : Set Plane, IsOpen U ∧ S ⊆ U ∧ U ∩ C ⊆ S := by
  refine ⟨⋃₀ {V : Set Plane | IsOpen V ∧ ∃ w ∈ S, ∀ z ∈ V ∩ C, PolyReaches C w z},
    isOpen_sUnion fun V hV => hV.1, fun w hw => ?_, ?_⟩
  · obtain ⟨V, hVopen, hwV, hVreach⟩ := hloc w (hS hw)
    exact ⟨V, ⟨hVopen, w, hw, hVreach⟩, hwV⟩
  · rintro z ⟨⟨V, ⟨_, w, hwS, hVreach⟩, hzV⟩, hzC⟩
    exact hstable w hwS z hzC (hVreach z ⟨hzV, hzC⟩)

/-! ### The theorem -/

/-- Lemma 1.1 (polygonal connectedness) over a carrier: in a relatively connected, locally
polygonally connected set, any two points are joined by a polygonal path inside the set.

The proof is the clopen argument. The points reachable from `x` are relatively open in `C`,
and so are the unreachable ones — the same lemma, since "unreachable" is stable under
reaching too, by symmetry. `IsPreconnected C` then forbids the split. -/
theorem PolyReaches.of_isPreconnected (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : PolyReaches C x y := by
  by_contra hxy
  set R : Set Plane := {w | w ∈ C ∧ PolyReaches C x w} with hRdef
  obtain ⟨U, hUopen, hRU, hUR⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := R) (fun _ hw => hw.1)
      (fun _ hw _ hzC hreach => ⟨hzC, hw.2.trans hreach⟩)
  obtain ⟨U', hU'open, hRU', hU'R⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := C \ R) (fun _ hw => hw.1)
      (fun w hw z hzC hreach => ⟨hzC, fun hzR => hw.2 ⟨hw.1, hzR.2.trans hreach.symm⟩⟩)
  obtain ⟨w, hwC, hwU, hwU'⟩ := hconn U U' hUopen hU'open
    (fun v hv => (em (v ∈ R)).imp (fun h => hRU h) (fun h => hRU' ⟨hv, h⟩))
    ⟨x, hx, hRU ⟨hx, PolyReaches.refl hx⟩⟩
    ⟨y, hy, hRU' ⟨hy, fun h => hxy h.2⟩⟩
  exact (hU'R ⟨hwU', hwC⟩).2 (hUR ⟨hwU, hwC⟩)

/-- The vertex-list reading of the carrier theorem, matching the shape `PolyPath` delivers. -/
theorem exists_poly_of_isPreconnected_of_locally (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ C ∧ vs.head h = x ∧ vs.getLast h = y :=
  (PolyReaches.of_isPreconnected hloc hconn hx hy).exists_poly

/-! ### Producers of the hypothesis -/

/-- Two convex pieces of `C` that meet make one polygonally connected piece: the bent path
through a common point. This is the shape brick B5 needs for the corner neighbourhood, which
is a disk minus an open quadrant — the union of two half-disks. -/
theorem polyReaches_union_of_convex {S T : Set Plane} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hST : (S ∩ T).Nonempty) (hsub : S ∪ T ⊆ C) (hx : x ∈ S ∪ T) (hy : y ∈ S ∪ T) :
    PolyReaches C x y := by
  obtain ⟨p, hpS, hpT⟩ := hST
  have hSC : ∀ {a b}, a ∈ S → b ∈ S → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hS.segment_subset ha hb).trans (subset_union_left.trans hsub))
  have hTC : ∀ {a b}, a ∈ T → b ∈ T → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hT.segment_subset ha hb).trans (subset_union_right.trans hsub))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hSC hx hy
  · exact (hSC hx hpS).trans (hTC hpT hy)
  · exact (hTC hx hpT).trans (hSC hpS hy)
  · exact hTC hx hy

/-- An open set is locally polygonally connected: the balls it contains are convex. This is
the only place a ball appears, and it is what recovers the old statement. -/
theorem isLocallyPolyConnected_of_isOpen (hC : IsOpen C) : IsLocallyPolyConnected C := by
  intro w hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hC w hw
  exact ⟨ball w r, isOpen_ball, mem_ball_self hr, fun z hz =>
    PolyReaches.of_segment
      (((convex_ball w r).segment_subset (mem_ball_self hr) hz.1).trans hball)⟩

/-- `PolyPath.exists_poly_of_isPreconnected`, re-derived from the carrier version. -/
theorem exists_poly_of_isPreconnected' {Ω : Set Plane} {x y : Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y :=
  exists_poly_of_isPreconnected_of_locally (isLocallyPolyConnected_of_isOpen hΩ) hconn hx hy

-- The generalisation is genuine: this `rfl` typechecks only if the statement above is
-- literally the one `PolyPath` proves, proof irrelevance doing the rest.
example : @exists_poly_of_isPreconnected = @exists_poly_of_isPreconnected' := rfl

end Schoenflies

end BundlePart384

section BundlePart385
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolyLocal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Local polygonal connectedness, in the form brick B7 consumes

`Schoenflies/LocallyPolygonal.lean` (brick B5) and `Schoenflies/PolygonalCarrier.lean`
(brick B6) were written independently and each carries its own "joined by a polygonal path
inside a set" relation — `PolyConnIn` as an existential over vertex lists, `PolyReaches` as
an inductive relation — with its own local form. This module makes them one, and then fixes
the shape problem that stops B5 from feeding B7.

## The shape problem

Both local forms ask only that the connecting path lie in `S`:

```
IsLocallyPolyConnAt S p  :  ∃ U open ∋ p, ∀ x y ∈ U ∩ S, PolyConnIn S x y
IsLocallyPolyConnected C :  ∀ w ∈ C, ∃ V open ∋ w, ∀ z ∈ V ∩ C, PolyReaches C w z
```

That is enough for B6 — the clopen argument only needs *some* path — but it is a property
with **no local content whatsoever**: any polygonally connected `S` satisfies it with
`U = univ`. In particular it does not survive intersection with an open set, and that is
exactly what B7 needs: `U_e` is a component of a relatively open piece of `M`, and a
replacement arc has to stay inside the thin tube, not merely inside `M`.

The fix is `IsLocallyPolyConnAt'`: *arbitrarily small* neighbourhoods `U` of `p` such that
any two points of `U ∩ S` are joined **inside `U ∩ S`**. B5's proof already produces this —
its paths are two segments inside convex pieces of the small square about `p`, and the
square's radius may be shrunk freely — so nothing geometric is lost, only misstated.
`isLocallyPolyConn'_compl_openSquare` and `isLocallyPolyConn'_compl_biUnion` are B5 in the
strengthened form, and `IsLocallyPolyConn'.weaken` recovers the original statements.

## Blueprint

Brick B5 ↔ brick B6 of `lem:polygonal-redrawing` (H6), and the interface B7 uses.

* `polyConnIn_iff_polyReaches` — the two relations agree.
* `IsLocallyPolyConn.isLocallyPolyConnected`, `IsLocallyPolyConnected.isLocallyPolyConn` —
  the two weak local forms agree, so B5 as originally stated does feed B6.
* `IsLocallyPolyConnAt'`, `IsLocallyPolyConn'` — the strengthened local form.
* `isLocallyPolyConnAt'_of_convex_cover` — the strengthened star lemma: a square about `p`
  cut by convex pieces, each of which contains `p` as soon as it is nonempty.
* `isLocallyPolyConnAt'_compl_openSquare`, `isLocallyPolyConn'_compl_biUnion` — **brick B5**,
  strengthened.
* `IsLocallyPolyConn'.inter_isOpen` — shrinkability: a relatively open piece of a locally
  polygonally connected set is locally polygonally connected.
* `IsRelOpenIn`, `isRelOpenIn_connectedComponentIn` — components of relatively open subsets
  are relatively open, the fact B7 quotes for `U_e`.
* `polyReaches_of_isPreconnected_of_isRelOpenIn`, `polyReaches_connectedComponentIn` — the
  payoff: two points of a connected relatively open piece are joined *inside that piece*.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

/-! ### The two relations agree

`PolyReaches.exists_poly` and `polyReaches_of_poly_subset` are both on `main`; this is the
one-line packaging that lets a producer of either relation serve a consumer of the other. -/

/-- The vertex-list relation of `LocallyPolygonal.lean` and the inductive relation of
`PolygonalCarrier.lean` are the same relation. -/
theorem polyConnIn_iff_polyReaches : PolyConnIn S x y ↔ PolyReaches S x y := by
  constructor
  · rintro ⟨vs, hne, hsub, hhead, hlast⟩
    have h := polyReaches_of_poly_subset hne hsub
    rwa [hhead, hlast] at h
  · intro h
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h.exists_poly
    exact ⟨vs, hne, hsub, hhead, hlast⟩

alias ⟨PolyConnIn.polyReaches, PolyReaches.polyConnIn⟩ := polyConnIn_iff_polyReaches

/-! ### The two weak local forms agree

`IsLocallyPolyConn` quantifies over *pairs* of points of the neighbourhood,
`IsLocallyPolyConnected` only over paths *from the centre*; symmetry and transitivity of the
relation make the two equivalent. -/

/-- Brick B5's conclusion, read as brick B6's hypothesis. -/
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

/-- The converse: a path from the centre to each of two points, run backwards and forwards. -/
theorem IsLocallyPolyConnected.isLocallyPolyConn (h : IsLocallyPolyConnected S) :
    IsLocallyPolyConn S := by
  intro p hp
  obtain ⟨V, hV, hpV, hreach⟩ := h p hp
  exact ⟨V, hV, hpV, fun x hx y hy => ((hreach x hx).symm.trans (hreach y hy)).polyConnIn⟩

/-! ### Squares are a neighbourhood basis

B5 builds its neighbourhoods as axis-parallel squares, and the strengthened local form needs
them arbitrarily small inside a given open set. -/

namespace Plane

/-- A square of half a radius sits inside the ball of that radius, because `√2 < 2`. The open
counterpart of `Plane.closedSquare_subset_ball`, restated here so that this module does not
have to import the graph layer. No sign condition on the radius: for `ε ≤ 0` the square is
already empty. -/
theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

/-- Inside any open set around `p` there is a square about `p`, of radius at most any
prescribed positive bound. -/
theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

/-! ### The strengthened local form -/

/-- `S` is polygonally connected near `p` **inside arbitrarily small neighbourhoods**: for
every open `W` containing `p` there is an open `U ⊆ W` containing `p` such that any two points
of `U ∩ S` are joined by a polygonal path lying in `U ∩ S`.

Two strengthenings over `IsLocallyPolyConnAt`, and both are needed by brick B7. The path is
confined to the neighbourhood, not merely to `S`, because a replacement arc has to stay in its
tube; and the neighbourhoods run through a basis at `p`, because otherwise the property does
not survive intersecting `S` with an open set (`IsLocallyPolyConn'.inter_isOpen`). -/
def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

/-- `S` is locally polygonally connected in the strengthened sense. -/
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

/-- The strengthened form implies the original brick B5 statement, so nothing is lost by
replacing one with the other. -/
theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

/-- What brick B6 consumes. -/
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

/-- The property is local: only the trace of `S` on a neighbourhood of `p` matters. This is
what reduces "finitely many squares" to "one square". -/
theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

/-- A neighbourhood of `p` already inside `S` settles the point: shrink it to a square, which
is convex, so a single segment joins any two of its points. -/
theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

/-- An open set is locally polygonally connected in the strengthened sense. -/
theorem isLocallyPolyConn'_of_isOpen (hS : IsOpen S) : IsLocallyPolyConn' S :=
  fun _ hp => isLocallyPolyConnAt'_of_nbhd_subset hS hp Subset.rfl

/-- **The strengthened star lemma**, and the whole geometric content of brick B5's three
shapes. Suppose that inside one square about `p` the trace of `S` is covered by convex sets
`H i`, that each `H i` meets that square only inside `S`, and that each `H i` which meets the
square contains `p`. Then `S` is locally polygonally connected at `p` in the strengthened
sense.

Two points of a small square about `p` are then joined by two segments through `p`, each
inside one convex piece of that *small* square — which is why the path never leaves the
neighbourhood. No piece is required to be nonempty and none is named, so the disk, the
half-disk and the three-quarter disk are all this statement. -/
theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  -- Every point of the small relative square is joined to the centre by one segment.
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

/-! ### Brick B5, strengthened

The two theorems of `LocallyPolygonal.lean`, reproved in the strengthened form. The geometry
is unchanged — `Plane.exists_radius_sides` still does all the work — because the pieces the
old proof used were already inside the neighbourhood; only the statement moves. -/

/-- **The one-square case of brick B5, strengthened.** The complement of an open axis-parallel
square is polygonally connected near every point of the plane, by paths confined to the
neighbourhood. -/
theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

/-- **Brick B5, strengthened.** The plane minus finitely many open axis-parallel squares whose
closed squares are pairwise disjoint is locally polygonally connected, with the connecting
paths confined to the neighbourhood.

The two cases are unchanged. Away from all the closed squares a small square about `p` lies
inside `M` outright. Otherwise `p` lies in exactly one closed square, and a small enough square
about `p` misses all the others, so near `p` the set `M` *is* the complement of that one open
square — which is what `IsLocallyPolyConnAt'.congr_nhds` says suffices. -/
theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc

-- A machine check that the strengthened form subsumes the original brick B5: this typechecks
-- only if the two statements line up on the nose.
example {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) :=
  (isLocallyPolyConn'_compl_biUnion hQ ρ hdisj).weaken

example (c : Plane) (r : ℝ) (p : Plane) : IsLocallyPolyConnAt (openSquare c r)ᶜ p :=
  (isLocallyPolyConnAt'_compl_openSquare c r p).weaken

/-! ### Shrinkability

The point of the strengthening. `IsLocallyPolyConn` does **not** have this property: it holds
for any polygonally connected `S` with `U = univ`, and the comb space — the segments
`{0} × [0,1]`, `{1/n} × [0,1]` and `[0,1] × {0}` — is polygonally connected while its
intersection with a thin open strip about `y = 1` is not locally polygonally connected at
`(0,1)`. -/

/-- **Shrinkability.** A relatively open piece of a locally polygonally connected set is
locally polygonally connected. Taking the neighbourhood inside `W` is what makes this work,
and it is the reason `IsLocallyPolyConnAt'` quantifies over all open `W ∋ p`. -/
theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

/-! ### Relatively open subsets and their components -/

/-- `A` is relatively open in `S`: cut out of `S` by an ambient open set. -/
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

theorem IsRelOpenIn.subset (h : IsRelOpenIn S A) : A ⊆ S := by
  obtain ⟨W, -, rfl⟩ := h
  exact inter_subset_left

theorem isRelOpenIn_self (S : Set Plane) : IsRelOpenIn S S :=
  ⟨univ, isOpen_univ, (inter_univ S).symm⟩

theorem IsOpen.isRelOpenIn (hA : IsOpen A) (hAS : A ⊆ S) : IsRelOpenIn S A :=
  ⟨A, hA, (inter_eq_self_of_subset_right hAS).symm⟩

/-- The shape `isRelOpen_of_polyReaches_stable` delivers, read as relative openness. -/
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

/-- Relative openness is transitive, which is how a component of a relatively open piece is
seen to be relatively open in the ambient set. -/
theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

/-- Shrinkability, phrased for a relatively open piece. -/
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

/-- **Components of relatively open subsets are relatively open.** For `S` locally polygonally
connected and `A` relatively open in `S`, each connected component of `A` is relatively open
in `S`.

The proof is `isRelOpen_of_polyReaches_stable`: a polygonal path inside `A` is a connected
subset of `A`, so it cannot leave the component it starts in, which is exactly the stability
that lemma asks for. -/
theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  -- The polygon carrying the path is connected, lies in `A` and starts at `w`.
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

/-- A component of a relatively open piece is itself locally polygonally connected, so the
whole interface applies again one level down. -/
theorem isLocallyPolyConn'_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsLocallyPolyConn' (connectedComponentIn A x) :=
  h.of_isRelOpenIn (isRelOpenIn_connectedComponentIn h hA x)

/-! ### The payoff -/

/-- **What brick B7 uses.** In a locally polygonally connected `S`, any two points of a
connected relatively open subset are joined by a polygonal path *inside that subset*. -/
theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

/-- The same, as a vertex list. -/
theorem exists_poly_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y :=
  (polyReaches_of_isPreconnected_of_isRelOpenIn h hC hconn hx hy).exists_poly

/-- The component form, which is how `U_e` arises: a component of a relatively open piece is
both relatively open and polygonally connected in itself. -/
theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies

end BundlePart385
