module
import verification.internal.checkpoint
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Separation.Hausdorff

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityObserverCover.lean -/







@[expose] public section

/-!
# Component observers without choosing code coordinates

Keep every original scalar functional as a coordinate. Closing an
observer's seed set under the scalar-identification graph does not
change its linear span. An exceptional component with exactly one
observer contributes at most one extra unit of rank. Linear Shearer
then gives precisely the inequality used in Proposition 6.6, while
allowing arbitrary linear relations between components.
-/

noncomputable section
namespace Papers.Rigidity.ObserverCover

open scoped Classical BigOperators

variable {I A M : Type*} [Fintype I] [Fintype A]
  [AddCommGroup M] [Module ℝ M] [Module.Finite ℝ M]

def line (forms : I → M) (i : I) : Submodule ℝ M := ℝ ∙ forms i

theorem line_eq_of_reachable
    (H : SimpleGraph I) (forms : I → M)
    (hedge : ∀ i j, H.Adj i j → line forms i = line forms j)
    {i j : I} (hij : H.Reachable i j) : line forms i = line forms j := by
  obtain ⟨w⟩ := hij
  induction w with
  | nil => rfl
  | @cons i j k hij w ih => exact (hedge i j hij).trans ih

/-- The coordinates in all components touched by the seed. -/
def closure (H : SimpleGraph I) (S : Finset I) : Finset I :=
  Finset.univ.filter fun i => ∃ j ∈ S, H.Reachable i j

theorem mem_closure (H : SimpleGraph I) (S : Finset I) (i : I) :
    i ∈ closure H S ↔ ∃ j ∈ S, H.Reachable i j := by
  simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subset_closure (H : SimpleGraph I) (S : Finset I) : S ⊆ closure H S := by
  intro i hi
  exact (mem_closure H S i).mpr ⟨i,hi,SimpleGraph.Reachable.rfl⟩

/-- Propagating scalar identifications does not increase the observer
rank. This includes all relations already present between components. -/
theorem span_closure
    (H : SimpleGraph I) (forms : I → M)
    (hedge : ∀ i j, H.Adj i j → line forms i = line forms j) (S : Finset I) :
    Submodule.span ℝ (forms '' (closure H S : Set I)) =
      Submodule.span ℝ (forms '' (S : Set I)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hij⟩ := (mem_closure H S i).mp hi
    have hm : forms i ∈ line forms j := by
      rw [← line_eq_of_reachable H forms hedge hij]
      exact Submodule.subset_span (Set.mem_singleton _)
    apply Submodule.span_mono (show {forms j} ⊆ forms '' (S : Set I) from ?_) hm
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨j,hj,hz.symm⟩
  · exact Submodule.span_mono (Set.image_mono (subset_closure H S))

theorem observerRank_closure
    (H : SimpleGraph I) (forms : I → M)
    (hedge : ∀ i j, H.Adj i j → line forms i = line forms j) (S : Finset I) :
    LinearCover.observerRank (K := ℝ) forms (closure H S) =
      LinearCover.observerRank (K := ℝ) forms S := by
  unfold LinearCover.observerRank
  rw [span_closure H forms hedge S]

def componentVertices (H : SimpleGraph I) (c : H.ConnectedComponent) : Finset I :=
  c.supp.toFinset

theorem mem_componentVertices (H : SimpleGraph I) (c : H.ConnectedComponent) (i : I) :
    i ∈ componentVertices H c ↔ H.connectedComponentMk i = c := by
  simp only [componentVertices, Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem component_rank_le_one
    (H : SimpleGraph I) (forms : I → M)
    (hedge : ∀ i j, H.Adj i j → line forms i = line forms j)
    (c : H.ConnectedComponent) :
    LinearCover.observerRank (K := ℝ) forms (componentVertices H c) ≤ 1 := by
  obtain ⟨i,hi⟩ := c.exists_rep
  have hspan : Submodule.span ℝ (forms '' (componentVertices H c : Set I)) = line forms i := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨j,hj,rfl⟩
      have heq : H.connectedComponentMk j = H.connectedComponentMk i :=
        ((mem_componentVertices H c j).mp hj).trans hi.symm
      rw [← line_eq_of_reachable H forms hedge (SimpleGraph.ConnectedComponent.exact heq)]
      exact Submodule.subset_span (Set.mem_singleton _)
    · apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span ⟨i,(mem_componentVertices H c i).mpr hi,rfl⟩
  unfold LinearCover.observerRank
  rw [hspan]
  exact finrank_span_le_card ({forms i} : Set M)

/-- Actual seed observers which touch the given component. -/
def observers (H : SimpleGraph I) (seed : A → Finset I) (c : H.ConnectedComponent) : Finset A :=
  Finset.univ.filter fun a => ∃ i ∈ seed a, H.connectedComponentMk i = c

theorem mem_observers_iff_closure
    (H : SimpleGraph I) (seed : A → Finset I) (a : A) (i : I) :
    a ∈ observers H seed (H.connectedComponentMk i) ↔ i ∈ closure H (seed a) := by
  simp only [observers, Finset.mem_filter, Finset.mem_univ, true_and, mem_closure]
  constructor
  · rintro ⟨j,hj,heq⟩
    exact ⟨j,hj,SimpleGraph.ConnectedComponent.exact heq.symm⟩
  · rintro ⟨j,hj,hreach⟩
    exact ⟨j,hj,(SimpleGraph.ConnectedComponent.sound hreach).symm⟩

abbrev ExceptionalComponent (H : SimpleGraph I) (seed : A → Finset I) :=
  {c : H.ConnectedComponent // (observers H seed c).card = 1}

def exceptionalCount (H : SimpleGraph I) (seed : A → Finset I) : ℕ :=
  Nat.card (ExceptionalComponent H seed)

/-- The component form of Proposition 6.6. The only covering premise is
that every component really meets an observer. The added cost counts
precisely the components with one observer, and no coordinate
independence is assumed. -/
theorem rank_bound_with_exceptional_components
    (H : SimpleGraph I) (forms : I → M) (seed : A → Finset I)
    (hedge : ∀ i j, H.Adj i j → line forms i = line forms j)
    (hseen : ∀ c : H.ConnectedComponent, (observers H seed c).Nonempty) :
    2 * Module.finrank ℝ (Submodule.span ℝ (Set.range forms)) ≤
      (∑ a : A, LinearCover.observerRank (K := ℝ) forms (seed a)) +
        exceptionalCount H seed := by
  letI : Fintype (ExceptionalComponent H seed) := Fintype.ofFinite _
  let augmented : A ⊕ ExceptionalComponent H seed → Finset I :=
    Sum.elim (fun a => closure H (seed a)) (fun c => componentVertices H c.val)
  have hcover : ∀ i : I,
      2 ≤ (Finset.univ.filter fun a => i ∈ augmented a).card := by
    intro i
    let c := H.connectedComponentMk i
    have hpos := Finset.card_pos.mpr (hseen c)
    by_cases hmany : 1 < (observers H seed c).card
    · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hmany
      apply Finset.Nontrivial.two_le_card
      refine ⟨Sum.inl a, ?_, Sum.inl b, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_observers_iff_closure H seed a i).mp ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_observers_iff_closure H seed b i).mp hb⟩
      · exact fun h => hab (Sum.inl.inj h)
    · have hc : (observers H seed c).card = 1 := by omega
      obtain ⟨a,ha⟩ := hseen c
      let e : ExceptionalComponent H seed := ⟨c,hc⟩
      apply Finset.Nontrivial.two_le_card
      refine ⟨Sum.inl a, ?_, Sum.inr e, ?_, Sum.inl_ne_inr⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_observers_iff_closure H seed a i).mp ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_componentVertices H c i).mpr rfl⟩
  have h := LinearCover.rank_twoCover (K := ℝ) forms augmented hcover
  rw [Fintype.sum_sum_type] at h
  have hleft : (∑ a : A, LinearCover.observerRank (K := ℝ) forms (augmented (Sum.inl a))) =
      ∑ a : A, LinearCover.observerRank (K := ℝ) forms (seed a) := by
    apply Finset.sum_congr rfl
    intro a _
    exact observerRank_closure H forms hedge (seed a)
  have hright : (∑ c : ExceptionalComponent H seed,
      LinearCover.observerRank (K := ℝ) forms (augmented (Sum.inr c))) ≤
        exceptionalCount H seed := by
    calc
      _ ≤ ∑ _c : ExceptionalComponent H seed, 1 :=
        Finset.sum_le_sum (fun c _ => component_rank_le_one H forms hedge c.val)
      _ = exceptionalCount H seed := by simp [exceptionalCount, Nat.card_eq_fintype_card]
  rw [hleft] at h
  exact h.trans (Nat.add_le_add_left hright _)

end Papers.Rigidity.ObserverCover

end
end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0001/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityMeasuredModes.lean -/




@[expose] public section

/-!
# Removing locally readable modes from a measured image

Biorthogonal actual modes remove exactly one image dimension for each
mode that can be read from the measurement. The remaining modes have
zero measurement. A descended coefficient map and rank-nullity prove
the identity; no dimension or independence of image vectors is assumed.
-/

noncomputable section
namespace Papers.Rigidity.ModeSplitting
open scoped Classical BigOperators
variable {K M N I : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Module.Finite K M] [AddCommGroup N] [Module K N] [Fintype I]

theorem measured_nullModes_finrank (f : M →ₗ[K] N)
    (ρ : I → M →ₗ[K] K) (s : I → M) (A : Finset I)
    (hdual : ∀ i j, ρ i (s j) = if i = j then 1 else 0)
    (hread : ∀ i ∈ A, ∀ x, f x = 0 → ρ i x = 0)
    (hinvisible : ∀ i ∉ A, f (s i) = 0) :
    Module.finrank K (f.domRestrict (nullModes ρ)).range + A.card =
      Module.finrank K f.range := by
  let g : M →ₗ[K] (A → K) := LinearMap.pi (fun i => ρ i.val)
  have hsurj : Function.Surjective f.rangeRestrict := by
    intro y
    obtain ⟨x,hx⟩ := y.property
    exact ⟨x,Subtype.ext hx⟩
  have hker : f.rangeRestrict.ker ≤ g.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext i
    exact hread i.val i.property x
      (congrArg Subtype.val (LinearMap.mem_ker.mp hx))
  let Λ : f.range →ₗ[K] (A → K) :=
    f.rangeRestrict.liftOfSurjective hsurj ⟨g,hker⟩
  have hΛ (x : M) : Λ (f.rangeRestrict x) = g x :=
    LinearMap.equivOfSurjective_apply _ _
  have hΛsurj : Function.Surjective Λ := by
    intro c
    let x : M := ∑ j : A, c j • s j.val
    refine ⟨f.rangeRestrict x,?_⟩
    rw [hΛ]
    ext i
    simp [g,x,hdual]
  have himage : Λ.ker.map f.range.subtype =
      (f.domRestrict (nullModes ρ)).range := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨x,hx⟩ := hsurj a
      have hzero : g x = 0 := by
        rw [← hΛ,hx]
        exact LinearMap.mem_ker.mp ha
      let z : M := x - ∑ i : I, ρ i x • s i
      have hz : z ∈ nullModes ρ := by
        intro i
        simp [z,hdual]
      have hfz : f z = f x := by
        have hsum : (∑ i : I, ρ i x • f (s i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          by_cases hi : i ∈ A
          · have hρ : ρ i x = 0 := congrFun hzero ⟨i,hi⟩
            simp [hρ]
          · simp [hinvisible i hi]
        simp only [z,map_sub,map_sum,map_smul,hsum,sub_zero]
      exact ⟨⟨z,hz⟩,hfz.trans (congrArg Subtype.val hx)⟩
    · rintro ⟨z,rfl⟩
      refine ⟨f.rangeRestrict z.val,?_,rfl⟩
      change Λ (f.rangeRestrict z.val) = 0
      rw [hΛ]
      ext i
      exact z.property i.val
  have hdim := Λ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hΛsurj,finrank_top] at hdim
  have hk := Submodule.finrank_map_subtype_eq f.range Λ.ker
  rw [himage] at hk
  have hcard : Module.finrank K (A → K) = A.card := by
    simp
  rw [hcard] at hdim
  omega

end Papers.Rigidity.ModeSplitting

end
end
end BundleSource0002

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0002/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0002.json"

section BundleSource0003
/- Source: Papers/RigidityAnnihilatorRank.lean -/





@[expose] public section

/-!
# How scalar constraints reduce a measured image

For an actual measurement map `f`, imposing the common kernel of `U`
removes exactly the dimension of the functionals in `U` that can already
be read from `f`.  This is the star-image identity used in Section 7.2.
-/

noncomputable section
namespace Papers.Rigidity.AnnihilatorRank

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Module.Finite K E] [AddCommGroup F] [Module K F]

def restrictionKernelEquiv (f : E →ₗ[K] F) (A : Submodule K E) :
    (f.domRestrict A).ker ≃ₗ[K] ↥(A ⊓ f.ker) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_restricted_image_add_kernel (f : E →ₗ[K] F) (A : Submodule K E) :
    Module.finrank K (f.domRestrict A).range +
      Module.finrank K ↥(A ⊓ f.ker) = Module.finrank K A := by
  have h := (f.domRestrict A).finrank_range_add_finrank_ker
  rw [(restrictionKernelEquiv f A).finrank_eq] at h
  exact h

/-- The readable functionals are precisely those vanishing on the
measurement kernel.  This is an intrinsic description of the dual row
space and does not require a choice of coordinates in the target. -/
def readable (f : E →ₗ[K] F) : Submodule K (Module.Dual K E) :=
  f.ker.dualAnnihilator

theorem finrank_readable (f : E →ₗ[K] F) :
    Module.finrank K (readable f) = Module.finrank K f.range := by
  have h := f.finrank_range_add_finrank_ker
  have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq f.ker
  change Module.finrank K f.ker + Module.finrank K (readable f) =
    Module.finrank K E at hdual
  omega

/-- Exact rank loss in an image when the scalar functionals `U` are
set to zero.  Neither side is introduced by a dimension prescription. -/
theorem finrank_restrict_coannihilator (f : E →ₗ[K] F)
    (U : Submodule K (Module.Dual K E)) :
    Module.finrank K (f.domRestrict U.dualCoannihilator).range +
      Module.finrank K ↥(U ⊓ readable f) = Module.finrank K f.range := by
  have hrest := finrank_restricted_image_add_kernel f U.dualCoannihilator
  have hU := Subspace.finrank_add_finrank_dualCoannihilator_eq U
  have hUL := Subspace.finrank_add_finrank_dualCoannihilator_eq (U ⊔ readable f)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (readable f)
  have hcoann : (U ⊔ readable f).dualCoannihilator = U.dualCoannihilator ⊓ f.ker := by
    rw [Submodule.dualCoannihilator_sup_eq, readable,
      Subspace.dualAnnihilator_dualCoannihilator_eq]
  rw [hcoann] at hUL
  rw [finrank_readable] at hsum
  omega

end Papers.Rigidity.AnnihilatorRank

end
end
end BundleSource0003

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0003/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0003.json"

section BundleSource0004
/- Source: Papers/RigidityLaman_Mathlib_Data_Set_Card.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Set/Card.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidates: small `Set.ncard` lemmas

The Lean namespace is the upstream one (`Set`), so promotion to mathlib is a
copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Set/Card.lean`)

* `Set.ncard_pair_le` — `({a, b} : Set α).ncard ≤ 2`. Unconditional companion
  to `Set.ncard_pair` (which gives `= 2` under `a ≠ b`); collapses the
  `ncard_insert_le` + `ncard_singleton` boilerplate when bounding the
  cardinality of a literal pair without first ruling out collisions.
* `Set.ncard_triple_le` — `({a, b, c} : Set α).ncard ≤ 3`. Same pattern,
  one level deeper.
* `Set.ncard_eq_card_coe` — `s.ncard = Fintype.card s` under `[Fintype s]`.
  Bridges `Set.ncard` to the `Fintype.card`-based dimension lemmas
  (`Module.finrank_pi`, `LinearMap.toMatrix`) without the
  `Set.ncard_eq_toFinset_card'` / `Set.toFinset_card` two-step rewrite.
* `Set.exists_injective_fin_of_le_ncard` — from `n ≤ s.ncard`, index `n`
  distinct elements of `s` by `Fin n`. Companion to `Set.exists_subset_card_eq`
  (which returns the subset); collapses the `exists_subset_card_eq` →
  `Set.Finite.fintype` → `Set.ncard_eq_toFinset_card'` /
  `Set.toFinset_card` → `Fintype.equivFinOfCardEq` chain.
* `Set.ncard_union_range_of_injective` — adding `k` new elements, listed injectively by
  `Fin k`, adds `k` to the cardinality: `(s ∪ range z).ncard = s.ncard + k`. Fuses
  `Set.ncard_union_eq`, the disjointness of `s` and `range z`, `Set.ncard_range_of_injective`
  and `Nat.card_fin`. The combinatorial-rigidity project uses it to count the bodies of an ear
  or of a chain of bridges in `Molecular/Molecule/Pencil/MainComponent/` (`Cut.lean`,
  `Ear.lean`, `Short.lean`, `Orbit.lean`, `SplitOff.lean`).
-/

@[expose] public section

namespace Set

variable {α : Type*}

/-- An unconditional bound for the cardinality of a literal pair: it is at most `2`
regardless of whether `a = b`. The companion `Set.ncard_pair` gives the exact `= 2`
under `a ≠ b`. -/
theorem ncard_pair_le (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (ncard_insert_le _ _).trans (by rw [ncard_singleton])

/-- An unconditional bound for the cardinality of a literal triple: it is at most `3`
regardless of any equalities among `a, b, c`. -/
theorem ncard_triple_le (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 :=
  (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_pair_le _ _) _)

/-- A direct bridge between `Set.ncard` and `Fintype.card`: `s.ncard = Fintype.card ↥s`
under `[Fintype s]`. The `Set.ncard_eq_toFinset_card'` (`s.ncard = s.toFinset.card`) +
`Set.toFinset_card` (`s.toFinset.card = Fintype.card s`) two-step rewrite collapses to
this one lemma. -/
theorem ncard_eq_card_coe (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- From `n ≤ s.ncard`, index `n` distinct elements of `s` by `Fin n`. Companion to
`Set.exists_subset_card_eq`: that lemma returns the size-`n` subset; this one returns
the `Fin n`-indexing of its elements. -/
theorem exists_injective_fin_of_le_ncard {s : Set α} {n : ℕ} (hns : n ≤ s.ncard) :
    ∃ q : Fin n → α, Function.Injective q ∧ ∀ i, q i ∈ s := by
  obtain ⟨t, hts, hcard⟩ := Set.exists_subset_card_eq hns
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · have ht_fin : t.Finite := Set.finite_of_ncard_pos (hcard ▸ hn)
    have : Fintype t := ht_fin.fintype
    have h_card_eq : Fintype.card t = n := (Set.ncard_eq_card_coe t).symm.trans hcard
    let e : Fin n ≃ t := (Fintype.equivFinOfCardEq h_card_eq).symm
    exact ⟨fun i => (e i).val, fun _ _ hij => e.injective (Subtype.ext hij),
      fun i => hts (e i).property⟩

/-- Adding `k` new elements, listed injectively by `Fin k`, to a finite set adds `k` to its
cardinality: `s` and `range z` are disjoint, and `range z` has `k` elements. -/
theorem ncard_union_range_of_injective {s : Set α} {k : ℕ} {z : Fin k → α}
    (hz : Function.Injective z) (hzs : ∀ i, z i ∉ s) (hs : s.Finite := by toFinite_tac) :
    (s ∪ range z).ncard = s.ncard + k := by
  rw [ncard_union_eq (disjoint_right.mpr (forall_mem_range.mpr hzs)) hs
    (image_univ (f := z) ▸ finite_univ.image z), ncard_range_of_injective hz, Nat.card_fin]

end Set


end
end BundleSource0004

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0004/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0004.json"

section BundleSource0005
/- Source: Papers/RigidityLaman_Mathlib_Combinatorics_SimpleGraph_Finite.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Combinatorics/SimpleGraph/Finite.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/




/-!
# Upstream candidates: `Set.ncard` companions for `SimpleGraph` cardinality lemmas

Mathlib has `Fintype.card` / `Finset.card`-flavored equalities for
`SimpleGraph.edgeSet`, `SimpleGraph.incidenceSet`, and the complete graph in
`Mathlib/Combinatorics/SimpleGraph/Finite.lean`. The lemmas below are the
`Set.ncard` companions that the combinatorial-rigidity project repeatedly
needs, plus a degree-one uniqueness fact companion to the existing
`degree_eq_one_iff_existsUnique_adj`.

The Lean namespace is the upstream one (`SimpleGraph`), not the project's, so
promotion to mathlib is a copy-paste alongside the existing `card_*_eq_*`
lemmas. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/Finite.lean`)

* `ncard_incidenceSet_eq_degree` — `(G.incidenceSet v).ncard = G.degree v`.
* `ncard_neighborSet_eq_degree` — `(G.neighborSet v).ncard = G.degree v`.
* `ncard_edgeSet_eq_card_edgeFinset` — `G.edgeSet.ncard = G.edgeFinset.card`.
* `ncard_edgeSet_top_eq_card_choose_two` — `(⊤ : SimpleGraph V).edgeSet.ncard
  = (Fintype.card V).choose 2`.
* `eq_of_adj_of_degree_le_one` — a vertex of degree at most one has at most
  one neighbor: any two vertices adjacent to it coincide.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- `Set.ncard` form of `SimpleGraph.card_incidenceSet_eq_degree`. -/
theorem ncard_incidenceSet_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (G.incidenceSet v).ncard = G.degree v := by
  classical
  rw [Set.ncard_eq_card_coe, card_incidenceSet_eq_degree]

/-- `Set.ncard` form of `SimpleGraph.card_neighborSet_eq_degree`. -/
theorem ncard_neighborSet_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (G.neighborSet v).ncard = G.degree v := by
  rw [Set.ncard_eq_card_coe, card_neighborSet_eq_degree]

/-- The `Set.ncard` of `G.edgeSet` agrees with the `Finset.card` of `G.edgeFinset`. Companion of
`SimpleGraph.coe_edgeFinset`. -/
theorem ncard_edgeSet_eq_card_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-- `Set.ncard` form of `SimpleGraph.card_edgeFinset_top_eq_card_choose_two`. -/
theorem ncard_edgeSet_top_eq_card_choose_two [Fintype V] :
    ((⊤ : SimpleGraph V).edgeSet).ncard = (Fintype.card V).choose 2 := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, card_edgeFinset_top_eq_card_choose_two]

/-- A vertex of degree at most one has at most one neighbor: any two vertices adjacent to it
coincide. Companion to `degree_eq_one_iff_existsUnique_adj`, stated for the inequality
hypothesis used when only an upper bound on the degree is in hand (not its exact value). -/
theorem eq_of_adj_of_degree_le_one {G : SimpleGraph V} {v x y : V} [Fintype (G.neighborSet v)]
    (hv : G.degree v ≤ 1) (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  have hdeg : G.degree v = 1 := le_antisymm hv hx.degree_pos_left
  obtain ⟨w, -, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  rw [huniq x hx, huniq y hy]

end SimpleGraph


end
end BundleSource0005

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0005/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0005.json"

section BundleSource0006
/- Source: Papers/RigidityLaman_EdgesIn.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/EdgesIn.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/








/-!
# `edgesIn`: edges with both endpoints in a vertex set

For `G : SimpleGraph V` and `s : Set V`, `G.edgesIn s` is the set of edges
of `G` whose both endpoints lie in `s`. It is the basic selector used by
the sparsity definition (see `Sparsity.lean`).

The closest mathlib analogues are `SimpleGraph.Subgraph.induce` and
`SimpleGraph.induce`, both of which materialize the same content as a
graph rather than a `Set (Sym2 V)`. See `DESIGN.md` for the rationale. The
blueprint presents the file in `sec:edgesIn`, with the edge count of a clique
in `sec:jacobs-laman3`.

## Main definition

* `SimpleGraph.edgesIn G s = G.edgeSet ∩ s.sym2`.

## Main lemmas

* `SimpleGraph.mem_edgesIn` — membership unfolding.
* `SimpleGraph.mk_mem_edgesIn` — specialised pair-form constructor for `mem_edgesIn`.
* `SimpleGraph.edgesIn_subset_edgeSet`, `edgesIn_mono` — basic inclusions.
* `SimpleGraph.edgesIn_univ`, `edgesIn_empty`, `edgesIn_bot` — corner cases.
* `SimpleGraph.edgeSet_fromEdgeSet_of_off_diag`,
  `SimpleGraph.edgesIn_fromEdgeSet_of_off_diag` — for off-diagonal `X`
  (i.e. `X ⊆ ⊤.edgeSet`), `fromEdgeSet X`'s `edgeSet` is already `X`, and
  consequently `(fromEdgeSet X).edgesIn S = X ∩ S.sym2`.
* `SimpleGraph.edgesIn_finite` — finiteness over a finite vertex set.
* `SimpleGraph.mem_edgesIn_compl_singleton`, `edgesIn_compl_singleton` — vertex-deletion
  identities.
* `SimpleGraph.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet` — vertex-deletion
  cardinality identity, used for the minimum degree of a Laman graph
  (`lem:isLaman-two-le-degree`).
* `SimpleGraph.edgesIn_inter` — edges-in distributes over intersection.
* `SimpleGraph.edgesIn_ncard_add_le` — supermodularity of edge counts:
  `(edgesIn S).ncard + (edgesIn T).ncard ≤ (edgesIn (S ∪ T)).ncard + (edgesIn (S ∩ T)).ncard`.
  The edge arithmetic of the closure of tight sets under union (`thm:isTightOn-union-inter`).
* `SimpleGraph.IsClique.ncard_edgesIn` — a clique's edge count: for `X : Finset V` a clique of
  `G`, `(G.edgesIn ↑X).ncard = X.card.choose 2` (`lem:clique-edgesIn-count`), the count of
  Jackson–Jordán's Lemma 5.2.
* `SimpleGraph.edgesIn_eq_edgeSet_of_support_subset` — `G.edgesIn S = G.edgeSet` whenever `S`
  contains every non-isolated vertex of `G`, used in the proof of `thm:jacobs` to restrict to
  the support.
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The set of edges of `G` whose both endpoints lie in `s` (`def:edgesIn`). -/
@[expose] def edgesIn (s : Set V) : Set (Sym2 V) := G.edgeSet ∩ s.sym2

variable {G}

@[simp] lemma mem_edgesIn {e : Sym2 V} {s : Set V} :
    e ∈ G.edgesIn s ↔ e ∈ G.edgeSet ∧ (e : Set V) ⊆ s := by
  rw [edgesIn, Set.mem_inter_iff, Set.mem_sym2_iff_subset]

/-- Specialised constructor for `mem_edgesIn` at an explicit pair `s(x, y)`: an adjacent pair with
both endpoints in `s` lies in `G.edgesIn s`. Replaces the term `mem_edgesIn.mpr ⟨_, by …⟩`, with
its rewrites by `Sym2.coe_mk`, `Set.insert_subset_iff` and `Set.singleton_subset_iff`, that recurs
across the project's proofs. -/
lemma mk_mem_edgesIn {x y : V} {s : Set V} (h : G.Adj x y) (hx : x ∈ s) (hy : y ∈ s) :
    s(x, y) ∈ G.edgesIn s :=
  mem_edgesIn.mpr ⟨h, by
    rw [Sym2.coe_mk]
    exact Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩⟩

/-- Companion to `mk_mem_edgesIn`: an edge `s(x, y)` whose **left** endpoint lies outside `s`
cannot lie in `G.edgesIn s`. -/
lemma notMem_edgesIn_mk_of_left_notMem {x y : V} {s : Set V} (hxs : x ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hxs (hmem.2 (Set.mem_insert _ _))

/-- Companion to `mk_mem_edgesIn`: an edge `s(x, y)` whose **right** endpoint lies outside `s`
cannot lie in `G.edgesIn s`. -/
lemma notMem_edgesIn_mk_of_right_notMem {x y : V} {s : Set V} (hys : y ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hys (hmem.2 (Set.mem_insert_of_mem _ rfl))

lemma edgesIn_subset_edgeSet (s : Set V) : G.edgesIn s ⊆ G.edgeSet :=
  Set.inter_subset_left

@[gcongr]
lemma edgesIn_mono {s t : Set V} (h : s ⊆ t) : G.edgesIn s ⊆ G.edgesIn t :=
  fun _ ⟨he₁, he₂⟩ ↦ ⟨he₁, (Set.mem_sym2_iff_subset.mp he₂).trans h |> Set.mem_sym2_iff_subset.mpr⟩

@[simp] lemma edgesIn_univ : G.edgesIn Set.univ = G.edgeSet := by
  simp [edgesIn]

@[simp] lemma edgesIn_empty : G.edgesIn (∅ : Set V) = ∅ := by
  simp [edgesIn]

@[simp] lemma edgesIn_bot (s : Set V) : (⊥ : SimpleGraph V).edgesIn s = ∅ := by
  simp [edgesIn]

/-- For an off-diagonal edge set `X` (i.e. `X ⊆ ⊤.edgeSet`), `fromEdgeSet X` already
has `X` as its edge set — no `sdiff Sym2.diagSet` to clear. -/
lemma edgeSet_fromEdgeSet_of_off_diag {X : Set (Sym2 V)}
    (hX : X ⊆ (⊤ : SimpleGraph V).edgeSet) : (fromEdgeSet X).edgeSet = X := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  intro e he_X he_diag
  exact (edgeSet_top (V := V) ▸ hX he_X) he_diag

/-- Combined `edgesIn` + off-diagonal `fromEdgeSet` simplification: for `X ⊆ ⊤.edgeSet`,
`(fromEdgeSet X).edgesIn S = X ∩ S.sym2`. Composes `edgeSet_fromEdgeSet_of_off_diag` with
the definition of `edgesIn`. -/
lemma edgesIn_fromEdgeSet_of_off_diag {X : Set (Sym2 V)}
    (hX : X ⊆ (⊤ : SimpleGraph V).edgeSet) (S : Set V) :
    (fromEdgeSet X).edgesIn S = X ∩ S.sym2 := by
  unfold edgesIn
  rw [edgeSet_fromEdgeSet_of_off_diag hX]

/-- A singleton set spans no edges (`lem:edgesIn-corners`): a single vertex contains no edge of a
simple graph because edges are non-loops. -/
@[simp] lemma edgesIn_singleton (G : SimpleGraph V) (v : V) : G.edgesIn ({v} : Set V) = ∅ := by
  ext e
  refine e.ind fun x y => ?_
  simp only [mem_edgesIn, mem_edgeSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hadj hsub
  have hx : x = v := hsub (Sym2.mem_mk_left x y)
  have hy : y = v := hsub (Sym2.mem_mk_right x y)
  rw [hx, hy] at hadj
  exact G.loopless.irrefl _ hadj

/-- For finite `s`, `G.edgesIn ↑s` is finite (it is contained in the symmetric square of `s`). -/
lemma edgesIn_finite (G : SimpleGraph V) (s : Finset V) : (G.edgesIn ↑s).Finite := by
  refine s.sym2.finite_toSet.subset ?_
  rw [Finset.coe_sym2]
  exact Set.inter_subset_right

/-- Edges of `G` with both endpoints in `S` are exactly the `Sym2.map Subtype.val`-image of the
edges of the induced subgraph `G.induce S` on `S`. The bridge between our `edgesIn` selector
(stated in `Sym2 V`) and mathlib's `SimpleGraph.induce` (whose edges live in `Sym2 ↥S`). -/
lemma edgesIn_eq_image_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    G.edgesIn S = Sym2.map (Subtype.val : ↥S → V) '' (G.induce S).edgeSet := by
  ext e
  simp only [mem_edgesIn, Set.mem_image]
  refine ⟨fun ⟨he_adj, he_sub⟩ => ?_, ?_⟩
  · induction e with | h u v =>
      rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff] at he_sub
      exact ⟨s(⟨u, he_sub.1⟩, ⟨v, he_sub.2⟩), he_adj, rfl⟩
  · rintro ⟨e', he', rfl⟩
    refine e'.ind (fun u v he' => ?_) he'
    refine ⟨he', ?_⟩
    rw [Sym2.map_mk, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨u.2, v.2⟩

/-- Cardinality bridge: edges in `S` and edges of the induced subgraph have the same count.
Follows from `edgesIn_eq_image_induce_edgeSet` and injectivity of `Sym2.map Subtype.val`. -/
lemma ncard_edgesIn_eq_ncard_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    (G.edgesIn S).ncard = (G.induce S).edgeSet.ncard := by
  rw [edgesIn_eq_image_induce_edgeSet,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

/-- **A set containing the support spans every edge.** If `S` contains every non-isolated vertex
of `G`, every edge of `G` has both endpoints in `S`: `G.edgesIn S = G.edgeSet`. The extension of
`edgesIn_univ` from the universal set to any set containing the support. With
`edgesIn_eq_image_induce_edgeSet` it identifies, in the proof of `thm:jacobs`, the image of the
edge set of `G` restricted to its support with the edge set of `G`. -/
lemma edgesIn_eq_edgeSet_of_support_subset {S : Set V} (hS : G.support ⊆ S) :
    G.edgesIn S = G.edgeSet := by
  refine Set.eq_of_subset_of_subset (edgesIn_subset_edgeSet S) fun e he => ?_
  refine mem_edgesIn.mpr ⟨he, ?_⟩
  induction e with
  | h x y =>
    rw [mem_edgeSet] at he
    rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hS he.left_mem_support, hS he.right_mem_support⟩

/-! ### Vertex deletion: edges avoiding a vertex

Edges of `G` whose both endpoints differ from `v` are exactly the edges of `G` that are not
incident to `v`. This relates `edgesIn` and `incidenceSet`, for the edge counts of vertex
deletion (`lem:mem-edgesIn-compl-singleton`, `lem:ncard-edgesIn-compl-singleton`). -/

lemma mem_edgesIn_compl_singleton {v : V} {e : Sym2 V} :
    e ∈ G.edgesIn ({v}ᶜ : Set V) ↔ e ∈ G.edgeSet ∧ v ∉ e := by
  rw [mem_edgesIn, Set.subset_compl_singleton_iff]
  rfl

/-- Edges with both endpoints in `{v}ᶜ` are precisely the edges not incident to `v`
(`lem:mem-edgesIn-compl-singleton`). -/
lemma edgesIn_compl_singleton (v : V) :
    G.edgesIn ({v}ᶜ : Set V) = G.edgeSet \ G.incidenceSet v := by
  ext e
  grind [mem_edgesIn_compl_singleton, incidenceSet]

/-- Edges of `G` partition into "not incident to `v`" plus "incident to `v`": the cardinality
identity `#(edgesIn {v}ᶜ) + #(incidenceSet v) = #edgeSet` (`lem:ncard-edgesIn-compl-singleton`),
the edge count of vertex deletion. -/
lemma ncard_edgesIn_compl_singleton_add_ncard_incidenceSet [Finite V] (v : V) :
    (G.edgesIn ({v}ᶜ : Set V)).ncard + (G.incidenceSet v).ncard = G.edgeSet.ncard := by
  rw [edgesIn_compl_singleton]
  exact Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v) G.edgeSet.toFinite

/-! ### Modularity: edges-in on the intersection / union lattice

`edgesIn` distributes exactly over set-intersection but only sub-distributes over union —
an edge `{x, y}` with `x ∈ S \ T` and `y ∈ T \ S` lies in `edgesIn (S ∪ T)` but in neither
`edgesIn S` nor `edgesIn T`. The cardinality consequence is the "supermodular edge count"
inequality `edgesIn_ncard_add_le`, the only edge arithmetic of the closure of tight sets under
union (`thm:isTightOn-union-inter`). -/

/-- `edgesIn` distributes over intersection (`lem:edgesIn-inter`):
`G.edgesIn (S ∩ T) = G.edgesIn S ∩ G.edgesIn T`.
The companion union direction is only an inclusion (cf. `edgesIn_ncard_add_le`). -/
lemma edgesIn_inter (S T : Set V) :
    G.edgesIn (S ∩ T) = G.edgesIn S ∩ G.edgesIn T := by
  ext e
  simp only [Set.mem_inter_iff, mem_edgesIn, Set.subset_inter_iff]
  tauto

/-- **Supermodularity of `edgesIn` counts** (`lem:edgesIn-ncard-add-le`). For any two vertex sets
`S, T`, the sum `(edgesIn S).ncard + (edgesIn T).ncard` is at most
`(edgesIn (S ∪ T)).ncard + (edgesIn (S ∩ T)).ncard`. The "edges crossing `S \ T` to `T \ S`" are
counted on the right but not on the left, so the inequality can be strict; intersection cancels via
`edgesIn_inter`. The lift of `Set.ncard_union_add_ncard_inter` to `edgesIn`. -/
lemma edgesIn_ncard_add_le [Finite V] (S T : Set V) :
    (G.edgesIn S).ncard + (G.edgesIn T).ncard ≤
      (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard := by
  have h_union : G.edgesIn S ∪ G.edgesIn T ⊆ G.edgesIn (S ∪ T) :=
    Set.union_subset (edgesIn_mono Set.subset_union_left)
                     (edgesIn_mono Set.subset_union_right)
  calc (G.edgesIn S).ncard + (G.edgesIn T).ncard
      = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn S ∩ G.edgesIn T).ncard :=
        (Set.ncard_union_add_ncard_inter _ _).symm
    _ = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn (S ∩ T)).ncard := by
        rw [← edgesIn_inter]
    _ ≤ (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard :=
        Nat.add_le_add_right (Set.ncard_le_ncard h_union) _

/-! ### Cliques

The edges induced on a clique are exactly the two-element subsets of it: transport
`edgesIn` to the induced subgraph (`ncard_edgesIn_eq_ncard_induce_edgeSet`), which is
complete on a clique (`induce_eq_top`), and count the complete graph's edges
(`ncard_edgeSet_top_eq_card_choose_two`). -/

/-- A clique's edge count (`lem:clique-edgesIn-count`): if `X : Finset V` is a clique of `G`
(every two distinct vertices of `X` adjacent), the edges of `G` inside `X` number exactly
`C(#X, 2)`. -/
theorem IsClique.ncard_edgesIn {X : Finset V} (h : G.IsClique (↑X : Set V)) :
    (G.edgesIn (↑X : Set V)).ncard = X.card.choose 2 := by
  classical
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet, induce_eq_top.mpr h,
    ncard_edgeSet_top_eq_card_choose_two]
  simp

end SimpleGraph


end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0006/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityLaman_Mathlib_Data_Finset_Card.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Finset/Card.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/




/-!
# Mirror file: `Mathlib/Data/Finset/Card.lean`

Upstream-eligible lemmas about `Finset.card`. See `DESIGN.md`
*Mirror directory* for the project convention.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

/-- If a finset has cardinality at most one and contains a given element, it is the singleton
of that element.

The dual reading of `Finset.card_le_one_iff`: the `≤ 1` cardinality bound *plus* a witnessing
element collapse to a singleton equality. -/
lemma eq_singleton_of_mem_of_card_le_one {s : Finset α} {z : α}
    (hz : z ∈ s) (h : s.card ≤ 1) : s = {z} :=
  (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hz)
    (h.trans_eq (Finset.card_singleton z).symm)).symm

/-- The `k`-scaled form of `Finset.card_union_add_card_inter`: multiplying both sides by a
common `Nat` factor distributes through union/intersection-pair cardinalities.

Saves three `rw` rewrites at each call site (`← Nat.mul_add` twice, then
`Finset.card_union_add_card_inter`) — useful when an `IsTightOn`-style accounting needs
to bridge `k * |s| + k * |t|` to `k * |s ∪ t| + k * |s ∩ t|`. -/
lemma mul_card_union_add_mul_card_inter [DecidableEq α] (s t : Finset α) (k : ℕ) :
    k * s.card + k * t.card = k * (s ∪ t).card + k * (s ∩ t).card := by
  rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]

/-- Two finsets of *complementary* cardinality (`|s| + |t| = |α|`) are disjoint exactly
when one is the complement of the other. The forward direction upgrades disjointness to
equality by a cardinality squeeze on `s ⊆ tᶜ`; the converse is immediate from
`Finset.disjoint_compl_right`. -/
lemma disjoint_iff_eq_compl [Fintype α] [DecidableEq α] {s t : Finset α}
    (hcard : s.card + t.card = Fintype.card α) : Disjoint s t ↔ t = sᶜ := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_compl]; exact fun hxS => h hxS hx
    · rw [Finset.card_compl]; omega
  · intro h x hxS hxT; rw [h, Finset.mem_compl] at hxT; exact hxT hxS

/-- Three distinct elements of a finset force its cardinality to be at least three. -/
lemma three_le_card_of_three_distinct_mem {s : Finset α} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : 3 ≤ s.card := by
  classical
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    simp [Finset.card_insert_of_notMem, hab, hac, hbc]
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  exact h3 ▸ Finset.card_le_card hsub

end Finset


end
end BundleSource0007

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0007/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0007.json"

section BundleSource0008
/- Source: Papers/RigidityLaman_Mathlib_Data_Sym_Sym2.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Mathlib/Data/Sym/Sym2.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/



/-!
# Upstream candidates: pointwise reasoning about `Sym2.map f e = s(x, y)`

Mathlib has `Sym2.mem_map` for membership of a single element of `β` in
`Sym2.map f z`, and `Sym2.coe_map` for the underlying-set coercion. What was
missing — and repeatedly needed in the combinatorial-rigidity project — is a
*pointwise* characterization, in terms of `f`-preimages, of the situation
"there is an `e` with property `P` such that `Sym2.map f e` equals a given
pair `s(x, y)`."

The main lemma here is `Sym2.exists_and_map_eq_mk_iff`:

```
(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)
```

This is the form that `simp` reaches automatically: starting from
`s(x, y) ∈ Sym2.map f '' S`, the lemma `Set.mem_image` (a `@[simp]` lemma)
unfolds to `∃ e, e ∈ S ∧ Sym2.map f e = s(x, y)`, after which membership in `S`
may have been further unfolded by other simp lemmas (e.g. `Set.mem_diff` if `S`
is a difference). The predicate-form lemma matches regardless.

We also provide the more direct (non-`@[simp]`) form
`Sym2.mk_mem_image_map_iff`, which talks about image membership before
`Set.mem_image` fires; it is convenient for hand-driven rewriting. The `f =
some` specializations close the loop for the `Option`-vertex extensions used in
this project.

The Lean namespace is the upstream one (`Sym2`), so promotion to mathlib is a
copy-paste alongside `Sym2.mem_map` / `Sym2.coe_map`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Sym/Sym2.lean`)

* `Sym2.exists_and_map_eq_mk_iff` — `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔
  ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`. Tagged `@[simp]`.
* `Sym2.mk_mem_image_map_iff` — image-membership form:
  `s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S`.
* `Sym2.map_some_injective` — `Sym2.map (some : α → Option α)` is injective.
  A common specialization that otherwise reads as
  `Sym2.map.injective (Option.some_injective _)`.
* `Sym2.notMem_map_some` — `none ∉ Sym2.map some e`. Tagged `@[simp]`.
* `Sym2.disjoint_image_map_some` — disjointness packaging: `Sym2.map some '' S`
  is disjoint from any `T` whose elements all contain `none`.
* `Sym2.coe_toFinset` — the `Set`-coercion of `z.toFinset` equals the
  `SetLike` coercion of `z`. Tagged `@[simp]` so `e.toFinset ⊆ C` and
  `(↑e : Set α) ⊆ (↑C : Set α)` interconvert in one rewrite (paired with
  `Finset.coe_subset`).
* `Sym2.mk_none_some_eq_iff` — `s(none, some u) = s(none, some v) ↔ u = v`,
  the pointwise iff for the "fresh edges" `s(none, some _)` of `Option`-vertex
  extensions. Collapses the four-line `Sym2.eq_iff` case-split + `Option.some.inj`
  ceremony at each `s(none, some a) ≠ s(none, some b)` proof.
-/

@[expose] public section

namespace Sym2

variable {α β : Type*}

/-- "Predicate-form" pointwise inverse of `Sym2.map`: a value `s(x, y)` is in
the image of an `e` satisfying `P` iff there is a preimage pair `(p, q)` with
`f p = x`, `f q = y`, and `P s(p, q)`. The asymmetry in `(p, q)` is harmless by
`Sym2.eq_swap`.

This is the form that survives `simp`'s unfolding of `Set.mem_image` and any
further unfolding of the membership predicate (e.g. `Set.mem_diff` for set
differences). Tagged `@[simp]` so image-membership goals close in one pass. -/
@[simp]
lemma exists_and_map_eq_mk_iff {f : α → β} {P : Sym2 α → Prop} {x y : β} :
    (∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q) := by
  constructor
  · rintro ⟨e, hP, hmap⟩
    induction e with | h α' β' => ?_
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmap
    · exact ⟨_, _, rfl, rfl, hP⟩
    · exact ⟨_, _, rfl, rfl, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨p, q, rfl, rfl, hP⟩
    exact ⟨s(p, q), hP, by rw [Sym2.map_mk]⟩

/-- An edge `s(x, y)` lies in `Sym2.map f '' S` iff there is a
preimage pair `(p, q)` with `f p = x`, `f q = y`, and `s(p, q) ∈ S`.

This is the "natural" hand-driven form. The companion `simp`-form
`Sym2.exists_and_map_eq_mk_iff` is what fires inside an automated rewrite. -/
lemma mk_mem_image_map_iff {f : α → β} {S : Set (Sym2 α)} {x y : β} :
    s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S := by
  rw [Set.mem_image]
  exact exists_and_map_eq_mk_iff

/-- `Sym2.map (some : α → Option α)` is injective. The named specialization of
`Sym2.map.injective` that arises whenever an `Option`-vertex extension counts edges
via `Set.ncard_image_of_injective`. -/
lemma map_some_injective : Function.Injective (Sym2.map (some : α → Option α)) :=
  Sym2.map.injective (Option.some_injective α)

/-- `none` is never an endpoint of `Sym2.map some e`: the image of any edge `e : Sym2 α`
under `some : α → Option α` has both endpoints in the `some`-branch of `Option α`. -/
lemma notMem_map_some (e : Sym2 α) :
    none ∉ Sym2.map (some : α → Option α) e := by
  rw [Sym2.mem_map]
  rintro ⟨_, _, h⟩
  exact Option.some_ne_none _ h

/-- The image `Sym2.map some '' S` is disjoint from any `T ⊆ Sym2 (Option α)` whose
elements all contain `none` as an endpoint. The typical use is when `T` is a literal
set of "fresh" edges of the form `s(none, some _)`. -/
theorem disjoint_image_map_some {S : Set (Sym2 α)} {T : Set (Sym2 (Option α))}
    (hT : ∀ e ∈ T, none ∈ e) : Disjoint (Sym2.map some '' S) T := by
  rw [Set.disjoint_left]
  rintro _ ⟨e, _, rfl⟩ heT
  exact notMem_map_some e (hT _ heT)

/-- The `Set`-coercion of `z.toFinset` equals the `SetLike` coercion of `z` itself.
Tagged `@[simp]` so the `Sym2.toFinset` cast canonicalizes to the underlying `SetLike`
coercion in goals like `e.toFinset ⊆ C ↔ (↑e : Set α) ⊆ (↑C : Set α)`. Not `norm_cast`
because both sides are coe functions; `norm_cast`'s direction-of-simplification heuristic
requires the RHS to have strictly fewer coes than the LHS. -/
@[simp]
lemma coe_toFinset [DecidableEq α] (z : Sym2 α) : (z.toFinset : Set α) = (↑z : Set α) := by
  ext x
  rw [Finset.mem_coe, Sym2.mem_toFinset, SetLike.mem_coe]

/-- Pointwise iff for "fresh edges" `s(none, some _) : Sym2 (Option α)`: two such edges agree
iff their `some`-endpoints agree. The `Sym2.eq_iff` case split is uniformly resolved because
the second disjunct (`none = some v ∧ some u = none`) is contradictory. -/
lemma mk_none_some_eq_iff {u v : α} :
    s((none : Option α), some u) = s(none, some v) ↔ u = v := by
  simp

end Sym2


end
end BundleSource0008

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0008/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0008.json"

section BundleSource0009
/- Source: Papers/RigidityLaman_Sparsity.lean -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/


/- Adapted without mathematical changes from Bryan Gin-ge Chen's
CombinatorialRigidity, commit 021c2284bc387efee3c3b20a18eb5f769638b578.
Upstream source: CombinatorialRigidity/Sparsity.lean
https://github.com/bryangingechen/CombinatorialRigidity
-/










/-!
# `(k, ℓ)`-sparsity and `(k, ℓ)`-tightness

A simple graph `G` is `(k, ℓ)`-**sparse** if every finite set `s` of
vertices spans at most `k * #s − ℓ` edges, whenever the bound is
non-negative. It is `(k, ℓ)`-**tight** if it is sparse and the total edge
count meets the bound exactly: `#E + ℓ = k * #V`.

These count conditions are the combinatorial side of the rigidity
matroid. The Laman case `(k, ℓ) = (2, 3)` is treated downstream in
`Laman.lean`.

## Main definitions

* `SimpleGraph.IsSparse G k ℓ` — for every finite `s : Finset V` with
  `ℓ ≤ k * #s`, `(G.edgesIn ↑s).ncard + ℓ ≤ k * #s`. Phrased additively
  to avoid `ℕ`-subtraction.
* `SimpleGraph.IsTight G k ℓ` — sparse and `(G.edgeSet).ncard + ℓ = k * Nat.card V`.
* `SimpleGraph.IsTightOn G k ℓ s` — `s : Finset V` is a tight subset:
  `(G.edgesIn ↑s).ncard + ℓ = k * s.card`. The localised version of `IsTight`.

## Main lemmas

* `SimpleGraph.bot_isSparse` — the empty graph is sparse for every `(k, ℓ)`.
* `SimpleGraph.IsSparse.mono_left` — sparsity is preserved under subgraph
  inclusion.
* `SimpleGraph.bot_isTight_iff` — characterisation of when the empty graph is tight.
* `SimpleGraph.IsSparse.edgeSet_ncard_add_le` — global edge count bound.
* `SimpleGraph.IsSparse.exists_one_le_degree_le_three` — strengthening for sparse graphs
  with at least one edge: some vertex has degree in `{1, 2, 3}`.
* `SimpleGraph.IsSparse.exists_degree_le_three` — every `(2, 3)`-sparse graph on
  `n ≥ 2` vertices has a vertex of degree at most 3.
* `SimpleGraph.IsSparse.exists_nonadj_among_three_neighbors` — in a `(2, 3)`-sparse
  graph, three pairwise distinct neighbors of any vertex contain a non-adjacent pair.
* `SimpleGraph.IsSparse.deleteEdges` — sparsity preserved under edge deletion.
* `SimpleGraph.IsTight.not_isSparse_of_lt` — proper supergraph of a tight graph is not sparse.
* `SimpleGraph.IsSparse.iso`, `SimpleGraph.IsTight.iso` — sparsity and tightness are
  preserved under graph isomorphism.
* `SimpleGraph.IsSparse.isTightOn_of_le` — in a `(k, ℓ)`-sparse graph, a Finset whose
  edge count meets the sparsity bound from below is exactly tight. The "squeeze" by which
  `IsSparse.typeII_reverse_blocker` extracts a tight set from a sparsity violation on a
  candidate graph.
* `SimpleGraph.IsTightOn.union_inter` — tight subsets are closed under union and
  intersection in a `(k, ℓ)`-sparse graph (subject to the standard `ℓ ≤ k * #(s ∩ t)`
  size proviso). The contradiction templates of the reverse decomposition run on it.
* `SimpleGraph.IsTightOn.union_inter_of_pair` — matroidal-regime specialization
  (`ℓ < 2 * k`): two tight sets sharing a pair of distinct vertices have tight union
  and intersection. The size proviso of `IsTightOn.union_inter` is auto-discharged.
* `SimpleGraph.IsSparse.exists_isTightOn_of_insert_not_sparse` — violation extraction:
  if `fromEdgeSet I` is `(k, ℓ)`-sparse but inserting an off-diagonal edge `s(u, v) ∉ I`
  breaks sparsity, then some Finset containing `u` and `v` is `(fromEdgeSet I)`-tight.
  Builds the "I-block" that anchors the `(k, ℓ)`-count matroid augmentation argument.
* `SimpleGraph.image_edgesIn_comap` — `Sym2.map`-image of `(G.comap f).edgesIn s'` is
  `G.edgesIn (f '' s')`; the comap analogue of `Iso.image_edgesIn`, used by the typeII-
  reverse blocker to pump edge counts back along the subtype embedding.
* `SimpleGraph.IsSparse.typeII_reverse_blocker` — per-pair tight-blocker witness for the
  typeII Henneberg reverse, sparse form: a sparsity violation on the candidate graph
  `(G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` extracts a tight set in `G` containing `x` and `y` but not
  `v`.
* `SimpleGraph.IsSparse.exists_typeI_or_typeII_reverse` — the reverse decomposition of a
  `(2, 3)`-sparse graph with an edge, at a vertex of degree one, two or three.

The `I`-components (`maxBlock`) and the count matroid's augmentation lemma
`IsSparse.exists_aug_of_lt_two_mul` are in `SparsityIComponents.lean`.

## Implementation notes

`IsSparse`, `IsTight`, and `IsTightOn` are non-reducible `def`s, so `grind`
will not unfold them. To break a goal involving `IsTight` into its sparse and
edge-count components, use `refine ⟨?_, ?_⟩` (or pattern-match `⟨h1, h2⟩`);
to surface the underlying equation of an `IsTightOn`, use `unfold IsTightOn`
(it is a one-equation `def`, not an And). See `TACTICS-GOLF.md` §4 for related
guidance.

The blueprint's `sec:sparsity` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A simple graph `G` is `(k, ℓ)`-sparse if every finite set `s` of vertices spans at most
`k * #s − ℓ` edges. The hypothesis `ℓ ≤ k * #s` keeps the bound nonnegative; the conclusion is
phrased additively to avoid `ℕ`-subtraction. -/
@[expose] def IsSparse (k ℓ : ℕ) : Prop :=
  ∀ s : Finset V, ℓ ≤ k * s.card → (G.edgesIn ↑s).ncard + ℓ ≤ k * s.card

/-- A finite vertex set `s` is a `(k, ℓ)`-**blocking witness** for `G` if it spans too many edges
for `G` to be `(k, ℓ)`-sparse: `ℓ ≤ k * #s` yet `k * #s < #E(s) + ℓ`. The vertex set of a reject
verdict of the pebble game is one (`runPebbleGameWith_isBlockingWitness`). -/
@[expose] def IsBlockingWitness (k ℓ : ℕ) (s : Finset V) : Prop :=
  ℓ ≤ k * s.card ∧ k * s.card < (G.edgesIn (↑s : Set V)).ncard + ℓ

/-- A graph with a blocking witness is not sparse. -/
theorem not_isSparse_of_isBlockingWitness {k ℓ : ℕ} {s : Finset V}
    (h : G.IsBlockingWitness k ℓ s) : ¬ G.IsSparse k ℓ :=
  fun hG => by have := hG s h.1; have := h.2; omega

/-- A simple graph `G` is `(k, ℓ)`-tight if it is `(k, ℓ)`-sparse and its total edge count is
exactly `k * #V − ℓ`. -/
@[expose] def IsTight (k ℓ : ℕ) : Prop :=
  G.IsSparse k ℓ ∧ G.edgeSet.ncard + ℓ = k * Nat.card V

/-- A finite vertex set `s` is `(k, ℓ)`-**tight in** `G` if it spans exactly `k * #s − ℓ`
edges. Subset-tight sets form a lattice in any `(k, ℓ)`-sparse graph subject to the standard
`ℓ ≤ k * #(s ∩ t)` size proviso; see `IsTightOn.union_inter`. -/
@[expose] def IsTightOn (k ℓ : ℕ) (s : Finset V) : Prop :=
  (G.edgesIn (↑s : Set V)).ncard + ℓ = k * s.card

variable {G}

/-- The empty graph is `(k, ℓ)`-sparse for any parameters. -/
theorem bot_isSparse (k ℓ : ℕ) : (⊥ : SimpleGraph V).IsSparse k ℓ := by
  intro s hs
  simpa using hs

/-- A subgraph of a `(k, ℓ)`-sparse graph is itself `(k, ℓ)`-sparse. -/
theorem IsSparse.mono_left {G G' : SimpleGraph V} (h : G ≤ G') {k ℓ : ℕ}
    (hG' : G'.IsSparse k ℓ) : G.IsSparse k ℓ := by
  intro s hs
  refine (Nat.add_le_add_right ?_ ℓ).trans (hG' s hs)
  refine Set.ncard_le_ncard ?_ (G'.edgesIn_finite s)
  exact fun _ ⟨he₁, he₂⟩ ↦ ⟨edgeSet_subset_edgeSet.mpr h he₁, he₂⟩

theorem IsTight.isSparse {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.IsSparse k ℓ := h.1

theorem IsTight.edgeSet_ncard {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.edgeSet.ncard + ℓ = k * Nat.card V := h.2

/-- The empty graph is `(k, ℓ)`-tight precisely when `ℓ = k * #V`. -/
@[simp] theorem bot_isTight_iff (k ℓ : ℕ) :
    (⊥ : SimpleGraph V).IsTight k ℓ ↔ ℓ = k * Nat.card V := by
  refine ⟨fun ⟨_, h⟩ ↦ by simpa using h, fun h ↦ ⟨bot_isSparse k ℓ, by simpa using h⟩⟩

/-! ### The global edge bound and consequences -/

/-- The global edge count of a `(k, ℓ)`-sparse graph is bounded by `k * #V − ℓ`,
provided `ℓ ≤ k * #V`. This is sparsity applied at `s = univ`. -/
theorem IsSparse.edgeSet_ncard_add_le [Finite V] {G : SimpleGraph V} {k ℓ : ℕ}
    (h : G.IsSparse k ℓ) (hV : ℓ ≤ k * Nat.card V) :
    G.edgeSet.ncard + ℓ ≤ k * Nat.card V := by
  have : Fintype V := Fintype.ofFinite V
  have := h Finset.univ
  grind only [= Finset.card_univ, Nat.card_eq_fintype_card, !Finset.coe_univ, edgesIn_univ]

/-- Deleting edges from a `(k, ℓ)`-sparse graph yields a `(k, ℓ)`-sparse graph. -/
theorem IsSparse.deleteEdges {G : SimpleGraph V} {k ℓ : ℕ}
    (h : G.IsSparse k ℓ) (s : Set (Sym2 V)) : (G.deleteEdges s).IsSparse k ℓ :=
  h.mono_left (G.deleteEdges_le s)

/-! ### Low-degree vertex in `(2, 3)`-sparse graphs

A `(2, 3)`-sparse graph on `n ≥ 2` vertices has `#E ≤ 2n − 3`, so by handshake the
average degree is `< 4` and some vertex has degree at most 3
(`IsLaman.exists_two_le_degree_le_three` uses it). The sparse-graph reverse decomposition
`IsSparse.exists_typeI_or_typeII_reverse` uses the strengthening
`IsSparse.exists_one_le_degree_le_three`, as Jordán's proof of his Theorem 2.2.1 finds a vertex
of degree one, two or three (p. 45). -/

/-- In a `(2, 3)`-sparse graph on `n ≥ 2` vertices, some vertex has degree at most 3.
The handshake identity gives `∑ deg = 2 #E ≤ 4n − 6`, so the average is `< 4` and some
vertex has degree `≤ 3`. -/
theorem IsSparse.exists_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hV : 2 ≤ Fintype.card V) :
    ∃ v, G.degree v ≤ 3 := by
  by_contra hcontra
  push Not at hcontra
  -- Sum of degrees ≥ 4n; handshake + sparsity gives sum ≤ 4n - 6 < 4n.
  have h4n : ∑ _ : V, (4 : ℕ) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum (fun v _ => by have := hcontra v; omega)
  simp at h4n
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have hE := h.edgeSet_ncard_add_le (by rw [Nat.card_eq_fintype_card]; omega)
  grind only [Nat.card_eq_fintype_card]

/-- In a `(2, 3)`-sparse graph with at least one edge, some vertex has degree in `{1, 2, 3}`.
Strengthens `exists_degree_le_three` by ruling out the isolated case (`G.degree v = 0`):
restricting the handshake / sparsity bound to `S := {v | 1 ≤ G.degree v}` gives
`∑_{v ∈ S} G.degree v = ∑_v G.degree v = 2 |E|`, all edges sit inside `edgesIn ↑S`, and
sparsity at `S` (size ≥ 2 from any edge) gives `|E| + 3 ≤ 2 |S|`. If every vertex in `S`
had degree ≥ 4 the sum would be `≥ 4 |S|`, contradicting `2 |E| ≤ 4 |S| − 6`. The
reverse decomposition `IsSparse.exists_typeI_or_typeII_reverse` needs the positive degree:
its three cases are the degrees one (pendant), two (Type I) and three (Type II). -/
theorem IsSparse.exists_one_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hE : G.edgeSet.Nonempty) :
    ∃ v, 1 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  classical
  by_contra hcontra
  push Not at hcontra
  -- `S`: positive-degree vertices. By `hcontra`, every `v ∈ S` has `G.degree v ≥ 4`.
  set S : Finset V := Finset.univ.filter (fun v => 1 ≤ G.degree v) with hS_def
  -- An edge gives two distinct positive-degree vertices, hence `|S| ≥ 2`.
  obtain ⟨e, he⟩ := hE
  induction e with | h u v => ?_
  rw [mem_edgeSet] at he
  have huv : u ≠ v := G.ne_of_adj he
  have hdu : 1 ≤ G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, he⟩
  have hdv : 1 ≤ G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, he.symm⟩
  have hu_in : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdu⟩
  have hv_in : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdv⟩
  have hS_ge2 : 2 ≤ S.card := by
    rw [show (2 : ℕ) = ({u, v} : Finset V).card from (Finset.card_pair huv).symm]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- Every edge has both endpoints in `S`, so `edgesIn ↑S = edgeSet`.
  have h_edgesIn : G.edgesIn (↑S : Set V) = G.edgeSet := by
    refine Set.eq_of_subset_of_subset (fun _ he => he.1) (fun e he => mem_edgesIn.mpr ⟨he, ?_⟩)
    induction e with | h x y => ?_
    rw [mem_edgeSet] at he
    rw [Sym2.coe_mk]
    rintro w (rfl | rfl)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he⟩⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he.symm⟩⟩)
  -- Sum-of-degrees ≥ 4 |S| from the by-contradiction hypothesis.
  have h_deg_4 : ∀ w ∈ S, 4 ≤ G.degree w := fun w hw => by
    have h1 := (Finset.mem_filter.mp hw).2
    have := hcontra w h1; omega
  have h_sum_4 : (∑ _ ∈ S, (4 : ℕ)) ≤ ∑ w ∈ S, G.degree w :=
    Finset.sum_le_sum h_deg_4
  simp at h_sum_4
  -- Restriction is harmless: vertices outside `S` have degree 0.
  have h_sum_eq : ∑ w ∈ S, G.degree w = ∑ w, G.degree w := by
    rw [hS_def]; exact Finset.sum_filter_of_ne fun w _ hw => by omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have h_sparse_S := h S (by omega)
  rw [h_edgesIn] at h_sparse_S
  omega

/-! ### Non-adjacent pair among three neighbors

In a `(2, 3)`-sparse graph, any three neighbors of a single vertex contain a non-adjacent
pair. This is the combinatorial input for the Type II Henneberg reverse move: given a
degree-3 vertex with neighbors `a, b, c`, we use this lemma to pick the two non-adjacent
ones to bridge with a fresh edge. `IsSparse.exists_typeI_or_typeII_reverse` uses it, and
`Henneberg.IsLaman.exists_typeI_or_typeII_reverse` through it; the proof uses sparsity, not
tightness. -/

/-- In a `(2, 3)`-sparse graph, three pairwise distinct neighbors of any vertex contain
a non-adjacent pair. Apply sparsity to the 4-set `{v, a, b, c}` (size 4, so at most
`2·4 − 3 = 5` edges); the three edges `v-a`, `v-b`, `v-c` are present, so among
`{a, b, c}` there are at most 2 edges, hence at least one of the three possible pairs is
missing. -/
theorem IsSparse.exists_nonadj_among_three_neighbors [Finite V]
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c := by
  classical
  have : Fintype V := Fintype.ofFinite V
  by_contra hall
  push Not at hall
  obtain ⟨hab_e, hac_e, hbc_e⟩ := hall
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  -- The 4-set `{v, a, b, c}` has cardinality 4.
  have hs_card : ({v, a, b, c} : Finset V).card = 4 := by
    grind [Finset.card_insert_of_notMem, Finset.card_singleton]
  -- The 6 candidate edges form a 6-element Finset, all contained in `G.edgesIn ↑{v,a,b,c}`.
  set E : Finset (Sym2 V) :=
    {s(v, a), s(v, b), s(v, c), s(a, b), s(a, c), s(b, c)} with hE_def
  have hE_card : E.card = 6 := by
    rw [hE_def]
    grind [Finset.card_insert_of_notMem, Finset.card_singleton, Sym2.eq_iff]
  have hE_sub : (↑E : Set (Sym2 V)) ⊆ G.edgesIn (↑({v, a, b, c} : Finset V) : Set V) := by
    intro e he
    simp only [hE_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mem_edgesIn.mpr ⟨by rwa [mem_edgeSet],
        by rw [Sym2.coe_mk]; rintro _ (rfl | rfl) <;> simp⟩
  have hsparse := h {v, a, b, c} (by omega)
  have h6_le : 6 ≤ (G.edgesIn (↑({v, a, b, c} : Finset V) : Set V)).ncard := by
    rw [← hE_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hE_sub
  omega

/-- A proper supergraph of a `(k, ℓ)`-tight graph cannot be `(k, ℓ)`-sparse: the global edge bound
is already saturated, so any extra edge violates it. -/
theorem IsTight.not_isSparse_of_lt [Finite V] {G H : SimpleGraph V} {k ℓ : ℕ}
    (hG : G.IsTight k ℓ) (h : G < H) : ¬ H.IsSparse k ℓ := fun hH => by
  have := hG.edgeSet_ncard
  have := hH.edgeSet_ncard_add_le (by grind only)
  have := Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.mpr h) (Set.toFinite H.edgeSet)
  grind only

/-! ### Transport along graph isomorphism

`IsSparse` and `IsTight` are preserved under graph isomorphism. The transport is mediated by
`Sym2.map φ` between edge sets and by `φ.toEquiv` between vertex types. -/

namespace Iso

variable {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Under a graph iso, the `Sym2.map`-image of `G.edgesIn s` is `H.edgesIn (φ '' s)`. The
`edgesIn` analogue of `Iso.image_neighborSet`. -/
lemma image_edgesIn (φ : G ≃g H) (s : Set V) :
    Sym2.map φ '' G.edgesIn s = H.edgesIn (φ '' s) := by
  ext e
  induction e with | h u v => ?_
  simp only [Sym2.mk_mem_image_map_iff, mem_edgesIn, mem_edgeSet, Sym2.coe_mk]
  constructor
  · rintro ⟨p, q, rfl, rfl, h_adj, hsub⟩
    refine ⟨φ.map_adj_iff.mpr h_adj, ?_⟩
    rintro x (rfl | rfl)
    · exact ⟨p, hsub (Or.inl rfl), rfl⟩
    · exact ⟨q, hsub (Or.inr rfl), rfl⟩
  · rintro ⟨h_adj, hsub⟩
    obtain ⟨p, hp, rfl⟩ := hsub (Or.inl rfl)
    obtain ⟨q, hq, rfl⟩ := hsub (Or.inr rfl)
    exact ⟨p, q, rfl, rfl, φ.map_adj_iff.mp h_adj,
      fun x hx => by rcases hx with rfl | rfl <;> assumption⟩

end Iso

/-- Under graph comap, the `Sym2.map`-image of `(G.comap f).edgesIn s'` is `G.edgesIn (f '' s')`.
The image-form equality holds without an injectivity hypothesis on `f`; injectivity lifts to the
ncard equality used downstream (via `Set.ncard_image_of_injective` on `Sym2.map f`). The
non-iso analogue of `Iso.image_edgesIn`; through `ncard_edgesIn_comap`, the typeII-reverse
blocker pumps the candidate graph's edge count back through `G` along the subtype embedding. -/
lemma image_edgesIn_comap (G : SimpleGraph V) {V' : Type*} (f : V' → V) (s' : Set V') :
    Sym2.map f '' ((G.comap f).edgesIn s') = G.edgesIn (f '' s') := by
  ext e
  refine e.ind fun p q => ?_
  rw [Sym2.mk_mem_image_map_iff]
  simp only [mem_edgesIn, mem_edgeSet, comap_adj, Sym2.coe_mk, Set.insert_subset_iff,
             Set.singleton_subset_iff, Set.mem_image]
  constructor
  · rintro ⟨u, w, rfl, rfl, hadj, hu, hw⟩
    exact ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
  · rintro ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
    exact ⟨u, w, rfl, rfl, hadj, hu, hw⟩

/-- Cardinality form of `image_edgesIn_comap`: under an injective vertex map `f`, the edge
count in the comap is preserved by pushing the index Finset through `f`. Combines
`Finset.coe_image`, `image_edgesIn_comap`, and `Set.ncard_image_of_injective` (with
`Sym2.map.injective`) into a single application. -/
lemma ncard_edgesIn_comap [DecidableEq V] {V' : Type*} (G : SimpleGraph V)
    {f : V' → V} (hf : Function.Injective f) (s' : Finset V') :
    ((G.comap f).edgesIn (↑s' : Set V')).ncard =
      (G.edgesIn (↑(s'.image f) : Set V)).ncard := by
  rw [Finset.coe_image, ← image_edgesIn_comap,
      Set.ncard_image_of_injective _ (Sym2.map.injective hf)]

/-- A graph isomorphism preserves `(k, ℓ)`-sparsity. -/
theorem IsSparse.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsSparse k ℓ) : H.IsSparse k ℓ := by
  classical
  intro s hs
  set s' : Finset V := s.image φ.symm
  have hs'_card : s'.card = s.card :=
    Finset.card_image_of_injective s φ.symm.toEquiv.injective
  have h_eq : (H.edgesIn (↑s : Set W)).ncard = (G.edgesIn (↑s' : Set V)).ncard := by
    rw [show (↑s' : Set V) = φ.symm '' ↑s from Finset.coe_image, ← Iso.image_edgesIn φ.symm,
      Set.ncard_image_of_injective _ (Sym2.map.injective φ.symm.injective)]
  rw [h_eq, ← hs'_card]
  exact h s' (hs'_card ▸ hs)

/-- A graph isomorphism preserves `(k, ℓ)`-tightness. -/
theorem IsTight.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsTight k ℓ) : H.IsTight k ℓ := by
  refine ⟨h.1.iso φ, ?_⟩
  have hE : H.edgeSet.ncard = G.edgeSet.ncard := by
    simp only [← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.mapEdgeSet.symm
  have hV : Nat.card W = Nat.card V := Nat.card_congr φ.toEquiv.symm
  grind only [h.2]

/-- The comap of a `(k, ℓ)`-sparse graph along an injective vertex map is `(k, ℓ)`-sparse.
The proof transports a candidate Finset on the source side to its `f`-image on the target,
and reads off `(G.comap f)`'s edge count via `image_edgesIn_comap`. The directional analogue
of `IsSparse.iso`; specialized to `Subtype.val : {w // w ≠ v} → V` by the sparse-graph
reverse decomposition. -/
theorem IsSparse.comap {V' : Type*} {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsSparse k ℓ)
    {f : V' → V} (hf : Function.Injective f) : (G.comap f).IsSparse k ℓ := by
  classical
  intro s' hs'
  set S : Finset V := s'.image f
  have hS_card : S.card = s'.card := Finset.card_image_of_injective s' hf
  have h_link : ((G.comap f).edgesIn (↑s' : Set V')).ncard = (G.edgesIn (↑S : Set V)).ncard :=
    G.ncard_edgesIn_comap hf s'
  rw [h_link, ← hS_card]
  exact h S (hS_card ▸ hs')

/-- **Squeeze: lower bound forces tight.** In a `(k, ℓ)`-sparse graph, if a Finset `s`
attains the sparsity upper bound from below, it must be exactly `(k, ℓ)`-tight. Used by
the typeII-reverse blocker (`IsSparse.typeII_reverse_blocker`) to convert a sparsity violation
on a candidate graph into a tight set in `G`. -/
theorem IsSparse.isTightOn_of_le {G : SimpleGraph V} {k ℓ : ℕ}
    (hG : G.IsSparse k ℓ) {s : Finset V} (hs : ℓ ≤ k * s.card)
    (h_le : k * s.card ≤ (G.edgesIn ↑s).ncard + ℓ) :
    G.IsTightOn k ℓ s := by
  grind only [IsTightOn, hG s hs]

/-! ### The tight-subset lattice

In a `(k, ℓ)`-sparse graph, the tight subsets are closed under union and intersection
(subject to a standard size proviso on the intersection). The squeeze is between two
inequalities: supermodularity of edge counts (`edgesIn_ncard_add_le`) lower-bounds the
edge sum on `s ∪ t` and `s ∩ t` by the same sum on `s` and `t`, while sparsity
upper-bounds it by the cardinality target. The bridging identity is the standard
Finset-cardinality fact `s.card + t.card = (s ∪ t).card + (s ∩ t).card`. -/

/-- **Tight subsets are closed under union and intersection.** In a `(k, ℓ)`-sparse graph,
if `s, t : Finset V` are both `(k, ℓ)`-tight subsets and the intersection is large enough
that sparsity applies there (`ℓ ≤ k * #(s ∩ t)`), then so are `s ∪ t` and `s ∩ t`. The
edge-arithmetic input is `edgesIn_ncard_add_le` (supermodularity); the cardinality input
is `Finset.card_union_add_card_inter`. -/
theorem IsTightOn.union_inter [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {s t : Finset V} (hs : G.IsTightOn k ℓ s) (ht : G.IsTightOn k ℓ t)
    (hG : G.IsSparse k ℓ) (h_inter : ℓ ≤ k * (s ∩ t).card) :
    G.IsTightOn k ℓ (s ∪ t) ∧ G.IsTightOn k ℓ (s ∩ t) := by
  have h_super := G.edgesIn_ncard_add_le (↑s : Set V) (↑t : Set V)
  rw [← Finset.coe_union, ← Finset.coe_inter] at h_super
  have h_sparse_inter := hG (s ∩ t) h_inter
  have h_sparse_union := hG (s ∪ t)
    (h_inter.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.inter_subset_union)))
  have h_card_mul := Finset.mul_card_union_add_mul_card_inter s t k
  grind only [IsTightOn]

/-- **Tight union with bonus edges.** Generalizes `IsTightOn.union_inter`'s union half: instead of
requiring `ℓ ≤ k * #(s ∩ t)` to extract sparsity at the intersection, allow the user to supply a
set `F` of "bonus" edges in `edgesIn (S₁ ∪ S₂)` disjoint from `edgesIn S₁ ∪ edgesIn S₂` and
ask only that `F` plus the intersection accounting close the gap, i.e.
`|F| + k * #(S₁ ∩ S₂) ≥ |edgesIn (S₁ ∩ S₂)| + ℓ`. Specializes to
`IsTightOn.union_inter`'s union conclusion at `F = ∅` (the size proviso then provides the
close-the-gap inequality via sparsity at `S₁ ∩ S₂`). -/
theorem IsTightOn.union_with_bonus [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {S₁ S₂ : Finset V} (h₁ : G.IsTightOn k ℓ S₁) (h₂ : G.IsTightOn k ℓ S₂)
    (hG : G.IsSparse k ℓ) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)))
    (h_close : (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard + ℓ ≤
               F.ncard + k * (S₁ ∩ S₂).card) :
    G.IsTightOn k ℓ (S₁ ∪ S₂) := by
  -- Step 1: refined supermodular bound. The bonus edges enlarge the union side by `|F|`.
  have h_un_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) := by
    rw [Finset.coe_union]
    exact Set.union_subset (edgesIn_mono Set.subset_union_left)
                           (edgesIn_mono Set.subset_union_right)
  have h_combined_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) :=
    Set.union_subset h_un_sub hF_sub
  have h_inter_eq : G.edgesIn (↑S₁ : Set V) ∩ G.edgesIn (↑S₂ : Set V) =
                    G.edgesIn (↑(S₁ ∩ S₂) : Set V) := by
    rw [Finset.coe_inter]; exact (edgesIn_inter _ _).symm
  have h_un_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard +
        (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard =
        (G.edgesIn (↑S₁ : Set V)).ncard + (G.edgesIn (↑S₂ : Set V)).ncard := by
    rw [← h_inter_eq]; exact Set.ncard_union_add_ncard_inter _ _
  have h_combined_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F).ncard =
        (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm
      ((G.edgesIn_finite S₁).union (G.edgesIn_finite S₂)) ((G.edgesIn_finite _).subset hF_sub)
  have h_le_union :=
    Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (S₁ ∪ S₂))
  -- Step 2: cardinality identity for the union/intersection split.
  have h_card_mul := Finset.mul_card_union_add_mul_card_inter S₁ S₂ k
  -- Step 3: squeeze to tightness via `IsSparse.isTightOn_of_le`.
  have h_S1_size : ℓ ≤ k * S₁.card := by grind only [IsTightOn]
  have h_union_size : ℓ ≤ k * (S₁ ∪ S₂).card :=
    h_S1_size.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.subset_union_left))
  refine hG.isTightOn_of_le h_union_size ?_
  grind only [IsTightOn]

/-- **Tight extension by a vertex with `k` boundary edges.** If `S` is `(k, ℓ)`-tight and a fresh
vertex `w ∉ S` can be added with at least `k` "new" edges `F ⊆ edgesIn (insert w S)` disjoint from
`edgesIn S`, then `insert w S` is itself `(k, ℓ)`-tight. The `|F| ≥ k` hypothesis is exactly the
edge-count needed to absorb the extra vertex while staying on the sparsity locus. -/
theorem IsTightOn.insert_vertex_with_edges [DecidableEq V] {G : SimpleGraph V}
    {k ℓ : ℕ} {S : Finset V} (h : G.IsTightOn k ℓ S) (hG : G.IsSparse k ℓ)
    {w : V} (hw : w ∉ S) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(insert w S) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S : Set V))) (h_card : k ≤ F.ncard) :
    G.IsTightOn k ℓ (insert w S) := by
  have h_S_sub : G.edgesIn (↑S : Set V) ⊆ G.edgesIn (↑(insert w S) : Set V) := by
    refine edgesIn_mono ?_; rw [Finset.coe_insert]; exact Set.subset_insert _ _
  have h_combined_sub :
      G.edgesIn (↑S : Set V) ∪ F ⊆ G.edgesIn (↑(insert w S) : Set V) :=
    Set.union_subset h_S_sub hF_sub
  have h_combined_card :
      (G.edgesIn (↑S : Set V) ∪ F).ncard = (G.edgesIn (↑S : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm (G.edgesIn_finite S) ((G.edgesIn_finite _).subset hF_sub)
  have h_le := Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (insert w S))
  have h_card_insert : (insert w S).card = S.card + 1 := Finset.card_insert_of_notMem hw
  have h_size : ℓ ≤ k * (insert w S).card := by
    unfold IsTightOn at h
    rw [h_card_insert, Nat.mul_add, Nat.mul_one]; omega
  refine hG.isTightOn_of_le h_size ?_
  rw [h_card_insert, Nat.mul_add, Nat.mul_one] at h_size ⊢
  grind only [IsTightOn]

/-! ### Matroidal-regime block closure (`ℓ < 2 * k`)

In the matroidal regime `ℓ < 2 * k`, the size proviso `ℓ ≤ k * #(s ∩ t)` of
`IsTightOn.union_inter` is automatically discharged for two tight sets sharing a common pair
of distinct vertices: `#(s ∩ t) ≥ 2 ≥ ⌈ℓ/k⌉` for any `ℓ < 2k`. This is the combinatorial
foundation of the `(k, ℓ)`-count matroid (Lorea; White and Whiteley; see Whiteley 1996,
Proposition A.1.1, and Lee–Streinu 2008, Theorem 2): blocks of an edge set `I` containing a
fixed pair `{u, v}` are closed under intersection and union, so the family has a unique
maximum element — the *I-component* of `{u, v}` — that drives the augmentation argument
(`SparsityIComponents.lean`). -/

/-- **Block closure under a shared pair (matroidal regime).** For `ℓ < 2 * k` and two
`(k, ℓ)`-tight finite sets `s, t` both containing distinct vertices `u ≠ v`, both `s ∪ t` and
`s ∩ t` are `(k, ℓ)`-tight. Specialization of `IsTightOn.union_inter` whose size proviso
`ℓ ≤ k * #(s ∩ t)` is auto-discharged via `#(s ∩ t) ≥ #{u, v} = 2` and `ℓ < 2k = k * 2`. -/
theorem IsTightOn.union_inter_of_pair [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {k ℓ : ℕ} (hℓ : ℓ < 2 * k) {s t : Finset V}
    (hs : G.IsTightOn k ℓ s) (ht : G.IsTightOn k ℓ t) (hG : G.IsSparse k ℓ)
    {u v : V} (huv : u ≠ v)
    (hu_s : u ∈ s) (hv_s : v ∈ s) (hu_t : u ∈ t) (hv_t : v ∈ t) :
    G.IsTightOn k ℓ (s ∪ t) ∧ G.IsTightOn k ℓ (s ∩ t) := by
  refine hs.union_inter ht hG ?_
  have h_uv_sub : ({u, v} : Finset V) ⊆ s ∩ t := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu_s, hu_t⟩
    · exact Finset.mem_inter.mpr ⟨hv_s, hv_t⟩
  have h_card : 2 ≤ (s ∩ t).card :=
    (Finset.card_pair huv).symm ▸ Finset.card_le_card h_uv_sub
  calc ℓ ≤ 2 * k := hℓ.le
       _ = k * 2 := Nat.mul_comm 2 k
       _ ≤ k * (s ∩ t).card := Nat.mul_le_mul_left k h_card

/-- **Add-an-edge identity for `fromEdgeSet.edgeSet`.** Adding an off-diagonal edge `s(u, v)`
to an edge set `I` inserts exactly the singleton `{s(u, v)}` into the resulting `edgeSet`
of `fromEdgeSet`. The `fromEdgeSet` constructor drops diagonals; the `u ≠ v` hypothesis keeps
`s(u, v)` off the diagonal. -/
lemma edgeSet_fromEdgeSet_insert {I : Set (Sym2 V)} {u v : V} (huv : u ≠ v) :
    (fromEdgeSet (insert s(u, v) I)).edgeSet = insert s(u, v) (fromEdgeSet I).edgeSet := by
  rw [edgeSet_fromEdgeSet, edgeSet_fromEdgeSet,
      Set.insert_sdiff_of_notMem _ (Sym2.mem_diagSet.not.mpr (Sym2.mk_isDiag_iff.not.mpr huv))]

/-- **I-block extraction from a sparsity violation (matroidal building block).** If
`fromEdgeSet I` is `(k, ℓ)`-sparse but adding a single off-diagonal edge `s(u, v) ∉ I`
breaks sparsity, then there is a `(fromEdgeSet I)`-tight Finset containing both `u` and `v`
— the "I-block" that the `(k, ℓ)`-count matroid augmentation argument anchors on. -/
theorem IsSparse.exists_isTightOn_of_insert_not_sparse
    {k ℓ : ℕ} {I : Set (Sym2 V)} (hI : (fromEdgeSet I).IsSparse k ℓ)
    {u v : V} (huv : u ≠ v) (he_notin : s(u, v) ∉ I)
    (h_violation : ¬ (fromEdgeSet (insert s(u, v) I)).IsSparse k ℓ) :
    ∃ S : Finset V, u ∈ S ∧ v ∈ S ∧ (fromEdgeSet I).IsTightOn k ℓ S := by
  unfold IsSparse at h_violation
  push Not at h_violation
  obtain ⟨S, h_size, h_lt⟩ := h_violation
  have hI_at_S := hI S h_size
  have h_new_notin_old : s(u, v) ∉ (fromEdgeSet I).edgeSet :=
    fun h => he_notin ((edgeSet_fromEdgeSet I) ▸ h).1
  have h_edgeSet_eq := edgeSet_fromEdgeSet_insert (I := I) huv
  -- Case-split on `{u, v} ⊆ S`. The "⊄" case contradicts `I`-sparsity at `S`; the "⊆"
  -- case extracts the I-block.
  by_cases h_uv : u ∈ S ∧ v ∈ S
  · obtain ⟨hu, hv⟩ := h_uv
    refine ⟨S, hu, hv, ?_⟩
    have h_uv_in_sym2 : s(u, v) ∈ (↑S : Set V).sym2 := by
      rw [Set.mem_sym2_iff_subset, Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨hu, Set.singleton_subset_iff.mpr hv⟩
    have h_edges_eq : (fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V) =
        insert s(u, v) ((fromEdgeSet I).edgesIn (↑S : Set V)) := by
      unfold edgesIn
      rw [h_edgeSet_eq, Set.insert_inter_of_mem h_uv_in_sym2]
    have h_new_notin_old_edgesIn : s(u, v) ∉ (fromEdgeSet I).edgesIn (↑S : Set V) :=
      fun h => h_new_notin_old h.1
    have h_ncard_eq : ((fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V)).ncard =
        ((fromEdgeSet I).edgesIn (↑S : Set V)).ncard + 1 := by
      rw [h_edges_eq, Set.ncard_insert_of_notMem h_new_notin_old_edgesIn
        ((fromEdgeSet I).edgesIn_finite S)]
    grind only [IsTightOn]
  · exfalso
    have h_uv_notin_sym2 : s(u, v) ∉ (↑S : Set V).sym2 := by
      rw [Set.mem_sym2_iff_subset, Sym2.coe_mk]
      exact fun h_sub => h_uv
        ⟨h_sub (Set.mem_insert _ _), h_sub (Set.mem_insert_of_mem _ rfl)⟩
    have h_edges_eq : (fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V) =
        (fromEdgeSet I).edgesIn (↑S : Set V) := by
      unfold edgesIn
      rw [h_edgeSet_eq, Set.insert_inter_of_notMem h_uv_notin_sym2]
    rw [h_edges_eq] at h_lt
    omega

/-! ### Three-neighbor obstruction and contradiction templates

For a vertex `v` with three distinct neighbors `a, b, c` in a `(2, 3)`-sparse graph,
inserting `v` into any tight set `T ⊆ V \ {v}` containing `{a, b, c}` overshoots the
sparsity bound: `IsSparse.no_isTightOn_excluding_three_neighbors`. The three contradiction
templates below each derive `False` from a configuration of one, two, or three tight
blockers covering pairs of `{a, b, c}`; they reduce to the primitive by building a tight
set in `V \ {v}` that contains all three neighbors. The unified dispatcher
`IsSparse.False_of_pairwise_blocker_or_edge` packages all three by case-splitting on the
adj-or-blocker disjunction for each pair.

These primitives drive the degree-three case of the sparse-graph reverse decomposition
`IsSparse.exists_typeI_or_typeII_reverse` below (Jordán Lemma 2.1.4(b)), from which
`Henneberg.IsLaman.exists_typeI_or_typeII_reverse` (`HennebergReverse.lean`) follows. -/

/-- **Three-neighbor obstruction.** In a `(2, 3)`-sparse graph, no `(2, 3)`-tight set
`T ⊆ V \ {v}` can contain three distinct neighbors `a, b, c` of `v`: inserting `v` adds
1 vertex but at least 3 edges (the incident edges `s(v, a), s(v, b), s(v, c)`),
overshooting the `(2, 3)`-sparsity bound at `insert v T`. -/
theorem IsSparse.no_isTightOn_excluding_three_neighbors
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {T : Finset V} (hvT : v ∉ T) (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T)
    (hT : G.IsTightOn 2 3 T) : False := by
  classical
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  set T' : Finset V := insert v T with hT'_def
  have hT'_card : T'.card = T.card + 1 := Finset.card_insert_of_notMem hvT
  set E3 : Set (Sym2 V) := {s(v, a), s(v, b), s(v, c)} with hE3_def
  have hne_ab : s(v, a) ≠ s(v, b) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hab h2) (fun ⟨h1, _⟩ => hvb h1)
  have hne_ac : s(v, a) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hac h2) (fun ⟨h1, _⟩ => hvc h1)
  have hne_bc : s(v, b) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hbc h2) (fun ⟨h1, _⟩ => hvc h1)
  have hE3_card : E3.ncard = 3 := by
    rw [hE3_def, Set.ncard_insert_of_notMem (by simp [hne_ab, hne_ac]) (Set.toFinite _),
        Set.ncard_pair hne_bc]
  have h_T_sub_T' : (↑T : Set V) ⊆ (↑T' : Set V) := by
    intro x hx
    rw [hT'_def, Finset.coe_insert]
    exact Or.inr hx
  have h_v_in_T' : v ∈ (↑T' : Set V) := by
    rw [hT'_def, Finset.coe_insert]; exact Set.mem_insert _ _
  have h_a_in_T' : a ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr haT)
  have h_b_in_T' : b ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hbT)
  have h_c_in_T' : c ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hcT)
  have h_E3_in : E3 ⊆ G.edgesIn (↑T' : Set V) := by
    rintro e (rfl | rfl | rfl)
    · exact G.mk_mem_edgesIn ha h_v_in_T' h_a_in_T'
    · exact G.mk_mem_edgesIn hb h_v_in_T' h_b_in_T'
    · exact G.mk_mem_edgesIn hc h_v_in_T' h_c_in_T'
  have h_disj : Disjoint E3 (G.edgesIn (↑T : Set V)) := by
    rw [Set.disjoint_left]
    rintro e he h_mem
    obtain ⟨_, hsub⟩ := mem_edgesIn.mp h_mem
    have hv_in_e : v ∈ (e : Set V) := by
      rcases he with rfl | rfl | rfl <;> (rw [Sym2.coe_mk]; exact Set.mem_insert _ _)
    exact hvT (Finset.mem_coe.mp (hsub hv_in_e))
  have h_edgesIn_sub : G.edgesIn (↑T : Set V) ⊆ G.edgesIn (↑T' : Set V) :=
    edgesIn_mono h_T_sub_T'
  have h_ncard_ge : (G.edgesIn (↑T : Set V)).ncard + 3 ≤ (G.edgesIn (↑T' : Set V)).ncard :=
    calc (G.edgesIn (↑T : Set V)).ncard + 3
        = (G.edgesIn (↑T : Set V)).ncard + E3.ncard := by rw [hE3_card]
      _ = (G.edgesIn (↑T : Set V) ∪ E3).ncard :=
          (Set.ncard_union_eq h_disj.symm (G.edgesIn_finite T) (Set.toFinite _)).symm
      _ ≤ (G.edgesIn (↑T' : Set V)).ncard :=
          Set.ncard_le_ncard (Set.union_subset h_edgesIn_sub h_E3_in) (G.edgesIn_finite T')
  have hT_card_ge : 3 ≤ T.card :=
    Finset.three_le_card_of_three_distinct_mem hab hac hbc haT hbT hcT
  have hT'_sparse := h T' (by rw [hT'_card]; omega)
  grind only [IsTightOn]

/-- **1-pair contradiction template.** A single blocker `S` containing two neighbors
`x, y` of `v`, with the third neighbor `z` connected to both `x` and `y` by edges of `G`:
case-split on `z ∈ S`. If yes, `S` already contains `{x, y, z}` and the primitive closes.
If no, extend to `T := insert z S`; the two edges `s(x, z)` and `s(y, z)` are in
`edgesIn T` but not in `edgesIn S` (since `z ∉ S`), giving `#(edgesIn T) ≥ #(edgesIn S) + 2`,
which combined with tightness of `S` saturates the squeeze at `T`. -/
theorem IsSparse.contradiction_one_pair
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxz_adj : G.Adj x z) (hyz_adj : G.Adj y z)
    {S : Finset V} (hvS : v ∉ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hS_tight : G.IsTightOn 2 3 S) : False := by
  classical
  by_cases hzS : z ∈ S
  · exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvS hxS hyS hzS hS_tight
  · set T : Finset V := insert z S with hT_def
    have hvT : v ∉ T := by
      simp only [hT_def, Finset.mem_insert, not_or]
      exact ⟨G.ne_of_adj hz, hvS⟩
    have hzT : z ∈ T := Finset.mem_insert_self z S
    have hxT : x ∈ T := Finset.mem_insert_of_mem hxS
    have hyT : y ∈ T := Finset.mem_insert_of_mem hyS
    have hxz_in_T : s(x, z) ∈ G.edgesIn (↑T : Set V) := G.mk_mem_edgesIn hxz_adj hxT hzT
    have hyz_in_T : s(y, z) ∈ G.edgesIn (↑T : Set V) := G.mk_mem_edgesIn hyz_adj hyT hzT
    have hxz_ne_yz : s(x, z) ≠ s(y, z) := fun heq =>
      (Sym2.eq_iff.mp heq).elim
        (fun ⟨h1, _⟩ => hxy h1)
        (fun ⟨h1, _⟩ => hxz h1)
    have hzS_set : z ∉ (↑S : Set V) := fun h => hzS (Finset.mem_coe.mp h)
    have hF_disj : Disjoint ({s(x, z), s(y, z)} : Set (Sym2 V)) (G.edgesIn (↑S : Set V)) := by
      rw [Set.disjoint_left]; rintro e (rfl | rfl)
      · exact notMem_edgesIn_mk_of_right_notMem hzS_set
      · exact notMem_edgesIn_mk_of_right_notMem hzS_set
    have hF_card : ({s(x, z), s(y, z)} : Set (Sym2 V)).ncard = 2 :=
      Set.ncard_pair hxz_ne_yz
    have hT_tight : G.IsTightOn 2 3 T :=
      hT_def ▸ hS_tight.insert_vertex_with_edges h hzS
        (F := {s(x, z), s(y, z)})
        (Set.insert_subset hxz_in_T (Set.singleton_subset_iff.mpr hyz_in_T))
        hF_disj (by rw [hF_card])
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight

/-- **2-pair contradiction template.** Two blockers sharing a vertex `z` (the third neighbor):
`Sxz` contains `{x, z}` and `Syz` contains `{y, z}`, with the third pair `(x, y)` adjacent.
Case-split on `2 ≤ #(Sxz ∩ Syz)`. If yes, `IsTightOn.union_inter` gives `Sxz ∪ Syz` tight,
which contains `{x, y, z}`. If no, the intersection is exactly `{z}` (size 1, contains `z`),
forcing `x ∉ Syz` and `y ∉ Sxz`; the cross-edge `s(x, y)` lies in `edgesIn (Sxz ∪ Syz)` but in
neither `edgesIn Sxz` nor `edgesIn Syz`, saturating the squeeze at `T := Sxz ∪ Syz`. -/
theorem IsSparse.contradiction_two_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy_adj : G.Adj x y)
    {Sxz : Finset V} (hvSxz : v ∉ Sxz) (hxSxz : x ∈ Sxz) (hzSxz : z ∈ Sxz)
    (hSxz_tight : G.IsTightOn 2 3 Sxz)
    {Syz : Finset V} (hvSyz : v ∉ Syz) (hySyz : y ∈ Syz) (hzSyz : z ∈ Syz)
    (hSyz_tight : G.IsTightOn 2 3 Syz) : False := by
  classical
  set T : Finset V := Sxz ∪ Syz with hT_def
  have hvT : v ∉ T := by
    simp only [hT_def, Finset.mem_union, not_or]
    exact ⟨hvSxz, hvSyz⟩
  have hxT : x ∈ T := Finset.mem_union_left _ hxSxz
  have hyT : y ∈ T := Finset.mem_union_right _ hySyz
  have hzT : z ∈ T := Finset.mem_union_left _ hzSxz
  by_cases h_big : 2 ≤ (Sxz ∩ Syz).card
  · have ⟨hT_tight, _⟩ := hSxz_tight.union_inter hSyz_tight h (by omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight
  · push Not at h_big
    have hz_inter : z ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hzSxz, hzSyz⟩
    have h_inter_card : (Sxz ∩ Syz).card = 1 := by
      have h_ge : 1 ≤ (Sxz ∩ Syz).card := Finset.card_pos.mpr ⟨z, hz_inter⟩
      omega
    have h_inter_eq : Sxz ∩ Syz = {z} :=
      Finset.eq_singleton_of_mem_of_card_le_one hz_inter (by omega)
    have hx_nin_Syz : x ∉ Syz := by
      intro hx_in
      have : x ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hxSxz, hx_in⟩
      rw [h_inter_eq, Finset.mem_singleton] at this
      exact hxz this
    have hy_nin_Sxz : y ∉ Sxz := by
      intro hy_in
      have : y ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hy_in, hySyz⟩
      rw [h_inter_eq, Finset.mem_singleton] at this
      exact hyz this
    have hxy_in_T : s(x, y) ∈ G.edgesIn (↑T : Set V) :=
      G.mk_mem_edgesIn hxy_adj (hT_def ▸ hxT) (hT_def ▸ hyT)
    have hF_disj : Disjoint ({s(x, y)} : Set (Sym2 V))
        (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V)) := by
      rw [Set.disjoint_left]; rintro e rfl
      rintro (h_in_Sxz | h_in_Syz)
      · exact notMem_edgesIn_mk_of_right_notMem
          (fun h => hy_nin_Sxz (Finset.mem_coe.mp h)) h_in_Sxz
      · exact notMem_edgesIn_mk_of_left_notMem
          (fun h => hx_nin_Syz (Finset.mem_coe.mp h)) h_in_Syz
    have h_e_inter : (G.edgesIn (↑(Sxz ∩ Syz) : Set V)).ncard = 0 := by
      rw [h_inter_eq, Finset.coe_singleton, edgesIn_singleton]
      exact Set.ncard_empty _
    have hT_tight : G.IsTightOn 2 3 T :=
      hT_def ▸ hSxz_tight.union_with_bonus hSyz_tight h
        (Set.singleton_subset_iff.mpr hxy_in_T) hF_disj
        (by rw [Set.ncard_singleton, h_inter_card]; omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight

/-- **2-pair contradiction auxiliary.** Two tight blockers `S₁, S₂` (each avoiding `v`) whose
intersection has size `≥ 2` give a tight union `S₁ ∪ S₂` via `IsTightOn.union_inter`; if that
union covers three distinct neighbors `a, b, c` of `v`, `no_isTightOn_excluding_three_neighbors`
closes. Used inside `IsSparse.contradiction_three_pair` to dispatch the three pair cases
uniformly regardless of which side of the union each neighbor sits on. -/
private theorem IsSparse.contradiction_pair_aux
    [Finite V] [DecidableEq V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S₁ S₂ : Finset V} (hvS₁ : v ∉ S₁) (hvS₂ : v ∉ S₂)
    (haU : a ∈ S₁ ∪ S₂) (hbU : b ∈ S₁ ∪ S₂) (hcU : c ∈ S₁ ∪ S₂)
    (hS₁_tight : G.IsTightOn 2 3 S₁) (hS₂_tight : G.IsTightOn 2 3 S₂)
    (h_inter : 2 ≤ (S₁ ∩ S₂).card) : False := by
  have ⟨hT_tight, _⟩ := hS₁_tight.union_inter hS₂_tight h (by omega)
  exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
    (by simp only [Finset.mem_union, not_or]; exact ⟨hvS₁, hvS₂⟩)
    haU hbU hcU hT_tight

/-- **3-pair contradiction template.** Three blockers covering all three pairs of `v`'s neighbors;
non-adjacency is only required at the "outer" pair `(b, c)`. If any pairwise intersection has
size `≥ 2`, that pair's union is tight (`IsTightOn.union_inter`) and contains `{a, b, c}`.
Otherwise all three pairwise intersections are singletons, the pairwise-disjoint edge sets
accumulate without overlap, and the third-pair intersection `(Sab ∪ Sac) ∩ Sbc = {b, c}`
contributes zero edges (since `(b, c)` is non-adj here), saturating the squeeze at
`T := Sab ∪ Sac ∪ Sbc`. -/
theorem IsSparse.contradiction_three_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbc_nadj : ¬ G.Adj b c)
    {Sab : Finset V} (hvSab : v ∉ Sab) (haSab : a ∈ Sab) (hbSab : b ∈ Sab)
    (hSab_tight : G.IsTightOn 2 3 Sab)
    {Sac : Finset V} (hvSac : v ∉ Sac) (haSac : a ∈ Sac) (hcSac : c ∈ Sac)
    (hSac_tight : G.IsTightOn 2 3 Sac)
    {Sbc : Finset V} (hvSbc : v ∉ Sbc) (hbSbc : b ∈ Sbc) (hcSbc : c ∈ Sbc)
    (hSbc_tight : G.IsTightOn 2 3 Sbc) : False := by
  classical
  by_cases h_ab_ac : 2 ≤ (Sab ∩ Sac).card
  · exact IsSparse.contradiction_pair_aux h ha hb hc hab hac hbc hvSab hvSac
      (Finset.mem_union_left _ haSab) (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSac) hSab_tight hSac_tight h_ab_ac
  by_cases h_ab_bc : 2 ≤ (Sab ∩ Sbc).card
  · exact IsSparse.contradiction_pair_aux h ha hb hc hab hac hbc hvSab hvSbc
      (Finset.mem_union_left _ haSab) (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSbc) hSab_tight hSbc_tight h_ab_bc
  by_cases h_ac_bc : 2 ≤ (Sac ∩ Sbc).card
  · exact IsSparse.contradiction_pair_aux h ha hb hc hab hac hbc hvSac hvSbc
      (Finset.mem_union_left _ haSac) (Finset.mem_union_right _ hbSbc)
      (Finset.mem_union_left _ hcSac) hSac_tight hSbc_tight h_ac_bc
  push Not at h_ab_ac h_ab_bc h_ac_bc
  have hab_ac_card : (Sab ∩ Sac).card = 1 := by
    have : 1 ≤ (Sab ∩ Sac).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨haSab, haSac⟩⟩
    omega
  have hab_bc_card : (Sab ∩ Sbc).card = 1 := by
    have : 1 ≤ (Sab ∩ Sbc).card :=
      Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨hbSab, hbSbc⟩⟩
    omega
  have hac_bc_card : (Sac ∩ Sbc).card = 1 := by
    have : 1 ≤ (Sac ∩ Sbc).card :=
      Finset.card_pos.mpr ⟨c, Finset.mem_inter.mpr ⟨hcSac, hcSbc⟩⟩
    omega
  have hab_ac_eq : Sab ∩ Sac = {a} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨haSab, haSac⟩) (by omega)
  have hab_bc_eq : Sab ∩ Sbc = {b} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨hbSab, hbSbc⟩) (by omega)
  have hac_bc_eq : Sac ∩ Sbc = {c} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨hcSac, hcSbc⟩) (by omega)
  have h_e_inter_ab_ac : (G.edgesIn (↑(Sab ∩ Sac) : Set V)).ncard = 0 := by
    rw [hab_ac_eq, Finset.coe_singleton, edgesIn_singleton]
    exact Set.ncard_empty _
  have h_super_12 : (G.edgesIn (↑Sab : Set V)).ncard + (G.edgesIn (↑Sac : Set V)).ncard
      ≤ (G.edgesIn (↑(Sab ∪ Sac) : Set V)).ncard := by
    have h_super := G.edgesIn_ncard_add_le (↑Sab : Set V) (↑Sac : Set V)
    have h_eq_union : (↑(Sab ∪ Sac) : Set V) = ↑Sab ∪ ↑Sac := Finset.coe_union _ _
    have h_eq_inter : (G.edgesIn (↑Sab ∩ ↑Sac : Set V)).ncard = 0 := by
      rw [← Finset.coe_inter]; exact h_e_inter_ab_ac
    rw [h_eq_union]
    omega
  have hT12_card : (Sab ∪ Sac).card = Sab.card + Sac.card - 1 := by
    have h1 := Finset.card_union_add_card_inter Sab Sac
    rw [hab_ac_card] at h1
    omega
  have h_T12_inter_Sbc_eq : (Sab ∪ Sac) ∩ Sbc = ({b, c} : Finset V) := by
    rw [Finset.union_inter_distrib_right, hab_bc_eq, hac_bc_eq]
    rfl
  have h_T12_inter_Sbc_card : ((Sab ∪ Sac) ∩ Sbc).card = 2 := by
    rw [h_T12_inter_Sbc_eq, Finset.card_pair hbc]
  have h_e_inter_T12_Sbc : (G.edgesIn (↑((Sab ∪ Sac) ∩ Sbc) : Set V)).ncard = 0 := by
    suffices h : G.edgesIn (↑((Sab ∪ Sac) ∩ Sbc) : Set V) = ∅ by
      rw [h]; exact Set.ncard_empty _
    rw [h_T12_inter_Sbc_eq]
    ext e
    refine e.ind fun p q => ?_
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_edgesIn, mem_edgeSet, Sym2.coe_mk,
               Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_insert_iff,
               Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro h_adj h_p h_q
    rcases h_p with rfl | rfl <;> rcases h_q with rfl | rfl
    · exact G.loopless.irrefl _ h_adj
    · exact hbc_nadj h_adj
    · exact hbc_nadj h_adj.symm
    · exact G.loopless.irrefl _ h_adj
  set T : Finset V := (Sab ∪ Sac) ∪ Sbc with hT_def
  have h_super_T : (G.edgesIn (↑(Sab ∪ Sac) : Set V)).ncard +
      (G.edgesIn (↑Sbc : Set V)).ncard ≤ (G.edgesIn (↑T : Set V)).ncard := by
    have h_super := G.edgesIn_ncard_add_le (↑(Sab ∪ Sac) : Set V) (↑Sbc : Set V)
    have h_eq_union : (↑T : Set V) = ↑(Sab ∪ Sac) ∪ ↑Sbc := by
      rw [hT_def]; exact Finset.coe_union _ _
    have h_eq_inter : (G.edgesIn (↑(Sab ∪ Sac) ∩ ↑Sbc : Set V)).ncard = 0 := by
      rw [← Finset.coe_inter]; exact h_e_inter_T12_Sbc
    rw [h_eq_union]
    omega
  have hT_card : T.card = Sab.card + Sac.card + Sbc.card - 3 := by
    have h1 := Finset.card_union_add_card_inter (Sab ∪ Sac) Sbc
    rw [h_T12_inter_Sbc_card, hT12_card, ← hT_def] at h1
    have hT12_ge : 1 ≤ (Sab ∪ Sac).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_union_left _ haSab⟩
    omega
  have hvT : v ∉ T := by
    simp only [hT_def, Finset.mem_union, not_or]
    exact ⟨⟨hvSab, hvSac⟩, hvSbc⟩
  have haT : a ∈ T := Finset.mem_union_left _ (Finset.mem_union_left _ haSab)
  have hbT : b ∈ T := Finset.mem_union_left _ (Finset.mem_union_left _ hbSab)
  have hcT : c ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ hcSac)
  have hT_card_ge : 3 ≤ T.card :=
    Finset.three_le_card_of_three_distinct_mem hab hac hbc haT hbT hcT
  have hT_tight : G.IsTightOn 2 3 T := h.isTightOn_of_le (by omega) (by
    grind only [IsTightOn])
  exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
    hvT haT hbT hcT hT_tight

/-- **Unified contradiction from per-pair adj-or-blocker.** Given three distinct neighbors
`a, b, c` of a vertex `v` in a `(2, 3)`-sparse graph, with each pair `(a,b), (a,c), (b,c)`
either adjacent in `G` or witnessed by a tight blocker not containing `v`, and at least one
pair non-adjacent, derive `False`.

Dispatches across 8 leaves: the all-adjacent leaf contradicts `h_some_nonadj`; the other
seven fan out by blocker count (1-pair, 2-pair, 3-pair) into the corresponding contradiction
template. The degree-three case of `IsSparse.exists_typeI_or_typeII_reverse` ends with it. -/
theorem IsSparse.False_of_pairwise_blocker_or_edge
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha_adj : G.Adj v a) (hb_adj : G.Adj v b) (hc_adj : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_ab : G.Adj a b ∨ ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ b ∈ S ∧ G.IsTightOn 2 3 S)
    (h_ac : G.Adj a c ∨ ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S)
    (h_bc : G.Adj b c ∨ ∃ S : Finset V, v ∉ S ∧ b ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S)
    (h_some_nonadj : ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c) :
    False := by
  rcases h_ab with hab_adj | ⟨Sab, hvSab, haSab, hbSab, hSab_tight⟩
  · rcases h_ac with hac_adj | ⟨Sac, hvSac, haSac, hcSac, hSac_tight⟩
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · rcases h_some_nonadj with h' | h' | h'
        · exact h' hab_adj
        · exact h' hac_adj
        · exact h' hbc_adj
      · exact IsSparse.contradiction_one_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
          hab_adj.symm hac_adj.symm hvSbc hbSbc hcSbc hSbc_tight
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_one_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
          hab_adj hbc_adj.symm hvSac haSac hcSac hSac_tight
      · exact IsSparse.contradiction_two_pair h ha_adj hb_adj hc_adj hab hac hbc
          hab_adj
          hvSac haSac hcSac hSac_tight
          hvSbc hbSbc hcSbc hSbc_tight
  · rcases h_ac with hac_adj | ⟨Sac, hvSac, haSac, hcSac, hSac_tight⟩
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_one_pair h ha_adj hb_adj hc_adj hab hac hbc
          hac_adj hbc_adj hvSab haSab hbSab hSab_tight
      · exact IsSparse.contradiction_two_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
          hac_adj
          hvSab haSab hbSab hSab_tight
          hvSbc hcSbc hbSbc hSbc_tight
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_two_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
          hbc_adj
          hvSab hbSab haSab hSab_tight
          hvSac hcSac haSac hSac_tight
      · rcases h_some_nonadj with hab_nadj | hac_nadj | hbc_nadj
        · exact IsSparse.contradiction_three_pair h hc_adj ha_adj hb_adj hac.symm hbc.symm hab
            hab_nadj
            hvSac hcSac haSac hSac_tight
            hvSbc hcSbc hbSbc hSbc_tight
            hvSab haSab hbSab hSab_tight
        · exact IsSparse.contradiction_three_pair h hb_adj ha_adj hc_adj hab.symm hbc hac
            hac_nadj
            hvSab hbSab haSab hSab_tight
            hvSbc hbSbc hcSbc hSbc_tight
            hvSac haSac hcSac hSac_tight
        · exact IsSparse.contradiction_three_pair h ha_adj hb_adj hc_adj hab hac hbc
            hbc_nadj
            hvSab haSab hbSab hSab_tight
            hvSac haSac hcSac hSac_tight
            hvSbc hbSbc hcSbc hSbc_tight

/-! ### Per-pair tight-blocker witness (typeII reverse, sparse form)

The combinatorial heart of the typeII Henneberg reverse: given a `(2, 3)`-sparse graph `G`,
a vertex `v`, vertices `x, y` both `≠ v`, and a *failed* candidate
`G' := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` — i.e. `¬ G'.IsSparse 2 3` — extract a `(2, 3)`-tight set
`S ⊆ V \ {v}` in `G` containing both `x` and `y`. The statement does not ask `x ≠ y`: at
`x = y` the bridge is a loop, which `fromEdgeSet` drops, so `G'` is `G ↾ {v}ᶜ`, which is sparse,
and the hypothesis fails. The proof lifts a sparsity-violating Finset
of `G'` along `Subtype.val` to a Finset of `V \ {v}`, then case-splits on whether the bridge
edge survives the lift (`xs, ys ∈ s'`): on the bridge-surviving side the squeeze closes via
`IsSparse.isTightOn_of_le`; on the other side the bridge is forced out and `G`'s sparsity
contradicts directly. This is the observation in Jordán's proof of his Lemma 2.1.4(b), that a
splitting is not suitable only if such a tight set exists (p. 44). -/

/-- **Per-pair tight-blocker witness for the typeII Henneberg reverse (sparse form).**

Inputs: a `(2, 3)`-sparse graph `G`; vertices `x, y` both `≠ v`; a sparsity violation on the
typeII-reverse candidate `G' := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}`.

Output: a `(2, 3)`-tight set `S` in `G` with `v ∉ S` and `{x, y} ⊆ S`.

The proof extracts a violating Finset `s'` from `¬ G'.IsSparse 2 3` and lifts it to
`S := s'.image Subtype.val ⊆ V \ {v}`. The bound `(G'.edgesIn ↑s').ncard ≤ (G.edgesIn ↑S).ncard
+ 1` (case `xs, ys ∈ s'`) combined with `G`'s sparsity at `S` gives tightness via
`IsSparse.isTightOn_of_le`; the remaining case (one of `xs, ys` outside `s'`) drops the `+1` and
contradicts `G`'s sparsity directly. -/
theorem IsSparse.typeII_reverse_blocker
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y : V}
    (hxv : x ≠ v) (hyv : y ≠ v)
    (h_not_sparse : ¬ (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
                       fromEdgeSet ({s(⟨x, hxv⟩, ⟨y, hyv⟩)} : Set (Sym2 _))).IsSparse 2 3) :
    ∃ S : Finset V, v ∉ S ∧ x ∈ S ∧ y ∈ S ∧ G.IsTightOn 2 3 S := by
  classical
  set f : {w : V // w ≠ v} → V := Subtype.val with hf_def
  set xs : {w : V // w ≠ v} := ⟨x, hxv⟩ with hxs_def
  set ys : {w : V // w ≠ v} := ⟨y, hyv⟩ with hys_def
  set bridge : Sym2 {w : V // w ≠ v} := s(xs, ys) with hbridge_def
  set G' : SimpleGraph {w : V // w ≠ v} :=
    G.comap f ⊔ fromEdgeSet ({bridge} : Set _) with hG'_def
  -- Extract violating Finset from `¬ G'.IsSparse 2 3`.
  unfold IsSparse at h_not_sparse
  push Not at h_not_sparse
  obtain ⟨s', hs'_card, hviol⟩ := h_not_sparse
  -- Lift to S = s'.image Subtype.val ⊆ V \ {v}.
  set S : Finset V := s'.image f with hS_def
  have hS_card : S.card = s'.card :=
    Finset.card_image_of_injective s' Subtype.val_injective
  have hvS : v ∉ S := by
    intro hmem
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hmem
    exact w.2 hw
  -- (G.comap f).edgesIn ↑s' has the same ncard as G.edgesIn ↑S.
  have h_link : ((G.comap f).edgesIn (↑s' : Set _)).ncard = (G.edgesIn (↑S : Set V)).ncard :=
    G.ncard_edgesIn_comap Subtype.val_injective s'
  -- G's sparsity at S.
  have hS_sparse : (G.edgesIn (↑S : Set V)).ncard + 3 ≤ 2 * S.card := by
    have := h S (by rw [hS_card]; exact hs'_card)
    exact this
  -- Case-split on whether both xs, ys ∈ s'.
  by_cases h_both : xs ∈ s' ∧ ys ∈ s'
  · -- Case 1: bridge potentially in G'.edgesIn ↑s'. Bound by (G.edgesIn ↑S).ncard + 1.
    obtain ⟨hxs_in, hys_in⟩ := h_both
    have h_subset : G'.edgesIn (↑s' : Set _) ⊆
        (G.comap f).edgesIn (↑s' : Set _) ∪ ({bridge} : Set _) := by
      intro e he
      rw [mem_edgesIn] at he
      obtain ⟨he_edge, he_sub⟩ := he
      rw [hG'_def, edgeSet_sup] at he_edge
      rcases he_edge with hin_comap | hin_bridge
      · exact Or.inl (mem_edgesIn.mpr ⟨hin_comap, he_sub⟩)
      · rw [edgeSet_fromEdgeSet] at hin_bridge
        exact Or.inr (Set.sdiff_subset hin_bridge)
    have h_ncard_bound : (G'.edgesIn (↑s' : Set _)).ncard ≤
        (G.edgesIn (↑S : Set V)).ncard + 1 :=
      calc (G'.edgesIn (↑s' : Set _)).ncard
          ≤ ((G.comap f).edgesIn (↑s' : Set _) ∪ ({bridge} : Set _)).ncard :=
            Set.ncard_le_ncard h_subset (Set.toFinite _)
        _ ≤ ((G.comap f).edgesIn (↑s' : Set _)).ncard + ({bridge} : Set _).ncard :=
            Set.ncard_union_le _ _
        _ = (G.edgesIn (↑S : Set V)).ncard + 1 := by
            rw [h_link, Set.ncard_singleton]
    have hx_in_S : x ∈ S := by
      simp only [hS_def, Finset.mem_image]
      exact ⟨xs, hxs_in, rfl⟩
    have hy_in_S : y ∈ S := by
      simp only [hS_def, Finset.mem_image]
      exact ⟨ys, hys_in, rfl⟩
    refine ⟨S, hvS, hx_in_S, hy_in_S, ?_⟩
    refine h.isTightOn_of_le ?_ ?_
    · rw [hS_card]; exact hs'_card
    · rw [hS_card]; omega
  · -- Case 2: one of xs, ys not in s'. Bridge excluded; bound by (G.edgesIn ↑S).ncard.
    have h_subset : G'.edgesIn (↑s' : Set _) ⊆ (G.comap f).edgesIn (↑s' : Set _) := by
      intro e he
      rw [mem_edgesIn] at he ⊢
      obtain ⟨he_edge, he_sub⟩ := he
      refine ⟨?_, he_sub⟩
      rw [hG'_def, edgeSet_sup] at he_edge
      rcases he_edge with hin_comap | hin_bridge
      · exact hin_comap
      · rw [edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_singleton_iff] at hin_bridge
        obtain ⟨rfl, _⟩ := hin_bridge
        rw [hbridge_def, Sym2.coe_mk, Set.insert_subset_iff,
            Set.singleton_subset_iff, Finset.mem_coe, Finset.mem_coe] at he_sub
        exact absurd he_sub h_both
    have h_ncard_bound : (G'.edgesIn (↑s' : Set _)).ncard ≤
        (G.edgesIn (↑S : Set V)).ncard := by
      rw [← h_link]
      exact Set.ncard_le_ncard h_subset (Set.toFinite _)
    exfalso
    rw [hS_card] at hS_sparse
    omega

/-! ### Flat-form Henneberg reverse decomposition

In a `(2, 3)`-sparse graph with at least one edge, a Henneberg reverse step exists distinguished
by `G.degree v ∈ {1, 2, 3}`: pendant reverse (delete a degree-1 vertex), Type I reverse (delete
a degree-2 vertex), or Type II reverse (split a degree-3 vertex with a non-adjacent neighbour
pair). The Laman form `Henneberg.IsLaman.exists_typeI_or_typeII_reverse`
(`HennebergReverse.lean`) is derived from it. It is stated in **flat form** per `DESIGN.md`
*Statement-form conventions*: the conclusion describes the smaller graph by its edges directly
(`G - v` as `G.comap Subtype.val`, the typeII candidate as
`G.comap Subtype.val ⊔ fromEdgeSet {bridge}`) rather than via the `typeI` / `typeII` Henneberg
operations.

Proof structure (Jordán's proof of his Theorem 2.2.1, p. 45, for the vertex, and his Lemma
2.1.4, p. 44, for the cases of degree two and three): pick a vertex `v` with
`1 ≤ G.degree v ≤ 3` via `IsSparse.exists_one_le_degree_le_three`; split on
`G.degree v ∈ {1, 2, 3}`. The pendant (`= 1`) and Type I (`= 2`) cases close via
`IsSparse.comap` after extracting neighbour data from `card_eq_one` / `card_eq_two`. The `= 3`
case runs the per-pair witness-or-blocker dispatch using `IsSparse.typeII_reverse_blocker` and
combines three blockers via `IsSparse.False_of_pairwise_blocker_or_edge`. -/

/-- Per-pair Type II dispatch helper for `IsSparse.exists_typeI_or_typeII_reverse`. For a
degree-3 vertex `v` with three distinct neighbours `x, y, c`, the pair `(x, y)` yields one of
three mutually exclusive outcomes: a Type II witness (when `x, y` are non-adjacent and the
augmented graph is sparse — short-circuits the outer proof), an edge `G.Adj x y` (fed into
`False_of_pairwise_blocker_or_edge`), or a tight blocker via `typeII_reverse_blocker`. The
three per-pair branches `h_ab` / `h_ac` / `h_bc` in `exists_typeI_or_typeII_reverse` each
consume one application of this helper. -/
private theorem IsSparse.typeII_pair_dispatch_aux
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3)
    {v : V} (x y c : {w : V // w ≠ v})
    (hxy : x.val ≠ y.val) (hcx : c.val ≠ x.val) (hcy : c.val ≠ y.val)
    (hN_iff : ∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) :
    (∃ x' y' c' : {w : V // w ≠ v}, x' ≠ y' ∧ c' ≠ x' ∧ c' ≠ y' ∧
        (∀ w : V, G.Adj v w ↔ w = x'.val ∨ w = y'.val ∨ w = c'.val) ∧
        ¬ G.Adj x'.val y'.val ∧
        (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
          fromEdgeSet ({s(x', y')} : Set _)).IsSparse 2 3)
      ∨ G.Adj x.val y.val
      ∨ ∃ S : Finset V, v ∉ S ∧ x.val ∈ S ∧ y.val ∈ S ∧ G.IsTightOn 2 3 S := by
  classical
  by_cases hxy_adj : G.Adj x.val y.val
  · exact Or.inr (Or.inl hxy_adj)
  · by_cases hsparse : (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _)).IsSparse 2 3
    · exact Or.inl ⟨x, y, c,
        fun heq => hxy (congrArg Subtype.val heq),
        fun heq => hcx (congrArg Subtype.val heq),
        fun heq => hcy (congrArg Subtype.val heq),
        hN_iff, hxy_adj, hsparse⟩
    · exact Or.inr (Or.inr (h.typeII_reverse_blocker x.2 y.2 hsparse))

/-- **Flat-form Henneberg reverse decomposition (Jordán, Lemma 2.1.4 and Theorem 2.2.1).**
Every `(2, 3)`-sparse graph with at least one edge admits a Henneberg reverse to a smaller
`(2, 3)`-sparse graph, distinguished by `G.degree v ∈ {1, 2, 3}`:

* **Pendant reverse** (`G.degree v = 1`): the unique neighbour `a` of `v` is exposed and
  the induced subgraph on `{w // w ≠ v}` is `(2, 3)`-sparse.
* **Type I reverse** (`G.degree v = 2`): the two distinct neighbours `a ≠ b` of `v` are
  exposed and the induced subgraph on `{w // w ≠ v}` is `(2, 3)`-sparse.
* **Type II reverse** (`G.degree v = 3`): three neighbours `x, y, c` of `v` are exposed,
  along with a non-adjacent pair `(x, y)`, such that the induced subgraph augmented with the
  bridging edge `s(x, y)` is `(2, 3)`-sparse.

The cases of degree two and three are Jordán's Lemma 2.1.4 (p. 44); the vertex of degree one,
two or three, and the case of degree one, are from his proof of Theorem 2.2.1 (p. 45).
`Henneberg.IsLaman.exists_typeI_or_typeII_reverse` is derived from this theorem. Stated
in flat form: the smaller graphs are described by their explicit edge constructions rather
than via the typeI / typeII Henneberg operations (see `DESIGN.md` *Statement-form
conventions*). The row-independence induction `IsSparse.exists_rowIndependent_placement`
(`MatroidIdentification.lean`) reconstructs the operation form at each step via
`isoTypeIOfTwoNeighbors` / `isoTypeIIOfThreeNeighbors` (`HennebergReverse.lean`). Its
pendant branch invokes `isoTypeIOfTwoNeighbors` at `a = b` (the unique neighbour):
`typeI G' a a` joins the new vertex to a single old vertex. -/
theorem IsSparse.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hE : G.edgeSet.Nonempty) :
    ∃ v : V,
      (G.degree v = 1 ∧
        ∃ a : {w : V // w ≠ v},
          (∀ w : V, G.Adj v w ↔ w = a.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsSparse 2 3)
      ∨
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsSparse 2 3)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsSparse 2 3) := by
  classical
  obtain ⟨v, hv1, hv3⟩ := h.exists_one_le_degree_le_three hE
  refine ⟨v, ?_⟩
  -- Case split on `G.degree v ∈ {1, 2, 3}`. Pendant and Type I close via `IsSparse.comap` after
  -- extracting neighbour data; Type II runs the existing per-pair witness/blocker dispatch.
  rcases (show G.degree v = 1 ∨ G.degree v = 2 ∨ G.degree v = 3 from by omega)
    with hdeg1 | hdeg2 | hdeg3
  · -- Pendant branch: `card_eq_one` extracts the unique neighbour `a`.
    obtain ⟨a, hN_eq⟩ := Finset.card_eq_one.mp hdeg1
    have hN_iff : ∀ w, G.Adj v w ↔ w = a := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr rfl
    have hva : v ≠ a := G.ne_of_adj ha_adj
    exact Or.inl ⟨hdeg1, ⟨a, hva.symm⟩, hN_iff, h.comap Subtype.val_injective⟩
  · -- Type I branch: `card_eq_two` extracts the two distinct neighbours `a, b`.
    obtain ⟨a, b, hab, hN_eq⟩ := Finset.card_eq_two.mp hdeg2
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr rfl)
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hab_s : (⟨a, hva.symm⟩ : {w : V // w ≠ v}) ≠ ⟨b, hvb.symm⟩ :=
      fun heq => hab (Subtype.mk.injEq .. |>.mp heq)
    exact Or.inr (Or.inl ⟨hdeg2, ⟨a, hva.symm⟩, ⟨b, hvb.symm⟩, hab_s, hN_iff,
      h.comap Subtype.val_injective⟩)
  · -- Type II branch: degree v = 3. For each pair of neighbors, dispatch
    -- `witness ∨ Adj ∨ blocker`; short-circuit on any witness; otherwise feed the three
    -- `Adj ∨ blocker` disjunctions to `IsSparse.False_of_pairwise_blocker_or_edge` together
    -- with the non-adj disjunction from `IsSparse.exists_nonadj_among_three_neighbors`.
    refine Or.inr (Or.inr ⟨hdeg3, ?_⟩)
    obtain ⟨a, b, c, hab, hac, hbc, hN_eq⟩ := Finset.card_eq_three.mp hdeg3
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr (Or.inl rfl))
    have hc_adj : G.Adj v c := (hN_iff c).mpr (Or.inr (Or.inr rfl))
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hvc : v ≠ c := G.ne_of_adj hc_adj
    have hN_iff_acb : ∀ w, G.Adj v w ↔ w = a ∨ w = c ∨ w = b := fun w => by
      rw [hN_iff]; tauto
    have hN_iff_bca : ∀ w, G.Adj v w ↔ w = b ∨ w = c ∨ w = a := fun w => by
      rw [hN_iff]; tauto
    -- Per-pair dispatch: `witness ∨ Adj ∨ blocker` via `typeII_pair_dispatch_aux`. The
    -- blocker side feeds into `False_of_pairwise_blocker_or_edge`; the witness side short-
    -- circuits the outer proof.
    have h_ab := h.typeII_pair_dispatch_aux ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩
      hab hac.symm hbc.symm hN_iff
    have h_ac := h.typeII_pair_dispatch_aux ⟨a, hva.symm⟩ ⟨c, hvc.symm⟩ ⟨b, hvb.symm⟩
      hac hab.symm hbc hN_iff_acb
    have h_bc := h.typeII_pair_dispatch_aux ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ ⟨a, hva.symm⟩
      hbc hab hac hN_iff_bca
    rcases h_ab with witness | h_ab
    · exact witness
    rcases h_ac with witness | h_ac
    · exact witness
    rcases h_bc with witness | h_bc
    · exact witness
    exact absurd
      (h.False_of_pairwise_blocker_or_edge ha_adj hb_adj hc_adj hab hac hbc h_ab h_ac h_bc
        (h.exists_nonadj_among_three_neighbors ha_adj hb_adj hc_adj hab hac hbc)) id

end SimpleGraph

-- Matroidal-regime I-components (`HasBlock`, `maxBlock`, `IsSparse.maxBlock_*`) and the
-- augmentation lemma `IsSparse.exists_aug_of_lt_two_mul` live in
-- `CombinatorialRigidity/SparsityIComponents.lean`. Files that need only the base
-- `(k, ℓ)`-sparsity API import this file alone; `CountMatroid.lean`, which uses the
-- augmentation lemma, imports `SparsityIComponents.lean`.


end
end BundleSource0009

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityFoundations01/block_0009/Consolidated/RigidityFoundations01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityFoundations01/checkpoint_0009.json"
