module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.SetTheory.Cardinal.Finite
public import paper_verification.literal002
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import paper_verification.literal001
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import paper_verification.literal000
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option Elab.async false

section TAF_LiteralSource_0167
/- Original module: TauCeti.GroupTheory.Perm.FiberSubgroup -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Permutations preserving the fibers of a map

Given `f : α → ι`, the permutations `σ` of `α` with `f (σ a) = f a` for every `a` form a subgroup
of `Equiv.Perm α`, here called `TauCeti.fiberSubgroup f`.  This file records that subgroup, the
transpositions it contains, the behaviour of the construction under conjugation, composition and
pairing two maps, the unions of fibers it preserves, its description for the two summands of
`α ⊕ β` as the image of `Equiv.Perm.sumCongrHom` (`TauCeti.fiberSubgroup_isLeft`), the criteria
for it to be trivial and for it to be a point stabilizer, and the isomorphism
restricting a fiber-preserving permutation to each fiber,

`fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i}`,

together with the two formulas reading that isomorphism, and its inverse, through a family of
equivalences `{a // f a = i} ≃ β i` of the fibers, which is how a concrete description of the
fibers is fed into it.

For finite `α` the cosets of `fiberSubgroup f` are the rearrangements of `f`: the coset of `g`
records the map `f ∘ g⁻¹`, and this identifies `Equiv.Perm α ⧸ fiberSubgroup f`, equivariantly,
with the maps `α → ι` having fibers of the same sizes as those of `f`
(`TauCeti.quotientFiberSubgroupEquiv`).  When the fibers of `f` are the rows of a tabloid this is
the description of the tabloids as the row-colourings of `α`, and the fixed points of a
permutation `π` on the cosets are the rearrangements `c` with `c ∘ π = c`
(`TauCeti.card_fixedPoints_quotient_fiberSubgroup`).

The order of `fiberSubgroup f` is the product of the factorials of the fiber sizes
(`TauCeti.natCard_fiberSubgroup`).  Summing these orders over all colourings `α → ι`, each
weighted by a function of its fiber sizes, therefore gives `(card α)!` times the sum of the weight
over the fiber-size functions of total `card α` (`TauCeti.sum_natCard_fiberSubgroup_smul`), the
orbit-stabilizer count that averages power sums over the symmetric group.

Mathlib already studies these permutations, but through the domain action of `Equiv.Perm α` on
`α → ι`: `DomMulAct.stabilizerMulEquiv` is the same isomorphism stated on
`(MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ`.  The `ᵈᵐᵃ`/`ᵐᵒᵖ` wrapping makes it awkward to use
where the object of interest is a subgroup of `Equiv.Perm α` itself, as it is for the row and
column groups of a Young tableau; `fiberSubgroup` is that subgroup.  The two presentations are
identified by `fiberSubgroupMulEquivStabilizer`, and the isomorphism above is Mathlib's
`DomMulAct.stabilizerMulEquiv` transported along it.
-/

public section

namespace TauCeti

variable {α ι κ : Type*}

/-- The subgroup of permutations of `α` that preserve every fiber of `f : α → ι`, that is, those
moving each point within its own fiber. -/
def fiberSubgroup (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  mul_mem' hσ hτ a := (hσ _).trans (hτ a)
  one_mem' _ := rfl
  inv_mem' {σ} hσ a := by
    have h := hσ (σ⁻¹ a)
    rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h

@[simp]
theorem mem_fiberSubgroup {f : α → ι} {σ : Equiv.Perm α} :
    σ ∈ fiberSubgroup f ↔ ∀ a, f (σ a) = f a :=
  Iff.rfl

/-- The transposition of two points lying in a common fiber of `f` preserves every fiber of `f`:
it moves each of the two points to the other, inside their shared fiber, and fixes the rest. -/
theorem swap_mem_fiberSubgroup [DecidableEq α] {f : α → ι} {x y : α} (h : f x = f y) :
    Equiv.swap x y ∈ fiberSubgroup f := by
  rw [mem_fiberSubgroup]
  intro a
  rcases eq_or_ne a x with rfl | hax
  · rw [Equiv.swap_apply_left, h]
  · rcases eq_or_ne a y with rfl | hay
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

/-- Conjugation by `e` transports the subgroup preserving the fibers of `f` to the subgroup
preserving the fibers of `g` when `e` identifies their fiber equivalence relations. -/
theorem fiberSubgroup_map_conj {f : α → ι} {g : α → κ} (e : Equiv.Perm α)
    (h : ∀ a b, f a = f b ↔ g (e a) = g (e b)) :
    (fiberSubgroup f).map (MulAut.conj e).toMonoidHom = fiberSubgroup g := by
  ext σ
  rw [Subgroup.mem_map_equiv, mem_fiberSubgroup, mem_fiberSubgroup]
  constructor
  · intro hσ a
    have hfa : f (e.symm (σ a)) = f (e.symm a) := by
      simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e.symm a)
    have ha := (h (e.symm (σ a)) (e.symm a)).mp hfa
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using ha
  · intro hσ a
    apply (h _ _).mpr
    simpa only [MulAut.conj_symm_apply, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hσ (e a)

/-- Composing with an injective map does not change the fibers of `f`, hence neither the
permutations preserving them. -/
theorem fiberSubgroup_comp_of_injective {g : ι → κ} (hg : Function.Injective g) (f : α → ι) :
    fiberSubgroup (g ∘ f) = fiberSubgroup f := by
  ext σ
  simp only [mem_fiberSubgroup, Function.comp_apply, hg.eq_iff]

/-- Composing with any map merges fibers of `f`, so it only enlarges the subgroup preserving
them. -/
theorem fiberSubgroup_le_comp (g : ι → κ) (f : α → ι) :
    fiberSubgroup f ≤ fiberSubgroup (g ∘ f) :=
  fun _ hσ a ↦ congrArg g (hσ a)

/-- A map to a subsingleton has a single fiber, preserved by every permutation. -/
theorem fiberSubgroup_eq_top [Subsingleton ι] (f : α → ι) : fiberSubgroup f = ⊤ :=
  eq_top_iff.mpr fun _ _ _ ↦ Subsingleton.elim _ _

/-- A fiber-preserving permutation maps each union `f ⁻¹' T` of fibers onto itself. -/
theorem image_preimage_of_mem_fiberSubgroup {f : α → ι} {σ : Equiv.Perm α}
    (hσ : σ ∈ fiberSubgroup f) (T : Set ι) : σ '' (f ⁻¹' T) = f ⁻¹' T := by
  ext a
  refine ⟨?_, fun ha ↦ ⟨σ.symm a, ?_, σ.apply_symm_apply a⟩⟩
  · rintro ⟨b, hb, rfl⟩
    rwa [Set.mem_preimage, hσ b]
  · rwa [Set.mem_preimage, ← hσ (σ.symm a), Equiv.apply_symm_apply]

/-- **Two fibers.**  The permutations of `α ⊕ β` preserving the summand of each point are those
acting separately on the two summands, the image of `Equiv.Perm.sumCongrHom`. -/
theorem fiberSubgroup_isLeft (α β : Type*) :
    fiberSubgroup (Sum.isLeft : α ⊕ β → Bool) = (Equiv.Perm.sumCongrHom α β).range := by
  ext σ
  constructor
  · intro h
    have hl (x : α ⊕ β) : (σ x).isLeft ↔ x.isLeft := by rw [h x]
    have hr (x : α ⊕ β) : (σ x).isRight ↔ x.isRight := by
      rw [← Sum.not_isLeft, ← Sum.not_isLeft, h x]
    refine ⟨(Equiv.sumIsLeft.permCongr (σ.subtypePerm hl),
      Equiv.sumIsRight.permCongr (σ.subtypePerm hr)), Equiv.ext ?_⟩
    rintro (a | b)
    · obtain ⟨a', ha'⟩ := Sum.isLeft_iff.mp ((hl (.inl a)).mpr rfl)
      simp [ha']
    · obtain ⟨b', hb'⟩ := Sum.isRight_iff.mp ((hr (.inr b)).mpr rfl)
      simp [hb']
  · rintro ⟨⟨σ₁, σ₂⟩, rfl⟩ (a | b) <;> simp

/-- Preserving the fibers of two maps at once is preserving the fibers of the paired map. -/
theorem fiberSubgroup_inf (f : α → ι) (g : α → κ) :
    fiberSubgroup f ⊓ fiberSubgroup g = fiberSubgroup fun a => (f a, g a) := by
  ext σ
  simp [Subgroup.mem_inf, Prod.ext_iff, forall_and]

/-- **A map whose fibers are `{a}` and at most one other makes the fiber subgroup a point
stabilizer.**  If `f` separates `a` from every other point and identifies all the others with one
another, then a permutation preserves the fibers of `f` exactly when it fixes `a`: the fiber `{a}`
can only be mapped to itself, and its complement -- a second fiber when it is nonempty, and empty
when `α = {a}` -- then takes care of itself. -/
theorem fiberSubgroup_eq_stabilizer {f : α → ι} {a : α} (hsep : ∀ x, x ≠ a → f x ≠ f a)
    (hrest : ∀ x y, x ≠ a → y ≠ a → f x = f y) :
    fiberSubgroup f = MulAction.stabilizer (Equiv.Perm α) a := by
  ext σ
  rw [mem_fiberSubgroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  constructor
  · intro hσ
    by_contra hne
    exact hsep (σ a) hne (hσ a)
  · intro hσ x
    rcases eq_or_ne x a with rfl | hx
    · rw [hσ]
    · exact hrest _ _ (fun h => hx (σ.injective (h.trans hσ.symm))) hx

/-- Only the identity preserves the fibers of an injective map, its fibers being singletons. -/
theorem fiberSubgroup_eq_bot_of_injective {f : α → ι} (hf : Function.Injective f) :
    fiberSubgroup f = ⊥ :=
  eq_bot_iff.mpr fun _ hσ => Subgroup.mem_bot.mpr (Equiv.ext fun a => hf (hσ a))

/-- If the identity is the only permutation preserving the fibers of `f`, then `f` is injective:
two points in a common fiber would be exchanged by a nontrivial fiber-preserving transposition. -/
theorem injective_of_fiberSubgroup_eq_bot {f : α → ι}
    (h : fiberSubgroup f = ⊥) : Function.Injective f := by
  classical
  intro a b hab
  by_contra hne
  have hswap : Equiv.swap a b ∈ fiberSubgroup f := swap_mem_fiberSubgroup hab
  rw [h, Subgroup.mem_bot, Equiv.Perm.one_def] at hswap
  exact hne (Equiv.swap_eq_refl_iff.mp hswap)

/-- The fibers of `f` are preserved only by the identity exactly when `f` is injective. -/
theorem fiberSubgroup_eq_bot_iff {f : α → ι} :
    fiberSubgroup f = ⊥ ↔ Function.Injective f :=
  ⟨injective_of_fiberSubgroup_eq_bot, fiberSubgroup_eq_bot_of_injective⟩

/-- The permutations preserving the fibers of `f` are the stabilizer of `f` for the domain action
of `Equiv.Perm α` on `α → ι`, read as a subgroup of `Equiv.Perm α` itself: the `ᵈᵐᵃ` and `ᵐᵒᵖ`
synonyms reverse multiplication twice, so `σ ↦ DomMulAct.mk σ` is an isomorphism. -/
def fiberSubgroupMulEquivStabilizer (f : α → ι) :
    fiberSubgroup f ≃* (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ where
  toFun σ := MulOpposite.op ⟨DomMulAct.mk (σ : Equiv.Perm α),
    DomMulAct.mem_stabilizer_iff.mpr (funext (mem_fiberSubgroup.mp σ.2))⟩
  invFun g := ⟨DomMulAct.mk.symm (g.unop : (Equiv.Perm α)ᵈᵐᵃ),
    mem_fiberSubgroup.mpr (congrFun (DomMulAct.mem_stabilizer_iff.mp g.unop.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Read in `(Equiv.Perm α)ᵈᵐᵃ`, the stabilizer element attached to a fiber-preserving permutation
is that permutation. -/
-- This is the defining equation of `fiberSubgroupMulEquivStabilizer`: its `toFun` is literally
-- `fun σ => MulOpposite.op ⟨DomMulAct.mk σ, _⟩`, so after `unop` and the subtype coercion the two
-- sides are the same term and `rfl` proves it.  The definition is deliberately not `@[expose]`d, so
-- the pre-bump `simp [fiberSubgroupMulEquivStabilizer]` has nothing to unfold; the parentheses in
-- `(rfl)` keep the definitional step inside this module, leaving this lemma and
-- `fiberSubgroupMulEquivStabilizer_symm_apply_coe` as the whole interface for importers.
@[simp]
theorem fiberSubgroupMulEquivStabilizer_apply_unop_coe (f : α → ι) (σ : fiberSubgroup f) :
    ((fiberSubgroupMulEquivStabilizer f σ).unop : (Equiv.Perm α)ᵈᵐᵃ) =
      DomMulAct.mk (σ : Equiv.Perm α) := (rfl)

/-- Read in `Equiv.Perm α`, the fiber-preserving permutation attached to an element of the
stabilizer is that element. -/
@[simp]
theorem fiberSubgroupMulEquivStabilizer_symm_apply_coe (f : α → ι)
    (g : (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) :
    (((fiberSubgroupMulEquivStabilizer f).symm g : fiberSubgroup f) : Equiv.Perm α) =
      DomMulAct.mk.symm (g.unop : (Equiv.Perm α)ᵈᵐᵃ) := by
  conv_rhs => rw [← (fiberSubgroupMulEquivStabilizer f).apply_symm_apply g]
  rw [fiberSubgroupMulEquivStabilizer_apply_unop_coe, Equiv.symm_apply_apply]

/-- Restricting a fiber-preserving permutation of `α` to each fiber of `f` is an isomorphism onto
the product of the permutation groups of the fibers.

This is Mathlib's `DomMulAct.stabilizerMulEquiv` transported along
`fiberSubgroupMulEquivStabilizer`. -/
def fiberSubgroupMulEquivPiPerm (f : α → ι) :
    fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i} :=
  (fiberSubgroupMulEquivStabilizer f).trans (DomMulAct.stabilizerMulEquiv f)

@[simp]
theorem fiberSubgroupMulEquivPiPerm_apply_coe (f : α → ι) (σ : fiberSubgroup f) (i : ι)
    (a : {a // f a = i}) : (fiberSubgroupMulEquivPiPerm f σ i a : α) = (σ : Equiv.Perm α) a := by
  obtain ⟨a, ha⟩ := a
  rw [fiberSubgroupMulEquivPiPerm, MulEquiv.trans_apply,
    DomMulAct.stabilizerMulEquiv_apply _ ha, fiberSubgroupMulEquivStabilizer_apply_unop_coe,
    Equiv.symm_apply_apply]

/-- The fiber-preserving permutation assembled from a family of permutations of the fibers of `f`
moves each point by the permutation of its own fiber. -/
@[simp]
theorem fiberSubgroupMulEquivPiPerm_symm_apply (f : α → ι)
    (σ : ∀ i, Equiv.Perm {a // f a = i}) (a : α) :
    ((fiberSubgroupMulEquivPiPerm f).symm σ : Equiv.Perm α) a = (σ (f a) ⟨a, rfl⟩ : α) := by
  conv_rhs => rw [← (fiberSubgroupMulEquivPiPerm f).apply_symm_apply σ]
  rw [fiberSubgroupMulEquivPiPerm_apply_coe]

section Transport

variable {β : ι → Type*}

/-- Reading `fiberSubgroupMulEquivPiPerm f` through equivalences `e i : {a // f a = i} ≃ β i` of
the fibers of `f`: the `i`-th component takes the point of `β i` matching `a` to the one matching
`σ a`.  Specialising this to a concrete family of fibers gives the component formula for the
transported isomorphism. -/
theorem fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply (f : α → ι)
    (e : ∀ i, {a // f a = i} ≃ β i) (σ : fiberSubgroup f) (i : ι) (a : {a // f a = i}) :
    (fiberSubgroupMulEquivPiPerm f).trans
        (MulEquiv.piCongrRight fun i => (e i).permCongrHom) σ i (e i a) =
      e i ⟨(σ : Equiv.Perm α) a, (mem_fiberSubgroup.mp σ.2 a).trans a.2⟩ := by
  rw [MulEquiv.trans_apply, MulEquiv.piCongrRight_apply, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact congrArg (e i) (Subtype.ext (fiberSubgroupMulEquivPiPerm_apply_coe f σ i a))

/-- Reading the inverse of `fiberSubgroupMulEquivPiPerm f` through equivalences
`e i : {a // f a = i} ≃ β i` of the fibers of `f`: the assembled permutation moves each point by
the permutation of its own fiber, read through `e`. -/
theorem fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply (f : α → ι)
    (e : ∀ i, {a // f a = i} ≃ β i) (σ : ∀ i, Equiv.Perm (β i)) (a : α) :
    ((((fiberSubgroupMulEquivPiPerm f).trans
        (MulEquiv.piCongrRight fun i => (e i).permCongrHom)).symm σ : Equiv.Perm α) a : α) =
      ((e (f a)).symm (σ (f a) (e (f a) ⟨a, rfl⟩)) : α) := by
  rw [MulEquiv.symm_trans_apply, fiberSubgroupMulEquivPiPerm_symm_apply,
    MulEquiv.piCongrRight_symm, MulEquiv.piCongrRight_apply, Equiv.permCongrHom_symm,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm]

end Transport

section Quotient

open Finset

variable [Fintype α]

/-- Local decidable equality for computing fiber cardinalities without an API constraint. -/
noncomputable local instance instDecidableEqFiberColour : DecidableEq ι := Classical.decEq ι

/-- **The cosets of the fiber subgroup of `f` are the rearrangements of `f`.**  The coset of `g`
in `Equiv.Perm α ⧸ fiberSubgroup f` is sent to the map `f ∘ g⁻¹`
(`TauCeti.quotientFiberSubgroupEquiv_mk`), and every map with fibers of the same sizes as those of
`f` arises in exactly one way.  The equivalence intertwines the left action of `Equiv.Perm α` on
the cosets with its action `c ↦ c ∘ π⁻¹` on maps (`TauCeti.quotientFiberSubgroupEquiv_smul`). -/
noncomputable def quotientFiberSubgroupEquiv (f : α → ι) :
    Equiv.Perm α ⧸ fiberSubgroup f ≃ {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} :=
  Equiv.ofBijective
    (Quotient.lift (fun g : Equiv.Perm α => ⟨f ∘ ⇑g⁻¹, card_filter_comp_perm f g⁻¹⟩)
      fun g h hgh => Subtype.ext <| funext fun a => by
        have hk := mem_fiberSubgroup.mp (QuotientGroup.leftRel_apply.mp hgh)
        simpa only [Equiv.Perm.coe_inv, Function.comp_apply, Equiv.Perm.mul_apply,
          Equiv.apply_symm_apply] using hk (h⁻¹ a))
    ⟨fun p q => Quotient.inductionOn₂ p q fun g h hgh => by
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr (mem_fiberSubgroup.mpr fun a => ?_))
      have := congrFun (congrArg Subtype.val hgh) (h a)
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Quotient.lift_mk, Function.comp_apply,
        Equiv.symm_apply_apply] using this,
    fun c => by
      have hcard : ∀ i, Fintype.card {a // c.1 a = i} = Fintype.card {a // f a = i} := fun i => by
        rw [Fintype.card_subtype, Fintype.card_subtype, c.2 i]
      -- Matching the fibers of `c` with those of `f` produces `e` with `f ∘ e = c`.
      let e : Equiv.Perm α := Equiv.ofFiberEquiv fun i => Fintype.equivOfCardEq (hcard i)
      refine ⟨Quotient.mk _ e⁻¹, Subtype.ext (funext fun a => ?_)⟩
      exact (inv_inv e).symm ▸ Equiv.ofFiberEquiv_map _ a⟩

/-- The coset of `g` is sent to the rearrangement `f ∘ g⁻¹` of `f`. -/
@[simp]
theorem quotientFiberSubgroupEquiv_mk (f : α → ι) (g : Equiv.Perm α) :
    (quotientFiberSubgroupEquiv f (g : Equiv.Perm α ⧸ fiberSubgroup f) : α → ι) = f ∘ ⇑g⁻¹ :=
  (rfl)

/-- **The rearrangement equivalence is equivariant**: moving a coset by `π` precomposes the
corresponding rearrangement with `π⁻¹`. -/
@[simp]
theorem quotientFiberSubgroupEquiv_smul (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    (quotientFiberSubgroupEquiv f (π • q) : α → ι) = quotientFiberSubgroupEquiv f q ∘ ⇑π⁻¹ :=
  QuotientGroup.induction_on q fun g => by
    rw [MulAction.Quotient.smul_mk, quotientFiberSubgroupEquiv_mk, quotientFiberSubgroupEquiv_mk,
      smul_eq_mul, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_assoc]

/-- A coset is fixed by `π` exactly when the corresponding rearrangement of `f` is invariant
under `π`. -/
@[simp]
theorem smul_eq_self_iff_quotientFiberSubgroupEquiv (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    π • q = q ↔ (quotientFiberSubgroupEquiv f q : α → ι) ∘ ⇑π = quotientFiberSubgroupEquiv f q := by
  rw [← (quotientFiberSubgroupEquiv f).apply_eq_iff_eq, Subtype.ext_iff,
    quotientFiberSubgroupEquiv_smul]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.symm_comp_self, Function.comp_id]
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.self_comp_symm, Function.comp_id]

/-- **The fixed cosets of `π` count the `π`-invariant rearrangements of `f`**: the number of cosets
of the fiber subgroup of `f` fixed by `π` is the number of maps `c : α → ι` with fibers of the same
sizes as those of `f` and with `c ∘ π = c`.  For the rows of a tabloid this is the value at `π` of
the permutation character on the tabloids. -/
theorem card_fixedPoints_quotient_fiberSubgroup [Fintype ι] (f : α → ι)
    (π : Equiv.Perm α) :
    Nat.card {q : Equiv.Perm α ⧸ fiberSubgroup f // π • q = q} =
      #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = #{a | f a = i}} := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (((quotientFiberSubgroupEquiv f).subtypeEquiv
    (q := fun c : {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} => c.1 ∘ π = c.1)
    fun q =>
      smul_eq_self_iff_quotientFiberSubgroupEquiv f π q).trans ?_)
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun c : α → ι => c ∘ π = c)).trans
    (Equiv.subtypeEquivRight fun _ => and_comm)

end Quotient

section Count

open Finset

variable [Fintype α] [Fintype ι] [DecidableEq ι]

/-- **The order of the fiber subgroup** is the product of the factorials of the fiber sizes: a
fiber-preserving permutation is an independent permutation of each fiber. -/
theorem natCard_fiberSubgroup (f : α → ι) :
    Nat.card (fiberSubgroup f) = ∏ i, (#{a | f a = i}).factorial := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      rw [mem_fiberSubgroup, funext_iff]; rfl :
      fiberSubgroup f ≃ {g : Equiv.Perm α // f ∘ g = f}),
    Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  simp only [Fintype.card_subtype]

/-- **Every distribution of the points of `α` among the colours is the fiber-size function of some
colouring**: a function `d : ι → ℕ` with total `card α` is `i ↦ #{a | f a = i}` for some
`f : α → ι`. -/
theorem exists_forall_card_filter_eq {d : ι → ℕ} (hd : ∑ i, d i = Fintype.card α) :
    ∃ f : α → ι, ∀ i, #{a | f a = i} = d i := by
  -- label the points of `α` by the points of `Σ i, Fin (d i)` and colour each by its block
  let e := Fintype.equivOfCardEq (show Fintype.card α = Fintype.card (Σ i, Fin (d i)) by
    simp [hd])
  refine ⟨fun a => (e a).1, fun i => ?_⟩
  rw [← Fintype.card_subtype, Fintype.card_congr (e.subtypeEquiv fun a => Iff.rfl :
      {a // (e a).1 = i} ≃ {x : Σ i, Fin (d i) // x.1 = i}),
    Fintype.card_congr (Equiv.sigmaSubtype i), Fintype.card_fin]

/-- **Summing the orders of the fiber subgroups over all colourings**, each colouring weighted by
a function of its fiber sizes: the colourings with a given fiber-size function `d` form one orbit
of `Equiv.Perm α`, whose stabilizers are their fiber subgroups, so together they contribute
`(card α)!` times the weight of `d`, and every `d` of total `card α` occurs. -/
theorem sum_natCard_fiberSubgroup_smul [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (F : (ι → ℕ) → M) :
    ∑ f : α → ι, Nat.card (fiberSubgroup f) • F (fun i => #{a | f a = i}) =
      (Fintype.card α).factorial • ∑ d ∈ piAntidiag univ (Fintype.card α), F d := by
  set c : (α → ι) → ι → ℕ := fun f i => #{a | f a = i} with hc_def
  have hc : ∀ f ∈ (univ : Finset (α → ι)), c f ∈ piAntidiag univ (Fintype.card α) :=
    fun f _ => by
      rw [mem_piAntidiag]
      refine ⟨?_, fun i _ => mem_univ i⟩
      rw [hc_def]
      exact (card_eq_sum_card_fiberwise fun a _ => mem_univ (f a)).symm
  -- group the colourings by their fiber-size functions
  rw [← sum_fiberwise_of_maps_to hc, smul_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_congr rfl fun f hf => by
    rw [show (fun i => #{a | f a = i}) = d from (mem_filter.1 hf).2], ← sum_smul]
  congr 1
  -- the colourings with fiber sizes `d` are the rearrangements of one of them, `f₀`
  obtain ⟨f₀, hf₀⟩ := exists_forall_card_filter_eq (α := α) ((mem_piAntidiag.1 hd).1)
  have hfib : ∀ f ∈ univ.filter fun f => c f = d,
      Nat.card (fiberSubgroup f) = Nat.card (fiberSubgroup f₀) := fun f hf => by
    rw [natCard_fiberSubgroup, natCard_fiberSubgroup]
    exact prod_congr rfl fun i _ => by
      rw [show #{a | f a = i} = d i from congrFun (mem_filter.1 hf).2 i, hf₀]
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  have hq : #(univ.filter fun f => c f = d) = Nat.card (Equiv.Perm α ⧸ fiberSubgroup f₀) := by
    rw [Nat.card_congr (quotientFiberSubgroupEquiv f₀), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    rw [hc_def, funext_iff]
    refine forall_congr' fun i => ?_
    rw [← hf₀ i]
    -- the two sides differ only in the instance deciding equality of colours
    convert Iff.rfl
  rw [hq, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
    Fintype.card_perm]

end Count

end TauCeti
end
end TAF_LiteralSource_0167

section TAF_LiteralSource_0168
/- Original module: TauCeti.RepresentationTheory.Symmetric.YoungSubgroup -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Young subgroups of symmetric groups

For a partition `μ` of `n`, this file defines its Young subgroup of `Equiv.Perm (Fin n)`.
The decreasing parts of `μ` cut `Fin n` into consecutive blocks, and the Young subgroup consists
exactly of the permutations preserving those blocks.  We identify it with the product of the
symmetric groups on the individual blocks and compute its cardinality and index.  Counting the
labels lying in the first `k` blocks recovers the partial sums of the decreasing parts
(`TauCeti.card_filter_youngBlock_lt`), which is the form in which the parts enter the dominance
order.

The Young subgroups of the shapes that have a name are computed here as well: the coarsest shape
`(n)` gives the whole symmetric group, the finest shape `(1ⁿ)` the trivial subgroup, and the shape
`(n+1, 1)` the stabilizer of the last label (`TauCeti.youngSubgroup_singletonSecondRow`), its two
blocks being all the labels but the last one and the last one alone.

The construction uses Mathlib's `finSigmaFinEquiv` to enumerate the consecutive blocks and
`DomMulAct.stabilizerMulEquiv` to decompose their stabilizer.

The consecutive-block design and the principal declaration signatures follow
`TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md` and its `Suggested.lean`.
-/

public section

namespace TauCeti

open Equiv

/-- The equivalence which enumerates the consecutive blocks whose sizes are the decreasing parts
of `μ`.

The coordinate `⟨i, j⟩` denotes position `j` in block `i`. -/
noncomputable def youngBlocksEquiv {n : ℕ} (μ : n.Partition) :
    (Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) ≃ Fin n :=
  finSigmaFinEquiv.trans <| finCongr <| by
    simp_rw [List.get_eq_getElem]
    rw [Fin.sum_univ_getElem, ← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- The consecutive-block equivalence sends a local coordinate to the preceding block sizes
plus that coordinate. -/
@[simp]
theorem youngBlocksEquiv_apply {n : ℕ} (μ : n.Partition)
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (youngBlocksEquiv μ x : ℕ) =
      ∑ i : Fin x.1,
        (μ.parts.sort (· ≥ ·)).get (Fin.castLE x.1.2.le i) + x.2 := by
  simp [youngBlocksEquiv]

/-- The block containing an element of `Fin n`. -/
noncomputable def youngBlock {n : ℕ} (μ : n.Partition) (j : Fin n) :
    Fin (μ.parts.sort (· ≥ ·)).length :=
  ((youngBlocksEquiv μ).symm j).1

/-- The block-coordinate equivalence sends a local coordinate to its block label. -/
@[simp]
theorem youngBlock_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    youngBlock μ (youngBlocksEquiv μ x) = x.1 := by
  simp [youngBlock]

/-- The local coordinates in block `i` are equivalent to the fiber of `youngBlock μ` over `i`. -/
noncomputable def youngBlockEquiv {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)]) ≃
      {j : Fin n // youngBlock μ j = i} :=
  Equiv.ofBijective
    (fun j => ⟨youngBlocksEquiv μ ⟨i, j⟩, youngBlock_youngBlocksEquiv μ ⟨i, j⟩⟩)
    ⟨by
      intro a b h
      have hs : (⟨i, a⟩ : Σ k, Fin ((μ.parts.sort (· ≥ ·)).get k)) = ⟨i, b⟩ :=
        (youngBlocksEquiv μ).injective (Subtype.ext_iff.mp h)
      cases hs
      rfl,
    by
      rintro ⟨j, hj⟩
      obtain ⟨⟨k, x⟩, rfl⟩ := (youngBlocksEquiv μ).surjective j
      simp only [youngBlock_youngBlocksEquiv] at hj
      subst k
      exact ⟨x, rfl⟩⟩

/-- The block-fiber equivalence is the consecutive-block equivalence with its block-membership
proof. -/
@[simp]
theorem youngBlockEquiv_apply {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)])) :
    youngBlockEquiv μ i j =
      ⟨youngBlocksEquiv μ ⟨i, j⟩, youngBlock_youngBlocksEquiv μ ⟨i, j⟩⟩ :=
  Subtype.ext rfl

private theorem youngBlockEquiv_val {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)])) :
    (youngBlockEquiv μ i j).1 = youngBlocksEquiv μ ⟨i, j⟩ := by
  simpa only using congrArg Subtype.val (youngBlockEquiv_apply μ i j)

/-- The labels whose `μ`-block is among the first `k` are as many as the first `k` parts of `μ`
add up to. -/
theorem card_filter_youngBlock_lt {n : ℕ} (μ : n.Partition) (k : ℕ) :
    (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) < k).card =
      ((μ.parts.sort (· ≥ ·)).take k).sum := by
  classical
  -- Each block of `μ` is the fiber of `youngBlock μ` over its label, and has the size of a part.
  have hfiber : ∀ i : ℕ, (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) = i).card =
      (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro i
    by_cases hi : i < (μ.parts.sort (· ≥ ·)).length
    · rw [List.getD_eq_getElem _ _ hi, ← Fintype.card_subtype]
      refine (Fintype.card_congr ((youngBlockEquiv μ ⟨i, hi⟩).trans
        (Equiv.subtypeEquivRight fun x => ?_))).symm.trans (Fintype.card_fin _)
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi), Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      exact fun x _ h => hi (h ▸ (youngBlock μ x).2)
  -- A partial sum of a list is the sum of its first entries, read off with `List.getD`.
  have hsum : ∀ m : ℕ, ((μ.parts.sort (· ≥ ·)).take m).sum =
      ∑ i ∈ Finset.range m, (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      rcases lt_or_ge m (μ.parts.sort (· ≥ ·)).length with h | h
      · rw [List.sum_take_succ _ _ h, List.getD_eq_getElem _ _ h]
      · rw [List.take_of_length_le h, List.take_of_length_le (h.trans (Nat.le_succ m)),
          List.getD_eq_default _ _ h, add_zero]
  -- Split the labels into blocks, and the partial sum into parts.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin n => (youngBlock μ x : ℕ)) (t := Finset.range k) (fun x hx => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simpa using hx),
    hsum k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hfiber i]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun h => h ▸ Finset.mem_range.mp hi

/-- The Young subgroup associated to `μ`, acting independently on the consecutive blocks whose
sizes are the decreasing parts of `μ`. -/
noncomputable def youngSubgroup {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ)).unop

private noncomputable def youngSubgroupStabilizerMulEquiv {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ ≃*
      (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ))ᵐᵒᵖ where
  toFun σ := MulOpposite.op ⟨DomMulAct.mk σ, σ.prop⟩
  invFun σ := ⟨DomMulAct.mk.symm σ.unop, σ.unop.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem mem_youngSubgroup_stabilizer_iff {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔
      DomMulAct.mk σ ∈
        MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ) :=
  Iff.rfl

/-- The Young subgroup is the product of the symmetric groups on its consecutive blocks. -/
noncomputable def youngSubgroupMulEquiv {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ ≃*
      (∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
        Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i))) :=
  (youngSubgroupStabilizerMulEquiv μ).trans <|
    (DomMulAct.stabilizerMulEquiv (youngBlock μ)).trans <|
      MulEquiv.piCongrRight fun i => (youngBlockEquiv μ i).symm.permCongrHom

private theorem youngSubgroupStabilizerMulEquiv_apply {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) :
    DomMulAct.mk.symm (youngSubgroupStabilizerMulEquiv μ σ).unop =
      (σ : Equiv.Perm (Fin n)) :=
  rfl

private theorem youngSubgroupMulEquiv_apply {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    youngSubgroupMulEquiv μ σ i =
      (youngBlockEquiv μ i).symm.permCongrHom
        ((DomMulAct.stabilizerMulEquiv (youngBlock μ))
          (youngSubgroupStabilizerMulEquiv μ σ) i) :=
  rfl

/-- The product decomposition records the local coordinate induced on each consecutive block. -/
@[simp]
theorem youngSubgroupMulEquiv_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (youngBlocksEquiv μ).symm
        ((σ : Equiv.Perm (Fin n)) (youngBlocksEquiv μ ⟨i, j⟩)) =
      ⟨i, (youngSubgroupMulEquiv μ σ) i j⟩ := by
  apply (youngBlocksEquiv μ).injective
  rw [Equiv.apply_symm_apply, ← youngBlockEquiv_val μ i ((youngSubgroupMulEquiv μ σ) i j)]
  have h := DomMulAct.stabilizerMulEquiv_apply
    (youngSubgroupStabilizerMulEquiv μ σ) (youngBlock_youngBlocksEquiv μ ⟨i, j⟩)
  rw [youngSubgroupStabilizerMulEquiv_apply] at h
  rw [← h, ← youngBlockEquiv_apply μ i j, youngSubgroupMulEquiv_apply]
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

/-- The inverse product decomposition acts on each consecutive block by the corresponding
permutation. -/
@[simp]
theorem youngSubgroupMulEquiv_symm_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (p : ∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i)))
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    ((youngSubgroupMulEquiv μ).symm p : Equiv.Perm (Fin n))
        (youngBlocksEquiv μ ⟨i, j⟩) =
      youngBlocksEquiv μ ⟨i, p i j⟩ := by
  apply (youngBlocksEquiv μ).symm.injective
  rw [Equiv.symm_apply_apply, youngSubgroupMulEquiv_apply_youngBlocksEquiv,
    MulEquiv.apply_symm_apply]

private theorem prod_factorial_sorted_parts {n : ℕ} (μ : n.Partition) :
    (∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
        ((μ.parts.sort (· ≥ ·)).get i).factorial) =
      (μ.parts.map Nat.factorial).prod := by
  simp_rw [List.get_eq_getElem]
  rw [Fin.prod_univ_fun_getElem, ← Multiset.prod_coe, ← Multiset.map_coe,
    Multiset.sort_eq]

/-- The order of a Young subgroup is the product of the factorials of the parts. -/
theorem card_youngSubgroup {n : ℕ} (μ : n.Partition) :
    Nat.card (youngSubgroup μ) = (μ.parts.map Nat.factorial).prod := by
  rw [Nat.card_congr (youngSubgroupMulEquiv μ).toEquiv, Nat.card_pi]
  simp only [Nat.card_perm, Nat.card_fin]
  exact prod_factorial_sorted_parts μ

/-- Membership in the Young subgroup is equivalent to preserving the consecutive-block label. -/
@[simp]
theorem mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  rw [mem_youngSubgroup_stabilizer_iff]
  exact DomMulAct.mem_stabilizer_iff

/-- The Young subgroup is the subgroup preserving the fibers of its consecutive-block map. -/
theorem youngSubgroup_eq_fiberSubgroup {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ = fiberSubgroup (youngBlock μ) := by
  ext σ
  rw [mem_youngSubgroup_iff, mem_fiberSubgroup]
  simp only [funext_iff, Function.comp_apply]

/-- The index of a Young subgroup times its order is `n!`. -/
theorem youngSubgroup_index_mul {n : ℕ} (μ : n.Partition) :
    (youngSubgroup μ).index * (μ.parts.map Nat.factorial).prod = n.factorial := by
  rw [← card_youngSubgroup, Subgroup.index_mul_card, Nat.card_perm, Nat.card_fin]

/-- The Young subgroup of the coarsest partition `(n)` is the whole symmetric group: its at most
one block imposes no condition. -/
@[simp]
theorem youngSubgroup_indiscrete (n : ℕ) :
    youngSubgroup (Nat.Partition.indiscrete n) = ⊤ :=
  Subgroup.eq_top_of_card_eq _ <| by
    rw [card_youngSubgroup, Nat.Partition.prod_map_factorial_indiscrete, Nat.card_perm,
      Nat.card_fin]

/-- The Young subgroup of the all-ones partition `(1ⁿ)` is trivial: every block is a singleton,
so only the identity preserves them all. -/
@[simp]
theorem youngSubgroup_ones (n : ℕ) : youngSubgroup (Nat.Partition.ones n) = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ <| by
    rw [card_youngSubgroup]
    simp

/-- The index of a Young subgroup is the multinomial quotient by the factorials of the parts. -/
theorem youngSubgroup_index {n : ℕ} (μ : n.Partition) :
    (youngSubgroup μ).index =
      n.factorial / (μ.parts.map Nat.factorial).prod :=
  Nat.eq_div_of_mul_eq_right
    (by
      apply Multiset.prod_ne_zero
      intro h
      obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp h
      exact Nat.factorial_ne_zero x hx)
    (by simpa only [mul_comm] using youngSubgroup_index_mul μ)

/-! ### The shape `(n+1, 1)`

The blocks of `Nat.Partition.singletonSecondRow n = (n+1, 1)` are the first `n+1` labels and the
last one, so its Young subgroup is the stabilizer of `Fin.last (n+1)`. -/

/-- Entries of the sorted parts of `(n+1, 1)`, in a form whose index is a bare natural number, so
that rewriting the sorted list does not disturb the bound on the index. -/
private theorem getElem_sort_parts_singletonSecondRow (n i : ℕ)
    (h : i < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length) :
    ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·))[i] = [n + 1, 1].getD i 0 := by
  rw [← List.getD_eq_getElem _ (0 : ℕ) h, Nat.Partition.sort_parts_singletonSecondRow]

/-- **The last label lies in the second block of the shape `(n+1, 1)`.**  The blocks are
consecutive with sizes `n+1` and `1`, so the block-coordinate equivalence sends the single
coordinate of the second block to `Fin.last (n+1)`. -/
@[simp]
theorem youngBlock_singletonSecondRow_last (n : ℕ) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) (Fin.last (n + 1))) : ℕ) = 1 := by
  have hlen : ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length = 2 := by
    rw [Nat.Partition.sort_parts_singletonSecondRow]
    rfl
  have h1 : (1 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length := by omega
  have h0 : (0 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).get ⟨1, h1⟩ := by
    rw [List.get_eq_getElem, getElem_sort_parts_singletonSecondRow]
    simp
  have hlast : youngBlocksEquiv (Nat.Partition.singletonSecondRow n) ⟨⟨1, h1⟩, ⟨0, h0⟩⟩ =
      Fin.last (n + 1) := by
    refine Fin.ext ?_
    rw [youngBlocksEquiv_apply, Fin.sum_univ_one, List.get_eq_getElem,
      getElem_sort_parts_singletonSecondRow]
    simp
  rw [← hlast, youngBlock_youngBlocksEquiv]

/-- **Every other label lies in the first block of the shape `(n+1, 1)`.**  The first block has
`n+1` of the `n+2` labels, so its complement is the single label already located by
`TauCeti.youngBlock_singletonSecondRow_last`. -/
@[simp]
theorem youngBlock_singletonSecondRow_eq_zero (n : ℕ) {x : Fin (n + 2)}
    (hx : x ≠ Fin.last (n + 1)) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) x) : ℕ) = 0 := by
  classical
  have hcard : (Finset.univ.filter fun y : Fin (n + 2) =>
      ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card = n + 1 := by
    rw [card_filter_youngBlock_lt, Nat.Partition.sort_parts_singletonSecondRow]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2))))
    (p := fun y => ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1))
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hsum
  by_contra hne
  have hx' : ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) x : ℕ) < 1) := by omega
  have hlt : 1 < (Finset.univ.filter fun y : Fin (n + 2) =>
      ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card :=
    Finset.one_lt_card.mpr ⟨x, by simpa using hx', Fin.last (n + 1), by simp, hx⟩
  omega

/-- **The Young subgroup of the shape `(n+1, 1)` is a point stabilizer.**  Its blocks are the last
label alone and all the others, so a permutation preserves them exactly when it fixes the last
label. -/
@[simp]
theorem youngSubgroup_singletonSecondRow (n : ℕ) :
    youngSubgroup (Nat.Partition.singletonSecondRow n) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)) := by
  rw [youngSubgroup_eq_fiberSubgroup]
  refine fiberSubgroup_eq_stabilizer (fun x hx h => ?_) (fun x y hx hy => Fin.ext ?_)
  · have hv := congrArg Fin.val h
    rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_last] at hv
    exact absurd hv (by omega)
  · rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_eq_zero n hy]

end TauCeti
end
end TAF_LiteralSource_0168

section TAF_LiteralSource_0169
/- Original module: TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Young permutation modules

For a partition `μ` of `n`, the Young permutation module `M^μ` is the rational permutation
representation of `Equiv.Perm (Fin n)` on the left cosets of the Young subgroup associated to
`μ`. These cosets are the `μ`-tabloids.

This file records the tabloid basis and its action, computes the stabilizer of a tabloid as the
group preserving its rows (`TauCeti.stabilizer_quotientGroup_mk_youngSubgroup`), identifies `M^μ`
with the representation induced from the trivial representation of the Young subgroup, and
computes its dimension and character. In particular, the dimension is the multinomial coefficient
`n! / ∏ i, μᵢ!`, while the character at a permutation is the number of fixed tabloids.

## Main definitions

* `TauCeti.permutationModule` is the Young permutation module `M^μ`.
* `TauCeti.permutationModuleBasis` is its basis indexed by `μ`-tabloids.
* `TauCeti.permutationModuleIsoIndTrivial` identifies `M^μ` with an induced trivial
  representation.
* `TauCeti.permutationModuleFDRep` is the finite-dimensional bundled form of `M^μ`.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, for Young permutation
  modules and tabloids.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1, “The permutation module”.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ## The tabloid model -/

/-- The Young permutation module `M^μ` over `ℚ`.

Its standard basis is indexed by the left cosets of `youngSubgroup μ`; these cosets are the
`μ`-tabloids, and the symmetric group acts on them by left multiplication. -/
noncomputable abbrev permutationModule {n : ℕ} (μ : n.Partition) :
    Rep ℚ (Equiv.Perm (Fin n)) :=
  Rep.ofMulAction ℚ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)

/-- The standard basis of `M^μ`, indexed by the `μ`-tabloids. -/
noncomputable abbrev permutationModuleBasis {n : ℕ} (μ : n.Partition) :
    Module.Basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ
      (permutationModule μ).V :=
  MonoidAlgebra.basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ

/-- **The stabilizer of a tabloid.** A permutation fixes the coset `gH` of the Young subgroup of
`μ` exactly when it preserves every fiber of the block map transported by `g`, that is, when it
permutes the labels within the rows of the tabloid. -/
theorem stabilizer_quotientGroup_mk_youngSubgroup {n : ℕ} (μ : n.Partition)
    (g : Equiv.Perm (Fin n)) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) =
      fiberSubgroup fun x => youngBlock μ (g⁻¹ x) := by
  rw [stabilizer_quotientGroup_mk, youngSubgroup_eq_fiberSubgroup]
  exact fiberSubgroup_map_conj g fun _ _ => by simp

/-! ## Induction, dimension, and character -/

/-- The Young permutation module is induction of the trivial representation of the Young
subgroup. -/
noncomputable def permutationModuleIsoIndTrivial {n : ℕ} (μ : n.Partition) :
    permutationModule μ ≅
      Rep.ind (youngSubgroup μ).subtype
        (Rep.trivial ℚ (youngSubgroup μ) ℚ) :=
  (indTrivialIso ℚ (youngSubgroup μ)).symm

/-- The dimension of `M^μ` is the index of its Young subgroup. -/
theorem finrank_permutationModule_eq_index {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModule μ).V = (youngSubgroup μ).index := by
  let : Fintype (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (permutationModuleBasis μ)]
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]

/-- The dimension of `M^μ` is the multinomial coefficient
`n! / ∏ i, μᵢ!`. -/
@[simp]
theorem finrank_permutationModule {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModule μ).V =
      n.factorial / (μ.parts.map Nat.factorial).prod := by
  rw [finrank_permutationModule_eq_index, youngSubgroup_index]

/-- The character of `M^μ` at `σ` is the number of `μ`-tabloids fixed by `σ`. -/
theorem char_permutationModule {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModule μ).ρ.character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : ℚ) := by
  let : Finite (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := inferInstance
  exact char_ofMulAction ℚ _ σ

/-- The Young permutation module bundled as a finite-dimensional representation. -/
noncomputable abbrev permutationModuleFDRep {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of (permutationModule μ).ρ

/-- The bundled Young permutation module has the same multinomial dimension. -/
@[simp]
theorem finrank_permutationModuleFDRep {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModuleFDRep μ) =
      n.factorial / (μ.parts.map Nat.factorial).prod :=
  finrank_permutationModule μ

/-- The character of the bundled Young permutation module counts fixed tabloids. -/
@[simp]
theorem char_permutationModuleFDRep {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModuleFDRep μ).character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : ℚ) :=
  char_permutationModule μ σ

end TauCeti
end
end TAF_LiteralSource_0169

section TAF_LiteralSource_0170
/- Original module: TauCeti.RepresentationTheory.Symmetric.PermutationModule.Form -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The tabloid form on a Young permutation module

The Young permutation module `M^μ` has a basis indexed by the `μ`-tabloids, and the bilinear form
declaring that basis orthonormal is the **tabloid form**.  It is the specialisation to `M^μ` of the
invariant form on a permutation representation, so the whole orthogonality API of
`TauCeti.permutationForm` applies verbatim: the tabloid form is symmetric, positive definite, and
preserved by the symmetric group, and the orthogonal complement of a subrepresentation of `M^μ` is
again a subrepresentation and is a complement.

This file names the form, reads it on the tabloid basis and on coset representatives, and records
the two statements that the theory of Specht modules uses: invariance under the symmetric group and
complementation.  The orthogonality relation itself is the tool behind James's submodule theorem,
which compares a submodule of `M^μ` with the orthogonal complement of the Specht module inside it.

## Main definitions

* `TauCeti.tabloidForm`: the tabloid form on `M^μ`.

## Main results

* `TauCeti.tabloidForm_basis_basis`: the tabloid basis is orthonormal.
* `TauCeti.tabloidForm_single_coe_single_coe_of_mem` and
  `TauCeti.tabloidForm_single_coe_single_coe_of_notMem`: two tabloids given by permutations pair to
  `1` or to `0` according to whether the permutations differ by an element of the Young subgroup.
* `TauCeti.tabloidForm_invariant`: the symmetric group acts on `M^μ` by isometries of the tabloid
  form.
* `TauCeti.isCompl_orthogonalSubrepresentation_permutationModule`: a subrepresentation of `M^μ` is
  complemented by its orthogonal complement.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, Chapter 1, where the form is
  introduced by declaring the tabloids orthonormal, and Chapter 4 for the submodule theorem.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, "The submodule theorem (James)", which asks for the tabloid bilinear form as an API in
  its own right.
-/

public section

namespace TauCeti

open _root_.LinearMap (BilinForm)

variable {n : ℕ} (μ : n.Partition)

/-- The **tabloid form** on the Young permutation module `M^μ`: the bilinear form for which the
tabloid basis is orthonormal. -/
noncomputable abbrev tabloidForm :
    BilinForm ℚ (MonoidAlgebra ℚ (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) :=
  permutationForm ℚ (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)

/-- The tabloid basis of `M^μ` is orthonormal for the tabloid form. -/
theorem tabloidForm_basis_basis (i j : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) [Decidable (i = j)] :
    tabloidForm μ (permutationModuleBasis μ i) (permutationModuleBasis μ j) =
      if i = j then 1 else 0 := by
  simpa using permutationForm_single_single i j (1 : ℚ) 1

/-- Two permutations describe the same `μ`-tabloid exactly when they differ by an element of the
Young subgroup, and then the corresponding basis vectors pair to `1`. -/
theorem tabloidForm_single_coe_single_coe_of_mem {g h : Equiv.Perm (Fin n)}
    (hgh : g⁻¹ * h ∈ youngSubgroup μ) :
    tabloidForm μ (MonoidAlgebra.single (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1)
        (MonoidAlgebra.single (h : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1) = 1 := by
  classical
  rw [permutationForm_single_single, ite_eq_left (QuotientGroup.eq.mpr hgh), mul_one]

/-- Permutations lying in different cosets of the Young subgroup describe distinct `μ`-tabloids, so
the corresponding basis vectors pair to `0`. -/
theorem tabloidForm_single_coe_single_coe_of_notMem {g h : Equiv.Perm (Fin n)}
    (hgh : g⁻¹ * h ∉ youngSubgroup μ) :
    tabloidForm μ (MonoidAlgebra.single (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1)
        (MonoidAlgebra.single (h : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1) = 0 := by
  classical
  rw [permutationForm_single_single, ite_eq_right fun hq => hgh (QuotientGroup.eq.mp hq)]

/-- The symmetric group acts on `M^μ` by isometries of the tabloid form: it permutes the tabloid
basis. -/
theorem tabloidForm_invariant (σ : Equiv.Perm (Fin n))
    (v w : MonoidAlgebra ℚ (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) :
    tabloidForm μ ((permutationModule μ).ρ σ v) ((permutationModule μ).ρ σ w) =
      tabloidForm μ v w :=
  permutationForm_ofMulAction_invariant σ v w

/-- **Invariant orthogonal complements in `M^μ`.**  A subrepresentation of the Young permutation
module is complemented by its orthogonal complement for the tabloid form.  Unlike the complement
produced by Maschke's theorem, this one is canonical: it is cut out by an explicit pairing. -/
theorem isCompl_orthogonalSubrepresentation_permutationModule
    (σ : Subrepresentation (permutationModule μ).ρ) :
    IsCompl σ (orthogonalSubrepresentation σ) :=
  isCompl_orthogonalSubrepresentation σ

end TauCeti
end
end TAF_LiteralSource_0170

section TAF_LiteralSource_0171
/- Original module: TauCeti.LinearAlgebra.Trace.Pi -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Traces on finite products

The trace of an endomorphism of a finite dependent product is the sum of the traces of its
diagonal blocks. In particular, a coordinatewise endomorphism has the sum of the component
traces, and a coordinate-reindexing endomorphism receives contributions only from fixed
coordinates.

The results are linear-algebra inputs for character formulas of induced representations and
finite direct sums of representations.

## Main results

* `LinearMap.trace_pi`: the trace of an arbitrary endomorphism of a finite dependent product is
  the sum of the traces of its diagonal blocks.
* `LinearMap.trace_piMap`: the trace of a coordinatewise endomorphism `LinearMap.piMap f` of a
  finite dependent product is the sum of the traces of its components.
-/

public section

namespace LinearMap

universe u v w

variable {k : Type u} {ι : Type v} [CommSemiring k] [Fintype ι] {M : ι → Type w}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
  [∀ i, Module.Finite k (M i)]

/-- The trace of an endomorphism of a finite dependent product is the sum of the traces of its
diagonal blocks. -/
theorem trace_pi [DecidableEq ι] (T : ((i : ι) → M i) →ₗ[k] (i : ι) → M i) :
    trace k ((i : ι) → M i) T =
      ∑ i, trace k (M i) (proj i ∘ₗ T ∘ₗ single k M i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  rw [trace_eq_matrix_trace k (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_eq_matrix_trace k (b i), Matrix.trace]
  simp [toMatrix_apply]

/-- The trace of the coordinatewise endomorphism `LinearMap.piMap f` of a finite dependent product
of finite free modules is the sum of the traces of the `f i`. -/
@[simp]
theorem trace_piMap (f : ∀ i, M i →ₗ[k] M i) :
    trace k ((i : ι) → M i) (piMap f) = ∑ i, trace k (M i) (f i) := by
  classical
  rw [trace_pi]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext m
  simp

end LinearMap
end
end TAF_LiteralSource_0171

section TAF_LiteralSource_0172
/- Original module: TauCeti.RepresentationTheory.OfModule -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The representation carried by a `k[G]`-module

Mathlib's `Representation.ofModule' M` reads a `k[G]`-module `M` whose `k`-module structure is
already the restriction of its `k[G]`-module structure as a representation of `G` on `M` itself,
rather than on a type synonym.  That is the convenient form -- a left ideal, say, stays a left
ideal -- but nothing is recorded about it, so the general theory of representations, which runs
on the type synonym `ρ.asModule`, cannot be applied to it.

This file records what is needed to pass between the two.  The algebra map of `ofModule' M` is
the given action (`TauCeti.Representation.asAlgebraHom_ofModule'`), so `(ofModule' M).asModule` is
`M` again, with the same `k[G]`-action
(`TauCeti.Representation.ofModule'AsModuleEquiv`).  Consequently `ofModule' M` is irreducible
exactly when `M` is a simple `k[G]`-module
(`TauCeti.Representation.isIrreducible_ofModule'_iff`), which is how a module built by hand -- a
left ideal, for instance -- is recognised as an irreducible representation.  That last statement
is stated here, beside the comparison of modules it is read off from, rather than among the
self-contained criteria of `TauCeti.RepresentationTheory.Irreducible`, which say nothing about
where the representation came from.

Characters are read off in the same spirit: the character of `ofModule'` of a finite product of
`k[G]`-modules is the sum of the characters of the factors
(`TauCeti.Representation.char_ofModule'_pi`), and a factor `ρ.asModule` contributes the character
of `ρ` itself (`Representation.char_ofModule'_asModule`).  Together they compute the
character of a direct sum of representations assembled as a `k[G]`-module.

## Main results

* `TauCeti.Representation.ofModule'_apply`: a group element acts by the corresponding
  group-algebra basis element.
* `TauCeti.Representation.asAlgebraHom_ofModule'`: the algebra map of `ofModule' M` is the action
  of `k[G]` on `M`.
* `TauCeti.Representation.ofModule'AsModuleEquiv`: `(ofModule' M).asModule` is `M` as a
  `k[G]`-module.
* `TauCeti.Representation.isIrreducible_ofModule'_iff`: `ofModule' M` is irreducible exactly when
  `M` is simple.
* `TauCeti.Representation.char_ofModule'_pi`: the character of `ofModule'` of a finite product is
  the sum of the characters of the factors.
* `Representation.char_ofModule'_asModule`: the character of `ofModule' ρ.asModule` is the
  character of `ρ`.
-/

public section

namespace TauCeti

namespace Representation

open scoped MonoidAlgebra

section Semiring

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]

/-- A group element acts on `Representation.ofModule' M` through the corresponding group-algebra
basis element. -/
@[simp]
theorem ofModule'_apply (g : G) (x : M) :
    _root_.Representation.ofModule' (k := k) (G := G) M g x = MonoidAlgebra.single g (1 : k) • x :=
  rfl

/-- The algebra map of `Representation.ofModule' M` is the action of `k[G]` on `M` that it was
built from. -/
-- Both are the `k[G]`-linear extension of the same map on group elements, and `MonoidAlgebra.lift`
-- says that extension is unique.
theorem asAlgebraHom_ofModule' :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom = Algebra.lsmul k k M := by
  rw [_root_.Representation.asAlgebraHom_def, _root_.Representation.ofModule']
  exact (MonoidAlgebra.lift k (Module.End k M) G).apply_symm_apply _

@[simp]
theorem asAlgebraHom_ofModule'_apply (r : k[G]) (x : M) :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r x = r • x := by
  rw [asAlgebraHom_ofModule']
  rfl

/-- **The `k[G]`-module underlying `Representation.ofModule' M` is `M` itself.**  The map is the
identity; the content is that the two `k[G]`-actions agree. -/
noncomputable def ofModule'AsModuleEquiv :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M where
  toFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv
  invFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, _root_.Representation.asModuleEquiv_map_smul,
      asAlgebraHom_ofModule'_apply]
  left_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.left_inv
  right_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.right_inv

/-- `TauCeti.Representation.ofModule'AsModuleEquiv` is the identity map: its two sides are the
same type, and all it records is that their `k[G]`-actions agree. -/
-- The proof is written `(rfl)` rather than `rfl`: the parenthesised form suppresses the automatic
-- `@[defeq]` tag, which an exported theorem may carry only if the definitions it unfolds are
-- exposed, and there is no reason to expose the body of the equivalence.
@[simp]
theorem ofModule'AsModuleEquiv_apply
    (x : (_root_.Representation.ofModule' (k := k) (G := G) M).asModule) :
    ofModule'AsModuleEquiv M x = x :=
  (rfl)

end Semiring

section Field

variable {k G : Type*} [Field k] [Monoid G]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]

/-- **`Representation.ofModule' M` is irreducible exactly when `M` is a simple `k[G]`-module.**
This is the form of `Representation.irreducible_iff_isSimpleModule_asModule` that applies to a
module given in advance, with no type synonym in the way. -/
theorem isIrreducible_ofModule'_iff :
    (_root_.Representation.ofModule' (k := k) (G := G) M).IsIrreducible ↔
      IsSimpleModule k[G] M := by
  rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule]
  exact (ofModule'AsModuleEquiv M).isSimpleModule_iff

end Field

section Character

variable {k G : Type*} [Field k] [Monoid G]

/-- **The character of `Representation.ofModule'` of a finite product of `k[G]`-modules is the
sum of the characters of the factors.**  This is the finite-product counterpart of
`Representation.char_prod`, for representations read off a `k[G]`-module; a factor of
the form `ρ.asModule` is then evaluated by `Representation.char_ofModule'_asModule`. -/
-- A group element acts on the product coordinatewise: `(MonoidAlgebra.single g 1 • x) i` is
-- `MonoidAlgebra.single g 1 • x i`, by `ofModule'_apply` and `Pi.smul_apply`, both of which hold
-- by `rfl`.  Rewriting with them instead of `rfl` is measurably slower, so `rfl` is kept.
@[simp]
theorem char_ofModule'_pi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, Module k[G] (M i)] [∀ i, IsScalarTower k k[G] (M i)]
    [∀ i, FiniteDimensional k (M i)] (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ((i : ι) → M i)).character g =
      ∑ i, (_root_.Representation.ofModule' (k := k) (G := G) (M i)).character g :=
  LinearMap.trace_piMap fun i ↦ _root_.Representation.ofModule' (k := k) (G := G) (M i) g

/-- **The character of `Representation.ofModule' ρ.asModule` is the character of `ρ`.**  This
lets a character computed on a `k[G]`-module assembled from `asModule` summands be expressed
through the original representations. -/
-- `ρ.asModuleEquiv` conjugates the action on `ρ.asModule` into `ρ g`, and the trace is invariant
-- under conjugation.  The conjugation identity is proved pointwise with explicit rewrites rather
-- than `simp`, which would leave a goal closed only by identifying `ρ.asModule` with `V`.
@[simp]
theorem _root_.Representation.char_ofModule'_asModule {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : _root_.Representation k G V) (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ρ.asModule).character g = ρ.character g := by
  have h : _root_.Representation.ofModule' (k := k) (G := G) ρ.asModule g =
      ρ.asModuleEquiv.symm.conj (ρ g) := by
    ext x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      _root_.Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply,
      ofModule'_apply, MonoidAlgebra.of_apply]
  rw [_root_.Representation.character, h, LinearMap.trace_conj', _root_.Representation.character]

end Character

end Representation

end TauCeti
end
end TAF_LiteralSource_0172

section TAF_LiteralSource_0173
/- Original module: TauCeti.Combinatorics.Young.StandardTableau.Reading -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Reading order, the superstandard tableaux, and the shapes with a unique standard tableau

Numbering the cells of a Young diagram `μ` in *reading order* -- left to right along the first
row, then left to right along the second, and so on -- labels the cell `(i, j)` by
`YoungDiagram.readingIndex μ (i, j) = μ.rowLen 0 + ⋯ + μ.rowLen (i - 1) + j`.  Reading
order increases along rows and down columns, so this labelling is a standard Young tableau, the
**row-superstandard tableau** `TauCeti.StandardYoungTableau.rowSuperstandard μ`; in particular
`TauCeti.standardCount μ`, the number `f^μ` of standard Young tableaux, is never zero.

Numbering the cells column by column instead gives a second standard Young tableau
`TauCeti.StandardYoungTableau.colSuperstandard μ`, the transpose of the row-superstandard tableau
of the transposed diagram.  The two disagree as soon as `μ` has a cell outside its first row *and*
a cell outside its first column, while a diagram with at most one row, or with at most one column
-- the empty diagram included -- has only one standard Young tableau at all.  So `f^μ = 1` holds
exactly for the diagrams with at most one row and those with at most one column.

## Main definitions

* `YoungDiagram.readingIndex`: the position of a cell in reading order.
* `TauCeti.StandardYoungTableau.rowSuperstandard`: the tableau numbering the cells row by row.
* `TauCeti.StandardYoungTableau.colSuperstandard`: the tableau numbering the cells column by
  column.

## Main results

* `TauCeti.standardCount_pos`: every Young diagram has a standard Young tableau.
* `TauCeti.standardCount_eq_one_iff`: a Young diagram has exactly one standard Young tableau
  precisely when it has at most one row or at most one column, the empty diagram included.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 5.
-/

public section

open scoped Nat

namespace YoungDiagram

variable {μ : YoungDiagram}

/-- The position of the coordinate pair `c` in reading order: the number of cells of `μ` lying in
rows above `c.1`, plus the column index `c.2`.  This is defined for an arbitrary pair, but it
numbers `μ` in reading order only on the cells of `μ`. -/
def readingIndex (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2

/-- The reading index of a coordinate pair is the sum of the lengths of the rows of `μ` above it,
plus its column index. -/
theorem readingIndex_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    readingIndex μ c = (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2 := by
  rw [readingIndex]

/-- In row `0` the reading index is the column index; for a cell of the first row of `μ` this says
that it is numbered by its column index. -/
@[simp]
theorem readingIndex_zero (μ : YoungDiagram) (j : ℕ) : readingIndex μ (0, j) = j := by
  simp [readingIndex]

/-- The reading index of `(1, 0)` is the length of the first row of `μ`; when `μ` has a second row,
`(1, 0)` is its first cell. -/
@[simp]
theorem readingIndex_one_zero (μ : YoungDiagram) : readingIndex μ (1, 0) = μ.rowLen 0 := by
  simp [readingIndex]

/-- The first `k` row lengths count the cells in the first `k` rows, so the reading index of a
cell of `μ` is smaller than the number of cells of `μ`. -/
theorem readingIndex_lt_card {c : ℕ × ℕ} (hc : c ∈ μ) : readingIndex μ c < μ.card := by
  have hsucc : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ μ.card := by
    rw [sum_range_rowLen_eq_card_filter_fst]
    exact Finset.card_filter_le _ _
  rw [Finset.sum_range_succ] at hsucc
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex]
  omega

/-- Reading order runs down the rows: a cell in an earlier row has the smaller reading index. -/
theorem readingIndex_lt_readingIndex_of_fst_lt {c d : ℕ × ℕ} (hc : c ∈ μ) (h : c.1 < d.1) :
    readingIndex μ c < readingIndex μ d := by
  have hsub : Finset.range (c.1 + 1) ⊆ Finset.range d.1 := by
    rw [Finset.range_subset_range]
    omega
  have hmono : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ ∑ i ∈ Finset.range d.1, μ.rowLen i :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_range_succ] at hmono
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex, readingIndex]
  omega

/-- Reading order runs along each row: within a row, a cell in an earlier column has the smaller
reading index. -/
theorem readingIndex_lt_readingIndex_of_snd_lt {c d : ℕ × ℕ} (hrow : c.1 = d.1) (h : c.2 < d.2) :
    readingIndex μ c < readingIndex μ d := by
  rw [readingIndex, readingIndex, hrow]
  omega

/-- Distinct cells of `μ` have distinct reading indices. -/
theorem eq_of_readingIndex_eq {c d : ℕ × ℕ} (hc : c ∈ μ) (hd : d ∈ μ)
    (h : readingIndex μ c = readingIndex μ d) : c = d := by
  rcases lt_trichotomy c.1 d.1 with hfst | hfst | hfst
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hc hfst).ne
  · rcases lt_trichotomy c.2 d.2 with hsnd | hsnd | hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst hsnd).ne
    · exact Prod.ext hfst hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst.symm hsnd).ne'
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hd hfst).ne'

end YoungDiagram

namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- The **row-superstandard tableau** of `μ`: the standard Young tableau numbering the cells of
`μ` in reading order, left to right along the first row, then left to right along the second, and
so on.  This is the tableau at which the classical-groups roadmap fixes the Young symmetrizer
`c_λ`. -/
noncomputable def rowSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ where
  toTableau :=
    Equiv.ofBijective
      (fun c => ⟨YoungDiagram.readingIndex μ c.1, YoungDiagram.readingIndex_lt_card c.2⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun c d hcd =>
          Subtype.ext (YoungDiagram.eq_of_readingIndex_eq c.2 d.2 (congrArg Fin.val hcd)),
          by simp⟩)
  row_strict' := fun {i j₁ j₂} h _ =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt
      (μ := μ) (c := (i, j₁)) (d := (i, j₂)) rfl h)
  col_strict' := fun {i₁ i₂ j} h hcell =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      (c := (i₁, j)) (d := (i₂, j)) (μ.up_left_mem h.le (le_refl j) hcell) h)

/-- The row-superstandard tableau labels a cell by its reading index. -/
@[simp]
theorem rowSuperstandard_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (rowSuperstandard μ c).val = YoungDiagram.readingIndex μ c.1 := by
  -- `rowSuperstandard` is not `@[expose]`d, so its body is reached through its equation lemma
  -- rather than by definitional unfolding.
  rw [rowSuperstandard]
  rfl

/-- The **column-superstandard tableau** of `μ`: the standard Young tableau numbering the cells of
`μ` top to bottom down the first column, then top to bottom down the second, and so on.  It is the
transpose of the row-superstandard tableau of the transposed diagram. -/
noncomputable def colSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ :=
  (transposeEquiv μ).symm (rowSuperstandard μ.transpose)

/-- The column-superstandard tableau labels a cell by the reading index of the transposed cell in
the transposed diagram. -/
@[simp]
theorem colSuperstandard_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (colSuperstandard μ c).val = YoungDiagram.readingIndex μ.transpose c.1.swap := by
  rw [colSuperstandard, transposeEquiv_symm_apply_val, rowSuperstandard_apply_val]

/-- Transposing the column-superstandard tableau of `μ` gives the row-superstandard tableau of the
transposed diagram: this is the defining property of `colSuperstandard`. -/
@[simp]
theorem transpose_colSuperstandard (μ : YoungDiagram) :
    (colSuperstandard μ).transpose = rowSuperstandard μ.transpose := by
  rw [colSuperstandard, ← transposeEquiv_apply, Equiv.apply_symm_apply]

/-- Every Young diagram carries a standard Young tableau. -/
instance instNonempty (μ : YoungDiagram) : Nonempty (StandardYoungTableau μ) :=
  ⟨rowSuperstandard μ⟩

/-! ### Diagrams with a unique standard Young tableau -/

/-- A diagram with at most one row has all of its cells in that row. -/
private theorem fst_eq_zero_of_colLen_le_one (h : μ.colLen 0 ≤ 1) {c : ℕ × ℕ} (hc : c ∈ μ) :
    c.1 = 0 := by
  have h₀ : (c.1, 0) ∈ μ := μ.up_left_mem (le_refl _) (Nat.zero_le _) hc
  have := _root_.YoungDiagram.mem_iff_lt_colLen.mp h₀
  omega

/-- A diagram with at most one row admits only the row-superstandard tableau: a standard Young
tableau on a single row labels the cells in increasing order of column index. -/
theorem eq_rowSuperstandard_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (T : StandardYoungTableau μ) :
    T = rowSuperstandard μ := by
  have hcard : μ.card = μ.rowLen 0 := YoungDiagram.card_eq_rowLen_of_colLen_le_one h
  have hmem : ∀ k : Fin μ.card, ((0, (k : ℕ)) : ℕ × ℕ) ∈ μ := fun k =>
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (hcard ▸ k.isLt)
  have hid : (fun k : Fin μ.card => T ⟨(0, (k : ℕ)), hmem k⟩) = id :=
    StrictMono.eq_id fun k l hkl => T.row_strict (Fin.lt_def.mp hkl) (hmem l)
  refine ext fun c => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := c
  have hmemij : ((i, j) : ℕ × ℕ) ∈ μ := hij
  have hi : i = 0 := fst_eq_zero_of_colLen_le_one h hmemij
  subst hi
  have hlt : j < μ.card := hcard ▸ _root_.YoungDiagram.mem_iff_lt_rowLen.mp hmemij
  refine Fin.ext ?_
  rw [rowSuperstandard_apply_val, YoungDiagram.readingIndex_zero]
  exact congrArg Fin.val (congrFun hid ⟨j, hlt⟩)

/-- A diagram with at most one row has at most one standard Young tableau. -/
theorem subsingleton_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  ⟨fun T U =>
    (eq_rowSuperstandard_of_colLen_le_one h T).trans
      (eq_rowSuperstandard_of_colLen_le_one h U).symm⟩

/-- A diagram with at most one column has at most one standard Young tableau. -/
theorem subsingleton_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  (transposeEquiv μ).subsingleton_congr.mpr (subsingleton_of_colLen_le_one (by simpa using h))

/-- If `μ` has a cell outside its first row and a cell outside its first column, then the
row-superstandard and the column-superstandard tableaux differ: reading by rows labels the cell
`(0, 1)` by `1`, while reading by columns labels it by the length of the first column. -/
theorem rowSuperstandard_ne_colSuperstandard (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    rowSuperstandard μ ≠ colSuperstandard μ := by
  have hmem : ((0, 1) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hrow
  intro heq
  have hval := congrArg Fin.val (DFunLike.congr_fun heq ⟨(0, 1), hmem⟩)
  rw [rowSuperstandard_apply_val, colSuperstandard_apply_val, YoungDiagram.readingIndex_zero,
    Prod.swap_prod_mk, YoungDiagram.readingIndex_one_zero,
    _root_.YoungDiagram.rowLen_transpose] at hval
  omega

end StandardYoungTableau

/-! ### Counting standard Young tableaux of extreme shapes -/

/-- **Every Young diagram has a standard Young tableau**, namely the row-superstandard one. -/
theorem standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.card_pos

/-- The number of standard Young tableaux of a given shape is never zero. -/
@[simp]
theorem standardCount_ne_zero (μ : YoungDiagram) : standardCount μ ≠ 0 :=
  (standardCount_pos μ).ne'

/-- A Young diagram with at most one row has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    standardCount μ = 1 := by
  have := StandardYoungTableau.subsingleton_of_colLen_le_one h
  rw [standardCount_def]
  exact Fintype.card_eq_one_iff.mpr
    ⟨StandardYoungTableau.rowSuperstandard μ, fun T => Subsingleton.elim _ _⟩

/-- A Young diagram with at most one column has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    standardCount μ = 1 := by
  rw [← standardCount_transpose]
  exact standardCount_eq_one_of_colLen_le_one (by simpa using h)

/-- A Young diagram with a cell outside its first row and a cell outside its first column has at
least two standard Young tableaux. -/
theorem one_lt_standardCount {μ : YoungDiagram} (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    1 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.one_lt_card_iff_nontrivial.mpr
    ⟨StandardYoungTableau.rowSuperstandard μ, StandardYoungTableau.colSuperstandard μ,
      StandardYoungTableau.rowSuperstandard_ne_colSuperstandard hrow hcol⟩

/-- **The shapes with a unique standard Young tableau** are exactly the diagrams with at most one
row and those with at most one column; the empty diagram, which satisfies both hypotheses, is one
of them. -/
@[simp]
theorem standardCount_eq_one_iff {μ : YoungDiagram} :
    standardCount μ = 1 ↔ μ.rowLen 0 ≤ 1 ∨ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h =>
    h.elim standardCount_eq_one_of_rowLen_le_one standardCount_eq_one_of_colLen_le_one⟩
  by_contra hcon
  have hrow : 1 < μ.rowLen 0 := by
    by_contra hrow
    exact hcon (Or.inl (by omega))
  have hcol : 1 < μ.colLen 0 := by
    by_contra hcol
    exact hcon (Or.inr (by omega))
  exact absurd h (one_lt_standardCount hrow hcol).ne'

end TauCeti
end
end TAF_LiteralSource_0173

section TAF_LiteralSource_0174
/- Original module: TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Character sums over a subgroup

For a finite subgroup `H` of a group `G` and a multiplicative character `χ : G →* k`, this file
studies the element `∑_{h ∈ H} χ(h) h` of the group algebra `k[G]`, here
`TauCeti.subgroupCharSum χ H`.

Two instances of it occur throughout representation theory, and are what this file exists to
share: the **norm element** `∑_{h ∈ H} h` of a subgroup, which is `χ = 1`, and the **signed sum**
`∑_{h ∈ H} sgn(h) h` of a subgroup of a permutation group, which is `χ = sgn`.  The row
symmetrizer and the column antisymmetrizer of a Young tableau are exactly these two.

Everything here follows from `χ` being multiplicative; no assumption that `χ` takes values in
square roots of `1` is needed, even for the square.  The translation laws say that left or right
multiplication by `p ∈ H` rescales the sum by `χ(p⁻¹)`, which is proved by reindexing the sum
along the bijection `h ↦ p * h` or `h ↦ h * p` of `H`; the square is then obtained by summing the
left translation law over `H`, where the scalars `χ(h) χ(h⁻¹) = χ(1) = 1` collapse and leave the
order of `H`.

The coefficients `k` form an arbitrary semiring, except in the right translation law: there the
scalar `χ(p⁻¹)` has to move past the values of `χ`, so `k` is taken to be commutative.

## Main definitions and results

* `TauCeti.subgroupCharSum`: the character sum `∑_{h ∈ H} χ(h) h` in `k[G]`;
* `TauCeti.subgroupCharSum_coeff`: its coefficients are `χ` on `H` and zero off `H`;
* `TauCeti.single_mul_subgroupCharSum` and `TauCeti.subgroupCharSum_mul_single`: the two
  translation laws, scaling by `χ(p⁻¹)` for `p ∈ H`;
* `TauCeti.subgroupCharSum_mul_self`: the character sum squares to `Nat.card H` times itself;
* `TauCeti.subgroupCharSum_eq_one` and `TauCeti.subgroupCharSum_eq_sum_of_eq_top`: its values on
  the two extreme subgroups, `⊥` and `⊤`.
-/

public section

namespace TauCeti

section Semiring

variable {k G : Type*} [Semiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- The **character sum** `∑_{h ∈ H} χ(h) h` of a multiplicative character `χ` over a finite
subgroup `H`, as an element of the group algebra `k[G]`. -/
noncomputable def subgroupCharSum : MonoidAlgebra k G :=
  ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G)

/-- The character sum is the `χ`-weighted sum of the basis elements indexed by `H`. -/
theorem subgroupCharSum_def :
    subgroupCharSum χ H = ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G) :=
  (rfl)

/-- The coefficient of a group element in the character sum is `χ` on `H` and zero off `H`. -/
@[simp]
theorem subgroupCharSum_coeff [DecidablePred (· ∈ H)] (g : G) :
    (subgroupCharSum χ H).coeff g = if g ∈ H then χ g else 0 := by
  classical
  simp [subgroupCharSum_def, MonoidAlgebra.coeff_sum, Finsupp.single_apply]
  split_ifs with hg
  · simpa [← Subtype.coe_inj] using Fintype.sum_ite_eq' (⟨g, hg⟩ : H) fun h : H => χ h
  · simp [fun h : H => ne_of_mem_of_not_mem h.property hg]

/-- Left multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem single_mul_subgroupCharSum (p : H) :
    MonoidAlgebra.single (p : G) 1 * subgroupCharSum χ H =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft p) _ _ fun h => ?_
  simp [MonoidAlgebra.smul_single, ← mul_assoc, ← map_mul]

/-- The character sum squares to the order of `H` times itself. -/
@[simp]
theorem subgroupCharSum_mul_self :
    subgroupCharSum χ H * subgroupCharSum χ H = Nat.card H • subgroupCharSum χ H := by
  nth_rewrite 1 [subgroupCharSum_def]
  simp only [Finset.sum_mul, smul_mul_assoc, MonoidAlgebra.of_apply, single_mul_subgroupCharSum,
    smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- Over the trivial subgroup the character sum has the single term `χ 1 • 1`, so it is `1`. -/
theorem subgroupCharSum_eq_one (h : H = ⊥) : subgroupCharSum χ H = 1 := by
  subst h
  simp [subgroupCharSum_def, MonoidAlgebra.one_def,
    Subsingleton.elim (default : (⊥ : Subgroup G)) 1]

/-- The character sum over the whole group is the `χ`-weighted sum over the group. -/
theorem subgroupCharSum_eq_sum_of_eq_top [Fintype G] (h : H = ⊤) :
    subgroupCharSum χ H = ∑ g : G, χ g • MonoidAlgebra.of k G g := by
  subst h
  exact Fintype.sum_equiv Subgroup.topEquiv.toEquiv _ _ fun _ => rfl

end Semiring

section CommSemiring

variable {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- Right multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem subgroupCharSum_mul_single (p : H) :
    subgroupCharSum χ H * MonoidAlgebra.single (p : G) 1 =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight p) _ _ fun h => ?_
  simp [MonoidAlgebra.smul_single, mul_comm (χ (p : G)⁻¹), mul_assoc, ← map_mul]

end CommSemiring

end TauCeti
end
end TAF_LiteralSource_0174

section TAF_LiteralSource_0175
/- Original module: TauCeti.RepresentationTheory.AsAlgebraHom -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The monoid-algebra action of a representation

General facts about `Representation.asAlgebraHom`, the extension of a representation `ρ` of a
monoid `G` to the monoid algebra `k[G]`.

The first is the description of the image of a monoid-algebra lift: since `k[G]` is spanned by
`G`, its image is, as a submodule, the span of the image of the defining monoid homomorphism
(`MonoidAlgebra.toSubmodule_range_lift`). For a representation this identifies both the submodule
and the subalgebra generated by its image. This is what turns a statement about a monoid action
into a statement about the subalgebra of endomorphisms it generates, as a double-centralizer
theorem needs.

The second is a vanishing criterion. An element `a` of the monoid algebra `k[G]` acting through a
representation `ρ` kills a vector `v` when three conditions meet: doubling is injective on `V`,
some `g` fixes `v`, and right multiplication by `g` negates `a`. The last two make
`ρ.asAlgebraHom a v` its own negative, and injective doubling turns being its own negative into
vanishing.

That is the mechanism behind the column-antisymmetrizer vanishing arguments of
`TauCeti/RepresentationTheory/Symmetric/`, which are its consumers: the antisymmetrizer of a set of
indices absorbs each permutation of those indices up to its sign, so against a vector fixed by an
odd such permutation the two conditions hold and the action is zero.

Nothing here is specific to symmetric groups or to `ℚ`. `G` is a monoid, and the module and the
scalars are arbitrary; nothing is asked of `2` in `k` at all: the hypothesis is that doubling is
injective on `V`, taken as an explicit assumption rather than read off the scalars. So this covers
torsion-free modules over `ℤ`, where `2` is not a unit, and equally modules over a ring with zero
divisors whose additive group has no `2`-torsion.

## Main results

* `MonoidAlgebra.toSubmodule_range_lift`: the image of a monoid-algebra lift is the span of the
  image of its defining monoid homomorphism.
* `Representation.range_asAlgebraHom_eq_adjoin`: the image of a representation's monoid-algebra
  action is the algebra generated by the representation.
* `Representation.mem_centralizer_range_asAlgebraHom_iff`: centralizing the monoid-algebra image
  is equivalent to commuting with every element of the monoid action.
* `Representation.commute_asAlgebraHom_of_forall_commute`: commuting with the monoid action
  propagates to the action of the monoid algebra.
* `Representation.asAlgebraHom_domCongr` and `Representation.asAlgebraHom_eq_sum`: the action of
  a transported element is the action through the pulled-back representation, and over a finite
  monoid the action of `x` is `∑ g, x g • ρ g`.
* `Representation.asAlgebraHom_quotient_mk`: the action on a quotient representation is induced
  by the action on the representation.
* `Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg`: with doubling injective on `V`, an
  algebra element negated by right multiplication by an element fixing `v` annihilates `v`.
-/

public section

section Range

namespace MonoidAlgebra

variable {k G A : Type*} [CommSemiring k] [Monoid G] [Semiring A] [Algebra k A]

/-- **The image of a monoid-algebra lift is the span of the image of the monoid homomorphism.**
The monoid algebra `k[G]` is spanned by the elements of `G`, so an element of its image is a finite
`k`-combination of the elements `F g`, and conversely every `F g` lies in the image. -/
theorem toSubmodule_range_lift (F : G →* A) :
    Subalgebra.toSubmodule (MonoidAlgebra.lift k A G F).range =
      Submodule.span k (Set.range F) := by
  -- `k[G]` is spanned by `G`: each element lies in the span of its support
  -- (`MonoidAlgebra.mem_span_support_coeff`), a subset of the image of `MonoidAlgebra.of`
  have htop : Submodule.span k (Set.range ⇑(MonoidAlgebra.of k G)) = ⊤ :=
    eq_top_iff.2 fun a _ =>
      Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff a)
  -- and `F` is the composite of `MonoidAlgebra.of` with the monoid-algebra lift
  have hrange : Set.range F = (MonoidAlgebra.lift k A G F).toLinearMap ''
      Set.range ⇑(MonoidAlgebra.of k G) := by
    rw [← Set.range_comp]
    simp [Function.comp_def]
  rw [hrange, ← Submodule.map_span, htop, Submodule.map_top]
  ext x
  simp [AlgHom.mem_range]

end MonoidAlgebra

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The image of a representation's monoid-algebra action is the span of the representation.** -/
theorem toSubmodule_range_asAlgebraHom (ρ : Representation k G V) :
    Subalgebra.toSubmodule ρ.asAlgebraHom.range = Submodule.span k (Set.range ρ) := by
  simpa only [Representation.asAlgebraHom_def] using MonoidAlgebra.toSubmodule_range_lift ρ

/-- **The image of a representation's monoid-algebra action is the algebra generated by the
representation.** -/
theorem range_asAlgebraHom_eq_adjoin (ρ : Representation k G V) :
    ρ.asAlgebraHom.range = Algebra.adjoin k (Set.range ρ) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Submodule.span k (Set.range ρ) := by
      rw [← toSubmodule_range_asAlgebraHom ρ]
      exact hx
    have hspan : Submodule.span k (Set.range ρ) ≤
        (Algebra.adjoin k (Set.range ρ)).toSubmodule :=
      Submodule.span_le.2 Algebra.subset_adjoin
    exact hspan hx'
  · exact Algebra.adjoin_le fun _ ⟨g, hg⟩ ↦ hg ▸
      ⟨MonoidAlgebra.of k G g, Representation.asAlgebraHom_of ρ g⟩

/-- If an endomorphism commutes with every operator in a representation, then it commutes with
the action of every element of the monoid algebra. -/
theorem commute_asAlgebraHom_of_forall_commute (ρ : Representation k G V) {x : Module.End k V}
    (h : ∀ g, Commute x (ρ g)) (a : MonoidAlgebra k G) : Commute x (ρ.asAlgebraHom a) := by
  refine Commute.span_right (R := k) (s := Set.range ρ) (fun y hy ↦ ?_) _ ?_
  · obtain ⟨g, rfl⟩ := hy
    exact h g
  · rw [← toSubmodule_range_asAlgebraHom ρ]
    exact ⟨a, rfl⟩

/-- An endomorphism centralizes the image of a representation's monoid-algebra action exactly
when it commutes with every operator in the representation. -/
theorem mem_centralizer_range_asAlgebraHom_iff (ρ : Representation k G V) {x : Module.End k V} :
    x ∈ Subalgebra.centralizer k (Set.range ⇑ρ.asAlgebraHom) ↔ ∀ g, Commute x (ρ g) := by
  rw [Subalgebra.mem_centralizer_iff]
  refine ⟨fun hx g ↦ (hx _ ⟨MonoidAlgebra.of k G g, Representation.asAlgebraHom_of ρ g⟩).symm,
    fun hx y hy ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hy
  exact (commute_asAlgebraHom_of_forall_commute ρ hx a).symm

/-- **The monoid-algebra action is natural in the monoid.** Acting by the transport of `x` along
an isomorphism `e : G ≃* H` is acting by `x` through the representation pulled back along `e`. -/
@[simp]
theorem asAlgebraHom_domCongr {H : Type*} [Monoid H] (ρ : Representation k H V) (e : G ≃* H)
    (x : MonoidAlgebra k G) :
    ρ.asAlgebraHom (MonoidAlgebra.domCongr k k e x) =
      Representation.asAlgebraHom (ρ.comp e.toMonoidHom) x :=
  MonoidAlgebra.lift_mapDomain ρ e.toMonoidHom x

/-- **The action of an element of the monoid algebra of a finite monoid** is the combination
`∑ g, x g • ρ g` of the operators of the representation, weighted by the coefficients of `x`. -/
theorem asAlgebraHom_eq_sum [Fintype G] (ρ : Representation k G V) (x : MonoidAlgebra k G) :
    ρ.asAlgebraHom x = ∑ g, x.coeff g • ρ g := by
  simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype]

end Representation

end Range

namespace Representation

section Quotient

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **The monoid-algebra action on a quotient representation** is induced by the action on the
representation: `x` sends the class of `v` to the class of `x · v`. -/
@[simp]
theorem asAlgebraHom_quotient_mk (ρ : Representation k G V) (N : Submodule k V)
    (hN : ∀ g, N ≤ N.comap (ρ g)) (x : MonoidAlgebra k G) (v : V) :
    (ρ.quotient N hN).asAlgebraHom x (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ.asAlgebraHom x v) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, Submodule.Quotient.mk_add]
  | single g r => simp [asAlgebraHom_single]

end Quotient

section Vanishing

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **An algebra element absorbed by a fixing element, up to sign, annihilates the vector.**
If doubling is injective on `V`, `g` fixes `v`, and right multiplication by `single g 1` negates
`a`, then `a` acts as zero on `v`. -/
theorem asAlgebraHom_eq_zero_of_mul_single_eq_neg
    (h2inj : Function.Injective fun w : V ↦ (2 : ℕ) • w)
    (ρ : Representation k G V) {a : MonoidAlgebra k G} {g : G} {v : V} (hfix : ρ g v = v)
    (hneg : a * MonoidAlgebra.single g 1 = -a) :
    ρ.asAlgebraHom a v = 0 := by
  -- Absorbing `g` into `a` costs a sign but leaves `v` alone, so the value equals its negation
  have key : ρ.asAlgebraHom a v = -(ρ.asAlgebraHom a v) := by
    conv_lhs => rw [← hfix]
    rw [← Representation.asAlgebraHom_single_one ρ, ← Module.End.mul_apply, ← map_mul, hneg,
      map_neg, LinearMap.neg_apply]
  -- so doubling it agrees with doubling `0`, and doubling is injective
  refine h2inj ?_
  simp only [two_nsmul, add_zero]
  nth_rewrite 1 [key]
  exact neg_add_cancel _

end Vanishing

end Representation
end
end TAF_LiteralSource_0175

section TAF_LiteralSource_0176
/- Original module: TauCeti.RepresentationTheory.SubgroupCharSum -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Character sums over a subgroup as operators

The character sum `∑_{h ∈ H} χ(h) h` of `TauCeti.subgroupCharSum` lives in the group algebra
`k[G]`, so it acts on any representation of `G` through `Representation.asAlgebraHom`.  This file
records the two facts every computation with that operator starts from.

Expanding it is immediate from the definition: it acts as the `χ`-weighted sum of the operators
`ρ h` over `h ∈ H` (`TauCeti.asAlgebraHom_subgroupCharSum_apply`).  Its vanishing is the
mechanism behind every antisymmetrizer argument: if some `p ∈ H` has `χ(p⁻¹) = -1`, the sum
absorbs `p` at the cost of a sign, so its value on a vector `p` fixes is its own negative, and
doubling being injective forces that value to be zero
(`TauCeti.asAlgebraHom_subgroupCharSum_apply_eq_zero`).  Injective doubling is the hypothesis of
`Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg`, taken as an assumption rather than
read off the scalars, so no invertibility of `2` in `k` is needed.

## Main results

* `TauCeti.asAlgebraHom_subgroupCharSum_apply`: the character sum acts as `∑_{h ∈ H} χ(h) ρ(h)`;
* `TauCeti.asAlgebraHom_subgroupCharSum_apply_eq_zero`: the character sum annihilates every vector
  fixed by an element of `H` whose inverse has character `-1`.
-/

public section

namespace TauCeti

section Semiring

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- The character sum of `χ` over `H`, acting on a representation, is the `χ`-weighted sum of the
actions of the elements of `H`. -/
theorem asAlgebraHom_subgroupCharSum_apply (ρ : Representation k G V) (v : V) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = ∑ h : H, χ (h : G) • ρ (h : G) v := by
  rw [subgroupCharSum_def, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun h _ => by
    rw [map_smul, LinearMap.smul_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]

end Semiring

section Ring

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- **A character sum annihilates whatever an element of character `-1` fixes.**  Right
multiplication by `p ∈ H` rescales the sum by `χ(p⁻¹) = -1`, so the value of the sum on a vector
fixed by `p` is its own negative; with doubling injective it vanishes. -/
theorem asAlgebraHom_subgroupCharSum_apply_eq_zero
    (h2inj : Function.Injective fun w : V => (2 : ℕ) • w) (ρ : Representation k G V) {p : G}
    (hp : p ∈ H) (hχ : χ p⁻¹ = -1) {v : V} (hfix : ρ p v = v) :
    ρ.asAlgebraHom (subgroupCharSum χ H) v = 0 :=
  Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg h2inj ρ hfix
    (by rw [subgroupCharSum_mul_single χ H ⟨p, hp⟩, hχ, neg_one_smul])

end Ring

end TauCeti
end
end TAF_LiteralSource_0176

section TAF_LiteralSource_0177
/- Original module: TauCeti.RepresentationTheory.Symmetric.RowColumnSubgroup -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The row and column groups of a Young tableau

A `μ`-tableau `t` is the datum a Young symmetrizer is built from: the row symmetrizer sums over
the permutations of the labels that stay inside their row of `t`, and the column antisymmetrizer
sums with signs over those that stay inside their column.

This file defines the two subgroups `YoungTableau.rowSubgroup t` and `YoungTableau.colSubgroup t`
of `Equiv.Perm (Fin μ.card)` cut out by those conditions, and proves the two facts the symmetrizer
theory rests on: the row and column groups meet trivially, because a cell is determined by its row
together with its column; and each of them is the product of the symmetric groups of the rows,
respectively columns, of `μ`.  It also records the transpositions that the two groups contain:
swapping two labels of a common row lies in the row group, and swapping two labels of a common
column lies in the column group.  Finally it recognises the two extreme shapes: the row group is
everything exactly when the diagram has at most one row, the column group is everything exactly
when it has at most one column, and either of those forces the other group to be trivial.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 2.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The **row group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own row of `t`. -/
def rowSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (rowIndex t)

/-- The **column group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own column of `t`. -/
def colSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (colIndex t)

@[simp]
theorem mem_rowSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ rowSubgroup t ↔ ∀ k, rowIndex t (σ k) = rowIndex t k :=
  mem_fiberSubgroup

@[simp]
theorem mem_colSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔ ∀ k, colIndex t (σ k) = colIndex t k :=
  mem_fiberSubgroup

/-- The row group of `t` is the group of permutations preserving the fibers of `rowIndex t`. -/
theorem rowSubgroup_def (t : YoungTableau μ) :
    rowSubgroup t = fiberSubgroup (rowIndex t) := by
  ext σ
  rw [mem_rowSubgroup, mem_fiberSubgroup]

/-- The column group of `t` is the group of permutations preserving the fibers of `colIndex t`. -/
theorem colSubgroup_def (t : YoungTableau μ) :
    colSubgroup t = fiberSubgroup (colIndex t) := by
  ext σ
  rw [mem_colSubgroup, mem_fiberSubgroup]

/-- The transposition of two labels lying in a common row of `t` belongs to the row group. -/
theorem swap_mem_rowSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : rowIndex t x = rowIndex t y) : Equiv.swap x y ∈ rowSubgroup t := by
  rw [rowSubgroup_def]
  exact swap_mem_fiberSubgroup h

/-- The transposition of two labels lying in a common column of `t` belongs to the column
group. -/
theorem swap_mem_colSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : colIndex t x = colIndex t y) : Equiv.swap x y ∈ colSubgroup t := by
  rw [colSubgroup_def]
  exact swap_mem_fiberSubgroup h

/-- The row and column groups of a `μ`-tableau meet only in the identity: a permutation of the
labels that stays inside the rows and inside the columns fixes every cell. -/
theorem rowSubgroup_inf_colSubgroup_eq_bot (t : YoungTableau μ) :
    rowSubgroup t ⊓ colSubgroup t = ⊥ := by
  rw [rowSubgroup_def, colSubgroup_def, fiberSubgroup_inf]
  exact fiberSubgroup_eq_bot_of_injective (rowIndex_colIndex_injective t)

/-- The row and column groups of a `μ`-tableau are disjoint subgroups of the symmetric group on
the labels. -/
theorem disjoint_rowSubgroup_colSubgroup (t : YoungTableau μ) :
    Disjoint (rowSubgroup t) (colSubgroup t) :=
  disjoint_iff.mpr (rowSubgroup_inf_colSubgroup_eq_bot t)

/-- The row group of a `μ`-tableau is the product, over the rows of `μ`, of the symmetric groups
of the rows.  Rows beyond the last one of `μ` are empty and contribute trivial factors. -/
def rowSubgroupMulEquiv (t : YoungTableau μ) :
    rowSubgroup t ≃* ∀ i, Equiv.Perm ↥(μ.row i) :=
  (MulEquiv.subgroupCongr (rowSubgroup_def t)).trans <|
    (fiberSubgroupMulEquivPiPerm (rowIndex t)).trans
      (MulEquiv.piCongrRight fun i => (rowFiberEquiv t i).permCongrHom)

/-- The column group of a `μ`-tableau is the product, over the columns of `μ`, of the symmetric
groups of the columns. -/
def colSubgroupMulEquiv (t : YoungTableau μ) :
    colSubgroup t ≃* ∀ j, Equiv.Perm ↥(μ.col j) :=
  (MulEquiv.subgroupCongr (colSubgroup_def t)).trans <|
    (fiberSubgroupMulEquivPiPerm (colIndex t)).trans
      (MulEquiv.piCongrRight fun j => (colFiberEquiv t j).permCongrHom)

/-- The `i`-th component of `rowSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem rowSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : rowSubgroup t) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowSubgroupMulEquiv t σ i (rowFiberEquiv t i k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  rw [rowSubgroupMulEquiv, MulEquiv.trans_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply, rowFiberEquiv_apply_coe]
  simp only [MulEquiv.subgroupCongr_apply]

/-- The `j`-th component of `colSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem colSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : colSubgroup t) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colSubgroupMulEquiv t σ j (colFiberEquiv t j k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  rw [colSubgroupMulEquiv, MulEquiv.trans_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply, colFiberEquiv_apply_coe]
  simp only [MulEquiv.subgroupCongr_apply]

/-- The permutation of the labels assembled from a family of permutations of the rows of `μ` moves
each label by the permutation of its own row. -/
@[simp]
theorem rowSubgroupMulEquiv_symm_apply (t : YoungTableau μ) (σ : ∀ i, Equiv.Perm ↥(μ.row i))
    (k : Fin μ.card) :
    (((rowSubgroupMulEquiv t).symm σ : Equiv.Perm (Fin μ.card)) k : Fin μ.card) =
      ((rowFiberEquiv t (rowIndex t k)).symm
        (σ (rowIndex t k) (rowFiberEquiv t (rowIndex t k) ⟨k, rfl⟩)) : Fin μ.card) := by
  rw [rowSubgroupMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply]

/-- The permutation of the labels assembled from a family of permutations of the columns of `μ`
moves each label by the permutation of its own column. -/
@[simp]
theorem colSubgroupMulEquiv_symm_apply (t : YoungTableau μ) (σ : ∀ j, Equiv.Perm ↥(μ.col j))
    (k : Fin μ.card) :
    (((colSubgroupMulEquiv t).symm σ : Equiv.Perm (Fin μ.card)) k : Fin μ.card) =
      ((colFiberEquiv t (colIndex t k)).symm
        (σ (colIndex t k) (colFiberEquiv t (colIndex t k) ⟨k, rfl⟩)) : Fin μ.card) := by
  rw [colSubgroupMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply]

/-! ### The extreme shapes -/

/-- A diagram whose zeroth column has at most one cell has only one row, so every label of a
tableau on it lies in row `0`. -/
theorem rowIndex_eq_zero_of_colLen_le_one (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1)
    (k : Fin μ.card) : rowIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).1 < μ.colLen (t.symm k : ℕ × ℕ).2 :=
    YoungDiagram.mem_iff_lt_colLen.mp hmem
  have hle : μ.colLen (t.symm k : ℕ × ℕ).2 ≤ μ.colLen 0 := μ.colLen_anti 0 _ (Nat.zero_le _)
  rw [rowIndex_def]
  omega

/-- A diagram whose zeroth row has at most one cell has only one column, so every label of a
tableau on it lies in column `0`. -/
theorem colIndex_eq_zero_of_rowLen_le_one (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1)
    (k : Fin μ.card) : colIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).2 < μ.rowLen (t.symm k : ℕ × ℕ).1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hle : μ.rowLen (t.symm k : ℕ × ℕ).1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 _ (Nat.zero_le _)
  rw [colIndex_def]
  omega

/-- The row group of a tableau is everything exactly when its shape has at most one row: with a
single row every permutation of the labels preserves it, while two rows are separated by a
transposition. -/
@[simp]
theorem rowSubgroup_eq_top_iff (t : YoungTableau μ) : rowSubgroup t = ⊤ ↔ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [rowIndex_eq_zero_of_colLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, rowIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, rowIndex t l = 1 :=
    ⟨t ⟨(1, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  have hswap := mem_rowSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The column group of a tableau is everything exactly when its shape has at most one column:
with a single column every permutation of the labels preserves it, while two columns are
separated by a transposition. -/
@[simp]
theorem colSubgroup_eq_top_iff (t : YoungTableau μ) : colSubgroup t = ⊤ ↔ μ.rowLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [colIndex_eq_zero_of_rowLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, colIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, colIndex t l = 1 :=
    ⟨t ⟨(0, 1), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  have hswap := mem_colSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The row and column groups meet trivially, so a full row group forces a trivial column
group. -/
theorem colSubgroup_eq_bot_of_rowSubgroup_eq_top (t : YoungTableau μ) (h : rowSubgroup t = ⊤) :
    colSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, top_inf_eq] at hinf

/-- The row and column groups meet trivially, so a full column group forces a trivial row
group. -/
theorem rowSubgroup_eq_bot_of_colSubgroup_eq_top (t : YoungTableau μ) (h : colSubgroup t = ⊤) :
    rowSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, inf_top_eq] at hinf

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0177

section TAF_LiteralSource_0178
/- Original module: TauCeti.RepresentationTheory.Symmetric.SignCharacter -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The sign character of a symmetric group

Mathlib's `Equiv.Perm.sign` is valued in `ℤˣ`. Representation theory wants the *linear character*
it induces over a coefficient ring: the homomorphism `Equiv.Perm α →* kˣ` obtained by pushing the
sign forward along `ℤ → k`. That is `TauCeti.signLinearCharacter`, and it is the `sgn` of the
character tables and of the induction examples -- the one-dimensional representation it carries is
`FDRep.ofLinearCharacter (signLinearCharacter k α)`, and restricting it along a subgroup inclusion
is precomposition, so a subgroup meets it as `(signLinearCharacter k α).comp H.subtype`.

Only two facts are needed to compute with it, and both are recorded here: its value in `k` is the
sign cast into `k`, and it sends a transposition to `-1`. In characteristic two those two values
coincide and the character is trivial; every statement that needs it to be nontrivial has to say so
by excluding that characteristic.

## Main definitions

* `TauCeti.signLinearCharacter`: the sign of a permutation, as a linear character valued in `kˣ`.

## Main statements

* `TauCeti.coe_signLinearCharacter_apply`: its value in `k` is the sign of the permutation, cast.
* `TauCeti.signLinearCharacter_swap`: it sends a transposition to `-1`.
-/

public section

namespace TauCeti

universe u v

/-- **The sign character of a symmetric group**: the linear character of `Equiv.Perm α` sending a
permutation to its sign, read in the units of `k` along the ring homomorphism `ℤ → k`. -/
def signLinearCharacter (k : Type u) [Ring k] (α : Type v) [DecidableEq α] [Fintype α] :
    Equiv.Perm α →* kˣ :=
  (Units.map (Int.castRingHom k).toMonoidHom).comp Equiv.Perm.sign

variable {k : Type u} [Ring k] {α : Type v} [DecidableEq α] [Fintype α]

/-- **The value of the sign character in `k` is the sign, cast into `k`.** This is the defining
equation: the definition itself is not exposed, and every computation with the character goes
through this lemma and `TauCeti.signLinearCharacter_swap`. -/
@[simp]
theorem coe_signLinearCharacter_apply (σ : Equiv.Perm α) :
    (signLinearCharacter k α σ : k) = ((Equiv.Perm.sign σ : ℤ) : k) :=
  -- `(rfl)`, not `rfl`: the body of `signLinearCharacter` is not `@[expose]`d, so this must not
  -- be inferred `@[defeq]`.
  (rfl)

/-- **The sign character sends a transposition to `-1`.** Over a ring of characteristic two this
value is `1`, which is why nontriviality of the character always carries a hypothesis on the
characteristic. -/
@[simp]
theorem signLinearCharacter_swap {i j : α} (h : i ≠ j) :
    signLinearCharacter k α (Equiv.swap i j) = -1 := by
  refine Units.ext ?_
  rw [coe_signLinearCharacter_apply, Equiv.Perm.sign_swap h]
  simp

end TauCeti
end
end TAF_LiteralSource_0178

section TAF_LiteralSource_0179
/- Original module: TauCeti.RepresentationTheory.Symmetric.Symmetrizer -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Young symmetrizers

For a Young tableau `t`, this file defines the row symmetrizer `a_t`, the column
antisymmetrizer `b_t`, and the Young symmetrizer `c_t = a_t b_t` in the rational group
algebra of the symmetric group on the entries of `t`.

The defining coefficient formulas are accompanied by the translation laws that characterize
the two factors: the row group fixes `a_t`, while the column group acts on `b_t` through the
sign character.  In particular, each factor squares to its subgroup order times itself.
Both factors are instances of a single construction: the character sum
`∑_{h ∈ H} χ(h) h` of a multiplicative character over a finite subgroup,
`TauCeti.subgroupCharSum`.  The row symmetrizer is the trivial character over the row group and
the column antisymmetrizer is the sign character over the column group, so the coefficient
formula, the two translation laws, the square, and the values on a trivial or full subgroup are
read off from that shared API instead of being proved once for each factor.
These are the elementary inputs to the essential-idempotence theorem for `c_t` and the
construction of Specht modules.  The two extreme shapes are also evaluated here: a trivial row or
column group collapses the corresponding factor to `1`, so on a shape with at most one row the
whole group fixes `c_t`, and on a shape with at most one column it scales `c_t` by the sign.  The
same two degeneracies evaluate the transported symmetrizer `youngSymmetrizerOver` outright, as the
full symmetrization `∑_σ σ` and the full antisymmetrization `∑_σ sgn(σ) σ` of the group algebra.
Finally, `b_t` acting on an arbitrary representation is unfolded into the signed sum over the
column group, which is how every downstream computation with the operator `b_t` begins.

The file closes with a third signed sum at the sign character, `TauCeti.antisymmetrizerOn X`: the
sum `∑ sgn(σ) σ` over the permutations of an arbitrary type fixing everything outside a finite set
`X`.  It is `b_t` with the column group replaced by the pointwise fixing subgroup of the
complement of `X`, so it shares the coefficient formula, the translation law and the vanishing
criterion with `b_t`, and it is the element the Garnir relations of
`TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean` are stated for.  Nothing about it
refers to a tableau, only to the sign character `TauCeti.signLinearCharacter`.

For a partition `μ` of `d`, `Nat.Partition.youngSymmetrizer` is the transported Young symmetrizer
of the row-superstandard tableau of the diagram of `μ`, with the labels of the diagram identified
with `Fin d`: the partition-indexed element `c_μ ∈ k[S_d]`.

The symmetrizers are built over `ℚ`, which is what the essential-idempotence theorem and the
Specht-module constructions downstream of this file work over.  The coefficients of `c_t` are in
fact integral -- each is a sum of signs -- so nothing about `c_t` itself demands rational
coefficients; it is *this* definition, over `ℚ`, whose coefficients are transported when `c_t` is
made to act on a module over another ring, which is `youngSymmetrizerOver`.  That transport goes
along `algebraMap ℚ k`, so it asks the target ring to be a `ℚ`-algebra.  The restriction is one
of the present implementation, not of the mathematics: an integral `c_t`, over `ℤ` or over an
arbitrary commutative ring, would remove it, and is a separate construction.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 2.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

noncomputable section

/-- Classical decidability of membership in the row group, used to form its finite sum. -/
local instance (t : YoungTableau μ) : DecidablePred (· ∈ rowSubgroup t) :=
  Classical.decPred _

/-- Classical decidability of membership in the column group, used to form its finite sum. -/
local instance decidablePredMemColSubgroup (t : YoungTableau μ) :
    DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- The **row symmetrizer** `a_t`, the sum of the permutations preserving the rows of `t`. -/
noncomputable def rowSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p

/-- The **column antisymmetrizer** `b_t`, the signed sum of the permutations preserving the
columns of `t`. -/
noncomputable def columnAntisymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ q : colSubgroup t,
    ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
      MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q

/-- The **Young symmetrizer** of `t`, with the convention `c_t = a_t b_t`. On a left module it
acts by column-antisymmetrization followed by row-symmetrization. -/
noncomputable def youngSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  rowSymmetrizer t * columnAntisymmetrizer t

/-- The row symmetrizer is the sum of the basis elements indexed by the row group. -/
theorem rowSymmetrizer_def (t : YoungTableau μ) :
    rowSymmetrizer t =
      ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p :=
  (rfl)

/-- The column antisymmetrizer is the sign-weighted sum of the basis elements indexed by the
column group. -/
theorem columnAntisymmetrizer_def (t : YoungTableau μ) :
    columnAntisymmetrizer t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q :=
  (rfl)

/-- The Young symmetrizer is the product `c_t = a_t b_t`. -/
theorem youngSymmetrizer_def (t : YoungTableau μ) :
    youngSymmetrizer t = rowSymmetrizer t * columnAntisymmetrizer t :=
  (rfl)

/-- The row symmetrizer is the character sum of the trivial character over the row group. -/
theorem rowSymmetrizer_eq_subgroupCharSum (t : YoungTableau μ) :
    rowSymmetrizer t = subgroupCharSum 1 (rowSubgroup t) := by
  rw [rowSymmetrizer_def, subgroupCharSum_def]
  simp

/-- The column antisymmetrizer is the character sum of the sign character over the column
group. -/
theorem columnAntisymmetrizer_eq_subgroupCharSum (t : YoungTableau μ) :
    columnAntisymmetrizer t =
      subgroupCharSum ((Units.coeHom ℚ).comp (signLinearCharacter ℚ (Fin μ.card)))
        (colSubgroup t) := by
  rw [columnAntisymmetrizer_def, subgroupCharSum_def]
  simp

/-- The coefficient of a permutation in the row symmetrizer is its row-group indicator. -/
@[simp]
theorem rowSymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (rowSymmetrizer t).coeff σ = if σ ∈ rowSubgroup t then 1 else 0 := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_coeff]
  simp

/-- The coefficient of a permutation in the column antisymmetrizer is its sign on the column
group and zero off that group. -/
@[simp]
theorem columnAntisymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (columnAntisymmetrizer t).coeff σ =
      if σ ∈ colSubgroup t then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_coeff]
  simp

/-- Left multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_left (t : YoungTableau μ) (p : rowSubgroup t) :
    MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 * rowSymmetrizer t =
      rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, single_mul_subgroupCharSum]
  simp

/-- Right multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_right (t : YoungTableau μ) (p : rowSubgroup t) :
    rowSymmetrizer t * MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 =
      rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_single]
  simp

/-- Left multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_left (t : YoungTableau μ) (q : colSubgroup t) :
    MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 * columnAntisymmetrizer t =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, single_mul_subgroupCharSum]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Equiv.Perm.sign_inv]

/-- Right multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    columnAntisymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_single]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Equiv.Perm.sign_inv]

/-- The row symmetrizer squares to the order of the row group times itself. -/
@[simp]
theorem rowSymmetrizer_sq (t : YoungTableau μ) :
    rowSymmetrizer t * rowSymmetrizer t =
      Nat.card (rowSubgroup t) • rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_self]

/-- The column antisymmetrizer squares to the order of the column group times itself. -/
@[simp]
theorem columnAntisymmetrizer_sq (t : YoungTableau μ) :
    columnAntisymmetrizer t * columnAntisymmetrizer t =
      Nat.card (colSubgroup t) • columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_self]

/-- The row group fixes the Young symmetrizer on the left. -/
@[simp]
theorem mul_youngSymmetrizer_left (t : YoungTableau μ) (p : rowSubgroup t) :
    MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 * youngSymmetrizer t =
      youngSymmetrizer t := by
  rw [youngSymmetrizer_def, ← mul_assoc, mul_rowSymmetrizer_left]

/-- The column group acts on the Young symmetrizer on the right through its sign character. -/
@[simp]
theorem mul_youngSymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    youngSymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        youngSymmetrizer t := by
  rw [youngSymmetrizer_def, mul_assoc, mul_columnAntisymmetrizer_right, mul_smul_comm]

/-- The coefficient of the identity permutation in a Young symmetrizer is one. -/
@[simp]
theorem youngSymmetrizer_coeff_one (t : YoungTableau μ) :
    (youngSymmetrizer t).coeff 1 = 1 := by
  rw [youngSymmetrizer_def, rowSymmetrizer_def, columnAntisymmetrizer_def,
    Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.coeff_sum, MonoidAlgebra.of_apply]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, one_mul]
  have hmul (p : rowSubgroup t) (q : colSubgroup t) :
      (p : Equiv.Perm (Fin μ.card)) * q = 1 ↔ p = 1 ∧ q = 1 := by
    constructor
    · intro hpq
      have hpq' := Subgroup.disjoint_iff_mul_eq_one.mp
        (disjoint_rowSubgroup_colSubgroup t) p.property q.property hpq
      exact ⟨Subtype.ext hpq'.1, Subtype.ext hpq'.2⟩
    · rintro ⟨rfl, rfl⟩
      simp
  have heq (p : rowSubgroup t) (q : colSubgroup t) :
      (q : Equiv.Perm (Fin μ.card)) =
          (p : Equiv.Perm (Fin μ.card))⁻¹ * 1 ↔ p = 1 ∧ q = 1 := by
    simpa only [mul_one] using
      ((mul_eq_one_iff_eq_inv' :
        (p : Equiv.Perm (Fin μ.card)) * q = 1 ↔
          (q : Equiv.Perm (Fin μ.card)) =
            (p : Equiv.Perm (Fin μ.card))⁻¹).symm.trans (hmul p q))
  simp_rw [heq]
  rw [Finset.sum_eq_single (1 : rowSubgroup t)]
  · rw [Finset.sum_eq_single (1 : colSubgroup t)] <;> simp
  · exact fun p _ hp => by simp [hp]
  · simp

/-- The coefficient of a row-group permutation in a Young symmetrizer is one: the row group
translates `c_t` to itself, so all of its coefficients on the row group agree with the
coefficient at the identity. -/
theorem youngSymmetrizer_coeff_eq_one_of_mem_rowSubgroup (t : YoungTableau μ)
    {p : Equiv.Perm (Fin μ.card)} (hp : p ∈ rowSubgroup t) :
    (youngSymmetrizer t).coeff p = 1 := by
  have h := congrArg (fun x => MonoidAlgebra.coeff x p) (mul_youngSymmetrizer_left t ⟨p, hp⟩)
  simpa using h.symm

/-- A Young symmetrizer is nonzero. -/
@[simp]
theorem youngSymmetrizer_ne_zero (t : YoungTableau μ) :
    youngSymmetrizer t ≠ 0 := by
  intro h
  have := congrArg (fun x =>
    x.coeff (1 : Equiv.Perm (Fin μ.card))) h
  simp at this

/-! ### The symmetrizers of an extreme shape -/

/-- A trivial row group leaves the row symmetrizer as the empty symmetrization, `1`. -/
theorem rowSymmetrizer_eq_one (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    rowSymmetrizer t = 1 := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_one _ _ h]

/-- A trivial column group leaves the column antisymmetrizer as the empty antisymmetrization,
`1`. -/
theorem columnAntisymmetrizer_eq_one (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    columnAntisymmetrizer t = 1 := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_one _ _ h]

/-- With a trivial column group the Young symmetrizer is the row symmetrizer. -/
theorem youngSymmetrizer_eq_rowSymmetrizer (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    youngSymmetrizer t = rowSymmetrizer t := by
  rw [youngSymmetrizer_def, columnAntisymmetrizer_eq_one t h, mul_one]

/-- With a trivial row group the Young symmetrizer is the column antisymmetrizer. -/
theorem youngSymmetrizer_eq_columnAntisymmetrizer (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    youngSymmetrizer t = columnAntisymmetrizer t := by
  rw [youngSymmetrizer_def, rowSymmetrizer_eq_one t h, one_mul]

/-- On a shape with at most one row every group element fixes the Young symmetrizer. -/
theorem single_mul_youngSymmetrizer_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = youngSymmetrizer t :=
  mul_youngSymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-- On a shape with at most one column every group element scales the Young symmetrizer by its
sign. -/
theorem single_mul_youngSymmetrizer_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t =
      ((Equiv.Perm.sign g : ℤ) : ℚ) • youngSymmetrizer t := by
  rw [youngSymmetrizer_eq_columnAntisymmetrizer t (rowSubgroup_eq_bot_of_colSubgroup_eq_top t h)]
  exact mul_columnAntisymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-! ### The column antisymmetrizer as an operator -/

/-- The column antisymmetrizer of `t` acts on any representation as the signed sum of the
permutations in the column group of `t`. -/
theorem asAlgebraHom_columnAntisymmetrizer_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (Equiv.Perm (Fin μ.card)) V) (t : YoungTableau μ) (v : V) :
    ρ.asAlgebraHom (columnAntisymmetrizer t) v =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) • ρ q v := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, asAlgebraHom_subgroupCharSum_apply]
  simp

section Transport

variable (k : Type*) [Semiring k] [Algebra ℚ k]

/-- The Young symmetrizer `c_t` with the coefficients of its rational form transported into a
`ℚ`-algebra `k`, so that it can act on a `k`-module. The algebra `k` need not be commutative.

The `ℚ`-algebra hypothesis comes from `youngSymmetrizer` being defined over `ℚ` here, not from
`c_t`, whose coefficients are integral. -/
noncomputable def youngSymmetrizerOver (t : YoungTableau μ) :
    MonoidAlgebra k (Equiv.Perm (Fin μ.card)) :=
  MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ k) (youngSymmetrizer t)

/-- The transport of a Young symmetrizer applies the structure map of the algebra to every
coefficient. -/
theorem youngSymmetrizerOver_def (t : YoungTableau μ) :
    youngSymmetrizerOver k t =
      MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ k) (youngSymmetrizer t) :=
  (rfl)

/-- The coefficients of the transported Young symmetrizer are the images of the rational
coefficients. -/
@[simp]
theorem youngSymmetrizerOver_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (youngSymmetrizerOver k t).coeff σ = algebraMap ℚ k ((youngSymmetrizer t).coeff σ) := by
  rw [youngSymmetrizerOver_def, MonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply]

/-- **The column group acts on the transported Young symmetrizer through its sign character.**
The sign acts as a rational scalar, using the `ℚ`-algebra structure of `k`. -/
@[simp]
theorem mul_youngSymmetrizerOver_right (t : YoungTableau μ) (q : colSubgroup t) :
    youngSymmetrizerOver k t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) • youngSymmetrizerOver k t := by
  have h := congrArg (MonoidAlgebra.mapAlgHom (Equiv.Perm (Fin μ.card)) (Algebra.ofId ℚ k))
    (mul_youngSymmetrizer_right t q)
  rw [map_mul, MonoidAlgebra.mapAlgHom_single, map_one, map_smul] at h
  rwa [youngSymmetrizerOver_def]

/-- **The Young symmetrizer of a shape with at most one row is the full symmetrization**
`∑_σ σ`: the row group is everything and the column group is trivial. -/
theorem youngSymmetrizerOver_eq_sum_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) :
    youngSymmetrizerOver k t =
      ∑ σ : Equiv.Perm (Fin μ.card), MonoidAlgebra.of k (Equiv.Perm (Fin μ.card)) σ := by
  rw [youngSymmetrizerOver_def,
    youngSymmetrizer_eq_rowSymmetrizer t (colSubgroup_eq_bot_of_rowSubgroup_eq_top t h),
    rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_sum_of_eq_top _ _ h, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MonoidHom.one_apply, one_smul, MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single,
    map_one, MonoidAlgebra.of_apply]

end Transport

section TransportRing

-- The signed sum below uses the target ring's `ℤ`-action.
variable (k : Type*) [Ring k] [Algebra ℚ k]

/-- **The Young symmetrizer of a shape with at most one column is the full antisymmetrization**
`∑_σ sgn(σ) σ`: the column group is everything and the row group is trivial. -/
theorem youngSymmetrizerOver_eq_sum_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) :
    youngSymmetrizerOver k t =
      ∑ σ : Equiv.Perm (Fin μ.card),
        (Equiv.Perm.sign σ : ℤ) • MonoidAlgebra.of k (Equiv.Perm (Fin μ.card)) σ := by
  rw [youngSymmetrizerOver_def,
    youngSymmetrizer_eq_columnAntisymmetrizer t (rowSubgroup_eq_bot_of_colSubgroup_eq_top t h),
    columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_sum_of_eq_top _ _ h, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply]
  rw [Int.cast_smul_eq_zsmul ℚ, map_zsmul, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapAlgHom_single, map_one, MonoidAlgebra.of_apply]

end TransportRing

end

end YoungTableau

/-! ## The antisymmetrizer of a set of points

The signed sum over the permutations supported in a finite set is the character sum of the sign
character over the pointwise fixing subgroup of the complement.  Nothing below refers to a
tableau, only to `TauCeti.signLinearCharacter`. -/

section AntisymmetrizerOn

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Classical decidability of membership in the subgroup of permutations fixing everything outside
a finite set, used to form its finite sum. -/
noncomputable local instance decidablePredMemFixingSubgroupCompl (X : Finset α) :
    DecidablePred (· ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  Classical.decPred _

/-- The **antisymmetrizer** of a finite set `X` of points: the signed sum `∑ sgn(σ) σ`, in the
rational group algebra of `Equiv.Perm α`, over the permutations `σ` fixing every point outside `X`.

For `X` the labels lying in one column of a Young tableau this is the factor of that tableau's
column antisymmetrizer belonging to that column; the relations it satisfies on the polytabloids of
a tableau are the Garnir relations. -/
noncomputable def antisymmetrizerOn (X : Finset α) : MonoidAlgebra ℚ (Equiv.Perm α) :=
  subgroupCharSum ((Units.coeHom ℚ).comp (signLinearCharacter ℚ α))
    (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ))

theorem antisymmetrizerOn_def (X : Finset α) :
    antisymmetrizerOn X =
      subgroupCharSum ((Units.coeHom ℚ).comp (signLinearCharacter ℚ α))
        (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  (rfl)

omit [DecidableEq α] [Fintype α] in
/-- A permutation fixing every point outside `X` belongs to the subgroup the antisymmetrizer of
`X` is summed over. -/
private theorem mem_fixingSubgroup_compl_of_forall_notMem {X : Finset α} {σ : Equiv.Perm α}
    (hσ : ∀ k ∉ X, σ k = k) : σ ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) :=
  (mem_fixingSubgroup_iff _).mpr fun k hk => hσ k (by simpa using hk)

/-- The coefficient of a permutation in `TauCeti.antisymmetrizerOn X` is its sign if it is
supported in `X`, and zero otherwise. -/
@[simp]
theorem antisymmetrizerOn_coeff (X : Finset α) (σ : Equiv.Perm α) :
    (antisymmetrizerOn X).coeff σ =
      if ∀ k ∉ X, σ k = k then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  classical
  rw [antisymmetrizerOn_def, subgroupCharSum_coeff]
  simp [mem_fixingSubgroup_iff]

/-- The permutations summed over by `TauCeti.antisymmetrizerOn X`, as a `Finset`. -/
private theorem mem_filter_forall_notMem_iff (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (σ : Equiv.Perm α) :
    σ ∈ ({σ : Equiv.Perm α | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm α)) ↔
      σ ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) := by
  simp [mem_fixingSubgroup_iff]

/-- The antisymmetrizer of a set, acting on a representation of the symmetric group, is the signed
sum of the actions of the permutations fixing everything outside that set.

The decidability of the summation range is an instance argument rather than a synthesized one, so
that the equation rewrites a sum however its own filter was built. -/
theorem asAlgebraHom_antisymmetrizerOn_apply {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (v : M) :
    V.asAlgebraHom (antisymmetrizerOn X) v =
      ∑ σ ∈ {σ : Equiv.Perm α | ∀ k ∉ X, σ k = k},
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • V σ v := by
  rw [antisymmetrizerOn_def, asAlgebraHom_subgroupCharSum_apply,
    ← Finset.sum_subtype _ (mem_filter_forall_notMem_iff X)
      (fun σ => ((Units.coeHom ℚ).comp (signLinearCharacter ℚ α)) σ • V σ v)]
  simp

/-- **Right multiplication by a permutation supported in `X` scales the antisymmetrizer of `X` by
its sign**, since the antisymmetrizer absorbs it up to that sign. -/
@[simp]
theorem antisymmetrizerOn_mul_single {X : Finset α} {p : Equiv.Perm α} (hp : ∀ k ∉ X, p k = k) :
    antisymmetrizerOn X * MonoidAlgebra.single p (1 : ℚ) =
      ((Equiv.Perm.sign p : ℤ) : ℚ) • antisymmetrizerOn X := by
  rw [antisymmetrizerOn_def,
    subgroupCharSum_mul_single _ _ ⟨p, mem_fixingSubgroup_compl_of_forall_notMem hp⟩]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Equiv.Perm.sign_inv]

/-- **A signed sum annihilates whatever an odd permutation in it fixes.**  If an odd permutation
supported in `X` fixes `v`, then the antisymmetrizer of `X` kills `v`: absorbing that permutation
negates the sum while leaving `v` alone. -/
theorem asAlgebraHom_antisymmetrizerOn_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) {X : Finset α} {p : Equiv.Perm α}
    (hp : ∀ k ∉ X, p k = k) (hsign : Equiv.Perm.sign p = -1) {v : M} (hv : V p v = v) :
    V.asAlgebraHom (antisymmetrizerOn X) v = 0 := by
  have : HasUniqueDiv M := .of_module_rat _
  rw [antisymmetrizerOn_def]
  refine asAlgebraHom_subgroupCharSum_apply_eq_zero _ _ (nsmul_right_injective two_ne_zero) V
    (mem_fixingSubgroup_compl_of_forall_notMem hp) ?_ hv
  simp [hsign]

end AntisymmetrizerOn

end TauCeti

namespace Nat.Partition

open TauCeti

variable {d : ℕ} (μ : d.Partition) (k : Type*) [CommSemiring k] [Algebra ℚ k]

/-- **The Young symmetrizer of a partition** `μ` of `d`, as an element of `k[S_d]`: the Young
symmetrizer `c_t = a_t b_t` of the row-superstandard tableau `t` of the diagram of `μ`, transported
to `k` and with the labels of the diagram identified with `Fin d` along
`YoungDiagram.card_ofPartition`. This is the identification along which `TauCeti.spechtModule μ`
is a representation of `S_d`. -/
noncomputable def youngSymmetrizer : MonoidAlgebra k (Equiv.Perm (Fin d)) :=
  MonoidAlgebra.domCongr k k (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom
    (YoungTableau.youngSymmetrizerOver k
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau)

/-- The Young symmetrizer of a partition is the transported Young symmetrizer of the
row-superstandard tableau of its diagram. -/
theorem youngSymmetrizer_def :
    μ.youngSymmetrizer k =
      MonoidAlgebra.domCongr k k (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom
        (YoungTableau.youngSymmetrizerOver k
          (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau) :=
  (rfl)

/-- The coefficient of the identity in the Young symmetrizer is `1`. -/
@[simp]
theorem youngSymmetrizer_coeff_one : (μ.youngSymmetrizer k).coeff 1 = 1 := by
  rw [youngSymmetrizer_def, MonoidAlgebra.coeff_domCongr, map_one,
    YoungTableau.youngSymmetrizerOver_coeff, YoungTableau.youngSymmetrizer_coeff_one, map_one]

end Nat.Partition
end
end TAF_LiteralSource_0179

section TAF_LiteralSource_0180
/- Original module: TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Young-symmetrizer left ideals

For a Young tableau `t`, this file constructs the principal left ideal
`ℚ[Sₙ] c_t` generated by its Young symmetrizer and bundles that ideal as a
finite-dimensional representation of the symmetric group.

Nothing here uses the essential idempotence `c_t * c_t = κ • c_t`: that runs the other way,
since identifying the scalar needs the dimension of the ideal, which puts it in the form
`κ = n! / finrank ℚ (ℚ[Sₙ] c_t)`, or equivalently `κ = n! / f^λ` through the standard basis
theorem `dim S^λ = f^λ`. Nor is this representation identified here with the span of the
polytabloids inside the Young permutation module.

## Main definitions

* `YoungTableau.spechtIdeal` is the principal left ideal generated by `c_t`.
* `YoungTableau.spechtIdealRep` is its symmetric-group representation.
* `YoungTableau.spechtIdealFDRep` is the finite-dimensional bundled form.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978],
  Chapter 2.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

noncomputable section

/-- The principal left ideal `ℚ[Sₙ] c_t` generated by the Young symmetrizer of `t`. -/
def spechtIdeal (t : YoungTableau μ) :
    Submodule (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :=
  MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) ∙ youngSymmetrizer t

/-- The Young-symmetrizer left ideal is contained in a submodule exactly when that
submodule contains its generator. -/
@[simp]
theorem spechtIdeal_le_iff (t : YoungTableau μ)
    (I : Submodule (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))) :
    spechtIdeal t ≤ I ↔ youngSymmetrizer t ∈ I := by
  rw [spechtIdeal, Submodule.span_singleton_le_iff_mem]

/-- An element lies in `ℚ[Sₙ] c_t` exactly when it is a left multiple of `c_t`. -/
@[simp]
theorem mem_spechtIdeal_iff (t : YoungTableau μ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    x ∈ spechtIdeal t ↔
      ∃ a : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)),
        a * youngSymmetrizer t = x := by
  simp only [spechtIdeal, Submodule.mem_span_singleton, smul_eq_mul]

/-- The Young symmetrizer belongs to the left ideal that it generates. -/
theorem youngSymmetrizer_mem_spechtIdeal (t : YoungTableau μ) :
    youngSymmetrizer t ∈ spechtIdeal t :=
  Submodule.mem_span_singleton_self _

/-- The Young-symmetrizer left ideal is zero exactly when its generator is zero. -/
@[simp]
theorem spechtIdeal_eq_bot_iff (t : YoungTableau μ) :
    spechtIdeal t = ⊥ ↔ youngSymmetrizer t = 0 :=
  Submodule.span_singleton_eq_bot

/-- The Young-symmetrizer left ideal is nonzero. -/
theorem spechtIdeal_ne_bot (t : YoungTableau μ) :
    spechtIdeal t ≠ ⊥ :=
  (spechtIdeal_eq_bot_iff t).not.mpr (youngSymmetrizer_ne_zero t)

/-- A Young-symmetrizer left ideal is a nontrivial module. -/
instance instNontrivialSpechtIdeal (t : YoungTableau μ) :
    Nontrivial (spechtIdeal t) :=
  Submodule.nontrivial_iff_ne_bot.mpr (spechtIdeal_ne_bot t)

/-- The representation of the symmetric group on `ℚ[Sₙ] c_t` by left multiplication. -/
noncomputable abbrev spechtIdealRep (t : YoungTableau μ) :
    Rep ℚ (Equiv.Perm (Fin μ.card)) :=
  Rep.of <| Representation.ofModule' (spechtIdeal t)

/-- The action on the Young-symmetrizer left ideal is multiplication on the left by the
corresponding group-algebra basis element. -/
@[simp]
theorem spechtIdealRep_ρ_apply_coe (t : YoungTableau μ)
    (g : Equiv.Perm (Fin μ.card))
    (x : spechtIdeal t) :
    ((spechtIdealRep t).ρ g x :
      MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      MonoidAlgebra.single g 1 *
        (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) := by
  rw [Rep.of_ρ, Representation.ofModule'_apply, Submodule.coe_smul, smul_eq_mul]

/-- A Young-symmetrizer left ideal is finite-dimensional over `ℚ`. -/
noncomputable instance instModuleFiniteSpechtIdeal (t : YoungTableau μ) :
    Module.Finite ℚ (spechtIdeal t) := by
  let : Module.Finite
      (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) (spechtIdeal t) :=
    Module.Finite.of_fg <| by
      rw [spechtIdeal]
      exact Submodule.fg_span_singleton _
  exact Module.Finite.trans
    (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) _

/-- The left ideal generated by a Young symmetrizer, bundled as a finite-dimensional
representation. -/
noncomputable abbrev spechtIdealFDRep (t : YoungTableau μ) :
    FDRep ℚ (Equiv.Perm (Fin μ.card)) :=
  FDRep.of (spechtIdealRep t).ρ

/-- The Young-symmetrizer left ideal has positive dimension. -/
theorem finrank_spechtIdeal_pos (t : YoungTableau μ) :
    0 < Module.finrank ℚ (spechtIdealFDRep t) :=
  Module.finrank_pos

/-- The dimension of `ℚ[Sₙ] c_t` is at most `n!`, the dimension of the regular
representation. -/
theorem finrank_spechtIdeal_le_factorial (t : YoungTableau μ) :
    Module.finrank ℚ (spechtIdealFDRep t) ≤ μ.card.factorial := by
  calc
    Module.finrank ℚ (spechtIdealFDRep t) ≤
        Module.finrank ℚ
          (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :=
      Submodule.finrank_le ((spechtIdeal t).restrictScalars ℚ)
    _ = Fintype.card (Equiv.Perm (Fin μ.card)) := by
      rw [Module.finrank_eq_card_basis
        (MonoidAlgebra.basis (Equiv.Perm (Fin μ.card)) ℚ)]
    _ = μ.card.factorial := by
      simpa using
        (Fintype.card_perm :
          Fintype.card (Equiv.Perm (Fin μ.card)) =
            (Fintype.card (Fin μ.card)).factorial)

end

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0180

section TAF_LiteralSource_0181
/- Original module: TauCeti.RepresentationTheory.Symmetric.Relabel -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Relabeling a Young tableau conjugates its Young symmetrizer

A Young symmetrizer, and with it the left ideal `ℚ[Sₙ] c_t` it generates, is built from a
`μ`-tableau `t`, while the Specht module it presents is meant to depend only on the shape `μ`.
This file supplies that independence.

Relabeling the labels of `t` by a permutation `σ` conjugates the row group and the column group
of `t`, hence conjugates the row symmetrizer, the column antisymmetrizer, and the Young
symmetrizer:

`c_{σt} = σ c_t σ⁻¹`.

Consequently `ℚ[Sₙ] c_{σt} = (ℚ[Sₙ] c_t) σ⁻¹`, and right multiplication by `σ` is an isomorphism
of representations from `ℚ[Sₙ] c_{σt}` to `ℚ[Sₙ] c_t`.  Since any two tableaux of the same shape
differ by a relabeling, the representation `ℚ[Sₙ] c_t`, and in particular its dimension and its
character, depend only on the shape of `t`.

## Main results

* `YoungTableau.youngSymmetrizer_relabel`: the Young symmetrizer of a relabeled tableau is the
  conjugate of the Young symmetrizer, and `YoungTableau.youngSymmetrizerOver_relabel` says the
  same for its transport to a `ℚ`-algebra.
* `YoungTableau.spechtIdealRelabelRepEquiv`: right multiplication by `σ` as an isomorphism of
  representations `ℚ[Sₙ] c_{σt} ≅ ℚ[Sₙ] c_t`.
* `YoungTableau.spechtIdealRepIso`, `YoungTableau.finrank_spechtIdeal_eq` and
  `YoungTableau.character_spechtIdealRep_eq`: the representation, its dimension, and its character
  depend only on the shape of the tableau.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 2 and 3: the Layer 3 Specht module `spechtModule μ` is indexed by the shape `μ` alone,
  while the Layer 2 Young symmetrizer and its left ideal are built from a tableau, so the
  tableau-independence proved here is what makes the Layer 3 indexing legitimate.
-/

public section

namespace TauCeti

namespace YoungTableau

section GroupAlgebra

variable {G : Type*} [Group G]

/-- The group-algebra basis element of `g`, as a unit whose inverse is the basis element of `g⁻¹`.
Private: this is the group-algebra plumbing for the conjugation computations and for the
right-translation equivalence below. -/
private noncomputable def singleUnit (g : G) : (MonoidAlgebra ℚ G)ˣ :=
  Units.map (MonoidAlgebra.of ℚ G) (toUnits g)

@[simp]
private theorem coe_singleUnit (g : G) :
    ((singleUnit g : (MonoidAlgebra ℚ G)ˣ) : MonoidAlgebra ℚ G) = MonoidAlgebra.single g 1 :=
  rfl

@[simp]
private theorem coe_inv_singleUnit (g : G) :
    (((singleUnit g)⁻¹ : (MonoidAlgebra ℚ G)ˣ) : MonoidAlgebra ℚ G) =
      MonoidAlgebra.single g⁻¹ 1 :=
  rfl

/-- Conjugating in the group algebra conjugates the indices of the coefficients.  Private: this is
group-algebra plumbing for the conjugation computations below. -/
private theorem coeff_conj (g h : G) (x : MonoidAlgebra ℚ G) :
    (MonoidAlgebra.single g (1 : ℚ) * x * MonoidAlgebra.single g⁻¹ 1).coeff h =
      x.coeff (g⁻¹ * h * g) := by
  simp [mul_assoc]

end GroupAlgebra

variable {μ : YoungDiagram} (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)

/-! ## The row and column groups of a relabeled tableau -/

/-- Relabeling by `σ` conjugates the row group by `σ`. -/
theorem rowSubgroup_relabel :
    rowSubgroup (relabel σ t) = (rowSubgroup t).map (MulAut.conj σ).toMonoidHom := by
  rw [rowSubgroup_def, rowSubgroup_def]
  exact (fiberSubgroup_map_conj σ fun _ _ => by simp).symm

/-- Relabeling by `σ` conjugates the column group by `σ`. -/
theorem colSubgroup_relabel :
    colSubgroup (relabel σ t) = (colSubgroup t).map (MulAut.conj σ).toMonoidHom := by
  rw [colSubgroup_def, colSubgroup_def]
  exact (fiberSubgroup_map_conj σ fun _ _ => by simp).symm

/-- A permutation preserves the rows of the relabeled tableau exactly when its conjugate preserves
the rows of the original one.

Not a `simp` lemma: `mem_rowSubgroup` and `rowIndex_relabel` already simplify the left-hand side
past this normal form, to the pointwise condition on rows. -/
theorem mem_rowSubgroup_relabel {τ : Equiv.Perm (Fin μ.card)} :
    τ ∈ rowSubgroup (relabel σ t) ↔ σ⁻¹ * τ * σ ∈ rowSubgroup t := by
  rw [rowSubgroup_relabel, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- A permutation preserves the columns of the relabeled tableau exactly when its conjugate
preserves the columns of the original one.

Not a `simp` lemma: `mem_colSubgroup` and `colIndex_relabel` already simplify the left-hand side
past this normal form, to the pointwise condition on columns. -/
theorem mem_colSubgroup_relabel {τ : Equiv.Perm (Fin μ.card)} :
    τ ∈ colSubgroup (relabel σ t) ↔ σ⁻¹ * τ * σ ∈ colSubgroup t := by
  rw [colSubgroup_relabel, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-! ## The symmetrizers of a relabeled tableau -/

/-- Relabeling by `σ` conjugates the row symmetrizer by `σ`. -/
@[simp]
theorem rowSymmetrizer_relabel :
    rowSymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * rowSymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  ext τ
  rw [coeff_conj, rowSymmetrizer_coeff, rowSymmetrizer_coeff]
  by_cases h : σ⁻¹ * τ * σ ∈ rowSubgroup t
  · rw [ite_eq_left h, ite_eq_left ((mem_rowSubgroup_relabel σ t).mpr h)]
  · rw [ite_eq_right h, ite_eq_right fun hτ => h ((mem_rowSubgroup_relabel σ t).mp hτ)]

/-- Relabeling by `σ` conjugates the column antisymmetrizer by `σ`; the signs are unchanged,
conjugate permutations having equal signs. -/
@[simp]
theorem columnAntisymmetrizer_relabel :
    columnAntisymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * columnAntisymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  ext τ
  rw [coeff_conj, columnAntisymmetrizer_coeff, columnAntisymmetrizer_coeff]
  have hsign : Equiv.Perm.sign (σ⁻¹ * τ * σ) = Equiv.Perm.sign τ := by
    rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]
  by_cases h : σ⁻¹ * τ * σ ∈ colSubgroup t
  · rw [ite_eq_left h, ite_eq_left ((mem_colSubgroup_relabel σ t).mpr h), hsign]
  · rw [ite_eq_right h, ite_eq_right fun hτ => h ((mem_colSubgroup_relabel σ t).mp hτ)]

/-- Relabeling by `σ` conjugates the Young symmetrizer by `σ`: `c_{σt} = σ c_t σ⁻¹`. -/
@[simp]
theorem youngSymmetrizer_relabel :
    youngSymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * youngSymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  have hσ : MonoidAlgebra.single σ⁻¹ (1 : ℚ) * MonoidAlgebra.single σ 1 = 1 := by
    simpa using (singleUnit σ).inv_mul
  rw [youngSymmetrizer_def, youngSymmetrizer_def, rowSymmetrizer_relabel,
    columnAntisymmetrizer_relabel]
  simp only [mul_assoc]
  rw [← mul_assoc (MonoidAlgebra.single σ⁻¹ (1 : ℚ)), hσ, one_mul]

/-- Relabeling by `σ` conjugates the transported Young symmetrizer, as it does the rational
one. -/
theorem youngSymmetrizerOver_relabel (k : Type*) [CommSemiring k] [Algebra ℚ k] :
    youngSymmetrizerOver k (relabel σ t) =
      MonoidAlgebra.single σ 1 * youngSymmetrizerOver k t * MonoidAlgebra.single σ⁻¹ 1 := by
  rw [youngSymmetrizerOver_def, youngSymmetrizerOver_def, youngSymmetrizer_relabel, map_mul,
    map_mul, MonoidAlgebra.mapAlgHom_single, MonoidAlgebra.mapAlgHom_single, map_one]

/-! ## The Young-symmetrizer left ideal of a relabeled tableau -/

/-- Membership in the left ideal generated by `c_{σt}` is membership in the right translate by
`σ⁻¹` of the left ideal generated by `c_t`. -/
theorem mem_spechtIdeal_relabel_iff {x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))} :
    x ∈ spechtIdeal (relabel σ t) ↔ x * MonoidAlgebra.single σ 1 ∈ spechtIdeal t := by
  have hσ : MonoidAlgebra.single σ⁻¹ (1 : ℚ) * MonoidAlgebra.single σ 1 = 1 := by
    simpa using (singleUnit σ).inv_mul
  have hσ' : MonoidAlgebra.single σ (1 : ℚ) * MonoidAlgebra.single σ⁻¹ 1 = 1 := by
    simpa using (singleUnit σ).mul_inv
  rw [mem_spechtIdeal_iff, mem_spechtIdeal_iff]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a * MonoidAlgebra.single σ 1, ?_⟩
    rw [youngSymmetrizer_relabel]
    simp only [mul_assoc, hσ, mul_one]
  · rintro ⟨b, hb⟩
    refine ⟨b * MonoidAlgebra.single σ⁻¹ 1, ?_⟩
    rw [youngSymmetrizer_relabel]
    simp only [mul_assoc]
    rw [← mul_assoc (MonoidAlgebra.single σ⁻¹ (1 : ℚ)), hσ, one_mul,
      ← mul_assoc, hb, mul_assoc, hσ', mul_one]

noncomputable section

/-- Right multiplication by `σ` as an equivalence of left `ℚ[Sₙ]`-modules from `ℚ[Sₙ] c_{σt}` to
`ℚ[Sₙ] c_t`: it is right multiplication by the unit `σ` of the group algebra, restricted to the
two ideals. -/
def spechtIdealRelabelEquiv :
    spechtIdeal (relabel σ t) ≃ₗ[MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))] spechtIdeal t :=
  (Units.mulRightLinearEquiv (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
      (singleUnit σ)).ofSubmodules _ _ <| by
    refine Submodule.ext fun x => ?_
    rw [Submodule.mem_map_equiv, Units.symm_mulRightLinearEquiv_apply,
      mem_spechtIdeal_relabel_iff, ← coe_singleUnit σ, Units.inv_mul_cancel_right]

@[simp]
theorem spechtIdealRelabelEquiv_apply_coe (x : spechtIdeal (relabel σ t)) :
    (spechtIdealRelabelEquiv σ t x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelEquiv, LinearEquiv.ofSubmodules_apply,
    Units.mulRightLinearEquiv_apply, coe_singleUnit]

@[simp]
theorem spechtIdealRelabelEquiv_symm_apply_coe (y : spechtIdeal t) :
    ((spechtIdealRelabelEquiv σ t).symm y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ⁻¹ 1 := by
  rw [spechtIdealRelabelEquiv, LinearEquiv.ofSubmodules_symm_apply,
    Units.symm_mulRightLinearEquiv_apply, coe_inv_singleUnit]

/-- Right multiplication by `σ` is an isomorphism of representations from `ℚ[Sₙ] c_{σt}` to
`ℚ[Sₙ] c_t`: being a map of left modules over the group algebra, it commutes with the action. -/
def spechtIdealRelabelRepEquiv :
    (spechtIdealRep (relabel σ t)).ρ.Equiv (spechtIdealRep t).ρ :=
  Representation.Equiv.mk ((spechtIdealRelabelEquiv σ t).restrictScalars ℚ) fun g =>
    -- the action of `g` is the scalar action of `single g 1`, which a map of left modules over the
    -- group algebra respects
    LinearMap.ext fun x => (spechtIdealRelabelEquiv σ t).map_smul (MonoidAlgebra.single g 1) x

@[simp]
theorem spechtIdealRelabelRepEquiv_apply_coe (x : spechtIdeal (relabel σ t)) :
    (spechtIdealRelabelRepEquiv σ t x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelRepEquiv, Representation.Equiv.mk_apply,
    LinearEquiv.restrictScalars_apply, spechtIdealRelabelEquiv_apply_coe]

/-- The left ideals of the Young symmetrizers of a tableau and of its relabelings are isomorphic
representations. -/
def spechtIdealRelabelRepIso : spechtIdealRep (relabel σ t) ≅ spechtIdealRep t :=
  Rep.mkIso (spechtIdealRelabelRepEquiv σ t)

@[simp]
theorem spechtIdealRelabelRepIso_hom_hom_apply_coe (x : spechtIdeal (relabel σ t)) :
    ((spechtIdealRelabelRepIso σ t).hom.hom x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelRepIso, Rep.mkIso_hom_hom_apply, Representation.Equiv.coe_toLinearMap,
    spechtIdealRelabelRepEquiv_apply_coe]

end

/-- Relabeling does not change the dimension of the Young-symmetrizer left ideal. -/
theorem finrank_spechtIdeal_relabel :
    Module.finrank ℚ (spechtIdeal (relabel σ t)) = Module.finrank ℚ (spechtIdeal t) :=
  ((spechtIdealRelabelEquiv σ t).restrictScalars ℚ).finrank_eq

/-- Relabeling does not change the character of the Young-symmetrizer left ideal. -/
@[simp]
theorem character_spechtIdealRep_relabel :
    (spechtIdealRep (relabel σ t)).ρ.character = (spechtIdealRep t).ρ.character :=
  Representation.char_iso (spechtIdealRelabelRepEquiv σ t)

/-- Relabeling does not change the character of the bundled Young-symmetrizer representation. -/
theorem character_spechtIdealFDRep_relabel :
    (spechtIdealFDRep (relabel σ t)).character = (spechtIdealFDRep t).character :=
  -- bundling leaves both the module and the action alone, so the two characters are the same
  -- function, as in `char_permutationModuleFDRep`
  character_spechtIdealRep_relabel σ t

/-! ## Independence of the tableau -/

variable (t' : YoungTableau μ)

/-- The Young-symmetrizer left ideals of two tableaux of the same shape are isomorphic
representations: up to isomorphism the representation depends only on the shape. -/
noncomputable def spechtIdealRepIso : spechtIdealRep t ≅ spechtIdealRep t' :=
  -- `t'` is the relabeling of `t` by `relabelPerm t t'`, and `eqToIso` transports along that
  (spechtIdealRelabelRepIso (relabelPerm t t') t).symm ≪≫
    CategoryTheory.eqToIso (congrArg spechtIdealRep (relabel_relabelPerm t t'))

/-- The dimension of the Young-symmetrizer left ideal depends only on the shape of the tableau. -/
theorem finrank_spechtIdeal_eq :
    Module.finrank ℚ (spechtIdeal t) = Module.finrank ℚ (spechtIdeal t') := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
  exact (finrank_spechtIdeal_relabel σ t).symm

/-- The character of the Young-symmetrizer left ideal depends only on the shape of the tableau. -/
theorem character_spechtIdealRep_eq :
    (spechtIdealRep t).ρ.character = (spechtIdealRep t').ρ.character := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
  exact (character_spechtIdealRep_relabel σ t).symm

/-- The character of the bundled Young-symmetrizer representation depends only on the shape of the
tableau. -/
theorem character_spechtIdealFDRep_eq :
    (spechtIdealFDRep t).character = (spechtIdealFDRep t').character :=
  character_spechtIdealRep_eq t t'

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0181

section TAF_LiteralSource_0182
/- Original module: TauCeti.RepresentationTheory.Symmetric.TableauSubgroupConjugacy -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tableau row groups and Young subgroups

The row group of a tableau depends on its labeling, whereas the Young subgroup attached to its
shape uses consecutive blocks. This file constructs the permutation sending the consecutive-block
labeling to a given tableau and proves that it conjugates the corresponding Young subgroup onto
the tableau's row group.

## References

* [G. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 3.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1.
-/

public section

namespace TauCeti

namespace YoungTableau

private abbrev rowBlocks (l : List ℕ) : Type :=
  Σ i : Fin l.length, Fin (l.get i)

private noncomputable def rowCellsEquiv (μ : YoungDiagram) :
    rowBlocks μ.rowLens ≃ ↥μ.cells where
  toFun x := ⟨(x.1, x.2), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.get_rowLens]
    exact x.2.2⟩
  invFun c :=
    ⟨⟨c.1.1, by
      rw [YoungDiagram.length_rowLens]
      exact (_root_.YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le
        (μ.colLen_anti 0 c.1.2 c.1.2.zero_le)⟩,
      ⟨c.1.2, by
        have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp c.2
        rw [← YoungDiagram.get_rowLens] at hj
        exact hj⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def sortedBlocksEquivRows (μ : YoungDiagram) :
    rowBlocks ((shapePartition μ).parts.sort (· ≥ ·)) ≃ rowBlocks μ.rowLens :=
  Equiv.cast (congrArg rowBlocks (shapePartition_parts_sort μ))

private theorem cast_rowBlocks_fst {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).1 : ℕ) = x.1 := by
  subst l₂
  rfl

private theorem cast_rowBlocks_snd {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).2 : ℕ) = x.2 := by
  subst l₂
  rfl

private theorem sortedBlocksEquivRows_fst (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).1 : ℕ) = x.1 :=
  cast_rowBlocks_fst (shapePartition_parts_sort μ) x

private theorem sortedBlocksEquivRows_snd (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).2 : ℕ) = x.2 :=
  cast_rowBlocks_snd (shapePartition_parts_sort μ) x

/-- The permutation carrying the consecutive-block labeling of a Young diagram to the labeling
of `t`. It sends each block of the shape partition to the correspondingly numbered row of `t`. -/
noncomputable def rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) :=
  (youngBlocksEquiv (shapePartition μ)).symm |>.trans <|
    (sortedBlocksEquivRows μ).trans ((rowCellsEquiv μ).trans t)

/-- The row of a label after applying `rowYoungConjugator t` is its consecutive-block number. -/
@[simp]
theorem rowIndex_rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ)
    (k : Fin μ.card) :
    rowIndex t (rowYoungConjugator t k) =
      youngBlock (shapePartition μ) k := by
  let x := (youngBlocksEquiv (shapePartition μ)).symm k
  have hk : youngBlocksEquiv (shapePartition μ) x = k :=
    Equiv.apply_symm_apply _ k
  rw [← hk, youngBlock_youngBlocksEquiv]
  simp only [rowYoungConjugator, Equiv.trans_apply, rowIndex_apply, rowCellsEquiv,
    Equiv.symm_apply_apply, x]
  exact sortedBlocksEquivRows_fst μ x

-- Not `@[simp]`: with `shapePartition_parts` and `Multiset.coe_sort` in the default simp set,
-- the left-hand side is no longer in simp normal form (the sorted parts reduce to `μ.rowLens`),
-- so the tag would be a `simpNF` violation. The lemma is for explicit `rw`/`exact` use.
/-- On consecutive-block coordinates, `rowYoungConjugator t` sends position `j` in block `i`
to the label in position `j` of row `i` of `t`. -/
theorem rowYoungConjugator_youngBlocksEquiv {μ : YoungDiagram} (t : YoungTableau μ)
    (x : Σ i : Fin
        ((shapePartition μ).parts.sort (· ≥ ·)).length,
      Fin (((shapePartition μ).parts.sort (· ≥ ·)).get i)) :
    rowYoungConjugator t
        (youngBlocksEquiv (shapePartition μ) x) =
      t ⟨(x.1, x.2), by
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
        let y := sortedBlocksEquivRows μ x
        calc
          (x.2 : ℕ) = y.2 := (sortedBlocksEquivRows_snd μ x).symm
          _ < μ.rowLens.get y.1 := y.2.2
          _ = μ.rowLen y.1 := YoungDiagram.get_rowLens
          _ = μ.rowLen x.1 := congrArg μ.rowLen (sortedBlocksEquivRows_fst μ x)⟩ := by
  simp only [rowYoungConjugator, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply congrArg t
  apply Subtype.ext
  apply Prod.ext
  · exact sortedBlocksEquivRows_fst μ x
  · exact sortedBlocksEquivRows_snd μ x

/-- Relabeling a tableau translates its conjugator on the left: the consecutive-block labeling is
carried to the relabeled tableau by first carrying it to `t` and then applying `σ`. -/
@[simp]
theorem rowYoungConjugator_relabel {μ : YoungDiagram} (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) :
    rowYoungConjugator (relabel σ t) = σ * rowYoungConjugator t := by
  have h : relabel σ t = t.trans σ := Equiv.ext fun c => relabel_apply σ t c
  simp only [rowYoungConjugator, Equiv.Perm.mul_def, Equiv.trans_assoc, h]

/-- Conjugation by `rowYoungConjugator t` carries the Young subgroup of the shape partition
onto the row group of `t`. -/
theorem youngSubgroup_map_conj_eq_rowSubgroup {μ : YoungDiagram} (t : YoungTableau μ) :
    (youngSubgroup (shapePartition μ)).map
        (MulAut.conj (rowYoungConjugator t)).toMonoidHom = rowSubgroup t := by
  rw [youngSubgroup_eq_fiberSubgroup, rowSubgroup_def]
  apply fiberSubgroup_map_conj
  intro a b
  simp only [rowIndex_rowYoungConjugator]
  exact Fin.ext_iff

/-- Conjugation by `rowYoungConjugator t` as a multiplicative equivalence from the Young
subgroup of the shape partition to the row group of `t`. -/
noncomputable def youngSubgroupConjMulEquiv {μ : YoungDiagram} (t : YoungTableau μ) :
    youngSubgroup (shapePartition μ) ≃*
      rowSubgroup t :=
  ((MulAut.conj (rowYoungConjugator t)).subgroupMap
      (youngSubgroup (shapePartition μ))).trans
    (MulEquiv.subgroupCongr (youngSubgroup_map_conj_eq_rowSubgroup t))

/-- The subgroup equivalence acts by conjugation with `rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (σ : youngSubgroup (shapePartition μ)) :
    ((youngSubgroupConjMulEquiv t σ : rowSubgroup t) : Equiv.Perm (Fin μ.card)) =
      rowYoungConjugator t * σ * (rowYoungConjugator t)⁻¹ :=
  by
    simp [youngSubgroupConjMulEquiv]
    rfl

/-- The inverse subgroup equivalence acts by conjugation with the inverse of
`rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_symm_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (τ : rowSubgroup t) :
    (((youngSubgroupConjMulEquiv t).symm τ :
        youngSubgroup (shapePartition μ)) :
      Equiv.Perm (Fin μ.card)) =
      (rowYoungConjugator t)⁻¹ * τ * rowYoungConjugator t := by
  simp [youngSubgroupConjMulEquiv]
  rfl

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0182

section TAF_LiteralSource_0183
/- Original module: TauCeti.RepresentationTheory.Symmetric.Specht.Module -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Polytabloids and the Specht module

The Young permutation module `M^μ` is the rational representation of `Sₙ` on the `μ`-tabloids,
which are the left cosets of the Young subgroup of the shape of `μ`.  A `μ`-tableau `t` names one
of them, its **tabloid** `{t}`, and antisymmetrizing that tabloid over the column group of `t`
produces the **polytabloid**

`e_t = b_t · {t} ∈ M^μ`.

The **Specht module** `S^μ` is the submodule of `M^μ` spanned by the polytabloids.  It is a
subrepresentation, because relabeling a tableau translates its polytabloid:
`e_{σt} = σ · e_t`.  Since the symmetric group acts transitively on tableaux, `S^μ` is in fact
the span of the orbit of a single polytabloid.

The conventions here are the ones the Schur-Weyl roadmap pins, and they have to be used
together: `M^μ` is a **left** module on the **left** cosets of the Young subgroup, the polytabloid
is the **column** antisymmetrization `b_t · {t}` of the tabloid, and the Young symmetrizer is
`c_t = a_t b_t`.  The opposite choices produce the dual Specht module.

The bridge between the two indexings is `rowYoungConjugator t`, the permutation carrying the
consecutive-block labeling of the shape of `μ` to the labeling of `t`: its coset is the tabloid of
`t`, and conjugation by it carries the Young subgroup onto the row group of `t`.  The tabloid of
`t` is therefore fixed exactly by the row group, which is what makes the polytabloid nonzero: the
column group meets the row group trivially, so the tabloids appearing in `e_t` are pairwise
distinct and the coefficient of `{t}` itself is `1`.

The identification of `S^μ` with the left ideal `ℚ[Sₙ] c_t` of
`TauCeti/RepresentationTheory/Symmetric/Specht/Ideal/Basic.lean` is a separate milestone and is not
proved here.  Neither is James's submodule theorem, which rests on the nonvanishing recorded below
and lives in `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean` together with
the irreducibility it yields.

## Main definitions

* `TauCeti.YoungTableau.tabloid`: the `μ`-tabloid of a tableau.
* `TauCeti.YoungTableau.polytabloid`: the polytabloid `e_t = b_t · {t}`.
* `TauCeti.spechtSubrepresentation`: the span of the polytabloids, as a subrepresentation of `M^μ`.
* `TauCeti.spechtModule`: the Specht module `S^μ` of a partition `μ` of `n`, that subrepresentation
  of the diagram of `μ` bundled as a finite-dimensional representation of `Sₙ`.

## Main results

* `TauCeti.YoungTableau.smul_tabloid_eq_self_iff`: the stabilizer of the tabloid of `t` is the row
  group of `t`.
* `TauCeti.YoungTableau.tabloid_eq_iff_rowIndex_eq`: two tableaux have the same tabloid exactly when
  they put every label in the same row.
* `TauCeti.YoungTableau.polytabloid_relabel`: relabeling translates the polytabloid.
* `TauCeti.YoungTableau.polytabloid_eq_single_of_colSubgroup_eq_bot`: with nothing to
  antisymmetrize over, the polytabloid is the bare tabloid.
* `TauCeti.YoungTableau.polytabloid_coeff_eq_zero_of_forall_ne`: only the tabloids reachable from
  `{t}` by a column permutation occur in `e_t`.
* `TauCeti.YoungTableau.polytabloid_ne_zero` and
  `TauCeti.YoungTableau.tabloidForm_polytabloid_self`: polytabloids are nonzero, and the tabloid
  form pairs one with itself to the order of the column group.
* `TauCeti.spechtSubrepresentation_eq_span_orbit` and `TauCeti.spechtSubrepresentation_ne_bot`: the
  Specht module is the span of the orbit of a single polytabloid, and it is nonzero.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapters 3 and 4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, "Polytabloids and the Specht module".
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The tabloid of a tableau -/

/-- The **tabloid** `{t}` of a `μ`-tableau `t`: the row-equivalence class of `t`, presented as the
coset of the Young subgroup of the shape of `μ` given by `rowYoungConjugator t`. -/
noncomputable def tabloid (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  QuotientGroup.mk (rowYoungConjugator t)

theorem tabloid_def (t : YoungTableau μ) :
    tabloid t = QuotientGroup.mk (rowYoungConjugator t) :=
  (rfl)

/-- Relabeling a tableau translates its tabloid. -/
@[simp]
theorem tabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    tabloid (relabel σ t) = σ • tabloid t := by
  rw [tabloid_def, tabloid_def, rowYoungConjugator_relabel, MulAction.Quotient.smul_coe,
    smul_eq_mul]

/-- Every `μ`-tabloid is the tabloid of a tableau. -/
theorem tabloid_surjective : Function.Surjective (tabloid (μ := μ)) := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨relabel (σ * (rowYoungConjugator t)⁻¹) t, ?_⟩
  rw [tabloid_def, rowYoungConjugator_relabel, inv_mul_cancel_right]

/-- **The stabilizer of a tabloid is the row group.** A permutation fixes the tabloid of `t`
exactly when it preserves the rows of `t`. -/
@[simp]
theorem smul_tabloid_eq_self_iff {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = tabloid t ↔ σ ∈ rowSubgroup t := by
  -- the stabilizer of a coset is the conjugate subgroup, and that conjugate is the row group
  have h : MulAction.stabilizer (Equiv.Perm (Fin μ.card)) (tabloid t) = rowSubgroup t := by
    rw [tabloid_def, stabilizer_quotientGroup_mk]
    exact youngSubgroup_map_conj_eq_rowSubgroup t
  rw [← h, MulAction.mem_stabilizer_iff]

/-- Two permutations send the tabloid of `t` to the same tabloid exactly when they differ by an
element of the row group of `t`. -/
@[simp]
theorem smul_tabloid_eq_iff {t : YoungTableau μ} {σ τ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = τ • tabloid t ↔ σ⁻¹ * τ ∈ rowSubgroup t := by
  rw [← smul_tabloid_eq_self_iff, mul_smul, inv_smul_eq_iff, eq_comm]

/-- **Two tableaux have the same tabloid exactly when they put every label in the same row.** -/
@[simp]
theorem tabloid_eq_iff_rowIndex_eq {t u : YoungTableau μ} :
    tabloid t = tabloid u ↔ rowIndex t = rowIndex u := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t u
  rw [tabloid_relabel, eq_comm, smul_tabloid_eq_self_iff, mem_rowSubgroup]
  constructor
  · intro hσ
    funext k
    simpa using hσ (σ⁻¹ k)
  · intro hσ k
    have hk := congrFun hσ (σ k)
    rw [rowIndex_relabel] at hk
    simpa using hk

/-- Distinct elements of the column group of `t` move the tabloid of `t` to distinct tabloids: the
column group meets the row group, which is the stabilizer, only in the identity. -/
theorem smul_tabloid_injective (t : YoungTableau μ) :
    Function.Injective fun q : colSubgroup t => (q : Equiv.Perm (Fin μ.card)) • tabloid t := by
  intro q r h
  have hrow : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t := smul_tabloid_eq_iff.mp h
  have hcol : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ colSubgroup t :=
    mul_mem (inv_mem q.2) r.2
  have hmem : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t ⊓ colSubgroup t :=
    Subgroup.mem_inf.mpr ⟨hrow, hcol⟩
  rw [rowSubgroup_inf_colSubgroup_eq_bot t, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact Subtype.ext hmem

/-! ## Polytabloids -/

attribute [local instance] YoungTableau.decidablePredMemColSubgroup

/-- The **polytabloid** `e_t = b_t · {t}`: the column antisymmetrizer of `t` acting on the tabloid
of `t` inside the Young permutation module of the shape of `μ`. -/
noncomputable def polytabloid (t : YoungTableau μ) :
    (permutationModule (shapePartition μ)).V :=
  (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
    (MonoidAlgebra.single (tabloid t) 1)

/-- The polytabloid is the column antisymmetrizer applied to the tabloid. -/
theorem polytabloid_def (t : YoungTableau μ) :
    polytabloid t =
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single (tabloid t) 1) :=
  (rfl)

/-- **A polytabloid with trivial column group is the bare tabloid.**  The column antisymmetrizer of
`t` is then `1`, so there is nothing to antisymmetrize.  A shape with at most one row is the case
of interest, by `TauCeti.YoungTableau.colSubgroup_eq_bot_of_rowSubgroup_eq_top`. -/
@[simp]
theorem polytabloid_eq_single_of_colSubgroup_eq_bot (t : YoungTableau μ)
    (h : colSubgroup t = ⊥) :
    polytabloid t = MonoidAlgebra.single (tabloid t) (1 : ℚ) := by
  rw [polytabloid_def, columnAntisymmetrizer_eq_one t h, map_one, Module.End.one_apply]

/-- The polytabloid is the signed sum of the tabloids obtained from `{t}` by the column group. -/
theorem polytabloid_eq_sum (t : YoungTableau μ) :
    polytabloid t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.single ((q : Equiv.Perm (Fin μ.card)) • tabloid t) (1 : ℚ) := by
  rw [polytabloid, columnAntisymmetrizer_def]
  simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]

/-- Relabeling a tableau translates its polytabloid: `e_{σt} = σ · e_t`. -/
@[simp]
theorem polytabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    polytabloid (relabel σ t) =
      (permutationModule (shapePartition μ)).ρ σ (polytabloid t) := by
  rw [polytabloid, polytabloid, columnAntisymmetrizer_relabel, map_mul, map_mul,
    Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one,
    tabloid_relabel]
  simp only [Module.End.mul_apply, Representation.ofMulAction_single, smul_smul,
    inv_mul_cancel, one_smul]

/-- **Relabeling by a column permutation of `t` scales the polytabloid by its sign**:
`e_{qt} = sgn(q) e_t` for `q` in the column group of `t`.  So the tableaux in one column-group
orbit all carry, up to sign, the same polytabloid.

This is not a `simp` lemma: its left-hand side is the one of
`TauCeti.YoungTableau.polytabloid_relabel`, which applies to every permutation. -/
theorem polytabloid_relabel_of_mem_colSubgroup {t : YoungTableau μ}
    {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    polytabloid (relabel q t) = ((Equiv.Perm.sign q : ℤ) : ℚ) • polytabloid t := by
  have hmul : MonoidAlgebra.single q (1 : ℚ) * columnAntisymmetrizer t =
      ((Equiv.Perm.sign q : ℤ) : ℚ) • columnAntisymmetrizer t :=
    mul_columnAntisymmetrizer_left t ⟨q, hq⟩
  rw [polytabloid_relabel, polytabloid_def, ← Representation.asAlgebraHom_single_one,
    ← Module.End.mul_apply, ← map_mul, hmul, map_smul, LinearMap.smul_apply]

/-- The coefficient, in the polytabloid `e_t`, of the tabloid obtained from `{t}` by a column
permutation `q` of `t` is the sign of `q`. -/
@[simp]
theorem polytabloid_coeff_smul_tabloid (t : YoungTableau μ) (q : colSubgroup t) :
    (polytabloid t).coeff ((q : Equiv.Perm (Fin μ.card)) • tabloid t) =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) := by
  classical
  rw [polytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single q]
  · simp [MonoidAlgebra.coeff_single]
  · intro r _ hr
    have hne : (r : Equiv.Perm (Fin μ.card)) • tabloid t ≠
        (q : Equiv.Perm (Fin μ.card)) • tabloid t := fun h =>
      hr (smul_tabloid_injective t h)
    simp [MonoidAlgebra.coeff_single, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The coefficient of the tabloid `{t}` in the polytabloid `e_t` is `1`; in particular `e_t` is a
nonzero element of `M^μ`. -/
@[simp]
theorem polytabloid_coeff_tabloid (t : YoungTableau μ) :
    (polytabloid t).coeff (tabloid t) = 1 := by
  have h := polytabloid_coeff_smul_tabloid t 1
  simpa using h

/-- Only the tabloids reachable from `{t}` by a column permutation occur in the polytabloid
`e_t`. -/
theorem polytabloid_coeff_eq_zero_of_forall_ne (t : YoungTableau μ)
    {X : Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)}
    (h : ∀ q ∈ colSubgroup t, q • tabloid t ≠ X) : (polytabloid t).coeff X = 0 := by
  classical
  rw [polytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hne := h (q : Equiv.Perm (Fin μ.card)) q.2
  simp [MonoidAlgebra.coeff_single, hne]

/-- Polytabloids are nonzero. -/
@[simp]
theorem polytabloid_ne_zero (t : YoungTableau μ) : polytabloid t ≠ 0 := by
  intro h
  have := polytabloid_coeff_tabloid t
  rw [h] at this
  simp at this

/-- **The tabloid form evaluates a polytabloid against itself to the order of the column group.**
This nonvanishing is the input that James's submodule theorem converts into irreducibility of the
Specht module. -/
theorem tabloidForm_polytabloid_self (t : YoungTableau μ) :
    tabloidForm (shapePartition μ) (polytabloid t) (polytabloid t) =
      (Nat.card (colSubgroup t) : ℚ) := by
  classical
  nth_rewrite 1 [polytabloid_eq_sum]
  rw [map_sum, LinearMap.sum_apply]
  have hterm : ∀ q : colSubgroup t,
      tabloidForm (shapePartition μ)
          (((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
            MonoidAlgebra.single ((q : Equiv.Perm (Fin μ.card)) • tabloid t) (1 : ℚ))
          (polytabloid t) = 1 := by
    intro q
    rw [map_smul, LinearMap.smul_apply, tabloidForm, permutationForm_single_left,
      polytabloid_coeff_smul_tabloid]
    rw [smul_eq_mul, one_mul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]

end YoungTableau

/-! ## The Specht module -/

open YoungTableau

/-- The **Specht module** `S^μ`, in its concrete presentation: the subrepresentation of the Young
permutation module `M^μ` spanned by the polytabloids of the `μ`-tableaux.

It is stable under the symmetric group because relabeling a tableau translates its polytabloid,
and the polytabloids of the relabelings of a fixed tableau are all of them. -/
noncomputable def spechtSubrepresentation (μ : YoungDiagram) :
    Subrepresentation (permutationModule (shapePartition μ)).ρ where
  toSubmodule := Submodule.span ℚ (Set.range (polytabloid (μ := μ)))
  apply_mem_toSubmodule σ _ hv := by
    -- stability of a span is checked on its generators
    have h : Submodule.span ℚ (Set.range (polytabloid (μ := μ))) ≤
        (Submodule.span ℚ (Set.range (polytabloid (μ := μ)))).comap
          ((permutationModule (shapePartition μ)).ρ σ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact Submodule.subset_span ⟨relabel σ t, polytabloid_relabel σ t⟩
    exact h hv

/-- The underlying submodule of the Specht module is the span of the polytabloids. -/
@[simp]
theorem spechtSubrepresentation_toSubmodule (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ (Set.range (polytabloid (μ := μ))) :=
  (rfl)

/-- Every polytabloid lies in the Specht module. -/
theorem polytabloid_mem_spechtSubrepresentation (t : YoungTableau μ) :
    polytabloid t ∈ spechtSubrepresentation μ :=
  Submodule.subset_span ⟨t, rfl⟩

/-- **The Specht module is cyclic.** It is the span of the orbit of a single polytabloid, because
the symmetric group permutes the `μ`-tableaux transitively. -/
theorem spechtSubrepresentation_eq_span_orbit (t : YoungTableau μ) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ
        (Set.range fun σ : Equiv.Perm (Fin μ.card) =>
          (permutationModule (shapePartition μ)).ρ σ (polytabloid t)) := by
  rw [spechtSubrepresentation_toSubmodule]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t', rfl⟩
    obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
    exact ⟨σ, (polytabloid_relabel σ t).symm⟩
  · rintro _ ⟨σ, rfl⟩
    exact ⟨relabel σ t, polytabloid_relabel σ t⟩

/-- The Specht module is nonzero. -/
@[simp]
theorem spechtSubrepresentation_ne_bot (μ : YoungDiagram) : spechtSubrepresentation μ ≠ ⊥ := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro h
  have hmem : polytabloid t ∈ (⊥ : Subrepresentation (permutationModule (shapePartition μ)).ρ) :=
    h ▸ polytabloid_mem_spechtSubrepresentation t
  exact polytabloid_ne_zero t (Submodule.mem_bot ℚ |>.mp hmem)

/-- The Specht module is finite-dimensional, being a submodule of the finite-dimensional Young
permutation module.  This is what lets it be bundled as an `FDRep`. -/
instance (μ : YoungDiagram) :
    FiniteDimensional ℚ (spechtSubrepresentation μ).toSubmodule :=
  FiniteDimensional.finiteDimensional_submodule _

/-- The **Specht module** `S^μ` of a partition `μ` of `n`, bundled as a finite-dimensional
representation of `Sₙ`: the span of the polytabloids of the tableaux of the Young diagram
`YoungDiagram.ofPartition μ`, with the symmetric group on the `(YoungDiagram.ofPartition μ).card`
entries of such a tableau identified with `Sₙ` along `YoungDiagram.card_ofPartition`.

The tabloid combinatorics is indexed by a diagram, since a tableau is a filling of one, while the
classification the Specht modules feed is indexed by partitions; this is the partition-indexed
name.  Its representation unfolds to `spechtSubrepresentation (YoungDiagram.ofPartition μ)` by
`FDRep.of_ρ'`, and `spechtSubrepresentation_toSubmodule` identifies the underlying module with the
span of the polytabloids. -/
noncomputable abbrev spechtModule {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of ((spechtSubrepresentation (YoungDiagram.ofPartition μ)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongrHom.toMonoidHom)

/-- The Specht module is nontrivial, so it has positive dimension. -/
theorem finrank_spechtModule_pos {n : ℕ} (μ : n.Partition) :
    0 < Module.finrank ℚ (spechtModule μ) :=
  have : Nontrivial (spechtSubrepresentation (YoungDiagram.ofPartition μ)).toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr fun h =>
      spechtSubrepresentation_ne_bot _ (Subrepresentation.toSubmodule_injective h)
  Module.finrank_pos

end TauCeti
end
end TAF_LiteralSource_0183

section TAF_LiteralSource_0184
/- Original module: TauCeti.RepresentationTheory.Symmetric.Specht.Garnir -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Garnir relations

The polytabloids `e_t` of the `μ`-tableaux span the Specht module `S^μ`, and the standard basis
theorem says that the polytabloids of the *standard* tableaux already do.  The relations that the
straightening algorithm rewrites an arbitrary polytabloid with are the **Garnir relations**, and
this file proves them.

Write `A_X` for the signed sum `∑ sgn(σ) σ` over the permutations `σ` fixing every label outside a
finite set `X` (`TauCeti.antisymmetrizerOn`, defined with the other signed sums in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`).  The Garnir relation is

`A_X · e_t = 0`

whenever `X` is too large to be spread over the rows available to it: all the labels of `X` lie in
columns of `μ` of length at most `r`, and `X` has more than `r` elements
(`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`).  Applied to the
polytabloid it reads as the vanishing of a signed sum of the polytabloids `e_{σt}`
(`TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero`).

Two facts drive the proof.

* **A signed sum kills whatever an odd permutation in it fixes.**  Absorbing an odd permutation
  supported in `X` turns `A_X` into its own negative, so `A_X` annihilates every vector that
  permutation fixes (`TauCeti.asAlgebraHom_antisymmetrizerOn_apply_eq_zero`).
* **Pigeonhole in the columns.**  A column permutation `q` of `t` moves a label only within its own
  column, so in the tabloid `q · {t}` the labels of `X` still lie in columns of length at most `r`,
  that is, in `r` rows.  As `X` has more than `r` elements, two of them share a row of `q · {t}`,
  and the transposition swapping those two fixes that tabloid.  Every tabloid occurring in `e_t` is
  of this form, so `A_X` kills them all.

The sets `X` the relation is applied to are the **Garnir sets** `TauCeti.YoungTableau.garnirSet t i
j`: the labels of `t` in column `j` from row `i` downwards together with those in column `j + 1`
from row `i` upwards.  As soon as `(i, j + 1)` is a cell of `μ` there are `μ.colLen j + 1` of them
(`TauCeti.YoungTableau.card_garnirSet`) while they occupy only the `μ.colLen j` rows of column `j`,
so the relation applies
(`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero`).
Those are the sets the straightening algorithm uses at a cell `(i, j)` where the rows of the
tableau fail to increase.  Their two halves are described here as well:
`TauCeti.YoungTableau.garnirSetLeft` names the column-`j` half, and a permutation supported in the
set preserves the columns of `t` exactly when it maps that half onto itself
(`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`), which is the classical
description of the permutations internal to the halves as a product of two symmetric groups.

The straightening step itself is *not* proved here, and the relation as stated does not supply it.
The permutations `σ` supported in `X` that lie in the column group of `t` satisfy
`e_{σt} = sgn(σ) e_t`, so their terms in the signed sum are further copies of `e_t` rather than of
anything nearer to standard; simply isolating the identity term of the sum therefore rewrites `e_t`
in terms of itself.  The classical Garnir *element* avoids this by summing only over a transversal
of the permutations internal to the two halves of the set, so that `A_X` factors as the signed sum
over those internal permutations times the Garnir element, and the identity coset contributes `e_t`
alone.  That repackaging is left to the file that performs the straightening induction; here the
relation is proved, and stated, for the whole of `A_X`.

## Main definitions

* `TauCeti.YoungTableau.garnirSet`: the Garnir set of a tableau at a row and a column.
* `TauCeti.YoungTableau.garnirSetLeft`: its column-`j` half.

## Main results

* `TauCeti.YoungTableau.exists_ne_rowIndex_relabel_eq`: the pigeonhole step, two labels of an
  oversized set share a row after any column permutation.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`: **the Garnir
  relation**.
* `TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero`: the relation as the
  vanishing of a signed sum of polytabloids.
* `TauCeti.YoungTableau.card_garnirSet`: a Garnir set has one more element than the column it
  straddles has cells.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero`: the Garnir
  relation at a Garnir set.
* `TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`: the permutations of a Garnir
  set internal to its halves are those preserving its left half.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Section 7.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose standard basis of the Specht module these relations straighten towards.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The Garnir relation -/

/-- **Pigeonhole in the columns.**  Suppose every label of `X` lies in a column of `μ` with at most
`r` cells, and `X` has more than `r` elements.  Then a column permutation `q` of `t` leaves two
distinct labels of `X` in a common row of `qt`: it moves each of them only inside its own column,
so all of them still lie in the top `r` rows. -/
theorem exists_ne_rowIndex_relabel_eq (t : YoungTableau μ) {X : Finset (Fin μ.card)} {r : ℕ}
    (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r) (hcard : r < X.card)
    {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ rowIndex (relabel q t) x = rowIndex (relabel q t) y := by
  have hmaps : ∀ k ∈ X, rowIndex (relabel q t) k ∈ Finset.range r := by
    intro k hk
    have hcol : colIndex t (q⁻¹ k) = colIndex t k := mem_colSubgroup.mp (inv_mem hq) k
    have hmem : (rowIndex t (q⁻¹ k), colIndex t (q⁻¹ k)) ∈ μ := rowIndex_colIndex_mem t (q⁻¹ k)
    have hlt : rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) :=
      YoungDiagram.mem_iff_lt_colLen.mp hmem
    rw [Finset.mem_range, rowIndex_relabel]
    calc rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) := hlt
      _ = μ.colLen (colIndex t k) := by rw [hcol]
      _ ≤ r := hX k hk
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hcard) hmaps

/-- The antisymmetrizer of `X` annihilates every tabloid reachable from `{t}` by a column
permutation of `t`, because two labels of `X` share a row of that tabloid. -/
private theorem asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (MonoidAlgebra.single (q • tabloid t) (1 : ℚ)) = 0 := by
  obtain ⟨x, hx, y, hy, hxy, hrow⟩ := exists_ne_rowIndex_relabel_eq t hX hcard hq
  refine asAlgebraHom_antisymmetrizerOn_apply_eq_zero _
    (fun k hk => Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hx)) fun h => hk (h ▸ hy))
    (Equiv.Perm.sign_swap hxy) ?_
  rw [Representation.ofMulAction_single, ← tabloid_relabel]
  exact congrArg (MonoidAlgebra.single · (1 : ℚ))
    (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow))

/-- **The Garnir relation.**  If every label of the finite set `X` lies in a column of `μ` with at
most `r` cells and `X` has more than `r` elements, then the antisymmetrizer of `X` annihilates the
polytabloid of `t`.

The labels of `X` cannot be spread over the rows of those columns, so every tabloid occurring in
`e_t` has two of them in a common row and is killed by the signed sum. -/
theorem asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (polytabloid t) = 0 := by
  rw [polytabloid_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero t hX hcard q.2,
    smul_zero]

/-- **The Garnir relation, as a signed sum of polytabloids.**  Under the hypotheses of
`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`, the signed sum of the
polytabloids of the relabelings `σt`, over the permutations `σ` supported in `X`, vanishes. -/
theorem sum_sign_smul_polytabloid_relabel_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card)
    [DecidablePred fun σ : Equiv.Perm (Fin μ.card) => ∀ k ∉ X, σ k = k] :
    ∑ σ ∈ {σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k},
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = 0 := by
  rw [← asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t hX hcard,
    asAlgebraHom_antisymmetrizerOn_apply]
  simp only [polytabloid_relabel]

/-! ## Garnir sets -/

/-- The **Garnir set** of a tableau `t` at row `i` and column `j`: the labels of `t` lying in
column `j` from row `i` downwards, together with those lying in column `j + 1` from row `i`
upwards.

When `(i, j + 1)` is a cell of `μ` this set has one element more than column `j` has cells, while
its labels stay in column `j` or `j + 1` under a column permutation of `t`; that is what makes the
Garnir relation apply to it. -/
def garnirSet (t : YoungTableau μ) (i j : ℕ) : Finset (Fin μ.card) :=
  {k | (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i)}

@[simp]
theorem mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card} :
    k ∈ garnirSet t i j ↔
      (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i) := by
  simp [garnirSet]

/-- Every label of a Garnir set at column `j` lies in a column with at most as many cells as column
`j` has, since columns of a Young diagram shorten to the right. -/
theorem colLen_colIndex_le_colLen_of_mem_garnirSet {t : YoungTableau μ} {i j : ℕ}
    {k : Fin μ.card} (hk : k ∈ garnirSet t i j) : μ.colLen (colIndex t k) ≤ μ.colLen j := by
  rcases mem_garnirSet.mp hk with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · rw [hcol]
  · rw [hcol]
    exact μ.colLen_anti j (j + 1) (Nat.le_succ j)

/-- The cells occupied by a Garnir set: those of column `j` from row `i` down, and those of column
`j + 1` from row `i` up. -/
private theorem image_rowIndex_colIndex_garnirSet (t : YoungTableau μ) (i j : ℕ) :
    (garnirSet t i j).image (fun k => (rowIndex t k, colIndex t k)) =
      {c ∈ μ.cells | (c.2 = j ∧ i ≤ c.1) ∨ (c.2 = j + 1 ∧ c.1 ≤ i)} := by
  ext c
  simp only [Finset.mem_image, mem_garnirSet, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨rowIndex_colIndex_mem t k, hk⟩
  · rintro ⟨hmem, hc⟩
    refine ⟨t ⟨c, hmem⟩, ?_, ?_⟩ <;> simp [hc]

/-- The cells of column `j` from row `i` down are those of the whole column that the first `i`
rows leave over. -/
private theorem card_filter_cells_col (i j : ℕ) :
    {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1}.card = μ.colLen j - i := by
  have htop : {c ∈ μ.col j | c.1 < i} = {c ∈ {c ∈ μ.cells | c.1 < i} | c.2 = j} := by
    simp [YoungDiagram.col, Finset.filter_filter, and_comm]
  have hbot : {c ∈ μ.col j | ¬ c.1 < i} = {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} := by
    simp [YoungDiagram.col, Finset.filter_filter]
  have hsplit := Finset.card_filter_add_card_filter_not (s := μ.col j)
    (p := fun c : ℕ × ℕ => c.1 < i)
  rw [htop, hbot, YoungDiagram.card_filter_fst_lt_filter_snd_eq, ← μ.colLen_eq_card] at hsplit
  omega

/-- The cells of column `j + 1` from row `i` up are those of that column in the first `i + 1`
rows, and `(i, j + 1) ∈ μ` says the column reaches that far. -/
private theorem card_filter_cells_col_succ {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i}.card = i + 1 := by
  have hlt : i < μ.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp h
  -- the counting lemma filters the first `i + 1` rows before the column, so its nested filter
  -- has to be flattened into the single filter of the statement
  have hflat : {c ∈ {c ∈ μ.cells | c.1 < i + 1} | c.2 = j + 1} =
      {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    simp [Finset.filter_filter, and_comm]
  have hcard := YoungDiagram.card_filter_fst_lt_filter_snd_eq μ (i + 1) (j + 1)
  rw [hflat] at hcard
  omega

/-- **A Garnir set is one bigger than the column it straddles.**  Column `j` contributes its cells
from row `i` down and column `j + 1` its cells from row `i` up, and `(i, j + 1) ∈ μ` makes both
counts available. -/
theorem card_garnirSet (t : YoungTableau μ) {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    (garnirSet t i j).card = μ.colLen j + 1 := by
  classical
  have hij : (i, j) ∈ μ := μ.up_left_mem (le_refl i) (Nat.le_succ j) h
  have hi : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
  have hinj : Function.Injective fun k : Fin μ.card => (rowIndex t k, colIndex t k) :=
    rowIndex_colIndex_injective t
  have hcard := Finset.card_image_of_injective (garnirSet t i j) hinj
  rw [image_rowIndex_colIndex_garnirSet] at hcard
  have hdisj :
      Disjoint {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    rw [Finset.disjoint_left]
    rintro c h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    omega
  rw [← hcard, Finset.filter_or, Finset.card_union_of_disjoint hdisj, card_filter_cells_col,
    card_filter_cells_col_succ h]
  omega

/-- **The Garnir relation at a Garnir set.**  If `(i, j + 1)` is a cell of `μ`, the antisymmetrizer
of the Garnir set of `t` at `(i, j)` annihilates the polytabloid of `t`. -/
theorem asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero (t : YoungTableau μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn (garnirSet t i j))
        (polytabloid t) = 0 :=
  asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t
    (fun _ hk => colLen_colIndex_le_colLen_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

/-! ## The left half of a Garnir set -/

/-- A permutation fixing everything outside `X` maps `X` to itself: were `σ k` outside `X` for
some `k` of `X`, it would be fixed, forcing `σ k = k`. -/
private theorem apply_mem_of_forall_notMem {α : Type*} {X : Finset α} {σ : Equiv.Perm α}
    (hσ : ∀ k ∉ X, σ k = k) {k : α} (hk : k ∈ X) : σ k ∈ X := by
  by_contra h
  have h' : σ k = k := σ.injective (hσ (σ k) h)
  rw [h'] at h
  exact h hk

/-- The **left half of a Garnir set**: the labels of `t` lying in column `j` from row `i`
downwards.  The Garnir set of `t` at `(i, j)` is this set together with the labels in column
`j + 1` from row `i` upwards, and the permutations of the Garnir set that preserve the columns of
`t` are exactly those preserving this half
(`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`). -/
def garnirSetLeft (t : YoungTableau μ) (i j : ℕ) : Finset (Fin μ.card) :=
  {k | colIndex t k = j ∧ i ≤ rowIndex t k}

@[simp]
theorem mem_garnirSetLeft {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card} :
    k ∈ garnirSetLeft t i j ↔ colIndex t k = j ∧ i ≤ rowIndex t k := by
  simp [garnirSetLeft]

/-- The left half of a Garnir set is part of it, being the first of the two cases of its
definition. -/
theorem garnirSetLeft_subset_garnirSet (t : YoungTableau μ) (i j : ℕ) :
    garnirSetLeft t i j ⊆ garnirSet t i j := fun _ hk =>
  mem_garnirSet.mpr (Or.inl (mem_garnirSetLeft.mp hk))

/-- A label of a Garnir set outside its left half lies in column `j + 1`, the two halves being the
two cases of the definition of the Garnir set. -/
theorem colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft {t : YoungTableau μ} {i j : ℕ}
    {k : Fin μ.card} (hk : k ∈ garnirSet t i j) (hk' : k ∉ garnirSetLeft t i j) :
    colIndex t k = j + 1 := by
  rcases mem_garnirSet.mp hk with h | h
  · exact absurd (mem_garnirSetLeft.mpr h) hk'
  · exact h.1

/-- **The internal permutations of a Garnir set are those preserving its left half.**  A
permutation supported in the Garnir set of `t` at `(i, j)` preserves the columns of `t` exactly
when it maps the column-`j` half of that set onto itself; it then automatically preserves the
column-`(j + 1)` half as well, so the internal permutations are the product of the two symmetric
groups on the halves. -/
theorem mem_colSubgroup_iff_image_garnirSetLeft_eq {t : YoungTableau μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin μ.card)} (hσ : ∀ k ∉ garnirSet t i j, σ k = k) :
    σ ∈ colSubgroup t ↔ (garnirSetLeft t i j).image σ = garnirSetLeft t i j := by
  constructor
  · intro hcol
    refine Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hmem : σ l ∈ garnirSet t i j :=
      apply_mem_of_forall_notMem hσ (garnirSetLeft_subset_garnirSet t i j hl)
    have hcolσ : colIndex t (σ l) = j := by
      rw [mem_colSubgroup.mp hcol l]
      exact (mem_garnirSetLeft.mp hl).1
    rcases mem_garnirSet.mp hmem with ⟨-, hrow⟩ | ⟨hc, -⟩
    · exact mem_garnirSetLeft.mpr ⟨hcolσ, hrow⟩
    · exact absurd hc (by omega)
  · intro himg
    rw [mem_colSubgroup]
    intro k
    by_cases hk : k ∈ garnirSet t i j
    · by_cases hkl : k ∈ garnirSetLeft t i j
      · have hmem : σ k ∈ garnirSetLeft t i j := himg ▸ Finset.mem_image_of_mem σ hkl
        rw [(mem_garnirSetLeft.mp hmem).1, (mem_garnirSetLeft.mp hkl).1]
      · have hnot : σ k ∉ garnirSetLeft t i j := by
          intro h
          rw [← himg] at h
          obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp h
          exact hkl (σ.injective hlk ▸ hl)
        rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft
            (apply_mem_of_forall_notMem hσ hk) hnot,
          colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk hkl]
    · rw [hσ k hk]

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0184

section TAF_LiteralSource_0185
/- Original module: TauCeti.Algebra.BigOperators.Finset.Swap -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Summing a product after transposing two indices

`TauCeti.sum_mul_swap` compares `∑ k ∈ s, f k * g (Equiv.swap x y k)` with `∑ k ∈ s, f k * g k`:
away from `x` and `y` the two sums agree termwise, so they differ only in that the terms
`f x * g x` and `f y * g y` are replaced by `f x * g y` and `f y * g x`. The comparison is stated
by adding the two exchanged pairs to the two sides rather than by subtracting them, so that it
holds in a monoid without subtraction -- in particular over `ℕ`, where such a weighted sum is a
convenient numerical measure of an arrangement of labels.
-/

public section

namespace TauCeti

/-- **Transposing two indices of a weighted sum exchanges the two weights.** Every term other than
those at `x` and `y` is unchanged, so adding `f x * g x + f y * g y` to the transposed sum gives
the original sum with `f x * g y + f y * g x` added. -/
theorem sum_mul_swap {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] [Mul M] (f g : ι → M)
    {s : Finset ι} {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (∑ k ∈ s, f k * g (Equiv.swap x y k)) + (f x * g x + f y * g y) =
      (∑ k ∈ s, f k * g k) + (f x * g y + f y * g x) := by
  have hsplit : ∀ F : ι → M, ∑ k ∈ s, F k = F x + (F y + ∑ k ∈ (s.erase x).erase y, F k) := by
    intro F
    rw [← Finset.add_sum_erase _ F hx,
      ← Finset.add_sum_erase _ F (Finset.mem_erase.mpr ⟨hne.symm, hy⟩)]
  have htail : ∀ k ∈ (s.erase x).erase y, f k * g (Equiv.swap x y k) = f k * g k := by
    intro k hk
    obtain ⟨hky, hk'⟩ := Finset.mem_erase.mp hk
    rw [Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp hk').1 hky]
  rw [hsplit fun k => f k * g (Equiv.swap x y k), hsplit fun k => f k * g k,
    Finset.sum_congr rfl htail, Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

end TauCeti
end
end TAF_LiteralSource_0185

section TAF_LiteralSource_0186
/- Original module: TauCeti.Algebra.Order.BigOperators.Sum.LtSum -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Comparing two sums when one index set dominates the other

Two finite sets of the same size, one of which carries a strictly larger weight at every point
than the other, have strictly ordered sums (`TauCeti.sum_lt_sum_of_forall_lt`): the sizes agreeing
is what makes the comparison work without any pointwise pairing of the two sets, since any
bijection between them compares the weights termwise.

`TauCeti.sum_lt_sum_image_sdiff` is the form in which the comparison is used. A permutation `σ`
of a finite set `X` that does not map a part `A` of it to itself must move some point of `A` out
of `A`; if `A` carries the larger weights, the image of the complementary part `X \ A` therefore
weighs strictly more than `X \ A` itself. The two sums involved differ only on the points that
`σ` moves in or out of `X \ A`, and those are compared by the previous lemma.

The weights take values in an additive commutative monoid preordered so that addition is strictly
monotone, which is what compares two sums of the same length termwise, and what turns the
comparison of the parts on which the two sums differ into a comparison of the sums themselves.
-/

public section

namespace TauCeti

variable {α M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftStrictMono M]

/-- **A set whose weights are all smaller than those of a second set of the same size has the
smaller sum.** The two sets have the same size, so some bijection matches them up, and along it
every weight of the first set is smaller than the weight of its partner. -/
theorem sum_lt_sum_of_forall_lt (f : α → M) {U V : Finset α}
    (hcard : V.card = U.card) (hU : U.Nonempty) (hlt : ∀ u ∈ U, ∀ v ∈ V, f v < f u) :
    ∑ v ∈ V, f v < ∑ u ∈ U, f u := by
  classical
  induction hU using Finset.Nonempty.cons_induction generalizing V with
  | singleton u =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by simpa using hcard)
    simpa using hlt u (by simp) v (by simp)
  | cons u U hu _ ih =>
    -- pair `u` off against any label of `V`, and compare the two remaining sums
    obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by simp [hcard])
    have hcard' : (V.erase v).card = U.card := by
      rw [Finset.card_erase_of_mem hv, hcard, Finset.card_cons]
      simp
    calc ∑ z ∈ V, f z
        = f v + ∑ z ∈ V.erase v, f z := (Finset.add_sum_erase _ f hv).symm
      _ < f u + ∑ z ∈ U, f z :=
          add_lt_add (hlt u (Finset.mem_cons_self _ _) v hv)
            (ih hcard' fun a ha b hb =>
              hlt a (Finset.mem_cons_of_mem ha) b (Finset.mem_of_mem_erase hb))
      _ = ∑ z ∈ Finset.cons u U hu, f z := (Finset.sum_cons _).symm

/-- **A permutation of a set that does not preserve a prescribed part increases the sum over the
other part.** If every weight of `A` exceeds every weight of `X \ A`, and `σ` permutes `X` without
mapping `A` to itself, then `σ` moves some point of `A` into the image of `X \ A`, exchanging a
point for one of strictly larger weight, so that image has the larger sum. -/
theorem sum_lt_sum_image_sdiff [DecidableEq α] (f : α → M) {X A : Finset α}
    {σ : Equiv.Perm α} (hAX : A ⊆ X) (hXimg : X.image σ = X) (himg : A.image σ ≠ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ X \ A, f b < f a) :
    ∑ z ∈ X \ A, f z < ∑ z ∈ (X \ A).image σ, f z := by
  classical
  have hmemX : ∀ k ∈ X, σ k ∈ X := fun k hk => hXimg ▸ Finset.mem_image_of_mem σ hk
  have hXA : X \ (X \ A) = A := Finset.sdiff_sdiff_eq_self hAX
  have hcard : ((X \ A).image σ).card = (X \ A).card :=
    Finset.card_image_of_injective _ σ.injective
  have hBsub : (X \ A).image σ ⊆ X := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hmemX k (Finset.sdiff_subset hk)
  -- the image of the second part is not the second part again, since `A` is not preserved
  have hne : (X \ A).image σ ≠ X \ A := by
    intro heq
    refine himg (Finset.eq_of_subset_of_card_le (fun z hz => ?_)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm))
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hnot : σ k ∉ X \ A := by
      intro hcontra
      have himg' : σ k ∈ (X \ A).image σ := heq.symm ▸ hcontra
      obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp himg'
      exact (Finset.mem_sdiff.mp hk').2 (σ.injective hk'eq ▸ hk)
    have hmem := Finset.mem_sdiff.mpr ⟨hmemX k (hAX hk), hnot⟩
    rwa [hXA] at hmem
  -- so the two differ, and what the image gains lies in `A`, above everything it loses
  have hUV := Finset.card_sdiff_comm hcard
  have hUne : (((X \ A).image σ) \ (X \ A)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  have hUlt : ∀ u ∈ ((X \ A).image σ) \ (X \ A), ∀ v ∈ (X \ A) \ ((X \ A).image σ), f v < f u := by
    intro u hu v hv
    obtain ⟨huX, huB⟩ := Finset.mem_sdiff.mp hu
    refine hlt u ?_ v (Finset.mem_sdiff.mp hv).1
    have hmem := Finset.mem_sdiff.mpr ⟨hBsub huX, huB⟩
    rwa [hXA] at hmem
  have hlt' := sum_lt_sum_of_forall_lt f hUV.symm hUne hUlt
  -- the two sums agree on the common part, so the two differences compare them
  have h1 := Finset.sum_sdiff (s₁ := (X \ A) ∩ ((X \ A).image σ))
    (s₂ := X \ A) (f := f) Finset.inter_subset_left
  rw [Finset.sdiff_inter_self_left] at h1
  have h2 := Finset.sum_sdiff (s₁ := ((X \ A).image σ) ∩ (X \ A))
    (s₂ := (X \ A).image σ) (f := f) Finset.inter_subset_left
  rw [Finset.sdiff_inter_self_left, Finset.inter_comm] at h2
  calc ∑ z ∈ X \ A, f z
      = (∑ z ∈ (X \ A) \ ((X \ A).image σ), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := h1.symm
    _ < (∑ z ∈ ((X \ A).image σ) \ (X \ A), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := by gcongr
    _ = ∑ z ∈ (X \ A).image σ, f z := h2

end TauCeti
end
end TAF_LiteralSource_0186

section TAF_LiteralSource_0187
/- Original module: TauCeti.RepresentationTheory.Symmetric.Specht.Straightening -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Garnir element and the straightening algorithm

The Garnir relation of `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean` says that the
signed sum

`∑_{σ} sgn(σ) e_{σt} = 0`

over the permutations `σ` supported in a set `X` whose labels cannot be spread over the rows
available to them vanishes.  As it stands the relation does not rewrite `e_t`: the permutations
that lie in the column group of `t` contribute further copies of `e_t` rather than of anything
else, so isolating the identity term rewrites `e_t` in terms of itself.  This file performs the
repackaging that Garnir's file leaves open -- **`e_t` is a rational combination of the polytabloids
`e_{σt}` of those `σ` that do not preserve the columns of `t`** -- and runs the resulting
straightening step to exhaustion: **every polytabloid is a rational combination of the
polytabloids of the standard tableaux of the same shape**, which is what makes the standard
polytabloids span the Specht module.

## Splitting the relation

The whole content is that the terms of the relation indexed by the column group of `t` are all
equal to `e_t` on the nose.  A column permutation `q` scales the polytabloid by its sign
(`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`), so its term
`sgn(q) e_{qt} = sgn(q)² e_t` is `e_t`.  Splitting the sum accordingly gives

`N · e_t + ∑_{σ ∉ colSubgroup t} sgn(σ) e_{σt} = 0`,

where `N` counts the permutations supported in `X` that preserve the columns of `t`; `N` is
positive because the identity is one of them, so `e_t` is `-1/N` times the second sum.  This is the
classical passage from the antisymmetrizer of `X` to the *Garnir element*, a signed sum over a
transversal of the internal permutations, written here without choosing a transversal: the terms
are constant on the cosets, so counting them suffices.

## Which permutations are internal

For the Garnir set `X` of `t` at a cell `(i, j)` -- the labels of `t` in column `j` from row `i`
down together with those in column `j + 1` from row `i` up -- the internal permutations are
exactly the ones preserving the column-`j` half `TauCeti.YoungTableau.garnirSetLeft`, by
`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq` of Garnir's file.  The
straightening step therefore rewrites `e_t` in terms of the polytabloids of the tableaux obtained
by genuinely exchanging labels between the two columns, which is what makes it progress towards a
standard tableau.

## The straightening algorithm

The straightening step is the second of two moves that rewrite an arbitrary polytabloid into
standard ones.  If two labels of one column of `t` are out of order, exchanging them is a
permutation of the column group of `t`, so it changes the polytabloid only by its sign
(`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`).  If instead the columns of `t`
increase but two labels of one row are out of order, then two labels in *adjacent* columns of one
row are, and the straightening step at that cell writes `e_t` in terms of the polytabloids of the
relabelings by the permutations of the Garnir set that move a label between the two columns it
straddles.

Both moves increase a numerical measure of the tableau that is bounded above, so the rewriting
terminates.  The measure is built from the two moments `∑_k c_k · k` and `∑_k r_k · k`, weighting
each label by the index of its column, respectively of its row.  The first move fixes every label
in its column and raises the row moment, since it moves the smaller of the two labels up.  The
second move raises the column moment: because the columns of `t` increase and its row does not at
the chosen cell, every label of the Garnir set lying in the earlier column exceeds every label of
it lying in the later one, so a permutation of the set that does not preserve the columns
exchanges labels of the earlier column for strictly smaller ones.  Weighting the column moment
heavily enough that a gain in it outweighs any loss of row moment combines the two into one
measure.

A tableau on which neither move applies increases down its columns and along its rows, so it is
standard (`TauCeti.exists_standardYoungTableau_toTableau_eq_iff`).

## Main results

* `TauCeti.YoungTableau.card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero`: the
  Garnir relation with its column-group terms collected, **the Garnir element relation**.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel`: `e_t` lies in the span of the
  polytabloids of the relabelings of `t` by permutations supported in `X` that leave the column
  group.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel_garnirSet`: **the
  straightening step**, the previous two combined at a Garnir set.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_standard`: **the straightening
  algorithm**, every polytabloid is a rational combination of the standard ones.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Sections 7 and 8.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Sections 2.5 and 2.6.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

attribute [local instance] YoungTableau.decidablePredMemColSubgroup

/-! ## Collecting the column-group terms of a Garnir relation -/

/-- **The Garnir element relation.**  Under the hypotheses of the Garnir relation
`TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero` -- every label of `X` lying in a
column of `μ` with at most `r` cells, and `X` having more than `r` elements -- the permutations
supported in `X` that preserve the columns of `t` contribute one copy of `e_t` each, so the
relation reads as a multiple of `e_t` cancelling against the remaining terms.

This is the form the straightening algorithm uses: the multiplicity `N` of `e_t` is the number of
internal permutations, and it is positive, the identity being one of them. -/
theorem card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card)
    [DecidablePred fun σ : Equiv.Perm (Fin μ.card) => ∀ k ∉ X, σ k = k] :
    ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
        Finset (Equiv.Perm (Fin μ.card))).card • polytabloid t +
      ∑ σ ∈ ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∉ colSubgroup t} :
          Finset (Equiv.Perm (Fin μ.card))),
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = 0 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ({σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm (Fin μ.card)))
    (fun σ => σ ∈ colSubgroup t)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t))
  rw [sum_sign_smul_polytabloid_relabel_eq_zero t hX hcard, Finset.filter_filter,
    Finset.filter_filter] at hsplit
  -- an internal permutation scales `e_t` by its sign twice over, so contributes `e_t`
  have hconst : ∀ σ ∈ ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))),
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = polytabloid t := by
    intro σ hσ
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign σ : ℤ) : ℚ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [polytabloid_relabel_of_mem_colSubgroup (Finset.mem_filter.mp hσ).2.2, smul_smul, hsq,
      one_smul]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const] at hsplit
  exact hsplit

/-- **The straightening step, in the abstract.**  Under the hypotheses of the Garnir relation, the
polytabloid of `t` lies in the rational span of the polytabloids of the relabelings `σt` for the
permutations `σ` that are supported in `X` and do **not** preserve the columns of `t`.

This is the division-free reading of
`TauCeti.YoungTableau.card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero`, whose
multiple of `e_t` is nonzero. -/
theorem polytabloid_mem_span_polytabloid_relabel (t : YoungTableau μ) {X : Finset (Fin μ.card)}
    {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r) (hcard : r < X.card) :
    polytabloid t ∈ Submodule.span ℚ
      ((fun σ => polytabloid (relabel σ t)) ''
        {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∉ colSubgroup t}) := by
  have hpos : 0 < ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))).card :=
    Finset.card_pos.mpr ⟨1, by simp⟩
  have hne : (({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  refine (Submodule.smul_mem_iff _ hne).mp ?_
  rw [Nat.cast_smul_eq_nsmul, eq_neg_of_add_eq_zero_left
    (card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero t hX hcard)]
  refine neg_mem (Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨σ, (Finset.mem_filter.mp hσ).2, rfl⟩

/-! ## The straightening step at a Garnir set -/

/-- **The straightening step.**  As soon as `(i, j + 1)` is a cell of `μ`, the polytabloid of `t`
lies in the rational span of the polytabloids of the relabelings `σt` by the permutations `σ` that
are supported in the Garnir set of `t` at `(i, j)` and move a label between its two halves, that
is between columns `j` and `j + 1`.

Applied at a cell where the rows of `t` fail to increase, this is the rewriting the straightening
algorithm performs on the way to the standard basis of the Specht module. -/
theorem polytabloid_mem_span_polytabloid_relabel_garnirSet (t : YoungTableau μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    polytabloid t ∈ Submodule.span ℚ
      ((fun σ => polytabloid (relabel σ t)) ''
        {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
          (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j}) := by
  have hindex : {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        σ ∉ colSubgroup t} =
      {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j} := by
    ext σ
    exact and_congr_right fun hσ => not_congr (mem_colSubgroup_iff_image_garnirSetLeft_eq hσ)
  rw [← hindex]
  exact polytabloid_mem_span_polytabloid_relabel t
    (fun _ hk => colLen_colIndex_le_colLen_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

/-! ## The straightening measure -/
/-- The column moment of a tableau: every label weighted by the index of its column.  A Garnir
step at a row inversion increases it, because it moves the small labels of the Garnir set into the
earlier of the two columns the set straddles. -/
private def colMoment (t : YoungTableau μ) : ℕ := ∑ k : Fin μ.card, colIndex t k * (k : ℕ)

/-- The row moment of a tableau: every label weighted by the index of its row.  Exchanging two
labels of one column into increasing order increases it, and leaves the column moment alone. -/
private def rowMoment (t : YoungTableau μ) : ℕ := ∑ k : Fin μ.card, rowIndex t k * (k : ℕ)

/-- The measure both steps of the straightening algorithm increase: the column moment, weighted
heavily enough that a gain in it outweighs any loss of row moment, plus the row moment. -/
private def straightWeight (t : YoungTableau μ) : ℕ :=
  (μ.card ^ 3 + 1) * colMoment t + rowMoment t

/-- A bound for `straightWeight`, which is what makes the straightening algorithm terminate. -/
private def straightBound (μ : YoungDiagram) : ℕ := (μ.card ^ 3 + 1) * μ.card ^ 3 + μ.card ^ 3

private theorem rowIndex_le_card (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k ≤ μ.card := by
  refine le_of_lt ((rowIndex_lt_colLen_zero t k).trans_le ?_)
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem colIndex_le_card (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t k ≤ μ.card := by
  refine le_of_lt ((colIndex_lt_rowLen t k).trans_le ?_)
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem colMoment_le (t : YoungTableau μ) : colMoment t ≤ μ.card ^ 3 :=
  calc colMoment t ≤ ∑ _k : Fin μ.card, μ.card * μ.card :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (colIndex_le_card t k) (le_of_lt k.isLt)
    _ = μ.card * (μ.card * μ.card) := by simp
    _ = μ.card ^ 3 := by ring

private theorem rowMoment_le (t : YoungTableau μ) : rowMoment t ≤ μ.card ^ 3 :=
  calc rowMoment t ≤ ∑ _k : Fin μ.card, μ.card * μ.card :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (rowIndex_le_card t k) (le_of_lt k.isLt)
    _ = μ.card * (μ.card * μ.card) := by simp
    _ = μ.card ^ 3 := by ring

private theorem straightWeight_le (t : YoungTableau μ) : straightWeight t ≤ straightBound μ :=
  Nat.add_le_add (Nat.mul_le_mul le_rfl (colMoment_le t)) (rowMoment_le t)

private theorem colMoment_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    colMoment (relabel σ t) = ∑ k : Fin μ.card, colIndex t k * ((σ k : Fin μ.card) : ℕ) := by
  rw [colMoment]
  simp only [colIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => colIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem rowMoment_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    rowMoment (relabel σ t) = ∑ k : Fin μ.card, rowIndex t k * ((σ k : Fin μ.card) : ℕ) := by
  rw [rowMoment]
  simp only [rowIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => rowIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem straightWeight_lt_of_colMoment_lt {t t' : YoungTableau μ}
    (h : colMoment t < colMoment t') : straightWeight t < straightWeight t' :=
  calc straightWeight t = (μ.card ^ 3 + 1) * colMoment t + rowMoment t := rfl
    _ < (μ.card ^ 3 + 1) * colMoment t + (μ.card ^ 3 + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_of_le (rowMoment_le t)) _
    _ = (μ.card ^ 3 + 1) * (colMoment t + 1) := (Nat.mul_succ _ _).symm
    _ ≤ (μ.card ^ 3 + 1) * colMoment t' := Nat.mul_le_mul le_rfl h
    _ ≤ straightWeight t' := Nat.le_add_right _ _

/-! ## Exchanging two labels of one column -/

/-- **Exchanging two labels of one column that are out of order increases the straightening
measure.**  The exchange leaves every label in its own column, so the column moment is unchanged,
while the smaller of the two labels moves to the earlier row and the row moment grows. -/
private theorem straightWeight_lt_of_swap {t : YoungTableau μ} {x y : Fin μ.card}
    (hcol : colIndex t x = colIndex t y) (hrow : rowIndex t x < rowIndex t y) (hyx : y < x) :
    straightWeight t < straightWeight (relabel (Equiv.swap x y) t) := by
  have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
  have hc := sum_mul_swap (colIndex t) Fin.val (Finset.mem_univ x) (Finset.mem_univ y) hne
  have hr := sum_mul_swap (rowIndex t) Fin.val (Finset.mem_univ x) (Finset.mem_univ y) hne
  rw [hcol] at hc
  have hcol' : colMoment (relabel (Equiv.swap x y) t) = colMoment t := by
    rw [colMoment_relabel, colMoment]
    refine Nat.add_right_cancel (m := colIndex t y * (x : ℕ) + colIndex t y * (y : ℕ)) ?_
    rw [hc]
    ring
  have hrow' : rowMoment t < rowMoment (relabel (Equiv.swap x y) t) := by
    rw [rowMoment_relabel]
    have hstep : rowMoment t + (rowIndex t x * (x : ℕ) + rowIndex t y * (y : ℕ)) <
        rowMoment t + (rowIndex t x * (y : ℕ) + rowIndex t y * (x : ℕ)) :=
      Nat.add_lt_add_left (mul_add_mul_lt_mul_add_mul hrow (Fin.lt_def.mp hyx)) _
    rw [rowMoment, ← hr] at hstep
    exact lt_of_add_lt_add_right hstep
  rw [straightWeight, straightWeight, hcol']
  exact Nat.add_lt_add_left hrow' _

/-! ## The Garnir step increases the measure -/

/-- **The left half of a Garnir set carries larger labels than the right half**, at a cell where
the columns of `t` increase but its rows do not.  The left half sits in column `j` weakly below
row `i`, so its labels are at least the label at `(i, j)`; the right half sits in column `j + 1`
weakly above row `i`, so its labels are at most the label at `(i, j + 1)`; and the row inversion
puts the second of those below the first. -/
private theorem lt_of_mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {x y : Fin μ.card}
    (hinc : ∀ p q : Fin μ.card, colIndex t p = colIndex t q → rowIndex t p < rowIndex t q → p < q)
    (hxr : rowIndex t x = i) (hxc : colIndex t x = j) (hyr : rowIndex t y = i)
    (hyc : colIndex t y = j + 1) (hyx : y < x) {a b : Fin μ.card}
    (ha : a ∈ garnirSetLeft t i j) (hb : b ∈ garnirSet t i j \ garnirSetLeft t i j) :
    b < a := by
  obtain ⟨hac, hai⟩ := mem_garnirSetLeft.mp ha
  obtain ⟨hbmem, hbnot⟩ := Finset.mem_sdiff.mp hb
  have hbc : colIndex t b = j + 1 :=
    colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hbmem hbnot
  have hbi : rowIndex t b ≤ i := by
    rcases mem_garnirSet.mp hbmem with h | h
    · omega
    · exact h.2
  have hxa : x ≤ a := by
    rcases eq_or_lt_of_le hai with h | h
    · exact le_of_eq (rowIndex_colIndex_injective t (Prod.ext (hxr.trans h) (hxc.trans hac.symm)))
    · exact le_of_lt (hinc x a (by rw [hxc, hac]) (by omega))
  have hby : b ≤ y := by
    rcases eq_or_lt_of_le hbi with h | h
    · exact le_of_eq
        (rowIndex_colIndex_injective t (Prod.ext (h.trans hyr.symm) (hbc.trans hyc.symm)))
    · exact le_of_lt (hinc b y (by rw [hbc, hyc]) (by omega))
  exact lt_of_le_of_lt hby (lt_of_lt_of_le hyx hxa)

/-- Summing over a Garnir set against the column index only sees which of its two halves a label
lies in: the left half contributes the weight `j` and the right half the weight `j + 1`. -/
private theorem sum_colIndex_garnirSet (t : YoungTableau μ) (i j : ℕ) (g : Fin μ.card → ℕ) :
    ∑ k ∈ garnirSet t i j, colIndex t k * g k =
      j * (∑ k ∈ garnirSet t i j, g k) + ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, g k := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  have hBc : ∀ k ∈ garnirSet t i j \ garnirSetLeft t i j,
      colIndex t k * g k = (j + 1) * g k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
    rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk1 hk2]
  have hAc : ∀ k ∈ garnirSetLeft t i j, colIndex t k * g k = j * g k := fun k hk => by
    rw [(mem_garnirSetLeft.mp hk).1]
  rw [← Finset.sum_sdiff hAX, ← Finset.sum_sdiff (f := g) hAX, Finset.sum_congr rfl hBc,
    Finset.sum_congr rfl hAc, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **A Garnir permutation that does not preserve the columns increases the column moment.**  It
exchanges labels of the left half of the Garnir set for labels of the right half; the latter are
the smaller ones, and they move into the earlier column. -/
private theorem colMoment_lt_of_garnir {t : YoungTableau μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin μ.card)} (hfix : ∀ k ∉ garnirSet t i j, σ k = k)
    (himg : (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j)
    (hlt : ∀ a ∈ garnirSetLeft t i j, ∀ b ∈ garnirSet t i j \ garnirSetLeft t i j,
      (b : ℕ) < (a : ℕ)) :
    colMoment t < colMoment (relabel σ t) := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  -- `σ` permutes the Garnir set, since it fixes everything outside it
  have hmemX : ∀ k ∈ garnirSet t i j, σ k ∈ garnirSet t i j := by
    intro k hk
    by_contra hnot
    have heq : σ k = k := σ.injective (hfix _ hnot)
    rw [heq] at hnot
    exact hnot hk
  have hXimg : (garnirSet t i j).image σ = garnirSet t i j :=
    Finset.eq_of_subset_of_card_le
      (fun z hz => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz; exact hmemX k hk)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
  -- the labels outside the Garnir set contribute the same to both moments
  have hout : ∀ k ∈ (garnirSet t i j)ᶜ,
      colIndex t k * ((σ k : Fin μ.card) : ℕ) = colIndex t k * (k : ℕ) :=
    fun k hk => by rw [hfix k (Finset.mem_compl.mp hk)]
  have hsum : ∀ g : Fin μ.card → ℕ,
      ∑ k : Fin μ.card, colIndex t k * g k =
        (∑ k ∈ garnirSet t i j, colIndex t k * g k) +
          ∑ k ∈ (garnirSet t i j)ᶜ, colIndex t k * g k :=
    fun g => (Finset.sum_add_sum_compl _ _).symm
  have himage : ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, ((σ k : Fin μ.card) : ℕ) =
      ∑ z ∈ (garnirSet t i j \ garnirSetLeft t i j).image σ, (z : ℕ) :=
    (Finset.sum_image fun x _ y _ hxy => σ.injective hxy).symm
  have hfull : ∑ k ∈ garnirSet t i j, ((σ k : Fin μ.card) : ℕ) =
      ∑ k ∈ garnirSet t i j, (k : ℕ) := by
    have h : ∑ z ∈ (garnirSet t i j).image σ, (z : ℕ) =
        ∑ k ∈ garnirSet t i j, ((σ k : Fin μ.card) : ℕ) :=
      Finset.sum_image fun x _ y _ hxy => σ.injective hxy
    rw [hXimg] at h
    exact h.symm
  -- so the two moments differ only in the sum over the right half of the Garnir set
  have hkey := sum_lt_sum_image_sdiff Fin.val hAX hXimg himg hlt
  rw [colMoment_relabel, colMoment, hsum fun k => ((σ k : Fin μ.card) : ℕ),
    hsum fun k => (k : ℕ), Finset.sum_congr rfl hout,
    sum_colIndex_garnirSet t i j fun k => ((σ k : Fin μ.card) : ℕ),
    sum_colIndex_garnirSet t i j fun k => (k : ℕ), hfull, himage]
  omega

/-! ## The straightening algorithm -/

/-- **A row inversion produces one between adjacent columns.**  Walking rightwards from the
earlier of the two cells, the first step at which the label drops is such an inversion. -/
private theorem exists_adjacent_row_inversion (t : YoungTableau μ) :
    ∀ (n : ℕ) (x y : Fin μ.card), colIndex t y - colIndex t x ≤ n →
      rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → y < x →
      ∃ u v : Fin μ.card,
        rowIndex t u = rowIndex t v ∧ colIndex t v = colIndex t u + 1 ∧ v < u := by
  intro n
  induction n with
  | zero =>
    intro x y hn _ hcol _
    omega
  | succ n ih =>
    intro x y hn hrow hcol hyx
    by_cases hadj : colIndex t y = colIndex t x + 1
    · exact ⟨x, y, hrow, hadj, hyx⟩
    · have hmem : (rowIndex t x, colIndex t x + 1) ∈ μ := by
        have hcell : (rowIndex t x, colIndex t y) ∈ μ := by
          rw [hrow]
          exact rowIndex_colIndex_mem t y
        exact μ.up_left_mem le_rfl (by omega) hcell
      obtain ⟨z, hzr, hzc⟩ := exists_rowIndex_colIndex t hmem
      rcases lt_trichotomy z x with hzx | hzx | hzx
      · exact ⟨x, z, hzr.symm, hzc, hzx⟩
      · exact absurd hzc (by rw [hzx]; omega)
      · refine ih z y ?_ (by rw [hzr, hrow]) ?_ (hyx.trans hzx)
        · omega
        · omega

/-- **A tableau that is not standard has its polytabloid in the span of heavier ones.**  If two
labels of one column are out of order, exchanging them is a column permutation, which changes the
polytabloid only by its sign; otherwise the rows fail to increase somewhere, and the Garnir
relation at that cell rewrites the polytabloid in terms of the relabelings that move a label
between the two columns concerned. -/
private theorem polytabloid_mem_span_of_lt (t : YoungTableau μ)
    (hns : ¬ ((∀ x y : Fin μ.card,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin μ.card, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y)) :
    polytabloid t ∈ Submodule.span ℚ
      {v | ∃ t' : YoungTableau μ, straightWeight t < straightWeight t' ∧ v = polytabloid t'} := by
  classical
  by_cases hinc : ∀ x y : Fin μ.card,
      colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y
  · -- the columns of `t` increase, so a row of `t` is out of order
    have hrowfail : ¬ ∀ x y : Fin μ.card,
        rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y :=
      fun h => hns ⟨hinc, h⟩
    push Not at hrowfail
    obtain ⟨x, y, hrow, hcol, hyx⟩ := hrowfail
    have hne : x ≠ y := fun h => absurd (congrArg (colIndex t) h) hcol.ne
    obtain ⟨u, v, huv, hadj, hvu⟩ := exists_adjacent_row_inversion t _ x y le_rfl hrow hcol
      (lt_of_le_of_ne hyx (Ne.symm hne))
    have hcell : (rowIndex t u, colIndex t u + 1) ∈ μ := by
      have h := rowIndex_colIndex_mem t v
      rwa [← huv, hadj] at h
    refine (Submodule.span_le.mpr ?_)
      (polytabloid_mem_span_polytabloid_relabel_garnirSet t hcell)
    rintro _ ⟨σ, ⟨hfix, himg⟩, rfl⟩
    refine Submodule.subset_span ⟨relabel σ t, ?_, rfl⟩
    refine straightWeight_lt_of_colMoment_lt (colMoment_lt_of_garnir hfix himg fun a ha b hb => ?_)
    exact Fin.lt_def.mp (lt_of_mem_garnirSet hinc rfl rfl huv.symm hadj hvu ha hb)
  · -- a column of `t` is out of order
    push Not at hinc
    obtain ⟨x, y, hcol, hrow, hyx⟩ := hinc
    have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
    have hswap : Equiv.swap x y ∈ colSubgroup t := by
      rw [mem_colSubgroup]
      intro k
      rcases eq_or_ne k x with rfl | hkx
      · rw [Equiv.swap_apply_left, hcol]
      rcases eq_or_ne k y with rfl | hky
      · rw [Equiv.swap_apply_right, hcol]
      · rw [Equiv.swap_apply_of_ne_of_ne hkx hky]
    have hsign : polytabloid (relabel (Equiv.swap x y) t) = -polytabloid t := by
      rw [polytabloid_relabel_of_mem_colSubgroup hswap, Equiv.Perm.sign_swap hne]
      simp
    have hmem : polytabloid (relabel (Equiv.swap x y) t) ∈ Submodule.span ℚ
        {v | ∃ t' : YoungTableau μ,
          straightWeight t < straightWeight t' ∧ v = polytabloid t'} :=
      Submodule.subset_span
        ⟨_, straightWeight_lt_of_swap hcol hrow (lt_of_le_of_ne hyx (Ne.symm hne)), rfl⟩
    rw [hsign] at hmem
    simpa using neg_mem hmem

/-- **The straightening algorithm**: every polytabloid is a rational combination of the
polytabloids of the standard tableaux of the same shape.  The straightening measure increases at
every rewriting step and is bounded, so the rewriting terminates, and it terminates only at a
tableau increasing down its columns and along its rows. -/
theorem polytabloid_mem_span_polytabloid_standard (t : YoungTableau μ) :
    polytabloid t ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau μ => polytabloid T.toTableau) := by
  classical
  suffices H : ∀ (N : ℕ) (t : YoungTableau μ), straightBound μ - straightWeight t ≤ N →
      polytabloid t ∈ Submodule.span ℚ
        (Set.range fun T : StandardYoungTableau μ => polytabloid T.toTableau) from
    H _ t le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t ht
    by_cases hstd : (∀ x y : Fin μ.card,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin μ.card, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y
    · obtain ⟨T, rfl⟩ := (exists_standardYoungTableau_toTableau_eq_iff t).mpr hstd
      exact Submodule.subset_span ⟨T, rfl⟩
    · refine (Submodule.span_le.mpr ?_) (polytabloid_mem_span_of_lt t hstd)
      rintro _ ⟨t', hlt, rfl⟩
      refine ih (straightBound μ - straightWeight t') ?_ t' le_rfl
      exact lt_of_lt_of_le
        (Nat.sub_lt_sub_left (lt_of_lt_of_le hlt (straightWeight_le t')) hlt) ht

end YoungTableau

end TauCeti
end
end TAF_LiteralSource_0187

section TAF_LiteralSource_0188
/- Original module: PaperVerification.AlternatingFormsTableauMinors -/


/-!
# Rectangular polytabloids and products of maximal minors

The map in this file sends a row tabloid to the literal matrix-entry monomial
recording the row occupied by each label. Column antisymmetrization therefore
maps to a product of actual determinants. This identifies the hypotheses of the
existing rational Specht straightening theorem with the maximal-minor
straightening problem; no standard-monomial relation is introduced as an axiom.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial TauCeti

namespace PaperVerification.AlternatingForms

def minorRectangle (s r : ℕ) : YoungDiagram where
  cells := Finset.range s ×ˢ Finset.range r
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe,Finset.mem_product,Finset.mem_range] at hb ⊢
    exact ⟨hab.1.trans_lt hb.1,hab.2.trans_lt hb.2⟩

@[simp] theorem mem_minorRectangle {s r i j : ℕ} :
    (i,j) ∈ minorRectangle s r ↔ i < s ∧ j < r := by
  simp [minorRectangle]

def rectangleCellEquiv (s r : ℕ) : ↥(minorRectangle s r).cells ≃ Fin s × Fin r where
  toFun c := ⟨⟨c.val.1,(mem_minorRectangle.mp c.property).1⟩,
    ⟨c.val.2,(mem_minorRectangle.mp c.property).2⟩⟩
  invFun p := ⟨(p.1.val,p.2.val),mem_minorRectangle.mpr ⟨p.1.isLt,p.2.isLt⟩⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

variable {s r n : ℕ}

def rectangleLabels (t : YoungTableau (minorRectangle s r)) :
    Fin s × Fin r ≃ Fin (minorRectangle s r).card :=
  (rectangleCellEquiv s r).symm.trans t

def rectangleRow (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) : Fin s :=
  ((rectangleLabels t).symm k).1

def rectangleColumn (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) : Fin r :=
  ((rectangleLabels t).symm k).2

@[simp] theorem rectangleRow_val (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) :
    (rectangleRow t k).val = YoungTableau.rowIndex t k := by
  rw [YoungTableau.rowIndex_def]
  rfl

@[simp] theorem rectangleColumn_val (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) :
    (rectangleColumn t k).val = YoungTableau.colIndex t k := by
  rw [YoungTableau.colIndex_def]
  rfl

@[simp] theorem rectangleRow_labels (t : YoungTableau (minorRectangle s r))
    (i : Fin s) (j : Fin r) : rectangleRow t (rectangleLabels t (i,j)) = i := by
  simp [rectangleRow]

@[simp] theorem rectangleColumn_labels (t : YoungTableau (minorRectangle s r))
    (i : Fin s) (j : Fin r) : rectangleColumn t (rectangleLabels t (i,j)) = j := by
  simp [rectangleColumn]

def rectangularRowMonomial
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) : MvPolynomial (Fin s × Fin n) ℚ :=
  ∏ k, X (rectangleRow t k,v k)

theorem rectangularRowMonomial_eq_of_tabloid_eq
    (v : Fin (minorRectangle s r).card → Fin n)
    {t u : YoungTableau (minorRectangle s r)}
    (h : YoungTableau.tabloid t = YoungTableau.tabloid u) :
    rectangularRowMonomial v t = rectangularRowMonomial v u := by
  apply Finset.prod_congr rfl
  intro k hk
  congr 2
  apply Fin.ext
  rw [rectangleRow_val, rectangleRow_val]
  exact congrFun (YoungTableau.tabloid_eq_iff_rowIndex_eq.mp h) k

def rectangularTabloidMonomial
    (v : Fin (minorRectangle s r).card → Fin n)
    (q : Equiv.Perm (Fin (minorRectangle s r).card) ⧸
      youngSubgroup (shapePartition (minorRectangle s r))) :
    MvPolynomial (Fin s × Fin n) ℚ :=
  rectangularRowMonomial v (Classical.choose (YoungTableau.tabloid_surjective q))

@[simp] theorem rectangularTabloidMonomial_tabloid
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMonomial v (YoungTableau.tabloid t) = rectangularRowMonomial v t := by
  apply rectangularRowMonomial_eq_of_tabloid_eq
  exact Classical.choose_spec (YoungTableau.tabloid_surjective (YoungTableau.tabloid t))

def rectangularTabloidMap (v : Fin (minorRectangle s r).card → Fin n) :
    (permutationModule (shapePartition (minorRectangle s r))).V →ₗ[ℚ]
      MvPolynomial (Fin s × Fin n) ℚ :=
  (permutationModuleBasis (shapePartition (minorRectangle s r))).constr ℚ
    (rectangularTabloidMonomial v)

@[simp] theorem rectangularTabloidMap_single
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMap v (MonoidAlgebra.single (YoungTableau.tabloid t) 1) =
      rectangularRowMonomial v t := by
  simpa only [rectangularTabloidMap,permutationModuleBasis,MonoidAlgebra.basis_apply,
    rectangularTabloidMonomial_tabloid] using
    (permutationModuleBasis (shapePartition (minorRectangle s r))).constr_basis ℚ
      (rectangularTabloidMonomial v) (YoungTableau.tabloid t)

def rectangleColumnPermutation (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) : YoungTableau.colSubgroup t :=
  ⟨(rectangleLabels t).permCongr (Equiv.prodCongrLeft fun j => (σ j).symm),by
    rw [YoungTableau.mem_colSubgroup]
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (rectangleLabels t).surjective k
    rw [← rectangleColumn_val, ← rectangleColumn_val]
    simp [Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]⟩

@[simp] theorem rectangleColumnPermutation_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s))
    (i : Fin s) (j : Fin r) :
    (rectangleColumnPermutation t σ : Equiv.Perm _) (rectangleLabels t (i,j)) =
      rectangleLabels t ((σ j).symm i,j) := by
  simp [rectangleColumnPermutation,Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]

@[simp] theorem rectangleColumnPermutation_inv_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s))
    (i : Fin s) (j : Fin r) :
    (rectangleColumnPermutation t σ : Equiv.Perm _).symm (rectangleLabels t (i,j)) =
      rectangleLabels t (σ j i,j) := by
  apply (rectangleColumnPermutation t σ : Equiv.Perm _).injective
  simp

theorem rectangleColumn_preserved (t : YoungTableau (minorRectangle s r))
    (q : YoungTableau.colSubgroup t) (k : Fin (minorRectangle s r).card) :
    rectangleColumn t ((q : Equiv.Perm _) k) = rectangleColumn t k := by
  apply Fin.ext
  rw [rectangleColumn_val, rectangleColumn_val]
  exact YoungTableau.mem_colSubgroup.mp q.property k

def rectangleColumnRows (t : YoungTableau (minorRectangle s r))
    (q : YoungTableau.colSubgroup t) (j : Fin r) : Equiv.Perm (Fin s) where
  toFun i := rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j)))
  invFun i := rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j)))
  left_inv i := by
    have hp : (rectangleLabels t).symm
        ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))) =
        (rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))),j) := by
      apply Prod.ext
      · rfl
      · have hc := rectangleColumn_preserved t q
          ((q : Equiv.Perm _).symm (rectangleLabels t (i,j)))
        rw [Equiv.apply_symm_apply] at hc
        exact hc.symm.trans (rectangleColumn_labels t i j)
    change rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t
      (rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))),j))) = i
    rw [← hp,Equiv.apply_symm_apply,Equiv.apply_symm_apply,rectangleRow_labels]
  right_inv i := by
    have hp : (rectangleLabels t).symm ((q : Equiv.Perm _) (rectangleLabels t (i,j))) =
        (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j) := by
      apply Prod.ext
      · rfl
      · exact (rectangleColumn_preserved t q (rectangleLabels t (i,j))).trans
          (rectangleColumn_labels t i j)
    change rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t
      (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j))) = i
    rw [← hp,Equiv.apply_symm_apply,Equiv.symm_apply_apply,rectangleRow_labels]

def rectangleColumnPermutationEquiv (t : YoungTableau (minorRectangle s r)) :
    (Fin r → Equiv.Perm (Fin s)) ≃ YoungTableau.colSubgroup t where
  toFun := rectangleColumnPermutation t
  invFun := rectangleColumnRows t
  left_inv σ := by
    funext j
    apply Equiv.ext
    intro i
    simp [rectangleColumnRows]
  right_inv q := by
    apply Subtype.ext
    apply Equiv.ext
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (rectangleLabels t).surjective k
    rw [rectangleColumnPermutation_apply]
    change rectangleLabels t (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j) = _
    apply (rectangleLabels t).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · exact ((rectangleColumn_preserved t q (rectangleLabels t (i,j))).trans
        (rectangleColumn_labels t i j)).symm

@[simp] theorem rectangleColumnPermutationEquiv_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangleColumnPermutationEquiv t σ = rectangleColumnPermutation t σ := rfl

theorem rectangleColumnPermutation_sign (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) :
    Equiv.Perm.sign (rectangleColumnPermutation t σ).val =
      ∏ j, Equiv.Perm.sign (σ j) := by
  simp only [rectangleColumnPermutation,Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_prodCongrLeft,Equiv.Perm.sign_symm]

theorem rectangularRowMonomial_column_relabel
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangularRowMonomial v
      (YoungTableau.relabel (rectangleColumnPermutation t σ : Equiv.Perm _) t) =
      ∏ j, ∏ i, (X (σ j i,v (rectangleLabels t (i,j))) :
        MvPolynomial (Fin s × Fin n) ℚ) := by
  classical
  rw [rectangularRowMonomial,← Equiv.prod_comp (rectangleLabels t)]
  rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  apply Fin.ext
  rw [rectangleRow_val,YoungTableau.rowIndex_relabel]
  rw [← rectangleRow_val]
  change (rectangleRow t ((rectangleColumnPermutation t σ : Equiv.Perm _).symm
    (rectangleLabels t (i,j)))).val = _
  simp only [rectangleColumnPermutation_inv_apply, rectangleRow_labels]

/-- Actual products of maximal minors, with arbitrary column values before
straightening. Repeated values are permitted at this intermediate stage. -/
def rectangularMinorProduct
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) : MvPolynomial (Fin s × Fin n) ℚ :=
  ∏ j, Matrix.det (Matrix.of (fun i k : Fin s => X (i,v (rectangleLabels t (k,j)))))

/-- Normalize the sign scalar before instantiating it at the large polynomial
and permutation-module expressions. This is the ordinary product-smul law. -/
private theorem rational_units_smul_prod
    {A : Type*} [CommRing A] [Algebra ℚ A]
    {ι : Type*} [Fintype ι] (c : ι → ℤˣ) (f : ι → A) :
    (((∏ i, c i : ℤˣ) : ℤ) : ℚ) • (∏ i, f i) = ∏ i, c i • f i := by
  rw [Finset.prod_smul]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- One actual column-antisymmetrizer summand maps to the corresponding
product of determinant summands. All relabeling and scalar conversions are
proved before the outer sum is formed. -/
theorem rectangularTabloidMap_signed_column
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangularTabloidMap v
      (((Equiv.Perm.sign (rectangleColumnPermutation t σ).val : ℤ) : ℚ) •
        MonoidAlgebra.single
          ((rectangleColumnPermutation t σ).val • YoungTableau.tabloid t) (1 : ℚ)) =
      ∏ j, Equiv.Perm.sign (σ j) •
        ∏ i, (X (σ j i, v (rectangleLabels t (i,j))) :
          MvPolynomial (Fin s × Fin n) ℚ) := by
  rw [map_smul, ← YoungTableau.tabloid_relabel, rectangularTabloidMap_single,
    rectangleColumnPermutation_sign, rectangularRowMonomial_column_relabel]
  exact rational_units_smul_prod
    (fun j => Equiv.Perm.sign (σ j))
    (fun j => ∏ i, (X (σ j i, v (rectangleLabels t (i,j))) :
      MvPolynomial (Fin s × Fin n) ℚ))

theorem rectangularTabloidMap_polytabloid
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMap v (YoungTableau.polytabloid t) = rectangularMinorProduct v t := by
  classical
  rw [YoungTableau.polytabloid_eq_sum,map_sum,
    ← Equiv.sum_comp (rectangleColumnPermutationEquiv t)]
  simp only [rectangleColumnPermutationEquiv_apply, rectangularMinorProduct,
    Matrix.det_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact rectangularTabloidMap_signed_column v t σ

/-- The exact rational Specht straightening theorem transported through the
literal matrix-monomial map. -/
theorem rectangularMinorProduct_mem_span_standard
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v t ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau (minorRectangle s r) =>
        rectangularMinorProduct v T.toTableau) := by
  rw [← rectangularTabloidMap_polytabloid]
  have h := YoungTableau.polytabloid_mem_span_polytabloid_standard t
  refine Submodule.span_induction
    (p := fun x _ => rectangularTabloidMap v x ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau (minorRectangle s r) =>
        rectangularMinorProduct v T.toTableau)) ?_ ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨T,rfl⟩ := hx
    rw [rectangularTabloidMap_polytabloid]
    exact Submodule.subset_span ⟨T,rfl⟩
  · simpa only [map_zero] using (Submodule.span ℚ _).zero_mem
  · intro x y hx hy hmx hmy
    simpa only [map_add] using (Submodule.span ℚ _).add_mem hmx hmy
  · intro a x hx hmx
    simpa only [map_smul] using (Submodule.span ℚ _).smul_mem a hmx

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0188

section TAF_LiteralSource_0189
/- Original module: PaperVerification.AlternatingFormsMinorStraightening -/


/-!
# Standard products span the algebra of maximal minors in characteristic zero

Each occurrence of a matrix-column value first receives its own label. Sorting
the labels makes their value map monotone; ordinary standard tableaux then
specialize to semistandard tableaux. A repeated value in one column gives a
zero determinant, while every other standard tableau gives a genuine
multichain of strictly increasing maximal-minor indices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial TauCeti

namespace PaperVerification.AlternatingForms

variable {s n r : ℕ}

def StandardMinorChain (s n r : ℕ) :=
  {I : Fin r → Fin s → Fin n // (∀ j, StrictMono (I j)) ∧ Monotone I}

instance standardMinorChain_fintype (s n r : ℕ) : Fintype (StandardMinorChain s n r) := by
  classical
  unfold StandardMinorChain
  infer_instance

def genericMinorProduct {K : Type*} [CommRing K] (I : Fin r → Fin s → Fin n) :
    MvPolynomial (Fin s × Fin n) K :=
  ∏ j, Matrix.det (Matrix.of (fun i k : Fin s => X (i,I j k)))

def genericStandardMinorProduct {K : Type*} [CommRing K]
    (C : StandardMinorChain s n r) : MvPolynomial (Fin s × Fin n) K :=
  genericMinorProduct C.val

theorem rectangleLabels_trans (t : YoungTableau (minorRectangle s r))
    (σ : Equiv.Perm (Fin (minorRectangle s r).card)) (p : Fin s × Fin r) :
    rectangleLabels (t.trans σ) p = σ (rectangleLabels t p) := rfl

theorem exists_sorted_rectangle_labels (I : Fin r → Fin s → Fin n) :
    ∃ (v : Fin (minorRectangle s r).card → Fin n)
      (t : YoungTableau (minorRectangle s r)),
      Monotone v ∧ ∀ i j, v (rectangleLabels t (i,j)) = I j i := by
  obtain ⟨t₀⟩ := YoungTableau.nonempty (minorRectangle s r)
  let u : Fin (minorRectangle s r).card → Fin n := fun k =>
    I (rectangleColumn t₀ k) (rectangleRow t₀ k)
  refine ⟨u ∘ Tuple.sort u,t₀.trans (Tuple.sort u).symm,Tuple.monotone_sort u,?_⟩
  intro i j
  simp only [Function.comp_apply,rectangleLabels_trans,Equiv.apply_symm_apply,u,
    rectangleColumn_labels,rectangleRow_labels]

theorem rectangularMinorProduct_eq_generic
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v t =
      genericMinorProduct (K := ℚ) (fun j i => v (rectangleLabels t (i,j))) := rfl

theorem standard_rectangle_values_row_monotone
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) :
    Monotone (fun j : Fin r => fun i : Fin s => v (rectangleLabels T.toTableau (i,j))) := by
  intro j k hjk i
  rcases eq_or_lt_of_le hjk with rfl | hjk
  · exact le_rfl
  · apply hv
    exact (T.row_strict hjk (mem_minorRectangle.mpr ⟨i.isLt,k.isLt⟩)).le

theorem standard_rectangle_values_column_monotone
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) (j : Fin r) :
    Monotone (fun i : Fin s => v (rectangleLabels T.toTableau (i,j))) := by
  intro i k hik
  rcases eq_or_lt_of_le hik with rfl | hik
  · exact le_rfl
  · apply hv
    exact (T.col_strict hik (mem_minorRectangle.mpr ⟨k.isLt,j.isLt⟩)).le

theorem genericMinorProduct_zero_of_repeated_column {K : Type*} [CommRing K]
    (I : Fin r → Fin s → Fin n) (j : Fin r) (h : ¬Function.Injective (I j)) :
    genericMinorProduct (K := K) I = 0 := by
  classical
  obtain ⟨i,k,hval,hne⟩ : ∃ i k, I j i = I j k ∧ i ≠ k := by
    by_contra hn
    apply h
    intro i k hik
    by_contra hne
    exact hn ⟨i,k,hik,hne⟩
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact Matrix.det_zero_of_column_eq hne (fun a => by simp only [Matrix.of_apply,hval])

theorem standard_rectangle_product_mem_span
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v T.toTableau ∈ Submodule.span ℚ
      (Set.range (genericStandardMinorProduct (K := ℚ) (s := s) (n := n) (r := r))) := by
  classical
  let I : Fin r → Fin s → Fin n := fun j i => v (rectangleLabels T.toTableau (i,j))
  change genericMinorProduct I ∈ _
  by_cases hI : ∀ j, Function.Injective (I j)
  · exact Submodule.subset_span ⟨⟨I,fun j =>
      (standard_rectangle_values_column_monotone v hv T j).strictMono_of_injective (hI j),
      standard_rectangle_values_row_monotone v hv T⟩,rfl⟩
  · obtain ⟨j,hj⟩ := not_forall.mp hI
    rw [genericMinorProduct_zero_of_repeated_column I j hj]
    exact (Submodule.span ℚ _).zero_mem

/-- Full maximal-minor straightening over the rational numbers, with every
number of rows, ambient columns, and minor factors retained. -/
theorem genericMinorProduct_mem_span_standard_rat (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := ℚ) I ∈ Submodule.span ℚ
      (Set.range (genericStandardMinorProduct (K := ℚ) (s := s) (n := n) (r := r))) := by
  obtain ⟨v,t,hv,hvt⟩ := exists_sorted_rectangle_labels I
  have he : genericMinorProduct (K := ℚ) I = rectangularMinorProduct v t := by
    rw [rectangularMinorProduct_eq_generic]
    congr 1
    funext j i
    exact (hvt i j).symm
  rw [he]
  apply Submodule.span_le.mpr (fun p hp => ?_)
    (rectangularMinorProduct_mem_span_standard v t)
  obtain ⟨T,rfl⟩ := hp
  exact standard_rectangle_product_mem_span v hv T

section CoefficientExtension

variable {K : Type*} [Field K] [CharZero K]

def rationalMatrixCoefficientMap :
    MvPolynomial (Fin s × Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin s × Fin n) K :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℚ K)

theorem rationalMatrixCoefficientMap_product (I : Fin r → Fin s → Fin n) :
    rationalMatrixCoefficientMap (K := K) (genericMinorProduct (K := ℚ) I) =
      genericMinorProduct (K := K) I := by
  simp only [genericMinorProduct,map_prod,AlgHom.map_det]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  apply Matrix.ext
  intro i k
  simp [rationalMatrixCoefficientMap]

/-- The rational straightening identities hold over every characteristic-zero
field by actual coefficient extension. -/
theorem genericMinorProduct_mem_span_standard (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := K) I ∈ Submodule.span K
      (Set.range (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r))) := by
  rw [← rationalMatrixCoefficientMap_product]
  have h := genericMinorProduct_mem_span_standard_rat I
  refine Submodule.span_induction
    (p := fun x _ => rationalMatrixCoefficientMap (K := K) x ∈ Submodule.span K
      (Set.range (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r))))
    ?_ ?_ ?_ ?_ h
  · intro p hp
    obtain ⟨C,rfl⟩ := hp
    change rationalMatrixCoefficientMap (genericMinorProduct C.val) ∈ _
    rw [rationalMatrixCoefficientMap_product]
    exact Submodule.subset_span ⟨C,rfl⟩
  · simpa only [map_zero] using (Submodule.span K _).zero_mem
  · intro x y hx hy hmx hmy
    simpa only [map_add] using (Submodule.span K _).add_mem hmx hmy
  · intro a x hx hmx
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ a hmx

end CoefficientExtension

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0189

section TAF_LiteralSource_0190
/- Original module: PaperVerification.WeightMonicSubringDescent -/


/-!
# Descent of a finite monic triangular expansion

If a finite polynomial family has distinct weight-monic leading monomials,
then a linear combination with coefficients in a larger field can have all
its polynomial coefficients in a subring only when all its expansion
coefficients already lie in that subring.  This is a saturation statement,
not a dimension argument or an assumption of flatness.

The main application is descent of rational maximal-minor straightening to
integer identities, followed by arbitrary coefficient extension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification

open scoped BigOperators Classical
open MvPolynomial
open AlternatingForms

variable {K R σ ι : Type*} [Field K] [CommRing R] [Fintype ι]

/-- A leading-coefficient argument works over an arbitrary subring of the
coefficient field.  Only the finite displayed family is ordered by weight. -/
theorem weightMonic_coefficients_mem_subring
    (S : Subring K) (w : σ → ℤ) (p : ι → MvPolynomial σ K)
    (a : ι → σ →₀ ℕ) (ha : Function.Injective a)
    (hp : ∀ i, IsWeightMonic w (p i) (a i))
    (hpS : ∀ i d, (p i).coeff d ∈ S) (c : ι → K)
    (hcomb : ∀ d, (∑ i, c i • p i).coeff d ∈ S) :
    ∀ i, c i ∈ S := by
  intro i
  by_contra hi
  let bad : Finset ι := Finset.univ.filter fun j ↦ c j ∉ S
  have hbad : bad.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨j, hj, hmax⟩ := bad.exists_max_image (fun j ↦ Finsupp.weight w (a j)) hbad
  have hjbad : c j ∉ S := (Finset.mem_filter.mp hj).2
  have hrest : (∑ k ∈ (Finset.univ : Finset ι).erase j,
      c k * (p k).coeff (a j)) ∈ S := by
    apply S.sum_mem
    intro k hk
    by_cases hkS : c k ∈ S
    · exact S.mul_mem hkS (hpS k (a j))
    · have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hkbad : k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkS⟩
      have hzero := (hp k).2 (a j) (fun he ↦ hkj (ha he.symm)) (hmax k hkbad)
      rw [hzero, mul_zero]
      exact S.zero_mem
  have hc := hcomb (a j)
  rw [coeff_sum] at hc
  simp only [coeff_smul, smul_eq_mul] at hc
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun k ↦ c k * (p k).coeff (a j)) (Finset.mem_univ j), (hp j).1, mul_one] at hc
  apply hjbad
  simpa only [add_sub_cancel_left] using S.sub_mem hc hrest

/-- An honest injective coefficient extension reflects membership in the
span of a monic triangular family.  In particular, rational spanning of
integer polynomials descends to integral spanning. -/
theorem weightMonic_span_descent
    (φ : R →+* K) (hφ : Function.Injective φ)
    (w : σ → ℤ) (p : ι → MvPolynomial σ R) (a : ι → σ →₀ ℕ)
    (ha : Function.Injective a)
    (hp : ∀ i, IsWeightMonic w (MvPolynomial.map φ (p i)) (a i))
    (q : MvPolynomial σ R)
    (hq : MvPolynomial.map φ q ∈
      Submodule.span K (Set.range fun i ↦ MvPolynomial.map φ (p i))) :
    q ∈ Submodule.span R (Set.range p) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have hcoeff : ∀ i, c i ∈ φ.range := by
    apply weightMonic_coefficients_mem_subring φ.range w _ a ha hp
    · intro i d
      exact ⟨(p i).coeff d, (MvPolynomial.coeff_map φ (p i) d).symm⟩
    · intro d
      rw [hc]
      exact ⟨q.coeff d, (MvPolynomial.coeff_map φ q d).symm⟩
  let d : ι → R := fun i ↦ Classical.choose (hcoeff i)
  have hd (i : ι) : φ (d i) = c i := Classical.choose_spec (hcoeff i)
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  refine ⟨d, ?_⟩
  apply MvPolynomial.map_injective φ hφ
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  simp_rw [hd]
  simpa only [MvPolynomial.smul_eq_C_mul] using hc

end PaperVerification
end
end
end TAF_LiteralSource_0190

section TAF_LiteralSource_0191
/- Original module: PaperVerification.AlternatingFormsIntegralStraightening -/


/-!
# Integral maximal-minor straightening and arbitrary coefficient change

The previously proved rational straightening theorem has integral input
polynomials.  Distinct monic diagonal leading terms force its expansion
coefficients to be integers.  Mapping these literal integer polynomial
identities proves straightening over every commutative ring, including
fields of positive characteristic.  The determinant expansion below
includes all zero-size boundary cases without any nonemptiness assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {s n r : ℕ}

theorem genericMinorProduct_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Fin r → Fin s → Fin n) :
    MvPolynomial.map φ (genericMinorProduct (K := R) I) =
      genericMinorProduct (K := S) I := by
  simp only [genericMinorProduct, map_prod, RingHom.map_det]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  apply Matrix.ext
  intro i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    MvPolynomial.map_X]

theorem genericStandardMinorProduct_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : StandardMinorChain s n r) :
    MvPolynomial.map φ (genericStandardMinorProduct (K := R) C) =
      genericStandardMinorProduct (K := S) C :=
  genericMinorProduct_map φ C.val

section MonicExpansion

variable {K : Type*} [Field K]

theorem genericMinorProduct_expansion (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := K) I =
      ∑ σ : Fin r → Equiv.Perm (Fin s),
        monomial (chainTermExponent I σ)
          (∏ j, Equiv.Perm.sign (σ j) • (1 : K)) := by
  classical
  have hd (j : Fin r) :
      Matrix.det (Matrix.of (fun i k : Fin s => (X (i,I j k) : MvPolynomial (Fin s × Fin n) K))) =
        ∑ σ : Equiv.Perm (Fin s), monomial (minorTermExponent (I j) σ)
          (Equiv.Perm.sign σ • (1 : K)) := by
    rw [Matrix.det_apply]
    simp only [Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [X, prod_monomial_eq_monomial_sum, Finset.prod_const_one,
      smul_monomial, minorTermExponent]
  simp only [genericMinorProduct, hd]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prod_monomial_eq_monomial_sum _ _

/-- The actual generic standard products have a unique monic greatest
diagonal monomial in every size, including empty rectangles. -/
theorem genericStandardMinorProduct_weightMonic (C : StandardMinorChain s n r) :
    IsWeightMonic (bandEntryWeight s n) (genericStandardMinorProduct (K := K) C)
      (chainDiagonalExponent C.val) := by
  apply isWeightMonic_of_finite_expansion _ _ _ _ (fun _ => 1)
    (genericMinorProduct_expansion C.val)
  · simp only [Equiv.Perm.sign_one, one_smul, Finset.prod_const_one]
  · exact chainTermExponent_weight_lt_diagonal C.val C.property.1

end MonicExpansion

/-- The diagonal exponent determines the standard chain by recovering
the sorted multiplicity list in every row. -/
theorem standardChainDiagonalExponent_injective :
    Function.Injective
      (fun C : StandardMinorChain s n r => chainDiagonalExponent C.val) := by
  classical
  intro C D h
  apply Subtype.ext
  funext t i
  have hperm : (List.ofFn fun t => C.val t i).Perm (List.ofFn fun t => D.val t i) := by
    apply List.perm_iff_count.mpr
    intro j
    simpa only [chainDiagonalExponent_apply] using congrArg (fun a => a (i,j)) h
  have hC : (List.ofFn fun t => C.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => C.val t i) from fun a b hab => C.property.2 hab i).sortedLE_ofFn).pairwise
  have hD : (List.ofFn fun t => D.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => D.val t i) from fun a b hab => D.property.2 hab i).sortedLE_ofFn).pairwise
  exact congrFun (List.ofFn_injective (List.Perm.eq_of_pairwise' hC hD hperm)) t

/-- Rational straightening descends to integral straightening by monicity,
so no tableau denominator remains in the maximal-minor identities. -/
theorem genericMinorProduct_mem_span_standard_int (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := ℤ) I ∈ Submodule.span ℤ
      (Set.range (genericStandardMinorProduct (K := ℤ) (s := s) (n := n) (r := r))) := by
  apply PaperVerification.weightMonic_span_descent
    (Int.castRingHom ℚ) Int.cast_injective (bandEntryWeight s n)
    (genericStandardMinorProduct (K := ℤ))
    (fun C : StandardMinorChain s n r => chainDiagonalExponent C.val)
    standardChainDiagonalExponent_injective
  · intro C
    rw [genericStandardMinorProduct_map]
    exact genericStandardMinorProduct_weightMonic C
  · simpa only [genericMinorProduct_map, genericStandardMinorProduct_map] using
      genericMinorProduct_mem_span_standard_rat I

/-- Explicit integral expansion coefficients exist for every product of
maximal minors.  The statement is a polynomial identity over `ℤ`. -/
theorem genericMinorProduct_integer_expansion (I : Fin r → Fin s → Fin n) :
    ∃ c : StandardMinorChain s n r → ℤ,
      (∑ C, c C • genericStandardMinorProduct (K := ℤ) C) =
        genericMinorProduct (K := ℤ) I :=
  (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (genericMinorProduct_mem_span_standard_int I)

/-- Every integral expansion remains exactly the same determinant identity
after arbitrary coefficient change, without an injectivity assumption. -/
theorem genericMinorProduct_integer_expansion_map
    {R : Type*} [CommRing R] (I : Fin r → Fin s → Fin n)
    (c : StandardMinorChain s n r → ℤ)
    (hc : (∑ C, c C • genericStandardMinorProduct (K := ℤ) C) =
      genericMinorProduct (K := ℤ) I) :
    (∑ C, (c C : R) • genericStandardMinorProduct (K := R) C) =
      genericMinorProduct (K := R) I := by
  have h := congrArg (MvPolynomial.map (Int.castRingHom R)) hc
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, genericStandardMinorProduct_map,
    genericMinorProduct_map, Int.coe_castRingHom] using h

/-- Full maximal-minor straightening over every commutative ring, with
all row counts, column counts, and factor counts retained. -/
theorem genericMinorProduct_mem_span_standard_all
    {R : Type*} [CommRing R] (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := R) I ∈ Submodule.span R
      (Set.range (genericStandardMinorProduct (K := R) (s := s) (n := n) (r := r))) := by
  obtain ⟨c,hc⟩ := genericMinorProduct_integer_expansion I
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  exact ⟨fun C => (c C : R), genericMinorProduct_integer_expansion_map I c hc⟩

/-- The same standard products are independent over every field; this
uses their actual distinct monic polynomial leading terms. -/
theorem genericStandardProducts_linearIndependent
    {K : Type*} [Field K] (s n r : ℕ) :
    LinearIndependent K (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r)) :=
  linearIndependent_of_weightMonic (bandEntryWeight s n) _ _
    standardChainDiagonalExponent_injective genericStandardMinorProduct_weightMonic

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0191

section TAF_LiteralSource_0192
/- Original module: PaperVerification.AlternatingFormsIntervalBasis -/


/-!
# The actual interval Plücker quotient has its standard-monomial basis

Integral generic-minor straightening gives spanning over every field in
the quotient by the actual generic-minor kernel. Forbidden coordinates then delete precisely
the chains outside the interval. Distinct diagonal monomials in the literal
band matrix prove independence and identify the full kernel of its minor map.
The row count is positive, as in the Grassmannians of the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n r : ℕ}

def pluckerWord (I : Fin r → PluckerIndex s n) : MvPolynomial (PluckerIndex s n) K :=
  ∏ j, X (I j)

def standardPluckerWord (C : StandardMinorChain s n r) :
    MvPolynomial (PluckerIndex s n) K :=
  pluckerWord (fun j => ⟨C.val j,C.property.1 j⟩)

theorem genericPluckerMap_word (I : Fin r → PluckerIndex s n) :
    genericPluckerMap (K := K) (pluckerWord I) =
      genericMinorProduct (fun j => (I j).val) := by
  simp only [pluckerWord,genericPluckerMap,map_prod,aeval_X,genericPluckerMinor,
    genericMinorProduct]

theorem genericPluckerMap_standardWord (C : StandardMinorChain s n r) :
    genericPluckerMap (K := K) (standardPluckerWord C) = genericStandardMinorProduct C :=
  genericPluckerMap_word _

def intervalAllStandardProduct (α β : Fin s → Fin n)
    (C : Σ r, BandChain α β r) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β :=
  intervalStandardProduct α β C.2

def intervalStandardSpan (α β : Fin s → Fin n) :
    Submodule K (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  Submodule.span K (Set.range (intervalAllStandardProduct (K := K) α β))

theorem standardWord_quotient_mem_intervalSpan (α β : Fin s → Fin n)
    (C : StandardMinorChain s n r) :
    Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (standardPluckerWord (K := K) C) ∈
      intervalStandardSpan α β := by
  classical
  by_cases hC : ∀ j i, α i ≤ C.val j i ∧ C.val j i ≤ β i
  · exact Submodule.subset_span
      ⟨⟨r,⟨C.val,C.property.1,hC,C.property.2⟩⟩,rfl⟩
  · obtain ⟨j,hj⟩ := not_forall.mp hC
    have hz : Ideal.Quotient.mk (intervalPluckerIdeal (K := K) α β)
        (X (⟨C.val j,C.property.1 j⟩ : PluckerIndex s n)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Submodule.mem_sup_right (Ideal.subset_span ⟨_,hj,rfl⟩)
    have hprod : Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
        (standardPluckerWord (K := K) C) = 0 := by
      simp only [standardPluckerWord,pluckerWord,map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    rw [hprod]
    exact (intervalStandardSpan α β).zero_mem

/-- Every word of any length straightens in the actual interval quotient. -/
theorem pluckerWord_quotient_mem_intervalSpan (α β : Fin s → Fin n)
    (I : Fin r → PluckerIndex s n) :
    Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (pluckerWord (K := K) I) ∈
      intervalStandardSpan α β := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (genericMinorProduct_mem_span_standard_all (R := K) (fun j => (I j).val))
  let p : MvPolynomial (PluckerIndex s n) K :=
    ∑ C : StandardMinorChain s n r, c C • standardPluckerWord C
  have hdiff : pluckerWord I-p ∈ matrixPluckerIdeal (K := K) (s := s) (n := n) := by
    change genericPluckerMap (pluckerWord I-p) = 0
    simp only [p,map_sub,map_sum,map_smul,genericPluckerMap_word,
      genericPluckerMap_standardWord]
    rw [hc,sub_self]
  have heq : Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (pluckerWord I) =
      Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (pluckerWord I) p).mpr (Submodule.mem_sup_left hdiff)
  rw [heq]
  simp only [p,map_sum,map_smul]
  exact (intervalStandardSpan α β).sum_mem fun C hC =>
    (intervalStandardSpan α β).smul_mem (c C)
      (standardWord_quotient_mem_intervalSpan α β C)

theorem intervalStandardSpan_mul_variable (α β : Fin s → Fin n)
    {z : MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β}
    (hz : z ∈ intervalStandardSpan α β) (I : PluckerIndex s n) :
    z * Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (X I) ∈ intervalStandardSpan α β := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨r,C⟩,rfl⟩ := hz
    have h := pluckerWord_quotient_mem_intervalSpan (K := K) α β
      ((Fin.cons I (fun j => (⟨C.val j,C.property.1 j⟩ : PluckerIndex s n))) :
        Fin (r+1) → PluckerIndex s n)
    rw [pluckerWord,Fin.prod_univ_succ] at h
    change Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
      (X I * chainPluckerProduct (K := K) α β C) ∈
        intervalStandardSpan α β at h
    rw [map_mul] at h
    change (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β))
        (chainPluckerProduct (K := K) α β C) *
      (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)) (X I) ∈ intervalStandardSpan α β
    rw [mul_comm]
    exact h
  | zero => simpa only [zero_mul] using (intervalStandardSpan α β).zero_mem
  | add x y hx hy hmx hmy =>
    simpa only [add_mul] using (intervalStandardSpan α β).add_mem hmx hmy
  | smul a x hx hmx =>
    simpa only [smul_mul_assoc] using (intervalStandardSpan α β).smul_mem a hmx

theorem intervalStandardSpan_eq_top (α β : Fin s → Fin n) :
    intervalStandardSpan (K := K) α β = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K (intervalPluckerIdeal α β) z
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 := pluckerWord_quotient_mem_intervalSpan (K := K) α β
      (Fin.elim0 : Fin 0 → PluckerIndex s n)
    simp only [pluckerWord,Fin.prod_univ_zero,map_one] at h1
    have ha := (intervalStandardSpan α β).smul_mem a h1
    simpa only [C_eq_smul_one,map_smul,map_one] using ha
  | add p q hp hq =>
    simpa only [map_add] using (intervalStandardSpan α β).add_mem hp hq
  | mul_X p I hp =>
    simpa only [map_mul] using intervalStandardSpan_mul_variable α β hp I

theorem chainDiagonalExponent_degree (I : Fin r → Fin s → Fin n) :
    Finsupp.weight (fun _ : Fin s × Fin n => (1 : ℕ)) (chainDiagonalExponent I) = r*s := by
  simp only [chainDiagonalExponent,chainTermExponent,minorTermExponent,map_sum,
    Finsupp.weight_single,one_smul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]

theorem allChainDiagonalExponent_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective (fun C : Σ r, BandChain α β r => chainDiagonalExponent C.2.val) := by
  rintro ⟨r,C⟩ ⟨r',C'⟩ h
  have hr := congrArg (Finsupp.weight (fun _ : Fin s × Fin n => (1 : ℕ))) h
  simp only [chainDiagonalExponent_degree] at hr
  have he : r=r' := Nat.eq_of_mul_eq_mul_right hs hr
  subst r'
  have hC : C = C' := chainDiagonalExponent_injective α β h
  cases hC
  rfl

theorem intervalBandProducts_all_linearIndependent (α β : Fin s → Fin n) (hs : 0 < s) :
    LinearIndependent K (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  apply linearIndependent_of_weightMonic (bandEntryWeight s n) _
    (fun C : S => chainDiagonalExponent C.val.2.val)
  · exact (allChainDiagonalExponent_injective α β hs).comp Subtype.val_injective
  · intro C
    exact bandStandardProduct_weightMonic α β C.val.2

/-- The band-minor map is injective on the literal interval quotient. -/
theorem intervalBandMap_injective (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Function.Injective (intervalBandMap (K := K) α β hα hβ) := by
  apply LinearMap.injective_of_linearIndependent
    (f := (intervalBandMap (K := K) α β hα hβ).toLinearMap)
    (show Submodule.span K (Set.range (intervalAllStandardProduct α β)) = ⊤ from
      intervalStandardSpan_eq_top α β)
  have he : (intervalBandMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
    funext C
    exact intervalBandMap_standardProduct α β hα hβ C.2
  rw [he]
  exact intervalBandProducts_all_linearIndependent α β hs

theorem intervalAllStandardProducts_linearIndependent (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    LinearIndependent K (intervalAllStandardProduct (K := K) α β) := by
  apply LinearIndependent.of_comp (intervalBandMap α β hα hβ).toLinearMap
  have he : (intervalBandMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
    funext C
    exact intervalBandMap_standardProduct α β hα hβ C.2
  rw [he]
  exact intervalBandProducts_all_linearIndependent α β hs

theorem intervalPluckerIdeal_eq_bandKernel (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    intervalPluckerIdeal (K := K) α β = RingHom.ker (bandPluckerMap α β).toRingHom := by
  apply le_antisymm (intervalPluckerIdeal_le_kernel α β hα hβ)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply intervalBandMap_injective α β hα hβ hs
  change bandPluckerMap α β p = intervalBandMap α β hα hβ 0
  rw [map_zero]
  exact hp

/-- The primeness clause of Lemma 2.2 for the actual generic-minor presentation. -/
theorem intervalPluckerIdeal_isPrime (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    (intervalPluckerIdeal (K := K) α β).IsPrime := by
  rw [intervalPluckerIdeal_eq_bandKernel α β hα hβ hs]
  exact RingHom.ker_isPrime _

/-- The complete standard-monomial basis, indexed by all interval multichains. -/
def intervalStandardBasis (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Module.Basis (Σ r, BandChain α β r) K
      (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  Module.Basis.mk
    (intervalAllStandardProducts_linearIndependent α β hα hβ hs)
    (by rw [← intervalStandardSpan_eq_top (K := K) α β]; exact le_rfl)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0192

section TAF_LiteralSource_0193
/- Original module: PaperVerification.AlternatingFormsIntervalHilbert -/


/-!
# Every actual graded piece of the interval Plücker quotient

The component is the image of the ordinary homogeneous polynomial submodule
under the literal quotient map. The standard basis in this component is
indexed by multichains of exactly that length. The proof uses homogeneous
projection in the band-matrix polynomial ring and the proved injectivity of
the band map, rather than assigning a grading by definition to a free model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Module

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n r : ℕ}

theorem bandMinor_isHomogeneous (α β I : Fin s → Fin n) :
    (bandMinor (K := K) α β I).IsHomogeneous s := by
  classical
  rw [bandMinor_expansion]
  apply IsHomogeneous.sum
  intro σ hσ
  apply isHomogeneous_monomial
  simp only [Finsupp.degree_eq_weight_one,minorTermExponent,map_sum,
    Finsupp.weight_single,Pi.one_apply,one_smul,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem bandStandardProduct_isHomogeneous (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    (bandStandardProduct (K := K) α β C).IsHomogeneous (s*r) := by
  simpa only [bandStandardProduct,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.mul_comm,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ (fun j => bandMinor (K := K) α β (C.val j))
      (fun _ => s) (fun j hj => bandMinor_isHomogeneous α β (C.val j))

theorem bandPluckerMap_isHomogeneous (α β : Fin s → Fin n)
    (p : MvPolynomial (PluckerIndex s n) K) (hp : p.IsHomogeneous r) :
    (bandPluckerMap α β p).IsHomogeneous (s*r) :=
  hp.aeval _ (fun I => bandMinor_isHomogeneous α β I.val)

theorem chainPluckerProduct_isHomogeneous (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    (chainPluckerProduct (K := K) α β C).IsHomogeneous r := by
  simpa only [chainPluckerProduct,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ
      (fun j => (X ⟨C.val j,C.property.1 j⟩ : MvPolynomial (PluckerIndex s n) K))
      (fun _ => 1) (fun j hj => isHomogeneous_X K _)

def intervalPluckerDegree (α β : Fin s → Fin n) (r : ℕ) :
    Submodule K (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  (homogeneousSubmodule (PluckerIndex s n) K r).map
    (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)).toLinearMap

theorem intervalStandardProduct_mem_degree (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    intervalStandardProduct (K := K) α β C ∈ intervalPluckerDegree α β r :=
  ⟨chainPluckerProduct α β C,chainPluckerProduct_isHomogeneous α β C,rfl⟩

theorem intervalBandMap_projection_lift (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ)
    (q : MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :
    ∃ y ∈ Submodule.span K (Set.range (intervalStandardProduct (K := K) (r := r) α β)),
      intervalBandMap α β hα hβ y =
        homogeneousComponent (s*r) (intervalBandMap α β hα hβ q) := by
  have hq : q ∈ intervalStandardSpan α β := by
    rw [intervalStandardSpan_eq_top]
    trivial
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨⟨l,C⟩,rfl⟩ := hq
    by_cases hl : l=r
    · subst l
      refine ⟨intervalStandardProduct α β C,Submodule.subset_span ⟨C,rfl⟩,?_⟩
      simpa only [intervalAllStandardProduct,intervalBandMap_standardProduct] using
        (homogeneousComponent_eq_self (bandStandardProduct_isHomogeneous (K := K) α β C)).symm
    · refine ⟨0,(Submodule.span K _).zero_mem,?_⟩
      change intervalBandMap α β hα hβ 0 =
        homogeneousComponent (s*r) (intervalBandMap α β hα hβ
          (intervalStandardProduct α β C))
      rw [map_zero,intervalBandMap_standardProduct,
        homogeneousComponent_of_mem (bandStandardProduct_isHomogeneous (K := K) α β C)]
      have hsr : s*r ≠ s*l := fun he => hl (Nat.eq_of_mul_eq_mul_left hs he.symm)
      rw [if_neg hsr]
  | zero =>
    exact ⟨0,(Submodule.span K _).zero_mem,by simp only [map_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x',hx',heqx⟩ := ihx
    obtain ⟨y',hy',heqy⟩ := ihy
    exact ⟨x'+y',(Submodule.span K _).add_mem hx' hy',by
      simp only [map_add,heqx,heqy]⟩
  | smul a x hx ih =>
    obtain ⟨x',hx',heq⟩ := ih
    exact ⟨a • x',(Submodule.span K _).smul_mem a hx',by simp only [map_smul,heq]⟩

theorem intervalPluckerDegree_eq_standardSpan (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    intervalPluckerDegree (K := K) α β r =
      Submodule.span K (Set.range (intervalStandardProduct (K := K) (r := r) α β)) := by
  apply le_antisymm
  · rintro q ⟨p,hp,rfl⟩
    obtain ⟨y,hy,heq⟩ := intervalBandMap_projection_lift α β hα hβ hs r
      (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p)
    change intervalBandMap α β hα hβ y =
      homogeneousComponent (s*r) (bandPluckerMap α β p) at heq
    rw [homogeneousComponent_eq_self (bandPluckerMap_isHomogeneous α β p hp)] at heq
    have hyq : y = Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p :=
      intervalBandMap_injective α β hα hβ hs heq
    rwa [hyq] at hy
  · apply Submodule.span_le.mpr
    rintro q ⟨C,rfl⟩
    exact intervalStandardProduct_mem_degree α β C

def intervalPluckerDegreeBasis (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    Basis (BandChain α β r) K (intervalPluckerDegree (K := K) α β r) :=
  (Basis.span (intervalStandardProducts_linearIndependent (K := K) α β hα hβ r)).map
    (LinearEquiv.ofEq _ _ (intervalPluckerDegree_eq_standardSpan α β hα hβ hs r).symm)

@[simp] theorem intervalPluckerDegreeBasis_apply (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) (C : BandChain α β r) :
    (intervalPluckerDegreeBasis (K := K) α β hα hβ hs r C :
      MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) =
      intervalStandardProduct α β C := by
  simp only [intervalPluckerDegreeBasis,Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Basis.coe_span_apply]

/-- The Hilbert function in Lemma 2.2, expressed by the exact multichain count
of its actual degree-r quotient component. -/
theorem intervalPluckerDegree_finrank (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    Module.finrank K (intervalPluckerDegree (K := K) α β r) = Fintype.card (BandChain α β r) :=
  Module.finrank_eq_card_basis (intervalPluckerDegreeBasis α β hα hβ hs r)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0193

section TAF_LiteralSource_0194
/- Original module: PaperVerification.AlternatingFormsNormalizedBand -/


/-!
# A polynomial normalization of the interval band matrix

Each leftmost allowed entry is specialized to one. One additional variable
multiplies row zero and records the Plücker degree. The missing pivot exponents
of a standard product are recovered from that degree and the other entries in
their row. Consequently the specialization is injective on the actual interval
Plücker ring. It uses exactly `1 + ∑ i, (β i - α i)` polynomial variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

section SupportExpansion

variable {K σ ι : Type*} [Field K] [Fintype ι]

theorem isWeightMonic_of_supported_finite_expansion
    (w : σ → ℤ) (p : MvPolynomial σ K) (a : ι → σ →₀ ℕ) (c : ι → K) (i₀ : ι)
    (hp : p = ∑ i, monomial (a i) (c i)) (hc : c i₀ = 1)
    (hlt : ∀ i, i ≠ i₀ → c i ≠ 0 →
      Finsupp.weight w (a i) < Finsupp.weight w (a i₀)) :
    IsWeightMonic w p (a i₀) := by
  classical
  constructor
  · rw [hp,coeff_sum,Finset.sum_eq_single i₀]
    · simp only [coeff_monomial,ite_true,hc]
    · intro i hi hne
      by_cases hci : c i = 0
      · simp only [hci,monomial_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]
      · have ha : a i ≠ a i₀ := by
          intro he
          have h := hlt i hne hci
          rw [he] at h
          exact (lt_irrefl _ h)
        simp only [coeff_monomial,if_neg ha]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  · intro b hba hweight
    rw [hp,coeff_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hci : c i = 0
    · simp only [hci,monomial_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]
    · have hab : a i ≠ b := by
        intro he
        by_cases hei : i=i₀
        · subst i
          exact hba he.symm
        · have h := hlt i hei hci
          rw [he] at h
          exact (not_lt_of_ge hweight h)
      simp only [coeff_monomial,if_neg hab]

end SupportExpansion

variable {K : Type*} [Field K] {s n r : ℕ}

abbrev BandNonpivot (α β : Fin s → Fin n) :=
  (i : Fin s) × {j : Fin n // α i < j ∧ j ≤ β i}

abbrev NormalizedBandVariable (α β : Fin s → Fin n) := Option (BandNonpivot α β)

def normalizedEntryExponent (α β : Fin s → Fin n) (a : Fin s × Fin n) :
    NormalizedBandVariable α β →₀ ℕ :=
  (if a.1.val=0 then Finsupp.single none 1 else 0) +
    if h : α a.1 < a.2 ∧ a.2 ≤ β a.1 then
      Finsupp.single (some ⟨a.1,⟨a.2,h⟩⟩) 1 else 0

def normalizeBand (α β : Fin s → Fin n) :
    MvPolynomial (Fin s × Fin n) K →ₐ[K]
      MvPolynomial (NormalizedBandVariable α β) K :=
  aeval fun a => monomial (normalizedEntryExponent α β a) 1

def normalizedEntryWeight (α β : Fin s → Fin n) : NormalizedBandVariable α β → ℤ
  | none => 0
  | some a => (a.1.val : ℤ) * (a.2.val.val : ℤ) -
      (a.1.val : ℤ) * ((α a.1).val : ℤ)

def normalizedMinorTermExponent (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s)) : NormalizedBandVariable α β →₀ ℕ :=
  ∑ i, normalizedEntryExponent α β (σ i,I i)

def normalizedChainTermExponent (α β : Fin s → Fin n) (I : Fin r → Fin s → Fin n)
    (σ : Fin r → Equiv.Perm (Fin s)) : NormalizedBandVariable α β →₀ ℕ :=
  ∑ t, normalizedMinorTermExponent α β (I t) (σ t)

def normalizedDiagonalExponent (α β : Fin s → Fin n) (I : Fin r → Fin s → Fin n) :
    NormalizedBandVariable α β →₀ ℕ :=
  normalizedChainTermExponent α β I (fun _ => 1)

theorem normalizeBand_entry (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) :
    normalizeBand (K := K) α β (bandMatrix α β i j) =
      monomial (normalizedEntryExponent α β (i,j)) (bandEntryCoefficient α β i j) := by
  simp only [normalizeBand,bandMatrix,aeval_monomial,MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_single_index (by simp)]
  simp only [pow_one,C_mul_monomial,mul_one]

theorem normalizeBand_minor_expansion (α β I : Fin s → Fin n) :
    normalizeBand (K := K) α β (bandMinor α β I) =
      ∑ σ : Equiv.Perm (Fin s),
        monomial (normalizedMinorTermExponent α β I σ) (minorTermCoefficient α β I σ) := by
  classical
  rw [bandMinor,AlgHom.map_det,Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [AlgHom.mapMatrix_apply,Matrix.map_apply,Matrix.submatrix_apply,id_eq,normalizeBand_entry,
    prod_monomial_eq_monomial_sum,smul_monomial,
    normalizedMinorTermExponent,minorTermCoefficient]

theorem normalizeBand_standard_expansion (α β : Fin s → Fin n) (C : BandChain α β r) :
    normalizeBand (K := K) α β (bandStandardProduct α β C) =
      ∑ σ : Fin r → Equiv.Perm (Fin s),
        monomial (normalizedChainTermExponent α β C.val σ)
          (chainTermCoefficient α β C.val σ) := by
  classical
  simp only [bandStandardProduct,map_prod,normalizeBand_minor_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prod_monomial_eq_monomial_sum _ _

theorem normalizedEntryExponent_weight (α β : Fin s → Fin n) (i : Fin s) (j : Fin n)
    (h : α i ≤ j ∧ j ≤ β i) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedEntryExponent α β (i,j)) =
      (i.val : ℤ) * (j.val : ℤ) - (i.val : ℤ) * ((α i).val : ℤ) := by
  classical
  rcases h.1.eq_or_lt with he | he
  · subst j
    by_cases hi : i.val=0 <;>
      simp [normalizedEntryExponent,normalizedEntryWeight,hi,Finsupp.weight_single]
  · by_cases hi : i.val=0 <;>
      simp [normalizedEntryExponent,normalizedEntryWeight,he,h.2,hi,Finsupp.weight_single]

theorem minorTermCoefficient_ne_zero_allowed (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s))
    (h : minorTermCoefficient (K := K) α β I σ ≠ 0) (i : Fin s) :
    α (σ i) ≤ I i ∧ I i ≤ β (σ i) := by
  classical
  by_contra hi
  apply h
  have hz : ∏ j, bandEntryCoefficient (K := K) α β (σ j) (I j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [bandEntryCoefficient,if_neg hi])
  simp only [minorTermCoefficient,hz,smul_zero]

theorem normalizedMinorTermExponent_weight (α β I : Fin s → Fin n)
    (σ : Equiv.Perm (Fin s))
    (h : minorTermCoefficient (K := K) α β I σ ≠ 0) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedMinorTermExponent α β I σ) =
      Finsupp.weight (bandEntryWeight s n) (minorTermExponent I σ) -
        ∑ i, (i.val : ℤ) * ((α i).val : ℤ) := by
  simp only [normalizedMinorTermExponent,map_sum,
    normalizedEntryExponent_weight α β _ _ (minorTermCoefficient_ne_zero_allowed α β I σ h _),
    Finset.sum_sub_distrib,minorTermExponent_weight]
  rw [Equiv.sum_comp σ (fun i => (i.val : ℤ) * ((α i).val : ℤ))]

theorem normalizedChainTermExponent_weight (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (σ : Fin r → Equiv.Perm (Fin s))
    (h : chainTermCoefficient (K := K) α β I σ ≠ 0) :
    Finsupp.weight (normalizedEntryWeight α β) (normalizedChainTermExponent α β I σ) =
      Finsupp.weight (bandEntryWeight s n) (chainTermExponent I σ) -
        (r : ℤ) * ∑ i, (i.val : ℤ) * ((α i).val : ℤ) := by
  classical
  have ht (t : Fin r) : minorTermCoefficient (K := K) α β (I t) (σ t) ≠ 0 := by
    intro hz
    apply h
    exact Finset.prod_eq_zero (Finset.mem_univ t) hz
  simp only [normalizedChainTermExponent,chainTermExponent,map_sum,
    normalizedMinorTermExponent_weight α β _ _ (ht _),Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem normalizeBand_standard_weightMonic (α β : Fin s → Fin n) (C : BandChain α β r) :
    IsWeightMonic (normalizedEntryWeight α β)
      (normalizeBand (K := K) α β (bandStandardProduct α β C))
      (normalizedDiagonalExponent α β C.val) := by
  have hc : chainTermCoefficient (K := K) α β C.val (fun _ => 1) = 1 := by
    simp only [chainTermCoefficient,
      minorTermCoefficient_diagonal α β _ (C.property.2.1 _),Finset.prod_const_one]
  apply isWeightMonic_of_supported_finite_expansion _ _ _ _ (fun _ => 1)
    (normalizeBand_standard_expansion α β C) hc
  intro σ hσ hnonzero
  rw [normalizedChainTermExponent_weight α β C.val σ hnonzero,
    normalizedChainTermExponent_weight α β C.val (fun _ => 1) (by rw [hc]; exact one_ne_zero)]
  exact sub_lt_sub_right
    (chainTermExponent_weight_lt_diagonal C.val C.property.1 σ hσ) _

@[simp] theorem normalizedEntryExponent_none (α β : Fin s → Fin n) (a : Fin s × Fin n) :
    normalizedEntryExponent α β a none = if a.1.val=0 then 1 else 0 := by
  classical
  simp only [normalizedEntryExponent,Finsupp.add_apply]
  split_ifs <;> simp [Finsupp.single_apply]

@[simp] theorem normalizedEntryExponent_some (α β : Fin s → Fin n)
    (a : Fin s × Fin n) (b : BandNonpivot α β) :
    normalizedEntryExponent α β a (some b) = if a=(b.1,b.2.val) then 1 else 0 := by
  classical
  have hnone : (if a.1.val=0 then Finsupp.single none 1 else
      (0 : NormalizedBandVariable α β →₀ ℕ)) (some b) = 0 := by
    split_ifs <;> simp [Finsupp.single_apply]
  rw [normalizedEntryExponent,Finsupp.add_apply,hnone,zero_add]
  by_cases ha : α a.1 < a.2 ∧ a.2 ≤ β a.1
  · rw [dif_pos ha,Finsupp.single_apply]
    have he : (some ⟨a.1,⟨a.2,ha⟩⟩ : NormalizedBandVariable α β) = some b ↔
        a = (b.1,b.2.val) := by
      constructor
      · intro h
        have h' := Option.some.inj h
        exact Prod.ext (congrArg Sigma.fst h')
          (congrArg (fun x : BandNonpivot α β => x.2.val) h')
      · intro h
        rcases a with ⟨i,j⟩
        cases h
        rfl
    simp only [he]
  · rw [dif_neg ha,Finsupp.zero_apply]
    symm
    apply if_neg
    intro he
    apply ha
    simpa only [he] using b.2.property

theorem normalizedDiagonalExponent_none (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (hs : 0 < s) :
    normalizedDiagonalExponent α β I none = r := by
  classical
  have hsum : (∑ i : Fin s, if i.val=0 then 1 else 0 : ℕ) = 1 := by
    let z : Fin s := ⟨0,hs⟩
    rw [Finset.sum_eq_single z]
    · simp only [z,ite_true]
    · intro i hi hiz
      rw [if_neg (fun hi0 => hiz (Fin.ext hi0))]
    · intro hz
      exact (hz (Finset.mem_univ _)).elim
  simp only [normalizedDiagonalExponent,normalizedChainTermExponent,
    normalizedMinorTermExponent,Finset.sum_apply',Equiv.Perm.one_apply,
    normalizedEntryExponent_none,hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]

theorem normalizedDiagonalExponent_some (α β : Fin s → Fin n)
    (I : Fin r → Fin s → Fin n) (b : BandNonpivot α β) :
    normalizedDiagonalExponent α β I (some b) = chainDiagonalExponent I (b.1,b.2.val) := by
  classical
  simp only [normalizedDiagonalExponent,normalizedChainTermExponent,normalizedMinorTermExponent,
    chainDiagonalExponent,chainTermExponent,minorTermExponent,Finset.sum_apply',
    Equiv.Perm.one_apply,normalizedEntryExponent_some,Finsupp.single_apply]

theorem chainDiagonalExponent_row_sum (I : Fin r → Fin s → Fin n) (i : Fin s) :
    ∑ j : Fin n, chainDiagonalExponent I (i,j) = r := by
  classical
  simp only [chainDiagonalExponent,chainTermExponent,minorTermExponent,
    Finset.sum_apply',Equiv.Perm.one_apply]
  rw [Finset.sum_comm]
  have ht (t : Fin r) : (∑ j : Fin n, ∑ a : Fin s,
      Finsupp.single (a,I t a) 1 (i,j)) = 1 := by
    rw [Finset.sum_comm,Finset.sum_eq_single i]
    · simp [Finsupp.single_apply]
    · intro a ha hai
      simp [Finsupp.single_apply,hai]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  simp only [ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem chainDiagonalExponent_outside (α β : Fin s → Fin n) (C : BandChain α β r)
    (i : Fin s) (j : Fin n) (h : ¬ (α i ≤ j ∧ j ≤ β i)) :
    chainDiagonalExponent C.val (i,j) = 0 := by
  classical
  rw [chainDiagonalExponent_apply,List.count_eq_zero]
  intro hj
  obtain ⟨t,ht⟩ := List.mem_ofFn.mp hj
  exact h (ht ▸ C.property.2.1 t i)

theorem normalizedDiagonalExponent_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective
      (fun C : Σ r, BandChain α β r => normalizedDiagonalExponent α β C.2.val) := by
  classical
  rintro ⟨r,C⟩ ⟨r',D⟩ h
  have hr := congrArg (fun a => a none) h
  simp only [normalizedDiagonalExponent_none α β _ hs] at hr
  subst r'
  have hnon (i : Fin s) (j : Fin n) (hj : j ≠ α i) :
      chainDiagonalExponent C.val (i,j) = chainDiagonalExponent D.val (i,j) := by
    by_cases hb : α i ≤ j ∧ j ≤ β i
    · let b : BandNonpivot α β := ⟨i,⟨j,lt_of_le_of_ne hb.1 (Ne.symm hj),hb.2⟩⟩
      simpa only [normalizedDiagonalExponent_some] using congrArg (fun a => a (some b)) h
    · rw [chainDiagonalExponent_outside α β C i j hb,
        chainDiagonalExponent_outside α β D i j hb]
  have he : chainDiagonalExponent C.val = chainDiagonalExponent D.val := by
    ext a
    rcases a with ⟨i,j⟩
    by_cases hj : j=α i
    · subst j
      have hrow := (chainDiagonalExponent_row_sum C.val i).trans
        (chainDiagonalExponent_row_sum D.val i).symm
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (α i)),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ (α i))] at hrow
      have hrest : ∑ j ∈ Finset.univ.erase (α i), chainDiagonalExponent C.val (i,j) =
          ∑ j ∈ Finset.univ.erase (α i), chainDiagonalExponent D.val (i,j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hnon i j (Finset.mem_erase.mp hj).1
      rw [hrest] at hrow
      exact Nat.add_left_cancel hrow
    · exact hnon i j hj
  have hCD := chainDiagonalExponent_injective α β he
  cases hCD
  rfl

theorem normalizedStandardProducts_linearIndependent (α β : Fin s → Fin n) (hs : 0 < s) :
    LinearIndependent K (fun C : Σ r, BandChain α β r =>
      normalizeBand (K := K) α β (bandStandardProduct α β C.2)) := by
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact linearIndependent_of_weightMonic (normalizedEntryWeight α β) _ _
    ((normalizedDiagonalExponent_injective α β hs).comp Subtype.val_injective)
    (fun C => normalizeBand_standard_weightMonic α β C.val.2)

def normalizedIntervalMap (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β →ₐ[K]
      MvPolynomial (NormalizedBandVariable α β) K :=
  (normalizeBand α β).comp (intervalBandMap α β hα hβ)

theorem normalizedIntervalMap_injective (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Function.Injective (normalizedIntervalMap (K := K) α β hα hβ) := by
  apply LinearMap.injective_of_linearIndependent
    (f := (normalizedIntervalMap (K := K) α β hα hβ).toLinearMap)
    (show Submodule.span K (Set.range (intervalAllStandardProduct α β)) = ⊤ from
      intervalStandardSpan_eq_top α β)
  have he : (normalizedIntervalMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => normalizeBand α β (bandStandardProduct α β C.2)) := by
    funext C
    change normalizeBand α β (intervalBandMap α β hα hβ (intervalStandardProduct α β C.2)) = _
    rw [intervalBandMap_standardProduct]
  rw [he]
  exact normalizedStandardProducts_linearIndependent α β hs

theorem normalizedBandVariable_card (α β : Fin s → Fin n) :
    Fintype.card (NormalizedBandVariable α β) = 1 + ∑ i, ((β i).val - (α i).val) := by
  classical
  rw [Fintype.card_option,Fintype.card_sigma]
  have hcard (i : Fin s) : Fintype.card {j : Fin n // α i < j ∧ j ≤ β i} =
      (β i).val - (α i).val := by
    let e : {j : Fin n // α i < j ∧ j ≤ β i} ≃ Finset.Ioc (α i) (β i) :=
      Equiv.subtypeEquivRight fun j => Finset.mem_Ioc.symm
    simpa only [Fintype.card_coe,Fin.card_Ioc] using Fintype.card_congr e
  simp only [hcard,Nat.add_comm]

theorem intervalPlucker_krullDim_le (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    ringKrullDim (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) ≤
      (1 + ∑ i, ((β i).val - (α i).val) : ℕ) := by
  letI := intervalPluckerIdeal_isPrime (K := K) α β hα hβ hs
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg K]
  have h := trdeg_le_of_injective (normalizedIntervalMap (K := K) α β hα hβ)
    (normalizedIntervalMap_injective α β hα hβ hs)
  rw [MvPolynomial.trdeg_of_isDomain] at h
  have hn := Cardinal.toNat_le_toNat h
    (Cardinal.lift_lt_aleph0.mpr (Cardinal.mk_lt_aleph0 (α := NormalizedBandVariable α β)))
  have hn' : (Algebra.trdeg K
      (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)).toNat ≤
        1 + ∑ i, ((β i).val - (α i).val) := by
    simpa only [Cardinal.toNat_lift,Cardinal.mk_toNat_eq_card,normalizedBandVariable_card]
      using hn
  exact_mod_cast hn'

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0194

section TAF_LiteralSource_0195
/- Original module: PaperVerification.AlternatingFormsWeightAlgebraic -/


/-!
# Algebraic independence from distinct weighted leading monomials

The criterion uses the actual multiplication and evaluation maps. It applies
to integer weights, with no term-order assumption: the support of each
individual polynomial is finite, and its displayed top term is unique.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K σ ι : Type*} [Field K]

theorem IsWeightMonic.weight_le {w : σ → ℤ} {p : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hb : p.coeff b ≠ 0) :
    Finsupp.weight w b ≤ Finsupp.weight w a := by
  by_contra h
  have hlt := lt_of_not_ge h
  exact hb (hp.2 b (fun he => hlt.ne (congrArg (Finsupp.weight w) he).symm) hlt.le)

theorem IsWeightMonic.eq_of_weight_ge {w : σ → ℤ} {p : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hb : p.coeff b ≠ 0)
    (hw : Finsupp.weight w a ≤ Finsupp.weight w b) : b=a := by
  by_contra he
  exact hb (hp.2 b he hw)

theorem IsWeightMonic.mul {w : σ → ℤ} {p q : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hq : IsWeightMonic w q b) :
    IsWeightMonic w (p*q) (a+b) := by
  classical
  have hterm {z : σ →₀ ℕ} (x : (σ →₀ ℕ) × (σ →₀ ℕ))
      (hx : x.1+x.2=z) (hc : p.coeff x.1 * q.coeff x.2 ≠ 0)
      (hw : Finsupp.weight w (a+b) ≤ Finsupp.weight w z) : x=(a,b) := by
    have hp0 := (mul_ne_zero_iff.mp hc).1
    have hq0 := (mul_ne_zero_iff.mp hc).2
    have hpw := hp.weight_le hp0
    have hqw := hq.weight_le hq0
    have hsum := congrArg (Finsupp.weight w) hx
    simp only [map_add] at hsum hw
    have hpa : x.1=a := hp.eq_of_weight_ge hp0 (by linarith)
    have hqb : x.2=b := hq.eq_of_weight_ge hq0 (by linarith)
    exact Prod.ext hpa hqb
  constructor
  · rw [MvPolynomial.coeff_mul,Finset.sum_eq_single (a,b)]
    · rw [hp.1,hq.1,mul_one]
    · intro x hx hne
      by_contra hc
      exact hne (hterm x (Finset.mem_antidiagonal.mp hx) hc le_rfl)
    · intro hab
      exact (hab (Finset.mem_antidiagonal.mpr rfl)).elim
  · intro z hza hw
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    by_contra hc
    have he := hterm x (Finset.mem_antidiagonal.mp hx) hc hw
    have hz := Finset.mem_antidiagonal.mp hx
    rw [he] at hz
    exact hza hz.symm

theorem isWeightMonic_one (w : σ → ℤ) : IsWeightMonic w (1 : MvPolynomial σ K) 0 := by
  classical
  constructor
  · simp
  · intro b hb hw
    simp [MvPolynomial.coeff_one,hb,Ne.symm hb]

theorem IsWeightMonic.pow {w : σ → ℤ} {p : MvPolynomial σ K} {a : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (n : ℕ) : IsWeightMonic w (p^n) (n • a) := by
  induction n with
  | zero => simpa only [pow_zero,zero_smul] using isWeightMonic_one (K := K) w
  | succ n ih =>
    simpa only [pow_succ,succ_nsmul] using ih.mul hp

theorem isWeightMonic_prod {w : σ → ℤ} (S : Finset ι)
    (p : ι → MvPolynomial σ K) (a : ι → σ →₀ ℕ)
    (hp : ∀ i ∈ S, IsWeightMonic w (p i) (a i)) :
    IsWeightMonic w (∏ i ∈ S, p i) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using isWeightMonic_one (K := K) w
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

theorem algebraicIndependent_of_weightMonic
    (w : σ → ℤ) (p : ι → MvPolynomial σ K) (a : ι → σ →₀ ℕ)
    (hp : ∀ i, IsWeightMonic w (p i) (a i))
    (ha : Function.Injective (Finsupp.linearCombination ℕ a)) :
    AlgebraicIndependent K p := by
  classical
  change Function.Injective (aeval (R := K) p)
  apply LinearMap.injective_of_linearIndependent (f := (aeval (R := K) p).toLinearMap)
    (MvPolynomial.basisMonomials ι K).span_eq
  have hmon (d : ι →₀ ℕ) :
      IsWeightMonic w (aeval (R := K) p (monomial d 1)) (Finsupp.linearCombination ℕ a d) := by
    rw [aeval_monomial,map_one,one_mul]
    exact isWeightMonic_prod d.support (fun i => p i ^ d i) (fun i => d i • a i)
      (fun i hi => (hp i).pow (d i))
  rw [MvPolynomial.coe_basisMonomials]
  change LinearIndependent K (fun d : ι →₀ ℕ => aeval (R := K) p (monomial d 1))
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact linearIndependent_of_weightMonic (K := K) w
    (fun d : S => aeval (R := K) p (monomial d.val 1))
    (fun d : S => Finsupp.linearCombination ℕ a d.val)
    (ha.comp Subtype.val_injective) (fun d => hmon d.val)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0195

section TAF_LiteralSource_0196
/- Original module: PaperVerification.AlternatingFormsIntervalDimension -/


/-!
# The dimension of the actual interval Plücker quotient

The lower bound uses the right-to-left saturated interval chain. Its normalized
diagonal exponents form a triangular integral matrix: each nonpivot coordinate
has coefficient one on its own chain member and can occur additionally only
in members with an earlier row. This proves algebraic independence over the
original field. Together with the normalized-band embedding it gives the exact
Krull dimension in Lemma 2.2.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

def intervalPathColumn (α β : Fin s → Fin n) :
    NormalizedBandVariable α β → Fin s → Fin n
  | none => α
  | some a => fun i => if i<a.1 then α i else if i=a.1 then a.2.val else β i

theorem intervalPathColumn_mem (α β : Fin s → Fin n) (hab : ∀ i, α i ≤ β i)
    (x : NormalizedBandVariable α β) (i : Fin s) :
    α i ≤ intervalPathColumn α β x i ∧ intervalPathColumn α β x i ≤ β i := by
  cases x with
  | none => exact ⟨le_rfl,hab i⟩
  | some a =>
    simp only [intervalPathColumn]
    split_ifs with hia hie
    · exact ⟨le_rfl,hab i⟩
    · subst i
      exact ⟨a.2.property.1.le,a.2.property.2⟩
    · exact ⟨hab i,le_rfl⟩

theorem intervalPathColumn_strictMono (α β : Fin s → Fin n)
    (hα : StrictMono α) (hβ : StrictMono β) (hab : ∀ i, α i ≤ β i)
    (x : NormalizedBandVariable α β) : StrictMono (intervalPathColumn α β x) := by
  cases x with
  | none => exact hα
  | some a =>
    intro i j hij
    change (if i<a.1 then α i else if i=a.1 then a.2.val else β i) <
      (if j<a.1 then α j else if j=a.1 then a.2.val else β j)
    by_cases hi : i<a.1
    · rw [if_pos hi]
      by_cases hj : j<a.1
      · rw [if_pos hj]
        exact hα hij
      · rw [if_neg hj]
        by_cases he : j=a.1
        · rw [if_pos he]
          exact lt_of_lt_of_le (hα (he ▸ hij)) a.2.property.1.le
        · rw [if_neg he]
          exact lt_of_lt_of_le (hα hij) (hab j)
    · have hj : ¬ j<a.1 := not_lt_of_ge (le_trans (le_of_not_gt hi) hij.le)
      have hja : j≠a.1 := ne_of_gt (lt_of_le_of_lt (le_of_not_gt hi) hij)
      rw [if_neg hi,if_neg hj,if_neg hja]
      by_cases he : i=a.1
      · rw [if_pos he]
        exact lt_of_le_of_lt a.2.property.2 (hβ (he ▸ hij))
      · rw [if_neg he]
        exact hβ hij

def intervalPathExponent (α β : Fin s → Fin n) (x : NormalizedBandVariable α β) :
    NormalizedBandVariable α β →₀ ℕ :=
  normalizedMinorTermExponent α β (intervalPathColumn α β x) 1

theorem intervalPathExponent_none (α β : Fin s → Fin n) (hs : 0 < s)
    (x : NormalizedBandVariable α β) : intervalPathExponent α β x none = 1 := by
  simpa only [normalizedDiagonalExponent,normalizedChainTermExponent,Fin.sum_univ_one,
    intervalPathExponent] using
    normalizedDiagonalExponent_none α β (fun _ : Fin 1 => intervalPathColumn α β x) hs

theorem normalizedMinorTermExponent_diagonal_some (α β I : Fin s → Fin n)
    (b : BandNonpivot α β) :
    normalizedMinorTermExponent α β I 1 (some b) = if I b.1=b.2.val then 1 else 0 := by
  classical
  simp only [normalizedMinorTermExponent,Finset.sum_apply',Equiv.Perm.one_apply,
    normalizedEntryExponent_some]
  rw [Finset.sum_eq_single b.1]
  · simp only [Prod.mk.injEq,true_and]
  · intro i hi hib
    simp only [Prod.mk.injEq,hib,false_and,ite_false]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

theorem intervalPathExponent_some (α β : Fin s → Fin n)
    (x : NormalizedBandVariable α β) (b : BandNonpivot α β) :
    intervalPathExponent α β x (some b) = (if x=some b then 1 else 0) +
      match x with
      | none => 0
      | some a => if a.1<b.1 ∧ b.2.val=β b.1 then 1 else 0 := by
  classical
  rw [intervalPathExponent,normalizedMinorTermExponent_diagonal_some]
  cases x with
  | none => simp only [intervalPathColumn,b.2.property.1.ne,ite_false,reduceCtorEq,zero_add]
  | some a =>
    by_cases hrow : a.1=b.1
    · rcases a with ⟨i,j,hj⟩
      rcases b with ⟨i',j',hj'⟩
      dsimp at hrow
      subst i'
      simp [intervalPathColumn,lt_irrefl,Subtype.ext_iff]
    · by_cases hlt : a.1<b.1
      · simp [intervalPathColumn,not_lt_of_ge hlt.le,Ne.symm hrow,hrow,hlt,
          eq_comm,show a ≠ b from fun h => hrow (congrArg Sigma.fst h),
          show b ≠ a from fun h => hrow (congrArg Sigma.fst h.symm)]
      · have hgt : b.1<a.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hrow)
        simp [intervalPathColumn,hgt,hlt,b.2.property.1.ne,
          show a ≠ b from fun h => hrow (congrArg Sigma.fst h)]

def earlierPathCount (α β : Fin s → Fin n)
    (c : NormalizedBandVariable α β →₀ ℕ) (i : Fin s) : ℕ :=
  ∑ a : BandNonpivot α β, if a.1 < i then c (some a) else 0

theorem intervalPathCombination_none (α β : Fin s → Fin n) (hs : 0 < s)
    (c : NormalizedBandVariable α β →₀ ℕ) :
    Finsupp.linearCombination ℕ (intervalPathExponent α β) c none =
      ∑ x, c x := by
  classical
  rw [Finsupp.linearCombination_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,
    intervalPathExponent_none α β hs,mul_one]

theorem intervalPathCombination_some (α β : Fin s → Fin n)
    (c : NormalizedBandVariable α β →₀ ℕ) (b : BandNonpivot α β) :
    Finsupp.linearCombination ℕ (intervalPathExponent α β) c (some b) =
      c (some b) + if b.2.val=β b.1 then earlierPathCount α β c b.1 else 0 := by
  classical
  rw [Finsupp.linearCombination_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,
    intervalPathExponent_some,mul_add,Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (some b)]
  · simp only [ite_true,mul_one]
    congr 1
    rw [Fintype.sum_option]
    by_cases hb : b.2.val=β b.1
    · simp [hb,earlierPathCount,mul_ite]
    · simp [hb]
  · intro x hx hxb
    rw [if_neg hxb,mul_zero]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

theorem intervalPathCombination_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective (Finsupp.linearCombination ℕ (intervalPathExponent α β)) := by
  classical
  intro c d h
  have hrow (k : ℕ) : ∀ i : Fin s, i.val=k →
      ∀ j : {j : Fin n // α i<j ∧ j≤β i}, c (some ⟨i,j⟩)=d (some ⟨i,j⟩) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi j
      have hearlier : earlierPathCount α β c i = earlierPathCount α β d i := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hai : a.1 < i
        · rw [if_pos hai,if_pos hai]
          exact ih a.1.val (by simpa only [← hi,Fin.lt_def] using hai) a.1 rfl a.2
        · rw [if_neg hai,if_neg hai]
      have he := congrArg (fun a => a (some ⟨i,j⟩)) h
      rw [intervalPathCombination_some,intervalPathCombination_some,hearlier] at he
      exact Nat.add_right_cancel he
  have hsome (a : BandNonpivot α β) : c (some a)=d (some a) :=
    hrow a.1.val a.1 rfl a.2
  apply Finsupp.ext
  intro x
  cases x with
  | some a => exact hsome a
  | none =>
    have he := congrArg (fun a => a none) h
    rw [intervalPathCombination_none α β hs,intervalPathCombination_none α β hs,
      Fintype.sum_option,Fintype.sum_option] at he
    have hsum : ∑ a : BandNonpivot α β, c (some a) = ∑ a, d (some a) :=
      Finset.sum_congr rfl (fun a ha => hsome a)
    rw [hsum] at he
    exact Nat.add_right_cancel he

theorem normalizedPathMinors_algebraicIndependent
    (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    AlgebraicIndependent K (fun x : NormalizedBandVariable α β =>
      normalizeBand (K := K) α β (bandMinor α β (intervalPathColumn α β x))) := by
  apply algebraicIndependent_of_weightMonic (normalizedEntryWeight α β) _
    (intervalPathExponent α β)
  · intro x
    let C : BandChain α β 1 := ⟨fun _ => intervalPathColumn α β x,
      fun _ => intervalPathColumn_strictMono α β hα hβ hab x,
      fun _ => intervalPathColumn_mem α β hab x,
      fun a b hab => le_rfl⟩
    simpa only [bandStandardProduct,Fin.prod_univ_one,normalizedDiagonalExponent,
      normalizedChainTermExponent,Fin.sum_univ_one,intervalPathExponent,C] using
      normalizeBand_standard_weightMonic (K := K) α β C
  · exact intervalPathCombination_injective α β hs

def intervalPathCoordinate (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (x : NormalizedBandVariable α β) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β :=
  Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
    (X ⟨intervalPathColumn α β x,intervalPathColumn_strictMono α β hα hβ hab x⟩)

theorem intervalPathCoordinates_algebraicIndependent
    (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    AlgebraicIndependent K (intervalPathCoordinate (K := K) α β hα hβ hab) := by
  apply AlgebraicIndependent.of_comp (normalizedIntervalMap α β hα.monotone hβ.monotone)
  convert normalizedPathMinors_algebraicIndependent (K := K) α β hα hβ hab hs using 1
  funext x
  change normalizeBand α β (bandPluckerMap α β
    (X ⟨intervalPathColumn α β x,intervalPathColumn_strictMono α β hα hβ hab x⟩)) = _
  apply congrArg (normalizeBand (K := K) α β)
  exact MvPolynomial.aeval_X
    (f := fun I : PluckerIndex s n => bandMinor (K := K) α β I.val) _

/-- The full Krull-dimension clause of Lemma 2.2, for all nonempty intervals
of positive-size subsets and the actual generic-minor Plücker presentation. -/
theorem intervalPlucker_krullDim (α β : Fin s → Fin n)
    (hα : StrictMono α) (hβ : StrictMono β) (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    ringKrullDim (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) =
      (1 + ∑ i, ((β i).val - (α i).val) : ℕ) := by
  apply le_antisymm (intervalPlucker_krullDim_le α β hα.monotone hβ.monotone hs)
  letI := intervalPluckerIdeal_isPrime (K := K) α β hα.monotone hβ.monotone hs
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg K]
  have h := (intervalPathCoordinates_algebraicIndependent (K := K) α β hα hβ hab hs).lift_cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0_of_finiteType (R := K)
    (S := MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)
  have hn := Cardinal.toNat_le_toNat h (by simpa using hfinite)
  have hn' : 1 + ∑ i, ((β i).val - (α i).val) ≤
      (Algebra.trdeg K
        (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)).toNat := by
    simpa only [Cardinal.toNat_lift,Cardinal.mk_toNat_eq_card,normalizedBandVariable_card]
      using hn
  exact_mod_cast hn'

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0196

section TAF_LiteralSource_0197
/- Original module: PaperVerification.AlternatingFormsOddInitialIdeal -/


/-!
# The exact weight initial ideal of the canonical odd isotropy locus

Both forbidden-coordinate families and the entire generic-minor kernel are
contained in the actual weight initial ideal.  The interval quotient is an
affine domain of the exact expected dimension.  The literal isotropic chart
gives the opposite dimension bound, so strict dimension drop rules out any
additional initial relation.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] {k s t : ℕ}

def oddIntervalLower (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*i.val,by have := i.isLt; omega⟩

def oddIntervalUpper (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*(k+1-s+i.val),by have := i.isLt; omega⟩

theorem oddIntervalLower_strictMono (k s : ℕ) (hs : s≤k+1) :
    StrictMono (oddIntervalLower k s hs) := by
  intro i j hij
  change 2*i.val<2*j.val
  omega

theorem oddIntervalUpper_strictMono (k s : ℕ) (hs : s≤k+1) :
    StrictMono (oddIntervalUpper k s hs) := by
  intro i j hij
  change 2*(k+1-s+i.val)<2*(k+1-s+j.val)
  omega

theorem oddIntervalLower_le_upper (k s : ℕ) (hs : s≤k+1) (i : Fin s) :
    oddIntervalLower k s hs i≤oddIntervalUpper k s hs i := by
  change 2*i.val≤2*(k+1-s+i.val)
  omega

theorem oddInterval_krullDim (k s : ℕ) (hs : s≤k+1) (hpos : 0<s) :
    ringKrullDim (MvPolynomial (PluckerIndex s (2*k+1)) K ⧸
      intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))=
      ((s*(2*k+2-2*s)+1 : ℕ) : WithBot ℕ∞) := by
  rw [intervalPlucker_krullDim _ _ (oddIntervalLower_strictMono k s hs)
    (oddIntervalUpper_strictMono k s hs) (oddIntervalLower_le_upper k s hs) hpos]
  have he (i : Fin s) :
      (oddIntervalUpper k s hs i).val-(oddIntervalLower k s hs i).val=2*(k+1-s) := by
    dsimp only [oddIntervalUpper,oddIntervalLower]
    omega
  apply congrArg (fun d : ℕ => (d : WithBot ℕ∞))
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have hgap : 2*k+2-2*s=2*(k+1-s) := by omega
  rw [hgap]
  omega

/-- The containment concerns the full actual interval ideal, including all
polynomial identities among generic maximal minors, not a chosen finite
list of Plücker equations. -/
theorem odd_interval_le_initial [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    intervalPluckerIdeal (K := K) (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs) ≤
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k)) := by
  apply sup_le
  · exact matrixPluckerIdeal_le_initial_isotropic _ _
  · apply Ideal.span_le.mpr
    rintro _ ⟨I,hbad,rfl⟩
    obtain ⟨i,hi⟩ := not_forall.mp hbad
    by_cases hl : oddIntervalLower k (t+2) hs i≤I.val i
    · have hr : ¬ I.val i≤oddIntervalUpper k (t+2) hs i :=
        fun h => hi ⟨hl,h⟩
      apply odd_right_variable_mem_initial I
      refine ⟨i,?_⟩
      have hv : 2*(k+1-(t+2)+i.val)<(I.val i).val := lt_of_not_ge hr
      omega
    · apply odd_left_variable_mem_initial I
      exact ⟨i,lt_of_not_ge hl⟩

/-- The complete canonical odd-pencil initial-ideal equality in the whole
nonempty isotropic-plane range `2 ≤ s ≤ k+1`, with `s=t+2`.
No dimension, primality, support, or containment premise is supplied. -/
theorem odd_isotropic_initial_eq_interval [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))=
    intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) := by
  letI := intervalPluckerIdeal_isPrime (K := K)
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)
  exact initial_eq_of_prime_candidate (K := K) _ _ _ ((t+2)*(2*k+2-2*(t+2))+1)
    (odd_interval_le_initial (K := K) k t hs)
    (oddInterval_krullDim (K := K) k (t+2) hs (by omega))
    (odd_isotropic_Plucker_cone_dimension_ge (K := K) k t hs)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0197

section TAF_LiteralSource_0198
/- Original module: PaperVerification.FermionFilteredModuleSpanning -/


/-!
# Descending reduction in an actual weighted basis

This is a module statement, so it applies to a noncommutative superalgebra
without replacing its ideal by a commutative one. Homogeneous relation
vectors may have any index type. Every relation used in the reduction is
replaced by an actual filtered lift, and the finite basis support supplies
the terminating degree bound.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)

def component (d : ℕ) : M →ₗ[R] M where
  toFun x := b.repr.symm ((b.repr x).filter (fun i ↦ w i = d))
  map_add' x y := by rw [map_add,Finsupp.filter_add,map_add]
  map_smul' a x := by rw [map_smul,Finsupp.filter_smul,map_smul,RingHom.id_apply]

@[simp] theorem repr_component (d : ℕ) (x : M) (i : I) :
    b.repr (component b w d x) i = if w i = d then b.repr x i else 0 := by
  simp only [component,LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.apply_symm_apply,
    Finsupp.filter_apply]

def Bound (d : ℕ) (x : M) : Prop := ∀ i, b.repr x i ≠ 0 → w i ≤ d

def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, b.repr x i ≠ 0 → w i = d

def HasTop (d : ℕ) (x y : M) : Prop := Bound b w d x ∧ component b w d x = y

theorem bound_zero (d : ℕ) : Bound b w d 0 := by
  intro i hi
  exact (hi (by simp)).elim

theorem bound_add {d : ℕ} {x y : M} (hx : Bound b w d x) (hy : Bound b w d y) :
    Bound b w d (x+y) := by
  intro i hi
  by_cases hxi : b.repr x i = 0
  · apply hy i
    simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
  · exact hx i hxi

theorem bound_sub {d : ℕ} {x y : M} (hx : Bound b w d x) (hy : Bound b w d y) :
    Bound b w d (x-y) := by
  intro i hi
  by_cases hxi : b.repr x i = 0
  · apply hy i
    intro hyi
    apply hi
    simp only [map_sub,Finsupp.sub_apply,hxi,hyi,sub_self]
  · exact hx i hxi

theorem bound_smul {d : ℕ} {x : M} (hx : Bound b w d x) (a : R) :
    Bound b w d (a • x) := by
  intro i hi
  apply hx i
  intro hz
  apply hi
  simp only [map_smul,Finsupp.smul_apply,hz,smul_zero]

theorem HasTop.zero (d : ℕ) : HasTop b w d 0 0 :=
  ⟨bound_zero b w d,map_zero _⟩

theorem HasTop.add {d : ℕ} {x x₀ y y₀ : M}
    (hx : HasTop b w d x x₀) (hy : HasTop b w d y y₀) :
    HasTop b w d (x+y) (x₀+y₀) :=
  ⟨bound_add b w hx.1 hy.1,by rw [map_add,hx.2,hy.2]⟩

theorem HasTop.smul {d : ℕ} {x x₀ : M} (hx : HasTop b w d x x₀) (a : R) :
    HasTop b w d (a • x) (a • x₀) :=
  ⟨bound_smul b w hx.1 a,by rw [map_smul,hx.2]⟩

theorem HasTop.sum {J : Type*} (S : Finset J) (x y : J → M) (d : ℕ)
    (h : ∀ j ∈ S, HasTop b w d (x j) (y j)) :
    HasTop b w d (∑ j ∈ S, x j) (∑ j ∈ S, y j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasTop.zero b w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj,Finset.sum_insert hj]
      exact HasTop.add b w (h j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

theorem homogeneous_component (d : ℕ) (x : M) : Homogeneous b w d (component b w d x) := by
  intro i hi
  by_contra hn
  exact hi (by simp only [repr_component,if_neg hn])

theorem bound_component (d : ℕ) (x : M) : Bound b w d (component b w d x) :=
  fun i hi ↦ (homogeneous_component b w d x i hi).le

theorem homogeneous_bound {d : ℕ} {x : M} (hx : Homogeneous b w d x) : Bound b w d x :=
  fun i hi ↦ (hx i hi).le

theorem component_of_homogeneous {d : ℕ} {x : M} (hx : Homogeneous b w d x) (e : ℕ) :
    component b w e x = if e=d then x else 0 := by
  apply b.repr.injective
  ext i
  rw [repr_component]
  by_cases hxi : b.repr x i = 0
  · split_ifs <;> simp only [hxi,map_zero,Finsupp.zero_apply]
  · have hw := hx i hxi
    by_cases he : e=d
    · subst e
      simp only [hw,if_true]
    · simp only [hw,if_neg he,if_neg (Ne.symm he),map_zero,Finsupp.zero_apply]

theorem homogeneous_basis (i : I) : Homogeneous b w (w i) (b i) := by
  classical
  intro j hj
  have hij : i=j := by
    by_contra hn
    exact hj (by simp only [Module.Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hn)])
  exact congrArg w hij.symm

theorem hasTop_basis (i : I) : HasTop b w (w i) (b i) (b i) := by
  exact ⟨homogeneous_bound b w (homogeneous_basis b w i),by
    rw [component_of_homogeneous b w (homogeneous_basis b w i),if_pos rfl]⟩

theorem exists_bound (x : M) : ∃ d, Bound b w d x := by
  classical
  refine ⟨(b.repr x).support.sup w,?_⟩
  intro i hi
  exact Finset.le_sup (f := w) (Finsupp.mem_support_iff.mpr hi)

theorem bound_pred_of_component_zero {d : ℕ} {x : M}
    (hx : Bound b w (d+1) x) (hz : component b w (d+1) x=0) : Bound b w d x := by
  intro i hi
  have hle := hx i hi
  have hne : w i ≠ d+1 := by
    intro he
    have hh := congrArg (fun y ↦ b.repr y i) hz
    apply hi
    simpa only [repr_component,if_pos he,map_zero,Finsupp.zero_apply] using hh
  omega

theorem eq_zero_of_bound_zero_component_zero {x : M}
    (hx : Bound b w 0 x) (hz : component b w 0 x=0) : x=0 := by
  apply b.repr.injective
  ext i
  by_cases hi : b.repr x i=0
  · simpa only [map_zero,Finsupp.zero_apply] using hi
  · have he := Nat.eq_zero_of_le_zero (hx i hi)
    have hh := congrArg (fun y ↦ b.repr y i) hz
    exact (hi (by simpa only [repr_component,if_pos he,map_zero,Finsupp.zero_apply] using hh)).elim

theorem component_mem_span (v : E → M) (degree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (degree e) (v e))
    (x : M) (hx : x ∈ Submodule.span R (Set.range v)) (d : ℕ) :
    component b w d x ∈ Submodule.span R (Set.range v) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨e,rfl⟩ := hx
      rw [component_of_homogeneous b w (hv e)]
      split_ifs
      · exact Submodule.subset_span ⟨e,rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using Submodule.zero_mem (Submodule.span R (Set.range v))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- Every homogeneous component of a relation has an actual bounded lift. -/
theorem relation_component_lifts (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (x : M) (hx : x ∈ Submodule.span R (Set.range g)) (d : ℕ) :
    ∃ y ∈ Submodule.span R (Set.range f), Bound b w d y ∧
      component b w d y = component b w d x := by
  classical
  have hg (j : J) : Homogeneous b w (degree j) (g j) := by
    rw [← (hf j).2]
    exact homogeneous_component b w _ _
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      by_cases hd : d=degree j
      · subst d
        refine ⟨f j,Submodule.subset_span ⟨j,rfl⟩,(hf j).1,?_⟩
        rw [(hf j).2,component_of_homogeneous b w (hg j),if_pos rfl]
      · refine ⟨0,Submodule.zero_mem _,bound_zero b w d,?_⟩
        rw [map_zero,component_of_homogeneous b w (hg j),if_neg hd]
  | zero => exact ⟨0,Submodule.zero_mem _,bound_zero b w d,rfl⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨u,hu,hub,huc⟩ := ihx
      obtain ⟨v,hv,hvb,hvc⟩ := ihy
      exact ⟨u+v,Submodule.add_mem _ hu hv,bound_add b w hub hvb,by rw [map_add,huc,hvc,map_add]⟩
  | smul a x hx ih =>
      obtain ⟨y,hy,hyb,hyc⟩ := ih
      exact ⟨a • y,Submodule.smul_mem _ a hy,bound_smul b w hyb a,by rw [map_smul,hyc,map_smul]⟩

/-- A homogeneous spanning family modulo the leading relations spans modulo
their actual filtered lifts. No regularity or associated-graded equality is
assumed. The argument is finite descending reduction in the given basis. -/
theorem spanning_lifts (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤) :
    Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range f)=⊤ := by
  let C := Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range f)
  have step (d : ℕ) (x : M) (hx : Bound b w d x) :
      ∃ z ∈ C, Bound b w d (x-z) ∧ component b w d (x-z)=0 := by
    have hm : x ∈ Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨y,hy,hyb,hyc⟩ := relation_component_lifts b w f g degree hf j hj d
    refine ⟨component b w d u+y,Submodule.add_mem C
      ((show Submodule.span R (Set.range v) ≤ C from le_sup_left)
        (component_mem_span b w v vdegree hv u hu d))
      ((show Submodule.span R (Set.range f) ≤ C from le_sup_right) hy),
      bound_sub b w hx (bound_add b w (bound_component b w d u) hyb),?_⟩
    have hid : component b w d (component b w d u)=component b w d u := by
      rw [component_of_homogeneous b w (homogeneous_component b w d u),if_pos rfl]
    rw [map_sub,map_add,hid,hyc,← huj,map_add,sub_self]
  have hmem : ∀ d x, Bound b w d x → x ∈ C := by
    intro d
    induction d with
    | zero =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step 0 x hx
        have he := eq_zero_of_bound_zero_component_zero b w hb hc
        rw [sub_eq_zero.mp he]
        exact hz
    | succ d ih =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step (d+1) x hx
        have hh := ih (x-z) (bound_pred_of_component_zero b w hb hc)
        simpa only [sub_add_cancel] using Submodule.add_mem C hh hz
  apply top_unique
  intro x hx
  obtain ⟨d,hd⟩ := exists_bound b w x
  exact hmem d x hd

end PaperVerification.Fermion.BasisFiltered
end
end
end TAF_LiteralSource_0198

section TAF_LiteralSource_0199
/- Original module: PaperVerification.FermionFilteredInitial -/


/-!
# Initial relations from actual bounded reduction and independence

The initial submodule is defined from the leading components of the actual
relation submodule.  Bounded reduction proves that it equals the homogeneous
relations once the same representatives are independent in the deformed
quotient.  No equality of dimensions or initial ideals is assumed.

This is an uncompiled source candidate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M I J E Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q] (b : Module.Basis I R M) (w : I → ℕ)

theorem bound_mono {d e : ℕ} {x : M} (hde : d ≤ e) (hx : Bound b w d x) :
    Bound b w e x := fun i hi ↦ (hx i hi).trans hde

theorem component_eq_zero_of_bound_lt {d e : ℕ} {x : M}
    (hde : d < e) (hx : Bound b w d x) : component b w e x=0 := by
  apply b.repr.injective
  ext i
  rw [repr_component,map_zero,Finsupp.zero_apply]
  split_ifs with hi
  · by_contra hxi
    have hw := hx i hxi
    omega
  · rfl

def initialSubmodule (N : Submodule R M) : Submodule R M :=
  Submodule.span R {y | ∃ x ∈ N, ∃ d, Bound b w d x ∧ component b w d x=y}

/-- Reduction preserves the degree bound and explicitly tracks the leading
part of the actual relation used. -/
theorem bounded_representative
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (d : ℕ) (x : M) (hx : Bound b w d x) :
    ∃ z ∈ Submodule.span R (Set.range v), Bound b w d z ∧
      x-z ∈ Submodule.span R (Set.range f) ∧
      component b w d (x-z) ∈ Submodule.span R (Set.range g) := by
  have hg (j : J) : Homogeneous b w (degree j) (g j) := by
    rw [← (hf j).2]
    exact homogeneous_component b w _ _
  have step (e : ℕ) (y : M) (hy : Bound b w e y) :
      ∃ u ∈ Submodule.span R (Set.range v), ∃ a ∈ Submodule.span R (Set.range f),
        Bound b w e u ∧ Bound b w e a ∧
        component b w e (y-u-a)=0 ∧
        component b w e a ∈ Submodule.span R (Set.range g) := by
    have hm : y ∈ Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a,ha,hab,hac⟩ := relation_component_lifts b w f g degree hf j hj e
    refine ⟨component b w e u,component_mem_span b w v vdegree hv u hu e,a,ha,
      bound_component b w e u,hab,?_,?_⟩
    · have huu : component b w e (component b w e u)=component b w e u := by
        rw [component_of_homogeneous b w (homogeneous_component b w e u),if_pos rfl]
      rw [map_sub,map_sub,huu,hac,← huj,map_add]
      abel
    · rw [hac]
      exact component_mem_span b w g degree hg j hj e
  induction d generalizing x with
  | zero =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      have he : x-u=a := sub_eq_zero.mp hz
      exact ⟨u,hu,hub,by rw [he]; exact ha,by rw [he]; exact hg⟩
  | succ d ih =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step (d+1) x hx
      have hb : Bound b w d (x-u-a) :=
        bound_pred_of_component_zero b w
          (bound_sub b w (bound_sub b w hx hub) hab) hc
      obtain ⟨z,hz,hzb,hr,ht⟩ := ih (x-u-a) hb
      have he : x-(u+z)=a+((x-u-a)-z) := by abel
      refine ⟨u+z,Submodule.add_mem _ hu hz,
        bound_add b w hub (bound_mono b w (Nat.le_succ d) hzb),?_,?_⟩
      · rw [he]
        exact Submodule.add_mem _ ha hr
      · rw [he,map_add,component_eq_zero_of_bound_lt b w (Nat.lt_succ_self d)
          (bound_sub b w hb hzb),add_zero]
        exact hg

/-- The actual leading submodule equals the homogeneous relation submodule.
The proof uses the independent representatives, not a dimension assertion. -/
theorem initialSubmodule_eq_of_basis [Fintype E]
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (q : M →ₗ[R] Q) (hker : q.ker=Submodule.span R (Set.range f))
    (hli : LinearIndependent R (fun e ↦ q (v e))) :
    initialSubmodule b w q.ker=Submodule.span R (Set.range g) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x,hx,d,hb,rfl⟩
    obtain ⟨z,hz,hzb,hr,ht⟩ := bounded_representative b w f g degree hf v vdegree hv hspan d x hb
    have hqz : q z=0 := by
      have hqr : q (x-z)=0 := by
        apply LinearMap.mem_ker.mp
        rwa [hker]
      rw [map_sub,LinearMap.mem_ker.mp hx,zero_sub,neg_eq_zero] at hqr
      exact hqr
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz
    have hzero : ∑ e, c e • q (v e)=0 := by
      simpa only [map_sum,map_smul] using (congrArg q hc).trans hqz
    have hcoef := Fintype.linearIndependent_iff.mp hli c hzero
    have hz0 : z=0 := by
      rw [← hc]
      simp only [hcoef,zero_smul,Finset.sum_const_zero]
    change component b w d x ∈ Submodule.span R (Set.range g)
    simpa only [hz0,sub_zero] using ht
  · apply Submodule.span_le.mpr
    rintro y ⟨j,rfl⟩
    apply Submodule.subset_span
    refine ⟨f j,?_,degree j,(hf j).1,(hf j).2⟩
    rw [hker]
    exact Submodule.subset_span ⟨j,rfl⟩

end PaperVerification.Fermion.BasisFiltered
end
end
end TAF_LiteralSource_0199

section TAF_LiteralSource_0200
/- Original module: PaperVerification.FilteredBasisTransfer -/


/-!
# Transferring an actual homogeneous quotient basis

Every leading relation is required to have a bounded lift in the actual
relation space. Descending weight proves spanning. Conversely, independence
is proved by taking the greatest weight with a nonzero coefficient in a
finite relation. Neither conclusion assumes a dimension comparison or an
isomorphism between the two quotients.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredBasisTransfer

open PaperVerification.Fermion.BasisFiltered
open scoped BigOperators

variable {K M I E Q Q₀ : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K Q₀]
  (b : Module.Basis I K M) (w : I → ℕ)

private theorem bound_sum (S : Finset E) (v : E → M) (d : ℕ)
    (h : ∀ e∈S,Bound b w d (v e)) : Bound b w d (∑ e∈S,v e) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero b w d
  | @insert e S he ih =>
      rw [Finset.sum_insert he]
      exact bound_add b w (h e (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Actual bounded lifts of every relation component suffice for spanning. -/
theorem spanning (N N₀ : Submodule K M)
    (hlift : ∀ x∈N₀,∀ d,∃ y∈N,Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hspan : Submodule.span K (Set.range v)⊔N₀=⊤) :
    Submodule.span K (Set.range v)⊔N=⊤ := by
  let C := Submodule.span K (Set.range v)⊔N
  have step (d : ℕ) (x : M) (hx : Bound b w d x) :
      ∃ z∈C,Bound b w d (x-z) ∧ component b w d (x-z)=0 := by
    have hm : x∈Submodule.span K (Set.range v)⊔N₀ := by rw [hspan]; trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨y,hy,hyb,hyc⟩ := hlift j hj d
    refine ⟨component b w d u+y,Submodule.add_mem C
      ((show Submodule.span K (Set.range v)≤C from le_sup_left)
        (component_mem_span b w v degree hv u hu d))
      ((show N≤C from le_sup_right) hy),
      bound_sub b w hx (bound_add b w (bound_component b w d u) hyb),?_⟩
    have hid : component b w d (component b w d u)=component b w d u := by
      rw [component_of_homogeneous b w (homogeneous_component b w d u),if_pos rfl]
    rw [map_sub,map_add,hid,hyc,←huj,map_add,sub_self]
  have hm : ∀ d x,Bound b w d x → x∈C := by
    intro d
    induction d with
    | zero =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step 0 x hx
        rw [sub_eq_zero.mp (eq_zero_of_bound_zero_component_zero b w hb hc)]
        exact hz
    | succ d ih =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step (d+1) x hx
        have hr := ih (x-z) (bound_pred_of_component_zero b w hb hc)
        simpa only [sub_add_cancel] using C.add_mem hr hz
  apply top_unique
  intro x hx
  obtain ⟨d,hd⟩ := exists_bound b w x
  exact hm d x hd

private theorem independent_finite [Fintype E]
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hli : LinearIndependent K (fun e => q₀ (v e))) :
    LinearIndependent K (fun e => q (v e)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc e
  by_contra hce
  let S := (Finset.univ : Finset E).filter (fun i => c i≠0)
  have hS : S.Nonempty := ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hce⟩⟩
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image degree hS
  have hcj : c j≠0 := (Finset.mem_filter.mp hj).2
  let x := ∑ i,c i • v i
  have hqx : q x=0 := by simpa only [x,map_sum,map_smul] using hc
  have hbound : Bound b w (degree j) x := by
    apply bound_sum b w
    intro i hi
    by_cases hci : c i=0
    · simpa only [hci,zero_smul] using bound_zero b w (degree j)
    · exact bound_smul b w
        (bound_mono b w (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hci⟩))
          (homogeneous_bound b w (hv i))) (c i)
  have ht := hinitial x hqx (degree j) hbound
  have he : q₀ (component b w (degree j) x)=
      ∑ i,(if degree j=degree i then c i else 0) • q₀ (v i) := by
    simp only [x,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [component_of_homogeneous b w (hv i)]
    split_ifs <;> simp only [map_zero,smul_zero,zero_smul]
  rw [he] at ht
  have hz := Fintype.linearIndependent_iff.mp hli
    (fun i => if degree j=degree i then c i else 0) ht j
  exact hcj (by simpa using hz)

/-- An infinite homogeneous family is independent after lifting whenever
its initial family is independent; only finite coefficient supports enter
the argument. -/
theorem independent
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hli : LinearIndependent K (fun e => q₀ (v e))) :
    LinearIndependent K (fun e => q (v e)) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact independent_finite b w q q₀ hinitial
    (fun e : S => v e.val) (fun e : S => degree e.val) (fun e => hv e.val)
    (hli.comp (fun e : S => e.val) Subtype.val_injective)

/-- Construct the lifted basis in the actual target of the original
surjection. All relation and projection hypotheses concern those maps. -/
def basis
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e)) :
    Module.Basis E K Q := by
  have hli₀ : LinearIndependent K (fun e => q₀ (v e)) := by
    simpa only [←hB₀] using B₀.linearIndependent
  have hspan₀ : Submodule.span K (Set.range v)⊔q₀.ker=⊤ := by
    apply (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq₀)).mp
    rw [Submodule.map_span,←Set.range_comp']
    simpa only [←hB₀] using B₀.span_eq
  have hspan : Submodule.span K (Set.range v)⊔q.ker=⊤ :=
    spanning b w q.ker q₀.ker
      (fun x hx d => by
        obtain ⟨y,hy,hb,ht⟩ := hlift x (LinearMap.mem_ker.mp hx) d
        exact ⟨y,LinearMap.mem_ker.mpr hy,hb,ht⟩)
      v degree hv hspan₀
  have hsp : Submodule.span K (Set.range (fun e => q (v e)))=⊤ := by
    rw [Set.range_comp',←Submodule.map_span]
    exact (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq)).mpr hspan
  exact Module.Basis.mk (independent b w q q₀ hinitial v degree hv hli₀)
    (by rw [hsp])

@[simp] theorem basis_apply
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e)) (e : E) :
    basis b w q q₀ hq hq₀ hinitial hlift v degree hv B₀ hB₀ e=q (v e) := by
  simp only [basis,Module.Basis.mk_apply]

end PaperVerification.FilteredBasisTransfer
end
end
end TAF_LiteralSource_0200

section TAF_LiteralSource_0201
/- Original module: PaperVerification.WeightedInitialBasis -/


/-!
# Lifting a full homogeneous basis through the actual initial ideal

The special-fiber kernel identity supplies an actual bounded relation for
every component of every initial relation. Thus a homogeneous basis of the
initial quotient lifts to the same representatives in the original quotient.
The index type may be infinite, and neither finite dimension nor preservation
of a chosen basis under arbitrary flat specialization is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial

variable {K σ E : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- Every component of an element of the full conventional initial ideal
has a bounded lift in the actual original ideal. The lift is obtained from
the proved Rees kernel coefficient identity. -/
theorem initial_component_lift (Q : Ideal P) (w : σ → ℕ)
    (p : P) (hp : p∈initialIdeal Q w) (d : ℕ) :
    ∃ a∈Q,WeightBound w d a ∧
      weightedHomogeneousComponent w d a=weightedHomogeneousComponent w d p := by
  have hp0 : specialMap Q w p=0 := initialIdeal_le_specialKernel Q w hp
  change fiberMap Q w (reesCover Q w (Polynomial.C p))=0 at hp0
  have hspan : reesCover Q w (Polynomial.C p)∈
      Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp0
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hspan
  obtain ⟨g,hg⟩ := reesCover_surjective Q w a
  let H : Polynomial P := Polynomial.C p-Polynomial.X*g
  have hcover : reesCover Q w H=0 := by
    change reesCover Q w (Polynomial.C p-Polynomial.X*g)=0
    rw [map_sub,map_mul]
    change reesCover Q w (Polynomial.C p)-reesParameter Q w*reesCover Q w g=0
    rw [hg,mul_comm (reesParameter Q w) a,ha,sub_self]
  have hH : reesMap Q w H=0 := congrArg Subtype.val hcover
  have hconstant : H.coeff 0=p := by
    simp only [H,Polynomial.coeff_sub,Polynomial.coeff_C_zero,
      Polynomial.coeff_X_mul_zero,sub_zero]
  refine ⟨coefficientLift w H d,coefficientLift_mem_of_reesMap_zero Q w H hH d,
    coefficientLift_bound w H d,?_⟩
  rw [coefficientLift_top,hconstant]

theorem initialIdeal_component_mem (Q : Ideal P) (w : σ → ℕ)
    (p : P) (hp : p∈initialIdeal Q w) (d : ℕ) :
    weightedHomogeneousComponent w d p∈initialIdeal Q w := by
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w p hp d
  rw [←ht]
  exact component_mem_initialIdeal Q w a ha d hb

theorem monomialBasis_component (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.component (basisMonomials σ K) (Finsupp.weight w) d p=
      weightedHomogeneousComponent w d p := by
  ext a
  change (basisMonomials σ K).repr
    (Fermion.BasisFiltered.component (basisMonomials σ K) (Finsupp.weight w) d p) a=_
  rw [Fermion.BasisFiltered.repr_component,coeff_weightedHomogeneousComponent]
  rfl

theorem monomialBasis_bound_iff (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.Bound (basisMonomials σ K) (Finsupp.weight w) d p ↔
      WeightBound w d p := Iff.rfl

theorem monomialBasis_homogeneous_iff (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.Homogeneous (basisMonomials σ K) (Finsupp.weight w) d p ↔
      p.IsWeightedHomogeneous w d := Iff.rfl

/-- A complete homogeneous initial-quotient basis yields a complete basis
of the original quotient with the very same polynomial representatives. -/
def liftedInitialBasis (Q : Ideal P) (w : σ → ℕ)
    (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) :
    Module.Basis E K (P⧸Q) :=
  FilteredBasisTransfer.basis (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K Q)
    (Ideal.Quotient.mkₐ_surjective K (initialIdeal Q w))
    (by
      intro p hp d hb
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [monomialBasis_component]
      exact component_mem_initialIdeal Q w p
        (Ideal.Quotient.eq_zero_iff_mem.mp hp) d hb)
    (by
      intro p hp d
      obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w p
        (Ideal.Quotient.eq_zero_iff_mem.mp hp) d
      exact ⟨a,Ideal.Quotient.eq_zero_iff_mem.mpr ha,hb,
        by simpa only [monomialBasis_component] using ht⟩)
    v degree (fun e => (monomialBasis_homogeneous_iff w (degree e) (v e)).mpr (hv e))
    B₀ hB₀

@[simp] theorem liftedInitialBasis_apply (Q : Ideal P) (w : σ → ℕ)
    (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) (e : E) :
    liftedInitialBasis Q w v degree hv B₀ hB₀ e=Ideal.Quotient.mk Q (v e) := by
  exact FilteredBasisTransfer.basis_apply _ _ _ _ _ _ _ _ _ _ _ _ _ e

end PaperVerification.WeightedInitialFiber
end
end
end TAF_LiteralSource_0201

section TAF_LiteralSource_0202
/- Original module: PaperVerification.AlternatingFormsOddStandardBasis -/


/-!
# The full standard basis in the original odd isotropic Plücker ring

Every interval multichain, of every length, gives the actual product of good
Plücker coordinates.  The exact initial-ideal equality and bounded lifting
of actual relations prove that these same products are a basis of the
original ring. This is not an inference from flatness alone.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber
open scoped BigOperators

variable {K : Type*} [Field K]

def OddStandardIndex (k t : ℕ) (hs : t+2≤k+1) :=
  Σ r,BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r

def oddStandardRepresentative (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K :=
  chainPluckerProduct (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) C.2

def oddStandardWeight (k t : ℕ) (hs : t+2≤k+1) (C : OddStandardIndex k t hs) : ℕ :=
  ∑ j : Fin C.1,pluckerVertexWeight (oddNatVertexWeight k)
    ⟨C.2.val j,C.2.property.1 j⟩

theorem oddStandardRepresentative_weighted (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    (oddStandardRepresentative (K := K) k t hs C).IsWeightedHomogeneous (pluckerVertexWeight (oddNatVertexWeight k))
        (oddStandardWeight k t hs C) := by
  apply IsWeightedHomogeneous.prod Finset.univ
  intro j hj
  exact isWeightedHomogeneous_X K _ _

theorem oddStandardRepresentative_homogeneous (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    (oddStandardRepresentative (K := K) k t hs C).IsHomogeneous C.1 :=
  chainPluckerProduct_isHomogeneous _ _ C.2

variable [CharZero K]

def oddInitialStandardBasis (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
          (pluckerVertexWeight (oddNatVertexWeight k))) :=
  (intervalStandardBasis (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)).map
      (Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval k t hs).symm).toLinearEquiv

@[simp] theorem oddInitialStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddInitialStandardBasis (K := K) k t hs C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) := by
  unfold oddInitialStandardBasis
  erw [Module.Basis.map_apply]
  simp only [intervalStandardBasis]
  erw [Module.Basis.mk_apply]
  simp only [intervalAllStandardProduct,intervalStandardProduct,
    AlgEquiv.coe_toLinearEquiv,Ideal.quotientEquivAlgOfEq_mk,oddStandardRepresentative]

/-- Every actual good-coordinate standard product, in every polynomial
degree, is retained as a basis vector of the original isotropic ring. -/
def oddPluckerStandardBasis (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  liftedInitialBasis _ (pluckerVertexWeight (oddNatVertexWeight k))
    (oddStandardRepresentative k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted k t hs) (oddInitialStandardBasis k t hs)
    (oddInitialStandardBasis_apply k t hs)

@[simp] theorem oddPluckerStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) :=
  liftedInitialBasis_apply _ _ _ _ _ _ _ C

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0202

section TAF_LiteralSource_0203
/- Original module: PaperVerification.AlternatingFormsOddStandardPieces -/


/-!
# Every actual homogeneous piece of the canonical odd Plücker ring

The full lifted basis restricts by the ordinary polynomial degree.  Its
degree-r component is indexed by precisely the length-r interval chains,
and each vector is the original product of its Plücker coordinates.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

def oddPluckerDegree (k t r : ℕ) : Submodule K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  HomogeneousIdealPieces.piece _ r

def oddStandardDegreeEquiv (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    {C : OddStandardIndex k t hs // C.1=r} ≃
      BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r where
  toFun C := C.property ▸ C.val.2
  invFun C := ⟨⟨r,C⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨a,C⟩,h⟩
    change a=r at h
    subst a
    rfl
  right_inv C := rfl

theorem oddPluckerStandardBasis_mem_degree (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs C∈oddPluckerDegree k t C.1 := by
  rw [oddPluckerStandardBasis_apply]
  exact ⟨oddStandardRepresentative k t hs C,
    oddStandardRepresentative_homogeneous k t hs C,rfl⟩

def oddPluckerDegreeBasis (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    Module.Basis
      (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r)
      K (oddPluckerDegree (K := K) k t r) :=
  (HomogeneousIdealPieces.componentBasis _ (isotropicPluckerIdeal_isHomogeneous _)
    (oddPluckerStandardBasis k t hs) (fun C => C.1)
    (oddPluckerStandardBasis_mem_degree k t hs) r).reindex
      (oddStandardDegreeEquiv k t hs r)

@[simp] theorem oddPluckerDegreeBasis_apply (k t : ℕ) (hs : t+2≤k+1) (r : ℕ)
    (C : BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :
    (oddPluckerDegreeBasis (K := K) k t hs r C :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (chainPluckerProduct _ _ C) := by
  unfold oddPluckerDegreeBasis
  erw [Module.Basis.reindex_apply,HomogeneousIdealPieces.componentBasis_coe]
  change oddPluckerStandardBasis (K := K) k t hs ⟨r,C⟩ = _
  exact oddPluckerStandardBasis_apply (K := K) k t hs ⟨r,C⟩

theorem oddPluckerDegree_finrank (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    Module.finrank K (oddPluckerDegree (K := K) k t r)=
      Fintype.card (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :=
  Module.finrank_eq_card_basis (oddPluckerDegreeBasis k t hs r)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0203

section TAF_LiteralSource_0204
/- Original module: PaperVerification.AlternatingFormsLinearPresentation -/


/-!
# The genuine exterior degree quotient and the linear Plücker presentation

The generic maximal minors have no linear relations.  Projection to ordinary
polynomial degree one therefore removes the entire Grassmannian identity
ideal and replaces the ideal generated by wedge coordinates with their
linear span.  This is the necessary comparison between the actual exterior
ideal quotient and the degree-one part of the isotropic Plücker ring.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n t : ℕ}

private def fullBandSingleton (I : PluckerIndex s (n+1)) :
    BandChain (fun _ : Fin s => (0 : Fin (n+1))) (fun _ => Fin.last n) 1 :=
  ⟨fun _ => I.val,fun _ => I.property,
    (by intro j i; exact ⟨Fin.zero_le _,Fin.le_last _⟩),monotone_const⟩

private theorem fullBandSingleton_injective :
    Function.Injective (fullBandSingleton (s := s) (n := n)) := by
  intro I J h
  apply Subtype.ext
  exact congrFun (congrArg Subtype.val h) (0 : Fin 1)

private theorem fullBandSingleton_minor (I : PluckerIndex s (n+1)) :
    bandStandardProduct (K := K) (fun _ : Fin s => (0 : Fin (n+1)))
      (fun _ => Fin.last n) (fullBandSingleton I)=genericPluckerMinor I := by
  rw [bandStandardProduct,Fin.prod_univ_one,bandMinor,genericPluckerMinor]
  congr 1
  ext i j
  rw [Matrix.submatrix_apply,bandMatrix_apply]
  simp only [fullBandSingleton,Matrix.of_apply,id_eq,
    Fin.zero_le,Fin.le_last,and_self,ite_true]

/-- All generic maximal minors are linearly independent, including every
row count for which increasing indices exist. -/
theorem genericPluckerMinors_linearIndependent :
    LinearIndependent K (genericPluckerMinor (K := K) (s := s) (n := n+1)) := by
  have h := (bandStandardProducts_linearIndependent (K := K)
    (fun _ : Fin s => (0 : Fin (n+1))) (fun _ => Fin.last n) 1).comp
      fullBandSingleton fullBandSingleton_injective
  simpa only [Function.comp_def,fullBandSingleton_minor] using h

/-- Every actual polynomial identity among maximal minors has zero ordinary
degree-one component.  This is proved from the matrix map, without choosing
a set of quadratic Plücker generators. -/
theorem matrixPluckerIdeal_component_one_eq_zero (hs : 0<s)
    (p : MvPolynomial (PluckerIndex s (n+1)) K) (hp : p∈matrixPluckerIdeal) :
    homogeneousComponent 1 p=0 := by
  classical
  have himage : genericPluckerMap (homogeneousComponent 1 p)=0 := by
    change genericPluckerMap p=0 at hp
    rw [←genericPluckerMap_component hs,hp,map_zero]
  rw [homogeneousComponent_one_eq_sum,map_sum] at himage
  simp only [map_smul,genericPluckerMap,aeval_X] at himage
  have hc := (Fintype.linearIndependent_iff.mp
    (genericPluckerMinors_linearIndependent (K := K) (s := s) (n := n)))
      (fun I => p.coeff (Finsupp.single I 1)) himage
  rw [homogeneousComponent_one_eq_sum]
  simp only [hc,zero_smul,Finset.sum_const_zero]

section LinearIdeal

variable {σ : Type*}

/-- The ordinary degree-one projection of an ideal generated by a linear
subspace lies in that same subspace.  Arbitrary polynomial multipliers are
replaced by their actual constant coefficients. -/
theorem linearIdeal_component_one_mem
    (R : Submodule K (MvPolynomial σ K))
    (hR : ∀ p∈R,p.IsHomogeneous 1)
    (p : MvPolynomial σ K) (hp : p∈Ideal.span (R : Set (MvPolynomial σ K))) :
    homogeneousComponent 1 p∈R := by
  induction hp using Submodule.closure_induction with
  | zero => simpa only [map_zero] using R.zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using R.add_mem ihp ihq
  | smul_mem a q hq =>
      change homogeneousComponent 1 (a*q)∈R
      rw [(hR q hq).homogeneousComponent_mul_right,if_pos (le_refl 1),
        Nat.sub_self,homogeneousComponent_zero]
      simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using
        R.smul_mem (a.coeff 0) hq

end LinearIdeal

/-- In degree one, adjoining the actual Grassmannian kernel creates exactly
the prescribed linear relations and no additional ones. -/
theorem mem_matrixPlusLinear_iff (hs : 0<s)
    (R : Submodule K (MvPolynomial (PluckerIndex s (n+1)) K))
    (hR : ∀ p∈R,p.IsHomogeneous 1)
    (p : MvPolynomial (PluckerIndex s (n+1)) K) (hp : p.IsHomogeneous 1) :
    p∈matrixPluckerIdeal⊔Ideal.span (R : Set (MvPolynomial (PluckerIndex s (n+1)) K)) ↔
      p∈R := by
  constructor
  · intro h
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h
    have he := congrArg (homogeneousComponent 1) hab
    rw [map_add,matrixPluckerIdeal_component_one_eq_zero hs a ha,
      zero_add,homogeneousComponent_eq_self hp] at he
    simpa only [he] using linearIdeal_component_one_mem R hR b hb
  · intro h
    exact Submodule.mem_sup_right (Ideal.subset_span h)

theorem exteriorPluckerCoordinates_isHomogeneous
    (x : ⋀[K]^s (Fin n → K)) :
    (exteriorPluckerCoordinates s n x).IsHomogeneous 1 := by
  classical
  rw [←(exteriorPluckerBasis (K := K) s n).sum_repr x,map_sum]
  apply IsHomogeneous.sum
  intro I hI
  rw [map_smul,exteriorPluckerCoordinates_basis]
  exact (homogeneousSubmodule (PluckerIndex s n) K 1).smul_mem _ (isHomogeneous_X K I)

theorem exteriorPluckerCoordinates_range (s n : ℕ) :
    LinearMap.range (exteriorPluckerCoordinates (K := K) s n)=
      homogeneousSubmodule (PluckerIndex s n) K 1 := by
  classical
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact exteriorPluckerCoordinates_isHomogeneous x
  · intro hp
    refine ⟨∑ I : PluckerIndex s n,p.coeff (Finsupp.single I 1) •
      exteriorPluckerBasis s n I,?_⟩
    simp only [map_sum,map_smul,exteriorPluckerCoordinates_basis]
    rw [←homogeneousComponent_one_eq_sum]
    exact homogeneousComponent_eq_self hp

/-- The literal sum of the two homogeneous wedge images. -/
def coefficientPairRelations (f g : StrictPairs n → K) :
    Submodule K (⋀[K]^(t+2) (Fin n → K)) :=
  LinearMap.range (coefficientWedge (t := t) f)⊔
    LinearMap.range (coefficientWedge (t := t) g)

def pairCoefficientForms (f g : StrictPairs n → K) : Fin 2 → StrictPairs n → K :=
  ![f,g]

/-- The complete polynomial isotropy presentation is the Grassmannian
kernel plus the ideal of the actual two-wedge image subspace. -/
theorem pair_isotropicIdeal_eq_linearIdeal (f g : StrictPairs n → K) :
    isotropicPluckerIdeal (t := t) (pairCoefficientForms f g)=matrixPluckerIdeal⊔
      Ideal.span (((coefficientPairRelations (t := t) f g).map
        (exteriorPluckerCoordinates (t+2) n)) :
          Set (MvPolynomial (PluckerIndex (t+2) n) K)) := by
  rw [isotropicPluckerIdeal_eq_wedgeCoordinates]
  congr 1
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i,x⟩,rfl⟩
    apply Ideal.subset_span
    apply Submodule.mem_map.mpr
    refine ⟨coefficientWedge (pairCoefficientForms f g i) x,?_,rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ _)
    · exact Submodule.mem_sup_right (LinearMap.mem_range_self _ _)
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp hp
    obtain ⟨a,⟨u,rfl⟩,b,⟨v,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    apply Ideal.add_mem
    · exact Ideal.subset_span ⟨((0 : Fin 2),u),rfl⟩
    · exact Ideal.subset_span ⟨((1 : Fin 2),v),rfl⟩

/-- Exact kernel comparison: a genuine exterior vector has zero linear
Plücker class precisely when it is a sum of the two actual wedge images. -/
theorem exteriorCoordinates_mem_pairIdeal_iff
    (f g : StrictPairs (n+1) → K) (x : ⋀[K]^(t+2) (Fin (n+1) → K)) :
    exteriorPluckerCoordinates (t+2) (n+1) x∈
      isotropicPluckerIdeal (pairCoefficientForms f g) ↔
      x∈coefficientPairRelations f g := by
  rw [pair_isotropicIdeal_eq_linearIdeal,
    mem_matrixPlusLinear_iff (by omega : 0<t+2) _
      (by
        intro p hp
        obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hp
        exact exteriorPluckerCoordinates_isHomogeneous y)
      _ (exteriorPluckerCoordinates_isHomogeneous x)]
  constructor
  · intro h
    obtain ⟨y,hy,hyx⟩ := Submodule.mem_map.mp h
    exact exteriorPluckerCoordinates_injective (t+2) (n+1) hyx ▸ hy
  · intro hx
    exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

/-- The wedge-image relations are exactly the homogeneous part of the
actual generated exterior ideal.  The degree reindexing retains the literal
products in the exterior algebra. -/
theorem coefficientPairRelations_eq_exterior (f g : StrictPairs n → K) :
    coefficientPairRelations (t := t) f g=exteriorDegreeRelations
      (twoFormOfCoefficients f (Pi.basisFun K (Fin n)))
      (twoFormOfCoefficients g (Pi.basisFun K (Fin n))) (t+2) := by
  ext x
  let y : ⋀[K]^(2+t) (Fin n → K) :=
    ⟨x,by simpa only [Nat.add_comm 2 t] using x.property⟩
  have he : x∈exteriorDegreeRelations
      (twoFormOfCoefficients f (Pi.basisFun K (Fin n)))
      (twoFormOfCoefficients g (Pi.basisFun K (Fin n))) (t+2) ↔
      y∈exteriorDegreeRelations
      (twoFormOfCoefficients f (Pi.basisFun K (Fin n)))
      (twoFormOfCoefficients g (Pi.basisFun K (Fin n))) (2+t) := Iff.rfl
  rw [he,exteriorDegreeRelations_eq_images]
  unfold coefficientPairRelations
  constructor
  · intro hx
    obtain ⟨a,⟨u,rfl⟩,b,⟨v,rfl⟩,huv⟩ := Submodule.mem_sup.mp hx
    apply Submodule.mem_sup.mpr
    refine ⟨_,LinearMap.mem_range_self _ u,_,LinearMap.mem_range_self _ v,?_⟩
    apply Subtype.ext
    have hh := congrArg Subtype.val huv
    change (twoFormOfCoefficients f (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * u +
      (twoFormOfCoefficients g (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * v = (x : ExteriorAlgebra K (Fin n → K)) at hh ⊢
    exact hh
  · intro hx
    obtain ⟨a,⟨u,rfl⟩,b,⟨v,rfl⟩,huv⟩ := Submodule.mem_sup.mp hx
    refine Submodule.mem_sup.mpr
      ⟨coefficientWedge (t := t) f u,⟨u,rfl⟩,
        coefficientWedge (t := t) g v,⟨v,rfl⟩,?_⟩
    apply Subtype.ext
    have hh := congrArg Subtype.val huv
    change (twoFormOfCoefficients f (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * u +
      (twoFormOfCoefficients g (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * v = (x : ExteriorAlgebra K (Fin n → K)) at hh ⊢
    exact hh

/-- The actual degree-one subspace in the full isotropic coordinate ring. -/
def pairLinearPluckerPiece (f g : StrictPairs n → K) :
    Submodule K (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      isotropicPluckerIdeal (t := t) (pairCoefficientForms f g)) :=
  (homogeneousSubmodule (PluckerIndex (t+2) n) K 1).map
    (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal (t := t)
      (pairCoefficientForms f g))).toLinearMap

def pairLinearPluckerClass (f g : StrictPairs n → K) :
    (⋀[K]^(t+2) (Fin n → K)) →ₗ[K]
      MvPolynomial (PluckerIndex (t+2) n) K ⧸
        isotropicPluckerIdeal (t := t) (pairCoefficientForms f g) :=
  (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal (t := t)
    (pairCoefficientForms f g))).toLinearMap.comp (exteriorPluckerCoordinates (t+2) n)

theorem pairLinearPluckerClass_ker (f g : StrictPairs (n+1) → K) :
    LinearMap.ker (pairLinearPluckerClass (t := t) f g)=
      exteriorDegreeRelations
        (twoFormOfCoefficients f (Pi.basisFun K (Fin (n+1))))
        (twoFormOfCoefficients g (Pi.basisFun K (Fin (n+1)))) (t+2) := by
  rw [←coefficientPairRelations_eq_exterior]
  ext x
  change Ideal.Quotient.mk _ (exteriorPluckerCoordinates (t+2) (n+1) x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,exteriorCoordinates_mem_pairIdeal_iff]

theorem pairLinearPluckerClass_range (f g : StrictPairs n → K) :
    LinearMap.range (pairLinearPluckerClass (t := t) f g)=pairLinearPluckerPiece f g := by
  rw [pairLinearPluckerClass,LinearMap.range_comp,exteriorPluckerCoordinates_range]
  rfl

/-- The comparison is an actual linear isomorphism from the exterior ideal
quotient, with no presentation, independence, or dimension premise. -/
def pairExteriorLinearPieceEquiv (f g : StrictPairs (n+1) → K) :
    ExteriorQuotientDegree
      (twoFormOfCoefficients f (Pi.basisFun K (Fin (n+1))))
      (twoFormOfCoefficients g (Pi.basisFun K (Fin (n+1)))) (t+2) ≃ₗ[K]
        pairLinearPluckerPiece (t := t) f g :=
  (Submodule.quotEquivOfEq _ _ (pairLinearPluckerClass_ker f g).symm).trans
    ((pairLinearPluckerClass f g).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (pairLinearPluckerClass_range f g)))

theorem pairExteriorLinearPieceEquiv_mk (f g : StrictPairs (n+1) → K)
    (x : ⋀[K]^(t+2) (Fin (n+1) → K)) :
    (pairExteriorLinearPieceEquiv (t := t) f g (Submodule.Quotient.mk x) :
      MvPolynomial (PluckerIndex (t+2) (n+1)) K ⧸
        isotropicPluckerIdeal (pairCoefficientForms f g))=
      Ideal.Quotient.mk _ (exteriorPluckerCoordinates (t+2) (n+1) x) := by
  simp only [pairExteriorLinearPieceEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearEquiv.coe_ofEq_apply,
    LinearMap.quotKerEquivRange_apply_mk]
  rfl

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0204

section TAF_LiteralSource_0205
/- Original module: PaperVerification.FermionSl2 -/


/-!
# The primitive-degree obstruction

This is the representation-theoretic core of the degree bound in Lemma 3.1.
The proof works over arbitrary commutative coefficient rings with the required
small integer factors invertible. No semisimplicity hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.Fermion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The two commutator relations needed for a raising/lowering argument. -/
structure RaisingLowering (e f h : Module.End R M) : Prop where
  lower_raise : e * f = f * e + h
  weight_raise : h * f = f * h - (2 : R) • f

namespace RaisingLowering

variable {e f h : Module.End R M} (H : RaisingLowering e f h)

include H

theorem lower_raise_apply (z : M) : e (f z) = f (e z) + h z := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply] using
    congrArg (fun a : Module.End R M ↦ a z) H.lower_raise

theorem weight_raise_apply (z : M) : h (f z) = f (h z) - (2 : R) • f z := by
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] using
    congrArg (fun a : Module.End R M ↦ a z) H.weight_raise

/-- The weight drops by two under each application of the raising operator. -/
theorem weight_pow_apply (c : R) (w : M) (hw : h w = c • w) (j : ℕ) :
    h ((f ^ j) w) = (c - 2 * (j : R)) • (f ^ j) w := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, H.weight_raise_apply, ih, map_smul,
      ← sub_smul]
    congr 1
    push_cast
    ring

/-- The exact `sl₂` coefficient in the paper's primitive-vector argument. -/
theorem lower_pow_apply (c : R) (w : M) (he : e w = 0) (hh : h w = c • w)
    (j : ℕ) :
    e ((f ^ (j + 1)) w) = (((j + 1 : ℕ) : R) * (c - (j : R))) • (f ^ j) w := by
  induction j with
  | zero =>
    simpa [he, hh] using H.lower_raise_apply w
  | succ j ih =>
    calc
      e ((f ^ (j + 1 + 1)) w) = e (f ((f ^ (j + 1)) w)) := by
        rw [pow_succ', Module.End.mul_apply]
      _ = f (e ((f ^ (j + 1)) w)) + h ((f ^ (j + 1)) w) :=
        H.lower_raise_apply _
      _ = (((j + 1 : ℕ) : R) * (c - (j : R))) • f ((f ^ j) w) +
          (c - 2 * ((j + 1 : ℕ) : R)) • (f ^ (j + 1)) w := by
        rw [ih, map_smul, H.weight_pow_apply c w hh]
      _ = ((((j + 1 : ℕ) : R) * (c - (j : R))) +
          (c - 2 * ((j + 1 : ℕ) : R))) • (f ^ (j + 1)) w := by
        rw [pow_succ', Module.End.mul_apply, add_smul]
      _ = (((j + 1 + 1 : ℕ) : R) * (c - ((j + 1 : ℕ) : R))) •
          (f ^ (j + 1)) w := by
        congr 1
        push_cast
        ring

end RaisingLowering

/-- Every positive integer up to `n` is a unit when `n!` is a unit. -/
theorem unit_natCast_of_factorial {n m : ℕ} (hn : IsUnit (n.factorial : R))
    (hm : 0 < m) (hmn : m ≤ n) : IsUnit (m : R) := by
  apply isUnit_of_dvd_unit _ hn
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hm hmn
  refine ⟨(q : R), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun a : ℕ ↦ (a : R)) hq

/-- Every smaller factorial is a unit under the paper's factorial hypothesis. -/
theorem unit_factorialCast_of_le {n d : ℕ} (hn : IsUnit (n.factorial : R))
    (hd : d ≤ n) : IsUnit (d.factorial : R) := by
  apply isUnit_of_dvd_unit _ hn
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hd
  refine ⟨(q : R), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun a : ℕ ↦ (a : R)) hq

/-- A primitive string cannot vanish before its nonnegative highest weight.

The unit assumption is only the factorial bound. In particular, this argument
works in all coefficient rings allowed by the paper, including positive
characteristic and nonreduced rings.
-/
theorem primitive_raising_power_eq_zero_iff
    (e f h : Module.End R M) (H : RaisingLowering e f h)
    (d c : ℕ) (hfac : IsUnit (d.factorial : R)) (hc : c ≤ d)
    (w : M) (he : e w = 0) (hh : h w = (c : R) • w) (j : ℕ) :
    j ≤ c → ((f ^ j) w = 0 ↔ w = 0) := by
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    constructor
    · intro hz
      have hjc : j ≤ c := by omega
      have hcast : (c : R) - (j : R) = ((c - j : ℕ) : R) := (Nat.cast_sub hjc).symm
      have hunit : IsUnit (((j + 1 : ℕ) : R) * ((c : R) - (j : R))) := by
        apply IsUnit.mul (unit_natCast_of_factorial hfac (by omega) (by omega))
        rw [hcast]
        exact unit_natCast_of_factorial hfac (by omega) (by omega)
      have hdown := H.lower_pow_apply (c : R) w he hh j
      rw [hz, map_zero] at hdown
      exact (ih hjc).mp (hunit.smul_eq_zero.mp hdown.symm)
    · intro hw
      simp [hw]

/-- A primitive vector in exterior degree greater than the number of pairs is zero.

The last hypothesis is precisely the degree bound for exterior powers: applying
`f` `j` times adds `2j` to exterior degree, and the algebra vanishes above `2d`.
This abstract statement makes all arithmetic and nilpotence dependencies explicit.
-/
theorem primitive_eq_zero_of_degree_gt
    (e f h : Module.End R M) (H : RaisingLowering e f h)
    (d k : ℕ) (hfac : IsUnit (d.factorial : R)) (hkd : d < k)
    (w : M) (he : e w = 0) (hh : h w = ((d : R) - (k : R)) • w)
    (hdegree : ∀ j : ℕ, 2 * d < k + 2 * j → (f ^ j) w = 0) : w = 0 := by
  classical
  by_contra hw
  have hd : (f ^ d) w = 0 := hdegree d (by omega)
  have hex : ∃ j : ℕ, (f ^ j) w = 0 := ⟨d, hd⟩
  let m : ℕ := Nat.find hex
  have hm : (f ^ m) w = 0 := Nat.find_spec hex
  have hm_le : m ≤ d := Nat.find_min' hex hd
  have hm_pos : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    exact hw (by simpa [hm0] using hm)
  let L := m - 1
  have hLm : L + 1 = m := by omega
  have hL : (f ^ L) w ≠ 0 := by
    exact Nat.find_min hex (by dsimp [L]; omega)
  have htotal : k + 2 * L ≤ 2 * d := by
    by_contra hn
    exact hL (hdegree L (by omega))
  let t := k + L - d
  have ht_pos : 0 < t := by omega
  have ht_le : t ≤ d := by omega
  have htd : t + d = k + L := by omega
  have htdR : (t : R) + (d : R) = (k : R) + (L : R) := by
    simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : R)) htd
  have hcoeff : (d : R) - (k : R) - (L : R) = -(t : R) := by
    calc
      (d : R) - (k : R) - (L : R) = (d : R) - ((k : R) + (L : R)) := by ring
      _ = (d : R) - ((t : R) + (d : R)) := by rw [htdR]
      _ = -(t : R) := by ring
  have hu₁ : IsUnit ((L + 1 : ℕ) : R) :=
    unit_natCast_of_factorial hfac (by omega) (by omega)
  have hu₂ : IsUnit ((d : R) - (k : R) - (L : R)) := by
    rw [hcoeff]
    exact (unit_natCast_of_factorial hfac ht_pos ht_le).neg
  have hz := H.lower_pow_apply ((d : R) - (k : R)) w he hh L
  have hm' : (f ^ (L + 1)) w = 0 := by simpa only [hLm] using hm
  rw [hm', map_zero] at hz
  exact hL ((hu₁.mul hu₂).smul_eq_zero.mp hz.symm)

end PaperVerification.Fermion
end
end TAF_LiteralSource_0205

section TAF_LiteralSource_0206
/- Original module: PaperVerification.FermionExterior -/


/-!
# Creation, annihilation, and the exterior number operator

These are the literal exterior-algebra operations used in Section 3. This file
connects their algebraic identities with the homogeneous exterior grading.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion
namespace Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

local notation "E" => ExteriorAlgebra R V

/-- Left exterior multiplication, viewed linearly as a function of its vector. -/
def creation : V →ₗ[R] Module.End R E :=
  (LinearMap.mul R E).comp (ExteriorAlgebra.ι R)

@[simp] theorem creation_apply (v : V) (w : E) :
    creation v w = ExteriorAlgebra.ι R v * w := rfl

/-- Left contraction by a linear functional. -/
def annihilation (l : Module.Dual R V) : Module.End R E :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) l

@[simp] theorem annihilation_one (l : Module.Dual R V) :
    annihilation l (1 : E) = 0 := CliffordAlgebra.contractLeft_one (0 : QuadraticForm R V) l

@[simp] theorem annihilation_algebraMap (l : Module.Dual R V) (r : R) :
    annihilation l (algebraMap R E r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap (0 : QuadraticForm R V) l r

/-- The creation-annihilation anticommutation relation, with its actual evaluation scalar. -/
theorem annihilation_creation (l : Module.Dual R V) (v : V) :
    annihilation l * creation v + creation v * annihilation l = (l v) • 1 := by
  apply LinearMap.ext
  intro w
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, creation_apply, annihilation]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp

theorem creation_anticomm (v w : V) :
    creation (R := R) v * creation w + creation w * creation v = 0 := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply, creation_apply]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem creation_anticomm_eq (v w : V) :
    creation (R := R) v * creation w = -(creation w * creation v) :=
  eq_neg_of_add_eq_zero_left (creation_anticomm v w)

theorem annihilation_anticomm_eq (l m : Module.Dual R V) :
    annihilation l * annihilation m = -(annihilation m * annihilation l) := by
  apply LinearMap.ext
  intro w
  simpa only [annihilation, Module.End.mul_apply, LinearMap.neg_apply] using
    CliffordAlgebra.contractLeft_comm l m w

theorem annihilation_square (l : Module.Dual R V) :
    annihilation l * annihilation l = 0 := by
  apply LinearMap.ext
  intro w
  exact CliffordAlgebra.contractLeft_contractLeft l w

theorem creation_square (v : V) : creation (R := R) v * creation v = 0 := by
  apply LinearMap.ext
  intro w
  simp only [Module.End.mul_apply, LinearMap.zero_apply, creation_apply]
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R V)

/-- The sum of the coordinate occupation operators. -/
noncomputable def number : Module.End R E :=
  ∑ i, creation (b i) * annihilation (b.coord i)

@[simp] theorem number_algebraMap (r : R) : number b (algebraMap R E r) = 0 := by
  simp [number, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_coord_creation (v : V) :
    (∑ i, (b.coord i v) • creation (R := R) (b i)) = creation v := by
  simp only [Module.Basis.coord_apply, ← map_smul, ← map_sum, b.sum_repr]

/-- Each creation increases the number operator by one. -/
theorem number_creation (v : V) :
    number b * creation v = creation v + creation v * number b := by
  have hterm (i : ι) :
      (creation (b i) * annihilation (b.coord i)) * creation v =
        (b.coord i v) • creation (b i) +
          creation v * (creation (b i) * annihilation (b.coord i)) := by
    have hcar : annihilation (b.coord i) * creation v =
        (b.coord i v) • 1 - creation v * annihilation (b.coord i) :=
      eq_sub_of_add_eq (annihilation_creation (b.coord i) v)
    rw [mul_assoc, hcar, mul_sub, mul_smul_comm, mul_one,
      ← mul_assoc, creation_anticomm_eq]
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.add_apply, LinearMap.smul_apply, sub_neg_eq_add]
  calc
    number b * creation v = ∑ i, (creation (b i) * annihilation (b.coord i)) * creation v := by
      rw [number, Finset.sum_mul]
    _ = ∑ i, ((b.coord i v) • creation (b i) +
        creation v * (creation (b i) * annihilation (b.coord i))) :=
      Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = creation v + creation v * number b := by
      rw [Finset.sum_add_distrib, sum_coord_creation, ← Finset.mul_sum, number]

theorem number_creation_apply (v : V) (w : E) :
    number b (ExteriorAlgebra.ι R v * w) =
      ExteriorAlgebra.ι R v * w + ExteriorAlgebra.ι R v * number b w := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply, creation_apply] using
    congrArg (fun a : Module.End R E ↦ a w) (number_creation b v)

theorem sum_dual_annihilation (l : Module.Dual R V) :
    (∑ i, l (b i) • annihilation (b.coord i)) = annihilation l := by
  unfold annihilation
  simp_rw [← map_smul]
  rw [← map_sum, b.sum_dual_apply_smul_coord]

/-- Each contraction decreases the number operator by one. -/
theorem number_annihilation (l : Module.Dual R V) :
    number b * annihilation l = annihilation l * number b - annihilation l := by
  have hterm (i : ι) :
      (creation (b i) * annihilation (b.coord i)) * annihilation l =
        annihilation l * (creation (b i) * annihilation (b.coord i)) -
          l (b i) • annihilation (b.coord i) := by
    have hcar : creation (b i) * annihilation l =
        l (b i) • 1 - annihilation l * creation (b i) :=
      eq_sub_of_add_eq (by simpa only [add_comm] using annihilation_creation l (b i))
    calc
      _ = creation (b i) * (annihilation (b.coord i) * annihilation l) := by rw [mul_assoc]
      _ = creation (b i) * (-(annihilation l * annihilation (b.coord i))) := by
        rw [annihilation_anticomm_eq]
      _ = -((creation (b i) * annihilation l) * annihilation (b.coord i)) := by
        apply LinearMap.ext
        intro w
        simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      _ = -((l (b i) • 1 - annihilation l * creation (b i)) * annihilation (b.coord i)) := by
        rw [hcar]
      _ = _ := by rw [sub_mul, smul_mul_assoc, one_mul, neg_sub, mul_assoc]
  calc
    number b * annihilation l =
        ∑ i, (creation (b i) * annihilation (b.coord i)) * annihilation l := by
      rw [number, Finset.sum_mul]
    _ = ∑ i, (annihilation l * (creation (b i) * annihilation (b.coord i)) -
        l (b i) • annihilation (b.coord i)) := Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_dual_annihilation, number]

/-- The occupation-number operator has eigenvalue `k` on the actual `k`th exterior power. -/
theorem number_homogeneous (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V) :
    number b w = (k : R) • w := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y k hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | mem_mul v hv k w hw ih =>
    obtain ⟨v, rfl⟩ := hv
    rw [number_creation_apply, ih, mul_smul_comm]
    simp only [Nat.cast_succ, add_smul, one_smul]
    exact add_comm _ _

include b in
/-- Exterior degrees larger than the number of basis vectors vanish over any coefficient ring. -/
theorem homogeneous_eq_zero_of_card_lt
    (k : ℕ) (hk : Fintype.card ι < k) (w : E) (hw : w ∈ ⋀[R]^k V) : w = 0 := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : IsEmpty (Set.powersetCard ι k) := ⟨fun s ↦ by
    have hcard := Finset.card_le_univ s.val
    have hs : s.val.card = k := s.prop
    omega⟩
  have hz : (⟨w, hw⟩ : ⋀[R]^k V) = 0 := by
    apply (b.exteriorPower k).repr.injective
    ext s
    exact isEmptyElim s
  exact congrArg Subtype.val hz

end Exterior

section OperatorIdentities

variable {A : Type*} [Ring A]

/-- The two-mode commutator, proved from four elementary anticommutation identities. -/
theorem pair_operator_commutator (a b c d : A)
    (hac : a * c + c * a = 1) (hbd : b * d + d * b = 1)
    (had : a * d + d * a = 0) (hbc : b * c + c * b = 0) :
    (b * a) * (c * d) = (c * d) * (b * a) + (1 - c * a - d * b) := by
  have hac' : a * c = 1 - c * a := eq_sub_of_add_eq hac
  have hbd' : b * d = 1 - d * b := eq_sub_of_add_eq hbd
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  have hbc' : b * c = -(c * b) := eq_neg_of_add_eq_zero_left hbc
  calc
    (b * a) * (c * d) = b * (a * c) * d := by noncomm_ring
    _ = b * (1 - c * a) * d := by rw [hac']
    _ = b * d - (b * c) * (a * d) := by noncomm_ring
    _ = (1 - d * b) - (-(c * b)) * (-(d * a)) := by rw [hbd', hbc', had']
    _ = 1 - d * b - c * (b * d) * a := by noncomm_ring
    _ = 1 - d * b - c * (1 - d * b) * a := by rw [hbd']
    _ = (c * d) * (b * a) + (1 - c * a - d * b) := by noncomm_ring

/-- Quadratic even operators on disjoint modes commute. -/
theorem disjoint_pair_operators_commute (a b c d : A)
    (hac : a * c + c * a = 0) (hbd : b * d + d * b = 0)
    (had : a * d + d * a = 0) (hbc : b * c + c * b = 0) :
    (b * a) * (c * d) = (c * d) * (b * a) := by
  have hac' : a * c = -(c * a) := eq_neg_of_add_eq_zero_left hac
  have hbd' : b * d = -(d * b) := eq_neg_of_add_eq_zero_left hbd
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  have hbc' : b * c = -(c * b) := eq_neg_of_add_eq_zero_left hbc
  calc
    (b * a) * (c * d) = b * (a * c) * d := by noncomm_ring
    _ = b * (-(c * a)) * d := by rw [hac']
    _ = -(b * c) * (a * d) := by noncomm_ring
    _ = (-(-(c * b))) * (-(d * a)) := by rw [hbc', had']
    _ = -c * (b * d) * a := by noncomm_ring
    _ = -c * (-(d * b)) * a := by rw [hbd']
    _ = (c * d) * (b * a) := by noncomm_ring

end OperatorIdentities

namespace Exterior

open scoped BigOperators

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [Fintype ι] [DecidableEq ι]

local notation "E" => ExteriorAlgebra R V

/- An ordered pairing of the `2d` exterior modes. -/
variable (b : Module.Basis (ι ⊕ ι) R V)

def pairLower (i : ι) : Module.End R E :=
  annihilation (b.coord (.inr i)) * annihilation (b.coord (.inl i))

def pairRaise (i : ι) : Module.End R E :=
  creation (b (.inl i)) * creation (b (.inr i))

/-- Contraction by the standard symplectic form. -/
def lowering : Module.End R E := ∑ i, pairLower b i

/-- Exterior multiplication by the sum of the paired two-forms. -/
def raising : Module.End R E := ∑ i, pairRaise b i

def weight : Module.End R E := (Fintype.card ι : R) • 1 - number b

theorem pair_commutator (i j : ι) :
    pairLower b i * pairRaise b j - pairRaise b j * pairLower b i =
      if i = j then
        1 - creation (b (.inl i)) * annihilation (b.coord (.inl i)) -
          creation (b (.inr i)) * annihilation (b.coord (.inr i))
      else 0 := by
  have hself (a : ι ⊕ ι) :
      annihilation (b.coord a) * creation (b a) +
        creation (b a) * annihilation (b.coord a) = (1 : Module.End R E) := by
    rw [annihilation_creation, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, one_smul]
  have hne (a c : ι ⊕ ι) (hac : a ≠ c) :
      annihilation (b.coord a) * creation (b c) +
        creation (b c) * annihilation (b.coord a) = (0 : Module.End R E) := by
    rw [annihilation_creation, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hac, zero_smul]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, sub_eq_iff_eq_add']
    unfold pairLower pairRaise
    exact pair_operator_commutator (A := Module.End R E)
      (annihilation (b.coord (.inl i))) (annihilation (b.coord (.inr i)))
      (creation (b (.inl i))) (creation (b (.inr i)))
      (hself (.inl i)) (hself (.inr i))
      (hne (.inl i) (.inr i) Sum.inl_ne_inr)
      (hne (.inr i) (.inl i) Sum.inr_ne_inl)
  · rw [if_neg hij, sub_eq_zero]
    unfold pairLower pairRaise
    exact disjoint_pair_operators_commute (A := Module.End R E)
      (annihilation (b.coord (.inl i))) (annihilation (b.coord (.inr i)))
      (creation (b (.inl j))) (creation (b (.inr j)))
      (hne (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h)))
      (hne (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h)))
      (hne (.inl i) (.inr j) Sum.inl_ne_inr)
      (hne (.inr i) (.inl j) Sum.inr_ne_inl)

theorem lower_raise : lowering b * raising b = raising b * lowering b + weight b := by
  apply sub_eq_iff_eq_add'.mp
  calc
    lowering b * raising b - raising b * lowering b =
        ∑ i, ∑ j, (pairLower b i * pairRaise b j - pairRaise b j * pairLower b i) := by
      simp only [lowering, raising, Finset.sum_sub_distrib]
      rw [← Fintype.sum_mul_sum, Finset.sum_comm, ← Fintype.sum_mul_sum]
    _ = ∑ i, (1 - creation (b (.inl i)) * annihilation (b.coord (.inl i)) -
        creation (b (.inr i)) * annihilation (b.coord (.inr i))) := by
      simp_rw [pair_commutator]
      simp
    _ = weight b := by
      simp only [weight, number, Fintype.sum_sum_type, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      abel

theorem number_pairRaise (i : ι) :
    number b * pairRaise b i = (2 : R) • pairRaise b i + pairRaise b i * number b := by
  unfold pairRaise
  rw [← mul_assoc, number_creation, add_mul, mul_assoc, number_creation, mul_add]
  simp only [← mul_assoc]
  simp only [two_smul]
  abel

theorem number_raising :
    number b * raising b = (2 : R) • raising b + raising b * number b := by
  simp only [raising, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    number_pairRaise, Finset.sum_add_distrib]

theorem weight_raise :
    weight b * raising b = raising b * weight b - (2 : R) • raising b := by
  simp only [weight, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [number_raising]
  abel

theorem number_pairLower (i : ι) :
    number b * pairLower b i = pairLower b i * number b - (2 : R) • pairLower b i := by
  unfold pairLower
  rw [← mul_assoc, number_annihilation, sub_mul, mul_assoc, number_annihilation, mul_sub]
  simp only [← mul_assoc, two_smul]
  abel

theorem number_lowering :
    number b * lowering b = lowering b * number b - (2 : R) • lowering b := by
  simp only [lowering, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    number_pairLower, Finset.sum_sub_distrib]

theorem weight_lower :
    weight b * lowering b = lowering b * weight b + (2 : R) • lowering b := by
  simp only [weight, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [number_lowering]
  abel

theorem raisingLowering : RaisingLowering (lowering b) (raising b) (weight b) :=
  ⟨lower_raise b, weight_raise b⟩

/-- The reversed orientation, useful for wedge injectivity below middle degree. -/
theorem loweringRaising : RaisingLowering (raising b) (lowering b) (-weight b) := by
  constructor
  · rw [← sub_eq_add_neg]
    exact eq_sub_of_add_eq (lower_raise b).symm
  · calc
      -weight b * lowering b = -(weight b * lowering b) := by
        apply LinearMap.ext
        intro w
        rfl
      _ = -(lowering b * weight b + (2 : R) • lowering b) :=
        congrArg Neg.neg (weight_lower b)
      _ = lowering b * -weight b - (2 : R) • lowering b := by
        apply LinearMap.ext
        intro w
        simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.smul_apply, map_neg]
        abel

theorem weight_homogeneous (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V) :
    weight b w = ((Fintype.card ι : R) - (k : R)) • w := by
  simp only [weight, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    number_homogeneous b k w hw, sub_smul]

theorem creation_mem_succ (v : V) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    creation v w ∈ ⋀[R]^(k + 1) V := by
  change ExteriorAlgebra.ι R v * w ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ (k + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) hw

theorem raising_mem_add_two {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    raising b w ∈ ⋀[R]^(k + 2) V := by
  rw [raising, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  exact creation_mem_succ _ (creation_mem_succ _ hw)

theorem raising_pow_mem {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) (j : ℕ) :
    (raising b ^ j) w ∈ ⋀[R]^(k + 2 * j) V := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert raising_mem_add_two b ih using 1 <;> congr 1 <;> omega

/-- The primitive bound of Lemma 3.1 for the literal exterior-algebra operators.

It holds over every commutative coefficient ring in which `d!` is a unit,
and uses the exterior grading, not a postulated nilpotence condition.
-/
theorem primitive_degree_bound
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hdegree : Fintype.card ι < k) : w = 0 := by
  apply primitive_eq_zero_of_degree_gt (lowering b) (raising b) (weight b)
    (raisingLowering b) (Fintype.card ι) k hfac hdegree w he (weight_homogeneous b k w hw)
  intro j hj
  apply homogeneous_eq_zero_of_card_lt b (k + 2 * j) _ _ (raising_pow_mem b hw j)
  simpa only [Fintype.card_sum, two_mul] using hj

/-- The precise Lefschetz truncation needed in the polynomial part of Lemma 3.1.
It is deduced from the actual exterior grading and the checked commutators. -/
theorem primitive_raising_pow_eq_zero
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hk : k ≤ Fintype.card ι) :
    (raising b ^ (Fintype.card ι - k + 1)) w = 0 := by
  let c := Fintype.card ι - k
  have hcast : (Fintype.card ι : R) - (k : R) = (c : R) := (Nat.cast_sub hk).symm
  have hh : weight b w = (c : R) • w := by
    rw [weight_homogeneous b k w hw, hcast]
  have hprimitive : lowering b ((raising b ^ (c + 1)) w) = 0 := by
    have h := (raisingLowering b).lower_pow_apply (c : R) w he hh c
    simpa only [sub_self, mul_zero, zero_smul] using h
  apply primitive_degree_bound b hfac (k + 2 * (c + 1)) _
    (raising_pow_mem b hw (c + 1)) hprimitive
  dsimp [c]
  omega

/-- Every stage through degree `d-k` of a nonzero primitive string is nonzero. -/
theorem primitive_raising_pow_ne_zero
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hk : k ≤ Fintype.card ι) (hne : w ≠ 0)
    (j : ℕ) (hj : j ≤ Fintype.card ι - k) : (raising b ^ j) w ≠ 0 := by
  apply mt (primitive_raising_power_eq_zero_iff (lowering b) (raising b) (weight b)
    (raisingLowering b) (Fintype.card ι) (Fintype.card ι - k) hfac (Nat.sub_le _ _)
    w he (by rw [weight_homogeneous b k w hw, Nat.cast_sub hk]) j hj).mp hne

end Exterior

end PaperVerification.Fermion
end
end
end TAF_LiteralSource_0206

section TAF_LiteralSource_0207
/- Original module: TauCeti.LinearAlgebra.CliffordAlgebra.Grading -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Reading the `ℤ/2`-grading: base cases, exterior bases, and ordered products

An induction over the `ℤ/2`-grading of a Clifford algebra — Mathlib's
`CliffordAlgebra.evenOdd_induction` — hands its base case back as membership in a power of
`LinearMap.range (ι Q)` whose exponent is a `ZMod.val`. Since `(0 : ZMod 2).val` is `0` and
`(1 : ZMod 2).val` is `1`, that membership says "a scalar" in the even case and "a vector" in the
odd one. Reading it that way is bookkeeping that every such induction repeats, so it is recorded
here once and shared.

In the other direction, the ordered product `(l.map (ι Q)).prod` of a list of vectors — the
spelling `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Basic.lean` uses for the volume
element — is homogeneous of degree `l.length`, which is Mathlib's
`SetLike.list_prod_map_mem_graded` for the graded monoid `CliffordAlgebra.evenOdd Q` with the
degree of each factor read off `CliffordAlgebra.ι_mem_evenOdd_one`. Reading it off by the parity of
the length is what matters downstream.

The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`, combining
Mathlib's `CliffordAlgebra.involute_eq_of_mem_even` and `CliffordAlgebra.involute_eq_of_mem_odd`
into one statement indexed by the parity. Once `2` is invertible, the two graded pieces are the
eigenspaces of the grade involution: the even part is its fixed space and the odd part its
`-1`-eigenspace. Mathlib proves one implication of each (the two lemmas above) and leaves the
converses as a TODO; they are recorded here. This is the form in which the grading is
transported along maps commuting with the involution, such as extension of scalars.

The coordinate basis of an exterior algebra is homogeneous for this grading: the basis vector
indexed by `s` has degree `s.card`, and — over a nontrivial ring, where a basis vector is nonzero
and the two graded pieces meet only in `0` — that degree is the *only* one it has. This statement
belongs to the grading API independently of any spin representation.

## Main results

* `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero`: in the even base case the
  element is a scalar.
* `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`: in the odd base case it is a vector.
* `CliffordAlgebra.ι_range_pow_le_evenOdd`: the `n`-th power of the range of `ι` lies in the
  graded piece of degree `n`.
* `CliffordAlgebra.prod_map_ι_mem_evenOdd`: an ordered product of `n` generators is homogeneous
  of degree `n`, and `CliffordAlgebra.prod_map_ι_mem_evenOdd_zero_of_even_length` and
  `CliffordAlgebra.prod_map_ι_mem_evenOdd_one_of_odd_length` read that off in the even and the odd
  case.
* `CliffordAlgebra.involute_eq_uzpow_smul_of_mem_evenOdd`: the grade involution acts on the graded
  piece of parity `p` by `(-1) ^ p`.
* `CliffordAlgebra.involute_eq_self_iff` and `CliffordAlgebra.involute_eq_neg_iff`: with `2`
  invertible, the even and odd parts are the `±1`-eigenspaces of the grade involution.
* `Module.Basis.exteriorAlgebra_mem_evenOdd_card`: an exterior coordinate-basis vector is
  homogeneous of degree given by the cardinality of its index set, and
  `Module.Basis.exteriorAlgebra_mem_evenOdd_iff` says that this is the only degree it has.
* `Module.Basis.mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero`: an exterior element is
  homogeneous of a given parity exactly when its coordinates vanish at every index set of the
  other parity.
-/

public section


universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- An element of the `(0 : ZMod 2).val`-th power of the range of `ι` is a scalar. This is the
`i = 0` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_algebraMap_of_mem_range_ι_pow_zero {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (0 : ZMod 2).val) :
    ∃ r : R, algebraMap R (CliffordAlgebra Q) r = v :=
  Submodule.mem_one.mp (by simpa using hv)

/-- An element of the `(1 : ZMod 2).val`-th power of the range of `ι` is a vector. This is the
`i = 1` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_ι_of_mem_range_ι_pow_one {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (1 : ZMod 2).val) : ∃ a, ι Q a = v := by
  simpa [ZMod.val_one] using hv

/-- **The `n`-th power of the vectors is homogeneous of degree `n`** for the `ℤ/2` grading: it is
one of the summands defining `CliffordAlgebra.evenOdd Q n`. -/
theorem ι_range_pow_le_evenOdd (n : ℕ) :
    LinearMap.range (ι Q) ^ n ≤ evenOdd Q (n : ZMod 2) := by
  rw [evenOdd]
  exact le_iSup (fun j : {m : ℕ // (m : ZMod 2) = (n : ZMod 2)} => LinearMap.range (ι Q) ^ (j : ℕ))
    ⟨n, rfl⟩

/-- **An ordered product of `n` generators is homogeneous of degree `n`** for the `ℤ/2` grading. -/
theorem prod_map_ι_mem_evenOdd (l : List M) :
    (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2) := by
  simpa using SetLike.list_prod_map_mem_graded (A := evenOdd Q) l (fun _ => (1 : ZMod 2)) (ι Q)
    fun j _ => ι_mem_evenOdd_one Q j

/-- **The ordered product of an even number of vectors is even.** -/
theorem prod_map_ι_mem_evenOdd_zero_of_even_length {l : List M} (hlen : Even l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 0 := by
  have h : (l.length : ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.even_iff.mp hlen, Nat.cast_zero]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-- **The ordered product of an odd number of vectors is odd.** -/
theorem prod_map_ι_mem_evenOdd_one_of_odd_length {l : List M} (hlen : Odd l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 1 := by
  have h : (l.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.odd_iff.mp hlen, Nat.cast_one]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-! ### The graded pieces as eigenspaces of the grade involution -/

section Involute

/-- Every Clifford element is the sum of an even and an odd element. -/
private theorem exists_add_eq (x : CliffordAlgebra Q) :
    ∃ e ∈ evenOdd Q 0, ∃ o ∈ evenOdd Q 1, e + o = x :=
  Submodule.mem_sup.mp ((evenOdd_isCompl Q).sup_eq_top ▸ Submodule.mem_top)

/-- **The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`.** -/
theorem involute_eq_uzpow_smul_of_mem_evenOdd {p : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q p) : involute x = ((-1 : ℤˣ) ^ p) • x := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by clear hx; revert p; decide
  · rw [involute_eq_of_mem_even hx, uzpow_zero, one_smul]
  · rw [involute_eq_of_mem_odd hx, uzpow_one, Units.neg_smul, one_smul]

variable [Invertible (2 : R)]

/-- **The even part is the fixed space of the grade involution** once `2` is invertible. Mathlib's
`CliffordAlgebra.involute_eq_of_mem_even` is the reverse implication. -/
theorem involute_eq_self_iff {x : CliffordAlgebra Q} : involute x = x ↔ x ∈ evenOdd Q 0 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_even⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • o = 0 := by linear_combination (norm := module) -hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using he

/-- **The odd part is the `-1`-eigenspace of the grade involution** once `2` is invertible.
Mathlib's `CliffordAlgebra.involute_eq_of_mem_odd` is the reverse implication. -/
theorem involute_eq_neg_iff {x : CliffordAlgebra Q} : involute x = -x ↔ x ∈ evenOdd Q 1 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_odd⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • e = 0 := by linear_combination (norm := module) hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using ho

end Involute

end CliffordAlgebra

namespace Module.Basis

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I]

/-- **An exterior coordinate-basis vector is homogeneous of degree its number of coordinates.** -/
@[simp] theorem exteriorAlgebra_mem_evenOdd_card (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (s.card : ZMod 2) := by
  rw [CliffordAlgebra.evenOdd]
  refine Submodule.mem_iSup_of_mem ⟨s.card, rfl⟩ ?_
  have h := (b.exteriorPower s.card
    (⟨s, rfl⟩ : Set.powersetCard I s.card)).2
  rw [← ExteriorAlgebra.basis_eq_coe_basis] at h
  exact h

/-- **An exterior coordinate-basis vector is homogeneous of exactly one degree**: it lies in the
graded piece `i` precisely when `i` is the parity of its number of coordinates. -/
@[simp]
theorem exteriorAlgebra_mem_evenOdd_iff [Nontrivial R] (b : Module.Basis I R M) (s : Finset I)
    (i : ZMod 2) :
    b.ExteriorAlgebra s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      (s.card : ZMod 2) = i := by
  refine ⟨fun hmem => ?_, fun h => h ▸ b.exteriorAlgebra_mem_evenOdd_card s⟩
  by_contra hne
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  have hpair : ∀ c d : ZMod 2, c ≠ d → (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by decide
  have hsplit := hpair _ _ hne
  have hbot : b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 0 ⊓
        CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 1 := by
    rcases hsplit with ⟨hc, hi⟩ | ⟨hc, hi⟩
    · exact ⟨hc ▸ hcard, hi ▸ hmem⟩
    · exact ⟨hi ▸ hmem, hc ▸ hcard⟩
  rw [(CliffordAlgebra.evenOdd_isCompl (Q := (0 : QuadraticForm R M))).inf_eq_bot,
    Submodule.mem_bot] at hbot
  exact b.ExteriorAlgebra.ne_zero s hbot

/-- **An exterior element is homogeneous of parity `i` exactly when it has no coordinates of the
other parity**: its coordinate in the exterior coordinate basis vanishes at every index set whose
cardinality has the other parity. -/
theorem mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero (b : Module.Basis I R M) {i : ZMod 2}
    {x : _root_.ExteriorAlgebra R M} :
    x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      ∀ t : Finset I, (t.card : ZMod 2) ≠ i → b.ExteriorAlgebra.repr x t = 0 := by
  classical
  have hsupp : ∀ (j : ZMod 2) (y : _root_.ExteriorAlgebra R M),
      (∀ t : Finset I, (t.card : ZMod 2) ≠ j → b.ExteriorAlgebra.repr y t = 0) →
        y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) j := by
    intro j y hy
    rw [← b.ExteriorAlgebra.linearCombination_repr y, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun s hs ↦ Submodule.smul_mem _ _ ?_
    have hs' : (s.card : ZMod 2) = j := by_contra fun h ↦ Finsupp.mem_support_iff.1 hs (hy s h)
    exact hs' ▸ b.exteriorAlgebra_mem_evenOdd_card s
  refine ⟨fun hx t ht ↦ ?_, hsupp i x⟩
  -- `y` is the part of `x` of the parity opposite to `i`; it is homogeneous of both parities.
  let y := b.ExteriorAlgebra.repr.symm
    ((b.ExteriorAlgebra.repr x).filter fun s ↦ (s.card : ZMod 2) ≠ i)
  have hrepr (s : Finset I) : b.ExteriorAlgebra.repr y s =
      if (s.card : ZMod 2) ≠ i then b.ExteriorAlgebra.repr x s else 0 := by
    simp only [y, LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  have hflip : ∀ c d : ZMod 2, c ≠ d + 1 → c = d := by decide
  have hy₁ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1) :=
    hsupp _ y fun s hs ↦ by rw [hrepr, ite_eq_right (not_not.2 (hflip _ _ hs))]
  have hy₀ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i := by
    have hrest : x - y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i :=
      hsupp i _ fun s hs ↦ by rw [map_sub, Finsupp.sub_apply, hrepr, ite_eq_left hs, sub_self]
    simpa using Submodule.sub_mem _ hx hrest
  have hdisj : Disjoint (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i)
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1)) := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint.symm
  have hy : y = 0 := (Submodule.disjoint_def.1 hdisj) y hy₀ hy₁
  have hcoord := hrepr t
  rw [hy, ite_eq_left ht, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  exact hcoord.symm

end Module.Basis
end
end TAF_LiteralSource_0207

section TAF_LiteralSource_0208
/- Original module: TauCeti.LinearAlgebra.CliffordAlgebra.Contraction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.

/-!
# Contraction against the `ℤ/2`-grading, and the change of form on right factors

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance because an
anisotropic vector orthogonal to a polarization acts on a spinor module by its scalar coordinate
times the grade involution. More precisely, contraction is a derivation twisted by the grade
involution, `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`, the graded Leibniz rule of an odd
operator.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so `evenOdd Q (i + 1)` and `evenOdd Q (i - 1)` are the same submodule; the statement below
names the first.

The parity statement is proved by induction over the grading; its base case is read off by
`CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
`CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`, which are general facts about the
grading and live with it.

Mathlib's `CliffordAlgebra.changeForm` is built by folding from the left, so Mathlib describes
it on left factors only (`CliffordAlgebra.changeForm_ι_mul`). The second half of this file supplies
the right-handed description `CliffordAlgebra.changeForm_mul_ι`, which rests on the graded
Leibniz rules for a contraction meeting a vector factor on the far side and on the commutation of
left with right contraction, left as a `TODO` in Mathlib. From it, `changeForm` commutes with
reversion when the bilinear form is symmetric; and since contraction anticommutes with the grade
involution, `changeForm` commutes with the grade involution for every bilinear form. In particular
`CliffordAlgebra.equivExterior` intertwines both operations with those of the exterior algebra.

## Main results

* `CliffordAlgebra.contractLeft_map`: contraction is natural under quadratic isometries.

* `CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**.
* `CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.
* `CliffordAlgebra.contractLeft_mul`: the graded Leibniz rule
  `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.
* `CliffordAlgebra.contractLeft_mul_ι` and `CliffordAlgebra.contractRight_ι_mul`: the graded
  Leibniz rules for a vector factor on the far side.
* `CliffordAlgebra.contractRight_contractLeft`: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`.
* `CliffordAlgebra.contractLeft_prod_map_ι_eq_zero`: a contraction kills a product of vectors in
  its kernel.
* `CliffordAlgebra.changeForm_mul_ι`: `changeForm` on a right vector factor.
* `CliffordAlgebra.changeForm_involute` and `CliffordAlgebra.changeForm_reverse`: `changeForm`
  commutes with the grade involution, and with reversion for a symmetric form.
* `CliffordAlgebra.equivExterior_involute` and `CliffordAlgebra.equivExterior_reverse`: the same
  for the isomorphism with the exterior algebra.
* `CliffordAlgebra.equivExterior_mem_evenOdd_iff`: that isomorphism preserves the `ℤ/2`-grading.
* `CliffordAlgebra.equivExterior_ι_mul` and `CliffordAlgebra.equivExterior_mul_ι`: that
  isomorphism on left and right vector factors.
* `CliffordAlgebra.equivExterior_prod_map_ι_of_pairwise_isOrtho`: that isomorphism sends a product
  of pairwise orthogonal vectors to their exterior product.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/

public section


universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

section Naturality

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Contraction against a linear functional commutes with the algebra map induced by a
quadratic isometry, after pulling back the functional. -/
theorem contractLeft_map (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂)
    (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, contractLeft_ι_mul, hx, map_sub,
      map_smul, LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap]

end Naturality

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) := by
  -- Two parity facts, used to keep the indices in `ZMod 2` honest.
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  have hshift : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_range_ι_pow_zero hv
      simp
    · obtain ⟨a, rfl⟩ := exists_ι_of_mem_range_ι_pow_one hv
      rw [contractLeft_ι, hone]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h₂ : ι Q m₂ * x ∈ evenOdd Q (i + 1) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) hx
    have h₁ : contractLeft d (ι Q m₂ * x) ∈ evenOdd Q i := by
      rw [contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hx) ?_
      simpa only [hshift] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) ih
    rw [mul_assoc, contractLeft_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ h₂) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₁) h₁

/-- **The graded Leibniz rule for contraction.** Contraction against `d` is a derivation twisted
by the grade involution: `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.  On a homogeneous
multivector `x` of degree `n` the involution is the sign `(-1) ^ n`, which gives the familiar
odd-derivation rule. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) = contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; abel
  | ι_mul x a hx =>
    rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, neg_mul, mul_assoc]
    abel

/-- **The graded Leibniz rule for a right vector factor.** Contraction against `d` passes through
a right factor `ι Q m`, at the cost of the term `d m • involute x` produced by contracting that
factor itself after it has moved past `x`. -/
theorem contractLeft_mul_ι (d : Module.Dual R M) (x : CliffordAlgebra Q) (m : M) :
    contractLeft d (x * ι Q m) = contractLeft d x * ι Q m + d m • involute x := by
  rw [contractLeft_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The graded Leibniz rule for right contraction and a left vector factor**, the mirror image of
`CliffordAlgebra.contractLeft_mul_ι` under reversion: `(ι Q a * x) ⌊ d` is
`ι Q a * (x ⌊ d) + d a • involute x`. -/
theorem contractRight_ι_mul (d : Module.Dual R M) (a : M) (x : CliffordAlgebra Q) :
    contractRight (ι Q a * x) d = ι Q a * contractRight x d + d a • involute x := by
  simp [contractRight_eq, contractLeft_mul_ι, reverse_involute_commute.eq]

/-- **Left and right contraction commute**: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`. This is the statement
left as a `TODO` after `CliffordAlgebra.contractRight_comm` in Mathlib. -/
theorem contractRight_contractLeft (d d' : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractRight (contractLeft d x) d' = contractLeft d (contractRight x d') := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x a hx =>
    simp [contractLeft_ι_mul, contractRight_ι_mul, hx, involute_contractLeft]
    abel

/-- Contraction against a functional `d` kills a product of vectors that `d` annihilates. -/
theorem contractLeft_prod_map_ι_eq_zero (d : Module.Dual R M) {l : List M}
    (h : ∀ m ∈ l, d m = 0) : contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h a List.mem_cons_self, zero_smul,
      ih fun m hm ↦ h m (List.mem_cons_of_mem a hm), mul_zero, sub_zero]

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}
  (h : B.toQuadraticMap = Q' - Q)

/-- **`changeForm` and a right vector factor**: the right-handed counterpart of Mathlib's
`CliffordAlgebra.changeForm_ι_mul`, in which the correction term contracts from the right against
the functional `B.flip m = B · m`. No symmetry of `B` is needed. -/
theorem changeForm_mul_ι (x : CliffordAlgebra Q) (m : M) :
    changeForm h (x * ι Q m) =
      changeForm h x * ι Q' m - contractRight (changeForm h x) (B.flip m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.commutes, changeForm_ι_mul, changeForm_algebraMap, contractLeft_algebraMap,
      contractRight_algebraMap, sub_zero, sub_zero, Algebra.commutes]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, LinearMap.add_apply]
    abel
  | ι_mul x a hx =>
    simp [mul_assoc, changeForm_ι_mul, hx, contractLeft_mul_ι, contractRight_contractLeft,
      contractRight_ι_mul, mul_sub, sub_mul]
    abel

/-- **`changeForm` commutes with the grade involution**, for every bilinear form `B`. -/
@[simp]
theorem changeForm_involute (x : CliffordAlgebra Q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_ι_mul, hx, involute_contractLeft]
    abel

/-- **`changeForm` commutes with reversion** when the bilinear form `B` is symmetric. This covers
`CliffordAlgebra.equivExterior`, whose bilinear form is the symmetric
`QuadraticMap.associated (-Q)`. -/
theorem changeForm_reverse (hB : LinearMap.IsSymm B) (x : CliffordAlgebra Q) :
    changeForm h (reverse x) = reverse (changeForm h x) := by
  have hflip : B.flip=B := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact hB.eq b a
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_mul_ι, hx, changeForm_ι_mul, contractRight_eq,hflip]

end changeForm

section equivExterior

variable [Invertible (2 : R)] (Q)

/-- `CliffordAlgebra.equivExterior` on a left vector factor: the specialization of Mathlib's
`CliffordAlgebra.changeForm_ι_mul` to the bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_ι_mul (m : M) (x : CliffordAlgebra Q) :
    equivExterior Q (ι Q m * x) =
      ExteriorAlgebra.ι R m * equivExterior Q x -
        contractLeft (QuadraticMap.associated (-Q) m) (equivExterior Q x) :=
  changeForm_ι_mul changeForm.associated_neg_proof m x

/-- `CliffordAlgebra.equivExterior` on a right vector factor: the specialization of
`CliffordAlgebra.changeForm_mul_ι` to the symmetric bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_mul_ι (x : CliffordAlgebra Q) (m : M) :
    equivExterior Q (x * ι Q m) =
      equivExterior Q x * ExteriorAlgebra.ι R m -
        contractRight (equivExterior Q x) (QuadraticMap.associated (-Q) m) := by
  rw [← QuadraticMap.associated_flip]
  exact changeForm_mul_ι changeForm.associated_neg_proof x m

/-- `CliffordAlgebra.equivExterior` intertwines the grade involutions.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, where `CliffordAlgebra.changeForm_involute` applies. -/
theorem equivExterior_involute (x : CliffordAlgebra Q) :
    equivExterior Q (involute x) = involute (equivExterior Q x) :=
  changeForm_involute changeForm.associated_neg_proof x

/-- **`CliffordAlgebra.equivExterior` preserves the `ℤ/2`-grading**: a Clifford element has
parity `i` exactly when its image in the exterior algebra has parity `i`. -/
theorem equivExterior_mem_evenOdd_iff {i : ZMod 2} {x : CliffordAlgebra Q} :
    equivExterior Q x ∈ evenOdd (0 : QuadraticForm R M) i ↔ x ∈ evenOdd Q i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · rw [← involute_eq_self_iff, ← involute_eq_self_iff, ← equivExterior_involute,
      (equivExterior Q).injective.eq_iff]
  · rw [← involute_eq_neg_iff, ← involute_eq_neg_iff, ← equivExterior_involute, ← map_neg,
      (equivExterior Q).injective.eq_iff]

/-- `CliffordAlgebra.equivExterior` intertwines reversion, because the bilinear form
`QuadraticMap.associated (-Q)` it changes the form by is symmetric.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_reverse (x : CliffordAlgebra Q) :
    equivExterior Q (reverse x) = reverse (equivExterior Q x) :=
  changeForm_reverse changeForm.associated_neg_proof (QuadraticForm.associated_isSymm R (-Q)) x

/-- **`CliffordAlgebra.equivExterior` sends a product of pairwise orthogonal vectors to their
exterior product.** Each correction term of `CliffordAlgebra.equivExterior_ι_mul` contracts the
later factors against the first, and vanishes by orthogonality. No hypothesis on `Q` is needed;
in particular `Q` may be degenerate. -/
theorem equivExterior_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    equivExterior Q (l.map (ι Q)).prod = (l.map (ExteriorAlgebra.ι R)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, equivExterior_ι_mul, ih hl.2,
      contractLeft_prod_map_ι_eq_zero, sub_zero, List.map_cons, List.prod_cons]
    intro m hm
    simp [hl.1 m hm]

end equivExterior

end CliffordAlgebra
end
end TAF_LiteralSource_0208

section TAF_LiteralSource_0209
/- Original module: TauCeti.LinearAlgebra.ExteriorPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module, and that exterior powers of projective
modules are projective.

It then builds the surjection `exteriorPower.fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M` that is
left inverse, up to the factor `n!`, to Mathlib's antisymmetrization
`exteriorPower.toTensorPower`: composing the antisymmetrization with it is `n! • id` on the exterior
power, while composing the two the other way round is the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. Consequently the antisymmetrization is injective once `n!` is a
unit in the base ring, and its image is the image of that operator. That is the statement a Young
symmetrizer of a one-column shape consumes.

Finally, it describes images of exterior powers under induced maps: inside the exterior algebra,
the image of `⋀ⁿ M` under `f` is the `n`th power of the degree-one image of `f`, and over a field an
injective map embeds `⋀ⁿ V` with its binomial dimension.

## Main definitions

* `exteriorPower.fromTensorPower` is the canonical surjection of the tensor power onto the
  exterior power.
## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.instProjective`: exterior powers of projective modules are projective.
* `exteriorPower.fromTensorPower_comp_toTensorPower`: antisymmetrizing and projecting back is
  multiplication by `n!`, whence `exteriorPower.toTensorPower_injective`.
* `exteriorPower.ιMulti_ne_zero_iff`: over a field, an exterior product of vectors is nonzero
  exactly when the vectors are linearly independent.
* `exteriorPower.toTensorPower_injective_of_free`: antisymmetrization is injective for free
  modules in every characteristic, without factorial invertibility.
* `exteriorPower.range_toTensorPower`: the image of the antisymmetrization is the image of the
  antisymmetrization operator on the tensor power.
* `exteriorPower.map_bijective`: a bijective linear map induces bijections of exterior powers.
* `exteriorPower.toTensorPower_comp_map` and `exteriorPower.map_comp_fromTensorPower`: the
  antisymmetrization and the canonical surjection are natural in the module.
* `TauCeti.ExteriorAlgebra.exteriorPower_map_map`: the image of `⋀ⁿ M` in the exterior algebra
  under the map induced by `f` is the `n`th power of the degree-one image of `f`.
* `TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one` and
  `TauCeti.ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one`: the first exterior power consists of
  the vectors, and `ExteriorAlgebra.ιInv` recovers the vector from its image.
* `TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower` and `TauCeti.ExteriorAlgebra.wedgeLeft`:
  left multiplication by a vector carries `⋀ⁿ M` into `⋀ⁿ⁺¹ M`, packaged as the linear map
  `v ↦ m ∧ v` with values in degree `n + 1`.
* `TauCeti.exteriorPower.finrank_range_map`: over a field, the image of `⋀ⁿ V` under the map
  induced by an injective linear map has dimension `(dim V).choose n`.
* `TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero`: over a field, a vector lies in
  the span of a linearly independent family exactly when its product with the exterior product of
  the family vanishes.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

/-! ### Antisymmetrization of free modules -/

section Free

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Pairing with a pure exterior product of linear forms factors through the
antisymmetrization into the tensor power. -/
theorem pairingDual_ιMulti_apply {n : ℕ} (g : Fin n → Module.Dual R M) (x : ⋀[R]^n M) :
    pairingDual R M n (ιMulti R n g) x =
      TensorPower.multilinearMapToDual R M n g (toTensorPower R M n x) := by
  simp [pairingDual, alternatingMapToDual]

/-- Antisymmetrization embeds every exterior power of a free module into its tensor power,
over any commutative ring, without requiring the factorial to be invertible. -/
theorem toTensorPower_injective_of_free [Module.Free R M] {n : ℕ} :
    Function.Injective (toTensorPower R M n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  -- Each exterior-basis coordinate factors through antisymmetrization.
  intro x y h
  apply (b.exteriorPower n).repr.injective
  ext s
  rw [basis_repr_apply, basis_repr_apply]
  simp only [ιMultiDual, ιMulti_family, pairingDual_ιMulti_apply, h]

end Free

/-! ### Projectivity -/

section Projective

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Exterior powers of a projective module are projective: `⋀[R]^n M` is a direct summand of the
exterior power of the free module `M →₀ R`. -/
instance instProjective [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  refine .of_split (map n s) (map n (Finsupp.linearCombination R id)) ?_
  rw [← map_comp, hs, map_id]

end Projective

/-! ### The exterior power as a quotient of the tensor power -/

section FromTensorPower

variable [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

variable (R M) in
/-- **The canonical surjection of the tensor power onto the exterior power**, sending a pure
tensor to the corresponding exterior product.

Mathlib's `exteriorPower.toTensorPower` runs the other way, by antisymmetrization; antisymmetrizing
and then projecting back is `n!` on the exterior power, while projecting and then antisymmetrizing
is the antisymmetrization operator `∑_σ sgn(σ) σ` on the tensor power. -/
noncomputable def fromTensorPower : (⨂[R]^n M) →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti R n).toMultilinearMap

@[simp]
theorem fromTensorPower_tprod (m : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod R m) = ιMulti R n m :=
  PiTensorProduct.lift.tprod m

theorem fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod R v, fromTensorPower_tprod n v⟩

/-- Antisymmetrizing an exterior product and projecting it back multiplies by `n!`: each of the
`n!` signed reorderings returns the same exterior product. -/
@[simp]
theorem fromTensorPower_comp_toTensorPower :
    (fromTensorPower R M n) ∘ₗ (toTensorPower R M n) =
      n.factorial • LinearMap.id (R := R) (M := ⋀[R]^n M) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) * ((Equiv.Perm.sign σ : ℤ)) = 1 := fun σ => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have h : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) • ιMulti R n (fun i => v (σ i)) = ιMulti R n v := fun σ => by
    rw [← Function.comp_def v σ, (ιMulti R n).map_perm, Units.smul_def, smul_smul, hsq, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_apply_ιMulti, map_sum]
  simp only [Units.smul_def, map_zsmul, fromTensorPower_tprod, h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- The antisymmetrization is injective as soon as `n!` is a unit in the base ring, for instance
over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit (n.factorial : R)) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the canonical surjection by `u⁻¹` makes it a left inverse of the antisymmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • fromTensorPower R M n) ?_
  rw [LinearMap.smul_comp, fromTensorPower_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← hu, u.inv_mul, one_smul]

/-- Projecting a tensor to the exterior power and antisymmetrizing it back is the
antisymmetrization operator `∑_σ sgn(σ) σ` of the tensor power. -/
theorem toTensorPower_comp_fromTensorPower :
    (toTensorPower R M n) ∘ₗ (fromTensorPower R M n) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, Function.comp_apply, fromTensorPower_tprod,
    toTensorPower_apply_ιMulti, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
  simp [Units.smul_def, Equiv.Perm.inv_def]

/-- The antisymmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R N n) ∘ₗ (map n f) =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (toTensorPower R M n) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  simp [Units.smul_def, Function.comp_def]

/-- The canonical surjection is natural in the module. -/
theorem map_comp_fromTensorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (map n f) ∘ₗ (fromTensorPower R M n) =
      (fromTensorPower R N n) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [Function.comp_def]

/-- The image of the antisymmetrization is the image of the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R M n) =
      LinearMap.range (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap) := by
  rw [← toTensorPower_comp_fromTensorPower, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fromTensorPower_surjective n), Submodule.map_top]

end FromTensorPower

/-! ### Exterior products over a field -/

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Over a field, the exterior product of `n` vectors is nonzero exactly when they are linearly
independent. -/
theorem ιMulti_ne_zero_iff {n : ℕ} (v : Fin n → V) :
    ιMulti K n v ≠ 0 ↔ LinearIndependent K v := by
  refine ⟨fun h ↦ by_contra fun hv ↦ h ((ιMulti K n).map_linearDependent v hv), fun hv ↦ ?_⟩
  -- The only `n`-element subset of `Fin n` is enumerated by the identity.
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ⇑(Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hs)) = id := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique hs (fun _ ↦ Finset.mem_univ _) strictMono_id).symm
  simpa [ιMulti_family, he] using (ιMulti_family_linearIndependent_field (n := n) hv).ne_zero
    (Set.powersetCard.ofCard hs)

end Field

/-! ### Bijectivity of induced maps -/

section Bijective

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- A bijective linear map induces a bijective map on every exterior power. -/
theorem map_bijective {n : ℕ} {f : M →ₗ[R] N} (hf : Function.Bijective f) :
    Function.Bijective (map n f) :=
  ⟨map_injective (LinearEquiv.ofBijective f hf).symm.toLinearMap (by ext; simp),
    map_surjective hf.2⟩

end Bijective

end exteriorPower

namespace TauCeti

namespace ExteriorAlgebra

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- Inside the exterior algebra, the image of the `n`th exterior power under the map induced by
`f` is the `n`th power of the degree-one image of the range of `f`. -/
theorem exteriorPower_map_map (n : ℕ) (f : M →ₗ[R] N) :
    (⋀[R]^n M).map (_root_.ExteriorAlgebra.map f).toLinearMap =
      ((LinearMap.range f).map (_root_.ExteriorAlgebra.ι R)) ^ n := by
  rw [_root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    _root_.ExteriorAlgebra.ι_range_map_map]

/-- A vector lies in the first exterior power. -/
theorem ι_mem_exteriorPower_one (m : M) : _root_.ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ m

/-- An element of the first exterior power is the vector `ExteriorAlgebra.ιInv` reads off from
it. -/
theorem ι_ιInv_of_mem_exteriorPower_one {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^1 M) :
    _root_.ExteriorAlgebra.ι R (_root_.ExteriorAlgebra.ιInv x) = x := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  rw [_root_.ExteriorAlgebra.ι_leftInverse]

/-- Left multiplication by a vector raises the exterior degree by one: it carries the `n`-th
exterior power into the `(n + 1)`-th. -/
theorem ι_mul_mem_exteriorPower (m : M) {n : ℕ} {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    _root_.ExteriorAlgebra.ι R m * x ∈ ⋀[R]^(n + 1) M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) hx

/-- Exterior multiplication `v ↦ m ∧ v` by a vector `m`, from the `n`-th exterior power to the
`(n + 1)`-th. Mathlib's `exteriorPower.wedge R M 1 n` is the same product with values in degree
`1 + n`, which is not definitionally `n + 1`; this form composes with maps out of `⋀ⁿ⁺¹ M`. -/
def wedgeLeft (m : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R m)).restrict fun _ hx ↦
    ι_mul_mem_exteriorPower m hx

/-- `wedgeLeft m n` is left multiplication by `ι R m` in the exterior algebra. -/
@[simp]
theorem coe_wedgeLeft_apply (m : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft m n x : _root_.ExteriorAlgebra R M) = _root_.ExteriorAlgebra.ι R m * x :=
  (rfl)

/-- `wedgeLeft m n` prepends `m` to a wedge product of vectors: `m ∧ (v₀ ∧ ⋯ ∧ vₙ₋₁)`. -/
@[simp]
theorem wedgeLeft_ιMulti (m : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft m n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R (n + 1) (Fin.cons m v) := by
  ext
  simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

end ExteriorAlgebra

namespace exteriorPower

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W]

/-- Over a field, the image of the `n`th exterior power of a finite-dimensional space under the
map induced by an injective linear map has dimension `(dim V).choose n`. -/
theorem finrank_range_map {f : V →ₗ[K] W} (hf : Function.Injective f) (n : ℕ) :
    Module.finrank K (LinearMap.range (_root_.exteriorPower.map n f)) =
      (Module.finrank K V).choose n := by
  rw [LinearMap.finrank_range_of_inj (_root_.exteriorPower.map_injective_field hf),
    _root_.exteriorPower.finrank_eq]

omit [Module.Finite K V] in
/-- Over a field, a vector lies in the span of a linearly independent family of `n` vectors exactly
when its product with the exterior product of the family vanishes in the exterior algebra. -/
theorem mem_span_range_iff_ι_mul_ιMulti_eq_zero {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (w : V) :
    w ∈ Submodule.span K (Set.range v) ↔
      _root_.ExteriorAlgebra.ι K w * (_root_.exteriorPower.ιMulti K n v : ExteriorAlgebra K V) =
        0 := by
  have hcons : w ∈ Submodule.span K (Set.range v) ↔
      ¬LinearIndependent K (Fin.cons w v : Fin (n + 1) → V) := by
    rw [linearIndependent_finCons]
    tauto
  rw [hcons, ← _root_.exteriorPower.ιMulti_ne_zero_iff, not_not, ← ZeroMemClass.coe_eq_zero,
    _root_.exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_succ_apply,
    _root_.exteriorPower.ιMulti_apply_coe]
  simp [Matrix.vecTail, Function.comp_def]

end exteriorPower

end TauCeti
end
end TAF_LiteralSource_0209

section TAF_LiteralSource_0210
/- Original module: TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.

Each of the two halves acts on an exterior basis vector by a single coordinate move, up to the
shuffle sign that carries the moved coordinate to the front: contraction erases the coordinate
from the index set, and left multiplication inserts it, each vanishing when the index set is on
the wrong side of that move. Creation after contraction at distinct coordinates therefore
replaces an occupied coordinate with an unoccupied one, with the product of their shuffle signs.

The grade involution is diagonal for the exterior basis as well: it multiplies an exterior
monomial, and so the basis vector indexed by `s`, by the parity of its degree.

Every basis vector is the product of the exterior-algebra generators of its index set, in
increasing order; for index sets with one or two elements this is also recorded in the explicit
forms `TauCeti.ExteriorAlgebra.basis_singleton` and `TauCeti.ExteriorAlgebra.basis_pair`.

Independently of a basis, `ExteriorAlgebra.contractLeft_map` states naturality under a linear
map: pull back the contracting functional and then map the contracted element. This follows
from the general quadratic-isometry statement `CliffordAlgebra.contractLeft_map`.

Independently of a basis, the grade involution is the sign `(-1) ^ n` on the `n`-th exterior power,
a contraction carries the `(n + 1)`-th exterior power into the `n`-th, and a vector graded-commutes
with every multivector: `ι m * x = involute x * ι m`.  Together with the graded Leibniz rule
`CliffordAlgebra.contractLeft_mul`, these say that a contraction is an odd derivation of degree
`-1` of the graded-commutative exterior algebra. On a wedge product of vectors it is the alternating
sum of deletions (`TauCeti.ExteriorAlgebra.contractLeft_ιMulti`); this is the differential of the
Koszul complex.

In degree at least the rank, contraction loses no information: if `d m = 1` and
`finrank R M ≤ n`, every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. Hence two forms killed by `d` multiply to
zero once their degrees add up to the rank, and in rank at most four a two-form `x` satisfies
`x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. This is the algebra behind the splitting of a two-form on a product
`ℝ × Y` along the unit normal of the factor `Y`.

On `M × R`, with `e = (0, 1)`, every element `z` of the exterior algebra splits as `a + e ∧ b`,
where `a` and `b` are the images in `⋀ M` of `z` and of its contraction by the second coordinate
(`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`). This is the
decomposition `⋀ᵏ⁺¹ (M × R) ≅ ⋀ᵏ⁺¹ M ⊕ e ∧ ⋀ᵏ M` used to adjoin one element to a Koszul complex.
In this splitting, the contraction by `φ + x · snd` acts as `d(a + e ∧ b) = (d a + x b) - e ∧ d b`
(`ExteriorAlgebra.map_fst_contractLeft_coprod`,
`ExteriorAlgebra.contractLeft_map_fst_contractLeft_snd`).
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An exterior-basis vector is the product of its generators in increasing order**: the basis
vector indexed by `s` is `ι (b i₁) * ⋯ * ι (b iₖ)` for `s.sort = [i₁, …, iₖ]`. -/
theorem _root_.Module.Basis.exteriorAlgebra_eq_prod_map_sort {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s = ((s.sort.map b).map (ExteriorAlgebra.ι R)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  congr 1
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard]
  exact congrArg (fun i ↦ ExteriorAlgebra.ι R (b i)) (Finset.orderEmbOfFin_apply _ _ _)

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  refine contractLeft_prod_map_ι_eq_zero _ fun m hm ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff]
  rintro rfl
  exact absurd ((Finset.mem_sort _).mp hj) hi

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

/-- **The grade involution acts on an exterior-basis vector by the parity of its index set.** The
basis vector indexed by `s` is the monomial on `s.card` generators. -/
@[simp]
theorem involute_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (b.ExteriorAlgebra s) =
      (-1 : R) ^ s.card • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  exact involute_ιMulti _

private def basisEraseSignOfErase {I : Type w} [LinearOrder I]
    (i : I) (t : Finset I) (hi : i ∉ t) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t' : Set.powersetCard I t.card := ⟨t, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t') (by simp [u, t', hi])).sign

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  basisEraseSignOfErase i (s.erase i) (by simp)

private theorem basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem
    {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) (hi : i ∈ s) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  let n := (s.erase i).card
  have hsCard : s.card = n + 1 := by
    simpa [n] using (Finset.card_erase_add_one hi).symm
  -- Enumerate `s` in increasing order. The position `k` of `i` counts precisely the entries
  -- which the shuffle crosses when it moves the singleton `{i}` to the front.
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i := by
    exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) =
      (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr ⟨fun h ↦ k.succAbove_ne j (e.injective (h.trans hek.symm)),
        Finset.orderEmbOfFin_mem s hsCard _⟩
    · exact e.strictMono.comp (Fin.strictMono_succAbove k)
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hsCard' : s.card = 1 + n := hsCard.trans (Nat.add_comm n 1)
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) hsCard' : Set.powersetCard I (1 + n)) := by
    apply Subtype.ext
    simp [u, t, hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  let p' : Equiv.Perm (Fin (n + 1)) := c.symm.trans (p.trans c)
  -- After reconciling the two cardinality presentations, this shuffle is the inverse cycle
  -- which moves position `k` to the front and shifts the preceding positions one step right.
  have hec : (fun q ↦ e (c q)) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop := by
    apply Finset.orderEmbOfFin_unique
    · intro q
      have hdval : (Set.powersetCard.disjUnion hdisj).val = s :=
        congrArg Subtype.val hunion
      rw [hdval]
      exact Finset.orderEmbOfFin_mem s hsCard (c q)
    · intro a b hab
      apply e.strictMono
      simpa [c, Fin.ext_iff] using hab
  have hp : p' = k.cycleRange.symm := by
    apply Equiv.ext
    intro j
    apply e.injective
    -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    -- The disjoint-union permutation enumerates the singleton first and the erased set second.
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    -- Expose the function represented by the increasing enumeration before applying `hec`.
    change (fun q ↦ e (c q)) (p (c.symm j)) = _
    rw [hec]
    let x : (Set.powersetCard.disjUnion hdisj).val :=
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm (c.symm j)))
    have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop (p (c.symm j)) = x := by
      have hpApply : p (c.symm j) =
          (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).symm x := rfl
      rw [hpApply]
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).apply_symm_apply x)
    rw [hx]
    cases j using Fin.cases with
    | zero =>
        have hzero : finSumFinEquiv.symm (c.symm 0) = Sum.inl (0 : Fin 1) := by
          apply finSumFinEquiv.injective
          apply Fin.ext
          rfl
        simp only [x, hzero, Fin.cons_zero]
        -- Coercing the disjoint-union subtype reveals the singleton entry.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        -- The unique increasing enumeration of a singleton is constant at its element.
        change Finset.orderEmbOfFin {i} (Finset.card_singleton i) 0 = i
        exact Finset.orderEmbOfFin_singleton i 0
    | succ q =>
        have hsucc : finSumFinEquiv.symm (c.symm q.succ) = Sum.inr q := by
          apply finSumFinEquiv.injective
          rw [finSumFinEquiv.apply_symm_apply]
          apply Fin.ext
          simp [c]
          omega
        simp only [x, hsucc, Fin.cons_succ]
        -- Coercing the right summand reveals the increasing enumeration of `s.erase i`.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inr ((Set.powersetCard.orderIsoOfFin t) q))) =
            (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rw [Equiv.Finset.disjUnionEquiv_inr]
        dsimp only [Set.powersetCard.orderIsoOfFin, t]
        change (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q =
          (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rfl
  have hsign : Equiv.Perm.sign p' = Equiv.Perm.sign p := by
    simp [p']
  rw [basisEraseSign]
  -- Unfolding the local permutation exposes the sign computed above.
  change Equiv.Perm.sign p = _
  rw [← hsign, hp, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  congr 1
  -- The initial segment below `k` is order-isomorphic to the elements of `s` strictly below `i`,
  -- so its cardinality is the exponent in the claimed sign.
  have himage : Finset.image e (Finset.Iio k) = s.filter (fun j ↦ j < i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hsCard j, hek ▸ e.strictMono hj⟩
    · rintro ⟨hxs, hxi⟩
      let j : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨x, hxs⟩
      refine ⟨j, ?_, ?_⟩
      · exact e.lt_iff_lt.mp (by simpa [e, j, k] using hxi)
      · exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨x, hxs⟩)
  rw [← Fin.card_Iio k, ← himage, Finset.card_image_of_injective _ e.injective]

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. This formula also applies when `i ∉ s`: inserting
`i` changes neither the erased set defining the shuffle nor the indices strictly below `i`. -/
@[simp]
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  by_cases hi : i ∈ s
  · exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i s hi
  · have hsign : basisEraseSign i (insert i s) = basisEraseSign i s := by
      simp [basisEraseSign, hi]
    have hfilter : (insert i s).filter (fun j ↦ j < i) = s.filter (fun j ↦ j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hji' | hjs, hji⟩
        · exact ((ne_of_lt hji) hji').elim
        · exact ⟨hjs, hji⟩
      · exact fun h ↦ ⟨Or.inr h.1, h.2⟩
    rw [← hsign, ← hfilter]
    exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i (insert i s)
      (Finset.mem_insert_self i s)

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  simp [b.exteriorAlgebra_eq_prod_map_sort]

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,
    Finset.sort_insert _ (by simpa using hij.le) (by simpa using hij.ne)]
  simp

/-- Multiplying the basis vector for `i` by the basis vector for `s.erase i` reconstructs the
basis vector for `s`, with the shuffle sign that moves `i` to the front. -/
theorem basis_singleton_mul_basis_erase {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
      basisEraseSign i s • b.ExteriorAlgebra s := by
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, u, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b u t hdisj
  rw [hunion] at hprod
  simpa [basisEraseSign, basisEraseSignOfErase, u, t] using hprod

/-- **Creating a basis coordinate inserts it into the index set**, with the shuffle sign that
moves it to the front; it is zero when the coordinate is already present, since a repeated
generator squares to zero. -/
@[simp]
theorem ι_mul_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0
        else basisEraseSign i (insert i s) • b.ExteriorAlgebra (insert i s) := by
  classical
  rw [← basis_singleton]
  split_ifs with hi
  · exact ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1) (⟨s, rfl⟩ : Set.powersetCard I s.card)
      (by simp [hi])
  · have h := basis_singleton_mul_basis_erase b i (insert i s) (Finset.mem_insert_self i s)
    rwa [Finset.erase_insert hi] at h

/-- Contracting an exterior-basis vector erases the contracted coordinate, with the shuffle sign
that moves that coordinate to the front; it is zero when the coordinate is absent. -/
@[simp]
theorem contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  split_ifs with hi
  · have hprod' := basis_singleton_mul_basis_erase b i s hi
    have hcontract : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
        (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra (s.erase i) := by
      rw [basis_singleton, contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_coord_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign
    · rw [hsign, one_smul] at hprod' ⊢
      rw [← hprod']
      exact hcontract
    · have hprodNeg : b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
          -b.ExteriorAlgebra s := by
        rw [hsign] at hprod'
        simpa using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      rw [hsign]
      simpa using h
  · exact contractLeft_coord_basis_eq_zero_of_not_mem b i s hi

/-- Creating an unoccupied coordinate after contracting an occupied one replaces that
coordinate in an exterior-basis vector, with the product of the two shuffle signs. -/
theorem ι_mul_contractLeft_coord_basis_of_not_mem_of_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i j : I) (s : Finset I) (hi : i ∉ s) (hj : j ∈ s) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord j) (b.ExteriorAlgebra s) =
      (basisEraseSign j s * basisEraseSign i (insert i (s.erase j))) •
        b.ExteriorAlgebra (insert i (s.erase j)) := by
  classical
  simp [contractLeft_coord_basis, ι_mul_basis, hi, hj, mul_smul_comm, smul_smul]

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate.

This is not a `simp` lemma because `contractLeft_coord_basis` is the canonical normal form for
the contraction in its left-hand side. -/
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [contractLeft_coord_basis]
  split_ifs with hi
  · rw [← basis_singleton]
    rw [mul_smul_comm]
    rw [basis_singleton_mul_basis_erase b i s hi]
    let n := (s.filter fun j ↦ j < i).card
    have hsignSq : ((-1 : ℤˣ) ^ n) * ((-1 : ℤˣ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [basisEraseSign_eq_neg_one_pow_card_filter_lt, smul_smul, hsignSq, one_smul]
  · rw [mul_zero]

/-! ### Exterior powers under the grade involution and contraction -/

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- Contraction annihilates the zeroth exterior power, the scalars. -/
theorem contractLeft_eq_zero_of_mem_exteriorPower_zero (d : Module.Dual R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x = 0 := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact contractLeft_algebraMap (Q := (0 : QuadraticForm R M)) d r

/-- **Contraction lowers the exterior degree by one**: it carries the `(n + 1)`-th exterior power
into the `n`-th. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih

/-- **Contraction of a wedge product of vectors** is the alternating sum of the contractions of
its factors: `d ⌋ (v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i d(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (v i)) •
        ExteriorAlgebra.ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hrem (i : Fin (n + 1)) : ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
        ExteriorAlgebra.ι R (v 0) *
          ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      ext j
      simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1),
      Finset.mul_sum]
    simp [hrem, pow_succ, sub_eq_add_neg, Matrix.vecTail, Fin.tail,
      Function.comp_def]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction against a functional commutes with an exterior-algebra map after pulling
back the functional. -/
theorem contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R N)) d (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f
        (contractLeft (Q := (0 : QuadraticForm R M)) (d ∘ₗ f) x) := by
  -- The exterior-algebra map is the zero-quadratic-form case of the Clifford-algebra map.
  exact CliffordAlgebra.contractLeft_map { f with map_app' := fun _ => rfl } d x

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction in degree at least the rank -/

variable [Module.Free R M] [Module.Finite R M]

/-- **A form of degree at least the rank is divisible by any vector `m` with `d m = 1`**: if
`d m = 1` and `finrank R M ≤ n`, then every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. -/
theorem eq_ι_mul_contractLeft_of_finrank_le {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {n : ℕ} (hn : Module.finrank R M ≤ n) {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    x = ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x := by
  -- `m ∧ x` lies above the rank, so it vanishes, and contracting it by `d` gives the claim.
  have h0 : ι R m * x = 0 := ZeroMemClass.coe_eq_zero.mpr <|
    exteriorPower.eq_zero_of_finrank_lt (1 + n) (by omega)
      ⟨_, SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) hx⟩
  have h := congrArg (contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  rwa [contractLeft_ι_mul, hdm, one_smul, map_zero, sub_eq_zero] at h

/-- **Forms killed by a contraction multiply to zero in degree at least the rank**: if `d m = 1`,
the forms `x ∈ ⋀ᵏ M` and `y ∈ ⋀ˡ M` satisfy `d ⌋ x = 0` and `d ⌋ y = 0`, and
`finrank R M ≤ k + l`, then `x ∧ y = 0`. -/
theorem mul_eq_zero_of_contractLeft_eq_zero {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {k l : ℕ} (hkl : Module.finrank R M ≤ k + l) {x y : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) (hy : y ∈ ⋀[R]^l M)
    (hdx : contractLeft (Q := (0 : QuadraticForm R M)) d x = 0)
    (hdy : contractLeft (Q := (0 : QuadraticForm R M)) d y = 0) : x * y = 0 := by
  rw [eq_ι_mul_contractLeft_of_finrank_le hdm hkl (SetLike.mul_mem_graded hx hy), contractLeft_mul,
    hdx, hdy, zero_mul, mul_zero, add_zero, mul_zero]

/-- **The square of a two-form in rank at most four.** If `d m = 1` and `finrank R M ≤ 4`, a
two-form `x` satisfies `x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. -/
theorem mul_self_eq_two_smul_mul_ι_mul_contractLeft {d : Module.Dual R M} {m : M}
    (hdm : d m = 1) (h4 : Module.finrank R M ≤ 4) {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^2 M) :
    x * x = 2 • (x * (ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x)) := by
  -- Write `x = m ∧ a + b` with `a = d ⌋ x`. Then `d ⌋ b = 0`, so `b ∧ b = 0` in rank at most
  -- four; also `(m ∧ a) ∧ (m ∧ a) = 0`, and the two-forms `m ∧ a` and `b` commute.
  -- The contraction `d ⌋ x` is a vector `a`.
  obtain ⟨a, ha⟩ : ∃ a, ι R a = contractLeft (Q := (0 : QuadraticForm R M)) d x :=
    ⟨_, ι_ιInv_of_mem_exteriorPower_one (contractLeft_mem_exteriorPower d (n := 1) hx)⟩
  rw [← ha]
  set g := ι R m * ι R a with hg
  have hgmem : g ∈ ⋀[R]^2 M :=
    SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) (ι_mem_exteriorPower_one a)
  -- The remainder `b = x - m ∧ a` is a two-form killed by `d`.
  set b := x - g with hb
  have hbmem : b ∈ ⋀[R]^2 M := sub_mem hx hgmem
  have hdb : contractLeft (Q := (0 : QuadraticForm R M)) d b = 0 := by
    have hda : contractLeft (Q := (0 : QuadraticForm R M)) d (ι R a) = 0 := by
      rw [ha, contractLeft_contractLeft]
    rw [hb, map_sub, hg, contractLeft_ι_mul, hdm, one_smul, hda, mul_zero, sub_zero, ha,
      sub_self]
  have hbb : b * b = 0 :=
    mul_eq_zero_of_contractLeft_eq_zero hdm (by omega) hbmem hbmem hdb hdb
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := R) a m
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι R m * (ι R a * ι R m) * ι R a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv : involute (Q := (0 : QuadraticForm R M)) b = b := by
    rw [involute_of_mem_exteriorPower hbmem]
    simp
  have hcomm : g * b = b * g := by
    rw [hg, mul_assoc, ι_mul_eq_involute_mul a b, hinv, ← mul_assoc, ι_mul_eq_involute_mul m b,
      hinv, mul_assoc]
  have hx' : x = b + g := (sub_add_cancel x g).symm
  rw [hx', add_mul, mul_add, mul_add, hbb, hgg, hcomm, add_mul, hgg, two_smul]
  abel

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Splitting off a free coordinate -/

/-- **Splitting off a free coordinate.** In the exterior algebra of `M × R`, with `e = (0, 1)`,
every element `z` is `a + e ∧ b`, where `a` is the image of `z` under `⋀ M × R → ⋀ M → ⋀ (M × R)`
and `b` is the image of the contraction of `z` by the second coordinate. -/
theorem map_inl_map_fst_add_ι_inr_mul_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.inl R M R) (map (LinearMap.fst R M R) z) +
        ι R (LinearMap.inr R M R 1) * map (LinearMap.inl R M R) (map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, mul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel
  | ι_mul z m ih =>
    -- Write `m = (m₁, 0) + m₂ e`; then `e ∧ e = 0` and `(m₁, 0) ∧ e = -(e ∧ (m₁, 0))`.
    have hm : ι R m = ι R (LinearMap.inl R M R m.1) + m.2 • ι R (LinearMap.inr R M R 1) := by
      rw [← map_smul, ← map_add]; congr 1; ext <;> simp
    have he := ι_sq_zero (R := R) (LinearMap.inr R M R (1 : R))
    have hc := eq_neg_of_add_eq_zero_right <|
      ι_add_mul_swap (R := R) (LinearMap.inr R M R (1 : R)) (LinearMap.inl R M R m.1)
    -- `left_induction` states the step with `CliffordAlgebra.ι 0`, which is `ι R` by definition.
    change _ = ι R m * z
    rw [contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, map_apply_ι]
    conv_rhs => rw [← ih, hm]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc, he, hc,
      smul_zero, add_zero, neg_mul, LinearMap.fst_apply, LinearMap.snd_apply]
    abel

/-! ### Contractions on `M × R` in the splitting `a + e ∧ b` -/

/-- The contraction by `φ.coprod ψ` on the image of `⋀ M` in `⋀ (M × N)` is the contraction
by `φ`. -/
theorem contractLeft_coprod_map_inl {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R M) (ψ : Module.Dual R N) (w : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R (M × N))) (φ.coprod ψ)
        (map (LinearMap.inl R M N) w) =
      map (LinearMap.inl R M N) (contractLeft (Q := (0 : QuadraticForm R M)) φ w) := by
  rw [contractLeft_map, LinearMap.coprod_inl]

/-- The contraction by `φ + x · snd` on `e ∧ w`, with `e = (0, 1)`: `d(e ∧ w) = x w - e ∧ d w`. -/
theorem contractLeft_coprod_ι_inr_mul (φ : Module.Dual R M) (x : R)
    (w : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x)) (ι R (LinearMap.inr R M R 1) * w) =
        x • w - ι R (LinearMap.inr R M R 1) *
          contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) w := by
  rw [contractLeft_ι_mul]
  simp

/-- Projection onto the first factor retracts the induced map of exterior algebras. -/
theorem leftInverse_map_fst_map_inl {N : Type*} [AddCommGroup N] [Module R N] :
    Function.LeftInverse (map (LinearMap.fst R M N)) (map (LinearMap.inl R M N)) :=
  leftInverse_map_iff.2 fun _ ↦ rfl

/-- The `⋀ M`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the `⋀ M`-component of `d z` is `d a + x b`. -/
theorem map_fst_contractLeft_coprod (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (φ.coprod (LinearMap.toSpanSingleton R R x)) z) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R) z) +
        x • map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z) := by
  conv_lhs => rw [← map_inl_map_fst_add_ι_inr_mul_contractLeft_snd z]
  rw [map_add, contractLeft_coprod_map_inl, contractLeft_coprod_ι_inr_mul,
    contractLeft_coprod_map_inl]
  simp only [LinearMap.coe_inr, map_add, map_sub, map_smul, map_mul, map_apply_ι,
    LinearMap.fst_apply, map_zero, zero_mul, sub_zero]
  rw [leftInverse_map_fst_map_inl, leftInverse_map_fst_map_inl]

/-- The `e`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the contraction `d b` is minus the
`e`-component of `d z`. -/
theorem contractLeft_map_fst_contractLeft_snd (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      -map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) z)) := by
  have hD := map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)
  rw [contractLeft_contractLeft, map_zero, map_zero, mul_zero, add_zero] at hD
  rw [← leftInverse_map_fst_map_inl (R := R) (M := M) (N := R) (contractLeft _ _),
    ← contractLeft_coprod_map_inl φ (LinearMap.toSpanSingleton R R x),
    hD, contractLeft_comm, map_neg]

end ExteriorAlgebra
end
end TAF_LiteralSource_0210

section TAF_LiteralSource_0211
/- Original module: PaperVerification.AlternatingFormsLefschetz -/


/-!
# Full symplectic prefix division

This file proves surjectivity of exterior multiplication by the standard
paired two-form from degree `d-1` to degree `d+1` in `2d` variables.  It is
the existence assertion in Lemma 3.1, for every size and every homogeneous
element, using the literal exterior operators.  The explicit Boolean
inverse is developed separately in `AlternatingFormsBoolean` and
`AlternatingFormsExteriorStraightening`.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open PaperVerification.Fermion
open PaperVerification.Fermion.Exterior
open scoped BigOperators

section DegreeLowering

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) R V)

local notation "E" => ExteriorAlgebra R V

theorem lowering_eq_zero_of_degree_lt_two {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (hr : r < 2) : lowering b w = 0 := by
  rw [lowering, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inr i))
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inl i)) w) = 0
  rcases r with _ | r
  · have hz := TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inl i)) hw
    rw [hz, map_zero]
  · have hr0 : r = 0 := by omega
    subst r
    exact TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inr i))
      (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower (b.coord (.inl i)) hw)

theorem lowering_mem_sub_two {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) :
    lowering b w ∈ ⋀[R]^(r - 2) V := by
  by_cases hr : r < 2
  · rw [lowering_eq_zero_of_degree_lt_two b hw hr]
    exact zero_mem _
  · have hr' : r = (r - 2) + 1 + 1 := by omega
    rw [lowering, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i hi
    change annihilation (b.coord (.inr i)) (annihilation (b.coord (.inl i)) w) ∈ _
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    simpa only [← hr'] using hw

theorem lowering_pow_mem {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) (j : ℕ) :
    (lowering b ^ j) w ∈ ⋀[R]^(r - 2 * j) V := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert lowering_mem_sub_two b ih using 1 <;> congr 1 <;> omega

/-- Actual degree lowering proves nilpotence; it is not postulated as an
extra property of the exterior representation. -/
theorem lowering_pow_eq_zero_of_degree_lt {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (j : ℕ) (hrj : r < 2 * j) : (lowering b ^ j) w = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    by_cases hr : r < 2 * j
    · rw [ih hr, map_zero]
    · exact lowering_eq_zero_of_degree_lt_two b (lowering_pow_mem b hw j) (by omega)

/-- The second orientation of the actual `sl₂` relations. -/
theorem swappedRaisingLowering :
    RaisingLowering (raising b) (lowering b) (-weight b) :=
  PaperVerification.Fermion.Exterior.loweringRaising b

/-- Exterior multiplication by the symplectic two-form is injective below
the middle degree.  The factorial hypothesis is sufficient over arbitrary
commutative coefficient rings and is automatic in characteristic zero
fields. -/
theorem raising_injective_below_middle
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    {r : ℕ} (hr : r < Fintype.card ι) {w : E}
    (hw : w ∈ ⋀[R]^r V) (hraise : raising b w = 0) : w = 0 := by
  let d := Fintype.card ι
  have hr2 : r ≤ 2 * d := by dsimp [d]; omega
  apply primitive_eq_zero_of_degree_gt (raising b) (lowering b) (-weight b)
    (swappedRaisingLowering b) d (2 * d - r) hfac (by dsimp [d]; omega)
    w hraise
  · rw [LinearMap.neg_apply, weight_homogeneous b r w hw, ← neg_smul]
    congr 1
    dsimp [d]
    rw [Nat.cast_sub hr2, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · intro j hj
    apply lowering_pow_eq_zero_of_degree_lt b hw j
    omega

end DegreeLowering

section PrefixDivision

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) K V)

local notation "E" => ExteriorAlgebra K V

/-- The standard paired two-form in the genuine second exterior power. -/
noncomputable def symplecticTwoForm : ⋀[K]^2 V :=
  ∑ i, exteriorPower.ιMulti K 2 ![b (.inl i), b (.inr i)]

theorem raising_eq_symplecticTwoForm_mul (w : E) :
    raising b w = (symplecticTwoForm b : E) * w := by
  simp only [raising, pairRaise, LinearMap.sum_apply, Module.End.mul_apply,
    creation_apply, symplecticTwoForm, Submodule.coe_sum,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, mul_one, Finset.sum_mul, mul_assoc]

/-- Exterior multiplication with its true homogeneous domain and codomain. -/
noncomputable def raisingDegreeMap (r : ℕ) : (⋀[K]^r V) →ₗ[K] ⋀[K]^(r + 2) V :=
  (raising b).restrict fun _ hw => raising_mem_add_two b hw

theorem raisingDegreeMap_injective
    (hfac : IsUnit ((Fintype.card ι).factorial : K))
    (r : ℕ) (hr : r < Fintype.card ι) :
    Function.Injective (raisingDegreeMap b r) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply raising_injective_below_middle b hfac hr (x - y).property
  rw [Submodule.coe_sub, map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hxy)

include b in
/-- The middle complementary exterior powers have the same dimension. -/
theorem prefix_wedge_dimensions (hd : 0 < Fintype.card ι) :
    Module.finrank K (⋀[K]^(Fintype.card ι - 1) V) =
      Module.finrank K (⋀[K]^(Fintype.card ι - 1 + 2) V) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis b, Fintype.card_sum]
  have hle : Fintype.card ι - 1 + 2 ≤ Fintype.card ι + Fintype.card ι := by omega
  have hsub : Fintype.card ι + Fintype.card ι - (Fintype.card ι - 1 + 2) =
      Fintype.card ι - 1 := by omega
  simpa only [hsub] using Nat.choose_symm hle

/-- The complete prefix map is an isomorphism, for every positive number
of pairs. -/
theorem prefix_wedge_bijective (hd : 0 < Fintype.card ι)
    (hfac : IsUnit ((Fintype.card ι).factorial : K)) :
    Function.Bijective (raisingDegreeMap b (Fintype.card ι - 1)) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  have hinj := raisingDegreeMap_injective b hfac (Fintype.card ι - 1) (by omega)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (prefix_wedge_dimensions b hd)).mp hinj⟩

/-- Lemma 3.1's division existence for every homogeneous prefix element,
including every squarefree monomial, over every characteristic-zero field.
No bound is imposed on the number of variables. -/
theorem prefix_division_exists [CharZero K] (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (symplecticTwoForm b : E) * η = (w : E) := by
  by_cases hd : 0 < Fintype.card ι
  · have hfac : IsUnit ((Fintype.card ι).factorial : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    let w' : ⋀[K]^(Fintype.card ι - 1 + 2) V :=
      ⟨w, by convert w.property using 1 <;> congr 1 <;> omega⟩
    obtain ⟨η, hη⟩ := (prefix_wedge_bijective b hd hfac).surjective w'
    refine ⟨η, ?_⟩
    rw [← raising_eq_symplecticTwoForm_mul]
    exact congrArg Subtype.val hη
  · have hd0 : Fintype.card ι = 0 := by omega
    have hw0 : (w : E) = 0 := homogeneous_eq_zero_of_card_lt b
      (Fintype.card ι + 1) (by simp [Fintype.card_sum, hd0]) w w.property
    exact ⟨0, by simp [hw0]⟩

/-- Prefix division remains inside the prefix variables after inclusion
in any larger vector space.  The witness is the image of an element of the
smaller exterior power, not an arbitrary ambient quotient representative. -/
theorem prefix_division_map_exists [CharZero K]
    {M : Type*} [AddCommGroup M] [Module K M] (φ : V →ₗ[K] M)
    (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (ExteriorAlgebra.map φ (symplecticTwoForm b) : ExteriorAlgebra K M) *
          ExteriorAlgebra.map φ η = ExteriorAlgebra.map φ w := by
  obtain ⟨η, hη⟩ := prefix_division_exists b w
  exact ⟨η, by simpa only [map_mul] using congrArg (ExteriorAlgebra.map φ) hη⟩

end PrefixDivision

section PrefixMonomials

variable {K M ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation of the formal paired generators at arbitrary ambient
vectors.  In the application the vectors are the first `2h` path variables. -/
noncomputable def pairedEvaluation (u v : ι → M) : (ι ⊕ ι → K) →ₗ[K] M :=
  (Pi.basisFun K (ι ⊕ ι)).constr K (Sum.elim u v)

@[simp] theorem pairedEvaluation_basis (u v : ι → M) (i : ι ⊕ ι) :
    pairedEvaluation u v (Pi.basisFun K (ι ⊕ ι) i) = Sum.elim u v i := by
  simp [pairedEvaluation]

/-- Evaluation carries the literal paired quadratic to the literal ambient
matching quadratic.  The finite sum is evaluated term by term. -/
theorem pairedEvaluation_symplectic (u v : ι → M) :
    ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm (Pi.basisFun K (ι ⊕ ι)) :
        ExteriorAlgebra K (ι ⊕ ι → K))=
      ∑ i,ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i) := by
  simp only [symplecticTwoForm,Submodule.coe_sum,map_sum,
    exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ExteriorAlgebra.ιMulti_apply,List.ofFn_succ,List.ofFn_zero,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,pairedEvaluation_basis,Sum.elim_inl,Sum.elim_inr,mul_one]

set_option maxHeartbeats 1000000 in
/-- The full squarefree-monomial assertion of Lemma 3.1, expressed without
an arbitrary choice of ordering of the odd and even halves.  The tuple may
even repeat variables; the alternating product then vanishes.  The witness
is explicitly required to use only the prescribed prefix variables. -/
theorem prefix_monomial_division (u v : ι → M)
    (a : Fin (Fintype.card ι + 1) → ι ⊕ ι) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) M,
      η ∈ LinearMap.range (exteriorPower.map (Fintype.card ι - 1) (pairedEvaluation u v)) ∧
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) * η =
        ExteriorAlgebra.ιMulti K (Fintype.card ι + 1) (Sum.elim u v ∘ a) := by
  let b := Pi.basisFun K (ι ⊕ ι)
  let w : ⋀[K]^(Fintype.card ι + 1) (ι ⊕ ι → K) :=
    exteriorPower.ιMulti K (Fintype.card ι + 1) (b ∘ a)
  let φ : (ι ⊕ ι → K) →ₗ[K] M := pairedEvaluation (K := K) u v
  obtain ⟨η, hη⟩ := prefix_division_map_exists b φ w
  let e : (⋀[K]^(Fintype.card ι - 1) (ι ⊕ ι → K)) →ₗ[K]
      (⋀[K]^(Fintype.card ι - 1) M) := exteriorPower.map (Fintype.card ι - 1) φ
  refine ⟨e η,LinearMap.mem_range_self e η,?_⟩
  change (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
    (exteriorPower.map (Fintype.card ι - 1) φ η : ExteriorAlgebra K M)=_
  have hform := pairedEvaluation_symplectic (K := K) u v
  change (ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm b) : ExteriorAlgebra K M) *
        ExteriorAlgebra.map (pairedEvaluation (K := K) u v) η=
      ExteriorAlgebra.map (pairedEvaluation (K := K) u v) w at hη
  rw [hform] at hη
  simpa only [exteriorPower.coe_map, w, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Function.comp_def, b, φ,
    pairedEvaluation_basis] using hη

end PrefixMonomials

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0211

section TAF_LiteralSource_0212
/- Original module: PaperVerification.AlternatingFormsOddExteriorCutoff -/


/-!
# The actual exterior quotient in every degree above the odd middle

The first canonical form already kills every exterior degree greater than
`k+1` in `2k+1` variables.  An increasing word of that length has its first
`k+1` letters among the first `2k` variables.  The full symplectic-prefix
division theorem applies to precisely those letters; the complete remaining
suffix is retained.  Thus this cutoff concerns the generated exterior ideal,
not a polynomial presentation or an anticipated dimension formula.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {k r s : ℕ}

private theorem odd_long_prefix_bound
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) (i : Fin (k+1)) :
    (I.val (Fin.castAdd (r+1) i)).val<2*k := by
  have hi : Fin.castAdd (r+1) i < Fin.natAdd (k+1) (0 : Fin (r+1)) := by
    change i.val<k+1+0
    simpa only [Nat.add_zero] using i.isLt
  have hstrict := I.property hi
  have hlast := (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).isLt
  change (I.val (Fin.castAdd (r+1) i)).val<
    (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).val at hstrict
  omega

set_option pp.all true in
/-- Normalize the finite prefix size before entering a dependent Plücker-index
context.  This is the same division theorem, with the cardinality of `Fin k`
written as `k`. -/
private theorem odd_prefix_division (u v : Fin k → (Fin (2*k+1) → K)) :
    ∀ b : Fin (k+1) → Fin k ⊕ Fin k,
      ∃ η : ⋀[K]^(k-1) (Fin (2*k+1) → K),
        η ∈ LinearMap.range (exteriorPower.map (k-1) (pairedEvaluation u v)) ∧
        (∑ j : Fin k, ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ι K (v j)) *
          (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
          ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
  have h := prefix_monomial_division (K := K) u v
  rw [Fintype.card_fin] at h
  exact h

/-- The literal increasing word is a multiple of the first canonical
quadratic, with every suffix letter preserved. -/
theorem odd_long_word_division
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) :
    ∃ a : ExteriorAlgebra K (Fin (2*k+1) → K),
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*a=
          indexExteriorWord (List.ofFn I.val) := by
  let z := Pi.basisFun K (Fin (2*k+1))
  let u : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathFirstLeft j)
  let v : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathMiddle j)
  let a : Fin (k+1) → Fin (2*k) := fun i =>
    ⟨(I.val (Fin.castAdd (r+1) i)).val,odd_long_prefix_bound I i⟩
  let b : Fin (k+1) → Fin k ⊕ Fin k := fun i => (evenOddPrefixEquiv k).symm (a i)
  have htuple : Sum.elim u v ∘ b=
      fun i => z (I.val (Fin.castAdd (r+1) i)) := by
    funext i
    have he : evenOddPrefixEquiv k (b i)=a i :=
      (evenOddPrefixEquiv k).apply_symm_apply (a i)
    change Sum.elim u v (b i)=_
    rcases hb : b i with j | j
    · rw [hb] at he
      change z (oddPathFirstLeft j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inl,a,oddPathFirstLeft] using congrArg Fin.val he
    · rw [hb] at he
      change z (oddPathMiddle j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inr,a,oddPathMiddle] using congrArg Fin.val he
  have hdiv := odd_prefix_division (K := K) u v
  obtain ⟨η,hηsupport,hη⟩ := hdiv b
  have hη' : (∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j)) *
      (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
      ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
    exact hη
  have hform : (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))=
      ∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j) := by
    simp only [oddPathFirstQuadratic,matchingQuadratic_coe,u,v]
  have hprefix :
      (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
        indexExteriorWord (List.ofFn (fun i : Fin (k+1) => I.val (Fin.castAdd (r+1) i))) := by
    rw [hform,hη',htuple]
    simp only [ExteriorAlgebra.ιMulti_apply,indexExteriorWord,List.map_ofFn,z,
      List.map_map,Function.comp_def]
  let L := List.ofFn (fun i : Fin (r+1) => I.val (Fin.natAdd (k+1) i))
  refine ⟨(η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L,?_⟩
  change (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
    ((η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L)=_
  rw [←mul_assoc,hprefix,←indexExteriorWord_append]
  congr 1
  exact (List.ofFn_add (f := I.val)).symm

private theorem odd_exteriorDegreeRelations_eq_top_add
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (r : ℕ) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g
      (k+1+(r+1))=⊤ := by
  apply eq_top_iff.mpr
  rw [←(exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨I,rfl⟩
  change ((exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1) I) :
    ExteriorAlgebra K (Fin (2*k+1) → K))∈exteriorRelationIdeal _ g
  obtain ⟨a,ha⟩ := odd_long_word_division (K := K) I
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,0,?_⟩
  rw [zero_mul,add_zero,
    ←(twoForm_commute (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) a).eq,ha]
  rw [exteriorPluckerBasis_apply]
  simp only [indexExteriorWord,exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply,List.map_ofFn,List.map_map,Function.comp_def]

/-- Full high-degree vanishing for the actual generated exterior ideal.
The second quadratic may be arbitrary; no upper bound on `s` is imposed. -/
theorem odd_exteriorDegreeRelations_eq_top
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s=⊤ := by
  let r := s-(k+2)
  have he : s=k+1+(r+1) := by dsimp only [r]; omega
  rw [he]
  exact odd_exteriorDegreeRelations_eq_top_add g r

theorem odd_exteriorQuotientDegree_subsingleton
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Subsingleton (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s) := by
  change Subsingleton ((⋀[K]^s (Fin (2*k+1) → K))⧸exteriorDegreeRelations _ g s)
  rw [odd_exteriorDegreeRelations_eq_top g hs]
  infer_instance

theorem odd_exteriorQuotientDegree_finrank_eq_zero
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Module.finrank K (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s)=0 := by
  letI := odd_exteriorQuotientDegree_subsingleton g hs
  exact Module.finrank_zero_of_subsingleton

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0212

section TAF_LiteralSource_0213
/- Original module: PaperVerification.AlternatingFormsOddExteriorBasis -/


/-!
# The complete good-monomial exterior basis for the canonical odd pencil

The index inequalities are written without truncated subtraction, so they
retain their meaning in every degree, including degrees above the middle.
Degrees zero and one use the proved absence of quadratic-generated relations;
the middle range uses the actual linear Plücker comparison and lifted standard
basis; all higher degrees use the actual generated-ideal cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K]

/-- The printed good-index inequalities, in zero-based coordinates and with
the upper inequality moved across the subtraction. -/
def GoodOddIndex (k s : ℕ) :=
  {I : PluckerIndex s (2*k+1) // ∀ i,
    2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}

instance goodOddIndex_fintype (k s : ℕ) : Fintype (GoodOddIndex k s) := by
  classical
  unfold GoodOddIndex
  infer_instance

abbrev OddExteriorQuotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s

def goodOddBandEquiv (k t : ℕ) (hs : t+2≤k+1) :
    GoodOddIndex k (t+2) ≃
      BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) 1 where
  toFun I := ⟨fun _ => I.val.val,fun _ => I.val.property,
    (by
      intro j i
      have hi := I.property i
      constructor
      · exact hi.1
      · change (I.val.val i).val≤2*(k+1-(t+2)+i.val)
        omega),monotone_const⟩
  invFun C := ⟨⟨C.val 0,C.property.1 0⟩,by
    intro i
    have hi := C.property.2.1 0 i
    constructor
    · exact hi.1
    · have hi2 := hi.2
      change (C.val 0 i).val≤2*(k+1-(t+2)+i.val) at hi2
      change (C.val 0 i).val+2*(t+2)≤2*k+2+2*i.val
      omega⟩
  left_inv I := rfl
  right_inv C := by
    apply Subtype.ext
    funext j i
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]

private theorem odd_pairCoefficientForms (k : ℕ) :
    pairCoefficientForms (oddPluckerForms (K := K) k 0) (oddPluckerForms k 1)=
      oddPluckerForms k := by
  funext i
  fin_cases i <;> rfl

def oddExteriorLinearClass (k t : ℕ) :
    (⋀[K]^(t+2) (Fin (2*k+1) → K)) →ₗ[K]
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) :=
  (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal (t := t) (oddPluckerForms k))).toLinearMap.comp
    (exteriorPluckerCoordinates (t+2) (2*k+1))

theorem oddExteriorLinearClass_ker (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).ker=exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) (t+2) := by
  apply Submodule.ext
  intro x
  change Ideal.Quotient.mk
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (exteriorPluckerCoordinates (K := K) (t+2) (2*k+1) x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,← odd_pairCoefficientForms (K := K) k,
    exteriorCoordinates_mem_pairIdeal_iff,coefficientPairRelations_eq_exterior,
    oddPluckerForms_first,oddPluckerForms_second]

theorem oddExteriorLinearClass_range (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).range=oddPluckerDegree k t 1 := by
  rw [oddExteriorLinearClass,LinearMap.range_comp,exteriorPluckerCoordinates_range]
  rfl

def oddExteriorLinearPieceEquiv (k t : ℕ) :
    OddExteriorQuotientDegree (K := K) k (t+2) ≃ₗ[K]
      oddPluckerDegree (K := K) k t 1 :=
  (Submodule.quotEquivOfEq _ _ (oddExteriorLinearClass_ker k t).symm).trans
    ((oddExteriorLinearClass k t).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (oddExteriorLinearClass_range k t)))

theorem oddExteriorLinearPieceEquiv_mk (k t : ℕ)
    (x : ⋀[K]^(t+2) (Fin (2*k+1) → K)) :
    (oddExteriorLinearPieceEquiv k t (Submodule.Quotient.mk x) :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (exteriorPluckerCoordinates (t+2) (2*k+1) x) := by
  simp only [oddExteriorLinearPieceEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearEquiv.coe_ofEq_apply,
    LinearMap.quotKerEquivRange_apply_mk]
  rfl

def oddExteriorMiddleBasis [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (GoodOddIndex k (t+2)) K (OddExteriorQuotientDegree (K := K) k (t+2)) :=
  ((oddPluckerDegreeBasis k t hs 1).map (oddExteriorLinearPieceEquiv k t).symm).reindex
    (goodOddBandEquiv k t hs).symm

@[simp] theorem oddExteriorMiddleBasis_apply [CharZero K] (k t : ℕ) (hs : t+2≤k+1)
    (I : GoodOddIndex k (t+2)) :
    oddExteriorMiddleBasis (K := K) k t hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis (t+2) (2*k+1) I.val) := by
  apply (oddExteriorLinearPieceEquiv k t).injective
  apply Subtype.ext
  simp only [oddExteriorMiddleBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    Module.Basis.map_apply,LinearEquiv.apply_symm_apply,oddPluckerDegreeBasis_apply,
    oddExteriorLinearPieceEquiv_mk,exteriorPluckerCoordinates_basis,
    goodOddBandEquiv,chainPluckerProduct,Fin.prod_univ_one]
  rfl

def goodOddLowEquiv (k s : ℕ) (hs : s<2) : GoodOddIndex k s ≃ PluckerIndex s (2*k+1) where
  toFun I := I.val
  invFun I := ⟨I,by
    intro i
    have hi := i.isLt
    have hI := (I.val i).isLt
    constructor <;> omega⟩
  left_inv I := rfl
  right_inv I := rfl

def oddExteriorLowBasis (k s : ℕ) (hs : s<2) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) :=
  ((exteriorPluckerBasis s (2*k+1)).reindex (goodOddLowEquiv k s hs).symm).map
    ((exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s).quotEquivOfEqBot (exteriorDegreeRelations_eq_bot _ _ hs)).symm

@[simp] theorem oddExteriorLowBasis_apply (k s : ℕ) (hs : s<2) (I : GoodOddIndex k s) :
    oddExteriorLowBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  simp only [oddExteriorLowBasis,Module.Basis.map_apply,Module.Basis.reindex_apply,
    Equiv.symm_symm,goodOddLowEquiv,Submodule.quotEquivOfEqBot_symm_apply]
  rfl

theorem goodOddIndex_isEmpty (k s : ℕ) (hs : k+1<s) : IsEmpty (GoodOddIndex k s) := by
  refine ⟨fun I => ?_⟩
  have hpos : 0<s := by omega
  have h := (I.property (⟨0,hpos⟩ : Fin s)).2
  change (I.val.val ⟨0,hpos⟩).val+2*s≤2*k+2+2*0 at h
  omega

def oddExteriorHighBasis [CharZero K] (k s : ℕ) (hs : k+1<s) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) := by
  letI := goodOddIndex_isEmpty k s hs
  letI := odd_exteriorQuotientDegree_subsingleton
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) hs
  exact Module.Basis.empty _

@[simp] theorem oddExteriorHighBasis_apply [CharZero K] (k s : ℕ) (hs : k+1<s) (I : GoodOddIndex k s) :
    oddExteriorHighBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  exact (goodOddIndex_isEmpty k s hs).false I |>.elim

/-- The basis covers every degree and every odd ambient dimension. -/
def oddExteriorBasis [CharZero K] (k : ℕ) : (s : ℕ) →
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s)
  | 0 => oddExteriorLowBasis k 0 (by decide)
  | 1 => oddExteriorLowBasis k 1 (by decide)
  | t+2 => if hs : t+2≤k+1 then oddExteriorMiddleBasis k t hs
      else oddExteriorHighBasis k (t+2) (Nat.lt_of_not_ge hs)

@[simp] theorem oddExteriorBasis_apply [CharZero K] (k s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasis (K := K) k s I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  cases s with
  | zero => exact oddExteriorLowBasis_apply k 0 (by decide) I
  | succ s =>
      cases s with
      | zero => exact oddExteriorLowBasis_apply k 1 (by decide) I
      | succ t =>
          dsimp only [oddExteriorBasis]
          split_ifs with hs
          · exact oddExteriorMiddleBasis_apply k t hs I
          · exact oddExteriorHighBasis_apply k (t+2) (Nat.lt_of_not_ge hs) I

/-- The complete exterior-basis clause of Theorem 1.3, faithfully stated
using the actual generated-ideal quotient and the original exterior words.
The separate degeneration and Koszul clauses are not part of this statement. -/
theorem paper_theorem_1_3_exterior_basis [CharZero K] (k s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  refine ⟨oddExteriorBasis k s,?_⟩
  intro I
  rw [oddExteriorBasis_apply,exteriorPluckerBasis_apply]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0213

section TAF_LiteralSource_0214
/- Original module: PaperVerification.AlternatingFormsOddTransport -/


/-!
# Naturality of the displayed odd pencil

The two matching quadrics commute with every linear map.  A chosen basis
therefore identifies their degree quotients with the standard-coordinate
quotient through the actual exterior algebra functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem exteriorPower_map_exteriorPair (l : M →ₗ[K] N) (u v : M) :
    exteriorPower.map 2 l (exteriorPair u v) = exteriorPair (l u) (l v) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, exteriorPair_coe, map_mul,
    ExteriorAlgebra.map_apply_ι]

theorem matchingQuadratic_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : M →ₗ[K] N) (u v : ι → M) :
    exteriorPower.map 2 l (matchingQuadratic u v) =
      matchingQuadratic (l ∘ u) (l ∘ v) := by
  simp only [matchingQuadratic, map_sum, exteriorPower_map_exteriorPair,
    Function.comp_apply]

theorem oddPathFirstQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathFirstQuadratic (K := K) z) =
      oddPathFirstQuadratic (K := K) (l ∘ z) := by
  rw [oddPathFirstQuadratic, matchingQuadratic_map]
  rfl

theorem oddPathSecondQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathSecondQuadratic (K := K) z) =
      oddPathSecondQuadratic (K := K) (l ∘ z) := by
  rw [oddPathSecondQuadratic, matchingQuadratic_map]
  rfl

def standardBasisEquiv {n : ℕ} (b : Module.Basis (Fin n) K M) :
    (Fin n → K) ≃ₗ[K] M :=
  (Pi.basisFun K (Fin n)).equiv b (Equiv.refl (Fin n))

@[simp] theorem standardBasisEquiv_basisFun {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) :
    standardBasisEquiv b (Pi.basisFun K (Fin n) i) = b i := by
  simp only [standardBasisEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

theorem oddPathFirstQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathFirstQuadratic (K := K) b := by
  rw [oddPathFirstQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

theorem oddPathSecondQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathSecondQuadratic (K := K) b := by
  rw [oddPathSecondQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

def oddExteriorBasisChangeEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s ≃ₗ[K]
    ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s :=
  exteriorQuotientDegreePencilEquiv (standardBasisEquiv b) _ _ _ _
    (by rw [oddPathFirstQuadratic_standardBasisEquiv,
      oddPathSecondQuadratic_standardBasisEquiv]) s

@[simp] theorem oddExteriorBasisChangeEquiv_mk {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ)
    (x : ⋀[K]^s (Fin (2*k+1) → K)) :
    oddExteriorBasisChangeEquiv b s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (exteriorPower.map s (standardBasisEquiv b).toLinearMap x) := by
  rw [oddExteriorBasisChangeEquiv, exteriorQuotientDegreePencilEquiv_mk]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0214

section TAF_LiteralSource_0215
/- Original module: PaperVerification.AlternatingFormsOddAbstractBasis -/


/-!
# The good exterior basis in arbitrary coordinates

This endpoint removes the choice of the standard coordinate vector space.
It covers every module with a basis of the requested size, every odd
dimension, and every exterior degree, and displays the original basis words.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] {k : ℕ}

def oddExteriorBasisAt (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s) :=
  (oddExteriorBasis k s).map (oddExteriorBasisChangeEquiv b s)

@[simp] theorem oddExteriorBasisAt_apply
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasisAt b s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) := by
  rw [oddExteriorBasisAt, Module.Basis.map_apply, oddExteriorBasis_apply,
    oddExteriorBasisChangeEquiv_mk, exteriorPluckerBasis_apply,
    exteriorPower.map_apply_ιMulti]
  congr 1
  apply congrArg (exteriorPower.ιMulti K s)
  funext i
  exact standardBasisEquiv_basisFun b (I.val.val i)

/-- The exterior-basis clause of Theorem 1.3 with its full basis-dependent
vector-space interpretation, including all boundary and vanishing degrees. -/
theorem paper_theorem_1_3_exterior_basis_with_basis
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s),
      ∀ I, B I = Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) :=
  ⟨oddExteriorBasisAt b s, oddExteriorBasisAt_apply b s⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0215

section TAF_LiteralSource_0216
/- Original module: PaperVerification.AlternatingFormsOddOrbitInterleaving -/


/-!
# The odd orbit normal form is the literal interleaved path pencil

The orbit calculation groups the `a` and `b` coordinates in two blocks.
The exterior straightening theorem interleaves them.  This file gives
the explicit permutation, identifies both quadratic generators including
their signs, and transports the complete good-monomial basis to the
actual orbit normal form in every exterior degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

/-- `aᵢ` occupies the odd position `2i+1` and `bⱼ` the even position `2j`. -/
def oddOrbitInterleave (t : ℕ) : OddOrbitMode t ≃ Fin (2*(t+1)+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr j =>
        have he : (2*j.val)%2=0 := by omega
        simp only [he, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv j := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

def oddOrbitInterleavedBasis (t : ℕ) :
    Module.Basis (Fin (2*(t+1)+1)) K (OddOrbitMode t → K) :=
  (Pi.basisFun K (OddOrbitMode t)).reindex (oddOrbitInterleave t)

theorem oddOrbitInterleavedBasis_at (t : ℕ) (i : OddOrbitMode t) :
    oddOrbitInterleavedBasis (K := K) t (oddOrbitInterleave t i) =
      Pi.basisFun K (OddOrbitMode t) i := by
  simp only [oddOrbitInterleavedBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply]

theorem oddOrbitInterleavedBasis_middle (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathMiddle i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inl i) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inl i)

theorem oddOrbitInterleavedBasis_first (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathFirstLeft i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.castSucc) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.castSucc)

theorem oddOrbitInterleavedBasis_second (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathSecondRight i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.succ) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.succ)

theorem exteriorPair_swap {M : Type*} [AddCommGroup M] [Module K M] (u v : M) :
    exteriorPair (K := K) u v = -exteriorPair v u := by
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

/-- The first orbit generator is exactly the second path generator. -/
theorem oddOrbitFirstForm_eq_path (t : ℕ) :
    oddOrbitFirstForm (K := K) t =
      oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitFirstForm, orbitIncidenceForm, oddPathSecondQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_middle,
    oddOrbitInterleavedBasis_second, exteriorPair]

/-- The second orbit generator is minus the first path generator.  The
sign is retained explicitly before comparing the generated ideals. -/
theorem oddOrbitSecondForm_eq_path (t : ℕ) :
    oddOrbitSecondForm (K := K) t =
      -oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitSecondForm, orbitIncidenceForm, oddPathFirstQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_first,
    oddOrbitInterleavedBasis_middle, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact exteriorPair_swap _ _

theorem quadraticSpan_swap_neg {M : Type*} [AddCommGroup M] [Module K M]
    (f g : ⋀[K]^2 M) :
    Submodule.span K ({f,g} : Set (⋀[K]^2 M)) =
      Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have hn : -f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) :=
        Submodule.subset_span (by simp)
      change f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M))
      have hnn := (Submodule.span K ({g,-f} : Set (⋀[K]^2 M))).neg_mem hn
      rw [neg_neg] at hnn
      exact hnn
    · rw [hx]
      exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.subset_span (by simp)
    · rw [hx]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))

theorem oddOrbit_quadraticSpan (t : ℕ) :
    Submodule.span K
      ({oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t),
        oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)} :
          Set (⋀[K]^2 (OddOrbitMode t → K))) =
      Submodule.span K ({oddOrbitFirstForm (K := K) t,oddOrbitSecondForm (K := K) t} :
        Set (⋀[K]^2 (OddOrbitMode t → K))) := by
  rw [oddOrbitFirstForm_eq_path, oddOrbitSecondForm_eq_path]
  exact quadraticSpan_swap_neg _ _

def oddOrbitQuotientDegreeEquiv (t s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)) s ≃ₗ[K]
    ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s :=
  exteriorQuotientDegreeGeneratorsEquiv _ _ _ _ (oddOrbit_quadraticSpan t) s

section CharacteristicZero

variable [CharZero K]

/-- The full good-word basis for the actual block orbit normal form. -/
def oddOrbitQuotientDegreeBasis (t s : ℕ) :
    Module.Basis (GoodOddIndex (t+1) s) K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) :=
  (oddExteriorBasisAt (oddOrbitInterleavedBasis (K := K) t) s).map (oddOrbitQuotientDegreeEquiv t s)

theorem oddOrbitQuotientDegreeBasis_apply (t s : ℕ) (I : GoodOddIndex (t+1) s) :
    oddOrbitQuotientDegreeBasis (K := K) t s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i))) := by
  rw [oddOrbitQuotientDegreeBasis, Module.Basis.map_apply, oddExteriorBasisAt_apply]
  simpa only [oddOrbitQuotientDegreeEquiv] using
    exteriorQuotientDegreeGeneratorsEquiv_mk
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t)
      (oddOrbit_quadraticSpan (K := K) t) s
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i)))

theorem oddOrbitQuotientDegree_finrank (t s : ℕ) :
    Module.finrank K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) =
      Fintype.card (GoodOddIndex (t+1) s) :=
  Module.finrank_eq_card_basis (oddOrbitQuotientDegreeBasis t s)

end CharacteristicZero

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0216

section TAF_LiteralSource_0217
/- Original module: PaperVerification.AlternatingFormsGoodPathBounds -/


/-!
# The exact good-index inequalities and binary strip bounds

The original exterior positions are shifted by one because the binary path
starts with a fixed up-step.  A selected position contributes a down-step.
The prefix count therefore counts indices `I_j+1<q` in a prefix of length
`q`.  The two inequalities below are exactly nonnegative height and the
upper strip bound, without truncated subtraction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

/-- Number of selected original letters in the first `q` binary steps,
including the initial fixed up-step in the prefix length. -/
def selectedBefore {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (I i).val+1<q).card

theorem selectedBefore_le {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedBefore I q≤s := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin s)

/-- A strictly increasing list meets every prefix in an initial segment. -/
theorem lt_selectedBefore_iff {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) (i : Fin s) :
    i.val<selectedBefore I q ↔ (I i).val+1<q := by
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hb : (I b).val≤(I a).val := hI.monotone hba
  omega

/-- Just before a selected down-step, exactly its predecessors have occurred. -/
theorem selectedBefore_at {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+1)=i.val := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+1)=Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    change (I j).val+1<(I i).val+1 ↔ j < i
    exact Nat.add_lt_add_iff_right.trans hI.lt_iff_lt
  rw [hf,Fin.card_Iio]

/-- Just after a selected down-step, it too has occurred. -/
theorem selectedBefore_after {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+2)=i.val+1 := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+2)=Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    have he : (I j).val≤(I i).val ↔ j ≤ i := hI.le_iff_le
    omega
  rw [hf,Fin.card_Iic]

/-- The literal down-step indicator at a binary position. -/
def selectedAt {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  if ∃ i,(I i).val+1=q then 1 else 0

theorem selectedAt_le_one {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedAt I q≤1 := by
  unfold selectedAt
  split_ifs <;> omega

/-- A prefix grows by precisely the selected-position indicator. -/
theorem selectedBefore_succ {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I (q+1)=selectedBefore I q+selectedAt I q := by
  by_cases hq : ∃ i,(I i).val+1=q
  · obtain ⟨i,rfl⟩ := hq
    rw [show (I i).val+1+1=(I i).val+2 by omega,
      selectedBefore_after hI i,selectedBefore_at hI i]
    simp [selectedAt]
  · have hf : (Finset.univ.filter fun i => (I i).val+1<q+1)=
        (Finset.univ.filter fun i => (I i).val+1<q) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hi : (I i).val+1≠q := fun he => hq ⟨i,he⟩
      omega
    simp only [selectedBefore,hf,selectedAt,if_neg hq,Nat.add_zero]

@[simp] theorem selectedBefore_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I 0=0 := by simp [selectedBefore]

@[simp] theorem selectedAt_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedAt I 0=0 := by simp [selectedAt]

/-- The final fixed up-step adds no selected position. -/
theorem selectedBefore_all {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I (n+1)=s := by
  have h : ∀ i,(I i).val+1<n+1 := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

theorem selectedBefore_eq_card_of_ge {s n : ℕ} (I : Fin s → Fin n) (q : ℕ)
    (hq : n+1≤q) : selectedBefore I q=s := by
  have h : ∀ i,(I i).val+1<q := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

/-- Exact equivalence between the printed good-index bounds and all binary
prefix heights in the strip.  It holds in every parameter range. -/
theorem good_bounds_iff_prefix_strip (k s : ℕ) (I : Fin s → Fin (2*k+1))
    (hI : StrictMono I) :
    (∀ i,2*i.val≤(I i).val ∧ (I i).val+2*s≤2*k+2+2*i.val) ↔
    (∀ q,q≤2*k+3 → 2*selectedBefore I q≤q ∧
      q+2*s≤2*k+3+2*selectedBefore I q) := by
  constructor
  · intro h q hq
    have hc := selectedBefore_le I q
    constructor
    · by_cases hz : selectedBefore I q=0
      · omega
      · let i : Fin s := ⟨selectedBefore I q-1,by omega⟩
        have hi : i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := (lt_selectedBefore_iff hI q i).mp hi
        have hb := (h i).1
        dsimp only [i] at hb hpos
        omega
    · by_cases he : selectedBefore I q=s
      · omega
      · let i : Fin s := ⟨selectedBefore I q,by omega⟩
        have hi : ¬ i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := mt (lt_selectedBefore_iff hI q i).mpr hi
        have hb := (h i).2
        dsimp only [i] at hb hpos
        omega
  · intro h i
    have hlt := (I i).isLt
    have hlo := (h ((I i).val+2) (by omega)).1
    have hhi := (h ((I i).val+1) (by omega)).2
    rw [selectedBefore_after hI i] at hlo
    rw [selectedBefore_at hI i] at hhi
    constructor <;> omega

/-- The actual finite selected set of an increasing exterior word. -/
def selectedSet {s n : ℕ} (I : Fin s → Fin n) : Finset (Fin n) :=
  Finset.univ.image I

theorem selectedSet_card {s n : ℕ} {I : Fin s → Fin n} (hI : StrictMono I) :
    (selectedSet I).card=s := by
  rw [selectedSet,Finset.card_image_of_injective _ hI.injective,Finset.card_univ,
    Fintype.card_fin]

/-- Sorted lists and subsets of the same cardinality are genuinely equivalent. -/
def increasingSelectionEquiv (s n : ℕ) :
    {I : Fin s → Fin n // StrictMono I} ≃ {S : Finset (Fin n) // S.card=s} where
  toFun I := ⟨selectedSet I.val,selectedSet_card I.property⟩
  invFun S := ⟨S.val.orderEmbOfFin S.property,(S.val.orderEmbOfFin S.property).strictMono⟩
  left_inv I := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (selectedSet_card I.property)
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property).symm
  right_inv S := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ S.val S.property

/-- Prefix counts agree with the literal selected set, so the preceding
strip characterization is a statement about the actual binary word. -/
theorem selectedBefore_eq_filter_card {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I q=((selectedSet I).filter fun x => x.val+1<q).card := by
  rw [selectedSet,Finset.filter_image]
  exact (Finset.card_image_of_injective _ hI.injective).symm

end PaperVerification.AlternatingForms.GoodPaths
end
end
end TAF_LiteralSource_0217

section TAF_LiteralSource_0218
/- Original module: PaperVerification.AlternatingFormsOddWalkCount -/


/-!
# The good odd exterior words count the paper's actual strip walks

An original exterior position `i` becomes downward step `i+1`.  Both
endpoints of a strip walk are upward steps, so every good downward set
of length `2*k+3` comes from exactly one increasing exterior word.
The proof constructs this equivalence using sorted finite sets.  It
therefore identifies the full good-word basis with the actual graph
walk count, including the degrees above the vanishing cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

open BooleanWalks

/-- The initial fixed up-step shifts every original exterior position by one. -/
def oddDownstepShift (k : ℕ) : Fin (2*k+1) ↪ Fin (2*k+3) where
  toFun i := ⟨i.val+1, by have := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have := congrArg Fin.val h
    change i.val+1=j.val+1 at this
    omega

def oddIndexDownset {k s : ℕ} (I : Fin s → Fin (2*k+1)) : Finset (Fin (2*k+3)) :=
  (GoodPaths.selectedSet I).map (oddDownstepShift k)

theorem oddIndexDownset_card {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) : (oddIndexDownset I).card=s := by
  rw [oddIndexDownset, Finset.card_map, GoodPaths.selectedSet_card hI]

theorem oddIndexDownset_prefix {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) (q : ℕ) :
    prefixCount (oddIndexDownset I) q = GoodPaths.selectedBefore I q := by
  rw [prefixCount, oddIndexDownset, Finset.filter_map, Finset.card_map]
  change ((GoodPaths.selectedSet I).filter (fun x => x.val+1<q)).card =
    GoodPaths.selectedBefore I q
  exact (GoodPaths.selectedBefore_eq_filter_card hI q).symm

def goodOddIndexToGoodSubset {k s : ℕ} (I : GoodOddIndex k s) :
    GoodSubset (2*k+3) s :=
  ⟨⟨oddIndexDownset I.val.val, oddIndexDownset_card I.val.property⟩, by
    intro q hq
    change 2*prefixCount (oddIndexDownset I.val.val) q≤q ∧
      q+2*s≤2*k+3+2*prefixCount (oddIndexDownset I.val.val) q
    rw [oddIndexDownset_prefix I.val.property]
    exact (GoodPaths.good_bounds_iff_prefix_strip k s I.val.val I.val.property).mp
      I.property q hq⟩

theorem goodOddIndexToGoodSubset_injective (k s : ℕ) :
    Function.Injective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro I J h
  have hs : oddIndexDownset I.val.val = oddIndexDownset J.val.val :=
    congrArg (fun S : GoodSubset (2*k+3) s => S.val.val) h
  have hi : GoodPaths.selectedSet I.val.val = GoodPaths.selectedSet J.val.val :=
    Finset.map_injective (oddDownstepShift k) hs
  apply Subtype.ext
  exact (GoodPaths.increasingSelectionEquiv s (2*k+1)).injective (Subtype.ext hi)

/-- A good downward set contains neither of the two endpoint steps. -/
theorem goodSubset_odd_interior {k s : ℕ} (S : GoodSubset (2*k+3) s)
    (j : Fin (2*k+3)) (hj : j∈S.val.val) :
    0<j.val ∧ j.val<2*k+2 := by
  have hfirst : (0 : Fin (2*k+3)) ∉ S.val.val := by
    intro hzero
    have hc := prefixCount_succ S.val.val 0
    have hd : selectedAt S.val.val 0 = 1 := by
      simpa only [Fin.val_zero, if_pos hzero] using
        selectedAt_position S.val.val (0 : Fin (2*k+3))
    have hc' : prefixCount S.val.val 1 = 1 := by
      simpa only [prefixCount_zero, hd, Nat.zero_add] using hc
    have hb : 2 * prefixCount S.val.val 1 ≤ 1 := (S.property 1 (by omega)).1
    rw [hc'] at hb
    norm_num at hb
  have hlast : (⟨2*k+2, by omega⟩ : Fin (2*k+3)) ∉ S.val.val := by
    intro hlast
    have hc := prefixCount_succ S.val.val (2*k+2)
    have hd := selectedAt_position S.val.val (⟨2*k+2, by omega⟩ : Fin (2*k+3))
    simp only [Fin.val_mk, if_pos hlast] at hd
    have ha := prefixCount_all S.val.val (2*k+3) le_rfl
    rw [S.val.property] at ha
    change prefixCount S.val.val (2*k+3) =
      prefixCount S.val.val (2*k+2) + selectedAt S.val.val (2*k+2) at hc
    rw [hd, ha] at hc
    have hb := (S.property (2*k+2) (by omega)).2
    omega
  have hj0 : j.val≠0 := by
    intro hz
    have he : j = (0 : Fin (2*k+3)) := Fin.ext hz
    exact hfirst (he ▸ hj)
  have hjlast : j.val≠2*k+2 := by
    intro hz
    have he : j = (⟨2*k+2, by omega⟩ : Fin (2*k+3)) := Fin.ext hz
    exact hlast (he ▸ hj)
  have hjlt := j.isLt
  omega

/-- Sort the downward steps and remove the initial fixed up-step. -/
def goodSubsetToOddIndex {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    Fin s → Fin (2*k+1) := fun i =>
  ⟨(S.val.val.orderEmbOfFin S.val.property i).val-1, by
    have h := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    omega⟩

theorem goodSubsetToOddIndex_strictMono {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    StrictMono (goodSubsetToOddIndex S) := by
  intro i j hij
  have hord := (S.val.val.orderEmbOfFin S.val.property).strictMono hij
  have hi := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property i)
  have hj := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property j)
  change (S.val.val.orderEmbOfFin S.val.property i).val <
    (S.val.val.orderEmbOfFin S.val.property j).val at hord
  change (S.val.val.orderEmbOfFin S.val.property i).val-1 <
    (S.val.val.orderEmbOfFin S.val.property j).val-1
  omega

theorem oddIndexDownset_goodSubsetToOddIndex {k s : ℕ}
    (S : GoodSubset (2*k+3) s) : oddIndexDownset (goodSubsetToOddIndex S)=S.val.val := by
  unfold oddIndexDownset GoodPaths.selectedSet
  rw [Finset.map_eq_image, Finset.image_image]
  have hf : (fun i => oddDownstepShift k (goodSubsetToOddIndex S i)) =
      S.val.val.orderEmbOfFin S.val.property := by
    funext i
    apply Fin.ext
    have hi := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    change (S.val.val.orderEmbOfFin S.val.property i).val-1+1 =
      (S.val.val.orderEmbOfFin S.val.property i).val
    omega
  simp only [Function.comp_def]
  rw [hf]
  exact Finset.image_orderEmbOfFin_univ S.val.val S.val.property

theorem goodSubsetToOddIndex_good {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    ∀ i, 2*i.val≤(goodSubsetToOddIndex S i).val ∧
      (goodSubsetToOddIndex S i).val+2*s≤2*k+2+2*i.val := by
  apply (GoodPaths.good_bounds_iff_prefix_strip k s (goodSubsetToOddIndex S)
    (goodSubsetToOddIndex_strictMono S)).mpr
  intro q hq
  rw [← oddIndexDownset_prefix (goodSubsetToOddIndex_strictMono S),
    oddIndexDownset_goodSubsetToOddIndex]
  exact S.property q hq

theorem goodOddIndexToGoodSubset_surjective (k s : ℕ) :
    Function.Surjective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro S
  refine ⟨⟨⟨goodSubsetToOddIndex S, goodSubsetToOddIndex_strictMono S⟩,
    goodSubsetToOddIndex_good S⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact oddIndexDownset_goodSubsetToOddIndex S

/-- Every good exterior word is precisely one bounded binary strip walk. -/
def goodOddIndexGoodSubsetEquiv (k s : ℕ) : GoodOddIndex k s ≃ GoodSubset (2*k+3) s :=
  Equiv.ofBijective goodOddIndexToGoodSubset
    ⟨goodOddIndexToGoodSubset_injective k s, goodOddIndexToGoodSubset_surjective k s⟩

theorem card_goodOddIndex_eq_paperWalkCount_of_le (k s : ℕ) (hs : s≤k+1) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  calc
    Fintype.card (GoodOddIndex k s) = Fintype.card (GoodSubset (2*k+3) s) :=
      Fintype.card_congr (goodOddIndexGoodSubsetEquiv k s)
    _ = StripWalks.walkCount (2*k+3-2*s) (2*k+3) :=
      card_goodSubset_eq_walkCount (2*k+3) s (by omega)
    _ = StripWalks.paperWalkCount (2*k+1) s := by
      unfold StripWalks.paperWalkCount
      congr 1 <;> omega

/-- A width-zero strip has no positive-length walk. -/
theorem stripWalkCount_zero_width (N : ℕ) (hN : 0<N) :
    StripWalks.walkCount 0 N=0 := by
  letI : Subsingleton (Fin (0+1)) := Fin.subsingleton_iff_le_one.mpr (by decide)
  letI : IsEmpty {p : (SimpleGraph.pathGraph (0+1)).Walk 0 (Fin.last 0) // p.length=N} :=
    ⟨fun p => by
      have hz := p.val.nil_of_subsingleton.length_eq_zero
      have hn := p.property
      omega⟩
  exact Fintype.card_of_isEmpty

theorem paperWalkCount_odd_above_cutoff (k s : ℕ) (hs : k+1<s) :
    StripWalks.paperWalkCount (2*k+1) s=0 := by
  unfold StripWalks.paperWalkCount
  rw [show 2*k+1+2-2*s=0 by omega]
  exact stripWalkCount_zero_width _ (by omega)

/-- The count equality is valid in every natural exterior degree. -/
theorem card_goodOddIndex_eq_paperWalkCount (k s : ℕ) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  by_cases hs : s≤k+1
  · exact card_goodOddIndex_eq_paperWalkCount_of_le k s hs
  · have hs' : k+1<s := by omega
    letI := goodOddIndex_isEmpty k s hs'
    rw [Fintype.card_of_isEmpty, paperWalkCount_odd_above_cutoff k s hs']

/-- The odd path pencil has exactly the paper's Hilbert function in all degrees. -/
theorem oddExteriorQuotientDegree_finrank_eq_paperWalkCount
    {K : Type*} [Field K] [CharZero K] (k s : ℕ) :
    Module.finrank K (OddExteriorQuotientDegree (K := K) k s) =
      StripWalks.paperWalkCount (2*k+1) s := by
  rw [Module.finrank_eq_card_basis (oddExteriorBasis (K := K) k s),
    card_goodOddIndex_eq_paperWalkCount]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0218

section TAF_LiteralSource_0219
/- Original module: PaperVerification.AlternatingFormsOddActualGeneric -/


/-!
# The actual odd generic quotient has the paper's complete walk series

This combines the explicit dominant orbit of the literal odd pencil, the
actual good exterior basis after its proved coordinate permutation, and
the bijection with the paper's bounded walks.  The single coefficient
polynomial controls every exterior degree simultaneously.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

theorem odd_actual_generic_hilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 → ∀ s : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨Q, hbase, hQ⟩ := oddOrbit_actual_hilbert_certificate (K := K) t
  refine ⟨Q, ?_, ?_⟩
  · intro hz
    exact hbase (by rw [hz, map_zero])
  · intro y hy s
    rw [hQ y hy s, oddOrbitQuotientDegree_finrank,
      card_goodOddIndex_eq_paperWalkCount]

theorem odd_actual_generic_paperHilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 →
        (∀ s : ℕ, Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s) ∧
        (∀ s : ℕ, t+2 < s →
          Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) = 0) := by
  obtain ⟨Q, hQ, h⟩ := odd_actual_generic_hilbert (K := K) t
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  refine ⟨h y hy, ?_⟩
  intro s hs
  rw [h y hy s, paperWalkCount_odd_above_cutoff (t+1) s (by omega)]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0219

section TAF_LiteralSource_0220
/- Original module: PaperVerification.MatrixPowerSeriesResolvent -/


/-!
# Formal generating series of an actual finite transfer matrix

The coefficient of degree N is the actual matrix power T^N.  The resolvent
identity is proved coefficient by coefficient, with no convergence or
invertibility assumption on T.  A row certificate then determines a selected
entry of the inverse. This new source awaits compilation and audit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.MatrixPowerSeries

variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- Every entry is the formal series of the corresponding entries of T^N. -/
def seriesMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  Matrix.of fun i j ↦ PowerSeries.mk fun N ↦ (T^N) i j

@[simp] theorem coeff_seriesMatrix (T : Matrix I I R) (N : ℕ) (i j : I) :
    PowerSeries.coeff N (seriesMatrix T i j)=(T^N) i j :=
  by simp only [seriesMatrix,Matrix.of_apply,PowerSeries.coeff_mk]

/-- The actual matrix I-zT over the formal power-series ring. -/
def resolventMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  1-(PowerSeries.X : PowerSeries R) • T.map (PowerSeries.C (R := R))

theorem series_equation (T : Matrix I I R) (i j : I) :
    seriesMatrix T i j-PowerSeries.X*
        (∑ k,PowerSeries.C (T i k)*seriesMatrix T k j)=
      PowerSeries.C ((1 : Matrix I I R) i j) := by
  apply PowerSeries.ext
  intro N
  cases N with
  | zero => simp [seriesMatrix]
  | succ N =>
      simp [coeff_seriesMatrix,PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul,pow_succ',Matrix.mul_apply]

/-- The coefficient-defined series is a right inverse of the actual resolvent. -/
theorem resolvent_mul_series (T : Matrix I I R) :
    resolventMatrix T*seriesMatrix T=1 := by
  rw [resolventMatrix,sub_mul,one_mul,Matrix.smul_mul]
  apply Matrix.ext
  intro i j
  change seriesMatrix T i j-PowerSeries.X*
      ((T.map (PowerSeries.C (R := R))*seriesMatrix T) i j)=
        (1 : Matrix I I (PowerSeries R)) i j
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [series_equation]
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

/-- A row certificate computes an inverse entry by associativity of the
actual finite matrix product. It is not a determinant or inverse assumption. -/
theorem row_certificate_entry (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first : I)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D) (last : I) :
    D*seriesMatrix T first last=row last := by
  have h := congrFun (Matrix.vecMul_vecMul row (resolventMatrix T) (seriesMatrix T)) last
  rw [hrow,resolvent_mul_series,Matrix.single_vecMul,Matrix.vecMul_one] at h
  exact h

/-- A unit-constant row certificate gives the entire formal inverse entry. -/
theorem series_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1) :
    seriesMatrix T first last=PowerSeries.X^height*PowerSeries.invOfUnit D 1 := by
  have hentry := row_certificate_entry T row D first hrow last
  rw [hlast] at hentry
  calc
    seriesMatrix T first last = 1*seriesMatrix T first last := (one_mul _).symm
    _ = (PowerSeries.invOfUnit D 1*D)*seriesMatrix T first last := by
      rw [PowerSeries.invOfUnit_mul D 1 hD]
    _ = PowerSeries.invOfUnit D 1*(D*seriesMatrix T first last) := mul_assoc _ _ _
    _ = PowerSeries.invOfUnit D 1*PowerSeries.X^height := by rw [hentry]
    _ = PowerSeries.X^height*PowerSeries.invOfUnit D 1 := mul_comm _ _

/-- All coefficients, including the unbounded length parameter, follow from
the formal row certificate. -/
theorem power_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1)
    (s : ℕ) :
    (T^(s+height)) first last=PowerSeries.coeff s (PowerSeries.invOfUnit D 1) := by
  have h := congrArg (PowerSeries.coeff (s+height))
    (series_entry_of_row_certificate T row D first last height hrow hlast hD)
  rwa [coeff_seriesMatrix,PowerSeries.coeff_X_pow_mul] at h

end PaperVerification.MatrixPowerSeries
end
end
end TAF_LiteralSource_0220

section TAF_LiteralSource_0221
/- Original module: PaperVerification.PowerSeriesInverseDeterminant -/


/-!
# The exact Hessenberg determinant for a reciprocal coefficient

The finite coefficient matrix of multiplication by a unit-constant power
series is lower triangular with determinant one.  Its first inverse column
is the coefficient vector of the reciprocal.  The adjugate formula gives
the Hessenberg determinant, including the zero-size case and every sign.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.PowerSeriesInverseDeterminant

variable {R : Type*} [CommRing R]

def coefficientTriangular (φ : PowerSeries R) (s : ℕ) :
    Matrix (Fin (s+1)) (Fin (s+1)) R :=
  fun i j => if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) φ else 0

theorem coefficientTriangular_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    (coefficientTriangular φ s).det = 1 := by
  have hl : (coefficientTriangular φ s).IsLowerTriangular := by
    intro i j hij
    change (if j.val ≤ i.val then _ else (0 : R)) = 0
    exact if_neg (by exact Nat.not_le_of_gt hij)
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp only [coefficientTriangular, le_refl, if_true, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, Finset.prod_const_one]

theorem coefficientTriangular_mulVec (φ ψ : PowerSeries R) (s : ℕ) (i : Fin (s+1)) :
    (coefficientTriangular φ s *ᵥ (fun j => PowerSeries.coeff j.val ψ)) i =
      PowerSeries.coeff i.val (ψ*φ) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [coefficientTriangular, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a ψ * PowerSeries.coeff b φ) i.val]
  apply Finset.sum_bij (fun j hj => j.val)
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h)
  · intro j hj l hl h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, by have hi := i.isLt; omega⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ hj'⟩
  · intro j hj
    exact mul_comm _ _

theorem coefficientTriangular_inverse_column (φ : PowerSeries R)
    (hφ : φ.constantCoeff = 1) (s : ℕ) :
    coefficientTriangular φ s *ᵥ
      (fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)) = Pi.single 0 1 := by
  funext i
  rw [coefficientTriangular_mulVec, PowerSeries.invOfUnit_mul φ 1 hφ, PowerSeries.coeff_one]
  by_cases hi : i = 0
  · subst i
    simp
  · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi, hiv, Pi.single_apply, Ne.symm hi]

/-- The literal cofactor matrix, with the row and column signs distributed
so that alternating reciprocal coefficients become unsigned entries. -/
def inverseCoefficientMatrix (φ : PowerSeries R) (s : ℕ) : Matrix (Fin s) (Fin s) R :=
  fun i j => (-1 : R)^i.val * ((-1 : R)^(j.val+1) *
    (if i.val ≤ j.val+1 then PowerSeries.coeff (j.val+1-i.val) φ else 0))

theorem sign_products (s : ℕ) :
    (∏ i : Fin s, (-1 : R)^i.val) * (∏ i : Fin s, (-1 : R)^(i.val+1)) = (-1 : R)^s := by
  rw [← Finset.prod_mul_distrib]
  have hi (i : Fin s) : (-1 : R)^i.val * (-1 : R)^(i.val+1) = -1 := by
    rw [← pow_add, show i.val+(i.val+1)=2*i.val+1 by omega, pow_add, pow_mul]
    simp
  simp_rw [hi]
  simp

theorem inverseCoefficientMatrix_det (φ : PowerSeries R) (s : ℕ) :
    (inverseCoefficientMatrix φ s).det = (-1 : R)^s *
      ((coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc).det := by
  let B := (coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc
  have he : inverseCoefficientMatrix φ s =
      Matrix.of (fun i j : Fin s => (-1 : R)^i.val *
        (Matrix.of (fun l r : Fin s => (-1 : R)^(r.val+1) * Bᵀ l r)) i j) := by
    ext i j
    rfl
  rw [he, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, sign_products,
    Matrix.det_transpose]

/-- The reciprocal coefficient equals a genuine finite determinant.  The
proof uses only actual multiplication coefficients and the adjugate identity. -/
theorem coeff_inverse_eq_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = (inverseCoefficientMatrix φ s).det := by
  let T := coefficientTriangular φ s
  let v : Fin (s+1) → R := fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)
  have hv : T *ᵥ v = Pi.single 0 1 := coefficientTriangular_inverse_column φ hφ s
  have hd : T.det = 1 := coefficientTriangular_det φ hφ s
  have he := congrArg (fun w : Fin (s+1) → R => T.adjugate *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hd, one_smul,
    Matrix.one_mulVec, Matrix.mulVec_single_one] at he
  have hc := congrFun he (Fin.last s)
  change PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = T.adjugate (Fin.last s) 0 at hc
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hc
  simp only [Fin.val_zero, Fin.val_last, Nat.zero_add, Fin.zero_succAbove,
    Fin.succAbove_last] at hc
  rw [inverseCoefficientMatrix_det]
  exact hc

end PaperVerification.PowerSeriesInverseDeterminant
end
end
end TAF_LiteralSource_0221

