module

public import paper_verification.literal002.PalomarPart000
import all paper_verification.literal002.PalomarPart000
public import paper_verification.literal001
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.List.FinRange
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.FunLike.Fintype
import Mathlib.Order.Preorder.Finite
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Choose
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

set_option Elab.async false

section TAF_LiteralSource_0160
/- Original module: TauCeti.Algebra.GroupAction.OrbitRelQuotient -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Generic orbit-relation quotient helpers

This file records small generic additions to Mathlib's `MulAction.orbitRel.Quotient` API.

## Main declarations

* `TauCeti.MulAction.orbitRelQuotientBotEquiv`: the quotient by the trivial subgroup is the
  original space.
* `TauCeti.MulAction.transversalEquivOrbitRelQuotient`: a set meeting every orbit, such that a
  group element carrying one of its points into it fixes that point, is a set of orbit
  representatives.
* `TauCeti.MulAction.exists_smul_out_eq`: every point of an orbit is a translate of the chosen
  representative `Quotient.out` of that orbit.
* `TauCeti.MulAction.card_orbitRelQuotient_eq_one`: a pretransitive action on a nonempty type
  has exactly one orbit.
* `TauCeti.MulAction.card_orbitRelQuotient_anti`: enlarging the acting subgroup can only
  decrease the number of orbits.
* `TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq_iff`: equality after the bottom-to-`H`
  quotient map is membership in an `H`-orbit.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem`: in a cancellative
  action, two translates have the same `H`-orbit class exactly when the translators differ on
  the right by an element of `H`; this holds for an arbitrary subgroup.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_base_iff`: in a cancellative action, a
  translate has the same `H`-orbit class as the base point exactly when the translator is in
  `H`.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq`: for a
  normal subgroup, equality of two translates in the `H`-orbit quotient is equality of the
  corresponding inverse representatives in `N(H) / H`.
* `TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal`: in a free transitive
  action, the quotient by a normal subgroup is the normalizer quotient `N(H) / H`.
* `TauCeti.MulAction.normalizerOrbitRelQuotientPermHom`: the normalizer action on the
  quotient by `H`-orbits.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotientPermHom`: the descended action of
  `N(H) / H` on the quotient by `H`-orbits.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotientIsPretransitive`: if the normalizer
  acts transitively, then the descended `N(H) / H` action on the `H`-orbit quotient is
  transitive.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff`: if the original
  action is free, then the descended `N(H) / H` action on the `H`-orbit quotient is free.
* `TauCeti.MulAction.orbitRelQuotientCongr`: an equivalence carrying one action to another along
  a group isomorphism induces an equivalence of orbit spaces.
* `TauCeti.MulAction.orbitRelQuotientLift`: a `G`-invariant map descends to the orbit space,
  uniquely (`TauCeti.MulAction.eq_orbitRelQuotientLift_iff`).
* `MulActionHom.orbitRelQuotientMap`: an equivariant map induces a map of orbit spaces,
  functorially, and descent is natural along it
  (`MulActionHom.orbitRelQuotientLift_comp_orbitRelQuotientMap`).
* `TauCeti.MulAction.stabilizer_sigma_mk`: the stabilizer of a sigma point is its fibre
  stabilizer.
* `TauCeti.MulAction.orbitRelQuotientSigmaEquiv`: the orbit space of a componentwise sigma
  action is the sigma type of the fibre orbit spaces.
* `TauCeti.MulAction.orbitRelQuotientSumEquiv`: the orbit space of an action on `X ⊕ Y` is the
  sum of the orbit spaces of `X` and `Y`.
* `TauCeti.MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk` and
  `TauCeti.MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE`: the representative convention of
  Mathlib's `equivSubgroupOrbitsQuotientGroup` and its naturality in subgroup inclusions.
* `MulAction.orbitRel.Quotient.instMulActionQuotientGroup`: for a normal subgroup `H`, the
  quotient group `G ⧸ H` acts on the space of `H`-orbits by translating representatives
  (`MulAction.orbitRel.Quotient.mk_smul_mk`), and its additive version.
-/

public section

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

private lemma eq_of_bot_orbitRel {x y : X}
    (h : MulAction.orbitRel (⊥ : Subgroup G) X x y) : x = y := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨g, hg⟩
  have hg_one : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  have hsmul : (g : G) • y = x := by
    simpa [Subgroup.smul_def] using hg
  rw [hg_one, one_smul] at hsmul
  exact hsmul.symm

/-- Quotienting a group action by the trivial subgroup gives back the original space. -/
noncomputable def MulAction.orbitRelQuotientBotEquiv :
    MulAction.orbitRel.Quotient (⊥ : Subgroup G) X ≃ X :=
  { toFun := Quotient.lift (fun x : X => x) fun _ _ h => eq_of_bot_orbitRel h
    invFun := Quotient.mk''
    left_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      rfl
    right_inv := by
      intro x
      rfl }

/-- The bottom-subgroup quotient equivalence sends a class to its representative. -/
@[simp]
lemma MulAction.orbitRelQuotientBotEquiv_mk (x : X) :
    MulAction.orbitRelQuotientBotEquiv
        (G := G) (X := X) (Quotient.mk'' x :
          MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) = x :=
  (MulAction.orbitRelQuotientBotEquiv (G := G) (X := X)).right_inv x

/-- The inverse bottom-subgroup quotient equivalence sends a point to its quotient class. -/
@[simp]
lemma MulAction.orbitRelQuotientBotEquiv_symm_apply (x : X) :
    (MulAction.orbitRelQuotientBotEquiv (G := G) (X := X)).symm x =
      (Quotient.mk'' x : MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :=
  ((MulAction.orbitRelQuotientBotEquiv (G := G) (X := X)).eq_symm_apply).mpr
    (MulAction.orbitRelQuotientBotEquiv_mk (G := G) (X := X) x)

/-- A set `s` meeting every orbit, such that a group element carrying a point of `s` into `s`
fixes that point, is a set of orbit representatives: sending a point of `s` to its orbit is a
bijection onto the orbit space. -/
noncomputable def MulAction.transversalEquivOrbitRelQuotient {s : Set X}
    (hex : ∀ x : X, ∃ g : G, g • x ∈ s)
    (hfix : ∀ x ∈ s, ∀ g : G, g • x ∈ s → g • x = x) : s ≃ MulAction.orbitRel.Quotient G X :=
  Equiv.ofBijective (fun x ↦ Quotient.mk'' x.1)
    ⟨fun x y h ↦ (Quotient.exact h).elim fun g (hg : g • (y : X) = x) ↦
      Subtype.ext <| hg.symm.trans <| hfix _ y.2 g <| hg ▸ x.2,
    Quotient.ind' fun x ↦ (hex x).elim fun g hg ↦
      ⟨⟨g • x, hg⟩, MulAction.orbitRel.Quotient.quotient_smul_eq⟩⟩

/-- `transversalEquivOrbitRelQuotient` sends a point of `s` to its orbit. -/
@[simp]
lemma MulAction.transversalEquivOrbitRelQuotient_apply {s : Set X}
    (hex : ∀ x : X, ∃ g : G, g • x ∈ s)
    (hfix : ∀ x ∈ s, ∀ g : G, g • x ∈ s → g • x = x) (x : s) :
    MulAction.transversalEquivOrbitRelQuotient hex hfix x = Quotient.mk'' (x : X) :=
  (rfl)

/-- The inverse of `transversalEquivOrbitRelQuotient` sends the orbit of `x ∈ s` back to `x`. -/
@[simp]
lemma MulAction.transversalEquivOrbitRelQuotient_symm_mk {s : Set X}
    (hex : ∀ x : X, ∃ g : G, g • x ∈ s)
    (hfix : ∀ x ∈ s, ∀ g : G, g • x ∈ s → g • x = x) (x : s) :
    (MulAction.transversalEquivOrbitRelQuotient hex hfix).symm (Quotient.mk'' (x : X)) = x :=
  (MulAction.transversalEquivOrbitRelQuotient hex hfix).symm_apply_apply x

/-- The inverse of `transversalEquivOrbitRelQuotient` picks the point of `s` in the given orbit. -/
lemma MulAction.transversalEquivOrbitRelQuotient_symm_mk_mem_orbit {s : Set X}
    (hex : ∀ x : X, ∃ g : G, g • x ∈ s) (hfix : ∀ x ∈ s, ∀ g : G, g • x ∈ s → g • x = x) (x : X) :
    ((MulAction.transversalEquivOrbitRelQuotient hex hfix).symm (Quotient.mk'' x) : X) ∈
      MulAction.orbit G x :=
  Quotient.exact <| (MulAction.transversalEquivOrbitRelQuotient hex hfix).apply_symm_apply _

/-- Equality of bottom-subgroup orbit classes is equality of representatives. -/
@[simp]
lemma MulAction.orbitRelQuotientBot_mk_eq_iff (x y : X) :
    (Quotient.mk'' x : MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) =
        Quotient.mk'' y ↔
      x = y := by
  constructor
  · intro h
    exact congrArg (MulAction.orbitRelQuotientBotEquiv (G := G) (X := X)) h
  · intro h
    rw [h]

/-- Orbit relations are monotone in the acting subgroup. -/
lemma MulAction.orbitRel_le_of_subgroup_le {H K : Subgroup G} (hHK : H ≤ K) :
    MulAction.orbitRel H X ≤ MulAction.orbitRel K X := by
  intro x y h
  rw [MulAction.orbitRel_apply] at h ⊢
  rcases h with ⟨g, hg⟩
  exact ⟨⟨g.1, hHK g.2⟩, hg⟩

/-- **Every point of an orbit is a translate of its chosen representative.** This is Mathlib's
`MulAction.orbitRel.Quotient.orbit_eq_orbit_out` in existential form. -/
lemma MulAction.exists_smul_out_eq {y : X} {ω : MulAction.orbitRel.Quotient G X}
    (h : (Quotient.mk'' y : MulAction.orbitRel.Quotient G X) = ω) : ∃ g : G, g • ω.out = y :=
  MulAction.mem_orbit_iff.1 <| MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq' ▸
    MulAction.orbitRel.Quotient.mem_orbit.2 h

/-- **A pretransitive action on a nonempty type has one orbit.** This is Mathlib's
`MulAction.pretransitive_iff_unique_quotient_of_nonempty` in counting form. -/
@[simp]
theorem MulAction.card_orbitRelQuotient_eq_one [Nonempty X] [MulAction.IsPretransitive G X] :
    Nat.card (MulAction.orbitRel.Quotient G X) = 1 :=
  let _ := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G X).mp ‹_›).some
  Nat.card_unique

/-- Enlarging the acting subgroup can only decrease the number of orbits. -/
theorem MulAction.card_orbitRelQuotient_anti {H K : Subgroup G} (hHK : H ≤ K)
    [Finite (MulAction.orbitRel.Quotient H X)] :
    Nat.card (MulAction.orbitRel.Quotient K X) ≤
      Nat.card (MulAction.orbitRel.Quotient H X) := by
  let f := Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK)
  apply Nat.card_le_card_of_surjective f
  intro q
  induction q using Quotient.inductionOn'
  exact ⟨Quotient.mk'' _, rfl⟩

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma MulAction.orbitRelQuotientMapOfLE_bot_eq (H : Subgroup G) :
    Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) =
      (fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X)) ∘
        MulAction.orbitRelQuotientBotEquiv (G := G) (X := X) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

/-- Equality in an `H`-orbit quotient can be checked after choosing representatives through
the bottom-subgroup quotient. -/
lemma MulAction.orbitRelQuotientMapOfLE_bot_eq_iff (H : Subgroup G)
    (x y : MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :
    Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) x =
        Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X)
          (bot_le : (⊥ : Subgroup G) ≤ H)) y ↔
      MulAction.orbitRelQuotientBotEquiv (G := G) (X := X) x ∈
        MulAction.orbit H (MulAction.orbitRelQuotientBotEquiv (G := G) (X := X) y) := by
  simp [MulAction.orbitRelQuotientMapOfLE_bot_eq, Quotient.eq'', MulAction.orbitRel_apply]

/-- In a cancellative action, two translates have the same subgroup-orbit quotient class
exactly when the translators differ on the right by an element of the subgroup. This holds
for an arbitrary subgroup; the normal-subgroup criterion
`orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq` follows from it. -/
lemma MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem [IsCancelSMul G X] (H : Subgroup G)
    (x : X) (g k : G) : (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      g * k⁻¹ ∈ H := by
  constructor
  · intro h
    rw [Quotient.eq'', MulAction.orbitRel_apply] at h
    rcases h with ⟨l, hl⟩
    have hmul : ((l : G) * k) • x = g • x := by
      simpa [Subgroup.smul_def, smul_smul] using hl
    have hg : (l : G) * k = g := IsCancelSMul.right_cancel _ _ x hmul
    simp [← hg, mul_assoc]
  · intro hg
    rw [Quotient.eq'', MulAction.orbitRel_apply]
    exact ⟨⟨g * k⁻¹, hg⟩, by simp [Subgroup.smul_def, smul_smul]⟩

/-- In a cancellative action, a translate has the same subgroup-orbit quotient class as the
base point exactly when the translating group element belongs to the subgroup. -/
lemma MulAction.orbitRelQuotient_smul_eq_base_iff [IsCancelSMul G X] (H : Subgroup G) (g : G)
    (x : X) :
    (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' x ↔
      g ∈ H := by
  simpa using MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem H x g 1

/-- In a cancellative action by `G`, equality of two translates in the quotient by a normal
subgroup `H` is equality of the corresponding inverse representatives in the normalizer
quotient `N(H) / H`. -/
lemma MulAction.orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq [IsCancelSMul G X]
    (H : Subgroup G) [H.Normal] (x : X) (g k : G) :
    (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      Subgroup.normalizerQuotientMk H
          ⟨g⁻¹, by simp [H.normalizer_eq_top]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨k⁻¹, by simp [H.normalizer_eq_top]⟩ := by
  rw [MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem,
    Subgroup.normalizerQuotientMk_eq_iff_div_mem, div_eq_mul_inv, inv_inv,
    (inferInstance : H.Normal).mem_comm_iff, ← inv_mem_iff]
  simp [mul_inv_rev]

/-- Mathlib's subgroup-orbit quotient equivalence sends the coset of `g` back to the orbit
class of `g⁻¹ • x`. This records the representative convention once, so later lemmas can
rewrite through a named theorem rather than relying directly on definitional equality. -/
@[simp]
lemma MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk
    [MulAction.IsPretransitive G X] [IsCancelSMul G X]
    (H : Subgroup G) (x : X) (g : G) : (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
        (QuotientGroup.mk (s := H) g) =
      (Quotient.mk'' (g⁻¹ • x) : MulAction.orbitRel.Quotient H X) :=
  rfl

/-- The subgroup-orbit quotient equivalence sends the orbit class of `g • x` to the coset
of `g⁻¹`. -/
@[simp]
lemma MulAction.equivSubgroupOrbitsQuotientGroup_apply_smul
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) (x : X) (g : G) :
    MulAction.equivSubgroupOrbitsQuotientGroup x H
        (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
      QuotientGroup.mk (s := H) g⁻¹ := by
  simpa [MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk, inv_inv] using
    (MulAction.equivSubgroupOrbitsQuotientGroup x H).apply_symm_apply
    (QuotientGroup.mk (s := H) g⁻¹)

private lemma orbitRelQuotientMapOfLE_mk {H K : Subgroup G} (hHK : H ≤ K) (x : X) :
    Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      (Quotient.mk'' x : MulAction.orbitRel.Quotient K X) :=
  TauCeti.Setoid.map_of_le_mk (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK) x

/-- The subgroup-orbit quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] {H K : Subgroup G} (hHK : H ≤ K) (x₀ : X)
    (x : MulAction.orbitRel.Quotient H X) :
    Subgroup.quotientMapOfLE hHK
        (MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x) =
      MulAction.equivSubgroupOrbitsQuotientGroup x₀ K
        (Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK) x) := by
  refine Quotient.inductionOn' x ?_
  intro x'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ x'
  rw [← hg]
  rw [MulAction.equivSubgroupOrbitsQuotientGroup_apply_smul]
  rw [orbitRelQuotientMapOfLE_mk hHK]
  rw [MulAction.equivSubgroupOrbitsQuotientGroup_apply_smul, Subgroup.quotientMapOfLE_apply_mk]

private lemma normalizer_smul_mem_orbit (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) {x y : X} (hxy : x ∈ MulAction.orbit H y) :
    (g : G) • x ∈ MulAction.orbit H ((g : G) • y) := by
  rcases hxy with ⟨h, hh⟩
  refine ⟨⟨(g : G) * h * (g : G)⁻¹, ?_⟩, ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.mp g.2) (h : G)).1 h.2
  · rw [← hh]
    simp [Subgroup.smul_def, mul_smul]

/-- A normalizer representative acts on the quotient by `H`-orbits. -/
def MulAction.normalizerOrbitRelQuotientMap (H : Subgroup G) (g : Subgroup.normalizer (H : Set G)) :
    MulAction.orbitRel.Quotient H X → MulAction.orbitRel.Quotient H X :=
  Quotient.map' (fun x : X => (g : G) • x) fun x y hxy => by
    rw [MulAction.orbitRel_apply] at hxy ⊢
    exact normalizer_smul_mem_orbit H g hxy

/-- The normalizer action on an orbit quotient sends a class to the class of its translate. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientMap_apply (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    MulAction.normalizerOrbitRelQuotientMap H g
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [MulAction.normalizerOrbitRelQuotientMap]

/-- The normalizer representative `1` acts trivially on the orbit quotient. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientMap_one (H : Subgroup G) :
    MulAction.normalizerOrbitRelQuotientMap (X := X) H ⟨1, by simp⟩ = id := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [MulAction.normalizerOrbitRelQuotientMap]

/-- Normalizer representatives act by composition on the orbit quotient. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientMap_mul (H : Subgroup G)
    (g k : Subgroup.normalizer (H : Set G)) :
    MulAction.normalizerOrbitRelQuotientMap (X := X) H (g * k) =
      MulAction.normalizerOrbitRelQuotientMap H g ∘
        MulAction.normalizerOrbitRelQuotientMap H k := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [MulAction.normalizerOrbitRelQuotientMap, mul_smul]

/-- A normalizer representative acts on the orbit quotient by a permutation. -/
def MulAction.normalizerOrbitRelQuotientEquiv
    (H : Subgroup G) (g : Subgroup.normalizer (H : Set G)) :
    Equiv.Perm (MulAction.orbitRel.Quotient H X) where
  toFun := MulAction.normalizerOrbitRelQuotientMap H g
  invFun := MulAction.normalizerOrbitRelQuotientMap H g⁻¹
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [MulAction.normalizerOrbitRelQuotientMap]
  right_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [MulAction.normalizerOrbitRelQuotientMap]

/-- A normalizer representative permutes orbit classes by translating representatives. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientEquiv_apply (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    MulAction.normalizerOrbitRelQuotientEquiv H g
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [MulAction.normalizerOrbitRelQuotientEquiv]

/-- The inverse normalizer permutation translates representatives by the inverse element. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientEquiv_symm_apply (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    (MulAction.normalizerOrbitRelQuotientEquiv H g).symm
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G)⁻¹ • x) :=
  by simp [MulAction.normalizerOrbitRelQuotientEquiv]

/-- The normalizer action on the orbit quotient as a permutation representation. -/
noncomputable def MulAction.normalizerOrbitRelQuotientPermHom (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) →*
      Equiv.Perm (MulAction.orbitRel.Quotient H X) where
  toFun := MulAction.normalizerOrbitRelQuotientEquiv H
  map_one' := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [MulAction.normalizerOrbitRelQuotientEquiv, MulAction.normalizerOrbitRelQuotientMap]
  map_mul' := by
    intro g k
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp only [MulAction.normalizerOrbitRelQuotientEquiv_apply, Equiv.Perm.coe_mul,
      Function.comp_apply]
    have hgk : ((g * k : Subgroup.normalizer (H : Set G)) : G) = (g : G) * (k : G) :=
      rfl
    rw [hgk]
    rw [mul_smul]

/-- The normalizer permutation homomorphism sends representatives to their translates. -/
@[simp]
lemma MulAction.normalizerOrbitRelQuotientPermHom_apply (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    MulAction.normalizerOrbitRelQuotientPermHom (X := X) H g
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [MulAction.normalizerOrbitRelQuotientPermHom]

/-- Any normalizer representative whose underlying group element lies in `H` acts trivially
on the quotient by `H`-orbits. -/
lemma MulAction.normalizerOrbitRelQuotientPermHom_eq_one_of_mem
    (H : Subgroup G) (g : Subgroup.normalizer (H : Set G)) (hg : (g : G) ∈ H) :
    MulAction.normalizerOrbitRelQuotientPermHom (X := X) H g = 1 := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rw [MulAction.normalizerOrbitRelQuotientPermHom_apply]
  exact Quotient.sound' ⟨⟨(g : G), hg⟩, rfl⟩

/-- The action of the normalizer on an orbit quotient descends to `N(H) / H`. -/
noncomputable def MulAction.normalizerQuotientOrbitRelQuotientPermHom (H : Subgroup G) :
    Subgroup.normalizerQuotient H →*
      Equiv.Perm (MulAction.orbitRel.Quotient H X) :=
  Subgroup.normalizerQuotientLift H (MulAction.normalizerOrbitRelQuotientPermHom (X := X) H)
    (MulAction.normalizerOrbitRelQuotientPermHom_eq_one_of_mem (X := X) H)

/-- The descended normalizer-quotient action sends a normalizer representative to the
corresponding translate on orbit classes. -/
lemma MulAction.normalizerQuotientOrbitRelQuotientPermHom_mk_apply (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    MulAction.normalizerQuotientOrbitRelQuotientPermHom (X := X) H
        (Subgroup.normalizerQuotientMk H g)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [MulAction.normalizerQuotientOrbitRelQuotientPermHom]

/-- The normalizer quotient `N(H) / H` acts on the quotient by `H`-orbits. -/
@[implicit_reducible]
noncomputable def MulAction.normalizerQuotientOrbitRelQuotientMulAction (H : Subgroup G) :
    MulAction (Subgroup.normalizerQuotient H) (MulAction.orbitRel.Quotient H X) :=
  MulAction.compHom (MulAction.orbitRel.Quotient H X)
    (MulAction.normalizerQuotientOrbitRelQuotientPermHom (X := X) H)

/-- A normalizer-quotient representative acts on the orbit quotient by translating
representatives. -/
lemma MulAction.normalizerQuotientOrbitRelQuotient_smul_mk (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (x : X) :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    Subgroup.normalizerQuotientMk H g •
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by
    -- The named action is the `compHom` action, whose smul applies the underlying
    -- permutation homomorphism to the point.
    change MulAction.normalizerQuotientOrbitRelQuotientPermHom (X := X) H
        (Subgroup.normalizerQuotientMk H g)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x)
    exact MulAction.normalizerQuotientOrbitRelQuotientPermHom_mk_apply (X := X) H g x

/-- In a free transitive action, quotienting by a normal subgroup `H` identifies the
`H`-orbit quotient with the normalizer quotient `N(H) / H`. The representative convention is
the same as Mathlib's `equivSubgroupOrbitsQuotientGroup`: the class of `g • x` corresponds to
the class of `g⁻¹`. -/
noncomputable def MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X) :
    MulAction.orbitRel.Quotient H X ≃ Subgroup.normalizerQuotient H :=
  (MulAction.equivSubgroupOrbitsQuotientGroup x H).trans
    (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.symm

/-- The normal-subgroup orbit quotient equivalence, followed by the normalizer quotient's
normal-case comparison, is Mathlib's equivalence to `G ⧸ H`. -/
@[simp]
lemma
  MulAction.normalizerQuotientEquivQuotientOfNormal_orbitRelQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x₀ : X)
    (x : MulAction.orbitRel.Quotient H X) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ x) =
      MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x :=
  (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.apply_symm_apply
    (MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x)

/-- The inverse normal-subgroup orbit-quotient equivalence sends a normalizer representative
to the orbit class of its inverse acting on the base point. -/
@[simp]
lemma MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X)
    (g : Subgroup.normalizer (H : Set G)) :
    (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x).symm
        (g : Subgroup.normalizerQuotient H) =
      (Quotient.mk'' ((g : G)⁻¹ • x) : MulAction.orbitRel.Quotient H X) := by
  -- The new equivalence is definitionally Mathlib's orbit-quotient equivalence transposed
  -- across the normal-subgroup comparison `N(H) / H ≃ G ⧸ H`.
  change (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
      (Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (Subgroup.normalizerQuotientMk H g)) =
    (Quotient.mk'' ((g : G)⁻¹ • x) : MulAction.orbitRel.Quotient H X)
  rw [Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  exact MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk H x (g : G)

/-- The normal-subgroup orbit-quotient equivalence sends the class of `g • x` to the
normalizer-quotient class of `g⁻¹`. -/
@[simp]
lemma MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X) (g : G) :
    MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x
        (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
      Subgroup.normalizerQuotientMk H
        ⟨g⁻¹, by simp [H.normalizer_eq_top]⟩ := by
  rw [← (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x).eq_symm_apply]
  rw [Subgroup.normalizerQuotientMk_apply]
  rw [MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mk]
  simp

/-- Under the normal-subgroup orbit-quotient equivalence, the descended normalizer-quotient
action is right multiplication by the inverse. -/
@[simp]
lemma MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x₀ : X)
    (a : Subgroup.normalizerQuotient H) (x : MulAction.orbitRel.Quotient H X) :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ (a • x) =
      MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ x * a⁻¹ := by
  let := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  obtain ⟨g, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
  refine Quotient.inductionOn' x ?_
  intro x
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G x₀ x
  rw [← hk]
  rw [MulAction.normalizerQuotientOrbitRelQuotient_smul_mk, ← mul_smul,
    MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul,
    MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  simp [mul_inv_rev]

/-- Applying the inverse normal-subgroup orbit-quotient equivalence after right
multiplication by `a⁻¹` is the same as acting by `a` on the orbit quotient. -/
lemma MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [MulAction.IsPretransitive G X] [IsCancelSMul G X]
    (H : Subgroup G) [H.Normal] (x₀ : X) (a y : Subgroup.normalizerQuotient H) :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).symm (y * a⁻¹) =
      a • (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).symm y := by
  let := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  apply (MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).injective
  rw [Equiv.apply_symm_apply,
    MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv,
    Equiv.apply_symm_apply]

/-- If the normalizer of `H` acts transitively on `X`, then the descended `N(H) / H` action on
the quotient by `H`-orbits is transitive. -/
theorem MulAction.normalizerQuotientOrbitRelQuotientIsPretransitive (H : Subgroup G)
    [MulAction.IsPretransitive (Subgroup.normalizer (H : Set G)) X] :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (MulAction.orbitRel.Quotient H X) := by
  let := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  let φ : Subgroup.normalizer (H : Set G) → Subgroup.normalizerQuotient H :=
    Subgroup.normalizerQuotientMk H
  let f : X →ₑ[φ] MulAction.orbitRel.Quotient H X := {
    toFun := Quotient.mk''
    map_smul' g x := by
      exact (MulAction.normalizerQuotientOrbitRelQuotient_smul_mk (X := X) H g x).symm }
  exact MulAction.IsPretransitive.of_surjective_map
    (f := f) Quotient.mk''_surjective inferInstance

/-- If `H` is normal and `G` acts transitively on `X`, then the descended `N(H) / H` action
on the quotient by `H`-orbits is transitive. -/
theorem MulAction.normalizerQuotientOrbitRelQuotientIsPretransitiveOfNormal
    [MulAction.IsPretransitive G X] (H : Subgroup G) [H.Normal] :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (MulAction.orbitRel.Quotient H X) := by
  let : MulAction.IsPretransitive (Subgroup.normalizer (H : Set G)) X :=
    MulAction.IsPretransitive.mk fun x y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
      refine ⟨⟨g, by simp [H.normalizer_eq_top]⟩, ?_⟩
      simpa using hg
  exact MulAction.normalizerQuotientOrbitRelQuotientIsPretransitive (X := X) H

/-- Equality after the descended `N(H) / H` action on an `H`-orbit quotient is equality of
normalizer-quotient elements, provided the original action is free. -/
@[simp]
lemma MulAction.normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff [IsCancelSMul G X]
    (H : Subgroup G) (a c : Subgroup.normalizerQuotient H)
    (x : MulAction.orbitRel.Quotient H X) :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    a • x = c • x ↔ a = c := by
  let := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
    obtain ⟨k, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H c
    refine Quotient.inductionOn' x ?_ h
    intro x h
    rw [MulAction.normalizerQuotientOrbitRelQuotient_smul_mk,
      MulAction.normalizerQuotientOrbitRelQuotient_smul_mk] at h
    rw [Subgroup.normalizerQuotientMk_eq_iff_div_mem]
    simpa [div_eq_mul_inv] using
      (MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem H x (g : G) (k : G)).mp h
  · intro h
    rw [h]

/-- If a group acts freely on `X`, then the descended `N(H) / H` action on the quotient of `X`
by `H`-orbits is free. This packages `normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff` as the
cancellativity of the descended action. -/
theorem MulAction.normalizerQuotientOrbitRelQuotientIsCancelSMul
    [IsCancelSMul G X] (H : Subgroup G) :
    letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    IsCancelSMul (Subgroup.normalizerQuotient H) (MulAction.orbitRel.Quotient H X) :=
  letI := MulAction.normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  { right_cancel' := fun a c x h =>
      (MulAction.normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff H a c x).mp h }

section Congr

variable {H Y : Type*} [Group H] [MulAction H Y]

/-- **An equivariant equivalence induces an equivalence of orbit spaces**: if `e : X ≃ Y` carries
the `G`-action to the `H`-action along a group isomorphism `φ : G ≃* H`, it maps the `G`-orbits
onto the `H`-orbits. -/
def MulAction.orbitRelQuotientCongr (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = φ g • e x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient H Y :=
  -- both orbit relations unfold to an existential over the acting group; reindex it along `φ`
  Quotient.congr e fun _ _ ↦ φ.toEquiv.exists_congr fun _ ↦ by simp [← he]

/-- `orbitRelQuotientCongr φ e he` sends the orbit of `x` to the orbit of `e x`. -/
@[simp]
theorem MulAction.orbitRelQuotientCongr_mk (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = φ g • e x) (x : X) :
    MulAction.orbitRelQuotientCongr φ e he (Quotient.mk'' x) = Quotient.mk'' (e x) :=
  (rfl)

/-- The inverse of `orbitRelQuotientCongr φ e he` sends the orbit of `y` to the orbit of
`e.symm y`. -/
@[simp]
theorem MulAction.orbitRelQuotientCongr_symm_mk (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = φ g • e x) (y : Y) :
    (MulAction.orbitRelQuotientCongr φ e he).symm (Quotient.mk'' y) = Quotient.mk'' (e.symm y) :=
  (rfl)

end Congr

section Sum

variable {Y : Type*} [MulAction G Y]

/-- **The orbits of an action on a sum are those of the two summands**: `G` acts on `X ⊕ Y`
summandwise, so its orbit space is the sum of the orbit spaces of `X` and `Y`. -/
def MulAction.orbitRelQuotientSumEquiv :
    MulAction.orbitRel.Quotient G (X ⊕ Y) ≃
      MulAction.orbitRel.Quotient G X ⊕ MulAction.orbitRel.Quotient G Y where
  toFun := Quotient.lift (Sum.map Quotient.mk'' Quotient.mk'') <| by
    rintro (x | y) (x' | y') ⟨g, ⟨⟩⟩ <;> simp
  invFun := Sum.elim
    (Quotient.map' Sum.inl fun _ _ ⟨g, hg⟩ ↦ ⟨g, congrArg Sum.inl hg⟩)
    (Quotient.map' Sum.inr fun _ _ ⟨g, hg⟩ ↦ ⟨g, congrArg Sum.inr hg⟩)
  left_inv := by rintro ⟨x | y⟩ <;> rfl
  right_inv := by rintro (q | q) <;> induction q using Quotient.inductionOn' <;> rfl

/-- `orbitRelQuotientSumEquiv` sends the orbit of `x : X ⊕ Y` to the orbit of its summand: the
orbit of `Sum.inl a` goes to `Sum.inl` of the orbit of `a`, and that of `Sum.inr b` to `Sum.inr`
of the orbit of `b`. -/
@[simp]
theorem MulAction.orbitRelQuotientSumEquiv_mk (x : X ⊕ Y) :
    MulAction.orbitRelQuotientSumEquiv (Quotient.mk'' x : MulAction.orbitRel.Quotient G (X ⊕ Y)) =
      x.map Quotient.mk'' Quotient.mk'' :=
  (rfl)

/-- The inverse of `orbitRelQuotientSumEquiv` sends `Sum.inl` of the orbit of `x` to the orbit of
`Sum.inl x`. -/
@[simp]
theorem MulAction.orbitRelQuotientSumEquiv_symm_inl_mk (x : X) :
    (MulAction.orbitRelQuotientSumEquiv (G := G) (Y := Y)).symm (.inl (Quotient.mk'' x)) =
      Quotient.mk'' (Sum.inl x) :=
  (rfl)

/-- The inverse of `orbitRelQuotientSumEquiv` sends `Sum.inr` of the orbit of `y` to the orbit of
`Sum.inr y`. -/
@[simp]
theorem MulAction.orbitRelQuotientSumEquiv_symm_inr_mk (y : Y) :
    (MulAction.orbitRelQuotientSumEquiv (G := G) (X := X)).symm (.inr (Quotient.mk'' y)) =
      Quotient.mk'' (Sum.inr y) :=
  (rfl)

end Sum

section Sigma

variable {ι : Type*} {Y : ι → Type*} [∀ i, MulAction G (Y i)]

/-- The stabilizer of a point in a sigma type is its stabilizer in its fibre. -/
@[simp]
theorem MulAction.stabilizer_sigma_mk (i : ι) (y : Y i) :
    MulAction.stabilizer G (Sigma.mk i y) = MulAction.stabilizer G y := by
  ext g
  simp

/-- The orbit space of a componentwise sigma action is the sigma type of the fibre orbit
spaces. No transitivity or nonemptiness hypotheses are needed. -/
def MulAction.orbitRelQuotientSigmaEquiv :
    MulAction.orbitRel.Quotient G (Σ i, Y i) ≃ Σ i, MulAction.orbitRel.Quotient G (Y i) where
  toFun := Quotient.lift (fun y ↦ Sigma.mk y.1 (Quotient.mk'' y.2)) <| by
    rintro ⟨i, y⟩ ⟨j, z⟩ ⟨g, hg⟩
    cases congrArg Sigma.fst hg
    exact congrArg (Sigma.mk i) (Quotient.sound ⟨g, by simpa using hg⟩)
  invFun q := Quotient.map' (s₁ := MulAction.orbitRel G (Y q.1))
    (s₂ := MulAction.orbitRel G (Σ i, Y i)) (Sigma.mk q.1)
    (fun _ _ ⟨g, hg⟩ ↦ ⟨g, by simp only [Sigma.smul_mk, hg]⟩) q.2
  left_inv := by rintro ⟨i, y⟩; rfl
  right_inv := by
    rintro ⟨i, q⟩
    induction q using Quotient.inductionOn'
    rfl

/-- The sigma orbit equivalence sends a point to its fibre index and its fibre orbit. -/
@[simp]
theorem MulAction.orbitRelQuotientSigmaEquiv_mk (y : Σ i, Y i) :
    MulAction.orbitRelQuotientSigmaEquiv
        (Quotient.mk'' y : MulAction.orbitRel.Quotient G (Σ i, Y i)) =
      Sigma.mk y.1 (Quotient.mk'' y.2) :=
  (rfl)

/-- The inverse sends a fibre orbit to the orbit of the corresponding sigma point. -/
@[simp]
theorem MulAction.orbitRelQuotientSigmaEquiv_symm_mk (i : ι) (y : Y i) :
    (MulAction.orbitRelQuotientSigmaEquiv (G := G) (Y := Y)).symm
        ⟨i, Quotient.mk'' y⟩ = Quotient.mk'' (Sigma.mk i y) :=
  (rfl)

end Sigma

section Lift

variable {Y Z : Type*}

/-- **Descent of an invariant map to the orbit space.** A map `f : X → Y` that is invariant under
the action of `G` factors through the orbit projection `X → MulAction.orbitRel.Quotient G X`. -/
def MulAction.orbitRelQuotientLift (f : X → Y) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    MulAction.orbitRel.Quotient G X → Y :=
  Quotient.lift f <| by
    rintro _ x ⟨g, rfl⟩
    exact hf g x

variable {f : X → Y} {hf : ∀ (g : G) (x : X), f (g • x) = f x}

/-- The descent of `f` sends the orbit of `x` to `f x`. -/
@[simp]
theorem MulAction.orbitRelQuotientLift_mk (x : X) :
    MulAction.orbitRelQuotientLift f hf (Quotient.mk (MulAction.orbitRel G X) x) = f x :=
  (rfl)

/-- The descent of `f` composed with the orbit projection is `f`. -/
@[simp]
theorem MulAction.orbitRelQuotientLift_comp_mk :
    MulAction.orbitRelQuotientLift f hf ∘ Quotient.mk (MulAction.orbitRel G X) = f :=
  (rfl)

/-- **Uniqueness of the descent**: a map out of the orbit space is the descent of `f` exactly when
its composite with the orbit projection is `f`. -/
theorem MulAction.eq_orbitRelQuotientLift_iff {φ : MulAction.orbitRel.Quotient G X → Y} :
    φ = MulAction.orbitRelQuotientLift f hf ↔ φ ∘ Quotient.mk (MulAction.orbitRel G X) = f := by
  refine ⟨fun h ↦ h ▸ MulAction.orbitRelQuotientLift_comp_mk, fun h ↦ funext fun q ↦ ?_⟩
  induction q using Quotient.inductionOn with
  | h x => exact congrFun h x

/-- Postcomposing the descent of `f` with a map `h` gives the descent of `h ∘ f`. -/
theorem MulAction.comp_orbitRelQuotientLift (h : Y → Z) :
    h ∘ MulAction.orbitRelQuotientLift f hf =
      MulAction.orbitRelQuotientLift (h ∘ f) fun g x ↦ congrArg h (hf g x) :=
  MulAction.eq_orbitRelQuotientLift_iff.2 (rfl)

/-- The descent of a pair of invariant maps is the pair of their descents. -/
theorem MulAction.orbitRelQuotientLift_prodMk {f' : X → Z}
    (hf' : ∀ (g : G) (x : X), f' (g • x) = f' x) :
    MulAction.orbitRelQuotientLift (fun x ↦ (f x, f' x))
        (fun g x ↦ Prod.ext (hf g x) (hf' g x)) =
      fun q ↦ (MulAction.orbitRelQuotientLift f hf q, MulAction.orbitRelQuotientLift f' hf' q) :=
  funext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

end Lift

end TauCeti

/-! ### The quotient group action on orbits of a normal subgroup -/

namespace MulAction.orbitRel.Quotient

variable {G P : Type*} [Group G] (H : Subgroup G) [MulAction G P] [H.Normal]

/-- Translating by elements of `G` that agree modulo the normal subgroup `H` sends points in the
same `H`-orbit to points in the same `H`-orbit. -/
@[to_additive /-- Translating by elements of `G` that agree modulo the normal subgroup `H` sends
points in the same `H`-orbit to points in the same `H`-orbit. -/]
theorem orbitRel_smul_smul {g g' : G} {p q : P} (hg : g⁻¹ * g' ∈ H)
    (hpq : orbitRel H P p q) : orbitRel H P (g • p) (g' • q) := by
  rw [orbitRel_apply, mem_orbit_iff] at hpq ⊢
  obtain ⟨⟨h, hh⟩, rfl⟩ := hpq
  refine ⟨⟨g * h * g'⁻¹, ?_⟩, ?_⟩
  · have hk : g * (h * (g⁻¹ * g')⁻¹) * g⁻¹ ∈ H :=
      ‹H.Normal›.conj_mem _ (H.mul_mem hh (H.inv_mem hg)) g
    simpa [mul_assoc] using hk
  · simp [subgroup_smul_def, smul_smul, mul_assoc]

/-- The quotient group `G ⧸ H` acts on the space of `H`-orbits by translating representatives. -/
@[to_additive /-- The quotient group `G ⧸ H` acts on the space of `H`-orbits by translating
representatives. -/]
instance instSMulQuotientGroup : SMul (G ⧸ H) (orbitRel.Quotient H P) where
  smul := Quotient.map₂ (· • ·) fun _ _ hg _ _ hpq =>
    orbitRel_smul_smul H (QuotientGroup.leftRel_apply.1 hg) hpq

/-- The action of `G ⧸ H` on `H`-orbits is computed on representatives. -/
@[to_additive (attr := simp) /-- The action of `G ⧸ H` on `H`-orbits is computed on
representatives. -/]
theorem mk_smul_mk (g : G) (p : P) :
    (g : G ⧸ H) • (Quotient.mk'' p : orbitRel.Quotient H P) = Quotient.mk'' (g • p) :=
  rfl

/-- The quotient group `G ⧸ H` acts on the space of `H`-orbits. -/
@[to_additive /-- The quotient group `G ⧸ H` acts on the space of `H`-orbits. -/]
instance instMulActionQuotientGroup : MulAction (G ⧸ H) (orbitRel.Quotient H P) where
  one_smul x := by
    induction x using Quotient.inductionOn' with
    | h p => rw [← QuotientGroup.mk_one, mk_smul_mk, one_smul]
  mul_smul g g' x := by
    induction g using QuotientGroup.induction_on with | H g =>
    induction g' using QuotientGroup.induction_on with | H g' =>
    induction x using Quotient.inductionOn' with
    | h p => rw [← QuotientGroup.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul]

end MulAction.orbitRel.Quotient

namespace MulActionHom

open TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {H Y : Type*} [Group H] [MulAction H Y]
  {σ : G → H}

/-- **The map of orbit spaces induced by an equivariant map.** A map `φ : X → Y` carrying the
`G`-action to the `H`-action along `σ : G → H` sends `G`-orbits into `H`-orbits, so it descends to
a map of orbit spaces. -/
def orbitRelQuotientMap (φ : X →ₑ[σ] Y) :
    MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient H Y :=
  MulAction.orbitRelQuotientLift (fun x ↦ Quotient.mk (MulAction.orbitRel H Y) (φ x))
    fun g x ↦ by
      rw [map_smulₛₗ]
      exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The map induced by `φ` sends the orbit of `x` to the orbit of `φ x`. -/
@[simp]
theorem orbitRelQuotientMap_mk (φ : X →ₑ[σ] Y) (x : X) :
    orbitRelQuotientMap φ (Quotient.mk (MulAction.orbitRel G X) x) =
      Quotient.mk (MulAction.orbitRel H Y) (φ x) :=
  (rfl)

/-- The map induced by `φ` composed with the orbit projection of `X` is the orbit projection of
`Y` composed with `φ`. -/
@[simp]
theorem orbitRelQuotientMap_comp_mk (φ : X →ₑ[σ] Y) :
    orbitRelQuotientMap φ ∘ Quotient.mk (MulAction.orbitRel G X) =
      Quotient.mk (MulAction.orbitRel H Y) ∘ φ :=
  (rfl)

/-- The identity map induces the identity of the orbit space. -/
@[simp]
theorem orbitRelQuotientMap_id :
    orbitRelQuotientMap (MulActionHom.id G (X := X)) = id := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The map induced by a composite of equivariant maps is the composite of the induced maps. -/
theorem orbitRelQuotientMap_comp {K Z : Type*} [Group K] [MulAction K Z] {τ : H → K}
    {χ : G → K} [CompTriple σ τ χ] (ψ : Y →ₑ[τ] Z) (φ : X →ₑ[σ] Y) :
    orbitRelQuotientMap (ψ.comp φ) = orbitRelQuotientMap ψ ∘ orbitRelQuotientMap φ := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- **Naturality of descent.** For a `σ`-equivariant map `φ : X → Y` and an `H`-invariant map
`f : Y → Z`, the descent of the `G`-invariant map `f ∘ φ` factors through the map of orbit spaces
induced by `φ`. -/
theorem orbitRelQuotientLift_comp_orbitRelQuotientMap {Z : Type*} (φ : X →ₑ[σ] Y)
    {f : Y → Z} (hf : ∀ (h : H) (y : Y), f (h • y) = f y) :
    MulAction.orbitRelQuotientLift f hf ∘ orbitRelQuotientMap φ =
      MulAction.orbitRelQuotientLift (f ∘ φ) fun g x ↦ by
        simp only [Function.comp_apply, map_smulₛₗ, hf] := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

end MulActionHom
end
end TAF_LiteralSource_0160

section TAF_LiteralSource_0161
/- Original module: TauCeti.RepresentationTheory.OfMulAction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Commuting permutation representations and invariants of permutation representations

If monoids `G` and `H` act on a type `X` and the two actions commute, then the permutation
representations `Representation.ofMulAction k G X` and `Representation.ofMulAction k H X` on the
free `k`-module `k[X]` commute with each other. For the left and right multiplication actions of
a group `G`, that is, commuting actions of `G` and `Gᵐᵒᵖ`, this makes `k[X]` a `k[G]`-bimodule.
On `k[G]` itself, the left regular representation `Representation.ofMulAction k G G` is left
multiplication by the monomials `single g 1`. Its equivariant endomorphism corresponding to
`x : k[G]` under `Rep.leftRegularHomEquiv` is right multiplication by `x`.

When `G` and `H` are groups, `G` permutes the `H`-orbits, and the orbit sums of `k[X]` along the
`H`-orbits are equivariant: the sum of the coefficients of `g • v` along the `H`-orbit of `g • x`
is the sum of the coefficients of `v` along the `H`-orbit of `x`. Hence if `g` fixes
`∑ i ∈ s, h i • v` for a family `h : ι → H` and `#s` is cancellable in `k`, then the `H`-orbit
sums of `v` are invariant under `g`. The orbit sums of `v` are the finitely supported function
`v.coeff.mapDomain (Quotient.mk (MulAction.orbitRel H X))` on the orbit space.

For a finite group `G`, the coefficient of the norm `∑ g, g • v` at `x` is `∑ g, v(g • x)`. In
particular the norm of the basis vector at `x` has coefficient `|G_x|` at `x` and vanishes off the
orbit of `x`, while a vector fixed by `G` has constant coefficients along each orbit, so it is
determined by its coefficients at a set of orbit representatives. These are the inputs of the
computation of the low-degree Tate cohomology of `k[X]`.

Over a commutative ring `k`, the invariants of `k[X]` under a group `I` acting on a finite set `X`
are free on the orbit space `MulAction.orbitRel.Quotient I X`, with the orbit sums as basis. If `I`
is a normal subgroup of a group `D` acting on `X`, then `D ⧸ I` permutes the `I`-orbits, and the
orbit sums identify the permutation representation of `D ⧸ I` on the free module on the `I`-orbits
with the representation of `D ⧸ I` on the `I`-invariants of `k[X]` (Mathlib's
`Representation.quotientToInvariants`). In arithmetic applications `D` and `I` are a
decomposition group and its inertia subgroup, acting on the cosets of a subgroup of a finite
Galois group.

## Main results

* `TauCeti.commute_ofMulAction`: commuting actions on `X` give commuting permutation
  representations on `k[X]`.
* `Representation.ofMulAction_comp_subtype`: restricting a permutation representation to a
  subgroup gives the permutation representation of the subgroup.
* `TauCeti.single_mul_eq_smul_ofMulAction`: on `k[G]`, left multiplication by a monomial
  `single g c` is `c` times the left regular action of `g`.
* `Rep.leftRegularHomEquiv_symm_apply`: equivariant endomorphisms of the left regular
  representation are right multiplications.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction`: the orbit sums of `k[X]` are invariant
  under the permutation representation.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction_smul`: for commuting actions of `G` and `H`,
  the `H`-orbit sums of `g • v` at `g • x` are those of `v` at `x`.
* `TauCeti.mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum`: if `g` fixes
  `∑ i ∈ s, h i • v` and `#s` is cancellable, the `H`-orbit sums of `v` are `g`-invariant.
* `TauCeti.coeff_smul_of_forall_ofMulAction_eq`: a fixed vector of `k[X]` has the same coefficient
  at every point of an orbit.
* `TauCeti.eq_of_coeff_out_eq_of_forall_ofMulAction_eq`: two fixed vectors of `k[X]` agreeing at
  the chosen representative of every orbit are equal.
* `TauCeti.coeff_norm_ofMulAction`: the coefficients of the norm of a vector of `k[X]`.
* `TauCeti.coeff_norm_ofMulAction_single_self`,
  `TauCeti.coeff_norm_ofMulAction_single_of_notMem_orbit`: the norm of the basis vector at `x` has
  coefficient `|G_x|` at `x` and vanishes off the orbit of `x`.
* `TauCeti.mem_invariants_ofMulAction_iff`: a vector of `k[X]` is invariant exactly when its
  coefficients are constant along orbits.
* `TauCeti.invariantOrbitSumBasis`: the orbit-sum basis of the invariants of `k[X]`, indexed by
  the orbit space.
* `TauCeti.coeff_invariantOrbitSumBasis`, `TauCeti.invariantOrbitSumBasis_mk_eq_sum`: the basis
  vector at an orbit is the indicator of the orbit, the sum of the basis vectors at its points.
* `TauCeti.ofMulAction_invariantOrbitSumBasis_mk`: an element normalizing `I` sends the sum over
  the `I`-orbit of `x` to the sum over the `I`-orbit of its translate of `x`.
* `TauCeti.orbitSumEquiv`: for a normal subgroup `I`, the permutation representation of `D ⧸ I`
  on the `I`-orbits is equivalent to the representation of `D ⧸ I` on the `I`-invariants.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The right coset sums
  `⟨ξ, K⟩` of §3 Theorem 2(a) are the orbit sums for the right action of `PSL(2, ℤ)` on the
  integral matrices of positive determinant, which commutes with the left action.
-/

public section

namespace TauCeti

open _root_.Representation

variable {k G H X : Type*} [Semiring k] [Monoid G] [Monoid H] [MulAction G X] [MulAction H X]

/-- If the actions of `G` and `H` on `X` commute, then so do the permutation representations of
`G` and `H` on `k[X]`. -/
theorem commute_ofMulAction [SMulCommClass G H X] (g : G) (h : H) :
    Commute (ofMulAction k G X g) (ofMulAction k H X h) := by
  ext
  simp [smul_comm g h]

/-- On the monoid algebra `k[G]`, left multiplication by the monomial `single g c` is `c` times
the left regular representation of `g`. -/
theorem single_mul_eq_smul_ofMulAction (g : G) (c : k) (a : MonoidAlgebra k G) :
    MonoidAlgebra.single g c * a = c • ofMulAction k G G g a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, ha, hb, map_add, smul_add]
  | single g' c' => simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single]

/-- The permutation representation of a subgroup `H` on `k[X]` is the restriction of that of
`G`. -/
theorem _root_.Representation.ofMulAction_subgroup {G : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (h : H) : ofMulAction k H X h = ofMulAction k G X h := by
  ext
  simp [Subgroup.smul_def]

/-- Restricting the permutation representation of a group `G` on `k[X]` to a subgroup `S` gives
the permutation representation of `S` on `k[X]`. -/
@[simp]
theorem _root_.Representation.ofMulAction_comp_subtype {G : Type*} [Group G] [MulAction G X]
    (S : Subgroup G) : (ofMulAction k G X).comp S.subtype = ofMulAction k S X :=
  MonoidHom.ext fun s ↦ (ofMulAction_subgroup S s).symm

section LeftRegular

open scoped _root_.MonoidAlgebra

variable {k G : Type*} [CommRing k] [Monoid G]

/-- The endomorphism of the left regular representation `k[G]` corresponding to `x`
under `Rep.leftRegularHomEquiv` is right multiplication by `x`. -/
@[simp↓]
theorem _root_.Rep.leftRegularHomEquiv_symm_apply (x a : k[G]) :
    ((Rep.leftRegularHomEquiv (Rep.leftRegular k G)).symm x).hom a = a * x := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, Rep.leftRegularHomEquiv_symm_single,
      TauCeti.single_mul_eq_smul_ofMulAction, one_smul]
  | add a b ha hb => rw [map_add, ha, hb, add_mul]
  | smul c a ha => rw [map_smul, ha, smul_mul_assoc]

end LeftRegular

/-! ### Orbit sums -/

open _root_.MonoidAlgebra _root_.MulAction

/-- The orbit sums `k[X] → (X ⧸ G →₀ k)` are invariant under the permutation representation. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction {G : Type*} [Group G] [MulAction G X] (g : G)
    (v : k[X]) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel G X)) =
      v.coeff.mapDomain (Quotient.mk (orbitRel G X)) := by
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Quotient.sound (s := orbitRel G X) (mem_orbit y g)]

section Commuting

variable {G H : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [SMulCommClass G H X]

open scoped Finset

/-- **Equivariance of orbit sums.** If the actions of `G` and `H` on `X` commute, then the sum of
the coefficients of `g • v` along the `H`-orbit of `g • x` is the sum of the coefficients of `v`
along the `H`-orbit of `x`. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction_smul (g : G) (v : k[X]) (x : X) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  classical
  -- `g` maps distinct `H`-orbits to distinct `H`-orbits
  have hmk (y : X) : Quotient.mk (orbitRel H X) (g • y) = Quotient.mk _ (g • x) ↔
      Quotient.mk (orbitRel H X) y = Quotient.mk _ x := by
    simp [Quotient.eq, orbitRel_apply, mem_orbit_iff, ← smul_comm g]
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Finsupp.single_apply, hmk]

/-- If the actions of `G` and `H` on `X` commute, `h : ι → H`, `#s` is cancellable in `k` and
`g • w = w` for `w = ∑ i ∈ s, h i • v`, then the `H`-orbit sums of `v` are invariant under `g`:
the coefficients of `v` have the same sum along the `H`-orbits of `g • x` and of `x`. -/
theorem mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum {ι : Type*} {s : Finset ι} {h : ι → H}
    {g : G} {v : k[X]} (hs : IsSMulRegular k #s)
    (hfix : ofMulAction k G X g (∑ i ∈ s, ofMulAction k H X (h i) v) =
      ∑ i ∈ s, ofMulAction k H X (h i) v) (x : X) :
    v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  -- the `H`-orbit sums of `∑ i ∈ s, h i • v` are `#s` times those of `v`
  exact hs <| by simpa [hfix, Finsupp.mapDomain_finsetSum] using
    mapDomain_orbitRel_mk_coeff_ofMulAction_smul (H := H) g (∑ i ∈ s, ofMulAction k H X (h i) v) x

end Commuting

/-! ### Norms and invariant vectors -/

section Norm

variable {G : Type*} [Group G] [MulAction G X]

/-- A vector of `k[X]` fixed by the permutation representation has the same coefficient at every
point of an orbit. -/
theorem coeff_smul_of_forall_ofMulAction_eq {v : k[X]} (hv : ∀ g, ofMulAction k G X g v = v)
    (g : G) (x : X) : v.coeff (g • x) = v.coeff x := by
  conv_rhs => rw [← hv g⁻¹]
  rw [coeff_ofMulAction, inv_inv]

/-- Two vectors of `k[X]` fixed by the permutation representation are equal as soon as they agree
at the chosen representative of every orbit. -/
theorem eq_of_coeff_out_eq_of_forall_ofMulAction_eq {v w : k[X]}
    (hv : ∀ g, ofMulAction k G X g v = v) (hw : ∀ g, ofMulAction k G X g w = w)
    (h : ∀ ω : MulAction.orbitRel.Quotient G X, v.coeff ω.out = w.coeff ω.out) : v = w := by
  ext x
  obtain ⟨g, hg⟩ : ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G X) x).out :=
    Quotient.mk_out (s := MulAction.orbitRel G X) x
  rw [← coeff_smul_of_forall_ofMulAction_eq hv g, ← coeff_smul_of_forall_ofMulAction_eq hw g, hg,
    h]

variable [Fintype G]

/-- The coefficient of the norm `∑ g, g • v` of `v : k[X]` at `x` is the sum of the coefficients of
`v` at the points `g • x`. -/
@[simp]
theorem coeff_norm_ofMulAction (v : k[X]) (x : X) :
    ((ofMulAction k G X).norm v).coeff x = ∑ g : G, v.coeff (g • x) := by
  simp only [Representation.norm, LinearMap.sum_apply, coeff_sum, Finsupp.finsetSum_apply,
    coeff_ofMulAction]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ ↦ rfl

/-- The norm of `single x r` has coefficient `|G_x| • r` at `x`, where `G_x` is the stabilizer
of `x`. -/
theorem coeff_norm_ofMulAction_single_self (x : X) (r : k) :
    ((ofMulAction k G X).norm (single x r)).coeff x = Nat.card (stabilizer G x) • r := by
  classical
  simp only [coeff_norm_ofMulAction, coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 2
  ext g
  simp [eq_comm]

/-- The norm of `single x r` vanishes off the orbit of `x`. -/
theorem coeff_norm_ofMulAction_single_of_notMem_orbit {x y : X} (h : y ∉ orbit G x) (r : k) :
    ((ofMulAction k G X).norm (single x r)).coeff y = 0 := by
  classical
  refine (coeff_norm_ofMulAction _ _).trans (Finset.sum_eq_zero fun g _ ↦ ?_)
  rw [coeff_single, Finsupp.single_apply, ite_eq_right_iff]
  rintro rfl
  exact absurd ⟨g⁻¹, inv_smul_smul g y⟩ h

end Norm

end TauCeti

/-! ### The orbit-sum basis of the invariants -/

namespace TauCeti

open _root_.MonoidAlgebra _root_.MulAction _root_.Representation

section OrbitSumBasis

variable {k I X : Type*} [CommRing k] [Group I] [MulAction I X]

/-- A vector of `k[X]` is invariant under the permutation representation exactly when its
coefficients are constant along the orbits. -/
theorem mem_invariants_ofMulAction_iff {v : k[X]} :
    v ∈ (ofMulAction k I X).invariants ↔ ∀ (g : I) (x : X), v.coeff (g • x) = v.coeff x := by
  refine ⟨fun hv ↦ coeff_smul_of_forall_ofMulAction_eq hv, fun hv g ↦ ?_⟩
  ext x
  rw [coeff_ofMulAction, hv]

variable (k I X) [Finite X]

/-- The coefficients of an invariant vector of `k[X]`, as a function on the orbit space; the
inverse sends a function on the orbit space to the vector with that coefficient at each point of
the corresponding orbit. -/
private noncomputable def invariantsEquivFun :
    (ofMulAction k I X).invariants ≃ₗ[k] (orbitRel.Quotient I X → k) where
  toFun v ω := Quotient.liftOn' ω (v : k[X]).coeff fun _ _ ⟨g, hg⟩ ↦ by
    rw [← hg]
    exact coeff_smul_of_forall_ofMulAction_eq v.2 g _
  map_add' v w := funext fun ω ↦ Quotient.inductionOn' ω fun _ ↦ rfl
  map_smul' r v := funext fun ω ↦ Quotient.inductionOn' ω fun _ ↦ rfl
  invFun c := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ c ⟦x⟧),
    (mem_invariants_ofMulAction_iff).2 fun g x ↦ by simp⟩
  left_inv v := Subtype.ext <| by ext x; simp [Quotient.liftOn'_mk'']
  right_inv c := funext fun ω ↦ Quotient.inductionOn' ω fun x ↦ by simp [Quotient.liftOn'_mk'']

/-- **The orbit-sum basis.** For a group `I` acting on a finite set `X`, the invariants of the
permutation representation `k[X]` are free on the orbit space: the basis vector at an orbit `ω`
is the orbit sum `∑ x ∈ ω, x` (`TauCeti.invariantOrbitSumBasis_mk_eq_sum`). -/
noncomputable def invariantOrbitSumBasis :
    Module.Basis (orbitRel.Quotient I X) k (ofMulAction k I X).invariants :=
  .ofEquivFun (invariantsEquivFun k I X)

variable {k I X}

/-- The coordinate of an invariant vector at the orbit of `x` is its coefficient at `x`. -/
@[simp]
theorem invariantOrbitSumBasis_repr_mk (v : (ofMulAction k I X).invariants) (x : X) :
    (invariantOrbitSumBasis k I X).repr v ⟦x⟧ = (v : k[X]).coeff x := by
  simp [invariantOrbitSumBasis, invariantsEquivFun, Quotient.liftOn'_mk'']

/-- The basis vector at an orbit `ω` is the indicator function of `ω`. -/
@[simp]
theorem coeff_invariantOrbitSumBasis (ω : orbitRel.Quotient I X) (x : X) :
    (invariantOrbitSumBasis k I X ω : k[X]).coeff x = ω.orbit.indicator 1 x := by
  classical
  simp [invariantOrbitSumBasis, invariantsEquivFun, Set.indicator_apply, Pi.single_apply,
    orbitRel.Quotient.mem_orbit]

/-- The vector with coordinates `c` in the orbit-sum basis has coefficient `c ⟦x⟧` at `x`. -/
@[simp]
theorem coeff_invariantOrbitSumBasis_equivFun_symm (c : orbitRel.Quotient I X → k) (x : X) :
    (((invariantOrbitSumBasis k I X).equivFun.symm c : _) : k[X]).coeff x = c ⟦x⟧ := by
  rw [← invariantOrbitSumBasis_repr_mk, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]

/-- The basis vector at the orbit of `x` is the sum of the basis vectors of `k[X]` at the points
of the orbit of `x`. -/
theorem invariantOrbitSumBasis_mk_eq_sum (x : X) [Fintype (orbit I x)] :
    (invariantOrbitSumBasis k I X ⟦x⟧ : k[X]) = ∑ y ∈ (orbit I x).toFinset, single y 1 := by
  classical
  ext y
  simp [coeff_invariantOrbitSumBasis, Set.indicator_apply, coeff_sum, Finsupp.finsetSum_apply,
    coeff_single, Finsupp.single_apply]

end OrbitSumBasis

/-! ### Equivariance of orbit sums under a normal subgroup -/

section Equivariance

variable (k : Type*) {D X : Type*} [CommRing k] [Group D] [MulAction D X] [Finite X]
  (I : Subgroup D)

variable {I} in
/-- **Orbit sums are equivariant.** An element `d` normalizing `I` sends the sum over the
`I`-orbit of `x` to the sum over the `I`-orbit of `d • x`. -/
theorem ofMulAction_invariantOrbitSumBasis_mk {d : D} (hd : d ∈ Subgroup.normalizer (I : Set D))
    (x : X) :
    ofMulAction k D X d (invariantOrbitSumBasis k I X ⟦x⟧) =
      invariantOrbitSumBasis k I X ⟦d • x⟧ := by
  ext y
  rw [coeff_ofMulAction, coeff_invariantOrbitSumBasis, coeff_invariantOrbitSumBasis]
  -- `d` permutes the `I`-orbits, sending the orbit of `d⁻¹ • y` to the orbit of `y`
  have h : (Quotient.mk'' (d⁻¹ • y) : orbitRel.Quotient I X) = ⟦x⟧ ↔
      (Quotient.mk'' y : orbitRel.Quotient I X) = ⟦d • x⟧ := by
    rw [← (MulAction.normalizerOrbitRelQuotientEquiv I ⟨d, hd⟩).apply_eq_iff_eq,
      MulAction.normalizerOrbitRelQuotientEquiv_apply,
      MulAction.normalizerOrbitRelQuotientEquiv_apply, smul_inv_smul]
  classical
  simp only [Set.indicator_apply, orbitRel.Quotient.mem_orbit, h, Pi.one_apply]

variable (X)

omit [Finite X] in
/-- The invariants of `k[X]` under the subgroup `I`, read through the permutation representation
of the ambient group, are those of the permutation representation of `I`. -/
theorem invariants_ofMulAction_comp_subtype :
    invariants ((ofMulAction k D X).comp I.subtype) = (ofMulAction k I X).invariants := by
  ext v
  simp [ofMulAction_subgroup]

/-- The linear isomorphism underlying `TauCeti.orbitSumEquiv`. -/
private noncomputable def orbitSumLinearEquiv :
    k[orbitRel.Quotient I X] ≃ₗ[k] invariants ((ofMulAction k D X).comp I.subtype) :=
  (MonoidAlgebra.basis _ k).equiv ((invariantOrbitSumBasis k I X).map
    (LinearEquiv.ofEq _ _ (invariants_ofMulAction_comp_subtype k X I).symm)) (.refl _)

private theorem coe_orbitSumLinearEquiv_single (ω : orbitRel.Quotient I X) :
    (orbitSumLinearEquiv k X I (single ω 1) : k[X]) = invariantOrbitSumBasis k I X ω := by
  simp [orbitSumLinearEquiv, ← MonoidAlgebra.basis_apply]

variable [I.Normal]

/-- **The orbit-sum equivalence.** For a normal subgroup `I`, the orbit sums identify the
permutation representation of `D ⧸ I` on the `I`-orbits with the representation of `D ⧸ I` on the
`I`-invariants of `k[X]`: the basis vector at an orbit goes to the sum over that orbit. -/
noncomputable def orbitSumEquiv :
    (ofMulAction k (D ⧸ I) (orbitRel.Quotient I X)).Equiv
      ((ofMulAction k D X).quotientToInvariants I) :=
  .mk (orbitSumLinearEquiv k X I) fun σ ↦ by
    induction σ using QuotientGroup.induction_on with | H d => ?_
    refine MonoidAlgebra.lhom_ext' fun ω ↦ LinearMap.ext_ring <| Subtype.ext ?_
    induction ω using Quotient.inductionOn with | h x => ?_
    simp [ofQuotient_coe_apply, coe_orbitSumLinearEquiv_single,
      ofMulAction_invariantOrbitSumBasis_mk k
        (by simp [Subgroup.normalizer_eq_top] : d ∈ Subgroup.normalizer (I : Set D))]

variable {k X I}

/-- The orbit-sum equivalence sends `r` times the basis vector at an orbit to `r` times the sum
over that orbit. -/
@[simp]
theorem coe_orbitSumEquiv_single (ω : orbitRel.Quotient I X) (r : k) :
    (orbitSumEquiv k X I (single ω r) : k[X]) = r • (invariantOrbitSumBasis k I X ω : k[X]) := by
  have hr : single ω r = r • single ω (1 : k) := by simp
  rw [hr, map_smul, Submodule.coe_smul]
  exact congrArg (r • ·) (coe_orbitSumLinearEquiv_single k X I ω)

/-- The coefficient of the image of `v` under the orbit-sum equivalence at `x` is the coefficient
of `v` at the orbit of `x`. -/
@[simp]
theorem coeff_orbitSumEquiv (v : k[orbitRel.Quotient I X]) (x : X) :
    ((orbitSumEquiv k X I v : _) : k[X]).coeff x = v.coeff ⟦x⟧ := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single ω r =>
    classical
    simp [coeff_single, Finsupp.single_apply, Set.indicator_apply,
      orbitRel.Quotient.mem_orbit, eq_comm]

/-- The coefficient of the preimage of `w` under the orbit-sum equivalence at the orbit of `x` is
the coefficient of `w` at `x`. -/
@[simp]
theorem coeff_orbitSumEquiv_symm (w : invariants ((ofMulAction k D X).comp I.subtype)) (x : X) :
    ((orbitSumEquiv k X I).symm w).coeff ⟦x⟧ = (w : k[X]).coeff x := by
  conv_rhs => rw [← (orbitSumEquiv k X I).apply_symm_apply w]
  rw [coeff_orbitSumEquiv]

end Equivariance

end TauCeti
end
end TAF_LiteralSource_0161

section TAF_LiteralSource_0162
/- Original module: TauCeti.GroupTheory.GroupAction.PiTransport -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Group actions that transport the factors of a product

Let a group `G` act on a type `X` that decomposes as a product `∏_{i : ι} M i`, with the indices
lying over a `G`-set `P` along `p : ι → P`, and suppose `g` carries the factor at `i` to the
factor at `j` along a bijection `T g : M i ≃ M j` whenever `p j = g • p i`. The action on `X`
need not be a `MulAction`: it is only required to be compatible with `T`. If every index is
carried to a fixed index `w`, an element of `X` is determined by the components at `w` of its
translates (`Equiv.eq_of_forall_transport_component_eq`); this needs only a scalar action
`SMul G P`. If moreover every element of `G` carries some index to `w`, every function `G → M w`
that is equivariant for the stabilizer of `p w` arises in this way
(`Equiv.exists_forall_transport_component_eq`).

The motivating example is the Galois group of `L/K` acting on the semi-local algebra
`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`, permuting the places above `v`. These two results are the
injectivity and surjectivity of the map into the representation coinduced from a decomposition
group, `TauCeti.resCoindToHom_bijective_of_transport`.

## Main results

* `Equiv.eq_of_forall_transport_component_eq`,
  `Equiv.exists_forall_transport_component_eq`: injectivity and surjectivity of the map
  `x ↦ (g ↦ (g • x)_w)` into the stabilizer-equivariant functions.
-/

public section

namespace Equiv

variable {G P ι X : Type*} {p : ι → P} {act : G → X → X} {M : ι → Type*} (e : X ≃ ∀ i, M i)
  {w : ι}

section SMul

variable [SMul G P] (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j)
  (he : ∀ (g : G) (x : X) {i j : ι} (h : p j = g • p i), e (act g x) j = T g h (e x i))

include he in
/-- If `G` carries every factor to the factor at `w`, an element of `X` is determined by the
components at `w` of its translates. -/
theorem eq_of_forall_transport_component_eq (htrans : ∀ i, ∃ g : G, p w = g • p i) {x x' : X}
    (h : ∀ g, e (act g x) w = e (act g x') w) : x = x' :=
  e.injective <| funext fun i ↦ by
    obtain ⟨g, hg⟩ := htrans i
    simpa only [he g _ hg, (T g hg).apply_eq_iff_eq] using h g

end SMul

section Group

variable [Group G] [MulAction G P] (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j)
  (he : ∀ (g : G) (x : X) {i j : ι} (h : p j = g • p i), e (act g x) j = T g h (e x i))

include he in
/-- If `G` carries every factor to the factor at `w`, every element of `G` carries some factor
to it, and the transport maps compose, then every function `G → M w` that is equivariant for the
stabilizer of `p w` is `g ↦ (g • x)_w` for some `x : X`. -/
theorem exists_forall_transport_component_eq
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i)
    (f : G → M w) (hf : ∀ (d : G) (hd : p w = d • p w) (g : G), f (d * g) = T d hd (f g)) :
    ∃ x : X, ∀ g, e (act g x) w = f g := by
  choose g hg using htrans
  -- the component at `i` is the value of `f` at an element `g i` carrying `i` to `w`,
  -- transported back to `M i`; equivariance of `f` for the stabilizer of `p w` makes the
  -- result independent of the choice of `g i`
  refine ⟨e.symm fun i ↦ (T (g i) (hg i)).symm (f (g i)), fun σ ↦ ?_⟩
  obtain ⟨i, hi⟩ := hsurj σ
  have hd : p w = (σ * (g i)⁻¹) • p w := by rw [mul_smul, inv_smul_eq_iff.mpr (hg i), ← hi]
  rw [he σ _ hi, e.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply, ← hf, inv_mul_cancel_right] using
    (hT (g i) (σ * (g i)⁻¹) (hg i) hd ((T (g i) (hg i)).symm (f (g i)))).symm

end Group

end Equiv
end
end TAF_LiteralSource_0162

section TAF_LiteralSource_0163
/- Original module: TauCeti.RepresentationTheory.Coinduced -/
/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/


/-!
# Coinduction: exactness and coextension of scalars

Coinduction along a subgroup preserves short exact sequences of representations. Unlike
coinduction along an arbitrary homomorphism, subgroup coinduction preserves epimorphisms;
together with its right adjoint structure this gives exactness, without a finite-index
assumption. This allows connecting maps to be compared through Shapiro's isomorphism.

On the module side, coinduction along a monoid homomorphism `φ : H →* G` is coextension of
scalars along `MonoidAlgebra.mapDomainRingHom k φ : k[H] →+* k[G]`: the `k[G]`-module
`Hom_{k[H]}(k[G], V)` of Mathlib's `ModuleCat.coextendScalars` is isomorphic to the module of
Mathlib's coinduced representation `Representation.coind φ ρ`, by evaluation at the
monoid elements (`Representation.coextendScalarsEquivCoind`). This transports statements about
coextension of scalars on module categories, such as its action on Grothendieck groups of group
algebras, to coinduced and induced representations.

If a representation `B` of `G` decomposes as a product whose factors `G` permutes transitively,
the map from `B` to the representation coinduced from the stabilizer of one factor, adjoint to the
projection to that factor, is bijective (`TauCeti.resCoindToHom_bijective_of_transport`). This
identifies the units of a semi-local algebra `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` with a representation
coinduced from a decomposition group.

Mathlib's coinduced action is evaluated by `Representation.coind_apply_coe_apply`:
`(h • f) h₁ = f (h₁ * h)`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6 and §9.
-/

public section

open CategoryTheory

namespace Rep

universe u v w t

variable {R : Type u} [CommRing R]

/-- Coinduction acts additively on coefficient maps. -/
instance {G : Type v} {H : Type w} [Monoid G] [Monoid H] (φ : H →* G) :
    (coindFunctor.{t} R φ).Additive where
  map_add := by intro X Y f g; ext x; rfl

/-- The counit of restriction–coinduction along a monoid homomorphism evaluates at `1`. -/
theorem resCoindAdjunction_counit_app_hom_apply
    {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Monoid G] [Monoid H]
    (φ : G →* H) (A : Rep.{max w t} k G) (f : Rep.coind φ A) :
    ((Rep.resCoindAdjunction.{t} k φ).counit.app A).hom f = f.1 1 :=
  rfl

variable {G : Type v} [Group G]

/-- Subgroup coinduction preserves homology of short complexes of representations. -/
noncomputable instance (H : Subgroup G) :
    (coindFunctor.{max v t} R H.subtype).PreservesHomology :=
  (coindFunctor.{max v t} R H.subtype).preservesHomology_of_preservesEpis_and_kernels

/-- Subgroup coinduction is exact, so also preserves finite colimits. -/
instance (H : Subgroup G) :
    Limits.PreservesFiniteColimits (coindFunctor.{max v t} R H.subtype) :=
  (coindFunctor.{max v t} R H.subtype).preservesFiniteColimits_of_preservesHomology

end Rep

namespace Representation

section Apply

variable {k G H V : Type*} [Semiring k] [Monoid G] [Monoid H] [AddCommMonoid V] [Module k V]

-- Not `@[simp]`: simp first unfolds the action `coind φ ρ h` through `Representation.coind_apply`,
-- so the left-hand side is not in simp-normal form (`simpNF`).
/-- The coinduced action translates the argument of a function: `(h • f) h₁ = f (h₁ * h)`. -/
theorem coind_apply_coe_apply (φ : G →* H) (ρ : Representation k G V) (f : coindV φ ρ)
    (h h₁ : H) : ((coind φ ρ h) f).1 h₁ = f.1 (h₁ * h) :=
  rfl

end Apply

open scoped MonoidAlgebra

universe u v w

-- The carrier `V` lives in `Type (max u v)`, the universe of `k[G]`, as Mathlib's `Rep.coindIso`
-- requires.
variable {k : Type u} {H : Type w} {G : Type v} [CommRing k] [Monoid H] [Monoid G] (φ : H →* G)
  {V : Type (max u v)} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

-- The explicit source type selects the restricted `k[H]`-action, so `x` is `k[H]`-linear.
private theorem coextendScalars_apply_mapDomain_mul
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (r : k[H]) (a : k[G]) :
    ρ.asModuleEquiv (x (MonoidAlgebra.mapDomainRingHom k φ r * a)) =
      ρ.asAlgebraHom r (ρ.asModuleEquiv (x a)) :=
  congrArg ρ.asModuleEquiv (map_smul (ModuleCat.CoextendScalars.equiv _ _ x) r
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a))

/-- `k[G]` acts on the coinduced representation `Representation.coind' φ A`, whose elements are
the morphisms `Rep.res φ (Rep.leftRegular k G) ⟶ A`, by right multiplication on the source
`k[G]`. -/
@[simp↓]
theorem coind'_asAlgebraHom_hom_apply (A : Rep k H) (r : k[G])
    (f : Rep.res φ (Rep.leftRegular k G) ⟶ A) (a : k[G]) :
    ((coind' φ A).asAlgebraHom r f).hom a = f.hom (a * r) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, asAlgebraHom_single_one, coind'_apply_apply,
      Rep.hom_comp, IntertwiningMap.comp_apply]
    apply congrArg f.hom
    rw [← IntertwiningMap.toLinearMap_apply, Rep.resMap_hom_toLinearMap,
      IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe,
      Rep.leftRegularHomEquiv_symm_apply]
  | add r r' hr hr' => simp [Rep.add_hom, hr, hr', mul_add]
  | smul c r hr =>
    simp only [map_smul, LinearMap.smul_apply, Rep.smul_hom, IntertwiningMap.coe_smul,
      Pi.smul_apply, mul_smul_comm, hr]

/-- A `k[H]`-linear map `k[G] → V` is an `H`-equivariant `k`-linear map from the restriction of
the left regular representation of `G`. -/
private noncomputable def coextendScalarsEquivCoind' :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (Rep.coind' φ (Rep.of ρ)).ρ.asModule where
  toFun x := Rep.ofHom
    { toFun a := ρ.asModuleEquiv (x a)
      map_add' a b := congrArg ρ.asModuleEquiv (map_add (ModuleCat.CoextendScalars.equiv _ _ x)
        (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
          (ModuleCat.of k[G] k[G])) from a) b)
      map_smul' c a := by
        -- `k`-linearity is `k[H]`-linearity at the scalars `single 1 c`.
        have : c • a = MonoidAlgebra.mapDomainRingHom k φ (.single 1 c) * a := by
          ext; simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_single_one_mul]
        rw [this, coextendScalars_apply_mapDomain_mul, asAlgebraHom_single, map_one]
        rfl
      isIntertwining' h := LinearMap.ext fun a ↦ by
        have := coextendScalars_apply_mapDomain_mul φ ρ x (.single h 1) a
        rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
          TauCeti.single_mul_eq_smul_ofMulAction, one_smul, asAlgebraHom_single_one] at this
        exact this }
  invFun f := (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun a := ρ.asModuleEquiv.symm (f.hom a)
      map_add' := map_add f.hom.toLinearMap
      map_smul' r a := by
        -- `r : k[H]` acts on the source `k[G]` through `mapDomainRingHom k φ`, and on the target
        -- through `ρ.asAlgebraHom`.
        change f.hom (MonoidAlgebra.mapDomainRingHom k φ r * show k[G] from a) =
          ρ.asAlgebraHom r (f.hom a)
        induction r using MonoidAlgebra.induction_linear with
        | zero => rw [map_zero, zero_mul, map_zero, map_zero, LinearMap.zero_apply]
        | add r r' hr hr' => rw [map_add, add_mul, map_add, hr, hr', map_add, LinearMap.add_apply]
        | single h c =>
          rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
            TauCeti.single_mul_eq_smul_ofMulAction, map_smul, asAlgebraHom_single]
          exact congrArg (fun v : V => c • v) (Rep.hom_comm_apply f h a) }
  map_add' x y := rfl
  map_smul' r x := Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun a ↦ by
    -- `r • f` in the module of `coind'` is `(coind' φ _).asAlgebraHom r f`.
    change _ = ((coind' φ (Rep.of ρ)).asAlgebraHom r _).hom a
    rw [coind'_asAlgebraHom_hom_apply]
    rfl
  left_inv x := rfl
  right_inv f := rfl

/-- **Coinduction is coextension of scalars.** For a monoid homomorphism `φ : H →* G` and a
representation `ρ` of `H` on `V`, the `k[G]`-module `Hom_{k[H]}(k[G], V)`, with `k[H]` acting on
`k[G]` through `φ`, is isomorphic to the module of Mathlib's coinduced representation
`Representation.coind φ ρ`: a homomorphism `x` corresponds to the function `g ↦ x (single g 1)`.
It is Mathlib's `Rep.coindIso` read through the identification of `k[H]`-linear maps
`k[G] → V` with the morphisms of `Rep.coind' φ`. -/
noncomputable def coextendScalarsEquivCoind :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (coind φ ρ).asModule :=
  (coextendScalarsEquivCoind' φ ρ).trans
    (TauCeti.Representation.asModuleLinearEquivOfEquiv
      (equivOfIso (Rep.coindIso φ (Rep.of ρ)).symm))

/-- `Representation.coextendScalarsEquivCoind` evaluates a homomorphism at the monoid elements. -/
@[simp]
theorem coextendScalarsEquivCoind_apply
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (g : G) :
    Subtype.val (p := (· ∈ coindV φ ρ)) (coextendScalarsEquivCoind φ ρ x) g =
      (x (.single g 1) : V) := by
  rw [coextendScalarsEquivCoind, LinearEquiv.trans_apply,
    TauCeti.Representation.asModuleLinearEquivOfEquiv_apply]
  rfl

/-- The inverse of `Representation.coextendScalarsEquivCoind` sends a coinduced function `y` to
the homomorphism taking the value `y g` at `single g 1`. -/
@[simp]
theorem coextendScalarsEquivCoind_symm_apply_single (y : (coind φ ρ).asModule) (g : G) :
    ((coextendScalarsEquivCoind φ ρ).symm y (.single g 1) : V) =
      Subtype.val (p := (· ∈ coindV φ ρ)) y g := by
  conv_rhs => rw [← (coextendScalarsEquivCoind φ ρ).apply_symm_apply y]
  rw [coextendScalarsEquivCoind_apply]

end Representation

namespace TauCeti

variable {G P ι : Type*} [Group G] [MulAction G P] {p : ι → P} {M : ι → Type*}
  (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j) {w : ι}

/-- **Coinduction from a stabilizer.** Let `B` be a representation of `G` that decomposes as a
product `∏_{i : ι} M i` on which `g` carries the factor at `i` to the factor at `j` along
`T g : M i ≃ M j` whenever `p j = g • p i`, and let `A` be a representation of the stabilizer of
`p w` whose underlying type is identified with `M w`, the action of the stabilizer being given by
`T`. If `G` permutes the factors transitively, every element of `G` carries some factor to `w`,
and the transport maps compose, then the map `B ⟶ Coind A` adjoint to the projection
`f : B ⟶ A` to the factor at `w` is bijective. -/
theorem resCoindToHom_bijective_of_transport {k : Type*} [CommRing k] {B : Rep k G}
    {A : Rep k (MulAction.stabilizer G (p w))}
    (f : Rep.res (MulAction.stabilizer G (p w)).subtype B ⟶ A) (e : B ≃ ∀ i, M i)
    (he : ∀ (g : G) (x : B) {i j : ι} (h : p j = g • p i), e (B.ρ g x) j = T g h (e x i))
    (eA : A ≃ M w) (hf : ∀ x, eA (f.hom x) = e x w)
    (hA : ∀ (d : MulAction.stabilizer G (p w)) (a : A),
      eA (A.ρ d a) = T d (MulAction.mem_stabilizer_iff.mp d.2).symm (eA a))
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i) :
    Function.Bijective (Rep.resCoindToHom _ B A f).hom := by
  refine ⟨fun x x' h ↦ e.eq_of_forall_transport_component_eq T he htrans fun g ↦ ?_,
    fun F ↦ ?_⟩
  · rw [← hf, ← hf]
    exact congrArg (fun F ↦ eA (F.1 g)) h
  obtain ⟨x, hx⟩ := e.exists_forall_transport_component_eq T he hT htrans hsurj
    (fun g ↦ eA (F.1 g)) fun d hd g ↦ by
      have hF := F.2 ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩ g
      simp only [Subgroup.subtype_apply] at hF
      rw [hF, hA]
  exact ⟨x, Subtype.ext <| funext fun g ↦ eA.injective <| (hf _).trans (hx g)⟩

end TauCeti
end
end TAF_LiteralSource_0163

section TAF_LiteralSource_0164
/- Original module: TauCeti.RepresentationTheory.Induction.Transitivity -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Transitivity of induction and coinduction

This file records restriction and coinduction in stages for representations along composable monoid
homomorphisms, and induction in stages along composable group homomorphisms. It obtains the natural
isomorphisms from the equality of restriction functors `MonoidHom.resFunctor_comp` and
Mathlib's induction--restriction and restriction--coinduction adjunctions. This is the categorical
core used by the subgroup form of induction.

Uniqueness of adjoints produces those isomorphisms without ever saying what they *do*, and a
comparison map known only up to an abstract adjoint characterisation is of no use to a computation
with induced characters or with the Mackey decomposition, both of which have to follow a chosen
coset representative through the isomorphism. The second half of this file therefore evaluates them
on representatives:

`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ ↦ ⟦ψ(h) κ ⊗ₜ a⟧`,  `⟦κ ⊗ₜ a⟧ ↦ ⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`

for induction, and dually `F ↦ (κ ↦ F κ 1)`, `f ↦ (κ ↦ (h ↦ f (ψ(h) κ)))` for coinduction.

The route to these formulas is the mates calculus rather than an unfolding of
`Adjunction.leftAdjointCompIso`. The identity `CategoryTheory.unit_conjugateEquiv` says that
conjugate natural transformations agree after composing with the two units; since the unit of the
induction--restriction adjunction is the generator map `a ↦ ⟦1 ⊗ₜ a⟧` and `resFunctorCompIso` is
the identity on vectors, that identity computes the *inverse* isomorphism
`(indFunctorCompIso φ ψ).inv` on the generator `⟦1 ⊗ₜ a⟧` of the singly induced representation,
which is where both units land. Equivariance then spreads that single value over all group
coordinates, giving the inverse on every generator, and the forward formula follows by inverting
it. Both steps use the relation `⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` inside the coinvariants
(`TauCeti.indV_mk_ind_mk`), which also says that the elements with inner coordinate `1`
generate, so that the formula determines the map. The coinduction side is the same argument run
through `CategoryTheory.conjugateEquiv_counit_symm` and the counit, which is evaluation at `1`;
there it is the forward isomorphism that the counits compute, and the inverse that is derived.

## Main definitions

* `TauCeti.Rep.resFunctorCompIso`, `TauCeti.Rep.indFunctorCompIso`,
  `TauCeti.Rep.coindFunctorCompIso`: restriction, induction and coinduction in stages, as natural
  isomorphisms of functors.
* `TauCeti.Rep.indFunctorMulEquivIso`: induction along a group isomorphism is restriction along
  its inverse.
* `TauCeti.Rep.indFunctorSubgroupOfIso`: induction in stages through an intermediate subgroup
  `S ≤ T ≤ G`, with `S` identified with the subgroup `S.subgroupOf T` of `T`.

## Main statements

* `TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk` and
  `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`: **induction in stages on representatives**,
  the two directions of the isomorphism computed on the generators of the induced representation.
* `TauCeti.Rep.eq_indFunctorCompIso_hom_app`: those formulas pin the isomorphism down. A morphism
  of representations sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to `⟦1 ⊗ₜ a⟧` for every `a : A` *is* the
  induction-in-stages isomorphism, which is how a comparison map built by hand is identified with
  the adjoint one.
* `TauCeti.Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply` and
  `TauCeti.Rep.coindFunctorCompIso_inv_app_hom_apply_coe_apply_coe_apply`: **coinduction in stages
  on functions**, the dual formulas.
* `TauCeti.indV_mk_apply_inv`, `TauCeti.indV_mk_ind_mk` and `TauCeti.indV_ind_hom_ext`: the
  coinvariants relation moving the group action of an induced representation into its group
  coordinate, its form for a twice-induced representation, and the resulting extensionality
  principle.
* `TauCeti.Rep.ind_hom_apply_mk` and `TauCeti.Rep.ind_ind_hom_ext`: a morphism out of an induced
  representation is the translate of its value at the group coordinate `1`, so two morphisms out of
  a twice-induced representation already agree once they agree on `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`.

## Implementation notes

The four representative formulas are tagged with the pre-order `@[simp↓]` rather than `@[simp]`,
like `TauCeti.Rep.resFunctorCompIso_hom_app_apply` above them. Their left-hand sides are readable
but not in post-order `simp`-normal form: on the induction side `Representation.IndV.mk φ ρ h` is a
reducible abbreviation that `simp` unfolds to `Representation.Coinvariants.mk _ (single h 1 ⊗ₜ a)`,
and on the coinduction side `simp` rewrites the source and target of
`(coindFunctorCompIso φ ψ).hom.app A`, which appear as implicit arguments, with
`CategoryTheory.Functor.comp_obj` and `Rep.coindFunctor_obj`. A plain `@[simp]` tag is therefore
rejected by the `simpNF` linter and would never fire, and restating the formulas in the linter's
normal form is not a way out: that form pairs rewritten implicit type arguments with an unrewritten
`Representation.IntertwiningMap.instFunLike` instance argument, which no surface syntax elaborates
to. `@[simp↓]` fires the lemma before those subterms are normalised, so `simp` closes goals stated
in the readable form, and `rw` and `exact` still apply the lemmas as usual.

## References

C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §10, and J.-P. Serre,
*Linear Representations of Finite Groups*, §7.
-/

public section

namespace TauCeti

open CategoryTheory

universe t u v w x y z

variable {k : Type u} {G : Type v} {H : Type w} {K : Type x}

/-! ### Generators of induced and coinduced representations

The lemmas of this section speak only about `Representation.IndV` and `Representation.coindV` and
mention no object of `Rep`, so they are not declared in the `Rep` namespace. They also stay out of a
`Representation` namespace: `scripts/lint-dot-notation.py` rejects a Mathlib type namespace nested
inside `TauCeti`, because the resulting name would not give dot notation on `Representation`. -/

section IndV

variable [CommRing k] [Group G] [Group H] [Group K]

/-- Moving the group action out of an induced representation into its group coordinate:
`⟦κ ⊗ₜ τ h⁻¹ y⟧ = ⟦ψ(h) κ ⊗ₜ y⟧`. This is `Representation.Coinvariants.mk_tmul_inv` for the
tensor product defining `Representation.IndV`. -/
lemma indV_mk_apply_inv {W : Type*} [AddCommGroup W] [Module k W] (ψ : H →* K)
    (τ : Representation k H W) (h : H) (κ : K) (y : W) :
    Representation.IndV.mk ψ τ κ (τ h⁻¹ y) = Representation.IndV.mk ψ τ (ψ h * κ) y := by
  -- `Representation.Coinvariants.mk_tmul_inv` is the `simp` lemma doing the work; the extra
  -- rewrite evaluates the left regular representation on the group coordinate.
  simp [Representation.ofMulAction_single]

/-- Moving the inner group coordinate of a twice-induced representation out to the outer one:
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Every element of `Ind_ψ (Ind_φ A)` is therefore a sum of
elements whose inner coordinate is `1`, which is what makes the two representative formulas below
determine the induction-in-stages isomorphism. -/
lemma indV_mk_ind_mk {V : Type*} [AddCommGroup V] [Module k V] (φ : G →* H) (ψ : H →* K)
    (ρ : Representation k G V) (h : H) (κ : K) (a : V) :
    Representation.IndV.mk ψ (Representation.ind φ ρ) κ (Representation.IndV.mk φ ρ h a) =
      Representation.IndV.mk ψ (Representation.ind φ ρ) (ψ h * κ)
        (Representation.IndV.mk φ ρ 1 a) := by
  rw [← indV_mk_apply_inv ψ (Representation.ind φ ρ) h κ, Representation.ind_mk, inv_inv, one_mul]

/-- Two linear maps out of a twice-induced representation agree as soon as they agree on the
elements `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` whose inner group coordinate is `1`. -/
lemma indV_ind_hom_ext {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : G →* H) (ψ : H →* K) (ρ : Representation k G V)
    {f g : Representation.IndV ψ (Representation.ind φ ρ) →ₗ[k] W}
    (hfg : ∀ (κ : K) (a : V),
      f (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ 1 a)) =
        g (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ 1 a))) :
    f = g := by
  have key : ∀ (κ : K) (h : H) (a : V),
      f (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ h a)) =
        g (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ h a)) := fun κ h a => by
    rw [indV_mk_ind_mk φ ψ ρ h κ a]
    exact hfg _ a
  exact Representation.IndV.hom_ext ψ _ fun κ =>
    Representation.IndV.hom_ext φ _ fun h => LinearMap.ext fun a => key κ h a

end IndV

section Restriction

variable [Semiring k] [Monoid G] [Monoid H] [Monoid K]

/-- Restriction along two composable group homomorphisms is naturally isomorphic to restriction
along their composite.  The two functors are in fact equal (`MonoidHom.resFunctor_comp`), so this is
that equality read as an isomorphism. -/
def Rep.resFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    Rep.resFunctor.{max u v w x} (k := k) ψ ⋙
      Rep.resFunctor.{max u v w x} (k := k) φ ≅
        Rep.resFunctor.{max u v w x} (k := k) (ψ.comp φ) :=
  eqToIso (MonoidHom.resFunctor_comp ψ φ).symm

/-- The forward component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma Rep.resFunctorCompIso_hom_app_apply (φ : G →* H) (ψ : H →* K) (A : Rep k K) (x : A.V) :
    ((Rep.resFunctorCompIso φ ψ).hom.app A) x = x := by
  unfold Rep.resFunctorCompIso
  rfl

/-- The inverse component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma Rep.resFunctorCompIso_inv_app_apply (φ : G →* H) (ψ : H →* K) (A : Rep k K) (x : A.V) :
    ((Rep.resFunctorCompIso φ ψ).inv.app A) x = x := by
  unfold Rep.resFunctorCompIso
  rfl

end Restriction

section Induction

variable [CommRing k] [Group G] [Group H] [Group K]

/-- Induction in stages: induction along a composite is naturally isomorphic to successive
inductions along the two group homomorphisms. -/
noncomputable def Rep.indFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    Rep.indFunctor.{max u v w x} k φ ⋙
      Rep.indFunctor.{max u v w x} k ψ ≅
        Rep.indFunctor.{max u v w x} k (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (Rep.indResAdjunction.{max u v w x} k φ)
    (Rep.indResAdjunction.{max u v w x} k ψ)
    (Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (Rep.resFunctorCompIso φ ψ)

/-- The induction-in-stages isomorphism is characterized by the restriction-composition
isomorphism under the adjunction equivalence. -/
@[simp]
lemma Rep.conjugateEquiv_indFunctorCompIso_inv (φ : G →* H) (ψ : H →* K) :
    conjugateEquiv
      ((Rep.indResAdjunction.{max u v w x} k φ).comp
        (Rep.indResAdjunction.{max u v w x} k ψ))
      (Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
      (Rep.indFunctorCompIso φ ψ).inv =
        (Rep.resFunctorCompIso φ ψ).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The unit of Mathlib's induction--restriction adjunction is the generator map
`a ↦ ⟦1 ⊗ₜ a⟧` of the induced representation. Used to turn the abstract adjunction identity
`unit_conjugateEquiv` into a statement about elements. -/
private lemma Rep.indResAdjunction_unit_app_hom_apply (φ : G →* H) (A : Rep.{max u w t} k G)
    (a : A) :
    ((Rep.indResAdjunction.{t} k φ).unit.app A).hom a =
      Representation.IndV.mk φ A.ρ 1 a :=
  rfl

/-- The induction-in-stages isomorphism, backwards, on the generator `⟦1 ⊗ₜ a⟧`. This is the
adjunction identity `unit_conjugateEquiv` read on elements: both units are generator maps and
`resFunctorCompIso` is the identity on vectors, so the abstract characterisation
`conjugateEquiv_indFunctorCompIso_inv` becomes this single value. -/
private lemma Rep.indFunctorCompIso_inv_app_hom_apply_mk_one (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (a : A) :
    ((Rep.indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) =
      Representation.IndV.mk ψ (Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a) := by
  have key := unit_conjugateEquiv
    ((Rep.indResAdjunction.{max u v w x} k φ).comp
      (Rep.indResAdjunction.{max u v w x} k ψ))
    (Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (Rep.indFunctorCompIso φ ψ).inv A
  rw [Rep.conjugateEquiv_indFunctorCompIso_inv] at key
  -- Read the resulting identity of morphisms on `a`, then rewrite the composite unit into the two
  -- generator maps and delete the restriction functors, which act as the identity on vectors.
  have key := congrArg (fun f => f.hom a) key
  simp only [Adjunction.comp_unit_app, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply] at key
  rw [Rep.resMap_hom_apply, Rep.resMap_hom_apply,
    Rep.indResAdjunction_unit_app_hom_apply, Rep.indResAdjunction_unit_app_hom_apply,
    Rep.indResAdjunction_unit_app_hom_apply, Rep.resFunctorCompIso_hom_app_apply] at key
  exact key.symm

/-- A morphism out of an induced representation is the `κ⁻¹`-translate of its value at the group
coordinate `1`: it sends `⟦κ ⊗ₜ b⟧` to `Y.ρ κ⁻¹` of its value on `⟦1 ⊗ₜ b⟧`. Together with
`TauCeti.indV_ind_hom_ext` this is what lets a formula at the coordinate `1` determine a
morphism out of an induced representation. -/
lemma Rep.ind_hom_apply_mk {J : Type y} [Group J] (σ : J →* K) {B : Rep.{z} k J}
    {Y : Rep.{max u x z} k K} (f : Rep.ind σ B ⟶ Y) (κ : K) (b : B) :
    f.hom (Representation.IndV.mk σ B.ρ κ b) =
      Y.ρ κ⁻¹ (f.hom (Representation.IndV.mk σ B.ρ 1 b)) := by
  have hsrc : Representation.IndV.mk σ B.ρ κ b =
      (Rep.ind σ B).ρ κ⁻¹ (Representation.IndV.mk σ B.ρ 1 b) := by
    simp
  rw [hsrc, Rep.hom_comm_apply]

/-- Two morphisms of `K`-representations out of a twice-induced representation agree as soon as
they agree on the elements `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. This is the `Rep`-morphism companion of
`TauCeti.indV_ind_hom_ext`: equivariance removes the outer group coordinate from its
hypothesis. -/
lemma Rep.ind_ind_hom_ext (φ : G →* H) (ψ : H →* K) (A : Rep.{max u v w x} k G)
    {B : Rep.{max u v w x} k K}
    {f g : (Rep.indFunctor.{max u v w x} k φ ⋙
      Rep.indFunctor.{max u v w x} k ψ).obj A ⟶ B}
    (hfg : ∀ a : A,
      f.hom (Representation.IndV.mk ψ (Rep.ind φ A).ρ 1
          (Representation.IndV.mk φ A.ρ 1 a)) =
        g.hom (Representation.IndV.mk ψ (Rep.ind φ A).ρ 1
          (Representation.IndV.mk φ A.ρ 1 a))) :
    f = g := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (indV_ind_hom_ext φ ψ A.ρ fun κ a => ?_))
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply,
    Rep.ind_hom_apply_mk ψ (B := Rep.ind φ A) f κ _,
    Rep.ind_hom_apply_mk ψ (B := Rep.ind φ A) g κ _, hfg]

/-- **Induction in stages on representatives, backwards**: the inverse of the induction-in-stages
isomorphism sends `⟦κ ⊗ₜ a⟧` to `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Tagged `@[simp↓]` rather than `@[simp]` because
`simp` unfolds the reducible `Representation.IndV.mk` in the left-hand side. -/
@[simp↓]
lemma Rep.indFunctorCompIso_inv_app_hom_apply_mk (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (κ : K) (a : A) :
    ((Rep.indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ κ a) =
      Representation.IndV.mk ψ (Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ 1 a) := by
  rw [Rep.ind_hom_apply_mk (ψ.comp φ) (B := A) ((Rep.indFunctorCompIso φ ψ).inv.app A) κ a,
    Rep.indFunctorCompIso_inv_app_hom_apply_mk_one]
  simp

/-- **Induction in stages on representatives**: the induction-in-stages isomorphism sends
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧` to `⟦ψ(h) κ ⊗ₜ a⟧`. This is the explicit formula the character and Mackey
computations consume, in place of the abstract adjoint comparison. Tagged `@[simp↓]` for the same
reason as `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. -/
@[simp↓]
lemma Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (h : H) (κ : K) (a : A) :
    ((Rep.indFunctorCompIso φ ψ).hom.app A).hom
        (Representation.IndV.mk ψ (Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ h a)) =
      Representation.IndV.mk (ψ.comp φ) A.ρ (ψ h * κ) a := by
  have hinv := Rep.indFunctorCompIso_inv_app_hom_apply_mk φ ψ A (ψ h * κ) a
  rw [← indV_mk_ind_mk φ ψ A.ρ h κ a] at hinv
  rw [← hinv, ← Rep.comp_apply, (Rep.indFunctorCompIso φ ψ).inv_hom_id_app,
    Rep.id_apply]

/-- **The induction-in-stages isomorphism is determined by its values on the generators.** A
morphism of `K`-representations `Ind_ψ (Ind_φ A) ⟶ Ind_{ψφ} A` sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to
`⟦1 ⊗ₜ a⟧` for every `a : A` is the induction-in-stages isomorphism. This is how a comparison map
built by hand is identified with the adjoint one produced by `TauCeti.Rep.indFunctorCompIso`. -/
lemma Rep.eq_indFunctorCompIso_hom_app (φ : G →* H) (ψ : H →* K) (A : Rep.{max u v w x} k G)
    {f : (Rep.indFunctor.{max u v w x} k φ ⋙
        Rep.indFunctor.{max u v w x} k ψ).obj A ⟶
      (Rep.indFunctor.{max u v w x} k (ψ.comp φ)).obj A}
    (hf : ∀ a : A, f.hom (Representation.IndV.mk ψ (Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a)) = Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) :
    f = (Rep.indFunctorCompIso φ ψ).hom.app A := by
  refine Rep.ind_ind_hom_ext φ ψ A fun a => ?_
  rw [hf, Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk φ ψ A 1 1 a, map_one, one_mul]

/-- **Induction along an isomorphism is restriction along its inverse.** For `e : G ≃* H`,
`Ind_e ≅ Res_{e⁻¹}` as functors `Rep k G ⥤ Rep k H`: both are left adjoint to `Res_e`, which is an
equivalence (`MulEquiv.resFunctorEquiv`). -/
noncomputable def Rep.indFunctorMulEquivIso (e : G ≃* H) :
    Rep.indFunctor.{max u v w} k e.toMonoidHom ≅
      Rep.resFunctor.{max u v w} e.symm.toMonoidHom :=
  (Rep.indResAdjunction.{max u v w} k e.toMonoidHom).leftAdjointUniq
      ((MulEquiv.resFunctorEquiv e).symm.toAdjunction.ofNatIsoRight
        (eqToIso (MulEquiv.resFunctorEquiv_functor e))) ≪≫
    eqToIso (MulEquiv.resFunctorEquiv_inverse e)

/-- **Induction in stages through an intermediate subgroup.** For subgroups `S ≤ T` of `G`,
inducing a representation of `S`, viewed as the subgroup `S.subgroupOf T` of `T`, first to `T`
and then to `G` is inducing it from `S` to `G` directly. The identification of `S.subgroupOf T`
with `S` is `Subgroup.subgroupOfEquivOfLe`. -/
noncomputable def Rep.indFunctorSubgroupOfIso {S T : Subgroup G} (h : S ≤ T) :
    Rep.indFunctor.{max u v} k (S.subgroupOf T).subtype ⋙
        Rep.indFunctor.{max u v} k T.subtype ≅
      Rep.resFunctor.{max u v} (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom ⋙
        Rep.indFunctor.{max u v} k S.subtype :=
  have hφ : T.subtype.comp (S.subgroupOf T).subtype =
      S.subtype.comp (Subgroup.subgroupOfEquivOfLe h).toMonoidHom := by
    ext
    rfl
  Rep.indFunctorCompIso _ _ ≪≫ eqToIso (by rw [hφ]) ≪≫ (Rep.indFunctorCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight (Rep.indFunctorMulEquivIso _) _

end Induction

section Coinduction

variable [CommRing k] [Monoid G] [Monoid H] [Monoid K]

/-- Coinduction in stages: successive coinductions are naturally isomorphic to coinduction along
the composite homomorphism. -/
noncomputable def Rep.coindFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    Rep.coindFunctor.{max u v w x} k φ ⋙
      Rep.coindFunctor.{max u v w x} k ψ ≅
        Rep.coindFunctor.{max u v w x} k (ψ.comp φ) := by
  let adjφ := Rep.resCoindAdjunction.{max u v w x} k φ
  let adjψ := Rep.resCoindAdjunction.{max u v w x} k ψ
  let adjφψ := adjψ.comp adjφ
  let adjψφ := Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ)
  exact conjugateIsoEquiv adjφψ adjψφ (Rep.resFunctorCompIso φ ψ).symm

/-- The coinduction-in-stages isomorphism is characterized by the inverse
restriction-composition isomorphism under the inverse adjunction equivalence. -/
@[simp]
lemma Rep.conjugateEquiv_symm_coindFunctorCompIso_hom (φ : G →* H) (ψ : H →* K) : ((conjugateEquiv
      ((Rep.resCoindAdjunction.{max u v w x} k ψ).comp
        (Rep.resCoindAdjunction.{max u v w x} k φ))
      (Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))).symm
      (Rep.coindFunctorCompIso φ ψ).hom) = (Rep.resFunctorCompIso φ ψ).inv := by
  unfold Rep.coindFunctorCompIso
  exact Equiv.symm_apply_apply _ _

/-- The coinduction-in-stages isomorphism evaluated at `1`: it reads off the value of a doubly
coinduced function at the pair `(1, 1)`. This is the adjunction identity
`conjugateEquiv_counit_symm` read on elements, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk_one`. -/
private lemma Rep.coindFunctorCompIso_hom_app_hom_apply_coe_one (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (F : Rep.coind ψ (Rep.coind φ A)) :
    (((Rep.coindFunctorCompIso φ ψ).hom.app A).hom F).1 1 = (F.1 1).1 1 := by
  have key := conjugateEquiv_counit_symm
    ((Rep.resCoindAdjunction.{max u v w x} k ψ).comp
      (Rep.resCoindAdjunction.{max u v w x} k φ))
    (Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))
    (Rep.coindFunctorCompIso φ ψ).hom A
  rw [Rep.conjugateEquiv_symm_coindFunctorCompIso_hom] at key
  -- Read the resulting identity of morphisms on `F`, then rewrite the composite counit into the
  -- two evaluations at `1` and delete the restriction functors, which act as the identity.
  have key := congrArg (fun f : _ ⟶ A => f.hom F) key
  simp only [Adjunction.comp_counit_app, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply] at key
  rw [Rep.resMap_hom_apply, Rep.resMap_hom_apply,
    Rep.resCoindAdjunction_counit_app_hom_apply, Rep.resCoindAdjunction_counit_app_hom_apply,
    Rep.resCoindAdjunction_counit_app_hom_apply, Rep.resFunctorCompIso_inv_app_apply] at key
  exact key

/-- **Coinduction in stages on functions**: the coinduction-in-stages isomorphism sends an
`H`-equivariant function `F : K → coind φ A`, whose values are themselves the `G`-equivariant
functions `H → A`, to `κ ↦ F κ 1`. This is the dual of
`TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk`, and is obtained from its value at `1` by
`K`-equivariance. Tagged `@[simp↓]` rather than `@[simp]` because `simp` rewrites the source and
target of the isomorphism component in the left-hand side. -/
@[simp↓]
lemma Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (F : Rep.coind ψ (Rep.coind φ A)) (κ : K) :
    (((Rep.coindFunctorCompIso φ ψ).hom.app A).hom F).1 κ = (F.1 κ).1 1 := by
  have hcomm := Rep.hom_comm_apply ((Rep.coindFunctorCompIso φ ψ).hom.app A) κ F
  have h1 := Rep.coindFunctorCompIso_hom_app_hom_apply_coe_one φ ψ A
    (((Rep.coindFunctor.{max u v w x} k φ ⋙
      Rep.coindFunctor.{max u v w x} k ψ).obj A).ρ κ F)
  rw [hcomm] at h1
  simp only [Functor.comp_obj, Rep.coindFunctor_obj, Rep.of_ρ] at h1
  rw [Representation.coind_apply_coe_apply, Representation.coind_apply_coe_apply] at h1
  simpa using h1

/-- **Coinduction in stages on functions, backwards**: the inverse of the coinduction-in-stages
isomorphism turns a `G`-equivariant function `f : K → A` into `κ ↦ (h ↦ f (ψ(h) κ))`, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. Tagged `@[simp↓]` for the same reason as
`TauCeti.Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply`. -/
@[simp↓]
lemma Rep.coindFunctorCompIso_inv_app_hom_apply_coe_apply_coe_apply (φ : G →* H) (ψ : H →* K)
    (A : Rep.{max u v w x} k G) (f : Rep.coind (ψ.comp φ) A) (κ : K) (h : H) :
    ((((Rep.coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 h = f.1 (ψ h * κ) := by
  have hfF : ((Rep.coindFunctorCompIso φ ψ).hom.app A).hom
      (((Rep.coindFunctorCompIso φ ψ).inv.app A).hom f) = f := by
    rw [← Rep.comp_apply, (Rep.coindFunctorCompIso φ ψ).inv_hom_id_app, Rep.id_apply]
  have hhom : ∀ κ' : K, ((((Rep.coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ').1 1 = f.1 κ' :=
    fun κ' => (Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply φ ψ A _ κ').symm.trans
      (congrArg (fun y : Rep.coind (ψ.comp φ) A => y.1 κ') hfF)
  have hmem := (((Rep.coindFunctorCompIso φ ψ).inv.app A).hom f).2 h κ
  simp only [Rep.coindFunctor_obj, Rep.of_ρ] at hmem
  have hx : f.1 (ψ h * κ) = ((((Rep.coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 (1 * h) := by
    rw [← hhom (ψ h * κ), hmem, Representation.coind_apply_coe_apply]
  rw [hx, one_mul]

end Coinduction

end TauCeti
end
end TAF_LiteralSource_0164

section TAF_LiteralSource_0165
/- Original module: TauCeti.RepresentationTheory.Induction.Permutation -/
/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The permutation representation as an induced representation

For a subgroup `H` of a group `G`, inducing the trivial `H`-representation along `H.subtype`
gives the permutation representation of `G` on the left cosets `G ⧸ H`, and its character is the
number of fixed cosets, cast into the coefficient field.

More generally, for subgroups `D ≤ C ≤ G`, inducing the permutation representation of `C` on
`C ⧸ (D ⊓ C)` gives the permutation representation of `G` on `G ⧸ D`: a permutation
representation on cosets can be induced in stages.

Feeding the first identification into the projection formula of
`TauCeti/RepresentationTheory/Induction/Projection.lean` gives the classical description of
inducing a restricted representation, `Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y`.

## Main definitions

* `TauCeti.indTrivialEquiv`: the equivalence of representations `Ind_H^G (trivial) ≃ k[G ⧸ H]`.
* `TauCeti.indTrivialIso`: the same statement in `Rep k G`.
* `TauCeti.indOfMulActionQuotientEquiv`: for `D ≤ C`, the equivalence of representations
  `Ind_C^G k[C ⧸ (D ⊓ C)] ≃ k[G ⧸ D]`.
* `TauCeti.indResProjection`: the corollary `Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y` of the projection
  formula `TauCeti.indProjection`.

## Main statements

* `TauCeti.char_ofMulAction`: the character of a permutation representation at `g` is the
  number of points fixed by `g`, cast into `k`.
* `TauCeti.char_ind_trivial`: the character of `Ind_H^G (trivial)` at `g` is the number of
  cosets fixed by `g`, cast into `k`.

Both statements are equalities in `k`, so in positive characteristic they determine the fixed-point
count only modulo the characteristic.

## Implementation notes

Mathlib's `Representation.ind` is built as the coinvariants of `k[G] ⊗[k] A`, so the coset
orientation is a proof obligation rather than a convention: the `H`-action being quotiented out is
left translation on `k[G]`, whose orbits are the *right* cosets `Hx`, while `G` acts by right
translation by the inverse. The equivalence below therefore sends `⟦single x r ⊗ₜ a⟧` to
`single ⟦x⁻¹⟧ (a • r)`; inversion is what converts right cosets carrying a right action into
Mathlib's left-coset quotient `G ⧸ H` with its left action. In the same way
`TauCeti.indOfMulActionQuotientEquiv` sends `⟦single x 1 ⊗ₜ single ⟦c⟧ s⟧` to `single ⟦x⁻¹ * c⟧ s`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.1 (the permutation character) and
  §3.3 (inducing the unit representation, and the projection formula).
-/

public section

open CategoryTheory MonoidalCategory Representation TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section Induced

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (H : Subgroup G)

/-- The `H`-representation on `k[G] ⊗[k] k` whose coinvariants define `Ind_H^G (trivial)`:
left translation by `H` on `k[G]`, and the trivial action on `k`. -/
private noncomputable abbrev indTrivialSource : Representation k H (k[G] ⊗[k] k) :=
  Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
    (Representation.trivial k H k)

/-- The linear map `k[G] ⊗[k] k →ₗ[k] k[G ⧸ H]` sending `single x r ⊗ₜ a` to
`single ⟦x⁻¹⟧ (a • r)`. -/
private noncomputable def indTrivialLift : (k[G] ⊗[k] k) →ₗ[k] k[G ⧸ H] :=
  MonoidAlgebra.mapDomainLinearMap k k (fun x : G ↦ (QuotientGroup.mk x⁻¹ : G ⧸ H)) ∘ₗ
    (TensorProduct.rid k k[G]).toLinearMap

private theorem indTrivialLift_tmul (x : G) (r a : k) :
    indTrivialLift k H (MonoidAlgebra.single x r ⊗ₜ a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) (a • r) := by
  simp [indTrivialLift]

private theorem indTrivialLift_comp (s : H) :
    indTrivialLift k H ∘ₗ indTrivialSource k H s = indTrivialLift k H := by
  ext x
  simp [indTrivialLift,Subgroup.smul_def,smul_eq_mul,mul_inv_rev,
    QuotientGroup.mk_mul_of_mem]

/-- The forward map of `TauCeti.indTrivialEquiv`, from `Ind_H^G (trivial)` to `k[G ⧸ H]`. -/
private noncomputable def indTrivialToQuotient :
    IndV H.subtype (Representation.trivial k H k) →ₗ[k] k[G ⧸ H] :=
  Coinvariants.lift _ (indTrivialLift k H) (indTrivialLift_comp k H)

private theorem indTrivialToQuotient_mk (x : G) (a : k) :
    indTrivialToQuotient k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a := by
  simp [indTrivialToQuotient, IndV.mk, indTrivialLift_tmul]

/-- The image of a coset `⟦x⟧` in `Ind_H^G (trivial)`, namely `⟦single x⁻¹ 1 ⊗ₜ 1⟧`. -/
private noncomputable def indTrivialMk (q : G ⧸ H) :
    IndV H.subtype (Representation.trivial k H k) :=
  Quotient.liftOn' q
    (fun x : G ↦ IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k))
    fun _ b hab ↦ by
      simpa using (indV_mk_apply_inv H.subtype (Representation.trivial k H k)
        ⟨_, QuotientGroup.leftRel_apply.1 hab⟩ b⁻¹ 1).symm

private theorem indTrivialMk_mk (x : G) :
    indTrivialMk k H (QuotientGroup.mk x) =
      IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  rfl

/-- The inverse map of `TauCeti.indTrivialEquiv`, from `k[G ⧸ H]` to `Ind_H^G (trivial)`. -/
private noncomputable def quotientToIndTrivial :
    k[G ⧸ H] →ₗ[k] IndV H.subtype (Representation.trivial k H k) :=
  Finsupp.linearCombination k (indTrivialMk k H) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem quotientToIndTrivial_single (q : G ⧸ H) (r : k) :
    quotientToIndTrivial k H (MonoidAlgebra.single q r) = r • indTrivialMk k H q := by
  simp [quotientToIndTrivial]

/-- **The permutation representation.** Inducing the trivial representation of a subgroup `H ≤ G`
along `H.subtype` gives the permutation representation of `G` on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialEquiv : ((Representation.trivial k H k).ind H.subtype).Equiv
      (Representation.ofMulAction k G (G ⧸ H)) := by
  refine Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (indTrivialToQuotient k H) (quotientToIndTrivial k H) ?_ ?_) ?_
  · refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp [quotientToIndTrivial_single, indTrivialMk_mk, indTrivialToQuotient,
        indTrivialLift_tmul]
  · refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    simp [indTrivialToQuotient, indTrivialLift_tmul, quotientToIndTrivial_single,
      indTrivialMk_mk]
  · intro g
    refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    simp [indTrivialToQuotient, indTrivialLift_tmul, ofMulAction_single, mul_inv_rev]

-- Pre-order simplification evaluates the map before `simp` unfolds `Representation.IndV.mk`.
/-- The generator computation rule for `TauCeti.indTrivialEquiv`. -/
@[simp↓]
theorem indTrivialEquiv_apply_mk (x : G) (a : k) :
    indTrivialEquiv k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a :=
  indTrivialToQuotient_mk k H x a

/-- The generator computation rule for the inverse of `TauCeti.indTrivialEquiv`. -/
@[simp]
theorem indTrivialEquiv_symm_apply_single (x : G) (r : k) :
    (indTrivialEquiv k H).symm (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) r) =
      r • IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  quotientToIndTrivial_single k H _ r

/-- **The permutation representation**, in `Rep k G`: inducing the trivial representation of a
subgroup `H ≤ G` gives the permutation representation on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialIso :
    Rep.ind H.subtype (Rep.trivial k H k) ≅ Rep.ofMulAction k G (G ⧸ H) :=
  Rep.mkIso (indTrivialEquiv k H)

-- Pre-order simplification evaluates the map before `simp` unfolds `Representation.IndV.mk`.
/-- The generator computation rule for `TauCeti.indTrivialIso`: it sends `⟦single x 1 ⊗ₜ a⟧` to
`single ⟦x⁻¹⟧ a`. -/
@[simp↓]
theorem indTrivialIso_hom_hom_apply_mk (x : G) (a : k) :
    (indTrivialIso k H).hom.hom (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a := by
  rw [indTrivialIso, Rep.mkIso_hom_hom_apply]
  exact indTrivialEquiv_apply_mk k H x a

-- `simp` reduces the carriers of the `abbrev`s `Rep.ind`, `Rep.trivial` and `Rep.ofMulAction`
-- in implicit type arguments before it looks a term up, so the left-hand side is stated through
-- `dsimp% only`, as in #8315.
/-- The computation rule for the inverse of `TauCeti.indTrivialIso` on the standard basis of
`k[G ⧸ H]`. -/
@[simp]
theorem indTrivialIso_inv_hom_apply_single (x : G) (r : k) :
    (dsimp% only
        ((indTrivialIso k H).inv.hom (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) r))) =
      r • IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) := by
  rw [indTrivialIso, Rep.mkIso_inv_hom_apply]
  exact indTrivialEquiv_symm_apply_single k H x r

/-- `Ind_H^G (trivial)` is a finite module whenever `H` has finite index. -/
instance instFiniteIndTrivial [Finite (G ⧸ H)] :
    Module.Finite k (IndV H.subtype (Representation.trivial k H k)) :=
  Module.Finite.equiv (indTrivialEquiv k H).toLinearEquiv.symm

end Induced

section InducedQuotient

variable (k : Type u) [CommRing k] {G : Type v} [Group G] {C D : Subgroup G} (h : D ≤ C)

/-- The `C`-representation on `k[G] ⊗[k] k[C ⧸ (D ⊓ C)]` whose coinvariants define the induced
representation. -/
private noncomputable abbrev indQuotientSource :
    Representation k C (k[G] ⊗[k] k[C ⧸ D.subgroupOf C]) :=
  Representation.tprod ((Representation.leftRegular k G).comp C.subtype)
    (Representation.ofMulAction k C (C ⧸ D.subgroupOf C))

/-- The linear map `k[G] ⊗[k] k[C ⧸ (D ⊓ C)] →ₗ[k] k[G ⧸ D]` sending
`single x r ⊗ₜ single ⟦c⟧ s` to `single ⟦x⁻¹ * c⟧ (r * s)`. -/
private noncomputable def indQuotientLift :
    (k[G] ⊗[k] k[C ⧸ D.subgroupOf C]) →ₗ[k] k[G ⧸ D] :=
  TensorProduct.lift <|
    Finsupp.linearCombination k (fun x : G ↦
        MonoidAlgebra.mapDomainLinearMap k k <|
          Quotient.map' (fun c : C ↦ x⁻¹ * c) fun a b hab ↦ by
            simpa [QuotientGroup.leftRel_apply, mul_assoc, Subgroup.mem_subgroupOf] using hab) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem indQuotientLift_tmul (x : G) (r : k) (c : C) (s : k) :
    indQuotientLift k (MonoidAlgebra.single x r ⊗ₜ
        MonoidAlgebra.single (QuotientGroup.mk c : C ⧸ D.subgroupOf C) s) =
      MonoidAlgebra.single (QuotientGroup.mk (x⁻¹ * c) : G ⧸ D) (r * s) := by
  simp [indQuotientLift]

private theorem indQuotientLift_comp (c : C) :
    indQuotientLift k ∘ₗ indQuotientSource k c = indQuotientLift k (D := D) := by
  refine TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring <|
    MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
  induction q using QuotientGroup.induction_on with
  | H y => simp [indQuotientLift_tmul, Representation.ofMulAction_single,
      Subgroup.smul_def,smul_eq_mul,mul_inv_rev,mul_assoc]

/-- The forward map of `TauCeti.indOfMulActionQuotientEquiv`, from `Ind_C^G k[C ⧸ (D ⊓ C)]` to
`k[G ⧸ D]`. -/
private noncomputable def indQuotientToQuotient :
    IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) →ₗ[k] k[G ⧸ D] :=
  Coinvariants.lift _ (indQuotientLift k) (indQuotientLift_comp k)

include h in
/-- The image of a coset `⟦x⟧` in `Ind_C^G k[C ⧸ (D ⊓ C)]`, namely `⟦single x⁻¹ 1 ⊗ₜ single ⟦1⟧ 1⟧`.
It is well defined because `D ≤ C` fixes the coset `⟦1⟧`. -/
private noncomputable def indQuotientMk (q : G ⧸ D) :
    IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) :=
  Quotient.liftOn' q
    (fun x : G ↦ IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
      (MonoidAlgebra.single (QuotientGroup.mk 1) 1))
    fun a b hab ↦ by
      have hd : a⁻¹ * b ∈ D := QuotientGroup.leftRel_apply.1 hab
      let d : C := ⟨a⁻¹ * b, h hd⟩
      have hfix : Representation.ofMulAction k C (C ⧸ D.subgroupOf C) d⁻¹
          (MonoidAlgebra.single (QuotientGroup.mk 1) 1) =
            MonoidAlgebra.single (QuotientGroup.mk 1) 1 := by
        rw [Representation.ofMulAction_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
        congr 1
        rw [QuotientGroup.eq]
        simpa [d] using Subgroup.mem_subgroupOf.2 hd
      have ha : a⁻¹ = C.subtype d * b⁻¹ := by simp [d]
      rw [ha, ← indV_mk_apply_inv, hfix]

private theorem indQuotientMk_mk (x : G) :
    indQuotientMk k h (QuotientGroup.mk x) =
      IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
        (MonoidAlgebra.single (QuotientGroup.mk 1) 1) :=
  rfl

include h in
/-- The inverse map of `TauCeti.indOfMulActionQuotientEquiv`, from `k[G ⧸ D]` to
`Ind_C^G k[C ⧸ (D ⊓ C)]`. -/
private noncomputable def quotientToIndQuotient :
    k[G ⧸ D] →ₗ[k] IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) :=
  Finsupp.linearCombination k (indQuotientMk k h) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem quotientToIndQuotient_single (q : G ⧸ D) (r : k) :
    quotientToIndQuotient k h (MonoidAlgebra.single q r) = r • indQuotientMk k h q := by
  simp [quotientToIndQuotient]

include h in
/-- **Induction of a coset permutation representation.** For subgroups `D ≤ C ≤ G`, inducing the
permutation representation of `C` on its cosets `C ⧸ (D ⊓ C)` along `C.subtype` gives the
permutation representation of `G` on `G ⧸ D`. For `D = C` this is `TauCeti.indTrivialEquiv` up to
the identification of `k[C ⧸ ⊤]` with the trivial representation. -/
noncomputable def indOfMulActionQuotientEquiv :
    ((Representation.ofMulAction k C (C ⧸ D.subgroupOf C)).ind C.subtype).Equiv
      (Representation.ofMulAction k G (G ⧸ D)) := by
  refine Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (indQuotientToQuotient k) (quotientToIndQuotient k h) ?_ ?_) ?_
  · refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp [quotientToIndQuotient_single, indQuotientMk_mk, indQuotientToQuotient,
        indQuotientLift_tmul]
  · refine IndV.hom_ext _ _ fun x ↦ MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      -- `⟦single x 1 ⊗ₜ single ⟦c⟧ 1⟧ = ⟦single (c⁻¹ * x) 1 ⊗ₜ single ⟦1⟧ 1⟧` in the coinvariants.
      simpa [quotientToIndQuotient_single, indQuotientMk_mk, indQuotientToQuotient,
        indQuotientLift_tmul, Representation.ofMulAction_single] using
        (indV_mk_apply_inv C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) c⁻¹ x
          (MonoidAlgebra.single (QuotientGroup.mk 1) 1)).symm
  · intro g
    refine IndV.hom_ext _ _ fun x ↦ MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      simp [indQuotientToQuotient, indQuotientLift_tmul, Representation.ofMulAction_single,
        mul_assoc]

-- Pre-order simplification evaluates the map before `simp` unfolds `Representation.IndV.mk`.
/-- The generator computation rule for `TauCeti.indOfMulActionQuotientEquiv`: it sends
`⟦single x 1 ⊗ₜ single ⟦c⟧ s⟧` to `single ⟦x⁻¹ * c⟧ s`. -/
@[simp↓]
theorem indOfMulActionQuotientEquiv_apply_mk (x : G) (c : C) (s : k) :
    indOfMulActionQuotientEquiv k h
        (IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x
          (MonoidAlgebra.single (QuotientGroup.mk c) s)) =
      MonoidAlgebra.single (QuotientGroup.mk (x⁻¹ * c) : G ⧸ D) s := by
  simp [indOfMulActionQuotientEquiv, indQuotientToQuotient, indQuotientLift_tmul]

/-- The generator computation rule for the inverse of `TauCeti.indOfMulActionQuotientEquiv`. -/
@[simp]
theorem indOfMulActionQuotientEquiv_symm_apply_single (x : G) (r : k) :
    (indOfMulActionQuotientEquiv k h).symm (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ D) r) =
      r • IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
        (MonoidAlgebra.single (QuotientGroup.mk 1) 1) :=
  quotientToIndQuotient_single k h _ r

end InducedQuotient

section Projection

variable {k : Type u} {G : Type u} [CommRing k] [Group G] {H : Subgroup G} (Y : Rep k G)

/-- **Induction of a restriction.** For a subgroup `H ≤ G`, restricting a `G`-representation to `H`
and inducing back up tensors it with the permutation representation on the cosets,
`Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y`. This is `TauCeti.indProjection` applied to the trivial
`H`-representation, followed by `TauCeti.indTrivialIso`. -/
noncomputable def indResProjection :
    Rep.ind H.subtype (Rep.res H.subtype Y) ≅ Rep.ofMulAction k G (G ⧸ H) ⊗ Y :=
  (Rep.indFunctor k H.subtype).mapIso (λ_ (Rep.res H.subtype Y)).symm ≪≫
    indProjection H.subtype (𝟙_ (Rep k H)) Y ≪≫
    (indTrivialIso k H ⊗ᵢ Iso.refl Y)

/-- `TauCeti.indResProjection` on generators: the coset orientation is the one inherited from
`TauCeti.indTrivialIso`, which sends `⟦x ⊗ₜ a⟧` to `single ⟦x⁻¹⟧ a`. -/
@[simp↓]
theorem indResProjection_hom_hom_apply (x : G) (y : Y) :
    (indResProjection Y).hom.hom (IndV.mk H.subtype (Rep.res H.subtype Y).ρ x y)
      = MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) (1 : k) ⊗ₜ[k] Y.ρ x⁻¹ y := by
  refine Eq.trans ?_ (congrArg (· ⊗ₜ[k] Y.ρ x⁻¹ y) (indTrivialIso_hom_hom_apply_mk k H x 1))
  refine Eq.trans ?_ (congrArg (Rep.Hom.hom (indTrivialIso k H ⊗ᵢ Iso.refl Y).hom)
    (indProjection_hom_hom_apply H.subtype (𝟙_ (Rep k H)) Y x 1 y))
  simp [indResProjection, Rep.indMap]

end Projection

section PermutationCharacter

variable (k : Type u) [Field k] {G : Type v} [Monoid G]

/-- **The permutation character.** The character of the permutation representation `k[X]` at `g`
is the number of points of `X` fixed by `g`, cast into `k`. -/
@[simp]
theorem char_ofMulAction (X : Type w) [MulAction G X] [Finite X] (g : G) :
    (Representation.ofMulAction k G X).character g = Nat.card {x : X // g • x = x} := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis X k), Matrix.trace]
  simp [LinearMap.toMatrix_apply, MonoidAlgebra.basis, Finsupp.single_apply,
    Fintype.card_subtype]

end PermutationCharacter

section Character

variable (k : Type u) [Field k] {G : Type v} [Group G] (H : Subgroup G)

/-- **The permutation character of an induced trivial representation.** The character of
`Ind_H^G (trivial)` at `g` is the number of cosets in `G ⧸ H` fixed by `g`, cast into `k`. -/
@[simp]
theorem char_ind_trivial [Finite (G ⧸ H)] (g : G) :
    ((Representation.trivial k H k).ind H.subtype).character g =
      Nat.card {q : G ⧸ H // g • q = q} := by
  rw [Representation.char_iso (indTrivialEquiv k H), char_ofMulAction]

end Character

end TauCeti
end
end TAF_LiteralSource_0165

section TAF_LiteralSource_0166
/- Original module: TauCeti.GroupTheory.Perm.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Elementary facts about permutations

This file records general-purpose facts about permutations: a map intertwining two permutations
intertwines their integer powers (`Function.Semiconj.perm_zpow_right`), a transposition
preserves the complement of a set containing neither of its swapped points, an identity between
transpositions,
a permutation transporting two points outside a fixed set to another such pair,
the values of the three-cycle written as a product of two transpositions sharing a point,
a characterization of permutations with a unique fixed point, functions constant on a permutation
orbit, the orbit relation of an involution, a positive-power representative of a relation inside a
periodic orbit, a function whose difference `z ↦ c (σ⁻¹ z) - c z` joins points in the same orbit
(`Equiv.Perm.SameCycle.exists_comp_symm_sub_eq`, `Equiv.Perm.exists_comp_symm_sub_eq_sum`), a
transposition forming one cycle on a `Fin 2` fibre over `Fin 1`, a
permutation transported along an injection, the combination of two
permutations transported along injections with disjoint ranges, a fiber-preserving permutation
carrying one finite family to another with the same equality pattern
(`TauCeti.exists_perm_apply_eq_of_eq_iff`), the fact that a permutation
is a single cycle on each of its own orbits, the transport of its cycles along an equivalence of
types, the relabelling of a two-argument family invariant under a permutation of its first argument
paired with a map on its second (`Equiv.Perm.apply_inv_eq_comp_of_apply_apply_eq`), transport of
cycle quotients along conjugating equivalences, and the factorization of an invariant function
through a map on whose fibres the permutation is a single cycle, and a correction by a power of
a cycle for a permutation commuting with it. Points over distinct classes of the cycle quotient are
distinct (`Equiv.Perm.ne_of_sameCycle_out`), and precomposing with `σ` does not change a sum over a
`σ`-orbit (`Equiv.Perm.sum_filter_sameCycle_comp`). It also identifies functions invariant under a
permutation with functions on its cycle quotient (`TauCeti.invariantColouringEquiv`); a function
invariant under a set of permutations is invariant under the subgroup they generate
(`TauCeti.apply_eq_of_mem_closure`), hence constant when that subgroup acts transitively
(`TauCeti.apply_eq_apply_of_isPretransitive_closure`). Finally, right
multiplication by `a` is a single cycle on the whole group exactly when `a` generates it
(`Equiv.isCycleOn_mulRight_univ_iff`). Alternating a signed sum over permutations a second time,
along a sign-preserving map of permutation groups, multiplies it by the number of permutations
alternated over (`TauCeti.sum_sign_smul_sum_sign_smul_eq_card_nsmul`), and a signed sum over the
permutations of `Fin (n + 1)` evaluated on a tuple `Fin.cons x w` expands along the slot that
receives `x` (`TauCeti.sum_sign_smul_cons_comp_eq_sum_insertNth`), or along the entry moved to the
front or to any other slot (`TauCeti.sum_sign_smul_comp_eq_sum_cons_removeNth`,
`TauCeti.sum_sign_smul_comp_eq_sum_insertNth_removeNth`). Removing a pair `{a, σ a}` from an
involution `σ` by left multiplication with `Equiv.swap a (σ a)` leaves an involution that agrees
with `σ` off the pair (`Function.Involutive.swap_mul`,
`Function.Involutive.swap_mul_apply_eq_self_or`), and multiplying back on the right recovers `σ`
(`Function.Involutive.swap_mul_mul_swap`). A permutation of a finite type sends as many points
into a set as out of it (`Equiv.Perm.card_filter_not_and_apply_eq`).
-/

public section

namespace Function.Semiconj

variable {α γ : Type*} {σ : Equiv.Perm α} {τ : Equiv.Perm γ} {g : α → γ}

/-- A map intertwining two permutations also intertwines all of their integer powers. This
extends `Function.Semiconj.iterate_right` to negative exponents. -/
theorem perm_zpow_right (hg : Function.Semiconj g σ τ) (k : ℤ) :
    Function.Semiconj g ⇑(σ ^ k) ⇑(τ ^ k) := by
  intro z
  have hinv : Function.Semiconj g (σ⁻¹ : Equiv.Perm α) (τ⁻¹ : Equiv.Perm γ) :=
    Function.Semiconj.inverses_right hg σ.right_inv τ.left_inv
  cases k with
  | ofNat m =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hg m z)
  | negSucc m =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hinv (m + 1) z)

end Function.Semiconj

namespace Equiv.Perm.SameCycle

variable {α : Type*} {β : Sort*} {σ : Equiv.Perm α} {x y : α} {f : α → β}

variable {γ : Type*} {τ : Equiv.Perm γ} {g : α → γ}

/-- A function invariant under one application of a permutation is constant on every orbit of
that permutation. -/
theorem apply_eq_of_apply_eq (hσ : σ.SameCycle x y) (hf : ∀ z, f (σ z) = f z) : f x = f y := by
  obtain ⟨k, rfl⟩ := hσ
  have hmap := Function.Semiconj.perm_zpow_right (τ := 1) (g := fun z => PLift.up (f z))
    (fun z => congrArg PLift.up (hf z)) k x
  exact congrArg PLift.down (by simpa only [one_zpow, Equiv.Perm.one_apply] using hmap.symm)

/-- A map intertwining two permutations carries orbits of the first permutation into orbits of
the second. -/
theorem map (hσ : σ.SameCycle x y) (hg : ∀ z, g (σ z) = τ (g z)) :
    τ.SameCycle (g x) (g y) := by
  obtain ⟨k, rfl⟩ := hσ
  exact ⟨k, (Function.Semiconj.perm_zpow_right hg k x).symm⟩

/-- If a periodic point `x` of `σ` shares its orbit with `y`, some positive natural power of `σ`
carries `x` to `y`. -/
theorem exists_pos_pow_eq_of_mem_periodicPts (h : σ.SameCycle x y)
    (hx : x ∈ Function.periodicPts (σ : α → α)) : ∃ j : ℕ, 0 < j ∧ (σ ^ j) x = y := by
  obtain ⟨k, hk⟩ := h
  have hperiod : MulAction.period σ x = Function.minimalPeriod (σ : α → α) x :=
    MulAction.period_eq_minimalPeriod
  have hpos : 0 < MulAction.period σ x :=
    hperiod ▸ Function.minimalPeriod_pos_of_mem_periodicPts hx
  have hnonneg : 0 ≤ k % (MulAction.period σ x : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hpos.ne')
  refine ⟨(k % (MulAction.period σ x : ℤ)).toNat + MulAction.period σ x, by omega, ?_⟩
  have hred : σ ^ (k % (MulAction.period σ x : ℤ) + (MulAction.period σ x : ℤ)) • x = y := by
    rw [MulAction.zpow_add_period_smul, MulAction.zpow_mod_period_smul]
    exact hk
  rw [Equiv.Perm.smul_def] at hred
  rw [← zpow_natCast, Nat.cast_add, Int.toNat_of_nonneg hnonneg]
  exact hred

/-- Two points `x`, `y` in the same orbit of `σ` are joined along the orbit: some `c : α → M`
has difference `z ↦ c (σ⁻¹ z) - c z` equal to `Pi.single y a - Pi.single x a`. -/
theorem exists_comp_symm_sub_eq [DecidableEq α] {M : Type*} [AddCommGroup M]
    (h : σ.SameCycle x y) (a : M) :
    ∃ c : α → M, (fun z => c (σ.symm z) - c z) = Pi.single y a - Pi.single x a := by
  -- Adding `s • [w]` to `c` adds `s • ([σ w] - [w])` to its difference.
  have step (c : α → M) (w : α) (s : ℤ) :
      (fun z => (c + s • Pi.single w a : α → M) (σ.symm z) - (c + s • Pi.single w a : α → M) z) =
        (fun z => c (σ.symm z) - c z) + s • (Pi.single (σ w) a - Pi.single w a) := by
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Equiv.symm_apply_eq]
    split_ifs <;> simp only [smul_sub] <;> abel
  obtain ⟨k, rfl⟩ := h
  induction k using Int.induction_on with
  | zero => exact ⟨0, funext fun z => by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (1 : ℤ) • Pi.single ((σ ^ (k : ℤ)) x) a, ?_⟩
    rw [step, hc, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm (1 : ℤ)]
    abel
  | pred k ih =>
    obtain ⟨c, hc⟩ := ih
    have h_exp : (1 + (-k - 1) : ℤ) = -k := by omega
    refine ⟨c + (-1 : ℤ) • Pi.single ((σ ^ (-k - 1 : ℤ)) x) a, ?_⟩
    rw [step, hc, ← Equiv.Perm.mul_apply, ← zpow_one_add, h_exp]
    abel

end Equiv.Perm.SameCycle

namespace TauCeti

/-- The transposition of `Fin 2` is one cycle on every fibre of a map to `Fin 1`. -/
theorem isCycleOn_swap_fin_two_fiber (f : Fin 2 → Fin 1) (i : Fin 1) :
    (Equiv.swap (0 : Fin 2) 1).IsCycleOn {p | f p = i} := by
  convert Equiv.Perm.isCycleOn_swap (a := (0 : Fin 2)) (b := 1)
    (by decide : (0 : Fin 2) ≠ 1) using 1
  ext p
  fin_cases p <;> simp [Subsingleton.elim (f _) i]

end TauCeti

namespace Equiv.Perm

variable {α : Type*} (σ : Equiv.Perm α)

/-- A permutation is a single cycle on each of its own orbits. -/
theorem isCycleOn_setOf_sameCycle (x : α) : σ.IsCycleOn {y | σ.SameCycle x y} :=
  ⟨σ.bijOn fun _ => sameCycle_apply_right, fun _ hy _ hz => hy.symm.trans hz⟩

/-- A permutation is a single cycle on each fibre of the quotient map onto its orbits. This is the
form in which the cyclic order around a vertex of a ribbon graph is read off a permutation. -/
theorem isCycleOn_preimage_quotientMk (b : Quotient (SameCycle.setoid σ)) :
    σ.IsCycleOn (Quotient.mk (SameCycle.setoid σ) ⁻¹' {b}) := by
  induction b using Quotient.inductionOn with
  | _ x =>
    have hfibre : Quotient.mk (SameCycle.setoid σ) ⁻¹' {Quotient.mk _ x} =
        {y | σ.SameCycle x y} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Set.mem_ofPred_eq]
      exact sameCycle_comm
    rw [hfibre]
    exact σ.isCycleOn_setOf_sameCycle x

/-- A function invariant under a permutation that is a single cycle on each fibre of `g` factors
through `g`. -/
theorem factorsThrough_of_forall_isCycleOn {ι β : Type*} {g : α → ι}
    (hσ : ∀ i, σ.IsCycleOn {x | g x = i}) {f : α → β} (hf : ∀ x, f (σ x) = f x) :
    f.FactorsThrough g :=
  fun _ b hab => ((hσ (g b)).2 hab rfl).apply_eq_of_apply_eq hf

variable {σ} in
/-- Points in the orbits of the representatives of two distinct classes of the cycle quotient
are distinct. -/
theorem ne_of_sameCycle_out {x y : α} {O P : Quotient (SameCycle.setoid σ)}
    (hx : σ.SameCycle x O.out) (hy : σ.SameCycle y P.out) (hOP : O ≠ P) : x ≠ y := by
  rintro rfl
  exact hOP ((Quotient.mk_eq_iff_out.mpr hx).symm.trans (Quotient.mk_eq_iff_out.mpr hy))

/-- Precomposing with `σ` does not change a product over a `σ`-orbit. -/
@[to_additive /-- Precomposing with `σ` does not change a sum over a `σ`-orbit. -/]
theorem prod_filter_sameCycle_comp {M : Type*} [CommMonoid M] [Fintype α]
    [DecidableRel σ.SameCycle] (x : α) (f : α → M) :
    ∏ y with σ.SameCycle y x, f (σ y) = ∏ y with σ.SameCycle y x, f y :=
  Finset.prod_equiv σ (fun _ => by simp [sameCycle_apply_left]) fun _ _ => rfl

/-- Finitely many pairs `u i`, `v i`, each in a single orbit of `σ`, are joined along the
orbits with weights `a i`: some `c : α → M` has difference `z ↦ c (σ⁻¹ z) - c z` equal to
`∑ i, Pi.single (v i) (a i) - ∑ i, Pi.single (u i) (a i)`. -/
theorem exists_comp_symm_sub_eq_sum [DecidableEq α] {ι M : Type*} [Fintype ι] [AddCommGroup M]
    {σ : Perm α} {u v : ι → α} (h : ∀ i, σ.SameCycle (u i) (v i)) (a : ι → M) :
    ∃ c : α → M, (fun z => c (σ.symm z) - c z) =
      ∑ i, Pi.single (v i) (a i) - ∑ i, Pi.single (u i) (a i) := by
  choose c hc using fun i => (h i).exists_comp_symm_sub_eq (a i)
  refine ⟨∑ i, c i, funext fun z => ?_⟩
  simp only [Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => congrFun (hc i) z

/-- A permutation commuting with a cycle can be corrected by a power of that cycle to fix its
support pointwise, without changing it outside the support. -/
theorem IsCycle.exists_mul_zpow_inv_apply_eq_of_commute [Fintype α] [DecidableEq α]
    {g t : Perm α} (hgc : g.IsCycle) (htg : Commute t g) :
    ∃ j : ℤ, (∀ z ∈ g.support, (t * (g ^ j)⁻¹) z = z) ∧
      (∀ z ∉ g.support, (t * (g ^ j)⁻¹) z = t z) := by
  obtain ⟨hts, j, hj⟩ := hgc.commute_iff.1 htg
  refine ⟨j, ?_, ?_⟩
  · intro z hz
    have hw : (g ^ j)⁻¹ z ∈ g.support := by rwa [← zpow_neg, zpow_apply_mem_support]
    rw [Perm.mul_apply, ← ofSubtype_subtypePerm_of_mem hts hw, ← hj, ← Perm.mul_apply,
      mul_inv_cancel, Perm.one_apply]
  · intro z hz
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq.2 (zpow_apply_eq_self_of_apply_eq_self
      (notMem_support.1 hz) j).symm]

/-- Transporting a permutation along an equivalence transports its cycles. -/
@[simp]
theorem sameCycle_permCongr {β : Type*} (e : α ≃ β) {x y : α} :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map fun z ↦ by simp⟩
  simpa using h.map (g := e.symm) fun z ↦ by simp

/-- The cycles of a permutation transported along an equivalence are the transported cycles:
two points lie in the same cycle of `e.permCongr σ` exactly when their preimages under `e` lie in
the same cycle of `σ`. -/
theorem sameCycle_permCongr_iff {β : Type*} (e : α ≃ β) {x y : β} :
    (e.permCongr σ).SameCycle x y ↔ σ.SameCycle (e.symm x) (e.symm y) := by
  rw [← sameCycle_permCongr σ e, e.apply_symm_apply, e.apply_symm_apply]

/-- Transporting a permutation along an equivalence transports its cycles on a set: the analogue of
`Equiv.Perm.IsCycleOn.conj` for an equivalence between two types. -/
theorem IsCycleOn.permCongr {σ : Perm α} {β : Type*} (e : α ≃ β) {s : Set α}
    (h : σ.IsCycleOn s) : (e.permCongr σ).IsCycleOn (e '' s) := by
  refine ⟨⟨?_, (e.permCongr σ).injective.injOn, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨σ x, h.1.mapsTo hx, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := h.1.surjOn hx
    exact ⟨e y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (sameCycle_permCongr σ e).2 (h.2 hx hy)

/-- If a two-argument family `F` is invariant under applying `σ` to its first argument together
with `f` to its second, then relabelling the first argument by `σ⁻¹` is the same as precomposing
every member of the family with `f`. -/
theorem apply_inv_eq_comp_of_apply_apply_eq {β γ : Sort*} (F : α → β → γ) (f : β → β)
    (hF : ∀ a b, F (σ a) (f b) = F a b) : (fun a => F (σ⁻¹ a)) = fun a => F a ∘ f := by
  funext a b
  simpa using (hF (σ⁻¹ a) b).symm

open _root_.Finset in
/-- A permutation of a finite type sends as many points from outside `p` into `p` as from
inside `p` out of it. -/
theorem card_filter_not_and_apply_eq [Fintype α] (p : α → Prop) [DecidablePred p] :
    #{x | ¬p x ∧ p (σ x)} = #{x | ¬p (σ x) ∧ p x} := by
  have hσ : #{x | p (σ x)} = #{x | p x} := card_equiv σ fun x ↦ by simp
  have h₁ := card_filter_add_card_filter_not (s := {x | p x}) fun x ↦ p (σ x)
  have h₂ := card_filter_add_card_filter_not (s := {x | p (σ x)}) p
  simp only [filter_filter] at h₁ h₂
  have h₃ : #{x | p (σ x) ∧ p x} = #{x | p x ∧ p (σ x)} := by simp only [and_comm]
  have h₄ : #{x | p x ∧ ¬p (σ x)} = #{x | ¬p (σ x) ∧ p x} := by simp only [and_comm]
  have h₅ : #{x | p (σ x) ∧ ¬p x} = #{x | ¬p x ∧ p (σ x)} := by simp only [and_comm]
  omega

end Equiv.Perm

namespace Equiv

/-- Right multiplication by `a` is a single cycle on the whole group exactly when `a` generates
the group. -/
@[to_additive /-- Right addition of `a` is a single cycle on the whole group exactly when `a`
generates the group. -/]
theorem isCycleOn_mulRight_univ_iff {G : Type*} [Group G] {a : G} :
    (Equiv.mulRight a).IsCycleOn _root_.Set.univ ↔ Subgroup.zpowers a = ⊤ := by
  simp only [Subgroup.eq_top_iff', Subgroup.mem_zpowers_iff]
  refine ⟨fun h y => ?_, fun h => ⟨(Equiv.mulRight a).bijective.bijOn_univ, fun x _ y _ => ?_⟩⟩
  · obtain ⟨k, hk⟩ := h.2 (Set.mem_univ 1) (Set.mem_univ y)
    exact ⟨k, by simpa using hk⟩
  · obtain ⟨k, hk⟩ := h (x⁻¹ * y)
    exact ⟨k, by simp [hk]⟩

end Equiv

namespace Equiv

section CycleQuotient

open Equiv.Perm

/-- An equivalence conjugating two permutations transports their cycle quotients. -/
def sameCycleQuotientCongr {α β : Type*} (e : α ≃ β)
    {σ : Equiv.Perm α} {τ : Equiv.Perm β} (h : τ = e.permCongr σ) :
    Quotient (SameCycle.setoid σ) ≃ Quotient (SameCycle.setoid τ) :=
  Quotient.congr e fun _ _ => by
    rw [h]
    exact (sameCycle_permCongr σ e).symm

/-- Cycle-quotient transport sends a class to the class of its transported representative. -/
@[simp] theorem sameCycleQuotientCongr_mk {α β : Type*} (e : α ≃ β)
    {σ : Equiv.Perm α} {τ : Equiv.Perm β} (h : τ = e.permCongr σ) (x : α) :
    sameCycleQuotientCongr e h (Quotient.mk _ x) = Quotient.mk _ (e x) := (rfl)

/-- Identity conjugacy induces identity transport of cycle quotients. -/
@[simp] theorem Perm.sameCycleQuotientCongr_refl {α : Type*} (σ : Equiv.Perm α) :
    sameCycleQuotientCongr (Equiv.refl α) (σ := σ) (by ext x; simp) =
      Equiv.refl _ := by
  ext q
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Inverting cycle-quotient transport reverses the conjugating equivalence. -/
@[simp] theorem sameCycleQuotientCongr_symm {α β : Type*} (e : α ≃ β)
    {σ : Equiv.Perm α} {τ : Equiv.Perm β} (h : τ = e.permCongr σ) :
    (sameCycleQuotientCongr e h).symm =
      sameCycleQuotientCongr e.symm (by ext x; simp [h]) := by
  ext q
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Transport of cycle quotients respects composition of conjugating equivalences. -/
theorem sameCycleQuotientCongr_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    {σ : Equiv.Perm α} {τ : Equiv.Perm β} {υ : Equiv.Perm γ}
    (he : τ = e.permCongr σ) (hf : υ = f.permCongr τ) :
    (sameCycleQuotientCongr e he).trans (sameCycleQuotientCongr f hf) =
      sameCycleQuotientCongr (e.trans f) (by ext x; simp [hf, he]) := by
  ext q
  induction q using Quotient.inductionOn with
  | _ x => rfl

end CycleQuotient

end Equiv

namespace TauCeti

open Equiv Equiv.Perm

variable {α σ : Type*}

/-- Colourings fixed by a permutation are exactly the colourings of its cycles. -/
def invariantColouringEquiv (π : Perm α) :
    (Quotient (SameCycle.setoid π) → σ) ≃ {f : α → σ // f ∘ π = f} where
  toFun g := ⟨fun a => g (Quotient.mk _ a), funext fun a =>
    congrArg g (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl π a)))⟩
  invFun f := Quotient.lift f.1 fun _ _ h =>
    SameCycle.apply_eq_of_apply_eq h (congrFun f.2)
  left_inv _ := funext fun c => Quotient.inductionOn c fun _ => rfl
  right_inv _ := rfl

/-- The colouring corresponding to a map on cycles evaluates at the cycle containing the point. -/
@[simp]
theorem invariantColouringEquiv_apply_coe (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) (a : α) :
    (invariantColouringEquiv π g : α → σ) a = g (Quotient.mk _ a) :=
  (rfl)

/-- The map on cycles corresponding to an invariant colouring evaluates at a cycle by evaluating
the colouring at any point in that cycle. -/
@[simp]
theorem invariantColouringEquiv_symm_apply (π : Perm α)
    (f : {f : α → σ // f ∘ π = f}) (a : α) :
    (invariantColouringEquiv π).symm f (Quotient.mk _ a) = f.1 a :=
  congrFun (congrArg Subtype.val ((invariantColouringEquiv π).apply_symm_apply f)) a

/-- A function invariant under every permutation in a set `S` is invariant under the whole
subgroup generated by `S`. -/
theorem apply_eq_of_mem_closure {β : Type*} {S : Set (Perm α)} {f : α → β}
    (hS : ∀ g ∈ S, ∀ a, f (g a) = f a) {g : Perm α} (hg : g ∈ Subgroup.closure S) (a : α) :
    f (g a) = f a := by
  induction hg using Subgroup.closure_induction generalizing a with
  | mem g hg => exact hS g hg a
  | one => rfl
  | mul g g' _ _ ih ih' => rw [Perm.mul_apply, ih, ih']
  | inv g _ ih => rw [← ih (g⁻¹ a), Perm.inv_def, apply_symm_apply]

/-- A function invariant under every permutation in a set `S` takes a single value when the
subgroup generated by `S` acts transitively. -/
theorem apply_eq_apply_of_isPretransitive_closure {β : Type*} {S : Set (Perm α)} {f : α → β}
    (hS : ∀ g ∈ S, ∀ a, f (g a) = f a)
    (hconn : MulAction.IsPretransitive (Subgroup.closure S) α) (a b : α) : f a = f b := by
  obtain ⟨g, rfl⟩ := hconn.exists_smul_eq a b
  exact (apply_eq_of_mem_closure hS g.2 a).symm

/-- Precomposing a function with a permutation preserves the cardinality of each fiber. -/
theorem card_filter_comp_perm {ι : Type*} [Fintype α] [DecidableEq ι]
    (f : α → ι) (g : Perm α) (i : ι) :
    (Finset.univ.filter fun a => f (g a) = i).card =
      (Finset.univ.filter fun a => f a = i).card :=
  Finset.card_equiv g fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A transposition of two points outside `s` maps the complement of `s` to itself. -/
theorem swap_apply_notMem {α : Type*} [DecidableEq α] {s : Finset α} {a b z : α}
    (ha : a ∉ s) (hb : b ∉ s) (hz : z ∉ s) : Equiv.swap a b z ∉ s := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

/-- Any ordered pair of distinct points outside `s` can be carried to another such pair by a
permutation fixing `s` pointwise. -/
theorem exists_pair_perm_fixed {α : Type*} {s : Set α}
    {i j i' j' : α} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hi : i ∉ s) (hj : j ∉ s) (hi' : i' ∉ s) (hj' : j' ∉ s) :
    ∃ perm : Equiv.Perm α, (∀ a ∈ s, perm a = a) ∧ perm i = i' ∧ perm j = j' := by
  classical
  let τ := Equiv.swap i i'
  let υ := Equiv.swap (τ j) j'
  have hτs (a : α) (ha : a ∈ s) : τ a = a :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ ha)) (fun h => hi' (h ▸ ha))
  have hτj : τ j ∉ s := by
    by_cases hji' : j = i'
    · simpa [τ, hji'] using hi
    · simpa [τ, Equiv.swap_apply_of_ne_of_ne hij.symm hji'] using hj
  have hτji' : τ j ≠ i' := by
    intro h
    exact hij (τ.injective ((Equiv.swap_apply_left i i').trans h.symm))
  refine ⟨τ.trans υ, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Equiv.trans_apply]
    rw [hτs a ha]
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hτj (h ▸ ha)) (fun h => hj' (h ▸ ha))
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hτji'.symm hi'j'
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

/-- Two points lie in the same orbit of an involution exactly when they are equal or one is the
image of the other. -/
theorem sameCycle_toPerm_iff {α : Type*} (f : α → α) (hf : Function.Involutive f) (a b : α) :
    (hf.toPerm f).SameCycle a b ↔ a = b ∨ a = f b := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.symm
    rcases Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self
      (f := hf.toPerm f) (x := b) (hf b) i with h | h
    · exact Or.inl (hi.symm.trans h)
    · exact Or.inr (hi.symm.trans h)
  · rintro (rfl | h)
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      have : f a = b := by
        calc
          f a = f (f b) := congrArg f h
          _ = b := hf b
      simpa using this

/-- Two points of an involutive permutation lie in one cycle exactly when they coincide or
one is the image of the other. -/
theorem _root_.Function.Involutive.sameCycle_iff {α : Type*} {f : Equiv.Perm α}
    (hf : Function.Involutive f) (x y : α) :
    f.SameCycle x y ↔ x = y ∨ x = f y := by
  have he : Function.Involutive.toPerm f hf = f := Equiv.ext fun _ ↦ rfl
  exact he ▸ sameCycle_toPerm_iff _ hf x y

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation moves all but one point exactly when it has a unique fixed point. -/
theorem card_support_add_one_eq_card_iff_existsUnique_fixedPoint (σ : Equiv.Perm α) :
    σ.support.card + 1 = Fintype.card α ↔ ∃! x : α, σ x = x := by
  have hfixed : (∃! x : α, x ∈ σ.supportᶜ) ↔ ∃! x : α, σ x = x := by
    simp only [Finset.mem_compl, Equiv.Perm.notMem_support]
  rw [← hfixed, ← Finset.card_eq_one_iff_existsUnique, Finset.card_compl]
  omega

/-- Whenever `a` and `c` are both distinct from `b`, the transpositions `(a b)` and `(b c)`
satisfy the braid relation. The two points `a` and `c` need not be distinct: for `a = c` both
sides are `(a b)`. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hcb : c ≠ b) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  rcases eq_or_ne a c with rfl | hac
  · rw [Equiv.swap_comm b a]
  · calc Equiv.swap a b * Equiv.swap b c * Equiv.swap a b
        = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
          rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
      _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hcb (Ne.symm hac)
      _ = Equiv.swap c a := Equiv.swap_comm a c
      _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
          (Equiv.swap_mul_swap_mul_swap hab hac).symm

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `a` to `b`. Together with `TauCeti.swap_mul_swap_apply_middle` and
`TauCeti.swap_mul_swap_apply_right` this evaluates that product, which for three distinct points
is the three-cycle `a ↦ b ↦ c ↦ a`, at each of the three points it moves. -/
@[simp]
theorem swap_mul_swap_apply_left {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hca : c ≠ a) : (Equiv.swap a b * Equiv.swap b c) a = b := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hca.symm, Equiv.swap_apply_left]

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `b` to `c`, the point the second transposition moves it to. -/
@[simp]
theorem swap_mul_swap_apply_middle {α : Type*} [DecidableEq α] {a b c : α} (hca : c ≠ a)
    (hcb : c ≠ b) : (Equiv.swap a b * Equiv.swap b c) b = c := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `c` to `a`, through the shared point `b`; no distinctness is needed for this value. -/
@[simp]
theorem swap_mul_swap_apply_right {α : Type*} [DecidableEq α] (a b c : α) :
    (Equiv.swap a b * Equiv.swap b c) c = a := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]

/-- **A permutation along an injection extends to a permutation of the ambient type.** Given an
injection `e : α → γ`, every permutation `σ` of `α` is realized along `e` by some
`ρ : Equiv.Perm γ`. This is `Equiv.Perm.viaEmbedding` stated in terms of the underlying function
of the injection, which is the form a consumer reindexing along `e` needs. -/
theorem exists_perm_apply_eq {α γ : Type*} {e : α → γ} (he : Function.Injective e)
    (σ : Equiv.Perm α) : ∃ ρ : Equiv.Perm γ, ∀ a, ρ (e a) = e (σ a) :=
  ⟨σ.viaEmbedding ⟨e, he⟩, fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a⟩

/-- **Two permutations along disjoint injections extend to one permutation of the ambient type.**
Given injections `e : α → γ` and `f : β → γ` with disjoint ranges, every pair of permutations
`σ` of `α` and `τ` of `β` is realized by a single `ρ : Equiv.Perm γ` which acts as `σ` along `e`
and as `τ` along `f`. -/
theorem exists_perm_apply_eq_of_disjoint_range {α β γ : Type*} {e : α → γ} {f : β → γ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    ∃ ρ : Equiv.Perm γ, (∀ a, ρ (e a) = e (σ a)) ∧ ∀ b, ρ (f b) = f (τ b) := by
  -- `Function.Embedding.coeFn_mk` is what carries a statement about the bundled embedding
  -- `⟨e, he⟩` over to the function `e` it is built from.
  have hrange_e : Set.range (⟨e, he⟩ : α ↪ γ) = Set.range e := by
    rw [Function.Embedding.coeFn_mk]
  have hrange_f : Set.range (⟨f, hf⟩ : β ↪ γ) = Set.range f := by
    rw [Function.Embedding.coeFn_mk]
  have hone : ∀ a, σ.viaEmbedding ⟨e, he⟩ (e a) = e (σ a) :=
    fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a
  have htwo : ∀ b, τ.viaEmbedding ⟨f, hf⟩ (f b) = f (τ b) :=
    fun b => Equiv.Perm.viaEmbedding_apply (ι := ⟨f, hf⟩) τ b
  refine ⟨σ.viaEmbedding ⟨e, he⟩ * τ.viaEmbedding ⟨f, hf⟩, fun a => ?_, fun b => ?_⟩
  · have hmem : e a ∉ Set.range (⟨f, hf⟩ : β ↪ γ) :=
      hrange_f ▸ Set.disjoint_left.mp hd ⟨a, rfl⟩
    rw [Equiv.Perm.mul_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨f, hf⟩) _ _ hmem, hone]
  · have hmem : f (τ b) ∉ Set.range (⟨e, he⟩ : α ↪ γ) :=
      hrange_e ▸ Set.disjoint_right.mp hd ⟨τ b, rfl⟩
    rw [Equiv.Perm.mul_apply, htwo,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨e, he⟩) _ _ hmem]

/-- **Families with the same equality pattern are related by a fiber-preserving permutation.**
If two finite families `a b : ι → β` have the same pattern of equalities between their entries,
and corresponding entries lie in the same fiber of `c : β → γ`, then some permutation of `β`
preserving every fiber of `c` carries `a` to `b`. Repeated entries are allowed, and `β` may be
infinite. With `c` constant this is a permutation of `β` carrying `a` to `b`. -/
theorem exists_perm_apply_eq_of_eq_iff {ι β γ : Type*} [Finite ι] (c : β → γ) {a b : ι → β}
    (hab : ∀ i j, a i = a j ↔ b i = b j) (hc : ∀ i, c (a i) = c (b i)) :
    ∃ σ : Equiv.Perm β, (∀ x, c (σ x) = c x) ∧ ∀ i, σ (a i) = b i := by
  classical
  -- The entries of `b`, read as a function of the entries of `a`.
  let g : Set.range a → β := fun x => b x.2.choose
  have hg (i : ι) : g ⟨a i, i, rfl⟩ = b i :=
    (hab _ _).mp (⟨a i, i, rfl⟩ : Set.range a).2.choose_spec
  have hg_inj : Function.Injective g := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hij
    rw [hg, hg] at hij
    exact Subtype.ext ((hab i j).mpr hij)
  have hcg (x : Set.range a) : c (g x) = c x := by
    obtain ⟨_, i, rfl⟩ := x
    rw [hg, hc]
  -- Extend `g` separately on each fiber of `c`.
  have hfiber (k : γ) : ∃ τ : Equiv.Perm {y // c y = k},
      ∀ x : {x : Set.range a // c x = k}, (τ ⟨x.1, x.2⟩ : β) = g x.1 := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair
      (fun x : {x : Set.range a // c x = k} => (⟨x.1, x.2⟩ : {y // c y = k}))
      (fun x => ⟨g x.1, (hcg x.1).trans x.2⟩)
      (fun _ _ hxy => Subtype.ext (Subtype.ext (Subtype.mk.inj hxy)))
      (fun _ _ hxy => Subtype.ext (hg_inj (Subtype.mk.inj hxy)))
    exact ⟨τ, fun x => congrArg Subtype.val (hτ x)⟩
  choose τ hτ using hfiber
  refine ⟨Equiv.ofFiberEquiv τ, Equiv.ofFiberEquiv_map τ, fun i => ?_⟩
  exact (hτ (c (a i)) ⟨⟨a i, i, rfl⟩, rfl⟩).trans (hg i)

/-- Alternating a signed sum over the permutations of `α` a second time, along any
sign-preserving map `ext` from the permutations of `β`, only multiplies it by the number of
permutations of `β`. With `ext` the
extension of permutations of a block of indices by the identity, this is the statement that the
alternatization of a partially alternatized multilinear map is a multiple of the alternatization. -/
theorem sum_sign_smul_sum_sign_smul_eq_card_nsmul {β M : Type*} [Fintype β] [DecidableEq β]
    [AddCommGroup M] (ext : Perm β → Perm α) (hext : ∀ τ, sign (ext τ) = sign τ)
    (T : Perm α → M) :
    ∑ σ : Perm α, sign σ • ∑ τ : Perm β, sign τ • T (σ * ext τ) =
      Fintype.card (Perm β) • ∑ σ : Perm α, sign σ • T σ := by
  rw [← Finset.card_univ, ← Finset.sum_const]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight (ext τ)) _ _ fun σ => ?_
  rw [Equiv.coe_mulRight, Equiv.Perm.sign_mul, hext, mul_smul, smul_comm]

/-- Expansion of a signed sum over the permutations of `Fin (n + 1)` along the slot that receives
the first entry: rearranging `Fin.cons x w` by all permutations is the same as inserting `x` at
each position `j`, with sign `(-1) ^ j`, into all rearrangements of `w`. Applied to the summand of
an alternatization, this expands the alternatization along its first argument, in the manner of
the Laplace expansion of a determinant along a column. -/
theorem sum_sign_smul_cons_comp_eq_sum_insertNth {α M : Type*} [AddCommGroup M] {n : ℕ}
    (g : (Fin (n + 1) → α) → M) (x : α) (w : Fin n → α) :
    ∑ σ : Perm (Fin (n + 1)), sign σ • g (Fin.cons x w ∘ σ) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ τ : Perm (Fin n), sign τ • g (j.insertNth x (w ∘ τ)) := by
  cases n with
  | zero => simp [Fin.insertNth_zero']
  | succ n =>
  -- Reindex by Mathlib's `decomposeFin'`: `(decomposeFin'Symm j τ⁻¹)⁻¹` sends `j` to `0` and
  -- `j.succAbove m` to `(τ m).succ`, so it rearranges `Fin.cons x w` into
  -- `j.insertNth x (w ∘ τ)`, and its sign is `(-1) ^ j * sign τ`.
  symm
  simp_rw [Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodCongr (Equiv.refl _) (Equiv.inv _)).trans
    (decomposeFin'.symm.trans (Equiv.inv _))) _ _ fun ⟨j, τ⟩ => ?_
  have hcomp : Fin.cons x w ∘ ⇑((decomposeFin'Symm j τ⁻¹)⁻¹) = j.insertNth x (w ∘ τ) := by
    rw [Fin.eq_insertNth_iff]
    refine ⟨by simp, funext fun m => ?_⟩
    have : (decomposeFin'Symm j τ⁻¹)⁻¹ (j.succAbove m) = (τ m).succ :=
      Perm.inv_eq_iff_eq.mpr (by simp)
    simp only [Fin.removeNth, Function.comp_apply, this, Fin.cons_succ]
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq,
    Equiv.inv_apply, decomposeFin'_symm]
  rw [hcomp, Perm.sign_inv, sign_decomposeFin'Symm, Perm.sign_inv, mul_smul]
  simp [Units.smul_def]

/-- Expansion of a signed sum over the permutations of `Fin (n + 1)` along the entry moved to the
front: rearranging `w` by all permutations is the same as moving each entry `w j` to the front,
with sign `(-1) ^ j`, followed by all rearrangements of the remaining entries `j.removeNth w`.
This is the expansion of an alternatization along the entry placed in its first argument. -/
theorem sum_sign_smul_comp_eq_sum_cons_removeNth {α M : Type*} [AddCommGroup M] {n : ℕ}
    (g : (Fin (n + 1) → α) → M) (w : Fin (n + 1) → α) :
    ∑ σ : Perm (Fin (n + 1)), sign σ • g (w ∘ σ) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ τ : Perm (Fin n), sign τ • g (Fin.cons (w j) (j.removeNth w ∘ τ)) := by
  cases n with
  | zero =>
    -- Both permutation groups are trivial and `Fin.cons (w 0) (Fin.removeNth 0 w) = w`.
    have h1 : ∀ σ : Perm (Fin (0 + 1)), σ = 1 := fun σ => Equiv.ext fun i => Fin.ext (by omega)
    rw [Fintype.sum_eq_single 1 (fun σ hσ => (hσ (h1 σ)).elim), Fin.sum_univ_one,
      Fintype.sum_eq_single 1 (fun σ hσ => (hσ (Subsingleton.elim _ _)).elim)]
    simp only [Perm.sign_one, Perm.coe_one, Function.comp_id, one_smul, Fin.val_zero, pow_zero]
    congr 1
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  | succ n =>
  -- Reindex by Mathlib's `decomposeFin'`: `decomposeFin'Symm j τ` sends `0` to `j` and `m.succ`
  -- to `j.succAbove (τ m)`, so it rearranges `w` into `Fin.cons (w j) (j.removeNth w ∘ τ)`,
  -- and its sign is `(-1) ^ j * sign τ`.
  simp_rw [Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_equiv decomposeFin'.symm _ _ fun ⟨j, τ⟩ => ?_
  have hcomp : w ∘ decomposeFin'Symm j τ = Fin.cons (w j) (j.removeNth w ∘ τ) := by
    funext m
    cases m using Fin.cases <;> simp [Fin.removeNth]
  rw [decomposeFin'_symm, hcomp, sign_decomposeFin'Symm, mul_smul]
  simp [Units.smul_def]

/-- Expansion of a signed sum over the permutations of `Fin (n + 1)` along the entry moved to an
arbitrary slot `p`: rearranging `w` by all permutations is, up to the sign `(-1) ^ p`, the same as
inserting each entry `w j` at `p`, with sign `(-1) ^ j`, into all rearrangements of the remaining
entries `j.removeNth w`. -/
theorem sum_sign_smul_comp_eq_sum_insertNth_removeNth {α M : Type*} [AddCommGroup M] {n : ℕ}
    (g : (Fin (n + 1) → α) → M) (w : Fin (n + 1) → α) (p : Fin (n + 1)) :
    ∑ σ : Perm (Fin (n + 1)), sign σ • g (w ∘ σ) =
      (-1 : ℤ) ^ (p : ℕ) • ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ τ : Perm (Fin n), sign τ • g (p.insertNth (w j) (j.removeNth w ∘ τ)) := by
  -- Precomposing with `p.cycleRange` moves the front slot to `p` and costs the sign `(-1) ^ p`.
  have h := sum_sign_smul_comp_eq_sum_cons_removeNth (fun u => g (u ∘ p.cycleRange)) w
  simp only [Function.comp_assoc, Fin.cons_comp_cycleRange] at h
  rw [← h, ← Fintype.sum_equiv (Equiv.mulRight p.cycleRange)
    (fun σ => sign (σ * p.cycleRange) • g (w ∘ ⇑(σ * p.cycleRange))) _ fun σ => rfl]
  simp only [Equiv.Perm.sign_mul, Fin.sign_cycleRange, Perm.coe_mul, mul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_comm, Units.smul_def ((-1) ^ (p : ℕ))]
  simp

end TauCeti

/-! ### Removing a transposition from an involution -/

namespace Function.Involutive

open Equiv (Perm)

variable {α : Type*} [DecidableEq α] {σ : Perm α}

/-- Removing the pair `{a, σ a}` from an involution `σ` fixes its two points and keeps every other
pair: `Equiv.swap a (σ a) * σ` agrees with `σ` away from `a` and `σ a`. -/
theorem swap_mul_apply_eq_self_or (hσ : Function.Involutive σ) (a x : α) :
    ((x = a ∨ x = σ a) ∧ (Equiv.swap a (σ a) * σ) x = x) ∨
      (x ≠ a ∧ x ≠ σ a ∧ (Equiv.swap a (σ a) * σ) x = σ x) := by
  by_cases hxa : x = a
  · subst hxa
    simp
  by_cases hxc : x = σ a
  · subst hxc
    simp [hσ a]
  refine Or.inr ⟨hxa, hxc, Equiv.swap_apply_of_ne_of_ne ?_ ?_⟩
  · exact fun h => hxc (by rw [← h, hσ x])
  · exact fun h => hxa (σ.injective h)

/-- Removing a pair `{a, σ a}` from an involution `σ` leaves an involution. -/
theorem swap_mul (hσ : Function.Involutive σ) (a : α) :
    Function.Involutive (Equiv.swap a (σ a) * σ) := by
  intro x
  rcases hσ.swap_mul_apply_eq_self_or a x with ⟨-, hx⟩ | ⟨hxa, hxc, hx⟩
  · rw [hx, hx]
  rcases hσ.swap_mul_apply_eq_self_or a (σ x) with ⟨hy, -⟩ | ⟨-, -, hy⟩
  · rcases hy with hy | hy
    · exact (hxc (by rw [← hy, hσ x])).elim
    · exact (hxa (σ.injective hy)).elim
  · rw [hx, hy, hσ x]

/-- Putting a removed pair back: `σ = (Equiv.swap a (σ a) * σ) * Equiv.swap a (σ a)` for an
involution `σ`. -/
theorem swap_mul_mul_swap (hσ : Function.Involutive σ) (a : α) :
    Equiv.swap a (σ a) * σ * Equiv.swap a (σ a) = σ := by
  rw [mul_assoc, Equiv.mul_swap_eq_swap_mul, hσ a, Equiv.swap_comm, Equiv.swap_mul_self_mul]

end Function.Involutive
end
end TAF_LiteralSource_0166

