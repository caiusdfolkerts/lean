module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Group.Subgroup.Defs

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# The relative incidence complex of forbidden chart tuples

This is the general finite-incidence construction from the introductory
section of BondalThomsen's CechNegativeSupportComparison, with its namespace
separated from the old complete-fan wrappers. The differential is the actual
alternating coface differential. No nerve or cohomology equivalence is
asserted by these definitions.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace ToricPower.NegativeSupportCech

variable {Ray : Type*} {Chart : Type}

def tupleForbidden (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : Prop :=
  ∃ ray, negative ray ∧ ∀ column, incidence ray (tuple column)

theorem tupleForbidden_precomp (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Chart)
    (forbidden : tupleForbidden incidence negative next tuple) :
    tupleForbidden incidence negative degree (tuple ∘ selection) := by
  obtain ⟨ray, negativeRay, contains⟩ := forbidden
  exact ⟨ray, negativeRay, fun column => contains (selection column)⟩

def negativeChartComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    PreAbstractSimplicialComplex Chart where
  faces := {face | face.Nonempty ∧ ∃ ray, negative ray ∧
    ∀ chart ∈ face, incidence ray chart}
  isRelLowerSet_faces := by
    intro face member
    refine ⟨member.1, ?_⟩
    intro smaller subset nonempty
    obtain ⟨ray, negativeRay, contains⟩ := member.2
    exact ⟨nonempty, ray, negativeRay, fun chart present => contains chart (subset present)⟩

theorem tupleForbidden_iff_face (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) (tuple : Fin (degree + 1) → Chart) :
    tupleForbidden incidence negative degree tuple ↔
      Finset.univ.image tuple ∈ negativeChartComplex incidence negative := by
  constructor
  · rintro ⟨ray, negativeRay, contains⟩
    refine ⟨⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩,
      ray, negativeRay, ?_⟩
    intro chart present
    obtain ⟨column, _, rfl⟩ := Finset.mem_image.mp present
    exact contains column
  · rintro ⟨_, ray, negativeRay, contains⟩
    exact ⟨ray, negativeRay, fun column =>
      contains (tuple column) (Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩)⟩

def relativeScalarCoefficient (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : AddSubgroup 𝕜 where
  carrier := {scalar | tupleForbidden incidence negative degree tuple → scalar = 0}
  zero_mem' := fun _ => rfl
  add_mem' := fun first second forbidden => by rw [first forbidden, second forbidden, zero_add]
  neg_mem' := fun scalar forbidden => by rw [scalar forbidden, neg_zero]

noncomputable def relativeCoefficient (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : AddCommGrpCat :=
  AddCommGrpCat.of (relativeScalarCoefficient 𝕜 incidence negative degree tuple)

noncomputable def relativeDegree (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) : AddCommGrpCat :=
  ∏ᶜ (relativeCoefficient 𝕜 incidence negative degree)

def relativeScalarRestriction (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Chart) :
    relativeScalarCoefficient 𝕜 incidence negative degree (tuple ∘ selection) →+
      relativeScalarCoefficient 𝕜 incidence negative next tuple where
  toFun scalar := ⟨scalar.val, fun forbidden => scalar.property
    (tupleForbidden_precomp incidence negative selection tuple forbidden)⟩
  map_zero' := rfl
  map_add' _first _second := rfl

noncomputable def relativeTupleMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1)) :
    relativeDegree 𝕜 incidence negative degree ⟶ relativeDegree 𝕜 incidence negative next :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (relativeCoefficient 𝕜 incidence negative degree) (tuple ∘ selection) ≫
      AddCommGrpCat.ofHom (relativeScalarRestriction 𝕜 incidence negative selection tuple))

noncomputable def relativeCosimplicial (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : CosimplicialObject AddCommGrpCat where
  obj simplex := relativeDegree 𝕜 incidence negative simplex.len
  map selection := relativeTupleMap 𝕜 incidence negative selection.toOrderHom
  map_id simplex := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [relativeTupleMap, Limits.Pi.lift_comp_π, Category.id_comp]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl
  map_comp first second := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [relativeTupleMap, Category.assoc, Limits.Pi.lift_comp_π]
    rw [← Category.assoc, Limits.Pi.lift_comp_π]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

noncomputable def relativeComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    CochainComplex AddCommGrpCat ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (relativeCosimplicial 𝕜 incidence negative)

theorem relativeComplex_d (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) :
    (relativeComplex 𝕜 incidence negative).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        relativeTupleMap 𝕜 incidence negative deleted.succAbove := by
  simp only [relativeComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d]
  rfl

end ToricPower.NegativeSupportCech

