module

public import ToricPower.ArrangementUniversalCells
public import ToricPower.CellularPointSupport

/-!
# The actual finite face star at a maximal support cell

The face category consists of the genuine closed polyhedra of the
universal arrangement. Its upper star is finite by local finiteness in
the ambient topology. Strict face incidences strictly raise the actual
cell dimension. Consequently a maximal cohomological support cell has
an unbounded, chain-level point-supported model on this exact star.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A

/-- The integral walls and active equalities uniquely recover the
actual cell, including its intrinsic dimension. -/
theorem universalIncidenceLabels_injective :
    Function.Injective (fun c : U => c.2.val) := by
  rintro ⟨p,c⟩ ⟨q,d⟩ h
  have active : c.val.2 = d.val.2 := congrArg Prod.snd h
  have hpq : p = q := by
    rw [← c.property.2, ← d.property.2, active]
  subst q
  have hcd : c = d := Subtype.ext h
  subst d
  rfl

/-- Literal inclusion of closed cells weakly increases dimension. -/
theorem universalIncidence_dimension_le {c d : U} (h : c ≤ d) : c.1 ≤ d.1 := by
  obtain ⟨x,hx⟩ := c.2.property.1
  have hxd := h (cell_subset_closedCell _ _ _ hx)
  by_cases hopen : x ∈ cell (augmentedForms A) d.2.val.1 d.2.val.2
  · have active := (cell_indices_unique (augmentedForms A) hx hopen).2
    have dims : c.1 = d.1 := by
      rw [← c.2.property.2, ← d.2.property.2, active]
    exact dims.le
  · obtain ⟨y,hy⟩ := d.2.property.1
    have dims := boundary_finrank_lt (augmentedForms A) d.2.val.1 d.2.val.2 hy hxd hopen
    rw [integralIndices_eq_of_mem_cell _ _ _ hx, c.2.property.2, d.2.property.2] at dims
    exact dims.le

/-- Equal-dimensional containment is equality of actual universal cells. -/
theorem universalIncidence_eq_of_dimension_eq {c d : U}
    (h : c ≤ d) (dims : c.1 = d.1) : c = d := by
  rcases c with ⟨p,c⟩
  rcases d with ⟨q,d⟩
  change p = q at dims
  subst q
  have same : c = d := cell_subset_closedCell_same_dimension A c d h
  subst d
  rfl

theorem universalIncidence_antisymm {c d : U} (h : c ≤ d) (h' : d ≤ c) : c = d :=
  universalIncidence_eq_of_dimension_eq A h
    (le_antisymm (universalIncidence_dimension_le A h) (universalIncidence_dimension_le A h'))

theorem universalIncidence_dimension_lt {c d : U} (h : c ≤ d) (hne : c ≠ d) :
    c.1 < d.1 :=
  lt_of_le_of_ne (universalIncidence_dimension_le A h)
    (fun dims => hne (universalIncidence_eq_of_dimension_eq A h dims))

/-- The exact local face star, with the actual geometric face order. -/
def UniversalFaceStar (c : U) := {d : U // c ≤ d}

/-- Local finiteness of the real arrangement proves finiteness of this
star; no artificial bound on lattice translates is imposed. -/
instance universalFaceStar_finite (c : U) : Finite (UniversalFaceStar A c) := by
  let x := cellCenter (augmentedForms A) c.2
  have hloc : LocallyFinite (universalIncidenceClosedCell A) :=
    (closedCells_locallyFinite (augmentedForms A)
      (fun i => (augmentedForms A i).continuous_of_finiteDimensional)).comp_injective
        (universalIncidenceLabels_injective A)
  have finite : {d : U | c ≤ d}.Finite := (hloc.point_finite x).subset (by
    intro d hd
    exact hd (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2)))
  exact finite.to_subtype

instance universalFaceStar_preorder (c : U) : Preorder (UniversalFaceStar A c) :=
  inferInstanceAs (Preorder {d : U // c ≤ d})

/-- The chosen cell is the genuine least element of its face star. -/
def universalFaceStarPoint (c : U) : UniversalFaceStar A c := ⟨c, le_rfl⟩

def universalFaceStarInclusion (c : U) : UniversalFaceStar A c ⥤ U where
  obj d := d.val
  map f := homOfLE f.le

theorem universalFaceStar_incoming (c : U) (d : UniversalFaceStar A c)
    (hne : d ≠ universalFaceStarPoint A c) :
    IsEmpty (d ⟶ universalFaceStarPoint A c) :=
  ⟨fun f => hne (Subtype.ext (universalIncidence_antisymm A f.le d.property))⟩

variable (k : Type) [Field k]

/-- Restriction of an actual module diagram to the literal local face star. -/
def universalFaceStarRestriction (c : U) :
    (U ⥤ ModuleCat.{0} k) ⥤ UniversalFaceStar A c ⥤ ModuleCat.{0} k :=
  (Functor.whiskeringLeft (UniversalFaceStar A c) U (ModuleCat.{0} k)).obj
    (universalFaceStarInclusion A c)

instance universalFaceStarRestriction_additive (c : U) :
    (universalFaceStarRestriction A k c).Additive := by
  unfold universalFaceStarRestriction
  infer_instance

/-- The dimension range alone supplies a maximal cohomological support
cell, even for an unbounded complex on infinitely many universal cells. -/
theorem exists_maximal_cohomological_support
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ)
    (nonzero : ∃ c : U, ¬ (K.asFunctor.obj c).Acyclic) :
    ∃ c : U, ¬ (K.asFunctor.obj c).Acyclic ∧
      ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1 := by
  classical
  let P : ℕ → Prop := fun q => ∃ c : U, ¬ (K.asFunctor.obj c).Acyclic ∧ c.1 = q
  obtain ⟨c₀,hc₀⟩ := nonzero
  have maximal : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (cell_dimension_le A c₀.2) ⟨c₀,hc₀,rfl⟩
  obtain ⟨c,hc,dim⟩ := maximal
  refine ⟨c,hc,fun d hd => ?_⟩
  rw [dim]
  exact Nat.le_findGreatest (cell_dimension_le A d.2) ⟨d,hd,rfl⟩

/-- The actual local restriction of a maximal support complex is
quasi-isomorphic to the coinduced coefficient at that cell. The map is
the literal evaluation unit and therefore retains all face naturality. -/
theorem maximalSupport_pointComplexUnit_quasiIso
    (K : CochainComplex (U ⥤ ModuleCat.{0} k) ℤ) (c : U)
    (maximal : ∀ d : U, ¬ (K.asFunctor.obj d).Acyclic → d.1 ≤ c.1) :
    QuasiIso (Cellular.pointComplexUnit k (.up ℤ) (universalFaceStarPoint A c)
      (((universalFaceStarRestriction A k c).mapHomologicalComplex (.up ℤ)).obj K)) := by
  apply Cellular.pointComplexUnit_quasiIso
    _ _ _ (universalFaceStar_incoming A c)
  intro d hd
  change (K.asFunctor.obj d.val).Acyclic
  by_contra hnonzero
  have different : c ≠ d.val := by
    intro same
    exact hd (Subtype.ext same.symm)
  exact (not_lt_of_ge (maximal d.val hnonzero))
    (universalIncidence_dimension_lt A d.property different)

end ToricPower.IntegralArrangement

end
