module

public import ToricPower.LinearVectorCopower
public import ToricPower.ArrangementCellularComplex

/-!
# Actual covariant labels for cellular realization

A covariant object diagram `Q` and a covariant vector-space diagram `F`
give a diagram of actual vector copowers `Q(c) ⊗ₖ F(c)`. Both factors of
every incidence map are retained. Applying the genuine arrangement
cellular cochain functor defines the finite cellular realization used in
the comparison with the derived coend.

This is a construction of complexes and natural maps. It does not assert
the representable comparison or geometric reconstruction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe v u

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} B]
  (Q : C ⥤ B) (F : C ⥤ ModuleCat.{u} k)

/-- Both literal coefficient maps act on each incidence. -/
def covariantCopowerDiagram : C ⥤ B where
  obj c := vectorCopower k (Q.obj c) (F.obj c)
  map {c d} f :=
    vectorCopowerMapObject k (Q.map f) (F.obj c) ≫
      (vectorCopowerFunctor k (Q.obj d)).map (F.map f)
  map_id c := by
    apply vectorCopower_hom_ext k (Q.obj c) (F.obj c)
    intro x
    simp only [Category.assoc, vectorCopowerInclusion_mapObject_assoc,
      vectorCopowerInclusion_map, Functor.map_id,
      ModuleCat.id_apply, Category.id_comp, Category.comp_id]
    rw [Q.map_id, F.map_id]
    simp only [ModuleCat.id_apply, Category.id_comp]
  map_comp {c d e} f g := by
    apply vectorCopower_hom_ext k (Q.obj c) (F.obj c)
    intro x
    simp only [Functor.map_comp, Category.assoc,
      vectorCopowerInclusion_mapObject_assoc, vectorCopowerInclusion_map_assoc,
      vectorCopowerInclusion_map, ConcreteCategory.comp_apply]

@[reassoc]
theorem covariantCopowerDiagram_map_inclusion {c d : C} (f : c ⟶ d) (x : F.obj c) :
    vectorCopowerInclusion k (Q.obj c) (F.obj c) x ≫
        (covariantCopowerDiagram k Q F).map f =
      Q.map f ≫ vectorCopowerInclusion k (Q.obj d) (F.obj d) (F.map f x) := by
  simp only [covariantCopowerDiagram, Category.assoc,
    vectorCopowerInclusion_mapObject_assoc, vectorCopowerInclusion_map]

variable {F} {G : C ⥤ ModuleCat.{u} k} (α : F ⟶ G)

/-- A natural map of the original vector diagrams induces the actual
natural map of the copower-labelled diagrams. -/
def covariantCopowerMap :
    covariantCopowerDiagram k Q F ⟶ covariantCopowerDiagram k Q G where
  app c := (vectorCopowerFunctor k (Q.obj c)).map (α.app c)
  naturality {c d} f := by
    apply vectorCopower_hom_ext k (Q.obj c) (F.obj c)
    intro x
    rw [← Category.assoc, covariantCopowerDiagram_map_inclusion,
      Category.assoc, vectorCopowerInclusion_map,
      ← Category.assoc, vectorCopowerInclusion_map,
      covariantCopowerDiagram_map_inclusion]
    congr 2
    exact ConcreteCategory.congr_hom (α.naturality f) x

/-- The actual covariant copower construction is functorial in every
vector diagram, not merely in finite-dimensional ones. -/
def covariantCopowerFunctor : (C ⥤ ModuleCat.{u} k) ⥤ (C ⥤ B) where
  obj := covariantCopowerDiagram k Q
  map := covariantCopowerMap k Q
  map_id F := by
    ext c
    exact (vectorCopowerFunctor k (Q.obj c)).map_id (F.obj c)
  map_comp α β := by
    ext c
    exact (vectorCopowerFunctor k (Q.obj c)).map_comp (α.app c) (β.app c)

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

universe v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {B : Type v} [Category.{0} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  (Q : IncidenceObject A ⥤ B)

/-- The actual finite cellular realization, with all incidence maps and
arbitrary vector coefficients. This is the literal `A_cell` complex. -/
def arrangementCellularRealization :
    (IncidenceObject A ⥤ ModuleCat.{0} k) ⥤ CochainComplex B ℕ :=
  Cellular.covariantCopowerFunctor k Q ⋙ arrangementCellularCochainFunctor A k

/-- Its finite length is the actual ambient dimension, regardless of
the dimensions of the input vector spaces. -/
theorem arrangementCellularRealization_isZero_X_above
    (F : IncidenceObject A ⥤ ModuleCat.{0} k) (q : ℕ) (above : n < q) :
    IsZero (((arrangementCellularRealization A k Q).obj F).X q) :=
  arrangementCellularCochainComplex_isZero_X_above A k
    (Cellular.covariantCopowerDiagram k Q F) q above

end ToricPower.IntegralArrangement
