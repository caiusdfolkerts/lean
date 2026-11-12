module

public import ToricPower.ArrangementCostalkPair
public import ToricPower.ArrangementEquivariant
public import ToricPower.ConvexComplementTopClass
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Cellular homology of the literal periodic costalk pair

The relative CW structure uses the lattice-periodic characteristic maps
of the original arrangement. Its base is the complement of the actual
costalk region. The cellular–singular comparison, followed by the actual
identification of the ambient carrier with Euclidean space, computes the
homology of this complex. All coefficients remain in `ModuleCat k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower

universe w v u

/-- Relative singular homology transports along an actual isomorphism
of topological pairs, by the actual maps in both directions. -/
def topPairHomologyIso {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
    {P Q : TopPair.{w}} (e : P ≅ Q) (M : A) (q : ℕ) :
    P.singularHomology M q ≅ Q.singularHomology M q where
  hom := TopPair.singularHomologyMap e.hom M q
  inv := TopPair.singularHomologyMap e.inv M q
  hom_inv_id := by
    rw [← TopPair.singularHomologyMap_comp, e.hom_inv_id, TopPair.singularHomologyMap_id]
  inv_hom_id := by
    rw [← TopPair.singularHomologyMap_comp, e.inv_hom_id, TopPair.singularHomologyMap_id]

/-- The redundant whole-space subtype is removed by an actual
isomorphism of pairs; the base set is unchanged. -/
def univInclusionPairIso {X : Type w} [TopologicalSpace X] (D : Set X) :
    TopPair.ofInclusion (X := TopCat.of X) (subset_univ D) ≅
      TopPair.ofSubset (X := TopCat.of X) D where
  hom := TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (𝟙 (TopCat.of D)) (by ext x; rfl)
  inv := TopPair.ofHom (TopCat.ofHom ⟨fun x => ⟨x, mem_univ x⟩, continuous_id.subtype_mk _⟩)
    (𝟙 (TopCat.of D)) (by ext x; rfl)
  hom_inv_id := by
    apply TopPair.hom_ext_of_fst
    ext x
    rfl
  inv_hom_id := by
    apply TopPair.hom_ext_of_fst
    ext x
    rfl

/-- The whole base pair of a relative CW structure on Euclidean space
is the literal ambient pair `(E,D)`. -/
def relativeUnivBasePairIso {X : Type w} [TopologicalSpace X] [T2Space X]
    {D : Set X} [RelCWComplex (univ : Set X) D] :
    TauCeti.complexBasePair (univ : Set X) ≅ TopPair.ofSubset (X := TopCat.of X) D :=
  eqToIso (TauCeti.complexBasePair_eq_ofInclusion (univ : Set X)) ≪≫ univInclusionPairIso D

/-- On ambient points the pair comparison is exactly the subtype
projection, independently of the presentation of the relative base. -/
@[simp]
theorem relativeUnivBasePairIso_hom_fst {X : Type w} [TopologicalSpace X] [T2Space X]
    {D : Set X} [RelCWComplex (univ : Set X) D] :
    TopPair.Hom.fst (relativeUnivBasePairIso (D := D)).hom =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
  change TopPair.proj₁.map ((eqToIso
    (TauCeti.complexBasePair_eq_ofInclusion (univ : Set X))).hom ≫
      (univInclusionPairIso D).hom) = _
  rw [Functor.map_comp, eqToIso.hom, eqToHom_map]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

namespace IntegralArrangement

section PeriodicPair

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)

local instance costalkPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- A closed union of cells, with the actual periodic characteristic maps. -/
def periodicCellwiseSubcomplex (S : Set (Fin n → ℝ)) (closed : IsClosed S)
    (cellwise : Cellwise (augmentedForms matrix) S) :
    CWComplex.Subcomplex (arrangementCarrier matrix) where
  carrier := S
  I d := {c : Cell (augmentedForms matrix) d | cellCenter (augmentedForms matrix) c ∈ S}
  closed' := closed
  union' := by
    rw [empty_union]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨d, hx⟩ := mem_iUnion.mp hx
      obtain ⟨c, hx⟩ := mem_iUnion.mp hx
      change x ∈ periodicCellMap matrix c.val '' Metric.ball 0 1 at hx
      rw [periodicCellMap_image_ball] at hx
      exact (cellwise c.val.val.1 c.val.val.2
        (cellCenter_mem (augmentedForms matrix) c.val) hx).mp c.property
    · intro x hx
      let c : Cell (augmentedForms matrix)
          (Module.finrank ℝ (cellDirection (augmentedForms matrix)
            (integralIndices (augmentedForms matrix) x))) :=
        ⟨(ceilingVector (augmentedForms matrix) x, integralIndices (augmentedForms matrix) x),
          ⟨x, mem_cell_self (augmentedForms matrix) x⟩, rfl⟩
      have center_mem : cellCenter (augmentedForms matrix) c ∈ S :=
        (cellwise c.val.1 c.val.2 (mem_cell_self (augmentedForms matrix) x)
          (cellCenter_mem (augmentedForms matrix) c)).mp hx
      refine mem_iUnion.2 ⟨_, mem_iUnion.2 ⟨⟨c, center_mem⟩, ?_⟩⟩
      change x ∈ periodicCellMap matrix c '' Metric.ball 0 1
      rw [periodicCellMap_image_ball]
      exact mem_cell_self (augmentedForms matrix) x

/-- The complementary subcomplex in the periodic CW structure. -/
def periodicCostalkComplementSubcomplex (selected : Set (Fin s ⊕ Fin n))
    (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ) :
    CWComplex.Subcomplex (arrangementCarrier matrix) :=
  periodicCellwiseSubcomplex matrix
    (costalkRegion (augmentedForms matrix) selected weight x)ᶜ
    (costalkRegion_isOpen (augmentedForms matrix) selected weight x).isClosed_compl
    (costalkRegion_cellwise (augmentedForms matrix) selected weight x).compl

/-- The literal relative pair with the same periodic disks as the global
cellular resolution. -/
@[instance_reducible]
def periodicCostalkRelativeCWComplex (selected : Set (Fin s ⊕ Fin n))
    (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ) :
    RelCWComplex (arrangementCarrier matrix)
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ :=
  relativeToSubcomplex (periodicCostalkComplementSubcomplex matrix selected weight x)

end PeriodicPair

section Homology

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ)
  {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- The actual relative cellular chain complex, retaining its canonical
singular-homology differential. -/
def periodicCostalkCellComplex : ChainComplex (ModuleCat.{0} k) ℕ := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix selected weight x
  exact TauCeti.cellularChainComplex (univ : Set (Fin n → ℝ)) M

/-- Cellular homology is the relative singular homology of the actual
open costalk region in its actual Euclidean ambient space. -/
def periodicCostalkCellularSingularIso (q : ℕ) :
    (periodicCostalkCellComplex matrix selected weight x M).homology q ≅
      (TopPair.ofSubset ((costalkRegion (augmentedForms matrix) selected weight x)ᶜ :
        Set (TopCat.of (Fin n → ℝ)))).singularHomology M q := by
  letI : RelCWComplex (univ : Set (Fin n → ℝ))
      (costalkRegion (augmentedForms matrix) selected weight x)ᶜ :=
    periodicCostalkRelativeCWComplex matrix selected weight x
  exact TauCeti.cellularSingularHomologyIso (univ : Set (Fin n → ℝ)) M q ≪≫
    topPairHomologyIso relativeUnivBasePairIso M q

/-- The top-degree cellular homology carries the chosen ambient top
class, with coefficients unchanged. -/
def periodicCostalkCellHomologyIso
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty) :
    (periodicCostalkCellComplex matrix selected weight x M).homology n ≅ M :=
  periodicCostalkCellularSingularIso matrix selected weight x M n ≪≫
    augmentedCostalkSingularHomologyIso matrix selected weight x M nonempty

/-- The actual relative cellular complex has no homology off the
ambient dimension. -/
theorem periodicCostalkCellComplex_isZero_homology
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((periodicCostalkCellComplex matrix selected weight x M).homology q) :=
  (augmentedCostalkSingularHomology_isZero matrix selected weight x M nonempty q different).of_iso
    (periodicCostalkCellularSingularIso matrix selected weight x M q)

end Homology
end IntegralArrangement
end ToricPower
