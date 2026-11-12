module

public import ToricPower.CWRelativeSubcomplex
public import ToricPower.CellularHomologyNaturality
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Functorial cellular chains of pairs with an increasing base

For subcomplexes `A ⊆ B ⊆ C`, the literal identity of the ambient space
is a cellular map `(C,A) → (C,B)`. A cell absorbed by `B` enters the base;
every other cell retains its original characteristic disk. This constructs
the actual functor of relative cellular chain complexes on the subcomplex
poset. It is the support-restriction functor used by costalk calculations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set

namespace ToricPower

universe w v u

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C]

/-- A named copy of the same carrier retains the chosen base in the
relative CW instance. It changes neither its points nor its topology. -/
def relativeCWCarrier (_A : CWComplex.Subcomplex C) : Set X := C

instance relativeCWCarrier_relativeCW (A : CWComplex.Subcomplex C) :
    RelCWComplex (relativeCWCarrier A) (A : Set X) :=
  relativeToSubcomplex A

/-- The literal ambient identity between two choices of relative base. -/
def relativeBaseInclusion (A B : CWComplex.Subcomplex C) :
    TopCat.of (relativeCWCarrier A) ⟶ TopCat.of (relativeCWCarrier B) :=
  𝟙 (TopCat.of C)

/-- Increasing the base preserves every actual relative skeleton. -/
theorem relativeBaseInclusion_cellular (A B : CWComplex.Subcomplex C) (hAB : A ≤ B) :
    TauCeti.IsCellular (relativeCWCarrier A) (relativeCWCarrier B)
      (relativeBaseInclusion A B) := by
  intro n x hx
  obtain inBase | ⟨m, lower, cellIndex, point⟩ :=
    RelCWComplex.mem_skeletonLT_iff.mp hx
  · exact RelCWComplex.mem_skeletonLT_iff.mpr (Or.inl (hAB inBase))
  · change {i // i ∉ A.I m} at cellIndex
    change x.val ∈ openCell (C := C) m cellIndex.val at point
    by_cases inTarget : cellIndex.val ∈ B.I m
    · exact RelCWComplex.mem_skeletonLT_iff.mpr
        (Or.inl (B.openCell_subset_of_mem inTarget point))
    · apply RelCWComplex.mem_skeletonLT_iff.mpr
      exact Or.inr ⟨m, lower, ⟨cellIndex.val, inTarget⟩, point⟩

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasCoproducts.{w} 𝒜] [Abelian 𝒜] (M : 𝒜)

/-- The actual relative cellular complex for a specified subcomplex base. -/
def relativeCellularComplex (A : CWComplex.Subcomplex C) : ChainComplex 𝒜 ℕ :=
  TauCeti.cellularChainComplex (relativeCWCarrier A) M

/-- The genuine map induced by the identity on the ambient space. -/
def relativeCellularMap (A B : CWComplex.Subcomplex C) (hAB : A ≤ B) :
    relativeCellularComplex M A ⟶ relativeCellularComplex M B :=
  TauCeti.cellularChainComplexMap (relativeCWCarrier A) (relativeCWCarrier B)
    (relativeBaseInclusion_cellular A B hAB) M

@[simp]
theorem relativeCellularMap_id (A : CWComplex.Subcomplex C) :
    relativeCellularMap M A A le_rfl = 𝟙 (relativeCellularComplex M A) := by
  exact TauCeti.cellularChainComplexMap_id (relativeCWCarrier A) M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem relativeCellularMap_comp (A B D : CWComplex.Subcomplex C)
    (hAB : A ≤ B) (hBD : B ≤ D) :
    relativeCellularMap M A D (hAB.trans hBD) =
      relativeCellularMap M A B hAB ≫ relativeCellularMap M B D hBD := by
  simpa only [relativeCellularComplex, relativeCellularMap, relativeBaseInclusion,
    Category.id_comp] using
    (TauCeti.cellularChainComplexMap_comp (relativeCWCarrier A) (relativeCWCarrier B)
      (relativeBaseInclusion_cellular A B hAB) (relativeCWCarrier D)
      (relativeBaseInclusion_cellular B D hBD) M)

/-- Relative cellular chains form an actual functor on all subcomplexes.
No finiteness or exactness hypothesis is built into this construction. -/
def relativeCellularFunctor : CWComplex.Subcomplex C ⥤ ChainComplex 𝒜 ℕ where
  obj A := relativeCellularComplex M A
  map h := relativeCellularMap M _ _ h.le
  map_id A := relativeCellularMap_id M A
  map_comp f g := relativeCellularMap_comp M _ _ _ f.le g.le

end ToricPower
