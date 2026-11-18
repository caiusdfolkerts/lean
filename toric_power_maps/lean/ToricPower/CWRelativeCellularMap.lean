module

public import ToricPower.CWRelativeSubcomplexMap

/-!
# Relative cellular maps induced by ambient cellular maps

An actual cellular map preserving two chosen subcomplex bases induces a
map of the relative CW pairs with their original characteristic disks.
Cells entering the target base are accounted for explicitly. This is
used for lattice translation of the costalk pairs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set
open scoped Classical

namespace ToricPower

universe w v u

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {C : Set X} {D : Set Y}
  [CWComplex C] [CWComplex D]
  (A : CWComplex.Subcomplex C) (B : CWComplex.Subcomplex D)
  (f : TopCat.of C ⟶ TopCat.of D)

/-- The same map on the two named relative carriers. -/
def relativeCWMap : TopCat.of (relativeCWCarrier A) ⟶ TopCat.of (relativeCWCarrier B) := f

/-- A cellular ambient map preserving the bases preserves all actual
relative skeleta, including cells absorbed by the target base. -/
theorem relativeCWMap_cellular (hf : TauCeti.IsCellular C D f)
    (base : ∀ x : C, x.val ∈ A → (f x).val ∈ B) :
    TauCeti.IsCellular (relativeCWCarrier A) (relativeCWCarrier B)
      (relativeCWMap A B f) := by
  intro n x hx
  obtain inBase | ⟨d, lower, c, point⟩ := RelCWComplex.mem_skeletonLT_iff.mp hx
  · exact RelCWComplex.mem_skeletonLT_iff.mpr (Or.inl (base x inBase))
  · change {j // j ∉ A.I d} at c
    change x.val ∈ openCell (C := C) d c.val at point
    have ambient : x.val ∈ (skeletonLT C n : Set X) :=
      CWComplex.mem_skeletonLT_iff.mpr ⟨d, lower, c.val, point⟩
    obtain ⟨e, lower', j, point'⟩ :=
      CWComplex.mem_skeletonLT_iff.mp (hf n ambient)
    by_cases absorbed : j ∈ B.I e
    · exact RelCWComplex.mem_skeletonLT_iff.mpr
        (Or.inl (B.openCell_subset_of_mem absorbed point'))
    · exact RelCWComplex.mem_skeletonLT_iff.mpr
        (Or.inr ⟨e, lower', ⟨j, absorbed⟩, point'⟩)

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasCoproducts.{w} 𝒜] [Abelian 𝒜] (M : 𝒜)

/-- The genuine cellular chain map of the two relative pairs. -/
def relativeCWChainMap (hf : TauCeti.IsCellular C D f)
    (base : ∀ x : C, x.val ∈ A → (f x).val ∈ B) :
    relativeCellularComplex M A ⟶ relativeCellularComplex M B :=
  TauCeti.cellularChainComplexMap (relativeCWCarrier A) (relativeCWCarrier B)
    (relativeCWMap_cellular A B f hf base) M

/-- Equality of the actual ambient maps identifies their induced chain
maps; the cellularity and base-preservation witnesses are proofs. -/
theorem relativeCWChainMap_congr (g : TopCat.of C ⟶ TopCat.of D)
    (hf : TauCeti.IsCellular C D f) (hg : TauCeti.IsCellular C D g)
    (baseF : ∀ x : C, x.val ∈ A → (f x).val ∈ B)
    (baseG : ∀ x : C, x.val ∈ A → (g x).val ∈ B) (equal : f = g) :
    relativeCWChainMap A B f M hf baseF = relativeCWChainMap A B g M hg baseG := by
  subst g
  rfl

/-- The actual identity of the ambient CW space gives the identity of
the relative cellular complex. -/
@[simp]
theorem relativeCWChainMap_id (A : CWComplex.Subcomplex C) :
    relativeCWChainMap A A (𝟙 (TopCat.of C)) M (TauCeti.isCellular_id C)
      (fun _ h => h) = 𝟙 (relativeCellularComplex M A) := by
  exact TauCeti.cellularChainComplexMap_id (relativeCWCarrier A) M

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z]
  {E : Set Z} [CWComplex E] (D' : CWComplex.Subcomplex E)
  (g : TopCat.of D ⟶ TopCat.of E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual relative cellular maps respect composition, including cells
which become part of either relative base. -/
@[reassoc]
theorem relativeCWChainMap_comp
    (hf : TauCeti.IsCellular C D f) (hg : TauCeti.IsCellular D E g)
    (baseF : ∀ x : C, x.val ∈ A → (f x).val ∈ B)
    (baseG : ∀ x : D, x.val ∈ B → (g x).val ∈ D') :
    relativeCWChainMap A D' (f ≫ g) M (TauCeti.IsCellular.comp C D hf hg)
        (fun x h => baseG (f x) (baseF x h)) =
      relativeCWChainMap A B f M hf baseF ≫ relativeCWChainMap B D' g M hg baseG := by
  exact TauCeti.cellularChainComplexMap_comp (relativeCWCarrier A) (relativeCWCarrier B)
    (relativeCWMap_cellular A B f hf baseF) (relativeCWCarrier D')
    (relativeCWMap_cellular B D' g hg baseG) M

end ToricPower
