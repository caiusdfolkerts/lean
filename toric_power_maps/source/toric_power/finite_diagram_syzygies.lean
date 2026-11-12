module

public import ToricPower.CellularFiniteResolution
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite coefficients in the canonical incidence resolution

For a finite category with finite Hom sets, every term of the actual
vector-cover resolution of a pointwise finite-dimensional diagram
remains pointwise finite-dimensional. These statements concern the
canonical covers and kernels themselves, not replacement presentations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k]

theorem moduleCoproduct_finite {I : Type u} [Finite I]
    (family : I → ModuleCat.{u} k) [∀ i, FiniteDimensional k (family i)] :
    FiniteDimensional k (∐ family : ModuleCat.{u} k) := by
  classical
  letI := Fintype.ofFinite I
  letI : HasBiproduct family := HasBiproduct.of_hasCoproduct family
  let e : (∐ family) ≅ ModuleCat.of k (∀ i, family i) :=
    (biproduct.isoCoproduct family).symm ≪≫ biproduct.isoProduct family ≪≫
      ModuleCat.piIsoPi family
  exact FiniteDimensional.of_injective e.hom.hom
    ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)

variable {C : Type u} [Category.{u} C]

theorem diagramCoproduct_finite {I : Type u} [Finite I]
    (family : I → C ⥤ ModuleCat.{u} k)
    [∀ i c, FiniteDimensional k ((family i).obj c)] (c : C) :
    FiniteDimensional k ((∐ family).obj c) := by
  letI (i : I) : FiniteDimensional k
      (((evaluation C (ModuleCat.{u} k)).obj c).obj (family i)) := by
    change FiniteDimensional k ((family i).obj c)
    infer_instance
  letI : FiniteDimensional k (∐ fun i =>
      ((evaluation C (ModuleCat.{u} k)).obj c).obj (family i) : ModuleCat.{u} k) :=
    moduleCoproduct_finite k _
  let e := PreservesCoproduct.iso ((evaluation C (ModuleCat.{u} k)).obj c) family
  exact FiniteDimensional.of_injective e.hom.hom
    ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)

theorem representable_finite [∀ c d : C, Finite (c ⟶ d)] (c d : C) :
    FiniteDimensional k ((representable k c).obj d) := by
  change FiniteDimensional k ((c ⟶ d) →₀ k)
  infer_instance

theorem vectorCopower_finite (P : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (P.obj c)] (M : ModuleCat.{u} k)
    [FiniteDimensional k M] (c : C) :
    FiniteDimensional k ((vectorCopower k P M).obj c) := by
  unfold vectorCopower
  exact diagramCoproduct_finite k _ c

variable [Finite C] [∀ c d : C, Finite (c ⟶ d)]

theorem diagramVectorCover_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (c : C) :
    FiniteDimensional k ((diagramVectorCoverObj k F).obj c) := by
  letI (d e : C) : FiniteDimensional k ((representable k d).obj e) :=
    representable_finite k d e
  letI (d e : C) : FiniteDimensional k ((vectorCopower k (representable k d)
      (F.obj d)).obj e) := vectorCopower_finite k _ _ e
  unfold diagramVectorCoverObj
  exact diagramCoproduct_finite k _ c

theorem diagramSyzygy_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (c : C) :
    FiniteDimensional k (((diagramSyzygy k).obj F).obj c) := by
  letI : FiniteDimensional k ((diagramVectorCoverObj k F).obj c) :=
    diagramVectorCover_finite k F c
  exact FiniteDimensional.of_injective
    ((kernel.ι (diagramVectorCoverMap k F)).app c).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

theorem diagramSyzygyIterate_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (n : ℕ) (c : C) :
    FiniteDimensional k (((diagramSyzygyIterate k n).obj F).obj c) := by
  induction n generalizing c with
  | zero =>
    change FiniteDimensional k (F.obj c)
    infer_instance
  | succ n ih =>
    letI (c : C) := ih c
    exact diagramSyzygy_finite k ((diagramSyzygyIterate k n).obj F) c

theorem diagramProjectiveTerm_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (n : ℕ) (c : C) :
    FiniteDimensional k ((diagramProjectiveTerm k F n).obj c) := by
  letI (c : C) := diagramSyzygyIterate_finite k F n c
  exact diagramVectorCover_finite k ((diagramSyzygyIterate k n).obj F) c

end ToricPower.Cellular

end
