module

public import ToricPower.LinearSliceCompactSupport
public import ToricPower.LinearSliceOpenDifferential
public import ToricPower.ModuleIncreasingSupport

/-! # Every cell of the full slice support in actual compact cochain coordinates

This is a degreewise comparison of the genuine filtered colimit, with
all finite-window inclusion maps. It retains every cell of an unbounded
support and uses finite support only for individual cochains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n)) (U : OpenCellSupport A)

instance sliceWindowSupport_cellsFinite (r q : ℕ) :
    Finite (SliceSupportCell A zeroRows (openCellWindow A U r) q) :=
  sliceSupportCell_finite A zeroRows (openCellWindow A U r)
    (openCellWindow_bounded A U r) q

/-- The actual window cells regarded as a subset of all strip cells. -/
def sliceWindowCellSet (r₀ q r : ℕ) : Set (SliceSupportCell A zeroRows U q) :=
  {c | cellCenter (augmentedForms A) c.val.val ∈ (openCellWindow A U (r₀ + r)).val}

theorem sliceWindowCellSet_mono (r₀ q : ℕ) :
    Monotone (sliceWindowCellSet A zeroRows U r₀ q) := by
  intro r t h c hc
  exact openCellWindow_mono A U (Nat.add_le_add_left h r₀) hc

theorem sliceWindowCellSet_exhaustive (r₀ q : ℕ)
    (c : SliceSupportCell A zeroRows U q) :
    ∃ r, c ∈ sliceWindowCellSet A zeroRows U r₀ q r := by
  have hc : cellCenter (augmentedForms A) c.val.val ∈ U.val := c.property
  have window : cellCenter (augmentedForms A) c.val.val ∈
      ⋃ r : ℕ, ((openCellWindow A U r).val : Set (Fin n → ℝ)) :=
    Eq.mpr (congrArg (fun T : Set (Fin n → ℝ) =>
      cellCenter (augmentedForms A) c.val.val ∈ T) (openCellWindow_exhausts A U)) hc
  rcases mem_iUnion.mp window with ⟨r, hr⟩
  exact ⟨r, openCellWindow_mono A U (by omega : r ≤ r₀ + r) hr⟩

/-- The two descriptions of an actual window cell have the same
underlying cell, including its original characteristic-disk orientation. -/
def sliceWindowCellEquiv (r₀ r q : ℕ) :
    SliceSupportCell A zeroRows (openCellWindow A U (r₀ + r)) q ≃
      sliceWindowCellSet A zeroRows U r₀ q r where
  toFun c := ⟨⟨c.val, c.property.1⟩, c.property⟩
  invFun c := ⟨c.val.val, c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

variable (k : Type) [Field k]

/-- The actual finite-window cochain term in the literal free-module
coordinates used by the increasing-support universal property. -/
def sliceWindowCochainCoordinates (r₀ r q : ℕ) :
    ((sliceWindowCochainSystem A zeroRows k U r₀).obj r).X q ≃ₗ[k]
      (sliceWindowCellSet A zeroRows U r₀ q r →₀ k) :=
  (sliceSupportCochainCoordinates A zeroRows k
    (openCellWindow A U (r₀ + r)) q).trans
      (Finsupp.domLCongr (sliceWindowCellEquiv A zeroRows U r₀ r q))

/-- At every degree the actual cochain system is naturally the
increasing system of free modules with extension-by-zero maps. -/
def sliceWindowCochainTermIso (r₀ q : ℕ) :
    sliceWindowCochainSystem A zeroRows k U r₀ ⋙
        HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q ≅
      ModuleIncreasingSupport.diagram k (sliceWindowCellSet A zeroRows U r₀ q)
        (sliceWindowCellSet_mono A zeroRows U r₀ q) :=
  NatIso.ofComponents (fun r => (sliceWindowCochainCoordinates A zeroRows U k r₀ r q).toModuleIso)
    (by
      intro r t f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      have h : openCellWindow A U (r₀ + r) ≤
          openCellWindow A U (r₀ + t) :=
        openCellWindow_mono A U (Nat.add_le_add_left f.le r₀)
      change Finsupp.domLCongr (R := k) (M := k)
          (sliceWindowCellEquiv A zeroRows U r₀ t q)
          (sliceSupportCochainCoordinates A zeroRows k
            (openCellWindow A U (r₀ + t)) q
            ((sliceSupportCochainExtension A zeroRows k h).f q φ)) =
        Finsupp.mapDomain
          (ModuleIncreasingSupport.indexMap (sliceWindowCellSet A zeroRows U r₀ q)
            (sliceWindowCellSet_mono A zeroRows U r₀ q) f.le)
          (Finsupp.domLCongr (R := k) (M := k)
            (sliceWindowCellEquiv A zeroRows U r₀ r q)
            (sliceSupportCochainCoordinates A zeroRows k
              (openCellWindow A U (r₀ + r)) q φ))
      have coordinates := sliceSupportCochainExtension_coordinates A zeroRows k
        (U := openCellWindow A U (r₀ + r))
        (V := openCellWindow A U (r₀ + t))
        h q φ
      refine (congrArg (Finsupp.domLCongr (R := k) (M := k)
        (sliceWindowCellEquiv A zeroRows U r₀ t q)) coordinates).trans ?_
      simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
      rfl)

/-- The actual degree of the filtered cochain colimit is the literal
finitely supported module on every cell of the full open strip. -/
def sliceCompactTermIso (r₀ q : ℕ) :
    (sliceCompactCochainComplex A zeroRows k U r₀).X q ≅
      ModuleCat.of k (SliceSupportCell A zeroRows U q →₀ k) :=
  preservesColimitIso (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q)
      (sliceWindowCochainSystem A zeroRows k U r₀) ≪≫
    HasColimit.isoOfNatIso (sliceWindowCochainTermIso A zeroRows U k r₀ q) ≪≫
      ModuleIncreasingSupport.fullSupportColimitIso k
        (sliceWindowCellSet A zeroRows U r₀ q)
        (sliceWindowCellSet_mono A zeroRows U r₀ q)
        (sliceWindowCellSet_exhaustive A zeroRows U r₀ q)

/-- The full-support comparison on an actual colimit leg is exactly
the proved window coordinates followed by extension by zero. -/
@[reassoc]
theorem sliceCompactTermIso_inclusion (r₀ r q : ℕ) :
    (colimit.ι (sliceWindowCochainSystem A zeroRows k U r₀) r).f q ≫
        (sliceCompactTermIso A zeroRows U k r₀ q).hom =
      (sliceWindowCochainCoordinates A zeroRows U k r₀ r q).toModuleIso.hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain (R := k) (M := k)
          (Subtype.val : sliceWindowCellSet A zeroRows U r₀ q r →
            SliceSupportCell A zeroRows U q)) := by
  change (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q).map
      (colimit.ι (sliceWindowCochainSystem A zeroRows k U r₀) r) ≫
      (preservesColimitIso (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q)
        (sliceWindowCochainSystem A zeroRows k U r₀)).hom ≫
      (HasColimit.isoOfNatIso (sliceWindowCochainTermIso A zeroRows U k r₀ q)).hom ≫
      (ModuleIncreasingSupport.fullSupportColimitIso k
        (sliceWindowCellSet A zeroRows U r₀ q)
        (sliceWindowCellSet_mono A zeroRows U r₀ q)
        (sliceWindowCellSet_exhaustive A zeroRows U r₀ q)).hom = _
  rw [ι_preservesColimitIso_hom_assoc,
    HasColimit.ι_isoOfNatIso_hom_assoc,
    ModuleIncreasingSupport.fullSupportColimitIso_inclusion]
  rfl

end ToricPower.IntegralArrangement
