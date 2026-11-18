module

public import ToricPower.DualDiagonalCompactSupport
public import ToricPower.ArrangementOpenSupportDifferential
public import ToricPower.ModuleIncreasingSupport

/-!
# Finite-support coordinates of the actual dual-strip colimit

The genuine finite-window cochains are naturally identified with the
free modules on the cells in those windows. The increasing-support
universal property identifies their actual colimit with the full
finitely supported module on all cells of the unrestricted open strip.
The comparison records its action on each actual window inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (u : Fin n → ℤ)

def dualDiagonalStripSupport : OpenCellSupport A :=
  ⟨⟨dualDiagonalStrip A S T u, dualDiagonalStrip_isOpen A S T u⟩,
    dualDiagonalStrip_cellwise A S T u⟩

abbrev DualDiagonalStripCell (q : ℕ) :=
  OpenSupportCell A (dualDiagonalStripSupport A S T u) q

instance dualDiagonalWindowSupport_cellsFinite (r q : ℕ) :
    Finite (OpenSupportCell A (dualDiagonalWindowSupport A S T u r) q) :=
  dualDiagonalWindow_cells_finite A S T u r q

/-- The actual window cells regarded as a subset of all strip cells. -/
def dualDiagonalWindowCellSet (r₀ q r : ℕ) : Set (DualDiagonalStripCell A S T u q) :=
  {c | cellCenter (augmentedForms A) c.val ∈ dualDiagonalWindow A S T u (r₀ + r)}

theorem dualDiagonalWindowCellSet_mono (r₀ q : ℕ) :
    Monotone (dualDiagonalWindowCellSet A S T u r₀ q) := by
  intro r t h c hc
  exact dualDiagonalWindow_mono A S T u (Nat.add_le_add_left h r₀) hc

theorem dualDiagonalWindowCellSet_exhaustive (r₀ q : ℕ)
    (c : DualDiagonalStripCell A S T u q) :
    ∃ r, c ∈ dualDiagonalWindowCellSet A S T u r₀ q r := by
  have hc : cellCenter (augmentedForms A) c.val ∈ dualDiagonalStrip A S T u := c.property
  rw [← dualDiagonalWindow_exhausts A S T u] at hc
  rcases mem_iUnion.mp hc with ⟨r, hr⟩
  exact ⟨r, dualDiagonalWindow_mono A S T u (by omega : r ≤ r₀ + r) hr⟩

/-- The two descriptions of an actual window cell have the same
underlying cell, including its original characteristic-disk orientation. -/
def dualDiagonalWindowCellEquiv (r₀ r q : ℕ) :
    OpenSupportCell A (dualDiagonalWindowSupport A S T u (r₀ + r)) q ≃
      dualDiagonalWindowCellSet A S T u r₀ q r where
  toFun c := ⟨⟨c.val, c.property.1⟩, c.property⟩
  invFun c := ⟨c.val.val, c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

variable (k : Type) [Field k]

/-- The actual finite-window cochain term in the literal free-module
coordinates used by the increasing-support universal property. -/
def dualDiagonalWindowCochainCoordinates (r₀ r q : ℕ) :
    ((dualDiagonalWindowCochainSystem A k S T u r₀).obj r).X q ≃ₗ[k]
      (dualDiagonalWindowCellSet A S T u r₀ q r →₀ k) :=
  (openSupportCochainCoordinates A k
    (dualDiagonalWindowSupport A S T u (r₀ + r)) q).trans
      (Finsupp.domLCongr (dualDiagonalWindowCellEquiv A S T u r₀ r q))

/-- At every degree the actual cochain system is naturally the
increasing system of free modules with extension-by-zero maps. -/
def dualDiagonalWindowCochainTermIso (r₀ q : ℕ) :
    dualDiagonalWindowCochainSystem A k S T u r₀ ⋙
        HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q ≅
      ModuleIncreasingSupport.diagram k (dualDiagonalWindowCellSet A S T u r₀ q)
        (dualDiagonalWindowCellSet_mono A S T u r₀ q) :=
  NatIso.ofComponents (fun r => (dualDiagonalWindowCochainCoordinates A S T u k r₀ r q).toModuleIso)
    (by
      intro r t f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      have h : dualDiagonalWindowSupport A S T u (r₀ + r) ≤
          dualDiagonalWindowSupport A S T u (r₀ + t) :=
        dualDiagonalWindow_mono A S T u (Nat.add_le_add_left f.le r₀)
      change Finsupp.domLCongr (R := k) (M := k)
          (dualDiagonalWindowCellEquiv A S T u r₀ t q)
          (openSupportCochainCoordinates A k
            (dualDiagonalWindowSupport A S T u (r₀ + t)) q
            ((openSupportCochainExtension A k h).f q φ)) =
        Finsupp.mapDomain
          (ModuleIncreasingSupport.indexMap (dualDiagonalWindowCellSet A S T u r₀ q)
            (dualDiagonalWindowCellSet_mono A S T u r₀ q) f.le)
          (Finsupp.domLCongr (R := k) (M := k)
            (dualDiagonalWindowCellEquiv A S T u r₀ r q)
            (openSupportCochainCoordinates A k
              (dualDiagonalWindowSupport A S T u (r₀ + r)) q φ))
      have coordinates := openSupportCochainExtension_coordinates A k
        (U := dualDiagonalWindowSupport A S T u (r₀ + r))
        (V := dualDiagonalWindowSupport A S T u (r₀ + t))
        h q φ
      refine (congrArg (Finsupp.domLCongr (R := k) (M := k)
        (dualDiagonalWindowCellEquiv A S T u r₀ t q)) coordinates).trans ?_
      simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
      rfl)

/-- The actual degree of the filtered cochain colimit is the literal
finitely supported module on every cell of the full open strip. -/
def dualDiagonalCompactTermIso (r₀ q : ℕ) :
    (dualDiagonalCompactCochainComplex A k S T u r₀).X q ≅
      ModuleCat.of k (DualDiagonalStripCell A S T u q →₀ k) :=
  preservesColimitIso (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q)
      (dualDiagonalWindowCochainSystem A k S T u r₀) ≪≫
    HasColimit.isoOfNatIso (dualDiagonalWindowCochainTermIso A S T u k r₀ q) ≪≫
      ModuleIncreasingSupport.fullSupportColimitIso k
        (dualDiagonalWindowCellSet A S T u r₀ q)
        (dualDiagonalWindowCellSet_mono A S T u r₀ q)
        (dualDiagonalWindowCellSet_exhaustive A S T u r₀ q)

/-- The full-support comparison on an actual colimit leg is exactly
the proved window coordinates followed by extension by zero. -/
@[reassoc]
theorem dualDiagonalCompactTermIso_inclusion (r₀ r q : ℕ) :
    (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q ≫
        (dualDiagonalCompactTermIso A S T u k r₀ q).hom =
      (dualDiagonalWindowCochainCoordinates A S T u k r₀ r q).toModuleIso.hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain (R := k) (M := k)
          (Subtype.val : dualDiagonalWindowCellSet A S T u r₀ q r →
            DualDiagonalStripCell A S T u q)) := by
  change (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q).map
      (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r) ≫
      (preservesColimitIso (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) q)
        (dualDiagonalWindowCochainSystem A k S T u r₀)).hom ≫
      (HasColimit.isoOfNatIso (dualDiagonalWindowCochainTermIso A S T u k r₀ q)).hom ≫
      (ModuleIncreasingSupport.fullSupportColimitIso k
        (dualDiagonalWindowCellSet A S T u r₀ q)
        (dualDiagonalWindowCellSet_mono A S T u r₀ q)
        (dualDiagonalWindowCellSet_exhaustive A S T u r₀ q)).hom = _
  rw [ι_preservesColimitIso_hom_assoc,
    HasColimit.ι_isoOfNatIso_hom_assoc,
    ModuleIncreasingSupport.fullSupportColimitIso_inclusion]
  rfl

end ToricPower.IntegralArrangement
