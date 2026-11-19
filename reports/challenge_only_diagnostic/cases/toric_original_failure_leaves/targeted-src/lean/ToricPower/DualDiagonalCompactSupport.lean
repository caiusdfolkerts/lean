module

public import ToricPower.DualDiagonalStrip
public import ToricPower.ArrangementOpenSupport
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# The actual compact-support colimit of dual-strip windows

The system consists of the scalar cochains of the genuine relative CW
pairs for bounded open integer windows. Every window has finitely many
cells. The transition maps are the actual duals of support restriction.
Filtered-colimit exactness in modules, proved in the imported library,
then computes the cohomology of the actual colimit of these complexes.
The normalization is the fixed ambient top class at every stage.

The comparison with the independent dual-diagonal coefficient matrix is
separate: this file does not identify a colimit with an infinite algebraic
dual or assume a geometric reconstruction theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]

local instance : IsConnected ℕ := IsFiltered.isConnected ℕ

/-- Actual scalar cochains, covariantly functorial in the open support. -/
def openSupportCochainFunctor :
    OpenCellSupport A ⥤ CochainComplex (ModuleCat.{0} k) ℕ :=
  (openSupportChainFunctor A (ModuleCat.of k k)).rightOp ⋙
    HomologicalComplex.opFunctor _ _ ⋙ (scalarDual k).mapHomologicalComplex _

@[simp]
theorem openSupportCochainFunctor_obj (U : OpenCellSupport A) :
    (openSupportCochainFunctor A k).obj U = openSupportCochainComplex A k U := rfl

@[simp]
theorem openSupportCochainFunctor_map {U V : OpenCellSupport A} (f : U ⟶ V) :
    (openSupportCochainFunctor A k).map f = openSupportCochainExtension A k f.le := rfl

variable (S T : Set (Fin s)) (u : Fin n → ℤ)

/-- The geometric window as a genuine open cell support. -/
def dualDiagonalWindowSupport (r : ℕ) : OpenCellSupport A :=
  ⟨⟨dualDiagonalWindow A S T u r, dualDiagonalWindow_isOpen A S T u r⟩,
    dualDiagonalWindow_cellwise A S T u r⟩

/-- An arbitrary tail of the increasing geometric exhaustion. -/
def dualDiagonalWindowSupportSystem (r₀ : ℕ) : ℕ ⥤ OpenCellSupport A where
  obj r := dualDiagonalWindowSupport A S T u (r₀ + r)
  map f := homOfLE (dualDiagonalWindow_mono A S T u (Nat.add_le_add_left f.le r₀))

/-- The actual finite-window cochain system, with literal support maps. -/
def dualDiagonalWindowCochainSystem (r₀ : ℕ) :
    ℕ ⥤ CochainComplex (ModuleCat.{0} k) ℕ :=
  dualDiagonalWindowSupportSystem A S T u r₀ ⋙ openSupportCochainFunctor A k

/-- The actual filtered colimit in the category of complexes. -/
def dualDiagonalCompactCochainComplex (r₀ : ℕ) : CochainComplex (ModuleCat.{0} k) ℕ :=
  colimit (dualDiagonalWindowCochainSystem A k S T u r₀)

theorem dualDiagonalWindow_tail_nonempty {r₀ : ℕ}
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) (r : ℕ) :
    (dualDiagonalWindow A S T u (r₀ + r)).Nonempty :=
  h₀.mono (dualDiagonalWindow_mono A S T u (Nat.le_add_right r₀ r))

/-- The actual top homology diagram is naturally the constant field.
This uses the genuine support maps and their coherent ambient classes. -/
def dualDiagonalWindowTopHomologyIso (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    dualDiagonalWindowCochainSystem A k S T u r₀ ⋙
        HomologicalComplex.homologyFunctor _ _ n ≅
      (Functor.const ℕ).obj (ModuleCat.of k k) :=
  NatIso.ofComponents (fun r =>
    openSupportCochainTopClassIso A k (dualDiagonalWindowSupport A S T u (r₀ + r))
      (dualDiagonalWindow_convex A S T u (r₀ + r))
      (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
      (dualDiagonalWindow_bounded A S T u (r₀ + r))) (by
        intro r t f
        exact (openSupportCochainTopClassIso_natural A k
            (U := dualDiagonalWindowSupport A S T u (r₀ + r))
            (V := dualDiagonalWindowSupport A S T u (r₀ + t))
            (dualDiagonalWindow_mono A S T u (Nat.add_le_add_left f.le r₀))
            (dualDiagonalWindow_convex A S T u (r₀ + r))
            (dualDiagonalWindow_convex A S T u (r₀ + t))
            (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
            (dualDiagonalWindow_tail_nonempty A S T u h₀ t)
            (dualDiagonalWindow_bounded A S T u (r₀ + r))
            (dualDiagonalWindow_bounded A S T u (r₀ + t))).trans
              (Category.comp_id _).symm)

/-- Filtered-colimit exactness gives the actual scalar-linear homology
comparison for this unrestricted increasing system of finite complexes. -/
def dualDiagonalCompactHomologyColimitIso (r₀ q : ℕ) :
    (dualDiagonalCompactCochainComplex A k S T u r₀).homology q ≅
      colimit (dualDiagonalWindowCochainSystem A k S T u r₀ ⋙
        HomologicalComplex.homologyFunctor _ _ q) :=
  preservesColimitIso (HomologicalComplex.homologyFunctor _ _ q) _

/-- Every nonempty dual strip has its single ambient top coefficient,
computed through the actual finite-window cochain colimit. -/
def dualDiagonalCompactTopClassIso (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    (dualDiagonalCompactCochainComplex A k S T u r₀).homology n ≅ ModuleCat.of k k :=
  dualDiagonalCompactHomologyColimitIso A k S T u r₀ n ≪≫
    HasColimit.isoOfNatIso (dualDiagonalWindowTopHomologyIso A k S T u r₀ h₀) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitConstCocone ℕ (ModuleCat.of k k))

theorem dualDiagonalCompactCochainComplex_isZero_homology (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) (q : ℕ) (different : q ≠ n) :
    IsZero ((dualDiagonalCompactCochainComplex A k S T u r₀).homology q) := by
  have hF : IsZero (dualDiagonalWindowCochainSystem A k S T u r₀ ⋙
      HomologicalComplex.homologyFunctor _ _ q) := Functor.isZero _ (fun r =>
    openSupportCochainComplex_isZero_homology A k
      (dualDiagonalWindowSupport A S T u (r₀ + r))
      (dualDiagonalWindow_convex A S T u (r₀ + r))
      (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
      (dualDiagonalWindow_bounded A S T u (r₀ + r)) q different)
  exact (colim.map_isZero hF).of_iso
    (dualDiagonalCompactHomologyColimitIso A k S T u r₀ q)

/-- Nonemptiness of the full strip gives a nonempty finite starting
window, so the preceding result does not impose a bounded-strip premise. -/
theorem dualDiagonalStrip_exists_nonempty_window
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    ∃ r₀, (dualDiagonalWindow A S T u r₀).Nonempty := by
  rcases nonempty with ⟨x, hx⟩
  rw [← dualDiagonalWindow_exhausts A S T u] at hx
  rcases mem_iUnion.mp hx with ⟨r, hr⟩
  exact ⟨r, x, hr⟩

end ToricPower.IntegralArrangement
