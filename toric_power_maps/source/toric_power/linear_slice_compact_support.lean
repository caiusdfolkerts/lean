module

public import ToricPower.ArrangementOpenWindows
public import ToricPower.LinearSliceOpenSupport
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Genuine compact cochains on an unbounded open part of a closed slice

This is the actual filtered colimit of bounded relative CW cochains,
with their literal support maps. Its unique nonzero cohomology degree
is the intrinsic dimension of the slice. The full open support may be
unbounded, and every stage uses the original characteristic disks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set Opposite

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (zeroRows : Set (Fin s ⊕ Fin n))
  (k : Type) [Field k]

local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

local instance : IsConnected ℕ := IsFiltered.isConnected ℕ

def sliceSupportCochainFunctor :
    OpenCellSupport A ⥤ CochainComplex (ModuleCat.{0} k) ℕ :=
  (sliceSupportChainFunctor A zeroRows (ModuleCat.of k k)).rightOp ⋙
    HomologicalComplex.opFunctor _ _ ⋙ (scalarDual k).mapHomologicalComplex _

@[simp]
theorem sliceSupportCochainFunctor_obj (U : OpenCellSupport A) :
    (sliceSupportCochainFunctor A zeroRows k).obj U =
      sliceSupportCochainComplex A zeroRows k U := rfl

@[simp]
theorem sliceSupportCochainFunctor_map {U V : OpenCellSupport A} (f : U ⟶ V) :
    (sliceSupportCochainFunctor A zeroRows k).map f =
      sliceSupportCochainExtension A zeroRows k f.le := rfl

variable (U : OpenCellSupport A)

def sliceWindowCochainSystem (r₀ : ℕ) :
    ℕ ⥤ CochainComplex (ModuleCat.{0} k) ℕ :=
  openCellWindowSystem A U r₀ ⋙ sliceSupportCochainFunctor A zeroRows k

def sliceCompactCochainComplex (r₀ : ℕ) : CochainComplex (ModuleCat.{0} k) ℕ :=
  colimit (sliceWindowCochainSystem A zeroRows k U r₀)

theorem sliceWindow_tail_nonempty {r₀ : ℕ}
    (h₀ : (Subtype.val ⁻¹' ((openCellWindow A U r₀).val : Set (Fin n → ℝ)) :
      Set L).Nonempty) (r : ℕ) :
    (Subtype.val ⁻¹' ((openCellWindow A U (r₀+r)).val : Set (Fin n → ℝ)) :
      Set L).Nonempty :=
  h₀.mono (Set.preimage_mono
    (openCellWindow_mono A U (Nat.le_add_right r₀ r)))

def sliceWindowTopHomologyIso
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ))) (r₀ : ℕ)
    (h₀ : (Subtype.val ⁻¹' ((openCellWindow A U r₀).val : Set (Fin n → ℝ)) :
      Set L).Nonempty) :
    sliceWindowCochainSystem A zeroRows k U r₀ ⋙
        HomologicalComplex.homologyFunctor _ _ (Module.finrank ℝ L) ≅
      (Functor.const ℕ).obj (ModuleCat.of k k) :=
  NatIso.ofComponents (fun r =>
    sliceSupportCochainTopClassIso A zeroRows k (openCellWindow A U (r₀+r))
      (openCellWindow_convex A U convexU (r₀+r))
      (sliceWindow_tail_nonempty A zeroRows U h₀ r)
      (openCellWindow_bounded A U (r₀+r))) (by
        intro r t f
        exact (sliceSupportCochainTopClassIso_natural A zeroRows k
          (U := openCellWindow A U (r₀+r)) (V := openCellWindow A U (r₀+t))
          (openCellWindow_mono A U (Nat.add_le_add_left f.le r₀))
          (openCellWindow_convex A U convexU (r₀+r))
          (openCellWindow_convex A U convexU (r₀+t))
          (sliceWindow_tail_nonempty A zeroRows U h₀ r)
          (sliceWindow_tail_nonempty A zeroRows U h₀ t)
          (openCellWindow_bounded A U (r₀+r))
          (openCellWindow_bounded A U (r₀+t))).trans (Category.comp_id _).symm)

def sliceCompactHomologyColimitIso (r₀ q : ℕ) :
    (sliceCompactCochainComplex A zeroRows k U r₀).homology q ≅
      colimit (sliceWindowCochainSystem A zeroRows k U r₀ ⋙
        HomologicalComplex.homologyFunctor _ _ q) :=
  preservesColimitIso (HomologicalComplex.homologyFunctor _ _ q) _

def sliceCompactTopClassIso
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ))) (r₀ : ℕ)
    (h₀ : (Subtype.val ⁻¹' ((openCellWindow A U r₀).val : Set (Fin n → ℝ)) :
      Set L).Nonempty) :
    (sliceCompactCochainComplex A zeroRows k U r₀).homology (Module.finrank ℝ L) ≅
      ModuleCat.of k k :=
  sliceCompactHomologyColimitIso A zeroRows k U r₀ (Module.finrank ℝ L) ≪≫
    HasColimit.isoOfNatIso (sliceWindowTopHomologyIso A zeroRows k U convexU r₀ h₀) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitConstCocone ℕ (ModuleCat.of k k))

theorem sliceCompactCochainComplex_isZero_homology
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ))) (r₀ : ℕ)
    (h₀ : (Subtype.val ⁻¹' ((openCellWindow A U r₀).val : Set (Fin n → ℝ)) :
      Set L).Nonempty) (q : ℕ) (different : q ≠ Module.finrank ℝ L) :
    IsZero ((sliceCompactCochainComplex A zeroRows k U r₀).homology q) := by
  have hF : IsZero (sliceWindowCochainSystem A zeroRows k U r₀ ⋙
      HomologicalComplex.homologyFunctor _ _ q) := Functor.isZero _ (fun r =>
    sliceSupportCochainComplex_isZero_homology A zeroRows k
      (openCellWindow A U (r₀+r))
      (openCellWindow_convex A U convexU (r₀+r))
      (sliceWindow_tail_nonempty A zeroRows U h₀ r)
      (openCellWindow_bounded A U (r₀+r)) q different)
  exact (colim.map_isZero hF).of_iso
    (sliceCompactHomologyColimitIso A zeroRows k U r₀ q)

theorem sliceOpenSupport_exists_nonempty_window
    (nonempty : (Subtype.val ⁻¹' (U.val : Set (Fin n → ℝ)) : Set L).Nonempty) :
    ∃ r₀, (Subtype.val ⁻¹' ((openCellWindow A U r₀).val : Set (Fin n → ℝ)) :
      Set L).Nonempty := by
  obtain ⟨x,hx⟩ := nonempty
  have point : x.val ∈ (U.val : Set (Fin n → ℝ)) := hx
  rw [← openCellWindow_exhausts A U] at point
  obtain ⟨r,hr⟩ := mem_iUnion.mp point
  exact ⟨r,x,hr⟩

end ToricPower.IntegralArrangement

end
