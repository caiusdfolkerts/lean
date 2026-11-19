module

public import ToricPower.DualDiagonalCompactCoordinates
public import ToricPower.ArrangementOpenSupportTranslationCoordinates
public import ToricPower.DualDiagonalTranslations
public import ToricPower.ModuleHomologyColimitClass
public import ToricPower.ArrangementOpenSupportTranslationSquare

/-!
# Monomial maps on the actual compact-support colimit

A regular monomial pair translates each finite window into a larger
finite window. The genuine relative cochain maps form a natural
transformation of the exhausting systems, and therefore induce a map of
the actual filtered colimits. Their coherent top classes commute with
this map with coefficient exactly one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (S T : Set (Fin s)) (u : Fin n → ℤ)

local instance : IsConnected ℕ := IsFiltered.isConnected ℕ

/-- Every actual finite-stage colimit map preserves the fixed top class. -/
@[reassoc]
theorem dualDiagonalCompactTopClassIso_inclusion (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) (r : ℕ) :
    HomologicalComplex.homologyMap
        (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r) n ≫
      (dualDiagonalCompactTopClassIso A k S T u r₀ h₀).hom =
    (openSupportCochainTopClassIso A k (dualDiagonalWindowSupport A S T u (r₀ + r))
      (dualDiagonalWindow_convex A S T u (r₀ + r))
      (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
      (dualDiagonalWindow_bounded A S T u (r₀ + r))).hom :=
  homologyColimitClassIso_inclusion k n
    (dualDiagonalWindowCochainSystem A k S T u r₀) (ModuleCat.of k k)
    (dualDiagonalWindowTopHomologyIso A k S T u r₀ h₀) r

variable (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)
  (C : ℕ) (bound : ∀ j, |latticeLift (-a.val) j| ≤ (C : ℝ))

local notation "v" => u + a.val + b.val

include bound

/-- The exact finite-stage translated inclusion, with a common index
shift for the whole exhausting diagram. -/
theorem dualDiagonalWindowSystem_translation (r₀ r : ℕ) :
    translatedRegion
        ((dualDiagonalWindowSupport A S T u (r₀ + r)).val : Set (Fin n → ℝ))
        (latticeLift (-a.val)) ⊆
      (dualDiagonalWindowSupport A S T v (r₀ + C + r)).val := by
  change translatedRegion (dualDiagonalWindow A S T u (r₀ + r)) (latticeLift (-a.val)) ⊆
    dualDiagonalWindow A S T v (r₀ + C + r)
  simpa only [Nat.add_right_comm] using
    dualDiagonalWindow_monomial_translation A S T u a b (r₀ + r) C bound

/-- The actual translated relative cochain maps commute with every
window inclusion, as can be checked in their literal cell coordinates. -/
def dualDiagonalWindowMonomialMap (r₀ : ℕ) :
    dualDiagonalWindowCochainSystem A k S T u r₀ ⟶
      dualDiagonalWindowCochainSystem A k S T v (r₀ + C) where
  app r := openSupportCochainTranslation A (-a.val)
    (dualDiagonalWindowSystem_translation A S T u a b C bound r₀ r) k
  naturality {r t} f := by
    exact openSupportCochainTranslation_square A k
      (U₀ := dualDiagonalWindowSupport A S T u (r₀ + r))
      (U₁ := dualDiagonalWindowSupport A S T u (r₀ + t))
      (V₀ := dualDiagonalWindowSupport A S T v (r₀ + C + r))
      (V₁ := dualDiagonalWindowSupport A S T v (r₀ + C + t))
      (finiteU₀ := fun q => dualDiagonalWindowSupport_cellsFinite A S T u (r₀ + r) q)
      (finiteU₁ := fun q => dualDiagonalWindowSupport_cellsFinite A S T u (r₀ + t) q)
      (finiteV₀ := fun q => dualDiagonalWindowSupport_cellsFinite A S T v (r₀ + C + r) q)
      (finiteV₁ := fun q => dualDiagonalWindowSupport_cellsFinite A S T v (r₀ + C + t) q)
      (-a.val)
      (dualDiagonalWindow_mono A S T u (Nat.add_le_add_left f.le r₀))
      (dualDiagonalWindow_mono A S T v (Nat.add_le_add_left f.le (r₀ + C)))
      (dualDiagonalWindowSystem_translation A S T u a b C bound r₀ r)
      (dualDiagonalWindowSystem_translation A S T u a b C bound r₀ t)

/-- Multiplication by the monomial pair on the actual compact-support
complex, induced by its genuine finite-stage maps. -/
def dualDiagonalCompactMonomialMap (r₀ : ℕ) :
    dualDiagonalCompactCochainComplex A k S T u r₀ ⟶
      dualDiagonalCompactCochainComplex A k S T v (r₀ + C) :=
  colim.map (dualDiagonalWindowMonomialMap A k S T u a b C bound r₀)

/-- A nonempty source starting window gives a nonempty target starting
window. The full strip need not be bounded. -/
theorem dualDiagonalWindowMonomial_nonempty {r₀ : ℕ}
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    (dualDiagonalWindow A S T v (r₀ + C)).Nonempty := by
  obtain ⟨x, hx⟩ := h₀
  exact ⟨x + latticeLift (-a.val),
    dualDiagonalWindow_monomial_translation A S T u a b r₀ C bound ⟨x, hx, rfl⟩⟩

/-- The genuine compact-support monomial map sends the chosen top class
to the same top class, with no scalar or orientation ambiguity. -/
theorem dualDiagonalCompactMonomialMap_topClass (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    HomologicalComplex.homologyMap
        (dualDiagonalCompactMonomialMap A k S T u a b C bound r₀) n ≫
      (dualDiagonalCompactTopClassIso A k S T v (r₀ + C)
        (dualDiagonalWindowMonomial_nonempty A S T u a b C bound h₀)).hom =
    (dualDiagonalCompactTopClassIso A k S T u r₀ h₀).hom := by
  apply homologyColimitClassIso_natural k n
    (dualDiagonalWindowCochainSystem A k S T u r₀) (ModuleCat.of k k)
    (dualDiagonalWindowTopHomologyIso A k S T u r₀ h₀)
    (dualDiagonalWindowCochainSystem A k S T v (r₀ + C))
    (dualDiagonalWindowTopHomologyIso A k S T v (r₀ + C)
      (dualDiagonalWindowMonomial_nonempty A S T u a b C bound h₀))
    (dualDiagonalWindowMonomialMap A k S T u a b C bound r₀)
  intro r
  exact openSupportCochainTopClassIso_translation A (-a.val)
    (dualDiagonalWindowSystem_translation A S T u a b C bound r₀ r) k
    (dualDiagonalWindow_convex A S T u (r₀ + r))
    (dualDiagonalWindow_convex A S T v (r₀ + C + r))
    (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
    (dualDiagonalWindow_tail_nonempty A S T v
      (dualDiagonalWindowMonomial_nonempty A S T u a b C bound h₀) r)
    (dualDiagonalWindow_bounded A S T u (r₀ + r))
    (dualDiagonalWindow_bounded A S T v (r₀ + C + r))

end ToricPower.IntegralArrangement
