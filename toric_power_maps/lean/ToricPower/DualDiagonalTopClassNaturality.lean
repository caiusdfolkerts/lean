module

public import ToricPower.DualDiagonalMonomialComparison

/-!
# Choice-independent top classes and genuine monomial naturality

Changing the starting window changes neither the full finite-support
complex nor its ambient top class. The proof compares the actual maps
from finite windows into both colimits. This removes all dependence on
the chosen nonempty starting window before assembling the Laurent
cohomology into a module over the product-chart coordinate ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))
  (u : Fin n → ℤ) (k : Type) [Field k]

/-- The full compact complexes have the same literal cell coordinates
for every starting window. -/
def dualDiagonalCompactTailIso (r₀ r₁ : ℕ) :
    dualDiagonalCompactCochainComplex A k S T u r₀ ≅
      dualDiagonalCompactCochainComplex A k S T u r₁ :=
  (dualDiagonalWeightCompactIso A S T u k r₀).symm ≪≫
    dualDiagonalWeightCompactIso A S T u k r₁

/-- The change of starting window commutes with the actual support map
from every source window into a sufficiently large target window. -/
@[reassoc]
theorem dualDiagonalCompactTailIso_inclusion (r₀ r₁ r : ℕ) :
    colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r ≫
        (dualDiagonalCompactTailIso A S T u k r₀ r₁).hom =
      openSupportCochainExtension A k
          (U := dualDiagonalWindowSupport A S T u (r₀ + r))
          (V := dualDiagonalWindowSupport A S T u (r₁ + (r₀ + r)))
          (dualDiagonalWindow_mono A S T u (Nat.le_add_left _ _)) ≫
        colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₁) (r₀ + r) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (dualDiagonalCompactCoordinates A S T u k r₁ q).injective
  change dualDiagonalCompactCoordinates A S T u k r₁ q
      ((dualDiagonalCompactCoordinates A S T u k r₁ q).symm
        (dualDiagonalWeightCoordinates A S T u k q
          ((dualDiagonalWeightCoordinates A S T u k q).symm
            (dualDiagonalCompactCoordinates A S T u k r₀ q
              ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r).f q φ))))) =
    dualDiagonalCompactCoordinates A S T u k r₁ q
      ((colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₁) (r₀ + r)).f q
        ((openSupportCochainExtension A k
          (U := dualDiagonalWindowSupport A S T u (r₀ + r))
          (V := dualDiagonalWindowSupport A S T u (r₁ + (r₀ + r)))
          (dualDiagonalWindow_mono A S T u (Nat.le_add_left _ _))).f q φ))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    dualDiagonalCompactCoordinates_inclusion, dualDiagonalCompactCoordinates_inclusion,
    openSupportCochainExtension_coordinates A k
      (U := dualDiagonalWindowSupport A S T u (r₀ + r))
      (V := dualDiagonalWindowSupport A S T u (r₁ + (r₀ + r)))
      (dualDiagonalWindow_mono A S T u (Nat.le_add_left _ _)) q,
    ← Finsupp.mapDomain_comp]
  congr 1

/-- The fixed ambient top class is unchanged by changing the starting
window of the genuine compact-support colimit. -/
theorem dualDiagonalCompactTailIso_topClass (r₀ r₁ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty)
    (h₁ : (dualDiagonalWindow A S T u r₁).Nonempty) :
    HomologicalComplex.homologyMap (dualDiagonalCompactTailIso A S T u k r₀ r₁).hom n ≫
        (dualDiagonalCompactTopClassIso A k S T u r₁ h₁).hom =
      (dualDiagonalCompactTopClassIso A k S T u r₀ h₀).hom := by
  apply (isColimitOfPreserves (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n)
    (colimit.isColimit (dualDiagonalWindowCochainSystem A k S T u r₀))).hom_ext
  intro r
  change HomologicalComplex.homologyMap
      (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r) n ≫ _ =
    HomologicalComplex.homologyMap
      (colimit.ι (dualDiagonalWindowCochainSystem A k S T u r₀) r) n ≫ _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    dualDiagonalCompactTailIso_inclusion, HomologicalComplex.homologyMap_comp,
    Category.assoc, dualDiagonalCompactTopClassIso_inclusion,
    dualDiagonalCompactTopClassIso_inclusion]
  exact openSupportCochainTopClassIso_natural A k
    (U := dualDiagonalWindowSupport A S T u (r₀ + r))
    (V := dualDiagonalWindowSupport A S T u (r₁ + (r₀ + r)))
    (dualDiagonalWindow_mono A S T u (Nat.le_add_left _ _))
    (dualDiagonalWindow_convex A S T u (r₀ + r))
    (dualDiagonalWindow_convex A S T u (r₁ + (r₀ + r)))
    (dualDiagonalWindow_tail_nonempty A S T u h₀ r)
    (dualDiagonalWindow_tail_nonempty A S T u h₁ (r₀ + r))
    (dualDiagonalWindow_bounded A S T u (r₀ + r))
    (dualDiagonalWindow_bounded A S T u (r₁ + (r₀ + r)))

/-- The top class of the original complex may be computed using any
proved nonempty starting window. -/
theorem dualDiagonalWeightTopClassIso_eq_window
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) (r₀ : ℕ)
    (h₀ : (dualDiagonalWindow A S T u r₀).Nonempty) :
    (dualDiagonalWeightTopClassIso A S T u k nonempty).hom =
      HomologicalComplex.homologyMap (dualDiagonalWeightCompactIso A S T u k r₀).hom n ≫
        (dualDiagonalCompactTopClassIso A k S T u r₀ h₀).hom := by
  let window := dualDiagonalStrip_exists_nonempty_window A S T u nonempty
  have coherence := dualDiagonalCompactTailIso_topClass A S T u k
    window.choose r₀ window.choose_spec h₀
  have result := congrArg (fun f =>
    HomologicalComplex.homologyMap
      (dualDiagonalWeightCompactIso A S T u k window.choose).hom n ≫ f) coherence
  simp only [dualDiagonalCompactTailIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMap_comp, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp] at result
  exact result.symm

variable (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

/-- The chosen ambient top classes of the original weight complexes
commute with the actual monomial multiplication maps. -/
theorem dualDiagonalWeightMonomialMap_topClass
    (nonempty : (dualDiagonalStrip A S T u).Nonempty)
    (targetNonempty : (dualDiagonalStrip A S T (u + a.val + b.val)).Nonempty) :
    HomologicalComplex.homologyMap (dualDiagonalWeightMonomialMap A S T u a b k) n ≫
        (dualDiagonalWeightTopClassIso A S T (u + a.val + b.val) k targetNonempty).hom =
      (dualDiagonalWeightTopClassIso A S T u k nonempty).hom := by
  obtain ⟨C, bound⟩ := latticeLift_exists_coordinateMargin (-a.val)
  obtain ⟨r₀, h₀⟩ := dualDiagonalStrip_exists_nonempty_window A S T u nonempty
  rw [dualDiagonalWeightTopClassIso_eq_window A S T u k nonempty r₀ h₀,
    dualDiagonalWeightTopClassIso_eq_window A S T (u + a.val + b.val) k targetNonempty
      (r₀ + C) (dualDiagonalWindowMonomial_nonempty A S T u a b C bound h₀)]
  exact dualDiagonalWeightMonomialMap_topClass_atWindow A S T u a b k C bound r₀ h₀

end ToricPower.IntegralArrangement
