module

public import ToricPower.DualDiagonalWeightComplex

/-!
# Dual-diagonal weights are genuine compact-support cochains

The original cellular complex of the two literal Laurent label factors
is isomorphic to the filtered colimit of actual bounded relative CW
cochains. The isomorphism is verified through the original incidence
matrices, not used to define either differential. Consequently each
nonempty strip contributes one scalar in the ambient degree and nothing
else, while an empty strip contributes zero in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (u : Fin n → ℤ) (k : Type) [Field k]

local instance dualComparisonPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local notation "K" => dualDiagonalWeightComplex A S T u k
local notation "indices" => DualDiagonalStripCell A S T u

theorem dualDiagonalCompactCoordinates_d_generator (r₀ q : ℕ)
    (i : indices q) (j : indices (q + 1)) (r : k) :
    dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
        ((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)
          ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm
            (Finsupp.single i r))) j =
      TauCeti.cellularIncidence (arrangementCarrier A) k q i.val j.val * r := by
  have scalar : Finsupp.single i r = r • Finsupp.single i (1 : k) := by simp
  rw [scalar, map_smul, map_smul, map_smul, Finsupp.smul_apply,
    dualDiagonalCompactCoordinates_differential_single]
  exact mul_comm _ _

/-- The independently constructed complexes have the same complete
differential on arbitrary finitely supported coefficients. -/
theorem dualDiagonalWeightCompact_differential (r₀ q : ℕ) (v : indices q →₀ k) :
    dualDiagonalWeightCoordinates A S T u k (q + 1)
      ((K).d q (q + 1) ((dualDiagonalWeightCoordinates A S T u k q).symm v)) =
    dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
      ((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)
        ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm v)) := by
  let actual : (indices q →₀ k) →ₗ[k] (indices (q + 1) →₀ k) :=
    (dualDiagonalWeightCoordinates A S T u k (q + 1)).toLinearMap.comp
      (((K).d q (q + 1)).hom.comp
        (dualDiagonalWeightCoordinates A S T u k q).symm.toLinearMap)
  let geometric : (indices q →₀ k) →ₗ[k] (indices (q + 1) →₀ k) :=
    (dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)).toLinearMap.comp
      (((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)).hom.comp
        (dualDiagonalCompactCoordinates A S T u k r₀ q).symm.toLinearMap)
  have equal : actual = geometric := by
    apply Finsupp.lhom_ext
    intro i r
    ext j
    obtain ⟨i', rfl⟩ := (dualDiagonalWeightCellEquiv A S T u q).surjective i
    obtain ⟨j', rfl⟩ := (dualDiagonalWeightCellEquiv A S T u (q + 1)).surjective j
    exact (dualDiagonalWeightCoordinates_d_generator A S T u k q i' j' r).trans
      (dualDiagonalCompactCoordinates_d_generator A S T u k r₀ q _ _ r).symm
  exact DFunLike.congr_fun equal v

def dualDiagonalWeightCompactTermIso (r₀ q : ℕ) :
    (K).X q ≅ (dualDiagonalCompactCochainComplex A k S T u r₀).X q :=
  ((dualDiagonalWeightCoordinates A S T u k q).trans
    (dualDiagonalCompactCoordinates A S T u k r₀ q).symm).toModuleIso

/-- An isomorphism of the actual full complexes in every integral
weight, with no restriction on the size or recession of the strip. -/
def dualDiagonalWeightCompactIso (r₀ : ℕ) :
    K ≅ dualDiagonalCompactCochainComplex A k S T u r₀ :=
  HomologicalComplex.Hom.isoOfComponents
    (dualDiagonalWeightCompactTermIso A S T u k r₀)
    (fun q r relation => by
      obtain rfl : r = q + 1 := relation.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply (dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)).injective
      change dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
          ((dualDiagonalCompactCochainComplex A k S T u r₀).d q (q + 1)
            ((dualDiagonalCompactCoordinates A S T u k r₀ q).symm
              (dualDiagonalWeightCoordinates A S T u k q v))) =
        dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)
          ((dualDiagonalCompactCoordinates A S T u k r₀ (q + 1)).symm
            (dualDiagonalWeightCoordinates A S T u k (q + 1) ((K).d q (q + 1) v)))
      rw [LinearEquiv.apply_symm_apply]
      have equal := dualDiagonalWeightCompact_differential A S T u k r₀ q
        (dualDiagonalWeightCoordinates A S T u k q v)
      rw [LinearEquiv.symm_apply_apply] at equal
      exact equal.symm)

/-- The nonempty actual dual-diagonal weight has the ambient top class. -/
def dualDiagonalWeightTopClassIso (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    (K).homology n ≅ ModuleCat.of k k :=
  let window := dualDiagonalStrip_exists_nonempty_window A S T u nonempty
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (dualDiagonalWeightCompactIso A S T u k window.choose) ≪≫
      dualDiagonalCompactTopClassIso A k S T u window.choose window.choose_spec

/-- All other cohomology of the actual dual-diagonal weight vanishes. -/
theorem dualDiagonalWeightComplex_isZero_homology
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) (q : ℕ) (different : q ≠ n) :
    IsZero ((K).homology q) := by
  obtain ⟨r₀, h₀⟩ := dualDiagonalStrip_exists_nonempty_window A S T u nonempty
  exact (dualDiagonalCompactCochainComplex_isZero_homology A k S T u r₀ h₀ q different).of_iso
    ((HomologicalComplex.homologyFunctor _ _ q).mapIso
      (dualDiagonalWeightCompactIso A S T u k r₀))

/-- An empty strip has no permitted cell in any degree. -/
theorem dualDiagonalWeightComplex_isZero_X_of_empty
    (empty : dualDiagonalStrip A S T u = ∅) (q : ℕ) : IsZero ((K).X q) := by
  letI : IsEmpty (indices q) := ⟨fun c => by
    have inside : cellCenter (augmentedForms A) c.val ∈ dualDiagonalStrip A S T u := c.property
    simpa only [empty, mem_empty_iff_false] using inside⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of k (indices q →₀ k))).of_iso
    (dualDiagonalWeightCoordinates A S T u k q).toModuleIso

theorem dualDiagonalWeightComplex_isZero_homology_of_empty
    (empty : dualDiagonalStrip A S T u = ∅) (q : ℕ) : IsZero ((K).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (dualDiagonalWeightComplex_isZero_X_of_empty A S T u k empty q)

end ToricPower.IntegralArrangement
