module

public import ToricPower.ArrangementLaurentWeightSum
public import ToricPower.ModuleDirectSumSupport

/-!
# Full-character homology of the actual representable cellular complex

The unrestricted Laurent complex splits into its genuine character
fibers. Every fiber is an actual relative cellular costalk complex.
Consequently all degrees except the ambient degree vanish. In the top
degree, precisely the characters with nonempty geometric support remain,
with the coefficient supplied by the fixed ambient orientation.

These are isomorphisms of scalar modules. Compatibility with the affine
coordinate-ring action and with chart restriction is proved separately;
it is not inferred from this scalar calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (k : Type) [Field k]

/-- The exact geometric support condition, with every integral character
retained until its actual fiber is computed. -/
def RepresentableSupportedWeight (m : Fin n → ℤ) : Prop :=
  (costalkRegion (augmentedForms A) (Sum.inl '' S)
    (augmentedLatticePairing A m) (incidenceCellCenter A c)).Nonempty

/-- Every character fiber vanishes outside the ambient degree, including
fibers whose geometric support is empty. -/
theorem representedWeightHomology_isZero_off_top (m : Fin n → ℤ)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((representedWeightCellularComplex A S c m k).homology q) := by
  by_cases supported : RepresentableSupportedWeight A S c m
  · exact representedWeightCellularComplex_isZero_homology A S c m k
      supported q different
  · exact representedWeightCellularComplex_isZero_homology_of_empty A S c m k
      (Set.not_nonempty_iff_eq_empty.mp supported) q

/-- The actual full Laurent complex is concentrated in ambient
cohomological degree. This uses the whole direct sum of all characters. -/
theorem representableLaurentHomology_isZero_off_top
    (q : ℕ) (different : q ≠ n) :
    IsZero ((representableLaurentCellularComplex A S k c).homology q) := by
  letI (m : Fin n → ℤ) :
      Subsingleton ((representedWeightCellularComplex A S c m k).homology q) :=
    ModuleCat.subsingleton_of_isZero
      (representedWeightHomology_isZero_off_top A S c k m q different)
  have zero : IsZero (ModuleCat.of k (Π₀ m : Fin n → ℤ,
      (representedWeightCellularComplex A S c m k).homology q)) :=
    ModuleCat.isZero_of_subsingleton _
  exact zero.of_iso (representableCellularHomologyWeightSumIso A S c k q)

/-- Omitting a character is justified by the vanishing of its actual
relative cellular cohomology, not by a finiteness assumption. -/
theorem representableUnsupportedWeight_subsingleton (m : Fin n → ℤ)
    (unsupported : ¬ RepresentableSupportedWeight A S c m) :
    Subsingleton ((representedWeightCellularComplex A S c m k).homology n) :=
  ModuleCat.subsingleton_of_isZero
    (representedWeightCellularComplex_isZero_homology_of_empty A S c m k
      (Set.not_nonempty_iff_eq_empty.mp unsupported) n)

/-- Top homology is exactly the unrestricted monomial module on the
geometrically permitted characters, over the original coefficient field. -/
def representableLaurentTopHomologyIso :
    (representableLaurentCellularComplex A S k c).homology n ≅
      ModuleCat.of k ({m : Fin n → ℤ // RepresentableSupportedWeight A S c m} →₀ k) :=
  representableCellularHomologyWeightSumIso A S c k n ≪≫
    (directSumSubtypeEquiv k
      (fun m : Fin n → ℤ => (representedWeightCellularComplex A S c m k).homology n)
      (RepresentableSupportedWeight A S c)
      (representableUnsupportedWeight_subsingleton A S c k)).toModuleIso ≪≫
    (DFinsupp.mapRange.linearEquiv (fun m :
      {m : Fin n → ℤ // RepresentableSupportedWeight A S c m} =>
      (representedWeightCellularHomologyIso A S c m.val k m.property).toLinearEquiv)).toModuleIso ≪≫
    (finsuppLequivDFinsupp k).symm.toModuleIso

end ToricPower.IntegralArrangement

end
