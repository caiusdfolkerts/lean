module

public import RootedCellLookup
public import RootedFacetCoverage

@[expose] public section

namespace Papers.RationalityTen.RootedCellLookupSemantics

open LiteralMaskGeometry RawFacetEmbeddingSemantics RootedFacetCoverage

/-- Transfer a complete geometric source universe to the literal rooted
universe. Every source index is checked; producer membership alone is never
used as a completeness premise. -/
theorem lookup_geometry {s t : Nat} (source : Fin s → ConcreteGrowth.Cell)
    (root : ConcreteGrowth.Cell) (target : Fin t → ConcreteGrowth.Cell)
    (allowed : Nat → Bool) (witness : Fin s → Fin t)
    (hsource : ∀ i, WellFormed (source i)) (hroot : WellFormed root)
    (hchecks : ∀ i, RootedCellLookup.check source root target allowed witness i = true)
    (i : Fin s) (hallowed : allowed (source i).kind = true)
    (hcompatible : (decodeCell (source i)).Compatible (decodeCell root)) :
    (target (witness i)).kind = (source i).kind ∧
      decodeCell (target (witness i)) = decodeCell (source i) := by
  have hc := compatible_of_geometry (source i) root
    (bounds_of_wellFormed _ (hsource i)) (bounds_of_wellFormed _ hroot) hcompatible
  obtain ⟨hk, hg⟩ := RootedCellLookup.check_sound source root target allowed witness i
    (hchecks i) hallowed hc
  exact ⟨hk, sameGeometry_decoded hg⟩

end Papers.RationalityTen.RootedCellLookupSemantics
