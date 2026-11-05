module
prelude
public import Papers.RawWitnesses.Type85Data

/-! Small ordinary kernel checks for Appendix B type 85. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type85
open Papers.RationalWitnesses.Raw

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 := by decide +kernel

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, (certificate.facets k).vertices i = true ∧
      (certificate.facets k).vertices j ≠ true := by decide +kernel

end Papers.RationalWitnesses.RawWitnesses.Type85
