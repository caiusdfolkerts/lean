module

public import CompletedSmall.RootedRows

@[expose] public section

/-! The complete nineteen-row list is discharged by the exact certificates. -/

namespace Papers.RationalityTen.CompletedSmall
open ChirotopeDensity

/-- The literal list is definitionally the `rootedBudgets` list in the
actual geometric assembly. Keeping this finite theorem independent of that
larger assembly avoids loading unrelated geometry during the nineteen cases. -/
theorem rooted_complete :
    ∀ B ∈ ([⟨11, 10, 0⟩, ⟨11, 10, 1⟩, ⟨11, 11, 0⟩, ⟨11, 11, 1⟩, ⟨11, 11, 2⟩,
      ⟨12, 10, 0⟩, ⟨12, 10, 1⟩, ⟨12, 11, 0⟩, ⟨12, 11, 1⟩, ⟨12, 11, 2⟩,
      ⟨12, 12, 1⟩, ⟨12, 12, 2⟩, ⟨12, 12, 3⟩, ⟨13, 10, 0⟩,
      ⟨13, 11, 0⟩, ⟨13, 11, 1⟩, ⟨13, 12, 2⟩, ⟨13, 12, 3⟩, ⟨13, 13, 4⟩] :
      List SmallFacetBudget),
      Nonempty (RootedFamilyClosure.FiniteClassification FacetUniverses.Small.cells
        (SmallFacetTargetBudgets.quota B.m B.E B.q) FacetUniverses.Small.root) := by
  intro B hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Row02.classification⟩
  · exact ⟨Row03.classification⟩
  · exact ⟨Row04.classification⟩
  · exact ⟨Row05.classification⟩
  · exact ⟨Row06.classification⟩
  · exact ⟨Row07.classification⟩
  · exact ⟨Row08.classification⟩
  · exact ⟨Row09.classification⟩
  · exact ⟨Row10.classification⟩
  · exact ⟨Row11.classification⟩
  · exact ⟨Row12.classification⟩
  · exact ⟨Row13.classification⟩
  · exact ⟨Row14.classification⟩
  · exact ⟨Row15.classification⟩
  · exact ⟨Row17.classification⟩
  · exact ⟨Row18.classification⟩
  · exact ⟨Row20.classification⟩
  · exact ⟨Row21.classification⟩
  · exact ⟨Row22.classification⟩

#print axioms rooted_complete
end Papers.RationalityTen.CompletedSmall
