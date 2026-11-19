module
prelude
public import Papers.RawWitnesses.TypeD0Spanning
public import Papers.RawWitnesses.TypeD0Facets
public import Papers.RawWitnesses.TypeD0LowRanks
public import Papers.RawWitnesses.TypeD0Relations
public import Papers.RawWitnesses.TypeD0Coverage
public import Papers.RawWitnesses.TypeD0Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD0
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.TypeD0
