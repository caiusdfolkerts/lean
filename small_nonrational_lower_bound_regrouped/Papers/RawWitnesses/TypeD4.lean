module
prelude
public import Papers.RawWitnesses.TypeD4Spanning
public import Papers.RawWitnesses.TypeD4Facets
public import Papers.RawWitnesses.TypeD4LowRanks
public import Papers.RawWitnesses.TypeD4Relations
public import Papers.RawWitnesses.TypeD4Coverage
public import Papers.RawWitnesses.TypeD4Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD4
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.TypeD4
