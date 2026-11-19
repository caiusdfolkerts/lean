module
prelude
public import Papers.RawWitnesses.TypeA73Spanning
public import Papers.RawWitnesses.TypeA73Facets
public import Papers.RawWitnesses.TypeA73LowRanks
public import Papers.RawWitnesses.TypeA73Relations
public import Papers.RawWitnesses.TypeA73Coverage
public import Papers.RawWitnesses.TypeA73Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA73
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.TypeA73
