module
prelude
public import Papers.RawWitnesses.Type85Spanning
public import Papers.RawWitnesses.Type85Facets
public import Papers.RawWitnesses.Type85LowRanks
public import Papers.RawWitnesses.Type85Relations
public import Papers.RawWitnesses.Type85Coverage
public import Papers.RawWitnesses.Type85Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type85
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Type85
