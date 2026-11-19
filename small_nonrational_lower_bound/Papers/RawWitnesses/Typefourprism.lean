module
prelude
public import Papers.RawWitnesses.TypefourprismSpanning
public import Papers.RawWitnesses.TypefourprismFacets
public import Papers.RawWitnesses.TypefourprismLowRanks
public import Papers.RawWitnesses.TypefourprismRelations
public import Papers.RawWitnesses.TypefourprismCoverage
public import Papers.RawWitnesses.TypefourprismPositivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typefourprism
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Typefourprism
