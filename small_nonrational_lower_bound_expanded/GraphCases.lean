module
public meta import Lean.Elab.Command

/-! Assemble the finite graph cases using their original geometric obligations.
The command arguments are the RawData record, budget row, complement-graph
mask, checked catalogue candidate and quota. Row 32 uses the six-facet
universe. All other input rows use the small-facet universe. -/
public meta section
open Lean

syntax (name := certifiedGraphCase) "certified_graph_case " ident num num ident num : command
macro_rules
 | `(certified_graph_case $record $row $mask $candidate $quota) => do
  let localId (suffix : String) := mkIdentFrom record (record.getId.appendAfter suffix)
  let i := mkIdent
  let valid := localId "_validity"
  let cells := localId "_cells_exact"
  let core := localId "_core"
  let parameters := localId "_parameters"
  let coverage := localId "_coverage"
  let result := localId "_result"
  let candidateChecked := mkIdentFrom candidate (candidate.getId.appendAfter "_checked")
  let isSix := row.getNat == 32
  let facetCells := i (if isSix then `FacetUniverses.FullSix0.cells else `FacetUniverses.FullSmall.cells)
  let graphRows := i (if isSix then `SharedSix0Incidence.graphRows else `SharedSmallGraph.graphRows)
  let allowed := i (if isSix then `GraphEmbeddingCoverage.sixAllowed else `SharedSmallGraph.allowedMask)
  let allowedProof := i (if isSix then `GraphCoverageDescriptions.six_allowed else `GraphCoverageDescriptions.small_allowed)
  let edges := i (if isSix then `GraphEmbeddingCoverage.six_edges else `GraphEmbeddingCoverage.small_edges)
  let coreCmd ← `(command| theorem $core : $(i `Core) $record where
    matrix := $(localId "_matrix_checked")
    valid := $valid
    literal := $(localId "_literal")
    nodes := $(localId "_raw_node_checks") $valid
    leaf_nodup := $(localId "_leaves_nodup")
    frames := $(localId "_frames_supported") $cells
    root_empty := by decide +kernel
    leaves_checked := ⟨$(localId "_certificates"), $(localId "_leaf_certificates_checked")⟩)
  let parametersCmd ← `(command| theorem $parameters :
      $(i `Parameters) $record ($(i `rowOfCode) $row) $mask where
    kind_count := by decide +kernel
    quota := by decide +kernel
    required := by decide +kernel
    internal_missing := by decide +kernel
    minimum_incidence := by decide +kernel)
  let coverageCmd ← `(command| theorem $coverage : $(i `Coverage) $record $facetCells $graphRows $mask :=
    $(i `GraphCoverageDescriptions.coverage_of_checked) $record $candidate $facetCells $graphRows
      ($allowed ($(i `GraphCoverageDescriptions.quota) $quota)) $mask
      (by rfl) $cells ($allowedProof $record $quota (by decide +kernel)) $edges $candidateChecked)
  let resultCmd ← if isSix then
    `(command| theorem $result : $(i `Result) ($row, $mask) :=
      $(i `of_six) $mask ⟨$record, $core, $parameters, $coverage⟩)
  else
    `(command| theorem $result : $(i `Result) ($row, $mask) :=
      $(i `of_small) $row $mask (by decide) ⟨$record, $core, $parameters, $coverage⟩)
  return mkNullNode #[coreCmd,parametersCmd,coverageCmd,resultCmd]
