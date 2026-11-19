module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00000Data
public import GraphInputsRow30Part00000Frames
public import GraphInputsRow30Part00000Leaves
public import GraphInputsRow30Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00000.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec370f23a8da2d8ae278e939475334ad1b4e31cccb2ac6b29c3723c2f362d49d2cca725cb4a72b2a9a96a968da8e87a71996558d64d98e538ce4b89e1783eb46b19c6c9aa669a6659366392e479715a5354b5334ad2745d0f5c358cd31cccb1ac9b16c3b61d4731d2725c5723c4f07fc0b42c8498360b8d1324950d48d0b4530cc4b0ac2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "26d369b6db6db6db6db6db6db6db6db6d36d369369b6d36db4924d36924d26da492449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000000006420ea7b0f80000", 1099511627776, hexnat% "22000000001000000", hexnat% "1200000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000000226420aa531880000", 8594128896, 5497558138880, hexnat% "1200000000000000000000000000", 2150629376]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22402000001000000", hexnat% "1240000000000240000000000000", 11543248896, 6184752906240, 21485322240, 10995121520640]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00000.record006
