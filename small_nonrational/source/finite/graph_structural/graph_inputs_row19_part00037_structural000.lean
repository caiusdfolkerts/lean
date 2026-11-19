module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00037Data
public import GraphInputsRow19Part00037Frames
public import GraphInputsRow19Part00037Leaves
public import GraphInputsRow19Part00037Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018
def vertexColumn : Fields := ⟨10, hexnat% "cd29c970dccca9a968dac9b16a59969595635a364da8e938ce8b92e2b86e8789e178d965555356354d4cd8b52d2b46d8749d1759354cd38cd3332e2b4acab1ae1b26c5b61d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f8b22a49515254552344d0b52344c9314c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db4db6db49349249a49269249349b6d36d24db493249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80e817408238e0000", 140754668224512, 9008298766368768, 3161095929856, 25895697857380352]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80e80f404238e0000", 281509336449024, 9008298766368768, 3161095929856, 25895697857380352]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8006d0368238e0000", 4504149383184384, 140754668224512, 127543348822016, 1044835113549955072]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8006c8364238e0000", 4504149383184384, 281509336449024, 127543348822016, 1044835113549955072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1030748222174003200, 13510798882242560, 36028797555834880, 4260607557632, hexnat% "80000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800fd0180218e0000", 127543382376448, 2662879723520, 1008947054019346432]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800110000238e0000", 30399297484750848, 1044835113549955072, 4260607557632, 127543348822016, 140789027962880]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023
def vertexColumn : Fields := ⟨10, hexnat% "cb0dc8f13c2f07cca8da2e87ac98d62d876c3a8e63a4e538ce8b92e2b86e2785e0fb29366394e725356354d70da358d9354d3362d4b61d4749d1743dc8cd3c2e8b62e4b52ccb8ad2b26c5b0ef07a1d8791d4731e2749c9715c3783d0f23c4f0bc1f8a92a89926264592545582d0b22c4b81d0721c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4db4db6db6d26db6d36d36db6db6da4db49249249a4924924d249b249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22001800000000000", hexnat% "8803000000000000000000", 51564773376, 206259093504, 8459649024, 17317308137472]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record023
