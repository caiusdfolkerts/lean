module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00078Data
public import GraphInputsRow26Part00078Frames
public import GraphInputsRow26Part00078Leaves
public import GraphInputsRow26Part00078Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007
def vertexColumn : Fields := ⟨10, hexnat% "2789d26cc729c6725c8f13c2f07c9ab1aa699a8e93a2ea66c5a9665a364d8b6c3a8e63a4e538ce8b92e2b86e8791e2783e666594e4b91e595955352d4756364d534cd4b4ad1b61d4749d1743d64d332cd8b92d4b32d2b2ae1b46c9b0ed8791d4731d2729e1745c970de0f43c8f13c2f07e4a1aa4619869464990e465454950d46342c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db4db6da6db6db69b6da6db4d249a49b6db4d269b6924934924924d24d2499249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410bdc0b4008023c00000", hexnat% "8100000000000000000000000", 35218731827200, 101334384640, 103766409871360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410bdc0b4004013c00000", hexnat% "8100000000000000000000000", 35218731827200, 101602820096, 104041287778304]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81004102900307ee103c00000", hexnat% "900004000000000000", 4647714815580569600, 130996502528, hexnat% "48000000030000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15c034061fbbc00000", hexnat% "8100410000000000000000000", hexnat% "80080002000000000", 131941395333120, hexnat% "a0000000c000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81004108400307ef083c00000", hexnat% "380004000000000000", 64424509440, 4647714815580569600, hexnat% "18000000030000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25c034441fbbc00000", hexnat% "8100410000000000000000000", hexnat% "80080002000000000", 63771674411008, hexnat% "90000000c000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b880347ee183c00000", hexnat% "8100410000000000000000000", 4647714815580569600, 128849018880, hexnat% "50000000030000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100410840030461fbbc00000", hexnat% "1c004000000000000", 61572651155456, hexnat% "30000000e000000000", hexnat% "80080000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4100840b47e3f8bc00000", hexnat% "8100000000000000000000000", hexnat% "58000000030000000", hexnat% "b0000000c000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000000000307eff83c00000", hexnat% "b80004000000000000", hexnat% "410000080000000000000", hexnat% "58000000038000000", 4611686018427387904]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000000000307e1180c00000", hexnat% "100000000000000e00000000", hexnat% "84084000000000000", hexnat% "58000000038000000", hexnat% "b0000000e000000000", hexnat% "410000000000003000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010
def vertexColumn : Fields := ⟨10, hexnat% "9b19c9715c3713c2f07c9a99a568da4e8ba1ea6665956359362d876c3a8e63a4e538ce8b92e2b86e4789e1783e9a599965392e47999595955352d475c368d6364d8b52d2b46d8751d2745d0f66364d332cc73c2e8b62e4b8ad2b2ac6b46c9b16c3bc1e8761e4789d2729c6745c9715c3783d0f23c4f0bc1f1e0749286a91866464990e5152543582d0b22c2b81d0721c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da4db6d26db69b69b6da6db69a49a6926db6db6934db6d24924926924924926924d3249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1810041000000683bc7bc7a00000", hexnat% "4100000400400000000", hexnat% "1600000000030000000", hexnat% "58000000030000000000", hexnat% "20400000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400059600683bb4035200000", hexnat% "810041000000000000000000000", hexnat% "4100000440440000000", hexnat% "1000000000000000000002800000", 255550554112]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400059600683bb4034a00000", hexnat% "810041000000000000000000000", hexnat% "4100000440440000000", hexnat% "1000000000000000000003000000", 255550554112]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400059600680037bb5200000", hexnat% "810041000000000000000000000", hexnat% "4100000440440000000", hexnat% "1000000000000000000002800000", 1046735069642752]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400059600680037bb4a00000", hexnat% "810041000000000000000000000", hexnat% "4100000440440000000", hexnat% "1000000000000000000003000000", 1046735069642752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1810041000000683bb3bb3a00000", hexnat% "1700000000004000000", hexnat% "5c000000004000000000", 74785044299776, hexnat% "20400000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30440001700080037ff5a00000", hexnat% "5c000000000000000000", hexnat% "800001000000000040000000000", hexnat% "1000000000000600000002000000", 1117103813820416]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1810041000000683fb3fb7a00000", hexnat% "1700000000000000000", hexnat% "400000000000000040000000", hexnat% "5c000000004000000000", hexnat% "20000000000000040000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1820401005700080470477a00000", hexnat% "10040000000000000000000000", 255550554112, hexnat% "58000600000000000000", 1047009947549696]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1020401000100000030037a00000", 273804165120, hexnat% "1600680000000000000", hexnat% "810040000000000000000000000", 1121501860331520, hexnat% "5c000000004000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c13 c5
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c14 c4
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c18 c0
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010
