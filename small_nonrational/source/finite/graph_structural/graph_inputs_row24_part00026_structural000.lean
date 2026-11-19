module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00026Data
public import GraphInputsRow24Part00026Frames
public import GraphInputsRow24Part00026Leaves
public import GraphInputsRow24Part00026Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015
def vertexColumn : Fields := ⟨10, hexnat% "d93349b13c1f3329a8ba1eb2699b168d9361da4e33a2e1b85e0fb614e4b91e745c9665595954d4753352d1b51d1743dc8e634ccb31cccb2ac5bc1e4731e2749c6745c570dc2f272621a89a0ea462588e1381e4c46926439454952344d0746324c3322c4b0ac1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4934db6934934936da4d3492692492693692489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6004612f1b0340000000", 9259436020393312256, hexnat% "200000042000000000", hexnat% "88080000400400000000", hexnat% "400000004000000000", hexnat% "20000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e06e20024b6140000000", 11263397114937344, 13835110831840296960, 109493776677863424, hexnat% "8000000000400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8080002400400000000", 109493776677863424, hexnat% "40004000130000000000", hexnat% "200020042040000000", hexnat% "440000004100000000", 11529259026533580800, hexnat% "20008000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record044
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044
def vertexColumn : Fields := ⟨10, hexnat% "1f362caa6a9687ad196635876c3a4e4b8ae1b85e0fb61ca66996479d156535475c364d4b4ad1b45d0f743c8e6358e5334c73c2e8b92e2b4acab1ae1b16c3bc1d8791d4731ca745c3783d0f13c9c26926198961588e0b81e26525194951548d0b41dc0e4348c6324c5382c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6926d24936db6926d2492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fcf9fcf9e2f8ffe00000000", hexnat% "2000200080000000000000", hexnat% "40004000200000000000", 4591560557592576, hexnat% "1020102040000000000000", 72057594037927936]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeff9e3d7f5ffe00000000", hexnat% "100010000000000000000", hexnat% "400200000000000000", hexnat% "200080000000000000", 13835233977142607872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeff9c3ffff3de00000000", hexnat% "100010000000000000000", 13331578486784, hexnat% "428000000000000000", hexnat% "204000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffbfee7ffffe00000000", hexnat% "100000000000000000000", 108086391056891904, hexnat% "401000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdfee7ffbde00000000", 4535485464576, 1224979098644774912, hexnat% "200080000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeff9eee77dffe00000000", hexnat% "100010000000000000000", hexnat% "200080000000000000", hexnat% "401000000000000000", 74344578223702016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffbc7feeb3f200000000", hexnat% "438000000000000000", 13245679140864, 4855443348258816, hexnat% "100000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff9d35fff3de00000000", hexnat% "204000002000000000", 576473946442956800, hexnat% "400200000000000000", hexnat% "28000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffdffeffbf200000000", hexnat% "20000000400000000", 4432406249472, 4503599627370496]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffbde7eef3f200000000", hexnat% "420000000000000000", hexnat% "100000001000c00000000", 576473946442956800, 1157425104234217472]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffbc64e653f200000000", hexnat% "438000000000000000", hexnat% "100000001000c00000000", 576473946442956800, 1369094286720630784, 6931321301499904]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9e3ffefd7f5ffe00000000", hexnat% "100010000000000000000", hexnat% "4000000200000000000000", hexnat% "2000000080000000000000", hexnat% "c0000000a00000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9c3ffefffff3de00000000", hexnat% "100010000000000000000", 13331578486784, hexnat% "4280000000000000000000", hexnat% "2040000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbffffeee7ffffe00000000", hexnat% "10000000000000000", 108086391056891904, hexnat% "4000001000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdfffffee7ffbde00000000", 4535485464576, 1224979098644774912, hexnat% "2000000080000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9efffeee77dffe00000000", hexnat% "100010000000000000000", hexnat% "2000000080000000000000", hexnat% "4000001000000000000000", 74344578223702016]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbc7ffeffeeb3f200000000", hexnat% "4380000000000000000000", 13245679140864, 4855443348258816, hexnat% "10000000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9d3ffff5fff3de00000000", hexnat% "2040000000002000000000", 576473946442956800, hexnat% "4000000200000000000000", hexnat% "280000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c11 c10
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdffffffeffbf200000000", hexnat% "200000000000400000000", 4432406249472, 4503599627370496]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbdfffee7eef3f200000000", hexnat% "4200000000000000000000", hexnat% "10001000c00000000", 576473946442956800, 1157425104234217472]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbc7ffee4e653f200000000", hexnat% "100010001000c00000000", hexnat% "4280000000000000000000", 576473946442956800, 1369094286720630784, 6931321301499904]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c39 c32
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c42 c25
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c43 c24
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbc1fbc008000f000000000", hexnat% "43a000000000000000", hexnat% "43a0000000000000000000", 576475063134453760, hexnat% "40004008a00200000000", 15569119009046528, 1675341260405080064]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c47 c0
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00026.record044_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00026.record044
