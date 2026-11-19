module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00032Data
public import GraphInputsRow23Part00032Frames
public import GraphInputsRow23Part00032Leaves
public import GraphInputsRow23Part00032Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003
def vertexColumn : Fields := ⟨10, hexnat% "23c7195635a361d98e538ce8b92e2ba1e4789e179c5554d58d4756354d3362d4b4ad8751d2745d70e5354cd31cf0ba2d8b52ccb4acab46c9b16d8789d2729c6785d1725e0f13e380f2328aa1a0e946318560d90e2382e07a318a6190e545314550d50d2342d0754330e2384c530ce0b42c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4424084800008900000000000", hexnat% "f8020000000000000", 9205366434438316032, hexnat% "3b700000000000000000", hexnat% "740000001000000000000", hexnat% "1db800000000000000000000", hexnat% "3a00000000000000000000000", 6298002603900928]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008
def vertexColumn : Fields := ⟨10, hexnat% "9595635a2e4b8ae879d16a565c565535535c354d8b4ad8751d38e9394d532ce8b32e2b4ae1b26e4751cc789d2729c6745c970dd0f23c4f07d544b0d22aa1615a0e0b951345292a54549615454558350d0b4c328e1324c5382c8b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "127744427db600000000", hexnat% "88800000000000000", hexnat% "20800000000000000000", hexnat% "4002004000800000000", hexnat% "9001000024000000000", 232076118297935872, 36310271995674624]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460e01c7ffe00000000", hexnat% "100200000000000000", hexnat% "10020000000000000", hexnat% "20800000000000000000", hexnat% "3001002000000000000", 108508603521957888, hexnat% "c0c00000000000000", hexnat% "18020040000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "306f3cc660e600000000", hexnat% "800001080000000000", hexnat% "9000000120800000000", 232076118297935872, hexnat% "10c000001000000000", hexnat% "6000000000000000000", 5497558138880]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "327f4dc26df600000000", 12682136585035055104, hexnat% "800001800000000000", hexnat% "5000004000000000000", hexnat% "8000000120000000000", 159877786771652608]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d66b23ffbfe00000000", 126100789566373888, hexnat% "800c00000000000000", hexnat% "12000000040000000000", hexnat% "20000000000000000000", hexnat% "194000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1675fc566dbe00000000", hexnat% "a0000004000000000", hexnat% "20800000000000000000", 108508603521957888, hexnat% "9000000120000000000", 155374187144282112]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a4601e3f4fe00000000", 150870587516911616, hexnat% "203004000000000000", hexnat% "800800080000000000", hexnat% "100000010000000000", hexnat% "9c400000000000000", hexnat% "5000000000000000000", 2199023255552]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "640080209c00000000", hexnat% "7000000000000000000", hexnat% "38000000000000000000", hexnat% "19c400000000000000", 232076118297935872, hexnat% "800801480200000000", 7834020347904, hexnat% "20040104000000000", 3460453363680804864]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009
def vertexColumn : Fields := ⟨10, hexnat% "749aa9595635a2e4b8ae879d16a655554d58b52d2b61d70da358ce3c4e9364e534ccb3c2e8b62d4b32e2b86d1b26e4751cc789d2729c6745c970dd0f23c4f07d523492a2aa1615a0e0b951345292a6151560d0b54330d2328e1344c9314e0b42c8b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "807ffffb6da00000000", hexnat% "2380000000000000000", hexnat% "5c00000000000000000", hexnat% "470000000000000000000", hexnat% "b80000000000000000000", 80418967650304]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d2693fffffdfe00000000", hexnat% "240000000000000000", hexnat% "48000000000000000000", hexnat% "201000000000000000000", hexnat% "90480000020000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12896c63bfdb600000000", 55169129795026944, hexnat% "201000000004000000000", 4107282860161892352, hexnat% "40200000000000000000", hexnat% "c06010000000000000000", hexnat% "90480000020000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "984dc30fff6e00000000", hexnat% "40200000001000000000", 67553994410557440, 4323456192031490048, hexnat% "201000000000000000000", hexnat% "120900000000000000000", hexnat% "c06020000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c964bfffffbfe00000000", hexnat% "240000000000000000", hexnat% "48000000000000000000", hexnat% "201000000000000000000", hexnat% "120900000040000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "984ec53bfb6e00000000", 55169164154765312, hexnat% "201000000008000000000", 4179340454199820288, hexnat% "40200000000000000000", hexnat% "c06010000000000000000", hexnat% "120900000040000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0e07cb3fff2200000000", 54043315787530240, 3746995714605973504, hexnat% "380000000000000000", hexnat% "70000000000000000000", hexnat% "1c00000000000000000", hexnat% "380000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8050003fa0200000000", hexnat% "90480000004800000000", hexnat% "120900000049000000000", hexnat% "c06020820000000000000", hexnat% "40200004000400000000", hexnat% "201000400002000000000", 13835059154793791488, 60798594969501696, 3674937295934324736]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c0
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c14 c0
  c15
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013
def vertexColumn : Fields := ⟨10, hexnat% "29a8e956358768b92e2b86e8785e0fa998e555354758b52d2b46d8745d0f72398e9394d5334e331ce8b4acab1ac5b0ed8731e2729e1745c3783d0f13d64271628aa1a2694649866258562382e079618a6192654549465254552342d0754388d2318e1324c5382c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d5bc181828c80000000000", hexnat% "40040010440000000000000", 6526701022478336, hexnat% "60380000000000000", 16140901064495857664, hexnat% "3c00000000000000000", hexnat% "2a00000000000000000000", hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "647fcffbee5e80000000000", hexnat% "10000004008000000000000", 5084141766836224, hexnat% "8000000000000000000000", hexnat% "3000000000000000000", hexnat% "2800000100000000000000", hexnat% "1000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c55cf810c9c80000000000", 6245226045767680, hexnat% "1e800000000000000", hexnat% "1001000200000000000000", hexnat% "60000000420000000000000", hexnat% "60100000000000000", hexnat% "22000000000000000000", hexnat% "2a80000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27e823603a7600000000000", hexnat% "40040010440000000000000", 6922525208477696, hexnat% "1c80000000000000000", hexnat% "24001800000000000000", hexnat% "18100000000000000000000", hexnat% "18000000000000000000", 16140901064495857664]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "660fd591c68480000000000", hexnat% "18100000000800000000000", 6526701022478336, hexnat% "60380000000000000", hexnat% "1c00000000000000000000", 16140901064495857664, hexnat% "2a00000000000000000", hexnat% "200000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5ef9c5000c9c80000000000", 6245226045767680, hexnat% "1001000200000000000000", hexnat% "40010420000000000000", 16717361816799281152, hexnat% "20020081000000000000000", hexnat% "60100000000000000", hexnat% "2a00000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46367f907e5200000000000", hexnat% "60002400000000000", 6922525208477696, hexnat% "18000000000000000000", hexnat% "1c80000000000000000000", hexnat% "20000001800000000000000", hexnat% "18000000000000000000000", 16140901064495857664]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ffe6191c60780000000000", hexnat% "10010004008800000000000", 6473924464345088, hexnat% "1c00000000000000000", hexnat% "60380000000000000", hexnat% "8200000000000000000", 11529215046068469760]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "66be7fbfd63f80000000000", 7881299347898368, hexnat% "40280000000000000", hexnat% "18000000000000000000", hexnat% "1400000000000000000000", hexnat% "18000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46987fbf97ff80000000000", hexnat% "60000400000000000000", hexnat% "40280000000000000", hexnat% "18000000000000000000", hexnat% "20200000000000000000000", hexnat% "1400000000000000000000", hexnat% "18000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8693f97ff80000000000", hexnat% "40280000000000000", hexnat% "18000000000000000000000", hexnat% "60000000400000000000000", hexnat% "1480000000000000000", hexnat% "18000000000000000000", hexnat% "60200000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ef9ffbf8efe80000000000", hexnat% "10000000000000000000000", 4521191813414912, hexnat% "40300000000000000", hexnat% "60000400000000000000", hexnat% "1000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f97dffbe7c80000000000", hexnat% "1000000000100000000000", hexnat% "18000000008000000000000", 4538783999459328, hexnat% "8200000000000000000", hexnat% "40040000400000000000000", hexnat% "20020000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fe6fbfce7e80000000000", 6772991627100160, hexnat% "40300000000000000", hexnat% "1000000000000000000", hexnat% "18000000000000000000", hexnat% "8000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37d86d7fbe7c80000000000", hexnat% "18000008000000000000", 4556376185503744, hexnat% "1080000000000000000", hexnat% "8200000000000000000000", hexnat% "40040000400000000000000", hexnat% "20200000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16d96d3f869c80000000000", hexnat% "8008000000000000000000", hexnat% "40040000400000000000000", hexnat% "40386000000000000", hexnat% "1001000000100000000000", 4538783999459328, hexnat% "20020080000000000000000", hexnat% "200200000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c21 c12
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ff97f882e7780000000000", 6896136929411072, hexnat% "8002000000000000000", hexnat% "60000400000000000000", hexnat% "10000004000000000000000", hexnat% "60100000000000000", hexnat% "11800000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f97d880c6580000000000", hexnat% "18000000008800000000000", 4820258976169984, hexnat% "40040010420000000000000", hexnat% "60300000000000000", hexnat% "8200000000000000000", hexnat% "20020001800000000000000", 6917529027641081856]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "663eef88465200000000000", hexnat% "1001000202500000000000", hexnat% "10010004008880000000000", hexnat% "8000002000000000000000", 4503599627370496, hexnat% "c00000000000000000000", hexnat% "11800000000000000", hexnat% "60180000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1619670c008880000000000", hexnat% "40040010460000000000000", hexnat% "1880000100000000000", hexnat% "8008002001400000000000", hexnat% "1c00000002000000000000", 5664683906301952, hexnat% "20020001800000000000000", hexnat% "200000000000000000000", hexnat% "60380000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c31 c8
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c6
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c34 c5
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c35 c4
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c37 c0
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00032.record013
