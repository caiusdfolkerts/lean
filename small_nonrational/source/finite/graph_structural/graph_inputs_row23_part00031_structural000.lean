module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00031Data
public import GraphInputsRow23Part00031Frames
public import GraphInputsRow23Part00031Leaves
public import GraphInputsRow23Part00031Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000
def vertexColumn : Fields := ⟨10, hexnat% "29635a364d8b61d98e9394e338ae1b89e1783ea54d58d5352d4756364d534cd2b46d2745d0f69334e334ccb31cd8b92d4b32cab1ac9b16c3bc1e8761d4731e2729c6745e0f07e544b2524aa4649a16258560d90e2384e0ba514a64549615254550d50d2344d0b64348e1324c530cd0b22c4b0ae0741c8711c2705c0f"⟩
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
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18005602416459776, 9115285645797883904, hexnat% "1f8040000000000000", hexnat% "3f400000000000000000", hexnat% "fc0200000000000000000", hexnat% "1fa000000000000000000000", hexnat% "7e01000000000000000000000", hexnat% "4000800100000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001
def vertexColumn : Fields := ⟨10, hexnat% "968da4e8ba1ea56359362d8769392e2785e0fa59365392e479954d54d4b51d64d4b49d1743d94cd34ccb31cf0ba2d8b52ccb8acab1ae1b46f07a1d8751cc789ca719e1745e0f43c8f13c2f07e4a4a89a1683a91926258560da494a4991643991525254550d64348c9314c3382d0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "31836306f846119a000000000", hexnat% "e100000000000000000", hexnat% "1c0000000000000000000", hexnat% "70800000000000000000000", hexnat% "e00000000000000000000000", 8697411853615104, 8899112863684100096, hexnat% "c001800000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e140000000000000000", hexnat% "2100420080040108000000000", hexnat% "3c0000020000000000000", hexnat% "f0800000000000000000000", hexnat% "1e00000000000000000000000", 8988919873929216, 9187343239835811840, hexnat% "f001e00000000000000000", hexnat% "38000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004
def vertexColumn : Fields := ⟨10, hexnat% "266c5a9665a568d9362d87663a4e538ce4b8ae4789e0fa65c5695656558d5352d4756364d534cd4b4ad4749d0f663c4e9364e538cd332cc7362e4b52ccb4acab46c9b0ef07a1d8751cc789d2729c5783c1f1b06a9186685916258364388e1382e1a64519615454950d50d2344d0b64318e1344c930cd0b22c4b0ae0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11940c65031940fff0000000000", hexnat% "e6030000000000000", hexnat% "3980c00000000000000000", hexnat% "e6030000000000000000000000", 846676729945653248, hexnat% "2f000000000000000000", hexnat% "bc0000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff8142e050bfff0000000000", 1098878309078401024, hexnat% "fa000000000000000", hexnat% "3d000000000000000000", hexnat% "3e80000000000000000000", hexnat% "4000100000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25ff897fe258afff0000000000", 522417556774977536, hexnat% "3680000000000000000000", hexnat% "108004000108000000000000000", hexnat% "d2000000000000000000000000", hexnat% "c2010000000000000", hexnat% "10000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50b8162ffffffff0000000000", hexnat% "1d000000000000000000", hexnat% "3e80000000000000000000", hexnat% "f40000000000000000000000", hexnat% "fa000000000000000000000000", hexnat% "100004000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50b8162a05fffff0000000000", hexnat% "fa000000000000000", hexnat% "1d000000000000000000", hexnat% "f40000000000000000000000", hexnat% "fa000000000000000000000000", hexnat% "3a80400000000000000000", hexnat% "100004000100000000000000000", hexnat% "400000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118fc463f118fc7ff0000000000", hexnat% "1000040001000000000000000", hexnat% "e6038000000000000", hexnat% "3980e00000000000000000", hexnat% "e6038000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff80c1e0307fff0000000000", 1116892707587883008, hexnat% "fc000000000000000", hexnat% "3e000000000000000000", hexnat% "3f00000000000000000000", hexnat% "4000100000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "23ff88ffe2385fff0000000000", 540431955284459520, hexnat% "3700000000000000000000", hexnat% "108004000108000000000000000", hexnat% "d4000000000000000000000000", hexnat% "c4020000000000000", hexnat% "10000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30780e1ffffffff0000000000", hexnat% "1e000000000000000000", hexnat% "3f00000000000000000000", hexnat% "f80000000000000000000000", hexnat% "fc000000000000000000000000", hexnat% "100004000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30780e1603fffff0000000000", hexnat% "fc000000000000000", hexnat% "1e000000000000000000", hexnat% "f80000000000000000000000", hexnat% "fc000000000000000000000000", hexnat% "3b00800000000000000000", hexnat% "100004000100000000000000000", hexnat% "400000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20830820c20ff7ff0000000000", hexnat% "1f000000000000000000", hexnat% "7c0000000000000000000000", hexnat% "df000000000000000", hexnat% "37c0000000000000000000", hexnat% "df000000000000000000000000", hexnat% "100004000100000000000000000", hexnat% "8000200008000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1135252352748486656, hexnat% "3f000000000000000000", hexnat% "fc0000000000000000000000", hexnat% "10000400010006040000000000", hexnat% "100004000100000c00000000000", hexnat% "ef008000000000000", hexnat% "3bc0200000000000000000", hexnat% "ef008000000000000000000000", hexnat% "30000c00030010000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005
def vertexColumn : Fields := ⟨10, hexnat% "9a87a659362d876c3a8e63a4e8b92e2b86e4789e0fa691e5954d4b51d70da358d9362d4b4ad1b51d2743d98d9394d5334d332cf0ba2d8b52ccb8ad2b2ad1b26c5b0ef07a1d8791e2749ca719e1715c4f07c729286a458960da0e4388e0b87192469454950d60d4348d0b64318d1324c530ce0b42c8b12c2b81d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20001000080384004000000000", hexnat% "7e000018000000000", hexnat% "7f800000000000000000", hexnat% "780100000000000000000", hexnat% "ff0000000000000000000000", hexnat% "f002000000000000000000000", 560888369119232, hexnat% "1000c80060001a000000000000", 2044634230826205184]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006
def vertexColumn : Fields := ⟨10, hexnat% "9a99a4e8ba1ea66659362d8769386e4789e0fa69665392e479995954d4b51d64d1b51d2743d98d934ccb31cf0ba2d8b52ccb8ad2b2ae1b16f07a1d8751cc789d2729e1715e0f43c8f13c2f07e4a1a91a2683a91866458960da491a5192643991465454950d64318d1324c3382d0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100420080200808000000000", hexnat% "1e100000000000000000", hexnat% "3c0000020000000000000", hexnat% "f0800000000000000000000", hexnat% "1e00000000000000000000000", 8865774571618304, 9061242450269437952, hexnat% "f001e00000000000000000", hexnat% "78000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00031.record006
