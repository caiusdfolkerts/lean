module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00098Data
public import GraphInputsRow24Part00098Frames
public import GraphInputsRow24Part00098Leaves
public import GraphInputsRow24Part00098Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002
def vertexColumn : Fields := ⟨10, hexnat% "ad0f43b13c1f2d2ccab2aa9aa5693aa9a9635a364d8b64b8ae4785e0fb31aa4e9565391e6a5396354d4753352d2b46d4745d0f6c3c8ea3c4e5354e334ce8b52ccb8ad2b2ad1b16c3ba1cc789d2729e1745c3743c8f0bc1f330ac328c61588e13a314c529154351342d84d1314d0b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6db6d36da69a6da6da49249a4db4924d269a4da6da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20410018ea591a400000", 180145084623224832, 648518346341351424, hexnat% "101000100004000000", hexnat% "20000000440000000000000", hexnat% "1000000000000800000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400000001100000000", hexnat% "20001000280000001000000", 3332928176128, hexnat% "10100004000000000", 272679353450496, hexnat% "101c08000000000000", 22517998149435392]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014
def vertexColumn : Fields := ⟨10, hexnat% "4f1b2b2aaa3aa9a3693a2e8e6558d64d8b68b92e1b91e0f9b1b26a93a699365392e4e5554d54d4b58b52d1b51d0f6c3c8ea368ce3a4d9354cd34ccb3a2e4b32e2b4acab1ae1b46c9b16c3b51cc789d2729c6745c9715c3783d0f13c2f07c5ca88d28a85a499161584e0b81ea84d18a459495151544d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "6da6d36d24d249369b4db4934924da6db69b6da6db6d36da6d34db491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90002e904102128e00000", hexnat% "1000040000000000000000", hexnat% "120004800000000000000000", hexnat% "2a0000000000000000000", hexnat% "81000000000000000", hexnat% "2040000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a000a904102128e00000", hexnat% "800020000000000000000", hexnat% "1000040000000000000000", hexnat% "120004800000000000000000", hexnat% "140005000000000000000", hexnat% "2000080000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "39e00a5800000128a00000", 11529215046072664064, hexnat% "840004002000000000", hexnat% "100200000000100000000000", hexnat% "20004000000000000000000", 72057594037927936]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "29600e7800000128a00000", hexnat% "280000000000000400000", hexnat% "4008000100000000000", hexnat% "21000000004002000000000", hexnat% "100000800000000000000000", 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000f800000100c00000", hexnat% "820020000000000000000", hexnat% "1000040004002008000000", hexnat% "120004800000000000000000", hexnat% "380000000000000000000", hexnat% "2000080000000020200000", 72075186223972352]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030
def vertexColumn : Fields := ⟨10, hexnat% "2f0ae0f83713c1f2e2b4ab29c8f2aa8eaa68da8e8ba1e96635a361d8ce1b89e1783eb4671a64d98e5391e565356354d4753352d1b51d2745d0f6c3c8e6358e9394cd38cc73a2d8b32e2b4ac6b86c9b16c3b51cc789d2719e1725c570dc8f13c2f07c744b03c4a9261990e0ba91344991550d0768330d0b22d0711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6936db6db6da6d34da4d26db4da69a4926da69b4934da6d269369a491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200129100140060365e00000", 1450159629769113600, hexnat% "400000000000000000000000", 4864308160757760, hexnat% "a08080000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21b080914e1105a00000", hexnat% "100000000000260400000", 99079191802150912, hexnat% "600008000000000000000000", 1441152430514372608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600129b081e0021365e00000", 1441152430514372608, 4516793766903808, 351843720888320]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6001291000c0021364c00000", 369295169446477824, 4947819102208, 10376293541461622784, hexnat% "a00001400000000000", 4512395720392704]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6001290005e1401004e00000", 10200547328, 4947819102208, 10376293541461622784, hexnat% "b00000000000000000", 4514599038615552]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9b090d14a1105800000", hexnat% "200020000000000000000000", hexnat% "100000000000260400000", hexnat% "400000000520000000000000", 4947802324992, 2097152]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200129009460009264c00000", hexnat% "400000000100000000000000", 4398065385472, hexnat% "b00080000000000000", 4584967782793216, 281474976710656]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400109009520009260e00000", 4518992806936576, hexnat% "200000100040000000000000", hexnat% "20000001400004000000", hexnat% "a00080000000000000", 4294967296]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600009009420001000800000", hexnat% "100000000000260400000", 4947819102208, hexnat% "b00080000000000000", 90071992549507072, hexnat% "20000001400004000000", 4514599038615552]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record041
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041
def vertexColumn : Fields := ⟨10, hexnat% "2e83d23c4f2e2ac8f2b2aaa9a8eac6a3a398d68d8b61d94e8b86e8791e0fab13c6a93a6394e4e5355352d4755352d4743da8ce3a4d9334e332cc73a2d4b32e2b2ac6b86d1b0ed4731ca719c9715c370bc1fac06ca49164384e384b11a465454354344d0b4c344c9342c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db6db6db69a69a4d369a49249a4934da4da69a4d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffbe5fcf7fffff000000", hexnat% "10000800000000000", 13510798882111488, 11529215046068469760, hexnat% "400000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ffaafec337fbfd000000", 70385924046848, hexnat% "800010000880000000000", 79938893385826304, hexnat% "440000000000000000", hexnat% "100020000002000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffba5bff5e7bff000000", hexnat% "40000000400000000", hexnat% "10000800000000000", 11817445422220181504, 35734127902720, hexnat% "400000010000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffedbef7fffff000000", 4503599627370496, hexnat% "10000800000000000", 2594073385365405696]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffedb637fffff000000", hexnat% "10000800000000000", 2594073385365405696, 7881299347898368, 36028797018963968]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffbbdb42feebff000000", 16888498602639360, 2594354929061593088, hexnat% "400000010000000000", hexnat% "40000000400000000", 36028797018963968]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffbffe71efafe000000", 246290604621824, 6755399457832960, 1120986464256, hexnat% "40000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffb5aa39e7aee000000", 1653562408960, 11835459820729663488, 105553384701952, 79938893402603520, hexnat% "40000000400000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ffbafec736fafc000000", 78812993495760896, hexnat% "800010000880000000000", 70385924046848, hexnat% "440000000100000000", 9008298799923200]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ffbafe43fefafc000000", hexnat% "10080000000000000", hexnat% "800000000000002000000", 79938893402603520, hexnat% "40000000500000000", hexnat% "400020010000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7fffe5e3e377fef000000", 2306125033946218496, 126100789566373888, 219902593990656, hexnat% "800010000000000000000", 9223372036854775808]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffbbfff6be6aee000000", 282093452001280, hexnat% "40008000501000000", hexnat% "400000010000000000", 70369012613120]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7fffe5e6e776fdf000000", 76561193665298432, hexnat% "800010000880000000000", 2306125103202566144, 9259400833873739776]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ffba5e62fe6edc000000", 79938893402603520, 11529496521045180416, hexnat% "10080000000000000", hexnat% "440000000100000000", 1717986918400, hexnat% "800000000000022000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record041
