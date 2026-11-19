module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00048Data
public import GraphInputsRow24Part00048Frames
public import GraphInputsRow24Part00048Leaves
public import GraphInputsRow24Part00048Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003
def vertexColumn : Fields := ⟨10, hexnat% "1acb8aaa6aa6a9693a1eac6698e665a8e63a4e4b8ae1b91e17ae15c789aa5a99a6594e479b15a5594e565555a358d9352d2b46d176c3a8da398ce364e534cc73a2d8b92e2b4acab1ae1b46c5b0ee8761e4731d2729c6745c9783d0f23c4f0bd1c1581e6852946585454554341da0e4328c6314e0b0ac1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6da4db69b4da6d269a6d249269a4d2492492493492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80034225337eff800000", 108227128545247232, hexnat% "100000040088000000000", 4507997673881600, hexnat% "4101000000000000000", hexnat% "800000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800003f5bf74c9800000", hexnat% "30000000030000000", hexnat% "100000000008804000000", hexnat% "4105000000000000000", hexnat% "800000000000000000", 8623489024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008352401baa3f800000", hexnat% "80000000204000000000", hexnat% "4100000000000000000", 36174003420790784, 86975786057203712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48050f19fb0cf800000", hexnat% "120000000800000000", 73183519714574336, hexnat% "10200000030000000", hexnat% "180000000000000000000", 35459249995776]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800003b5b776cd800000", hexnat% "30000000030000000", hexnat% "801000088000000000", hexnat% "100000040000800000000", hexnat% "4004000000002000000", hexnat% "100000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8003422537e47d800000", hexnat% "100000040080800000000", hexnat% "4801000000000000000", 112590070141157376, 140737521909760, hexnat% "100000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48041a5b7748f800000", hexnat% "30200000030000000", hexnat% "180000000000000000000", 4503609291046912, hexnat% "101000000000000000", 18023778718056448]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4034280b77eff800000", hexnat% "180000000000000000000", hexnat% "100040000000000000", 86975767803592704, hexnat% "801000088000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180801240bfe83f800000", hexnat% "4104000000000000000", hexnat% "30000000000000000", 112590070141157376, 10414592391905280]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180000200a6c027000000", hexnat% "34000000000000000", hexnat% "4801000080000000000", 18829279232000, 86975794647138304, hexnat% "100040000880000000", 36028866006876160]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014
def vertexColumn : Fields := ⟨10, hexnat% "29c9729a9693a699964d89e1783ee4669a66594e6c569695656554d68d9361d2745d0f6c368d63a4e534ce8b92d2b86d1b26c5b0ed8731d2729d1715c3723c6c6486a198961382e07a91646491a619194951342d0758348c6344c9312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a49249b6936d24934934d2492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c2 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fbeffffbdfa780000000", hexnat% "100000200000000000", 1126002986057728, hexnat% "4000000004000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1ffffffffffff80000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c6
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffffffd780000000", 171798691840]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c1 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffdfbdfff80000000", 144150372447944704, 1125899906842624]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c14 c10
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c1 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c16 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffefffffdfd780000000", 171798691840, hexnat% "100000200000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe7fd7bdfff80000000", 1125899906842624, hexnat% "80080000000000000", hexnat% "100200200000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c15
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffd7df5bff8780000000", 1126002986057728, 45035996273704960, 412316860416, hexnat% "282000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa839d1fdf9f00000000", hexnat% "400020000080000000", 412316860416, hexnat% "140240200000000000", hexnat% "286080000000000000", hexnat% "5000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa179e51650000000000", hexnat% "286082020000000000", 547608330240, 3536029394927616, hexnat% "1c00000000000000000", hexnat% "4000000000000000000", 81074139141505024]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c28 c27
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record014
