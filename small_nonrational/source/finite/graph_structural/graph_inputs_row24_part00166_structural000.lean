module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00166Data
public import GraphInputsRow24Part00166Frames
public import GraphInputsRow24Part00166Leaves
public import GraphInputsRow24Part00166Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010
def vertexColumn : Fields := ⟨10, hexnat% "338ad26c8f1b23c8da398b633a1e27b31ac5b13c7299a569c64d98e5391e6a5996958d4b5934cd8b52d1b61d2743d68d6338d9334d332cc7352ccb86c9b16d2729c6785c970de0f43c8f07ce4468c6138e18c5312c619464c5894a51960d134c344c9342c4b06c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d34da4936d349a4d249349b6d24934924d269a491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280000402edb4e000000", 47287796355825664, 4611703748052385792, hexnat% "28004000000000000", 1945555039024054272, hexnat% "1e00000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21e2db243e5b42000000", hexnat% "8000040000004000000", 38280597101084672, 687328985088]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c2db24046042000000", 56294995610566656, hexnat% "2000002a0200000000", hexnat% "28000000000100000000", 653036355584, 17592186044416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280002c02edb5e000000", 1740641255978696704, 4611703748052385792, hexnat% "28004000000000000", hexnat% "1e00100000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "29c24240365304000000", 8797166764032, 9224498074200571904, hexnat% "201100000000000000", 584551759872, 623748548390813696]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "29e0dbec06411e000000", 790273982464, hexnat% "20000000000000000", 43990128787456, 17592186044416]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28800aec04411e000000", 790273982464, hexnat% "201100000200000000", hexnat% "102c000000000000000", 46180562108416, hexnat% "400000100000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280002c0044104000000", 721990713344, 1740641255978696704, 28657095540736, hexnat% "28004000000000000", hexnat% "1c04000000000000000", hexnat% "200100200200000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018
def vertexColumn : Fields := ⟨10, hexnat% "2b29c8f26a96a3ab268d8b61d92e2b86e8791e2785eac6713c5a95a4e9c96352d4754b4ad1b61d4749d17723a8da398d6338e9394cd38ccb31cd8b52ccb4acab1ae1b46c9b16f0789d2729c6785d1725c570de0f43c8f13c2f07cd8388d23289a16a2649a164381e384d13249916625496154341d"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b49369b4926d36926d36924db6d369b6da6db69349b4db6d36d1249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨25, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000200000000c00000000", 8646911284553449472, hexnat% "8400420000000000000000", hexnat% "42002100000000000000000", hexnat% "f0000000000000000000", 10151105845526528]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020
def vertexColumn : Fields := ⟨10, hexnat% "2b83e1b43d0ecccab26caaaa6a5a36a3a2e9a665956359362da2e4b8aecc4f13a659366392e47939555355352d4753362d4b4ad1b723c4e5354cd38cd332ce4b32e2b4acab86c9b16c3b51cc789d2729d1725c570de0f43c8f0bccc2b0d2328c62384e8c5318a5251342d84d1314e0b12d0711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6db6d36db4db6936da6db69b4924d24926926d34d269a69a491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10208400090770b55e00000", 29273397577908224, hexnat% "200400000000000000", hexnat% "10000002000000000", 985162418487296]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10208400098460905400000", 9940500480, hexnat% "10040010000000000", hexnat% "200400100000000000", 1020484229529600, 9007199256838144]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208010403c62b15000000", hexnat% "200000300000000000", 18015498023206912, hexnat% "10000000098000000400000", 9007200336871424, hexnat% "400000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102084000bbc60b55e00000", hexnat% "10040010000000000", hexnat% "200400100000000000", 35321811042304]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208410068772b55e00000", 985162418487296, hexnat% "10000000090000000000000", hexnat% "200400000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [33855111216234496, hexnat% "8000400000000000000", hexnat% "10000400080000000000000", hexnat% "200010000002000000000", 1037938976620544, hexnat% "200000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10208600493f32b55e00000", 4398046511104, hexnat% "10040000000000000", 11258999068426240]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10008600093f72855e00000", 297237575406452736, 12884901888, hexnat% "200010000000000000000", 20266198323167232]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000400093f72a55e00000", hexnat% "200400000000000000", hexnat% "208000000000100000000", 29273397577908224, hexnat% "10000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000610093330840e00000", 4535502241792, 29273397577908224, 140746413834240, hexnat% "208000000400100000000", 288230376151711744]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61007bf72815e00000", 288230377225453568, hexnat% "208000000000100000000", hexnat% "10000000080000000000000", 8589934592]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2086100d3f32b14c00000", hexnat% "10000000008000000000000", 297237576480194560, 4398065385472]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200610043f22914800000", hexnat% "8000400000000000000", 9665773568, 5497574916096, hexnat% "10000000098000000400000", 9007199254740992]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61047bf62854a00000", 1099528404992, hexnat% "208000000000100000000", hexnat% "10000000080000000400000", 8589934592]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600423f62814800000", hexnat% "208000000000100000000", 9665773568, hexnat% "10040010000000000", hexnat% "10000000098000000400000", 16777216]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "610003220800800000", hexnat% "10000000098000000400000", hexnat% "208000000400100000000", 5635013869568, 27021597766320128, 140746413834240, 288247969411497984]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c25 c20
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022
def vertexColumn : Fields := ⟨10, hexnat% "f83d0ec370bc1f332aa8ea96a3a4e87a698e655a364d876338ae1b85e0fb31aa659366394e4b969555356354d4b5334ad2745d0f723a8da3c4e5354e334ce8b92e2b4acab86d1b16c3b61d4789d2729e1745c570dc8f13c2f07e384d0ca8a8aa31926298c98645931515154c382c8b12d0721c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d269b49b4d26db6926da4d34da6db6db6926934d269349a4d9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1729382261272346624, hexnat% "60000020800000000", hexnat% "c0000000000220000000", hexnat% "3000000000044000000000", hexnat% "10200010040000000", hexnat% "408000000002008000000", hexnat% "3000090000001800000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023
def vertexColumn : Fields := ⟨10, hexnat% "3323caaa3aa5a8e87a69956359362d92e2ba1e1783ecc4f1aa4e9966391e5a5554d54d4b54b4ad8745d0f723a8da338f1394d5334e334ccb31ce8b92ccb8ad2b2ac6b86c5b0ed8751cc749ca785d1725c570de0f43c8f13c2f07ccc8c93232a2a2a8c6458562384e8c531326292a4c5454552344d"⟩
def kindColumn : Fields := ⟨3, hexnat% "26934da49b4d34d269b49369a6db6db6936da4d36db69b69a6da4d9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600830040061a0451800000", hexnat% "8020000000000000000", hexnat% "800040000000000000000", hexnat% "100400000000000000000000", hexnat% "1000080000000000000000", hexnat% "8020401000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18200c10061a0451800000", hexnat% "8400000000000000000", hexnat% "20001000000000000000000", hexnat% "108000000000000000000000", hexnat% "40002000000000000000000", hexnat% "480024000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800040000100410800000", hexnat% "20001000000020001000000", hexnat% "100008000006000000000000", hexnat% "1000080000000040000000", hexnat% "40002000000080000000000", hexnat% "8020401000000000000000", hexnat% "480024000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record023
