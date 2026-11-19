module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00081Data
public import GraphInputsRow24Part00081Frames
public import GraphInputsRow24Part00081Leaves
public import GraphInputsRow24Part00081Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007
def vertexColumn : Fields := ⟨10, hexnat% "1d4570dc74aca568da1e9c6a9996558d64d8b6a394e33a2e4789e1783e746b1b2699564d98e479716a565555355352d68d534cd8b51d2745db0dc3a8d9354cd34ccb31ce8b92d4b32c6b46c9b16c3ba1d8751cc789d2729d1725c570de0f43c8f13c1f0f22a0b9513462916439454950d42d0768350cc388e0b12c2b41c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6da6da4db4926d24936d24924d26da4926d24924924d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "103263c309347bf000000", hexnat% "1000000000008800000000", 180425528791007232, hexnat% "8c180000000000000000", 72163284593147904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002e1ab103dfbd000000", hexnat% "3002000100000000000", hexnat% "1000000000000000000000", hexnat% "100400002002000000", hexnat% "8c000000000000000000", 72303884642549760]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1033638301367ad000000", hexnat% "1000000000008810000000", hexnat% "8c080400000000000000", 180566197559885824, 72163215907225600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "103263830134fad000000", hexnat% "1000000000008010000000", 180566197559885824, hexnat% "8c180400000000000000", 72163353346179072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1180202330f3f1a3000000", hexnat% "3000400000000000000", 36310306623848448, 25971130368, hexnat% "1e1800000000000000", hexnat% "c000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30021001101a1000000", hexnat% "1100000000000000000000", hexnat% "3e1c00000000000000", 180566197559885824, 885233025024, hexnat% "8c000030020000000000", 105759308251136]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011
def vertexColumn : Fields := ⟨10, hexnat% "2b8ad2cc732aca70dc8f0bcb2a9a36a3ab1a9635a36c3a8e9394e33a2e4b86e8791e2785e0f9c9aa4d92e5c5a94d52d68d6354d3362d4b4ad1b51d2745d0f4d3a2ccb8ad2b1ad1b26c5ba1cc789d2719d1725c5783d0f23c4f0bc1f52a2a0e94689836524c926439514c52543550c3342c4b0ac1b41c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da6da6da69b6db49a49a4da4db6d34da49249a49249a692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000580021fc217000000", hexnat% "100000000000c00000000", 4719772478203756544, 576460759819616256, hexnat% "14080000800000000000", 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5518012d7c4000000", 9800536476616753152, hexnat% "104080000000802000000", hexnat% "10000000000c0000000000", 1099780063232, hexnat% "10000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11040800000e1fd7000000", 1729945206863691776, hexnat% "44180000000000000", 19516331393024, hexnat% "10000000800000000000", hexnat% "18000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "140dd982829497000000", hexnat% "1100000000000000000000", 48318382080, 23364622090240, 8796093022208]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11040880021fd517000000", 1729382260131495936, hexnat% "50080000000000000", 42949672960, hexnat% "10000100800000000000", 4611686018427387904]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "140dd18293d417000000", hexnat% "1100000000000000000000", 13194139533312, 576460759819616256, 42949672960]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000180821fd417000000", hexnat% "44100000000000000", hexnat% "14080000800000000000", hexnat% "100000000000a00000000", 576460759819616256, 1152921504606846976]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10040800820f1402000000", 5764607524107976704, hexnat% "1800000c000000000", hexnat% "40100100004000000", hexnat% "100000000000a00000000", 576460758762651648, hexnat% "10000000800010000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record011
