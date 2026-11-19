module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00079Data
public import GraphInputsRow29Part00079Frames
public import GraphInputsRow29Part00079Leaves
public import GraphInputsRow29Part00079Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002
def vertexColumn : Fields := ⟨10, hexnat% "398e538cc729c6725c3723c2f07ce2a9a968da8e8ba1eb86a5a5635a362d876c3a8e63a4e538ce8b92e2b86e8789e1783ec6599364b9c5595354b5c358d534cd4b4ad1b61d4749d1743d34cb31cf0b52ccb4acab86c9b16c3bc1d4731d2729e1725c570de0f43c8f13c2f07c781d30a6286ac19861987162469264590e585194951543560c6342c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6da4db6d26db6934db6da6db69269269b6d36926d24926924924d24d2499249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000281077427202013c0000000", hexnat% "81000000000000000000000000", hexnat% "2040000000000502800000000", 4512395720392704, 8246337208320, 4222124650659840]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100028107742720100bc0000000", hexnat% "81000000000000000000000000", hexnat% "2040000000000603000000000", 4512395720392704, 8246337208320, 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10002810444271f4fa3c0000000", hexnat% "81000000000000000000000000", hexnat% "300000001800000000", hexnat% "3000000300000000000", hexnat% "2040000000020000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "730031f7283c0000000", hexnat% "81028000000000000000000000", hexnat% "440400002000000000", 14293651161088, hexnat% "102040100002020000000000000", 103079215104]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10002810004273f2f93c0000000", hexnat% "81000000000000000000000000", hexnat% "4400000000000000000", hexnat% "300000002800000000", hexnat% "3000000500000000000", hexnat% "2040000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10002810004273f1f8bc0000000", hexnat% "81000000000000000000000000", hexnat% "4400000000000000000", hexnat% "300000003000000000", hexnat% "3000000600000000000", hexnat% "2040000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1030681007427247fbbc0000000", hexnat% "7000000000000000000", hexnat% "8000000000001a000000000000", 281474976710656]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102068100742724303bc0000000", hexnat% "81000000000000000000000000", 4512395720392704, hexnat% "7000000400000000000", 8246337208320, 3096224743817216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204000774272477b9c0000000", hexnat% "100028100000000000200000000", hexnat% "1000000000000080000000000", 7599824371187712, hexnat% "80000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10102810474270c4fbbc0000000", hexnat% "80000000000012000000000000", hexnat% "2040000000020300000000000", hexnat% "3000000000000000000", 281474976710656]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010281047427064fbbc0000000", hexnat% "80000000000018000000000000", hexnat% "2040000000020300000000000", hexnat% "3000000000000000000", 281474976710656]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010281044427044d23c0000000", hexnat% "8000000000001a000000000000", hexnat% "2200000020000000000", hexnat% "2040000000020301800000000", hexnat% "1100001008000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "574271f70a3c0000000", hexnat% "2000000020000000000", hexnat% "81028000000000000000000000", 14293651161088, hexnat% "102040100000020000000000000", 103079215104]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37427050fbbc0000000", hexnat% "4000000400000000000", hexnat% "81028000000000000000000000", 7318349394477056, hexnat% "102040100000020000000000000", 52776558133248]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1810281044427150a23c0000000", 6150393167872, 2937895069417472, hexnat% "300000000000000000", hexnat% "3000000000000000000", hexnat% "2040000000020000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1020601022427257239c0000000", hexnat% "4400000000000000000", hexnat% "8000000000001a000200000000", hexnat% "1100000008000000000", hexnat% "10000000000000d0000000000", hexnat% "8000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20200037427050fbbc0000000", hexnat% "81008000000000000000000000", hexnat% "4000000400000000000", 7318349394477056, hexnat% "100040100000020000000000000", 52776558133248]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8302000004231f7fa3c0000000", hexnat% "4400400000000000000", hexnat% "3000000000000000000", hexnat% "100040100000020000000000000", hexnat% "8000000000000000000000", hexnat% "300000001800000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202000444270d02a1c0000000", hexnat% "80000000000012000200000000", hexnat% "10000000000000d0000000000", hexnat% "300000001800000000", hexnat% "100040100000020000000000000", hexnat% "3000000700000000000", hexnat% "8000000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c27 c14
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c31 c4
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003
def vertexColumn : Fields := ⟨10, hexnat% "dc2f07ce4b8aa6a5a36a3a2e87ac5996358b6c398e338ae8789e1783ee4789a6659366392e479c5595354b5c358d334ad8749d1743de0f13a4d9394cd38ccb3c2e8b62e4b32e2b2ae1b26c5b0ef0751cc749ca785d1783d0f07c741b0721a98619896158362384e0b8711a58519495154352344d0b70360c6384c9314c3382c8b12c2b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db6da6926926926db6da692692692492492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "66600666f4e9dff8000000000", hexnat% "1100011001020000000000000", hexnat% "1010010100100002000000000000", 90071992547409920, 11529215046068469760]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "66400000400000000000", hexnat% "6640000000000000000000000", hexnat% "80001a50000000000", hexnat% "101003010030001e008000000000", 1143916504375361536, hexnat% "7f000080000000000", hexnat% "1100011000000100000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005
def vertexColumn : Fields := ⟨10, hexnat% "394370bc1f392368ba1eb86c5a9665a5635a362d876c398e538ce4b8ae1b89e1783ee44d92e479e1715a5595954d58d4b5c354d3352d2b49d1743de0f13a4d9394cd38ccb3c2d4b32d2b2ac9b16c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07c746306c1c98a1a87162469c158519615254550d50d2344d0b70360c6384c9314c3342c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db4db6db69a6db4db6da4924924924924924924924924d36db693493492649249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨91, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000017f27ffffa02e400000000", hexnat% "80d000000000800000000", hexnat% "800000000300000000", hexnat% "5080000000000040000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000017f27ffff006e200000000", hexnat% "d800000000800000000", hexnat% "80000000a000000000000", hexnat% "5080000000000000500000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f277f26002e000000000", hexnat% "8800001000000010040000000000", hexnat% "80d000000000800000000", hexnat% "800080000700000000", hexnat% "508000000000a000000000000", hexnat% "80d00000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8800001ffff7f0fa02e400000000", hexnat% "80d00000800000000", 144115200960757760, hexnat% "5080000000000040000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f0c7f0f002e000000000", hexnat% "8800001000300000040000000000", 1080863944928657408, hexnat% "80008000a000000000000", hexnat% "5080000000000000700000000", hexnat% "f000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5080d4f8d1f8a06ef00000000", hexnat% "2e070000000000000", hexnat% "2b0700000000000000000", hexnat% "8800001000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffdf0108002e800000000", hexnat% "7e000000000000000", hexnat% "2000200000700000000", hexnat% "508000000000a040000000000", hexnat% "8800001000000070000000000000", hexnat% "80d00000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5207fff002e800000000", hexnat% "a00080000000000000000", hexnat% "5a0000000000000000000", hexnat% "508000000000a040700000000", hexnat% "8800001000700000000000000000", hexnat% "d800000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "508015fc15fca06ef00000000", hexnat% "a000a0000000000000000", hexnat% "4a000000000000000", hexnat% "4a0000000000000000000", hexnat% "8800001000300030000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff07ff00002ec00000000", hexnat% "f800000000000000000", hexnat% "508000000000a040300000000", hexnat% "8800001000000070000000000000", 1116892707587883008]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff00ff07002ec00000000", 1116892707587883008, hexnat% "508000000000a040300000000", hexnat% "8800001000700000000000000000", hexnat% "f800000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880508125072507a06ef00000000", 1116892707587883008, hexnat% "5a000000000000000", hexnat% "f800000000000000000", hexnat% "5a0000000000000000000", hexnat% "800080000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "508125fa25faa06ef00000000", hexnat% "800080000000000000000", hexnat% "8800000000500050000000000000", hexnat% "5a000000000000000", hexnat% "5a0000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f077f00002ee00000000", hexnat% "f800000000000000000", hexnat% "80008000a000000000000", hexnat% "5080000000000040100000000", hexnat% "8800000000000070000000000000", 1116892707587883008]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000012d07ffffa008e00000000", hexnat% "520000000000000000000", hexnat% "f800000000000000000", hexnat% "800000000000000000000", hexnat% "5080000000000066100000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50812d79f5fda06ef00000000", 11538222245323210752, hexnat% "d08000000000000000000", hexnat% "8800000000600000000000000000", hexnat% "20000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f077f04002ef00000000", hexnat% "f800000000000000000", hexnat% "508000000000a040000000000", hexnat% "800080000000000000000", hexnat% "8800000000000030000000000000", 1116892707587883008]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f0075040000f00000000", 1116892707587883008, hexnat% "80008000a000000000000", 11529218207164399616, hexnat% "f800000000000000000", hexnat% "5080000000000040000000000", hexnat% "8800000000700030000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c25 c14
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c26 c13
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c31 c8
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c33 c4
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "394e499a368ba1eb86c5a9665a5635a362d876c398e338aee4599564d94e4b91e785c569565655554d58d5352d475c354d3352d2b783c4e9364e5334e332cf0b62ccb2ad1b26c5b0ef07a1d8791cc789ca785d1725c570de0f43d8c1b0721a8662384e0bb116447162469c15851950d2344d0b46384c9314c3322c4b0ae0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4db6db69a4926db4934db6da4924d24924d24d24924924d2491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 79), (facetIndex 84), (facetIndex 99)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 77), (facetIndex 78), (facetIndex 85)]))
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 68), (facetIndex 90)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1036d000009040000424923ffffe2da001b6db6824848z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000" 23

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000" "{\"ridges\":[[78,772],[85,784]],\"owners\":[[78,772,[89,97],[19,46,67,77,98,104]],[85,784,[97],[24,61,77,103,104]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-1],[-6,-2],[-6,-3],[-6,-4],[-6,-5],[-7,-1],[-7,-2],[-7,-3],[-7,-4],[-7,-5],[-13,-10],[-13,-11],[-13,-12],[-14,-6],[-14,-7],[-15,-1],[-15,-2],[-15,-3],[-15,-4],[-15,-5],[-15,-14],[-8,13,15],[-9,15],[-16,6,7,8,9],[-17,10,11,12],[-18,1,2,3,4,5,14],[-19,16],[-19,17],[-20,19],[-21,18],[-22,21],[-23,20],[-23,22],[23]],\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":75,\"b\":35},{\"tag\":\"incompatible\",\"a\":75,\"b\":36},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":75,\"b\":39},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":77,\"b\":35},{\"tag\":\"incompatible\",\"a\":77,\"b\":36},{\"tag\":\"incompatible\",\"a\":77,\"b\":37},{\"tag\":\"incompatible\",\"a\":77,\"b\":39},{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":75},{\"tag\":\"incompatible\",\"a\":90,\"b\":77},{\"tag\":\"incompatible\",\"a\":97,\"b\":35},{\"tag\":\"incompatible\",\"a\":97,\"b\":36},{\"tag\":\"incompatible\",\"a\":97,\"b\":37},{\"tag\":\"incompatible\",\"a\":97,\"b\":39},{\"tag\":\"incompatible\",\"a\":97,\"b\":68},{\"tag\":\"incompatible\",\"a\":97,\"b\":90},{\"tag\":\"mate\",\"ridge\":772,\"a\":78,\"owners\":[89,97]},{\"tag\":\"mate\",\"ridge\":784,\"a\":85,\"owners\":[97]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[75,77,78,85],\"full_literals\":[-16,6,7,8,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[86,87,88],\"full_literals\":[-17,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,36,37,39,68,90],\"full_literals\":[-18,1,2,3,4,5,14]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,16,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-19,false,17],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,18,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-22,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-23,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-23,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 23 34\n-6 -1 0\n-6 -2 0\n-6 -3 0\n-6 -4 0\n-6 -5 0\n-7 -1 0\n-7 -2 0\n-7 -3 0\n-7 -4 0\n-7 -5 0\n-13 -10 0\n-13 -11 0\n-13 -12 0\n-14 -6 0\n-14 -7 0\n-15 -1 0\n-15 -2 0\n-15 -3 0\n-15 -4 0\n-15 -5 0\n-15 -14 0\n-8 13 15 0\n-9 15 0\n-16 6 7 8 9 0\n-17 10 11 12 0\n-18 1 2 3 4 5 14 0\n-19 16 0\n-19 17 0\n-20 19 0\n-21 18 0\n-22 21 0\n-23 20 0\n-23 22 0\n23 0\n"
  "35 20 0 34 32 0\n36 22 0 34 33 0\n37 19 0 35 29 0\n38 21 0 36 31 0\n39 16 0 37 27 0\n40 17 0 37 28 0\n41 18 0 38 30 0\n42 -6 0 41 1 2 3 4 5 14 26 0\n43 -7 0 41 6 7 8 9 10 15 26 0\n44 15 13 0 42 43 39 23 22 24 0\n45 -15 0 41 16 17 18 19 20 21 26 0\n46 13 0 45 44 0\n47 -10 0 46 11 0\n48 -11 0 46 12 0\n49 -12 0 46 13 0\n50 0 48 47 40 49 25 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record000
