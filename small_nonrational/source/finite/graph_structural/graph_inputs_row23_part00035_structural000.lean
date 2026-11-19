module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00035Data
public import GraphInputsRow23Part00035Frames
public import GraphInputsRow23Part00035Leaves
public import GraphInputsRow23Part00035Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002
def vertexColumn : Fields := ⟨10, hexnat% "f2c68d6c3a2e4b8ae1ba1e478f1c64d5c362d4b4ad1b61d47713a4d9394d532cc73c2e2b4acab1ac9b16c3bc1e8761e4751e2749e1745c9715c8f13c1f390e234a1a468c6298668390e0b8e134619464c5294658350d0b4c328c6384d1324c5382d0b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4010003010000000000000", hexnat% "3e00000000000000000", hexnat% "f80000000000000000000", hexnat% "10641800001e4000000000", hexnat% "2008040808000000000000", 2218264709038080, 540431955284459520, hexnat% "3c060000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022
def vertexColumn : Fields := ⟨10, hexnat% "9723c5693a358b68b92e2b86e8791e2783eca719965598e539a9695954d58d4b59352d2b46d4749d0f5a364d5334d332cd4b8acab1ae1b26c3b31e2749c6785d170de0f43c8f8b21c1712a4685a298961584e0b81e8a529865191662529615254558344d0b41d48ca344c9314d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "312383ec0e5de0000000000", hexnat% "1c0010018000000000000", hexnat% "cc00000000010000000000", hexnat% "7c00000200000000000", hexnat% "c02000000000000000000000", hexnat% "300000000100000000000000", 4467570830351532032, hexnat% "c0000000002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28a08fdc0edcd0000000000", hexnat% "7020000300000000000", hexnat% "15400000000020000000000", hexnat% "1f0000010000000000000", hexnat% "c02000000000000000000000", hexnat% "c0000000002000000000000", 4467570830351532032, hexnat% "300000000100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "322381cc1f5ee0000000000", hexnat% "1c0030008000000000000", hexnat% "cc00000000010000000000", 4467588422537576448, hexnat% "301000000000000000000000", hexnat% "c00000200000000000000000", hexnat% "7c00000000000000000", hexnat% "c0000000002000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18a00197ffdfb0000000000", hexnat% "8048000000000000000", hexnat% "26400000000040000000000", hexnat% "1f0020000000000000000", hexnat% "301000000000000000000000", hexnat% "c0000000002000000000000", hexnat% "7c00000000000000000", hexnat% "c00000200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "df743fff8fffff0000000000", hexnat% "300000000000000000000", 6917529027641081856, hexnat% "c0000000000000000000", hexnat% "8800000000000000000000", hexnat% "200000001000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777f3fffffeff0000000000", hexnat% "c000000000000000000", hexnat% "80800000000000000000000", hexnat% "200000000000000000000000", hexnat% "8000000001000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777f3ffa7fedf0000000000", 4611967493404098560, hexnat% "c000000000000000000", hexnat% "8800000000000000000000", hexnat% "200000001000000000000000", hexnat% "80000000800200000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777b1fefffeff0000000000", hexnat% "80800000000000000000000", hexnat% "8000001000000000000", hexnat% "6010000000000000000", hexnat% "200040000000000000000000", hexnat% "8000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d774b1fee7ffdf0000000000", hexnat% "300000000000000000000", hexnat% "c000000000000000000", hexnat% "80000000800200000000000", hexnat% "2010000000000000000", hexnat% "8800000000000000000000", hexnat% "200040001000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d7b638fec6e7df0000000000", hexnat% "4800000000000000000000", hexnat% "7010000200000000000", hexnat% "80000000800000000000000", hexnat% "200040001118000000000000", 2305843009213693952, hexnat% "180000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d76638fcc7fdcf0000000000", hexnat% "8800010000000000000000", 4035278042682097664, hexnat% "1c0020000000000000000", hexnat% "201000000000000000000000", hexnat% "80001000002000000000000", hexnat% "6000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffff0fb86fcbf0000000000", 1224979098644774912, hexnat% "7000000000000000000", 6917529027641081856, hexnat% "8040001400000000000", 577023702256844800]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefd3dfdfeffff0000000000", hexnat% "200000000000000000000", hexnat% "40000100000000000000", hexnat% "10000020000000000000000", hexnat% "82000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefd79f9bffebf0000000000", hexnat% "200040000000000000000", hexnat% "10000020000000000000000", 4612037862148276224, hexnat% "6000000000000000000", hexnat% "80000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefffeff8efdff0000000000", hexnat% "10000000000000000000000", hexnat% "1000002000000000000", 1224979098644774912, 6917529027641081856]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffdfafb8efcbf0000000000", 1224979098644774912, hexnat% "5000000000000000000", hexnat% "200040000000000000000", 6917529027641081856, 914793674309632]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "feffb0fd8eecbf0000000000", hexnat% "10000020000000000000000", hexnat% "1000002000000000000", hexnat% "40001110000000000000", 6917529027641081856, hexnat% "6000000000000000000", hexnat% "8000001400000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffe38ff86fddf0000000000", 6917529027641081856, hexnat% "40001100000000000000", hexnat% "180000000000000000000", hexnat% "1000802200000000000", hexnat% "6000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff7f30fe86fc9e0000000000", hexnat% "40001100000000000000", 6917529027641081856, hexnat% "c000000000000000000", hexnat% "82010000000000000000", hexnat% "8000000001410000000000", hexnat% "1000802200000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d63f30f886e48e0000000000", 6917529027641081856, hexnat% "c000000000000000000", hexnat% "1c000000000000000000000", hexnat% "80001000802300000000000", hexnat% "200040001118000000000000", hexnat% "82030000000000000000", hexnat% "40001410000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42a00fdfc0d3fd0000000000", hexnat% "200000024000000000000", hexnat% "15400000000020000000000", 4469822630165217280, hexnat% "800080200000000000000000", hexnat% "c0800000000000000000000", hexnat% "170000000000000000000", hexnat% "300000000100000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f77df2ffffff7f0000000000", hexnat% "200000000000000000000", hexnat% "8000000000800000000000", hexnat% "80001000000000000000000", hexnat% "c000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f77730ffffff7f0000000000", hexnat% "8000000800000000000", hexnat% "c0000000000000000000", hexnat% "8800000000000000000000", hexnat% "80001000000000000000000", hexnat% "6000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "777430ffe7f7ef0000000000", hexnat% "300000000000000000000", hexnat% "c000000000000000000", hexnat% "8800000008000000000000", hexnat% "800082000000000000000000", hexnat% "40001000000000000000", hexnat% "80001000800100000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "775638ffc7e5cf0000000000", hexnat% "8800000008000000000000", hexnat% "7000000300000000000", hexnat% "1c0000010000000000000", hexnat% "802000000000000000000000", hexnat% "80000000802000000000000", 3458764513820540928]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffff0df87dd3f0000000000", hexnat% "2200000000000000000", 4035225266123964416, 4620904323914661888, hexnat% "c000000000000000000", hexnat% "1000002000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfd3fdfefefff0000000000", hexnat% "200000000000000000000", hexnat% "80200000000000000000", hexnat% "20000000010000000000000", hexnat% "40001000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfdb7ffcfcf3f0000000000", hexnat% "200000020000000000000", hexnat% "20000000010000000000000", 3458764513820540928, hexnat% "8000000c00000000000", hexnat% "40000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfff1dff7fdff0000000000", hexnat% "20000000000000000000000", 577023702256844800, hexnat% "2200000000000000000", hexnat% "c000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffdf1dfd7dd3f0000000000", 2882303761517117440, hexnat% "2200000000000000000", hexnat% "200000020000000000000", hexnat% "c000000000000000000", 774056185954304]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c47 c46
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdff71dd87ed3f0000000000", hexnat% "20000000010000000000000", 577023702256844800, 3458764513820540928, hexnat% "82220000000000000000", hexnat% "c000000000000000000", 4611897124659920896]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c50 c45
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c51 c42
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffe30dfc7fdef0000000000", hexnat% "c000000000000000000", hexnat% "82200000000000000000", hexnat% "140000000000000000000", hexnat% "1000802100000000000", 3458764513820540928]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff7f30df87f52e0000000000", 6917529027641081856, hexnat% "82200000000000000000", hexnat% "c000000000000000000", hexnat% "40001008000000000000", hexnat% "8000000000c10000000000", hexnat% "1000802100000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "753f30dc87c50e0000000000", hexnat% "c000000000000000000", 6917529027641081856, hexnat% "2c000000000000000000000", hexnat% "80001000802300000000000", hexnat% "800082230000000000000000", hexnat% "40001018000000000000", 9219404998901760]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c57 c52
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c58 c41
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c59 c40
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5190081a7efffb0000000000", hexnat% "200048000000000000000", hexnat% "26400000000040000000000", hexnat% "200040000100000000000000", hexnat% "7c10000000000000000", hexnat% "c0800000000000000000000", hexnat% "800080200000000000000000", hexnat% "130000000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefe38ffe6f7ef0000000000", hexnat% "10000000000100000000000", hexnat% "40001108000000000000", hexnat% "7000000000000000000", hexnat% "180000000000000000000", 576460752303423488]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefc37dffedfbd0000000000", hexnat% "8000000400000000000", hexnat% "300000000000000000000", hexnat% "10000000020020000000000", hexnat% "40000100000000000000", hexnat% "80200000000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefc30dfe6f7ed0000000000", hexnat% "c000000000000000000", hexnat% "300000000000000000000", hexnat% "82200000000000000000", hexnat% "10000000000120000000000", hexnat% "1000800000000000000", hexnat% "40001108000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c65 c62
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfe3cdec7ffdf0000000000", hexnat% "20000000000200000000000", 4035225266123964416, hexnat% "82210000000000000000", hexnat% "140000000000000000000", hexnat% "1000000000000000000"]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfc3fdbbeffbb0000000000", 4611756387171565568, hexnat% "300000000000000000000", hexnat% "20000040000040000000000", hexnat% "40000100000000000000", hexnat% "80200000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfc34dae6ff9b0000000000", hexnat% "8040000400000000000", hexnat% "300000000000000000000", hexnat% "40001100000000000000", hexnat% "20000000000240000000000", hexnat% "1000800000000000000", hexnat% "82210000000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c69 c68
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c70 c67
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5cbc30d8e6c7890000000000", hexnat% "c000000000000000000", hexnat% "300000000000000000000", hexnat% "200040001118000000000000", hexnat% "800082230000000000000000", hexnat% "34000000000000000000000", hexnat% "1000800300000000000", hexnat% "40020460000000000"]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c72 c71
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c73 c66
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5400001866c5880000000000", hexnat% "cc08000000000000000", hexnat% "330000000000000000000", hexnat% "3c400000000000000000000", hexnat% "80001000802300000000000", hexnat% "200040001118000000000000", hexnat% "800082230000000000000000", hexnat% "40020470000000000", hexnat% "3800000000000000000000"]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c76 c61
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c77 c60
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c78 c35
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c79 c34
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c80 c3
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c81 c2
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c82 c1
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c83 c0
  c84
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024
def vertexColumn : Fields := ⟨10, hexnat% "c9aa669b16959568d93633a2e4b86e8791e2783ec96a569715955558d5353362d4b46d8751d2743dc8ea368f1394d538cd3332e2b4ac6b86d1b26c3bc1e8761e4751cc719c970de0f43cac170aa16a26498a6859161588e1382e078a916625494a5855151548d1342d0762348ca384d1314c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020002001180000000000", hexnat% "703c0000000000000", hexnat% "381c00800000000000", hexnat% "703c00000000000000000", hexnat% "381c000000000000000000", hexnat% "703c000000000000000000000", hexnat% "381c0000000000000000000000", 17557001672327168, hexnat% "c000c000c000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024
