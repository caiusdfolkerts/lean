module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00033Data
public import GraphInputsRow29Part00033Frames
public import GraphInputsRow29Part00033Leaves
public import GraphInputsRow29Part00033Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001
def vertexColumn : Fields := ⟨10, hexnat% "da2b89e3a4ad32cab16ca723c2f07ce8b62d4b4acaaaa9a96aa6a5ae1b26a99a659b16a5956c3a8e53a2e4b8ae1ba1e2785ee86b13c729aa569a66392e47969565554b51d54d4b4ad1b49d1743de0f23a8da358ce3c4e9354cd3c2e8b52e2b4acab1ae1b26d8751d2729c6745c5743c8f13c2fa4a1a16896079611a459494a52542d0754324c5312c1b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6d26db6d36db6da49b6da6da49a6d24926db4da49b4db492493492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "411c3b0888884c00000", 1152921509455462400, hexnat% "300018000000000600000000", 1241513984, hexnat% "2000000000140000000000", 18014398509481984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020080000c01c03efc00000", hexnat% "100000808800000000", hexnat% "100014000000000400000000", 10596969923202777088, hexnat% "10020000000000000", 4611686018427387904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20201c0040e01c878f800000", hexnat% "100000000000000000000000", hexnat% "110000000800000000", 140739103162368, 10596969923202777088]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20040140b01c8f8fc00000", hexnat% "100000800000000000", hexnat% "300018000000000000000000", 9439544820579172352, 1170935903116328960]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000800d3d00003efc00000", hexnat% "2000000000140000000000", hexnat% "100014000000000400000000", hexnat% "10020000800000000", 150083337191424, hexnat% "100000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000800d3d00003efc00000", hexnat% "2000000000140000000000", hexnat% "100014000000000400000000", 150117696929792, hexnat% "10020000000000000", hexnat% "100000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10d3900081efc00000", hexnat% "10020000800000000", 149533581377536, hexnat% "200008000040000200000000", hexnat% "2000000000140000000000", hexnat% "100014000000000400000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1103a08889efc00000", 13835058055282163712, hexnat% "2000000000140200000000", 1175439502743699456, hexnat% "30001c000000000400000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40143f00c8e8dc00000", 10376293546293460992, hexnat% "100000000002000000", hexnat% "300018000000000000000000", hexnat% "2000000000100000000000", 140738562097152]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1043a08889efc00000", hexnat% "11010000000000000", 9223372036854775808, hexnat% "2000000000140200000000", hexnat% "200008000040000000000000", hexnat% "100014000000000400000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1113b08089efc00000", 13202729467904, 13835058055282163712, hexnat% "200008000040000000000000", hexnat% "2000000000100000000000", hexnat% "100014000000000400000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1103a080880f800000", 8798240505856, 22517998141046784, 13835058056355905536, 1152921509438685184, hexnat% "2000000000140200000000", hexnat% "30001c000000000400000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009
def vertexColumn : Fields := ⟨10, hexnat% "ae178ad1742f07ce8b52cc972aa96a56a3a4e87aa996655a364d8763386e1783ee8751cc6b1aa699566394e4b9a9695556354d4b5334ad2743de0f43c8ea368f1394d538cd33a2d4b32e2b4acab86d1b16c3ba1d4731e2749ca785d1715c370bc1fcc0ac1703cc8aa22a8a62384e0bb11544591548d1341dc0e8350c8b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4934d36db4db6d249a4db4db6d36d249249a69b49369b4d24da6d3489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aa082c8003ed4a4a92c000000", hexnat% "4000100000000000000000000", 72128031501582336, hexnat% "10820000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8002d8823fd4c4912c000000", hexnat% "4000100000000000000000000", hexnat% "208000000000000000000000", 35356170780672]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8002c8003fd484a12c000000", hexnat% "4000100000000000000000000", hexnat% "208000000000000000000000", hexnat% "10820000000000000000", 105656195481600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003c8003cc004010c000000", hexnat% "2208000000000000000000000", 144256063003164672, hexnat% "10000114000000000000", 105656195481600, hexnat% "820000008020000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000d88237d4e4b92c000000", hexnat% "300000000000000000000", hexnat% "2008000000000000000000000", hexnat% "c000000000800000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003d8823cd4e4912c000000", 171798691840, 216172782113783808, hexnat% "2208000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8001d88237d4e4912c000000", hexnat% "200000000000800000000", hexnat% "c000000000800000000000000", hexnat% "2208000000000000000000000", 137438953472]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000d8823114609024000000", hexnat% "c000000000c00000000000000", hexnat% "300000000000008000000", 140913582014464, hexnat% "20000000002c0000000000000", hexnat% "208000000000040000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ca083d8003fd4a4a12c000000", hexnat% "2000000000000000000000000", 70471823392768, hexnat% "820000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082d8001fd4a4a12c000000", 2305843043573432320, hexnat% "820000000000000000", hexnat% "c000100000000000000000000", 70437463654400]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082c88017d4e4b92c000000", 2882303761517117440, hexnat% "10020000000000000000", hexnat% "c000100000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ea083c8003cd4e4a12c000000", 103079215104, 216172782113783808, hexnat% "10820000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082c8001fd4e4a12c000000", 2305843043573432320, hexnat% "10820000000000000000", hexnat% "c000100000000000000000000", 68719476736]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082088017d4e4b928000000", hexnat% "10020000000000000000", 2882303761584226304, hexnat% "c000140000000000000000000", hexnat% "80000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ca083c8003cd4e4a12c000000", hexnat% "2000000000200000000000000", 103079215104, hexnat% "10820000000000000000", 72057594037927936]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082c8003ed0e4a92c000000", hexnat% "c000100000000000000000000", 73183562664247296, hexnat% "10820000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082480036d0e4a108000000", 103616086016, hexnat% "c000000000800000000000000", hexnat% "10000104000000000000", hexnat% "820000000000000000", hexnat% "180000000000004000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c29 c16
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a082c88234d4e4b92c000000", hexnat% "10000100000000000000", hexnat% "2000000000200000000000000", hexnat% "c000000000800000000000000", hexnat% "100000000000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e8003c8823fd444992c000000", hexnat% "10000000000000000000", 176059299397632, hexnat% "208000000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28001d88237d444992c000000", hexnat% "200000000200000000000", hexnat% "c000000000800000000000000", hexnat% "208000000000000000000000", 140874927308800]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28000d88233d4c4b924000000", hexnat% "208000000000000000000000", hexnat% "200000000200008000000", hexnat% "c000000000c00000000000000", hexnat% "100000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003d082339444992c000000", 864691128455135232, 176059299397632, hexnat% "8000040000000000000", hexnat% "2208000000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8001d0823394449924000000", hexnat% "200000000200008000000", hexnat% "2208000000040000000000000", hexnat% "c000000000c00000000000000", 140874927308800, hexnat% "8000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c39 c34
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ca083d8003fd484a92c000000", hexnat% "2000000000000000000000000", 105621835743232, hexnat% "820000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082d8001fd484a92c000000", 2305878193585782784, hexnat% "820000000000000000", hexnat% "c000100000000000000000000", 70437463654400]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ea083c8003cd4c4a92c000000", 35253091565568, 216172782113783808, hexnat% "10820000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082c8001fd4c4a92c000000", 2305878193585782784, hexnat% "10820000000000000000", hexnat% "c000100000000000000000000", 68719476736]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c47 c17
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a082080016d084a928000000", 2305878193652891648, hexnat% "c000000000800000000000000", hexnat% "10820004000000000000", 72128031501582336, hexnat% "1c0000000000000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c50 c44
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000200003c00e4b92c000000", hexnat% "10820004000000000000", hexnat% "2208000000040000000000000", hexnat% "1c0000000000000000000", 256705178760118272, hexnat% "800008000000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003d0003f9464912c000000", hexnat% "820000000000000000", hexnat% "8000040000000000000", 140909287047168, hexnat% "2208000000000000000000000"]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003c0003d1424812c000000", 70471823392768, hexnat% "10820000000000000000", hexnat% "80000c0000000000000", hexnat% "2208000000000000000000000", 144256063003164672]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000280003c00e4b92c000000", hexnat% "10820004000000000000", hexnat% "140000000000000000000", hexnat% "2208000000040000000000000", 256705178760118272, hexnat% "800008000000000000000000"]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e8003c8003fd024892c000000", 140874927308800, hexnat% "208000000000000000000000", 1196337370497024, hexnat% "10820000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "68002880017d0a4a928000000", 2882303761584226304, hexnat% "208000000000000000000000", 1196337370497024, hexnat% "10820000000000000000", hexnat% "8000140000000000000000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c59 c57
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8003c0003c9424892c000000", hexnat% "18000000000000000000", 72128031501582336, hexnat% "820000000000000000", 162270461512646656, hexnat% "2208000000000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0003c8003cc024892c000000", 144256063003164672, hexnat% "2208000000000000000000000", hexnat% "800000000014000000000000", 72128031501582336, hexnat% "10820000000000000000"]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0003c0003c8024892c000000", 73253931408424960, 162270461512646656, hexnat% "10820000000000000000", hexnat% "800008000010000000000000", hexnat% "2208000000000000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c000348024892c000000", hexnat% "c000000000800000000000000", 73253931408424960, 162270461512646656, hexnat% "10820000000000000000", hexnat% "2208000000000000000000000", hexnat% "800008000010000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c65 c62
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c66 c61
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c67 c60
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c68 c56
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c69 c55
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c70 c52
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c71 c51
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c72 c41
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c73 c30
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c74 c13
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c75 c6
  c76
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record009
