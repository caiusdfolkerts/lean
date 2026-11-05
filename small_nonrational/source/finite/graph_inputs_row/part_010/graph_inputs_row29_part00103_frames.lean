module
prelude
public import GraphInputsRow29Part00103Data
public import RawFrameSupport
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x648314d86ea2b4f7274930497d4b7a5852b494c49ea4c124491b486a4191d08e146d1a64cb263c2b91584a7a518282938497a49a23b919c8864321f78f7c79e3031790b3855229613909384562080fc07503861800b8058029e1480a084e826612c09284782140ef068826c12207803701a00be05e02e016c0b405802b81580aa04001b00c004e026012008c04402000f807803a01b009004401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x695b39198aa62513a82d288932486239d1a88ad443a1910848304069fecf6a7a53c994b89e64d72080ff87b03b31d00de46a63301870bf05b22c714089c44be20d10407e83d81e50eb87203761ad0d306603221730b605942b21520a5851027a13609784a02260f706a826c12207803701a00be05e02e016c0b405802b81580aa04001b00c004e026012008c04402000f807803a01b009004401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x6b4d199babd552a693ca784e49b134a634b895d28a4e4909151ba344626dcd19942e65c8b61662c6574ab151296520a113f2624b89590a21240c7e8fa1e83b4740e21be3646b0c818a308600bf17c2f45e0bb1742e45b0b215a25c468760d81982e85c0b41642c0560aa1502984006c0c01382604808c1102003e0780e81b0240440780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xc8d8f31a5a5b33646a0538a4d446824ed9a931e59ca5923206304598a4eddd5ba36a6d359f32a63cc317baec5b6b395e2b052aa4145a2f45086d039fd3d875ce59bc35e678ca1762de5a4ae15228e4f098925234430750c61362043d8690c41782a8540a41442804e09a1302583c0680c01382604808c1102003e0780e81b0240440780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x93121e3f424827029ed3d5794ef9dbba872ce35c137a6dad91a4344680b2d5e2b44f49d9362614ba9391da3144c871082073d278cee19f334640c017a2d655ca814627c4cc9591021440c7d0f51de3a4720de1ae344620ad1242003c86a0c817c2b0550a61482884f09c1342603c0680b8130250460881081f03c0740e01a0240440780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x8790b612bb5752e8db836d6c8d5da7b42664ca18e31560abf5722e05ba9b13025a44c8850b2093fe7c4f11db3a2724dd9b433665cca1612ba550a59452724bc9391d232434838f51e63c4750e41be36c6c0d21963105b0a61242003c8690c016c298520a013c2704c0961282483a0680bc1382604808c1102003e0780e81b0240440780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame006_links_0000 record000_frame006_links_0064)
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0643.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0643.count (({ width := 9, code := 0x89c3612fd7bbcdd6ea74399cae16e369b0d76a34994c9642f16cb2552a54ea55228136994ba59269144a210e7f3f1f0f4793a9c0dc6c359a0cc5e2e970b4592c15cac552a14ca24f269289043208f472381b0d46832188c05e2c1509844210f8783a1b0d0643016090441e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0643.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame007_links_0000 record000_frame007_links_0064)
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0643
    Papers.RationalityTen.SharedFrameCatalogue.group0643_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5c6ad6569a9f14e0a6cd25a918476231d16a89043a211904080f3f61f6cf2077d3b597bcb845b429c949ca044e726b92f0948481232115c87842f1fa8f9c7b634e19d0c545ee2e81650ac051426d130091c4741ff0f9079438c1b50d406703201850bc85b4288109064026c12207803701a00be05e02e016c0b405802b81580aa04001b00c004e026012008c04402000f807803a01b009004401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame008_links_0000 record000_frame008_links_0064)
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x69867e6765a858657b52a5205074f34e54cc4bb4aa49949247f47544f44643b36734a33f2ee2e42c92b02a429027f26e25924f2402392132071fe1bf1bb1ae19e19618617c17216515d14f14713312e12711e11a11410d1071000f90f30e60ce0b309908f07706d06705e05d05b05a05905705605505404003603002702602402302202001f01e01d01b01201100f00e00d00b00a009008006005004003002001000 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame009_links_0000 record000_frame009_links_0064)
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x7eaf9df037d6ded99a033b66ccb99431e62ac2d812fd5eabbd6e2d459c9ad2ea5445a8990f216420818fe9f53d879cf11dc394704de1863025e4b69672b6534a29382644ac9110b2063ec798ed1ce3886f0da1a833c608ab11c1fc3d8680c216c2a0530a21402784d09812c2503a0680b81382604808c1102003e0780e81b0240440780e01a02c050090100180280400600800800 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record000_frame010_links_0000 record000_frame010_links_0064)
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a14cf56752ac14f094448623b51d08e146d234d1988c545f22dd15c8a9451226512488b33918e4a3a4e426313049744b3256929893e498248922090647d23a91bc8d231916d0aa453228a13d09ac4b624c11e087441c1c60db069c32e1880bc05a42b213a09583dc1e00e9071036c1a80af04d81e00ee06e03581a80d206802f81700b605a02000fc06c03301900c4060027012008c04401b009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a62cea660a97d4488e7456a20d0f286742aa1150668224081ff8fc87dc3e59ec8f4479029593c07663791a78d146663211888bfc5dc2dc1650ac055029713f09b84b81ec0eb87083761b40d6869833e1980c8860c2f81590a9052c28813d09b04bc25011a08983d41dc0e707003641a60af04d81e00ee06e03581a80d206802f81700b605a02000fc06c03301900c4060027012008c04401b009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8238108056e46bc5e65b659658f58757f57756f56755f55654b54553d53352b5243ec3bc2f62ce2b32ac2a429c29428c28427c27326826225a2502482411d81c31b01a81a119919018818117916916213e13612f12711e11610f1070f70f00d40d00cc0c80c40c00a909b07807706e06b06a06906805f05c05b05a04003f03603303203103002702402302201b01200f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
def record001_frame004_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1722b5d5a5a7b937c8c744821c10c084941aa08d0248013f79f78fa27c33d71e34ef67692f616fc9ce4bc2501258908474233916889843f219109483840c1f90f947b22f71650a7451427813689804a424711d08904261c60da86a03381900c285e42da1570a2041c1f20e906f035018c0ab04d81e00ee06e03581a80d206802f81700b605a02000fc06c03301900c4060027012008c04401b009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record001_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 4) (record001.inverseMaps 4) record001_frame004_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record001) (record001.maps 4)
      (record001.inverseMaps 4) record001_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame004_links_0000 record001_frame004_links_0064)
theorem record001_frame004_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 4 :=
  of_group record001 4 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record001_frame004_indices record001_frame004_graph record001_frame004_links
def record001_frame005_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x66064a64157c55a4d74bb4ab4a74a149b49448d48748047947146f46845f45745136a34c2bc29c28c28828227b27526e26826225b25425124b24323b2351b619b18717c17617216e16816315d15414a12511a11210d1071020fe0fa0f20e80cc0c70c20be0bc0ba0a309707607506c06906806706605d05a05905803e03d03503203103002f02702402302201b01200f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record001_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 5) (record001.inverseMaps 5) record001_frame005_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record001) (record001.maps 5)
      (record001.inverseMaps 5) record001_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame005_links_0000 record001_frame005_links_0064)
theorem record001_frame005_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 5 :=
  of_group record001 5 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record001_frame005_indices record001_frame005_graph record001_frame005_links
def record001_frame006_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x69967f6745a55834f34cc4b94b64ac4a249b49448b48147746d46945e44d4444393643472b029027d27a27026525b25124924223b23122d2222112051fc19e18617917216b16515d15514f14713e13a11e11a11410d1071000f90f30eb0e60cc0c80c20bd0b70b10a609907707606d06a06906806705e05b05a05904003f03603303203103002702402302201b01200f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record001_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 6) (record001.inverseMaps 6) record001_frame006_indices (Fin.ofNat record001.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record001_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record001) (record001.maps 6)
      (record001.inverseMaps 6) record001_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record001_frame006_links_0000 record001_frame006_links_0064)
theorem record001_frame006_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 6 :=
  of_group record001 6 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record001_frame006_indices record001_frame006_graph record001_frame006_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (Fin.cases (record001_frame004_supported hcells) (Fin.cases (record001_frame005_supported hcells) (Fin.cases (record001_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xcee646b141878a8951427ad3ae9824bea5bd2c295a4a6251527a930491246d21a90647fa3dd1e26fb34b1958c825722b094f4a30505270934497a49a23b919c88643221190448043031790b38552296139098849c22b10407e03a81c30da068832614f0a40504274133096049423c11708503bc11c08d04601ac0d406903401780b805b02d01600ae05602a815006603201880c004c024011808804001f00f007403801b008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd9e6943385994ac752fa89142094449924311ce8d4456a26910e86442120c101a7fb3f49f60f9059329593c09b84101ff0f607663a01bc8d986a63301870bf05b22c715a8a9052820d10407e83d81e50eb87403901bb0d686983301910c506082f81590a9052c28813d09b04bc25012108983dc11c08d04601ac0d406903401780b805b02d01600ae05602a815006603201880c004c024011808804001f00f007403801b008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x34264ec51872b7538a2541a5d4b89592824d48e9112023b46a8c91622944c889101c3350654c79692d0588ae1592a6540a61472824f89c1352644b8961001fe3e4798f01d439c718de1b0354678cc192314618b616a2d0598b21622c0578ae1582a041081100194320630c41602b0550a81482885009e138198320620c0130240460881001f03c0740e01b02203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x3766aed0d9e2d9574a994fa794f09c9362694c69812e2574a2939242454848f91e1d3368680cc9732e45b0b31632ba568ab151296520a113f2784e09b10a21240c7e8fa1e83c4768e81c437c6c8d61a633c668c017e2f85e8bc1762e85c8b816c2c8450891101a4340670cc1702d0590b01582a8540a6148198320620c0130240460881001f03c0740e01b02203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x26f97a519322c86e0e825e6795df765d6741cd725c56fdbc6d9b36c1ac6a9845cd665853e4f5374c52e4a1254851d45d144390b42104408d9360d2330c930cc02f0b82c8af2a4a628c9f2749023c8e2348c22c8a22488218821b06b1a85a1645815c4d12c4a1244711845110430cc320c4300982408c220801f0781d0701b0440f0380d02c0a0240801c060140400c0200400 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc295f6aec5736a9a52fa88541c97a4b5a521258919475235118289e43da1c509283440fa020fe86a633018bcc3c5a42cb95ecaca55829b14a0a304f926d93489624a224a120c8e23ab1cd8dec6c43521948c5c60a2e31610ae052828113789684921ee0f007443861b90d5866030c1760a8844411c08d04601ac0d406903401780b805b02d01600ae05602a815006603201880c004c024011808804001f00f007403801b008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6a96806616525d15a858657a53b53752a51e51950a5014f94ec4df4da4ce4c64be4b64b04083dc3ba3ad35234b33832b32430e3042f82e92da2d42bf2b42aa29e29321420b1fc1ed1e61cf1c51ba1aa19d19618117416b16015512211b11510e1091040fd0f70f10e50cb08208108006906806706605c05a05905805605505405305203303203103002602402302202001f01e01d01c01b01100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame007_links_0000 record002_frame007_links_0064)
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6e96ce6a769b5f35cd5ac59f54b54553252551c5054f84ed4df4ce4c94b24a749a48e4853b939336f3653113092fa2eb2e22c82bf2b32a229428f27826a25f25424b1df1d91c81b91b61a81a019718817717016615f15714e14a12812211c11611010d1081010f90ee0d508a08908806906806706605c05a05905805605505405305203303203103002602402302202001f01e01d01c01b01100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame008_links_0000 record002_frame008_links_0064)
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1002.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1002.count (({ width := 8, code := 0xd4d0cbc9c7c3bebcbab9b7b5b4b0afadaba9a8a6a4a3a1a09995908e8c8b89878682817f7d7b7a78767573726b6a68666561605e5c5a5957555452514a4948474645444342403f3b3a3937363534312f2e2d2b2a292827252423221f1d1c1b191817161514110f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame009_links_0000 record002_frame009_links_0064)
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1002
    Papers.RationalityTen.SharedFrameCatalogue.group1002_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xbe75c5ad5d69ca4c4f726f936892d48c23b118e8b544822150e8846410203cfd87db3e91efcf566462f616fcb6a53929394089ce4d725e12c8948481232115c87842f213106081234e19d0c545ee2e81650afc56028a136898048e23a118888c4261c60da86a03381900c285e42da1640a2042411c08d04601ac0d406903401780b805b02d01600ae05602a815006603201880c004c024011808804001f00f007403801b008803c01c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame010_links_0000 record002_frame010_links_0064)
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x5af59357c5764fa4db4c74c148447f47046145844944243c43042241c40e4084023fc3f636c34933232c2e42d92c82bb2b029f29828f27e27126c25e25725224823f1df1d41c11b01a719a19318a17916816115615114d14313a1161101091040fe0f80f30ed0e80de0c808408308206806706606505b05905805705505405305205103303203103002602402302202001f01e01d01c01b01100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame011_links_0000 record002_frame011_links_0064)
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
def record002_frame012_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x6bc69667c6775d15a558357c52a5205074f34e54cc4c34bb4aa49949247f47546e46545b3953643473402ee2e42c92b02a429028727f26e25924f24023923222921f1bf1bb1ae19e19618617f17c17216515d14f14714013d13a11e11a11410d1071000f90f30ed0e60ce08c08b08a06a06906806705d05b05a05905705605505405303303203103002602402302202001f01e01d01c01b01100f00e00d00b00a009008007006005004003002001000 } : Fields).get c.val)
theorem record002_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 12)
      (record002.inverseMaps 12) record002_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame012_links_0000 record002_frame012_links_0064)
theorem record002_frame012_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 12 :=
  of_group record002 12 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record002_frame012_indices record002_frame012_graph record002_frame012_links
def record002_frame013_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1048.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1048.count (({ width := 9, code := 0x10c82c05fef9793b9d8e773389bede6db69b0d568b419acc65b2990bd5b2c960ab5529946a24fa7938994aa51229047a391882409f4f4793b1d4e670361acd06733194c65b2d164b0572b154a8532893c90472310882401f8e46e361a8cc6431180bc562a148a044200f878381b0d06430170883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1048.localPairCheck (smallEmbedding record002) (record002.maps 13)
      (record002.inverseMaps 13) record002_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame013_links_0000 record002_frame013_links_0064)
theorem record002_frame013_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 13 :=
  of_group record002 13 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1048
    Papers.RationalityTen.SharedFrameCatalogue.group1048_facts record002_frame013_indices record002_frame013_graph record002_frame013_links
def record002_frame014_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1049.count (({ width := 9, code := 0x187bc5cae163aa53a99409fce66b3397cb65727914823b1b8d4622d037a3b9d8e06fb65aad367b3596c7613017abb5d2e16ca451a75329749a451e8b43211027f3f1f0f471381bcdc6d361acd46933994b4592c144a04f271108441200f87a3c1d8e86632188c04c2411888401f0f074381b0883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1049.localPairCheck (smallEmbedding record002) (record002.maps 14)
      (record002.inverseMaps 14) record002_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame014_links_0000 record002_frame014_links_0064)
theorem record002_frame014_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 14 :=
  of_group record002 14 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1049
    Papers.RationalityTen.SharedFrameCatalogue.group1049_facts record002_frame014_indices record002_frame014_graph record002_frame014_links
def record002_frame015_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1047.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1047.count (({ width := 9, code := 0x13c9b4d26528914823d158a43a150982c1204fe7cbdde8f278bbddadd6bb55a6ca64b0d7ebe5d2e56eb3572b152a753291449349231108741a09007c3b9d4e470379b4d66230980be5e2e970b65a2c1589c4d261208e46228f4763a1c8dc6c351a0cc5e2e168b04822108803c1d0e06c34190883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1047.localPairCheck (smallEmbedding record002) (record002.maps 15)
      (record002.inverseMaps 15) record002_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame015_links_0000 record002_frame015_links_0064)
theorem record002_frame015_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 15 :=
  of_group record002 15 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1047
    Papers.RationalityTen.SharedFrameCatalogue.group1047_facts record002_frame015_indices record002_frame015_graph record002_frame015_links
def record002_frame016_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x43b84f06e0bbcf772eb1d4386700dc5b235e6a2d35a433c65ec9d8f316624c1d802994f89b1342484868d91522643485d09a063f47d0f59e53c4768e998e3105d8b296029e52ca493d2624a49091922a438850e71c23686a0cd1943105e8ba15824c318620c21482885009e120230450881082084007e0f81682c0560a81182104007c0e81c0360680c81802203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 16)
      (record002.inverseMaps 16) record002_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame016_links_0000 record002_frame016_links_0064)
theorem record002_frame016_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 16 :=
  of_group record002 16 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record002_frame016_indices record002_frame016_graph record002_frame016_links
def record002_frame017_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0936.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0936.count (({ width := 9, code := 0x11085c220cfb7bbd1e2eb7539dcae370b79b8da6bb59a6d267b3998bd5cad568ad562a94ea5512853c9c4d2612a93492411c8441a04fc7d3d1e0ea73389bcda6b3499cca5f2f170b6582b958a6512792c7c3d1e0dc6c351a0c8602f170b0562a148a04622108803c1c0d86830170b05428130883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record002) (record002.maps 17)
      (record002.inverseMaps 17) record002_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame017_links_0000 record002_frame017_links_0064)
theorem record002_frame017_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 17 :=
  of_group record002 17 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0936
    Papers.RationalityTen.SharedFrameCatalogue.group0936_facts record002_frame017_indices record002_frame017_graph record002_frame017_links
def record002_frame018_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x653c8b8ef1adb7b49662c9540a7149a88d049db37e6a4c796729648c818e71a632bc976cea9d235369acf99531e618c057baec5b6b395e2b054aa714ca2f45086d039fd3d877ceb9cb3786bccf19430e5fcbd95c2a451c9e13124a468860fd1d43183d0790f01843005f0bc150290510a01382684c096128198320620c0130240460881001f03c0740e01b02203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record002) (record002.maps 18)
      (record002.inverseMaps 18) record002_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame018_links_0000 record002_frame018_links_0064)
theorem record002_frame018_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 18 :=
  of_group record002 18 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record002_frame018_indices record002_frame018_graph record002_frame018_links
def record002_frame019_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x44f8770b2133c5768ea1d23706dad91abb4f684ce999328638c5582afd5eabb974a7c4d697d2da26442859049ff3e27a4f11db3a2724dd9b4358690d01612ba550a59452724d09792723a464869072043f47c0ea1c837c6d8d81a432c620bf16c2983b0750e81782e85c0b61482804f09c1302584a092120190310600bc130240460881001f03c0740e01b02203c0700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record002_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record002) (record002.maps 19)
      (record002.inverseMaps 19) record002_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame019_links_0000 record002_frame019_links_0064)
theorem record002_frame019_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 19 :=
  of_group record002 19 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record002_frame019_indices record002_frame019_graph record002_frame019_links
def record002_frame020_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0642.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0642.count (({ width := 9, code := 0xf4793b9d8e873389c0d96c359a6d267b3996c963b1584c1602f978b559abd5aa652a8d409f4e26d30964a2491e8e46a2d127f3f1f0f2783a9d0e26f369acd06733190c45c2d968b2582b958aa542994494492410c8441200e870371b0d06632188c0562a148a044200f878381b0d06430170883c1c0d058281208038180a04018080200 } : Fields).get c.val)
theorem record002_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record002_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0642.localPairCheck (smallEmbedding record002) (record002.maps 20)
      (record002.inverseMaps 20) record002_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record002_frame020_links_0000 record002_frame020_links_0064)
theorem record002_frame020_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 20 :=
  of_group record002 20 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0642
    Papers.RationalityTen.SharedFrameCatalogue.group0642_facts record002_frame020_indices record002_frame020_graph record002_frame020_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (Fin.cases (record002_frame012_supported hcells) (Fin.cases (record002_frame013_supported hcells) (Fin.cases (record002_frame014_supported hcells) (Fin.cases (record002_frame015_supported hcells) (Fin.cases (record002_frame016_supported hcells) (Fin.cases (record002_frame017_supported hcells) (Fin.cases (record002_frame018_supported hcells) (Fin.cases (record002_frame019_supported hcells) (Fin.cases (record002_frame020_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73172e72b71d7097066de6c26bf69e69468d68662b61e60c5de5ca5be5a159458957f53052851c4ff4d34c84be49c48e48847a47346c45e43341c4053d53ba3af39138037536d31730b3002e22b22a729f27c26f26925c25624e2421be1a317115714913a0fd0f50e70d20bf0bd0b40b30ae0aa0a209e09508c08a07f05204901c017014012010009007002001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x422e113083822c05601ef5b76d3b4dc96e0e6f937058cac2a5f4ad65618ae55522a394eca644cc26192c292546ca30d16485941c20910007eb3e99ec4e626f635a9894bb05b12b81568a84530232114885a3f11d28e3c6fc3251820bc05982b714f89f43e21dc0d606202f616e09704802240fe070836c19c0cd06002dc1520a304c824011c08302a012c03801700a00480200090038008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0xfddfb3f57e6fc1f6be47bef71eabd279ef29ceb9a728e05bb36e6c0d65a8b4d642c6d89b045d4b816dabd564ab55029a520a1538a6e4d0955252414648ad10a1c3da7a0f01d23726c4d699230a600ba96e2c8564969222143cc758e31762c45489b11e228428841041fc3e0790ea1b8360650860f80e0170280480800900e00800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0599.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0599.count (({ width := 11, code := 0x38870ee19c1b82702de9bcb786dada9afb5a6aecf99e33b658ca191b1d630c4d88af45ceb8d712cd590b015729a52aa19402784d896d2ca5848c9011ba3245688d102013f87d0f99ed3ba76ce29b436068cce98f312590b015429a520a212422c4147f0f11902f8590a612e2083e0760ea1cc3906f0dc198308590aa1001e82704a0700900900e00800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0599
    Papers.RationalityTen.SharedFrameCatalogue.group0599_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x38fe378ae2386e0f80dfb74d9f65d8353d1b3fca321c6f07c06ffb96d1b36b8aceadaa2a2a5e879ea779c2659665191a358be2186a168460c801f2789d86f5bb6d99b6519262d7e5c16b5754e4b50d411013d4f3374d5328c12f4b127c97244872087f1ec741cc6f1b4691a06717c58144420e03508c1e050100340800400 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0490.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0490.count (({ width := 8, code := 0xe0dedbd9d7d5d3d2cfcccbc9c6bfbdbcbab9b5b2b0a7a4a3a2a09e9d9c9b9a999795928e8d8b8887858483817f7e7d7c7a6f6d6c69686665615d5c5a58524e4d4c4a4842413f3e3d3b3733322f2d2b2928272422201f1e191715120f0e0b09050403020100 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0490
    Papers.RationalityTen.SharedFrameCatalogue.group0490_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0469.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0469.count (({ width := 8, code := 0x9694918f8d8b89888582817f7d7977767473706f6e6b6a69686664636261605f5e5d5b595857545351504f4d4b4a49484744434241403f3e3c3a39383734302f2e2d2c29282726252422201f1e1d1c1b1a191715141312110f0e0c0a090706050403020100 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0469
    Papers.RationalityTen.SharedFrameCatalogue.group0469_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x88087d86c86a86085f83382d8288247c67987476ff6cc6bb6a969e67365564b62761c6145f65ec5e158a56a54253a5295094b049048547c47044a4414314233ef3d33c43be38b34032030d2e32df29d25323422b1f51df1d21c21a918918116814912e1221050f30eb0d40cb0c00b80ad0ab0a609f09c09808107206e06c06a05d04403102c029025023008007002001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xf5f7ad3be9cdee60716b87daf0d3566732ad91cc6b6052fed790bba589ab414d2a46514a81931296048ca3a91c48dc46b230d15c8a544a21a10647913b39d1cd50683335183cbfc5d92e396b8b3658b29d14a0a0e4f625091e48d84402160ffc7c03d11d00e3c6d435819f8cb06382cb15c8a6050e23210507f43a21bd0c805c42c413108e045c1ec0e106e82f012406f03181800b605702a815008c04501c00d004601d00e00380100070018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73272770c6c569968f66765f6516496306055fe5d75d05875675435294e44c649d49248e47e47a46745845243c43841e4073fb3f13d73cb3c139937b36934d32d31930d2ea2bd2ad29b27f27626c26325924423c23621c2031f91f51ef1c51aa19518116f16c16515e13311f10f1080fb0f80d50c50c10bf0bd0ad0a109407106805f05805605204f04c04404103803102802201f01c00e00d009007002001000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73272770c6c569968f66765f65164963562f62060e6055f75d85cf57b55b54252a4d84ba49e49548b48147746045845245044b4444404393fb3f63dd3ca3c237b37335532e31f30c2c52ad2a527e27326f26025c24a23c23622421b20b2021f91f41f01c51aa19518017016b16415f13311e10e1090fc0f70d50c60c00bf0bd0ad0a109407006805e05805505204404103903102902202001c00e00d009007002001000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x6323129832bff57c2bc95acac655eaab5518a7e53aa99d48ea3443720f104e7e63e81ea0bf45f62ef9744b905ba2cd9630afe5702a915089a04a724c91988ae43a1ef8f0c71436a15b0a184e823b11488203701890bc851426a11c07c83b01be0cf05a02b015009e04c825c12a094048023011007a03901a40a0042015808803201700b005002000d } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x85c85083782c77276675374573d7307137066fc6ef6d06c556b55754e53652e52238437836535734f34232531830e3012e22d728827426b25324b23f2112051ea1dd18d17a17215c15414911b1081000ea0e20d70cd0c90c50c10b50ac0a709e09909709509409008c08807a07206905004202b02201901701601401000d } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0906.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0906.count (({ width := 8, code := 0x999897969594939291908e8d8c8b8988858482807e7c797877767574737271706f6e6b6a6866646261605f5e5958565452504f4c4a464442413f3d3b38373635333231302f2e2d2a2625201d17161211100f0c09 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0906.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0906.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0906.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0906.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0906
    Papers.RationalityTen.SharedFrameCatalogue.group0906_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0xa551e8741964aa51279349643208fc7a3518793c1daea7438d74b85b2d568b357ab95aac542993a9b4c255268e4521d06813a1c8de6c35194c25f2e164ae52289409e4e2612c90472210c84411f0ec74391b0c44c250e05c24110803c1809 } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record015_frame004_links_0000 record015_frame004_links_0064)
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
def record015_frame005_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0490.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0490.count (({ width := 8, code := 0xc7c5c2c0b6b4b3b1afadabaaa9a8a6a5989694918f8c7b79787775747371706e6b6a676463605e5b595755534b49474543403c3a39363431302e2c2a28252421201f1e1d1c1b1a171614110e0c0a080706050403 } : Fields).get c.val)
theorem record015_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record015_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record015) (record015.maps 5)
      (record015.inverseMaps 5) record015_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record015_frame005_links_0000 record015_frame005_links_0064)
theorem record015_frame005_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 5 :=
  of_group record015 5 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0490
    Papers.RationalityTen.SharedFrameCatalogue.group0490_facts record015_frame005_indices record015_frame005_graph record015_frame005_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (Fin.cases (record015_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x60c3049644af254927a534099149da4b1214902451a1d90bc81e3759ad0d426533201804bfa5a72b0943097248423390e07b83cc1d90e807243801a90d006643201810bf05902a813b899049a22a10987283421910ba058028612f07c03a416409d04602240f607603881b40d205a02a81500a004201880b0052025011007403801600680280100070018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x70ee01aab4c670c357daf85c6b7d67ac855ea955028b4b293d23a3545a86108a003da764d91a7338620b71682c4570ab95228e5009e1382584988c11120c4007c8ee1ce348640c51742cc540a212623c4107b0e41bc348640c417c2d84d09011c2183d05a0ac140250440740e01601a0280400700600800800 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x78b7837006f16cc66a6476416126055e85da5a058757d5564b749b48e4604554294203f03c43a335a33d3242fb2be2b62a929a29228626925d2522492302272041f31db1d21c41a919816514f14612e11a1050f50d20ca0a409508608307707206e06a06605705205104e04103002c02902502201d01c01600d00a008007003002001000 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record016_frame003_links_0000 record016_frame003_links_0064)
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0909.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0909.count (({ width := 9, code := 0xd5eab53a8d3e9b258fc5e1f077cbbdd6e56fb659ac760aed6eb357aa54aa14d98cb6552892c8e3f1d8d4622b1186c2a11078240dfefe7dbe9ecf3783b5d4e873391c2df6eb69a4c7602d95ea945a25007e31984b0562893c9a4b2311086421d0e46e36178ac4c230f870240d0502410070200c0401 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0909.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0909
    Papers.RationalityTen.SharedFrameCatalogue.group0909_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe4871e38c5b82da36c8b4a1a14cf86593261920c815fbaecd73cb55588abf1590aba559aa754a898a4b2a5692588d7459229d0f283f41ba0bcf4e79a3c11db0eba74637e9bc0db06c23599a70cec66932c1950c8a63f2fa1704abc544298945ca144d125b929091447d22d915c8a23ff1c98d4065e31c17e8b7455e28e13d897047822410e08543b81b50d204f025c12407f83c41ce0d206402fc0c205a02a814008803a01700a404802200f807402e01400700340120080028008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x70d7006f96da6c068466463562161a6025dc5ac57d56553152451f5114ea4dd4db4a94a149846c46044944343642e42241a3db3bd3b039537f37734932a32130e2e62df2d32b92b428727f27025723222a1fa1ec1e31c51af19a19517b16b14a13d13211d11010a0fb0de0d70c30bf0ba0ae0a70a308a08707106e05f05805605305104804604404303a02402201f01d00e00d009008002001000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xf08717b7e9bd0d84695b4559c6cbd647b1d1794b955c1ac7d58cab053f2961454a0f4d9268d32a9784b2255529a92448ea43d2008ec47223650ba8214059e7ce7a7243759b14d3067b2df165ca9c51627993848ec466221108c7e03e11a78ca05be2a714209c840e1f70e986d03021720a384e426412408f846021610307f03d41d40e406e03581a00b2055823011006902800c405c02c01580a404802200f007403801900b805802800f0068024010007 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2040f247723969bd2d8f6aeb4a9a16c3c5fc2f796dab07578aae551ca61523a71532696d472a2b505e7e93db1e9ce106c435518e4ba65bd2c29568a5a513248917c8723b11bc8bec56a28213988a44362000f507743ae1ac0d2865c3141740b7054428612e094048420a0e9059023011006903181700b405602a81500a0031015809004401e00e807003201700b005001e00d004802000e0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1d64e80737b7c9b80daf6ad352da7ad2068633f59eab8a59a2bbd56aa8850f272130694948e238d1a28cd45e22c114489c44a222cfec7c13a41cd0e3070c37c9bb0d626933381970c725f32ef970cb6e5a42cb9570a7c51b28393909764ae252126492248a23a91c48d24211df0eb068631b1808a7c4ea26812388b43fa1f20de064830a1640a5046821e0f207503881b60d405f82ac0e607003481900c205a028812008603a01980c40560240110034012008003800c004001 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3ac9d00e6f6f93701b5ed5a6a5b4f5a40d0c67eb3d58d6c275c5ad6d676aae53c287d3de9cf4a124311c48d446522fd16e8b044ca25111688442c200cea473337c9b94d766a734999dccb864b2fe9778b485902b31548a7c52228393d89784ab253925891447d23c11c48d24352100ef87543701a18c7860229e13b899849222d0fd87c83761940c1859829411808783c41d60e206d835017e0ab03901ac0d206302e016808603b01c00c40580290110034012008003800c004001 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x106a094057f4f91e03b5742e39c53706d4d8da9b4c684cc196326640c5d7bae059eb2d5529c524a1138a614ac9291ea3145482cfc9ea3c8784eb1cc3746d8cd19331860cbe9782c856ca814a27c4ac8e917214400758e61702c44f88f0e01bc340660b21542704c09011c2304406e0d41782b0480880f01d0380580780d0120200380400600800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1c5edfa6bab46191ebca5caac41566a2a4afa5312348ff474a38d1a28c0457213d03480b3c21ce8e406d43611a60cfc66b30297d0ba85c22d7166cabc53f28b14089c249c23a11988804231f80f8472c3851b28d4c67e32c1778b4054e29313908b440a1f70e886d030217208f045c1fa0e304601a40c605c02d01580aa054028814009004301d80e006202b012008803c01d00e005801e00d004802000e0040018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1012789b725a7cc275faaf856b4b0457a2a954f2a61519274130097049323fd1d28bb41e201cfd27c23d39bccd826ad3131740b805712a294b49fc49c22610f07e43cb1da8e1c6102d315a8a384e6230111081c3d41e40eb86cc34a19e0c505d02dc14a09e04d424210b08282c413a096049823c11808903481680ac05502a014406202200f007403801a00c005802a00f00680240100070018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xea86f434e1a1cc58612304172eb4859dabcd592ab2542a8ad3b89cf4c3a57528c91946822ed15e89f4499fccf8a7b53a11be4dd86ab34319d0c8c5ed2d2165caac53128f93c495449524491e88e03e81dd0da462e30316d0a244d425a11687fc3e41a60c385dc29411c08782c413a096049823c11808903481680ac05502a014406202200f007403801a00c005802a00f00680240100070018008002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x67a33b59c8cce635315d848c0d5d52e616d6b5855529e147ca2c4ffa7b127c90c46422d912288442c2004fe479f3c71d48e826f937499b0c505fd2f61690b28517269928c912474230911c8724252018db86b63421968c7c6062ef1560a7051627b13789684961fb0f787243721a80cc06302ee16808c04301ce0e1059827c12a08e04682300d606902e01680ae05502a00c8062023011007803a01c00a805001a0080038008002000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x98a619825f9765c9665693e4e92e488ba2487a1d86a177f5f3769d0729c871dc5711bc6e9b66d5ad6ad94625866157d5ed64565434e1354cd314bd2e4b5214751744d0e41d033d4f13ace7388db35cc22fcb52c4ab29ca226c972087f1b86b190621805c16c5a1384c114431003e0f42a0a41e0741906017050130340801c0200400 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record032_frame002_links_0000 record032_frame002_links_0064)
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x38f5c14ddb6e6b6e1b10d5c6a5b4d1982c586062f1171cb715b22c795ccac655daa194cca5b51ea8d53dc9b44c6a60929e92848ea3fd1ee8b0428a0f10227fc3f39f78f327923a69d18e6472238c1b68d6a6a334019d4ca864230f9850c085fa2f996dcb285852b21574a7e53028794209f24f027512c48d045821c90a483438b1be8cac63a3051780a2c4b623d110880c3f41a20bb857c28c12e093032818e09804902380b005502a013008c02000e807002e012007002c0100070028008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x8274081fbede96aeb42d90ac3c5f6adb5664b0756eaae551ca61523a8853889924ada47d1d28aa4209fa4f4e7513841ae4c725fe2e996a4b0a55a296944c9da49022f109c7d63b51bb0c3456a27311508504001ea0d6069432018a0ba05b82a013c097849c24211308584141e00c7059023011007903481900b405602a81500a004101880b004401e00e807003201700b004c01e00d004802000e0050018008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3b75d64e7a70eb7c9b74d5a6a534d9a40d0c678ae296b4b27577aad54e6a1e4f726ed306949483a38d1a28cd45f22e11608a244e2251116884426a00cf787523999c74e166f936e1aecd4e69333b9970c665fd2ef1720b6c5a42c39598aa453e291141c9bc4bc255929c93049224511f48f04712348ef868630112608b441c1f20b4852825610f07803881b60d406382fc1600ab04e01cc0d206402d010c076031016008802e00d0058024010007002800c004001 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x8ea388a6208721483e0c81dfe7d9f17a5e5785dc741c26ddad699a06558f629835f5745bd6a5915d5614e4f9394cd2e4891d45d0f419013e4f03b4dd354cf30cc02c8ad2809824885200721bc66160501384d12c4a124471003a0d8350d0320b42b098250801e0701b0681604c0f034090200700c0200400 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcb3635b07172eb2455929d54569b84a324251a08af449a1f90827f639b1c20df26d93521a4cce865c31b1784b665a42c2153ca7c51f283938492e48923e11c08564171f38ef87223671a18c5c60229b13b89a847622d0ff87c83701940c3856029411c08783bc18e09604601e40d205a02b01540a8051028013809004302080ec06202c011008003c01d00e005802600f00680240100070018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0x1daebf4b97bcd86b34f9bc6e22ff77b85b6d566add52a54da3512813f9ecde632f95c92451d8dc661f0d8542202fd7b3bdcee16d349a2c45e2dd56a74c25112813e1bcd65e2d15094492410478381a0cc642f170b4582b1489c482310078381b0d058260f068241007018080200 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0522.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0522.count (({ width := 9, code := 0x1007ebe9eef1763a5cee16e365aed468b419ecd64b1d8cc4613057ebe5e2e970b75aacd64b057ab554a953a99429d4ca4d1e8c43209027a3a1c4d2672f974b0522791c8a3d1d8e06632188a850261188842200f8783a1c0d06430170b050261208838180a0481c0c05018080200 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0522.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0522.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0522
    Papers.RationalityTen.SharedFrameCatalogue.group0522_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xefc76ebac1d06e6071db875be0dc36d035edab4d4a69b3449a16cf667730a9712b555642ad14eea1d4f4a57129090b46fa35519c8be45aa289136895445a21109a79c3a91ccce3a70b37c9b70d1c68032e18a0bfa5de2e416d8b4858729c94aca0e4d325e12ac94e49824912288fa46f23490947e23d71968c04526276137893046e20e0f786c032618c0b4855025610c07803ac1c60db06a02fc15607503781a40cc06002d011808603b01900c405802301100340160080038014004001 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x2a1d289fb3a26a4ab9031d23245b8ab11a1bc1d815009fcbe3796f09d6b9f71ee09bc3736c2d0593b11600bd9762d5584a654a2824ca94120a254187ecf81ed3c276ce49bd346678c898a2f85d4b215a2a8538a49392624a8859051e839c718d319e2c4570aa0fc1f43d0740e219c310570ac1442804c0760d81802c0460881001d0380580980e01a0280400700600800800 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
def record042_frame002_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0612.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0612.count (({ width := 9, code := 0x3077fba5c2d962abd5aa750a752e8f409ecea6f3196cae49208dc5e270f85401f0f67abc5d8ea73379b8d76933d98c55eae16ab357ab54ca24d2612a9448a3d188a4421908803f9f0de6d34194c65e2e1389a4b2210c8441200f07033190b4582b13090401f0d06430150a048200c058240e06018080200 } : Fields).get c.val)
theorem record042_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record042_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record042) (record042.maps 2)
      (record042.inverseMaps 2) record042_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record042_frame002_links_0000 record042_frame002_links_0064)
theorem record042_frame002_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 2 :=
  of_group record042 2 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0612
    Papers.RationalityTen.SharedFrameCatalogue.group0612_facts record042_frame002_indices record042_frame002_graph record042_frame002_links
def record042_frame003_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0519.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0519.count (({ width := 10, code := 0x8861682204801f77adea795e2781da75dcf721c5709b86cdb06a9a3669996498e621795c56b5996057158549495153e4e9384d12e48d2046d1945110429043e0f33c0ea394e2368d3338c9314bd2e0b126c9522c892107b1dc6117c5c1284911c4410c3f0f4370d8310c02e09c2207c1e06c1a06417058120400c02c080180500c0200400 } : Fields).get c.val)
theorem record042_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record042_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record042) (record042.maps 3)
      (record042.inverseMaps 3) record042_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record042_frame003_links_0000 record042_frame003_links_0064)
theorem record042_frame003_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 3 :=
  of_group record042 3 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0519
    Papers.RationalityTen.SharedFrameCatalogue.group0519_facts record042_frame003_indices record042_frame003_graph record042_frame003_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (Fin.cases (record042_frame002_supported hcells) (Fin.cases (record042_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x6bf59abd4e9b49a0cee471987c0ddee571b358abd5aaad1a833e9dcde653095496431d8c45225108642607017f3e1e8f2773b1cae36fb6daed56833590c35f2e168b05328938994923d0a823d1d4e26832974b457220f47235188c05e2c158a852261208c42200f07432180b858260f068241007018080200 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x13c6714cf98d2ca4fc838ed15a26c4086904a013f57a4f2ddf3b3746dbdacb4f67aca19031c600bdd78ae75b8b29612ba560a714928d4fa9b532a5f4aa9391ca3545c8790aa093ea7bcf11d53826acce9912e0574a71492824f09311e2123d8760d81a0314600bb0f01a42e85209c134260490901181f83906c0d01682b04a0880f01d0380580980f01a0240400700600800800 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
def record043_frame003_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0520.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0520.count (({ width := 9, code := 0x73f9dcbe571b87bbdc6bb55a6d16772d92c5e1b0980bcda6c35cac54ea14ea350a833e9d4e66f3498caa4f2691c7a371a8bc52190a83409fafa783adcce06d3499cc95e2d95cab5328d329647221067a3b9c8de6c2a1348c3f1e0ec74371b0d46630170b04e2611880381b0d058260f068241007018080200 } : Fields).get c.val)
theorem record043_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record043_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record043) (record043.maps 3)
      (record043.inverseMaps 3) record043_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record043_frame003_links_0000 record043_frame003_links_0064)
theorem record043_frame003_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 3 :=
  of_group record043 3 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0520
    Papers.RationalityTen.SharedFrameCatalogue.group0520_facts record043_frame003_indices record043_frame003_graph record043_frame003_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (Fin.cases (record043_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record043_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103
