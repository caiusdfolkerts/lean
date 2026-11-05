module
prelude
public import GraphInputsSix0Part00042Data
public import RawFrameSupport
public import SharedFrameGroups009Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x126d92b491244b1ff8f4475a36f13f889c33214102f80bbd09e3aedb75b3971c8ac5b5fc2fc9762b7d5a7aafd4b6a55501274936a93f49b231911e88543e2038fb47d23e21eb4efa76b3609950c7e60e2ff9784ba45b62a494dca044e626b92ec9644a1238915889242e213105c8163e71ed8d8469a30617b0b645922bf15709b44be24711c88c444c2110f907943b01640aa050c26210607d03ac190063030016c0b405602a812407e02b0140098046022010807803a016009804001c00d00580240100040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x14faa70d356979495a3e51a68a13bd9c4ccda5f52af94dc5762650e185641ee0d6d5e662b2e9948c8f63d2e295d0adc5602aad53a9bb4d8a54923490a47f227d0ce857426a11506c82f3999a24cf4668330994cc9863f2c395d4aa253429314249f84e8262129c93247c23791948c24562288df06d433018f0bf85da2dd1648a3c4fa25d12608f046422a10e08544101570a284ec26210807f03d01a4063030016c0b405602a812407e02b0140098046022010807803a016009804001c00d00580240100040018008002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x92090f90c9068fd8f78ec8db8aa8998828698498407e97e07d27ba7ac7a56c569669467f6706635fb5b85b459a58b58253b5354fe4e64e24de4ad49148b48848047046b3fa3ae3a739939438b38637e3323293143052fd2f12ed2e52ce2c22bd2ae2a92a52a12962932302211fc1f21e31db1d61c91a519d18f18517e17a17216516115a1010f80f00e70d20ca0c10b006105e05905805405304703e02b02802602302202101e01d01601301000e00d00b009008004003002001000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x129794049ee4cf22b90948363f31bd8d246662d715186f414e0490067e73eedf06f5977939adca4e326feb7a1b66ccc62dafe9728b605a8a9694aca144f226d927e93847022a510e80c3ec1f4cf10776360994cc8060b2f59778b7c5b52a494e09e84e626492ec964452215109c7f43e51ec8d846963171840ba85b62c01578a744f025211888804281f10f2075436a19c0bc85902b014009084541d20de06a03240e406f031818009203a01b80d406403101580a004a023011006c02c01300600280120080028010006002 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x82f82d82a82782281f81c8198148128108087fd7e57c67b979378878577d77075773172c7066fb6f86f06a668a67566165364b5da5d65c35a458253b53751e4fd4e34ba4a84a348d4864443ff3f83e63d33ca3b13a535c35533c33031f30e3022df2cc2c72b82b22ad24e24822a22020b1fe1e51da1d51c41a418617817415b15114a13e12c10c0f60ee0e10cb0c10b20ab0a409f06f06c06105e04703903603403103002b02802502302201b01601300c00a009008005004003002 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x4a024f121290546922a90ff870c23200cfce7ddbe0de3aeb6733b959c34e086e836f999ac5a5a8ab054b6a144fb279138c9b649fa3051148874119fbcfa67883bb1b00ca864230597a4bbc5bc2da9524a7a4b223390fc84e40c1f28f646c233d18b8bcc5d42c616009e04da25f129091c47223111008083e21e40ea86d43381790b2056025a12108a83e41bc0d4064827c138077031818008804101f80d406403101580a0048023011006c02c013006002c0120080028010006002 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x935488e3f91b58a343de1a70848023f35f72f82792bc5dd7ceb070d3821ba0dbe665b1697f4b865a92d45582a5a4f426e136c93f48f23c51828ba445221d0928234061fbcfb07d33d01e20eec6c232a9918bcc5b92da952ca72502270935c96c4b2233917087e43421390308003e51ec8d8c62e2fd1750b405802b0136897048e23611888944101f10f206a033818b0c285e42d01640a984d824211507c83bc1bc0d406482bc15809f04e01c80de0680318180064031018009804602200d802c0120080030014006002 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1641b14d82abef5d6ae1568ab1f587ab9d4569f1486a35ccfa64f304976c92a46b1cb8d9432e16508f83f3aa5b56cfd644312d87eb4654c288d3cc9da4c7261d2fc9704af256d2929464a024c5246918487240d2008ed473237cfa87123509984c8858b2b914f4a2450526d934497a477230910c8584231fb0f7c79e31c1818b38546296136098849c2080f9075037a1b40c385c02c01550a104ec26a12d093048023010f08584181f80f507803a01ca0dc06b034813e09c04a82480f807903901bc060026011808804001e00e806c02200e006802c012008 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record007_frame001_links_0000 (interval_append _ 64 128 133 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x126a92d48e64471fc8f6472e36b1928c3451a2650d385fbff9fd6fb37d03cc5e4aeca75f389dc28ddd6e533398b4bf75c3ad4d69eabe52d27a93749b54a124ed2428f346022f111288843fa13d04e80a3f99f58faa7a13c49ddcd846552fa171cb6c54b29c94089c24d725b12c894846422890f08524261fe0f9c7b63631a70c545e42e81628afc56026d12e091c46c23110307c83ca1d10d506783281870bd85c42ca1520a384e024011408603d81e20db068832813e09c04a82480f807903901bc060026011808804001e00e806c02200e006802c012008 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record007_frame002_links_0000 (interval_append _ 64 128 133 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x80f8087fc7f77f17e77dd7d67cf7cb7be7b379078874273e73172a7076fd6df6d66a369e68c68362b5e75b659057a5775325014d94c44c248c48948047245d45a44544443f4314244194104054043f23eb3e43a537434e33732d2ee2e42c82b72b029b29828f27126925e25325223a2302291e91df1c11ac1a719619318a16815d15614e14d13512a12311b10a1051010f90f40f00ea0e20df0da0d10cc0c90c20bf0b80b50b209309108a08807807506f06c03002602302202001e01d01b01100e00d00b009008 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record007_frame003_links_0000 (interval_append _ 64 128 133 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x582abef5a2ac7c90a45b1c08d3c34a173094841ba85b56d01677322989ac3c5a32a71512a254f4275d31c9874bf25c12bc95b4a4a51928092348ea43921090047d23c91d88e046c9f70e1e6a0330191cb085672a19440a164d926b92f48ee46622190c48464161fa8f6879431517c0b5054229c13509a049c2080fb87503841b40d386182d615b0aa854029214209d84c825a12608e846022610708003e41e00e807203701ac0d304f827011a08c03e01e40d406901800ac05002000f0074036016009802c012008 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x48e64471cb8dabcb5e3aec675b38bdc3ede56eab3358b4bf85f3ae216a8b4e55f296d4989eb4dda6d128493b490a3cd1808bc444a2210fe82740c1fccfc87d53e59eccf3c7783b31b0cca85f32e316dca9252d28393809b84b525a12908c845621e10b884c41d1fd8f907b036119f8c645e22ec1620b0456026d12f891c47223111408143de1e20e887243701aa0cf063030e17b0b485942c213a09404702180f6077036c1a20ce04f827011a08c03e01e40d406901800ac05002000f0074036016009802c012008 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x7fc7f77dd7d67046fb6dd6d36a86a168f68862a5e75b75af59157b5765325024fa4da4c54c148c48948047245d45a44544443f42441f41040b4043ff3f73f13e53de3a637334d33632e2ec2de2cb2b62b429a29928f27126b25e25625224b23922d2251e71d91c51ab1aa19519418a16816015615014d14613412612011b11711110a1050fc0f90f40eb0ea0e60db0d50d00c90c20be0b80b50b309309108308207807506706603002b02802001e01d01b01601300b009008 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x7bef7bed7da7adf55e9bd1f91f0dd7ba8747e57c8780ef5d97b0b5ae97d2795f28648c7f8db165c1b295a28d4ed9771da394548850ea1b4137e2fa1e8b996becc5932d759cb2155aa552ea3143a724c29651aa2f422770e99c936068cce1913185c0b315727a4c48b1121ce36c6a8cb1802ec5b0a610019c2e8590ac1502804f08e0fc1b02b04e098120220420780e8160240400780d0160240400400600800800 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xbcd5da2d05664afcd5e6ad149aa2a4dfa6c730693cc9aa2c314a89bc44a1f30e87472e79580a5051da5611ca8ad44ca0bcfb67ca3c999a8b1851c28390907623791b28bec54e29612f88544102010f507943bc1d70e786d035a1a50cf866030217a0b284a023211208283d81de0e906a8244102077037018c0be05c02d01580aa04901f80d8056027012008803c01d00d8058024011008003c01a00c00580240100040018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe31e18dc2dabd94d63d57d23d0acb4c9dc86c55c49bdcbcfbc7bb0ba4b99ad29a093c8f58e884f7f57bf7a774f6ef6dd6a063b5d75905835034bb49047f4353e83da3a63393203132e52d92cd2be2ab2752672592492392071f81cb15613612a10b0f20e70db0b408b07d07506c06105d05a05805405304903f03602b02702402201e01d01b01601201101000f00d00c00b009008004003002001000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x92c9228ea8d98c689788d86d86382b81a8077d87ce78878277d76f7697656de5eb59f56f5614fa4c94aa49d46442841b3f93b236633332b2c129027126422b1ec1e31c019018718116f16c16616115c14914313c13813212311d10e0e50d90d30c90bf0b90b50a908307706f06705c05805505304f04e04603e03602b02702402201e01d01b01601201101000f00d00c00b009008004003002001000 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c3c82e3df17f8a9c33616af355f9abcd5a29354489bdcd9665b314983496247f22d5cf2b69568a50513a50d1d28c144ca22905a7db3dc9e4ccd45a62c014709e640f1da8e346ca35617c8a9c50a25f10a88204021ea0f287783ae1cf0e3870836819f0c886042e61650af851027812f08c842c20a0f607803a01aa09104081c80dc05f02e81680ac05502480e806c027012808803c01d00d8058024011008003c01a00c00500240100050018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33879b6c82e2ff153866c2d5e5ad0166ea4b513266731a95ec9e24cb25891fc8b641d1fa888c3e21cedb866aab69518a50505a5692868e8460a25d11482c3fd9f98fb67a93c99698ab051c26b909881e3b41c68d8c6ac2f81638ac854e27512f88543f41f30f587943bc1c70e106d033e1910c085b02ca15f0a904ec25e128090046421810407b03c01c20d504081e00e406e02e81680ae0550248100074036012808803e01d00d8058024011008003801a00c00500240100050020008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe14dbbdbad96d76d61d55d06cadcacc88c68c53c47c26c0cbb2ba7b93a91a0494c9078be8538447e37d27b17497136fa6ee6dc6bb69e5e159c5034f94dd4cf4af4a147b4043e73d93b43a433b2e82d92cd2a92562282172081f91e91d81ba1ae17f17316515614313512910d0fc0f30e80cb0b309f08f08b07d06706605505304904003a03603203103002b02701f01e01d01b01101000d00a008007006005004002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa51d24691b47b975cb5257b29c91948621950b684fc21a04100e7ec3f1df76faa7cd34d5a52d0367e33bd642b0954ea99536a99d498a3e51e28e846d232918a8b7457229d14689b44a222cdac6bf326189cb0256a27b93489924ba256929093049124412108f647723891a47243861630af847821810588003e41db0ac84d425011d08783e41e20e9071036c1a80b805201c80dc06d034818c0be05e02d00e806c03401880ac04e025011005802400d0050024010007002000c004001 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x4ff67c539b9c3ccba62f1858b7c4aa22f0bc851c18e0a3041813c0519fcc3b54ca75931a9814ada55128e918483a3f11f48f3475a3911b270c3201614a0a4f426810c88224011f88f8462c29614289843861a20c906082e41550a8052428413b09904b424c11f08b043c21210507f03d41e00ea07103701ac0d0052025412208c04081c80dc06902480e806c03101800ac04e026012808803e01e00e8070036016009004402000d0050024010007 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33cb9c0c99e40b1898aec4fe2170dd863c2be10305367fb3358aac1f5b4abc5586aa953ba94cdea6dd2f596d4af64ef26c92bc8fa4591db8e1467e30f16a7cfb355738ada52d289d41694446a225d10e80d3f31ee4f527933341698a4c4f326b90407403631a98b6456428513a897c42a20d10407e83ca1d70e406ec35a1980c885cc2d816509b04bc24011308584101ee0e807083540f807803901b80d005e02d01600aa04402000e806c030013008804001d00d8058024011007803801a00b00500240100060028008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x3d97adf49e7fce79af33e63cb795f29e4bc8761eb7d4fa8745e81cf39d737e6bc23816f6de7bb373ee3dc3b7b6e6d7da7b33646c1d538defadbeb47666c8d40a093726a4918e11862d452812f45dabab746d4d8f2fe5eeaf151296522a2d1ba2f45086cfe9ec3ae72cde19e3285d8b796924a4687e0ea1c6364630b715a26c360690ca1882f0540a01382583f0780dc1a03004c0881001d0360580901101e0380680b0140240400600a00800800 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb63dacec155f7aeb570ab4558fa8cd3f27373879974c5e48522d8c445c9b5ccee647b0ed692a89515275931a9874bf25912b694d4a3a50124691d48723f11f48f247623911b27d037d9a60c805852b91584a2c505270934097a477233110c8224021f80f8462c3031790a9c52c27213089384101f70ea06883261810b905542a01490a104ec26412d093047c22c10f085840c1fc0f507803a01c80dc06b034012208c03701a406c03101800ac04e026012008804001e00e8070036016009004401e00d0058024010007 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x153da95d27690f454a204bae5a92c195048f24451848b6c16208302780ab4d5a5ed18685b40d9d4b26586aad153aa604dd268529093147a23b51d08e1467231517c8b7458a29d14489b44aa22cdac6c93389604ae851c26492e895a4a424c124491048423e91dc8de4691ca0e106342c415a0a644ce24c11e08a843020e10007bc3a21b60c205a42b214709a84ac23a10c07c83c01d20e306d835015e09b03b81b40d206802f016808003a01b00c806202b013808c04400d00580280100070028010004001 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x13a19c649aa4af23990fc6122db058820c09e02ad35685b3a964cab453026e92908f4476a3a11c28ce462a2f916e8b1454a2891368954459b58ce258128e13189824ba25992b494849f24c124491048323e91dc8de4691ca0c685882a914c899c4b624c11e08a843a20e10007bc38c1b60c205e02d21590a384e825611d08603dc1e00e9071836c1a80af04d81dc0d206802d010007e03a01b00c8062030015809c04602200d803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1237911c4e624f0f4871414e07cf567a3bc4de08c976173009570a5851925fd2348f44702345174881431a14d086838411a04d0067f83f319b4c18555280136899c4bb25412588fa476235117c89a44721d90c083c4191b80c405de2ce15c89d44d025b12688ec45c22110988043b61c80c7060c2ee16c0ae854828c13b09604642100f707583701a40af04d81dc0d206802d010007e03a01b00c8062030015809c04602200d803401800b005002000e0060028010004001 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
def record028_frame003_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xa6ba68a069fb9e99de99c99693c93492491d7ec7c67af6e66af68d6395f25cf5cb5c85c15b05a75a059959458b58457d57856e4814423bf37935435034934333e33633132a32331a31630f3082ff2fa28322b20d1f91eb1c21bc1b31ac1a019819018717b16315512c12511d1141081030fa0f30e70dc0d60d00cc0c50c10a809b07706906805a04003f03a03603203103002b02702302201b00d00c00b00a008007006005004002001 } : Fields).get c.val)
theorem record028_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record028_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record028) (record028.maps 3)
      (record028.inverseMaps 3) record028_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record028_frame003_links_0000 record028_frame003_links_0064)
theorem record028_frame003_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 3 :=
  of_group record028 3 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record028_frame003_indices record028_frame003_graph record028_frame003_links
def record028_frame004_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe21e14d80d76d60d59d13d06c72c68c52c4ba9ba57a0394c9078be8537fa7a279a79378375a73e72a7167076f06de6cb6bd69d5e159c5034bc4744704634554474314284184073f03e93db3ca3b33a333b2e82a92962862562492392282172091fa1e91d81ba1ae17f17316515614313712b11c1080f10e60d90cf0be0b209f09507506706605804003f03a03603203103002b02702302201b00d00c00b00a008007006005004002001 } : Fields).get c.val)
theorem record028_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record028_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record028) (record028.maps 4)
      (record028.inverseMaps 4) record028_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record028_frame004_links_0000 record028_frame004_links_0064)
theorem record028_frame004_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 4 :=
  of_group record028 4 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record028_frame004_indices record028_frame004_graph record028_frame004_links
def record028_frame005_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x7f57f07a179b78e78c76876271570e7016fc6746616475e05af5785415104d94d34d14cc4be4b64b04aa4a449d49749148c4824003d335d3302f72f52f12ec2e62df2da2d42ce2c52c22bd2b82b22ad2512141e11d51cc1ad1a419919118317c17316815c14613e11d11510c1010f30ed0e50d80cc0bb0b70b20ac0a409e09008807306606505803e03d03903503103002f02b02702302201b00d00c00b00a008007006005004002001 } : Fields).get c.val)
theorem record028_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record028_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record028) (record028.maps 5)
      (record028.inverseMaps 5) record028_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record028_frame005_links_0000 record028_frame005_links_0064)
theorem record028_frame005_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 5 :=
  of_group record028 5 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record028_frame005_indices record028_frame005_graph record028_frame005_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (Fin.cases (record028_frame003_supported hcells) (Fin.cases (record028_frame004_supported hcells) (Fin.cases (record028_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5db2b7b573ab3d16258b273934ab714c0a0d4ac2399106879433a0890207fe3ee1f2cf747902d414b09b24241d90d3c68a3331770b705942a814b8a184b82150f587083761a40cf86603221890c185f02ea16d0ac854829614409b04bc25011a08984301ea0ee07383641a609b03c01dc0d2068031817c0b605a02000fc062030015809c04602200d805802400e006803001600a004001c00c005002000c004001 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe1dd7dd5ed56d0fc6fc50c489499048c184f7f679a79378373e72a7166f06de6cb69d5e359e55f5034bc4744704634284184073e93db3ca3a33392e62962862582492392282192091fa1e91da1ba1ae1a019117316515613712b11c0f10e60d90be0b209507607506706606105d05905804003f03103002b02702302201b01601200e00d00c00b00a008007006005004003002001 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x9248b189488b8657f27d57cc5a95775494fa4ca49449248645c44d43f42941c4133f637033e3102c129125b25624d2212142061ed1e41da1bd19017015414f13b13813212d12812511f11811210a1051000fb0f00ea0e50da0d40cf0be0b80b30aa0a708b07006f06206105c05805405303f03e03103002b02702302201b01601200e00d00c00b00a008007006005004003002001 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record029_frame003_links_0000 record029_frame003_links_0064)
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1efbdefb5f69ecbd8fadf55e9bd1f91f0dd83abf50e5bc8f90f01debb4b676c2d3fa6b49e74cdf9ab32e5fcb3642b8d659d332a5c4728a910a1b4137f0fb5f23de7b2ce99732359cb2155aa552ea1d392614b290515a2343674ce49b0346670c61702cc55ca3139250480890e71c236c6a8cb1802ec5b0970fe1ec328620ba1582a05009e1382383f06a0d01882b04c0901102103c0740e01602003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8d58c18a789388b88a88687c87786d85284b82381d8167ee7e87e47c67bd79178e78875c75975374874674374173f73c68167166b5d25bf5b35525285094fa4d04a949f4994944903ae3a83a233533131730f2fd2e62d82c82c02a729a29729422921e2081ef1e81d21b91b119818a18117517116311610b0fe0f60e70d40cc0c40a008a08606a06706105a05805405305204703e03503403102b02602402202101e01d01c01601000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x1616c2577aed5d6ba56dad359eb0549a8d4c695526a3144a874fd9ed39e734dc99131a5fcb49612b655ca894904e003f8744e3dc1b5667ccc9943115fcbdd792ee5d094525a4641081cfa9f03ca75ce49c037269ccd99832856ca914326e4c49291a2264207d0f41d639c700bf1782e0598ad14a28c4f8820e21b83005d0b61502904e09a130208390620c0168290480881001f03806c0d01602003c0680b0120200380400600800800 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
def record030_frame004_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0262.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0262.count (({ width := 7, code := 0x1ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record030_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0262.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0262.localPairCheck (embedding (N := 44310) record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0262.localPairCheck (embedding (N := 44310) record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0262.localPairCheck (embedding (N := 44310) record030) (record030.maps 4)
      (record030.inverseMaps 4) record030_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame004_links_0000 record030_frame004_links_0064)
theorem record030_frame004_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 4 :=
  of_group record030 4 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0262
    Papers.RationalityTen.SharedFrameCatalogue.group0262_facts record030_frame004_indices record030_frame004_graph record030_frame004_links
def record030_frame005_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0154.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0154.count (({ width := 7, code := 0x1ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record030_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0154.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0154.localPairCheck (embedding (N := 44310) record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0154.localPairCheck (embedding (N := 44310) record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0154.localPairCheck (embedding (N := 44310) record030) (record030.maps 5)
      (record030.inverseMaps 5) record030_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame005_links_0000 record030_frame005_links_0064)
theorem record030_frame005_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 5 :=
  of_group record030 5 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0154
    Papers.RationalityTen.SharedFrameCatalogue.group0154_facts record030_frame005_indices record030_frame005_graph record030_frame005_links
def record030_frame006_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0232.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0232.count (({ width := 7, code := 0x1ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record030_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0232.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0232.localPairCheck (embedding (N := 44310) record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0232.localPairCheck (embedding (N := 44310) record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0232.localPairCheck (embedding (N := 44310) record030) (record030.maps 6)
      (record030.inverseMaps 6) record030_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame006_links_0000 record030_frame006_links_0064)
theorem record030_frame006_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 6 :=
  of_group record030 6 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0232
    Papers.RationalityTen.SharedFrameCatalogue.group0232_facts record030_frame006_indices record030_frame006_graph record030_frame006_links
def record030_frame007_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0130.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0130.count (({ width := 7, code := 0x1ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record030_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0130.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0130.localPairCheck (embedding (N := 44310) record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0130.localPairCheck (embedding (N := 44310) record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record030_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0130.localPairCheck (embedding (N := 44310) record030) (record030.maps 7)
      (record030.inverseMaps 7) record030_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record030_frame007_links_0000 record030_frame007_links_0064)
theorem record030_frame007_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 7 :=
  of_group record030 7 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0130
    Papers.RationalityTen.SharedFrameCatalogue.group0130_facts record030_frame007_indices record030_frame007_graph record030_frame007_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (Fin.cases (record030_frame004_supported hcells) (Fin.cases (record030_frame005_supported hcells) (Fin.cases (record030_frame006_supported hcells) (Fin.cases (record030_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0xc1b82affdfdbeb7cef8dd3b7b632bad57aad556aa540a7f4f29dd37a6747e8f51da3345e894a893925643c848fb1da1a42d847062073fd7defa9edbd2798f0ddbbad692d059e31a618c1d80af55dab956cad2592a654a28f5109cd31a594a8778da9a233c66cba96b2be560951041ba32c620b81642b05409312222c338660ca0901182201402402003 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb1eb0faf8aecad3ad0acaa49a0696190989a89888788485685484c84884484081b81781481280e8057327247176f56f36e96dd66365b6486356286135f75ef5d75cc5bf5b65a15884de4d54cd48f47d47146845644743a42741d40f3b53ac3a539d37535b34a33e27c23d22421b2111dd1cc1c11b717b1471110fb0f20e50dd0d10c80b00ac09a06e06c06b02502402300a009004003 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8d9c6c231f1888b0457627913587841f60b2fdc7da3cddd80e60720b785696b40593ac4d5e0ad555e2a9d546a8b53a29813c49c54d4263d31296e4a5a4b51788b0446a1c4eac7423961c94df66d835f1accd5c6883359984be85d22dd96c8b5e58d2b89598a264f926d93487803651910c4057628a13c08fc45a1bb0c785fc29413a077038417409a03d81e40f005902b8158084041020008003e01e } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x95495394e94d94c94b9459449419359128de8cc88c85381f80d7cd60b6055f85ea5d35cc5bc5ab5a259c58b57952e5255124fe4f44ef4e14ce49348f4784653d23c73ba3b139a38d37d37236935c34a3402f52e42d02c52bb2af29f29525a24a23522c19217215e15a13e12e12a11a1150f70e60e10d00cb0b20ae09f08a07307107005205004f04104003f02001f01e } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
def record037_frame003_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0xc8f91b1fe3ec798ef17e2dc4b877025ebbc973ed5d92b175da4ac9091520a3946c8c515e28c4b87d0be00bfd7e8fb1f2be27a8f11d23a072ae1d91b1b62ac41802f25ccb796c2ce58aaf547a844ee9b933a604b094919229438854cf97b2ca588a413626046c8a8f21be360620bd14c2844b8860e01b83685109e1381f83e07a0800f81e } : Fields).get c.val)
theorem record037_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record037_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record037) (record037.maps 3)
      (record037.inverseMaps 3) record037_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record037_frame003_links_0000 record037_frame003_links_0064)
theorem record037_frame003_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 3 :=
  of_group record037 3 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record037_frame003_indices record037_frame003_graph record037_frame003_links
def record037_frame004_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xdcdb976f6dcdabb5366ecbd85acb4a687d0b9b725e33c5587690d1ea33446804fc9df392704db99d2da45c878f71c636c688b711e12421829011c9b8d712e0db935c6a2d21a2b3b666ca57eaeb5beb5d69ac9582ae54b2894fc9d8ef9b032c638b39542944c0930fa1d6394698cc1602a44e8880e61c4380530a21402003f07c0800f81e } : Fields).get c.val)
theorem record037_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record037) (record037.maps 4) (record037.inverseMaps 4) record037_frame004_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record037) (record037.maps 4) (record037.inverseMaps 4) record037_frame004_indices (Fin.ofNat record037.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record037_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record037) (record037.maps 4)
      (record037.inverseMaps 4) record037_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record037_frame004_links_0000 record037_frame004_links_0064)
theorem record037_frame004_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 4 :=
  of_group record037 4 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record037_frame004_indices record037_frame004_graph record037_frame004_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (Fin.cases (record037_frame003_supported hcells) (Fin.cases (record037_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0xb0d7ab95aac5566d2a8f44a0cfa7b3cddeec75391bede6eb5da4d167b2588c3612f16eb65a2c55aaa4ea411a7a3a9c4da6832180a64e25118823d1c8d85e2a118883e1e0d0643014098481e0e058281206028080200 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x1aeb5a67acf394f295d6bab74ae8d9bb23636be56fac156a834fc9f13165c4a994718229c4b86f0aa1141782703dfe3f17d6e31c537f6eed9daeb50688cfd9ab28638bad63a98516a053e27a4a092d22a3b46c734e39a332e634c41862b84e0991282463fc7a0ec1cc36c698cd1922f0520550a814c218410800a01381f03c03c0700a01201001800 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8c9c5021db086737b7c1b20d1d687b40597ccab65131ed86eb3858fac55550a60516286537099b4c8257127292d48723dd1c2871426a0b50307543a91d1ce787313939bf0dca6cb35a1a64cf866132e98dcc4c5f32ea16f4b6658d2b89598a9e53d297946c9a44cb25a927091c3aa1c60db06c430815c09744682220f0070c37214f0a004c02020ba04902440ae056024807c03c01000780380140090028010006000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x23471508844029ff8f657abbad1c6ad9f68e3439a00cbe655b289870bef5df2ea1674b2158b2a9d4c2a2b50c26c932a98e438a0c903a7543a91d1ce787313939a80d2c67933017ccba85bd2d99634ae25662a794f4a5e51b26911c88ba44e2048f947923bf1c70db86c63471990c806102b812508c84401e00e186e43221810b88404174061030017c0ae05602480d406603200f80780140090028010006000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5b0ad5d63cb12465a3010cc859be71f18f747b5b83dbd2dc36d835a19fec905d52e116bcb4b581aa694569a14c9a6312ee9694b1255929e94848e243d2068fc476a398efe76639f1c4cdce6c334c97b0b8c59f2c615c4a9e52b28c13008ce45c22390ac8384141f78f7c6fa3571980c746042e015e0aa44a21f80f687603781ad0d286002e014909d84d025012108d04242060fc07503881b80d9069024812206f037012404a024011807c03c0100078038014009 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (embedding record050) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0xbb174ae3dc4b796eada5adb295e2af53ea4344282503a013fe7f4ac937172194137a6ec5c2b756dcd7dac323642c758cb1461ebf57caf25cab75692c3526a1d3f2754de9992ea464648a911a1d432839041c332662cc297e2f053ca493524a470768e21ae3386289c12e18c310540a613c270470820d01983204a0901181f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x5612afd51fa8d4d0e65d30797949e64cd238912b8e9c5ee226b1332592cc8363e2e395d8ab95532a7d2a68a041ea0d8f1477d3ac1cc4dc06d33571a1ccea66832d1944c8663d2e31680b1857b29a9464a0c4f827712a091847923591988b64562290f0c7303811b78c7c5fe2ea16c8b384fc25e12488e046422310e08583c01b70d104f01fe0d202e016c0ae056027810c08204001c80dc06c024011807c03c00f0070028012005002000c002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11b18d6457a2b310b87cc3160df0578043f29f64f6377bbb61da6eaa7373951c56def6ceb635a02cc6659b285872bee5dfaea562aac95582aa14c0a2c50ca4b10e27dc3e31d60e9a7373929bb8daa6bb3591984c546192ef171cb645972bd9594aa853229214689a44c524f12408be4502220f8c78e3be1d78d8867c3251898b8c5842b814809f44d623411108483fe1b90b1840019205c02d815c0ac04f021810408003801b80d804c024011807c03c00f007002c014009002000c002000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x605c077c6f7dd8ba9726d65a6b37636c457aadb5aaad556a8d4ee98d25a33462794e39bb34658c9891320e2ec4f8930fa1241581eef9bd348688ca992b1b616c017c2eb5c2b2d5d2b453ea3d3f2764d89852d24b4808f50e2184087dcf49e33ba704d71a5342600b99682b6540a313e2604a08e9102144107f8e41902a8490530a41382684807e0f41e03606a0d0128230440780e80f01c02c0500900800c00800 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record062_frame002_links_0000 record062_frame002_links_0064)
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
def record062_frame003_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x58cb1760abed73ae3592a053aa5d49290516a1741e79ced9c935e674c39732de2cc4787d0ea0cc017e2fade03b5762ea1c83806f2d01892ed5ccb015daae546a414227a4e69491fa3a44c861072073f87dcf69e33b6768e09ba354690cb9923205dcb51622bc5149c12e2504788d11420a3f07c0ea1ca390700c717028c4a8540a613c2704707a0ec1d0340660c8120220420740e00f01c02c0500900800c00800 } : Fields).get c.val)
theorem record062_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record062_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record062) (record062.maps 3)
      (record062.inverseMaps 3) record062_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record062_frame003_links_0000 record062_frame003_links_0064)
theorem record062_frame003_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 3 :=
  of_group record062 3 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record062_frame003_indices record062_frame003_graph record062_frame003_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (Fin.cases (record062_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x4de65ff2fe965c9d24e512586442d20ef04d81b3a6dbb6d4f68bb401888b8458baa89516a184d5a4d923e8cb46122bd14c89a4461f84e5e6cc3321938bb457728793e494a49c24492008ec46a1e98cb05dc26b12588b441a2000f206202d014a0950474202094049024011a06f03501800b605702b01540a803701900a004601f00f0074038014009804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
def record073_frame002_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x96595495394e93f93e92491c91b91190a9078e18a685e82e8197ca76371e6d86c96746265d75c656e56454c5425345254e747a42c3dd3cc3753302ea2db28b28126925f2512422131df1c819018017116115b14c11e10e0ff0ef0e90da09409209008d06f06a06005b05705605505403703202802301f01e01d01c01401301000e00a009008007004003002001000 } : Fields).get c.val)
theorem record073_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record073) (record073.maps 2) (record073.inverseMaps 2) record073_frame002_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record073) (record073.maps 2) (record073.inverseMaps 2) record073_frame002_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record073) (record073.maps 2)
      (record073.inverseMaps 2) record073_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame002_links_0000 record073_frame002_links_0064)
theorem record073_frame002_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 2 :=
  of_group record073 2 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record073_frame002_indices record073_frame002_graph record073_frame002_links
def record073_frame003_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0x5a6d167b3596c963b1586c15faf56aa54ba14f669299146e330e833f9f8f378bb1d6e97237dacce633116eb054a9d3c9c4ba59288f45a08fa75399b8da6b33188c05b2d160a641200f87835190bc582a148a04e210f06c30160a850260f070301408038180a04018080200 } : Fields).get c.val)
theorem record073_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (embedding (N := 44310) record073) (record073.maps 3) (record073.inverseMaps 3) record073_frame003_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (embedding (N := 44310) record073) (record073.maps 3) (record073.inverseMaps 3) record073_frame003_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (embedding (N := 44310) record073) (record073.maps 3)
      (record073.inverseMaps 3) record073_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame003_links_0000 record073_frame003_links_0064)
theorem record073_frame003_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 3 :=
  of_group record073 3 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record073_frame003_indices record073_frame003_graph record073_frame003_links
def record073_frame004_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0650.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0650.count (({ width := 9, code := 0x446210f87436190b8542611078340dfcfa79bb9cee16db51a4c961af174b258abd5cad55aa1449c4aa4d14843e9ece672381bcdc6c3518cbc572b150a65228134984a249208c3d1e0e87033180b45428138984a210f06c30160a850260f070301408038180a04018080200 } : Fields).get c.val)
theorem record073_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (embedding (N := 44310) record073) (record073.maps 4) (record073.inverseMaps 4) record073_frame004_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (embedding (N := 44310) record073) (record073.maps 4) (record073.inverseMaps 4) record073_frame004_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (embedding (N := 44310) record073) (record073.maps 4)
      (record073.inverseMaps 4) record073_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame004_links_0000 record073_frame004_links_0064)
theorem record073_frame004_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 4 :=
  of_group record073 4 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0650
    Papers.RationalityTen.SharedFrameCatalogue.group0650_facts record073_frame004_indices record073_frame004_graph record073_frame004_links
def record073_frame005_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0647.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0647.count (({ width := 9, code := 0x496492391486411f8f476391b8d4662b0f84411fef979bb1d4e26db4da2c963b0d84c05e2ed6aae53291389647a350a833f9f8f8783a9b8d46330974b85a2b14ca24d261288c3b1d0e06c32178b052271309448210f06c30160a850260f070301408038180a04018080200 } : Fields).get c.val)
theorem record073_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (embedding (N := 44310) record073) (record073.maps 5) (record073.inverseMaps 5) record073_frame005_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (embedding (N := 44310) record073) (record073.maps 5) (record073.inverseMaps 5) record073_frame005_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0647.localPairCheck (embedding (N := 44310) record073) (record073.maps 5)
      (record073.inverseMaps 5) record073_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame005_links_0000 record073_frame005_links_0064)
theorem record073_frame005_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 5 :=
  of_group record073 5 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0647
    Papers.RationalityTen.SharedFrameCatalogue.group0647_facts record073_frame005_indices record073_frame005_graph record073_frame005_links
def record073_frame006_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x193317e2dc33823035cab696bad2598b294ca85cda9632823744184b015febdd77ce89cd3726d4d6da8b48678c1d69ab551ca1d3123c43c85cf61e53ac734e19b831c584a912b2444708790b2043906c0cf18a3085d8861082083f8670c616c2b8530a4144280360620a01181f03c0740e0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record073_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record073) (record073.maps 6) (record073.inverseMaps 6) record073_frame006_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record073) (record073.maps 6) (record073.inverseMaps 6) record073_frame006_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record073) (record073.maps 6)
      (record073.inverseMaps 6) record073_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame006_links_0000 record073_frame006_links_0064)
theorem record073_frame006_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 6 :=
  of_group record073 6 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record073_frame006_indices record073_frame006_graph record073_frame006_links
def record073_frame007_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0535.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0535.count (({ width := 10, code := 0x2178521384a1184208806007fdfe7f5f47b1e4769d5731c46d9a86999962d7e5f16658d5b55d52531464f52f48920449043d8f4380dd354d1330c62f8b62c4a02689623c8c218781c86e19c641784a124471103c0e0360d4310c02f0b82b0a8240801c06c1a06413048100380a0240801c0400c0200400 } : Fields).get c.val)
theorem record073_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (embedding (N := 44310) record073) (record073.maps 7) (record073.inverseMaps 7) record073_frame007_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (embedding (N := 44310) record073) (record073.maps 7) (record073.inverseMaps 7) record073_frame007_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (embedding (N := 44310) record073) (record073.maps 7)
      (record073.inverseMaps 7) record073_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame007_links_0000 record073_frame007_links_0064)
theorem record073_frame007_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 7 :=
  of_group record073 7 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0535
    Papers.RationalityTen.SharedFrameCatalogue.group0535_facts record073_frame007_indices record073_frame007_graph record073_frame007_links
def record073_frame008_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0534.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0534.count (({ width := 8, code := 0xd7d6d5d4d3d2d1d0cfcecdccc9c5c1bdbbb8b2ada8a6a09b9694908f8d8c8b8986807b76746e6964625e5d5b5a595754514e4b4a4847464441403e3d3c3a31302f2e292825242221201f1b1a1716141312110d0c0b0a080706050403020100 } : Fields).get c.val)
theorem record073_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (embedding (N := 44310) record073) (record073.maps 8) (record073.inverseMaps 8) record073_frame008_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (embedding (N := 44310) record073) (record073.maps 8) (record073.inverseMaps 8) record073_frame008_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (embedding (N := 44310) record073) (record073.maps 8)
      (record073.inverseMaps 8) record073_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame008_links_0000 record073_frame008_links_0064)
theorem record073_frame008_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 8 :=
  of_group record073 8 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0534
    Papers.RationalityTen.SharedFrameCatalogue.group0534_facts record073_frame008_indices record073_frame008_graph record073_frame008_links
def record073_frame009_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0531.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0531.count (({ width := 9, code := 0x6532390c7e3b1b89c36170983c15eee96eb1d7aab4ea3cfe7b34964924511874220d037f3e1e2e970b7da6cb6230968b1562a54ca14d24d187e3d1d4e47035980b8582a1489a391c0dc6c2e160a4502612890461f0f0642e150a04c240d0602c1408038180a04018080200 } : Fields).get c.val)
theorem record073_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (embedding (N := 44310) record073) (record073.maps 9) (record073.inverseMaps 9) record073_frame009_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (embedding (N := 44310) record073) (record073.maps 9) (record073.inverseMaps 9) record073_frame009_indices (Fin.ofNat record073.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record073_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (embedding (N := 44310) record073) (record073.maps 9)
      (record073.inverseMaps 9) record073_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record073_frame009_links_0000 record073_frame009_links_0064)
theorem record073_frame009_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 9 :=
  of_group record073 9 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0531
    Papers.RationalityTen.SharedFrameCatalogue.group0531_facts record073_frame009_indices record073_frame009_graph record073_frame009_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (Fin.cases (record073_frame002_supported hcells) (Fin.cases (record073_frame003_supported hcells) (Fin.cases (record073_frame004_supported hcells) (Fin.cases (record073_frame005_supported hcells) (Fin.cases (record073_frame006_supported hcells) (Fin.cases (record073_frame007_supported hcells) (Fin.cases (record073_frame008_supported hcells) (Fin.cases (record073_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x88387886085584383a82a8217f27d57cb7bd7b67ac76d75c75774c7467416e16736335a857854851a5124c949e47f46b4393b13ab37d3783553453343302ec2e42ce2c52b62a92752642432242182101b91a519117e17416415a12511c1151060fc0f50ee0e008107f06906405a05505105004f04e04904603703202a02802602301f01e01d01c01401301000e00a009008007004003002001000 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
def record074_frame002_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1f03dffb9f6fe9fd27a0f3ddf7ad752e95ce7986ecd8fb135c6a5d4574ab3d2b97523e39450893051fc3df7a6eb9983255ecbc5672be546a7d312584828d9122133f67c8e99bb356684b395628c4c8949182243e0788ec1c236c6a8d018c2043e0680c61682a8510a013c2704b08e0dc1902a0500981181f03c0740e0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record074_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record074) (record074.maps 2) (record074.inverseMaps 2) record074_frame002_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record074) (record074.maps 2) (record074.inverseMaps 2) record074_frame002_indices (Fin.ofNat record074.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record074_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record074) (record074.maps 2)
      (record074.inverseMaps 2) record074_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record074_frame002_links_0000 record074_frame002_links_0064)
theorem record074_frame002_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 2 :=
  of_group record074 2 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record074_frame002_indices record074_frame002_graph record074_frame002_links
def record074_frame003_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x1ce39a724e41c3f85703dfbb4f606b7d63aa75165fc9791f1ce2cc4d67a9f5149612062841e82cf7ddf3a4726db1782eb58ab1153a954f69dd2023a448869049f93ba73cda1a3332634ad1492704a08f91321c3c4760e51b6348668c817a2083e86c0d01782c8550a814c2904d0900dc1902a0500981181f03c0740e0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record074_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record074) (record074.maps 3) (record074.inverseMaps 3) record074_frame003_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record074) (record074.maps 3) (record074.inverseMaps 3) record074_frame003_indices (Fin.ofNat record074.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record074_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record074) (record074.maps 3)
      (record074.inverseMaps 3) record074_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record074_frame003_links_0000 record074_frame003_links_0064)
theorem record074_frame003_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 3 :=
  of_group record074 3 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record074_frame003_indices record074_frame003_graph record074_frame003_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (Fin.cases (record074_frame002_supported hcells) (Fin.cases (record074_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x7ef7cf7c97ba7b07aa76d75c75774c7467416305ae5a85195124c949e47f46b4393b13ab3353302ec2ce2b62a926d26422d2242172101b91af1a519118817e17416412511e1151060fe0f50ee0e008107f07907606906405a05505105004f04e04904603703202802301f01e01d01c01b01501401301101000e00a009008007004003002001000 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
def record075_frame002_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x26832e79684a024bf24c892c322169077826c0d986ca9f545a4cd23e8cb457a2691187d33309938a184f925292248ec46a1f50f4c68232c1810bb84d625a12588b443820d10007903101770b4052827212a08e840412408d04382040de06a030016c0ae05602a815009e04901b80c805002300f807803a01c00d8054028013008804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record075_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record075_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 2)
      (record075.inverseMaps 2) record075_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record075_frame002_links_0000 record075_frame002_links_0064)
theorem record075_frame002_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 2 :=
  of_group record075 2 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record075_frame002_indices record075_frame002_graph record075_frame002_links
def record075_frame003_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e0d678b3757feb775b2a04cdd26d930c961caed804a4f51d23591868303f49edcf2a6ce28d941874438f17e0ad450626111908ac3f41f30f1877034c19e0cb862830417b0ba859c27a135097048423211208603f812408d04382040de06a030016c0ae05602a815009e04901b80c805002300f807803a01c00d8054028013008804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record075_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record075_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record075) (record075.maps 3)
      (record075.inverseMaps 3) record075_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record075_frame003_links_0000 record075_frame003_links_0064)
theorem record075_frame003_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 3 :=
  of_group record075 3 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record075_frame003_indices record075_frame003_graph record075_frame003_links
def record075_frame004_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x28a509a0f40e7fcfd9d739270cdb9b1356273ea7c8e25c236169aced97b0f556a9525245444828fd1f0398710cb98f308600a49422724a490117220404720de1b0334630c01762c03f87b0ea1c8330610ae1482704d09812c2304406e0c81402303e0780e81c0360540a0130220400700a0120200380400600800800 } : Fields).get c.val)
theorem record075_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record075_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record075) (record075.maps 4)
      (record075.inverseMaps 4) record075_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record075_frame004_links_0000 record075_frame004_links_0064)
theorem record075_frame004_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 4 :=
  of_group record075 4 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record075_frame004_indices record075_frame004_graph record075_frame004_links
def record075_frame005_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x95d95194f94493b93892491c91b91190a9077c06d56c95d45c656e54c5345254dd3da3cc2e72db28b26925124221a2131e61df1cf1c819018718017116816115b14c11e11510e0ff0f60ef0e90da09208d08708106f06a06005b05705605505404f04903703202802301f01e01d01c01b01501401301101000e00a009008007004003002001000 } : Fields).get c.val)
theorem record075_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record075_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record075) (record075.maps 5)
      (record075.inverseMaps 5) record075_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record075_frame005_links_0000 record075_frame005_links_0064)
theorem record075_frame005_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 5 :=
  of_group record075 5 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record075_frame005_indices record075_frame005_graph record075_frame005_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (Fin.cases (record075_frame002_supported hcells) (Fin.cases (record075_frame003_supported hcells) (Fin.cases (record075_frame004_supported hcells) (Fin.cases (record075_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x31e56e8b65da7ed15659af1d72e80d3e99e64dda6c72eb9684aee49b234911c78a3931b48ca45f22e2ee27123561a1ece359cab294a4a264df239d1b28ab447a0650147fa3f49f4cf6c7953029658a3c4f22450ecc74a3771ad8b945ac2c615a8a7c50426111587b03aa1ad0c806282f81740b384f425c12107f03bc1d20be04a024011a07003501800b805b02b01540a803801900a004802300f0074038014009803c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x16f2b7157b6889429a024fa676f3679a9c84e4071ea885c3da1c3098843c1da07903080ec025fecfe36b431f98a4b0350ca7b53409614a5243120a8ff474a37103e77136019fccb05e02e015d8a3050726f93008a4442218908c81e3f01e88dc46a23071548a604e02510f1874c3841b40d006042c414809d04cc22e10a07b03a41c608d03501840c005c02d81580aa05402780e406a03201480a004802300f0074038014009803c01c009004001c00a0040018008002000 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (embedding record077) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
def record079_frame001_indices (c : Fin record079.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33cb933c81624f0f981ec09d7feb775b2a034fa67993769b1cbae5a12bb926c8d24471e28e4c6d232917c8b8b38d7ecb3c563a93d44c8e746b22ad0147fa3f49ed8f2a6c2304164ca364f21d98e886ee2d61630ad450426111908ac41a2080fd07b03c61d50e406b433c1900c506082f81740b384f426a12e09084641fc0ef074823410e07003501800b805b02b01540a804f01c00c8050024011807803a01c00d8054028013008803c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record079_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record079.data.requiredEdges q = true := by decide +kernel
theorem record079_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record079_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record079_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1)
      (record079.inverseMaps 1) record079_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record079_frame001_links_0000 record079_frame001_links_0064)
theorem record079_frame001_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) : Supported record079 1 :=
  of_group record079 1 (embedding record079) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record079_frame001_indices record079_frame001_graph record079_frame001_links
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (Fin.cases (record079_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb90dc3ad39687b2f588ac0f304965caee3a31b88d6469631b17980138d5c2ad58686b38981eb4958bab294aaa39512a6f919c8ac44d223d0608244079fe4fa67b73ca1b6cc2a5e32cb1484a0a4f12450e686f03661ad8bf05e02db1628a7c50626011587743ac1d00dd86b434c1960c785f02ea16609e84b824210c077836c13c09004681a80c005b02d015c0ac05401900a004602200f8078038014009803801a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (embedding record080) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2a3f51aa8251166392e093cc8e238f1b986ec2a2140f957c23d55e88f13717b2598f8be95a3aae5566aa454da7652a692e48322810f685341ea0d906078a3ac1b80d5c6753341968ca264531e9680af653528c93e09dc4a824611ac8cc45b22b11487d43951b78c7c6162fd1770b384fc26a12e093446422310e08543c01b70d105e82aa13c08b83fc1b40d203c01b80b805b02b815809e04302000e406c024011807c03c014009003c01c00d0050024010005002000c002000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (embedding record084) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0xa2b43e84d009e53a2734db9af34665cbb9672c6584ae9552a2524878fd1a22d43c85301df43b5752e8dcab856dad91abb4c66ccd18ab0f614bc5722e05bcb1d46a6c4c096926235450825021f93ca76ce89c93706a0cd99732a60ca5942272464851071ea3cc788ee1b034c660bd1722a4500941241ac348600a41402784b0940e81b03404808c1001f03c0480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x1ecbd6fabf53e93cff9ef37e5fc878df17dc3b7761eafd039c732e2dc53846fedcfb7f6ced8d9fb37626c2c8d8f31a61bc17792e7da5b2b44684cd994b25a36c608b315214c1a7e2f71dbbab746ca98e30c59cae958295520a2d36a504888bd1421b40e7e4f99db3ae72cde1af34c668c19762de5a8989262363e4798cd1822844d8810f61482884d09811c1f03c06c0d0138240460880f81e03a06c0880f01c02c0500900800c00800 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1377997ccb6597274939448e1ef0df83bc13606ce9b6edb495a2ed096803111708b175582a89516a184d5a51126c91f465a30916c8af4532230fc272f36619c8cc864e2ed15dca3a50f27c929493849024492008d43571960c645dc26b12588f045a20d0f206202d01590a504a8202094048023811a06b03501700b605702b01540a8033019009004601f00f0074038014008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
def record091_frame002_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1071820c0d1f98f9c7c7bafdd24e87720384dc10d2866bb069800bed5eead655d6a9f52fa9494729dc4c224b123c903438a16506881f4019ec4ec66f93561980cb06432f916b4aca55d2a3934897c4a224a11f888438c1b60d886762b81498a044de24810806e432e1860bb0540242094048023811a06b03501700b605702b01540a8033019009004601f00f0074038014008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record091_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record091_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record091) (record091.maps 2)
      (record091.inverseMaps 2) record091_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record091_frame002_links_0000 record091_frame002_links_0064)
theorem record091_frame002_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 2 :=
  of_group record091 2 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record091_frame002_indices record091_frame002_graph record091_frame002_links
def record091_frame003_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x9fc9dd9d99ac98d9899149008f88c98b78ad8297e478577a77076a7256db6a567166a6566205ea5b65af59b55955254653f53651c4d948344a40f4083f43b637d34233b3272e42dd2d12ca2c22ab22420c2041e81a819618f18616f15812811610d1070ef0d809208e08c08b06b06a05c05b05705605505403303202402301f01e01d01c01401000f00e00a009008007004003002001000 } : Fields).get c.val)
theorem record091_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record091_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record091) (record091.maps 3)
      (record091.inverseMaps 3) record091_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record091_frame003_links_0000 record091_frame003_links_0064)
theorem record091_frame003_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 3 :=
  of_group record091 3 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record091_frame003_indices record091_frame003_graph record091_frame003_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (Fin.cases (record091_frame002_supported hcells) (Fin.cases (record091_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x15eda5250fa8473b79b3cd4e3ad1bd8d2442e1ed0e184c421e0ecd68646b1f9606a2850ca58523690c48323fd1b87713721b00d2c67f2f015d8a30507260119c8a4442219108c81e3d11b88c1c55229812887e03c61d30e186d03401620a404e826611e08b84281ec0e904702340d606a03081700b605702b01540a804f01c80d4066032014809004601f00f00740380140078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
def record092_frame002_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x110783740ca048fc97c6bdfdd5aea174938b9c44e136e436ddb5cc7b5f6af8d5d6a5f52924b10e284841a207cf626ed34b19e4cc06512f396a0aca55a28d93489824b025112509024421ff0ebc6c43541840ae054a29314089bc4b02100f0070c3721860bb054424210104702340d606a03081700b605702b01540a804f01c80d4066032014809004601f00f00740380140078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record092_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record092_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 2)
      (record092.inverseMaps 2) record092_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record092_frame002_links_0000 record092_frame002_links_0064)
theorem record092_frame002_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 2 :=
  of_group record092 2 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record092_frame002_indices record092_frame002_graph record092_frame002_links
def record092_frame003_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x8eb8ad89388e86c85684d7f67ee7e87c57bf7b77a07997926d868067a6005a85a251e4da4cd4c64be49a43b4013ee3dc3d038735532b3252fb2d42c92be2b42aa29c2722492171ed1e71bd19618b18017416b15e13411b10e1090f70f10e50d10c508208106906805f05a05905505405305204f03903503303202902402301f01e01d01c01400f00e00a009008007005004003002001000 } : Fields).get c.val)
theorem record092_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record092_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record092) (record092.maps 3)
      (record092.inverseMaps 3) record092_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record092_frame003_links_0000 record092_frame003_links_0064)
theorem record092_frame003_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 3 :=
  of_group record092 3 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record092_frame003_indices record092_frame003_graph record092_frame003_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (Fin.cases (record092_frame002_supported hcells) (Fin.cases (record092_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x679736d933c7be2370ed827c08dc12d6f6adaffd6eeb653e29e2ceea5d32ce961c92e465228694297d49e9b34a4239d1ac8304061fecfd2795295946c8fe4141d98e885f82d81638ad44c220d10407e83d81e30d3067832e1910c506082ce15f0a9051027a135094048423211307f03c011c08d04381ac0d406102e016c0ae05602a815009e03301900a404802300f807803a01c00d80540280110078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (embedding record093) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x14a4a49d23a8fb36e9ab4c6e60b2ba94cc98e4a114089643e61c3099840413e070d5368534119facf56772ddd560a9c53c299941694449824311f48f147423691988c345fa2dd1608a944ca249116722339192cc726282e694749ec4e426993249744ad253128092c49124511f48ea46f234902c6322da1638af84d625612488f045a1db0c405cc2cc1590a503e41e20e9071036c1a80be05501c40d606a03481880b805b02d00e006603201880a4048023011003c01c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x7bcf77ed7da7aef57e7fcef79ee3d8ba2f3de61ba36e6d4d67aa7515b2adf59a85cc897323e2b4428770da0a40e80ef49c233865ec917b2ad548a5d46a875029c9312574a48dd091fb364688ce1923185fcb81672c0554999172243e0788ec1ce384600bb1561f43e0640c61582a8540a21402704b07e0cc1902a04808c1102103e0780e01401e0380680b0140240380400600800800 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
def record095_frame002_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11898b9c4da2410f6872c27a12105a81d4065f6af957ba3ae1d3ce8771cb87dc10c805f6af815daa5f51c27712588ea46a23210e28644259ec0dd866032a1908bcc5652ab94d8a5051528413a89a44c225992108823fe1b10cf06523171818b8c5842b81550a4849220f0ff86e43501970c305d821c10006c023811a06b03501700b605a02b81580a804f01f80cc06402a012008c04402100f8078038014007803801a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record095_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record095_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 2)
      (record095.inverseMaps 2) record095_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record095_frame002_links_0000 record095_frame002_links_0064)
theorem record095_frame002_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 2 :=
  of_group record095 2 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record095_frame002_indices record095_frame002_graph record095_frame002_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (Fin.cases (record095_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xa3cd17a8794219cace066cb3518fac77237b1a489444561ed0e1646b141878a284f5a75d3569624ae255529a94648e245921e907480239d1c08d934b1958c8251828213cc9c24d123391508844322118aa452a28413909883f01e50e9870c3681550a8052428413b09a04ac24811f08c044421610307e03d41e00ea07103701ac0d0055023811a08c04381ac0d406902780cc06403101800a8052024011808803e01e00e807003601500a003c01c00d0050024010007 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
def record096_frame002_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x9984c6a5e92de934494244f20f878c3761790a882340b6016ff264ab2018f2ab8551aa7145495b4a4a4d9246911454225910687042f20e906682c32c9910c7c535292945ca144fc254126091447d2378c7c61a2fd1770b744fc26c12e09344782010fa878c39e1ba0d286242ee16d0ad052427a12d090845021810007803901ae0d1055023811a08c04381ac0d406902780cc06403101800a8052024011808803e01e00e807003601500a003c01c00d0050024010007 } : Fields).get c.val)
theorem record096_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 2) (record096.inverseMaps 2) record096_frame002_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 2) (record096.inverseMaps 2) record096_frame002_indices (Fin.ofNat record096.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record096_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 2)
      (record096.inverseMaps 2) record096_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record096_frame002_links_0000 record096_frame002_links_0064)
theorem record096_frame002_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 2 :=
  of_group record096 2 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record096_frame002_indices record096_frame002_graph record096_frame002_links
def record096_frame003_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xd4da9350e9bd11a1b41e80cbf9772d656c8f91b21e40abf532a34b894b27e41c4487d0de174277fefe5f93e97c4f49e73ca688cc5952bb564aa15129b4e09992da534926d8d61a133263cb415f2aa53ca412223a4588810a2063ec7a0ef1d03886d8d119a31c620bd1662bc548a51261f43e07b0f0188308600920cc190310600a8148240460880f81e03a0700d81502803c0700d01402404007 } : Fields).get c.val)
theorem record096_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record096) (record096.maps 3) (record096.inverseMaps 3) record096_frame003_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record096) (record096.maps 3) (record096.inverseMaps 3) record096_frame003_indices (Fin.ofNat record096.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record096_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record096) (record096.maps 3)
      (record096.inverseMaps 3) record096_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record096_frame003_links_0000 record096_frame003_links_0064)
theorem record096_frame003_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 3 :=
  of_group record096 3 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record096_frame003_indices record096_frame003_graph record096_frame003_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (Fin.cases (record096_frame002_supported hcells) (Fin.cases (record096_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x98d4b7a5af250907c8221bb0a885040b5fe4fe964aaae1546a9c516a54d28292e45022390f682e32c9910c7c5e129a949ca324a824d12308a031f1868bf45dc2dd13f09b04b824d11e07c83c01cc0db868831817a0a404f022e10b07f836811c08d04381ac0d406903401700b605702b015009e03301900c4060024011807c03c01c00d805402800f0070034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
def record097_frame002_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xdf9ddbdd9d92d7bd78cebccdccbc84c6dc6aa4e9038d68c48927f77e17d075073c72869f59d57056253d4bd4ad49f4364264163a52e72d82cc2be2ac25a24823822821a1ba1ae1a019118317116313712b0fd0f30e80bf08808708306906806706605a05905505405204f03303203103002402301f01e01c01b01501400f00e00d00a009008007006005004003001000 } : Fields).get c.val)
theorem record097_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record097_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record097) (record097.maps 2)
      (record097.inverseMaps 2) record097_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record097_frame002_links_0000 record097_frame002_links_0064)
theorem record097_frame002_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 2 :=
  of_group record097 2 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record097_frame002_indices record097_frame002_graph record097_frame002_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (Fin.cases (record097_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042
