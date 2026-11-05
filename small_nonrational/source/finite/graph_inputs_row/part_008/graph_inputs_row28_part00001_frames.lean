module
prelude
public import GraphInputsRow28Part00001Data
public import RawFrameSupport
public import SharedFrameGroups019Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups065Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x30154688f643a21050027e73e19ddce6a5f22f01660b185722a194dca3a4f8274932890447322e911085c41a2040eec73837e1ad8cf063c2fd1780ae04f225a12688804261fa0ec071c3241800bb05b029e14509d849812208d03701a80be05b02b81580aa054029813c09203601900bc054027013008c03e01e00e8070032014009004001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x602af9d762b8251a23d90e88414009f9cf8677739a97c89d248222e90b88343ac1ce0e386fc34c19e0cb863c30417e8bc059a2b813c899c4b424d11688804261fa0ed071c3241820bb05b02a214509d849812208d045821c10206e035017c0b605702b01540a8053027812406c032013808c03e01e00e807003601a00c8054028012008804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x147e89cfe9eb3966ec8f8fd10602bf47bcecdd839a724e1593b1459aa093625845a8ad0b20f40676ce61b0332604b796326a4b88f10d1ee398700bc1642b04a88d1042003f87d0d41a43285c0b41642a0530a40dc1a83104e0901181e03a0700c81402403c0700b0120200380400600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0xbcf5068bd029c73165546086106606bff794eedceb926f6db1b334d688cc58d3165f4ba1542a45129fd37a68494901172144207d8ee99d3345f8ba16226649c870f31b63185d8800fa19c320600b61642b0550a013c2704d0921141c83606a0c81702904e0901181e03a0700c81402403c0700901001c0280400600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3321938c5259e2bbd41c92f473a2610147b63ca9da0e3c6082dd93687f63b31b20b5850426111808a444821d10688003f41ec0f187383901b90d6867830417c0ba059c2b015109e84d425c12808c83f81de0e9048823411608704001c00dc06a02f81700b605602a81500a604f02400e006c032013809004601e00e807003601a00c8054028012008803c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x13766b4c79211fa20c067e8f79d839270adf1b5328628b3541a6c4b08ad07a033be76ceb1cc3786c0d5999322604bc96f2c65449d13525c4788910d1ee3b4730e01a22f0590ac1001f43d8790ea1a8348650b81682c8540a61482884d08c0dc1a83104e0901181e03a0700d81a0320540a01202203c0700b0120200380400600800800 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x1036033ff7aaf19c8b5d692cc588af85d2b896cab053a985172204187a4e81c434c684ce9953125f4bc96c2cc558a894727e4c08d11621e3fc7a0ef1be3606a0cc17a29c500990dc1ac348670c81682c05509a12c2504508810c2104007a0cc1882e04e0901181e03a0700d81a0320540a01202203c0700b0120200380400600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x72db66dad8cff6752eed530a4f496237d15c8924459d98cb261128212e091046f23489e84d624c11e08384001970c405a42b212b08e83c01d20e206d83501840b205782b813c09b03c01d40dc06a03481980be05b02d010007a03601900c405c0270118088032012007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x142e5bc7d8d1182144147f2fc9ddb9d6fada5a4b45616b2961ab25449712b24344c7c8f29d73a6568aa14727e4d08e91920a400788e81b8318608a71442784d0951222404386d0d619c328610c01782c8570a61481e83a0680cc1883005a098128230440480700d0140240400700800c01001 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x1432624929071f62b441855085f3bc074ee51bab6d670bc975ad6586a4d47a834c08cd1421b428640c41752e0584a4140240464820fc1d8354668ac1502844c89211a2304386c0d419c328610c01782c8560a41441e0390640c01702d056094120220420480700d0140240400700800c01001 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x271d2848fc4702364bc25d02d615cca9a52b28213d095649923391508644011f88dc86c233d1820b7857829514288f04541f80f2870c3241820aa853828e12b08b04241f80f507103701ac0d005782b8136091046823011607803701a80d205302000d806403101800bc05c02a013809404602200f807803a01c00d8068032015009004001c00d0050024010007 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb12aad93f90882076a7536fb6ec6085e257653e52e51c4c04b14a24904393ed3e338837b2f92e92642542311df1d21b51a81851761691541451351141010f70ea0cc0a80a709008d08507806e06a06906605b05605405304d04003603503203103002f02e02602302101e01c01901401301200e00d009008007005004003001000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0xc661b0379b4596c156a3cfa793999cae53269045a1b0b8440deeea70b75b4d4673298ec05b2c15ca350a712c904722502773a1c8bc5d2e164b0572a14ca44f271349444219087e391c0d46833180bc562a14898401e0e06c32170b0481e0e068281208018080200 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0289.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0289.count (({ width := 8, code := 0xbab8b5b1b0aeaba7a6a2a1a09c989796928e8b8a888581807c7b797572716f6b676564605f5c585655524e4a4948403f3e3b3a39363534333231302d2c2b2a2524232221201f1d1c1b1a1514131211100f0b0a090807060503020100 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0289.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0289.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0289.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0289.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0289
    Papers.RationalityTen.SharedFrameCatalogue.group0289_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x7293779a8acb663c30556e6ad354da68d3289764a023c11c28c3446a12d06c82f3e29c6ccda63d2ba156ca86518273933896c48b23011588a235a1a60c7c5dc2b915589f849a22310e085428613909804181f80f306903281820a404d826812208003c01d80dc05f02f016c0b405902b015408e04001e80d804e025011808804001e00e804801e00e00680280120080018008002000 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x71a6ee6bf6916606325ef5aa57f52f5235134f44d84cc4bb4a648647046b4383ec39d37b32831630c2f72e42d22c82b52a02962932142091f31dc1bc1b119e18616b1651610f60ef0e60d00c90c00b00a90a509609109008b07a07407206c05d05c05905805705405304503f03c03602702502302202001e01d01200f00e00d00a009008003002001000 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x189ab4d555a6cd0ae8434079f6cefa76b39098fcb685a329b9494a044d725091f88e245722490bc82e3e71ed8f1869a3221830b6455c29a136898048e23a10887c83ca1c30da06402da1540a184c420c0fa06402e013609904881e00ea06e02f816c0b405702b01540a604902000fc07c03d01b00bc04e026011808804201f00f0074032012008003801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcc5628ae194169fa4a1a4711f48c1439a18d0607fb3d29e4ce3a65226b931881e3e81e30e3467e32f17e0b1c4e225f10307fc3f41f30f2877838e1ba0da069833e1910c085b02ca15f0ac051027a12f09404642180f6078035413609104582040f007603701980be05d02d81680ae05602a814c09204001f00d805c027012808c04401f00f007403601a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6b26996555e45dd57c56c5555305004f84da4b248748046942b3c23bc36235734832d3073022ed2cf2af2aa23c2382302262122091e81dd1d51c41b71a518f18117a17116614613a11f1130fb0eb0cd0c50a208b08507f07506f06e06806005b05905705605305205104f04503e03d03602e02702502302201f01e01d01b01a01901201101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4d5882ab53669a149623f51b68a442d211501e7db3be9dace426ad2da1690a7051027a132492048022b90bc7ce3db19c0c8862a3061740b6455e28913c09804a423a11107c83ca1d50e286703201790b6855826210807d832013609104582040f007603701980be05d02d81680ae05602a814c09204001f00d805c027012808c04401f00f007403601a00c8048022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x4bd94f2161bc327d2f71e7bb8730e49beb68686cf593301568ac13ca6e4cc9591ea3945486d03203352690d019b31c620ba9662c4558a894627649c9211f22e4087d8e91c4354640b716026c460871021e4398720d81902e85b0b21602a8540a61442484007c0d81702704a08c1101f03c0740d81a0320480881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x3b7748e29a2b4263ec698ab075e8bc573ad457aae55328548e91110a1a420804f69eb3c0758de9bb2e25acb21622a45389e93125c4908e91120a3c8770ec1d23706b8cc18e2fc598a413c2243f87d0f21c03586a0c81702a8530a41442704d0981282083b0740d4168260480881081f03c0740d81a0320480881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa049e98447a378f77f7507136b169e67e4f947b46c45f4364043b43a431e3113052f52d92cd29528525a2282081f91e91a01911831731651561351291090fc0f30e80b309f09e08b08507d07606c06806706606506405d05505405305104904003603203103002f02e02701f01e01d01b01a01901201101000e00d00a009008007006005004003002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1ad8cea5dda93d1be8ae449222cd846b2348997cada55d29e142898c4bf25c122090246f234916056c2a613d09ac49823c10d08384001d30e1865c3101690ac84dc25611d07803a41c40db06a030815e0ae04d81e00ea06e03501a40cc05f02d81680a604001f80f807a03601a80c806203001780b804e0260118088032012007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6b633a91da8e646fa2b912488b26312fc97048823791a451427a135896c49823c10e88384001a70cb86202f01690ac84e825611d07b83c01d20e206d83501840af057026c11607803b81d80ea06e03501a40d0067033017c0b605a029810007e03e01e80d806403101800bc05c027011808803601a00c804801c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x87a10839e6769af6759a56d585454e5312548920439033e8ed390d931cb42ac9c24c8e20c801dc741a46618860164561485012c4a118451083f0ec380c42a09825084200781b064170501203c0c02c080140400c0200400 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x186aa8648d22d915e89a449a1f10a28063a41970c925f328393d092048923b11c088242b20d100074c37c1950c044f224b11e08b441a2000f906582d01590a504a823a10f064025411807a03901a40c605a02b81580aa054029014409e0490218108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x33498d2c0c5edae956ce8c7430a0f10427fc3f39e2ce7e71b38a99a8c125f82a913f49dc4c520d0fc06d830c17e8bc04b424a11e88804202030fd05d82d215f0a284e025c12608a83d8132092047022810607d02c81540a804b025011408803701980a004801f00e807002e014009004001c0080038008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x70761c5695285225004f54d44d048e45f42b4214003ee3d239f37236233f33531030b2ff2f92f42ce2c12b72a929c29426325724522621820b1f11ce1a819018817215413311e0fc0ec0de0c60c10bb08708606e06705e05805305205004f04403903703103002b02802302201e01d01c01b01a01401301100d00b008007004002001000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0801.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0801.count (({ width := 10, code := 0x1cf6fdb36716e5ad5e52546509364c92f438ed3ace1344cf334c530cb12bca62649725090238871f8751ac641745814450138481143f0ec3a0e4380dc350cc320bc29090220841f0781b06418050120400e0340a020070140400c0200400 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0801.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0801.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0801
    Papers.RationalityTen.SharedFrameCatalogue.group0801_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xabe551258523090a45721950ae8364179ee0ef470e368197cc8661b2e716bcaa0540292941c9f84c325992608f446f22b11448543d21a78c7c5fc2dd15709f84ba23c115088c4382150e486d83161690ab84ec2600fe07983480fa07903981bc0b605a02b01540a404e022810407603701680a804602200f007402e013008003c01c00d00580280120080018008002000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x30151fa8404162000fd87e73d89d94e366f034719f0c5a61b2f91580aac50b28093b89d24a222e10b48344091f88ef475a39e1bd0d7469a33e18d0bf45ec2e01660a7c4d025a12608ec45c22010908043f41da0bb057428a12c09304681f20e604882340c005c02a81500a404b02280f006c032014009c04802300f007403801b00d005002601000780300100070020008002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xcf3676b1cd7c2ac154329dd4cc95548d242d1f48cb457a26901078a33f1924c7062829493d09c64d325292248ec45921610087d23d31d30df86802d91638aa0512279135892c45a20d100071434c1960c405a029412a08e824811a08c04501f40f406f03501a40c005b02d015c0ac05502a014808a04201b80c8062028011808803e01e00e807003601a00c005c028013008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1cecdbd68832358a0c115ac2aad4509eb4e0263d2848fc473a3811b265631d98b4c285e22c915809e64e126592ac88443220e8f6c77c3a51b98c8c5e228413909704781d30e186b82d81550a704902060f507103581a00af0568298136091047023411808a04181e00dc06b03501a406603101800bc052024011007c03a01c00d806802800f0068028010007 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x29092f491547b21c909c84141820390027f03f39ec8f387663a81cd4e446bb32d17f8b7656f2aa9468a004e924011948ba45021b10b884241a1ef8eec71637e1b70d6c65631e1870bf45e02b913b893447a21310187e82ec16c0a284ec24c10907481c00d806302f816c0ae05502a014409e04c0248118070034015809c04601f00e807002c014009004001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x66359452850f5094d04b74a94994944904433f437336a35433031730e3002fd2d72c82bf2b12a729a29729427826721e2081e81b91b118a17517115714512811f11610b0f60e70cc0c409e09b08607606e06a06706105a05805405305204f04d04103803403102f02d02b02a02402201e01d01c01601401000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0x33799ca64b057cbbdd2e570b3d7aad52a853a652b8742207007f3f1ecf1763a5d0e66933582bf5dae56eb2582b154a751a813a9b4ba4d228f43204ec6e351989248229108642209007a3c1c0d86431180bc5c2d160ac542913094421f0d86832180b8582a1409848221007030160a048200e04018080200 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (Fin.cases (record071_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0xbe5ead365acd5aa14da4d1e89418b449fafa7a3c1d8eb73b91bcdc6b33578ab54299449f4e2692e9046a290e853d1d8dc6b3298ca853289389a4a2311488411f8f8783a1b8d86a34198c0582a14898482210078361a0c8602e160a85026100683014090401c0a04018080200 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (smallEmbedding record074) (small_cells_exact record074 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x644af195f2a344fea7c93a897b457a23109083440f9fccfbc7c838318f8c1a6012f49694a0e4e92581288928470230914885e4202000eb05e62d21498a044de24811b08903c01c30d586182ec1660a104c8222101054027412a08c04481e80e4069034019c0ca06303081740b405702b01540a805102100e806203001780b4056029012808803e01e00e807003601a00c00580280100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
def record075_frame002_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6bdb18d62c9fe4e4270535a98349b24a121890647fa3c11d48e33ca99a4c5a6192f115cc95648722110c88464011f88f8477c3aa1b98c104782180e9870c3681920c105c829013a096047822e11008203f41de0e9056027412a08c04481e80e4069034019c0ca06303081740b405702b01540a805102100e806203001780b4056029012808803e01e00e807003601a00c00580280100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record075_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record075) (record075.maps 2)
      (record075.inverseMaps 2) record075_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame002_links_0000 record075_frame002_links_0064)
theorem record075_frame002_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 2 :=
  of_group record075 2 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record075_frame002_indices record075_frame002_graph record075_frame002_links
def record075_frame003_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x727b3d96c4a354fda7ad36a94543aa1450187fb3f49f1cf6e7a7317140498e4b7240904468231d16c0b1c56a29314189cc4a624c11c08383821b30cb864431417b0ba85b82a414409b04a024211a08604141ee0f0056027412a08c04481e80e4069034019c0ca06303081740b405702b01540a805102100e806203001780b4056029012808803e01e00e807003601a00c00580280100068028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record075_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record075) (record075.maps 3)
      (record075.inverseMaps 3) record075_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame003_links_0000 record075_frame003_links_0064)
theorem record075_frame003_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 3 :=
  of_group record075 3 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record075_frame003_indices record075_frame003_graph record075_frame003_links
def record075_frame004_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x732d1d7e2aa52ea514627a4b294d23a454848ed1ca363ec690c898e30c5d0a994d2824fc9e1352664c09412523a42c750e41b0358698cc19431c5f8bd1762e45c0b716a2d0590b114e2644888810c1e0380670cc194318610be16c2c0550a814c290500840e81883005e0b41582904a0880f81e03a0700d81a0300580a01001a0280480800e0180280400600800800 } : Fields).get c.val)
theorem record075_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record075) (record075.maps 4)
      (record075.inverseMaps 4) record075_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame004_links_0000 record075_frame004_links_0064)
theorem record075_frame004_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 4 :=
  of_group record075 4 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record075_frame004_indices record075_frame004_graph record075_frame004_links
def record075_frame005_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0978.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0978.count (({ width := 8, code := 0xf7f3ece8e4e2ded8cdcac5c4c3c0bfbeb8b4b0aeaaa4999691908f8c8b8a8785817b706d6867666362615d5b595756555352504f4e4d4c494847464342413f3d3b383634333231302f2e2b2a29272523201e1c1b1a1918171513110e0c0a09080706050403020100 } : Fields).get c.val)
theorem record075_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0978.localPairCheck (smallEmbedding record075) (record075.maps 5)
      (record075.inverseMaps 5) record075_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame005_links_0000 record075_frame005_links_0064)
theorem record075_frame005_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 5 :=
  of_group record075 5 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0978
    Papers.RationalityTen.SharedFrameCatalogue.group0978_facts record075_frame005_indices record075_frame005_graph record075_frame005_links
def record075_frame006_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0489.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0489.count (({ width := 8, code := 0x8c8b8a89878582807d7b78767472706e6c6b6a696867666564636261605f5e5d5c5b5a595857565554534f4c494644423f3d3a38333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record075_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0489.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0489.localPairCheck (smallEmbedding record075) (record075.maps 6) (record075.inverseMaps 6) record075_frame006_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0489.localPairCheck (smallEmbedding record075) (record075.maps 6) (record075.inverseMaps 6) record075_frame006_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0489.localPairCheck (smallEmbedding record075) (record075.maps 6)
      (record075.inverseMaps 6) record075_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame006_links_0000 record075_frame006_links_0064)
theorem record075_frame006_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 6 :=
  of_group record075 6 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0489
    Papers.RationalityTen.SharedFrameCatalogue.group0489_facts record075_frame006_indices record075_frame006_graph record075_frame006_links
def record075_frame007_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0495.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0495.count (({ width := 9, code := 0x7e3e1e8ef76badcadf6ab4d9ccd653218cc55d2c560af562a146a14e26d30964a24d1c8c44a1904803e1e8ee76399c8ce632f16cb0562914496492210c843f1f0f478391c0dc6c351a0c8602f170b4582b1509842200f8783a1c0d0602e160a8502612088401e0d058281208038180a04018080200 } : Fields).get c.val)
theorem record075_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record075) (record075.maps 7) (record075.inverseMaps 7) record075_frame007_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record075) (record075.maps 7) (record075.inverseMaps 7) record075_frame007_indices (Fin.ofNat record075.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record075_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record075) (record075.maps 7)
      (record075.inverseMaps 7) record075_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record075_frame007_links_0000 record075_frame007_links_0064)
theorem record075_frame007_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 7 :=
  of_group record075 7 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0495
    Papers.RationalityTen.SharedFrameCatalogue.group0495_facts record075_frame007_indices record075_frame007_graph record075_frame007_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (Fin.cases (record075_frame002_supported hcells) (Fin.cases (record075_frame003_supported hcells) (Fin.cases (record075_frame004_supported hcells) (Fin.cases (record075_frame005_supported hcells) (Fin.cases (record075_frame006_supported hcells) (Fin.cases (record075_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x55d5245114c94b149e48547f46b45b4454393f73c237e37537035634233d32f2ec2db2ce2bc2b62a927526a26424322a2242101b91a519117e17416414212d1251060ee0e00c908107f06906405b05a05705505105004f04e04904804604503703202902802502301f01e01d01c01401301000e00a009008007005004003002001000 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x193eb3c53a28d933e8e7455a028ff47e93e29ed8f2a76b3041500a0446b1d98ddc5ac2c615a8a44504261129893048a22b111083840e2010fc87cc3d81dc0ea87203661ad0cf06403141740b3856029413d09a84b824211207f03bc1d208d04382180e006c03501800b805b02b01540a804f02700e0068032014009004601e00e807003601a00c0054028013008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
def record080_frame002_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x6fd69263d61b5e058c56852852251d50e5074fb4f047e4223ff3bf36333e2ff2f92f42e62e02d52ce2c22b829428426425825124823d23221720a1f11d71d01bc1a819f17d16915414313512811e10b0f20d50c60c108708308206e06a06805e05a05905405305204d04c03703303102802402301e01d01c01b01a01801501401301000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record080_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record080_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 2)
      (record080.inverseMaps 2) record080_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record080_frame002_links_0000 record080_frame002_links_0064)
theorem record080_frame002_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 2 :=
  of_group record080 2 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record080_frame002_indices record080_frame002_graph record080_frame002_links
def record080_frame003_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x236c42831005efbaa720d65a934f680ce196b225eab1156a894b690906a074087d0f69e23b8758e81bb36c6acd219f336658c89822f45bcaf1582964fc9d92523242c7f8f21d83986e0ce1742bc5407b0ec1d4320610be15c2985209a1302584708c0d8190300500901181e03a0700d81a0300540a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record080_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record080) (record080.maps 3) (record080.inverseMaps 3) record080_frame003_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record080) (record080.maps 3) (record080.inverseMaps 3) record080_frame003_indices (Fin.ofNat record080.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record080_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record080) (record080.maps 3)
      (record080.inverseMaps 3) record080_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record080_frame003_links_0000 record080_frame003_links_0064)
theorem record080_frame003_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 3 :=
  of_group record080 3 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record080_frame003_indices record080_frame003_graph record080_frame003_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (Fin.cases (record080_frame002_supported hcells) (Fin.cases (record080_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x23fd1b68c7452224110a846410203cfd87db3e91ea4f2077d3b594489e84e726492f0964481232115c87842f213101c7ea3e71ed8f1c76a3a91c68e046da34f19c8c9062830617b8b9c5b22ca15f8ac053828a13b89b44c025112388e84622110ff87c83ca1d50e286d434e19c0c806102f216d0b203200ba05c02d81680b005702b015404a024011808804001f00f007403601a00c005402000f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
def record082_frame002_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0xde1b4b646acd45a6b3c65ec9d8f316624bfd7d2f15d08f51822a4408690ba063f47d0f59e53c4748e79c93866e4d91ad346678cb18f30e5fcba96d2ca57cab94f296524a013d2684c4949242424648a9082063f07a8ee1cc3846c8d419a324620bd1741c82384608a110210410800fc1102104007c0e81c0360680c01702a04c0800f01c0340580a0120200280400600800800 } : Fields).get c.val)
theorem record082_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record082_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record082) (record082.maps 2)
      (record082.inverseMaps 2) record082_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record082_frame002_links_0000 record082_frame002_links_0064)
theorem record082_frame002_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 2 :=
  of_group record082 2 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record082_frame002_indices record082_frame002_graph record082_frame002_links
def record082_frame003_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0699.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0699.count (({ width := 8, code := 0xc0bcbab6b4b2afadacaaa9a8a6a5a4a3817d7b777573706e6d6b6a6967666564636261605f5e5c5a59575655535251504e4c4b49484745444342403f3e3d3b39383635343231302f29272625242221201f1d1c1b1a18171615141312110f0e0d0c0a090807050403020100 } : Fields).get c.val)
theorem record082_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record082_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record082) (record082.maps 3)
      (record082.inverseMaps 3) record082_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record082_frame003_links_0000 record082_frame003_links_0064)
theorem record082_frame003_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 3 :=
  of_group record082 3 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0699
    Papers.RationalityTen.SharedFrameCatalogue.group0699_facts record082_frame003_indices record082_frame003_graph record082_frame003_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (Fin.cases (record082_frame002_supported hcells) (Fin.cases (record082_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x55328d1440a0d4bba3f50e283040d9fccfbc7c83d71d68d6463e3171874c1a6012fe1654af254128393a49a449e248120c8e046122910fc7c23c51de8ea865031615c0a4c49023611207e83d61e00e7070c3721960c205d02c614209904802020d705201e80de06e03481740ae05602a012408403701b00c406002f016809804a01f00f0070028013009004001a00a004802000e005002000c002000 } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ab78b7636c96936495fe5c858357857356555454b54553e53852f52952251c46542e3f03e438934d32330c3042d02c92b62b02ab2472041dd1d31c019418516d15f15813211410c0ed0e60d80cc0c80c40c109809108d07606f06b06505f05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
def record084_frame002_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0779.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0779.count (({ width := 8, code := 0xcdc9c5bab6b2aca8a4a3a2a09d9c9b9a99989796958c8986857e7b7876756d6c696867615e5a5957514f4d4b4a4642413e3d3b3a3938373533312f2d2b2927252322211a191817141312110f0e0d0b0a090806050403020100 } : Fields).get c.val)
theorem record084_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record084) (record084.maps 2)
      (record084.inverseMaps 2) record084_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame002_links_0000 record084_frame002_links_0064)
theorem record084_frame002_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 2 :=
  of_group record084 2 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0779
    Papers.RationalityTen.SharedFrameCatalogue.group0779_facts record084_frame002_indices record084_frame002_graph record084_frame002_links
def record084_frame003_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0752.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0752.count (({ width := 9, code := 0x1017ebd1d0e46d3519ec561b057cbb5cadd6ab459ac962b055aa948a24f2712e9348a190881401fcfa7a3a1c8dc6631980be5e2b948a04c259289248239188a43208f476381a8cc5e2d148a04c251208c3e1e0e86c30150a048220f070281007018080200 } : Fields).get c.val)
theorem record084_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record084) (record084.maps 3)
      (record084.inverseMaps 3) record084_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame003_links_0000 record084_frame003_links_0064)
theorem record084_frame003_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 3 :=
  of_group record084 3 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0752
    Papers.RationalityTen.SharedFrameCatalogue.group0752_facts record084_frame003_indices record084_frame003_graph record084_frame003_links
def record084_frame004_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xce263cb04d5e6a9351da6752708f646f232913e86142620f90608214061ff8fe07e734f98f8bfc5f82b194389e64e926c91688a042b21090686de30f17b0bc059025811e88784061fa0d885d02d614309d049822a10707c03a413409304781d80de06b032817c0b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record084_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record084) (record084.maps 4)
      (record084.inverseMaps 4) record084_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame004_links_0000 record084_frame004_links_0064)
theorem record084_frame004_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 4 :=
  of_group record084 4 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record084_frame004_indices record084_frame004_graph record084_frame004_links
def record084_frame005_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x49890518a0a3fa7b4ecdc936c6cad7dacb4667acd59832963ec6989b0d586a9143a824ae8d510a1641c790f09cc38c704c416e2ba560a512923c438839031da358688bd1762bc540a413e2704007d0f41b8350670c21702c8570a61481c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record084_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record084) (record084.maps 5) (record084.inverseMaps 5) record084_frame005_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record084) (record084.maps 5) (record084.inverseMaps 5) record084_frame005_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record084) (record084.maps 5)
      (record084.inverseMaps 5) record084_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame005_links_0000 record084_frame005_links_0064)
theorem record084_frame005_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 5 :=
  of_group record084 5 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record084_frame005_indices record084_frame005_graph record084_frame005_links
def record084_frame006_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0769.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0769.count (({ width := 8, code := 0x95918d837f7b76726e6d6c6b6a69686766656463625d5c5a5956555351504c4b494847454441403e3b3a3837363331302e2d2c2b2a292827252322201e1d1b191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record084_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record084) (record084.maps 6) (record084.inverseMaps 6) record084_frame006_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record084) (record084.maps 6) (record084.inverseMaps 6) record084_frame006_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record084) (record084.maps 6)
      (record084.inverseMaps 6) record084_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame006_links_0000 record084_frame006_links_0064)
theorem record084_frame006_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 6 :=
  of_group record084 6 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0769
    Papers.RationalityTen.SharedFrameCatalogue.group0769_facts record084_frame006_indices record084_frame006_graph record084_frame006_links
def record084_frame007_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0741.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0741.count (({ width := 8, code := 0x95918d837f7b76726e6d6c6b6a69686766656463625d5c5a5956555351504c4b494847454441403e3b3a3837363331302e2d2c2b2a292827252322201e1d1b191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record084_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record084) (record084.maps 7) (record084.inverseMaps 7) record084_frame007_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record084) (record084.maps 7) (record084.inverseMaps 7) record084_frame007_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record084) (record084.maps 7)
      (record084.inverseMaps 7) record084_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame007_links_0000 record084_frame007_links_0064)
theorem record084_frame007_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 7 :=
  of_group record084 7 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0741
    Papers.RationalityTen.SharedFrameCatalogue.group0741_facts record084_frame007_indices record084_frame007_graph record084_frame007_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (Fin.cases (record084_frame002_supported hcells) (Fin.cases (record084_frame003_supported hcells) (Fin.cases (record084_frame004_supported hcells) (Fin.cases (record084_frame005_supported hcells) (Fin.cases (record084_frame006_supported hcells) (Fin.cases (record084_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
def record085_frame001_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x29092f691647ea3d909c84041820390007f03f39af4cb85fe2de1634ae255629c1470a024ee274936c9924a323a11948b845022290d885a42120d0e786fc36f19f0c7861e2fd17b0bc05be24c11e88484061fa0ec06d03241760a2849823010907c83a40e006c030017c0b805b02a815007e03801a00bc05a028013809004602100e8070028013009004001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record085_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record085_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record085) (record085.maps 1)
      (record085.inverseMaps 1) record085_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record085_frame001_links_0000 record085_frame001_links_0064)
theorem record085_frame001_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) : Supported record085 1 :=
  of_group record085 1 (smallEmbedding record085) (small_cells_exact record085 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record085_frame001_indices record085_frame001_graph record085_frame001_links
def record085_frame002_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x5a754d51d50a5064b04a749d48447e47346b4053d83aa38e37736836034f34433832b3293223152fd2e52d92d52cd2c62ba2b52b02a926425324e23622421c2102092051fa19b19017316d16414a1351251150f50e00d30c80be0b206a06605a05905605504f04e03f03803402f02d02802702402302101d01c01401301201000f00e00b008007004003002001000 } : Fields).get c.val)
theorem record085_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record085) (record085.maps 2) (record085.inverseMaps 2) record085_frame002_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record085) (record085.maps 2) (record085.inverseMaps 2) record085_frame002_indices (Fin.ofNat record085.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record085_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record085) (record085.maps 2)
      (record085.inverseMaps 2) record085_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record085_frame002_links_0000 record085_frame002_links_0064)
theorem record085_frame002_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) : Supported record085 2 :=
  of_group record085 2 (smallEmbedding record085) (small_cells_exact record085 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record085_frame002_indices record085_frame002_graph record085_frame002_links
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (Fin.cases (record085_frame001_supported hcells) (Fin.cases (record085_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xb01550a9092f691647ea3d909c84041820390007f03f39af4cb85fe2ab14049dc4e923291708a043621690848344091fa0f8077a3ad1cf0e346fc36f1ae8d3467c32d18f0c3c5fa2f61780b3054226812608f445c21210187e83b41b60c905d828a12608d04241f20e903b81c00d806002f81700b605502a00fc070034014009c04802300e807003601a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
def record086_frame002_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xae254ba8d531c92c474234908c83340f1fc4fba7c73d89bc0d4663f2d89594a68526257128492646e230114488442f21010608003ef1f08f4c78a3bd1d60e6871837a1b60d8867632718a8bc85a22a814009b84b623511188403da1d00dc865c2a012108804001e80e703b81c00d806002f81700b605502a00fc070034014009c04802300e807003601a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record086_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record086_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 2)
      (record086.inverseMaps 2) record086_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record086_frame002_links_0000 record086_frame002_links_0064)
theorem record086_frame002_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 2 :=
  of_group record086 2 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record086_frame002_indices record086_frame002_graph record086_frame002_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (Fin.cases (record086_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6473095818c0555a2951476a344bda4591fa8f643a1f9ccdc60d2fc17c8aac50127713a490441a2048fd07c03bd1d68e7871a37e1b78d7469a33e1968c7861e2fd17b0bc059a2a213c89684401fa0ed06d83241760a2849812409104702340de06e03581a80c005f02e016c0ae05602a815006e03601980c8050027012008c03e01e00e807003601a00c0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
def record088_frame001_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x306dd3b3d51282cd09511be34c648b915a13c2283304e07c08784d3191b1a5a6a0d3e26f4bc96d2123243a8690a1cd3165f4b515f2ae4ec999242364547e8e71c2340658c71722d8590aa11221c4287f0de1b4358640c217c2d0590ac150210410680cc1482704a0881001e03804c0900f01a0280480700600800800 } : Fields).get c.val)
theorem record088_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record088_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record088) (record088.maps 1)
      (record088.inverseMaps 1) record088_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record088_frame001_links_0000 record088_frame001_links_0064)
theorem record088_frame001_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) : Supported record088 1 :=
  of_group record088 1 (smallEmbedding record088) (small_cells_exact record088 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record088_frame001_indices record088_frame001_graph record088_frame001_links
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (Fin.cases (record088_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x66b6666625a65a259e50e4a346f4683a93a63a239a39238e38037737035834433d32c32a3162fe2ec2db2ce2bc2b629d29028927726c26424522c22420a2061ec1d01b91a519117e17415314913411210a0f20e40df0ba0ae0a609e08708107f07e07206906406304203703203103002f02d02902802502302201f01e01d01c01b01a01801401301000e00d00a009008007 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
def record089_frame002_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xc63627b0f13fc9ea4eba5412068e046c99a4caa6413169864c0c5e22e89700ae653c29593809a24ab243919c8844232008fc477c3aa1cb8dcc6c43511820b3457827113108f04301f80e986d03241820aa853828012408e84241f80f507103701ac0d004e824811a08c03d01bc0d406902100dc06403101800bc05a029014009404602200f807803a01c00d8068030014009804001c00d0050024010007 } : Fields).get c.val)
theorem record089_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record089) (record089.maps 2) (record089.inverseMaps 2) record089_frame002_indices (Fin.ofNat record089.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record089_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record089) (record089.maps 2)
      (record089.inverseMaps 2) record089_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record089_frame002_links_0000 record089_frame002_links_0064)
theorem record089_frame002_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 2 :=
  of_group record089 2 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record089_frame002_indices record089_frame002_graph record089_frame002_links
def record089_frame003_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x3af758e99ac35369ebcd5d29f53693525a4747e8e91c22e4568a50c20b40c7c8f69e03aa72ce09b7352690ca18e318604bd9762ca56cac9442824d09411f2264207f0f91d03886b0be1742a45089d11e228438840ec1c43686c0ca1802e05b07c0dc190310600bc168290500941182203e0780e81c0360680c0140260400700d01402404007 } : Fields).get c.val)
theorem record089_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record089) (record089.maps 3) (record089.inverseMaps 3) record089_frame003_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record089) (record089.maps 3) (record089.inverseMaps 3) record089_frame003_indices (Fin.ofNat record089.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record089_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record089) (record089.maps 3)
      (record089.inverseMaps 3) record089_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record089_frame003_links_0000 record089_frame003_links_0064)
theorem record089_frame003_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 3 :=
  of_group record089 3 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record089_frame003_indices record089_frame003_graph record089_frame003_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (Fin.cases (record089_frame002_supported hcells) (Fin.cases (record089_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x66b6666625a65a259e55d52450b5074c94b149e48547f3a93a63a237033d32c32a2ec2db2ce2bc2b629d29028927726c26424522c22420a2061ec1d01b91a519117e17415714b14213612d1251060ee0c908708107f07e07206906406305b05a05705505405105004f04e04203703203102902802502302201f01e01d01c01b01a01801401301000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x60b5ef5be55d5245114f04d94c94b149e48547f46b4133f83c337033d32f3142fc2ec2db2ce2bc2b62a929d29028927726c26424522c2242101fb1b91b01a519118917e17416415714b14213612d1251060ee0e00d50c908107f06e06d06906405b05a05705505105004f04e03e03c03703202902802502301f01e01d01c01b01a01801401301000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
def record091_frame002_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x2e771b6d92c760acd5aa950a4d1e893e9348a370d84411fafa7bbd1d8eb73b85bcdc6cb59a8d266b2990c35e2bd56a85127d389a49a411a8a43a1506763719cca632813c8c45219087c3d1e0ec6e361a8d0582a1409c44211007c361a0c8602e160a84c24100703014090401c0a04018080200 } : Fields).get c.val)
theorem record091_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record091_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record091) (record091.maps 2)
      (record091.inverseMaps 2) record091_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record091_frame002_links_0000 record091_frame002_links_0064)
theorem record091_frame002_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 2 :=
  of_group record091 2 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record091_frame002_indices record091_frame002_graph record091_frame002_links
def record091_frame003_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0x29948a24de693194ca24b238f472331584411faef75391b8da6bb55a0cf65b1d8ac360af978b95a2c960aa50a5d269146a290e85401f4f4783b1cce26830970b4582210c7e3e1e0ec70371b0d46632188c0542913094401f0f07432180b8582a1409844200e060281208038180a04018080200 } : Fields).get c.val)
theorem record091_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record091_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record091) (record091.maps 3)
      (record091.inverseMaps 3) record091_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record091_frame003_links_0000 record091_frame003_links_0064)
theorem record091_frame003_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 3 :=
  of_group record091 3 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record091_frame003_indices record091_frame003_graph record091_frame003_links
def record091_frame004_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x16c6b2954426451f48bf439a13d06080c3f49f1cf6e79531797d4aa845d1e30e2c67e31b17e0b6056a29314189844a624c12288e046222b10707e43e61dc0e3869833e1970c5060c2f61750b3857c2b01520a5051027a12108603f81ec0f004902340ec07403781a80c206002e816c0ae05602a815007c03c01b80c8052028012808c03e01e00e807003601a00c00500260100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record091_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 4) (record091.inverseMaps 4) record091_frame004_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 4) (record091.inverseMaps 4) record091_frame004_indices (Fin.ofNat record091.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record091_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 4)
      (record091.inverseMaps 4) record091_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record091_frame004_links_0000 record091_frame004_links_0064)
theorem record091_frame004_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 4 :=
  of_group record091 4 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record091_frame004_indices record091_frame004_graph record091_frame004_links
def record091_frame005_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x2184207eeee5c9b836e2da1b0b5569acfd9db2f5e2b795ba764a491119229444855051fe3f47c0f49e23bc750e59c4356658c79802da524a19392524848b9102023f07b0f21d83a0720cd1762c0560a80fe1ec3586a0cc1842c0570a81482704d09812c1e03b06e0c81482804a08c0f81e03a0700d81a0300500981001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record091_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record091) (record091.maps 5) (record091.inverseMaps 5) record091_frame005_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record091) (record091.maps 5) (record091.inverseMaps 5) record091_frame005_indices (Fin.ofNat record091.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record091_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record091) (record091.maps 5)
      (record091.inverseMaps 5) record091_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record091_frame005_links_0000 record091_frame005_links_0064)
theorem record091_frame005_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 5 :=
  of_group record091 5 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record091_frame005_indices record091_frame005_graph record091_frame005_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (Fin.cases (record091_frame002_supported hcells) (Fin.cases (record091_frame003_supported hcells) (Fin.cases (record091_frame004_supported hcells) (Fin.cases (record091_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x59358958557056555d54052c5245114f14da4c94b149e48547f46b39a39238e38037737035834433d32f3162fe2ec2db2ce2bc2b62a929d29028927726c26424522c2242101ec1d01b91a519117e17416414212d12511f1060ff0ee0e00d60c908107f06906406206105f05b05a05705505105004f04e03703203002f02d02902802502301f01e01d01c01b01a01801401301000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
def record092_frame002_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x13909c14dd26b534c9a04c1a5b92d095149b24a123690c47fa3c11d48dc3169864c0c5e22e89700ae653c29593c895648723391088464011f88f4477c3aa1cb8dcc6c43511820b3457828311e08603f01d30da06483041620a404e826612c08b84402080f607783a412408d03781a80d006703281840c005d02d815c0ac05502a00dc06403001780b4052028012808c03e01e00e807003601a00c00500260100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record092_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record092) (record092.maps 2)
      (record092.inverseMaps 2) record092_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame002_links_0000 record092_frame002_links_0064)
theorem record092_frame002_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 2 :=
  of_group record092 2 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record092_frame002_indices record092_frame002_graph record092_frame002_links
def record092_frame003_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x1a434267ecd596b2862ac2181af45c0b55662c056eaa953a9c47e8e91c22e4568a50c20b40c7d4f01d5396704db9a9348670ca18e318604bd9762ca56cac9492684a08f9132103f87c8f01bc348660c71702c85309e1342543886d0c01702d0590ae14c2905009e12c250490900dc1903005e0b41482804a08c0f81e03a0700d81a0300500981001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record092_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record092) (record092.maps 3)
      (record092.inverseMaps 3) record092_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame003_links_0000 record092_frame003_links_0064)
theorem record092_frame003_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 3 :=
  of_group record092 3 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record092_frame003_indices record092_frame003_graph record092_frame003_links
def record092_frame004_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x13f69eb4ec26d53429914a2a42d1f48bf43aa14506080c3f49f1cf6e79526392dc94848123691748223d71e30e2c68231d17e0b6056a29314189844a624c12288e046222b10707e43e61dc0e086cc34c1970c505ec2ea1670a9051027a13609084682180fe07b83c012408d03781a80d006703281840c005d02d815c0ac05502a00dc06403001780b4052028012808c03e01e00e807003601a00c00500260100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record092_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 4) (record092.inverseMaps 4) record092_frame004_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 4) (record092.inverseMaps 4) record092_frame004_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 4)
      (record092.inverseMaps 4) record092_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame004_links_0000 record092_frame004_links_0064)
theorem record092_frame004_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 4 :=
  of_group record092 4 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record092_frame004_indices record092_frame004_graph record092_frame004_links
def record092_frame005_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x14ba94522a3144a874f49c537a644b294d272474848ed1ca33322638c5986306604ba16b2d2578a994d2905049e1352664b4941252444748d118216408800f51d43906f8d81a6330650c417e2f45e0bb1702dc5a8b31642c4470890da1a0330650c617c2f05b0b21542a0530a40dc1903005e0b41482804a08c0f81e03a0700d81a0300500981001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record092_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record092) (record092.maps 5) (record092.inverseMaps 5) record092_frame005_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record092) (record092.maps 5) (record092.inverseMaps 5) record092_frame005_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record092) (record092.maps 5)
      (record092.inverseMaps 5) record092_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame005_links_0000 record092_frame005_links_0064)
theorem record092_frame005_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 5 :=
  of_group record092 5 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record092_frame005_indices record092_frame005_graph record092_frame005_links
def record092_frame006_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0495.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0495.count (({ width := 9, code := 0x1daeb74395c6e16fb75b6d86ab4da2ce653218cc2582bd5cac55aa950a75329146a14f27130964a2411c8c45225108743215088341200fa7c3b9d8e66f3398cc25e2c158a44e2592482401d8e870371b0d06632188bc5c2d1609044200f878381b0d0642e160a85026120883c1c0d060281208038180a04018080200 } : Fields).get c.val)
theorem record092_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record092) (record092.maps 6) (record092.inverseMaps 6) record092_frame006_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record092) (record092.maps 6) (record092.inverseMaps 6) record092_frame006_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (smallEmbedding record092) (record092.maps 6)
      (record092.inverseMaps 6) record092_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame006_links_0000 record092_frame006_links_0064)
theorem record092_frame006_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 6 :=
  of_group record092 6 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0495
    Papers.RationalityTen.SharedFrameCatalogue.group0495_facts record092_frame006_indices record092_frame006_graph record092_frame006_links
def record092_frame007_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0473.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0473.count (({ width := 8, code := 0x9f9e9c9b9a9998979694939291908f8e8d8c7f7e7d7b7a797776757372706d6b686664615f5d5b5a59585756555453514e4d494845423f3d3c3b3938363534333231302f2e2d2c2b2a2928272625241f1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record092_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0473.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (smallEmbedding record092) (record092.maps 7) (record092.inverseMaps 7) record092_frame007_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (smallEmbedding record092) (record092.maps 7) (record092.inverseMaps 7) record092_frame007_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (smallEmbedding record092) (record092.maps 7)
      (record092.inverseMaps 7) record092_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame007_links_0000 record092_frame007_links_0064)
theorem record092_frame007_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 7 :=
  of_group record092 7 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0473
    Papers.RationalityTen.SharedFrameCatalogue.group0473_facts record092_frame007_indices record092_frame007_graph record092_frame007_links
def record092_frame008_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0474.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0474.count (({ width := 8, code := 0xadacaba9a8a7a5a4a3a19f9d9a9794918f8c807e7c7b7a7978777675726f6c6b676663605f5e5c5b5a595857565452504e4d4b4a4847444241403e3d3b3a383631302d2c2b2a2928272625242322211f1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record092_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0474.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0474.localPairCheck (smallEmbedding record092) (record092.maps 8) (record092.inverseMaps 8) record092_frame008_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0474.localPairCheck (smallEmbedding record092) (record092.maps 8) (record092.inverseMaps 8) record092_frame008_indices (Fin.ofNat record092.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record092_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0474.localPairCheck (smallEmbedding record092) (record092.maps 8)
      (record092.inverseMaps 8) record092_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record092_frame008_links_0000 record092_frame008_links_0064)
theorem record092_frame008_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 8 :=
  of_group record092 8 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0474
    Papers.RationalityTen.SharedFrameCatalogue.group0474_facts record092_frame008_indices record092_frame008_graph record092_frame008_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (Fin.cases (record092_frame002_supported hcells) (Fin.cases (record092_frame003_supported hcells) (Fin.cases (record092_frame004_supported hcells) (Fin.cases (record092_frame005_supported hcells) (Fin.cases (record092_frame006_supported hcells) (Fin.cases (record092_frame007_supported hcells) (Fin.cases (record092_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30c525e909473a30115a89a43221090607fb3f49ed4f4a79337e8fec7aa3b31c60de46cc3301870bf058e2b514089c44be253126091447020d0f607943ba1d70e807203821bb0d986b434c1910c505cc2d81650af85602a414a0a204f425012108c844c1aa09304001f80e006102e016c0b405802b81580aa04802300e0052024011808804001f00f007403601a00c005002200f007003401600a004802000a0040018008002000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc8a51924b11fc8ea46a22a910e87142320d103e7dc3e31ebce3270d3839bc0c785fc2cb15e8aca54229b14a0a2a4d226212b894449422f914088038c1b60d886523171818bc45c62d01610ae050226f12388d044420e0f587383721970c305d82a010e080032413209703d01c00b805b02d015c0ac05502100fc07c03c01c00bc05a024011808804201f00f0074028010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (smallEmbedding record096) (small_cells_exact record096 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x52fa8d5448a104fda7ad3b09b545e21d50a28304061fecfd27b33d19e44a56501278137098e4b7252120471034118e8bf05b02c715a89fc4de25d129893048a238107081c4021f90f987b03ae1d00e086cc34c1970c886282f61520a204f426c128090844421410307e03dc1e00d403d01ac0d4069034019c0ca06102b81580aa04201980c806203001780b405201f00f007403601a00c005002000f0070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
def record097_frame002_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x52fa8d1442a0e4fea7c93dc9d447e22bd11887142420d103e7da3e21eb4cc063e3179878c1a6012fe17a4a8050727493489604a224a117489c43e21790808304001d60e6871837a1b60d886523171798b4857029314089bc4901e00e186e43561860bb053c28013008f84442020c803d01ac0d4069034019c0ca06102b81580aa04201980c806203001780b405201f00f007403601a00c005002000f0070034014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record097_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record097_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record097) (record097.maps 2)
      (record097.inverseMaps 2) record097_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record097_frame002_links_0000 record097_frame002_links_0064)
theorem record097_frame002_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 2 :=
  of_group record097 2 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record097_frame002_indices record097_frame002_graph record097_frame002_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (Fin.cases (record097_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
def record098_frame001_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1560a8853c299928891c48623e9178899449222ced27593a49c98d66690339192cc7262830a1810be85d12af14eca3a4f6272134c98c4bf25892588ea46f2348c645de2da1638ad854c29914389e84d623c11688383a61c30db069032e1880ac85282560f007483881b60d403801ac0d406903081700b605a01f80f807803801980c806203001780b4052024011808802800f007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record098_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record098_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 1)
      (record098.inverseMaps 1) record098_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record098_frame001_links_0000 record098_frame001_links_0064)
theorem record098_frame001_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 1 :=
  of_group record098 1 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record098_frame001_indices record098_frame001_graph record098_frame001_links
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (Fin.cases (record098_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001
