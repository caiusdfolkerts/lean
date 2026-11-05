module
prelude
public import GraphInputsRow27Part00012Data
public import RawFrameSupport
public import SharedFrameGroups004Checked
public import SharedFrameGroups006Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012
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
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6982da162ca8a52da72530091f47221950a883240e2030f687a63ca98d0bc455629392548983eb1d80cc46402fe1740b60500272130891c47e23911488884001f90e106e83641a40cb864430616d0b3854029414409e04d424211308583f81ec0f007403880f807103581840b605502a0110072033014808c03a01c00c806002c01500a003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x80ef3ddeb9871eda9acb41658c0d802f95e4bad682cb58ea3d3da5849c8a50b1ff3d6710e09ba3666b4c998f3165fcbc9752d85a0a81492484748c9122144187e0e61c4350690d11943205d0ae14a2684a89111a224340600b6150278490900f01a02f05008c0e81c0320600b01502803c0700c0140200380500600800800 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc7f60eac555149804aba4811cc86642a2070ff47c53d31e54e966e92f095588984231f60ec86643201740b18522272130891c47e23211508884281ff0fc87cc3d61c90dc86c83301900c185b42ce1510a504d424211208603f81ec0ef07483880e206c03181800b605502a00e406802b014008c03a01c00c806002c015009804001c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x412816f9ded39b724e21b9b4567cc8d8aafd5daba16d2d0546a4d30a5a4a691512a1f4127f8f49de3b4714de9b535a69ccf18f316620c016b2ae5389912d23a420810f01d4364650be1722b85389f130240318610b21582884b0940dc1982b05008c0e81c0320600b0150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x53da513c66647a8df17e22c1882aff1f93d978ef01d439d6b4cd171ad5590add452824d696d22237464859061fd3e27a8ed9c637c6e0d618b2f45c8ac14f27a4848d10a2083cc718d61a23105f8b91682b4350660ba1682a84f09c0e01a02b05008c0e81c0320600b0150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x63fac5553ca8a51327253249804ada47d1c88af42a207101a7c83d31e54e965e12b515589e449522f113084e3eb1d80dec6402e816c8a504e426112388fc46422a11108504001f90ea87243721b20cc064030617c0ba05b42ce1500a50510278135097849c24211308583f81ec0e203e01c40b605802a8150088039011808003a01c00c806002c015009803c01c00c005802000e0050018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc7f5e52e7d6d0b2d545298149ca254e4a64930095b44d21810a88324109ff4f907a63ca1d2cd2c66b31a17e4aac52c28d13c492a45e226109c6cc32c1900bf85da2c914a09c84c024711f88c845422210a07e43d61e40eb07403921c20d9069033a18f0c185f02ea16d0b3054029414409e04d425e127090844c1ec0e8071036c0ea05b02d01600a803d011808804001c00c806002c015009803801a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb2e5652afd530a7850827bd3c09bf4bd255129a940442a1090688114001f74f5677e3b61cfcd9a6c134c99d0c185ed2ef9700b0255c2aa152896447d23991648964312048fa07b83ab1cf0e0c6ec36d1b08c505ec2e71648afc56229d13b09784a0238112084c4021f30f306cc34e19c0c786102f216c0b205102100ea07003580ea05b02d01600a803d011808804001c00c806002c015009803801a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6ba2e796d0a9c52727252f691f474a2650c08544192084f907b43ca19a8c6856828d125488e3eb1da8d9465832017f0bb4528280130091c47e21510007a83c81d70e787243841b20d2067430617c0b3054029414409e04d425e11308584141ec0e8071036c108075035817c0b405802a013007a033013808804001c00c806002c015009003c01a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2d4d600a9e530a93138e98048ea39515a8454081fb0f967aa3c8187cb9856a296946092644c1f48ec46f231116e0ae052e27612e091c47e22210007a83c81d70e486e435a1a50cc062830617c0ba05b829414409a84bc25012108984141dc0e006c834c0e807103481980c605c02d00f007203101700ac04802200c806002c015007803401800b004802000e005002000c004001 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
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
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xbc95b428953929924ab243913286042a20c8ffa7d63e41e50d2a63427892548bc4221ed0d9465832017f0b24544294130091c47e22a11187e03ca1d60e787243841b20d2063c2f81750b3054029414409e04bc24e11908984141ec0e8071036c104075036817c0b405802a012807a035013808804001c00c806002c013009004401a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
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
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x3976f2d8db03556a2ce199b1d61ec0d79ada59aaf15ba854c492d2423c47086d0b2003e67a0ec1c136a698d11802e05a8ab14f2964d89911e234460860fb1ee3c8768ea1b4358670c91842f45b8b014a258490700cc1842d85009c128248480780d8178240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x4af9091ae32c4e8930a611bfe7d6f8de83b0748e49c5b50638bf17aad95acaad5227b4c897924a2b44083d049e83b6750dc1b035262cc316f2d458ca89432744d49712521a4207b8ed1cc3806c0d11862c85607c0e21a83205a0b0150298520820dc180240440780e81c0320600a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0328.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0328.count (({ width := 8, code := 0xb3b1aeadabaaa8a7a4a2a1a09d9c9b9a969491908e8d8b8a87858483807f7e7d74706f6a686762605d5c5b5653514f4d4b474643403e3c3a383532302c29272624232221201d1b1a181716151411100d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0328
    Papers.RationalityTen.SharedFrameCatalogue.group0328_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0242.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0242.count (({ width := 9, code := 0xcc6431588c260afd7cbb5cae16eb459ac962aa5328d44a04fa7538994ba592a9248a411e7e3c9dce26e3619cca612f974b055299449e4d2411886401f0f074381a8c8602c1489c4c241188842200e86c34180b8582a14088401a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0242
    Papers.RationalityTen.SharedFrameCatalogue.group0242_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
def record021_frame005_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0x173b4d92c55faed66af52a6d2a91419fcf679329448e431e8e4622d11864260f007f3f1f6e76f36da0cc63af572ac542953a9649a411c8b3f9f0ec73381b0d2673095caa4a220f878381b0d066321609848200f070361a0b858261208038180a0401c0c04018080200 } : Fields).get c.val)
theorem record021_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record021) (record021.maps 5) (record021.inverseMaps 5) record021_frame005_indices (Fin.ofNat record021.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record021_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record021) (record021.maps 5)
      (record021.inverseMaps 5) record021_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record021_frame005_links_0000 record021_frame005_links_0064)
theorem record021_frame005_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 5 :=
  of_group record021 5 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record021_frame005_indices record021_frame005_graph record021_frame005_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (Fin.cases (record021_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
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
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x1aed6eaf55a7d2e8f459ecee571f89c2606ed73b8d8abd5aacd5e994aa3d1687409d4e2672f94c92411d87c3a14fa7b3c9e0ef73389bcdd6cb61a8be582b938994923d1680389b8c25a2b954a44d2591c8a3d188a04c230f87032160983c1a090400c0200 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x68967e6506466075c15b556f52951f5104ce4b547e46d46a45344c43242a4143ff3b93ad35e32130f3082bc2ad27626a25c24e23e22a21720c1f31e21d91d21bc1a818517717016715f15212811e1171040fc0dd0d90d40ca0c20bd0b80a609808c06c06405c05b05805204e03a03202a02802601f01c01501100e009007006002001000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
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
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xa8b44e67c5886cfa5da36e66ac9985af65dab8169ad052ea0d3d2744b29511e22942c820fb9f436e6c4c918c2f25c8aa14e27a4c89291c1e63b4710dc19c314588ac1441fc3405a0aa1402704b092120228390660c8138250460800d8120220300480700c00800800 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x233c628a71321fc3880af95ed3d1786ef9d73a2720e1dbd3666aad1597b25642c49872fd5daba16f2d659aafd5ca9550e9ed34a604a68e11722843a84d019f13be758e31c136a698ce9983045e4b79642b050c9993023c4648a1072063dc770e71b4348608b515e2784c09211a1b4358530a41381c03604c0840f81101c0340600901001800800 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a3ed09644b1bd860c0e594ab0d520a7053029714249e24daa6092b892f46ba28109482140a9fb4fc27be3c09dbce7470036c9b20d826533071784b6c5872b1145c9f44e826792f4926453215905c7d63df1d18dec6d236218a8c045d02d415f89e04ba25211b88c44441f20f286e833e1910be05b827c12308b83a01be0d506401f40f405e02e8164074037013008403e01100700340180090040018002000 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x347da12c89637b0c181cac552e28493c49b5470a2a902a7e13df1e04ede73737c1b44d8c6c13439988cb26533071784b6c57b2ab14eca204f0274131497a49324011948a643d215905c7d63df1b40d8862a3031740b5857e27812e894846e23111107c83ca19d0c885e82dc141091845c1d00df06a83200bc059028013408a04201d00dc05c026012808403e01100700340180090040018002000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x14ba95d0fa153ee7948c8d315a23c3a7a2ee9bfb6a6b6d159fb2a62ec39843065eeba572ae059cb095ba9e51a9ed372634c29512923f4728c51422043084d042053886f8d019831c618bf1622a8544a194027649c921031f83a8718cc1862f4540a314026c2e05709c12c228420740dc1702604a0840f81101c0340600901001800800 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x2e05b7ac54aa684717b8e75b835b6a4cd18fb1360ec11772df5aeb355b2a452a9fd2d24e47487d0c213418808f51da3ae6c0c61772dc598b215527e4f49591d2284147a8e81a2320618b21582a45208e0da1702b84f09a1142103a06e0b0130250460840f0130220340600a01001800800 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x2a2d1fa232ee34c56856f79e13b572ee0db7b676a6cd593b0b5eebb5702d35a0b295529b5189e93a26d4ce9812b25546a885049fc3e2798ec1ca376694c21732b2550a714b2884e89992a242450848fd1da38c6e8d619a3105e8b015629c4a85f09c1142003906c0cc1902f0540941182102c0300480800c01001802 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x7026cf69966e64861b6155f05de5bb5b55595245075014cc4b34a74a348c46b44b43b4264203fc3e93e13cc3c53ab3a537e33132631d2de2d82cd2a029c27525a24423921b20e2031f31e41e21c51b61ac19c19218618317c16e1370fe0e70d40c40ae0a50a107506c05a05404503b02602402101e00f009004003001000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x6a73475a1ed01677b37597ecac651321186eb3658ea921454a174db26652ca94248223d11bc8a243fa17105c8193b39d48e787273809b94d966b434c99f0cc265d31b9898bee5b32c295a4acc53d29793e09b44d2265927091c3ad1c40da069632f18e8b905862a214389d44b223811308543b81bf0d7862c2f614f0a204d024a11008083c41c80d204902440f607102a811c08a02e016007c03c011008003000a000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
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
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xa794da9450ba132ee54c988c114215c1e7d0f79e13b072ee0db53676a6d2192b21606bd576ae05a6b05602bb558a7547a854f49d136a5c4a49451aa0b3f87c4f59da39a6f4d99a52ea564aa14e2804e49812a242464848fd1e43846d8d619a3185e8b015a29c4f89b12a2183485c0b61141c8330640941180c01201802003 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
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
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78d73e72c6bf6af6a469968567d6075f45e95d95ce5ba57c55554e53b5344e04a643842841c3e43dc36735734731a30c2e02c32bf2ac28924723422921c2112051c31b91b01a118517817416616113e13512b12110c0f80f40e80df0ce0cb0bd0b80a709d07506f06405f03703503302702602301301200c00a008006003002 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x53f931005cab7166ec8182ae15acb2160aae52ea51392654b4941272394628b504a033d078cec1bf340648c31782aa53ca393d2624a48f11c20a3fc7c8ed1c2358668c71782e0540a51302383685d08e1141e83706a0d01982c04e098128230260480600a01001801802 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
def record064_frame002_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0761.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0761.count (({ width := 8, code := 0x938b847d7974737271706f6e6d6c6b6a696867666564635f5d5958555352514e4b474645444342403f3c3b3a393837353331302c2b2a2926231d1c1b1a19181716151413120d0c080706040302 } : Fields).get c.val)
theorem record064_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0761.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record064_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (smallEmbedding record064) (record064.maps 2)
      (record064.inverseMaps 2) record064_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record064_frame002_links_0000 record064_frame002_links_0064)
theorem record064_frame002_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 2 :=
  of_group record064 2 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0761
    Papers.RationalityTen.SharedFrameCatalogue.group0761_facts record064_frame002_indices record064_frame002_graph record064_frame002_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (Fin.cases (record064_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x1e23bc772ea5ce38c6fada9b3b5e69cc6189b04600b916c2c9590b0d5e2ab5409d93826c4d29812ea19428798ee9d43a272ce51c537e698c91862fe5e4ba16a2cc578ad1402744c08f91921a418810fb1c636c698c617a2e85a0ac14427c4c88d1142083e06f0dc1542a0520720d81302003a0640b81302401801802 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x31b1834ba0589abc1590ab454c24311ee8af44c211103e7f83f41f5cf947b939c1b98cd85df2de1650b005641ec0f0c6f63641880bac5882b41518a5850a243116887c42e21010487f83f61f00f687683a61ca0e186e03601a00cc86383181860bf85e029814609b84a823c11708a84382040ff07a03c81d60e306c03580fe07d03a81bc0be05e02d81640aa04702280f406e027013008c04201d } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc1a5edac55590a8c537a941476a134e524d521e8ea46ba2a113a86642920fd03e7fa3f49b98d4e5e12ca1560a7651c283937c92c4011ed8ed87463741b48cc863c30b1758b1856a24311688404121fe0fd87c03da1e60ef87503a21ca0df06d43541a00cc864c3161860bf85c42d415a0aa053028c13e09b849424411d08784202020f407903a81be0d803f81f40f207303001640ac055023811408203b014008403c01d } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
def record070_frame002_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x4628b50ee1541982102201bf77cef1dddbaf754e75ccb87702dedb8b676c4c958c2f45c6b2d602b7562a894726b4b693122a354648810d214414800fd9d03846b8d219832e620c39802f45a8b49632a853ca494427e4e899930252460891001f23d0770e81c63686c0d518a2f45a0a91502884c8950e21bc368680b61542905108a10c1f8390500840f01d } : Fields).get c.val)
theorem record070_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record070_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record070) (record070.maps 2)
      (record070.inverseMaps 2) record070_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record070_frame002_links_0000 record070_frame002_links_0064)
theorem record070_frame002_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 2 :=
  of_group record070 2 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record070_frame002_indices record070_frame002_graph record070_frame002_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (Fin.cases (record070_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x160eb9d3fa232ae504988f5005f739571adc59b321616b81682c8582aa54f2945049992d25049c9292223b4628b5049fd3d078cec1b333e648c31722aa53ca013d26c4d49892923c470828ff1e63b4728d619a31c5e0b81502944c05d08e1101e83806a0d01982904e0981282302c0480600a01001801802 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
def record077_frame002_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0704.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0704.count (({ width := 9, code := 0x30982be5d2d568b357aad50a350a793094492311489442190a83409f4f67a3c9e0ee763a1ccde6c349a0ca602e970b255291449e4e26930964a2411c8843209007e3d1d8e46e36190c460291087c3c1d0d86832170b0542813070301007030100602 } : Fields).get c.val)
theorem record077_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0704.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (smallEmbedding record077) (record077.maps 2) (record077.inverseMaps 2) record077_frame002_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (smallEmbedding record077) (record077.maps 2) (record077.inverseMaps 2) record077_frame002_indices (Fin.ofNat record077.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record077_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (smallEmbedding record077) (record077.maps 2)
      (record077.inverseMaps 2) record077_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record077_frame002_links_0000 record077_frame002_links_0064)
theorem record077_frame002_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 2 :=
  of_group record077 2 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0704
    Papers.RationalityTen.SharedFrameCatalogue.group0704_facts record077_frame002_indices record077_frame002_graph record077_frame002_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (Fin.cases (record077_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
def record078_frame001_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7b47a779c77c77276474b7466c36b96b068a67963f62460f5df5c758e57156454652b52551a4c74bd4b34b24ab4a44864774704634504314244174073f43c73be3b73a338d37836535e34633b31d3173043022fc2f123d2321e11d019318617314d1350ff0ea0df0cb0c60c10a908c08b07d05404502101e01901000f00e00b009004003000 } : Fields).get c.val)
theorem record078_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record078_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record078) (record078.maps 1)
      (record078.inverseMaps 1) record078_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record078_frame001_links_0000 record078_frame001_links_0064)
theorem record078_frame001_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) : Supported record078 1 :=
  of_group record078 1 (smallEmbedding record078) (small_cells_exact record078 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record078_frame001_indices record078_frame001_graph record078_frame001_links
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (Fin.cases (record078_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8808307f77d17bd7b17547086a868e6145ea5d05ad5a859058c5745705104fc4f54a749a45d4374223da39f39236e35934f34233732f31b3143002fc2ab2902532382211ea1c61ba1b21ac19917c1761541301261091010f90f30e00db0c60c207a07806e05b05705604304204003903602602302101f01e01901401201000e00d00a009008004003001000 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
def record082_frame002_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0832.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0832.count (({ width := 9, code := 0x1add468f419dcde3b0776b7d7eb352a551e853f9d4de5b2892c662f0a823fdeaec75381b6d86a3419ac862b017ab3582a14aa04ba491e8d45a18fc7c3b9c8de673298cc25c2d154a643208fc74361a8bc5c2c150a444210f87438170a048200e0682812080200c0200 } : Fields).get c.val)
theorem record082_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record082_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (smallEmbedding record082) (record082.maps 2)
      (record082.inverseMaps 2) record082_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record082_frame002_links_0000 record082_frame002_links_0064)
theorem record082_frame002_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 2 :=
  of_group record082 2 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0832
    Papers.RationalityTen.SharedFrameCatalogue.group0832_facts record082_frame002_indices record082_frame002_graph record082_frame002_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (Fin.cases (record082_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
def record085_frame001_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a36ccd546292142691c47d234518289a431a0c10387fb3f49f6cf4a7932ac14509be3e81e30e7471a3661978bf05d02c715a8a9c4e225f10787fc3f41f30ef07403841ba0da069832218a0c085b02ca14409e84d425e12809084642180f607803540f607103301740b605a02b81580aa04301c80b804a023011007c03c01d00c8054022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record085_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record085_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record085) (record085.maps 1)
      (record085.inverseMaps 1) record085_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record085_frame001_links_0000 record085_frame001_links_0064)
theorem record085_frame001_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) : Supported record085 1 :=
  of_group record085 1 (smallEmbedding record085) (small_cells_exact record085 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record085_frame001_indices record085_frame001_graph record085_frame001_links
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (Fin.cases (record085_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9dd9ce9bd9ba9a899998b9749659458c68b48a789b88987986784e83a81f62d61f61060e6005f55e75d85cc5b24b64a749a49348547a46c45c44d43837035d34b3463363243112fe2ee2d22ca2ba2ac2a429628927826825824123c22c21c20c1f81e21d51c41b51a81981871780ab0a807f07806605f03d03602e027019012006005004003002 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
def record086_frame002_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0714.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0714.count (({ width := 9, code := 0x31386c05fef979bb5cee16ab1582bd5bacd5aa751a752e39198a44e210d8541e08ff6c359a6d26833998ca6431554a65027d36984aa451c894421502803e9ecf2763a1c4e06d3519cc8612f970b4592c158aa42208f076381b8a45022108502206028100602 } : Fields).get c.val)
theorem record086_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record086_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (smallEmbedding record086) (record086.maps 2)
      (record086.inverseMaps 2) record086_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record086_frame002_links_0000 record086_frame002_links_0064)
theorem record086_frame002_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 2 :=
  of_group record086 2 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0714
    Papers.RationalityTen.SharedFrameCatalogue.group0714_facts record086_frame002_indices record086_frame002_graph record086_frame002_links
def record086_frame003_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x2e35c1b6f6d6d85abb49676cb58ba4f47e8850ba053ee77ce69bb331cbb92710e19c0b7c6eadb9b3b5c524a293da764da9992d2514908dcee9d639671ce09b93626a8d1998326630c097d2ee5bcb39602b2538a59472864fc9d93525e4948f118224430838a613e1ec3a8640ba0f01b02e04e0640900600a01001802 } : Fields).get c.val)
theorem record086_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record086) (record086.maps 3) (record086.inverseMaps 3) record086_frame003_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record086) (record086.maps 3) (record086.inverseMaps 3) record086_frame003_indices (Fin.ofNat record086.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record086_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record086) (record086.maps 3)
      (record086.inverseMaps 3) record086_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record086_frame003_links_0000 record086_frame003_links_0064)
theorem record086_frame003_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 3 :=
  of_group record086 3 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record086_frame003_indices record086_frame003_graph record086_frame003_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (Fin.cases (record086_frame002_supported hcells) (Fin.cases (record086_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xadb56aab3158eac055caac9556aa454da6b53369824bca59d2ac943498247920a8fa474233d18c8b4451a2410fa86b42919f0cea66d3341984cb46533261914c7a57c2b79568aa854629c14a4a3650d27b93bc9c44cd26392e495649c24712008d43741b28d2068c3371930c5460a2f516b0b4c5882a71528a5850a274132095046a234116889843e21810687e83b01d40df86a832a1820b8853c29c14109b04a823c11108203e41da0e103f81e00ea06e033017c08e04001e80d805c027 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
def record087_frame002_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xb125802ba15b6ac7559aa81518a7b530a69932897c4b7a56d28e934490243d1ea8ef474237d1b48d3466231517c8b74571b1cd6e69e34a1a10cea66232798f0c465722b11524a7e52f29014349f44e726713209824b825992b494c49f24c12449103871b90d3c6923341900c305ec2e11608afc5602921480a044e0262129890c44c22510b88203f21ea0ee073435e1ad0cf06342fe1700b0050c284134092845820e0fa07983b01ca0de03f81e00ea06e033017c08e04001e80d805c027 } : Fields).get c.val)
theorem record087_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record087) (record087.maps 2)
      (record087.inverseMaps 2) record087_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame002_links_0000 record087_frame002_links_0064)
theorem record087_frame002_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 2 :=
  of_group record087 2 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record087_frame002_indices record087_frame002_graph record087_frame002_links
def record087_frame003_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x2418f6388de348c22c8a625882108320781a037fdfb7e1f47bded7a5e478de0771d8755d1731a66919e6759a65d926418d621765d16e5b56a59d625815d5615554d4d53149519414fd3c4dd254891a4651543d0b419013e8f93d8ee3b4e938cdf368d5338cd324c5304bd2e4b62b8ad2a4a327c9a2548e23489214811f4791d4711b46915c5514c51128480e8350cc2e09c22 } : Fields).get c.val)
theorem record087_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record087) (record087.maps 3)
      (record087.inverseMaps 3) record087_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame003_links_0000 record087_frame003_links_0064)
theorem record087_frame003_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 3 :=
  of_group record087 3 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record087_frame003_indices record087_frame003_graph record087_frame003_links
def record087_frame004_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0x15bacd5ead55aa5469f4da55027d3c9dcea73369a4ca5f2e964aa532893c9245208ec220f058240e04ff7f3f1f2ef773b1d6ea74b99cae370379badb6d365b0d56a3499ec5612f578b95b2cd5eab53a99469e4ea692e9448231108742208fe7c3c9d8e270369a8ce632f96cb4572a9489e4c2491c88411b8d86833178b85025120843c1b } : Fields).get c.val)
theorem record087_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record087) (record087.maps 4)
      (record087.inverseMaps 4) record087_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame004_links_0000 record087_frame004_links_0064)
theorem record087_frame004_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 4 :=
  of_group record087 4 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record087_frame004_indices record087_frame004_graph record087_frame004_links
def record087_frame005_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xac855a2a61518a775312941476a27505a52526a919487a3f51d48d746222c112a88b43ca17d0aa845419a0890207fe3f21650b005642ac150ca5c51c28393cc9ae4152008f947b63c91db0e8c72037c1b08d5c68a32b1908c445fe2ee16e0b2856021010487f83f61f40f687983be1d80e687283861b80da86b834e1a00cc864830e1860bf85e02e216a0b0856829e14c0a284f826e130094847823a11608784202020fa07983b01ca0de03f81e00ea06e033017c08e04001e80d805c027 } : Fields).get c.val)
theorem record087_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record087) (record087.maps 5) (record087.inverseMaps 5) record087_frame005_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record087) (record087.maps 5) (record087.inverseMaps 5) record087_frame005_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record087) (record087.maps 5)
      (record087.inverseMaps 5) record087_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame005_links_0000 record087_frame005_links_0064)
theorem record087_frame005_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 5 :=
  of_group record087 5 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record087_frame005_indices record087_frame005_graph record087_frame005_links
def record087_frame006_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x5c5b816e2da5afb5568ece595b1b49e8fd10a1740a7dcef9cd376664c797f2c2554a093323241c798cee59c8b8970ae01bdb746dad99af2f85e0b856dad1594af55a2aa530a494527b4ec9b53325a4a29211b9de3ae728e41c23746c8d59a432e650c69802fc5e0b81682c2568a694c290510a013c26c4c09412623e4648990d2103fc7f0f61de39c6f0d719e320600b70f61d43906c0c81742283f0780d817027 } : Fields).get c.val)
theorem record087_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record087) (record087.maps 6) (record087.inverseMaps 6) record087_frame006_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record087) (record087.maps 6) (record087.inverseMaps 6) record087_frame006_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record087) (record087.maps 6)
      (record087.inverseMaps 6) record087_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame006_links_0000 record087_frame006_links_0064)
theorem record087_frame006_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 6 :=
  of_group record087 6 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record087_frame006_indices record087_frame006_graph record087_frame006_links
def record087_frame007_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1093.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1093.count (({ width := 8, code := 0xb5b4b2b1b0afaeadacabaaa9a7a6a5a4a3a2a1a09f9e9c9b9a9998979695949391908f8e8d8c8b8a8988868584838281807f7e7d7b7a79787776757473716e6d6b6967656361605e5b5a58565452504e4d4b49474543413e3d3b3937353331302e2c2a28262422201e1c1b1a191817161514131211 } : Fields).get c.val)
theorem record087_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record087) (record087.maps 7) (record087.inverseMaps 7) record087_frame007_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record087) (record087.maps 7) (record087.inverseMaps 7) record087_frame007_indices (Fin.ofNat record087.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record087_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record087) (record087.maps 7)
      (record087.inverseMaps 7) record087_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record087_frame007_links_0000 record087_frame007_links_0064)
theorem record087_frame007_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 7 :=
  of_group record087 7 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1093
    Papers.RationalityTen.SharedFrameCatalogue.group1093_facts record087_frame007_indices record087_frame007_graph record087_frame007_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (Fin.cases (record087_frame002_supported hcells) (Fin.cases (record087_frame003_supported hcells) (Fin.cases (record087_frame004_supported hcells) (Fin.cases (record087_frame005_supported hcells) (Fin.cases (record087_frame006_supported hcells) (Fin.cases (record087_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6bf6ba6af69e69366666362761f5f25d95c25a558b57f54e53a51d4fe4ec4e049048a47847547346143942541b4073c63b339237e37136431b3102ed2e72dd2c02bb2b726e26124c2051f81ef1c61ab1a518f18917916815412e11b10d0ff0f90e20d80c40a908707c06f06105505405204104003402501f01c01300d00a007004001000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0585.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0585.count (({ width := 8, code := 0xc4c2c1beb8b7b5b0afa9a7a39f9a9491908d8c87807f7b7a7877757372706f6c6a676661605f5e5c5b585352504f4d4b48473d3b383634312f2b2a262421201e1d1c1b1a19171513110c0b0605020100 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0585
    Papers.RationalityTen.SharedFrameCatalogue.group0585_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1032.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1032.count (({ width := 9, code := 0x3017ebd5e2ed75b9dbed364add62ad54a95469145994b63d1b8943e1b09843fdf8f8783b9cce36f36db0cf65b1988c05ead96ab057a91449d4ca591a8c42a11007b3b1d4d06530978ae552812c92431d8d4622e160ac502712888381a0b844200b038080200 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1032
    Papers.RationalityTen.SharedFrameCatalogue.group1032_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
def record093_frame002_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x2825009db3aa714df9a52ca50c958f317a2bc4e8970fe15421770e99b736266ec6187ae85cab4566ac8514a01352654b894122a2d442845051fc3e8798f11a934e628c297b2dc580a21422644b49111521a4246e8d619e3205e0b21542884c08c0ee1882b85309c12c228440820e41802904a06c0a00b00e00800800 } : Fields).get c.val)
theorem record093_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record093_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record093) (record093.maps 2)
      (record093.inverseMaps 2) record093_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record093_frame002_links_0000 record093_frame002_links_0064)
theorem record093_frame002_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 2 :=
  of_group record093 2 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record093_frame002_indices record093_frame002_graph record093_frame002_links
def record093_frame003_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0582.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0582.count (({ width := 7, code := 0x31e2c382fdebb72ddab362bd6ab529d2a3427ce9b325ca93223c5890e0c07ef9ebc76e9cb86ed9ab466c98b05eb962b54a54274c952234280f9e3a70d9a3260b962a50992224070d18244060808080 } : Fields).get c.val)
theorem record093_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record093_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record093) (record093.maps 3)
      (record093.inverseMaps 3) record093_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record093_frame003_links_0000 record093_frame003_links_0064)
theorem record093_frame003_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 3 :=
  of_group record093 3 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0582
    Papers.RationalityTen.SharedFrameCatalogue.group0582_facts record093_frame003_indices record093_frame003_graph record093_frame003_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (Fin.cases (record093_frame002_supported hcells) (Fin.cases (record093_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7ce7cd7cb7c27bb7b47a979f78d78677c77476774474173d6dc6c765063a6245a558957153e53a53552b5254cf4b54274163fe36835d33d31330e3052ff2f92b529525123822d2162091cd1c91b01aa18617716a13d1321201130ea0e30d60c60c10ba0b508d08c07b07a07106105404003f03702801d01000f00b004000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x59a2cb964eb0657dabc15ccadb5682a89530a8d54129e14daa4d51d288529a9464a023b91ba8c945ba29912483441120450007ee3ee9f08f5a7943a29cfce727173859bf4de06e436b1a94d3268c34019d0cce6473191874aa854f2a514109ec4e926c932c97c473233116489643e218906c8163f91db8eac73e38f1c18ddc6da3671b08d406743241898c105ea2e616b8b2056229d14509d84d625e128091447022210887fc34e19b0c786102f016c0b2055828613009204602100fa07503801ac0c800c005c02c01500a004c022010007803001600a0018008002000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame001_links_0000 (interval_append _ 64 128 136 record095_frame001_links_0064 record095_frame001_links_0128))
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
def record095_frame002_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5ef2f3d780ba85ccae29708b7d5bb2d01652b155822bdd5caaa454baa1534098e4bea4ed25291848624151fc8a344621d90c485242120890248023db9e8cf1c76b3ab9d08e6e7303951bdcdca6d23609ac8d446603289904ae85652ac147ca2050327c93d09de4a724a92108ea46922f111887442f1fb0f8879e3be1d70e7871837c1b68d7869c33e1960c7061a30417e8bd85c42ce15c8a84516277133096449622c10f884436c1a30c886082ec16b0b0054428a13a097849823410907c03a41ba0d300c005c02c01500a004c022010007803001600a0018008002000 } : Fields).get c.val)
theorem record095_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record095) (record095.maps 2)
      (record095.inverseMaps 2) record095_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame002_links_0000 (interval_append _ 64 128 136 record095_frame002_links_0064 record095_frame002_links_0128))
theorem record095_frame002_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 2 :=
  of_group record095 2 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record095_frame002_indices record095_frame002_graph record095_frame002_links
def record095_frame003_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x7d4f99f1bde7b4f5deabd179cf19e03ba76cec1d539c72ce41a9b50698cdd9a330656ca19231561ac117eaf55d8b816c2cf562ab95529f538a614a29151aa0d3da734dc9992f24f48e8fcfc9f63e6768eb9d43a0734e51ba3646a8d199b326624c09792d058caf9572a4538a39442844f89c93525c4ac949262464849011a22e444861072023f07b8ef1d4394668ca18a3005e8b81682c4570a914a28c4f89812423c4588703005c0b01502804c0881001e0300580a00600800800 } : Fields).get c.val)
theorem record095_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record095) (record095.maps 3) (record095.inverseMaps 3) record095_frame003_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record095) (record095.maps 3) (record095.inverseMaps 3) record095_frame003_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record095) (record095.maps 3) (record095.inverseMaps 3) record095_frame003_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (smallEmbedding record095) (record095.maps 3)
      (record095.inverseMaps 3) record095_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame003_links_0000 (interval_append _ 64 128 136 record095_frame003_links_0064 record095_frame003_links_0128))
theorem record095_frame003_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 3 :=
  of_group record095 3 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record095_frame003_indices record095_frame003_graph record095_frame003_links
def record095_frame004_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x627b0f5856c0c5ffafcd7c8bd55e1ada96bab515a12ccd642adb56aab393da9d84dfa5e12cc9554a124bd23a8c5459a28911e87c435213108a83e4019fc4fbc7bd3d79e80f207803b69c4ce0a6f63731b58d8667c33a99bcb6659f2c5954ca8a5372941468a184c625c12a893648d23f91988c245c216905c8063ed1ea8f0074e3931be0db46be34f19e8cb863a30c17e0bb05982be1570a7051a27c135896c496231115088c3961b60d086342f61690ab851c27613009284602140fe07983a01b60d200c005c02c01500a004c022010007803001600a0018008002000 } : Fields).get c.val)
theorem record095_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 4) (record095.inverseMaps 4) record095_frame004_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 4) (record095.inverseMaps 4) record095_frame004_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 4) (record095.inverseMaps 4) record095_frame004_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 4)
      (record095.inverseMaps 4) record095_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame004_links_0000 (interval_append _ 64 128 136 record095_frame004_links_0064 record095_frame004_links_0128))
theorem record095_frame004_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 4 :=
  of_group record095 4 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record095_frame004_indices record095_frame004_graph record095_frame004_links
def record095_frame005_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xdff7cde777dd371dbb6bd9f5ad5f54d474ed2b3cce735c570fc2af6bc2ebb9ae2b7ac5afebaad6b1ab6a3a7e9ba3e8aa167f9ea759c66d9aa5894e4e92a4690e338be2c83205801ee79de2779db761c36f1b76cdb06b5a668da0661976599363987601785c16b5995f56150521424f93a4c92d4991f45d0f42505404f83d0f0370d533ccc318c22f0b52bcab2949e26c952448b210810601705815050130441003c0c02c0a00c0200400 } : Fields).get c.val)
theorem record095_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record095) (record095.maps 5) (record095.inverseMaps 5) record095_frame005_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record095) (record095.maps 5) (record095.inverseMaps 5) record095_frame005_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record095) (record095.maps 5) (record095.inverseMaps 5) record095_frame005_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record095) (record095.maps 5)
      (record095.inverseMaps 5) record095_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame005_links_0000 (interval_append _ 64 128 136 record095_frame005_links_0064 record095_frame005_links_0128))
theorem record095_frame005_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 5 :=
  of_group record095 5 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record095_frame005_indices record095_frame005_graph record095_frame005_links
def record095_frame006_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1021.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1021.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1021.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1021.localPairCheck (smallEmbedding record095) (record095.maps 6) (record095.inverseMaps 6) record095_frame006_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1021.localPairCheck (smallEmbedding record095) (record095.maps 6) (record095.inverseMaps 6) record095_frame006_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1021.localPairCheck (smallEmbedding record095) (record095.maps 6) (record095.inverseMaps 6) record095_frame006_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1021.localPairCheck (smallEmbedding record095) (record095.maps 6)
      (record095.inverseMaps 6) record095_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame006_links_0000 (interval_append _ 64 128 136 record095_frame006_links_0064 record095_frame006_links_0128))
theorem record095_frame006_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 6 :=
  of_group record095 6 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1021
    Papers.RationalityTen.SharedFrameCatalogue.group1021_facts record095_frame006_indices record095_frame006_graph record095_frame006_links
def record095_frame007_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x77ddc761d3741cd72dc8715c3701bd6edb86d5b46c5ad68d9f66d926398a619825f9775cd6f5ad6758d615755954d5053547515414fd3d4e5364d1304b92c4a127491214551243d07411013f8fb3e0f13b8eb3a0e5388e0374da35cd5348d133ccc32cc8314c2300bd2e8b72d0b12b8ab2a8a8294a227c9c2649624c9223c8c220842007c1e0741c46e1a866188601785a158521404f0441003c0e0340c02809020070180500c0200400 } : Fields).get c.val)
theorem record095_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record095) (record095.maps 7) (record095.inverseMaps 7) record095_frame007_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record095) (record095.maps 7) (record095.inverseMaps 7) record095_frame007_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record095) (record095.maps 7) (record095.inverseMaps 7) record095_frame007_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record095) (record095.maps 7)
      (record095.inverseMaps 7) record095_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame007_links_0000 (interval_append _ 64 128 136 record095_frame007_links_0064 record095_frame007_links_0128))
theorem record095_frame007_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 7 :=
  of_group record095 7 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record095_frame007_indices record095_frame007_graph record095_frame007_links
def record095_frame008_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9f79f29ee9e59de9d89d49cb9c499298b98498097796d93e93592c86e85f85181e80b7f87e27d17c177176275273d7297156ef6dd6ca69068b68567c67566e66a66365d62f62862061a61360a5d95d25c95215145064dc4ce4bf4ae4a04924544464384274174063e83da3c939538a37f37936d36035034333832d3203133032f32e52d72cb2bc2a02962862732652582472372262071f81e719f19018217216415514613612a11b10b0fe0f20e70da0ce0c00b401801701601501401301101000f00c00b00a003002001000 } : Fields).get c.val)
theorem record095_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record095) (record095.maps 8) (record095.inverseMaps 8) record095_frame008_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record095) (record095.maps 8) (record095.inverseMaps 8) record095_frame008_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record095) (record095.maps 8) (record095.inverseMaps 8) record095_frame008_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record095) (record095.maps 8)
      (record095.inverseMaps 8) record095_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame008_links_0000 (interval_append _ 64 128 136 record095_frame008_links_0064 record095_frame008_links_0128))
theorem record095_frame008_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 8 :=
  of_group record095 8 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record095_frame008_indices record095_frame008_graph record095_frame008_links
def record095_frame009_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0x9dd3b275ce69c73866f4dd9b3336654c798730a5ecaf95328e2fc5c8b10ce14c2383504e03bdb7a4f29e0bb9758e6dc93886d2d9db335f6b8d65ab3546a2d11a0b3c670cd999324644c756bad55a4ae1572a953ea6947a694be96927a4b4808bd1321d4007f0fc9f53e67b8f49e63c677cec1ce3866f0d99ac34a668c81892fc5d8b71672c0570a914527c4e4851041fc3e0798ea1ca3746a0ca1822e0568a51382504688503005c0b01502804c0881001e0300580a00600800800 } : Fields).get c.val)
theorem record095_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record095) (record095.maps 9) (record095.inverseMaps 9) record095_frame009_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record095) (record095.maps 9) (record095.inverseMaps 9) record095_frame009_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record095) (record095.maps 9) (record095.inverseMaps 9) record095_frame009_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record095) (record095.maps 9)
      (record095.inverseMaps 9) record095_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame009_links_0000 (interval_append _ 64 128 136 record095_frame009_links_0064 record095_frame009_links_0128))
theorem record095_frame009_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 9 :=
  of_group record095 9 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record095_frame009_indices record095_frame009_graph record095_frame009_links
def record095_frame010_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0580.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0580.count (({ width := 8, code := 0xe3e2e1dfdedddcdbdad9d8d6d4d3d1cdcccac0bfbebbbab9b8b7b6b5b4b3b1b0afacabaaa4a3a2a09f9e9d9c9b9a99979594928e8d8b81807f7c7b7a7978777675747271706d6c6b66656361605e5c5b5a59585654535251504f4e4d4b48464442403e3b393732312f2e2d2b2a2928262524232221201f1e131211100f0e0d0c0b0a090803020100 } : Fields).get c.val)
theorem record095_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0580.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0580.localPairCheck (smallEmbedding record095) (record095.maps 10) (record095.inverseMaps 10) record095_frame010_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0580.localPairCheck (smallEmbedding record095) (record095.maps 10) (record095.inverseMaps 10) record095_frame010_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0580.localPairCheck (smallEmbedding record095) (record095.maps 10) (record095.inverseMaps 10) record095_frame010_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0580.localPairCheck (smallEmbedding record095) (record095.maps 10)
      (record095.inverseMaps 10) record095_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame010_links_0000 (interval_append _ 64 128 136 record095_frame010_links_0064 record095_frame010_links_0128))
theorem record095_frame010_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 10 :=
  of_group record095 10 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0580
    Papers.RationalityTen.SharedFrameCatalogue.group0580_facts record095_frame010_indices record095_frame010_graph record095_frame010_links
def record095_frame011_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa9fa99a95a8aa86a81a76a6aa64a36a32a2da21a15a0f9d79c89c18fa8e68d689a88887886684d8397ec7d67c27ae79878375a74472d6e86e36e06d56d06cb6c26b46ab67f67b67766e66165962b61d61356d55f55251e5105034f34e34d549248447946b45b44c42d41f4113d93cd3c63bd3ae3a439538637936b35834d33f32f31d30a2f82e82c72b72ad29f2912842732632532322232131c31b41a719718617716b1561441341251151030f60e90dc0cd0bf01801701601501401301101000f00c00b00a003002001000 } : Fields).get c.val)
theorem record095_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record095) (record095.maps 11) (record095.inverseMaps 11) record095_frame011_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record095) (record095.maps 11) (record095.inverseMaps 11) record095_frame011_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record095) (record095.maps 11) (record095.inverseMaps 11) record095_frame011_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record095) (record095.maps 11)
      (record095.inverseMaps 11) record095_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame011_links_0000 (interval_append _ 64 128 136 record095_frame011_links_0064 record095_frame011_links_0128))
theorem record095_frame011_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 11 :=
  of_group record095 11 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record095_frame011_indices record095_frame011_graph record095_frame011_links
def record095_frame012_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xac5582afd56aa954aa854da954fa9d537a6b4c696520a3345257caa94d1fa39c698c51722941f827022013fa7e4f81e93c3738e65cb38e714e21c3384700dd1b7b6c6d4d9db0b5569ad1977aeb5d0b115eab455eaa55227a4e499d312594ac9191d22e412804ff1fa3ea7bcf59e83cc780ea1cb3886f8db9b135a69ccc98e30c5f8bd1722d8598b1957296500871062003f07a8f11d83986e0d219630c5c0ae14a2804d09103005c0b01502804c0881001e0300580a00600800800 } : Fields).get c.val)
theorem record095_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record095) (record095.maps 12) (record095.inverseMaps 12) record095_frame012_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record095) (record095.maps 12) (record095.inverseMaps 12) record095_frame012_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record095) (record095.maps 12) (record095.inverseMaps 12) record095_frame012_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record095) (record095.maps 12)
      (record095.inverseMaps 12) record095_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame012_links_0000 (interval_append _ 64 128 136 record095_frame012_links_0064 record095_frame012_links_0128))
theorem record095_frame012_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 12 :=
  of_group record095 12 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record095_frame012_indices record095_frame012_graph record095_frame012_links
def record095_frame013_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x9632be574a493d2724bc95927212414808fb1e639c638bd172023fd7ecf65e83c877eee5d9b8d70edf9bcb716d2d71aa34c664cbd96b2463cc6d8b314622bfd7e2fa5ecbcd76add5aeb4d45a875069b533a624b895d29a374648ad13a214388510820c3ee7b8f41e03ae740e49c13766d4d59a533c664c918c30e604bb96e2ce580ad15529e520a213b2664b0859011f43c8740e11b8354668c71882f85b8af1522905089b03005c0b01502804c0881001e0300580a00600800800 } : Fields).get c.val)
theorem record095_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record095) (record095.maps 13) (record095.inverseMaps 13) record095_frame013_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record095) (record095.maps 13) (record095.inverseMaps 13) record095_frame013_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record095) (record095.maps 13) (record095.inverseMaps 13) record095_frame013_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record095) (record095.maps 13)
      (record095.inverseMaps 13) record095_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame013_links_0000 (interval_append _ 64 128 136 record095_frame013_links_0064 record095_frame013_links_0128))
theorem record095_frame013_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 13 :=
  of_group record095 13 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record095_frame013_indices record095_frame013_graph record095_frame013_links
def record095_frame014_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0834.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0834.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0834.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0834.localPairCheck (smallEmbedding record095) (record095.maps 14) (record095.inverseMaps 14) record095_frame014_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0834.localPairCheck (smallEmbedding record095) (record095.maps 14) (record095.inverseMaps 14) record095_frame014_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0834.localPairCheck (smallEmbedding record095) (record095.maps 14) (record095.inverseMaps 14) record095_frame014_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0834.localPairCheck (smallEmbedding record095) (record095.maps 14)
      (record095.inverseMaps 14) record095_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame014_links_0000 (interval_append _ 64 128 136 record095_frame014_links_0064 record095_frame014_links_0128))
theorem record095_frame014_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 14 :=
  of_group record095 14 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0834
    Papers.RationalityTen.SharedFrameCatalogue.group0834_facts record095_frame014_indices record095_frame014_graph record095_frame014_links
def record095_frame015_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xdc770dbf6edb76cda765d8753d4b51d3f4cd273dceb37c1f02bf6ecb9ee2b6ad1b22aeaaaa6a869aa4e859fa779b26b9aa699a2679966297e5394a5193e4c9263d8ea3782605805f47c1ec79ddd74dba6d9b26b5a667d91629835dd765d5715b5695915f5695755151535495153f4dd2f49121479194551143507404f53c0eb348ce328c62f8b62c0a82849a2548f220831f8791c86d0601705815050130441003c0c02c0a00c0200400 } : Fields).get c.val)
theorem record095_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record095) (record095.maps 15) (record095.inverseMaps 15) record095_frame015_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record095) (record095.maps 15) (record095.inverseMaps 15) record095_frame015_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record095) (record095.maps 15) (record095.inverseMaps 15) record095_frame015_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record095) (record095.maps 15)
      (record095.inverseMaps 15) record095_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame015_links_0000 (interval_append _ 64 128 136 record095_frame015_links_0064 record095_frame015_links_0128))
theorem record095_frame015_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 15 :=
  of_group record095 15 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record095_frame015_indices record095_frame015_graph record095_frame015_links
def record095_frame016_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0xcd6673197cb6572993c9647218fc7637198ac461aeb74b9d9ec75fadd5ea745a14fe79399b4c25b2a9248e45219047e3d1d8e46e35198c45e2d1488c39ecf57a3a1c8e06e361a8c7623057cbb5c2c95caa50a813e9e4ea71369a4ca5d2a9348235148742204fc7d3e1e8f0763a1c8e06e361a8c05e2e168b0562a950a24e259208a43208fc7a3a0b8582a1409848200f0702c1409018080200 } : Fields).get c.val)
theorem record095_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record095) (record095.maps 16) (record095.inverseMaps 16) record095_frame016_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record095) (record095.maps 16) (record095.inverseMaps 16) record095_frame016_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record095) (record095.maps 16) (record095.inverseMaps 16) record095_frame016_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record095) (record095.maps 16)
      (record095.inverseMaps 16) record095_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame016_links_0000 (interval_append _ 64 128 136 record095_frame016_links_0064 record095_frame016_links_0128))
theorem record095_frame016_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 16 :=
  of_group record095 16 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record095_frame016_indices record095_frame016_graph record095_frame016_links
def record095_frame017_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0363.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0363.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0363.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0363.localPairCheck (smallEmbedding record095) (record095.maps 17) (record095.inverseMaps 17) record095_frame017_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0363.localPairCheck (smallEmbedding record095) (record095.maps 17) (record095.inverseMaps 17) record095_frame017_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0363.localPairCheck (smallEmbedding record095) (record095.maps 17) (record095.inverseMaps 17) record095_frame017_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0363.localPairCheck (smallEmbedding record095) (record095.maps 17)
      (record095.inverseMaps 17) record095_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame017_links_0000 (interval_append _ 64 128 136 record095_frame017_links_0064 record095_frame017_links_0128))
theorem record095_frame017_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 17 :=
  of_group record095 17 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0363
    Papers.RationalityTen.SharedFrameCatalogue.group0363_facts record095_frame017_indices record095_frame017_graph record095_frame017_links
def record095_frame018_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0420.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0420.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0420.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0420.localPairCheck (smallEmbedding record095) (record095.maps 18) (record095.inverseMaps 18) record095_frame018_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0420.localPairCheck (smallEmbedding record095) (record095.maps 18) (record095.inverseMaps 18) record095_frame018_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0420.localPairCheck (smallEmbedding record095) (record095.maps 18) (record095.inverseMaps 18) record095_frame018_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0420.localPairCheck (smallEmbedding record095) (record095.maps 18)
      (record095.inverseMaps 18) record095_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame018_links_0000 (interval_append _ 64 128 136 record095_frame018_links_0064 record095_frame018_links_0128))
theorem record095_frame018_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 18 :=
  of_group record095 18 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0420
    Papers.RationalityTen.SharedFrameCatalogue.group0420_facts record095_frame018_indices record095_frame018_graph record095_frame018_links
def record095_frame019_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0106.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0106.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0106.localPairCheck (smallEmbedding record095) (record095.maps 19) (record095.inverseMaps 19) record095_frame019_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0106.localPairCheck (smallEmbedding record095) (record095.maps 19) (record095.inverseMaps 19) record095_frame019_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0106.localPairCheck (smallEmbedding record095) (record095.maps 19) (record095.inverseMaps 19) record095_frame019_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0106.localPairCheck (smallEmbedding record095) (record095.maps 19)
      (record095.inverseMaps 19) record095_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame019_links_0000 (interval_append _ 64 128 136 record095_frame019_links_0064 record095_frame019_links_0128))
theorem record095_frame019_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 19 :=
  of_group record095 19 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0106
    Papers.RationalityTen.SharedFrameCatalogue.group0106_facts record095_frame019_indices record095_frame019_graph record095_frame019_links
def record095_frame020_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0105.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0105.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0105.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0105.localPairCheck (smallEmbedding record095) (record095.maps 20) (record095.inverseMaps 20) record095_frame020_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0105.localPairCheck (smallEmbedding record095) (record095.maps 20) (record095.inverseMaps 20) record095_frame020_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0105.localPairCheck (smallEmbedding record095) (record095.maps 20) (record095.inverseMaps 20) record095_frame020_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0105.localPairCheck (smallEmbedding record095) (record095.maps 20)
      (record095.inverseMaps 20) record095_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame020_links_0000 (interval_append _ 64 128 136 record095_frame020_links_0064 record095_frame020_links_0128))
theorem record095_frame020_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 20 :=
  of_group record095 20 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0105
    Papers.RationalityTen.SharedFrameCatalogue.group0105_facts record095_frame020_indices record095_frame020_graph record095_frame020_links
def record095_frame021_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0104.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0104.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0104.localPairCheck (smallEmbedding record095) (record095.maps 21) (record095.inverseMaps 21) record095_frame021_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0104.localPairCheck (smallEmbedding record095) (record095.maps 21) (record095.inverseMaps 21) record095_frame021_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0104.localPairCheck (smallEmbedding record095) (record095.maps 21) (record095.inverseMaps 21) record095_frame021_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0104.localPairCheck (smallEmbedding record095) (record095.maps 21)
      (record095.inverseMaps 21) record095_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame021_links_0000 (interval_append _ 64 128 136 record095_frame021_links_0064 record095_frame021_links_0128))
theorem record095_frame021_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 21 :=
  of_group record095 21 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0104
    Papers.RationalityTen.SharedFrameCatalogue.group0104_facts record095_frame021_indices record095_frame021_graph record095_frame021_links
def record095_frame022_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0103.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0103.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0103.localPairCheck (smallEmbedding record095) (record095.maps 22) (record095.inverseMaps 22) record095_frame022_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0103.localPairCheck (smallEmbedding record095) (record095.maps 22) (record095.inverseMaps 22) record095_frame022_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0103.localPairCheck (smallEmbedding record095) (record095.maps 22) (record095.inverseMaps 22) record095_frame022_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0103.localPairCheck (smallEmbedding record095) (record095.maps 22)
      (record095.inverseMaps 22) record095_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame022_links_0000 (interval_append _ 64 128 136 record095_frame022_links_0064 record095_frame022_links_0128))
theorem record095_frame022_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 22 :=
  of_group record095 22 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0103
    Papers.RationalityTen.SharedFrameCatalogue.group0103_facts record095_frame022_indices record095_frame022_graph record095_frame022_links
def record095_frame023_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0097.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0097.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0097.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0097.localPairCheck (smallEmbedding record095) (record095.maps 23) (record095.inverseMaps 23) record095_frame023_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0097.localPairCheck (smallEmbedding record095) (record095.maps 23) (record095.inverseMaps 23) record095_frame023_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0097.localPairCheck (smallEmbedding record095) (record095.maps 23) (record095.inverseMaps 23) record095_frame023_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0097.localPairCheck (smallEmbedding record095) (record095.maps 23)
      (record095.inverseMaps 23) record095_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame023_links_0000 (interval_append _ 64 128 136 record095_frame023_links_0064 record095_frame023_links_0128))
theorem record095_frame023_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 23 :=
  of_group record095 23 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0097
    Papers.RationalityTen.SharedFrameCatalogue.group0097_facts record095_frame023_indices record095_frame023_graph record095_frame023_links
def record095_frame024_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0055.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0055.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0055.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0055.localPairCheck (smallEmbedding record095) (record095.maps 24) (record095.inverseMaps 24) record095_frame024_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0055.localPairCheck (smallEmbedding record095) (record095.maps 24) (record095.inverseMaps 24) record095_frame024_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0055.localPairCheck (smallEmbedding record095) (record095.maps 24) (record095.inverseMaps 24) record095_frame024_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0055.localPairCheck (smallEmbedding record095) (record095.maps 24)
      (record095.inverseMaps 24) record095_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame024_links_0000 (interval_append _ 64 128 136 record095_frame024_links_0064 record095_frame024_links_0128))
theorem record095_frame024_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 24 :=
  of_group record095 24 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0055
    Papers.RationalityTen.SharedFrameCatalogue.group0055_facts record095_frame024_indices record095_frame024_graph record095_frame024_links
def record095_frame025_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0094.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0094.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0094.localPairCheck (smallEmbedding record095) (record095.maps 25) (record095.inverseMaps 25) record095_frame025_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0094.localPairCheck (smallEmbedding record095) (record095.maps 25) (record095.inverseMaps 25) record095_frame025_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0094.localPairCheck (smallEmbedding record095) (record095.maps 25) (record095.inverseMaps 25) record095_frame025_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0094.localPairCheck (smallEmbedding record095) (record095.maps 25)
      (record095.inverseMaps 25) record095_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame025_links_0000 (interval_append _ 64 128 136 record095_frame025_links_0064 record095_frame025_links_0128))
theorem record095_frame025_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 25 :=
  of_group record095 25 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0094
    Papers.RationalityTen.SharedFrameCatalogue.group0094_facts record095_frame025_indices record095_frame025_graph record095_frame025_links
def record095_frame026_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x648b1fd8dac4661b307d814bf65efade96d0b555a12cb562eac855a2a8130096d4ada4391f88e946b230d15e85442220c904280f3fe9f6cf947b93ae9d2ce727123811bacdac6c23559918c6862130717e4bc65942c015b08984392138f687903b51d10e3c6f63201880bf85da2db1648a9c52c285127091c48023911908ac44421b10a083c4102010fc07c43d41e30ee07543921c20dd86c83561a40ce865831e1810bd05cc29414309e04d425c127090846422410b08283f81ec0ef07403881b60d500c005c02c01500a004c022010007803001600a0018008002000 } : Fields).get c.val)
theorem record095_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 26) (record095.inverseMaps 26) record095_frame026_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 26) (record095.inverseMaps 26) record095_frame026_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 26) (record095.inverseMaps 26) record095_frame026_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 26)
      (record095.inverseMaps 26) record095_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame026_links_0000 (interval_append _ 64 128 136 record095_frame026_links_0064 record095_frame026_links_0128))
theorem record095_frame026_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 26 :=
  of_group record095 26 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record095_frame026_indices record095_frame026_graph record095_frame026_links
def record095_frame027_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6bb6b46aa69b69468a68567e67765c65264864163562c6075fc5f357456e56553e53752c52251c5164e74de4d54ca4c44bb4a94a049546b46445a44c44543b43542e42740c4023f83ee3e33da3b53a93a032031930e2ea2e42db2d22cc2c629728e28527927026525124b24222421d21720f2061fd1f41ec1e51de1d51cc1c31bb1b41af1ab1a719f19819118818117b17316b16215014813f11d11811210b1050fe0f90f10eb0e40df0d90d50cf0c80c30bc0b501801701601501401301101000f00c00b00a003002001000 } : Fields).get c.val)
theorem record095_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record095) (record095.maps 27) (record095.inverseMaps 27) record095_frame027_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record095) (record095.maps 27) (record095.inverseMaps 27) record095_frame027_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record095) (record095.maps 27) (record095.inverseMaps 27) record095_frame027_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record095) (record095.maps 27)
      (record095.inverseMaps 27) record095_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame027_links_0000 (interval_append _ 64 128 136 record095_frame027_links_0064 record095_frame027_links_0128))
theorem record095_frame027_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 27 :=
  of_group record095 27 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record095_frame027_indices record095_frame027_graph record095_frame027_links
def record095_frame028_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1025.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1025.count (({ width := 9, code := 0xb75b2d566b258ac35faed72b356aa5469d48a2d0a592b94c86411e8e46e33178ac52210e86c220d057cbddeaf177bb5d8ea7439dc8e16fb71b2d3683356eb65a2b156a953a9948a25027d36994c24d22904421906813f9f0f4793c1dcea72381bcdc6d361acd46833188c05d2d160aa51279308642200f87a3b1d0e06e351a0cc6230170b4582b0a04c24110803c1c0d0602c1409018080200 } : Fields).get c.val)
theorem record095_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1025.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record095) (record095.maps 28) (record095.inverseMaps 28) record095_frame028_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record095) (record095.maps 28) (record095.inverseMaps 28) record095_frame028_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record095) (record095.maps 28) (record095.inverseMaps 28) record095_frame028_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1025.localPairCheck (smallEmbedding record095) (record095.maps 28)
      (record095.inverseMaps 28) record095_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame028_links_0000 (interval_append _ 64 128 136 record095_frame028_links_0064 record095_frame028_links_0128))
theorem record095_frame028_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 28 :=
  of_group record095 28 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1025
    Papers.RationalityTen.SharedFrameCatalogue.group1025_facts record095_frame028_indices record095_frame028_graph record095_frame028_links
def record095_frame029_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x90c823f1e8ec7237198c452271288c3e1d0a8441e05017fbf1f6f97bbd9e8f077bb5d6ea74395c8e26fb79badc6db69b2d76b349a2d067b3598c86331580bf5eae972b75aad164ae56aad52a85328d44a04ea7136994b251228e45a250c84409f8f6793b9d4e26e361a4cc633097cba592b954a24f26128904722908803f1e8e870361a8cc602e0a04c24110803c1a0c058241007018080200 } : Fields).get c.val)
theorem record095_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record095) (record095.maps 29) (record095.inverseMaps 29) record095_frame029_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record095) (record095.maps 29) (record095.inverseMaps 29) record095_frame029_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record095) (record095.maps 29) (record095.inverseMaps 29) record095_frame029_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record095) (record095.maps 29)
      (record095.inverseMaps 29) record095_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame029_links_0000 (interval_append _ 64 128 136 record095_frame029_links_0064 record095_frame029_links_0128))
theorem record095_frame029_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 29 :=
  of_group record095 29 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record095_frame029_indices record095_frame029_graph record095_frame029_links
def record095_frame030_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1020.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1020.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1020.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1020.localPairCheck (smallEmbedding record095) (record095.maps 30) (record095.inverseMaps 30) record095_frame030_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1020.localPairCheck (smallEmbedding record095) (record095.maps 30) (record095.inverseMaps 30) record095_frame030_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1020.localPairCheck (smallEmbedding record095) (record095.maps 30) (record095.inverseMaps 30) record095_frame030_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1020.localPairCheck (smallEmbedding record095) (record095.maps 30)
      (record095.inverseMaps 30) record095_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame030_links_0000 (interval_append _ 64 128 136 record095_frame030_links_0064 record095_frame030_links_0128))
theorem record095_frame030_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 30 :=
  of_group record095 30 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1020
    Papers.RationalityTen.SharedFrameCatalogue.group1020_facts record095_frame030_indices record095_frame030_graph record095_frame030_links
def record095_frame031_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1014.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1014.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1014.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1014.localPairCheck (smallEmbedding record095) (record095.maps 31) (record095.inverseMaps 31) record095_frame031_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1014.localPairCheck (smallEmbedding record095) (record095.maps 31) (record095.inverseMaps 31) record095_frame031_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1014.localPairCheck (smallEmbedding record095) (record095.maps 31) (record095.inverseMaps 31) record095_frame031_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1014.localPairCheck (smallEmbedding record095) (record095.maps 31)
      (record095.inverseMaps 31) record095_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame031_links_0000 (interval_append _ 64 128 136 record095_frame031_links_0064 record095_frame031_links_0128))
theorem record095_frame031_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 31 :=
  of_group record095 31 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1014
    Papers.RationalityTen.SharedFrameCatalogue.group1014_facts record095_frame031_indices record095_frame031_graph record095_frame031_links
def record095_frame032_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0054.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0054.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record095_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0054.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0054.localPairCheck (smallEmbedding record095) (record095.maps 32) (record095.inverseMaps 32) record095_frame032_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0054.localPairCheck (smallEmbedding record095) (record095.maps 32) (record095.inverseMaps 32) record095_frame032_indices (Fin.ofNat record095.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record095_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0054.localPairCheck (smallEmbedding record095) (record095.maps 32) (record095.inverseMaps 32) record095_frame032_indices (Fin.ofNat record095.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record095_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0054.localPairCheck (smallEmbedding record095) (record095.maps 32)
      (record095.inverseMaps 32) record095_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record095_frame032_links_0000 (interval_append _ 64 128 136 record095_frame032_links_0064 record095_frame032_links_0128))
theorem record095_frame032_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 32 :=
  of_group record095 32 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0054
    Papers.RationalityTen.SharedFrameCatalogue.group0054_facts record095_frame032_indices record095_frame032_graph record095_frame032_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (Fin.cases (record095_frame002_supported hcells) (Fin.cases (record095_frame003_supported hcells) (Fin.cases (record095_frame004_supported hcells) (Fin.cases (record095_frame005_supported hcells) (Fin.cases (record095_frame006_supported hcells) (Fin.cases (record095_frame007_supported hcells) (Fin.cases (record095_frame008_supported hcells) (Fin.cases (record095_frame009_supported hcells) (Fin.cases (record095_frame010_supported hcells) (Fin.cases (record095_frame011_supported hcells) (Fin.cases (record095_frame012_supported hcells) (Fin.cases (record095_frame013_supported hcells) (Fin.cases (record095_frame014_supported hcells) (Fin.cases (record095_frame015_supported hcells) (Fin.cases (record095_frame016_supported hcells) (Fin.cases (record095_frame017_supported hcells) (Fin.cases (record095_frame018_supported hcells) (Fin.cases (record095_frame019_supported hcells) (Fin.cases (record095_frame020_supported hcells) (Fin.cases (record095_frame021_supported hcells) (Fin.cases (record095_frame022_supported hcells) (Fin.cases (record095_frame023_supported hcells) (Fin.cases (record095_frame024_supported hcells) (Fin.cases (record095_frame025_supported hcells) (Fin.cases (record095_frame026_supported hcells) (Fin.cases (record095_frame027_supported hcells) (Fin.cases (record095_frame028_supported hcells) (Fin.cases (record095_frame029_supported hcells) (Fin.cases (record095_frame030_supported hcells) (Fin.cases (record095_frame031_supported hcells) (Fin.cases (record095_frame032_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012
