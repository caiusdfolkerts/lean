module
prelude
public import GraphInputsRow31Part00025Data
public import RawFrameSupport
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x83d8358127f77ee7c57ab7a679b78b78677b76375f7587437316f96d86c96b86a269367f65964964061d6105fe5e75db5c859e59158357857356555454b54553e53852f52952251c4c34ae4a64a046542e3f03e43dc3cc38934d32331a30c3043012f32d02c92b62b02ab2902472041ec1dd1d31cf1c01b719418516d15f15814f14513211410c0ed0e60d80cc0c80c40c109809108d07606f06b06505f05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame001_links_0000 (interval_append _ 64 128 131 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x19e73865dc9d8f30f5febf37aae9dcdb83682cdd95b095caa953da5f48a885059f3376694cd96d2c65449a92722238c6b8c71722b44c8790ce16c2884506609c0e812f0ddc3b275adf1a6325638c5983ad3550a2943a7b4de9b931a384668750ca15408734d118f3085f0bc16a2c85049a1242344588810a1fa39c708d01963045c8b61642bc438820fe1b4340640c217c2d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame002_links_0000 (interval_append _ 64 128 131 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0779.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0779.count (({ width := 8, code := 0xd9d8d5d4d3d0cdcccbc9c8c7c5c4c3c2c1bebcbab9b8b6b5b3b2b1afaeacabaaa8a6a5a4a3a2a09d9c9b9a9998979695949392918c89868584837e7b7877767574726d6c69686766615e5b5a59585755514f4d4b4a49484642413e3d3b3a3938373533312f2d2b2927252322211a191817141312110f0e0d0b0a090806050403020100 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame003_links_0000 (interval_append _ 64 128 131 record000_frame003_links_0064 record000_frame003_links_0128))
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0779
    Papers.RationalityTen.SharedFrameCatalogue.group0779_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0752.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0752.count (({ width := 9, code := 0x432170883c1a0701803fdfafc7d3d1e6f177bb9d6ea7439dcce471375b4d96bb59a8d36933d94c862b0d82be5dae56eb55a2cd64b1582bd5cad562ad54a4512853e9e4e25d2c9348a411a8642205007f3f1f4f4773a1c8e26e36198c6602f978ba5b2b948a04c259289248239188a43208f476381a8cc5e2d148a04c251208c3e1e0e86c30150a048220f070281007018080200 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0752.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame004_links_0000 (interval_append _ 64 128 131 record000_frame004_links_0064 record000_frame004_links_0128))
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0752
    Papers.RationalityTen.SharedFrameCatalogue.group0752_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0722.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0722.count (({ width := 8, code := 0xa09f9c9b9a9795949391908f8d8c8b8a8986858382817f7e7c7b7a797876757472706f6e6d6c6b6a696867666564636261605f5e5d5c5a5958575655535251504f4e4c4b4948474645444241403f3e3d3b3a38373635343331302e2d2c2b2a292827252322201e1d1b191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0722.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0722.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame005_links_0000 (interval_append _ 64 128 131 record000_frame005_links_0064 record000_frame005_links_0128))
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0722
    Papers.RationalityTen.SharedFrameCatalogue.group0722_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
def record000_frame006_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x38a9bf6dc76cc35b1a70ce266bb2c58f2c6e624304d81cc065e72e616c6b05579ab5554aa9353aa911476a354e8a70133a96c4ada4e120c8fe47b237919489f430a13107c830410a030ffc7f03f39ca8e3a7173869a7cc7c5fe2fc17ccbac56328713cc9de4e926c934c95445a22810ac84241a1f30dbc61e2fe17b0bc05d02c8154096047a21e10187e83e41e00d885d02d614309d049822a10707c03a413409304781d80de06b032817c0b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record000_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 6) (record000.inverseMaps 6) record000_frame006_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 6)
      (record000.inverseMaps 6) record000_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame006_links_0000 (interval_append _ 64 128 131 record000_frame006_links_0064 record000_frame006_links_0128))
theorem record000_frame006_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 6 :=
  of_group record000 6 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record000_frame006_indices record000_frame006_graph record000_frame006_links
def record000_frame007_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x14f29bd24a294367cce19b73465fcbc9652724bc909071da2b43e8710be1141b824ff9fc3f47b4f51e4bbb76eeb9cdb9671ce25c2b7b6dad95b0b5a6a8d31a3341678be9782ed5d0b0d522865029f939a4444c8590920b40a80cfc1db3aa704de9b834e5f4ad95329a520a293d26e4848d90e20a4087f0fa1d635c698c41822ec5a0b115c2a8440851021b0338640be1682b8550a21401b8360660c81482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record000_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record000) (record000.maps 7) (record000.inverseMaps 7) record000_frame007_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record000) (record000.maps 7)
      (record000.inverseMaps 7) record000_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame007_links_0000 (interval_append _ 64 128 131 record000_frame007_links_0064 record000_frame007_links_0128))
theorem record000_frame007_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 7 :=
  of_group record000 7 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record000_frame007_indices record000_frame007_graph record000_frame007_links
def record000_frame008_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x13ba734de99b30e5549892f24a414808f318a2f4588930fa12c1a82903a00bfa7ecf89ed3d677eeedd9ba0738e49bcb726d8d95afb5968ccf59ab30652c7d8d31361aba16f2da5aeb0d52287504a013aa5746a8850f21641c835019e43c2730e31c1366620b71642ba560ab14a28a4a48f10e20e40c7f8f91da358688bd1762bc540a413e2704007d0f41b8350670c21702c8570a61481c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record000_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 8) (record000.inverseMaps 8) record000_frame008_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record000) (record000.maps 8)
      (record000.inverseMaps 8) record000_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame008_links_0000 (interval_append _ 64 128 131 record000_frame008_links_0064 record000_frame008_links_0128))
theorem record000_frame008_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 8 :=
  of_group record000 8 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record000_frame008_indices record000_frame008_graph record000_frame008_links
def record000_frame009_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0769.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0769.count (({ width := 8, code := 0xa09f9c9b9a9795949391908f8d8c8b8a8986858382817f7e7c7b7a797876757472706f6e6d6c6b6a696867666564636261605f5e5d5c5a5958575655535251504f4e4c4b4948474645444241403f3e3d3b3a38373635343331302e2d2c2b2a292827252322201e1d1b191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record000) (record000.maps 9) (record000.inverseMaps 9) record000_frame009_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record000) (record000.maps 9)
      (record000.inverseMaps 9) record000_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame009_links_0000 (interval_append _ 64 128 131 record000_frame009_links_0064 record000_frame009_links_0128))
theorem record000_frame009_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 9 :=
  of_group record000 9 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0769
    Papers.RationalityTen.SharedFrameCatalogue.group0769_facts record000_frame009_indices record000_frame009_graph record000_frame009_links
def record000_frame010_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0741.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0741.count (({ width := 8, code := 0xa09f9c9b9a9795949391908f8d8c8b8a8986858382817f7e7c7b7a797876757472706f6e6d6c6b6a696867666564636261605f5e5d5c5a5958575655535251504f4e4c4b4948474645444241403f3e3d3b3a38373635343331302e2d2c2b2a292827252322201e1d1b191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record000) (record000.maps 10) (record000.inverseMaps 10) record000_frame010_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0741.localPairCheck (smallEmbedding record000) (record000.maps 10)
      (record000.inverseMaps 10) record000_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame010_links_0000 (interval_append _ 64 128 131 record000_frame010_links_0064 record000_frame010_links_0128))
theorem record000_frame010_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 10 :=
  of_group record000 10 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0741
    Papers.RationalityTen.SharedFrameCatalogue.group0741_facts record000_frame010_indices record000_frame010_graph record000_frame010_links
def record000_frame011_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0720.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0720.count (({ width := 8, code := 0x8281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0720.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0720.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0720.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0720.localPairCheck (smallEmbedding record000) (record000.maps 11) (record000.inverseMaps 11) record000_frame011_indices (Fin.ofNat record000.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record000_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0720.localPairCheck (smallEmbedding record000) (record000.maps 11)
      (record000.inverseMaps 11) record000_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record000_frame011_links_0000 (interval_append _ 64 128 131 record000_frame011_links_0064 record000_frame011_links_0128))
theorem record000_frame011_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 11 :=
  of_group record000 11 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0720
    Papers.RationalityTen.SharedFrameCatalogue.group0720_facts record000_frame011_indices record000_frame011_graph record000_frame011_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (Fin.cases (record000_frame006_supported hcells) (Fin.cases (record000_frame007_supported hcells) (Fin.cases (record000_frame008_supported hcells) (Fin.cases (record000_frame009_supported hcells) (Fin.cases (record000_frame010_supported hcells) (Fin.cases (record000_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd8d6b0b4c99cecd4658b1f98d6c4860ab03580cb765b4ad8d484a3c51aa7f12f6916482a3f51ec8ec469a29509c84041820390007f03f39f24f6c7a23be9da8eac72a38e9c5cd7a6b03481970c9e62f2ff17e4be65bc2ce9634ae25562a414e0a3850127a13b89d24db264928c8e846522e114088a436216908483440d1fc0f9073c37e1b78cf863c30f17e8bd85e02df1680a9449823d109080c3f41ef0ec06d03241760a2849823010907c83a40e006c030017c0b805b02a815007e03801a00bc05a028013809004602100e8070028013009004001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record001_frame001_links_0000 (interval_append _ 64 128 141 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcf266fb2818f0c6662630ad836c015e62ecd73ab3558e2c5146aa2350827c131c92c481a3a11a48c845a224508c83340f1fc4fba7c73d89e74f2a7903c01dd0eda7453979c98de06e13639a8cd2e67a31f98c4c405fc2f59768b865b12d39658af45652a394d0a4c51528313a09884ae250924c90846e230114488443321210647c23c51de8e306d836219d8c9c62a30317b0b5450026e11a888c4201ff0f587383721970a8048421c10007a039c0e006c030017c0b805b02a815007e03801a00bc05a028013809004602100e8070028013009004001e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record001_frame002_links_0000 (interval_append _ 64 128 141 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6f06e56d46be6b46a669769068466d66766362a6246215a75a359f58754d51d51250a5065014f54de4b04a749d48447e47346b45f45645444d44944143442e42b4053fa3e83d83cf3c53aa3a73a338e38237736836035a34f34433833032b3293223152fd2e52d92d52cd2c62ba2b52b02a92a129428a26425324e23622421c2102092051fa1ee1d219b19017316d16415a14a1351251150f50e00d30c80be0b206a06605a05905605504f04e03f03803402f02d02802702402302101d01c01401301201000f00e00b008007004003002001000 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record001_frame003_links_0000 (interval_append _ 64 128 141 record001_frame003_links_0064 record001_frame003_links_0128))
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a419fcce36663289920c7e62c311586abdf5daae8167cb2b581ab11564a8a51b28994249dc4aca39d1868ab44c21e10a880a3fd1fa0f8a7b63d31e54edc75c3a51c90e227013559a04cd860a2fb973cb2057e2ab14089e44de254109476638f1bb8d9068832016b0b1856829114109c84c22531260914470231115888c43a216107081c4021f90f987b03b81d50e7070036419f0c806243061740b6859c2b014a09e84b82240fe07b03bc1d20e203b81c00d806002f81700b605502a00fc070034014009c04802300e807003601a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame001_links_0000 (interval_append _ 64 128 143 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x34c982ac0d6032fa97babce5da2e9d730b765b4ad8d602af556aaa8552aa7552128f146a9f94bda45920a8fd47b234114684e42020c101c8003f81f9cf927b63d11df4ed47563951c74e2e6bd3581a40cb864f31797f8bf25f32e01558a024f427713a499a4a723291708a043621690848344091fa0f8077a3ad1cf0e346fc36f1ae8d3467c32d18f0c3c5fa2f61780b3054226812608f445c21210187e83b41b60c905d828a12608d04241f20e903b81c00d806002f81700b605502a00fc070034014009c04802300e807003601a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame002_links_0000 (interval_append _ 64 128 143 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x7416e06d96d26c16ba6b36a069a69367766c66763d6336216045fa5e85c75c25bb5a456352a51c51550e4fb4e74c04b94b149c49348948147046a46345244b44442741c4173eb3e13cf3b13a739537737236b35430c2d92cc2c52be2ab29726c26325924724023823122922221b20e2051fd1f51ee1e71dd1d41cc1c41bd1b61ab1a71a319618817516315a15214013713112811d1131050eb0d90d50cf0c90c307707006c06005f05c05b05505403f03803402802702402301d01c01b01a01801401301201000f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame003_links_0000 (interval_append _ 64 128 143 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3281798bb35ceae25706b7f5b8ada56cab3558e2c515c4ad355d2a5d512a7251aa88d4209ef4c724b12068e846922c911e846419a078fe27dd3e39ec4f3a7953c81e00ee876d3a29cbce4c6f03709b1cd4669733d18fcc626202fe96c4aca54729a1498a144ec257128492646e230114488442f21010608003ef1f08f4c78a3bd1d60e6871837a1b60d8867632718a8bc85a22a814009b84b623511188403da1d00dc865c2a012108804001e80e703b81c00d806002f81700b605502a00fc070034014009c04802300e807003601a00c0050026012008003c01c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame004_links_0000 (interval_append _ 64 128 143 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7286b86a969d69268a68768067a67665a64764162461d6095f05e95d95b55ae5a158d5545255125034f64e94da4af4a649948247a46e46445645344d44544143c41f4104073ea3e23d13b63ae3a037b37136735331a2eb2d82c62bd2ae29e27526925e24823d23322a21f2172122082001fa1f11eb1e51e01d81d01c71bf1b91ad1a619e18e17d16c15e15614f14113813212711b1101070ed0da0d40cf0c90c107506e06a05e05d05a05905305203f03803402802702402301d01c01b01a01801401301201000f00e00c00b008007004003002001000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 128 143 :=
  interval_of_check _ 128 15 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 143 record002_frame005_links_0000 (interval_append _ 64 128 143 record002_frame005_links_0064 record002_frame005_links_0128))
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6db34c991cc2560630157d4bdd5e72ed174eb985bb2da56c6b2855a2951486a3b51a27e52f6916482a3f51ec8743f39f24f6c7a23be9da8eac72a38e9c5cdc866e30697fcbf05f22e01558a024f427713a490441a2048fd07c03bd1d68e7871a37e1b78d7469a33e1968c7861e2fd17b0bc059a2a213c89684401fa0ed06d83241760a2849812409104702340de06e03581a80c005f02e016c0ae05602a815006e03601980c8050027012008c03e01e00e807003601a00c0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0xd368b399ac9e47218fc7637198bc56271183bede2eb71b7da6bf57aa53e9b4390472371a8cc622f168ac521f0982405fafb7c3c9daeb73b95bcc560afd7cbb5cadd6cb559ac15eae562a950a65127d3a9b4d25d228c43204f87635180904723114803f1f0f46c35198c8602f170b45228138983e1e0e06c32180b8582a1409844200f07034180a048200e04018080200 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0481.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0481.count (({ width := 9, code := 0x894461b0c8441e0d058240e0501803fdfcfb7bbd5e8f1783bdd6ea74b95c8df65b1d8cc56230d84c1602fd78b85b2d564b1572a950a75228d3c8b4421d0c854220d0481401fcfc7d3e1ecf4793c1dcec753a1cce06d3519cc8612e1608e46229107e3e1e8f06c35198c8602f170b45228138983e1e0e06c32180b8582a1409844200f07034180a048200e04018080200 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0481.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0481.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0481.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0481.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0481
    Papers.RationalityTen.SharedFrameCatalogue.group0481_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x7cbba41b68d2866fb321944c9063f316188ac355efaed5740b6756da97d474a2250727712b28e7461a2ad1308303ca9db8eb874a3921c44e026ab34099b0c665a729594189dc4da254109476638f1bb8d905f8261129893048a23811888ac44621d10b083840e2010fc87cc3d81dc0ea87383821b30d3065c2f61670ac052827a12e08903f812409104702340de06e03581a80c005f02e016c0ae05602a815006e03601980c8050027012008c03e01e00e807003601a00c0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x19c32f64ec1b78ae9dcdb3d672ca584a8945a885059bd342664b69632a24d4938df1a63245c8ad0d617c2784506609c0f810f09d6ba573cdf5b7368698c8d8d31560eb4d41a7c4de9b92f25b4848f11921d434851021cd3165f4bc16a2be55ca293b2664908d9152204287e8e71c2340658c71722d8590aa11221c4287f0de1b4358640c217c2d0590ac150210410680cc1482704a0881001e03804c0900f01a0280480700600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x7743addc50df76b935adacad586a8b525a5cd19688b3e19eccee5cfae016d0b1356baa154eea66519a8513f89a74b5a4652168fa478a3991b08cc462a2fd16a8b0454a28d1368924459dc0ec07503839a04c7062830d982cbf65b2296138c9a64c926112e89684ad253125891e48a23d91dc8de4692198bb45b22c715f0a9050a26b12488b44162000ed87043441880b3052825011d07c83c41d20e206d835016209d03b01d00de06a034819c0ca06002d816808403801b80d006403101480a004a023011004c01c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record005_frame001_links_0000 (interval_append _ 64 128 132 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x70b7076f56e96d26ce6ca6c16ba6ae69a68a67e66a66866460b5fe5ef5d45be5a55a259e58557556554552c50f50b5075044ef4d84ca4c04b74a549f49448b48047146a42741e4153ef3ba3a63a239f39739037033d32c32a32731e30e3062f62ed2d82d22cf2b92b72ad2a828b20f20a2062001e71cb1b91a319117c17415d1481331251131060f30ee0da0cb0bc0b00a80a009108706e06d06906406306105f05a05505404203803703403203102902802502302201300e00d00a009008007004003002001 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record005_frame002_links_0000 (interval_append _ 64 128 132 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xa794d28bd0d9e73be75ce59bd35a61cb595b26e4c4918930fa1c422820fedfcbf37ccf69e93bb75ce61ca38f718e11bd3746dcda5afb5d6aad41a533f676ba1702dc586a614127d4ee9cd3624f44c841062094087f4fc9f23dc77cec9d838e714dd9b734e544a714928a4f49992b2424708710b1fc3d8758e41ae33c620c21702cc568a914c28c4a08a0d81a8338630c41802f85b0ae1582003706c0cc188300520a01282304404c0700d0140240400700800c01001 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record005_frame003_links_0000 (interval_append _ 64 128 132 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6f56e96c866b66666265463d60c5a65a259e59c59258857a56c56154a53352850e50c5084f94e24cc4b84a34a148c48246f46845f4494143a93a63a239a39238e38037737035834433d32c32a3162fe2ec2db2ce2bc2b629d29028927726c26424522c22420a2061ec1d01b91a519117e17415314914413412f12612011210a1071000f20ef0e40df0d90cc0ba0ae0a609e08708107f07e07206906406304203703203103002f02d02902802502302201f01e01d01c01b01a01801401301000e00d00a009008007 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame001_links_0000 (interval_append _ 64 128 133 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7577487106bc6b76b36aa69464e5ee5e95e55e15db5d25c55bb5b258456a55b52c52951f5084f64e04c34ae4ab49548f48447d4794654253cd3c83c33bd3b43ac39f39338c36335034832131b3082fb2ed2d62c62b82b42a429b29328527927124422f2261fc1f41e31d41c41aa19918b18716e16316015014913d13011b10f10a0fd0f00ec0e00d40cf0c60bb0b20a60a108c08608108007006906406304003703203103002f02d02902802502302201f01e01d01c01b01a01801401301000e00d00a009008007 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame002_links_0000 (interval_append _ 64 128 133 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0765.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0765.count (({ width := 8, code := 0xc2c1c0bebdbcbbbab8b5b4b3b2b1b0afaeadabaaa9a6a5a3a1a09f9c9a9996949291908f8d8a898887868584838281807f7d7c7b7a79777674737271706e6c6b696766656462605f5e5d5c5b5a5958565553514f4e4d4b494846454442403f3e3d3b3a39383634323126242221201f1e1d1c1b1a1918171615141312100f0d0c0b09080706 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0765.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0765.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame003_links_0000 (interval_append _ 64 128 133 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0765
    Papers.RationalityTen.SharedFrameCatalogue.group0765_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0739.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0739.count (({ width := 8, code := 0xcbcac9c7c6c5c4c3c1bebdbcbbb9b7b5b4b3b1b0afacaba9a7a6a5a2a09f9c9a9897969593908f8e8c8a88878685848382807f7e7d7c7a797776757473716f6e6c6a69686765636261605f5e5c5a59565553514f4e4d4b494846454442403f3e3d3b3a39383634323126242221201f1e1d1c1b1a1918171615141312100f0d0c0b09080706 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame004_links_0000 (interval_append _ 64 128 133 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0739
    Papers.RationalityTen.SharedFrameCatalogue.group0739_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0719.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0719.count (({ width := 9, code := 0x1259146e271288c3a17037cbe1eef67abd1e4f177bb1d4e97238dc0de6eb69aed56a3459ccb6531d88bc592c560af572b558ab5529d4aa44fa793a9c4d25d2c9449a411e8e46229128541204fa7c3d1e0ec74399c8e26e369b0d26832988c05e2e96cb05729948a24f2612c94492291086421f8f4763a170b054291409c4a22108803c1d0e06c34190c05c2a1108038180b048200e06 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0719.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0719.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame005_links_0000 (interval_append _ 64 128 133 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0719
    Papers.RationalityTen.SharedFrameCatalogue.group0719_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe8471cb5f98c6c4f61e307d7a8b194ff27a93ae9cd4e326fd3609a94d0a6192e29694a8253928c939495a47121e90348023cd1d68e046ca2fd0d479a3349954c8262d30c9818bc45d12e015cca7852b270134495648723391088464011f88ef87543971b98d886a23041668af04e226211e08603f01d30da06483041550a7052428013b09a04b424811d08c044421210507e03d41e00ea07103701ac0d004e824811a08c03d01bc0d406902100dc06403101800bc05a029014009404602200f807803a01c00d8068030014009804001c00d0050024010007 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame006_links_0000 (interval_append _ 64 128 133 record006_frame006_links_0064 record006_frame006_links_0128))
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x3f97e8f65d7bac74ce89ceb826b0d4da7b4d68ed059cb32656c6586b065e6bc5762e45b2b39622ba572ab954a9f536a5d48a7449a92d23a3f4748e11722b45286105a063e47b4f01d5396704db9a9348650c718c3025ecbb1652b6564a21412684a08f9132103f87c8e81c437c6b0d319c3205f0ba1722cc548a71422744d89611e228438840ec1c43686c0ca1802e05b07c0dc190310600bc168290500941182203e0780e81c0360680c0140260400700d01402404007 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame007_links_0000 (interval_append _ 64 128 133 record006_frame007_links_0064 record006_frame007_links_0128))
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x5edbb369ea6d48a894ea94cef93725648c8c9112123ec778e516e2243d8450820cc0a7f4fb9f03d179ef09ddbb375eea9cdb6962ec4586b065fabd976ae55c0af9562aa518a1d392634b09111922343c82d011fc3e47b0f29bf350690bf9772cc56caa14026c4989110e20e4147f0fa1ea3bc730df1b6354668cc1862f05c0b31542984f89a1061f83d0790e01a8330650840dc190310600bc168290500941182203e0780e81c0360680c0140260400700d01402404007 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame008_links_0000 (interval_append _ 64 128 133 record006_frame008_links_0064 record006_frame008_links_0128))
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
def record006_frame009_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0763.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0763.count (({ width := 8, code := 0x84838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0763.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0763.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0763.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0763.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0763.localPairCheck (smallEmbedding record006) (record006.maps 9)
      (record006.inverseMaps 9) record006_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame009_links_0000 (interval_append _ 64 128 133 record006_frame009_links_0064 record006_frame009_links_0128))
theorem record006_frame009_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 9 :=
  of_group record006 9 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0763
    Papers.RationalityTen.SharedFrameCatalogue.group0763_facts record006_frame009_indices record006_frame009_graph record006_frame009_links
def record006_frame010_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0737.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0737.count (({ width := 8, code := 0x84838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0737.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0737.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0737.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0737.localPairCheck (smallEmbedding record006) (record006.maps 10) (record006.inverseMaps 10) record006_frame010_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0737.localPairCheck (smallEmbedding record006) (record006.maps 10)
      (record006.inverseMaps 10) record006_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame010_links_0000 (interval_append _ 64 128 133 record006_frame010_links_0064 record006_frame010_links_0128))
theorem record006_frame010_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 10 :=
  of_group record006 10 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0737
    Papers.RationalityTen.SharedFrameCatalogue.group0737_facts record006_frame010_indices record006_frame010_graph record006_frame010_links
def record006_frame011_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0718.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0718.count (({ width := 8, code := 0x84838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0718.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0718.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0718.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0718.localPairCheck (smallEmbedding record006) (record006.maps 11) (record006.inverseMaps 11) record006_frame011_indices (Fin.ofNat record006.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record006_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0718.localPairCheck (smallEmbedding record006) (record006.maps 11)
      (record006.inverseMaps 11) record006_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record006_frame011_links_0000 (interval_append _ 64 128 133 record006_frame011_links_0064 record006_frame011_links_0128))
theorem record006_frame011_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 11 :=
  of_group record006 11 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0718
    Papers.RationalityTen.SharedFrameCatalogue.group0718_facts record006_frame011_indices record006_frame011_graph record006_frame011_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (Fin.cases (record006_frame009_supported hcells) (Fin.cases (record006_frame010_supported hcells) (Fin.cases (record006_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x66b66666265463d60c5a65a259e59658c58655d52450b5074c94b149e48547f45f4494143a93a63a239d39538f37033d32c32a2ec2db2ce2bc2b629d29028927726c26424522c22420a2061ec1d01b91a519117e17415714b14213612d1251060ee0c908708107f07e07206906406305b05a05705505405105004f04e04203703203102902802502302201f01e01d01c01b01a01801401301000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6bc6b76b36aa69464e5ee5e95e55df5d45cb5af5555225194da4bc4a549348d4794654253cd3c83c33be3b73af38c34832131b2ed2d62c62b82b42a429b29328527927124422f2261fc1f41e31d41c41aa19918b18717116615f15414613a1070eb0c508c08608108007006906406305d05c05905705605305205105004003703203102902802502302201f01e01d01c01b01a01801401301000e00d00a009008007005004003002001000 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0739.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0739.count (({ width := 8, code := 0xc7c6c5c4c3c1bebdbcbab8b6b2aeaaa8a4a19e9b99969593908f8e8d8b898582807f7c7a797776757473716f6e6c6a69686765636261605f5e5d5b585754524c47413b3a393836343231302f2e2d2c2b2a2928262422211d1c1b1a1918171615141312100f0d0c0b09080706050403020100 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0739.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0739
    Papers.RationalityTen.SharedFrameCatalogue.group0739_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19ecce0665328988ab6751aa88d4209ff4f7a7713228fa456226906080c3f49f1cf6e76e38898cca024ef26e132c9764a822e8f186f036617e0b6056a293141894c49824511c08c445620e0fc87cc3ac1d00e086cc34c1970c505ec2ea15f0ac054829414409e84842180f004e824811a08c03d01bc0d406903081800ba05b02d015c0ac05502a010806e03201880a4050025011808803e01e00e807003601a00c00500260100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6c966c65463d60b5fb5ef5d15be5a859658c58655d5245115004f04d94c94b149e48547f46b45f4494134073f83da3c33ab39d39538f37033d32f3263142fc2ec2db2ce2bc2b62a929d29028927726c26424522c2242101fb1b91b01a519118917e17416415714b14213612d1251060ee0e00d50c908107f06e06d06906405b05a05705505105004f04e03e03c03703202902802502301f01e01d01c01b01a01801401301000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x2fb7bbcde2e772b8dbadb6ab459ecd64b1d82b759ab552a149a3d127d3b9ac9a49228ec6e2f158a44e1b08823fdfafa7bbd1d8eb73b85bcdc6cb59a8d266b2990c35e2bd56a85127d389a49a411a8a43a1506763719cca632813c8c45219087c3d1e0ec6e361a8d0582a1409c44211007c361a0c8602e160a84c24100703014090401c0a04018080200 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0x2b354a8d42994aa451689409e4ee75379a4c6572994496471e8e4662b13884220b047fbf5f2f57a3cddeea72379b8da6bb55a0cf65b1d8ac360af978b95a2c960aa50a5d269146a290e85401f4f4783b1cce26830970b4582210c7e3e1e0ec70371b0d46632188c0542913094401f0f07432180b8582a1409844200e060281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
def record008_frame004_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1caecfb65131156c6b40594ab19510a3a4ffa7bd3b899147d22fd114873427a0c10187e93e39edcf2a76e38898bcc185f52c91550a0c4cb25d92a08ba3c61c58d5867e31b17e0b6056a29314189844a624c12288e046222b10707e43e61dc0e3869833e1970c5060c2f61750b3857c2b01520a5051027a12108603f81ec0f004902340ec07403781a80c206002e816c0ae05602a815007c03c01b80c8052028012808c03e01e00e807003601a00c00500260100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record008_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4) (record008.inverseMaps 4) record008_frame004_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 4)
      (record008.inverseMaps 4) record008_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame004_links_0000 record008_frame004_links_0064)
theorem record008_frame004_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 4 :=
  of_group record008 4 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame004_indices record008_frame004_graph record008_frame004_links
def record008_frame005_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x248c788c916218427841021fbbe47b2f51e73b9726e0dbcb716d0d85aab4d67eced97b25630bc573ade58eadd52a9a52aa3d3b2524888e919229444855051fe3f47c0f49e23bc750e59c4356658c79802da524a19392524848b9102023f07b0f21d83a0720cd1762c0560a80fe1ec3586a0cc1842c0570a81482704d09812c1e03b06e0c81482804a08c0f81e03a0700d81a0300500981001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record008_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 5) (record008.inverseMaps 5) record008_frame005_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record008) (record008.maps 5)
      (record008.inverseMaps 5) record008_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame005_links_0000 record008_frame005_links_0064)
theorem record008_frame005_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 5 :=
  of_group record008 5 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record008_frame005_indices record008_frame005_graph record008_frame005_links
def record008_frame006_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0491.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0491.count (({ width := 9, code := 0x35fa5d1683399acce5b2b92c7e3b1b86bfdf2ed74b8db2cb5bab54a9346a2cf27337994be572792c8e411f8f46a2b1086425fafc7b3b5d2e772381bcdc6c359a8cf632f570b555a9d48a04b2451c8a43a0d007235984ba5a211047a3c1d0e46833190c45c2d160ac5027120883e1e0e87032180b8582a1409844200e060281208038180a04018080200 } : Fields).get c.val)
theorem record008_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record008) (record008.maps 6) (record008.inverseMaps 6) record008_frame006_indices (Fin.ofNat record008.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record008_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record008) (record008.maps 6)
      (record008.inverseMaps 6) record008_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record008_frame006_links_0000 record008_frame006_links_0064)
theorem record008_frame006_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 6 :=
  of_group record008 6 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0491
    Papers.RationalityTen.SharedFrameCatalogue.group0491_facts record008_frame006_indices record008_frame006_graph record008_frame006_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (Fin.cases (record008_frame004_supported hcells) (Fin.cases (record008_frame005_supported hcells) (Fin.cases (record008_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record008_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025
