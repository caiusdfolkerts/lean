module
prelude
public import GraphInputsSix0Part00090Data
public import RawFrameSupport
public import SharedFrameGroups010Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x2eb5ceb7f6f6d55a1b3964ac7d85af75d2a9d4fa8f50e9ed38a4d48e8bd14a174226c4bb93323a4447d8d911212c1e829025fe3ed7ccf5de63bf768ea5ce38f708dedb53656b0d25a2b4163cbb9652c7584acd52a9150e9d9362614b095d1fa334508790a2023e279cf09df3986e8d819c324608bf1662a05189f13b25c4708d10e2104187f0fa1ea3bc748e41b6350648c717c2e05a0a91482784d093114208400660c81642c0560620c01282304402c0500900c01402003 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record000_frame001_links_0000 (interval_append _ 64 128 134 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x28dd19a25442804fe9f73d679cf29db3aa6ecda9a734266ccc9792e255ca89432762543383f05e08c077def35d73a673ee59c13766e2d91ad34e682cf99ab2b646c6d87b0c602bd976ae5594aa142a814f89c52f2514948e117a25438869082063fa7e0f71df3a2720e09c0350664c99812ea5a4b09562905009c93425847c8e10d20e4107f8f81e43c4750e31b4354658c41742d4590a713e2604b09110a2043f0650c615c2b0540660c81302404602c0500900c01402003 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (embedding (N := 44310) record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (embedding (N := 44310) record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record000_frame002_links_0000 (interval_append _ 64 128 134 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0358.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0358.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0358.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (embedding (N := 44310) record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (embedding (N := 44310) record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (embedding (N := 44310) record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0358.localPairCheck (embedding (N := 44310) record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record000_frame003_links_0000 (interval_append _ 64 128 134 record000_frame003_links_0064 record000_frame003_links_0128))
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0358
    Papers.RationalityTen.SharedFrameCatalogue.group0358_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0435.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0435.count (({ width := 8, code := 0xc5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaea5a3a19f9e9d9a98969593928f8d8b8a898785848382817f7d7c7b7a7978757271706f6d6b6a68666462605f5e5d5c5b59585755545351504f4d4c4b4948464442413f3e3d3b3a3938373635343332312f2e2d2b2a29282625242221201e1d1b1a1915141211100b0a0906050403 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0435.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (embedding (N := 44310) record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (embedding (N := 44310) record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (embedding (N := 44310) record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0435.localPairCheck (embedding (N := 44310) record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record000_frame004_links_0000 (interval_append _ 64 128 134 record000_frame004_links_0064 record000_frame004_links_0128))
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0435
    Papers.RationalityTen.SharedFrameCatalogue.group0435_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0296.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0296.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0296.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0296.localPairCheck (embedding (N := 44310) record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0296.localPairCheck (embedding (N := 44310) record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0296.localPairCheck (embedding (N := 44310) record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0296.localPairCheck (embedding (N := 44310) record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record000_frame005_links_0000 (interval_append _ 64 128 134 record000_frame005_links_0064 record000_frame005_links_0128))
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0296
    Papers.RationalityTen.SharedFrameCatalogue.group0296_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2925477a09cfe27bb3cf99f4c9e3a91bb8cac5fe2d715d865c2ca069021803bfd1ba6d13648314d86eb6e55728ad3dc9d24d7a66932697e4b825892ae9554a6a50926292348e245921490747e23b51cc8df3fd9ca0d3264d2f496c8b3e56129e94609fe4f826512688ee46722c90f08383ef1ef8f586f43431980bc859c2a91480a244b622b10407e03d41cd0d686002e01670ab854029214209d84d025e12808d043c21610307e03e01e00e807103701b20d204f026c12609103d81e00e006e013009004602000f807802200f007002c014009 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record001_frame001_links_0000 (interval_append _ 64 128 130 record001_frame001_links_0064 record001_frame001_links_0128))
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x3bb76fec7d87acf58e85d038e715e15c23806ffdd3b9f6aed1d95b1b44e61c8d8f31a607b97696ccd91af7582aa53ea5945e7fcfe9eb36266cb9957282464898d918e2e45583af7ddbba7714dcdb3b4d67cca98d3195f4bb16dace58eae14f295520a353825148a8a10da073f07d0ed1cb3786bcd39993045d8b796b2c8578aa14a27e4cc9511f20a3c0758e01ac34c638be1682a85389c1062043e87b0d61a43206204c0901182003e0780880f01c02c05009 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record001_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record001_frame002_links_0000 (interval_append _ 64 128 130 record001_frame002_links_0064 record001_frame002_links_0128))
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2909458a15504e6a731e98bcb8a51d254926c84e2150df86ac2aa0b502f80fbfd1c7edb068bb2e1962caa652327592cc916452b5558eab95582ab1548a9d4cc25d92a693c49a23951868a0444a20509684641ea0d906066f3309968ca864a32298fcabe54329a94b4a284d225b12a094048723391808b64562290c7c6122fb1770b744fc26812d0934478233115888c4382150d106482fc14309c845c20c0fc06d03480f607102f01700b605902b8158084038012809004602000f807801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x94093b93693491790d90b8fb8d68c48c18af85784e84883c8168057fe7f07337006d069b69368d68367766c66565859c58b57956756555a54f4ec4de4cb4bb4b848f47846545545042441d40e4053fd35c34a3403373233213162ac29c29228c27624a23522c22420d1ee1df1d51cc1c417116916316115d13d13512f12d12912612011611110e0f60f10eb0d70d10c40bd0b70ab0a907306a05705505405205004f04103802502402302001f01e00f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x295d25a3946e8ad0fa1d4367fcfa9f33de704df9b735e654c89893064e4868cf142254478891021e439868f0ddebb575ceb5d4ba56dad91abb4c696cb591315616c2976aeb5c8b816f2784e49b134a614c09710da0f412810fa9db3a2724e21b834c67ccd99732a52ca113b2724d08c91021441c810fe1f23d4798f11b034c660b91682a4520a0128248358630a41402784d0961281e03604a0901182003e0780780e01a0280480800800c00800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x21d10c0841c1e60d304e824c099f88fa97d23e05d8ceb9755ba51c8ee3a7163855a4acd163d30a983ac0f601afd57dcbea5eaaa2d4e8a605242909448a114b5a52125891548422c111a87142da14100e7f83ee1f18f666883359984cb663c3191884b1456e2b29580a824f926d93489984ad24491bc8be4502220d8869833a1948c5c5702a31488a044de26012588d044420e0dc86c03341600a704802160fe06b83240f607102f01700b605902b8158084038012809004602000f807801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x88087186585f84483382f82981080a8077f67af7a379f79878377c7707647026d76a768467e67a67767367266e6675ce5c65c05b85b55ad5a854653152951b5164ed4e34d14c34be4a149c49348f48c3bb3b23af3aa3a139d39932831b3183152ff2dc2cf2c92c62b02a229b2962932912091f91ec1e81e01b21a219519018a18417c17417016c13712f1220fc0f40df0d20ca0b50ae07706f05c05a05905705505404103802502402302001f01e00f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x26d4d799932e604bb9752da554a594928642c839031f635c678cb18611c16804fc9f73eb7d4fa1f2be17bcde9b8b6b6c4d81adb56666cad93b1f63cc2581af85e2bc16cad759cb2562a624ba95d2924948c90d0aa10418824ff1e93ce788ef9d53906f8dc9b4362544a514227c4e48c11021441c800fb1e83a8720e218c30c5f0a914a2684a89110c210330610a01382684b0921201d03504a0901182003e0780780e01a0280480800800c00800 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (embedding (N := 44310) record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1ea7d179cf37df3b9f66ec5d2b9f734e61baf72edfda9ae3586abd459031be2dc498730a58cb055ca714d499715a2844982902a01bff7f0fc5f43dd7aeec1c2b616bad5da6b43676b215f2ad546a7d40a724c49392424146a8bd112193926ecd91ab3425fcb81672b8534a313d26249c8f0f81e23b0738e11b6354630c0176298410690ac1542885009e0e41c02a04c0901182103e0780e81402003c0700b0140240400400600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x437616108283bc18a08302480cbef5f38f7f7ba3afdd5cea2743b901c5ee23704361db00d7b6b835a5ac8c1d601afb94fea6853024b123c903438a16508c83440fa038fec7dc3e31d78de26a734c9a20cf866b330965caf65652ab151ca104ea26912b894449424111cc8be4501c60db06c435419d8b8c5842b81528a044de25d12388d04441b90d4065c30c1760b1854024210e080032412807002e016c0ae05602a80e407002a013009004602100f807803a014008003c01c00b00500240100040018008002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x12624ac929231ea39c6d8d31822dc5289f0820e417820fe5fa3f17d4f25e23c1778ee1d9b746d6d8d8f318622b2163ac352ea4545a885049f53ba6e4d094119a2043a85d0920d41071cdd9b435c6b0cc98f3085e0bb9722d45a4b115e25c4989091f22c3f47a8f11d438c6f0da1a4338650ae1562a0538a413c2684808d114200370600a013c2584a0920e41c02a04c0901182103e0780e81402003c0700b0140240400400600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x62330eb82ac085c12dc36c4b56d7febc35c9ad950ae8334079f14f167753ac9c9cdee6773229864ba659d2c3957ca424f125c921c8be22b0fc874c3161610a0695b029568a8c53124791f48e746b22fd06081c4061fecfd27db3da9e94dac5802ac14b87d43c61d98e887162fc1740b6058e2b51538a044e223910788204021fa0f987b03c61dc0e106d034c1970c886283021730b6054828813d09a84a024211907f03d81e00d503881840ba05c02d815c0ac05501c80a404a024011807c03c01d00a8050022010007803801800a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame001_links_0000 (interval_append _ 64 128 135 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x436e19d09783ac15a08103280bbec5f36f8d7b93b35d88ebf756ba85d24e8573d39bdc9ce4572038b9c44e1370337edbe0dd26e036c9b0ed806bdb5c1ad2d645f72d49516a74530256526c92c48da3fd0e285c42420d103e80b3ee1f18ebc69933e1984b1456e2b29568a864d226092c0944494243117c8a04011d68e6c71837b1b60d886a033b17a0b4c57029314089bc4b223411107803861b90d506182ec16509084402020c903881840ba05c02d815c0ac05501c80a404a024011807c03c01d00a8050022010007803801800a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame002_links_0000 (interval_append _ 64 128 135 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8a88a289588e87a87086c86584884283b8337fb7f97f77ef7eb7e57df7dc7d97cf7cc7ca7c37be7b87b27ae7ac7a47a079c78878578378077b7796cf66b5eb5db5ce53d52a52551e50e4c94bd4b14a749a49147946d4313b03a23943012f22eb2e42d428f28327726a25f25723c2322091e11d91d01c81bf1b91b41ad19017f17016515f15714d14013712211611010c1010f90f20da0d40d00b406f05f05b05a05905505405303902902502402301f01e01d01501401101000f00e00c00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record004_frame003_links_0000 (interval_append _ 64 128 135 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1704b6fdb0ad6f5ffaefd71eb774079f14f1677530c974cb3a58711988043821950b584c34b9814a5f527a8e936c94949aa48521e8fd47520c103c80c3fd9fa4fb47c93d99e8cdac52b28d94189044152008fb47b63c91db0bf05d42d81638ad454c29513f89bc47220f10408043f41f30f6078c3b81a60cf065c32218a0c105ec2ce1600ac854829614409e84a024211808884282060f707803500d606a03101840ae05602a80cc06402a014807c03c01d00a80500220100078038014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xdffdf4de9ddbd99d8dd85d7bcf1ce6cdbccdc8bc7fc77c6dbb3ba8b94b87b79b68a539d49038f48e789384683a82d81f80c7f975073a7267137006ee6dc6c46b166a59d58f58253e4fb4f24e74dd4cf4c04364244144043f53e73d93c33b437932d3203133052f52e72d72cb25a24823822821a2081f91cd1c21ba1ae1a019118315614613512911a1090f30e80b306906806005f05505405303303202a02901f01e01d01501401101000f00e00a009008007006005004003002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x9119069028fa8c88bb8b78ad85284984383b8097ff7f87ee77176b76275c75474966f60e57656e56052b4f34ef4e54e14d54ce46545844943c43042741a40c4033d533d33232a2f22ba2b42af2a529f29522c21d2102031f71eb1e21d31ca1ac18b18718117c17717116a16413d13713112d12912411e11010c10a1051000fb0f60e50e00d80d20cd0c70c00ba0a806406305b05a05004f04e03303202a02901f01e01d01501401101000f00e00a009008007006005004003002000 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x105681f40c2044fb17ccbe2defaebf756ba85d24e407173889c26d896c1b5e9ae4d6c6b1afbd6a4a5f527a8e53aa97f4b72571296939496a1c50bc84841a207d0147f53ed1f10ebc66032a990cbd45a92cd1634afc5712b313489864b0251125090a47222e91388023ad1cd8e306f636c1b10d406762b81538a4c50226f12d09204201fd0f707803a21c30dc86182ec1640a7850026011108083200d606a03101840ae05602a80cc06402a014807c03c01d00a80500220100078038014009004001c00c005002000c004000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x87a86e86b8688488418398367f77ef7eb7e57ca7c37be7b878a78678278177d7786d066b5cd5c55b957d55054754053452d5264c94bf4b14a749a49048647746b43139338b37f34331630b3042fc2f52ec28f28527726a25f25624c23a2302091e11d91d01c81bf1b91b41ad17016b16515f15714e14913212d12812211c1161101010f90f10ec0e60df0d50d00b306906806005f05505405303303202a02901f01e01d01501401101000f00e00a009008007006005004003002000 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x442a1c90a283fc19209903c8123efdf4ef977bfbae1d6ceab747ba11cf2e6e71cb8ddc58e10702b7e9bdec7a60eb00d7dcbea5302961448a11496248520489e43da1c50ce8454071f70f8c7b33789a64cf866132718c8c425ed2cb95ecaca5542a31464a104f9275136c9a44c025692088be4502220d8869e33c1948c5c5c62c215c0a9450226f12e88d044420e0f0070c3721ad0cb058c2a2120087035c19207002e016c0b005702b010c0720380130090046021010007c03c014007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb96dc6ad6f6b5b555a56cff636b0dd6eeb735aaac7d5e27ff3fd9f04ee27573929bd4c126032e69604aba51f277695a98944ea134dca4c92188e746823090c884241820810127b53d29e5ca5c4f326f92147fc3d81d98e7071c3301870bf05d82d514089c44c623910407e83d81dd0eb87403761ad0d3067832218a0b985b02ca1600ac854829614409e84d025a11307e83dc1b40d503d81c00bc05c02d81600ae05602180e004c024011808003e01e00a805002200f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xef3dd7b4767ecbd8fb0f54ea5d1fa3744e85d039071fe37c3b8670ae11be37bef5ddbbaf74ee7c8d696ccd93af34e293511a033ea63cb394b272474608b314ddbbab74ae25a6b3e654c6d8b2ec5b6b39622b952aa414626e45086d039f13d877ce59bc35e690ca1872ec5bcb49632b8548a393c26248c8c0ea19e3185189b0d61902a0520a21382684c07c0d8130240460800f81e02a0500880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (embedding (N := 44310) record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0xa2b44a8650ba1341e81cff9f93da7acf29e13ba6f4dd9b735a6a4d199d31e634c49812f65dcb9878ed5d4ba5728db5b2357698d219431c62ac3d812e45c0b79362604b892d10a164127f0fc9db3a2724e09b833665cca9822ba550a593d2724d09391d232448839021ea3cc788ed1d43906f8db1b0340648b61522984a0920d61882905009e1302584a07a0d8130240460800f81e02a0500880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (embedding (N := 44310) record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x834c19204501e80b4021feefc47dfbdf5ef2f717b1bd49d70eb6755ba3dd08e7973738e5c6ee2c7083815bf4def5f72981448a114ec25ad29092c48aa40913c87b438a18108a7dc3e31ecccc263231097b4b2e57b2b29550a8c4f926d934898a4ad22f91408884011cd8dec6c433c1948c5c5c62c215c0a9c50226f11a088841c1fd0f707803a21c30dc86a432c15109004441ae0c903d81c00bc05c02d81600ae05602180e004c024011808003e01e00a805002200f007003401600a004802000c005002000c002000 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x93525e4949191d22e444849072023fc7b8f11d22fc5e8bb16a2b45389f10e2143f8790e61b433796d71a734a688c8d8e31861cc21792ed5d2b8d6cabb56cac921a354608a1031ff3f67c8f61d73a673ce49c034a684cf1802ac530a29362644b88f918226430808fb1d83a4738e31be36c6b8d219c320608ab13e268448860cc1842905009e1302584a0780d8130240460800f81e02a0500880f01c0340580a0120200300500800c00800 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record007_frame005_links_0000 record007_frame005_links_0064)
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18d2c5e6267105869c1160867ff3fa9eecf0a75f3969b94c125fb2e2965cada52f26f697297d4729b649aa43d1d48cf45822750c8842418202cfb47b33d19e58a5650524110047b63b61cd8df06d23301870bf05ae2a613f89bc4c423910407e83d81dd0eb87403761ad0d3065830417c0b305802b21520a5851027a128090846021410307e03dc1b60d403d81ac0d406203081600ae05602180cc06402a014808003e01e00a805002200f007003401600a004801c00c005002000c004000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x110087dc37e1a90c4847421dd70eb5753ba79d0ce7b73338e5c6ce2870fb81dbf8de75f7a97d4709d54b7252d25a914476a35d13c87b438a11d0147da3e21ec8cc06422f51668afc5662a994e4a564f926d934895e48522e91388864011cd8dec6c433c1948c5c5c62c215c0a484b424910787f43dc1e00e8870c3721860bb059028013008f84441b00c803d81ac0d406203081600ae05602180cc06402a014808003e01e00a805002200f007003401600a004801c00c005002000c004000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8b28b08aa8a489e8918907f47f17ed7ea7e07dd7d67c77c57c07bd7b37af7a96d05cd5b857d5475345265175084fb4df4ce4c94b049047746b46539337e34330b2fc2ec2dd2cb2c22a229428f27625623a23022b2091d91c81b91ae1a81a018817717016414e14a13112d12812211c1161101010f90f10e60df0d80d50ba0b307906906806005f05605505404303303202a02902001f01e01501401100f00e00d00b00a009007006005004003002000 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x149ca43508281936c9aa4c666072b4949c98649cd576933461a14d055582a89288936470a34d1988c645e22dd1608aa451226512488d3939ad0d2267232e9748abe53c28e94209904c125d12cc95a4a624e925892248a24091f48ea46f2358c6460c29913d09ac4b023c116886841c1e40db065c3101750ac852826e12b08083e01e00e9071036c1a807003581a80c205c02d80e407003501980c80540290130090046014007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x110687c423e0ff06e8314092032fc97debdfdee8c7c61030197e0beb52fa94925891e450a1f90e486a42220dd0448123fb9f64f867b43789a58cf266032897a8b2e57b2b29558a3850b27e13b49bc4d325f92b094a49723f91d08b844d2228d886a82e31610ae054a28113789604922100f0070c3721a80c305d82c6151090844c1fe0f2072835818e07003581a80c205c02d80e407003501980c80540290130090046014007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa5ba53a23a1a9f39eb9d39ca9ab99f98197a7ad78777c77276f67166a5b65af56e56055b55654c54754053a53252852151d47b43842140f4013ae36c3573423343073002f92f22eb2e62de2d72d22cb2c32be2b52af2ac2041f71bc1ae1a819e18f18617917015813c12e12811e10d1070f90f00d80cf0c90c30c00bd0b707006b06a06105c05b03903803503303202a02902602402301400f00e00b00a009008007005004003002001 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x296d4aba3cd17a7a13c29cace0644721c8fac7722bf1518944455ac0c8d63cb1958a0c3c57da8a1428a004f5a75d35e9624ae255529a94649fa4e126292a491a47122290a483a4011f28f2473a3811b277d34f9a30cf065f324978ca3050427993849a24c4259128091c47d236913487643821410608103e91ec8f246e82a914a8a104e426212a890c46221f10707f83bc1cc0e486e43521990bd05a82b41570a8052428413b09a04ac24811f08c044421610307e03d41e40ec07303801b40d404a024c11c08d04601c40e006b03501a4054029012008c04401500a003c01c00d } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame001_links_0000 (interval_append _ 64 128 138 record010_frame001_links_0064 record010_frame001_links_0128))
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x96296095e95994b94894594092792692592191891591290d86582281a81480f80875d6e46d26c66bc6af6755ec5dd5cd5bd5ab59959058858057857056255a55754e54653e53152a52247b3f23e33d33c33b136f2f62e42d82ce2c12b62ad2a529d29528d27f27727426b26325b24e24723f2201d81d01c91c31bd1b81b11a91a219a19118517e17a17216a16315815014914613f13713012811f11310c1081000f80f10e60de0d70d50d10cd0c90c50c109409308e08d08c07107006b06a06902a02902402302201501400f00e00d } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame002_links_0000 (interval_append _ 64 128 138 record010_frame002_links_0064 record010_frame002_links_0128))
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x89e2588e2187a1b862158521384a1183a0b8220579dcf731ca725c66d59d6699865d9461d6e5b16a599625815e5715a5615654d515414e5314a51d4550d314611645110431033ace8398e5388df374db364d7354d2340cf334cb324c6310c22e8a227c9d2709925894248902388c2248721884208801f47b1e4781d8741c8701b86b1a468198641885f1745b168591605715855104400ec3a0e42c0ac260942405c160441003c0801c0200400 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (embedding (N := 44310) record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame003_links_0000 (interval_append _ 64 128 138 record010_frame003_links_0064 record010_frame003_links_0128))
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x8ca318c22f8ba2d8b22b8aa298a22789a2589223856027fdfd7f1f97b5da75dd5751d171db36c1ae6a9a46859e66d98655926358a6258660d805ed795d96a559535454d51d3f4b12949d2648d204751a45d144450c42508415023fcfa3e0f53bcdc364d7358d3340cd328c7310c12f0b92e0b52c8af2a8a8294a42849e26c98254902348c2248620c7e1f0791e0771d8751d073190631785d170511404b128490a82909023088150500f0380d } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (embedding (N := 44310) record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (embedding (N := 44310) record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (embedding (N := 44310) record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (embedding (N := 44310) record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame004_links_0000 (interval_append _ 64 128 138 record010_frame004_links_0064 record010_frame004_links_0128))
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x8ca318c22f8ba2d8b22b8aa298a22789a2589223856027fdfd7f1f97b5da75dd5751d171db36c1ae6a9a46859e66d98655926358a6258660d805ed795d96a559535454d51d3f4b12949d2648d204751a45d144450c42508415023fcfa3e0f53bcdc364d7358d3340cd328c7310c12f0b92e0b52c8af2a8a8294a42849e26c98254902348c2248620c7e1f0791e0771d8751d073190631785d170511404b128490a82909023088150500f0380d } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (embedding (N := 44310) record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (embedding (N := 44310) record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (embedding (N := 44310) record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (embedding (N := 44310) record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame005_links_0000 (interval_append _ 64 128 138 record010_frame005_links_0064 record010_frame005_links_0128))
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
def record010_frame006_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x9ea789da749c66e9ae6899e66996649865e96e588ea2287e1d87219821f07b5eb7a9e7769c16f9bc6e1b36c1ae6ada8695a26759a6659664d906318a621765755a5615453d454b52a4a1274912147d1c4651644d0e42d0a41d04404fd3ecf93c4d9358d434cd0334cb320c5308bf2e8b72d8b32c0ad2a4a7294a42889f27099258912388d22887210801f87c1ec7a1e4781dc76188611705b1684d13047118450a82909023088150500f0380d } : Fields).get c.val)
theorem record010_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record010) (record010.maps 6) (record010.inverseMaps 6) record010_frame006_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (embedding (N := 44310) record010) (record010.maps 6)
      (record010.inverseMaps 6) record010_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame006_links_0000 (interval_append _ 64 128 138 record010_frame006_links_0064 record010_frame006_links_0128))
theorem record010_frame006_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 6 :=
  of_group record010 6 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record010_frame006_indices record010_frame006_graph record010_frame006_links
def record010_frame007_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x2bd578aed5d2b2d63ac35829d539a6d4d292d24a43482654ad94b27a4d4958d30c61542183904e003ba768ea5cf39470ee01bd3756dedadafb566a8d35a3b41670cd197b07582ae958aa5536a09252424768d51622443885d08a0d4107ecf99f13d478cef1d53a2730dd98a3085f8bd9782e85b8b49622b6554a494027c4dc9892a23c464899102164107e8f71e23946e8da1a6330630ba16a2bc568a71402744c8951042043e07b0f419c330620c21801482804808c1101502803c0700d } : Fields).get c.val)
theorem record010_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (embedding (N := 44310) record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (embedding (N := 44310) record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (embedding (N := 44310) record010) (record010.maps 7) (record010.inverseMaps 7) record010_frame007_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (embedding (N := 44310) record010) (record010.maps 7)
      (record010.inverseMaps 7) record010_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame007_links_0000 (interval_append _ 64 128 138 record010_frame007_links_0064 record010_frame007_links_0128))
theorem record010_frame007_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 7 :=
  of_group record010 7 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record010_frame007_indices record010_frame007_graph record010_frame007_links
def record010_frame008_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0653.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0653.count (({ width := 8, code := 0xe7e6e5e4e3e2e1e0dfdedddcdbdad9d8d3d0cecdcccac7c4c2c1c0bebdb9b7b6b4b2b0aeadacabaaa7a5a4a2a09f9d9c9b989492918f8d8b8886858482817f7e7d7c7b7876757371706e6d6c6b6866656462615f5e5d5c5b5856555351504e4d4c4b494847464542403f3d3b3a38373635343332313027262322211b1a1716150f0e0b0a090605020100 } : Fields).get c.val)
theorem record010_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (embedding (N := 44310) record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (embedding (N := 44310) record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (embedding (N := 44310) record010) (record010.maps 8) (record010.inverseMaps 8) record010_frame008_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (embedding (N := 44310) record010) (record010.maps 8)
      (record010.inverseMaps 8) record010_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame008_links_0000 (interval_append _ 64 128 138 record010_frame008_links_0064 record010_frame008_links_0128))
theorem record010_frame008_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 8 :=
  of_group record010 8 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0653
    Papers.RationalityTen.SharedFrameCatalogue.group0653_facts record010_frame008_indices record010_frame008_graph record010_frame008_links
def record010_frame009_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x2411f8f476391b8d46631178b4562913894461d0b84c1e0b0380bfdfcfd7e3edf4f87b3d1e4f0773add0e57137db2d56a349a0ce64b1584c15f2ed72b75aacd64b1582bd5cad5529d48a14f2652c9549a451e8b44215088341205007f3f1f0f4783b1d0e26f371b0d4683298cc2602f170b4582b150a65228138984a2491c8c43200f47436190c4602f170b4582b150a434190c05c2c110803c1c0d } : Fields).get c.val)
theorem record010_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (embedding (N := 44310) record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (embedding (N := 44310) record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (embedding (N := 44310) record010) (record010.maps 9) (record010.inverseMaps 9) record010_frame009_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (embedding (N := 44310) record010) (record010.maps 9)
      (record010.inverseMaps 9) record010_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame009_links_0000 (interval_append _ 64 128 138 record010_frame009_links_0064 record010_frame009_links_0128))
theorem record010_frame009_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 9 :=
  of_group record010 9 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record010_frame009_indices record010_frame009_graph record010_frame009_links
def record010_frame010_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0x24d2591c8a371a8c45e1b0c8542605017fbf9daeb753a5d0e772b8dc4e17037dbcdc6d361acd4693419ccc6532188c1602f978ba5b2cd64b1572ad52a752a8d44a15027d3c9d4da652e9549a411c8d45a250e8441205007f3f1f4f87b3d1e0ec74391c0da6b351a0cc643097cbc5d2d964ae5529944a04f2692c9247231148842200f878391b0d46833190c4602f170b4381b0d06430110803c1c0d } : Fields).get c.val)
theorem record010_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record010) (record010.maps 10) (record010.inverseMaps 10) record010_frame010_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record010) (record010.maps 10)
      (record010.inverseMaps 10) record010_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame010_links_0000 (interval_append _ 64 128 138 record010_frame010_links_0064 record010_frame010_links_0128))
theorem record010_frame010_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 10 :=
  of_group record010 10 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record010_frame010_indices record010_frame010_graph record010_frame010_links
def record010_frame011_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0248.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0248.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0248.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (embedding (N := 44310) record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (embedding (N := 44310) record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (embedding (N := 44310) record010) (record010.maps 11) (record010.inverseMaps 11) record010_frame011_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (embedding (N := 44310) record010) (record010.maps 11)
      (record010.inverseMaps 11) record010_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame011_links_0000 (interval_append _ 64 128 138 record010_frame011_links_0064 record010_frame011_links_0128))
theorem record010_frame011_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 11 :=
  of_group record010 11 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0248
    Papers.RationalityTen.SharedFrameCatalogue.group0248_facts record010_frame011_indices record010_frame011_graph record010_frame011_links
def record010_frame012_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0247.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0247.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0247.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0247.localPairCheck (embedding (N := 44310) record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0247.localPairCheck (embedding (N := 44310) record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0247.localPairCheck (embedding (N := 44310) record010) (record010.maps 12) (record010.inverseMaps 12) record010_frame012_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0247.localPairCheck (embedding (N := 44310) record010) (record010.maps 12)
      (record010.inverseMaps 12) record010_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame012_links_0000 (interval_append _ 64 128 138 record010_frame012_links_0064 record010_frame012_links_0128))
theorem record010_frame012_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 12 :=
  of_group record010 12 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0247
    Papers.RationalityTen.SharedFrameCatalogue.group0247_facts record010_frame012_indices record010_frame012_graph record010_frame012_links
def record010_frame013_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0153.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0153.count (({ width := 9, code := 0x2391b8d46631178b456291389446210f87436150782c0e02ff7ebedf4f97c3ddecf4793c1dcec7539dc8e16f36daad16833998ca62b057ebe5dae16cb4592c15eae56ab156aa53a91429e4da59269248239188842a0d0481401fcfc7d3e1e8f0763a1c8de6d361a8d06631984c05f2e96cb2572a94ca4512793496492411c8c43200f47436190c4602f170b4582b150a434190c05c2c110803c1c0d } : Fields).get c.val)
theorem record010_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (embedding (N := 44310) record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (embedding (N := 44310) record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (embedding (N := 44310) record010) (record010.maps 13) (record010.inverseMaps 13) record010_frame013_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (embedding (N := 44310) record010) (record010.maps 13)
      (record010.inverseMaps 13) record010_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame013_links_0000 (interval_append _ 64 128 138 record010_frame013_links_0064 record010_frame013_links_0128))
theorem record010_frame013_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 13 :=
  of_group record010 13 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0153
    Papers.RationalityTen.SharedFrameCatalogue.group0153_facts record010_frame013_indices record010_frame013_graph record010_frame013_links
def record010_frame014_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0148.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0148.count (({ width := 9, code := 0x215098441e0d058240e0501803fdfcfd7e3edf2f77abcde2ef773b5d8eb753a5d0e672389c0de6e365acd36833592c76330d80bd5cadd6ab4592c15cac552a14ea652a9146a24fa71329649a3d1a8c44a19067f3e9ecf4793c1dcec753a1c8e06e361a8d06733190c4602f174b85b2c95caa532893c9c4d259248e452210c84401f0f074381b0d46833190c4602f170b4381b0d06430110803c1c0d } : Fields).get c.val)
theorem record010_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (embedding (N := 44310) record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (embedding (N := 44310) record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (embedding (N := 44310) record010) (record010.maps 14) (record010.inverseMaps 14) record010_frame014_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0148.localPairCheck (embedding (N := 44310) record010) (record010.maps 14)
      (record010.inverseMaps 14) record010_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame014_links_0000 (interval_append _ 64 128 138 record010_frame014_links_0064 record010_frame014_links_0128))
theorem record010_frame014_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 14 :=
  of_group record010 14 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0148
    Papers.RationalityTen.SharedFrameCatalogue.group0148_facts record010_frame014_indices record010_frame014_graph record010_frame014_links
def record010_frame015_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0147.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0147.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0147.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0147.localPairCheck (embedding (N := 44310) record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0147.localPairCheck (embedding (N := 44310) record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0147.localPairCheck (embedding (N := 44310) record010) (record010.maps 15) (record010.inverseMaps 15) record010_frame015_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0147.localPairCheck (embedding (N := 44310) record010) (record010.maps 15)
      (record010.inverseMaps 15) record010_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame015_links_0000 (interval_append _ 64 128 138 record010_frame015_links_0064 record010_frame015_links_0128))
theorem record010_frame015_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 15 :=
  of_group record010 15 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0147
    Papers.RationalityTen.SharedFrameCatalogue.group0147_facts record010_frame015_indices record010_frame015_graph record010_frame015_links
def record010_frame016_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0145.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0145.count (({ width := 8, code := 0x898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record010_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0145.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0145.localPairCheck (embedding (N := 44310) record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0145.localPairCheck (embedding (N := 44310) record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record010_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0145.localPairCheck (embedding (N := 44310) record010) (record010.maps 16) (record010.inverseMaps 16) record010_frame016_indices (Fin.ofNat record010.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record010_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0145.localPairCheck (embedding (N := 44310) record010) (record010.maps 16)
      (record010.inverseMaps 16) record010_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record010_frame016_links_0000 (interval_append _ 64 128 138 record010_frame016_links_0064 record010_frame016_links_0128))
theorem record010_frame016_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 16 :=
  of_group record010 16 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group0145
    Papers.RationalityTen.SharedFrameCatalogue.group0145_facts record010_frame016_indices record010_frame016_graph record010_frame016_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (Fin.cases (record010_frame006_supported hcells) (Fin.cases (record010_frame007_supported hcells) (Fin.cases (record010_frame008_supported hcells) (Fin.cases (record010_frame009_supported hcells) (Fin.cases (record010_frame010_supported hcells) (Fin.cases (record010_frame011_supported hcells) (Fin.cases (record010_frame012_supported hcells) (Fin.cases (record010_frame013_supported hcells) (Fin.cases (record010_frame014_supported hcells) (Fin.cases (record010_frame015_supported hcells) (Fin.cases (record010_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x9af4d1a6593169544a1e4e325e8a044b22190f484cc2020c304a6abb429a08cfd67ab3b9704ab0550aa3542c94449aa4851de8e8470a3691a68cc463a3011528a244ca24911c7273391978c966393141748a3a50927b13909a64c826092e89664ad253127492c491245120c8fa47523791a480c3191828bc45722a914c8a284f426b12b892043a20e0f0875838c1b60d3865c3101740b284e82560fe07b83c01d20e206e03500d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe08e01de8ddada7d9fd84d7acfacf3cdacccc99c91c76c6cabfa55a46a39a28a149819038f68e98957f77e47d379c7937837727637537467326f06de6c36b06aa61959d58c57f57056253e4bd4ab49d4904804764704634554474394204104073f83e93db3c23b33a337a2e72da2ce2a029628627526725a2452352091fa1ca1c21ba1ae1a019118316f16113712b0fb0f10e60d90cc0c20b206906805a05903903803303203102a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x7e47e37d77d27b07ae7a379d75d75674a74572772171771068066065c65865264b6035ab5a259756450c5064fb4d64d14cc4c64c14bc4b84b249d49748f48948542a3d43c93bc3b23a538733132631e30f3022fa2f52f12ec2e62e12d72d12ce2c72c22bd2b62b22ad28a2132091fc1db1d51cc1c41b91b11a019617c17315214b14613e13412c1211121080ed0e50c20bb0b70b20ab0a509e06806705a05903803703203103002a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x835416a05f0207e2bed5f14f7b767bb05d3ee907283909c40e1163e2fc17d2bd35dd2e915d2a5f528a8ed3b692c48ea41518a8b3450a2410fc87243621550187f73ec9f0cf766f13301948c8062f30f17a8aca5572a214d8a5051c28593f09da4de26992fc9584a524b921c8e845c22690f48083621a98cf860c2f41718b4c5842b81520a404b624910687f43dc1e00e8870c3721a70ca05982a211e08783fc1e40e506c831c0d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x9ec9e89d79d19a899898897e91d9199078fe8dd8ce8bd8b47ad77276e7677607596da67166965861f5b65ae59d57c57556e56756055b55755053953252852151e47b40f4023f13e63db3ae34233532431930e3073002f92f22eb2e62de2d72d22cb2c52be2b52af2aa2802041f61eb1cb1c31bc1b51ae1a819d19317c17015514b14313c13512e12811d1130fc0f00d50ce0c90c30c00be0b706b06a05c05b03903803303203102a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xdf9df8df2dd9dcfdcadc1d92d91d8cd78d72d6cd62cebceace4ccbcc1cbccb3c84c83c7ec6ac64c5ec54abea5197f9068d98c68947f77e17d079b79078076f7607507377236c66b36a36195a057356453f4bd4ad49f47546d4604524444364214113c53b63aa3792e72d82cc2be2ac2a029628627526725a22821a1e71d91cb1c21ba1ae1a019118317116313712b0fd0bf0b406f06e05a05905705605505403903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame001_links_0000 (interval_append _ 64 128 130 record012_frame001_links_0064 record012_frame001_links_0128))
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x209504981e407a02b0077fb3e95f48f977bcbdc1ec4f5175c3ad9d56e8f74239e5cdce3971bb8b1c20e056fd37bd8f4bee571a981448a114ec24b123490246122c113c88d43da1c50b68453ee1f18f666f133098c8c425ed2b29564a8c51928413e49d44db269130095a45f22811108023621a88cf06523171830bd05c62d31610ae050226f11a088841c1fd0f707803a21c30dc86a432c1660a884801ae0c903881c00b805b02c81600ae05601c80e0048023010808003e01e00a805001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame002_links_0000 (interval_append _ 64 128 130 record012_frame002_links_0064 record012_frame002_links_0128))
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x2f378bbddaeb74b9dcae370b7dbadb6cb4da2cf66b2d92c762b0d82bf5eaed72a952a2d02793a9b4c25f2d94496451f8e46a31158742e12fe7cbd5e6ef74ba1cce16f36db0d569b459cc7623095c9b4ca612e964a2451c8b4421906823d9e0ea74391bcd86933188be5a2c9508e441e0ec6833188c05e2e1409c401f0e870361a088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame003_links_0000 (interval_append _ 64 128 130 record012_frame003_links_0064 record012_frame003_links_0128))
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0149.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0149.count (({ width := 9, code := 0x2bf5eaed72b75aacd62af56aad52a752a7d3a9b4ca5d2a9348a3d1a8b44a1d0a75389649e47218ec5e2d1487c32130681c05fefc7abc9e0e670b75b6d768b419cc96330d80bd5dae56caf562a93c8c45a29128843211027e3d9e4ec75371acd06732988be5c2c958a64e2692076381a8d05c2d158a85228128903c1d0d8683218088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame004_links_0000 (interval_append _ 64 128 130 record012_frame004_links_0064 record012_frame004_links_0128))
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0149
    Papers.RationalityTen.SharedFrameCatalogue.group0149_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0229.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0229.count (({ width := 9, code := 0x22b1489c4a231087c3a1b0c85c2a130882c12070280c01fefe7ebf1f6fa7cbe1e2f07438dc4e16f365b0d76b351a4d06733596c963b1588bb5b2d568b1562ad54a953a9546a150279389a4c25d187a3c9e0ee763a1c8de6c3499cc8632e164ac55299409a4a23910823c1d8d85a2b148a04e261289046220f8783a1c0d8683218088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame005_links_0000 (interval_append _ 64 128 130 record012_frame005_links_0064 record012_frame005_links_0128))
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0229
    Papers.RationalityTen.SharedFrameCatalogue.group0229_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2df96f8b6ddad6d53694b3f57debed5deadcd6a6b1d5779ffcff67c13b89d5ce4a6f5304980cb9a5812ae947c9ddc5ad2b59fa98944ea134dca39d1aa8c244421d90c885242120c10368093da9e94f2e60b29713cc9be4851d98e8471c3541a10cc063c30e17e0b9c5aa281138898c4721ec0f207743ae1d00e487083761b40d6869832218a0b985b02ca1600ac854829614409e84d025a11a08983f41b40d503881c00b805b02c81600ae05601c80e0048023010808003e01e00a805001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame006_links_0000 (interval_append _ 64 128 130 record012_frame006_links_0064 record012_frame006_links_0128))
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x90c90b9058f98f48f08e98c28c18ba8ac8a589f89684d84c84883a83782f82a8038027fe7ed7e77de7d76d066c5d057955a54f52c4cb4c04b249548f48347846c46545544640e4053fd3973403213162f329228627b25c25324a23d23522c21a20d1d51cc1c41ac17116b16516115d15715414f14914313d12d12911611110e10c10a1051000fb0f60ee0e80da0d40c40ab0a906a06905505405205105004f03903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame007_links_0000 (interval_append _ 64 128 130 record012_frame007_links_0064 record012_frame007_links_0128))
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x87687586d86786285e85a84484384083583182c8287f47f37ee7e47de7db7d87c77c67c27b77b17ad7ab7186cf6255ce5af5a258052551d5114ee4e84df4d94ce4c94bc4ae47946d4663eb3943723683462eb2e32d72b42ad2a229d29428f28227423c23222c2091b91b51ae1a81a019819018817f17717015f15714013713012d12812211c11611010b1060f30ee0d90b90b406f06e05a05905705605505403903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame008_links_0000 (interval_append _ 64 128 130 record012_frame008_links_0064 record012_frame008_links_0128))
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
def record012_frame009_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x91a459124390a419023f8fa3d8f23b8ea398da358d2338ca318c22f8ba2d8b22b8aa29856127e9ef7a9e7789d0735c96f5b96d5b16b5aa6a1a465d926397a5a95e56955529485153f4ed374cd2f4b12949118451103e8dc364d7354d3340cc320c4300bd2d4b22a0a32749a25c9323c8b21c831f8741c4661484d1003f0d8350cc320c4300a8290801f0741c06c1a0441003c0e0340c02c0a02408018050100300400 } : Fields).get c.val)
theorem record012_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record012_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record012) (record012.maps 9)
      (record012.inverseMaps 9) record012_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record012_frame009_links_0000 (interval_append _ 64 128 130 record012_frame009_links_0064 record012_frame009_links_0128))
theorem record012_frame009_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 9 :=
  of_group record012 9 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record012_frame009_indices record012_frame009_graph record012_frame009_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (Fin.cases (record012_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xe07e01df9df7df0de5dcfdcadc1da5d9fd92d90d8ad82d72d6cd62d51d49d3ecf9cf3cebce9ce2cd7cc1cbccb3c97c91c84c82c7cc74c64c5ec54c43c3bc30bb1ba6b9ab84b78b6eabda519809068937f77df7ce7bf7a879b79078076f7607507397256c66b361a5a053e4bd4ab49d49048047546d4604524444364234133c53b63792e72d82cc2be2ac2a029628627526725a2472371e71d91c21ba1ae1a019118315614613712b0c00b406005f05a05905805705605505402a02902402302202102001f01e01501400f00e00d00c00b00a009006005004003002001000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame001_links_0000 (interval_append _ 64 128 148 record013_frame001_links_0064 record013_frame001_links_0128))
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xa4a51e68bd45ca29d0e283b4129fbcea672b3819bfcdd66c334b99ecc9a625307978483a3eb1dc8edc74a3731a08cac5fe27712888ac44e20f0f286dc32e16509f849c209f50f9b7c5bdf1ee6f6a6b1b2415fca2b4d725852b29524a6251527c93749824a524491b489242d1d08e13bc1a64bc651828213cc9c24d125f12b093448823b919c8a64411f78f7c6e82a914a8a104e426212788f445621910407e03c81d20c005c02ac14f0a4050427413308f045c22010a06b83440c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame002_links_0000 (interval_append _ 64 128 148 record013_frame002_links_0064 record013_frame002_links_0128))
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xefdde7bb775ee3dafb0f5ceb3d3ba2f41e81cf79bf2fe55c9b8f719e2dbc376ee8dcfb936e6d3da1b27606bcd67acb576a9d43a774b690d17a1720e38c5d8970f616b635ca854cb91d15a274478850ee1ac2f85108a0dc14817011eebd770cced7baad548a754ba8d510a053ca724d49892ba4f444864fe1b2352688ce19231a61cbf9772e059cae95524e4788890d2104087e8f81ce3846e0d61562982e05b0ac1542a0530a41442802a052090118220420800f81e02a0500780e01a0300580a0120180280400600800800 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (embedding (N := 44310) record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame003_links_0000 (interval_append _ 64 128 148 record013_frame003_links_0064 record013_frame003_links_0128))
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x8a989f89d89c89a89188888187b86886685c85b85985484784183882c8288248057fe7fc7fa7f47ed7e57e07df7d47d27cb7c97c47bd7b47b27ad7a779f79877777477176b7697676d46815fc5a956051e51851150a5014fa4f34ec4e64df4da4d34cc4a749f43f3dd38a32b32331930e3042f92f12e92e22da2d42ca2bd28727c24c1ed1e51db1cf1c51bb1b21aa1a519d19618c17f14713d12912211b11510e1090f70f10eb0e50b50ae06005f05a05905805705605505402a02902402302202102001f01e01501400f00e00d00c00b00a009006005004003002001000 } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame004_links_0000 (interval_append _ 64 128 148 record013_frame004_links_0064 record013_frame004_links_0128))
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
def record013_frame005_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x8f91de3ac748e31ba344668cb1862f45d8b916a2b44e8971221fc3b87308a10c1e83b06e0ac0f819021febfb7ecfd5f93ef7d2f9df2be27bcf69e53c5784ef5dcbb470cd8d9a3115dcb2162ac157aadd58aad54aa854ea97524a3137268468820f09b435e6a8d319f336664ca18f312610bf1792c4578a712123a45c8890c2104107e8f81ea3c4758e519c328618c21782dc5a0ae14e2904f89b1042002b0550a013c2704d09812c2502a052090118220420800f81e02a0500780e01a0300580a0120180280400600800800 } : Fields).get c.val)
theorem record013_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (embedding (N := 44310) record013) (record013.maps 5)
      (record013.inverseMaps 5) record013_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame005_links_0000 (interval_append _ 64 128 148 record013_frame005_links_0064 record013_frame005_links_0128))
theorem record013_frame005_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 5 :=
  of_group record013 5 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record013_frame005_indices record013_frame005_graph record013_frame005_links
def record013_frame006_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xb8ddc22df96f5b6c5afed53694b3f587ac075f7af9d76eb875a9ac755deab153fa9650768173ff9fd4f767853ab9c94dea6533109824bf65c52cb9574a3e4ef25d92248c222d0fd875c31e1650a2715b4ad684a624db239d1a68c0456a269110876432214908483040ea02cf6a7a530714b89043b31cf8e306f23661aa0d0866031e1870bf05d22d714089c44721ec0f207743ae1d00e487083761b40d6869833a1960b985b02c01590a9052c28813d094048423411306d83540c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record013_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record013) (record013.maps 6)
      (record013.inverseMaps 6) record013_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame006_links_0000 (interval_append _ 64 128 148 record013_frame006_links_0064 record013_frame006_links_0128))
theorem record013_frame006_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 6 :=
  of_group record013 6 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame006_indices record013_frame006_graph record013_frame006_links
def record013_frame007_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x91491390c9099048ff8f48f08e98ce8cd8c28c08b98b58a589f89688788387d85885484d84b84684083782f82a81780e8038017fd7f67e77de7d77c87c27be77076a76675b75374d6cf66c5d157952b4cb4be4b04aa49e49548f48347846c46545744840e4053983402f229228427927126525c25324a23d23522c21c20f1d51cc1ac17116b16516115d15715414f14914313d13613011611110c10a1051000fb0f60e50e00da0d40ac0a905b05a05505405305205105004f02a02902402302202102001f01e01501400f00e00d00c00b00a009006005004003002001000 } : Fields).get c.val)
theorem record013_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (embedding (N := 44310) record013) (record013.maps 7)
      (record013.inverseMaps 7) record013_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame007_links_0000 (interval_append _ 64 128 148 record013_frame007_links_0064 record013_frame007_links_0128))
theorem record013_frame007_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 7 :=
  of_group record013 7 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record013_frame007_indices record013_frame007_graph record013_frame007_links
def record013_frame008_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x83705e09c1282103a0640980d00a003fe7fafedfcbf77e8fc5f73eb7d0f79ee3da7b2f59e9bd079cf31e4bc778af11e03bc770ed9da3b275cea9d039f73ce75ce39b6baca96929f4e29412624948e91120a3e4768e11aa3245a8a90da183bc6acbe95c2b0554a995029a528a39442824f89c93624e4908a0f31de3b0750e71c83846f0db1b0354680cd17c2ec5b8b616a2d0598b215e2b8568ac14828c2e05b0ac1542a0530a41442802a052090118220420800f81e02a0500780e01a0300580a0120180280400600800800 } : Fields).get c.val)
theorem record013_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record013) (record013.maps 8)
      (record013.inverseMaps 8) record013_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame008_links_0000 (interval_append _ 64 128 148 record013_frame008_links_0064 record013_frame008_links_0128))
theorem record013_frame008_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 8 :=
  of_group record013 8 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record013_frame008_indices record013_frame008_graph record013_frame008_links
def record013_frame009_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1003.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1003.count (({ width := 9, code := 0xcd6632d95ca64f2590c762f1387c36170983c0dfefb7cbddeaf378bbdd6e771b85bedd6db65aed367b2d92c762b057ab95bad566b157a9d1e752e90452251087c36170983c1607017f3f1e0ee743719cc2602f97abb5cadd6ab358abd58aa4f2712a8943a150882401f8f87a3c1d8e6713298cc05f2f174b85b2c15cac552813c82401d8e872381b8d86a291408c44211007c3c1d0a8501e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record013_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1003.localPairCheck (embedding (N := 44310) record013) (record013.maps 9)
      (record013.inverseMaps 9) record013_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame009_links_0000 (interval_append _ 64 128 148 record013_frame009_links_0064 record013_frame009_links_0128))
theorem record013_frame009_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 9 :=
  of_group record013 9 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1003
    Papers.RationalityTen.SharedFrameCatalogue.group1003_facts record013_frame009_indices record013_frame009_graph record013_frame009_links
def record013_frame010_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x92923e4548990d20e3fc7b8ef1c636c698d118e2f4588a713a254468850d21943085f0b214c2684908a0ec1982b0520840c81101a024027fafe1f23e37c4f85efbdd728d697babd51a9b1342654c69812ea5a4ae95128a4e4929191ba343e26dcc39662c457cae95a2ae550a894e296520a19402624b88f0fd1f23d87a0f11dc3ac740e51c437c6d0d7190314608c017e2f85e8bc1722e05b8b615c2b43005f0b41642c0570ac1542a02a052090118220420800f81e02a0500780e01a0300580a0120180280400600800800 } : Fields).get c.val)
theorem record013_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record013) (record013.maps 10)
      (record013.inverseMaps 10) record013_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame010_links_0000 (interval_append _ 64 128 148 record013_frame010_links_0064 record013_frame010_links_0128))
theorem record013_frame010_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 10 :=
  of_group record013 10 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record013_frame010_indices record013_frame010_graph record013_frame010_links
def record013_frame011_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0xb75b6d96bb55a6d167b3596c963b1586c15faf576b95bad566b157ab556a953a9546a14fa7536994ba55269147a35168943a1506813f9dcc24316853f5f6f87bbd1e2ef773b5d8eb74399b6d969b2178af56aa952a651a85409f4f275349846a2d107b3c9d8ea72379b4d86b351a4cc642c95ca85329144a04f2612c94492210c7238198c86230178b85a251207c3c1d0e06c34190a8501e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record013_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (embedding (N := 44310) record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (embedding (N := 44310) record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (embedding (N := 44310) record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (embedding (N := 44310) record013) (record013.maps 11)
      (record013.inverseMaps 11) record013_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame011_links_0000 (interval_append _ 64 128 148 record013_frame011_links_0064 record013_frame011_links_0128))
theorem record013_frame011_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 11 :=
  of_group record013 11 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record013_frame011_indices record013_frame011_graph record013_frame011_links
def record013_frame012_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0x9248e45219047e3d1d8e46631178b456291389446210f8742e15098441e0d058240e00ff7f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef773b1cce46eb6db2d76ab4da2cf66b2d92c762b096eb4582b546a250a813e9e4e26930964a249228f42a0d007f3f1f4f87b3c9dcea73389bcdc6c31180b85a2c158a8522713094481d0dc582b150a4502713094481c0d86832180b8582a14088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record013_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (embedding (N := 44310) record013) (record013.maps 12)
      (record013.inverseMaps 12) record013_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame012_links_0000 (interval_append _ 64 128 148 record013_frame012_links_0064 record013_frame012_links_0128))
theorem record013_frame012_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 12 :=
  of_group record013 12 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record013_frame012_indices record013_frame012_graph record013_frame012_links
def record013_frame013_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0151.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0151.count (({ width := 8, code := 0xb8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868583817f7d7b79777573716f6d6b69676564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a49484746454443413f3d3b393733312f2d242221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (embedding (N := 44310) record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (embedding (N := 44310) record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (embedding (N := 44310) record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (embedding (N := 44310) record013) (record013.maps 13)
      (record013.inverseMaps 13) record013_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame013_links_0000 (interval_append _ 64 128 148 record013_frame013_links_0064 record013_frame013_links_0128))
theorem record013_frame013_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 13 :=
  of_group record013 13 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0151
    Papers.RationalityTen.SharedFrameCatalogue.group0151_facts record013_frame013_indices record013_frame013_graph record013_frame013_links
def record013_frame014_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0150.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0150.count (({ width := 8, code := 0x939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0150.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (embedding (N := 44310) record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (embedding (N := 44310) record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record013_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (embedding (N := 44310) record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record013_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (embedding (N := 44310) record013) (record013.maps 14)
      (record013.inverseMaps 14) record013_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record013_frame014_links_0000 (interval_append _ 64 128 148 record013_frame014_links_0064 record013_frame014_links_0128))
theorem record013_frame014_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 14 :=
  of_group record013 14 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0150
    Papers.RationalityTen.SharedFrameCatalogue.group0150_facts record013_frame014_indices record013_frame014_graph record013_frame014_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (Fin.cases (record013_frame005_supported hcells) (Fin.cases (record013_frame006_supported hcells) (Fin.cases (record013_frame007_supported hcells) (Fin.cases (record013_frame008_supported hcells) (Fin.cases (record013_frame009_supported hcells) (Fin.cases (record013_frame010_supported hcells) (Fin.cases (record013_frame011_supported hcells) (Fin.cases (record013_frame012_supported hcells) (Fin.cases (record013_frame013_supported hcells) (Fin.cases (record013_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa4851ea8a743f9b0cd26637305955ca2a4c7250696b499a3ed18688b4299fecfc67ab3b962ab03578ab79594ab654b2a3d4fca6c4d4a65d30a9724af252925492348924011de8e8470a3691a68cc461a2f916e8b0455a29113a8964479a8cd0267232c9930c726282a714b0a3a50427b93909a64ba2569298940498248922890847b23a91bc8d235a1978c7061c2f316e8b2853227a135895849823c11688884141fc0f7078036c1970c405cc2d21590a504fc24e11908583f41f20f007483881b60d505902780e206201a00cc064031012809004602200580280120080028010006002 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame001_links_0000 (interval_append _ 64 128 140 record016_frame001_links_0064 record016_frame001_links_0128))
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xdc5b77686cdd5baa74f698d19a2b4167faf15d2b7569acb586ab553a9d52268ccd98f30a5f4ba95f2b253ca18c91762ac4f89310e1cc3585b09a0fc1882102a023fe7e8fc1f43e17b8f61ea3d0798d4da4b44678ce198b2a592af95daae552a894da834ec9c53625e4a892921a384668b9141c93786dcd91a4334640bb16b2d056cab14f29050c9c13325c4a08a9092043e87a8ee1ce38c6c8d219c320628bb1682c0550a7132224340590680cc1903104a090118220160280480800a01001802 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame002_links_0000 (interval_append _ 64 128 140 record016_frame002_links_0064 record016_frame002_links_0128))
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xcfe7b3b9ccde6b3398cbe5b2b94bd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (embedding (N := 44310) record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (embedding (N := 44310) record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (embedding (N := 44310) record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (embedding (N := 44310) record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame003_links_0000 (interval_append _ 64 128 140 record016_frame003_links_0064 record016_frame003_links_0128))
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
def record016_frame004_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0xbc5deed75ba5cee571b85bedd6db1d86bd5bacd5ea551a7d3287419f4ee7337994c65f2c93492431e8e46a2b148943e190a83c1205007dbe9f0f5793c5e0ef77399c8e37037dbcdc6b351a6d067b3998c660af978b95b2cd60ae562ad54a24ea6930954923d12874320d04813f9f8f87a3c9e0e872389b8da6c351a4ce653218cc4602f174b85b2b9448c3b1309448230f074381b058281208028100602 } : Fields).get c.val)
theorem record016_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (embedding (N := 44310) record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (embedding (N := 44310) record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (embedding (N := 44310) record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (embedding (N := 44310) record016) (record016.maps 4)
      (record016.inverseMaps 4) record016_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame004_links_0000 (interval_append _ 64 128 140 record016_frame004_links_0064 record016_frame004_links_0128))
theorem record016_frame004_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 4 :=
  of_group record016 4 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record016_frame004_indices record016_frame004_graph record016_frame004_links
def record016_frame005_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0xeb757a9d1e672f95c7e2f1387c1d6eaf51a5d1e87399bcce5b0d84c0dfaf97abadd2e56fb3592c35eae56aab54a953e994aa3d1285409dcea7135994c6612f97476371a8bc5a291180bf5f6f87abc9dee77137dbad96ab459ccc6532590bb5b2cd62ad54a9534964a2451c8b44219088240a00f6793c1d4e872379b4d6693419ccc6431184c05f2d14c903c1309448230f074381b058281208028100602 } : Fields).get c.val)
theorem record016_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record016) (record016.maps 5)
      (record016.inverseMaps 5) record016_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame005_links_0000 (interval_append _ 64 128 140 record016_frame005_links_0064 record016_frame005_links_0128))
theorem record016_frame005_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 5 :=
  of_group record016 5 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record016_frame005_indices record016_frame005_graph record016_frame005_links
def record016_frame006_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xcfe7b3b9ccde6b3398cbe5b2b94bd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record016_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (embedding (N := 44310) record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (embedding (N := 44310) record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (embedding (N := 44310) record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (embedding (N := 44310) record016) (record016.maps 6)
      (record016.inverseMaps 6) record016_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame006_links_0000 (interval_append _ 64 128 140 record016_frame006_links_0064 record016_frame006_links_0128))
theorem record016_frame006_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 6 :=
  of_group record016 6 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record016_frame006_indices record016_frame006_graph record016_frame006_links
def record016_frame007_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1082.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1082.count (({ width := 9, code := 0xacd62af56aad52a752a8d429f4e9dcea71369acd26330974b23d1d8dc6631178a44e230f83c1a090280c01fafc7d3e1ecf579bc5e0ef763add2e772b91c6e270b4da0cf6632d90c55dae16eb459ac15aa752a8d449e4da652e94492451e8541a05007c3c9dce46f371acd46732188be5d2e168ac532913c9c4b241188641200f87a3a1c0dc6a34180a4441b0a04c241107034180b0401c0c05018080200 } : Fields).get c.val)
theorem record016_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (embedding (N := 44310) record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (embedding (N := 44310) record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (embedding (N := 44310) record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1082.localPairCheck (embedding (N := 44310) record016) (record016.maps 7)
      (record016.inverseMaps 7) record016_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame007_links_0000 (interval_append _ 64 128 140 record016_frame007_links_0064 record016_frame007_links_0128))
theorem record016_frame007_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 7 :=
  of_group record016 7 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1082
    Papers.RationalityTen.SharedFrameCatalogue.group1082_facts record016_frame007_indices record016_frame007_graph record016_frame007_links
def record016_frame008_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa58a50a3aa2d9ee9ea9d59cc9aa99a98397c78d78778177c7767727697667607596a469968d68267a67365f65a64f6425e95de5d65ce5c25b85a459f59358957c57556e56756055b55354e54754053b53452d52651f42e41640f3fe3f23e63db36134d34233132531930e2f92eb2e62e12d92d22cb2c62bc2b52af2aa22620e2051fd1ed1e01d61bc1ae1a819c19718f18618016c16615d15413c12e12811c11710d1071000ec0e40df0d40d00c90c30c00bd0b80a609c07106203403303203102502402302200b00a009008005004003002 } : Fields).get c.val)
theorem record016_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record016) (record016.maps 8)
      (record016.inverseMaps 8) record016_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame008_links_0000 (interval_append _ 64 128 140 record016_frame008_links_0064 record016_frame008_links_0128))
theorem record016_frame008_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 8 :=
  of_group record016 8 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record016_frame008_indices record016_frame008_graph record016_frame008_links
def record016_frame009_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xc6b8cf17e2ec3785305604bef7daf4de09b335a684c99893025bcb495f29e24c458810f61bc3084f0920e4177c8f79eb3d079af1ddf3ba76aeb5d2b9f738e5dc7b886fededbab6f6ced8db035a6a6b856a2cf590b115f2b94ec9ad3425e4b09552723d45e8a912a17422825009f63e47b0f319f326634c417a2e65a8ab9502985089e1362664bc9211d234450820f81e43b0748e31ba364688cd190310600b81662c0558a712c21c3585e0640c41802f04808c110210160280480800a01001802 } : Fields).get c.val)
theorem record016_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record016) (record016.maps 9)
      (record016.inverseMaps 9) record016_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame009_links_0000 (interval_append _ 64 128 140 record016_frame009_links_0064 record016_frame009_links_0128))
theorem record016_frame009_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 9 :=
  of_group record016 9 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record016_frame009_indices record016_frame009_graph record016_frame009_links
def record016_frame010_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0989.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0989.count (({ width := 8, code := 0xafaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9c9b9a9998979695949391908f8e8d8c8b8a8988868584838281807f7e7d7b7a79787776757473706e6d6b6a6968656362605f5e5d5a585756545352514f4e4d4c494746454342413e3c3b3938373635333231302d2b2a28272625242221201f1e1c1b1a1918171615141211100f0d0c0b0a0807060503020100 } : Fields).get c.val)
theorem record016_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (embedding (N := 44310) record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (embedding (N := 44310) record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (embedding (N := 44310) record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (embedding (N := 44310) record016) (record016.maps 10)
      (record016.inverseMaps 10) record016_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame010_links_0000 (interval_append _ 64 128 140 record016_frame010_links_0064 record016_frame010_links_0128))
theorem record016_frame010_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 10 :=
  of_group record016 10 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0989
    Papers.RationalityTen.SharedFrameCatalogue.group0989_facts record016_frame010_indices record016_frame010_graph record016_frame010_links
def record016_frame011_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0987.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0987.count (({ width := 8, code := 0x8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record016_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0987.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0987.localPairCheck (embedding (N := 44310) record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0987.localPairCheck (embedding (N := 44310) record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0987.localPairCheck (embedding (N := 44310) record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0987.localPairCheck (embedding (N := 44310) record016) (record016.maps 11)
      (record016.inverseMaps 11) record016_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame011_links_0000 (interval_append _ 64 128 140 record016_frame011_links_0064 record016_frame011_links_0128))
theorem record016_frame011_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 11 :=
  of_group record016 11 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0987
    Papers.RationalityTen.SharedFrameCatalogue.group0987_facts record016_frame011_indices record016_frame011_graph record016_frame011_links
def record016_frame012_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0985.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0985.count (({ width := 8, code := 0xafaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9c9b9a9998979695949391908f8e8d8c8b8a8988868584838281807f7e7d7b7a79787776757473706e6d6b6a6968656362605f5e5d5a585756545352514f4e4d4c494746454342413e3c3b3938373635333231302d2b2a28272625242221201f1e1c1b1a1918171615141211100f0d0c0b0a0807060503020100 } : Fields).get c.val)
theorem record016_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0985.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (embedding (N := 44310) record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (embedding (N := 44310) record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (embedding (N := 44310) record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record016_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0985.localPairCheck (embedding (N := 44310) record016) (record016.maps 12)
      (record016.inverseMaps 12) record016_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record016_frame012_links_0000 (interval_append _ 64 128 140 record016_frame012_links_0064 record016_frame012_links_0128))
theorem record016_frame012_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 12 :=
  of_group record016 12 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group0985
    Papers.RationalityTen.SharedFrameCatalogue.group0985_facts record016_frame012_indices record016_frame012_graph record016_frame012_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (Fin.cases (record016_frame004_supported hcells) (Fin.cases (record016_frame005_supported hcells) (Fin.cases (record016_frame006_supported hcells) (Fin.cases (record016_frame007_supported hcells) (Fin.cases (record016_frame008_supported hcells) (Fin.cases (record016_frame009_supported hcells) (Fin.cases (record016_frame010_supported hcells) (Fin.cases (record016_frame011_supported hcells) (Fin.cases (record016_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x870c3661750ad82641060490197d3be71efef7453fa9a14c0a5851d289142295c49ca4b5248904476a35d13c87b438a16509283440f9a9cd3268833e19accc264e32218c8c425a92cd1634afc5712b3154ca905392959464a104f9275136c9a44b1251125071836c1b10d3c67a32918b8b8c5842b81528a5050226f12e891c46822210707803861b90d4066030c1760b4053c28013008f843812805802b81580aa04301c80a804202000f807803a010007803801a00b0050024010005002000c004000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa3551968a343d99a4cbe63330393c49d24c324e5772b1d566aa754629ed4d29824ada51d276920487a3f51c08d2465a30917a8b64579b1cd6e6a634a1a10cea65a32798f0c565722b11544a7e52f29014149f44e726b131c9804b925912b094a49724812246ae32c18c8c045e02da1638a644f426b12c093047822d10f88303fc1f00f106d832e1880ba85a42b214a09e04a423610d07f83d812805802b81580aa04301c80a804202000f807803a010007803801a00b0050024010005002000c004000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xe99e93e87e6ee03dfddf1dd8d92d8bd83d6bd53d4bd2c9c19a399496f9609518c68b48a989b88987985f84e83a8277f77d47c07ab79678176e6135fe5f35d75cb5bc54353352851f5115044ec4e44d64c749b48247746845944a43d36b35834d34133131f2fa2ea2d82ad2932862742652552462232132011f01e21d51cd1c41b51a818717816b15514313312311310407b06205805705605504302a02001f01e01d01501101000f00e00d00b00a009008006005004003002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x86b432a17109481f40c2044ff77ccbe2defaf527913c3ddb6a7f5342981474a24508a5fd2dc95c4a5a4e525a91448223b51ae89e43da1c50bc84941a207cd1066b3309910c646212d49668b1a57e2b89598aa654829c94ac9f24db269130c9624a224a0eb473638c1bd8db06c433d1948c5c5c62c215c0a9c528281137891c46822210707f43dc1e00e8870c3721980c305d82c814f0a004c023e11103d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xeb3abeaba8e8fa2e879fe6b99e6396e4f92e46edb9ee4b66d5b46afaaea7a8e9fa6e90a2a839f2739ba6b98a5c9524c7edf77d5eb799e1715c3705bf6f5bb6c1ad69da165d93645875fd785c5384d1304b529499174450b400fb3e4f23ace6384d4340cc324c5304bd2e8b62cca527c9923c8820c7e1e474140430e4380dc360d0270741c06c1a054110400f0380d02c0a02408018050100300800 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc4261b70c5828b6fdb0ad6f67faefd71eb77578aadd50aa26aa053ba989476a27509a52526a921487a3f51d48cf46222c113a86442120c103c80d3fd9fa4ad8543297141c9e64df20a90047da3db1e48ed87363901be0da466030e17e0ba85b22c715a883c4102010fd07cc3d81de0eb87403761ad0d306783301910c505e82e616c0b285802b21520a5851027a12f0940484230111085040c1f80f703d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
def record018_frame005_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x82181f81a8107e87e47df7d57c17c07b77a979b79778b5825735665555485404f04e84e04d94d04c54b24ae4a349a48047046645b45544843e37a36836234a3413382e92e02d82d12c62be2aa2a429a29227826625f25324a2402361cb1c51bf1bc1b71b01a419d19618417a17316b16615e15714b14313d13913312c12712311d1161070ff0f90f10e90e10dc0d70d407205c05205105004f04002a02001f01e01d01501101000f00e00d00b00a009008006005004003002000 } : Fields).get c.val)
theorem record018_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 5)
      (record018.inverseMaps 5) record018_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame005_links_0000 record018_frame005_links_0064)
theorem record018_frame005_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 5 :=
  of_group record018 5 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record018_frame005_indices record018_frame005_graph record018_frame005_links
def record018_frame006_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8a589f89b89386e86b86885b84183983682981e8188075e45d35ce5ba5af5a255054754053452d5265175135084fb4df4ce4c94bf4b24a749a3a839b39438037236831630b3042fc2f52ec2dd2d92cb2c22a229428f28527826a25f1e11d91d01c81bf1b91af1a81a018817717016b16615f15714814013713012d12812211c1161101081010f90f10ec0e60df0d80d507906005605505405304302a02001f01e01d01501101000f00e00d00b00a009008006005004003002000 } : Fields).get c.val)
theorem record018_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record018) (record018.maps 6)
      (record018.inverseMaps 6) record018_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame006_links_0000 record018_frame006_links_0064)
theorem record018_frame006_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 6 :=
  of_group record018 6 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record018_frame006_indices record018_frame006_graph record018_frame006_links
def record018_frame007_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0784.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0784.count (({ width := 9, code := 0xa3d1a8b44a1d0a83409fcfa7b3c9dcea731f8ec7233188bc421d0c854220d01803f9f8f87b3d5e6f1783bdb4d86bb51a6d265b258ec561b0578bb5cadd66b1582b958ab55259289248239188843210fa793b9d0e26e35998c8623097cba5b2c95caa4f261248842200f87a3c1a0bc502713094481f0c05c2c150a0401e0e0683014090401c0c050200c0400 } : Fields).get c.val)
theorem record018_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (embedding (N := 44310) record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (embedding (N := 44310) record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0784.localPairCheck (embedding (N := 44310) record018) (record018.maps 7)
      (record018.inverseMaps 7) record018_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame007_links_0000 record018_frame007_links_0064)
theorem record018_frame007_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 7 :=
  of_group record018 7 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0784
    Papers.RationalityTen.SharedFrameCatalogue.group0784_facts record018_frame007_indices record018_frame007_graph record018_frame007_links
def record018_frame008_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0724.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0724.count (({ width := 7, code := 0xf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record018_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0724.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0724.localPairCheck (embedding (N := 44310) record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0724.localPairCheck (embedding (N := 44310) record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record018_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0724.localPairCheck (embedding (N := 44310) record018) (record018.maps 8)
      (record018.inverseMaps 8) record018_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record018_frame008_links_0000 record018_frame008_links_0064)
theorem record018_frame008_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 8 :=
  of_group record018 8 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0724
    Papers.RationalityTen.SharedFrameCatalogue.group0724_facts record018_frame008_indices record018_frame008_graph record018_frame008_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (Fin.cases (record018_frame005_supported hcells) (Fin.cases (record018_frame006_supported hcells) (Fin.cases (record018_frame007_supported hcells) (Fin.cases (record018_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xeabea6e6fe63e15e10dd9dcddacd9fd6ed64b22b0baffaf4adbaccabc9c29a59969729639548aa88c87c85183d82a8138037f87ed7d77c37a879978477074f7387217096125fb5f05e15d45c85b952750e5014f04e14d34c44b64a749c49348547a46445c44d44042e41840a3f93eb34e3343222fd2ed2db2c72b72ad2a12932862652552462212111ff1ee1e21d51cd1c41b51a818717816b1411311211111020f50e80da0cb0c007106203903403303203102a02502402302201500c00b00a009008006005004003002 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame001_links_0000 (interval_append _ 64 128 135 record019_frame001_links_0064 record019_frame001_links_0128))
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x440a1e3098844c1aa0b4ffa7f4bf15f6af557a230517f4bf05f4af41774ba454129ad4c2a3d513284d2bc93b497241d1de8d9462a2cd14289043f21c90b484c41ba088ffe7ea3ea1ef8d0a6683301948c8262f30f1628adc5652ab9514a6c52828e142c9f84ed26f134c97e4b4252925c90e46c22e113487a38e1b70d8c68032c18d0c185e82e31698b0857029414089bc48a23211008303fa1ee0f007443861b90cc06182ec14d09f04b823a10f07f83c81ca0d606501c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame002_links_0000 (interval_append _ 64 128 135 record019_frame002_links_0064 record019_frame002_links_0128))
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x3aeeb7a9e9ba5e93a0e779ce6f97e534ed2345d0337ccb2dbbae8b96dab5ad2aa2a0a728ba127d9e6779d2729be6c9825d9564d8fe3a8d6317e9f67d1ef7a9e5781c06f1ba6c9ac699a06719a661966519260d805e5725a9635815d565314a927461124310640d003f8fb3e4eb398e134ccf32cc8314c12f4ba2d8b32949f264872087d1e0721b86b1a0601784c10c300ac2a0a42809c220842007c150300b02809020060140400c02 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (embedding (N := 44310) record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame003_links_0000 (interval_append _ 64 128 135 record019_frame003_links_0064 record019_frame003_links_0128))
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0785.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0785.count (({ width := 10, code := 0x291a428fa3a8da328ba2a89a2287a1a549424e92e47912418460c8260480a00799e0775d373dcb725c7715c3705bf6e5b76c9ad695a267d9c5c56d5ad6859160571434fd3d4ed384d5324bd2d4ad2949d254791c4591042d06411023fcdf364d6334c7304bb2e4b72d4b32c4a92909f2549223c8d22c8921c8520c811e4741bc641845e1705915c5514c4e134450f82c09c260942408c1e0741c06c150300b02809020060140400c02 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0785.localPairCheck (embedding (N := 44310) record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame004_links_0000 (interval_append _ 64 128 135 record019_frame004_links_0064 record019_frame004_links_0128))
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0785
    Papers.RationalityTen.SharedFrameCatalogue.group0785_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
def record019_frame005_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x523e8f3431a0ecd7a68d2fa971caa250f240913347da22d0a68233f19eacee578ab2956ca8f53f29b130a95e4a5248d224900477a3a11c28da469a3311868be45ba2c114889d44b223cd466813391978c986393141538a5851d28493dc9c84d326413049744b3256929893a498248922890647b23a91bc8d235a1978c705e62dd1650ae455229914509e84d624c11e08b44141fc0f707803ac1c60db069c32e1880b4856429412708c842c1fa0f707803a41c40db06a81c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record019_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 5)
      (record019.inverseMaps 5) record019_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame005_links_0000 (interval_append _ 64 128 135 record019_frame005_links_0064 record019_frame005_links_0128))
theorem record019_frame005_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 5 :=
  of_group record019 5 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record019_frame005_indices record019_frame005_graph record019_frame005_links
def record019_frame006_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa57a4fa28a1f9ec9e89be9b89a899897196678177677276e76676075968d67a67365a64f6425d65c25b859f59358957c57556e56756055b55354e54754053452d52651f42e41640f4023f23e63db36134d34233532531930e3073002f92f22eb2e62de2d92d22cb2c52bc2b52af2aa22620e2051ed1e01d61cb1c31bc1b51ae1a819718f18616c16615d15414b14313c13512e12811710d1070ec0e40df0d40ce0c90c30c00bd0b807106203903403303203102a02502402302201500c00b00a009008006005004003002 } : Fields).get c.val)
theorem record019_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record019) (record019.maps 6)
      (record019.inverseMaps 6) record019_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame006_links_0000 (interval_append _ 64 128 135 record019_frame006_links_0064 record019_frame006_links_0128))
theorem record019_frame006_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 6 :=
  of_group record019 6 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record019_frame006_indices record019_frame006_graph record019_frame006_links
def record019_frame007_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0754.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0754.count (({ width := 9, code := 0x69749a3d1687419fcf677399bcd6170782c05f6f779b458ec15bacd5e8b409ece26d34994c25d2c954a247218ec66291288439f2f579bc1dceb74355a2cf663298ec4613017cbc5d2e166b156aa54ca451a89408f45a250a83409fcfc7d3e1ecf476399c0d2673298cc4613017cbc5d2c958a64c251208c452210c843f1f0f06a291208c44211006c34190c048180b050241006028100602 } : Fields).get c.val)
theorem record019_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (embedding (N := 44310) record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (embedding (N := 44310) record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (embedding (N := 44310) record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record019_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (embedding (N := 44310) record019) (record019.maps 7)
      (record019.inverseMaps 7) record019_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record019_frame007_links_0000 (interval_append _ 64 128 135 record019_frame007_links_0064 record019_frame007_links_0128))
theorem record019_frame007_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 7 :=
  of_group record019 7 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0754
    Papers.RationalityTen.SharedFrameCatalogue.group0754_facts record019_frame007_indices record019_frame007_graph record019_frame007_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (Fin.cases (record019_frame005_supported hcells) (Fin.cases (record019_frame006_supported hcells) (Fin.cases (record019_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0xec74f9dc9e370b7fbdde6e76fb6d96c35d92c863b198ac4daed368964ae552692c92431f8ec72371a8ac4a210e86c32110581401fcfc7bbd1e0ec74b9dc8e26fb69aed26331588c05eaed70b659ab956a650a7936994ba55208d449fcfa7b3d1e4f073381b8b2582b8ec7439138984a24030140803 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xd2fcb7c47c45c2bc288c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476962b61d61360b5fe5f35e55d75cb5b454053052751c50e5014f14e14d34b64a749c49348547a46c45c44d43836e35b34e34433432230f2fd2ed2d32c72b72ad2a12932862752652551e21d51cd1c41b51a81981871781531411311211111020f50e80da0cb09906e05f04003602702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x3d1f37c9f23c7f1afabdaf2bbae9b92ddb52cbafabbadeb3abeaba9ea2a6e94a323d8ea378d2318ba2a8921e85dfd7e9f77cdef7ade576dd1715c26fdbb6ddb36b9a768197561555494f52d4750d3b4cd27491214791a4591243908408df36cd734ccf32cc72fcb72989f2609322c872087d1e0711a05011c370cc270982509023088120300b02809020060140400c02 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (embedding (N := 44310) record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x3df5b5ed4069c34d9a6a93548f24151e28e046622e9152895441a1e10c084941aa08d0248013f79f78fa26473191874c1c5ff2f79784ba45c22da14eca4e51228113d09ce4d726492f095049624211d08ce45a22610fc8644251a98cf464e3171840be45d42db1660af856229d14509e04da260129091c4741d60e306d435019c0c806142f216d0a9850025a12108a841c1f20e906f035013606e02f810006c0270130094048023011004801800b00500240100060028010006002 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00090
