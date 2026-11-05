module
prelude
public import GraphInputsSix0Part00046Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaa2a6da03a009d09bf9ae98796795e95594f94193692d91f90e9048e28d08c38b186c86677e77376575172c6cb68567d65a64f6005d95ba59f58956c55e54d52e52c5255194e54e04cb4b647042841c3e639436734730e2fa2ec2bb2b62b028e2892702592292112051e01d61c21b91b01a018f17416616115413e13412b1201070f40e80df0d40c70c40c10b60a709d08d08a07506405805503303102302201d01c01a01801500a008003002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8d18b98a388f85484d82d81780e7e57b57aa79a79577e77676b76073172f72c7287267236cc6965b459859058156b53952e5094ea4d64a949b48b4854383de3a338237e36a35433032631d30e2fd2de2d72cd2bf2a729c29027a27426124b20b1ef1e81c219818a17b16c15714e14513c13712811610b0f60e70cc0c40ae07907105a05805405304503b02f02d02a02402201e01d01901701000f00d00b009008004003002001000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a18ce3665b26d89bc315e76ed76bcb32d7f2ad3420a074efa7653089764b4657911287cc3a21870ae84f32e17eab0451da7713949a44c0246d1f88ad43320fcfd27ca3c99e10d825d028392a092c4702260f9c7903791990c2c56a29612f895449c24511f08c04442070f887903bc1d70dc86cc33c1980c505e82ca1580a8852828613d09a84a024211208283bc1d20d503f81cc0b805a02b015408e03b012008803c01d00d006403001700a804001e00d00580240100040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8da8bd8b08ab87b86c85184a82b81580c7e37b57aa79a79577e77676b76073172f72c7287267236586255e85b459759057f56953952e5094ea4d64a949b48b4854383de3a338337e36c35632631d2fd2de2cd2a729c29028a28127927425e24822420b1fd1ef1e81c21bf1a619818a17b16c15814e14613c13712a11610b0f60e70cc0c40ae07907105a05805405304503b02402201e01d01a01901801701501000f00d00b009008004003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x116988b41a1fc2fc379e3b45d76e8872fb949c78e096f03711b2cd4a646b1b98a8be95c92c3960aafd57b2b6d584a8753829654809ee4f4270934a95b49c2460e127003721b28d0666632097f8bf05df2e41630ae0510279134c99c4a524b91908aa43d20d10447e63d71c50da867a2fb16f8b6857c2b91590a5c50827212208e444e20b0f4877c3981c20dc869430c1760a8050826406703281880b403d01d80d006202200c805c02000d002000c004001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record006_frame001_links_0000 record006_frame001_links_0064)
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
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x235d1a48c5c6062cf15b8a8c4e225d11488141b60befe07edbf21f74f3b79b3c01ddeed175dba21cbee5271e3825bc0dc46cb352991ac6e62a2fa55eca8753829013e09e84e326a52b69383d31c6ce1e7073801b7cd8a6833331948c825fc2fc1764b8458c2b8155ca064e526992fc94a49724391908aa43d20c90447e23d51c50da867a2df15f0ae452e284139091047222710587ac3be1ce0e106e43501860bb054028413202d00f807a03c01d80e406803101780b405402200c805c02000d002000c004001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x2a754da9952aa4547a8d512a1540a7d49e92d16a2b44e88d06a0b4067f4ef9d93a26ecdb9b134a66cca98d29e4047a8eb1320d3fb7eaf95e53c4772ec5cbb8d620b8d6fadc5b2b41622ac53ea5548a774ea9b13324e4808cd0da0f40a7f0fa9ed3ca764e71c23706bcd419d3045e8b695428c50c9a93024a4508910a2003e47a8ef1d038c700d61a031c610bc0ac0f81e83c0760e41a03105e0b41502203205c0800d00800c01001 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x39cf33e63cb794f28e4bc7b8df16e29b5f676b8d6dacf58697d2ba2b42e64cbd94f23640c6b89f0fe19c21722c1d7badb5067c4cf98f2ce46c878f118e20432722d45a6345680cc991b0a5f4bbd752cf596b095ba9d51e9f12f24c4828dd16a2643a82d021f73d6790ed1c9352684c796c2be56ca61452744949091a222420810fb1ec3c4760e11b6334640c30b00f81e83c0760e41a03105e0b41502203205c0800d00800c01001 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11a98cc455a28b0e0828bf79f58f3975dba21c78e096a5323190ac69627b0457eeb925872c155faaf656dab0950ea7052ca9013de9e84e2269d2b693845c229912a883439a1a50728243fe1f90f9c7a93d31c88e2c70a3819ba4d9e68f3391970c905fd2fc1774b8c58c2b8143ca004f1271135099a4a724c91e88cc45721d10c48444182088fb87a438a1b50d4467a1ed0ef87403841b90d506182ec1500a104c811805a011006803201800b805402000d002000c004001 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x7cff95f17e07b6ef5d5fa6f34e03bcb6a6cad099532964cc858af0fe02b9b726e3dc3b776cac9587ae35baa8d46a754ae824f29792c25349e92721637c6089b0f61741f838f8df03db7aaf2de13a172adfdbdb626b0d31a1b24632bd175ae25b2b3d632b755aa794a28a4f89e93aa6b4c294d2321f4207f8fc14f2884e4971232324247f8ed1ca36c3f0560440680c81802e0540800d00800c01001 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x571ad356ea8d3ca1d4027cce096b2aa484858b912223c4287b0d617c1c7fefedfc3f67e6f99eebd9798f1ddabb2750e6dc437d6a6d25a133a660ca98cb0f608be178ae65c8b0d5eab8568ab951297524a1940a724e09b130a5349a8c114222438851082023f47c0f39e23b0750e69c33786ccd398f30c5f0bb8f71e03a8720df1b2340650be1722d03a0500440680c81802e0540800d00800c01001 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
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
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46a63311848b8455a28b13188ec3820e10517e5beb1e4eef8761baedc88e3c6e3b6d9918c84634b13d81cbf45c92be95e8ad155c29f94cea4c4f5259928690945422150e883c4139ff8fcc7d03d41e98e146e93679970bfa5f72ee9718b1056c2a2943c9e24d4266929c93246622b90e886242220c10447dc3d21c50da86a233d1770b345742a114309d04c223b11488203b61be0dd066c3121790a6051426a11c07c83b01be0cf04601d80e807103480b8058025011006803201800b805402000d } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x182f04607c097fafe5f9bef7baeeddbb8f712d9daeb3966ac2583ae55ba845069fb3d671cdb98323a454838f91a22fc56877025fd3e377eecdd739f730e29c0b796d6da19b32662ab81602bc564aa149a8e5069ad2f25549c8fd1ba2643e84907a0c412814fb1e638c6e4d69a631e600bb16e2c656ca91422724b48c10920a3dc768e51a633c638bc15a2a45289d0f81a8348670c00ac150240420680c81802e0540800d } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (embedding (N := 44310) record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb15b0eb07b02af6ae9ae0ad8ac4a6fa5fa24a199de9d298f98c93c9388fc8f77f17ee7de7ce7ad79f76b7016f96f16e86c66b269f66d62060d5e45ac5995895715675535455395245214b94a34894343f93f13e13ce3ab3a338c36b35333f33531d30f2f52ea2da2d42ca2bf2b72a528f25a24523222a2021ee1de1d01c61bc1b019b18f17f16114d14813312711c1030ff0f70e90d60cd0c40bc08607207106e06602d02c02502201a01901801701501000d } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x20e106d7e5bf21e4af127663b0dc9ae446ea370d724afa57a2b45570a7e533a9313de9e74e2269d2ae934480a1c906e8223f09f2cf587a63839c04dbe6c534399a8ca45fd2fb9774b8c5882b615149a64a524b91908aa43d21b90a08364141fc0f707283741ae0d0c5da2eb1660b285762a014409d84c625111e08a840e1f50ec87603781bb0da067831817c0a5851c26e11a07d03b41c00d003b01d00e206903301900ba05a01f00f007203101700b004a022 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x2cf59cb05602b4d66aa153a99d31a3746245c5289f11e1ec2783502dfbbf17d8f81e2bbb752e19bbb706c2d69a9350602bf97c2f15aeb295d2a353aa5d46a6e4ca95519a2543e841052024027f4fc9f33d2760d91a0318618b51692b6568aa1482864f49b1312544848a9112064087a0f21d238c6e0d31883085e0b31542904f0990ce1983205d0b816c2a85206e0d81a02d0580ac12822 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x38e715db9b6752ea1cab94b0d613bb775e86cc998d2ea56c9390b1e231c5d8ad11a1441b818f89e7bc8768eb5d2ba4692d199cb2c624c157b2de5acb355fa9e526a092f24f4948e519a2b4508850e2154107d4e71bf35a68cbf97e2e25bcb415d2ac53ca393e26e4b89191d21e438800fe1f43c8738df196324618b91582944f0990e41c4370670c818c2e85a07c0f01c83105c0b012822 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e83731b2758feabb544a11d046663318930c921970b635aa2ca1600a9f53b29313b89c64d226012388f8460a0ccffc7ec3dd1ea8f207843179880be85cc2b59508a304a824911c08983e81e20e345fe2ca15c0a184ec25c12b093c49424311a889c4081f60f3877c37e1bd0d886bc34e19c0c9062c30817e0bb05bc2c815b0a7853428213e09c04c0252122088043420c0fb07603941bc0d703b01d00e206903301900ba05a01f00f007203101700b004a022 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8ba44860daff27ebbf21e9af327893badd98ec375dba4dc9ae4471e3851ba8dc36d02bf15e8ad655ea9f94ce9e74aba4d120287241ba088fc27cb3d61e98e0e70136f9b14d0e66a32917f4bee5dd2e31620ad8545269929492e46422a90f48324111f88f5471436a19e8bc45c42d01608ae054a281137892046c2240dc866030c1760a104c81e40e506b031c0d206603201740b403e01e00e406202e016009404401900b804001a00a004802000e005002000c004001 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x22dd11b8343f85fb0fc379e3ccde48eec768bb0dd2ae8a7293911c2ce0b67cb219830bfe5e82bed5eaad455daa054d49ee4f4a70934a95d49d246114e88443920dd0447fd3f09f2cf587003419998c825fe2fb977cb905882b615149e84d626992d094a49723611908aa43d20d10487e63d71c68db45c02bf15c0a044de24611b08903d21dd0e607003721a50c305d829c142099040c1e40e506b031c0d206703281880b403d01d80d006202e016009404400d0050024010007002000c004001 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xaa154c29974b399dcba25a327c917c85628f13387d438a14508982840e5abcd21689b3f1746b945b5ad215e0ac951ba8a13fe9dc4c225751c48d446622dd1608a344da2511168813a69ce0e306f935099fcc985f82f1970cb4854c29513dc9704ab253126092248a23d91dc8e246921610707d03ba1ac8cb86062a814b0a244ee26b12d08f045a20b10007c838a1b30d306503101770ac852825011d08783c41d20e206d83500d205a01e80ec06803101700b004a02200d006002a00d0050024010007002000c004001 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8bbc5b2249119828bfc1fbcfac7a5bce5da2ec374aba29ca4e4470b382d90cc185ff2f415f6af556a2aed502a6a4f7a7a53889a74aea4e914e88443920dd0447fd3f09f2cf587a63841c00dc46c83419998c825fd2fb9774b8c5882b615149e84d626992d094a49723611908aa43d20c10487dc3d21c68db46a22f31700b4857e2b81538a044de24611b08903da1dd0e807003721aa0c305d829c142099040c1e40e506b031c0d205a01e80ec06803101700b004a02200d006002a00d0050024010007002000c004001 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa9da93a73a689e59ba9b299596b96292091b9038fa8df8d18b98b07b37837787666e86e36cb6b968c67962d6286116005d55c157056255b54754053352b52451b51748f48847045c42c4143f23c23bb3a439435f34b3252f62e82e62d92d22cb2bc2b82b22aa28e28827025922520d1f41c21ba1b41ab1a81a018f18616d16916014213913412c12812010d1070ed0e70e20ca0c30c00bd0b706905a03d03b03403102e02c02502201a01801500d00a009008007004003002001 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x23531988c0455a28b12d8704145fbcfda7d63ce5e6aeff7773b45d76ea37443949c78e24704b215822bf75c92bd950ea7052027bd3d09c44d3a56d2708a6441a1cd0728243fe1f90f9c7a93d31c20e006e23641a0cccc6412fe97e0bba5c62c615c09ec4d8269128892846e230914886242220c10447dc3d21c50da86a233d16f8af857229714209c8488239113882c3da1df0e807083721aa0c305d82a014209904081e00e306a031411805a01e80ec068031011007c03c01d00e006803201800b805402000d002000c004001 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (embedding record016) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8b3c4520bf0007f03ee9eb6f3b75dba4dd10e3c70a3825916c67626abd14fca674f827a138c9a94ada4e10e283440f9f78f907a63841c04dc46c834399a8bf85f82ec9708b185702ab941c9d24d2261928892846122910648223f11ea8e286d433d1710b04570281137892046c2240f5877c39c1c20dc86a030c1760a8050826408c03481680ae05602a815006202f01680a804401f00f007403801900b804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0xa9150292d17a2d446845069d93a6744d89a734a3f4778e5061fc3f2794f11dcbb172ee35ab341670c898cb105bab6968ac655aa853ba754d89992724046687508a043fc7d0f61d73986e0d79a833a608bd16d2ac520a112e246458889091f23d4778e81c63806b0d018e3085e07a0c6158298520a21401882f05a0a81101f03c0740e01902e0400680a0120200380400600800800 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x23531988ab45161c10517f83f79f58f4b79cbaedd26e8871e3851c12b9257dabd15a8abb53f299d3de9e84e2269d2b6938438a0d103e7de3e41e98e107013711b20d0e66a2fe97e0bba5c62c615c09a44a224a11848a443121110608223ee1e90e286d435119e8bcc5c42d21608ae054e281137892046c2240f6877c3a01c20dc86a830c1760a8050826408c03481680ae05602a815006202200f807803a01c00d006403001700a804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x3e7fcaf8bf03db77aeb9d5fa6f38e69c077bef2da9b3b65602b89702dbdacb1d606a8d46a754ae824f291f1ae2e439855071ebbd178eef5ceb906c4d61a6343648c65662b4554a4543a7a4ea9ad30a5348c87d081fe3f0778e99c73786d0d519931c5ecb916729e5109c92e246464848ff1da3946d87e0c6158298520a21401882203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x2b8d69ab75469e50ea054027cce39c12d656caa92121e42c1c7eefd5f73e57b8f51dabb2750e6dc437d65cc59862f55dcb915bab3556a814aa8f4e49c1362614a6935091ff3ee790ef9d439a70cde1b334e63cc317c2ee58cac14f2905009d12e248454869091ee3c0750e41be364680ca17c2e45a0740be1402684c0961281882203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2afd558a86d38e8d333b9744b464f922f90ac46e1f10e0838413a06ece15d1ae456d6b48576ab1946ea254ffa77130295a465a2d915e89a449a204e9a73c38c1be4d4a6832fc179cb865a42a814b894a49024491d88e045b22210b08303e81dd0d546543031780aa053028913c89ac4b423c11688344001f20e286d434c1960c405dc2b214a095047421e08c03481680ae05602a815006202200f807803a01c00d006403001700a804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame004_links_0000 record019_frame004_links_0064)
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
def record019_frame005_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x2ebdd1b8d70edbd99b1161abed6fadb52ea3d43a5f4aa9348b8a713e2543f84f069fbbf27d8f81e43bd70add9b7b606b2d41812fe5f6bcd6baca546a794ba8d4e299d1922443c83d049ff3f67d8f81e33a66b0cd98a3085b8b315f2ac53ca51422784bc9391e21c41c7f0f81da39c6c8d018c3045d8780ba1482784e09a1301682203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record019_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (embedding (N := 44310) record019) (record019.maps 5)
      (record019.inverseMaps 5) record019_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame005_links_0000 record019_frame005_links_0064)
theorem record019_frame005_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 5 :=
  of_group record019 5 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record019_frame005_indices record019_frame005_graph record019_frame005_links
def record019_frame006_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x3ebfc9f5fe73bc710dd1b8f69eb0d5993f2263dc1d802fd50d99531a5f4b092721631c5f8ad11a15c1f7c0f39e33b2758e91a5b4667acbd893055bcb6566abf542a5d2e24e4908dd1922744085d082003e0724db9a934060cbd9742d659cb095529c4ec9a92c232448859041fa3dc728dd19e320610840ce1682b8560aa1501882203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record019_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record019) (record019.maps 6)
      (record019.inverseMaps 6) record019_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame006_links_0000 record019_frame006_links_0064)
theorem record019_frame006_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 6 :=
  of_group record019 6 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record019_frame006_indices record019_frame006_graph record019_frame006_links
def record019_frame007_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34319e8ccb64db137701b3cd9bebf9572ab4d00e7773b29844b12578cb85b3ad51658b0454fa9d93b89ca4d226012408fc4181fecfd27b73d39e10c666202fc1740ad654225412588e044c1f60f205f82c715a8a0c4e6255127091447c23011107fc3e21e40ef07043741b30d6069833c1910c505ec2ea16e0ac054429414309e84d4250121089043020a08c03481680ae05602a815006202200f807803a01c00d006403001700a804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 7)
      (record019.inverseMaps 7) record019_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame007_links_0000 record019_frame007_links_0064)
theorem record019_frame007_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 7 :=
  of_group record019 7 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame007_indices record019_frame007_graph record019_frame007_links
def record019_frame008_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8d38cf8c28be8ab8788588548468268227f57e67e17c87b97b469763563061e60a5e35d258d58757456253f52c4c94a749a47b46f45d3fb3f63e33d23a739a35334d33932a3032f428f26a25f23e23422121921220e1ff1f01ce1bd1b51af18f18717e17617016b15f15714914213912712111b11511010c1010f90ed0e80e108806705805505405305203102201f01e01d01c01a01901801701501000d00a009008007004003002001000 } : Fields).get c.val)
theorem record019_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record019) (record019.maps 8) (record019.inverseMaps 8) record019_frame008_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record019) (record019.maps 8) (record019.inverseMaps 8) record019_frame008_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record019) (record019.maps 8)
      (record019.inverseMaps 8) record019_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame008_links_0000 record019_frame008_links_0064)
theorem record019_frame008_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 8 :=
  of_group record019 8 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record019_frame008_indices record019_frame008_graph record019_frame008_links
def record019_frame009_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x99198e98798597995b95295094393493192292091e91090b90880277576a75073a7066ef68a67e65f64760d5f356e55554c53452c51f49048446544d4133f938737c36234c31830128b27226925124923c23522c22521820b1ea1dd1d01ca1af1a71a019819018717917116115b15313d13512e12611e1151070ff0ef0e90e108c06905a05705605505403102201f01e01d01c01a01901801701501000d00a009008007004003002001000 } : Fields).get c.val)
theorem record019_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 9) (record019.inverseMaps 9) record019_frame009_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 9) (record019.inverseMaps 9) record019_frame009_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record019) (record019.maps 9)
      (record019.inverseMaps 9) record019_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame009_links_0000 record019_frame009_links_0064)
theorem record019_frame009_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 9 :=
  of_group record019 9 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record019_frame009_indices record019_frame009_graph record019_frame009_links
def record019_frame010_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x29e53aa714da9a529a4b48e8fd1aa3344a87d0ea1341e82c878a914a22c37841051f6bea7b4f31d93a56b2d119e32c64cc65732e35a6b1954a9f4d89a92e25246e8bcf59d539c6f4db9ab34a67cce19631c5d8b51632c2530a394227c4e89a92a24445c8990d1f43d8788ec1ce3886b0cf1882fc5d0760b413c2604b0941241702203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record019_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (embedding (N := 44310) record019) (record019.maps 10) (record019.inverseMaps 10) record019_frame010_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (embedding (N := 44310) record019) (record019.maps 10) (record019.inverseMaps 10) record019_frame010_indices (Fin.ofNat record019.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record019_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (embedding (N := 44310) record019) (record019.maps 10)
      (record019.inverseMaps 10) record019_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record019_frame010_links_0000 record019_frame010_links_0064)
theorem record019_frame010_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 10 :=
  of_group record019 10 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record019_frame010_indices record019_frame010_graph record019_frame010_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (Fin.cases (record019_frame005_supported hcells) (Fin.cases (record019_frame006_supported hcells) (Fin.cases (record019_frame007_supported hcells) (Fin.cases (record019_frame008_supported hcells) (Fin.cases (record019_frame009_supported hcells) (Fin.cases (record019_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a18ce3665b0c579dbb5daf2cf7665afe55caad349da004efa7652ec968caf253f280935c54227312e65c2fd5608a9e4ee2729348980456a19907e7e93db1e9cf086c12e815a895049623811306f23321858ad450427312a893848a23e118088840e2000f2075c3721b30cf066031417c0ba05b82b01510a5050c27a135094048420a0ef07482300e606902e01680ac05502a00ec062024011007803a01c00d006403001700a803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3431996c2cde76ed76bcb3dd996bf9572ab4d30e95f49da40d19a8af41ea0650027393839bbcbaa59f2c494ec9fa4e515089cc4b9970bf5582277138c9a44c0247515a8413f49ed8f4e784360974095049223811307d23791868ad450427312a893848a23e118088840e2000f2075c3661ac0cf06282e816e0ac052827a13509784a024211308283c01d208c03481980c805c02d01580aa05401880b8058024011007803a01c00d006403001700a803c01a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8da8b086885184a82b81c81580c7e77e37cd7ca7c77c47c17be7b37a87a279078d78b77476976375b75875673a7387366586255e859758f57f56953a5094d74a94944904854383de38337d36c3563272fd2ce2a729729428a28127927425e24822421d1fd1e81bf1b81a618a17517115814613712a12011610b0f70e70cd0c408606706406205a05805405305203102e02c02402201e01d01c01a01901801701500f00d009008007005004003002001000 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record026_frame002_links_0000 record026_frame002_links_0064)
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x2c3d7dadd59ab255eab155aa954aa9150aa053ea7b4ee9cd36a694c694526a4b4728cd16a27446885009ff3fa46c5e84ef71eabce786ea1c436868ecd1973235e6af53926b4c69691f2193f4774e41c33726d0d81ae344660c217f2d456c9f13925a460851041f23bc730e21be368698c717c2bc5587a0bc16c2d0530a21342604b05e0b4158240440780e81c0340640c01702a03c0680901001c0280400600800800 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record026_frame003_links_0000 record026_frame003_links_0064)
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x53e69a93da9d34b563911ba8d946a613b05b81e4082002fd77e33ebdf46f0377c3b69da6e4f715328993cbd35e42cc564cac95592ab132c97048e238d17a869425a0e10607663a11af0d3066932f9928c7e6102fd95c4ac254c2a0142c9c84d425f92cc8fc46723091588a43bd1b18d4468a2fb1768b085602a412d093046622b10e88543d81d30b4050c26212208b84181e80e506d034814209703381780b204d0228108076038011807802600d0040010002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb4653afcb76fbb05c1ed61673b33d6ceb41585ab0548ea3b4459afc59e26111e88443be1b50b8851c265bead3c67bac39566aa253e28f5332970484a3d118c86b423a01cff07c23d31e54bb457f2b71520a1246521e0f5478039219b8c4c5a62c414709c84c224511888183821820ba85b42ce14a09384842320fe07403881780a0049823c0fc06f02d81540a804601b808c03a01c00d006002601100700280100070018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x50c683537c9aeca5a4d721c8e5c5f22d31538a1446e21d0fd86b42aa0ff0147fabf19f4eeb175439f5ce8d46650b0e1828b7757aaa554789b74c8a54925890647f22790627f13f39f70e506b0340993cc405ff2fc95f4ac252828613cc9de4a2249119c8a243821110687c03d11d68e6c70034d19d8c805fc2f616609a049823e11708484081fa0e506d83421740b5858028613a097849823407402b01540a804d02380f0058029012807803a01c00d006002600f00600240100070018008002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1928c8bdf96f3b76bb5d59eecd15e0ae456f2b3157dab945c62cf12e8933f75dacdc969f33dd7ccb1c57a2a954f2a3d513268d332970499a4991fe8c6457a1450788073f49f08f4e79535917a0b805712a294249e446f23290f07fe3f21e58e486f631d1840b4c56a28e139898448a23110387543661900c505d02dc1670ab84d824e12108d042c20a0fe07b825812608f03281580aa054016807803a01c00d006002600f004802000e0060018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87c85983b8228067fa7d47ca7b57ab7747537177167157147137126ad67d66d5f15ea5c05b95a95864f34dc4a747346b46642541c3fa3ec3c53b73aa38f38a36e36434b33b33031830d3002f52d92d52ba2b02a928928326c26125423722c2212111eb1de1cf1c21b01a319b18917c16d16414b1361251060ee0e00d50be0b205a05504f04e04704403803402802301d01c01a01801300e00c008007004003002001000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x1b035569cd1194f17628c0f7e6ea5d2b8f706d95abb3964ac6585ad157aae55aab1556a8d4fa9936e5943282eff5e2ba8734e21bf361682cf19cac8582a954fa874ac91515a2442e800fa9e73b673cde9b834c67cc016b2a44f89d13624443c859052043e4760e81b034c678c51762d4570aa0f21cc338570a2140248430780d8168230420740e01902e0500981001c0280400700600800800 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32cf94dbf2de66edf679b39567ab07574a22cd7e2cf13088f44221df0da85c428e132df569e33dd61caa253e28f53469994b8242d1e88c643ba1ad08e8073fc1f08f4c7952ed15b8a9050923791948783d71e00e486863371898b4c58828e139098448a2310fc87042ea16d0b3855c26c12709084681fc0f707403881780a0049823c0de06502d81540a8037016808c03a01c00d006002600e005002000e0060018008002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x88287c85f85980c8098068007fd7fa7e87e17db7a479d7977747537177167157147137126ad67d66d5ea5b95a958556552c4a747346b4663ec3b73aa38e38a37736e36434b34433b33030d2f52d92d52ba2b02a928928326c26125423722c2212111de1c21a319b17c16d16412511f1060ff0ee0e00d60be0b206105f05a05504f04e04704403803402f02d02802301d01c01a01801300e008007006004003002001000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
def record049_frame002_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x16f6b73590ec5754faa554f6a4d50fa7951668874289a44cd663d2198a63e85f22f817bb3db5ec8d43655b1ad5bca4650326e934c96e482a3891b88d43a51aa0cd46062fc9744b7a59b2a894f0a504f624e11e48804311ff8f807a23971c50d8869c32c1710b3457228711688283a21c20c805c42c4133096045c22010407b03bc1c60dd03381940c005b02a815009a04501c00d005e02d014008c03a01c00d006002600e004001c00c0040018008002000 } : Fields).get c.val)
theorem record049_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record049_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record049) (record049.maps 2)
      (record049.inverseMaps 2) record049_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record049_frame002_links_0000 record049_frame002_links_0064)
theorem record049_frame002_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 2 :=
  of_group record049 2 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record049_frame002_indices record049_frame002_graph record049_frame002_links
def record049_frame003_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x48a90f20e3fc788ed1d639c728e11a6344668a714a28c4986f0460840e817026043d1780ec5bdb6a6b4cfd96b0857aa894e29a4d2961272384688ad13a2242282d021f63ba748df9bd350684ce18c3105ecba16e2c056cab94a262494891101f83d0780cc18e2e0590a613c2684888c0b215c2904f092120220410700d01782d05008c0e81c0340600980e01001c0300400600800800 } : Fields).get c.val)
theorem record049_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record049_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record049) (record049.maps 3)
      (record049.inverseMaps 3) record049_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record049_frame003_links_0000 record049_frame003_links_0064)
theorem record049_frame003_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 3 :=
  of_group record049 3 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record049_frame003_indices record049_frame003_graph record049_frame003_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (Fin.cases (record049_frame002_supported hcells) (Fin.cases (record049_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x48b9011ee3d46f8c917e2bc5488f0d60dc1682704a07c0d81902a03bcd786efdd837a6eed99acb4a688cbd9330a602bd1712dd5aeb49602bc554a854e27445689909a0d4127dcf01d7348680ce17d2f25c0ad9562964d89410f2103c0718e01ae350638bd1782c8540a313c2684808b0f41c43385c0a61402484806e0c81782803e0740e01801c0240400700c00800800 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (embedding (N := 44310) record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (embedding record050) hcells Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
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
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xca38f313e22c2b816f55e1b9b6b6d4d93b1f636c657baf35dab956dad5536a5d119952ee2b44785701ded3c276ae4dc1b6f6ced4d93af75d4b816ead3562ab14da8c4ee9d13926d4ac9551ba094027c4f31df3b4728dd9a72e6578ac95129c4e89992f242450838fb1e438c6e8d919a310600b015629c4a8890da18c308450800e41b03205e08c1080901001001802 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8d38ca8a589c83d8348007f77bb78672f72c7267236c669066c6666205e35ba5b559954253652550c4f24df4cd4ac4a448e42a3d03a138437e36334d32d32632331d3002fd2e42de2d42cd2b12a72a229c29027b27525624022221b21720e1ec1e81ce1c51bd1b619518a18417c16c15c14a13811810d1030ec0e80dd0d90c50bc0b30af09508f07a07204504103b03802402201e01d00f00d009008 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
def record061_frame002_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb65dadec2d603a3f518e6d535690dc541f30f887b8bda1bd6d1863eb1c170cab350c282d37e97a4b9256d29a93a49324552008fb46fa01ce4066730697e4b8459b2ae1530a8452d278938496249c24191d088042320b901079e39e1c50d4c6582ed16e8b4c57c282139090845a21410287443681a80ca85802a214309a047c23011208183f81ea0f107203701ac0d2051825c1000740238108076038012008803c01d0078034012008 } : Fields).get c.val)
theorem record061_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record061_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 2)
      (record061.inverseMaps 2) record061_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record061_frame002_links_0000 record061_frame002_links_0064)
theorem record061_frame002_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 2 :=
  of_group record061 2 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record061_frame002_indices record061_frame002_graph record061_frame002_links
def record061_frame003_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xca392f2063cc2b83af7deab79692bad73add5b288ce59752d64145685509604bd97a2f0ddb3a1724e11b83686a8c9d7bac3562ab14da8c4ee9d13926d4ac9552223c4628ad09a074007e4f41df3b4728dd9a1336668c91762e2578ac95129c4e89992e24e458861001e83906f0da19832c618c116a2bc550a811220c3906d08a1001c8360460840e81c01e03404808 } : Fields).get c.val)
theorem record061_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record061_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record061) (record061.maps 3)
      (record061.inverseMaps 3) record061_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record061_frame003_links_0000 record061_frame003_links_0064)
theorem record061_frame003_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 3 :=
  of_group record061 3 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record061_frame003_indices record061_frame003_graph record061_frame003_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (Fin.cases (record061_frame002_supported hcells) (Fin.cases (record061_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8ca89c8438348067f77bb78673172f72c7287267236c66906666205e35ba5b55975445325094ee4e14a94a248b42a3d03a137e36334d32631d3002fd2de2cd2b12a729c29027b27525624022221b21720e1ec1e81ce1c51bd1b619518a18417c16c13711610b0e70c40ae07a07205a05805405304504103b03802402201e01d00f00d009008004003002001000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb865a0a8f94619b44d524371507d33e61f10f7a7b8bda1bd6d186382e19566a0b4a623fd1b48d443da1ad00e7bf3d49c80df86843339828bf25c22cd9578a9853f29693c49c24ae24e12148e844021190508083cf1cd8e286a632c1778b745a02be14109c847e22d10b08143a21b40d286542c013308f045c1fa0e306881700b405602a812008e04201e00ec070024011007803a00f00680240100040018008002000 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2ac5543a7252fe79d3b09cd4df26672f795dca9e4a72128f6c76e24eeff77a3931b22cf8659320573cafc5642a75314965496235d16487941fa0dd05e8243d51e7ced87463801bd4d8469c3399998cb465332298fcb825692af1510a2e50a26e134496e48a23e91988b64572288e4c6a033c1978bf45ba2af14d8a384b823c11908904382150ee06d427812e09203fc1e20e706901840b4055024011807c03c01700a404802200f807402e01400700340120080028008002000 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
def record076_frame002_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x91890e8f98f08b78b58b38b18a189487286f85e84e83182e80a7797787446f96c46a566461a5e05be57d5315245114ed4e04cd4a94a149849547c47846845c44a44642c4183fe3eb3dd3d43bd3b037234934233031930e2ef2e82db2be2b42a028727f2702252031fa1f31db1c51ab1a319c18016b16214a13d13211a10d0e50de0d70c50bf0ba0ae05f05805304804603e03c02e02902402201f01d01701400e00d009008005002001000 } : Fields).get c.val)
theorem record076_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record076_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record076) (record076.maps 2)
      (record076.inverseMaps 2) record076_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record076_frame002_links_0000 record076_frame002_links_0064)
theorem record076_frame002_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 2 :=
  of_group record076 2 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record076_frame002_indices record076_frame002_graph record076_frame002_links
def record076_frame003_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x326646c838df13623c4387f09e0cbf77e6fade8baf756df57aaf152a87ced9af2b63bc5487d055eabcc770e75c73796bcd61a934f67ace194320626c39812f85ccb6568acb57eae94c2784ea9b12ba5547e8e91721441e7fcf99f03d06e0cf1953205dcb41582a453c9d93325a4888d9162063dc690ce1922e4590b114c1742b05108c1101e03a0580a01182103c0700b81401c0340480800a00800800 } : Fields).get c.val)
theorem record076_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record076_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record076) (record076.maps 3)
      (record076.inverseMaps 3) record076_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record076_frame003_links_0000 record076_frame003_links_0064)
theorem record076_frame003_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 3 :=
  of_group record076 3 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record076_frame003_indices record076_frame003_graph record076_frame003_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (Fin.cases (record076_frame002_supported hcells) (Fin.cases (record076_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaa2a6da0ea0aa03a009ed9d29c49ae99997997495e9368ef89d88f88888186c8668117c47807757647517336be69a64f5f35cf58956c55e52c5255194e44694363e638d35530e2fa2ec2d62b62b028e28926825122e2162051f81e01d61c21b91b019218f17d16616115413e13412b1121070fd0e80df0d40c70c40c10b609108a07507006406105805504804603303102302201d01c01a01800a008003002000 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (embedding record082) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8c389585784783c8328127ff7f57c77be79b78b78977f75675473a73873667f67861d5e05cf5c75905775615094a949449048542d3d33be3b53a838337e36334d32f3222fd2e32d62a729f29729427a27425323d22321d2161ee1e81cd1be1b819718a18117517114e13c13711f11610b0e70c408606705a05805405305204603c03503102402201e01d01c01901701400f00d009008007004003002001000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (embedding record084) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
def record085_frame001_indices (c : Fin record085.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5c76e1569eb44cd5268d29f9404542272dd065c2f795daa9e545a8dd3b89ca4c9a5b525e90e456a19907e80a3f49ed8f4e78435516e4ad455728192a092c45f21c8fec7b43791990c2c5ac2b514109cc4ac24f125090c45c220102880c3fa1e60f0076037c1b60d506543161850be85dc2de1640ad855029a14609f04c425212208e042420c0fb07903a81be0d8069023010007303801a40b805a02b01540a804801d80e0062024011007803a01c } : Fields).get c.val)
theorem record085_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record085.data.requiredEdges q = true := by decide +kernel
theorem record085_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record085_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record085) (record085.maps 1) (record085.inverseMaps 1) record085_frame001_indices (Fin.ofNat record085.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record085_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record085) (record085.maps 1)
      (record085.inverseMaps 1) record085_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record085_frame001_links_0000 record085_frame001_links_0064)
theorem record085_frame001_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) : Supported record085 1 :=
  of_group record085 1 (embedding record085) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record085_frame001_indices record085_frame001_graph record085_frame001_links
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (Fin.cases (record085_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa9aa65a059e19d69c199197d96995c94b93e93a93393091c8fd8f28e38e08bc8a789886c8668137c678677b75172c7167046c168f65c64f5f65c45a158957356555452c5255194de4bf4aa46742b3ef3e638b34a32230e3012f32b62b029028726324c2202082051e51e01d61c01bb1b719618f17116616115414513212d1161070f10e80df0d40cc0c40c10b608a07606505905504704504203303102302201d01c01901701400a008003002000 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
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
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x53aa98b36b998cbd65a1251908480a0c50277e9bf09dfeef4723b8ddc54d9467db2ad912c815cd2be15a0abe554aa7533898c4bba4a91d28d946221dd08a83f41ba0bcf5c7a23b79d24e086f83629a7cce066232d1934c8a63f2b59548a144de26291f48b64572288e646c035419f0cac5f22dd15f8acc53a28a12c08f045822410e08543dc1ca0c7052025c12408583c41ce0d203e81e80e607002d015405e024011007c03a01800700340120080030008002000 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2acd547a74530e6d733197acb424a321090145f62cf15289e43aa16b08483a414602cfd17e03bfdde8e4771bb8a9b28cfb655b225902ba157fab05558a9d4ce25dd1d28c441fa0dd05e8243d71e6ced07423821bc4d7c698336997ccb464a32298fcb8a56b2ae1548a2a50a26f133c98a48823e91848b64572288e5c6c033e1968bec5ba2bf14e8a304b423c11588904382150f7072831c14809704902160f107383480b4055023811408403d01d80e005e024011007c03a01800700340120080030008002000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
def record091_frame002_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x91b90f8fc8f18af8a089288c85d84c84b81381180e80c7fd7eb7dc7da7d37c27ab7a977977873e73572f6fb6c669d67366461c5e25b659b57d53852b4f44e74a94a149849547d47746745b44b4454294153f33e03dd3c43bd3b037534a34033931730e2f02e72e32bc2b429528727f27022820c1fb1f11d91c51b31a419b17e16b15714a13d1321211141040eb0de0d70cb0bf0ba0ae05805304704504203d03b03802f02402201f01d01800e00d009008006002001000 } : Fields).get c.val)
theorem record091_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record091_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record091) (record091.maps 2)
      (record091.inverseMaps 2) record091_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record091_frame002_links_0000 record091_frame002_links_0064)
theorem record091_frame002_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 2 :=
  of_group record091 2 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record091_frame002_indices record091_frame002_graph record091_frame002_links
def record091_frame003_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x327e47c858eb0ee11c17822fa5e6bc972ae35c3b816ced85a8b4f68aced91b1d5eabc546a7d4e288cef9a32d656c798ad0e212c157baf3dd03966bcd61a934f67ccdd93b1f628c3580af75beb4968ac357eae94da794e89c12b2554808e51a21341e7e4f99f03d06ecd219631e5d8b415c2a65389d13324e4888d9162103f0768d719c3245f0b21622982b05108a10c2003b0720d8168230420780e01801c0340480800c00800800 } : Fields).get c.val)
theorem record091_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record091_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record091) (record091.maps 3)
      (record091.inverseMaps 3) record091_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record091_frame003_links_0000 record091_frame003_links_0064)
theorem record091_frame003_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 3 :=
  of_group record091 3 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record091_frame003_indices record091_frame003_graph record091_frame003_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (Fin.cases (record091_frame002_supported hcells) (Fin.cases (record091_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x116e88dc09e036ff37f0be09eecf4e79e3971bbadd56d0b64d9f2c8d57d27b93d29b74cd25752748fb455a2210e486241ba0890187e13e59eb0e1270136b9af4d0e66a31f17f8bee5cd2db1620ad8510279134c94a497232115487a41a2090f8878c38d1b68ce85de2ce15c0a044de23611207a43ba1cc0e006e432a1860bb053828413208a83c81ca0d606382740ec074034819c0ca05a02100c405c02c014809404400d0050024010007002000c004001 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8ba459e243114812c069fe4fe07c03dd5e9af3b646abf15e8ac6556a9f94cea344f827a13689974ada4e11fc8b944b21c906e8223f09f2cf587a63839c04dae6bd34399a8c7c5fc2fc1744b7458c2b81508a064e5269931c94a49724391908aa43d20c90447be3c31c50da85e22e21680b0457029314089bc49023611207ac3be1ce0e106e432e1860bb054028413208983c81ca0d606381e80d205a02100f807803101780b404401900b805002000d0050024010007002000c004001 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (embedding record093) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
def record093_frame002_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa9fd4b698f4af98d4c125d52d3931493e4632176b2ae99722b5859c2bb558ca8651d28953d89cc4c0a5692348e946da33116e8b044da2511168813a49cf0e126e93529a0cc925f42f396d0b2855029713d097e4b1253127c92248a24191dc8e246921810607a23a61aa8ca854c29814389e44d624b11e08b441a2000f9070c36a1a40cb06202d01590a504a823a10f07c03a41c40db06a01e80d205a02100f807803101780b404401900b805002000d0050024010007002000c004001 } : Fields).get c.val)
theorem record093_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record093_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record093) (record093.maps 2)
      (record093.inverseMaps 2) record093_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record093_frame002_links_0000 record093_frame002_links_0064)
theorem record093_frame002_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) : Supported record093 2 :=
  of_group record093 2 (embedding record093) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record093_frame002_indices record093_frame002_graph record093_frame002_links
def record093_frame003_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa99a91a71a649d49cb9bb9b398297b96c9637b66e96e26c16b068a67765262e6276085f65d35bf59757756955b54754052b52451b51748e48946745542f4183ef3c13bc39d38b36334e3222fd2ef2e62e02d22cb2c52b82b22aa28f28726324c22220a1c11bb1b31ad1a819618f18616f16916014113b13312d12811610d1070ef0e70e20cf0c30c00bd0b707a06905a04203e03c03102f02d02201901701401000d00a009008007004003002001 } : Fields).get c.val)
theorem record093_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record093_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record093) (record093.maps 3)
      (record093.inverseMaps 3) record093_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record093_frame003_links_0000 record093_frame003_links_0064)
theorem record093_frame003_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) : Supported record093 3 :=
  of_group record093 3 (embedding record093) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record093_frame003_indices record093_frame003_graph record093_frame003_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (Fin.cases (record093_frame002_supported hcells) (Fin.cases (record093_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x22d911980c3f79ee6f39774bb79cb8ddd6eab685b26afa4f7a7a536e99a4aea4e91f687241ba088fc27cb3d61e98e0e70136b9af4d0e66a31f17f4bee5cd2db1620ad84d3252925c8c845521e90608243e21e30e346da33a15c0aa050226f12d88d84481ed0ee87403801b90ca86182ec14e0a104c81e40e506b031c13a07603a01a40b404201f00f006202e01600a404a02200d006001a00c0050024010007002000c004001 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8d3c6623071548a2c4c20670188013f79f1cf737aebce5cbcddf6eb3695b2ac8c5c92bf53de9e84da265d2b693847f22e112a87341ca090fc87ce3d49e98e0e70136b9af4d0e66a31f17f4bf05d12dd1630ae0542282939c9a44a224a11848a443121110608223df1e18e286d42f01678ae4556284139097847222710587b43be1d00e106e432e1860bb054028413208903c01c60d406282300f405a02100f8078031011007c03c01d00e006803201800b805002000d002000c004001 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xa1ed08a7fd3e39b34d4a65f31874935f9ae0d3d68ab32d94ac63616ac65616ad855829994809fe4e5a71137e9b84d1a6552f296b4a824e526492b492247121e90748023cd1d68e446c9e68c0c5fc2e29678aa853027712ac90e467219108c7e23e11cb8e346ac32f1728b044fe23c10c07e03861b40c105c829c14a0a004f026812d093847c23011108604141fc0f507803881b80d6068027411807a03480c405e02d011007c03c01d00e006803000d0050024010007 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
def record097_frame002_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x818c08e000ff07c63df9eb6f4b67cb22d908c5861f30397e8bc65c92bed5e8ac6556a9f94cea34502a7e93e29ea4e0268d2cc94347ca2e9150897442a1d10a883c4139ff8fcc7d03d41c20bf85f92e996f0b1c57229f941c9d24d225112508c245220c104c7c83c81c78dbc66e2f31690ae050226f11b08903d41e60e687243741ae0cf86242f21690ad051426a11c08a03bc1c40d3062027411807a03480c405e02d011007c03c01d00e006803000d0050024010007 } : Fields).get c.val)
theorem record097_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record097) (record097.maps 2) (record097.inverseMaps 2) record097_frame002_indices (Fin.ofNat record097.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record097_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record097) (record097.maps 2)
      (record097.inverseMaps 2) record097_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record097_frame002_links_0000 record097_frame002_links_0064)
theorem record097_frame002_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 2 :=
  of_group record097 2 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record097_frame002_indices record097_frame002_graph record097_frame002_links
def record097_frame003_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x89288d87e87685584c83c8357246df6db6c46b469a68766a64c6076035ef5e05c15b359257356d56956655654a53452750f4f64ef4e94e24dc4d04c84c04b24aa4a249744b3973943773653463333142f02e12d42b42aa28927e25925623b22a2061f71d61b11a419617416b14913f12011e11311110b1050ff0f80f20ec0e70e00d90d00cc0be0b90b40ad08f08007606703102f02d02201f01e01d01c01a01800d00a009008007 } : Fields).get c.val)
theorem record097_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record097) (record097.maps 3) (record097.inverseMaps 3) record097_frame003_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record097) (record097.maps 3) (record097.inverseMaps 3) record097_frame003_indices (Fin.ofNat record097.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record097_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record097) (record097.maps 3)
      (record097.inverseMaps 3) record097_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record097_frame003_links_0000 record097_frame003_links_0064)
theorem record097_frame003_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 3 :=
  of_group record097 3 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record097_frame003_indices record097_frame003_graph record097_frame003_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (Fin.cases (record097_frame002_supported hcells) (Fin.cases (record097_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00046
