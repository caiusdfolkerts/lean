module
prelude
public import GraphInputsRow24Part00033Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M009
public import InducedTerminalMatches.M010
public import InducedTerminalMatches.M011
public import InducedTerminalMatches.M012
public import InducedTerminalMatches.M013
public import InducedTerminalMatches.M014

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota [] (.quota 1) = true
  exact empty_checked record000.data.quota 1 (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota [] (.quota 1) = true
  exact empty_checked record001.data.quota 1 (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record001_leaf_certificates_checked

noncomputable def record002_rawLeaves (j : Fin record002.l) : List Cell :=
  (record002.leaf j).map record002.data.cells
theorem record002_raw_exact (j : Fin record002.l) :
    (record002.leaf j).map record002.data.cells = record002_rawLeaves j := rfl
noncomputable def record002_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota [] (.quota 1) = true
  exact empty_checked record002.data.quota 1 (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record002_leaf_certificates_checked

noncomputable def record003_rawLeaves (j : Fin record003.l) : List Cell :=
  (record003.leaf j).map record003.data.cells
theorem record003_raw_exact (j : Fin record003.l) :
    (record003.leaf j).map record003.data.cells = record003_rawLeaves j := rfl
noncomputable def record003_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota [] (.quota 1) = true
  exact empty_checked record003.data.quota 1 (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record003_leaf_certificates_checked

noncomputable def record004_rawLeaves (j : Fin record004.l) : List Cell :=
  (record004.leaf j).map record004.data.cells
theorem record004_raw_exact (j : Fin record004.l) :
    (record004.leaf j).map record004.data.cells = record004_rawLeaves j := rfl
noncomputable def record004_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota [] (.quota 1) = true
  exact empty_checked record004.data.quota 1 (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record004_leaf_certificates_checked

noncomputable def record005_rawLeaves (j : Fin record005.l) : List Cell :=
  (record005.leaf j).map record005.data.cells
theorem record005_raw_exact (j : Fin record005.l) :
    (record005.leaf j).map record005.data.cells = record005_rawLeaves j := rfl
noncomputable def record005_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota [] (.quota 1) = true
  exact empty_checked record005.data.quota 1 (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record005_leaf_certificates_checked

noncomputable def record006_rawLeaves (j : Fin record006.l) : List Cell :=
  (record006.leaf j).map record006.data.cells
theorem record006_raw_exact (j : Fin record006.l) :
    (record006.leaf j).map record006.data.cells = record006_rawLeaves j := rfl
noncomputable def record006_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record006_certificates (j : Fin record006.l) : Certificate :=
  record006_certificateTable.get j.val
theorem record006_leaf_checked_0 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
      (record006_certificates 0) = true := by
  change RawLeafCertificate.check record006.data.quota [] (.quota 1) = true
  exact empty_checked record006.data.quota 1 (by decide +kernel)
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record006_leaf_certificates_checked

noncomputable def record007_rawLeaves (j : Fin record007.l) : List Cell :=
  (record007.leaf j).map record007.data.cells
theorem record007_raw_exact (j : Fin record007.l) :
    (record007.leaf j).map record007.data.cells = record007_rawLeaves j := rfl
noncomputable def record007_certificateTable : Table Certificate :=
(.branch 79
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0319))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0320)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0321))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0322))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0323))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0324)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0325))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0326))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0327))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0328))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0329)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0330))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0331))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0332)))))
 (.branch 16
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0333))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0334)))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0335))
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0336))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0337)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0338))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0339)))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0340))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0341))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0342)))))
 (.branch 26
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0343))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0344)))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0345))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0346))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0347))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0348))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0349)))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0350))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M010.r0351))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0352)))))
 (.branch 36
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0353))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0354)))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0355))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0356))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0357))))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0358))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0359)))
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0360))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0361))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0362)))))
 (.branch 46
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0363))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0364)))
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0365))
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0366))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0367))))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0368))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0369)))
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0370))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0371))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0372)))))
 (.branch 56
 (.branch 55
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0373))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0374)))
 (.branch 57
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0375))
 (.branch 58
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0376))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0377)))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0378))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0379)))
 (.branch 62
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0380))
 (.branch 63
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0381))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0382)))))
 (.branch 66
 (.branch 65
 (.leaf (.matching Nonrational.InducedTerminalMatches.M011.r0383))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0384)))
 (.branch 67
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0385))
 (.branch 68
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0386))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0387))))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0388))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0389)))
 (.branch 72
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0390))
 (.branch 73
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0391))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0392)))))
 (.branch 76
 (.branch 75
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0393))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0394)))
 (.branch 77
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0395))
 (.branch 78
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0396))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0397)))))))))
 (.branch 118
 (.branch 98
 (.branch 88
 (.branch 83
 (.branch 81
 (.branch 80
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0398))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0399)))
 (.branch 82
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0400))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0401))))
 (.branch 85
 (.branch 84
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0402))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0403)))
 (.branch 86
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0404))
 (.branch 87
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0405))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0406))))))
 (.branch 93
 (.branch 90
 (.branch 89
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0407))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0408)))
 (.branch 91
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0409))
 (.branch 92
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0410))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0411)))))
 (.branch 95
 (.branch 94
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0412))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0413)))
 (.branch 96
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0414))
 (.branch 97
 (.leaf (.matching Nonrational.InducedTerminalMatches.M012.r0415))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0416)))))))
 (.branch 108
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0417))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0418)))
 (.branch 101
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0419))
 (.branch 102
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0420))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0421)))))
 (.branch 105
 (.branch 104
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0422))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0423)))
 (.branch 106
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0424))
 (.branch 107
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0425))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0426))))))
 (.branch 113
 (.branch 110
 (.branch 109
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0427))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0428)))
 (.branch 111
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0429))
 (.branch 112
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0430))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0431)))))
 (.branch 115
 (.branch 114
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0432))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0433)))
 (.branch 116
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0434))
 (.branch 117
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0435))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0436))))))))
 (.branch 138
 (.branch 128
 (.branch 123
 (.branch 120
 (.branch 119
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0437))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0438)))
 (.branch 121
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0439))
 (.branch 122
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0440))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0441)))))
 (.branch 125
 (.branch 124
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0442))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0443)))
 (.branch 126
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0444))
 (.branch 127
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0445))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0446))))))
 (.branch 133
 (.branch 130
 (.branch 129
 (.leaf (.matching Nonrational.InducedTerminalMatches.M013.r0447))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0448)))
 (.branch 131
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0449))
 (.branch 132
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0450))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0451)))))
 (.branch 135
 (.branch 134
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0452))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0453)))
 (.branch 136
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0454))
 (.branch 137
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0455))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0456)))))))
 (.branch 148
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0457))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0458)))
 (.branch 141
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0459))
 (.branch 142
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0460))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0461)))))
 (.branch 145
 (.branch 144
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0462))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0463)))
 (.branch 146
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0464))
 (.branch 147
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0465))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0466))))))
 (.branch 153
 (.branch 150
 (.branch 149
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0467))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0468)))
 (.branch 151
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0469))
 (.branch 152
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0470))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0471)))))
 (.branch 155
 (.branch 154
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0472))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0473)))
 (.branch 156
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0474))
 (.branch 157
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0475))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M014.r0476))))))))))
noncomputable def record007_certificates (j : Fin record007.l) : Certificate :=
  record007_certificateTable.get j.val
theorem record007_leaf_checked_0 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
      (record007_certificates 0) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M009.r0319) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 0) Nonrational.InducedTerminalMatches.M009.r0319
    Nonrational.InducedTerminalMatches.M009.r0319_checked (by decide +kernel)
theorem record007_leaf_checked_1 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
      (record007_certificates 1) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M010.r0320) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 1) Nonrational.InducedTerminalMatches.M010.r0320
    Nonrational.InducedTerminalMatches.M010.r0320_checked (by decide +kernel)
theorem record007_leaf_checked_2 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
      (record007_certificates 2) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M010.r0321) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 2) Nonrational.InducedTerminalMatches.M010.r0321
    Nonrational.InducedTerminalMatches.M010.r0321_checked (by decide +kernel)
theorem record007_leaf_checked_3 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
      (record007_certificates 3) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M010.r0322) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 3) Nonrational.InducedTerminalMatches.M010.r0322
    Nonrational.InducedTerminalMatches.M010.r0322_checked (by decide +kernel)
theorem record007_leaf_checked_4 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
      (record007_certificates 4) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M010.r0323) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 4) Nonrational.InducedTerminalMatches.M010.r0323
    Nonrational.InducedTerminalMatches.M010.r0323_checked (by decide +kernel)
theorem record007_leaf_checked_5 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
      (record007_certificates 5) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M010.r0324) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 5) Nonrational.InducedTerminalMatches.M010.r0324
    Nonrational.InducedTerminalMatches.M010.r0324_checked (by decide +kernel)
theorem record007_leaf_checked_6 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
      (record007_certificates 6) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M010.r0325) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 6) Nonrational.InducedTerminalMatches.M010.r0325
    Nonrational.InducedTerminalMatches.M010.r0325_checked (by decide +kernel)
theorem record007_leaf_checked_7 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
      (record007_certificates 7) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M010.r0326) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 7) Nonrational.InducedTerminalMatches.M010.r0326
    Nonrational.InducedTerminalMatches.M010.r0326_checked (by decide +kernel)
theorem record007_leaf_checked_8 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
      (record007_certificates 8) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M010.r0327) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 8) Nonrational.InducedTerminalMatches.M010.r0327
    Nonrational.InducedTerminalMatches.M010.r0327_checked (by decide +kernel)
theorem record007_leaf_checked_9 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
      (record007_certificates 9) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M010.r0328) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 9) Nonrational.InducedTerminalMatches.M010.r0328
    Nonrational.InducedTerminalMatches.M010.r0328_checked (by decide +kernel)
theorem record007_leaf_checked_10 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
      (record007_certificates 10) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M010.r0329) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 10) Nonrational.InducedTerminalMatches.M010.r0329
    Nonrational.InducedTerminalMatches.M010.r0329_checked (by decide +kernel)
theorem record007_leaf_checked_11 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
      (record007_certificates 11) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M010.r0330) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 11) Nonrational.InducedTerminalMatches.M010.r0330
    Nonrational.InducedTerminalMatches.M010.r0330_checked (by decide +kernel)
theorem record007_leaf_checked_12 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
      (record007_certificates 12) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M010.r0331) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 12) Nonrational.InducedTerminalMatches.M010.r0331
    Nonrational.InducedTerminalMatches.M010.r0331_checked (by decide +kernel)
theorem record007_leaf_checked_13 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
      (record007_certificates 13) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M010.r0332) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 13) Nonrational.InducedTerminalMatches.M010.r0332
    Nonrational.InducedTerminalMatches.M010.r0332_checked (by decide +kernel)
theorem record007_leaf_checked_14 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
      (record007_certificates 14) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M010.r0333) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 14) Nonrational.InducedTerminalMatches.M010.r0333
    Nonrational.InducedTerminalMatches.M010.r0333_checked (by decide +kernel)
theorem record007_leaf_checked_15 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
      (record007_certificates 15) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M010.r0334) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 15) Nonrational.InducedTerminalMatches.M010.r0334
    Nonrational.InducedTerminalMatches.M010.r0334_checked (by decide +kernel)
theorem record007_leaf_checked_16 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
      (record007_certificates 16) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M010.r0335) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 16) Nonrational.InducedTerminalMatches.M010.r0335
    Nonrational.InducedTerminalMatches.M010.r0335_checked (by decide +kernel)
theorem record007_leaf_checked_17 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
      (record007_certificates 17) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M010.r0336) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 17) Nonrational.InducedTerminalMatches.M010.r0336
    Nonrational.InducedTerminalMatches.M010.r0336_checked (by decide +kernel)
theorem record007_leaf_checked_18 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
      (record007_certificates 18) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M010.r0337) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 18) Nonrational.InducedTerminalMatches.M010.r0337
    Nonrational.InducedTerminalMatches.M010.r0337_checked (by decide +kernel)
theorem record007_leaf_checked_19 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
      (record007_certificates 19) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M010.r0338) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 19) Nonrational.InducedTerminalMatches.M010.r0338
    Nonrational.InducedTerminalMatches.M010.r0338_checked (by decide +kernel)
theorem record007_leaf_checked_20 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
      (record007_certificates 20) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M010.r0339) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 20) Nonrational.InducedTerminalMatches.M010.r0339
    Nonrational.InducedTerminalMatches.M010.r0339_checked (by decide +kernel)
theorem record007_leaf_checked_21 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
      (record007_certificates 21) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M010.r0340) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 21) Nonrational.InducedTerminalMatches.M010.r0340
    Nonrational.InducedTerminalMatches.M010.r0340_checked (by decide +kernel)
theorem record007_leaf_checked_22 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
      (record007_certificates 22) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M010.r0341) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 22) Nonrational.InducedTerminalMatches.M010.r0341
    Nonrational.InducedTerminalMatches.M010.r0341_checked (by decide +kernel)
theorem record007_leaf_checked_23 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
      (record007_certificates 23) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M010.r0342) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 23) Nonrational.InducedTerminalMatches.M010.r0342
    Nonrational.InducedTerminalMatches.M010.r0342_checked (by decide +kernel)
theorem record007_leaf_checked_24 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 24)
      (record007_certificates 24) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M010.r0343) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 24) Nonrational.InducedTerminalMatches.M010.r0343
    Nonrational.InducedTerminalMatches.M010.r0343_checked (by decide +kernel)
theorem record007_leaf_checked_25 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 25)
      (record007_certificates 25) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M010.r0344) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 25) Nonrational.InducedTerminalMatches.M010.r0344
    Nonrational.InducedTerminalMatches.M010.r0344_checked (by decide +kernel)
theorem record007_leaf_checked_26 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 26)
      (record007_certificates 26) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M010.r0345) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 26) Nonrational.InducedTerminalMatches.M010.r0345
    Nonrational.InducedTerminalMatches.M010.r0345_checked (by decide +kernel)
theorem record007_leaf_checked_27 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 27)
      (record007_certificates 27) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M010.r0346) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 27) Nonrational.InducedTerminalMatches.M010.r0346
    Nonrational.InducedTerminalMatches.M010.r0346_checked (by decide +kernel)
theorem record007_leaf_checked_28 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 28)
      (record007_certificates 28) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M010.r0347) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 28) Nonrational.InducedTerminalMatches.M010.r0347
    Nonrational.InducedTerminalMatches.M010.r0347_checked (by decide +kernel)
theorem record007_leaf_checked_29 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 29)
      (record007_certificates 29) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M010.r0348) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 29) Nonrational.InducedTerminalMatches.M010.r0348
    Nonrational.InducedTerminalMatches.M010.r0348_checked (by decide +kernel)
theorem record007_leaf_checked_30 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 30)
      (record007_certificates 30) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M010.r0349) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 30) Nonrational.InducedTerminalMatches.M010.r0349
    Nonrational.InducedTerminalMatches.M010.r0349_checked (by decide +kernel)
theorem record007_leaf_checked_31 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 31)
      (record007_certificates 31) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M010.r0350) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 31) Nonrational.InducedTerminalMatches.M010.r0350
    Nonrational.InducedTerminalMatches.M010.r0350_checked (by decide +kernel)
theorem record007_leaf_checked_32 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 32)
      (record007_certificates 32) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M010.r0351) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 32) Nonrational.InducedTerminalMatches.M010.r0351
    Nonrational.InducedTerminalMatches.M010.r0351_checked (by decide +kernel)
theorem record007_leaf_checked_33 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 33)
      (record007_certificates 33) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M011.r0352) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 33) Nonrational.InducedTerminalMatches.M011.r0352
    Nonrational.InducedTerminalMatches.M011.r0352_checked (by decide +kernel)
theorem record007_leaf_checked_34 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 34)
      (record007_certificates 34) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M011.r0353) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 34) Nonrational.InducedTerminalMatches.M011.r0353
    Nonrational.InducedTerminalMatches.M011.r0353_checked (by decide +kernel)
theorem record007_leaf_checked_35 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 35)
      (record007_certificates 35) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M011.r0354) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 35) Nonrational.InducedTerminalMatches.M011.r0354
    Nonrational.InducedTerminalMatches.M011.r0354_checked (by decide +kernel)
theorem record007_leaf_checked_36 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 36)
      (record007_certificates 36) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M011.r0355) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 36) Nonrational.InducedTerminalMatches.M011.r0355
    Nonrational.InducedTerminalMatches.M011.r0355_checked (by decide +kernel)
theorem record007_leaf_checked_37 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 37)
      (record007_certificates 37) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M011.r0356) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 37) Nonrational.InducedTerminalMatches.M011.r0356
    Nonrational.InducedTerminalMatches.M011.r0356_checked (by decide +kernel)
theorem record007_leaf_checked_38 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 38)
      (record007_certificates 38) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M011.r0357) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 38) Nonrational.InducedTerminalMatches.M011.r0357
    Nonrational.InducedTerminalMatches.M011.r0357_checked (by decide +kernel)
theorem record007_leaf_checked_39 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 39)
      (record007_certificates 39) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M011.r0358) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 39) Nonrational.InducedTerminalMatches.M011.r0358
    Nonrational.InducedTerminalMatches.M011.r0358_checked (by decide +kernel)
theorem record007_leaf_checked_40 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 40)
      (record007_certificates 40) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M011.r0359) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 40) Nonrational.InducedTerminalMatches.M011.r0359
    Nonrational.InducedTerminalMatches.M011.r0359_checked (by decide +kernel)
theorem record007_leaf_checked_41 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 41)
      (record007_certificates 41) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M011.r0360) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 41) Nonrational.InducedTerminalMatches.M011.r0360
    Nonrational.InducedTerminalMatches.M011.r0360_checked (by decide +kernel)
theorem record007_leaf_checked_42 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 42)
      (record007_certificates 42) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M011.r0361) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 42) Nonrational.InducedTerminalMatches.M011.r0361
    Nonrational.InducedTerminalMatches.M011.r0361_checked (by decide +kernel)
theorem record007_leaf_checked_43 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 43)
      (record007_certificates 43) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M011.r0362) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 43) Nonrational.InducedTerminalMatches.M011.r0362
    Nonrational.InducedTerminalMatches.M011.r0362_checked (by decide +kernel)
theorem record007_leaf_checked_44 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 44)
      (record007_certificates 44) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M011.r0363) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 44) Nonrational.InducedTerminalMatches.M011.r0363
    Nonrational.InducedTerminalMatches.M011.r0363_checked (by decide +kernel)
theorem record007_leaf_checked_45 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 45)
      (record007_certificates 45) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M011.r0364) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 45) Nonrational.InducedTerminalMatches.M011.r0364
    Nonrational.InducedTerminalMatches.M011.r0364_checked (by decide +kernel)
theorem record007_leaf_checked_46 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 46)
      (record007_certificates 46) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M011.r0365) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 46) Nonrational.InducedTerminalMatches.M011.r0365
    Nonrational.InducedTerminalMatches.M011.r0365_checked (by decide +kernel)
theorem record007_leaf_checked_47 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 47)
      (record007_certificates 47) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M011.r0366) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 47) Nonrational.InducedTerminalMatches.M011.r0366
    Nonrational.InducedTerminalMatches.M011.r0366_checked (by decide +kernel)
theorem record007_leaf_checked_48 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 48)
      (record007_certificates 48) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M011.r0367) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 48) Nonrational.InducedTerminalMatches.M011.r0367
    Nonrational.InducedTerminalMatches.M011.r0367_checked (by decide +kernel)
theorem record007_leaf_checked_49 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 49)
      (record007_certificates 49) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M011.r0368) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 49) Nonrational.InducedTerminalMatches.M011.r0368
    Nonrational.InducedTerminalMatches.M011.r0368_checked (by decide +kernel)
theorem record007_leaf_checked_50 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 50)
      (record007_certificates 50) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M011.r0369) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 50) Nonrational.InducedTerminalMatches.M011.r0369
    Nonrational.InducedTerminalMatches.M011.r0369_checked (by decide +kernel)
theorem record007_leaf_checked_51 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 51)
      (record007_certificates 51) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M011.r0370) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 51) Nonrational.InducedTerminalMatches.M011.r0370
    Nonrational.InducedTerminalMatches.M011.r0370_checked (by decide +kernel)
theorem record007_leaf_checked_52 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 52)
      (record007_certificates 52) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M011.r0371) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 52) Nonrational.InducedTerminalMatches.M011.r0371
    Nonrational.InducedTerminalMatches.M011.r0371_checked (by decide +kernel)
theorem record007_leaf_checked_53 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 53)
      (record007_certificates 53) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M011.r0372) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 53) Nonrational.InducedTerminalMatches.M011.r0372
    Nonrational.InducedTerminalMatches.M011.r0372_checked (by decide +kernel)
theorem record007_leaf_checked_54 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 54)
      (record007_certificates 54) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M011.r0373) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 54) Nonrational.InducedTerminalMatches.M011.r0373
    Nonrational.InducedTerminalMatches.M011.r0373_checked (by decide +kernel)
theorem record007_leaf_checked_55 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 55)
      (record007_certificates 55) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M011.r0374) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 55) Nonrational.InducedTerminalMatches.M011.r0374
    Nonrational.InducedTerminalMatches.M011.r0374_checked (by decide +kernel)
theorem record007_leaf_checked_56 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 56)
      (record007_certificates 56) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M011.r0375) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 56) Nonrational.InducedTerminalMatches.M011.r0375
    Nonrational.InducedTerminalMatches.M011.r0375_checked (by decide +kernel)
theorem record007_leaf_checked_57 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 57)
      (record007_certificates 57) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 57)
    (.matching Nonrational.InducedTerminalMatches.M011.r0376) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 57) Nonrational.InducedTerminalMatches.M011.r0376
    Nonrational.InducedTerminalMatches.M011.r0376_checked (by decide +kernel)
theorem record007_leaf_checked_58 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 58)
      (record007_certificates 58) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 58)
    (.matching Nonrational.InducedTerminalMatches.M011.r0377) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 58) Nonrational.InducedTerminalMatches.M011.r0377
    Nonrational.InducedTerminalMatches.M011.r0377_checked (by decide +kernel)
theorem record007_leaf_checked_59 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 59)
      (record007_certificates 59) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 59)
    (.matching Nonrational.InducedTerminalMatches.M011.r0378) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 59) Nonrational.InducedTerminalMatches.M011.r0378
    Nonrational.InducedTerminalMatches.M011.r0378_checked (by decide +kernel)
theorem record007_leaf_checked_60 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 60)
      (record007_certificates 60) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 60)
    (.matching Nonrational.InducedTerminalMatches.M011.r0379) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 60) Nonrational.InducedTerminalMatches.M011.r0379
    Nonrational.InducedTerminalMatches.M011.r0379_checked (by decide +kernel)
theorem record007_leaf_checked_61 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 61)
      (record007_certificates 61) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 61)
    (.matching Nonrational.InducedTerminalMatches.M011.r0380) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 61) Nonrational.InducedTerminalMatches.M011.r0380
    Nonrational.InducedTerminalMatches.M011.r0380_checked (by decide +kernel)
theorem record007_leaf_checked_62 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 62)
      (record007_certificates 62) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 62)
    (.matching Nonrational.InducedTerminalMatches.M011.r0381) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 62) Nonrational.InducedTerminalMatches.M011.r0381
    Nonrational.InducedTerminalMatches.M011.r0381_checked (by decide +kernel)
theorem record007_leaf_checked_63 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 63)
      (record007_certificates 63) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 63)
    (.matching Nonrational.InducedTerminalMatches.M011.r0382) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 63) Nonrational.InducedTerminalMatches.M011.r0382
    Nonrational.InducedTerminalMatches.M011.r0382_checked (by decide +kernel)
theorem record007_leaf_checked_64 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 64)
      (record007_certificates 64) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 64)
    (.matching Nonrational.InducedTerminalMatches.M011.r0383) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 64) Nonrational.InducedTerminalMatches.M011.r0383
    Nonrational.InducedTerminalMatches.M011.r0383_checked (by decide +kernel)
theorem record007_leaf_checked_65 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 65)
      (record007_certificates 65) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 65)
    (.matching Nonrational.InducedTerminalMatches.M012.r0384) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 65) Nonrational.InducedTerminalMatches.M012.r0384
    Nonrational.InducedTerminalMatches.M012.r0384_checked (by decide +kernel)
theorem record007_leaf_checked_66 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 66)
      (record007_certificates 66) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 66)
    (.matching Nonrational.InducedTerminalMatches.M012.r0385) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 66) Nonrational.InducedTerminalMatches.M012.r0385
    Nonrational.InducedTerminalMatches.M012.r0385_checked (by decide +kernel)
theorem record007_leaf_checked_67 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 67)
      (record007_certificates 67) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 67)
    (.matching Nonrational.InducedTerminalMatches.M012.r0386) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 67) Nonrational.InducedTerminalMatches.M012.r0386
    Nonrational.InducedTerminalMatches.M012.r0386_checked (by decide +kernel)
theorem record007_leaf_checked_68 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 68)
      (record007_certificates 68) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 68)
    (.matching Nonrational.InducedTerminalMatches.M012.r0387) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 68) Nonrational.InducedTerminalMatches.M012.r0387
    Nonrational.InducedTerminalMatches.M012.r0387_checked (by decide +kernel)
theorem record007_leaf_checked_69 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 69)
      (record007_certificates 69) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 69)
    (.matching Nonrational.InducedTerminalMatches.M012.r0388) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 69) Nonrational.InducedTerminalMatches.M012.r0388
    Nonrational.InducedTerminalMatches.M012.r0388_checked (by decide +kernel)
theorem record007_leaf_checked_70 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 70)
      (record007_certificates 70) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 70)
    (.matching Nonrational.InducedTerminalMatches.M012.r0389) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 70) Nonrational.InducedTerminalMatches.M012.r0389
    Nonrational.InducedTerminalMatches.M012.r0389_checked (by decide +kernel)
theorem record007_leaf_checked_71 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 71)
      (record007_certificates 71) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 71)
    (.matching Nonrational.InducedTerminalMatches.M012.r0390) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 71) Nonrational.InducedTerminalMatches.M012.r0390
    Nonrational.InducedTerminalMatches.M012.r0390_checked (by decide +kernel)
theorem record007_leaf_checked_72 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 72)
      (record007_certificates 72) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 72)
    (.matching Nonrational.InducedTerminalMatches.M012.r0391) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 72) Nonrational.InducedTerminalMatches.M012.r0391
    Nonrational.InducedTerminalMatches.M012.r0391_checked (by decide +kernel)
theorem record007_leaf_checked_73 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 73)
      (record007_certificates 73) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 73)
    (.matching Nonrational.InducedTerminalMatches.M012.r0392) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 73) Nonrational.InducedTerminalMatches.M012.r0392
    Nonrational.InducedTerminalMatches.M012.r0392_checked (by decide +kernel)
theorem record007_leaf_checked_74 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 74)
      (record007_certificates 74) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 74)
    (.matching Nonrational.InducedTerminalMatches.M012.r0393) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 74) Nonrational.InducedTerminalMatches.M012.r0393
    Nonrational.InducedTerminalMatches.M012.r0393_checked (by decide +kernel)
theorem record007_leaf_checked_75 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 75)
      (record007_certificates 75) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 75)
    (.matching Nonrational.InducedTerminalMatches.M012.r0394) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 75) Nonrational.InducedTerminalMatches.M012.r0394
    Nonrational.InducedTerminalMatches.M012.r0394_checked (by decide +kernel)
theorem record007_leaf_checked_76 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 76)
      (record007_certificates 76) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 76)
    (.matching Nonrational.InducedTerminalMatches.M012.r0395) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 76) Nonrational.InducedTerminalMatches.M012.r0395
    Nonrational.InducedTerminalMatches.M012.r0395_checked (by decide +kernel)
theorem record007_leaf_checked_77 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 77)
      (record007_certificates 77) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 77)
    (.matching Nonrational.InducedTerminalMatches.M012.r0396) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 77) Nonrational.InducedTerminalMatches.M012.r0396
    Nonrational.InducedTerminalMatches.M012.r0396_checked (by decide +kernel)
theorem record007_leaf_checked_78 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 78)
      (record007_certificates 78) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 78)
    (.matching Nonrational.InducedTerminalMatches.M012.r0397) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 78) Nonrational.InducedTerminalMatches.M012.r0397
    Nonrational.InducedTerminalMatches.M012.r0397_checked (by decide +kernel)
theorem record007_leaf_checked_79 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 79)
      (record007_certificates 79) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 79)
    (.matching Nonrational.InducedTerminalMatches.M012.r0398) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 79) Nonrational.InducedTerminalMatches.M012.r0398
    Nonrational.InducedTerminalMatches.M012.r0398_checked (by decide +kernel)
theorem record007_leaf_checked_80 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 80)
      (record007_certificates 80) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 80)
    (.matching Nonrational.InducedTerminalMatches.M012.r0399) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 80) Nonrational.InducedTerminalMatches.M012.r0399
    Nonrational.InducedTerminalMatches.M012.r0399_checked (by decide +kernel)
theorem record007_leaf_checked_81 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 81)
      (record007_certificates 81) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 81)
    (.matching Nonrational.InducedTerminalMatches.M012.r0400) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 81) Nonrational.InducedTerminalMatches.M012.r0400
    Nonrational.InducedTerminalMatches.M012.r0400_checked (by decide +kernel)
theorem record007_leaf_checked_82 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 82)
      (record007_certificates 82) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 82)
    (.matching Nonrational.InducedTerminalMatches.M012.r0401) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 82) Nonrational.InducedTerminalMatches.M012.r0401
    Nonrational.InducedTerminalMatches.M012.r0401_checked (by decide +kernel)
theorem record007_leaf_checked_83 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 83)
      (record007_certificates 83) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 83)
    (.matching Nonrational.InducedTerminalMatches.M012.r0402) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 83) Nonrational.InducedTerminalMatches.M012.r0402
    Nonrational.InducedTerminalMatches.M012.r0402_checked (by decide +kernel)
theorem record007_leaf_checked_84 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 84)
      (record007_certificates 84) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 84)
    (.matching Nonrational.InducedTerminalMatches.M012.r0403) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 84) Nonrational.InducedTerminalMatches.M012.r0403
    Nonrational.InducedTerminalMatches.M012.r0403_checked (by decide +kernel)
theorem record007_leaf_checked_85 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 85)
      (record007_certificates 85) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 85)
    (.matching Nonrational.InducedTerminalMatches.M012.r0404) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 85) Nonrational.InducedTerminalMatches.M012.r0404
    Nonrational.InducedTerminalMatches.M012.r0404_checked (by decide +kernel)
theorem record007_leaf_checked_86 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 86)
      (record007_certificates 86) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 86)
    (.matching Nonrational.InducedTerminalMatches.M012.r0405) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 86) Nonrational.InducedTerminalMatches.M012.r0405
    Nonrational.InducedTerminalMatches.M012.r0405_checked (by decide +kernel)
theorem record007_leaf_checked_87 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 87)
      (record007_certificates 87) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 87)
    (.matching Nonrational.InducedTerminalMatches.M012.r0406) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 87) Nonrational.InducedTerminalMatches.M012.r0406
    Nonrational.InducedTerminalMatches.M012.r0406_checked (by decide +kernel)
theorem record007_leaf_checked_88 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 88)
      (record007_certificates 88) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 88)
    (.matching Nonrational.InducedTerminalMatches.M012.r0407) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 88) Nonrational.InducedTerminalMatches.M012.r0407
    Nonrational.InducedTerminalMatches.M012.r0407_checked (by decide +kernel)
theorem record007_leaf_checked_89 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 89)
      (record007_certificates 89) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 89)
    (.matching Nonrational.InducedTerminalMatches.M012.r0408) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 89) Nonrational.InducedTerminalMatches.M012.r0408
    Nonrational.InducedTerminalMatches.M012.r0408_checked (by decide +kernel)
theorem record007_leaf_checked_90 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 90)
      (record007_certificates 90) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 90)
    (.matching Nonrational.InducedTerminalMatches.M012.r0409) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 90) Nonrational.InducedTerminalMatches.M012.r0409
    Nonrational.InducedTerminalMatches.M012.r0409_checked (by decide +kernel)
theorem record007_leaf_checked_91 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 91)
      (record007_certificates 91) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 91)
    (.matching Nonrational.InducedTerminalMatches.M012.r0410) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 91) Nonrational.InducedTerminalMatches.M012.r0410
    Nonrational.InducedTerminalMatches.M012.r0410_checked (by decide +kernel)
theorem record007_leaf_checked_92 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 92)
      (record007_certificates 92) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 92)
    (.matching Nonrational.InducedTerminalMatches.M012.r0411) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 92) Nonrational.InducedTerminalMatches.M012.r0411
    Nonrational.InducedTerminalMatches.M012.r0411_checked (by decide +kernel)
theorem record007_leaf_checked_93 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 93)
      (record007_certificates 93) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 93)
    (.matching Nonrational.InducedTerminalMatches.M012.r0412) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 93) Nonrational.InducedTerminalMatches.M012.r0412
    Nonrational.InducedTerminalMatches.M012.r0412_checked (by decide +kernel)
theorem record007_leaf_checked_94 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 94)
      (record007_certificates 94) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 94)
    (.matching Nonrational.InducedTerminalMatches.M012.r0413) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 94) Nonrational.InducedTerminalMatches.M012.r0413
    Nonrational.InducedTerminalMatches.M012.r0413_checked (by decide +kernel)
theorem record007_leaf_checked_95 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 95)
      (record007_certificates 95) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 95)
    (.matching Nonrational.InducedTerminalMatches.M012.r0414) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 95) Nonrational.InducedTerminalMatches.M012.r0414
    Nonrational.InducedTerminalMatches.M012.r0414_checked (by decide +kernel)
theorem record007_leaf_checked_96 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 96)
      (record007_certificates 96) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 96)
    (.matching Nonrational.InducedTerminalMatches.M012.r0415) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 96) Nonrational.InducedTerminalMatches.M012.r0415
    Nonrational.InducedTerminalMatches.M012.r0415_checked (by decide +kernel)
theorem record007_leaf_checked_97 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 97)
      (record007_certificates 97) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 97)
    (.matching Nonrational.InducedTerminalMatches.M013.r0416) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 97) Nonrational.InducedTerminalMatches.M013.r0416
    Nonrational.InducedTerminalMatches.M013.r0416_checked (by decide +kernel)
theorem record007_leaf_checked_98 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 98)
      (record007_certificates 98) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 98)
    (.matching Nonrational.InducedTerminalMatches.M013.r0417) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 98) Nonrational.InducedTerminalMatches.M013.r0417
    Nonrational.InducedTerminalMatches.M013.r0417_checked (by decide +kernel)
theorem record007_leaf_checked_99 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 99)
      (record007_certificates 99) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 99)
    (.matching Nonrational.InducedTerminalMatches.M013.r0418) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 99) Nonrational.InducedTerminalMatches.M013.r0418
    Nonrational.InducedTerminalMatches.M013.r0418_checked (by decide +kernel)
theorem record007_leaf_checked_100 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 100)
      (record007_certificates 100) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 100)
    (.matching Nonrational.InducedTerminalMatches.M013.r0419) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 100) Nonrational.InducedTerminalMatches.M013.r0419
    Nonrational.InducedTerminalMatches.M013.r0419_checked (by decide +kernel)
theorem record007_leaf_checked_101 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 101)
      (record007_certificates 101) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 101)
    (.matching Nonrational.InducedTerminalMatches.M013.r0420) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 101) Nonrational.InducedTerminalMatches.M013.r0420
    Nonrational.InducedTerminalMatches.M013.r0420_checked (by decide +kernel)
theorem record007_leaf_checked_102 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 102)
      (record007_certificates 102) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 102)
    (.matching Nonrational.InducedTerminalMatches.M013.r0421) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 102) Nonrational.InducedTerminalMatches.M013.r0421
    Nonrational.InducedTerminalMatches.M013.r0421_checked (by decide +kernel)
theorem record007_leaf_checked_103 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 103)
      (record007_certificates 103) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 103)
    (.matching Nonrational.InducedTerminalMatches.M013.r0422) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 103) Nonrational.InducedTerminalMatches.M013.r0422
    Nonrational.InducedTerminalMatches.M013.r0422_checked (by decide +kernel)
theorem record007_leaf_checked_104 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 104)
      (record007_certificates 104) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 104)
    (.matching Nonrational.InducedTerminalMatches.M013.r0423) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 104) Nonrational.InducedTerminalMatches.M013.r0423
    Nonrational.InducedTerminalMatches.M013.r0423_checked (by decide +kernel)
theorem record007_leaf_checked_105 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 105)
      (record007_certificates 105) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 105)
    (.matching Nonrational.InducedTerminalMatches.M013.r0424) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 105) Nonrational.InducedTerminalMatches.M013.r0424
    Nonrational.InducedTerminalMatches.M013.r0424_checked (by decide +kernel)
theorem record007_leaf_checked_106 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 106)
      (record007_certificates 106) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 106)
    (.matching Nonrational.InducedTerminalMatches.M013.r0425) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 106) Nonrational.InducedTerminalMatches.M013.r0425
    Nonrational.InducedTerminalMatches.M013.r0425_checked (by decide +kernel)
theorem record007_leaf_checked_107 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 107)
      (record007_certificates 107) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 107)
    (.matching Nonrational.InducedTerminalMatches.M013.r0426) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 107) Nonrational.InducedTerminalMatches.M013.r0426
    Nonrational.InducedTerminalMatches.M013.r0426_checked (by decide +kernel)
theorem record007_leaf_checked_108 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 108)
      (record007_certificates 108) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 108)
    (.matching Nonrational.InducedTerminalMatches.M013.r0427) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 108) Nonrational.InducedTerminalMatches.M013.r0427
    Nonrational.InducedTerminalMatches.M013.r0427_checked (by decide +kernel)
theorem record007_leaf_checked_109 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 109)
      (record007_certificates 109) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 109)
    (.matching Nonrational.InducedTerminalMatches.M013.r0428) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 109) Nonrational.InducedTerminalMatches.M013.r0428
    Nonrational.InducedTerminalMatches.M013.r0428_checked (by decide +kernel)
theorem record007_leaf_checked_110 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 110)
      (record007_certificates 110) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 110)
    (.matching Nonrational.InducedTerminalMatches.M013.r0429) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 110) Nonrational.InducedTerminalMatches.M013.r0429
    Nonrational.InducedTerminalMatches.M013.r0429_checked (by decide +kernel)
theorem record007_leaf_checked_111 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 111)
      (record007_certificates 111) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 111)
    (.matching Nonrational.InducedTerminalMatches.M013.r0430) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 111) Nonrational.InducedTerminalMatches.M013.r0430
    Nonrational.InducedTerminalMatches.M013.r0430_checked (by decide +kernel)
theorem record007_leaf_checked_112 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 112)
      (record007_certificates 112) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 112)
    (.matching Nonrational.InducedTerminalMatches.M013.r0431) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 112) Nonrational.InducedTerminalMatches.M013.r0431
    Nonrational.InducedTerminalMatches.M013.r0431_checked (by decide +kernel)
theorem record007_leaf_checked_113 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 113)
      (record007_certificates 113) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 113)
    (.matching Nonrational.InducedTerminalMatches.M013.r0432) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 113) Nonrational.InducedTerminalMatches.M013.r0432
    Nonrational.InducedTerminalMatches.M013.r0432_checked (by decide +kernel)
theorem record007_leaf_checked_114 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 114)
      (record007_certificates 114) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 114)
    (.matching Nonrational.InducedTerminalMatches.M013.r0433) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 114) Nonrational.InducedTerminalMatches.M013.r0433
    Nonrational.InducedTerminalMatches.M013.r0433_checked (by decide +kernel)
theorem record007_leaf_checked_115 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 115)
      (record007_certificates 115) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 115)
    (.matching Nonrational.InducedTerminalMatches.M013.r0434) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 115) Nonrational.InducedTerminalMatches.M013.r0434
    Nonrational.InducedTerminalMatches.M013.r0434_checked (by decide +kernel)
theorem record007_leaf_checked_116 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 116)
      (record007_certificates 116) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 116)
    (.matching Nonrational.InducedTerminalMatches.M013.r0435) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 116) Nonrational.InducedTerminalMatches.M013.r0435
    Nonrational.InducedTerminalMatches.M013.r0435_checked (by decide +kernel)
theorem record007_leaf_checked_117 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 117)
      (record007_certificates 117) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 117)
    (.matching Nonrational.InducedTerminalMatches.M013.r0436) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 117) Nonrational.InducedTerminalMatches.M013.r0436
    Nonrational.InducedTerminalMatches.M013.r0436_checked (by decide +kernel)
theorem record007_leaf_checked_118 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 118)
      (record007_certificates 118) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 118)
    (.matching Nonrational.InducedTerminalMatches.M013.r0437) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 118) Nonrational.InducedTerminalMatches.M013.r0437
    Nonrational.InducedTerminalMatches.M013.r0437_checked (by decide +kernel)
theorem record007_leaf_checked_119 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 119)
      (record007_certificates 119) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 119)
    (.matching Nonrational.InducedTerminalMatches.M013.r0438) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 119) Nonrational.InducedTerminalMatches.M013.r0438
    Nonrational.InducedTerminalMatches.M013.r0438_checked (by decide +kernel)
theorem record007_leaf_checked_120 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 120)
      (record007_certificates 120) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 120)
    (.matching Nonrational.InducedTerminalMatches.M013.r0439) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 120) Nonrational.InducedTerminalMatches.M013.r0439
    Nonrational.InducedTerminalMatches.M013.r0439_checked (by decide +kernel)
theorem record007_leaf_checked_121 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 121)
      (record007_certificates 121) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 121)
    (.matching Nonrational.InducedTerminalMatches.M013.r0440) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 121) Nonrational.InducedTerminalMatches.M013.r0440
    Nonrational.InducedTerminalMatches.M013.r0440_checked (by decide +kernel)
theorem record007_leaf_checked_122 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 122)
      (record007_certificates 122) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 122)
    (.matching Nonrational.InducedTerminalMatches.M013.r0441) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 122) Nonrational.InducedTerminalMatches.M013.r0441
    Nonrational.InducedTerminalMatches.M013.r0441_checked (by decide +kernel)
theorem record007_leaf_checked_123 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 123)
      (record007_certificates 123) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 123)
    (.matching Nonrational.InducedTerminalMatches.M013.r0442) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 123) Nonrational.InducedTerminalMatches.M013.r0442
    Nonrational.InducedTerminalMatches.M013.r0442_checked (by decide +kernel)
theorem record007_leaf_checked_124 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 124)
      (record007_certificates 124) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 124)
    (.matching Nonrational.InducedTerminalMatches.M013.r0443) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 124) Nonrational.InducedTerminalMatches.M013.r0443
    Nonrational.InducedTerminalMatches.M013.r0443_checked (by decide +kernel)
theorem record007_leaf_checked_125 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 125)
      (record007_certificates 125) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 125)
    (.matching Nonrational.InducedTerminalMatches.M013.r0444) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 125) Nonrational.InducedTerminalMatches.M013.r0444
    Nonrational.InducedTerminalMatches.M013.r0444_checked (by decide +kernel)
theorem record007_leaf_checked_126 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 126)
      (record007_certificates 126) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 126)
    (.matching Nonrational.InducedTerminalMatches.M013.r0445) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 126) Nonrational.InducedTerminalMatches.M013.r0445
    Nonrational.InducedTerminalMatches.M013.r0445_checked (by decide +kernel)
theorem record007_leaf_checked_127 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 127)
      (record007_certificates 127) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 127)
    (.matching Nonrational.InducedTerminalMatches.M013.r0446) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 127) Nonrational.InducedTerminalMatches.M013.r0446
    Nonrational.InducedTerminalMatches.M013.r0446_checked (by decide +kernel)
theorem record007_leaf_checked_128 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 128)
      (record007_certificates 128) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 128)
    (.matching Nonrational.InducedTerminalMatches.M013.r0447) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 128) Nonrational.InducedTerminalMatches.M013.r0447
    Nonrational.InducedTerminalMatches.M013.r0447_checked (by decide +kernel)
theorem record007_leaf_checked_129 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 129)
      (record007_certificates 129) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 129)
    (.matching Nonrational.InducedTerminalMatches.M014.r0448) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 129) Nonrational.InducedTerminalMatches.M014.r0448
    Nonrational.InducedTerminalMatches.M014.r0448_checked (by decide +kernel)
theorem record007_leaf_checked_130 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 130)
      (record007_certificates 130) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 130)
    (.matching Nonrational.InducedTerminalMatches.M014.r0449) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 130) Nonrational.InducedTerminalMatches.M014.r0449
    Nonrational.InducedTerminalMatches.M014.r0449_checked (by decide +kernel)
theorem record007_leaf_checked_131 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 131)
      (record007_certificates 131) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 131)
    (.matching Nonrational.InducedTerminalMatches.M014.r0450) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 131) Nonrational.InducedTerminalMatches.M014.r0450
    Nonrational.InducedTerminalMatches.M014.r0450_checked (by decide +kernel)
theorem record007_leaf_checked_132 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 132)
      (record007_certificates 132) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 132)
    (.matching Nonrational.InducedTerminalMatches.M014.r0451) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 132) Nonrational.InducedTerminalMatches.M014.r0451
    Nonrational.InducedTerminalMatches.M014.r0451_checked (by decide +kernel)
theorem record007_leaf_checked_133 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 133)
      (record007_certificates 133) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 133)
    (.matching Nonrational.InducedTerminalMatches.M014.r0452) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 133) Nonrational.InducedTerminalMatches.M014.r0452
    Nonrational.InducedTerminalMatches.M014.r0452_checked (by decide +kernel)
theorem record007_leaf_checked_134 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 134)
      (record007_certificates 134) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 134)
    (.matching Nonrational.InducedTerminalMatches.M014.r0453) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 134) Nonrational.InducedTerminalMatches.M014.r0453
    Nonrational.InducedTerminalMatches.M014.r0453_checked (by decide +kernel)
theorem record007_leaf_checked_135 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 135)
      (record007_certificates 135) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 135)
    (.matching Nonrational.InducedTerminalMatches.M014.r0454) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 135) Nonrational.InducedTerminalMatches.M014.r0454
    Nonrational.InducedTerminalMatches.M014.r0454_checked (by decide +kernel)
theorem record007_leaf_checked_136 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 136)
      (record007_certificates 136) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 136)
    (.matching Nonrational.InducedTerminalMatches.M014.r0455) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 136) Nonrational.InducedTerminalMatches.M014.r0455
    Nonrational.InducedTerminalMatches.M014.r0455_checked (by decide +kernel)
theorem record007_leaf_checked_137 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 137)
      (record007_certificates 137) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 137)
    (.matching Nonrational.InducedTerminalMatches.M014.r0456) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 137) Nonrational.InducedTerminalMatches.M014.r0456
    Nonrational.InducedTerminalMatches.M014.r0456_checked (by decide +kernel)
theorem record007_leaf_checked_138 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 138)
      (record007_certificates 138) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 138)
    (.matching Nonrational.InducedTerminalMatches.M014.r0457) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 138) Nonrational.InducedTerminalMatches.M014.r0457
    Nonrational.InducedTerminalMatches.M014.r0457_checked (by decide +kernel)
theorem record007_leaf_checked_139 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 139)
      (record007_certificates 139) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 139)
    (.matching Nonrational.InducedTerminalMatches.M014.r0458) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 139) Nonrational.InducedTerminalMatches.M014.r0458
    Nonrational.InducedTerminalMatches.M014.r0458_checked (by decide +kernel)
theorem record007_leaf_checked_140 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 140)
      (record007_certificates 140) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 140)
    (.matching Nonrational.InducedTerminalMatches.M014.r0459) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 140) Nonrational.InducedTerminalMatches.M014.r0459
    Nonrational.InducedTerminalMatches.M014.r0459_checked (by decide +kernel)
theorem record007_leaf_checked_141 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 141)
      (record007_certificates 141) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 141)
    (.matching Nonrational.InducedTerminalMatches.M014.r0460) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 141) Nonrational.InducedTerminalMatches.M014.r0460
    Nonrational.InducedTerminalMatches.M014.r0460_checked (by decide +kernel)
theorem record007_leaf_checked_142 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 142)
      (record007_certificates 142) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 142)
    (.matching Nonrational.InducedTerminalMatches.M014.r0461) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 142) Nonrational.InducedTerminalMatches.M014.r0461
    Nonrational.InducedTerminalMatches.M014.r0461_checked (by decide +kernel)
theorem record007_leaf_checked_143 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 143)
      (record007_certificates 143) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 143)
    (.matching Nonrational.InducedTerminalMatches.M014.r0462) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 143) Nonrational.InducedTerminalMatches.M014.r0462
    Nonrational.InducedTerminalMatches.M014.r0462_checked (by decide +kernel)
theorem record007_leaf_checked_144 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 144)
      (record007_certificates 144) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 144)
    (.matching Nonrational.InducedTerminalMatches.M014.r0463) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 144) Nonrational.InducedTerminalMatches.M014.r0463
    Nonrational.InducedTerminalMatches.M014.r0463_checked (by decide +kernel)
theorem record007_leaf_checked_145 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 145)
      (record007_certificates 145) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 145)
    (.matching Nonrational.InducedTerminalMatches.M014.r0464) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 145) Nonrational.InducedTerminalMatches.M014.r0464
    Nonrational.InducedTerminalMatches.M014.r0464_checked (by decide +kernel)
theorem record007_leaf_checked_146 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 146)
      (record007_certificates 146) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 146)
    (.matching Nonrational.InducedTerminalMatches.M014.r0465) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 146) Nonrational.InducedTerminalMatches.M014.r0465
    Nonrational.InducedTerminalMatches.M014.r0465_checked (by decide +kernel)
theorem record007_leaf_checked_147 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 147)
      (record007_certificates 147) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 147)
    (.matching Nonrational.InducedTerminalMatches.M014.r0466) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 147) Nonrational.InducedTerminalMatches.M014.r0466
    Nonrational.InducedTerminalMatches.M014.r0466_checked (by decide +kernel)
theorem record007_leaf_checked_148 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 148)
      (record007_certificates 148) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 148)
    (.matching Nonrational.InducedTerminalMatches.M014.r0467) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 148) Nonrational.InducedTerminalMatches.M014.r0467
    Nonrational.InducedTerminalMatches.M014.r0467_checked (by decide +kernel)
theorem record007_leaf_checked_149 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 149)
      (record007_certificates 149) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 149)
    (.matching Nonrational.InducedTerminalMatches.M014.r0468) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 149) Nonrational.InducedTerminalMatches.M014.r0468
    Nonrational.InducedTerminalMatches.M014.r0468_checked (by decide +kernel)
theorem record007_leaf_checked_150 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 150)
      (record007_certificates 150) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 150)
    (.matching Nonrational.InducedTerminalMatches.M014.r0469) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 150) Nonrational.InducedTerminalMatches.M014.r0469
    Nonrational.InducedTerminalMatches.M014.r0469_checked (by decide +kernel)
theorem record007_leaf_checked_151 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 151)
      (record007_certificates 151) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 151)
    (.matching Nonrational.InducedTerminalMatches.M014.r0470) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 151) Nonrational.InducedTerminalMatches.M014.r0470
    Nonrational.InducedTerminalMatches.M014.r0470_checked (by decide +kernel)
theorem record007_leaf_checked_152 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 152)
      (record007_certificates 152) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 152)
    (.matching Nonrational.InducedTerminalMatches.M014.r0471) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 152) Nonrational.InducedTerminalMatches.M014.r0471
    Nonrational.InducedTerminalMatches.M014.r0471_checked (by decide +kernel)
theorem record007_leaf_checked_153 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 153)
      (record007_certificates 153) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 153)
    (.matching Nonrational.InducedTerminalMatches.M014.r0472) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 153) Nonrational.InducedTerminalMatches.M014.r0472
    Nonrational.InducedTerminalMatches.M014.r0472_checked (by decide +kernel)
theorem record007_leaf_checked_154 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 154)
      (record007_certificates 154) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 154)
    (.matching Nonrational.InducedTerminalMatches.M014.r0473) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 154) Nonrational.InducedTerminalMatches.M014.r0473
    Nonrational.InducedTerminalMatches.M014.r0473_checked (by decide +kernel)
theorem record007_leaf_checked_155 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 155)
      (record007_certificates 155) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 155)
    (.matching Nonrational.InducedTerminalMatches.M014.r0474) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 155) Nonrational.InducedTerminalMatches.M014.r0474
    Nonrational.InducedTerminalMatches.M014.r0474_checked (by decide +kernel)
theorem record007_leaf_checked_156 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 156)
      (record007_certificates 156) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 156)
    (.matching Nonrational.InducedTerminalMatches.M014.r0475) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 156) Nonrational.InducedTerminalMatches.M014.r0475
    Nonrational.InducedTerminalMatches.M014.r0475_checked (by decide +kernel)
theorem record007_leaf_checked_157 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 157)
      (record007_certificates 157) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 157)
    (.matching Nonrational.InducedTerminalMatches.M014.r0476) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 157) Nonrational.InducedTerminalMatches.M014.r0476
    Nonrational.InducedTerminalMatches.M014.r0476_checked (by decide +kernel)
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (Fin.cases record007_leaf_checked_1 (Fin.cases record007_leaf_checked_2 (Fin.cases record007_leaf_checked_3 (Fin.cases record007_leaf_checked_4 (Fin.cases record007_leaf_checked_5 (Fin.cases record007_leaf_checked_6 (Fin.cases record007_leaf_checked_7 (Fin.cases record007_leaf_checked_8 (Fin.cases record007_leaf_checked_9 (Fin.cases record007_leaf_checked_10 (Fin.cases record007_leaf_checked_11 (Fin.cases record007_leaf_checked_12 (Fin.cases record007_leaf_checked_13 (Fin.cases record007_leaf_checked_14 (Fin.cases record007_leaf_checked_15 (Fin.cases record007_leaf_checked_16 (Fin.cases record007_leaf_checked_17 (Fin.cases record007_leaf_checked_18 (Fin.cases record007_leaf_checked_19 (Fin.cases record007_leaf_checked_20 (Fin.cases record007_leaf_checked_21 (Fin.cases record007_leaf_checked_22 (Fin.cases record007_leaf_checked_23 (Fin.cases record007_leaf_checked_24 (Fin.cases record007_leaf_checked_25 (Fin.cases record007_leaf_checked_26 (Fin.cases record007_leaf_checked_27 (Fin.cases record007_leaf_checked_28 (Fin.cases record007_leaf_checked_29 (Fin.cases record007_leaf_checked_30 (Fin.cases record007_leaf_checked_31 (Fin.cases record007_leaf_checked_32 (Fin.cases record007_leaf_checked_33 (Fin.cases record007_leaf_checked_34 (Fin.cases record007_leaf_checked_35 (Fin.cases record007_leaf_checked_36 (Fin.cases record007_leaf_checked_37 (Fin.cases record007_leaf_checked_38 (Fin.cases record007_leaf_checked_39 (Fin.cases record007_leaf_checked_40 (Fin.cases record007_leaf_checked_41 (Fin.cases record007_leaf_checked_42 (Fin.cases record007_leaf_checked_43 (Fin.cases record007_leaf_checked_44 (Fin.cases record007_leaf_checked_45 (Fin.cases record007_leaf_checked_46 (Fin.cases record007_leaf_checked_47 (Fin.cases record007_leaf_checked_48 (Fin.cases record007_leaf_checked_49 (Fin.cases record007_leaf_checked_50 (Fin.cases record007_leaf_checked_51 (Fin.cases record007_leaf_checked_52 (Fin.cases record007_leaf_checked_53 (Fin.cases record007_leaf_checked_54 (Fin.cases record007_leaf_checked_55 (Fin.cases record007_leaf_checked_56 (Fin.cases record007_leaf_checked_57 (Fin.cases record007_leaf_checked_58 (Fin.cases record007_leaf_checked_59 (Fin.cases record007_leaf_checked_60 (Fin.cases record007_leaf_checked_61 (Fin.cases record007_leaf_checked_62 (Fin.cases record007_leaf_checked_63 (Fin.cases record007_leaf_checked_64 (Fin.cases record007_leaf_checked_65 (Fin.cases record007_leaf_checked_66 (Fin.cases record007_leaf_checked_67 (Fin.cases record007_leaf_checked_68 (Fin.cases record007_leaf_checked_69 (Fin.cases record007_leaf_checked_70 (Fin.cases record007_leaf_checked_71 (Fin.cases record007_leaf_checked_72 (Fin.cases record007_leaf_checked_73 (Fin.cases record007_leaf_checked_74 (Fin.cases record007_leaf_checked_75 (Fin.cases record007_leaf_checked_76 (Fin.cases record007_leaf_checked_77 (Fin.cases record007_leaf_checked_78 (Fin.cases record007_leaf_checked_79 (Fin.cases record007_leaf_checked_80 (Fin.cases record007_leaf_checked_81 (Fin.cases record007_leaf_checked_82 (Fin.cases record007_leaf_checked_83 (Fin.cases record007_leaf_checked_84 (Fin.cases record007_leaf_checked_85 (Fin.cases record007_leaf_checked_86 (Fin.cases record007_leaf_checked_87 (Fin.cases record007_leaf_checked_88 (Fin.cases record007_leaf_checked_89 (Fin.cases record007_leaf_checked_90 (Fin.cases record007_leaf_checked_91 (Fin.cases record007_leaf_checked_92 (Fin.cases record007_leaf_checked_93 (Fin.cases record007_leaf_checked_94 (Fin.cases record007_leaf_checked_95 (Fin.cases record007_leaf_checked_96 (Fin.cases record007_leaf_checked_97 (Fin.cases record007_leaf_checked_98 (Fin.cases record007_leaf_checked_99 (Fin.cases record007_leaf_checked_100 (Fin.cases record007_leaf_checked_101 (Fin.cases record007_leaf_checked_102 (Fin.cases record007_leaf_checked_103 (Fin.cases record007_leaf_checked_104 (Fin.cases record007_leaf_checked_105 (Fin.cases record007_leaf_checked_106 (Fin.cases record007_leaf_checked_107 (Fin.cases record007_leaf_checked_108 (Fin.cases record007_leaf_checked_109 (Fin.cases record007_leaf_checked_110 (Fin.cases record007_leaf_checked_111 (Fin.cases record007_leaf_checked_112 (Fin.cases record007_leaf_checked_113 (Fin.cases record007_leaf_checked_114 (Fin.cases record007_leaf_checked_115 (Fin.cases record007_leaf_checked_116 (Fin.cases record007_leaf_checked_117 (Fin.cases record007_leaf_checked_118 (Fin.cases record007_leaf_checked_119 (Fin.cases record007_leaf_checked_120 (Fin.cases record007_leaf_checked_121 (Fin.cases record007_leaf_checked_122 (Fin.cases record007_leaf_checked_123 (Fin.cases record007_leaf_checked_124 (Fin.cases record007_leaf_checked_125 (Fin.cases record007_leaf_checked_126 (Fin.cases record007_leaf_checked_127 (Fin.cases record007_leaf_checked_128 (Fin.cases record007_leaf_checked_129 (Fin.cases record007_leaf_checked_130 (Fin.cases record007_leaf_checked_131 (Fin.cases record007_leaf_checked_132 (Fin.cases record007_leaf_checked_133 (Fin.cases record007_leaf_checked_134 (Fin.cases record007_leaf_checked_135 (Fin.cases record007_leaf_checked_136 (Fin.cases record007_leaf_checked_137 (Fin.cases record007_leaf_checked_138 (Fin.cases record007_leaf_checked_139 (Fin.cases record007_leaf_checked_140 (Fin.cases record007_leaf_checked_141 (Fin.cases record007_leaf_checked_142 (Fin.cases record007_leaf_checked_143 (Fin.cases record007_leaf_checked_144 (Fin.cases record007_leaf_checked_145 (Fin.cases record007_leaf_checked_146 (Fin.cases record007_leaf_checked_147 (Fin.cases record007_leaf_checked_148 (Fin.cases record007_leaf_checked_149 (Fin.cases record007_leaf_checked_150 (Fin.cases record007_leaf_checked_151 (Fin.cases record007_leaf_checked_152 (Fin.cases record007_leaf_checked_153 (Fin.cases record007_leaf_checked_154 (Fin.cases record007_leaf_checked_155 (Fin.cases record007_leaf_checked_156 (Fin.cases record007_leaf_checked_157 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record007_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033
