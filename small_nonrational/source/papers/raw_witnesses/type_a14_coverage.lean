module
prelude
public import Papers.RawWitnesses.TypeA14Data
public import Papers.RawWitnesses.TypeA14Coverage00
public import Papers.RawWitnesses.TypeA14Coverage01
public import Papers.RawWitnesses.TypeA14Coverage02
public import Papers.RawWitnesses.TypeA14Coverage03
public import Papers.RawWitnesses.TypeA14Coverage04
public import Papers.RawWitnesses.TypeA14Coverage05
public import Papers.RawWitnesses.TypeA14Coverage06
public import Papers.RawWitnesses.TypeA14Coverage07
public import Papers.RawWitnesses.TypeA14Coverage08
public import Papers.RawWitnesses.TypeA14Coverage09
public import Papers.RawWitnesses.TypeA14Coverage10
public import Papers.RawWitnesses.TypeA14Coverage11
public import Papers.RawWitnesses.TypeA14Coverage12
public import Papers.RawWitnesses.TypeA14Coverage13
public import Papers.RawWitnesses.TypeA14Coverage14
public import Papers.RawWitnesses.TypeA14Coverage15
public import Papers.RawWitnesses.TypeA14Coverage16
public import Papers.RawWitnesses.TypeA14Coverage17
public import Papers.RawWitnesses.TypeA14Coverage18
public import Papers.RawWitnesses.TypeA14Coverage19
public import Papers.RawWitnesses.TypeA14Coverage20
public import Papers.RawWitnesses.TypeA14Coverage21
public import Papers.RawWitnesses.TypeA14Coverage22
public import Papers.RawWitnesses.TypeA14Coverage23
public import Papers.RawWitnesses.TypeA14Coverage24
public import Papers.RawWitnesses.TypeA14Coverage25
public import Papers.RawWitnesses.TypeA14Coverage26
public import Papers.RawWitnesses.TypeA14Coverage27
public import Papers.RawWitnesses.TypeA14Coverage28
public import Papers.RawWitnesses.TypeA14Coverage29
public import Papers.RawWitnesses.TypeA14Coverage30
public import Papers.RawWitnesses.TypeA14Coverage31

/-! Small ordinary kernel checks for Appendix B type A14. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA14
open Papers.RationalWitnesses.Raw

theorem coverage_check : Coverage certificate :=
  (forallMask_succ (n := 9) (fun tail => Covered certificate tail)
    (forallMask_succ (n := 8) (fun tail => Covered certificate (Fin.cases false tail))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases false (Fin.cases false tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_00
    coverage_chunk_01)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_02
    coverage_chunk_03))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_04
    coverage_chunk_05)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_06
    coverage_chunk_07)))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases false (Fin.cases true tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_08
    coverage_chunk_09)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_10
    coverage_chunk_11))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_12
    coverage_chunk_13)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_14
    coverage_chunk_15))))
    (forallMask_succ (n := 8) (fun tail => Covered certificate (Fin.cases true tail))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases true (Fin.cases false tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_16
    coverage_chunk_17)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_18
    coverage_chunk_19))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_20
    coverage_chunk_21)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_22
    coverage_chunk_23)))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases true (Fin.cases true tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_24
    coverage_chunk_25)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_26
    coverage_chunk_27))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_28
    coverage_chunk_29)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_30
    coverage_chunk_31)))))

end Papers.RationalWitnesses.RawWitnesses.TypeA14
