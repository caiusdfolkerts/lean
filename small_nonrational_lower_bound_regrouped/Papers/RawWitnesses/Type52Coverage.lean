module
prelude
public import Papers.RawWitnesses.Type52Data
public import Papers.RawWitnesses.Type52Coverage00
public import Papers.RawWitnesses.Type52Coverage01
public import Papers.RawWitnesses.Type52Coverage02
public import Papers.RawWitnesses.Type52Coverage03
public import Papers.RawWitnesses.Type52Coverage04
public import Papers.RawWitnesses.Type52Coverage05
public import Papers.RawWitnesses.Type52Coverage06
public import Papers.RawWitnesses.Type52Coverage07
public import Papers.RawWitnesses.Type52Coverage08
public import Papers.RawWitnesses.Type52Coverage09
public import Papers.RawWitnesses.Type52Coverage10
public import Papers.RawWitnesses.Type52Coverage11
public import Papers.RawWitnesses.Type52Coverage12
public import Papers.RawWitnesses.Type52Coverage13
public import Papers.RawWitnesses.Type52Coverage14
public import Papers.RawWitnesses.Type52Coverage15
public import Papers.RawWitnesses.Type52Coverage16
public import Papers.RawWitnesses.Type52Coverage17
public import Papers.RawWitnesses.Type52Coverage18
public import Papers.RawWitnesses.Type52Coverage19
public import Papers.RawWitnesses.Type52Coverage20
public import Papers.RawWitnesses.Type52Coverage21
public import Papers.RawWitnesses.Type52Coverage22
public import Papers.RawWitnesses.Type52Coverage23
public import Papers.RawWitnesses.Type52Coverage24
public import Papers.RawWitnesses.Type52Coverage25
public import Papers.RawWitnesses.Type52Coverage26
public import Papers.RawWitnesses.Type52Coverage27
public import Papers.RawWitnesses.Type52Coverage28
public import Papers.RawWitnesses.Type52Coverage29
public import Papers.RawWitnesses.Type52Coverage30
public import Papers.RawWitnesses.Type52Coverage31

/-! Small ordinary kernel checks for Appendix B type 52. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type52
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

end Papers.RationalWitnesses.RawWitnesses.Type52
