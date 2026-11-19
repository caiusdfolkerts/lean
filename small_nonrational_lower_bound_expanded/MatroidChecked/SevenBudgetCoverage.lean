module
prelude
public import Init.Omega
public import Init.ByCases
public import Init.RCases
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Lemmas

@[expose] public section

/-! Exact Appendix C.3 numerical budget coverage.
The descriptor functions use ordinary natural-number cases so this finite
module imports only Lean Init. All mathematical predicates, literal rows, and coverage statements are preserved.
The bounded searches use List.any and split the mixed case by its34 root indices
to limit kernel memory. Proof-producing reduction remains mandatory.
The list contains one harmless extra nonpentagonal mixed budget.
No geometric hypothesis or facet-template completeness is asserted here. -/

namespace Papers.RationalityTen.MatroidChecked.SevenBudgetCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Descriptor where
  triangles : Nat
  quads : Nat
  pentagons : Nat
  hexagons : Nat
  deriving DecidableEq

def six (i : Fin 7) : Descriptor :=
  match i.val with
  | 0 => ⟨8,0,0,0⟩
  | 1 => ⟨6,1,0,0⟩
  | 2 => ⟨8,0,0,0⟩
  | 3 => ⟨6,1,0,0⟩
  | 4 => ⟨5,0,1,0⟩
  | 5 => ⟨4,2,0,0⟩
  | _ => ⟨2,3,0,0⟩

def seven (i : Fin 34) : Descriptor :=
  match i.val with
  | 0 => ⟨10,0,0,0⟩
  | 1 => ⟨10,0,0,0⟩
  | 2 => ⟨8,1,0,0⟩
  | 3 => ⟨8,1,0,0⟩
  | 4 => ⟨10,0,0,0⟩
  | 5 => ⟨10,0,0,0⟩
  | 6 => ⟨8,1,0,0⟩
  | 7 => ⟨8,1,0,0⟩
  | 8 => ⟨8,1,0,0⟩
  | 9 => ⟨8,1,0,0⟩
  | 10 => ⟨7,0,1,0⟩
  | 11 => ⟨6,2,0,0⟩
  | 12 => ⟨6,2,0,0⟩
  | 13 => ⟨4,3,0,0⟩
  | 14 => ⟨10,0,0,0⟩
  | 15 => ⟨8,1,0,0⟩
  | 16 => ⟨8,1,0,0⟩
  | 17 => ⟨7,0,1,0⟩
  | 18 => ⟨6,2,0,0⟩
  | 19 => ⟨6,2,0,0⟩
  | 20 => ⟨6,2,0,0⟩
  | 21 => ⟨6,2,0,0⟩
  | 22 => ⟨6,0,0,1⟩
  | 23 => ⟨6,2,0,0⟩
  | 24 => ⟨6,2,0,0⟩
  | 25 => ⟨4,3,0,0⟩
  | 26 => ⟨5,1,1,0⟩
  | 27 => ⟨4,3,0,0⟩
  | 28 => ⟨6,2,0,0⟩
  | 29 => ⟨4,3,0,0⟩
  | 30 => ⟨5,1,1,0⟩
  | 31 => ⟨4,3,0,0⟩
  | 32 => ⟨3,2,1,0⟩
  | _ => ⟨2,4,0,0⟩

def epsilonSeven (i : Fin 34) : Nat := if i = 13 then 1 else 0
def epsilonSix (i : Fin 7) : Nat := if i = 6 then 1 else 0

theorem epsilonSeven_le (i : Fin 34) : epsilonSeven i ≤ 1 := by
  unfold epsilonSeven; split <;> omega
theorem epsilonSix_le (i : Fin 7) : epsilonSix i ≤ 1 := by
  unfold epsilonSix; split <;> omega

structure CaseRow where
  template : Nat
  sixTemplate : Option Nat
  m : Nat
  E : Nat
  q : Nat
  SP : Nat
  BP : Nat
  T : Nat
  pentagons : Nat
  deriving DecidableEq

def noSixCases : List CaseRow :=
  [⟨0,none,11,12,3,6,3,1,0⟩,
   ⟨1,none,11,12,3,6,3,1,0⟩,
   ⟨2,none,10,12,2,3,6,0,0⟩,
   ⟨2,none,10,12,3,5,4,0,0⟩,
   ⟨2,none,11,12,3,5,4,1,0⟩,
   ⟨3,none,10,12,2,3,6,0,0⟩,
   ⟨3,none,10,12,3,5,4,0,0⟩,
   ⟨3,none,11,12,3,5,4,1,0⟩,
   ⟨4,none,11,12,3,6,3,1,0⟩,
   ⟨5,none,11,12,3,6,3,1,0⟩,
   ⟨6,none,10,12,2,3,6,0,0⟩,
   ⟨6,none,10,12,3,5,4,0,0⟩,
   ⟨6,none,11,12,3,5,4,1,0⟩,
   ⟨7,none,10,12,2,3,6,0,0⟩,
   ⟨7,none,10,12,3,5,4,0,0⟩,
   ⟨7,none,11,12,3,5,4,1,0⟩,
   ⟨8,none,10,12,2,3,6,0,0⟩,
   ⟨8,none,10,12,3,5,4,0,0⟩,
   ⟨8,none,11,12,3,5,4,1,0⟩,
   ⟨9,none,10,12,2,3,6,0,0⟩,
   ⟨9,none,10,12,3,5,4,0,0⟩,
   ⟨9,none,11,12,3,5,4,1,0⟩,
   ⟨11,none,10,12,2,2,7,0,0⟩,
   ⟨11,none,10,12,3,4,5,0,0⟩,
   ⟨11,none,11,12,3,4,5,1,0⟩,
   ⟨12,none,10,12,2,2,7,0,0⟩,
   ⟨12,none,10,12,3,4,5,0,0⟩,
   ⟨12,none,11,12,3,4,5,1,0⟩,
   ⟨13,none,10,12,3,3,6,0,0⟩,
   ⟨13,none,10,12,4,5,4,0,0⟩,
   ⟨13,none,11,12,3,3,6,1,0⟩,
   ⟨13,none,11,12,4,5,4,1,0⟩,
   ⟨13,none,12,12,4,5,4,2,0⟩,
   ⟨14,none,11,12,3,6,3,1,0⟩,
   ⟨15,none,10,12,2,3,6,0,0⟩,
   ⟨15,none,10,12,3,5,4,0,0⟩,
   ⟨15,none,11,12,3,5,4,1,0⟩,
   ⟨16,none,10,12,2,3,6,0,0⟩,
   ⟨16,none,10,12,3,5,4,0,0⟩,
   ⟨16,none,11,12,3,5,4,1,0⟩,
   ⟨18,none,10,12,2,2,7,0,0⟩,
   ⟨18,none,10,12,3,4,5,0,0⟩,
   ⟨18,none,11,12,3,4,5,1,0⟩,
   ⟨19,none,10,12,2,2,7,0,0⟩,
   ⟨19,none,10,12,3,4,5,0,0⟩,
   ⟨19,none,11,12,3,4,5,1,0⟩,
   ⟨20,none,10,12,2,2,7,0,0⟩,
   ⟨20,none,10,12,3,4,5,0,0⟩,
   ⟨20,none,11,12,3,4,5,1,0⟩,
   ⟨21,none,10,12,2,2,7,0,0⟩,
   ⟨21,none,10,12,3,4,5,0,0⟩,
   ⟨21,none,11,12,3,4,5,1,0⟩,
   ⟨23,none,10,12,2,2,7,0,0⟩,
   ⟨23,none,10,12,3,4,5,0,0⟩,
   ⟨23,none,11,12,3,4,5,1,0⟩,
   ⟨24,none,10,12,2,2,7,0,0⟩,
   ⟨24,none,10,12,3,4,5,0,0⟩,
   ⟨24,none,11,12,3,4,5,1,0⟩,
   ⟨25,none,10,12,3,3,6,0,0⟩,
   ⟨25,none,11,12,3,3,6,1,0⟩,
   ⟨27,none,10,12,3,3,6,0,0⟩,
   ⟨27,none,11,12,3,3,6,1,0⟩,
   ⟨28,none,10,12,2,2,7,0,0⟩,
   ⟨28,none,10,12,3,4,5,0,0⟩,
   ⟨28,none,11,12,3,4,5,1,0⟩,
   ⟨29,none,10,12,3,3,6,0,0⟩,
   ⟨29,none,11,12,3,3,6,1,0⟩,
   ⟨31,none,10,12,3,3,6,0,0⟩,
   ⟨31,none,11,12,3,3,6,1,0⟩]

def oneSixCases : List CaseRow :=
  [⟨2,(some 6),10,13,5,6,2,0,0⟩,
   ⟨3,(some 6),10,13,5,6,2,0,0⟩,
   ⟨6,(some 6),10,13,5,6,2,0,0⟩,
   ⟨7,(some 6),10,13,5,6,2,0,0⟩,
   ⟨8,(some 6),10,13,5,6,2,0,0⟩,
   ⟨9,(some 6),10,13,5,6,2,0,0⟩,
   ⟨11,(some 6),10,13,5,5,3,0,0⟩,
   ⟨12,(some 6),10,13,5,5,3,0,0⟩,
   ⟨13,(some 0),10,13,5,7,1,0,0⟩,
   ⟨13,(some 1),10,13,5,6,2,0,0⟩,
   ⟨13,(some 2),10,13,5,7,1,0,0⟩,
   ⟨13,(some 3),10,13,5,6,2,0,0⟩,
   ⟨13,(some 5),10,13,5,5,3,0,0⟩,
   ⟨13,(some 6),10,13,5,4,4,0,0⟩,
   ⟨13,(some 6),10,13,6,6,2,0,0⟩,
   ⟨13,(some 6),11,13,6,6,2,1,0⟩,
   ⟨15,(some 6),10,13,5,6,2,0,0⟩,
   ⟨16,(some 6),10,13,5,6,2,0,0⟩,
   ⟨18,(some 6),10,13,5,5,3,0,0⟩,
   ⟨19,(some 6),10,13,5,5,3,0,0⟩,
   ⟨20,(some 6),10,13,5,5,3,0,0⟩,
   ⟨21,(some 6),10,13,5,5,3,0,0⟩,
   ⟨23,(some 6),10,13,5,5,3,0,0⟩,
   ⟨24,(some 6),10,13,5,5,3,0,0⟩,
   ⟨25,(some 6),10,13,5,4,4,0,0⟩,
   ⟨27,(some 6),10,13,5,4,4,0,0⟩,
   ⟨28,(some 6),10,13,5,5,3,0,0⟩,
   ⟨29,(some 6),10,13,5,4,4,0,0⟩,
   ⟨31,(some 6),10,13,5,4,4,0,0⟩,
   ⟨33,(some 6),10,13,5,3,5,0,0⟩,
   ⟨10,(some 4),10,13,2,4,4,0,1⟩,
   ⟨17,(some 4),10,13,2,4,4,0,1⟩,
   ⟨26,(some 4),10,13,2,3,5,0,1⟩,
   ⟨30,(some 4),10,13,2,3,5,0,1⟩]

def NoSixAdmissible (i : Fin 34) (m q : Nat) : Prop :=
  (seven i).pentagons = 0 ∧ (seven i).hexagons = 0 ∧
  10 ≤ m ∧ m ≤ 12 ∧ 11-m ≤ (seven i).quads ∧ (seven i).quads ≤ 3 ∧
  (seven i).quads ≤ q ∧ m-8 ≤ q ∧ q ≤ 3 + epsilonSeven i ∧
  (seven i).quads ≤ 2*q ∧ 2*q ≤ 9 + (seven i).quads

def NoSixMatches (i : Fin 34) (m q : Nat) (B : CaseRow) : Prop :=
  B.template = i.val ∧ B.sixTemplate = none ∧ B.m = m ∧ B.E = 12 ∧ B.q = q ∧
  B.SP = 2*q - (seven i).quads ∧ B.BP = 9 + (seven i).quads - 2*q ∧
  B.T = m-10 ∧ B.pentagons = 0

def OneSixAdmissible (i : Fin 34) (j : Fin 7) (m q : Nat) : Prop :=
  (seven i).pentagons = 0 ∧ (seven i).hexagons = 0 ∧ (six j).pentagons = 0 ∧
  (six j).hexagons = 0 ∧ 11-m ≤ (seven i).quads ∧
  ((m = 10 ∧ q = 5 ∧ 1 ≤ epsilonSeven i + epsilonSix j) ∨
    ((m = 10 ∨ m = 11) ∧ q = 6 ∧ epsilonSeven i = 1 ∧ epsilonSix j = 1)) ∧
  (seven i).quads + (six j).quads ≤ 2*q ∧
  2*q ≤ 8 + (seven i).quads + (six j).quads

def OneSixMatches (i : Fin 34) (j : Fin 7) (m q : Nat) (B : CaseRow) : Prop :=
  B.template = i.val ∧ B.sixTemplate = some j.val ∧ B.m = m ∧ B.E = 13 ∧ B.q = q ∧
  B.SP = 2*q - ((seven i).quads + (six j).quads) ∧
  B.BP = 8 + (seven i).quads + (six j).quads - 2*q ∧ B.T = m-10 ∧
  B.pentagons = 0

def PentagonAdmissible (i : Fin 34) : Prop :=
  (seven i).pentagons = 1 ∧ (seven i).hexagons = 0 ∧ (seven i).quads ≤ 1

def PentagonMatches (i : Fin 34) (B : CaseRow) : Prop :=
  B.template = i.val ∧ B.sixTemplate = some 4 ∧ B.m = 10 ∧ B.E = 13 ∧ B.q = 2 ∧
  B.SP = 4 - (seven i).quads ∧ B.BP = 4 + (seven i).quads ∧
  B.T = 0 ∧ B.pentagons = 1

instance (i : Fin 34) (m q : Nat) : Decidable (NoSixAdmissible i m q) := by
  unfold NoSixAdmissible; infer_instance
instance (i : Fin 34) (m q : Nat) (B : CaseRow) : Decidable (NoSixMatches i m q B) := by
  unfold NoSixMatches; infer_instance
instance (i : Fin 34) (j : Fin 7) (m q : Nat) : Decidable (OneSixAdmissible i j m q) := by
  unfold OneSixAdmissible; infer_instance
instance (i : Fin 34) (j : Fin 7) (m q : Nat) (B : CaseRow) :
    Decidable (OneSixMatches i j m q B) := by
  unfold OneSixMatches; infer_instance
instance (i : Fin 34) : Decidable (PentagonAdmissible i) := by
  unfold PentagonAdmissible; infer_instance
instance (i : Fin 34) (B : CaseRow) : Decidable (PentagonMatches i B) := by
  unfold PentagonMatches; infer_instance

private theorem noSixFiniteCheck : ∀ (i : Fin 34) (m : Fin 13) (q : Fin 5),
    NoSixAdmissible i m q →
      (noSixCases.any fun B => decide (NoSixMatches i m q B)) = true := by
  decide +kernel

private theorem noSixFinite : ∀ (i : Fin 34) (m : Fin 13) (q : Fin 5),
    NoSixAdmissible i m q → ∃ B, B ∈ noSixCases ∧ NoSixMatches i m q B := by
  intro i m q h
  obtain ⟨B, hB, hm⟩ := List.any_eq_true.mp (noSixFiniteCheck i m q h)
  exact ⟨B, hB, of_decide_eq_true hm⟩

private theorem oneSixFiniteCheck_00 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 0 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 0 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_01 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 1 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 1 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_02 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 2 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 2 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_03 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 3 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 3 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_04 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 4 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 4 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_05 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 5 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 5 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_06 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 6 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 6 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_07 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 7 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 7 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_08 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 8 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 8 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_09 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 9 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 9 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_10 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 10 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 10 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_11 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 11 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 11 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_12 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 12 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 12 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_13 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 13 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 13 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_14 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 14 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 14 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_15 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 15 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 15 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_16 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 16 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 16 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_17 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 17 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 17 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_18 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 18 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 18 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_19 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 19 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 19 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_20 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 20 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 20 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_21 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 21 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 21 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_22 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 22 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 22 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_23 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 23 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 23 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_24 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 24 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 24 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_25 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 25 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 25 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_26 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 26 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 26 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_27 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 27 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 27 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_28 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 28 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 28 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_29 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 29 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 29 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_30 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 30 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 30 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_31 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 31 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 31 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_32 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 32 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 32 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck_33 : ∀ (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible 33 j m q →
      (oneSixCases.any fun B => decide (OneSixMatches 33 j m q B)) = true := by
  decide +kernel

private theorem oneSixFiniteCheck : ∀ (i : Fin 34) (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible i j m q →
      (oneSixCases.any fun B => decide (OneSixMatches i j m q B)) = true := by
  intro i

  by_cases h0 : i = 0
  · subst i
    exact oneSixFiniteCheck_00

  by_cases h1 : i = 1
  · subst i
    exact oneSixFiniteCheck_01

  by_cases h2 : i = 2
  · subst i
    exact oneSixFiniteCheck_02

  by_cases h3 : i = 3
  · subst i
    exact oneSixFiniteCheck_03

  by_cases h4 : i = 4
  · subst i
    exact oneSixFiniteCheck_04

  by_cases h5 : i = 5
  · subst i
    exact oneSixFiniteCheck_05

  by_cases h6 : i = 6
  · subst i
    exact oneSixFiniteCheck_06

  by_cases h7 : i = 7
  · subst i
    exact oneSixFiniteCheck_07

  by_cases h8 : i = 8
  · subst i
    exact oneSixFiniteCheck_08

  by_cases h9 : i = 9
  · subst i
    exact oneSixFiniteCheck_09

  by_cases h10 : i = 10
  · subst i
    exact oneSixFiniteCheck_10

  by_cases h11 : i = 11
  · subst i
    exact oneSixFiniteCheck_11

  by_cases h12 : i = 12
  · subst i
    exact oneSixFiniteCheck_12

  by_cases h13 : i = 13
  · subst i
    exact oneSixFiniteCheck_13

  by_cases h14 : i = 14
  · subst i
    exact oneSixFiniteCheck_14

  by_cases h15 : i = 15
  · subst i
    exact oneSixFiniteCheck_15

  by_cases h16 : i = 16
  · subst i
    exact oneSixFiniteCheck_16

  by_cases h17 : i = 17
  · subst i
    exact oneSixFiniteCheck_17

  by_cases h18 : i = 18
  · subst i
    exact oneSixFiniteCheck_18

  by_cases h19 : i = 19
  · subst i
    exact oneSixFiniteCheck_19

  by_cases h20 : i = 20
  · subst i
    exact oneSixFiniteCheck_20

  by_cases h21 : i = 21
  · subst i
    exact oneSixFiniteCheck_21

  by_cases h22 : i = 22
  · subst i
    exact oneSixFiniteCheck_22

  by_cases h23 : i = 23
  · subst i
    exact oneSixFiniteCheck_23

  by_cases h24 : i = 24
  · subst i
    exact oneSixFiniteCheck_24

  by_cases h25 : i = 25
  · subst i
    exact oneSixFiniteCheck_25

  by_cases h26 : i = 26
  · subst i
    exact oneSixFiniteCheck_26

  by_cases h27 : i = 27
  · subst i
    exact oneSixFiniteCheck_27

  by_cases h28 : i = 28
  · subst i
    exact oneSixFiniteCheck_28

  by_cases h29 : i = 29
  · subst i
    exact oneSixFiniteCheck_29

  by_cases h30 : i = 30
  · subst i
    exact oneSixFiniteCheck_30

  by_cases h31 : i = 31
  · subst i
    exact oneSixFiniteCheck_31

  by_cases h32 : i = 32
  · subst i
    exact oneSixFiniteCheck_32

  by_cases h33 : i = 33
  · subst i
    exact oneSixFiniteCheck_33

  omega

private theorem oneSixFinite : ∀ (i : Fin 34) (j : Fin 7) (m : Fin 12) (q : Fin 7),
    OneSixAdmissible i j m q → ∃ B, B ∈ oneSixCases ∧ OneSixMatches i j m q B := by
  intro i j m q h
  obtain ⟨B, hB, hm⟩ := List.any_eq_true.mp (oneSixFiniteCheck i j m q h)
  exact ⟨B, hB, of_decide_eq_true hm⟩

theorem no_six_covered (i : Fin 34) (m q : Nat) (h : NoSixAdmissible i m q) :
    ∃ B, B ∈ noSixCases ∧ NoSixMatches i m q B := by
  have he := epsilonSeven_le i
  have hm : m < 13 := by unfold NoSixAdmissible at h; omega
  have hq : q < 5 := by unfold NoSixAdmissible at h; omega
  exact noSixFinite i ⟨m,hm⟩ ⟨q,hq⟩ h

theorem one_six_covered (i : Fin 34) (j : Fin 7) (m q : Nat)
    (h : OneSixAdmissible i j m q) :
    ∃ B, B ∈ oneSixCases ∧ OneSixMatches i j m q B := by
  have hm : m < 12 := by unfold OneSixAdmissible at h; omega
  have hq : q < 7 := by unfold OneSixAdmissible at h; omega
  exact oneSixFinite i j ⟨m,hm⟩ ⟨q,hq⟩ h

private theorem pentagonFiniteCheck : ∀ (i : Fin 34), PentagonAdmissible i →
    (oneSixCases.any fun B => decide (PentagonMatches i B)) = true := by
  decide +kernel

theorem pentagon_covered : ∀ (i : Fin 34), PentagonAdmissible i →
    ∃ B, B ∈ oneSixCases ∧ PentagonMatches i B := by
  intro i h
  obtain ⟨B, hB, hm⟩ := List.any_eq_true.mp (pentagonFiniteCheck i h)
  exact ⟨B, hB, of_decide_eq_true hm⟩

end Papers.RationalityTen.MatroidChecked.SevenBudgetCoverage
