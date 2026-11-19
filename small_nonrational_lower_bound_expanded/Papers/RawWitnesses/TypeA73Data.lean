module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typeA73.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA73
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [178, 1, 0, 1, 1],
      [202, 0, 1, -1, -1],
      [202, 0, -1, -1, -1],
      [1400, 7, -9, -5, -10],
      [1400, -7, 9, -5, -10],
      [5690, 21, 18, 15, 25],
      [5690, -21, -18, 15, 25],
      [78, 0, 0, 0, -1],
      [302, 0, 0, 0, 1],
      [178, -1, 0, 1, 1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 14 0 21 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 5320
  spanningInverse := fun i j => (([
      [14, -2, 16, -1, 1],
      [0, 3420, -3420, 380, -380],
      [0, 2660, -2660, 0, 0],
      [1736, -5568, -3336, 408, 656],
      [1092, 2504, 3908, -610, -454]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 3, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([3, -760, -380, -8, 234] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 11700, inverse := fun i j => (([
      [525, 270, -12, -21],
      [-134950, -68400, 3820, 5710],
      [-52850, -22500, 740, 2270],
      [53200, 20340, -1684, -1972]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 3, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([3, -380, 760, 752, -906] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 72480, inverse := fun i j => (([
      [315, 540, -54, -3],
      [22010, -14040, 3820, -1130],
      [69230, 118680, -16700, -2270],
      [-5600, -82080, 5792, 1664]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 3, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([9, -2280, 760, 3396, -2718] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 13590, inverse := fun i j => (([
      [0, 0, 0, 45],
      [-2265, 906, 453, -11400],
      [-10570, -302, 604, -3750],
      [15855, -906, -453, 3390]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([9, 0, 1900, -2304, 702] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 7020, inverse := fun i j => (([
      [0, 0, 0, 90],
      [2925, 234, -117, -2340],
      [0, -468, -156, 19780],
      [4095, -234, 117, -13680]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 4, 5, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([9, 0, -1900, -2304, 702] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3510, inverse := fun i j => (([
      [0, 0, 0, 45],
      [-8775, -702, 351, 7020],
      [0, 234, 78, -9890],
      [12285, 702, -351, -15030]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 5, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 0, 0, 124, -302] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 5, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 13590, inverse := fun i j => (([
      [0, 0, 0, 45],
      [13590, -453, -453, 9060],
      [-15855, 906, 151, -10570],
      [0, 453, 453, -17070]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 3, 4, 7] : List Nat).contains i.val,
        normal := fun i => ([1, 0, 0, 124, 78] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 5460, inverse := fun i j => (([
      [-35, -35, 7, 7],
      [3510, -3510, 390, -390],
      [2730, -2730, 0, 0],
      [-9800, -9800, 1414, 1414]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 3, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([7, -1900, 0, 3528, -2114] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 105700, inverse := fun i j => (([
      [-105, 525, -42, 14],
      [36050, -134950, 17440, -780],
      [52850, -52850, 0, 0],
      [-74060, 53200, -8484, 2828]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 2, 4, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([7, 1900, 0, 3528, -2114] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 105700, inverse := fun i j => (([
      [525, -105, -42, 14],
      [134950, -36050, -17440, 780],
      [52850, -52850, 0, 0],
      [53200, -74060, -8484, 2828]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 4, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([63, -7600, -13300, -5488, 4914] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 24570, inverse := fun i j => (([
      [0, 0, 0, 315],
      [17550, -2574, 312, -22010],
      [0, 1638, 546, -69230],
      [-24570, 1638, 546, -5600]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([3, 380, -760, 752, -906] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 95130, inverse := fun i j => (([
      [0, 0, 0, 315],
      [67950, -9966, 1208, -22010],
      [0, 6342, 2114, -69230],
      [-95130, 6342, 2114, -5600]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([2, 3, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([63, 7600, 13300, -5488, 4914] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 24570, inverse := fun i j => (([
      [0, 0, 0, 315],
      [-17550, 2574, -312, 22010],
      [0, -1638, -546, 69230],
      [-24570, 1638, 546, -5600]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([2, 4, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([3, 760, 380, -8, 234] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 40950, inverse := fun i j => (([
      [0, 0, 0, 525],
      [-3510, -2574, -1092, 134950],
      [-16380, 1638, -546, 52850],
      [-24570, -1638, 546, 53200]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([4, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([9, 2280, -760, 3396, -2718] : List (Int)).getD i.val 0,
        rows := fun i => ([4, 6, 8, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 13590, inverse := fun i j => (([
      [0, 0, 45, 0],
      [-906, -453, 11400, 2265],
      [302, -604, 3750, 10570],
      [-906, -453, 3390, 15855]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => Fin.elim0 k
  relations := fun i j => (([
      [1, 1, 1, 0, 0, 0, 0, -2, -2, 1],
      [-175, -90, 0, 4, 0, 7, 0, 50, 0, 0],
      [15, 0, 0, 0, 0, -1, -1, 0, 20, 15],
      [5, 0, 0, -2, 0, 0, 1, 20, 0, -30],
      [-30, 0, 0, 0, -2, 1, 0, 20, 0, 5],
      [0, 0, -90, 0, 4, 0, 7, 50, 0, -175],
      [0, 5, 5, -1, -1, 0, 0, 10, 0, 0],
      [0, 15, -75, 6, 0, -2, 0, 0, 50, 0],
      [0, -75, 15, 0, 6, 0, -2, 0, 50, 0],
      [-105, 0, -180, 18, 0, 0, 1, 0, 80, 0],
      [0, -180, 0, 0, 18, 1, 0, 0, 80, -105],
      [0, -5, -5, 1, 1, 0, 0, -10, 0, 0],
      [-15, 0, 0, 0, 0, 1, 1, 0, -20, -15],
      [-5, 0, 0, 2, 0, 0, -1, -20, 0, 30],
      [30, 0, 0, 0, 2, -1, 0, -20, 0, -5],
      [0, -15, 75, -6, 0, 2, 0, 0, -50, 0],
      [0, 75, -15, 0, -6, 0, 2, 0, -50, 0],
      [175, 90, 0, -4, 0, -7, 0, -50, 0, 0],
      [0, 0, 90, 0, -4, 0, -7, -50, 0, 175],
      [105, 0, 180, -18, 0, 0, -1, 0, -80, 0],
      [0, 180, 0, 0, -18, -1, 0, 0, -80, 105]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.TypeA73
