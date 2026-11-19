module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typeA14.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA14
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [4, -1, 1, 1, 3],
      [1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0],
      [1, 0, 1, 0, 0],
      [2, 0, 0, 1, 0],
      [267, -148, 0, 152, -37],
      [1217, 308, 1140, 0, -77],
      [53, 48, 30, 4, -3],
      [191, -114, 10, 114, -27],
      [1, 0, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 15 0 24 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 3
  spanningInverse := fun i j => (([
      [0, 3, 0, 0, 0],
      [0, -3, 3, 0, 0],
      [0, -3, 0, 3, 0],
      [0, -6, 0, 0, 3],
      [1, -2, 1, -1, -1]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 3, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 369, inverse := fun i j => (([
      [0, 369, 0, 0],
      [-27, 624, 57, -3],
      [0, -369, 369, 0],
      [114, -161, -104, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 4, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -1, 0, -2, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 93, inverse := fun i j => (([
      [30, 78, -26, -1],
      [-30, 15, 26, 1],
      [3, -141, -15, 3],
      [-60, -156, 145, 2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 3, 4, 7] : List Nat).contains i.val,
        normal := fun i => ([47, -16, -47, -94, -21] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 63, inverse := fun i j => (([
      [48, -78, -52, 1],
      [-15, -15, 11, 1],
      [-48, 141, 52, -1],
      [-96, 156, 167, -2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 4, 8] : List Nat).contains i.val,
        normal := fun i => ([369, -114, -369, -738, -161] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 161, inverse := fun i j => (([
      [114, -104, 0, -1],
      [-47, 57, 161, -1],
      [-114, 265, 0, 1],
      [-228, 208, 161, 2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 3, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([2, -1, -2, -1, -2] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 616, inverse := fun i j => (([
      [1232, -51272, 52, -308],
      [-308, 10538, -11, 77],
      [-1232, 51888, -52, 308],
      [-3388, 163738, -167, 1001]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 0, 1, -2, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 4588, inverse := fun i j => (([
      [1480, -416, 104, -148],
      [-370, 4816, -57, 37],
      [1258, 1060, -265, 333],
      [-2960, 5420, -208, 296]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 3, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 77, inverse := fun i j => (([
      [77, 0, 0, 0],
      [-77, 77, 0, 0],
      [-77, 0, 77, 0],
      [-231, 308, 1140, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 4, 5, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 37, inverse := fun i j => (([
      [37, 0, 0, 0],
      [-37, 37, 0, 0],
      [-74, 0, 37, 0],
      [111, -148, 152, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 2, 5, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 154, 555, 2280] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2280, inverse := fun i j => (([
      [2280, 0, 0, 0],
      [-2280, 2280, 0, 0],
      [-1818, -616, 0, 2],
      [-6225, 2220, 15, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 3, 5, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 19, 0, 37, 76] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 11704, inverse := fun i j => (([
      [11704, 0, 0, 0],
      [-2926, -43320, 0, 38],
      [-11704, 11704, 0, 0],
      [-23408, -42180, 77, 37]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 190, 57, 185, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 5, 8, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 740, inverse := fun i j => (([
      [740, 0, 0, 0],
      [1520, -5, 0, -185],
      [1196, -57, 74, -111],
      [-740, 0, 0, 740]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([2, 4, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([5, -5, 2, -10, 15] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1110, inverse := fun i j => (([
      [1480, -1520, 10, 0],
      [-370, 1520, -10, 0],
      [-1628, -300, 1, 37],
      [-2960, 4150, -20, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([2, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1140, -1140, -986, 5115, -1140] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 6, 7, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2280, inverse := fun i j => (([
      [0, 0, 0, 2280],
      [2280, 0, 0, -2280],
      [-616, 2, 0, -1818],
      [-22740, -15, 570, 10785]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 13 => {
        vertices := fun i => ([3, 4, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([3, -1, -3, -6, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 924, inverse := fun i j => (([
      [45480, -1232, -48, 308],
      [-14790, 308, 15, -77],
      [-44556, 1232, 48, -308],
      [-90960, 3388, 96, -616]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([5, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([104000, -33125, -12832, 106685, 1321260] : List (Int)).getD i.val 0,
        rows := fun i => ([5, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 34352760, inverse := fun i j => (([
      [1429220, 23140, -247000, -1896960],
      [-475865, -28015, 863170, 604200],
      [-1397188, 13000, 30476, 1861848],
      [-2747875, -67925, 1274330, 3920460]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => Fin.elim0 k
  relations := fun i j => (([
      [-30, 0, -78, 0, 26, 0, 0, 1, 0, 93],
      [0, -1134, 1664, 0, 0, 1, 1, -38, 0, 0],
      [0, 0, 0, 31590, -9152, 0, -39, 407, 66, 0],
      [0, 5698, 0, -6500, 0, -231, 3, 0, 308, 0],
      [0, 0, -2886, 0, 650, 78, 0, 37, -111, 0],
      [-308, 0, 0, 12818, 0, 0, -13, 77, 0, 154],
      [0, -148, 148, 0, -152, 1, 0, 0, 0, 37],
      [130, 104, 208, 0, 0, 0, 0, -4, -1, -429],
      [-370, 0, 0, 0, 104, -26, 0, 0, 37, 1147],
      [0, 154, -308, -1140, 0, 0, 1, 0, 0, 77],
      [0, -154, 308, 1140, 0, 0, -1, 0, 0, -77],
      [30, 0, 78, 0, -26, 0, 0, -1, 0, -93],
      [0, 148, -148, 0, 152, -1, 0, 0, 0, -37],
      [114, 208, 0, -104, 0, 0, 0, 0, -1, -369],
      [0, 0, 0, -31590, 9152, 0, 39, -407, -66, 0],
      [-114, -208, 0, 104, 0, 0, 0, 0, 1, 369],
      [370, 0, 0, 0, -104, 26, 0, 0, -37, -1147],
      [0, 1134, -1664, 0, 0, -1, -1, 38, 0, 0],
      [0, 0, 2886, 0, -650, -78, 0, -37, 111, 0],
      [0, 3568, 1300, 0, 0, -171, -2, 0, 228, -325],
      [0, -5698, 0, 6500, 0, 231, -3, 0, -308, 0],
      [308, 0, 0, -12818, 0, 0, 13, -77, 0, -154],
      [1, 1, 1, -1, -1, 0, 0, 0, 0, -3],
      [-42, 0, 0, 312, 416, 0, 0, -8, -3, 21]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.TypeA14
