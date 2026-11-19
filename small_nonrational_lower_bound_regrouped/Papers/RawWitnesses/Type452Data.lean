module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B type452.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type452
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [58, -1, -2, 2, 1],
      [44, 1, -4, -10, -2],
      [36, -1, 0, 1, 1],
      [36, 1, -4, -11, -3],
      [44, 1, -5, -9, -2],
      [1, 0, 0, 0, 0],
      [28, -1, 0, 0, 0],
      [22, 0, -1, 0, 0],
      [22, 0, 0, 1, 0],
      [58, 0, 0, 0, -1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 16 1 26 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 176
  spanningInverse := fun i j => (([
      [12, 18, -13, 1, -20],
      [336, 680, -540, -148, -560],
      [88, 220, -110, 22, -264],
      [88, 44, -110, 22, -88],
      [-184, -12, 214, -206, 248]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 4, 7] : List Nat).contains i.val,
        normal := fun i => ([1, -148, 22, 22, -206] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 206, inverse := fun i j => (([
      [13, 21, -14, -22],
      [548, 806, -812, -864],
      [80, 256, -102, -278],
      [80, 50, -102, -72]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 4, 6] : List Nat).contains i.val,
        normal := fun i => ([19, 532, 242, 66, -218] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 218, inverse := fun i j => (([
      [-5, 28, 2, -21],
      [-140, 784, 56, -806],
      [-144, 414, 14, -256],
      [40, -6, -16, -50]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, -1, 0, 0, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 0, 1, 0],
      [1, -2, 58, -2],
      [0, 0, 22, -1],
      [1, -1, 22, -2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 2, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 28, 0, -22, 14] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 14, inverse := fun i j => (([
      [0, -1, 1, 1],
      [0, -28, 14, 28],
      [-7, 7, 0, 7],
      [0, 22, -22, -8]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 3, 4, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([5, 140, 110, -66, 202] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 202, inverse := fun i j => (([
      [19, 28, -30, -21],
      [532, 784, -840, -790],
      [216, 414, -458, -260],
      [32, -6, -8, -46]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 28, 22, -22, 58] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 58, inverse := fun i j => (([
      [-1, 1, 2, 2],
      [-28, -30, 56, 56],
      [-22, 22, -14, 44],
      [22, -22, -44, 14]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 3, 4, 6] : List Nat).contains i.val,
        normal := fun i => ([3, 84, 22, 22, -46] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 184, inverse := fun i j => (([
      [18, 1, -13, -4],
      [688, -156, -548, -112],
      [224, -8, -80, -152],
      [40, -8, -80, 32]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 3, 5, 6] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -2, 1, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [0, 0, 0, 4],
      [4, -4, -4, 112],
      [-10, -1, 9, 152],
      [4, 0, -4, -32]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 2, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([0, -8, 0, 1, -9] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 9, inverse := fun i j => (([
      [0, 0, 9, 0],
      [-1, -10, 316, 4],
      [0, 0, 198, -9],
      [-1, -1, -8, 4]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 3, 4, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -324, -22, -22, 14] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 14, inverse := fun i j => (([
      [-1, 1, 0, 1],
      [422, -352, -56, -156],
      [36, -22, -14, -8],
      [22, -22, 0, -8]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 3, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, -4, -1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 0, 1, 0],
      [3, -2, -236, 8],
      [0, 0, -22, 1],
      [1, -1, 14, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([1, 4, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, -2, 0, 0, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 0, 1, 0],
      [-9, 10, 264, -14],
      [0, 0, 22, -1],
      [-1, 1, 22, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([2, 5, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 5, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, 28, -1, 0],
      [0, -22, 0, 1],
      [1, 14, -1, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 13 => {
        vertices := fun i => ([3, 4, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -16, 22, -22, 58] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 58, inverse := fun i j => (([
      [1, -1, 1, 2],
      [-132, 190, -422, 258],
      [22, -22, -36, 44],
      [-22, 22, -22, 14]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 14 => {
        vertices := fun i => ([3, 5, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -11, 4, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 6, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [0, 4, 0, 0],
      [0, 112, -4, 0],
      [-1, -110, -1, 3],
      [0, 232, 0, -4]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([3, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 28, 22, -18, 58] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 6, 7, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 638, inverse := fun i j => (([
      [0, 0, 0, 11],
      [0, -638, 0, 308],
      [0, 0, -638, 242],
      [-58, -58, 232, -24]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | _ => {
        vertices := fun i => ([1, 2, 3, 6] : List Nat).contains i.val,
        rows := fun i => ([2, 3, 6] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [-1, -1, 1, 0, 1, 0, 0, 1, 0, 0],
      [0, 1, 0, 0, -1, -44, 0, 1, 1, 0],
      [0, 0, -1, 0, 0, 44, 1, 0, 1, -1],
      [2, 1, 0, -2, 0, 0, -3, 0, -16, 6],
      [0, -1, 1, 1, 0, 0, -1, 0, 0, 0],
      [-1, 0, 0, -1, 1, 0, 1, 1, 0, 0],
      [0, 1, -1, -1, 0, 0, 1, 0, 0, 0],
      [0, 0, 0, 1, -1, 0, 0, 1, 2, -1],
      [4, 1, -2, 0, 0, 0, -1, -12, 4, 0],
      [-1, 0, 1, 0, 0, -44, 0, 2, 1, 0],
      [0, -1, 0, 0, 1, 44, 0, -1, -1, 0],
      [1, 0, 0, -1, 2, -44, 0, -8, 5, 0],
      [0, 2, -1, 0, -3, 0, 0, 7, -6, 1],
      [1, 0, 0, 0, 0, 0, -1, -2, -2, 1],
      [0, -1, 0, 1, 0, 44, 0, 0, 1, -1],
      [-1, 0, 0, 0, 0, 0, 1, 2, 2, -1],
      [1, 1, -1, 0, -1, 0, 0, -1, 0, 0],
      [1, 0, 0, 1, -1, 0, -1, -1, 0, 0],
      [0, 0, 0, -1, 1, 0, 0, -1, -2, 1],
      [-1, 1, 0, 0, -2, 0, 0, 8, -6, 1],
      [1, 0, -1, 0, 0, 44, 0, -2, -1, 0],
      [0, 1, 0, -1, 0, -44, 0, 0, -1, 1],
      [0, 0, 1, 0, 0, -44, -1, 0, -1, 1],
      [1, 0, 0, 1, 0, -44, 0, -6, 9, -2],
      [0, -2, 1, -1, 4, 0, 0, -8, 4, 0],
      [0, -1, -1, 0, 0, 132, 0, 4, -9, 1]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Type452
