module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B type85.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type85
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [53, 3, 1, -2, 1],
      [1, 0, 0, 0, 0],
      [123, 3, 8, -2, 8],
      [16, 0, 0, -1, 0],
      [23, -1, 0, 0, 0],
      [19, -1, 0, -1, 0],
      [22, 0, -1, 0, 0],
      [18, 0, -1, -1, 0],
      [29, -3, -4, 0, 1],
      [12, 0, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 12 3 22 where
  spanningRows := fun i => ([0, 1, 2, 3, 6] : List (Fin 10)).getD i.val 0
  spanningDenominator := 21
  spanningInverse := fun i j => (([
      [0, 21, 0, 0, 0],
      [8, -77, -1, -14, 0],
      [0, 462, 0, 0, -21],
      [0, 336, 0, -21, 0],
      [-3, -672, 3, 0, 21]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 3, 4, 5] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -1, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 3] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 21, inverse := fun i j => (([
      [0, 21, 0, 0],
      [8, -77, -1, -14],
      [-3, -210, 3, 0],
      [0, 336, 0, -21]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, -2, 0, -3, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 21, inverse := fun i j => (([
      [0, 21, 0, 0],
      [8, -301, -1, 0],
      [0, 462, 0, -21],
      [-3, -672, 3, 21]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 1, 3, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, -1, 0, 0, 3] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3, inverse := fun i j => (([
      [0, 3, 0, 0],
      [1, -43, -2, 1],
      [0, 66, 0, -3],
      [0, 48, -3, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 2, 3, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([3, -11, 6, 48, -36] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 252, inverse := fun i j => (([
      [-3, 3, -21, 21],
      [107, -23, -91, -77],
      [-6, 6, 210, -210],
      [-48, 48, -588, 336]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([3, -71, 66, -12, -36] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 72, inverse := fun i j => (([
      [3, -3, -6, 3],
      [-59, 155, 118, -83],
      [66, -138, -132, 66],
      [-12, 84, -48, -12]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([1, 2, 4, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -1, -4, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 8, inverse := fun i j => (([
      [8, 0, 0, 0],
      [184, 0, -8, 0],
      [-96, 1, 3, -8],
      [-96, 0, 0, 8]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 3, 4, 5, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [23, 0, -1, 0],
      [22, 0, 0, -1],
      [16, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 4, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, -1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [23, -1, 0, 0],
      [22, 0, -1, 0],
      [128, -3, -4, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([2, 3, 5, 9] : List Nat).contains i.val,
        normal := fun i => ([2, 6, -1, 32, -24] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 24, inverse := fun i j => (([
      [0, 0, 0, 2],
      [0, 24, -24, 6],
      [3, -15, 9, -25],
      [0, -24, 0, 32]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([2, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 23, -13, -4, -12] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 120, inverse := fun i j => (([
      [1, -1, -2, 2],
      [23, -143, -46, 46],
      [-10, 100, 20, -50],
      [-4, 124, -112, -8]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([3, 5, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 3, 2, 16, -12] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 12, inverse := fun i j => (([
      [7, -3, -4, 1],
      [33, -21, -12, 3],
      [26, -6, -20, 2],
      [100, -48, -64, 16]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([4, 5, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 23, 22, -4, 128] : List (Int)).getD i.val 0,
        rows := fun i => ([4, 5, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 128, inverse := fun i j => (([
      [3, 0, 4, -1],
      [-59, 0, 92, -23],
      [66, 0, -40, -22],
      [116, -128, -16, 4]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([1, 3, 4, 5] : List Nat).contains i.val,
        rows := fun i => ([3, 4, 5] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 20, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([1, 3, 6, 7] : List Nat).contains i.val,
        rows := fun i => ([3, 6, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 20, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([4, 5, 6, 7] : List Nat).contains i.val,
        rows := fun i => ([5, 6, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, 1, -1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [-1, 0, 0, 0, 0, 0, 1, 2, -1, 2],
      [1, 0, -1, 7, 0, 0, 0, -7, 0, 7],
      [0, 20, 0, -1, 0, 0, -1, 1, 0, 0],
      [0, -20, 0, 1, 1, -1, 0, 0, 0, 0],
      [-8, 840, 1, 0, -35, 14, 0, 0, 0, 0],
      [0, 0, 0, -7, 0, 3, 0, 4, -1, 1],
      [0, 0, 0, 0, -1, 1, 1, -1, 0, 0],
      [1, 140, -1, 0, 0, 0, -7, 0, 0, 7],
      [0, -20, 1, -6, 0, 0, 0, 4, 1, -9],
      [-8, 0, 1, 42, 7, -28, 0, 0, 0, 0],
      [0, -140, 0, 0, 3, 0, 4, 0, -1, 1],
      [1, 0, 0, 0, 0, 0, -1, -2, 1, -2],
      [0, 0, 1, 0, -1, -2, 0, 0, 2, -10],
      [8, 0, -1, -42, -7, 28, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, -1, -1, 1, 0, 0],
      [0, 0, -1, 0, 1, 2, 0, 0, -2, 10],
      [0, -20, 0, 1, 0, 0, 1, -1, 0, 0],
      [-1, 0, 1, -7, 0, 0, 0, 7, 0, -7],
      [0, 0, 0, 7, 0, -3, 0, -4, 1, -1],
      [-1, -140, 1, 0, 0, 0, 7, 0, 0, -7],
      [0, 140, 0, 0, -3, 0, -4, 0, 1, -1],
      [8, -140, -1, -35, 0, 21, 0, 0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Type85
