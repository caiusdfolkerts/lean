module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B type52.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type52
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [87, -4, 2, -3, 0],
      [1, 0, 0, 0, 0],
      [11, -1, 0, 0, 0],
      [12, 0, 0, -1, 0],
      [24, 0, -1, 0, 0],
      [53, -2, -4, -1, 0],
      [10, 0, 0, 0, -1],
      [10, -1, 0, 0, -1],
      [23, 0, -1, 0, -1],
      [11, 0, 0, -1, -1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 11 6 18 where
  spanningRows := fun i => ([0, 1, 2, 3, 6] : List (Fin 10)).getD i.val 0
  spanningDenominator := 2
  spanningInverse := fun i j => (([
      [0, 2, 0, 0, 0],
      [0, 22, -2, 0, 0],
      [1, -7, -4, -3, 0],
      [0, 24, 0, -2, 0],
      [0, 20, 0, 0, -2]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 3, 4, 5] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 3] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [0, 2, 0, 0],
      [0, 22, -2, 0],
      [1, -7, -4, -3],
      [0, 24, 0, -2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, -3, -2, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [0, 2, 0, 0],
      [0, 22, -2, 0],
      [1, -43, -4, 0],
      [0, 20, 0, -2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 1, 3, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, -1, -2, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [0, 4, 0, 0],
      [-1, 51, 3, 0],
      [0, 48, -4, 0],
      [0, 40, 0, -4]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 2, 3, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([2, 22, -7, 24, -2] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [0, 2, 0, -2],
      [0, 20, 0, -22],
      [1, -11, -3, 7],
      [0, 24, -2, -24]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 0, -42, 1, 10] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 6, 7, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 10, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, 10, -10, 0],
      [5, -7, -20, -15],
      [0, 11, 0, -10]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([1, 2, 4, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, -1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [11, -1, 0, 0],
      [24, 0, -1, 0],
      [10, 0, 0, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 3, 4, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, -1, 0, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 2, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [24, 0, -1, 0],
      [12, -1, 0, 0],
      [10, 0, 0, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([2, 3, 5, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([4, 44, 19, 48, -4] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [4, 0, 0, -4],
      [40, 0, 0, -44],
      [21, 1, -1, -19],
      [48, -4, 0, -48]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([2, 4, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 11, 24, -65, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, -1],
      [10, 0, 0, -11],
      [24, -1, 0, -24],
      [-63, 4, -1, 65]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([3, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([2, -55, 48, 24, -2] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [0, 2, 0, -2],
      [1, -51, -1, 55],
      [0, 46, 0, -48],
      [-2, 24, 0, -24]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([5, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 0, 13, 1, 10] : List (Int)).getD i.val 0,
        rows := fun i => ([5, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 10, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, 10, -10, 0],
      [0, 23, 0, -10],
      [-10, -59, 20, 40]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([1, 2, 6, 7] : List Nat).contains i.val,
        rows := fun i => ([2, 6, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 11, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([1, 3, 6, 9] : List Nat).contains i.val,
        rows := fun i => ([3, 6, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 11, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([1, 4, 6, 8] : List Nat).contains i.val,
        rows := fun i => ([4, 6, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 11, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, 1, -1],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([2, 3, 7, 9] : List Nat).contains i.val,
        rows := fun i => ([3, 7, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [1, 1, -1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([2, 4, 7, 8] : List Nat).contains i.val,
        rows := fun i => ([4, 7, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([3, 4, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([4, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [-1, 0, 4, 3, 3, 0, 5, 0, -5, 0],
      [0, 0, 0, 0, 0, -1, -7, 2, 4, 1],
      [0, 0, 1, 0, -1, 0, 0, -1, 1, 0],
      [0, 0, -1, 1, 0, 0, 0, 1, 0, -1],
      [0, 0, 0, -1, 1, 0, 0, 0, -1, 1],
      [1, -286, 2, 0, 14, -3, 0, 0, 0, 0],
      [0, 11, 0, -1, 0, 0, -1, 0, 0, 1],
      [0, -11, 0, 1, 0, 0, 1, 0, 0, -1],
      [-1, 209, 0, 1, -10, 2, 0, 0, 0, 0],
      [0, 0, 1, -1, 0, 0, 0, -1, 0, 1],
      [0, 0, -1, 0, 1, 0, 0, 1, -1, 0],
      [0, 0, 0, 0, 0, 1, 7, -2, -4, -1],
      [-2, 33, 10, 7, 0, -1, 0, 0, 0, 0],
      [0, 0, 0, 1, -1, 0, 0, 0, 1, -1],
      [0, 11, -1, 0, 0, 0, -1, 1, 0, 0],
      [0, -11, 1, 0, 0, 0, 1, -1, 0, 0],
      [2, -33, -10, -7, 0, 1, 0, 0, 0, 0],
      [7, 0, -38, -26, -6, 5, 0, 0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Type52
