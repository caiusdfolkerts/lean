module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typetwo_prism_0.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typetwoprism0
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [1, 0, 0, 0, 0],
      [17, 1, 1, 0, 0],
      [19, 1, 0, 0, 0],
      [16, -1, 2, 2, 7],
      [13, 0, 0, 1, 0],
      [10, 0, 0, 0, 1],
      [8, 0, 1, 0, 1],
      [12, -1, 2, 1, 6],
      [13, 1, 0, 1, 0],
      [17, 0, 1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 14 5 23 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 7
  spanningInverse := fun i j => (([
      [7, 0, 0, 0, 0],
      [-133, 0, 7, 0, 0],
      [14, 7, -7, 0, 0],
      [-91, 0, 0, 0, 7],
      [-13, -2, 3, 1, -2]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 4, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-19, 0, 1, 0],
      [2, 1, -1, 0],
      [-13, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 5, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-19, 0, 1, 0],
      [2, 1, -1, 0],
      [-10, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 4, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 4, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-19, 1, 0, 0],
      [-13, 0, 1, 0],
      [-10, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 4, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 2, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-80, -1, 2, 7],
      [-13, 0, 1, 0],
      [-10, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 4, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 6, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 4, 7, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-35, 1, -1, 2],
      [-17, 0, 0, 1],
      [-13, 1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 5, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 5, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-44, 4, 2, -1],
      [2, -1, 1, 0],
      [-10, 1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 5, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([1, -19, 2, 25, -10] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 10, inverse := fun i j => (([
      [0, 0, 1, 0],
      [0, 10, -19, 0],
      [10, -10, 2, 0],
      [-20, 30, -35, 10]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([6, -114, 12, 36, -41] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 41, inverse := fun i j => (([
      [-2, 4, 1, -1],
      [38, -35, -19, 19],
      [37, -33, 2, -2],
      [-12, -17, 6, 35]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 3, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([2, -19, -15, -7, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, -1, -3, 2],
      [-8, 9, 26, -18],
      [-8, 8, 25, -16],
      [-4, 5, 12, -9]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 4, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 0, -17, -13, 9] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 9, inverse := fun i j => (([
      [1, 1, -1, -1],
      [0, -9, 0, 9],
      [-8, -8, 17, 8],
      [-13, -4, 13, 13]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([2, 3, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([2, -38, 23, 12, -20] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 20, inverse := fun i j => (([
      [0, 0, 2, 0],
      [20, 0, -38, 0],
      [10, -10, -27, 20],
      [0, 20, -8, -20]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([3, 4, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 0, 40, -13, -10] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 10, inverse := fun i j => (([
      [0, 0, 1, 0],
      [0, -10, 0, 10],
      [5, -15, 5, 5],
      [0, 10, -13, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([3, 4, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 19, -17, -13, 9] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 9, inverse := fun i j => (([
      [-1, 1, 0, 1],
      [17, -8, 18, -26],
      [8, -8, 9, -8],
      [13, -4, 0, -13]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([3, 4, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([5, 0, -66, -65, 26] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 26, inverse := fun i j => (([
      [-1, 3, 2, -1],
      [0, -26, 0, 26],
      [8, -24, 10, 8],
      [13, -13, -26, 13]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 9] : List Nat).contains i.val,
        rows := fun i => ([1, 2, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([19, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [-1, 1, 1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 4, 8] : List Nat).contains i.val,
        rows := fun i => ([2, 4, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([19, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 5, 6, 9] : List Nat).contains i.val,
        rows := fun i => ([5, 6, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([19, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, -1, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([1, 2, 5, 6] : List Nat).contains i.val,
        rows := fun i => ([2, 5, 6] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([1, 4, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([4, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [-1, 1, 1],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [0, -1, 0, -1, 0, 0, 1, 1, 1, 0],
      [0, 1, -1, 0, 0, 1, -1, 0, 0, 0],
      [-19, 0, 1, 0, 1, 0, 0, 0, -1, 0],
      [19, 0, 0, 0, 0, -1, 1, 0, 0, -1],
      [0, -1, 0, 0, -1, 0, 0, 0, 1, 1],
      [-19, 0, 0, -1, 1, 1, 0, 1, 0, 0],
      [0, 0, 1, 4, -1, 0, 2, -5, -2, 0],
      [0, 1, 0, 0, 1, 0, 0, 0, -1, -1],
      [19, 0, -1, 0, -1, 0, 0, 0, 1, 0],
      [0, -1, 1, 0, 0, -1, 1, 0, 0, 0],
      [-19, 0, 0, 0, 0, 1, -1, 0, 0, 1],
      [0, 0, 2, 0, 0, -3, -3, 1, -1, 1],
      [0, 0, 1, 0, -1, -2, -4, 1, 0, 2],
      [0, 0, -1, 1, 0, 2, 3, -2, 0, -1],
      [0, 0, -1, -1, 0, 1, 0, 1, 1, 0],
      [0, 0, 0, -1, 1, 0, 1, 1, 0, -1],
      [0, 1, 0, 1, 0, 0, -1, -1, -1, 0],
      [0, 0, 1, 1, 0, -1, 0, -1, -1, 0],
      [0, 0, 0, 1, -1, 0, -1, -1, 0, 1],
      [0, -1, 0, 1, 0, 1, 4, -2, 0, -1],
      [19, 0, 0, 1, -1, -1, 0, -1, 0, 0],
      [-19, 2, -3, 1, 0, 5, 0, -2, 0, 0],
      [0, 1, 0, -2, 1, -1, -3, 3, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Typetwoprism0
