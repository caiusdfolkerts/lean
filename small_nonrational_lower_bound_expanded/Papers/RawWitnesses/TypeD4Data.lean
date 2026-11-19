module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typeD4.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD4
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [1, 0, 0, 0, 0],
      [137, -1, 4, 1, 10],
      [29, 1, 0, 1, 0],
      [29, 1, 0, 0, 0],
      [20, 0, 1, 0, 0],
      [20, 0, 1, 1, 0],
      [127, 4, -1, 1, 5],
      [149, -2, -2, 2, 5],
      [11, 0, 0, 0, 1],
      [24, 0, 0, 1, 0]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 15 3 25 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 10
  spanningInverse := fun i j => (([
      [10, 0, 0, 0, 0],
      [-290, 0, 0, 10, 0],
      [-200, 0, 0, 0, 10],
      [0, 0, 10, -10, 0],
      [-86, 1, -1, 2, -4]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 4, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 15, inverse := fun i j => (([
      [15, 0, 0, 0],
      [1605, 5, -40, -10],
      [-300, 0, 15, 0],
      [75, 2, -10, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 3, 4, 5, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-29, 0, 1, 0],
      [-20, 0, 0, 1],
      [0, 1, -1, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 3, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 5, 0, 2] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [2, 0, 0, 0],
      [-58, 0, 2, 0],
      [207, 2, -4, -1],
      [0, 2, -2, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 4, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-29, 1, 0, 0],
      [-20, 0, 1, 0],
      [-11, 0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 3, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 1, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 5, inverse := fun i j => (([
      [5, 0, 0, 0],
      [-145, 5, 0, 0],
      [980, -30, 5, -5],
      [185, -10, 2, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 4, 5, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 5, 0, 0, 2] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [2, 0, 0, 0],
      [189, -4, 2, -1],
      [-40, 2, 0, 0],
      [0, -2, 2, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 5, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -17, -8, -12, -11] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 110, inverse := fun i j => (([
      [2, 10, -10, -2],
      [-89, -555, 500, 144],
      [-71, -575, 520, 126],
      [31, 375, -210, -86]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 3, 4, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -29, -20, 24, -11] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 55, inverse := fun i j => (([
      [1, 5, -5, -1],
      [-29, -90, 145, 29],
      [-20, -100, 155, 20],
      [-31, -375, 210, 86]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 4, 5, 6] : List Nat).contains i.val,
        normal := fun i => ([3, -79, -60, 0, -25] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 375, inverse := fun i j => (([
      [4, -10, -5, 1],
      [-147, 555, 90, 57],
      [-80, 575, 100, -20],
      [0, -375, 375, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 4, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([1, 107, -20, 0, 5] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 75, inverse := fun i j => (([
      [-2, 10, 0, 1],
      [-189, 795, 75, 57],
      [40, -125, 0, -20],
      [0, -75, 75, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 5, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 19, 4, -24, -11] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 5, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 110, inverse := fun i j => (([
      [0, 0, 0, 10],
      [-44, 110, -33, 795],
      [22, 0, -11, -125],
      [-22, 110, 11, -75]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([2, 3, 4, 5, 6] : List Nat).contains i.val,
        normal := fun i => ([5, -145, -100, 0, -31] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 31, inverse := fun i j => (([
      [-1, -3, 1, 1],
      [29, 118, -29, -29],
      [20, 60, 11, -20],
      [31, -31, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([2, 3, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([1, -29, 196, 0, 37] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 185, inverse := fun i j => (([
      [0, 10, -2, 1],
      [0, -105, 58, -29],
      [185, 665, -207, 11],
      [185, -185, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 13 => {
        vertices := fun i => ([2, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -5, 4, -24, -11] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 5, 8, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 11, inverse := fun i j => (([
      [0, 0, 1, 0],
      [11, 0, -5, -11],
      [0, 11, 4, -11],
      [0, 0, -24, 11]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([2, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -5, 28, -24, -11] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 110, inverse := fun i j => (([
      [0, 0, 0, 10],
      [0, 22, -11, -105],
      [110, -44, -33, 665],
      [110, -22, 11, -185]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 2, 3, 9] : List Nat).contains i.val,
        rows := fun i => ([2, 3, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([24, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [-1, 1, 1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 4, 5, 9] : List Nat).contains i.val,
        rows := fun i => ([4, 5, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([24, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, -1, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([2, 3, 4, 5] : List Nat).contains i.val,
        rows := fun i => ([3, 4, 5] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [0, -1, -5, 0, 0, 5, 1, 0, 5, 0],
      [0, 0, 10, 0, 0, 0, -2, 1, 5, -10],
      [-24, 0, 0, 0, 1, -1, 0, 0, 0, 1],
      [24, 0, 0, 0, -1, 1, 0, 0, 0, -1],
      [0, 0, 1, -1, 1, -1, 0, 0, 0, 0],
      [0, 0, -1, 1, -1, 1, 0, 0, 0, 0],
      [-240, -2, 0, 0, 10, 0, 0, 1, 15, 0],
      [240, 0, 0, -10, 0, 0, 2, -1, -5, 0],
      [0, 4, 0, 30, -25, 0, -7, -1, 0, 5],
      [-24, 0, -1, 1, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, -1, -3, 0, 0, -10, 1],
      [0, 0, -4, 2, 0, -2, 0, -1, 5, 8],
      [0, -1, 0, -5, 5, 0, 1, 0, 5, 0],
      [-240, 0, 0, 10, 0, 0, -2, 1, 5, 0],
      [0, 1, 5, 0, 0, -5, -1, 0, -5, 0],
      [0, 0, -2, -2, 1, 0, 1, 0, -5, 1],
      [0, -2, 0, 0, 0, 10, 0, 1, 15, -10],
      [24, 0, 1, -1, 0, 0, 0, 0, 0, -1],
      [0, 1, 0, 5, -5, 0, -1, 0, -5, 0],
      [0, 0, -10, 0, 0, 0, 2, -1, -5, 10],
      [0, 2, 0, 0, 0, -10, 0, -1, -15, 10],
      [0, -1, 0, 5, 0, 0, -2, -1, 25, 5],
      [240, 2, 0, 0, -10, 0, 0, -1, -15, 0],
      [-48, 0, 2, 0, 0, 2, 0, 1, -5, -6],
      [144, 0, 0, -2, -2, 0, 0, -1, 5, 2]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.TypeD4
