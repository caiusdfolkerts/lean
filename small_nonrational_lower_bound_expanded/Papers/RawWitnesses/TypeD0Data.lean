module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typeD0.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD0
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [1, 0, 0, 0, 0],
      [136, 1, -7, -1, -1],
      [69, 1, 0, 1, 0],
      [57, 1, 0, 0, 0],
      [96, 5, -23, -3, -1],
      [27, 0, 1, 0, 0],
      [39, 0, 1, 1, 0],
      [176, 3, -28, -3, -1],
      [186, 0, 0, 0, -1],
      [59, 0, 0, 1, 0]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 15 3 25 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 16
  spanningInverse := fun i j => (([
      [16, 0, 0, 0, 0],
      [-912, 0, 0, 16, 0],
      [-244, 1, -2, 6, -1],
      [-192, 0, 16, -16, 0],
      [3164, -23, -2, -10, 7]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [2, 0, 0, 0],
      [-607, -1, 21, 1],
      [-54, 0, 2, 0],
      [43, -3, 7, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 3, 5, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-57, 0, 1, 0],
      [-27, 0, 0, 1],
      [-12, 1, -1, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 3, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 1, 0, -28] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 28, inverse := fun i j => (([
      [28, 0, 0, 0],
      [-1596, 0, 28, 0],
      [41, -3, 6, -1],
      [-336, 28, -28, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 4, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, -3] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3, inverse := fun i j => (([
      [3, 0, 0, 0],
      [-171, 3, 0, 0],
      [-81, 0, 0, 3],
      [432, 5, -1, -23]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 5, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 5, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 2, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-27, 1, 0, 0],
      [-12, -1, 1, 0],
      [186, 0, 0, -1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 28, 3, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 7, 8, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 3, inverse := fun i j => (([
      [3, 0, 0, 0],
      [-167, 1, -1, 3],
      [-177, 0, 0, 3],
      [558, 0, -3, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 4, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([5, -191, -41, -154, 930] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1860, inverse := fun i j => (([
      [15, 10, -5, -10],
      [-387, 2222, 5, -2594],
      [63, 662, -145, -1034],
      [-648, -1052, 340, 3284]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 3, 4, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -57, -27, 82, 186] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 5] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 372, inverse := fun i j => (([
      [3, 2, -1, -2],
      [-171, 258, 57, 114],
      [-81, -54, 27, 426],
      [432, 908, -268, -3140]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 4, 5, 7] : List Nat).contains i.val,
        normal := fun i => ([2, 215, -54, 822, 43] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 86, inverse := fun i j => (([
      [6, 0, -14, -2],
      [645, 43, -1720, -258],
      [-162, 0, 464, 54],
      [2509, 43, -6872, -908]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 4, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([8, 155, 66, -378, 1159] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 6954, inverse := fun i j => (([
      [65, -7, 14, -10],
      [535, 2617, 1720, -2222],
      [826, 232, -464, -662],
      [-3361, 41, 6872, 1052]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 131, 20, -59, 186] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1302, inverse := fun i j => (([
      [0, 0, 0, 7],
      [4650, 1302, -1116, -2617],
      [558, 0, -186, -232],
      [-558, 1302, 186, -41]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([2, 3, 4, 7] : List Nat).contains i.val,
        normal := fun i => ([5, -285, 194, -60, -5227] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 5227, inverse := fun i j => (([
      [-15, 86, -28, 23],
      [855, 325, 1596, -1311],
      [-582, 1246, -41, -153],
      [5407, -6259, 336, -276]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([2, 3, 4, 8] : List Nat).contains i.val,
        normal := fun i => ([23, -1311, -339, -276, 4278] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 4, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 4278, inverse := fun i j => (([
      [0, 0, 0, 23],
      [0, 4278, 0, -1311],
      [-558, 1488, -186, -153],
      [4278, -4278, 0, -276]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 13 => {
        vertices := fun i => ([2, 3, 5, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -57, -27, -12, 186] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 186, inverse := fun i j => (([
      [0, 0, 0, 1],
      [0, 186, 0, -57],
      [0, 0, 186, -27],
      [186, -186, 0, -12]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([2, 4, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -10, 20, -59, -237] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1659, inverse := fun i j => (([
      [65, -22, -86, 15],
      [535, 457, -325, -387],
      [826, -203, -1246, 63],
      [-3361, 1061, 6259, -648]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 2, 3, 9] : List Nat).contains i.val,
        rows := fun i => ([2, 3, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([47, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
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
        vertices := fun i => ([0, 5, 6, 9] : List Nat).contains i.val,
        rows := fun i => ([5, 6, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([47, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
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
    | _ => {
        vertices := fun i => ([2, 3, 5, 6] : List Nat).contains i.val,
        rows := fun i => ([3, 5, 6] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [0, -3, -2, 0, 1, 0, 2, 0, 2, 0],
      [0, 0, 2, 0, -1, 0, 5, 1, 0, -7],
      [-47, 0, 0, 0, 0, 1, -1, 0, 0, 1],
      [47, 0, 1, -1, 0, 0, 0, 0, 0, -1],
      [0, 0, -1, 1, 0, -1, 1, 0, 0, 0],
      [0, -3, 0, -2, 1, 2, 0, 0, 2, 0],
      [0, 53, 0, 0, -7, 42, 0, -6, -40, 14],
      [0, 1, 0, 2, 0, -8, -13, -1, 0, 11],
      [0, -3, 0, 0, 0, 0, 7, 1, 2, -7],
      [-329, 0, 0, 2, -1, 5, 0, 1, 0, 0],
      [0, 0, 1, -1, 0, 1, -1, 0, 0, 0],
      [0, 1, -1, 0, 0, 3, 4, 0, -1, -2],
      [0, 1, 4, 0, -1, -6, -10, 0, 0, 4],
      [329, 3, 0, 0, 0, -7, 0, -1, -2, 0],
      [-47, 0, -1, 1, 0, 0, 0, 0, 0, 1],
      [0, 3, 0, 0, 0, 0, -7, -1, -2, 7],
      [47, 0, 0, 0, 0, -1, 1, 0, 0, -1],
      [-329, -3, 0, 0, 0, 7, 0, 1, 2, 0],
      [0, 3, 2, 0, -1, 0, -2, 0, -2, 0],
      [0, 3, 0, 2, -1, -2, 0, 0, -2, 0],
      [0, 0, -2, 0, 1, 0, -5, -1, 0, 7],
      [0, 13, 0, -7, 0, 28, 7, -2, -11, 0],
      [329, 0, 0, -2, 1, -5, 0, -1, 0, 0],
      [0, -1, 1, 0, 0, -3, -4, 0, 1, 2],
      [-94, 1, 1, -2, 0, 7, 0, 0, -1, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.TypeD0
