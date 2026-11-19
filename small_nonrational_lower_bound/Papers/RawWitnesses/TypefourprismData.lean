module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typefour_prism.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typefourprism
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [17, 0, 0, 0, 1],
      [1, 0, 0, 0, 0],
      [11, 1, 1, 0, 1],
      [16, -1, 0, 0, 0],
      [7, 1, 1, 1, 1],
      [6, 0, 0, 1, 0],
      [13, 2, 4, 8, 1],
      [6, 0, 1, 1, 0],
      [10, 0, 1, 0, 0],
      [16, -1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 12 9 20 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 1
  spanningInverse := fun i j => (([
      [0, 1, 0, 0, 0],
      [0, 16, 0, -1, 0],
      [-1, -10, 1, 1, 0],
      [0, 4, -1, 0, 1],
      [1, -17, 0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 3, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 3] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, 16, 0, -1],
      [-1, -10, 1, 1],
      [1, -17, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 4, 5, 9] : List Nat).contains i.val,
        normal := fun i => ([0, -1, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [-1, 6, 1, 0],
      [0, 4, -1, 1],
      [1, -17, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 3, 4, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 16, -10, 4, -17] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 17, inverse := fun i j => (([
      [1, 0, 0, 0],
      [16, 0, -17, 0],
      [-27, 17, 17, 0],
      [4, -17, 0, 17]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 3, 4, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([1, 16, -5, -1, -17] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 68, inverse := fun i j => (([
      [4, 0, 0, 0],
      [64, -68, 0, 0],
      [-139, 102, 136, -17],
      [47, -34, -68, 17]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 3, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([2, 32, 0, -7, -34] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 6, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 136, inverse := fun i j => (([
      [8, 0, 0, 0],
      [128, -136, 0, 0],
      [0, 136, 0, -136],
      [-45, -34, 17, 68]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 4, 5, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 6, 10, -6, -17] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 4, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 34, inverse := fun i j => (([
      [2, 0, 0, 0],
      [-39, 68, 68, -17],
      [37, -34, -102, 17],
      [-12, 0, 34, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 4, 5, 6] : List Nat).contains i.val,
        normal := fun i => ([0, -3, 1, 0, 2] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [2, 0, 0, 0],
      [1, -4, 8, -1],
      [-23, 6, -8, 1],
      [8, -2, 2, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([0, -8, 0, 1, 8] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 8, inverse := fun i j => (([
      [8, 0, 0, 0],
      [-8, 8, 0, -8],
      [-80, 0, 0, 8],
      [29, -2, 1, -2]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 3, 5, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [16, -1, 0, 0],
      [0, 0, -1, 1],
      [-6, 0, 1, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 5, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([0, -1, 0, 0, 2] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 5, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2, inverse := fun i j => (([
      [2, 0, 0, 0],
      [35, -4, 1, -4],
      [0, -2, 0, 2],
      [-12, 2, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([2, 4, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -4, -10, 4, 3] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3, inverse := fun i j => (([
      [4, -6, 1, -2],
      [-4, 9, -1, -1],
      [-37, 57, -10, 23],
      [13, -21, 4, -8]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([3, 5, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 16, 0, -6, 3] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3, inverse := fun i j => (([
      [-2, 4, -1, 4],
      [-35, 64, -16, 64],
      [0, -3, 0, 3],
      [12, -21, 6, -24]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 9] : List Nat).contains i.val,
        rows := fun i => ([1, 2, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [-10, 1, 1],
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
        vertices := fun i => ([0, 2, 3, 8] : List Nat).contains i.val,
        rows := fun i => ([2, 3, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, 1, -1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 3, 4, 7] : List Nat).contains i.val,
        rows := fun i => ([3, 4, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, 1, -1],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 4, 5, 9] : List Nat).contains i.val,
        rows := fun i => ([4, 5, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
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
    | 4 => {
        vertices := fun i => ([1, 2, 4, 5] : List Nat).contains i.val,
        rows := fun i => ([2, 4, 5] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 10, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([1, 3, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([3, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 10, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [-1, 1, 1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 5, 7, 8] : List Nat).contains i.val,
        rows := fun i => ([5, 7, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 10, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, -1, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([2, 4, 7, 8] : List Nat).contains i.val,
        rows := fun i => ([4, 7, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([3, 5, 7, 9] : List Nat).contains i.val,
        rows := fun i => ([5, 7, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [-1, 1, 1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [1, 0, -1, -1, 0, 0, 0, 0, 1, 0],
      [-1, 0, 1, 1, 0, 0, 0, 0, -1, 0],
      [1, 0, 0, 0, -1, 1, 0, 0, 0, -1],
      [0, -10, 0, 0, 0, 1, 0, -1, 1, 0],
      [0, 0, 0, -1, 0, -1, 0, 1, 0, 1],
      [0, 10, -1, 0, 1, -1, 0, 0, 0, 0],
      [-1, 0, 0, 1, 1, 0, 0, -1, 0, 0],
      [0, 0, 1, 0, -1, 0, 0, 1, -1, 0],
      [-1, -10, 1, 0, 0, 0, 0, 0, 0, 1],
      [0, 10, 0, 1, 0, 0, 0, 0, -1, -1],
      [1, -20, 0, 2, 0, 8, -1, 0, 0, -4],
      [0, 0, 2, 1, -3, -2, 1, -3, 0, 0],
      [-1, 0, -2, 0, 4, 2, -1, 2, 0, 0],
      [1, 0, 0, -1, -1, 0, 0, 1, 0, 0],
      [0, 0, -1, 0, 1, 0, 0, -1, 1, 0],
      [-1, 0, 0, 0, 1, -1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0, -1, 0, -1],
      [0, 0, 0, -1, 1, 2, -1, 5, -2, 0],
      [0, -10, 1, 0, -1, 1, 0, 0, 0, 0],
      [0, 10, 0, 0, 0, -1, 0, 1, -1, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Typefourprism
