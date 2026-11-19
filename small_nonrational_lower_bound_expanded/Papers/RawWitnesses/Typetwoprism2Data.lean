module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B typetwo_prism_2.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typetwoprism2
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [1, 0, 0, 1, 0],
      [1, 0, 0, 0, 1],
      [1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0],
      [1, 1, 0, 0, 0],
      [1, 1, 1, 0, 0],
      [3, 1, -1, 5, 1],
      [3, -1, 1, 1, 5],
      [1, 1, 0, 1, 0],
      [1, 0, 1, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 14 5 24 where
  spanningRows := fun i => ([0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0
  spanningDenominator := 1
  spanningInverse := fun i j => (([
      [0, 0, 1, 0, 0],
      [0, 0, -1, 0, 1],
      [0, 0, -1, 1, 0],
      [1, 0, -1, 0, 0],
      [0, 1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 0, 1, 0],
      [-5, -1, 3, 1],
      [1, 0, -1, 0],
      [0, 1, -1, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 2, 3, 4, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, -1, 0, 1],
      [0, -1, 1, 0],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 2, 3, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 5, 0, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [1, 1, 1, -1],
      [0, -1, 1, 0],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 2, 4, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 1, 0, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, -1, 1, 0],
      [5, -3, 1, -1],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 3, 5, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([1, 0, -1, -1, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [5, -2, 1, -1],
      [0, -1, 1, 0],
      [-5, 3, -1, 1],
      [-4, 2, -1, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([0, 3, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 1, -1, -1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 3, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 6, inverse := fun i j => (([
      [6, 0, 0, 0],
      [-18, 6, 5, -1],
      [-6, 6, 0, 0],
      [-6, 0, 1, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 2, 3, 4, 5, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 4] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, -1, 0, 1],
      [0, -1, 1, 0],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([1, 2, 3, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [5, -3, 1, -1],
      [0, -1, 1, 0],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([1, 2, 4, 6] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 5, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [0, 1, 0, 0],
      [0, -1, 1, 0],
      [1, 1, 1, -1],
      [1, -1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([1, 4, 5, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -1, 0, 1, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 5, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-1, 1, 0, 0],
      [0, -1, 1, 0],
      [-4, 2, -1, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([1, 4, 6, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([1, -1, 1, 0, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 4, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 6, inverse := fun i j => (([
      [6, 0, 0, 0],
      [-6, 6, 0, 0],
      [-18, 6, -1, 5],
      [-6, 0, 1, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([3, 5, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([5, 0, -5, -4, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 6, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [3, -1, 1, -1],
      [-4, 4, 0, 0],
      [1, 1, -1, 1],
      [-4, 0, 0, 4]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 12 => {
        vertices := fun i => ([4, 5, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([5, -5, 0, 0, -4] : List (Int)).getD i.val 0,
        rows := fun i => ([4, 5, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 4, inverse := fun i j => (([
      [3, -1, 1, -1],
      [1, 1, -1, 1],
      [-4, 4, 0, 0],
      [-4, 0, 0, 4]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([5, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([2, -1, -1, -1, -1] : List (Int)).getD i.val 0,
        rows := fun i => ([5, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 6, inverse := fun i j => (([
      [-6, -3, 3, 12],
      [0, -1, -1, 6],
      [12, 4, -2, -18],
      [6, 4, -2, -12]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 2, 4, 8] : List Nat).contains i.val,
        rows := fun i => ([2, 4, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, -1, 1],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 3, 5, 8] : List Nat).contains i.val,
        rows := fun i => ([3, 5, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, -1, 1],
      [0, 0, 0],
      [0, 0, 0],
      [1, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([1, 2, 3, 9] : List Nat).contains i.val,
        rows := fun i => ([2, 3, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([1, 4, 5, 9] : List Nat).contains i.val,
        rows := fun i => ([4, 5, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [1, -1, 1],
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
      [1, 1, -1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [-6, -6, 6, 0, 0, 0, 1, 1, 0, 0],
      [0, 0, 0, 0, 0, 6, 1, 1, -6, -6],
      [0, 0, -1, 1, 1, -1, 0, 0, 0, 0],
      [0, 0, 1, -1, -1, 1, 0, 0, 0, 0],
      [1, 1, 0, -2, 0, -1, 0, -1, 0, 4],
      [-1, 0, 1, 0, -1, 0, 0, 0, 1, 0],
      [1, 0, -1, 0, 1, 0, 0, 0, -1, 0],
      [0, 1, -1, 1, 0, 0, 0, 0, 0, -1],
      [0, -1, 0, 0, 1, -1, 0, 0, 0, 1],
      [2, -2, 0, 0, 0, 0, -1, 1, 2, -2],
      [-1, 0, 0, 1, 0, -1, 0, 0, 1, 0],
      [6, 0, 0, -6, 0, 0, -1, -1, 0, 6],
      [0, 6, 0, 0, -6, 0, -1, -1, 6, 0],
      [1, 0, 0, -1, 0, 1, 0, 0, -1, 0],
      [4, 1, -2, -1, 0, 0, -1, 0, 1, 0],
      [0, 1, 0, 0, -1, 1, 0, 0, 0, -1],
      [-2, 2, 0, 0, 0, 0, 1, -1, -2, 2],
      [-6, 0, 0, 6, 0, 0, 1, 1, 0, -6],
      [0, -6, 0, 0, 6, 0, 1, 1, -6, 0],
      [0, -1, 1, -1, 0, 0, 0, 0, 0, 1],
      [6, 6, -6, 0, 0, 0, -1, -1, 0, 0],
      [0, 0, 0, 0, 0, -6, -1, -1, 6, 6],
      [1, 4, -2, 0, -1, 0, 0, -1, 0, 1],
      [1, 1, 0, 0, -2, -1, -1, 0, 4, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Typetwoprism2
