module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B type53.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type53
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [1, 0, 0, 0, 0],
      [151, 0, 0, 0, 1],
      [48855, 1300, -364, -630, -1239],
      [84315, -350, 98, -90, -177],
      [146, 0, 0, -1, 0],
      [183, 0, 0, -1, -1],
      [111, 1, 0, 0, 0],
      [74, 1, 0, 0, 1],
      [912, 0, 1, 0, 0],
      [875, 0, 1, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 11 7 20 where
  spanningRows := fun i => ([0, 1, 2, 3, 6] : List (Fin 10)).getD i.val 0
  spanningDenominator := 47250
  spanningInverse := fun i j => (([
      [47250, 0, 0, 0, 0],
      [-5244750, 0, 0, 0, 47250],
      [-43092000, 0, -45, 315, 168750],
      [31770900, -92925, -49, -182, 0],
      [-7134750, 47250, 0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 3, 4, 5] : List Nat).contains i.val,
        normal := fun i => ([0, 7, 25, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 3] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 33750, inverse := fun i j => (([
      [33750, 0, 0, 0],
      [4872150, 0, 9, -63],
      [22693500, -66375, -35, -130],
      [-5096250, 33750, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 45, -26, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 364, inverse := fun i j => (([
      [364, 0, 0, 0],
      [-40404, 0, 0, 364],
      [91644, -1239, -1, 1300],
      [-54964, 364, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 1, 3, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 9, 0, -35, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 350, inverse := fun i j => (([
      [350, 0, 0, 0],
      [21666, -177, -1, 98],
      [-319200, 0, 0, 350],
      [-52850, 350, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 1, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, -1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 1, inverse := fun i j => (([
      [1, 0, 0, 0],
      [-111, 0, 1, 0],
      [-912, 0, 0, 1],
      [-151, 1, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 2, 3, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, -59, 30] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 47250, inverse := fun i j => (([
      [47250, 0, 0, 0],
      [-5244750, 0, 0, 47250],
      [-43092000, -45, 315, 168750],
      [17739225, -49, -182, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([1, 2, 4, 7] : List Nat).contains i.val,
        normal := fun i => ([91, 7007, 61016, 13286, -13741] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 54964, inverse := fun i j => (([
      [364, 0, 0, 0],
      [-26936, 0, 0, 54964],
      [-139325, -151, 95130, 196300],
      [53144, 0, -54964, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 3, 4, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([1, 77, -724, 146, -151] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 14798, inverse := fun i j => (([
      [98, 0, 0, 0],
      [-7252, 0, 0, 14798],
      [-97075, 151, -13590, 52850],
      [14308, 0, -14798, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([2, 3, 5, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([29, -3219, -26448, -466, 5773] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 18184950, inverse := fun i j => (([
      [98, 364, -94500, 0],
      [-10878, -40404, 10489500, 18184950],
      [-106695, -210735, 86184000, 64946250],
      [17934, 66612, -35478450, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([2, 4, 5, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([13, -1443, -8331, 1898, 481] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 5, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 13468, inverse := fun i j => (([
      [0, -364, 364, 0],
      [0, 40404, -40404, 13468],
      [-37, 210735, -187425, 48100],
      [0, -66612, 53144, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([3, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([7, -495, -6384, 1022, 259] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 12950, inverse := fun i j => (([
      [0, -350, 350, 0],
      [-37, 21531, -18201, 3626],
      [0, 319200, -319200, 12950],
      [0, -64050, 51100, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([4, 5, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -111, -912, 146, 37] : List (Int)).getD i.val 0,
        rows := fun i => ([4, 5, 6, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 37, inverse := fun i j => (([
      [-1, 1, 0, 0],
      [111, -111, 37, 0],
      [912, -912, 0, 37],
      [-183, 146, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 4, 5] : List Nat).contains i.val,
        rows := fun i => ([1, 4, 5] : List (Fin 10)).getD i.val 0, denominator := fun i => ([188, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 6, 7] : List Nat).contains i.val,
        rows := fun i => ([1, 6, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([188, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, 1, -1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 1, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([1, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([188, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [1, 1, -1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([2, 3, 6, 8] : List Nat).contains i.val,
        rows := fun i => ([3, 6, 8] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [7, 3750, -1050],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 0],
      [0, 0, 1],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([4, 5, 6, 7] : List Nat).contains i.val,
        rows := fun i => ([5, 6, 7] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([4, 5, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([5, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, -1, 1],
      [1, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([6, 7, 8, 9] : List Nat).contains i.val,
        rows := fun i => ([7, 8, 9] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [1, 1, -1],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [0, 525, -1, 0, 0, 630, 1300, 0, 770, -1134],
      [0, -5625, 7, 26, 12150, -18900, 0, 0, 0, 0],
      [-188, 1, 0, 0, -1, 1, 0, 0, 0, 0],
      [0, 75, 0, -1, 90, 0, 0, -350, 0, 98],
      [188, -1, 0, 0, 0, 0, -1, 1, 0, 0],
      [0, 0, 0, 0, -1, 1, 0, 0, -1, 1],
      [-1057500, 0, 7, 26, 6525, -13275, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1, -1, -1, 1],
      [0, 0, 0, 0, 0, 0, -1, 1, 1, -1],
      [0, 0, 1, -7, 0, 0, -3750, 0, 1050, 0],
      [0, 0, -1, 7, 0, 0, 3750, 0, -1050, 0],
      [0, 0, 0, 0, 1, -1, 1, -1, 0, 0],
      [-188, 1, 0, 0, 0, 0, 1, -1, 0, 0],
      [1057500, 0, -7, -26, -6525, 13275, 0, 0, 0, 0],
      [0, 0, 0, 0, -1, 1, -1, 1, 0, 0],
      [0, 0, 0, 0, 1, -1, 0, 0, 1, -1],
      [188, -1, 0, 0, 0, 0, 0, 0, -1, 1],
      [-188, 1, 0, 0, 0, 0, 0, 0, 1, -1],
      [0, -75, 0, 1, -90, 0, 0, 350, 0, -98],
      [2284200, -6525, -7, -26, 0, 6750, 0, 0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Type53
