module
prelude
public import Papers.IntegerFacetRawData
public import Init.Data.List.BasicAux

/-! Sole Lean integer data for Appendix B type679.
Untrusted generated input. The corresponding check module proves its finite
properties by ordinary kernel reduction; no real theorem is assumed. -/

@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type679
open Papers.RationalWitnesses.Raw

def coordinates : Configuration 10 :=
  fun i j => (([
      [32055, 18000, 2910, 6902, 13757],
      [42235, 19400, -2910, 3298, 7663],
      [12553, 2910, -2910, 4947, 4365],
      [63815, 0, 18430, 3686, 12901],
      [8750, 1455, -1455, 0, -291],
      [1, 0, 0, 0, 0],
      [2, 1, 0, 0, 0],
      [1, 0, 1, 0, 0],
      [1, 0, 0, 1, 0],
      [1, 0, 0, 0, -1]] : List (List Int)).getD i.val []).getD j.val 0

def certificate : FacetCertificate 10 13 1 23 where
  spanningRows := fun i => ([0, 1, 2, 3, 6] : List (Fin 10)).getD i.val 0
  spanningDenominator := 1116116415600
  spanningInverse := fun i j => (([
      [-32178780, 27202680, 17692800, 12169620, 0],
      [64357560, -54405360, -35385600, -24339240, 1116116415600],
      [86890369, -173852300, -17692800, 16596267, 1860194026000],
      [85555940, -320501920, 328983600, -12169620, 3720388052000],
      [10599190, 205373920, -156237600, 6084810, -3720388052000]] : List (List Int)).getD i.val []).getD j.val 0
  facets := fun k => match k.val with
    | 0 => {
        vertices := fun i => ([0, 1, 2, 3, 4, 5] : List Nat).contains i.val,
        normal := fun i => ([0, 3, 5, 10, -10] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 3] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 372038805200, inverse := fun i j => (([
      [-10726260, 9067560, 5897600, 4056540],
      [22512439, 2402272, -27418960, -7504599],
      [30729988, -23721780, -31937200, 6546224],
      [32051710, -38376000, 57582000, -2028270]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 1 => {
        vertices := fun i => ([0, 1, 2, 6, 8] : List Nat).contains i.val,
        normal := fun i => ([5820, -11640, 7937, -5820, 2910] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 2, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 5902265700, inverse := fun i j => (([
      [-282270, -2028270, 1746000, 39348438000],
      [564540, 4056540, -3492000, -72794610300],
      [306617, -3881593, 2159940, 63498372800],
      [564540, 477240, 87300, -19674219000]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 2 => {
        vertices := fun i => ([0, 1, 3, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([14744, -29488, -14744, 274153, -130198] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 1, 3, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 128817901200, inverse := fun i j => (([
      [-3575420, 5823880, 1484100, -48625712000],
      [7150840, -11647760, -2968200, 226069325200],
      [9890023, -22749620, 1835949, 263322214000],
      [12450435, 12920400, 74205, -474763590000]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 3 => {
        vertices := fun i => ([0, 2, 3, 7, 8] : List Nat).contains i.val,
        normal := fun i => ([55290, 68261, -55290, -55290, -178710] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 2, 3, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2416480878000, inverse := fun i j => (([
      [10726260, -66348000, 68961180, -1495240644000],
      [167522977, -205818800, -37454689, -396134652800],
      [-10726260, 66348000, -68961180, 3911721522000],
      [-132070350, 816930000, -193522050, 6328202400000]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 4 => {
        vertices := fun i => ([0, 6, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([1, -2, -1, -1, 1] : List (Int)).getD i.val 0,
        rows := fun i => ([0, 6, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 13757, inverse := fun i j => (([
      [-1, 18000, 2910, 6902],
      [2, -22243, -5820, -13804],
      [1, -18000, 10847, -6902],
      [1, -18000, -2910, 6855]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 5 => {
        vertices := fun i => ([1, 2, 4, 6, 9] : List Nat).contains i.val,
        normal := fun i => ([1455, -2910, 5549, 0, 1455] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 2, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 21593655, inverse := fun i j => (([
      [-4365, 2910, 2910, 71978850],
      [8730, -5820, -5820, -122364045],
      [-17520, 11680, -3161, 310498455],
      [-4365, 7275, -5820, 71978850]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 6 => {
        vertices := fun i => ([1, 3, 4, 5, 6] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 2, 25, -10] : List (Int)).getD i.val 0,
        rows := fun i => ([1, 3, 4, 6] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 1454450980, inverse := fun i j => (([
      [-11058, 9894, 147440, 0],
      [22116, -19788, -294880, 1454450980],
      [-44384, 39712, -407836, 1454450980],
      [413365, 24735, -513420, -7272254900]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 7 => {
        vertices := fun i => ([2, 3, 5, 8] : List Nat).contains i.val,
        normal := fun i => ([0, 22, 7, 0, -10] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 3, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 55290, inverse := fun i j => (([
      [0, 0, 55290, 0],
      [19, 3, -324901, -105051],
      [0, 3, -180387, -11058],
      [0, 0, -55290, 55290]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 8 => {
        vertices := fun i => ([2, 4, 5, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 1, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 4, 5, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 24735, inverse := fun i j => (([
      [0, 0, 24735, 0],
      [1, 15, -138856, -4947],
      [0, 0, -24735, 24735],
      [5, -10, 49470, -24735]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 9 => {
        vertices := fun i => ([2, 6, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([2910, -5820, 6151, -2910, 2910] : List (Int)).getD i.val 0,
        rows := fun i => ([2, 6, 8, 9] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 2910, inverse := fun i j => (([
      [0, 0, 0, 2910],
      [0, 2910, 0, -5820],
      [-1, 2910, 4947, 1786],
      [0, 0, 2910, -2910]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 10 => {
        vertices := fun i => ([3, 5, 6, 7] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 7, -2] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 3] : List (Fin 5)).getD i.val 0,
        denominator := 3686, inverse := fun i j => (([
      [0, 3686, 0, 0],
      [0, -7372, 3686, 0],
      [0, -3686, 0, 3686],
      [1, -45385, 0, -18430]] : List (List Int)).getD i.val []).getD j.val 0 }
    | 11 => {
        vertices := fun i => ([3, 5, 7, 8, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 1, 0, 0, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([3, 5, 7, 8] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 2, 3, 4] : List (Fin 5)).getD i.val 0,
        denominator := 12901, inverse := fun i j => (([
      [0, 12901, 0, 0],
      [0, -12901, 12901, 0],
      [0, -12901, 0, 12901],
      [1, -41699, -18430, -3686]] : List (List Int)).getD i.val []).getD j.val 0 }
    | _ => {
        vertices := fun i => ([4, 5, 6, 7, 9] : List Nat).contains i.val,
        normal := fun i => ([0, 0, 0, 1, 0] : List (Int)).getD i.val 0,
        rows := fun i => ([4, 5, 6, 7] : List (Fin 10)).getD i.val 0, columns := fun i => ([0, 1, 2, 4] : List (Fin 5)).getD i.val 0,
        denominator := 291, inverse := fun i j => (([
      [0, 291, 0, 0],
      [0, -582, 291, 0],
      [0, -291, 0, 291],
      [-1, 7295, 1455, -1455]] : List (List Int)).getD i.val []).getD j.val 0 }
  lowRanks := fun k => match k.val with
    | _ => {
        vertices := fun i => ([1, 3, 4, 5] : List Nat).contains i.val,
        rows := fun i => ([3, 4, 5] : List (Fin 10)).getD i.val 0, denominator := fun i => ([1, 57, 1, 1, 1, 1, 1, 1, 1, 1] : List (Int)).getD i.val 0,
        coefficients := fun i j => (([
      [0, 0, 0],
      [51, 760, -7497170],
      [0, 0, 0],
      [1, 0, 0],
      [0, 1, 0],
      [0, 0, 1],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0],
      [0, 0, 0]] : List (List Int)).getD i.val []).getD j.val 0 }
  relations := fun i j => (([
      [0, 0, 1, 0, -2, 4947, 0, 0, -4947, 4947],
      [-1, 0, 0, 0, 0, 0, 18000, 2910, 6902, -13757],
      [679, 0, -4200, 697, 0, 0, 0, -27043600, 13521800, 0],
      [0, -57, 0, 51, 760, -7497170, 0, 0, 0, 0],
      [0, 0, 0, -1, 0, 54600, 0, 18430, 3686, -12901],
      [-5529, 4674, 3040, 2091, 0, -191772580, 0, 0, 0, 0],
      [97, -260, 0, 51, 0, 0, 3298000, -1978800, 0, 0],
      [0, 57, 0, -51, -760, 7497170, 0, 0, 0, 0],
      [19, 0, 0, -3, 0, 163800, -342000, 0, -120080, 222680],
      [0, 1, -1, 0, 0, -1649, -16490, 0, 1649, 3298],
      [97, -533, 630, 0, 0, 0, 6760900, 0, -2028270, 0],
      [-97, 533, -630, 0, 0, 0, -6760900, 0, 2028270, 0],
      [0, 0, 0, 0, -1, 7004, 1455, -1455, 0, 291],
      [0, 0, 0, 0, 1, -7004, -1455, 1455, 0, -291],
      [1, 0, 0, 0, 0, 0, -18000, -2910, -6902, 13757],
      [0, -3, 2, 0, 2, 0, 49470, 0, 0, -14841],
      [12833391, -14233068, -7056160, -1825443, 45122960, 0, 0, 0, 0, 0],
      [0, 0, -1, 0, 2, -4947, 0, 0, 4947, -4947],
      [0, 3, -2, 0, -2, 0, -49470, 0, 0, 14841],
      [0, 0, 0, 1, 0, -54600, 0, -18430, -3686, 12901],
      [-97, 260, 0, -51, 0, 0, -3298000, 1978800, 0, 0],
      [-291, 369, 160, 0, -1640, 6084810, 0, 0, 0, 0],
      [-679, 0, 4200, -697, 0, 0, 0, 27043600, -13521800, 0]] : List (List Int)).getD i.val []).getD j.val 0

end Papers.RationalWitnesses.RawWitnesses.Type679
