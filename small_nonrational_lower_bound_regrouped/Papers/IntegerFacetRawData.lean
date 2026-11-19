module
prelude
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Fin.Lemmas
public import Init.Data.List.OfFn

/-! Finite integer facet certificates with only Lean's `Init` dependency.
The translation to actual Mathlib facet certificates is proved separately in
`IntegerFacetRawBridge`. No theorem about real polytopes is asserted here. -/

@[expose] public section

namespace Papers.RationalWitnesses.Raw

abbrev Configuration (n : Nat) := Fin n → Fin 5 → Int
abbrev VertexMask (n : Nat) := Fin n → Bool

def sumFin {n : Nat} (f : Fin n → Int) : Int := (List.ofFn f).sum

def card {n : Nat} (S : VertexMask n) : Nat :=
  (List.ofFn fun i => if S i = true then 1 else 0).sum

/-- Exhausts all Boolean-valued families. In dimension ten this checks all
1,024 vertex subsets; it does not sample or assume a list is exhaustive. -/
noncomputable def decidableForallMask :
    (n : Nat) → (P : VertexMask n → Prop) →
      [DecidablePred P] → Decidable (∀ S, P S)
  | 0, P, h =>
      match h (fun i => Fin.elim0 i) with
      | isTrue hp => isTrue (fun S => by
          have hS : S = (fun i => Fin.elim0 i) := by
            funext i
            exact Fin.elim0 i
          simpa only [hS] using hp)
      | isFalse hp => isFalse (fun hall => hp (hall _))
  | n + 1, P, h =>
      match @decidableForallMask n (fun S => P (Fin.cases false S))
          (fun S => h (Fin.cases false S)),
            @decidableForallMask n (fun S => P (Fin.cases true S))
          (fun S => h (Fin.cases true S)) with
      | isTrue hf, isTrue ht => isTrue (fun S => by
          have hS : S = Fin.cases (S 0) (fun i => S i.succ) := by
            funext i
            exact Fin.cases rfl (fun _ => rfl) i
          cases hzero : S 0 with
          | false => exact (congrArg P hS).mpr (by
              simpa only [hzero] using hf (fun i => S i.succ))
          | true => exact (congrArg P hS).mpr (by
              simpa only [hzero] using ht (fun i => S i.succ)))
      | isFalse hf, _ => isFalse (fun hall => hf (fun S => hall (Fin.cases false S)))
      | _, isFalse ht => isFalse (fun hall => ht (fun S => hall (Fin.cases true S)))

noncomputable instance {n : Nat} (P : VertexMask n → Prop) [DecidablePred P] :
    Decidable (∀ S, P S) := decidableForallMask n P

/-- A scaled integer right inverse certifies a nonzero square minor.
The bridge proves the determinant conclusion; this finite definition uses
only integer addition and multiplication. -/
def MinorValid {n k : Nat} (w : Configuration n)
    (rows : Fin k → Fin n) (columns : Fin k → Fin 5)
    (denominator : Int) (inverse : Fin k → Fin k → Int) : Prop :=
  denominator ≠ 0 ∧ ∀ i j,
    sumFin (fun t => w (rows i) (columns t) * inverse t j) =
      if i = j then denominator else 0

instance {n k : Nat} (w : Configuration n)
    (rows : Fin k → Fin n) (columns : Fin k → Fin 5)
    (denominator : Int) (inverse : Fin k → Fin k → Int) :
    Decidable (MinorValid w rows columns denominator inverse) := by
  unfold MinorValid
  infer_instance

structure FacetData (n : Nat) where
  vertices : VertexMask n
  normal : Fin 5 → Int
  rows : Fin 4 → Fin n
  columns : Fin 4 → Fin 5
  denominator : Int
  inverse : Fin 4 → Fin 4 → Int

def FacetData.Valid {n : Nat} (w : Configuration n) (F : FacetData n) : Prop :=
  (∃ j, F.normal j ≠ 0) ∧
  (∀ i, F.vertices i = true → sumFin (fun j => F.normal j * w i j) = 0) ∧
  (∀ i, F.vertices i ≠ true → 0 < sumFin (fun j => F.normal j * w i j)) ∧
  (∀ k, F.vertices (F.rows k) = true) ∧
  MinorValid w F.rows F.columns F.denominator F.inverse

instance {n : Nat} (w : Configuration n) (F : FacetData n) :
    Decidable (F.Valid w) := by unfold FacetData.Valid; infer_instance

structure LowRankData (n : Nat) where
  vertices : VertexMask n
  rows : Fin 3 → Fin n
  denominator : Fin n → Int
  coefficients : Fin n → Fin 3 → Int

def LowRankData.Valid {n : Nat} (w : Configuration n) (L : LowRankData n) : Prop :=
  ∀ i, L.vertices i = true → L.denominator i ≠ 0 ∧ ∀ j,
    L.denominator i * w i j =
      sumFin (fun k => L.coefficients i k * w (L.rows k) j)

instance {n : Nat} (w : Configuration n) (L : LowRankData n) :
    Decidable (L.Valid w) := by unfold LowRankData.Valid; infer_instance

def RelationValid {n : Nat} (w : Configuration n) (c : Fin n → Int) : Prop :=
  ∀ j, sumFin (fun i => c i * w i j) = 0

def RelationExcludes {n : Nat} (c : Fin n → Int) (S : VertexMask n) : Prop :=
  (∀ i, S i ≠ true → 0 ≤ c i) ∧ ∃ i, S i ≠ true ∧ 0 < c i

instance {n : Nat} (w : Configuration n) (c : Fin n → Int) :
    Decidable (RelationValid w c) := by unfold RelationValid; infer_instance
instance {n : Nat} (c : Fin n → Int) (S : VertexMask n) :
    Decidable (RelationExcludes c S) := by unfold RelationExcludes; infer_instance

structure FacetCertificate (n f l c : Nat) where
  spanningRows : Fin 5 → Fin n
  spanningDenominator : Int
  spanningInverse : Fin 5 → Fin 5 → Int
  facets : Fin f → FacetData n
  lowRanks : Fin l → LowRankData n
  relations : Fin c → Fin n → Int

def Coverage {n f l c : Nat} (C : FacetCertificate n f l c) : Prop :=
  ∀ S : VertexMask n,
    (∃ k, ∀ i, S i = (C.facets k).vertices i) ∨
    card S ≤ 3 ∨ (∀ i, S i = true) ∨
    (∃ k, ∀ i, S i = true → (C.lowRanks k).vertices i = true) ∨
    ∃ k, RelationExcludes (C.relations k) S

noncomputable instance {n f l c : Nat} (C : FacetCertificate n f l c) :
    Decidable (Coverage C) := by unfold Coverage; infer_instance

def FacetCertificate.Valid {n f l c : Nat}
    (w : Configuration n) (C : FacetCertificate n f l c) : Prop :=
  MinorValid w C.spanningRows id C.spanningDenominator C.spanningInverse ∧
  (∀ k, (C.facets k).Valid w) ∧
  (∀ k, (C.lowRanks k).Valid w) ∧
  (∀ k, RelationValid w (C.relations k)) ∧ Coverage C

noncomputable instance {n f l c : Nat} (w : Configuration n)
    (C : FacetCertificate n f l c) : Decidable (C.Valid w) := by
  unfold FacetCertificate.Valid
  infer_instance

end Papers.RationalWitnesses.Raw
