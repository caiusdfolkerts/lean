module
prelude
public import Papers.IntegerFacetRawData

/-! Constructive assembly of all Boolean-mask branches. The leaf proofs name
their actual facet, low-rank, or separating-relation witness; no unverified
enumeration or Boolean soundness assertion is imported. -/

@[expose] public section
namespace Papers.RationalWitnesses.Raw

abbrev Covered {n f l c : Nat} (C : FacetCertificate n f l c) (S : VertexMask n) : Prop :=
  (∃ k, ∀ i, S i = (C.facets k).vertices i) ∨
  card S ≤ 3 ∨ (∀ i, S i = true) ∨
  (∃ k, ∀ i, S i = true → (C.lowRanks k).vertices i = true) ∨
  ∃ k, RelationExcludes (C.relations k) S

theorem coverage_iff_forallCovered {n f l c : Nat} (C : FacetCertificate n f l c) :
    Coverage C ↔ ∀ S, Covered C S := Iff.rfl

theorem forallMask_zero (P : VertexMask 0 → Prop)
    (h : P (fun i => Fin.elim0 i)) : ∀ S, P S := by
  intro S
  have hS : S = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  simpa only [hS] using h

theorem forallMask_succ {n : Nat} (P : VertexMask (n + 1) → Prop)
    (hfalse : ∀ S : VertexMask n, P (Fin.cases false S))
    (htrue : ∀ S : VertexMask n, P (Fin.cases true S)) : ∀ S, P S := by
  intro S
  have hS : S = Fin.cases (S 0) (fun i => S i.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  cases hzero : S 0 with
  | false => exact (congrArg P hS).mpr (by
      simpa only [hzero] using hfalse (fun i => S i.succ))
  | true => exact (congrArg P hS).mpr (by
      simpa only [hzero] using htrue (fun i => S i.succ))

end Papers.RationalWitnesses.Raw
