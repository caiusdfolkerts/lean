module

public import RawFacePlacement
public import RawFacetEmbeddingSemantics

@[expose] public section

/-!
# Every face-compatible injection has a compressed placement code

The source order puts the common local face first. The target order puts
the common root face first and the vertices outside the root immediately
after it. Only the two resulting smaller injections need to be enumerated.
This lemma is independent of every candidate universe and certificate.
-/

noncomputable section
namespace Papers.RationalityTen.FacePlacementCodes

open FiniteCycleCandidates

structure Block (m : Nat) where
  shared : Nat
  outside : Nat
  shared_le : shared ≤ m
  remaining_le : m - shared ≤ outside
  target_le : shared + outside ≤ 10
  source : Equiv.Perm (Fin m)
  target : Equiv.Perm (Fin 10)

def Block.normalized {m : Nat} (B : Block m) (f : Fin m → Fin 10) (i : Fin m) : Fin 10 :=
  B.target.symm (f (B.source i))

def Block.Fits {m : Nat} (B : Block m) (f : Fin m → Fin 10) : Prop :=
  ∀ i : Fin m, if i.val < B.shared then (B.normalized f i).val < B.shared
    else B.shared ≤ (B.normalized f i).val ∧
      (B.normalized f i).val < B.shared + B.outside

def Block.decoded {m : Nat} (B : Block m) (inner outer : Nat) (i : Fin m) : Fin 10 :=
  B.target (if h : (B.source.symm i).val < B.shared then
      ⟨(decodeInjection B.shared B.shared (Nat.le_refl _) inner
          ⟨(B.source.symm i).val, h⟩).val,
        lt_of_lt_of_le (Fin.isLt _)
          ((Nat.le_add_right B.shared B.outside).trans B.target_le)⟩
    else
      ⟨B.shared + (decodeInjection B.outside (m - B.shared) B.remaining_le outer
          ⟨(B.source.symm i).val - B.shared, by
            have := (B.source.symm i).isLt
            omega⟩).val,
        lt_of_lt_of_le (Nat.add_lt_add_left (Fin.isLt _) _) B.target_le⟩)

theorem count_eq (n k : Nat) : RawFacePlacement.count n k = injectionCount n k := by
  induction k generalizing n with
  | zero => simp only [RawFacePlacement.count, injectionCount]
  | succ k ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [RawFacePlacement.count, injectionCount, ih]

/-- Completeness of the compressed domain. Injectivity is the sole
mathematical property of the original labeling used here. -/
theorem exists_codes {m : Nat} (B : Block m) (f : Fin m ↪ Fin 10)
    (hfit : B.Fits f) :
    ∃ inner, inner < injectionCount B.shared B.shared ∧
      ∃ outer, outer < injectionCount B.outside (m - B.shared) ∧
        B.decoded inner outer = f := by
  have hshared := B.shared_le
  let g := B.normalized f
  have hginj : Function.Injective g :=
    B.target.symm.injective.comp (f.injective.comp B.source.injective)
  have hinner (i : Fin B.shared) :
      (g ⟨i.val, lt_of_lt_of_le i.isLt B.shared_le⟩).val < B.shared := by
    have h := hfit ⟨i.val, lt_of_lt_of_le i.isLt B.shared_le⟩
    simpa only [if_pos i.isLt] using h
  let a : Fin B.shared → Fin B.shared := fun i =>
    ⟨(g ⟨i.val, lt_of_lt_of_le i.isLt B.shared_le⟩).val, hinner i⟩
  have ha : Function.Injective a := by
    intro i j hij
    have hv : (g ⟨i.val, lt_of_lt_of_le i.isLt B.shared_le⟩).val =
        (g ⟨j.val, lt_of_lt_of_le j.isLt B.shared_le⟩).val :=
      congrArg (fun z : Fin B.shared => z.val) hij
    have h := hginj (Fin.ext hv)
    exact Fin.ext (congrArg (fun z : Fin m => z.val) h)
  have houter (i : Fin (m - B.shared)) :
      B.shared ≤ (g ⟨B.shared + i.val, by omega⟩).val ∧
        (g ⟨B.shared + i.val, by omega⟩).val < B.shared + B.outside := by
    have h := hfit ⟨B.shared + i.val, by omega⟩
    simpa only [show ¬ B.shared + i.val < B.shared by omega, if_false] using h
  let b : Fin (m - B.shared) → Fin B.outside := fun i =>
    ⟨(g ⟨B.shared + i.val, by omega⟩).val - B.shared, by
      have := houter i
      omega⟩
  have hb : Function.Injective b := by
    intro i j hij
    have hi := houter i
    have hj := houter j
    have heq : g ⟨B.shared + i.val, by omega⟩ = g ⟨B.shared + j.val, by omega⟩ := by
      apply Fin.ext
      have := congrArg Fin.val hij
      change (g ⟨B.shared + i.val, by omega⟩).val - B.shared =
        (g ⟨B.shared + j.val, by omega⟩).val - B.shared at this
      omega
    have h := congrArg Fin.val (hginj heq)
    apply Fin.ext
    change B.shared + i.val = B.shared + j.val at h
    omega
  obtain ⟨inner, hi, hia⟩ := exists_injection_code (Nat.le_refl B.shared) a ha
  obtain ⟨outer, ho, hob⟩ := exists_injection_code B.remaining_le b hb
  refine ⟨inner, hi, outer, ho, ?_⟩
  funext i
  apply B.target.symm.injective
  simp only [Block.decoded, B.target.symm_apply_apply, hia, hob]
  have hgi : g (B.source.symm i) = B.target.symm (f i) := by
    simp only [g, Block.normalized, B.source.apply_symm_apply]
  split_ifs with h
  · exact (Fin.ext rfl).trans hgi
  · apply Fin.ext
    have hbound := hfit (B.source.symm i)
    rw [if_neg h] at hbound
    have hj : (⟨B.shared + ((B.source.symm i).val - B.shared), by omega⟩ : Fin m) =
        B.source.symm i := by
      apply Fin.ext
      change B.shared + ((B.source.symm i).val - B.shared) = (B.source.symm i).val
      omega
    have hsmall : B.shared ≤ (g (B.source.symm i)).val := hbound.1
    rw [hgi] at hsmall
    change B.shared + ((g ⟨B.shared + ((B.source.symm i).val - B.shared), by omega⟩).val -
        B.shared) = (B.target.symm (f i)).val
    rw [hj, hgi]
    omega

end Papers.RationalityTen.FacePlacementCodes
