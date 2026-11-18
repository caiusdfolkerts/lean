module

public import Continuation.CycleBounds.TwoChords
public import Continuation.CycleBounds.NoncrossingWords

@[expose] public section

/-! # No-K4 graphs give noncrossing active-component partitions

This is the literal graph-minor step of Proposition6.8. Connected components are
used through ordinary monochromatic graph walks; no cactus or noncrossing
property is a hypothesis of the result.
-/

noncomputable section
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E α : Type*}

/-- The cycle partition of any connected-component labeling in a K4-minor-free
multigraph is noncrossing. -/
theorem noncrossing_of_no_K4 {G : IncidenceGraph V E}
    (hK : ¬G.HasK4Minor) (c : V → α)
    (hconnected : ∀ x y, x ≠ y → c x = c y → ∃ l : List V,
      (x :: (l ++ [y])).IsChain (Adj G) ∧
      ∀ z ∈ x :: (l ++ [y]), c z = c x)
    (w : List V) (hw : CycleWord G w) : Noncrossing (w.map c) := by
  intro A B hAB hcross
  obtain ⟨a, b, a', b', ha, hb, ha', hb', p₀, p₁, p₂, p₃, p₄, heq⟩ :=
    alternating_vertices c hcross
  let I := p₂ ++ a' :: p₃
  let O := p₄ ++ p₀ ++ a :: p₁
  have hcy₁ : CycleWord G (b :: (I ++ b' :: O)) := by
    have hh := hw.rotate_of_eq
      (u := p₀ ++ a :: p₁) (v := b :: (p₂ ++ a' :: (p₃ ++ b' :: p₄)))
      (by simpa only [List.append_assoc, List.cons_append] using heq)
    simpa only [I, O, List.append_assoc, List.cons_append] using hh
  have haa' : a ≠ a' := by
    have htail : (a :: (p₁ ++ b :: (p₂ ++ a' :: (p₃ ++ b' :: p₄)))).Nodup :=
      (List.nodup_append.mp (heq ▸ hw.nodup)).2.1
    intro he
    apply (List.nodup_cons.mp htail).1
    rw [he]
    simp
  have hbb' : b ≠ b' := by
    intro he
    apply (List.nodup_cons.mp hcy₁.nodup).1
    rw [he]
    simp
  obtain ⟨la, hla, hma⟩ := hconnected a a' haa' (ha.trans ha'.symm)
  have hma' : ∀ z ∈ a :: (la ++ [a']), c z = A := by
    intro z hz
    exact (hma z hz).trans ha
  obtain ⟨x, hxO, y, hyI, pa, hpa, hpaAvoid, hpaMono⟩ :=
    bridge_across_arcs c A B hAB b b' a I O (la ++ [a']) hcy₁ hb hb'
      (by simp [O]) hla hma' ⟨a', by simp, by simp [I]⟩
  obtain ⟨O₁, O₂, hO⟩ := List.mem_iff_append.mp hxO
  obtain ⟨I₁, I₂, hI⟩ := List.mem_iff_append.mp hyI
  let J := O₂ ++ b :: I₁
  let K := I₂ ++ b' :: O₁
  have hcy₂ : CycleWord G (x :: (J ++ y :: K)) := by
    have hh := hcy₁.rotate_of_eq
      (u := b :: (I₁ ++ y :: (I₂ ++ b' :: O₁))) (v := x :: O₂)
      (by simp only [hI, hO, List.append_assoc, List.cons_append])
    simpa only [J, K, List.append_assoc, List.cons_append] using hh
  have hcx : c x = A := hpaMono x (by simp)
  have hcy : c y = A := hpaMono y (by simp)
  obtain ⟨lb, hlb, hmb⟩ := hconnected b' b hbb'.symm (hb'.trans hb.symm)
  have hmb' : ∀ z ∈ b' :: (lb ++ [b]), c z = B := by
    intro z hz
    exact (hmb z hz).trans hb'
  obtain ⟨z, hzK, t, htJ, pb, hpb, hpbAvoid, hpbMono⟩ :=
    bridge_across_arcs c B A hAB.symm x y b' J K (lb ++ [b]) hcy₂ hcx hcy
      (by simp [K]) hlb hmb' ⟨b, by simp, by simp [J]⟩
  obtain ⟨J₁, J₂, hJ⟩ := List.mem_iff_append.mp htJ
  obtain ⟨K₁, K₂, hKsplit⟩ := List.mem_iff_append.mp hzK
  let W := x :: (J₁ ++ t :: (J₂ ++ y :: (K₁ ++ z :: K₂)))
  have hW : x :: (J ++ y :: K) = W := by
    simp only [W, hJ, hKsplit, List.append_assoc, List.cons_append]
  have hcyW : CycleWord G W := hW ▸ hcy₂
  have hmem (v : V) : v ∈ b :: (I ++ b' :: O) ↔ v ∈ W := by
    rw [← hW]
    simp only [hI, hO, J, K, List.mem_cons, List.mem_append]
    tauto
  have hpaW : ∀ v ∈ pa, v ∉ W := by
    intro v hv hWv
    exact hpaAvoid v hv ((hmem v).mpr hWv)
  have hpbW : ∀ v ∈ pb.reverse, v ∉ W := by
    intro v hv hWv
    exact hpbAvoid v (List.mem_reverse.mp hv) (hW.symm ▸ hWv)
  have hdis : List.Disjoint pa pb.reverse := by
    apply List.disjoint_left.mpr
    intro v hva hvb
    have hA := hpaMono v (by simp [hva])
    have hB := hpbMono v (by simp [List.mem_reverse.mp hvb])
    exact hAB (hA.symm.trans hB)
  exact hK (cycle_two_chords_hasK4Minor x t y z J₁ J₂ K₁ K₂ pa pb.reverse
    hcyW hpa (reverse_arc hpb) hpaW hpbW hdis)

#print axioms noncrossing_of_no_K4
end Unimodular.CycleBounds
