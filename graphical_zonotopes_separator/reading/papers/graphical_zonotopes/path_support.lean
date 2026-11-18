module

public import Papers.GraphicalZonotopes.GraphicalCone
public import Papers.GraphicalZonotopes.PathPropagation
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

/-- The third power of the path on labels `0,...,n-1`. -/
def graph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + 3 ∧ v.val ≤ u.val + 3
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A translated finite mask, intersected with the actual vertex set. Bounds
are imposed explicitly when full-size cliques are used. -/
def window (n i : ℕ) (T : Finset ℕ) : Finset (Fin n) :=
  univ.filter (fun v => i ≤ v.val ∧ v.val - i ∈ T)

@[simp] theorem mem_window (n i : ℕ) (T : Finset ℕ) (v : Fin n) :
    v ∈ window n i T ↔ i ≤ v.val ∧ v.val - i ∈ T := by simp [window]

def masks : Finset (Finset ℕ) :=
  {{0,1}, {0,2}, {0,3}, {0,1,2}, {0,1,3}, {0,2,3}, {0,1,2,3}}

/-- The seven nonsingleton subsets of a four-position window containing its
least position. The proof has no bound on the path length. -/
theorem mask_classification {T : Finset ℕ} (h0 : 0 ∈ T)
    (hT : T ⊆ {0,1,2,3}) (hc : 2 ≤ T.card) : T ∈ masks := by
  have hmem : ∀ k, k ∈ T → k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    intro k hk
    simpa only [mem_insert, mem_singleton] using hT hk
  by_cases h1 : 1 ∈ T <;> by_cases h2 : 2 ∈ T <;> by_cases h3 : 3 ∈ T
  · have he : T = {0,1,2,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1,2} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,2,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,2} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he] at hc

theorem window_card {n i : ℕ} (T : Finset ℕ)
    (hbound : ∀ k ∈ T, i + k < n) : (window n i T).card = T.card := by
  apply card_bij (fun v hv => v.val - i)
  · intro v hv
    exact ((mem_window n i T v).mp hv).2
  · intro v hv w hw he
    have hv' := ((mem_window n i T v).mp hv).1
    have hw' := ((mem_window n i T w).mp hw).1
    apply Fin.ext
    omega
  · intro k hk
    refine ⟨⟨i+k, hbound k hk⟩, ?_, ?_⟩
    · simp [window, hk]
    · simp

/-- Every nonsingleton clique is exactly one of the seven listed local patterns,
with every mask coordinate inside the true finite vertex set. -/
theorem clique_window_classification {n : ℕ} {C : Finset (Fin n)}
    (hc : 2 ≤ C.card)
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (graph n).Adj u v) :
    ∃ i T, T ∈ masks ∧ (∀ k ∈ T, i + k < n) ∧ C = window n i T := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let a := C.min' hne
  let i := a.val
  let T := C.image (fun v => v.val - i)
  have ha : a ∈ C := min'_mem C hne
  have hleast : ∀ v ∈ C, i ≤ v.val := by
    intro v hv
    exact min'_le C v hv
  have hupper : ∀ v ∈ C, v.val ≤ i + 3 := by
    intro v hv
    by_cases hva : v = a
    · subst v; omega
    · exact (hcl a ha v hv (Ne.symm hva)).2.2
  have h0 : 0 ∈ T := by
    exact mem_image.mpr ⟨a, ha, by simp [i]⟩
  have hT : T ⊆ {0,1,2,3} := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
    have h1 := hleast v hv
    have h2 := hupper v hv
    simp only [mem_insert, mem_singleton]
    omega
  have hinj : Set.InjOn (fun v : Fin n => v.val - i) C := by
    intro v hv w hw he
    change v.val-i=w.val-i at he
    have h1 := hleast v hv
    have h2 := hleast w hw
    apply Fin.ext
    omega
  have hcard : 2 ≤ T.card := by
    rw [show T = C.image (fun v => v.val - i) from rfl, card_image_iff.mpr hinj]
    exact hc
  refine ⟨i, T, mask_classification h0 hT hcard, ?_, ?_⟩
  · intro k hk
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
    have h := hleast v hv
    omega
  · ext v
    rw [mem_window]
    constructor
    · intro hv
      exact ⟨hleast v hv, mem_image.mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hk⟩
      obtain ⟨w, hw, he⟩ := mem_image.mp hk
      have hw' := hleast w hw
      change w.val-i=v.val-i at he
      have hwe : w = v := Fin.ext (by omega)
      simpa [hwe] using hw

/-- Reading all coefficients, including the zero ones, in the paper's coordinates. -/
def coordinates {n : ℕ} (y : SetFunction (Fin n)) : Coordinates n where
  edge1 := fun i => y (window n i.val {0,1})
  edge2 := fun i => y (window n i.val {0,2})
  edge3 := fun i => y (window n i.val {0,3})
  tri012 := fun i => y (window n i.val {0,1,2})
  tri013 := fun i => y (window n i.val {0,1,3})
  tri023 := fun i => y (window n i.val {0,2,3})
  tetra := fun i => y (window n i.val {0,1,2,3})

/-- The seven coordinate families determine every normalized clique-supported
coefficient: there is no omitted independent coefficient. -/
theorem coordinates_injective_on_supported {n : ℕ} {y y' : SetFunction (Fin n)}
    (hy : CliqueSupported (graph n) y) (hy' : CliqueSupported (graph n) y')
    (he : coordinates y = coordinates y') : y = y' := by
  funext C
  by_cases hc : 2 ≤ C.card
  · by_cases hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (graph n).Adj u v
    · obtain ⟨i, T, hT, hbound, rfl⟩ := clique_window_classification hc hcl
      simp only [masks, mem_insert, mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have hi : i < n - 1 := by have h := hbound 1 (by simp); omega
        exact congrFun (congrArg Coordinates.edge1 he) ⟨i, hi⟩
      · have hi : i < n - 2 := by have h := hbound 2 (by simp); omega
        exact congrFun (congrArg Coordinates.edge2 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.edge3 he) ⟨i, hi⟩
      · have hi : i < n - 2 := by have h := hbound 2 (by simp); omega
        exact congrFun (congrArg Coordinates.tri012 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tri013 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tri023 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tetra he) ⟨i, hi⟩
    · push_neg at hcl
      obtain ⟨u, hu, v, hv, huv, hnon⟩ := hcl
      rw [hy.2.2 C u v hu hv huv hnon, hy'.2.2 C u v hu hv huv hnon]
  · have hc' : C.card ≤ 1 := by omega
    obtain hC | hC := Nat.le_one_iff_eq_zero_or_eq_one.mp hc'
    · have heC : C = ∅ := card_eq_zero.mp hC
      rw [heC, hy.1, hy'.1]
    · obtain ⟨v, rfl⟩ := card_eq_one.mp hC
      rw [hy.2.1 v, hy'.2.1 v]

end Path
end GraphicalZonotopes
