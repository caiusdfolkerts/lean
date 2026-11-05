import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# The graph of a combinatorial cube

Vertices are actual bit vectors. Edges change exactly one coordinate.
The counting lemmas apply to every proper two-coloring, so they do not choose
or assume a particular orientation of a polytope's bipartition.
-/

namespace Cubical.Cube

abbrev Vertex (n : ℕ) := Fin n → Bool

def flip {n : ℕ} (x : Vertex n) (i : Fin n) : Vertex n :=
  Function.update x i (!(x i))

@[simp] theorem flip_same {n : ℕ} (x : Vertex n) (i : Fin n) :
    flip x i i = !(x i) := by simp [flip]

@[simp] theorem flip_other {n : ℕ} (x : Vertex n) (i j : Fin n) (h : j ≠ i) :
    flip x i j = x j := by simp [flip, h]

@[simp] theorem flip_flip {n : ℕ} (x : Vertex n) (i : Fin n) :
    flip (flip x i) i = x := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem flip_ne_self {n : ℕ} (x : Vertex n) (i : Fin n) : flip x i ≠ x := by
  intro h
  have hi := congrFun h i
  simpa using hi

theorem flip_index_injective {n : ℕ} (x : Vertex n) :
    Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simpa [hij] using hi

theorem flip_comm {n : ℕ} (x : Vertex n) (i j : Fin n) :
    flip (flip x i) j = flip (flip x j) i := by
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> subst_vars <;> simp_all

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := ∃ i, y = flip x i
  symm := by
    constructor
    rintro x y ⟨i, rfl⟩
    exact ⟨i, (flip_flip x i).symm⟩
  loopless := by
    constructor
    intro x
    rintro ⟨i, hi⟩
    exact flip_ne_self x i hi.symm

theorem graph_adj_iff {n : ℕ} (x y : Vertex n) :
    (graph n).Adj x y ↔ ∃ i, y = flip x i := Iff.rfl

/-- The local two-coloring condition on cube edges. -/
def ProperColoring {n : ℕ} (c : Vertex n → Bool) : Prop :=
  ∀ x i, c (flip x i) = !(c x)

abbrev Black {n : ℕ} (c : Vertex n → Bool) := {x : Vertex n // c x = false}
abbrev White {n : ℕ} (c : Vertex n → Bool) := {x : Vertex n // c x = true}

def colorSplit {n : ℕ} (c : Vertex n → Bool) : Vertex n ≃ (Black c ⊕ White c) where
  toFun x := if h : c x = false then Sum.inl ⟨x, h⟩
    else Sum.inr ⟨x, by cases h' : c x <;> simp_all⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv x := by by_cases h : c x = false <;> simp [h]
  right_inv x := by
    rcases x with ⟨x, hx⟩ | ⟨x, hx⟩ <;> simp [hx]

def colorEquiv {n : ℕ} (c : Vertex n → Bool) (hc : ProperColoring c) (i : Fin n) :
    Black c ≃ White c where
  toFun x := ⟨flip x i, by rw [hc, x.property]; rfl⟩
  invFun x := ⟨flip x i, by rw [hc, x.property]; rfl⟩
  left_inv x := Subtype.ext (flip_flip x i)
  right_inv x := Subtype.ext (flip_flip x i)

theorem card_vertex (n : ℕ) : Fintype.card (Vertex n) = 2 ^ n := by simp [Vertex]

theorem card_colors {k : ℕ} (c : Vertex (k + 1) → Bool) (hc : ProperColoring c) :
    Fintype.card (Black c) = 2 ^ k ∧ Fintype.card (White c) = 2 ^ k := by
  have heq := Fintype.card_congr (colorEquiv c hc (Fin.last k))
  have hsum := Fintype.card_congr (colorSplit c)
  rw [card_vertex, Fintype.card_sum, pow_succ] at hsum
  omega

/-- Edges oriented from black to white, indexed by their black endpoint and
the changed coordinate. -/
abbrev Edge {n : ℕ} (c : Vertex n → Bool) := Black c × Fin n

def whiteEndpoint {n : ℕ} (c : Vertex n → Bool) (hc : ProperColoring c)
    (e : Edge c) : White c :=
  ⟨flip e.1 e.2, by rw [hc, e.1.property]; rfl⟩

theorem whiteEndpoint_injective_at_black {n : ℕ}
    (c : Vertex n → Bool) (hc : ProperColoring c) (b : Black c) :
    Function.Injective (fun i ↦ whiteEndpoint c hc (b, i)) := by
  intro i j h
  apply flip_index_injective b.val
  exact congrArg Subtype.val h

theorem card_edge {k : ℕ} (c : Vertex (k + 1) → Bool) (hc : ProperColoring c) :
    Fintype.card (Edge c) = (k + 1) * 2 ^ k := by
  simp only [Edge, Fintype.card_prod, Fintype.card_fin, (card_colors c hc).1, mul_comm]

/-- The coordinate matching across a facet of a cube. -/
theorem matched_across_ridge {n : ℕ} (x : Vertex n) (i : Fin n) (a : Bool)
    (hx : x i ≠ a) : (flip x i) i = a := by
  rw [flip_same]
  cases h : x i <;> cases a <;> simp_all

theorem matched_black_to_white {n : ℕ} (c : Vertex n → Bool)
    (hc : ProperColoring c) (x : Vertex n) (i : Fin n) (a : Bool)
    (hx : x i ≠ a) (hblack : c x = false) :
    ∃ y : Vertex n, y i = a ∧ c y = true ∧ (graph n).Adj x y := by
  refine ⟨flip x i, matched_across_ridge x i a hx, ?_, ⟨i, rfl⟩⟩
  rw [hc, hblack]
  rfl

/-- The vertices of the cube face with free coordinates `A` through `s`. -/
def FaceAt {n : ℕ} (s : Vertex n) (A : Finset (Fin n)) : Set (Vertex n) :=
  {t | ∀ i, i ∉ A → t i = s i}

theorem flip_mem_faceAt_iff {n : ℕ} (s : Vertex n) (A : Finset (Fin n)) (i : Fin n) :
    flip s i ∈ FaceAt s A ↔ i ∈ A := by
  classical
  constructor
  · intro h
    by_contra hi
    have hbad := h i hi
    simpa using hbad
  · intro hi j hj
    have hji : j ≠ i := by intro h; subst j; exact hj hi
    exact flip_other s i j hji

noncomputable def faceNeighborEquiv {n : ℕ} (s : Vertex n) (A : Finset (Fin n)) :
    A ≃ {t : Vertex n // t ∈ FaceAt s A ∧ (graph n).Adj s t} :=
  Equiv.ofBijective
    (fun i => ⟨flip s i, (flip_mem_faceAt_iff s A i).mpr i.property, ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      exact Subtype.ext (flip_index_injective s (congrArg Subtype.val h)),
     by
      rintro ⟨t, ht, i, rfl⟩
      exact ⟨⟨i, (flip_mem_faceAt_iff s A i).mp ht⟩, rfl⟩⟩

theorem ridge_matching {n : ℕ} (s x : Vertex n) (A : Finset (Fin n))
    (hA : A.card + 1 = n) (hx : x ∉ FaceAt s A) :
    ∃ y : Vertex n, y ∈ FaceAt s A ∧ (graph n).Adj x y := by
  classical
  have hcard : Aᶜ.card = 1 := by simp only [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have houtside (j : Fin n) (hj : j ∉ A) : j = i := by
    have : j ∈ Aᶜ := Finset.mem_compl.mpr hj
    simpa only [hi, Finset.mem_singleton] using this
  have hxi : x i ≠ s i := by
    intro heq
    apply hx
    intro j hj
    simpa only [houtside j hj] using heq
  refine ⟨flip x i, ?_, ⟨i, rfl⟩⟩
  intro j hj
  rw [houtside j hj]
  exact matched_across_ridge x i (s i) hxi

/-- In a two-dimensional cube face, two distinct neighbors of a vertex have
a second common neighbor; they are its only neighbors within that face. -/
theorem square_completion {n : ℕ} (s a b : Vertex n) (A : Finset (Fin n))
    (hA : A.card = 2) (ha : a ∈ FaceAt s A) (hb : b ∈ FaceAt s A)
    (hsa : (graph n).Adj s a) (hsb : (graph n).Adj s b) (hab : a ≠ b) :
    ∃ z : Vertex n, z ∈ FaceAt s A ∧ z ≠ s ∧
      (graph n).Adj a z ∧ (graph n).Adj b z ∧
      ∀ y, y ∈ FaceAt s A → (graph n).Adj s y → y = a ∨ y = b := by
  classical
  obtain ⟨i, rfl⟩ := hsa
  obtain ⟨j, rfl⟩ := hsb
  have hi := (flip_mem_faceAt_iff s A i).mp ha
  have hj := (flip_mem_faceAt_iff s A j).mp hb
  have hij : i ≠ j := by intro h; subst j; exact hab rfl
  have hAeq : A = {i, j} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rcases Finset.mem_insert.mp hk with hki | hkj
      · simpa [hki] using hi
      · simpa [Finset.mem_singleton.mp hkj] using hj
    · simp [hij, hA]
  let z := flip (flip s i) j
  refine ⟨z, ?_, ?_, ⟨j, rfl⟩, ⟨i, flip_comm s i j⟩, ?_⟩
  · intro k hk
    have hki : k ≠ i := fun h ↦ hk (h ▸ hi)
    have hkj : k ≠ j := fun h ↦ hk (h ▸ hj)
    simp [z, hki, hkj]
  · intro heq
    have h := congrFun heq i
    simp [z, hij] at h
  · intro y hy hsy
    obtain ⟨k, rfl⟩ := hsy
    have hk := (flip_mem_faceAt_iff s A k).mp hy
    rw [hAeq] at hk
    rcases Finset.mem_insert.mp hk with hki | hkj
    · exact Or.inl (congrArg (flip s) hki)
    · exact Or.inr (congrArg (flip s) (Finset.mem_singleton.mp hkj))

end Cubical.Cube
