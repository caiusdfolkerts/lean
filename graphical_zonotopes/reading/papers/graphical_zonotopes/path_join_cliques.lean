module

public import Papers.GraphicalZonotopes.PathJoinPolynomial

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset

def privatePart {n : ℕ} (C : Finset (Vertex n)) : Finset (Vertex n) :=
  (C.erase (hubA n)).erase (hubB n)

@[simp] theorem privatePart_hub {n : ℕ} :
    privatePart (clique (.inl () : Slot n))=∅ := by simp [privatePart,clique]

@[simp] theorem privatePart_single {n : ℕ} (r : Fin 3) (i : Fin (n+2)) :
    privatePart (clique (.inr (.inl (r,i)) : Slot n))={vertex i} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem privatePart_pair {n : ℕ} (r : Fin 4) (i : Fin (n+1)) :
    privatePart (clique (.inr (.inr (r,i)) : Slot n))=
      {vertex i.castSucc,vertex i.succ} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem vertex_mem_privatePart {n : ℕ} (C : Finset (Vertex n))
    (i : Fin (n+2)) : vertex i∈privatePart C ↔ vertex i∈C := by
  simp [privatePart]

theorem eq_of_privatePart {n : ℕ} {C D : Finset (Vertex n)}
    (hp : privatePart C=privatePart D)
    (ha : hubA n∈C ↔ hubA n∈D) (hb : hubB n∈C ↔ hubB n∈D) : C=D := by
  ext v
  rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
  · exact ha
  · exact hb
  · rw [← vertex_mem_privatePart C i,← vertex_mem_privatePart D i,hp]

theorem pathPair_injective {n : ℕ} : Function.Injective
    (fun i : Fin (n+1) => ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))) := by
  intro i j h
  change ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))=
    {vertex j.castSucc,vertex j.succ} at h
  have hl : vertex i.castSucc ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  have hr : vertex i.succ ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  simp only [mem_insert,mem_singleton,vertex_inj,Fin.ext_iff,vertex,
    Fin.val_castSucc,Fin.val_succ] at hl hr
  apply Fin.ext
  omega

theorem clique_injective {n : ℕ} : Function.Injective (clique (n := n)) := by
  intro x y h
  have hp := congrArg privatePart h
  have ha : hubA n∈clique x ↔ hubA n∈clique y := by rw [h]
  have hb : hubB n∈clique x ↔ hubB n∈clique y := by rw [h]
  rcases x with u | ⟨r,i⟩ | ⟨r,i⟩ <;>
    rcases y with v | ⟨s,j⟩ | ⟨s,j⟩
  · cases u; cases v; rfl
  · cases u; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp).elim
  · cases u; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex j.castSucc∈(∅ : Finset (Vertex n)) := by rw [hp]; simp
    simp at hm
  · cases v; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp.symm).elim
  · simp only [privatePart_single,Finset.singleton_inj,vertex_inj] at hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right j)] at hc
    omega
  · cases v; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex i.castSucc∈(∅ : Finset (Vertex n)) := by rw [← hp]; simp
    simp at hm
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right i)] at hc
    omega
  · simp only [privatePart_pair] at hp
    have hij := pathPair_injective hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl

theorem privatePart_vertex {n : ℕ} {C : Finset (Vertex n)} {v : Vertex n}
    (hv : v∈privatePart C) : ∃ i : Fin (n+2),v=vertex i := by
  have hA : v≠hubA n := (mem_erase.mp (mem_erase.mp hv).2).1
  have hB : v≠hubB n := (mem_erase.mp hv).1
  rcases vertex_cases v with ha | hb | hi
  · exact (hA ha).elim
  · exact (hB hb).elim
  · exact hi

theorem privatePart_subset {n : ℕ} (C : Finset (Vertex n)) : privatePart C⊆C :=
  (erase_subset _ _).trans (erase_subset _ _)

theorem privatePart_card_le_two {n : ℕ} {C : Finset (Vertex n)}
    (hC : (graph n).IsClique C) : (privatePart C).card≤2 := by
  by_contra hn
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp (Nat.lt_of_not_ge hn)
  obtain ⟨i,rfl⟩ := privatePart_vertex hu
  obtain ⟨j,rfl⟩ := privatePart_vertex hv
  obtain ⟨k,rfl⟩ := privatePart_vertex hw
  have hij := (graph_vertices i j).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hv) huv)
  have hik := (graph_vertices i k).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hw) huw)
  have hjk := (graph_vertices j k).mp
    (hC (privatePart_subset C hv) (privatePart_subset C hw) hvw)
  omega

theorem adjacent_pair_index {n : ℕ} {i j : Fin (n+2)}
    (hij : (graph n).Adj (vertex i) (vertex j)) :
    ∃ k : Fin (n+1),({vertex i,vertex j} : Finset (Vertex n))=
      {vertex k.castSucc,vertex k.succ} := by
  rcases (graph_vertices i j).mp hij with h | h
  · let k : Fin (n+1) := ⟨i.val,by omega⟩
    have hi : k.castSucc=i := Fin.ext rfl
    have hj : k.succ=j := Fin.ext h
    exact ⟨k,by rw [hi,hj]⟩
  · let k : Fin (n+1) := ⟨j.val,by omega⟩
    have hj : k.castSucc=j := Fin.ext rfl
    have hi : k.succ=i := Fin.ext h
    exact ⟨k,by rw [hi,hj]; exact pair_comm _ _⟩

theorem clique_covers {n : ℕ} (C : Finset (Vertex n))
    (hC : IsCliqueCoordinate (graph n) C) : ∃ i : Slot n,clique i=C := by
  have hcard := hC.1
  have hcl := hC.2
  have hp_le := privatePart_card_le_two hcl
  by_cases h0 : (privatePart C).card=0
  · have hp0 : privatePart C=∅ := card_eq_zero.mp h0
    have hsub : C⊆{hubA n,hubB n} := by
      intro v hv
      rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
      · simp
      · simp
      · have hm : vertex i∈privatePart C := (vertex_mem_privatePart C i).mpr hv
        rw [hp0] at hm
        exact (notMem_empty _ hm).elim
    have he : C={hubA n,hubB n} := eq_of_subset_of_card_le hsub (by simpa using hcard)
    exact ⟨.inl (),he.symm⟩
  by_cases h1 : (privatePart C).card=1
  · obtain ⟨v,hp⟩ := card_eq_one.mp h1
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hv
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inl (2,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (0,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (1,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · have he : C={vertex i} := eq_of_privatePart (by simpa [privatePart] using hp)
        (by simp [ha]) (by simp [hb])
      rw [he,card_singleton] at hcard
      omega
  · have h2 : (privatePart C).card=2 := by omega
    obtain ⟨u,v,huv,hp⟩ := card_eq_two.mp h2
    have hu : u∈privatePart C := by rw [hp]; simp
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hu
    obtain ⟨j,rfl⟩ := privatePart_vertex hv
    have hadj := hcl (privatePart_subset C hu) (privatePart_subset C hv) huv
    obtain ⟨k,hk⟩ := adjacent_pair_index hadj
    rw [hk] at hp
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inr (3,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (1,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (2,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (0,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]

theorem graphical_coordinates {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (hG : Graphical (graph n) f) :
    f=FiniteMonomial.polynomial clique (fun i => mobius f (clique i)) :=
  FiniteMonomial.graphical_eq_polynomial clique clique_injective clique_covers hn hG

end GraphicalZonotopes.PathJoin
