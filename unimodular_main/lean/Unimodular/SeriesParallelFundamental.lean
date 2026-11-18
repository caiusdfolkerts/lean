module

public import Unimodular.SeriesParallelCycles
public import Unimodular.SeriesParallelGraphs

@[expose] public section

open scoped BigOperators
open Set TauCeti.Toric SimpleGraph

namespace Unimodular.SeriesParallel

noncomputable section

universe u v w z

/-- The ordinary bipartite fundamental graph of a matrix. The row and column
labels are disjoint even when their original indexing types coincide. -/
def supportGraph {I J : Type*} (A : I → J → ℤ) : SimpleGraph (I ⊕ J) where
  Adj
    | .inl i, .inr j => A i j ≠ 0
    | .inr j, .inl i => A i j ≠ 0
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

@[simp] theorem supportGraph_left_right {I J : Type*} (A : I → J → ℤ) (i : I) (j : J) :
    (supportGraph A).Adj (.inl i) (.inr j) ↔ A i j ≠ 0 := Iff.rfl

@[simp] theorem supportGraph_right_left {I J : Type*} (A : I → J → ℤ) (i : I) (j : J) :
    (supportGraph A).Adj (.inr j) (.inl i) ↔ A i j ≠ 0 := Iff.rfl

@[simp] theorem supportGraph_left_left {I J : Type*} (A : I → J → ℤ) (i i' : I) :
    ¬(supportGraph A).Adj (.inl i) (.inl i') := id

@[simp] theorem supportGraph_right_right {I J : Type*} (A : I → J → ℤ) (j j' : J) :
    ¬(supportGraph A).Adj (.inr j) (.inr j') := id

/-- The genuine two-coloring of the fundamental graph. -/
def supportColor {I J : Type*} (A : I → J → ℤ) : (supportGraph A).Coloring Bool :=
  Coloring.mk (fun x => match x with | .inl _ => false | .inr _ => true)
    (by intro x y h; cases x <;> cases y <;> simp_all [supportGraph])

private theorem adj_swap {I J : Type*} (A : I → J → ℤ) (x y : I ⊕ J) :
    (supportGraph (fun j i => A i j)).Adj x.swap y.swap ↔
      (supportGraph A).Adj x y := by
  cases x <;> cases y <;> rfl

private def swapPath {I J : Type*} (A : I → J → ℤ)
    (p : InducedPath (supportGraph A)) :
    InducedPath (supportGraph (fun j i => A i j)) where
  length := p.length
  vertex := fun i => (p.vertex i).swap
  injective := (Equiv.sumComm I J).injective.comp p.injective
  adjacent := fun i j => (adj_swap A _ _).trans (p.adjacent i j)

private def swapDomino {I J : Type*} (A : I → J → ℤ)
    (d : InducedDomino (supportGraph A)) :
    InducedDomino (supportGraph (fun j i => A i j)) where
  left := fun i => (d.left i).swap
  right := fun i => (d.right i).swap
  left_injective := (Equiv.sumComm I J).injective.comp d.left_injective
  right_injective := (Equiv.sumComm I J).injective.comp d.right_injective
  disjoint := fun i j h => d.disjoint i j ((Equiv.sumComm I J).injective h)
  left_nonadjacent := fun i j h => d.left_nonadjacent i j ((adj_swap A _ _).mp h)
  right_nonadjacent := fun i j h => d.right_nonadjacent i j ((adj_swap A _ _).mp h)
  cross := fun i j => (adj_swap A _ _).trans (d.cross i j)

private theorem domino_pattern_of_left {I J : Type*} (A : I → J → ℤ)
    (d : InducedDomino (supportGraph A)) (a : I) (ha : d.left 1 = .inl a) :
    ∃ (r : Fin 3 ↪ I) (c : Fin 3 ↪ J),
      ∀ i j, A (r i) (c j) ≠ 0 ↔ dominoCross i j := by
  have hright : ∀ j, ∃ c : J, d.right j = .inr c := by
    intro j
    have hadj := (d.cross 1 j).mpr (by simp [dominoCross])
    rw [ha] at hadj
    cases h : d.right j with
    | inl b => simp [h] at hadj
    | inr b => exact ⟨b, rfl⟩
  choose c hc using hright
  have hleft : ∀ i, ∃ r : I, d.left i = .inl r := by
    intro i
    have hadj := (d.cross i 1).mpr (by simp [dominoCross])
    rw [hc 1] at hadj
    cases h : d.left i with
    | inl b => exact ⟨b, rfl⟩
    | inr b => simp [h] at hadj
  choose r hr using hleft
  refine ⟨⟨r, ?_⟩, ⟨c, ?_⟩, ?_⟩
  · intro i j h
    apply d.left_injective
    rw [hr i, hr j, h]
  · intro i j h
    apply d.right_injective
    rw [hc i, hc j, h]
  · intro i j
    change A (r i) (c j) ≠ 0 ↔ dominoCross i j
    simpa only [hr i, hc j, supportGraph_left_right] using d.cross i j

/-- An induced domino in the fundamental graph is exactly an induced domino
submatrix, up to interchanging its two color classes. The latter interchange
is harmless because the domino matrix is symmetric. -/
theorem supportGraph_domino_pattern {I J : Type*} (A : I → J → ℤ)
    (d : InducedDomino (supportGraph A)) :
    ∃ (r : Fin 3 ↪ I) (c : Fin 3 ↪ J),
      ∀ i j, A (r i) (c j) ≠ 0 ↔ dominoCross i j := by
  cases h : d.left 1 with
  | inl a => exact domino_pattern_of_left A d a h
  | inr a =>
    obtain ⟨c, r, hp⟩ := domino_pattern_of_left (fun j i => A i j)
      (swapDomino A d) a (by simp [swapDomino, h])
    refine ⟨r, c, fun i j => (hp j i).trans ?_⟩
    fin_cases i <;> fin_cases j <;> simp [dominoCross]

private theorem path_left_parity {I J : Type*} (A : I → J → ℤ)
    (p : InducedPath (supportGraph A)) (hzero : ∃ a, p.vertex 0 = .inl a) :
    ∀ n (hn : n < p.length + 1),
      (∃ a, p.vertex ⟨n, hn⟩ = .inl a) ↔ n % 2 = 0 := by
  intro n
  induction n with
  | zero => intro hn; simpa using hzero
  | succ n ih =>
    intro hn
    have hn' : n < p.length + 1 := by omega
    have hadj := (p.adjacent ⟨n, hn'⟩ ⟨n + 1, hn⟩).mpr (Or.inl rfl)
    have hp := ih hn'
    cases hx : p.vertex ⟨n, hn'⟩ with
    | inl a =>
      have heven : n % 2 = 0 := hp.mp ⟨a, hx⟩
      cases hy : p.vertex ⟨n + 1, hn⟩ with
      | inl b => simp [hx, hy] at hadj
      | inr b =>
        have hnext : (n + 1) % 2 ≠ 0 := by omega
        simp [hy, hnext]
    | inr a =>
      have hodd : n % 2 ≠ 0 := by
        intro heven
        obtain ⟨b, hb⟩ := hp.mpr heven
        simp [hx] at hb
      cases hy : p.vertex ⟨n + 1, hn⟩ with
      | inl b =>
        have hnext : (n + 1) % 2 = 0 := by omega
        simp [hy, hnext]
      | inr b => simp [hx, hy] at hadj

/-- Reading an induced bipartite cycle from one of its column vertices gives
an exact cyclic support matrix. The cycle length is arbitrary. -/
private theorem cycle_pattern_of_right {I J : Type*} (A : I → J → ℤ)
    (p : InducedPath (supportGraph A)) (hp : 4 ≤ p.length) (z : J)
    (hz : ∀ i, Sum.inr z ≠ p.vertex i)
    (hadj : ∀ i, (supportGraph A).Adj (.inr z) (p.vertex i) ↔
      i.val = 0 ∨ i.val = p.length) :
    ∃ (k : ℕ), 3 ≤ k ∧ ∃ (r : Fin k ↪ I) (c : Fin k ↪ J),
      ∀ i j, A (r i) (c j) ≠ 0 ↔ cycleSupport i j := by
  have hzero : ∃ a, p.vertex 0 = .inl a := by
    have h := (hadj 0).mpr (Or.inl rfl)
    cases h0 : p.vertex 0 with
    | inl a => exact ⟨a, rfl⟩
    | inr b => simp [h0] at h
  have hlast : ∃ a, p.vertex (Fin.last p.length) = .inl a := by
    have h := (hadj (Fin.last p.length)).mpr (Or.inr rfl)
    cases h0 : p.vertex (Fin.last p.length) with
    | inl a => exact ⟨a, rfl⟩
    | inr b => simp [h0] at h
  have heven : p.length % 2 = 0 :=
    (path_left_parity A p hzero p.length (Nat.lt_succ_self _)).mp hlast
  let t := p.length / 2
  have ht : p.length = 2 * t := by dsimp [t]; omega
  have htpos : 2 ≤ t := by omega
  let evenIndex (i : Fin (t + 1)) : Fin (p.length + 1) := ⟨2 * i.val, by omega⟩
  let oddIndex (i : Fin t) : Fin (p.length + 1) := ⟨2 * i.val + 1, by omega⟩
  have hrows : ∀ i : Fin (t + 1), ∃ a, p.vertex (evenIndex i) = .inl a := by
    intro i
    apply (path_left_parity A p hzero _ _).mpr
    omega
  have hcols : ∀ j : Fin t, ∃ a, p.vertex (oddIndex j) = .inr a := by
    intro j
    cases h : p.vertex (oddIndex j) with
    | inl a =>
      have he := (path_left_parity A p hzero _ _).mp ⟨a, h⟩
      omega
    | inr a => exact ⟨a, rfl⟩
  choose r hr using hrows
  choose c hc using hcols
  let cc : Fin (t + 1) → J := Fin.lastCases z c
  have hrinj : Function.Injective r := by
    intro i j h
    have hv : p.vertex (evenIndex i) = p.vertex (evenIndex j) := by rw [hr, hr, h]
    have hi := congrArg Fin.val (p.injective hv)
    apply Fin.ext
    dsimp [evenIndex] at hi
    omega
  have hcinj : Function.Injective cc := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => intro _; rfl
      | cast j =>
        intro he
        have he' : z = c j := by simpa [cc] using he
        exact False.elim (hz (oddIndex j) (by rw [hc j, he']))
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        intro he
        have he' : c i = z := by simpa [cc] using he
        exact False.elim (hz (oddIndex i) (by rw [hc i, he']))
      | cast j =>
        intro he
        have he' : c i = c j := by simpa [cc] using he
        have hv : p.vertex (oddIndex i) = p.vertex (oddIndex j) := by rw [hc, hc, he']
        have hi := congrArg Fin.val (p.injective hv)
        apply Fin.ext
        dsimp [oddIndex] at hi
        simp only [Fin.val_castSucc]
        omega
  refine ⟨t + 1, by omega, ⟨r, hrinj⟩, ⟨cc, hcinj⟩, ?_⟩
  intro i j
  induction j using Fin.lastCases with
  | last =>
    have h := hadj (evenIndex i)
    rw [hr i] at h
    change A (r i) z ≠ 0 ↔ _ at h
    change A (r i) (cc (Fin.last t)) ≠ 0 ↔ _
    simp only [cc, Fin.lastCases_last]
    have hnum : (2 * i.val = 0 ∨ 2 * i.val = p.length) ↔
        cycleSupport i (Fin.last t) := by
      simp only [cycleSupport, Fin.ext_iff, Fin.val_last]
      constructor
      · rintro (hi0 | hilast)
        · have hi : i.val = 0 := Nat.mul_left_cancel (by decide : 0 < 2)
            (by simpa using hi0)
          exact Or.inr (Or.inr ⟨hi, trivial⟩)
        · exact Or.inl (Nat.mul_left_cancel (by decide : 0 < 2) (hilast.trans ht))
      · rintro (hi | hi | ⟨hi, _⟩)
        · exact Or.inr (by rw [hi]; exact ht.symm)
        · exact ((Nat.ne_of_lt i.isLt) hi).elim
        · exact Or.inl (by rw [hi])
    exact h.trans hnum
  | cast j =>
    have h := p.adjacent (evenIndex i) (oddIndex j)
    rw [hr i, hc j] at h
    change A (r i) (c j) ≠ 0 ↔ _ at h
    change A (r i) (cc j.castSucc) ≠ 0 ↔ _
    simp only [cc, Fin.lastCases_castSucc]
    exact h.trans (by
      simp only [cycleSupport, Fin.ext_iff, Fin.val_castSucc]
      change (2 * i.val + 1 = 2 * j.val + 1 ∨ 2 * j.val + 1 + 1 = 2 * i.val) ↔ _
      omega)

/-- Reversing both index orders transposes a cyclic support matrix. -/
theorem cycleSupport_reverse_transpose {k : ℕ} (i j : Fin k) :
    cycleSupport j.rev i.rev ↔ cycleSupport i j := by
  simp only [cycleSupport, Fin.ext_iff, Fin.val_rev]
  omega

/-- Every actual induced long cycle in a fundamental graph gives an exact
cyclic square submatrix. No graph characterization theorem is assumed here. -/
theorem supportGraph_cycle_pattern {I J : Type*} (A : I → J → ℤ)
    (h : HasLongInducedCycle (supportGraph A)) :
    ∃ (k : ℕ), 3 ≤ k ∧ ∃ (r : Fin k ↪ I) (c : Fin k ↪ J),
      ∀ i j, A (r i) (c j) ≠ 0 ↔ cycleSupport i j := by
  obtain ⟨p, hp, z, hz, hadj⟩ := h
  cases z with
  | inr z => exact cycle_pattern_of_right A p hp z hz hadj
  | inl z =>
    have hz' : ∀ i, Sum.inr z ≠ (swapPath A p).vertex i := by
      intro i h
      exact hz i ((Equiv.sumComm I J).injective h)
    have ha' : ∀ i, (supportGraph (fun j i => A i j)).Adj (.inr z)
        ((swapPath A p).vertex i) ↔ i.val = 0 ∨ i.val = p.length := by
      intro i
      exact (adj_swap A (.inl z) (p.vertex i)).trans (hadj i)
    obtain ⟨k, hk, c, r, hpat⟩ :=
      cycle_pattern_of_right (fun j i => A i j) (swapPath A p) hp z hz' ha'
    refine ⟨k, hk,
      ⟨fun i => r i.rev, fun _ _ h => Fin.rev_injective (r.injective h)⟩,
      ⟨fun i => c i.rev, fun _ _ h => Fin.rev_injective (c.injective h)⟩, ?_⟩
    intro i j
    exact (hpat j.rev i.rev).trans (cycleSupport_reverse_transpose i j)

/-- The actual fundamental graph of any ray family in a ray basis of a complete
regular positive-criterion fan has no induced long cycle and no induced domino.
All row sets, column sets, and original dimensions are unrestricted. -/
theorem fan_supportGraph_forbidden {I : Type u} {J : Type v} {N : Type w} {V : Type z}
    [Fintype I] [DecidableEq I] [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (hb : ∀ i, ConeBases.IsRay Φ (b i)) (U : J → N)
    (hU : ∀ j, ConeBases.IsRay Φ (U j)) :
    ¬HasLongInducedCycle (supportGraph (fun i j => b.repr (U j) i)) ∧
      ¬Nonempty (InducedDomino (supportGraph (fun i j => b.repr (U j) i))) := by
  constructor
  · intro h
    obtain ⟨k, hk, r, c, hpat⟩ := supportGraph_cycle_pattern _ h
    exact fan_no_cycle_rows Φ hc hr hp b hb k hk r (U ∘ c) (fun j => hU (c j)) hpat
  · rintro ⟨d⟩
    obtain ⟨r, c, hpat⟩ := supportGraph_domino_pattern _ d
    apply fan_no_domino_rows Φ hc hr hp b hb r (U (c 0)) (U (c 1)) (U (c 2))
      (hU _) (hU _) (hU _)
    · intro i
      have h := hpat i 0
      fin_cases i <;> simpa [dominoCross] using h
    · intro i
      exact (hpat i 1).mpr (by simp [dominoCross])
    · intro i
      have h := hpat i 2
      fin_cases i <;> simpa [dominoCross] using h

/-- The complete pruning certificate for the finite fundamental graph of a fan.
This is an unbounded consequence of geometric contraction and the proved finite
graph elimination theorem. -/
theorem fan_supportGraph_prunable {I : Type u} {J : Type v} {N : Type w} {V : Type z}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (hb : ∀ i, ConeBases.IsRay Φ (b i)) (U : J → N)
    (hU : ∀ j, ConeBases.IsRay Φ (U j)) :
    Prunable (supportGraph (fun i j => b.repr (U j) i)) Finset.univ := by
  obtain ⟨hcy, hdom⟩ := fan_supportGraph_forbidden Φ hc hr hp b hb U hU
  exact prunable_of_forbidden _ (supportColor _) hcy hdom Finset.univ

#print axioms Unimodular.SeriesParallel.fan_supportGraph_forbidden
#print axioms Unimodular.SeriesParallel.fan_supportGraph_prunable

end
end Unimodular.SeriesParallel
