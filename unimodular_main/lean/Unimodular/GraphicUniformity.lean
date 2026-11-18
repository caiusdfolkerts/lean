module

public import Unimodular.Extensions

@[expose] public section

noncomputable section

namespace Unimodular.Graphic

open scoped BigOperators

/-- A directed incidence column has at most one entry +1 and at most one entry -1.
Zero columns and columns with a deleted endpoint are included. -/
structure IncidenceColumn {I : Type*} (v : I → ℤ) : Prop where
  entries : ∀ i, v i = 0 ∨ v i = 1 ∨ v i = -1
  positive_unique : ∀ {i j}, v i = 1 → v j = 1 → i = j
  negative_unique : ∀ {i j}, v i = -1 → v j = -1 → i = j

namespace IncidenceColumn

variable {I J : Type*} {v : I → ℤ}

theorem comp (h : IncidenceColumn v) (f : J → I) (hf : Function.Injective f) :
    IncidenceColumn (v ∘ f) where
  entries j := h.entries (f j)
  positive_unique hi hj := hf (h.positive_unique hi hj)
  negative_unique hi hj := hf (h.negative_unique hi hj)

theorem eq_neg_of_ne (h : IncidenceColumn v) {i j : I} (hij : i ≠ j)
    (hi : v i ≠ 0) (hj : v j ≠ 0) : v i = -v j := by
  rcases h.entries i with hi0 | hi1 | him
  · exact (hi hi0).elim
  · rcases h.entries j with hj0 | hj1 | hjm
    · exact (hj hj0).elim
    · exact (hij (h.positive_unique hi1 hj1)).elim
    · simp [hi1, hjm]
  · rcases h.entries j with hj0 | hj1 | hjm
    · exact (hj hj0).elim
    · simp [him, hj1]
    · exact (hij (h.negative_unique him hjm)).elim

/-- A column either sums to zero or has exactly one nonzero entry. -/
theorem sum_zero_or_singleton [Fintype I] (h : IncidenceColumn v) :
    (∑ i, v i) = 0 ∨ ∃ i, v i ≠ 0 ∧ ∀ j, j ≠ i → v j = 0 := by
  classical
  by_cases hz : ∀ i, v i = 0
  · left; simp [hz]
  · push_neg at hz
    obtain ⟨i, hi⟩ := hz
    by_cases hs : ∀ j, j ≠ i → v j = 0
    · exact Or.inr ⟨i, hi, hs⟩
    · push_neg at hs
      obtain ⟨j, hji, hj⟩ := hs
      have hij : i ≠ j := Ne.symm hji
      have hop := h.eq_neg_of_ne hij hi hj
      have hrest : ∀ k, k ≠ i → k ≠ j → v k = 0 := by
        intro k hki hkj
        by_contra hk
        have hki' := h.eq_neg_of_ne hki hk hi
        have hkj' := h.eq_neg_of_ne hkj hk hj
        omega
      have he : v = Pi.single i (v i) + Pi.single j (v j) := by
        funext k
        by_cases hki : k = i
        · subst k; simp [Pi.single_apply, hij, hji]
        · by_cases hkj : k = j
          · subst k; simp [Pi.single_apply, hij, hji]
          · simp [Pi.single_apply, hki, hkj, eq_comm, hrest k hki hkj]
      left
      rw [he]
      simp [Finset.sum_add_distrib, hop]

end IncidenceColumn

/-- The determinant bound for arbitrary square directed incidence submatrices. The
proof is induction on the dimension, with no bound on rank or number of labels. -/
theorem determinant_abs_le_one : ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℤ,
    (∀ j, IncidenceColumn (fun i => A i j)) → |A.det| ≤ 1 := by
  intro n
  induction n with
  | zero => intro A hA; simp
  | succ n ih =>
    intro A hA
    classical
    by_cases hz : ∀ j, (∑ i, A i j) = 0
    · have hrows : (∑ i, (1 : ℤ) • A i) = 0 := by
        ext j
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply]
          using hz j
      have hd : A.det = 0 := by
        calc
          A.det = (A.updateRow 0 (∑ i, (1 : ℤ) • A i)).det := by
            simpa only [one_smul] using (Matrix.det_updateRow_sum A 0 (fun _ => 1)).symm
          _ = 0 := by
            rw [hrows]
            exact Matrix.det_eq_zero_of_row_eq_zero 0 (by simp)
      simp [hd]
    · push_neg at hz
      obtain ⟨j, hj⟩ := hz
      rcases (hA j).sum_zero_or_singleton with hj0 | ⟨i, hi, hsingle⟩
      · exact (hj hj0).elim
      · have habs : |A i j| = 1 := by
          rcases (hA j).entries i with h0 | h1 | hm
          · exact (hi h0).elim
          · simp [h1]
          · simp [hm]
        rw [Matrix.det_succ_column A j, Finset.sum_eq_single i]
        · simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, habs, one_mul]
          exact ih _ (fun k => (hA (j.succAbove k)).comp i.succAbove Fin.succAbove_right_injective)
        · intro k hk hki
          rw [hsingle k hki]
          simp
        · simp

/-- Every square submatrix of a directed incidence matrix has determinant 0 or ±1,
including matrices obtained by deleting a root row and retaining repeated edge labels. -/
theorem all_minors_abs_le_one {I J : Type*} (A : Matrix I J ℤ)
    (hA : ∀ j, IncidenceColumn (fun i => A i j)) {k : ℕ}
    (rows : Fin k → I) (hrows : Function.Injective rows) (columns : Fin k → J) :
    |(A.submatrix rows columns).det| ≤ 1 :=
  determinant_abs_le_one k _ (fun j => (hA (columns j)).comp rows hrows)

/-- The coordinate of a vertex in a rooted graphic representation; the root is `none`. -/
def endpoint {I : Type*} (p : Option I) (i : I) : ℤ := by
  classical
  exact if p = some i then 1 else 0

theorem endpoint_difference_column {I : Type*} (p q : Option I) :
    IncidenceColumn (fun i => endpoint p i - endpoint q i) where
  entries i := by
    classical
    unfold endpoint
    split_ifs <;> norm_num
  positive_unique := by
    classical
    intro i j hi hj
    have hpi : p = some i := by
      by_contra hpi
      simp only [endpoint, if_neg hpi] at hi
      split_ifs at hi <;> omega
    have hpj : p = some j := by
      by_contra hpj
      simp only [endpoint, if_neg hpj] at hj
      split_ifs at hj <;> omega
    exact Option.some.inj (hpi.symm.trans hpj)
  negative_unique := by
    classical
    intro i j hi hj
    have hqi : q = some i := by
      by_contra hqi
      simp only [endpoint, if_neg hqi] at hi
      split_ifs at hi <;> omega
    have hqj : q = some j := by
      by_contra hqj
      simp only [endpoint, if_neg hqj] at hj
      split_ifs at hj <;> omega
    exact Option.some.inj (hqi.symm.trans hqj)

section GraphicConfigurations

variable {n : ℕ} {M E : Type*} [AddCommGroup M] [Module ℤ M]

/-- Assign zero to the root vertex and the chosen lattice basis to all other vertices. -/
def vertex (b : Module.Basis (Fin n) ℤ M) : Option (Fin n) → M
  | none => 0
  | some i => b i

@[simp] theorem repr_vertex (b : Module.Basis (Fin n) ℤ M) (p : Option (Fin n)) (i : Fin n) :
    b.repr (vertex b p) i = endpoint p i := by
  classical
  cases p <;> simp [vertex, endpoint, Finsupp.single_apply, eq_comm]

/-- All directed incidence vectors, allowing arbitrary parallel labels, signs, and
loops, satisfy the full maximal-minor condition in the chosen integral basis. -/
theorem incidence_uniform (b : Module.Basis (Fin n) ℤ M)
    (source target : E → Option (Fin n)) :
    IntegralRigidity.Uniform b (fun e => vertex b (source e) - vertex b (target e)) := by
  intro a
  rw [Module.Basis.det_apply]
  apply determinant_abs_le_one
  intro j
  change IncidenceColumn (fun i =>
    b.repr (vertex b (source (a j)) - vertex b (target (a j))) i)
  simpa only [map_sub, Finsupp.sub_apply, repr_vertex] using
    endpoint_difference_column (source (a j)) (target (a j))

/-- A configuration represented by arbitrary rooted incidence endpoints is uniformly
unimodular, independent of the cardinality or repetition of its labels. -/
theorem uniform_of_incidence_representation (b : Module.Basis (Fin n) ℤ M)
    (u : E → M) (hu : ∀ e, ∃ p q, u e = vertex b p - vertex b q) :
    IntegralRigidity.Uniform b u := by
  classical
  choose p q hpq using hu
  rw [show u = (fun e => vertex b (p e) - vertex b (q e)) from funext hpq]
  exact incidence_uniform b p q

/-- The complete graphic root system ±bᵢ and bᵢ-bⱼ, together with optional zero
columns, is uniformly unimodular in every rank. -/
theorem signed_roots_uniform (b : Module.Basis (Fin n) ℤ M) (u : E → M)
    (hu : ∀ e, u e = 0 ∨ (∃ i, u e = b i) ∨ (∃ i, u e = -b i) ∨
      ∃ i j, u e = b i - b j) : IntegralRigidity.Uniform b u := by
  apply uniform_of_incidence_representation b u
  intro e
  rcases hu e with hz | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij⟩
  · exact ⟨none, none, by simpa [vertex] using hz⟩
  · exact ⟨some i, none, by simpa [vertex] using hi⟩
  · exact ⟨none, some i, by simpa [vertex] using hi⟩
  · exact ⟨some i, some j, hij⟩

end GraphicConfigurations

/-- The graphic determinant bound in the standard ambient lattice normalization. -/
theorem incidence_uniform_standard {n : ℕ} {E : Type*}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (source target : E → Option (Fin n)) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun e => vertex b (source e) - vertex b (target e)) := by
  intro a
  rw [← BasisCover.basis_determinant_abs b (Pi.basisFun ℤ (Fin n))]
  exact incidence_uniform b source target a

end Unimodular.Graphic

end
