import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
/-! # Augmented simplicial chains as genuine exterior-algebra chains

The empty face has chain degree zero. Thus chain degree `i` represents reduced simplicial
homology degree `i - 1`, including the empty-face class in degree zero. The differential is the
actual exterior contraction by the sum of the coordinates, with its usual signed face boundary.
-/

noncomputable section

namespace CommAlg.Simplicial

open CliffordAlgebra

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)

def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra

def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | K s ∧ s.card = i})

def Downward (K : Finset V → Prop) : Prop :=
  ∀ ⦃s t⦄, t ⊆ s → K s → K t

def deletion (K : Finset V → Prop) (e : V) (s : Finset V) : Prop := K s ∧ e ∉ s

def link (K : Finset V → Prop) (e : V) (s : Finset V) : Prop := K (insert e s) ∧ e ∉ s

lemma downward_deletion {K : Finset V → Prop} (hK : Downward K) (e : V) :
    Downward (deletion K e) := by
  intro s t hts hs
  exact ⟨hK hts hs.1, fun h => hs.2 (hts h)⟩

lemma downward_link {K : Finset V → Prop} (hK : Downward K) (e : V) :
    Downward (link K e) := by
  intro s t hts hs
  exact ⟨hK (Finset.insert_subset_insert e hts) hs.1, fun h => hs.2 (hts h)⟩

abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))

abbrev contraction (e : V) : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k))) ((Pi.basisFun k V).coord e)

abbrev creation (e : V) : Ambient V k →ₗ[k] Ambient V k :=
  LinearMap.mulLeft k (ExteriorAlgebra.ι k ((Pi.basisFun k V) e))

lemma boundary_boundary (z : Ambient V k) : boundary (boundary z) = 0 :=
  contractLeft_contractLeft _ z

lemma contraction_boundary (e : V) (z : Ambient V k) :
    contraction e (boundary z) = -boundary (contraction e z) :=
  contractLeft_comm _ _ z

lemma boundary_creation (e : V) (z : Ambient V k) :
    boundary (creation e z) = z - creation e (boundary z) := by
  rw [show creation e z = ExteriorAlgebra.ι k ((Pi.basisFun k V) e) * z from rfl,
    contractLeft_ι_mul]
  simp [Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma contraction_creation (e : V) (z : Ambient V k) :
    contraction e (creation e z) = z - creation e (contraction e z) := by
  rw [show creation e z = ExteriorAlgebra.ι k ((Pi.basisFun k V) e) * z from rfl,
    contractLeft_ι_mul]
  simp [Module.Basis.coord_apply]

lemma contraction_basis (e : V) (s : Finset V) :
    contraction (k := k) e (basis s) =
      if e ∈ s then TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (s.erase e) else 0 :=
  TauCeti.ExteriorAlgebra.contractLeft_coord_basis (Pi.basisFun k V) e s

lemma creation_basis (e : V) (s : Finset V) :
    creation (k := k) e (basis s) =
      if e ∈ s then 0 else
        TauCeti.ExteriorAlgebra.basisEraseSign e (insert e s) • basis (insert e s) :=
  TauCeti.ExteriorAlgebra.ι_mul_basis (Pi.basisFun k V) e s

lemma boundary_eq_sum (z : Ambient V k) :
    boundary z = ∑ e : V, contraction e z := by
  let φ := Fintype.linearCombination k (fun _ : V => (1 : k))
  change contractLeft φ z = _
  conv_lhs => rw [← (Pi.basisFun k V).sum_dual_apply_smul_coord φ]
  rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp [φ, Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma basis_mem {K : Finset V → Prop} {i : ℕ} {s : Finset V}
    (hK : K s) (hi : s.card = i) : basis (k := k) s ∈ Chains K i :=
  Submodule.subset_span ⟨s, ⟨hK, hi⟩, rfl⟩

lemma chains_mono {K L : Finset V → Prop} (h : ∀ s, K s → L s) (i : ℕ) :
    Chains (k := k) K i ≤ Chains L i :=
  Submodule.span_mono (Set.image_mono (fun s hs => ⟨h s hs.1, hs.2⟩))

lemma contraction_mem {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K (i + 1)) : contraction e z ∈ Chains (link K e) i := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [contraction_basis]
    split_ifs with he
    · apply Submodule.smul_mem
      apply basis_mem
      · exact ⟨by simpa [Finset.insert_erase he] using hs, Finset.notMem_erase _ _⟩
      · simpa [hcard] using Finset.card_erase_of_mem he
    · exact Submodule.zero_mem _
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) (link K e) i))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma contraction_zero_of_deletion {K : Finset V → Prop} (e : V) {i : ℕ}
    {z : Ambient V k} (hz : z ∈ Chains (deletion K e) i) : contraction e z = 0 := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, _⟩, rfl⟩ := ha
    simp [contraction_basis, hs.2]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha, ihb]
  | smul r a ha ih => simp [ih]

lemma link_le_deletion {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ) :
    Chains (k := k) (link K e) i ≤ Chains (deletion K e) i :=
  chains_mono (fun s hs => ⟨hK (Finset.subset_insert e s) hs.1, hs.2⟩) i

lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by
  rw [boundary_eq_sum]
  apply Submodule.sum_mem
  intro e he
  exact chains_mono (fun s hs => hs.1) i
    (link_le_deletion hK e i (contraction_mem e hz))

lemma boundary_zero_degree_zero {K : Finset V → Prop} {z : Ambient V k}
    (hz : z ∈ Chains K 0) : boundary z = 0 := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp hcard
    simp [boundary_eq_sum, contraction_basis]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha, ihb]
  | smul r a ha ih => simp [ih]

lemma creation_mem_link {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains (link K e) i) : creation e z ∈ Chains K (i + 1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [creation_basis, if_neg hs.2]
    apply Submodule.smul_mem
    exact basis_mem hs.1 (by simp [hs.2, hcard])
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i + 1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma delete_part_mem {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K i) : z - creation e (contraction e z) ∈ Chains (deletion K e) i := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    by_cases he : e ∈ s
    · have hprojection : creation (k := k) e (contraction e (basis s)) = basis s := by
        have h := TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis (Pi.basisFun k V) e s
        rw [if_pos he] at h
        exact h
      rw [hprojection, sub_self]
      exact Submodule.zero_mem _
    · rw [contraction_basis, if_neg he, map_zero, sub_zero]
      exact basis_mem ⟨hs, he⟩ hcard
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) (deletion K e) i))
  | add a b ha hb iha ihb =>
    simpa [mul_add, add_sub_add_comm] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa [smul_sub] using Submodule.smul_mem _ r ih

lemma mem_deletion_of_contraction_zero {K : Finset V → Prop} (e : V) {i : ℕ}
    {z : Ambient V k} (hz : z ∈ Chains K i) (he : contraction e z = 0) :
    z ∈ Chains (deletion K e) i := by
  simpa [he] using delete_part_mem e hz

end CommAlg.Simplicial
end
