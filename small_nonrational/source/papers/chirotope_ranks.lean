module
public import Papers.ChirotopeDensity
public import Papers.RationalityTenRestrictedColumns
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

noncomputable section

open Matrix Set Module

namespace Papers.RationalityTen.ChirotopeDensity

/-- Extend any independent subconfiguration to a full labelled basis.
The finite index set has exactly the actual ambient rank. -/
theorem exists_indexed_basis_extension {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p) {S : Set (Fin n)}
    (hS : LinearIndepOn ℝ p S) :
    ∃ b : Fin r → Fin n, Function.Injective b ∧
      LinearIndependent ℝ (p ∘ b) ∧ S ⊆ Set.range b := by
  classical
  let T := hS.extend (Set.subset_univ S)
  have hT : LinearIndepOn ℝ p T := hS.linearIndepOn_extend _
  have hST : S ⊆ T := hS.subset_extend _
  have hspan : Submodule.span ℝ (Set.range (fun i : T => p i)) = ⊤ := by
    rw [range_restricted_family]
    change Submodule.span ℝ (p '' hS.extend (Set.subset_univ S)) = ⊤
    rw [hS.span_image_extend_eq_span_image,Set.image_univ]
    exact hp
  let B : Basis T ℝ (Fin r → ℝ) := Basis.mk hT (by rw [hspan])
  have hcard : Fintype.card T = r := by
    have h := Module.finrank_eq_card_basis B
    simpa [Module.finrank_fintype_fun_eq_card] using h.symm
  let e : Fin r ≃ T := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let b : Fin r → Fin n := fun i => (e i).1
  refine ⟨b,Subtype.val_injective.comp e.injective,?_,?_⟩
  · exact hT.comp e e.injective
  · intro i hi
    refine ⟨e.symm ⟨i,hST hi⟩,?_⟩
    simp [b]

theorem SameChirotope.zero_iff {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (h : SameChirotope p q) (b : Fin r → Fin n) :
    minor p b = 0 ↔ minor q b = 0 := by
  constructor
  · intro hp
    apply sign_eq_zero_iff.mp
    exact (h b).trans (sign_eq_zero_iff.mpr hp)
  · intro hq
    apply sign_eq_zero_iff.mp
    exact (h b).symm.trans (sign_eq_zero_iff.mpr hq)

theorem nonzero_minor_iff_independent {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (b : Fin r → Fin n) :
    minor p b ≠ 0 ↔ LinearIndependent ℝ (p ∘ b) := by
  change (Matrix.of (fun i j => p (b i) j)).det ≠ 0 ↔
    LinearIndependent ℝ (fun i => p (b i))
  rw [← isUnit_iff_ne_zero,← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_row_iff_isUnit]
  rfl

theorem independent_of_zero_minor_pattern {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (hp : Spans p)
    (hzero : ∀ b, minor p b = 0 ↔ minor q b = 0)
    {S : Set (Fin n)} (hS : LinearIndepOn ℝ p S) :
    LinearIndepOn ℝ q S := by
  classical
  obtain ⟨b,hb,hpb,hSb⟩ := exists_indexed_basis_extension p hp hS
  have hpnz := (nonzero_minor_iff_independent p b).mpr hpb
  have hqnz : minor q b ≠ 0 := fun h => hpnz ((hzero b).mpr h)
  have hqb := (nonzero_minor_iff_independent q b).mp hqnz
  have hqrange : LinearIndepOn ℝ q (Set.range b) := by
    let e : Fin r ≃ Set.range b := Equiv.ofInjective b hb
    have he : ∀ i, (e i).1 = b i := fun _ => rfl
    have h' := hqb.comp e.symm e.symm.injective
    change LinearIndependent ℝ (fun i : Set.range b => q i.val)
    have heq : (fun i : Set.range b => q i.val) = (q ∘ b) ∘ e.symm := by
      funext i
      exact congrArg q (congrArg Subtype.val (e.apply_symm_apply i)).symm
    rw [heq]
    exact h'
  exact hqrange.mono hSb

theorem spans_of_zero_minor_pattern {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (hp : Spans p)
    (hzero : ∀ b, minor p b = 0 ↔ minor q b = 0) : Spans q := by
  classical
  have hempty : LinearIndepOn ℝ p (∅ : Set (Fin n)) := by simp
  obtain ⟨b,hb,hpb,_⟩ := exists_indexed_basis_extension p hp hempty
  have hpnz := (nonzero_minor_iff_independent p b).mpr hpb
  have hqnz : minor q b ≠ 0 := fun h => hpnz ((hzero b).mpr h)
  have hqb := (nonzero_minor_iff_independent q b).mp hqnz
  have hspan : Submodule.span ℝ (Set.range (q ∘ b)) = ⊤ :=
    hqb.span_eq_top_of_card_eq_finrank' (by simp)
  apply top_unique
  rw [← hspan]
  exact Submodule.span_mono (Set.range_comp_subset_range _ _)

theorem SameChirotope.independent_iff {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (h : SameChirotope p q) (hp : Spans p)
    (S : Set (Fin n)) :
    LinearIndepOn ℝ p S ↔ LinearIndepOn ℝ q S := by
  have hz := h.zero_iff
  have hq := spans_of_zero_minor_pattern hp hz
  exact ⟨independent_of_zero_minor_pattern hp hz,
    independent_of_zero_minor_pattern hq (fun b => (hz b).symm)⟩

theorem finrank_span_image_le_of_independence_imp
    {n r s : ℕ} (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (h : ∀ T : Set (Fin n), LinearIndepOn ℝ p T → LinearIndepOn ℝ q T)
    (S : Set (Fin n)) :
    finrank ℝ (Submodule.span ℝ (p '' S)) ≤
      finrank ℝ (Submodule.span ℝ (q '' S)) := by
  classical
  have hempty : LinearIndepOn ℝ p (∅ : Set (Fin n)) := by simp
  let T := hempty.extend (Set.empty_subset S)
  have hT : LinearIndepOn ℝ p T := hempty.linearIndepOn_extend _
  have hTS : T ⊆ S := hempty.extend_subset _
  have hqT : LinearIndepOn ℝ q T := h T hT
  have hspan : Submodule.span ℝ (p '' T) = Submodule.span ℝ (p '' S) :=
    hempty.span_image_extend_eq_span_image _
  have hpdim : Fintype.card T = finrank ℝ (Submodule.span ℝ (p '' T)) := by
    have hh := linearIndependent_iff_card_eq_finrank_span.mp hT
    change Fintype.card T = finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : T => p i.val))) at hh
    rw [range_restricted_family] at hh
    exact hh
  have hqdim : Fintype.card T = finrank ℝ (Submodule.span ℝ (q '' T)) := by
    have hh := linearIndependent_iff_card_eq_finrank_span.mp hqT
    change Fintype.card T = finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : T => q i.val))) at hh
    rw [range_restricted_family] at hh
    exact hh
  calc
    finrank ℝ (Submodule.span ℝ (p '' S)) = Fintype.card T := by rw [← hspan,← hpdim]
    _ = finrank ℝ (Submodule.span ℝ (q '' T)) := hqdim
    _ ≤ finrank ℝ (Submodule.span ℝ (q '' S)) :=
      Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hTS))

/-- Maximal-minor signs preserve the ranks of every labelled subset,
which is the precise rank information needed in the relation-space argument. -/
theorem SameChirotope.subset_rank_eq {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (h : SameChirotope p q) (hp : Spans p)
    (S : Set (Fin n)) :
    finrank ℝ (Submodule.span ℝ (p '' S)) =
      finrank ℝ (Submodule.span ℝ (q '' S)) := by
  apply Nat.le_antisymm
  · exact finrank_span_image_le_of_independence_imp p q
      (fun T => (h.independent_iff hp T).mp) S
  · exact finrank_span_image_le_of_independence_imp q p
      (fun T => (h.independent_iff hp T).mpr) S

end Papers.RationalityTen.ChirotopeDensity
