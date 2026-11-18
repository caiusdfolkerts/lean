module

public import Unimodular.SeriesParallelAbstract

@[expose] public section

noncomputable section

open Set
open scoped Matroid

namespace Unimodular.SeriesParallel

attribute [local instance] Classical.propDecidable

namespace FiniteRelabel

variable {α β γ δ : Type*}

/-- Relabel a matroid by a bijection from the new labels to its old labels. -/
def pull (M : Matroid α) (e : β ≃ α) : Matroid β := M.mapEquiv e.symm

@[simp] theorem pull_ground (M : Matroid α) (e : β ≃ α) :
    (pull M e).E = e ⁻¹' M.E := by
  rw [pull, Matroid.mapEquiv_ground_eq, Equiv.image_eq_preimage_symm, Equiv.symm_symm]

@[simp] theorem pull_indep (M : Matroid α) (e : β ≃ α) (I : Set β) :
    (pull M e).Indep I ↔ M.Indep (e '' I) := by
  simp only [pull, Matroid.mapEquiv_indep_iff, Equiv.symm_symm]

@[simp] theorem pull_dep (M : Matroid α) (e : β ≃ α) (I : Set β) :
    (pull M e).Dep I ↔ M.Dep (e '' I) := by
  simp only [pull, Matroid.mapEquiv_dep_iff, Equiv.symm_symm]

@[simp] theorem pull_dual (M : Matroid α) (e : β ≃ α) :
    pull M✶ e = (pull M e)✶ := by
  simp only [pull, Matroid.mapEquiv, Matroid.mapEmbedding, Matroid.map_dual]

@[simp] theorem pull_comp (M : Matroid α) (e : β ≃ α) (f : γ ≃ β) :
    pull (pull M e) f = pull M (f.trans e) := by
  apply Matroid.ext_indep
  · ext x
    simp only [pull_ground, Set.mem_preimage, Equiv.trans_apply]
  · intro I hI
    simp only [pull_indep, Set.image_image, Equiv.trans_apply] <;> rfl

@[simp] theorem pull_id (M : Matroid α) : pull M (Equiv.refl α) = M := by
  apply Matroid.ext_indep
  · simp [pull_ground]
  · intro I hI
    simp [pull_indep]

@[simp] theorem pull_symm_cancel (M : Matroid α) (e : β ≃ α) :
    pull (pull M e) e.symm = M := by
  rw [pull_comp]
  simpa using pull_id M

@[simp] theorem pull_mapped (M : Matroid α) (f : α ≃ β) (e : γ ≃ α) :
    pull (M.mapEquiv f) (e.trans f) = pull M e := by
  apply Matroid.ext_indep
  · ext x
    simp only [pull_ground, Matroid.mapEquiv_ground_eq, Set.mem_preimage,
      Equiv.trans_apply, Set.mem_image_equiv, Equiv.symm_apply_apply]
  · intro I hI
    simp only [pull_indep, Matroid.mapEquiv_indep_iff, Set.image_image,
      Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp] theorem pull_isLoop (M : Matroid α) (e : β ≃ α) (x : β) :
    (pull M e).IsLoop x ↔ M.IsLoop (e x) := by
  rw [← Matroid.singleton_dep, ← Matroid.singleton_dep, pull_dep]
  simp only [Set.image_singleton]

@[simp] theorem pull_isNonloop (M : Matroid α) (e : β ≃ α) (x : β) :
    (pull M e).IsNonloop x ↔ M.IsNonloop (e x) := by
  rw [← Matroid.indep_singleton, ← Matroid.indep_singleton, pull_indep]
  simp

@[simp] theorem pull_isColoop (M : Matroid α) (e : β ≃ α) (x : β) :
    (pull M e).IsColoop x ↔ M.IsColoop (e x) := by
  change (pull M e)✶.IsLoop x ↔ M✶.IsLoop (e x)
  rw [← pull_dual, pull_isLoop]

@[simp] theorem pull_isCircuit (M : Matroid α) (e : β ≃ α) (C : Set β) :
    (pull M e).IsCircuit C ↔ M.IsCircuit (e '' C) := by
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep,
    Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep, pull_dep]
  apply and_congr_right
  intro hC
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hi := (pull_indep M e _).1 (h y hy)
    simpa only [Set.image_sdiff e.injective, Set.image_singleton] using hi
  · intro h y hy
    apply (pull_indep M e _).2
    have hi := h (e y) ⟨y, hy, rfl⟩
    simpa only [Set.image_sdiff e.injective, Set.image_singleton] using hi

@[simp] theorem pull_isCocircuit (M : Matroid α) (e : β ≃ α) (C : Set β) :
    (pull M e).IsCocircuit C ↔ M.IsCocircuit (e '' C) := by
  rw [Matroid.isCocircuit_def, ← pull_dual, pull_isCircuit, Matroid.isCocircuit_def]

theorem pull_delete (M : Matroid α) (e : β ≃ α) (D : Set α) :
    pull (M ＼ D) e = (pull M e) ＼ (e.symm '' D) := by
  apply Matroid.ext_indep
  · rw [pull_ground, Matroid.delete_ground, Matroid.delete_ground, pull_ground,
      Set.preimage_sdiff, Equiv.image_eq_preimage_symm, Equiv.symm_symm]
  · intro I hI
    rw [pull_indep, Matroid.delete_indep_iff, Matroid.delete_indep_iff, pull_indep]
    apply and_congr_right
    intro hi
    rw [Equiv.image_symm_eq_preimage, Set.disjoint_left, Set.disjoint_left]
    constructor
    · intro hd x hx hxD
      exact hd ⟨x, hx, rfl⟩ hxD
    · rintro hd x ⟨y, hy, rfl⟩ hxD
      exact hd hy hxD

theorem pull_contract (M : Matroid α) (e : β ≃ α) (C : Set α) :
    pull (M ／ C) e = (pull M e) ／ (e.symm '' C) := by
  calc
    pull (M ／ C) e = pull ((M✶ ＼ C)✶) e := rfl
    _ = (pull (M✶ ＼ C) e)✶ := pull_dual _ _
    _ = ((pull M e)✶ ＼ (e.symm '' C))✶ := by rw [pull_delete, pull_dual]
    _ = (pull M e) ／ (e.symm '' C) := rfl

/-- Relabeling a commutative square of embeddings gives literal equality of the
resulting matroids. This allows varying finite label types during deletion induction. -/
theorem pull_embedding_square (M : Matroid β) (f : β ↪ α)
    (e : γ ≃ β) (g : δ ≃ α) (h : γ ↪ δ)
    (hcomm : ∀ x, g (h x) = f (e x)) :
    pull (M.mapEmbedding f) g = (pull M e).mapEmbedding h := by
  have hpre (I : Set δ) : f ⁻¹' (g '' I) = e '' (h ⁻¹' I) := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨e.symm x, ?_, by simp⟩
      have hh : h (e.symm x) = y := g.injective (by
        rw [hcomm, e.apply_symm_apply]
        exact heq.symm)
      change h (e.symm x) ∈ I
      simpa only [hh] using hy
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, hy, hcomm y⟩
  have hrange (I : Set δ) : g '' I ⊆ Set.range f ↔ I ⊆ Set.range h := by
    constructor
    · intro hs x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx, rfl⟩
      refine ⟨e.symm y, g.injective ?_⟩
      rw [hcomm, e.apply_symm_apply, hy]
    · rintro hs x ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := hs hy
      exact ⟨e z, (hcomm z).symm⟩
  apply Matroid.ext_indep
  · rw [pull_ground, Matroid.mapEmbedding_ground_eq,
      Matroid.mapEmbedding_ground_eq, pull_ground]
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨e.symm y, by simpa using hy, g.injective ?_⟩
      rw [hcomm, e.apply_symm_apply, heq]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, hy, (hcomm y).symm⟩
  · intro I hI
    rw [pull_indep, Matroid.mapEmbedding_indep_iff,
      Matroid.mapEmbedding_indep_iff, pull_indep, hpre]
    exact and_congr Iff.rfl (hrange I)

/-- Extend any enumeration of the old labels by placing the new label first. -/
def extendEquiv {m : ℕ} (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (e : Fin m ≃ β) : Fin (m + 1) ≃ α :=
  Equiv.ofBijective (Fin.cons new (fun j => f (e j))) ⟨by
    apply Fin.cons_injective_of_injective
    · rintro ⟨j, hj⟩
      have hn : f (e j) ≠ new := by
        have hm : f (e j) ∈ Set.range f := ⟨e j, rfl⟩
        rw [hrange] at hm
        exact hm
      exact hn hj
    · exact f.injective.comp e.injective,
    by
      intro x
      by_cases hx : x = new
      · exact ⟨0, by simp [hx]⟩
      · have hm : x ∈ Set.range f := by rw [hrange]; exact hx
        obtain ⟨y, rfl⟩ := hm
        exact ⟨(e.symm y).succ, by simp⟩⟩

@[simp] theorem extendEquiv_zero {m : ℕ} (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (e : Fin m ≃ β) :
    extendEquiv f new hrange e 0 = new := rfl

@[simp] theorem extendEquiv_succ {m : ℕ} (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (e : Fin m ≃ β) (j : Fin m) :
    extendEquiv f new hrange e j.succ = f (e j) := rfl

@[simp] theorem extendEquiv_symm_new {m : ℕ} (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (e : Fin m ≃ β) :
    (extendEquiv f new hrange e).symm new = 0 := by
  apply (extendEquiv f new hrange e).injective
  simp

theorem normalized_delete {m : ℕ} {M : Matroid β} {N : Matroid α}
    (f : β ↪ α) (new : α) (hrange : Set.range f = ({new} : Set α)ᶜ)
    (e : Fin m ≃ β) (hdel : N ＼ ({new} : Set α) = M.mapEmbedding f) :
    (pull N (extendEquiv f new hrange e)) ＼ ({0} : Set _) =
      (pull M e).mapEmbedding (oldLabels m) := by
  have hh := congrArg (fun L => pull L (extendEquiv f new hrange e)) hdel
  rw [pull_delete] at hh
  simpa only [Set.image_singleton, extendEquiv_symm_new,
    pull_embedding_square M f e (extendEquiv f new hrange e) (oldLabels m)
      (fun j => rfl)] using hh

theorem normalized_contract {m : ℕ} {M : Matroid β} {N : Matroid α}
    (f : β ↪ α) (new : α) (hrange : Set.range f = ({new} : Set α)ᶜ)
    (e : Fin m ≃ β) (hcon : N ／ ({new} : Set α) = M.mapEmbedding f) :
    (pull N (extendEquiv f new hrange e)) ／ ({0} : Set _) =
      (pull M e).mapEmbedding (oldLabels m) := by
  have hh := congrArg (fun L => pull L (extendEquiv f new hrange e)) hcon
  rw [pull_contract] at hh
  simpa only [Set.image_singleton, extendEquiv_symm_new,
    pull_embedding_square M f e (extendEquiv f new hrange e) (oldLabels m)
      (fun j => rfl)] using hh

end FiniteRelabel

/-- A label-independent version of the standard finite abstract construction class.
The equivalence covers the actual element type and thus retains every label. -/
def FiniteSeriesParallel {α : Type*} (M : Matroid α) : Prop :=
  ∃ m : ℕ, ∃ e : Fin m ≃ α, HasSeriesParallelConstruction (M.mapEquiv e.symm)

namespace FiniteSeriesParallel

open FiniteRelabel

variable {α β : Type*} {M : Matroid β} {N : Matroid α}

theorem relabel (hM : FiniteSeriesParallel M) (k : β ≃ α) :
    FiniteSeriesParallel (M.mapEquiv k) := by
  obtain ⟨m, e, h⟩ := hM
  refine ⟨m, e.trans k, ?_⟩
  change HasSeriesParallelConstruction (pull (M.mapEquiv k) (e.trans k))
  rw [pull_mapped]
  exact h

theorem addLoop (hM : FiniteSeriesParallel M) (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (hground : N.E = Set.univ)
    (hloop : N.IsLoop new)
    (hdel : N ＼ ({new} : Set α) = M.mapEmbedding f) : FiniteSeriesParallel N := by
  obtain ⟨m, e, h⟩ := hM
  refine ⟨m + 1, extendEquiv f new hrange e, ?_⟩
  change HasSeriesParallelConstruction (pull N (extendEquiv f new hrange e))
  change HasSeriesParallelConstruction (pull M e) at h
  apply HasSeriesParallelConstruction.addLoop h
  · simp [pull_ground, hground]
  · simpa only [pull_isLoop, extendEquiv_zero] using hloop
  · exact normalized_delete f new hrange e hdel

theorem addColoop (hM : FiniteSeriesParallel M) (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (hground : N.E = Set.univ)
    (hcoloop : N.IsColoop new)
    (hdel : N ＼ ({new} : Set α) = M.mapEmbedding f) : FiniteSeriesParallel N := by
  obtain ⟨m, e, h⟩ := hM
  refine ⟨m + 1, extendEquiv f new hrange e, ?_⟩
  change HasSeriesParallelConstruction (pull N (extendEquiv f new hrange e))
  change HasSeriesParallelConstruction (pull M e) at h
  apply HasSeriesParallelConstruction.addColoop h
  · simp [pull_ground, hground]
  · simpa only [pull_isColoop, extendEquiv_zero] using hcoloop
  · exact normalized_delete f new hrange e hdel

theorem parallel (hM : FiniteSeriesParallel M) (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (hground : N.E = Set.univ)
    (selected : β) (heligible : M.IsNonloop selected)
    (hpair : N.IsCircuit {new, f selected})
    (hdel : N ＼ ({new} : Set α) = M.mapEmbedding f) : FiniteSeriesParallel N := by
  obtain ⟨m, e, h⟩ := hM
  refine ⟨m + 1, extendEquiv f new hrange e, ?_⟩
  change HasSeriesParallelConstruction (pull N (extendEquiv f new hrange e))
  change HasSeriesParallelConstruction (pull M e) at h
  apply HasSeriesParallelConstruction.parallel (e.symm selected) h
  · simp [pull_ground, hground]
  · simpa only [pull_isNonloop, e.apply_symm_apply] using heligible
  · simpa only [pull_isCircuit, Set.image_pair, extendEquiv_zero,
      extendEquiv_succ, e.apply_symm_apply] using hpair
  · exact normalized_delete f new hrange e hdel

theorem series (hM : FiniteSeriesParallel M) (f : β ↪ α) (new : α)
    (hrange : Set.range f = ({new} : Set α)ᶜ) (hground : N.E = Set.univ)
    (selected : β) (heligible : ¬M.IsColoop selected)
    (hpair : N.IsCocircuit {new, f selected})
    (hcon : N ／ ({new} : Set α) = M.mapEmbedding f) : FiniteSeriesParallel N := by
  obtain ⟨m, e, h⟩ := hM
  refine ⟨m + 1, extendEquiv f new hrange e, ?_⟩
  change HasSeriesParallelConstruction (pull N (extendEquiv f new hrange e))
  change HasSeriesParallelConstruction (pull M e) at h
  apply HasSeriesParallelConstruction.series (e.symm selected) h
  · simp [pull_ground, hground]
  · simpa only [pull_isColoop, e.apply_symm_apply] using heligible
  · simpa only [pull_isCocircuit, Set.image_pair, extendEquiv_zero,
      extendEquiv_succ, e.apply_symm_apply] using hpair
  · exact normalized_contract f new hrange e hcon

theorem of_isEmpty [IsEmpty α] (N : Matroid α) : FiniteSeriesParallel N := by
  let e : Fin 0 ≃ α := Equiv.equivOfIsEmpty _ _
  exact ⟨0, e, HasSeriesParallelConstruction.empty _⟩

/-- On a Fin label type the label-independent class is exactly the previously
proved standard abstract class; changing the enumeration adds no hypothesis. -/
theorem fin_iff {m : ℕ} (M : Matroid (Fin m)) :
    FiniteSeriesParallel M ↔ HasSeriesParallelConstruction M := by
  constructor
  · rintro ⟨k, e, h⟩
    have hkm : k = m := by simpa using Fintype.card_congr e
    subst k
    have hh := HasSeriesParallelConstruction.relabel e h
    change HasSeriesParallelConstruction (pull (pull M e) e.symm) at hh
    rwa [pull_symm_cancel] at hh
  · intro h
    refine ⟨m, Equiv.refl _, ?_⟩
    change HasSeriesParallelConstruction (pull M (Equiv.refl _))
    rwa [pull_id]

theorem ground_eq_univ (hM : FiniteSeriesParallel M) : M.E = Set.univ := by
  obtain ⟨m, e, h⟩ := hM
  have hg : (pull M e).E = Set.univ := h.ground_eq_univ
  rw [pull_ground] at hg
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, rfl⟩ := e.surjective x
  exact show j ∈ e ⁻¹' M.E from hg.symm ▸ Set.mem_univ j

end FiniteSeriesParallel

end Unimodular.SeriesParallel

end
