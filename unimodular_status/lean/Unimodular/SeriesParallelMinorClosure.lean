module

public import Unimodular.SeriesParallelFinite

@[expose] public section

noncomputable section

open Set
open scoped Matroid

namespace Unimodular.SeriesParallel

attribute [local instance] Classical.propDecidable

namespace EmbeddingTransport

variable {α β γ : Type*}

@[simp] theorem map_dual (M : Matroid α) (f : α ↪ β) :
    (M.mapEmbedding f)✶ = M✶.mapEmbedding f := by
  simp only [Matroid.mapEmbedding, Matroid.map_dual]

theorem map_comp (M : Matroid α) (f : α ↪ β) (g : β ↪ γ) :
    (M.mapEmbedding f).mapEmbedding g = M.mapEmbedding (f.trans g) := by
  apply Matroid.ext_indep
  · simp only [Matroid.mapEmbedding_ground_eq, Set.image_image]
    rfl
  · intro I hI
    simp only [Matroid.mapEmbedding, Matroid.map_indep_iff]
    constructor
    · rintro ⟨J, ⟨K, hK, rfl⟩, rfl⟩
      exact ⟨K, hK, by rw [Set.image_image]; rfl⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨f '' K, ⟨K, hK, rfl⟩, by rw [Set.image_image]; rfl⟩

theorem map_injective (f : α ↪ β) :
    Function.Injective (fun M : Matroid α => M.mapEmbedding f) := by
  intro M N h
  have hh := congrArg (fun L : Matroid β => L.comap f) h
  simpa only [Matroid.mapEmbedding, Matroid.comap_map f.injective] using hh

theorem map_delete (M : Matroid α) (f : α ↪ β) (D : Set β) :
    M.mapEmbedding f ＼ D = (M ＼ (f ⁻¹' D)).mapEmbedding f := by
  apply Matroid.ext_indep
  · ext x
    simp only [Matroid.delete_ground, Matroid.mapEmbedding_ground_eq,
      Set.mem_sdiff, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hd⟩
      exact ⟨y, ⟨hy, hd⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hd⟩
  · intro I hI
    rw [Matroid.delete_indep_iff, Matroid.mapEmbedding_indep_iff,
      Matroid.mapEmbedding_indep_iff, Matroid.delete_indep_iff]
    constructor
    · rintro ⟨⟨hi, hr⟩, hd⟩
      exact ⟨⟨hi, Set.disjoint_left.2 (fun x hx hxD =>
        Set.disjoint_left.1 hd hx hxD)⟩, hr⟩
    · rintro ⟨⟨hi, hd⟩, hr⟩
      refine ⟨⟨hi, hr⟩, Set.disjoint_left.2 ?_⟩
      intro x hx hxD
      obtain ⟨y, rfl⟩ := hr hx
      exact Set.disjoint_left.1 hd hx hxD

theorem map_delete_image (M : Matroid α) (f : α ↪ β) (D : Set α) :
    (M ＼ D).mapEmbedding f = M.mapEmbedding f ＼ (f '' D) := by
  rw [map_delete, Set.preimage_image_eq _ f.injective]

theorem map_contract (M : Matroid α) (f : α ↪ β) (C : Set β) :
    M.mapEmbedding f ／ C = (M ／ (f ⁻¹' C)).mapEmbedding f := by
  apply Matroid.dual_inj.1
  simp only [Matroid.dual_contract, map_dual, map_delete]

theorem map_contract_image (M : Matroid α) (f : α ↪ β) (C : Set α) :
    (M ／ C).mapEmbedding f = M.mapEmbedding f ／ (f '' C) := by
  rw [map_contract, Set.preimage_image_eq _ f.injective]

@[simp] theorem map_image_indep (M : Matroid α) (f : α ↪ β) (I : Set α) :
    (M.mapEmbedding f).Indep (f '' I) ↔ M.Indep I := by
  rw [Matroid.mapEmbedding_indep_iff, Set.preimage_image_eq _ f.injective]
  simp only [Set.image_subset_range, and_true]

@[simp] theorem map_image_dep (M : Matroid α) (f : α ↪ β) (I : Set α) :
    (M.mapEmbedding f).Dep (f '' I) ↔ M.Dep I := by
  rw [Matroid.dep_iff, Matroid.dep_iff, map_image_indep,
    Matroid.mapEmbedding_ground_eq, Set.image_subset_image_iff f.injective]

@[simp] theorem map_image_circuit (M : Matroid α) (f : α ↪ β) (C : Set α) :
    (M.mapEmbedding f).IsCircuit (f '' C) ↔ M.IsCircuit C := by
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep,
    Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep, map_image_dep]
  apply and_congr_right
  intro hC
  constructor
  · intro h x hx
    have hh := h (f x) ⟨x, hx, rfl⟩
    rw [← Set.image_singleton, ← Set.image_sdiff f.injective, map_image_indep] at hh
    exact hh
  · rintro h x ⟨y, hy, rfl⟩
    rw [← Set.image_singleton, ← Set.image_sdiff f.injective, map_image_indep]
    exact h y hy

@[simp] theorem map_image_cocircuit (M : Matroid α) (f : α ↪ β) (C : Set α) :
    (M.mapEmbedding f).IsCocircuit (f '' C) ↔ M.IsCocircuit C := by
  rw [Matroid.isCocircuit_def, map_dual, map_image_circuit,
    Matroid.isCocircuit_def]

@[simp] theorem map_isLoop (M : Matroid α) (f : α ↪ β) (x : α) :
    (M.mapEmbedding f).IsLoop (f x) ↔ M.IsLoop x := by
  rw [← Matroid.singleton_isCircuit, ← Matroid.singleton_isCircuit,
    ← Set.image_singleton, map_image_circuit]

@[simp] theorem map_isNonloop (M : Matroid α) (f : α ↪ β) (x : α) :
    (M.mapEmbedding f).IsNonloop (f x) ↔ M.IsNonloop x := by
  rw [← Matroid.indep_singleton, ← Matroid.indep_singleton,
    ← Set.image_singleton, map_image_indep]

@[simp] theorem map_isColoop (M : Matroid α) (f : α ↪ β) (x : α) :
    (M.mapEmbedding f).IsColoop (f x) ↔ M.IsColoop x := by
  change (M.mapEmbedding f)✶.IsLoop (f x) ↔ M✶.IsLoop x
  rw [map_dual, map_isLoop]

end EmbeddingTransport

/-- The ordinary series--parallel construction on the actual ground set of a
matroid. Unlike a predicate on all ambient labels, this remains meaningful after
Mathlib deletion and contraction. Its equivalence to the full-ground construction
class is proved below; it introduces no additional mathematical assumption. -/
inductive GroundSeriesParallel {α : Type*} : Matroid α → Prop
  | empty (M : Matroid α) (hE : M.E = ∅) : GroundSeriesParallel M
  | addLoop {M : Matroid α} {e : α} :
      GroundSeriesParallel (M ＼ {e}) → M.IsLoop e → GroundSeriesParallel M
  | addColoop {M : Matroid α} {e : α} :
      GroundSeriesParallel (M ＼ {e}) → M.IsColoop e → GroundSeriesParallel M
  | parallel {M : Matroid α} {e f : α} :
      GroundSeriesParallel (M ＼ {e}) → e ≠ f → M.IsCircuit {e, f} →
      GroundSeriesParallel M
  | series {M : Matroid α} {e f : α} :
      GroundSeriesParallel (M ／ {e}) → e ≠ f → M.IsCocircuit {e, f} →
      GroundSeriesParallel M

namespace GroundSeriesParallel

open EmbeddingTransport

variable {α β : Type*} {M N : Matroid α}

theorem dual (h : GroundSeriesParallel M) : GroundSeriesParallel M✶ := by
  induction h with
  | empty M hE => exact .empty _ (by simpa using hE)
  | @addLoop M e h he ih =>
    apply GroundSeriesParallel.addColoop (e := e) _ he.dual_isColoop
    have hh : M ／ ({e} : Set α) = M ＼ {e} :=
      Matroid.contract_eq_delete_of_subset_loops (Set.singleton_subset_iff.2 he)
    rw [← Matroid.dual_contract, hh]
    exact ih
  | @addColoop M e h he ih =>
    apply GroundSeriesParallel.addLoop (e := e) _ he.dual_isLoop
    have hh : M ／ ({e} : Set α) = M ＼ {e} :=
      Matroid.contract_eq_delete_of_subset_coloops (Set.singleton_subset_iff.2 he)
    rw [← Matroid.dual_contract, hh]
    exact ih
  | @parallel M e f h hef hp ih =>
    exact .series (by simpa only [Matroid.dual_delete] using ih) hef
      (by simpa only [Matroid.isCocircuit_def, Matroid.dual_dual] using hp)
  | @series M e f h hef hp ih =>
    exact .parallel (by simpa only [Matroid.dual_contract] using ih) hef hp

theorem mapEmbedding (h : GroundSeriesParallel M) (g : α ↪ β) :
    GroundSeriesParallel (M.mapEmbedding g) := by
  induction h with
  | empty M hE => exact .empty _ (by simp [hE])
  | @addLoop M e h he ih =>
    apply GroundSeriesParallel.addLoop (e := g e)
    · simpa only [map_delete_image, Set.image_singleton] using ih
    · exact (map_isLoop M g e).2 he
  | @addColoop M e h he ih =>
    apply GroundSeriesParallel.addColoop (e := g e)
    · simpa only [map_delete_image, Set.image_singleton] using ih
    · exact (map_isColoop M g e).2 he
  | @parallel M e f h hef hp ih =>
    apply GroundSeriesParallel.parallel (e := g e) (f := g f)
    · simpa only [map_delete_image, Set.image_singleton] using ih
    · exact g.injective.ne hef
    · simpa only [Set.image_pair] using (map_image_circuit M g _).2 hp
  | @series M e f h hef hp ih =>
    apply GroundSeriesParallel.series (e := g e) (f := g f)
    · simpa only [map_contract_image, Set.image_singleton] using ih
    · exact g.injective.ne hef
    · simpa only [Set.image_pair] using (map_image_cocircuit M g _).2 hp

/-- Injectively relabeling a matroid reflects the ordinary construction class.
Every element used by an extension belongs to the actual image ground, so the
induction pulls that extension back to its unique old label. -/
theorem of_mapEmbedding (g : α ↪ β) (h : GroundSeriesParallel (M.mapEmbedding g)) :
    GroundSeriesParallel M := by
  suffices main : ∀ N : Matroid β, GroundSeriesParallel N →
      ∀ X : Matroid α, N = X.mapEmbedding g → GroundSeriesParallel X from
    main _ h M rfl
  intro N hN
  induction hN with
  | empty N hE =>
    intro X hX
    apply GroundSeriesParallel.empty X
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hgx : g x ∈ N.E := by
      rw [hX, Matroid.mapEmbedding_ground_eq]
      exact ⟨x, hx, rfl⟩
    simpa only [hE, Set.mem_empty_iff_false] using hgx
  | @addLoop N e h he ih =>
    intro X hX
    have heE : e ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using he.mem_ground
    obtain ⟨x, hx, rfl⟩ := heE
    apply GroundSeriesParallel.addLoop (e := x)
    · apply ih (X ＼ {x})
      rw [map_delete_image, Set.image_singleton, ← hX]
    · exact (map_isLoop X g x).1 (hX ▸ he)
  | @addColoop N e h he ih =>
    intro X hX
    have heE : e ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using he.mem_ground
    obtain ⟨x, hx, rfl⟩ := heE
    apply GroundSeriesParallel.addColoop (e := x)
    · apply ih (X ＼ {x})
      rw [map_delete_image, Set.image_singleton, ← hX]
    · exact (map_isColoop X g x).1 (hX ▸ he)
  | @parallel N e f h hef hp ih =>
    intro X hX
    have heE : e ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using hp.subset_ground (by simp)
    have hfE : f ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using hp.subset_ground (by simp)
    obtain ⟨x, hx, rfl⟩ := heE
    obtain ⟨y, hy, rfl⟩ := hfE
    apply GroundSeriesParallel.parallel (e := x) (f := y)
    · apply ih (X ＼ {x})
      rw [map_delete_image, Set.image_singleton, ← hX]
    · exact fun hxy => hef (congrArg g hxy)
    · apply (map_image_circuit X g {x, y}).1
      simpa only [Set.image_pair] using hX ▸ hp
  | @series N e f h hef hp ih =>
    intro X hX
    have heE : e ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using hp.subset_ground (by simp)
    have hfE : f ∈ g '' X.E := by
      simpa only [hX, Matroid.mapEmbedding_ground_eq] using hp.subset_ground (by simp)
    obtain ⟨x, hx, rfl⟩ := heE
    obtain ⟨y, hy, rfl⟩ := hfE
    apply GroundSeriesParallel.series (e := x) (f := y)
    · apply ih (X ／ {x})
      rw [map_contract_image, Set.image_singleton, ← hX]
    · exact fun hxy => hef (congrArg g hxy)
    · apply (map_image_cocircuit X g {x, y}).1
      simpa only [Set.image_pair] using hX ▸ hp

@[simp] theorem mapEmbedding_iff (g : α ↪ β) :
    GroundSeriesParallel (M.mapEmbedding g) ↔ GroundSeriesParallel M :=
  ⟨of_mapEmbedding g, fun h => h.mapEmbedding g⟩

theorem ground_finite (h : GroundSeriesParallel M) : M.E.Finite := by
  induction h with
  | empty M hE => simp [hE]
  | @addLoop M e h he ih =>
    apply (ih.insert e).subset
    intro x hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr ⟨hx, hxe⟩
  | @addColoop M e h he ih =>
    apply (ih.insert e).subset
    intro x hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr ⟨hx, hxe⟩
  | @parallel M e f h hef hp ih =>
    apply (ih.insert e).subset
    intro x hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr ⟨hx, hxe⟩
  | @series M e f h hef hp ih =>
    apply (ih.insert e).subset
    intro x hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr ⟨hx, hxe⟩

end GroundSeriesParallel

namespace GroundNormalization

open EmbeddingTransport

variable {α : Type*}

abbrev normal (M : Matroid α) : Matroid M.E := M.restrictSubtype M.E

abbrev val (M : Matroid α) : M.E ↪ α := Function.Embedding.subtype _

@[simp] theorem normal_map_val (M : Matroid α) :
    (normal M).mapEmbedding (val M) = M :=
  M.map_val_restrictSubtype_ground_eq

@[simp] theorem normal_loop (M : Matroid α) (e : M.E) :
    (normal M).IsLoop e ↔ M.IsLoop e := by
  have h := map_isLoop (normal M) (val M) e
  rw [normal_map_val] at h
  exact h.symm

@[simp] theorem normal_nonloop (M : Matroid α) (e : M.E) :
    (normal M).IsNonloop e ↔ M.IsNonloop e := by
  have h := map_isNonloop (normal M) (val M) e
  rw [normal_map_val] at h
  exact h.symm

@[simp] theorem normal_coloop (M : Matroid α) (e : M.E) :
    (normal M).IsColoop e ↔ M.IsColoop e := by
  have h := map_isColoop (normal M) (val M) e
  rw [normal_map_val] at h
  exact h.symm

@[simp] theorem normal_circuit (M : Matroid α) (C : Set M.E) :
    (normal M).IsCircuit C ↔ M.IsCircuit (Subtype.val '' C) := by
  have h := map_image_circuit (normal M) (val M) C
  rw [normal_map_val] at h
  exact h.symm

@[simp] theorem normal_cocircuit (M : Matroid α) (C : Set M.E) :
    (normal M).IsCocircuit C ↔ M.IsCocircuit (Subtype.val '' C) := by
  have h := map_image_cocircuit (normal M) (val M) C
  rw [normal_map_val] at h
  exact h.symm

def deleteIncl (M : Matroid α) (e : α) : (M ＼ {e}).E ↪ M.E :=
  ⟨fun x => ⟨x.1, x.2.1⟩, fun x y h =>
    Subtype.ext (congrArg (fun z : M.E => z.val) h)⟩

@[simp] theorem deleteIncl_range (M : Matroid α) (e : α) (he : e ∈ M.E) :
    Set.range (deleteIncl M e) = ({⟨e, he⟩} : Set M.E)ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ hx
    exact y.2.2 (congrArg Subtype.val hx)
  · intro hx
    refine ⟨⟨x.1, x.2, ?_⟩, rfl⟩
    intro hxe
    exact hx (Subtype.ext hxe)

theorem normal_delete (M : Matroid α) (e : α) (he : e ∈ M.E) :
    (normal M) ＼ ({⟨e, he⟩} : Set M.E) =
      (normal (M ＼ {e})).mapEmbedding (deleteIncl M e) := by
  apply map_injective (val M)
  dsimp only
  rw [map_delete_image, Set.image_singleton, normal_map_val, map_comp]
  exact (normal_map_val (M ＼ {e})).symm

abbrev contractIncl (M : Matroid α) (e : α) : (M ／ {e}).E ↪ M.E :=
  deleteIncl M e

@[simp] theorem contractIncl_range (M : Matroid α) (e : α) (he : e ∈ M.E) :
    Set.range (contractIncl M e) = ({⟨e, he⟩} : Set M.E)ᶜ :=
  deleteIncl_range M e he

theorem normal_contract (M : Matroid α) (e : α) (he : e ∈ M.E) :
    (normal M) ／ ({⟨e, he⟩} : Set M.E) =
      (normal (M ／ {e})).mapEmbedding (contractIncl M e) := by
  apply map_injective (val M)
  dsimp only
  rw [map_contract_image, Set.image_singleton, normal_map_val, map_comp]
  exact (normal_map_val (M ／ {e})).symm

end GroundNormalization

namespace GroundSeriesParallel

open GroundNormalization

variable {α : Type*} {M : Matroid α}

/-- The ground-set construction is exactly the existing finite abstract class,
with no ghost ambient elements included as loops. -/
theorem finite_onGround (h : GroundSeriesParallel M) : FiniteSeriesParallel (normal M) := by
  induction h with
  | empty M hE =>
    letI : IsEmpty M.E := ⟨fun x => by simpa only [hE, Set.mem_empty_iff_false] using x.2⟩
    exact FiniteSeriesParallel.of_isEmpty _
  | @addLoop M e h he ih =>
    exact ih.addLoop (deleteIncl M e) ⟨e, he.mem_ground⟩
      (deleteIncl_range M e he.mem_ground) Matroid.restrictSubtype_ground
      ((normal_loop M _).2 he) (normal_delete M e he.mem_ground)
  | @addColoop M e h he ih =>
    exact ih.addColoop (deleteIncl M e) ⟨e, he.mem_ground⟩
      (deleteIncl_range M e he.mem_ground) Matroid.restrictSubtype_ground
      ((normal_coloop M _).2 he) (normal_delete M e he.mem_ground)
  | @parallel M e f h hef hp ih =>
    have heE : e ∈ M.E := hp.subset_ground (by simp)
    have hfE : f ∈ M.E := hp.subset_ground (by simp)
    let old : (M ＼ {e}).E := ⟨f, hfE, hef.symm⟩
    have hf : M.IsNonloop f := hp.isNonloop_of_mem (Set.nontrivial_pair hef) (by simp)
    apply ih.parallel (deleteIncl M e) ⟨e, heE⟩ (deleteIncl_range M e heE)
      Matroid.restrictSubtype_ground old
    · apply (normal_nonloop _ _).2
      exact Matroid.delete_isNonloop_iff.2 ⟨hf, hef.symm⟩
    · rw [normal_circuit,Set.image_pair]
      change M.IsCircuit {e,f}
      exact hp
    · exact normal_delete M e heE
  | @series M e f h hef hp ih =>
    have heE : e ∈ M.E := hp.subset_ground (by simp)
    have hfE : f ∈ M.E := hp.subset_ground (by simp)
    let old : (M ／ {e}).E := ⟨f, hfE, hef.symm⟩
    have hf : M✶.IsNonloop f := hp.isCircuit.isNonloop_of_mem
      (Set.nontrivial_pair hef) (by simp)
    apply ih.series (contractIncl M e) ⟨e, heE⟩ (contractIncl_range M e heE)
      Matroid.restrictSubtype_ground old
    · rw [normal_coloop, Matroid.contract_isColoop_iff]
      exact fun hcol => hf.not_isLoop hcol.1
    · rw [normal_cocircuit,Set.image_pair]
      change M.IsCocircuit {e,f}
      exact hp
    · exact normal_contract M e heE

/-- For a full-ground matroid the ground-set construction is the ordinary finite
label-independent construction on that very label type. -/
theorem finite (h : GroundSeriesParallel M) (hE : M.E = Set.univ) :
    FiniteSeriesParallel M := by
  let e : M.E ≃ α := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun x => ⟨⟨x, hE.symm ▸ Set.mem_univ x⟩, rfl⟩⟩
  have hh := h.finite_onGround.relabel e
  change FiniteSeriesParallel ((normal M).mapEmbedding (val M)) at hh
  simpa only [normal_map_val] using hh

theorem hasConstruction {m : ℕ} {N : Matroid (Fin m)}
    (h : GroundSeriesParallel N) (hE : N.E = Set.univ) :
    HasSeriesParallelConstruction N :=
  (FiniteSeriesParallel.fin_iff N).1 (h.finite hE)

end GroundSeriesParallel

/-- Every full-ground standard construction is also a construction on its actual
embedded ground set. This direction preserves every extension and relabeling. -/
theorem HasSeriesParallelConstruction.groundConstruction {m : ℕ} {M : Matroid (Fin m)}
    (h : HasSeriesParallelConstruction M) : GroundSeriesParallel M := by
  induction h with
  | empty M =>
    apply GroundSeriesParallel.empty
    ext x
    exact Fin.elim0 x
  | @addLoop m M N h hg he hd ih =>
    exact .addLoop (hd.symm ▸ ih.mapEmbedding (oldLabels m)) he
  | @addColoop m M N h hg he hd ih =>
    exact .addColoop (hd.symm ▸ ih.mapEmbedding (oldLabels m)) he
  | @parallel m M N e h hg he hp hd ih =>
    exact .parallel (hd.symm ▸ ih.mapEmbedding (oldLabels m)) (Ne.symm (Fin.succ_ne_zero e)) hp
  | @series m M N e h hg he hp hc ih =>
    exact .series (hc.symm ▸ ih.mapEmbedding (oldLabels m)) (Ne.symm (Fin.succ_ne_zero e)) hp
  | relabel e h ih => exact ih.mapEmbedding e.toEmbedding

theorem FiniteSeriesParallel.groundConstruction {α : Type*} {M : Matroid α}
    (h : FiniteSeriesParallel M) : GroundSeriesParallel M := by
  obtain ⟨m, e, hm⟩ := h
  have hh := hm.groundConstruction.mapEmbedding e.toEmbedding
  change GroundSeriesParallel (FiniteRelabel.pull (FiniteRelabel.pull M e) e.symm) at hh
  simpa only [FiniteRelabel.pull_symm_cancel] using hh

/-- The ground-set predicate and the ordinary abstract construction are
mathematically equivalent, with the precise ground-subtype convention exposed. -/
theorem groundSeriesParallel_iff_finite_onGround {α : Type*} (M : Matroid α) :
    GroundSeriesParallel M ↔ FiniteSeriesParallel (M.restrictSubtype M.E) := by
  constructor
  · exact GroundSeriesParallel.finite_onGround
  · intro h
    have hh := h.groundConstruction.mapEmbedding (GroundNormalization.val M)
    simpa only [GroundNormalization.normal_map_val] using hh

namespace ParallelMinorLemmas

open FiniteRelabel

variable {α : Type*} {M : Matroid α} {e f : α}

private theorem swap_image_eq_self {I : Set α} (h : e ∈ I ↔ f ∈ I) :
    Equiv.swap e f '' I = I := by
  classical
  ext x
  simp only [Set.mem_image_equiv, Equiv.symm_swap]
  by_cases hxe : x = e
  · subst x
    simpa only [Equiv.swap_apply_left] using h.symm
  by_cases hxf : x = f
  · subst x
    simpa only [Equiv.swap_apply_right] using h
  simp only [Equiv.swap_apply_of_ne_of_ne hxe hxf]

/-- Transposing two ordinary parallel elements is an automorphism of the complete
matroid, including all independent sets and its embedded ground set. -/
theorem pair_swap_pull (hp : M.IsCircuit {e, f}) (hef : e ≠ f) :
    pull M (Equiv.swap e f) = M := by
  classical
  have heE : e ∈ M.E := hp.subset_ground (by simp)
  have hfE : f ∈ M.E := hp.subset_ground (by simp)
  apply Matroid.ext_indep
  · ext x
    simp only [pull_ground, Set.mem_preimage]
    by_cases hxe : x = e
    · subst x
      simp only [Equiv.swap_apply_left, heE, hfE]
    by_cases hxf : x = f
    · subst x
      simp only [Equiv.swap_apply_right, heE, hfE]
    simp only [Equiv.swap_apply_of_ne_of_ne hxe hxf]
  · intro I hI
    rw [pull_indep]
    by_cases heI : e ∈ I
    · by_cases hfI : f ∈ I
      · rw [swap_image_eq_self (iff_of_true heI hfI)]
      · rw [Equiv.image_swap_of_mem_of_notMem heI hfI]
        have hset : insert f I \ {e} = insert f (I \ {e}) := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨rfl | hx, hxe⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hx, hxe⟩
          · rintro (rfl | ⟨hx, hxe⟩)
            · exact ⟨Or.inl rfl, hef.symm⟩
            · exact ⟨Or.inr hx, hxe⟩
        rw [hset]
        have hswap := (Matroid.pair_circuit_insert_indep_iff hp hef (I \ {e})
          (by simp) (fun hx => hfI hx.1)).symm
        simpa only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem heI] using hswap
    · by_cases hfI : f ∈ I
      · rw [Equiv.swap_comm]
        have hp' : M.IsCircuit {f, e} := by simpa only [Set.pair_comm] using hp
        rw [Equiv.image_swap_of_mem_of_notMem hfI heI]
        have hset : insert e I \ {f} = insert e (I \ {f}) := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨rfl | hx, hxf⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hx, hxf⟩
          · rintro (rfl | ⟨hx, hxf⟩)
            · exact ⟨Or.inl rfl, hef⟩
            · exact ⟨Or.inr hx, hxf⟩
        rw [hset]
        have hswap := (Matroid.pair_circuit_insert_indep_iff hp' hef.symm (I \ {f})
          (by simp) (fun hx => heI hx.1)).symm
        simpa only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hfI] using hswap
      · rw [swap_image_eq_self (iff_of_false heI hfI)]

/-- Contracting one element of an ordinary parallel pair makes its partner a loop. -/
theorem pair_contract_loop (hp : M.IsCircuit {e, f}) (hef : e ≠ f) :
    (M ／ ({f} : Set α)).IsLoop e := by
  have hfE : f ∈ M.E := hp.subset_ground (by simp)
  have hfcl : f ∈ M.closure ({f} : Set α) :=
    M.subset_closure ({f} : Set α) (Set.singleton_subset_iff.2 hfE) (by simp)
  exact Matroid.contract_isLoop_iff_mem_closure.2
    ⟨(Matroid.pair_circuit_mem_closure_iff hp hef _).2 hfcl, hef⟩

/-- A parallel pair disjoint from a contracted set either remains an ordinary
parallel pair, or its first element becomes a loop (and so does its partner). -/
theorem pair_contract_loop_or_circuit (hp : M.IsCircuit {e, f}) (hef : e ≠ f)
    (C : Set α) (hC : Disjoint C ({e, f} : Set α)) :
    (M ／ C).IsLoop e ∨ (M ／ C).IsCircuit {e, f} := by
  by_cases he : (M ／ C).IsLoop e
  · exact Or.inl he
  right
  have heC : e ∉ C := fun hx => Set.disjoint_left.1 hC hx (by simp)
  have hfC : f ∉ C := fun hx => Set.disjoint_left.1 hC hx (by simp)
  have heq : (M ／ C).IsLoop e ↔ (M ／ C).IsLoop f := by
    rw [Matroid.contract_isLoop_iff_mem_closure,
      Matroid.contract_isLoop_iff_mem_closure]
    exact and_congr (Matroid.pair_circuit_mem_closure_iff hp hef C)
      (iff_of_true heC hfC)
  have hf : ¬ (M ／ C).IsLoop f := fun h => he (heq.2 h)
  have hd : (M ／ C).Dep {e, f} := hp.contract_dep hC
  have hen : (M ／ C).IsNonloop e :=
    (Matroid.not_isLoop_iff (hd.subset_ground (by simp))).1 he
  have hfn : (M ／ C).IsNonloop f :=
    (Matroid.not_isLoop_iff (hd.subset_ground (by simp))).1 hf
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  refine ⟨hd, ?_⟩
  intro x hx
  rcases hx with rfl | rfl
  · simpa only [Set.pair_sdiff_left hef] using hfn.indep
  · simpa only [Set.pair_sdiff_right hef] using hen.indep

/-- The exact reduction when the newly added element of a parallel pair is
contracted. This identity handles the surviving loop explicitly. -/
theorem pair_contract_delete (hp : M.IsCircuit {e, f}) (hef : e ≠ f) :
    M ／ ({e} : Set α) ＼ {f} = (M ＼ ({e} : Set α)) ／ {f} := by
  have hp' : M.IsCircuit {f, e} := by simpa only [Set.pair_comm] using hp
  have hf := pair_contract_loop hp' hef.symm
  have he := pair_contract_loop hp hef
  calc
    M ／ ({e} : Set α) ＼ {f} = M ／ ({e} : Set α) ／ {f} :=
      (Matroid.contract_eq_delete_of_subset_loops (Set.singleton_subset_iff.2 hf)).symm
    _ = M ／ ({f} : Set α) ／ {e} := Matroid.contract_comm _ _ _
    _ = M ／ ({f} : Set α) ＼ {e} :=
      Matroid.contract_eq_delete_of_subset_loops (Set.singleton_subset_iff.2 he)
    _ = (M ＼ ({e} : Set α)) ／ {f} :=
      Matroid.contract_delete_comm _ (Set.disjoint_singleton.2 hef.symm)

end ParallelMinorLemmas

namespace GroundSeriesParallel

open FiniteRelabel ParallelMinorLemmas

variable {α : Type*} {M N : Matroid α}

private def SingleClosed (M : Matroid α) : Prop :=
  ∀ x : α, GroundSeriesParallel (M ＼ {x}) ∧ GroundSeriesParallel (M ／ {x})

private theorem SingleClosed.dual (h : SingleClosed M) : SingleClosed M✶ := by
  intro x
  exact ⟨by simpa only [Matroid.dual_contract] using (h x).2.dual,
    by simpa only [Matroid.dual_delete] using (h x).1.dual⟩

private theorem loop_step_closed {e : α} (hbase : GroundSeriesParallel (M ＼ {e}))
    (he : M.IsLoop e) (ih : SingleClosed (M ＼ {e})) : SingleClosed M := by
  intro x
  by_cases hxe : x = e
  · subst x
    refine ⟨hbase, ?_⟩
    rw [Matroid.contract_eq_delete_of_subset_loops (Set.singleton_subset_iff.2 he)]
    exact hbase
  have hex : e ≠ x := Ne.symm hxe
  constructor
  · apply GroundSeriesParallel.addLoop (e := e)
    · rw [Matroid.delete_comm]
      exact (ih x).1
    · exact Matroid.delete_isLoop_iff.2 ⟨he, hex⟩
  · apply GroundSeriesParallel.addLoop (e := e)
    · rw [Matroid.contract_delete_comm M (Set.disjoint_singleton.2 hxe)]
      exact (ih x).2
    · exact Matroid.contract_isLoop_iff_mem_closure.2 ⟨he.mem_closure _, hex⟩

private theorem parallel_step_closed {e f : α}
    (hbase : GroundSeriesParallel (M ＼ {e})) (hef : e ≠ f)
    (hp : M.IsCircuit {e, f}) (ih : SingleClosed (M ＼ {e})) : SingleClosed M := by
  classical
  intro x
  by_cases hxe : x = e
  · subst x
    refine ⟨hbase, ?_⟩
    apply GroundSeriesParallel.addLoop (e := f)
    · rw [pair_contract_delete hp hef]
      exact (ih f).2
    · have hp' : M.IsCircuit {f, e} := by simpa only [Set.pair_comm] using hp
      exact pair_contract_loop hp' hef.symm
  by_cases hxf : x = f
  · subst x
    constructor
    · have hs := hbase.mapEmbedding (Equiv.swap e f).symm.toEmbedding
      change GroundSeriesParallel (pull (M ＼ {e}) (Equiv.swap e f)) at hs
      rw [pull_delete, pair_swap_pull hp hef] at hs
      simpa only [Set.image_singleton, Equiv.symm_swap, Equiv.swap_apply_left] using hs
    · apply GroundSeriesParallel.addLoop (e := e)
      · rw [Matroid.contract_delete_comm M (Set.disjoint_singleton.2 hef.symm)]
        exact (ih f).2
      · exact pair_contract_loop hp hef
  have hex : e ≠ x := Ne.symm hxe
  have hfx : f ≠ x := Ne.symm hxf
  constructor
  · apply GroundSeriesParallel.parallel (e := e) (f := f)
    · rw [Matroid.delete_comm]
      exact (ih x).1
    · exact hef
    · exact Matroid.delete_isCircuit_iff.2 ⟨hp, by simp [hxe, hxf]⟩
  · have hb : GroundSeriesParallel ((M ／ ({x} : Set α)) ＼ {e}) := by
      rw [Matroid.contract_delete_comm M (Set.disjoint_singleton.2 hxe)]
      exact (ih x).2
    rcases pair_contract_loop_or_circuit hp hef ({x} : Set α)
      (by simp [hxe, hxf]) with hl | hc
    · exact .addLoop hb hl
    · exact .parallel hb hef hc

/-- Deletion and contraction of any single element preserve the ordinary
series--parallel construction. The proof includes loop and coloop degenerations;
series steps follow from the parallel analysis by actual matroid duality. -/
theorem single_closed (h : GroundSeriesParallel M) :
    ∀ x : α, GroundSeriesParallel (M ＼ {x}) ∧ GroundSeriesParallel (M ／ {x}) := by
  induction h with
  | empty M hE =>
    intro x
    exact ⟨.empty _ (by simp [hE]), .empty _ (by simp [hE])⟩
  | @addLoop M e h he ih => exact loop_step_closed h he ih
  | @addColoop M e h he ih =>
    have hc : M ／ ({e} : Set α) = M ＼ {e} :=
      Matroid.contract_eq_delete_of_subset_coloops (Set.singleton_subset_iff.2 he)
    have hd : M✶ ＼ ({e} : Set α) = (M ＼ ({e} : Set α))✶ := by
      rw [← Matroid.dual_contract, hc]
    have hb : GroundSeriesParallel (M✶ ＼ ({e} : Set α)) := hd.symm ▸ h.dual
    have hi : SingleClosed (M✶ ＼ ({e} : Set α)) :=
      hd.symm ▸ SingleClosed.dual ih
    have hh := SingleClosed.dual (loop_step_closed hb he.dual_isLoop hi)
    simpa only [SingleClosed, Matroid.dual_dual] using hh
  | @parallel M e f h hef hp ih => exact parallel_step_closed h hef hp ih
  | @series M e f h hef hp ih =>
    have hb : GroundSeriesParallel (M✶ ＼ ({e} : Set α)) := by
      simpa only [Matroid.dual_contract] using h.dual
    have hi : SingleClosed (M✶ ＼ ({e} : Set α)) := by
      simpa only [Matroid.dual_contract] using SingleClosed.dual ih
    have hh := SingleClosed.dual (parallel_step_closed hb hef hp.isCircuit hi)
    simpa only [SingleClosed, Matroid.dual_dual] using hh

theorem deleteElem (h : GroundSeriesParallel M) (x : α) :
    GroundSeriesParallel (M ＼ {x}) := (h.single_closed x).1

theorem contractElem (h : GroundSeriesParallel M) (x : α) :
    GroundSeriesParallel (M ／ {x}) := (h.single_closed x).2

/-- Arbitrary deletion is reduced to the finite part of the deleted set lying in
its actual ground set. Elements outside the ground have no effect. -/
theorem delete (h : GroundSeriesParallel M) (D : Set α) :
    GroundSeriesParallel (M ＼ D) := by
  classical
  have hfin (s : Finset α) : GroundSeriesParallel (M ＼ (s : Set α)) := by
    induction s using Finset.induction_on with
    | empty => simpa using h
    | @insert x s hx ih =>
      have hh := ih.deleteElem x
      simpa only [Matroid.delete_delete, Finset.coe_insert,
        Set.union_singleton] using hh
  have hf : (D ∩ M.E).Finite := h.ground_finite.subset Set.inter_subset_right
  rw [← Matroid.delete_inter_ground_eq M D]
  simpa only [Set.Finite.coe_toFinset] using hfin hf.toFinset

theorem contract (h : GroundSeriesParallel M) (C : Set α) :
    GroundSeriesParallel (M ／ C) := by
  have hh := (h.dual.delete C).dual
  simpa only [Matroid.dual_delete_dual] using hh

/-- Full closure under the literal Mathlib minor relation, without an ambient
full-ground hypothesis, a representability assumption, or a restriction on ranks. -/
theorem minor (h : GroundSeriesParallel M) (hNM : N ≤m M) :
    GroundSeriesParallel N := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact (h.contract C).delete D

end GroundSeriesParallel

/-- Any minor of a finite series--parallel matroid is again an ordinary finite
series--parallel matroid after retaining exactly its actual ground labels. -/
theorem FiniteSeriesParallel.minor_onGround {α : Type*} {M N : Matroid α}
    (hM : FiniteSeriesParallel M) (hNM : N ≤m M) :
    FiniteSeriesParallel (N.restrictSubtype N.E) :=
  (hM.groundConstruction.minor hNM).finite_onGround

end Unimodular.SeriesParallel

end
