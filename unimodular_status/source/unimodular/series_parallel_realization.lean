module

public import Unimodular.SeriesParallelPrograms
public import Unimodular.CubicalPolytopes

@[expose] public section

noncomputable section

namespace Unimodular.SeriesParallel

open scoped BigOperators
open TriangleExtension

attribute [local instance] Classical.propDecidable

namespace FanRealization

variable {n d m : ℕ}

def realLift : Ambient n →ₗ[ℝ] Ambient (n + 1) where
  toFun x := Fin.cons 0 x
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

def realTail : Ambient (n + 1) →ₗ[ℝ] Ambient n where
  toFun x := Fin.tail x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem realTail_apply (x : Ambient (n + 1)) : realTail x = Fin.tail x := rfl

@[simp] theorem realTail_cons (a : ℝ) (x : Ambient n) : realTail (Fin.cons a x) = x := rfl

@[simp] theorem lift_zero : TriangleExtension.lift (0 : Lattice n) = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [TriangleExtension.lift]

@[simp] theorem embed_lift (v : Lattice n) :
    embed (TriangleExtension.lift v) = realLift (embed v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [TriangleExtension.lift, realLift, embed]

@[simp] theorem embed_zero : embed (0 : Lattice n) = 0 := by ext i; simp [embed]

@[simp] theorem embed_cons (a : ℤ) (v : Lattice n) :
    embed (Fin.cons a v) = Fin.cons (a : ℝ) (embed v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [embed]

@[simp] theorem realTail_realLift (x : Ambient n) : realTail (realLift x) = x := rfl

theorem realLift_injective : Function.Injective (realLift : Ambient n → Ambient (n + 1)) := by
  intro x y h
  simpa only [realTail_realLift] using congrArg realTail h

def keep (q : Ambient n →ₗ[ℝ] Ambient d) : Ambient (n + 1) →ₗ[ℝ] Ambient (d + 1) where
  toFun x := Fin.cons (x 0) (q (Fin.tail x))
  map_add' x y := by
    have ht : Fin.tail (x + y) = Fin.tail x + Fin.tail y := rfl
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [ht, map_add]
  map_smul' a x := by
    have ht : Fin.tail (a • x) = a • Fin.tail x := rfl
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [ht, map_smul]

def skip (q : Ambient n →ₗ[ℝ] Ambient d) : Ambient (n + 1) →ₗ[ℝ] Ambient (d + 1) :=
  realLift.comp (q.comp realTail)

@[simp] theorem keep_lift (q : Ambient n →ₗ[ℝ] Ambient d) (x : Ambient n) :
    keep q (realLift x) = realLift (q x) := by simp [keep, realLift]

@[simp] theorem skip_lift (q : Ambient n →ₗ[ℝ] Ambient d) (x : Ambient n) :
    skip q (realLift x) = realLift (q x) := by rfl

@[simp] theorem skip_newRay_true (q : Ambient n →ₗ[ℝ] Ambient d) (u : Lattice n) :
    skip q (embed (newRay u true)) = realLift (q (embed u)) := by
  simp [skip, newRay, embed_cons]

@[simp] theorem skip_newRay_false (q : Ambient n →ₗ[ℝ] Ambient d) (u : Lattice n) :
    skip q (embed (newRay u false)) = 0 := by
  simp [skip, newRay, embed_cons]

@[simp] theorem keep_newRay_true (q : Ambient n →ₗ[ℝ] Ambient d) (u : Lattice n) :
    keep q (embed (newRay u true)) = Fin.cons 1 (q (embed u)) := by
  simp [keep, newRay, embed_cons]

@[simp] theorem keep_newRay_false (q : Ambient n →ₗ[ℝ] Ambient d) (u : Lattice n) :
    keep q (embed (newRay u false)) = embed (Fin.cons (-1) (0 : Lattice d)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [keep, newRay, embed_cons]

/-- Lifting the contracted rays maps their actual real span exactly. -/
theorem span_lifted (C : Finset (Lattice n)) :
    Submodule.span ℝ (embed '' (↑(C.image TriangleExtension.lift) : Set (Lattice (n + 1)))) =
      (Submodule.span ℝ (embed '' (C : Set (Lattice n)))).map realLift := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨embed y, ⟨y, hy, rfl⟩, (embed_lift y).symm⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨TriangleExtension.lift y, Finset.mem_image.2 ⟨y, hy, rfl⟩, embed_lift y⟩

theorem annihilates_contracted (q : Ambient n →ₗ[ℝ] Ambient d) (C : Finset (Lattice n))
    (hker : LinearMap.ker q = Submodule.span ℝ (embed '' (C : Set (Lattice n))))
    {z : Lattice n} (hz : z ∈ C) : q (embed z) = 0 := by
  change embed z ∈ LinearMap.ker q
  rw [hker]
  exact Submodule.subset_span ⟨z, hz, rfl⟩

/-- Keeping the new coordinate contracts exactly the lifted old contracted space. -/
theorem kernel_keep (q : Ambient n →ₗ[ℝ] Ambient d) (C : Finset (Lattice n))
    (hker : LinearMap.ker q = Submodule.span ℝ (embed '' (C : Set (Lattice n)))) :
    LinearMap.ker (keep q) =
      Submodule.span ℝ (embed '' (↑(C.image TriangleExtension.lift) : Set (Lattice (n + 1)))) := by
  apply le_antisymm
  · intro x hx
    have hh : x 0 = 0 := by simpa [keep] using congrFun hx 0
    have ht : q (Fin.tail x) = 0 := by
      ext j
      exact congrFun hx j.succ
    rw [span_lifted]
    refine ⟨Fin.tail x, ?_, ?_⟩
    · rw [← hker]
      exact ht
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [realLift, hh, Fin.tail]
  · apply Submodule.span_le.2
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    change keep q (embed (TriangleExtension.lift y)) = 0
    rw [embed_lift, keep_lift, annihilates_contracted q C hker hy, map_zero]

/-- Forgetting the new coordinate contracts exactly the old contracted rays and the
new lower ray; no larger kernel is silently allowed. -/
theorem kernel_skip (q : Ambient n →ₗ[ℝ] Ambient d) (C : Finset (Lattice n))
    (hker : LinearMap.ker q = Submodule.span ℝ (embed '' (C : Set (Lattice n))))
    (u : Lattice n) :
    LinearMap.ker (skip q) = Submodule.span ℝ
      (embed '' (↑(insert (newRay u false) (C.image TriangleExtension.lift)) : Set (Lattice (n + 1)))) := by
  let S := Submodule.span ℝ
    (embed '' (↑(insert (newRay u false) (C.image TriangleExtension.lift)) : Set (Lattice (n + 1))))
  apply le_antisymm
  · intro x hx
    have ht : q (Fin.tail x) = 0 := by
      change realLift (q (realTail x)) = 0 at hx
      have h := congrArg realTail hx
      rw [realTail_realLift,map_zero] at h
      exact h
    have htail : Fin.tail x ∈ Submodule.span ℝ (embed '' (C : Set (Lattice n))) := by
      rw [← hker]
      exact ht
    have hlift : realLift (Fin.tail x) ∈ S := by
      have hm : realLift (Fin.tail x) ∈
          Submodule.span ℝ (embed '' (↑(C.image TriangleExtension.lift) : Set (Lattice (n + 1)))) := by
        rw [span_lifted]
        exact ⟨Fin.tail x, htail, rfl⟩
      exact (Submodule.span_mono (Set.image_mono (by
        intro z hz
        exact Finset.mem_insert_of_mem hz))) hm
    have hb : embed (newRay u false) ∈ S :=
      Submodule.subset_span ⟨newRay u false, Finset.mem_insert_self _ _, rfl⟩
    have hxdec : x = realLift (Fin.tail x) + (-x 0) • embed (newRay u false) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [realLift, newRay, embed, Fin.tail, Pi.smul_apply, smul_eq_mul]
    rw [hxdec]
    exact S.add_mem hlift (S.smul_mem _ hb)
  · apply Submodule.span_le.2
    rintro x ⟨z, hz, rfl⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact skip_newRay_false q u
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      change skip q (embed (TriangleExtension.lift y)) = 0
      rw [embed_lift, skip_lift, annihilates_contracted q C hker hy, map_zero]

theorem lift_mem_rays (old : SmoothCompleteFan n) (u v : Lattice n) (hv : v ∈ old.rays) :
    TriangleExtension.lift v ∈ (TriangleExtension.fan old u).rays := by
  rw [rays_eq]
  exact Or.inl ⟨v, hv, rfl⟩

theorem newRay_mem_rays (old : SmoothCompleteFan n) (u : Lattice n) (s : Bool) :
    newRay u s ∈ (TriangleExtension.fan old u).rays := by
  rw [rays_eq]
  right
  cases s <;> simp

def appendChosen (f : Fin m ↪ Lattice n) (u : Lattice n) : Fin (m + 1) ↪ Lattice (n + 1) where
  toFun := Fin.cons (newRay u true) (fun j => TriangleExtension.lift (f j))
  inj' := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨j, hj⟩
      have hh := congrFun hj 0
      norm_num [newRay, TriangleExtension.lift] at hh
    · exact TriangleExtension.lift_injective.comp f.injective

theorem lift_chosen_not_mem {f : Fin m ↪ Lattice n} (C : Finset (Lattice n))
    (h : ∀ j, f j ∉ C) (j : Fin m) :
    TriangleExtension.lift (f j) ∉ C.image TriangleExtension.lift := by
  rintro hz
  obtain ⟨z, hz, he⟩ := Finset.mem_image.1 hz
  exact h j ((TriangleExtension.lift_injective he) ▸ hz)

theorem newRay_not_mem_lifted (C : Finset (Lattice n)) (u : Lattice n) (s : Bool) :
    newRay u s ∉ C.image TriangleExtension.lift := by
  intro hz
  obtain ⟨z, hz, he⟩ := Finset.mem_image.1 hz
  exact newRay_not_mem_lift u s (C : Set (Lattice n)) ⟨z, hz, he⟩

end FanRealization

namespace MinorWitness

open FanRealization

variable {m d n : ℕ} {old : SmoothCompleteFan n} {U : Fin m → Lattice d}

/-- Append a represented element while contracting the new lower ray. This implements
loop summands and parallel extensions, depending on the selected vector u. -/
def appendContract (h : MinorWitness old U) (u : Lattice n) (v : Lattice d)
    (hu : h.projection (embed u) = embed v) :
    MinorWitness (TriangleExtension.fan old u)
      (Fin.cons (liftColumn v) (fun j => liftColumn (U j))) where
  chosen := appendChosen h.chosen u
  chosen_rays := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact newRay_mem_rays old u true
    · exact lift_mem_rays old u _ (h.chosen_rays i)
  contracted := insert (newRay u false) (h.contracted.image TriangleExtension.lift)
  contracted_rays := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact newRay_mem_rays old u false
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      exact lift_mem_rays old u x (h.contracted_rays x hx)
  disjoint := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change newRay u true ∉ insert (newRay u false) _
      simp only [Finset.mem_insert, not_or]
      exact ⟨newRays_ne u, newRay_not_mem_lifted h.contracted u true⟩
    · change TriangleExtension.lift (h.chosen i) ∉ insert (newRay u false) _
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, lift_chosen_not_mem h.contracted h.disjoint i⟩
      intro he
      have hh := congrFun he 0
      norm_num [newRay, TriangleExtension.lift] at hh
  projection := skip h.projection
  kernel := kernel_skip h.projection h.contracted h.kernel u
  image := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change skip h.projection (embed (newRay u true)) = embed (liftColumn v)
      rw [skip_newRay_true, hu]
      exact (embed_lift v).symm
    · change skip h.projection (embed (TriangleExtension.lift (h.chosen i))) =
        embed (liftColumn (U i))
      rw [embed_lift, skip_lift, h.image i]
      exact (embed_lift (U i)).symm

/-- An independent singleton summand comes from the zero-selected extension, with
no new contraction. -/
def appendColoop (h : MinorWitness old U) :
    MinorWitness (TriangleExtension.fan old 0)
      (Fin.cons (newColumn d) (fun j => liftColumn (U j))) where
  chosen := appendChosen h.chosen 0
  chosen_rays := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact newRay_mem_rays old 0 true
    · exact lift_mem_rays old 0 _ (h.chosen_rays i)
  contracted := h.contracted.image TriangleExtension.lift
  contracted_rays := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact lift_mem_rays old 0 x (h.contracted_rays x hx)
  disjoint := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact newRay_not_mem_lifted h.contracted 0 true
    · exact lift_chosen_not_mem h.contracted h.disjoint i
  projection := keep h.projection
  kernel := kernel_keep h.projection h.contracted h.kernel
  image := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change keep h.projection (embed (newRay 0 true)) = embed (newColumn d)
      rw [keep_newRay_true, embed_zero, map_zero]
      ext k
      refine Fin.cases ?_ (fun i => ?_) k <;> simp [newColumn, embed]
    · change keep h.projection (embed (TriangleExtension.lift (h.chosen i))) =
        embed (liftColumn (U i))
      rw [embed_lift, keep_lift, h.image i]
      exact (embed_lift (U i)).symm

end MinorWitness

namespace FanRealization

variable {n m : ℕ}

def seriesTail (f : Fin m ↪ Lattice n) (u : Lattice n) (e : Fin m) (j : Fin m) :
    Lattice (n + 1) :=
  if j = e then newRay u true else TriangleExtension.lift (f j)

theorem seriesTail_injective (f : Fin m ↪ Lattice n) (u : Lattice n) (e : Fin m) :
    Function.Injective (seriesTail f u e) := by
  intro i j he
  by_cases hi : i = e
  · by_cases hj : j = e
    · exact hi.trans hj.symm
    · have hh := congrFun he 0
      norm_num [seriesTail, hi, hj, newRay, TriangleExtension.lift] at hh
  · by_cases hj : j = e
    · have hh := congrFun he 0
      norm_num [seriesTail, hi, hj, newRay, TriangleExtension.lift] at hh
    · apply f.injective
      apply TriangleExtension.lift_injective
      simpa only [seriesTail, if_neg hi, if_neg hj] using he

def seriesChosen (f : Fin m ↪ Lattice n) (u : Lattice n) (e : Fin m) :
    Fin (m + 1) ↪ Lattice (n + 1) where
  toFun := Fin.cons (newRay u false) (seriesTail f u e)
  inj' := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨j, hj⟩
      have hh := congrFun hj 0
      by_cases he : j = e <;>
        norm_num [seriesTail, he, newRay, TriangleExtension.lift] at hh
    · exact seriesTail_injective f u e

end FanRealization

namespace MinorWitness

open FanRealization

variable {m d n : ℕ} {old : SmoothCompleteFan n} {U : Fin m → Lattice d}

/-- The literal series extension: discard the selected old ray and retain the upper and
lower new rays, whose sum is its lift. The contracted set is only lifted. -/
def series (h : MinorWitness old U) (e : Fin m) :
    MinorWitness (TriangleExtension.fan old (h.chosen e))
      (Fin.cons (Fin.cons (-1) 0)
        (fun j => if j = e then Fin.cons 1 (U e) else liftColumn (U j))) where
  chosen := seriesChosen h.chosen (h.chosen e) e
  chosen_rays := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact newRay_mem_rays old (h.chosen e) false
    · change seriesTail h.chosen (h.chosen e) e i ∈ _
      by_cases hi : i = e
      · simp only [seriesTail, if_pos hi]
        exact newRay_mem_rays old (h.chosen e) true
      · simp only [seriesTail, if_neg hi]
        exact lift_mem_rays old (h.chosen e) _ (h.chosen_rays i)
  contracted := h.contracted.image TriangleExtension.lift
  contracted_rays := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact lift_mem_rays old (h.chosen e) x (h.contracted_rays x hx)
  disjoint := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact newRay_not_mem_lifted h.contracted (h.chosen e) false
    · change seriesTail h.chosen (h.chosen e) e i ∉ _
      by_cases hi : i = e
      · simp only [seriesTail, if_pos hi]
        exact newRay_not_mem_lifted h.contracted (h.chosen e) true
      · simp only [seriesTail, if_neg hi]
        exact lift_chosen_not_mem h.contracted h.disjoint i
  projection := keep h.projection
  kernel := kernel_keep h.projection h.contracted h.kernel
  image := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact keep_newRay_false h.projection (h.chosen e)
    · change keep h.projection (embed (if i = e then newRay (h.chosen e) true
          else TriangleExtension.lift (h.chosen i))) =
        embed (if i = e then Fin.cons 1 (U e) else liftColumn (U i))
      by_cases hi : i = e
      · rw [if_pos hi, if_pos hi, keep_newRay_true, h.image e]
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp [embed]
      · rw [if_neg hi, if_neg hi, embed_lift, keep_lift, h.image i]
        exact (embed_lift (U i)).symm

/-- Relabeling changes neither the fan nor the contracted set. -/
def relabel (h : MinorWitness old U) (e : Equiv.Perm (Fin m)) :
    MinorWitness old (U ∘ e) where
  chosen := ⟨fun j => h.chosen (e j), h.chosen.injective.comp e.injective⟩
  chosen_rays j := h.chosen_rays (e j)
  contracted := h.contracted
  contracted_rays := h.contracted_rays
  disjoint j := h.disjoint (e j)
  projection := h.projection
  kernel := h.kernel
  image j := h.image (e j)

end MinorWitness

/-- A complete fan realization certificate for a program with m elements. Both counts
refer to actual ray vectors and actual geometric maximal cones. -/
structure ProgramRealization {m : ℕ} (P : SPProgram m) where
  fan : SmoothCompleteFan m
  criterion : fan.PositiveCoordinateCriterion
  cubical : CubicalFan fan
  witness : MinorWitness fan P.columns
  ray_count : fan.rays.ncard = 2 * m
  cone_injective : Set.InjOn basisCone
    (↑fan.maximal : Set (Module.Basis (Fin m) ℤ (Lattice m)))
  cone_count : (fan.maximal.image basisCone).card = 2 ^ m

namespace ProgramRealization

open FanRealization

/-- A general induction step: the genuine fan extension and exact minor witness
carry the geometric counts through one increase of dimension. -/
def extend {m : ℕ} {P : SPProgram m} (R : ProgramRealization P)
    (Q : SPProgram (m + 1)) (u : Lattice m)
    (hu : ∀ b ∈ R.fan.maximal, ∑ i, max (b.repr u i) 0 ≤ 1)
    (w : MinorWitness (TriangleExtension.fan R.fan u) Q.columns) : ProgramRealization Q where
  fan := TriangleExtension.fan R.fan u
  criterion := positiveCriterion_of_bound R.fan u hu R.criterion
  cubical := R.cubical.extend u
  witness := w
  ray_count := by rw [rays_ncard, R.ray_count]; omega
  cone_injective := cone_injective_on_maximal R.fan u R.cone_injective
  cone_count := by
    rw [geometric_maximal_card R.fan u R.cone_injective, R.cone_count, pow_succ]
    omega

def empty : ProgramRealization SPProgram.empty where
  fan := zeroFan
  criterion := zeroFan_positiveCriterion
  cubical := CubicalFan.zero
  witness :=
    { chosen := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
      chosen_rays := fun i => Fin.elim0 i
      contracted := ∅
      contracted_rays := by simp
      disjoint := fun i => Fin.elim0 i
      projection := 0
      kernel := by
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        simp [hx]
      image := fun i => Fin.elim0 i }
  ray_count := by
    have hz : zeroFan.rays = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro x ⟨b, hb, i, hi⟩
      exact Fin.elim0 i
    simp [hz]
  cone_injective := zeroFan_cone_injective
  cone_count := by
    rw [Finset.card_image_of_injOn zeroFan_cone_injective]
    simp [zeroFan]

def addLoop {m : ℕ} {P : SPProgram m} (R : ProgramRealization P) :
    ProgramRealization P.addLoop := by
  apply R.extend P.addLoop 0 (by intro b hb; simp)
  have h := R.witness.appendContract 0 0 (by simp)
  have hz : liftColumn (0 : Lattice m) = 0 := lift_zero
  simpa only [SPProgram.columns, hz] using h

def addColoop {m : ℕ} {P : SPProgram m} (R : ProgramRealization P) :
    ProgramRealization P.addColoop :=
  R.extend P.addColoop 0 (by intro b hb; simp) R.witness.appendColoop

def parallel {m : ℕ} {P : SPProgram m} (R : ProgramRealization P) (e : Fin m) :
    ProgramRealization (P.parallel e) :=
  R.extend (P.parallel e) (R.witness.chosen e)
    (fun b hb => R.criterion b hb _ (R.witness.chosen_rays e))
    (R.witness.appendContract (R.witness.chosen e) (P.columns e) (R.witness.image e))

def series {m : ℕ} {P : SPProgram m} (R : ProgramRealization P) (e : Fin m) :
    ProgramRealization (P.series e) :=
  R.extend (P.series e) (R.witness.chosen e)
    (fun b hb => R.criterion b hb _ (R.witness.chosen_rays e)) (R.witness.series e)

def relabel {m : ℕ} {P : SPProgram m} (R : ProgramRealization P)
    (e : Equiv.Perm (Fin m)) : ProgramRealization (P.relabel e) where
  fan := R.fan
  criterion := R.criterion
  cubical := R.cubical
  witness := R.witness.relabel e
  ray_count := R.ray_count
  cone_injective := R.cone_injective
  cone_count := R.cone_count

end ProgramRealization

/-- Every finite series/parallel construction has a genuine complete smooth fan
realization, with exact contraction kernel and the paper's ray and cone counts.
Admissibility is not needed for the construction; it is used in the separate theorem
identifying programs with the standard matroid extension operations. -/
theorem program_has_realization {m : ℕ} (P : SPProgram m) : Nonempty (ProgramRealization P) := by
  induction P with
  | empty => exact ⟨ProgramRealization.empty⟩
  | addLoop P ih => obtain ⟨R⟩ := ih; exact ⟨R.addLoop⟩
  | addColoop P ih => obtain ⟨R⟩ := ih; exact ⟨R.addColoop⟩
  | parallel P e ih => obtain ⟨R⟩ := ih; exact ⟨R.parallel e⟩
  | series P e ih => obtain ⟨R⟩ := ih; exact ⟨R.series e⟩
  | relabel P e ih => obtain ⟨R⟩ := ih; exact ⟨R.relabel e⟩

/-- The quantitative constructive conclusion of Proposition 6.7, with the dimension
chosen to equal the target's number of elements. The target minor is certified by
all independent subsets of an actual quotient, and the Matroid bridge identifies it
with the standard contraction/deletion operations. -/
theorem program_fan_realization {m : ℕ} (P : SPProgram m) :
    ∃ σ : SmoothCompleteFan m, σ.PositiveCoordinateCriterion ∧
      Nonempty (MinorWitness σ P.columns) ∧ σ.rays.ncard = 2 * m ∧
      (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨R⟩ := program_has_realization P
  exact ⟨R.fan, R.criterion, ⟨R.witness⟩, R.ray_count, R.cone_count⟩

/-- The fan certificate also yields an actual deeply monotone smooth reflexive
polytope, with exactly the same primitive facet-normal configuration. -/
theorem program_polytope_realization {m : ℕ} (P : SPProgram m) :
    ∃ σ : SmoothCompleteFan m, ∃ Q : SmoothReflexivePresentation m,
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      Nonempty (MinorWitness σ P.columns) ∧ σ.rays.ncard = 2 * m ∧
      (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨σ, hσ, hminor, hrays, hcones⟩ := program_fan_realization P
  refine ⟨σ, σ.polarPresentation hσ, hσ, σ.polarPresentation_deeplyMonotone hσ,
    ?_, hminor, hrays, hcones⟩
  ext u
  exact σ.mem_rayFinset u

/-- Proposition 6.7's geometric construction: an actual deeply monotone smooth
reflexive polytope, a face-lattice isomorphism with the ordinary cube, the target
configuration as a genuine quotient/deletion witness, and the stated counts. -/
theorem program_cubical_polytope_realization {m : ℕ} (P : SPProgram m) :
    ∃ σ : SmoothCompleteFan m, ∃ Q : SmoothReflexivePresentation m,
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      Nonempty (MinorWitness σ P.columns) ∧ σ.rays.ncard = 2 * m ∧
      (σ.maximal.image basisCone).card = 2 ^ m := by
  obtain ⟨R⟩ := program_has_realization P
  refine ⟨R.fan, R.fan.polarPresentation R.criterion, R.criterion,
    R.fan.polarPresentation_deeplyMonotone R.criterion,
    R.cubical.polar_isCombinatorialCube R.criterion, ?_, ⟨R.witness⟩,
    R.ray_count, R.cone_count⟩
  ext u
  exact R.fan.mem_rayFinset u

end Unimodular.SeriesParallel

end
