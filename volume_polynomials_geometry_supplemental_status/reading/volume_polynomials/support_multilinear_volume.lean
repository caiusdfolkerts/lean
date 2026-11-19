module

public import VolumePolynomials.MixedSupportForm
public import VolumePolynomials.OpenConeMultilinear

@[expose] public section
set_option autoImplicit false

/-! # The actual volume polynomial on unrestricted support directions

The full finite multilinear extension is constructed from actual mixed
volumes of the cone bodies. Its diagonal agrees with their genuine Haar
volume in the ambient dimension. Permutation symmetry is inherited from the
proved coefficient definition, and its first two arguments agree with the
previously constructed symmetric support form.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem bodyAtHeight_tuple_update
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (i : Fin n) (a : ι → ℝ) :
    (fun j => bodyAtHeight l h₀ hp hc (Function.update H i a j)) =
      Function.update (fun j => bodyAtHeight l h₀ hp hc (H j)) i
        (bodyAtHeight l h₀ hp hc a) := by
  first
  | funext j
    by_cases hji : j = i <;> simp [hji]

def heightVolumeValue
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) : ℝ :=
  mixedVolume μ (fun j => bodyAtHeight l h₀ hp hc (H j))

theorem heightVolumeValue_isMultilinearOnCone
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) (n : ℕ) :
    OpenConeModuleExtension.IsMultilinearOnCone (typeCone l h₀ hp hc)
      (heightVolumeValue μ l h₀ hp hc (n := n)) where
  add H hH i a ha b hb := by
    first
    | simp only [heightVolumeValue, bodyAtHeight_tuple_update]
      rw [bodyAtHeight_add l h₀ hp hc ha hb, mixedVolume_add]
  smul H hH i r hr a ha := by
    first
    | simp only [heightVolumeValue, bodyAtHeight_tuple_update]
      rw [bodyAtHeight_smul l h₀ hp hc ha hr, mixedVolume_smul μ _ _ _ hr.le]
      rfl

def supportMultilinearVolume
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ :=
  OpenConeModuleExtension.multilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (heightVolumeValue μ l h₀ hp hc)
    (heightVolumeValue_isMultilinearOnCone μ l h₀ hp hc n)

theorem supportMultilinearVolume_eq
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    supportMultilinearVolume μ l h₀ hg hp hc n H =
      mixedVolume μ (fun j => bodyAtHeight l h₀ hp hc (H j)) :=
  OpenConeModuleExtension.multilinearExtension_eq _ _ _ _ _ H hH

theorem supportMultilinearVolume_diagonal
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) :
    supportMultilinearVolume μ l h₀ hg hp hc n (fun _ => h) = μ.real (body l h) := by
  first
  | rw [supportMultilinearVolume_eq μ l h₀ hg hp hc _ (fun _ => hh),
      mixedVolume_diagonal μ hdim, coe_bodyAtHeight l h₀ hp hc hh]

theorem supportMultilinearVolume_reindex
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (e : Equiv.Perm (Fin n)) :
    supportMultilinearVolume μ l h₀ hg hp hc n (fun j => H (e j)) =
      supportMultilinearVolume μ l h₀ hg hp hc n H := by
  first
  | let F := supportMultilinearVolume μ l h₀ hg hp hc n
    have he : F.domDomCongr e = F := by
      apply OpenConeModuleExtension.multilinearMap_ext_of_eq_on_cone
        (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
        (typeCone_nonempty l h₀ hg hp hc)
      intro x hx
      change supportMultilinearVolume μ l h₀ hg hp hc n (fun j => x (e j)) = _
      rw [supportMultilinearVolume_eq μ l h₀ hg hp hc _ (fun j => hx (e j)),
        supportMultilinearVolume_eq μ l h₀ hg hp hc _ hx]
      exact mixedVolume_reindex μ (fun j => bodyAtHeight l h₀ hp hc (x j)) e
    exact congrArg (fun G : MultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ => G H) he

/-- Fixing all but the first two arguments of a genuine multilinear map gives
its ordinary bilinear form. -/
def firstTwoForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ) (H : Fin n → V) :
    LinearMap.BilinForm ℝ V where
  toFun x := {
    toFun := fun y => F (Fin.cons x (Fin.cons y H))
    map_add' := fun y z => (F.curryLeft x).cons_add H y z
    map_smul' := fun r y => (F.curryLeft x).cons_smul H r y
  }
  map_add' x y := by
    first
    | ext z
      exact F.cons_add (Fin.cons z H) x y
  map_smul' r x := by
    first
    | ext y
      exact F.cons_smul (Fin.cons y H) r x

theorem firstTwoForm_apply {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 2) => V) ℝ) (H : Fin n → V)
    (x y : V) : firstTwoForm (n := n) F H x y =
      F (Fin.cons x (Fin.cons y H) : Fin (n + 2) → V) := rfl

theorem bilinear_ext_of_eq_on_cone
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : ConvexCone ℝ V) (ho : IsOpen (C : Set V)) (hn : (C : Set V).Nonempty)
    {F G : LinearMap.BilinForm ℝ V}
    (hFG : ∀ x ∈ C, ∀ y ∈ C, F x y = G x y) : F = G := by
  first
  | apply LinearMap.ext
    intro x
    apply OpenConeExtension.linearMap_ext_of_eq_on_cone C ho hn
    intro y hy
    have he : F.flip y = G.flip y :=
      OpenConeExtension.linearMap_ext_of_eq_on_cone C ho hn (fun z hz => hFG z hz y hy)
    exact congrArg (fun f : V →ₗ[ℝ] ℝ => f x) he

set_option maxHeartbeats 1000000 in
theorem supportMultilinearVolume_firstTwoForm
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (H : Fin n → ι → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    firstTwoForm (n := n) (V := ι → ℝ)
      (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H =
      mixedSupportForm μ l h₀ hg hp hc (d := n)
        (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) := by
  first
  | refine bilinear_ext_of_eq_on_cone (typeCone l h₀ hp hc)
      (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
      (F := firstTwoForm (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H)
      (G := mixedSupportForm μ l h₀ hg hp hc
        (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j))) ?_
    intro x hx y hy
    let T : Fin (n + 2) → ι → ℝ := Fin.cons x (Fin.cons y H)
    have hT : ∀ j : Fin (n + 2), T j ∈ typeCone l h₀ hp hc :=
      fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j
    calc
      firstTwoForm (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H x y =
          supportMultilinearVolume μ l h₀ hg hp hc (n + 2) T :=
        firstTwoForm_apply (n := n) (supportMultilinearVolume μ l h₀ hg hp hc (n + 2)) H x y
      _ = mixedVolume μ (fun j : Fin (n + 2) => bodyAtHeight l h₀ hp hc (T j)) :=
        supportMultilinearVolume_eq μ l h₀ hg hp hc T hT
      _ = mixedSupportValue μ l h₀ hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) x y := by
        change mixedVolume μ (fun j : Fin (n + 2) => bodyAtHeight l h₀ hp hc (T j)) =
          mixedVolume μ (Fin.cons (bodyAtHeight l h₀ hp hc x)
            (Fin.cons (bodyAtHeight l h₀ hp hc y)
              (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j))) :
            Fin (n + 2) → ConvexBody E)
        apply congrArg (fun L : Fin (n + 2) → ConvexBody E => mixedVolume μ L)
        funext j
        exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j
      _ = mixedSupportForm μ l h₀ hg hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) x y :=
        (mixedSupportForm_eq_value μ l h₀ hg hp hc
          (fun j : Fin n => bodyAtHeight l h₀ hp hc (H j)) (x := x) (y := y) hx hy).symm

end VolumePolynomials.PolyhedralSupport
