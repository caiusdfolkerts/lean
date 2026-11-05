module

public import VolumePolynomials.OpenConeModuleExtension

@[expose] public section
set_option autoImplicit false

/-! # The unique finite multilinear extension from a genuine open cone

The construction is a finite induction on the arity. At each step, the
remaining arguments form an ordinary vector space of multilinear maps, and
the first argument is extended by actual differences of cone elements.
-/

noncomputable section
open Set

namespace VolumePolynomials.OpenConeModuleExtension

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

structure IsMultilinearOnCone {n : ℕ} (f : (Fin n → V) → W) : Prop where
  add : ∀ (x : Fin n → V), (∀ j, x j ∈ C) → ∀ i a, a ∈ C → ∀ b, b ∈ C →
    f (Function.update x i (a + b)) = f (Function.update x i a) + f (Function.update x i b)
  smul : ∀ (x : Fin n → V), (∀ j, x j ∈ C) → ∀ i (r : ℝ), 0 < r → ∀ a, a ∈ C →
    f (Function.update x i (r • a)) = r • f (Function.update x i a)

theorem IsMultilinearOnCone.cons {n : ℕ} {f : (Fin (n + 1) → V) → W}
    (hf : IsMultilinearOnCone C f) {a : V} (ha : a ∈ C) :
    IsMultilinearOnCone C (fun x : Fin n → V => f (Fin.cons a x)) where
  add x hx i b hb c hc := by
    first
    | simpa only [Fin.cons_update] using
        hf.add (Fin.cons a x) (fun j => Fin.cases ha hx j) i.succ b hb c hc
  smul x hx i r hr b hb := by
    first
    | simpa only [Fin.cons_update] using
        hf.smul (Fin.cons a x) (fun j => Fin.cases ha hx j) i.succ r hr b hb

include hopen hne in
theorem exists_multilinearExtension {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) :
    ∃ F : MultilinearMap ℝ (fun _ : Fin n => V) W,
      ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = f x := by
  first
  | classical
    induction n with
    | zero =>
        refine ⟨MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => V)
          (f (fun i : Fin 0 => Fin.elim0 i)), ?_⟩
        intro x _
        have he : x = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
        rw [he]
        rfl
    | succ n ih =>
        let G : V → MultilinearMap ℝ (fun _ : Fin n => V) W := fun a =>
          if ha : a ∈ C then
            Classical.choose (ih (fun x => f (Fin.cons a x)) (hf.cons C ha))
          else 0
        have hG (a : V) (ha : a ∈ C) (x : Fin n → V) (hx : ∀ i, x i ∈ C) :
            G a x = f (Fin.cons a x) := by
          dsimp only [G]
          rw [dif_pos ha]
          exact Classical.choose_spec (ih (fun x => f (Fin.cons a x)) (hf.cons C ha)) x hx
        have hadd : AdditiveOn C G := by
          intro a ha b hb
          apply multilinearMap_ext_of_eq_on_cone C hopen hne
          intro x hx
          rw [MultilinearMap.add_apply, hG a ha x hx, hG b hb x hx,
            hG (a + b) (C.add_mem ha hb) x hx]
          simpa only [Fin.update_cons_zero] using
            hf.add (Fin.cons a x) (fun j => Fin.cases ha hx j) 0 a ha b hb
        have hsmul : PositiveHomogeneousOn C G := by
          intro r hr a ha
          apply multilinearMap_ext_of_eq_on_cone C hopen hne
          intro x hx
          rw [MultilinearMap.smul_apply, hG a ha x hx,
            hG (r • a) (C.smul_mem hr ha) x hx]
          simpa only [Fin.update_cons_zero] using
            hf.smul (Fin.cons a x) (fun j => Fin.cases ha hx j) 0 r hr a ha
        refine ⟨(linearExtension C hopen hne G hadd hsmul).uncurryLeft, ?_⟩
        intro x hx
        rw [LinearMap.uncurryLeft_apply, linearExtension_eq C hopen hne G hadd hsmul (hx 0),
          hG (x 0) (hx 0) (Fin.tail x) (fun j => hx j.succ), Fin.cons_self_tail]

def multilinearExtension {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) : MultilinearMap ℝ (fun _ : Fin n => V) W :=
  Classical.choose (exists_multilinearExtension C hopen hne f hf)

theorem multilinearExtension_eq {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f) (x : Fin n → V) (hx : ∀ i, x i ∈ C) :
    multilinearExtension C hopen hne f hf x = f x :=
  Classical.choose_spec (exists_multilinearExtension C hopen hne f hf) x hx

theorem multilinearExtension_unique {n : ℕ} (f : (Fin n → V) → W)
    (hf : IsMultilinearOnCone C f)
    (F : MultilinearMap ℝ (fun _ : Fin n => V) W)
    (hF : ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = f x) :
    F = multilinearExtension C hopen hne f hf :=
  multilinearMap_ext_of_eq_on_cone C hopen hne (fun x hx =>
    (hF x hx).trans (multilinearExtension_eq C hopen hne f hf x hx).symm)

include hopen in
theorem positive_of_nonnegative_on_cone {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin n => V) ℝ)
    (hF : ∀ x : Fin n → V, (∀ i, x i ∈ C) → 0 ≤ F x)
    {p : V} (hp : p ∈ C) (hdiag : 0 < F (fun _ => p))
    (H : Fin n → V) (hH : ∀ i, H i ∈ C) : 0 < F H := by
  first
  | obtain ⟨ε, hε, hG⟩ := OpenConeExtension.exists_pos_sub_all C hopen H hH p
    let G : Fin n → V := fun i => H i - ε • p
    have hscale : ε • p ∈ C := C.smul_mem hε hp
    have hdecomp : H = (fun _ : Fin n => ε • p) + G := by
      funext i
      change H i = ε • p + (H i - ε • p)
      abel
    have hterm (s : Finset (Fin n)) : 0 ≤ F (s.piecewise (fun _ => ε • p) G) := by
      apply hF
      intro i
      by_cases hi : i ∈ s
      · simpa only [Finset.piecewise, hi, if_true] using hscale
      · simpa only [Finset.piecewise, hi, if_false, G] using hG i
    have hle : F (fun _ : Fin n => ε • p) ≤ F H := by
      rw [hdecomp, F.map_add_univ]
      have he := Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Finset (Fin n) => F (s.piecewise (fun _ => ε • p) G))
        (fun s _ => hterm s) (Finset.mem_univ (Finset.univ : Finset (Fin n)))
      simpa only [Finset.piecewise_univ] using he
    have hhom : F (fun _ : Fin n => ε • p) = ε ^ n * F (fun _ => p) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
        F.map_smul_univ (fun _ : Fin n => ε) (fun _ => p)
    rw [hhom] at hle
    exact (mul_pos (pow_pos hε n) hdiag).trans_le hle

end VolumePolynomials.OpenConeModuleExtension
