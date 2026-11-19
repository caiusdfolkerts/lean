/- Exact effective rational arithmetic, including unbounded word encodings. -/
module

public import mixed_volume.computability.rational_code
public import mixed_volume.computability.fractional_words
public import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false

@[expose] public section
open Matrix
open scoped BigOperators

namespace MixedVolume

/-- A rational-valued function has a primitive-recursive exact rational output
code. This is a property of its actual value, not a restriction on input sizes. -/
def RationalPrimrec {α : Type*} [Primcodable α] (f : α → ℚ) : Prop :=
  ∃ c : α → RationalCode.Code, Primrec c ∧ ∀ x, RationalCode.eval (c x) = f x

namespace RationalPrimrec

open RationalCode
variable {α β : Type*} [Primcodable α] [Primcodable β] {f g : α → ℚ}

theorem const (q : ℚ) : RationalPrimrec (fun _ : α => q) := by
  obtain ⟨c, hc⟩ := eval_surjective q
  exact ⟨fun _ => c, Primrec.const c, fun _ => hc⟩

theorem eval : RationalPrimrec RationalCode.eval := ⟨id, Primrec.id, fun _ => rfl⟩

theorem of_eq (hf : RationalPrimrec f) (h : ∀ x, f x = g x) : RationalPrimrec g := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨c, hc, fun x => (he x).trans (h x)⟩

theorem comp (hf : RationalPrimrec f) {h : β → α} (hh : Primrec h) :
    RationalPrimrec (fun x => f (h x)) := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨c ∘ h, hc.comp hh, fun x => he (h x)⟩

theorem neg (hf : RationalPrimrec f) : RationalPrimrec (fun x => -f x) := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨fun x => RationalCode.neg (c x), neg_primrec.comp hc, by intro x; simp [he]⟩

theorem inv (hf : RationalPrimrec f) : RationalPrimrec (fun x => (f x)⁻¹) := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨fun x => RationalCode.inv (c x), inv_primrec.comp hc, by intro x; simp [he]⟩

theorem abs (hf : RationalPrimrec f) : RationalPrimrec (fun x => |f x|) := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨fun x => RationalCode.abs (c x), abs_primrec.comp hc, by intro x; simp [he]⟩

theorem add (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    RationalPrimrec (fun x => f x + g x) := by
  obtain ⟨c, hc, he⟩ := hf
  obtain ⟨d, hd, hdv⟩ := hg
  exact ⟨fun x => RationalCode.add (c x) (d x), add_primrec.comp hc hd,
    by intro x; simp [he, hdv]⟩

theorem mul (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    RationalPrimrec (fun x => f x * g x) := by
  obtain ⟨c, hc, he⟩ := hf
  obtain ⟨d, hd, hdv⟩ := hg
  exact ⟨fun x => RationalCode.mul (c x) (d x), mul_primrec.comp hc hd,
    by intro x; simp [he, hdv]⟩

theorem sub (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    RationalPrimrec (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem div (hf : RationalPrimrec f) (hg : RationalPrimrec g) :
    RationalPrimrec (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem pow (hf : RationalPrimrec f) (n : ℕ) :
    RationalPrimrec (fun x => f x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (const (α := α) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem nat_cast {f : α → ℕ} (hf : Primrec f) :
    RationalPrimrec (fun x => (f x : ℚ)) :=
  ⟨fun x => RationalCode.nat (f x), nat_primrec.comp hf, fun x => eval_nat (f x)⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → α → ℚ}
    (hf : ∀ i ∈ s, RationalPrimrec (f i)) :
    RationalPrimrec (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (α := α) 0)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem prod {ι : Type*} (s : Finset ι) {f : ι → α → ℚ}
    (hf : ∀ i ∈ s, RationalPrimrec (f i)) :
    RationalPrimrec (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (α := α) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finite_sum {ι : Type*} [Fintype ι] {f : ι → α → ℚ}
    (hf : ∀ i, RationalPrimrec (f i)) :
    RationalPrimrec (fun x => ∑ i, f i x) := sum Finset.univ (fun i _ => hf i)

theorem finite_prod {ι : Type*} [Fintype ι] {f : ι → α → ℚ}
    (hf : ∀ i, RationalPrimrec (f i)) :
    RationalPrimrec (fun x => ∏ i, f i x) := prod Finset.univ (fun i _ => hf i)

theorem matrix_mul {ι κ ν : Type*} [Fintype κ]
    {M : α → Matrix ι κ ℚ} {N : α → Matrix κ ν ℚ}
    (hM : ∀ i k, RationalPrimrec (fun x => M x i k))
    (hN : ∀ k j, RationalPrimrec (fun x => N x k j)) (i : ι) (j : ν) :
    RationalPrimrec (fun x => (M x * N x) i j) := by
  exact finite_sum (fun k => (hM i k).mul (hN k j))

theorem vecMul {ι κ : Type*} [Fintype ι]
    {p : α → ι → ℚ} {M : α → Matrix ι κ ℚ}
    (hp : ∀ i, RationalPrimrec (fun x => p x i))
    (hM : ∀ i j, RationalPrimrec (fun x => M x i j)) (j : κ) :
    RationalPrimrec (fun x => (p x ᵥ* M x) j) := by
  exact finite_sum (fun i => (hp i).mul (hM i j))

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : α → Matrix ι ι ℚ} (hM : ∀ i j, RationalPrimrec (fun x => M x i j)) :
    RationalPrimrec (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  exact finite_sum (fun σ => (const _).mul (finite_prod (fun i => hM (σ i) i)))

/-- All finite rational output arrays can be emitted jointly. -/
theorem finite_output {n : ℕ} {f : α → Fin n → ℚ}
    (hf : ∀ i, RationalPrimrec (fun x => f x i)) :
    ∃ c : α → Fin n → Code, Primrec c ∧ ∀ x i, RationalCode.eval (c x i) = f x i := by
  classical
  choose c hc he using hf
  exact ⟨fun x i => c i x, MatrixMortality.Primrec.fin_function hc, fun x i => he i x⟩

private def digitCode : Bool → Code
  | false => nat 1
  | true => nat 2

private def valueCode (w : List Bool) : Code :=
  w.foldr (fun b c => RationalCode.div (RationalCode.add (digitCode b) c) (nat 4)) (nat 0)

private theorem valueCode_primrec : Primrec valueCode := by
  unfold valueCode
  apply Primrec.list_foldr (h := fun (_ : List Bool) (p : Bool × Code) =>
    RationalCode.div (RationalCode.add (digitCode p.1) p.2) (nat 4))
    Primrec.id (Primrec.const (nat 0))
  apply Primrec₂.mk
  exact div_primrec.comp
    (add_primrec.comp ((Primrec.dom_finite digitCode).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)) (Primrec.const (nat 4))

private theorem valueCode_eval (w : List Bool) :
    RationalCode.eval (valueCode w) = FractionalWords.value w := by
  induction w with
  | nil => simp [valueCode]
  | cons b w ih =>
    change RationalCode.eval (RationalCode.div
      (RationalCode.add (digitCode b) (valueCode w)) (nat 4)) = _
    simp only [eval_div, eval_add, eval_nat, ih, FractionalWords.value_cons]
    cases b <;> simp [digitCode, FractionalWords.digit]

theorem word_value : RationalPrimrec FractionalWords.value :=
  ⟨valueCode, valueCode_primrec, valueCode_eval⟩

private def scaleCode (w : List Bool) : Code :=
  w.foldr (fun _ c => RationalCode.div c (nat 4)) (nat 1)

private theorem scaleCode_primrec : Primrec scaleCode := by
  unfold scaleCode
  apply Primrec.list_foldr (h := fun (_ : List Bool) (p : Bool × Code) =>
    RationalCode.div p.2 (nat 4)) Primrec.id (Primrec.const (nat 1))
  apply Primrec₂.mk
  exact div_primrec.comp (Primrec.snd.comp Primrec.snd) (Primrec.const (nat 4))

private theorem scaleCode_eval (w : List Bool) :
    RationalCode.eval (scaleCode w) = FractionalWords.scale w := by
  induction w with
  | nil => simp [scaleCode]
  | cons b w ih =>
    change RationalCode.eval (RationalCode.div (scaleCode w) (nat 4)) = _
    simp only [eval_div, eval_nat, ih, FractionalWords.scale_cons, Nat.cast_ofNat]

theorem word_scale : RationalPrimrec FractionalWords.scale :=
  ⟨scaleCode, scaleCode_primrec, scaleCode_eval⟩

end RationalPrimrec
end MixedVolume
