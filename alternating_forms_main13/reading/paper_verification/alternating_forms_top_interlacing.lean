module

public import TauCeti.Data.Sym.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
# Interlacing and the symmetric-power indexing set in Corollary 5.2

The selected `a` indices are zero based.  If `c` enumerates the omitted
`b` indices, the inequalities are `cᵢ ≤ aᵢ < cᵢ₊₁`.  Subtracting `i`
from both kinds of entries gives the literal weak list in the paper.
The construction is an equivalence with unordered tuples, not a cardinality
assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

def abIndex (k : ℕ) : Fin k ⊕ Fin (k+1) ≃ Fin (2*k+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have h : ¬(2*i.val+1)%2=0 := by omega
        simp only [h, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have h : (2*i.val)%2=0 := by omega
        simp only [h, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

theorem strictMonoFin_lower {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : i.val ≤ (f i).val := by
  have h : ∀ r : ℕ, ∀ hr : r<m, r ≤ (f ⟨r,hr⟩).val := by
    intro r
    induction r with
    | zero => intro hr; exact Nat.zero_le _
    | succ r ih =>
        intro hr
        have hr' : r<m := by omega
        have hp := ih hr'
        have hs := hf (show (⟨r,hr'⟩ : Fin m) < ⟨r+1,hr⟩ from Nat.lt_succ_self r)
        change (f ⟨r,hr'⟩).val < (f ⟨r+1,hr⟩).val at hs
        omega
  exact h i.val i.isLt

theorem strictMonoFin_upper {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : (f i).val + m ≤ n+i.val := by
  have hr : StrictMono (fun j : Fin m => (f j.rev).rev) := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hab))
  have h := strictMonoFin_lower _ hr i.rev
  simp only [Fin.val_rev, Fin.rev_rev] at h
  have hi := i.isLt
  have hf' := (f i).isLt
  omega

def Interlacing (p q : ℕ) :=
  {ac : (Fin p → Fin (p+q)) × (Fin (p+1) → Fin (p+q+1)) //
    StrictMono ac.1 ∧ StrictMono ac.2 ∧
      ∀ i : Fin p, (ac.2 i.castSucc).val ≤ (ac.1 i).val ∧
        (ac.1 i).val < (ac.2 i.succ).val}

def WeakWord (r q : ℕ) := {z : Fin r → Fin (q+1) // Monotone z}

instance (p q : ℕ) : Fintype (Interlacing p q) := by
  unfold Interlacing
  infer_instance
instance (r q : ℕ) : Fintype (WeakWord r q) := by
  unfold WeakWord
  infer_instance

def weakValue {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) : ℕ :=
  if h : j.val%2=0 then
    (I.val.2 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2
  else (I.val.1 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2

theorem weakValue_le {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) :
    weakValue I j ≤ q := by
  unfold weakValue
  split_ifs with hj
  · have h := strictMonoFin_upper I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega
  · have h := strictMonoFin_upper I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega

theorem weakValue_a {p q : ℕ} (I : Interlacing p q) (i : Fin p) :
    weakValue I (abIndex p (.inl i)) = (I.val.1 i).val-i.val := by
  have h : ¬(2*i.val+1)%2=0 := by omega
  have hd : (2*i.val+1)/2=i.val := by omega
  change weakValue I (⟨2*i.val+1, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_false, hd]

theorem weakValue_c {p q : ℕ} (I : Interlacing p q) (i : Fin (p+1)) :
    weakValue I (abIndex p (.inr i)) = (I.val.2 i).val-i.val := by
  have h : (2*i.val)%2=0 := by omega
  have hd : (2*i.val)/2=i.val := by omega
  change weakValue I (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_true, hd]

theorem weakValue_monotone {p q : ℕ} (I : Interlacing p q) :
    Monotone (weakValue I) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  by_cases hj : j.val%2=0
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have he : j.castSucc=abIndex p (.inr i.castSucc) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have ho : j.succ=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [he, ho, weakValue_c, weakValue_a]
    exact Nat.sub_le_sub_right (I.property.2.2 i).1 _
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have ho : j.castSucc=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have he : j.succ=abIndex p (.inr i.succ) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [ho, he, weakValue_a, weakValue_c]
    have hi := (I.property.2.2 i).2
    have ha := strictMonoFin_lower I.val.1 I.property.1 i
    have hc := strictMonoFin_lower I.val.2 I.property.2.1 i.succ
    simp only [Fin.val_succ] at *
    omega

def toWeakWord {p q : ℕ} (I : Interlacing p q) : WeakWord (2*p+1) q :=
  ⟨fun j => ⟨weakValue I j, Nat.lt_succ_of_le (weakValue_le I j)⟩,
    fun i j hij => weakValue_monotone I hij⟩

def ofWeakWord {p q : ℕ} (z : WeakWord (2*p+1) q) : Interlacing p q :=
  ⟨(fun i => ⟨(z.val (abIndex p (.inl i))).val+i.val,
      by have := (z.val (abIndex p (.inl i))).isLt; have := i.isLt; omega⟩,
    fun i => ⟨(z.val (abIndex p (.inr i))).val+i.val,
      by have := (z.val (abIndex p (.inr i))).isLt; have := i.isLt; omega⟩), by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hz := z.property (show abIndex p (.inl i) ≤ abIndex p (.inl j) from by
        change 2*i.val+1≤2*j.val+1
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inl i))).val ≤ (z.val (abIndex p (.inl j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inl i))).val+i.val <
        (z.val (abIndex p (.inl j))).val+j.val
      omega
    · intro i j hij
      have hz := z.property (show abIndex p (.inr i) ≤ abIndex p (.inr j) from by
        change 2*i.val≤2*j.val
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inr i))).val ≤ (z.val (abIndex p (.inr j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inr i))).val+i.val <
        (z.val (abIndex p (.inr j))).val+j.val
      omega
    · intro i
      have hl := z.property (show abIndex p (.inr i.castSucc) ≤ abIndex p (.inl i) from by
        change 2*i.val≤2*i.val+1
        omega)
      have hr := z.property (show abIndex p (.inl i) ≤ abIndex p (.inr i.succ) from by
        change 2*i.val+1≤2*(i.val+1)
        omega)
      change (z.val (abIndex p (.inr i.castSucc))).val ≤
        (z.val (abIndex p (.inl i))).val at hl
      change (z.val (abIndex p (.inl i))).val ≤
        (z.val (abIndex p (.inr i.succ))).val at hr
      dsimp only
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor <;> omega⟩

def interlacingWeakEquiv (p q : ℕ) : Interlacing p q ≃ WeakWord (2*p+1) q where
  toFun := toWeakWord
  invFun := ofWeakWord
  left_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inl i))+i.val=(I.val.1 i).val
      rw [weakValue_a, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.1 i)]
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inr i))+i.val=(I.val.2 i).val
      rw [weakValue_c, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.2.1 i)]
  right_inv z := by
    apply Subtype.ext
    funext j
    obtain ⟨j,rfl⟩ := (abIndex p).surjective j
    apply Fin.ext
    cases j with
    | inl i =>
        change weakValue (ofWeakWord z) (abIndex p (.inl i)) = _
        rw [weakValue_a]
        exact Nat.add_sub_cancel _ _
    | inr i =>
        change weakValue (ofWeakWord z) (abIndex p (.inr i)) = _
        rw [weakValue_c]
        exact Nat.add_sub_cancel _ _

theorem weakToSym_injective (r q : ℕ) :
    Function.Injective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro z w h
  apply Subtype.ext
  apply List.ofFn_injective
  have hp : (List.ofFn z.val).Perm (List.ofFn w.val) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [TauCeti.Sym.coe_ofFn] using
      congrArg (fun x : Sym (Fin (q+1)) r => (x : Multiset (Fin (q+1)))) h
  exact hp.eq_of_pairwise' z.property.sortedLE_ofFn.pairwise w.property.sortedLE_ofFn.pairwise

theorem weakToSym_surjective (r q : ℕ) :
    Function.Surjective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro s
  let L := (s : Multiset (Fin (q+1))).sort
  have hl : L.length=r := by simp [L, s.property]
  let f : Fin r → Fin (q+1) := fun i => L[i.val]'(by rw [hl]; exact i.isLt)
  have hf : List.ofFn f=L := by
    apply List.ext_getElem
    · simp [hl]
    · intro i hi hi'
      simp [f]
  have hmono : Monotone f := by
    apply List.sortedLE_ofFn_iff.mp
    rw [hf]
    exact (Multiset.pairwise_sort _ _).sortedLE
  refine ⟨⟨f,hmono⟩, ?_⟩
  change TauCeti.Sym.ofFn f=s
  apply Sym.coe_injective
  rw [TauCeti.Sym.coe_ofFn, hf]
  exact Multiset.sort_eq _ _

def weakSymEquiv (r q : ℕ) : WeakWord r q ≃ Sym (Fin (q+1)) r :=
  Equiv.ofBijective (fun z => TauCeti.Sym.ofFn z.val)
    ⟨weakToSym_injective r q, weakToSym_surjective r q⟩

/-- The actual indexing equivalence underlying the plethysm in Corollary 5.2. -/
def interlacingSymEquiv (p q : ℕ) : Interlacing p q ≃ Sym (Fin (q+1)) (2*p+1) :=
  (interlacingWeakEquiv p q).trans (weakSymEquiv (2*p+1) q)

theorem interlacing_card (p q : ℕ) :
    Fintype.card (Interlacing p q) = (2*p+q+1).choose q := by
  rw [Fintype.card_congr (interlacingSymEquiv p q), Sym.card_sym_eq_multichoose,
    Fintype.card_fin, Nat.multichoose_eq]
  rw [show q+1+(2*p+1)-1=2*p+q+1 by omega]
  simpa only [show 2*p+q+1-q=2*p+1 by omega] using
    (Nat.choose_symm (show q≤2*p+q+1 by omega))

end PaperVerification.AlternatingForms.TopInterlacing
