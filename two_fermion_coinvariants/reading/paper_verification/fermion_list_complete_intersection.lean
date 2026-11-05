module

public import PaperVerification.FermionCompleteIntersectionLength
public import PaperVerification.HomogeneousRegularSequence
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn

/-!
# Complete-intersection length for literal lists of generators

This interface preserves the actual order of a finite generator list and
its corresponding list of homogeneous degrees. It combines the proved
polynomial parameter theorem with the proved Hilbert-series calculation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

theorem ofFn_get_cast {α : Type*} (l : List α) {m : ℕ} (h : l.length = m) :
    List.ofFn (fun i : Fin m ↦ l.get (i.cast h.symm)) = l := by
  subst m
  exact List.ofFn_get l

theorem forall₂_exists_of_mem_left {α β : Type*} {r : α → β → Prop}
    {l : List α} {m : List β} (h : List.Forall₂ r l m) {a : α} (ha : a ∈ l) :
    ∃ b ∈ m, r a b := by
  induction h with
  | nil => simp at ha
  | @cons x y xs ys hxy hrest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- The weighted length formula, with the actual generators and degrees
retained as lists rather than supplied as an assumed Hilbert function. -/
theorem weighted_list_complete_intersection_finrank
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (rs : List P) (degrees : List ℕ) (hlen : rs.length = n)
    (hhom : List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e) rs degrees)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P rs)
    [Module.Finite K (P ⧸ Ideal.ofList rs)] :
    Module.finrank K (P ⧸ Ideal.ofList rs) * (∏ i, w i) = degrees.prod := by
  have hdlen : degrees.length = n := hhom.length_eq.symm.trans hlen
  let f : Fin n → P := fun i ↦ rs.get (i.cast hlen.symm)
  let d : Fin n → ℕ := fun i ↦ degrees.get (i.cast hdlen.symm)
  have hfrs : List.ofFn f = rs := ofFn_get_cast rs hlen
  have hdds : List.ofFn d = degrees := ofFn_get_cast degrees hdlen
  have hfd (i : Fin n) : (f i).IsWeightedHomogeneous w (d i) := by
    exact hhom.get (by simpa only [hlen] using i.isLt)
      (by simpa only [hdlen] using i.isLt)
  have hI : Ideal.span (Set.range f) = Ideal.ofList rs := by
    rw [← hfrs, Ideal.ofList]
    congr 1
    ext p
    exact List.mem_ofFn.symm
  letI : Module.Finite K (P ⧸ Ideal.span (Set.range f)) := by rw [hI]; infer_instance
  have hreg : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f) := by rwa [hfrs]
  have h := weighted_complete_intersection_finrank w hw f d hfd hreg
  have hp : (∏ i, d i) = degrees.prod := by rw [← List.prod_ofFn, hdds]
  have hq := (Ideal.quotientEquivAlgOfEq K hI).toLinearEquiv.finrank_eq
  rw [hq,hp] at h
  exact h

/-- A full positive homogeneous parameter list has the stated length.
Regularity is proved from the actual radical containment and not supplied
as an extra assumption. -/
theorem weighted_list_parameters_finrank
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (rs : List P) (degrees : List ℕ) (hlen : rs.length = n)
    (hhom : List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e) rs degrees)
    (hpositive : ∀ e ∈ degrees, 0 < e)
    (hrad : HomogeneousLocalization.originIdeal (K := K) (ι := Fin n) ≤
      (Ideal.ofList rs).radical)
    [Module.Finite K (P ⧸ Ideal.ofList rs)] :
    Module.finrank K (P ⧸ Ideal.ofList rs) * (∏ i, w i) = degrees.prod := by
  apply weighted_list_complete_intersection_finrank w hw rs degrees hlen hhom
  apply HomogeneousLocalization.homogeneous_parameters_regular w
    (fun i ↦ (hw i).ne') rs
  · intro p hp
    obtain ⟨e, he, hpe⟩ := forall₂_exists_of_mem_left hhom hp
    exact ⟨e, hpe⟩
  · intro p hp
    obtain ⟨e, he, hpe⟩ := forall₂_exists_of_mem_left hhom hp
    rw [HomogeneousLocalization.mem_originIdeal, MvPolynomial.constantCoeff_eq]
    exact hpe.coeff_eq_zero 0 (by simpa using (hpositive e he).ne'.symm)
  · exact hrad
  · simpa only [Fintype.card_fin] using hlen

end PaperVerification.GradedHilbert
