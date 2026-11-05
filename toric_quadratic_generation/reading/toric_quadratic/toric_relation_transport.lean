module

public import PaperVerification.ToricPrimitiveRelations

@[expose] public section

/-!
# Transport of actual primitive relations across equal focus stars

Only the cone-membership proofs change. The positive/negative ray sets,
integer coefficients and lattice equation are literally retained.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» Γ : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem degree_congr_on_rays (a b : Lattice n → ℝ)
    (hP : ∀ v ∈ R.positive, a v = b v)
    (hN : ∀ v ∈ R.negative, a v = b v) : R.degree a = R.degree b := by
  unfold degree
  congr 1
  · exact Finset.sum_congr rfl hP
  · exact Finset.sum_congr rfl (fun v hv => congrArg ((R.coefficient v : ℝ) * ·) (hN v hv))

theorem degree_change_one_negative (a b : Lattice n → ℝ)
    (e : Lattice n) (he : e ∈ R.negative) (t : ℝ)
    (hP : ∀ v ∈ R.positive, a v = b v)
    (hN : ∀ v ∈ R.negative.erase e, a v = b v)
    (heq : a e = b e - t) :
    R.degree a = R.degree b + (R.coefficient e : ℝ) * t := by
  have hpos : (∑ v ∈ R.positive, a v) = ∑ v ∈ R.positive, b v :=
    Finset.sum_congr rfl hP
  have hneg : (∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * a v) =
      ∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * b v :=
    Finset.sum_congr rfl (fun v hv => congrArg ((R.coefficient v : ℝ) * ·) (hN v hv))
  unfold degree
  rw [hpos, ← Finset.add_sum_erase R.negative
    (fun v => (R.coefficient v : ℝ) * a v) he,
    ← Finset.add_sum_erase R.negative (fun v => (R.coefficient v : ℝ) * b v) he,
    hneg, heq]
  ring

def copyToFan (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones) :
    Γ.PrimitiveRelation :=
  ⟨R.positive, R.negative, R.coefficient, hP, hN, R.coefficient_pos, R.equation⟩

@[simp] theorem copyToFan_degree (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones)
    (a : Lattice n → ℝ) :
    (R.copyToFan Γ hP hN).degree a = R.degree a := rfl

theorem copyToFan_contractible
    (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones)
    (hstars : ∀ s : Finset (Lattice n), R.negative ⊆ s →
      (s ∈ «Σ».cones ↔ s ∈ Γ.cones))
    (hR : R.IsCombinatoriallyContractible) :
    (R.copyToFan Γ hP hN).IsCombinatoriallyContractible := by
  intro ν hν hdisj hNν x hx
  have hNνold := (hstars (R.negative ∪ ν) Finset.subset_union_left).mpr hNν
  have hνold := «Σ».downward _ hNνold ν Finset.subset_union_right
  have hreplace := hR ν hνold hdisj hNνold x hx
  exact (hstars (R.positive.erase x ∪ R.negative ∪ ν)
    (Finset.subset_union_right.trans Finset.subset_union_left)).mp hreplace

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
