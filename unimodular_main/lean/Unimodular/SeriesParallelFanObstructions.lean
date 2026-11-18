module

public import Unimodular.RankThreeMinors
public import Unimodular.SeriesParallelIntegral
public import Unimodular.SeriesParallelPivot
public import Unimodular.RayContractions

@[expose] public section

open scoped BigOperators Pointwise Topology
open Set TauCeti.Toric

namespace Unimodular.SeriesParallel

noncomputable section

/-- Encode a nonzero ternary integer by an actual sign. -/
def coefficientSign (z : ℤ) : Bool := decide (z = -1)

lemma coefficientSign_eq {z : ℤ} (hb : |z| ≤ 1) (hz : z ≠ 0) :
    (RankThree.signUnit (coefficientSign z) : ℤ) = z := by
  have he : z = 1 ∨ z = -1 := by have := abs_le.mp hb; omega
  rcases he with rfl | rfl <;> norm_num [coefficientSign, RankThree.signUnit]

/-- A finite-coordinate determinant identity is transported back to the full
integral basis determinant, with every quantifier over column selections. -/
lemma dependence_pattern_of_coordinates {N : Type*} [AddCommGroup N] [Module ℤ N]
    (b : Module.Basis (Fin 3) ℤ N) (W : Fin 6 → N) (C : Fin 6 → Lattice 3)
    (hcoord : ∀ j, b.equivFun (W j) = C j)
    (hfinite : ∀ i j k, detThree (C i) (C j) (C k) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0) :
    ∀ a : Fin 3 → Fin 6,
      b.det (W ∘ a) = 0 ↔
        (Pi.basisFun ℤ (Fin 3)).det (RankThree.baseRoot ∘ a) = 0 := by
  intro a
  rw [RankThree.det_eq_coordinate_rows, Pi.basisFun_det_apply]
  have he : (fun i => b.equivFun ((W ∘ a) i)) = C ∘ a := by
    funext i
    exact hcoord (a i)
  rw [he]
  have ha : a = ![a 0, a 1, a 2] := by
    funext i
    fin_cases i <;> rfl
  have hleft : C ∘ a = ![C (a 0), C (a 1), C (a 2)] := by
    funext i
    fin_cases i <;> rfl
  have hright : RankThree.baseRoot ∘ a =
      ![RankThree.baseRoot (a 0), RankThree.baseRoot (a 1), RankThree.baseRoot (a 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright, ← detThree_eq, ← detThree_eq]
  exact hfinite _ _ _

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- A positive-criterion fan of rank three cannot have a ray basis and one ray
on each of the three two-coordinate supports. All signs are unrestricted. -/
theorem fan_no_triangle_support (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis (Fin 3) ℤ N)
    (hb : ∀ i, ConeBases.IsRay Φ (b i)) (v₀ v₁ v₂ : N)
    (hv₀ : ConeBases.IsRay Φ v₀) (hv₁ : ConeBases.IsRay Φ v₁)
    (hv₂ : ConeBases.IsRay Φ v₂)
    (hs₀ : ∀ i, b.repr v₀ i ≠ 0 ↔ i = 0 ∨ i = 1)
    (hs₁ : ∀ i, b.repr v₁ i ≠ 0 ↔ i = 0 ∨ i = 2)
    (hs₂ : ∀ i, b.repr v₂ i ≠ 0 ↔ i = 1 ∨ i = 2) : False := by
  classical
  let R : Set N := {u | ConeBases.IsRay Φ u}
  have hU := FanBridge.uniform_of_positiveCriterion Φ hcomplete hregular hcriterion b
  have habs (v : N) (hv : ConeBases.IsRay Φ v) (i : Fin 3) : |b.repr v i| ≤ 1 :=
    Heller.coordinate_abs_le_one b R hU hb hv i
  let s : Fin 6 → Bool := ![coefficientSign (b.repr v₀ 0), coefficientSign (b.repr v₀ 1),
    coefficientSign (b.repr v₁ 0), coefficientSign (b.repr v₁ 2),
    coefficientSign (b.repr v₂ 1), coefficientSign (b.repr v₂ 2)]
  have h₀₀ := coefficientSign_eq (habs v₀ hv₀ 0) ((hs₀ 0).mpr (Or.inl rfl))
  have h₀₁ := coefficientSign_eq (habs v₀ hv₀ 1) ((hs₀ 1).mpr (Or.inr rfl))
  have h₁₀ := coefficientSign_eq (habs v₁ hv₁ 0) ((hs₁ 0).mpr (Or.inl rfl))
  have h₁₂ := coefficientSign_eq (habs v₁ hv₁ 2) ((hs₁ 2).mpr (Or.inr rfl))
  have h₂₁ := coefficientSign_eq (habs v₂ hv₂ 1) ((hs₂ 1).mpr (Or.inl rfl))
  have h₂₂ := coefficientSign_eq (habs v₂ hv₂ 2) ((hs₂ 2).mpr (Or.inr rfl))
  have hz₀ : b.repr v₀ 2 = 0 := by simpa using not_congr (hs₀ 2)
  have hz₁ : b.repr v₁ 1 = 0 := by simpa using not_congr (hs₁ 1)
  have hz₂ : b.repr v₂ 0 = 0 := by simpa using not_congr (hs₂ 0)
  let W : Fin 6 → N := ![b 0, b 1, b 2, v₀, v₁, v₂]
  have hcoord : ∀ j, b.equivFun (W j) = RankThree.signedColumns s j := by
    intro j
    funext i
    fin_cases j <;> fin_cases i <;>
      simp [W, RankThree.signedColumns, s, Module.Basis.equivFun_self,
        Module.Basis.equivFun_apply, h₀₀, h₀₁, h₁₀, h₁₂, h₂₁, h₂₂, hz₀, hz₁, hz₂]
  have hW : ∀ j, ConeBases.IsRay Φ (W j) := by
    intro j
    fin_cases j
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact hv₀
    · exact hv₁
    · exact hv₂
  have hdet : ∀ a : Fin 3 → Fin 6, |b.det (W ∘ a)| ≤ 1 := by
    intro a
    exact hU (fun i => ⟨W (a i), hW (a i)⟩)
  have hC : |detThree (RankThree.signedColumns s 3)
      (RankThree.signedColumns s 4) (RankThree.signedColumns s 5)| ≤ 1 := by
    have hd := hdet ![3, 4, 5]
    rw [RankThree.det_eq_coordinate_rows] at hd
    rw [detThree_eq]
    convert hd using 2
    congr 1
    ext i j
    fin_cases i
    · simpa [Matrix.of_apply, Function.comp_def] using congrFun (hcoord 3).symm j
    · simpa [Matrix.of_apply, Function.comp_def] using congrFun (hcoord 4).symm j
    · simpa [Matrix.of_apply, Function.comp_def] using congrFun (hcoord 5).symm j
  apply RankThree.fan_no_K4_dependence_pattern Φ hcomplete hregular hcriterion b W hW
  exact dependence_pattern_of_coordinates b W (RankThree.signedColumns s) hcoord
    (triangle_uniform_has_K4_pattern s hC)

/-- The rank-three domino obstruction, with all seven integral signs free. -/
theorem fan_no_domino_support (Φ : Fan ι)
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)
    (hcriterion : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis (Fin 3) ℤ N)
    (hb : ∀ i, ConeBases.IsRay Φ (b i)) (v₀ v₁ v₂ : N)
    (hv₀ : ConeBases.IsRay Φ v₀) (hv₁ : ConeBases.IsRay Φ v₁)
    (hv₂ : ConeBases.IsRay Φ v₂)
    (hs₀ : ∀ i, b.repr v₀ i ≠ 0 ↔ i = 0 ∨ i = 1)
    (hs₁ : ∀ i, b.repr v₁ i ≠ 0)
    (hs₂ : ∀ i, b.repr v₂ i ≠ 0 ↔ i = 1 ∨ i = 2) : False := by
  classical
  let R : Set N := {u | ConeBases.IsRay Φ u}
  have hU := FanBridge.uniform_of_positiveCriterion Φ hcomplete hregular hcriterion b
  have habs (v : N) (hv : ConeBases.IsRay Φ v) (i : Fin 3) : |b.repr v i| ≤ 1 :=
    Heller.coordinate_abs_le_one b R hU hb hv i
  let s : Fin 7 → Bool := ![coefficientSign (b.repr v₀ 0), coefficientSign (b.repr v₀ 1),
    coefficientSign (b.repr v₁ 0), coefficientSign (b.repr v₁ 1), coefficientSign (b.repr v₁ 2),
    coefficientSign (b.repr v₂ 1), coefficientSign (b.repr v₂ 2)]
  have h₀₀ := coefficientSign_eq (habs v₀ hv₀ 0) ((hs₀ 0).mpr (Or.inl rfl))
  have h₀₁ := coefficientSign_eq (habs v₀ hv₀ 1) ((hs₀ 1).mpr (Or.inr rfl))
  have h₁₀ := coefficientSign_eq (habs v₁ hv₁ 0) (hs₁ 0)
  have h₁₁ := coefficientSign_eq (habs v₁ hv₁ 1) (hs₁ 1)
  have h₁₂ := coefficientSign_eq (habs v₁ hv₁ 2) (hs₁ 2)
  have h₂₁ := coefficientSign_eq (habs v₂ hv₂ 1) ((hs₂ 1).mpr (Or.inl rfl))
  have h₂₂ := coefficientSign_eq (habs v₂ hv₂ 2) ((hs₂ 2).mpr (Or.inr rfl))
  have hz₀ : b.repr v₀ 2 = 0 := by simpa using not_congr (hs₀ 2)
  have hz₂ : b.repr v₂ 0 = 0 := by simpa using not_congr (hs₂ 0)
  let W : Fin 6 → N := ![b 0, b 1, b 2, v₀, v₁, v₂]
  have hcoord : ∀ j, b.equivFun (W j) = dominoColumns s j := by
    intro j
    funext i
    fin_cases j <;> fin_cases i <;>
      simp [W, dominoColumns, s, Module.Basis.equivFun_self,
        Module.Basis.equivFun_apply,
        h₀₀, h₀₁, h₁₀, h₁₁, h₁₂, h₂₁, h₂₂, hz₀, hz₂]
  have hW : ∀ j, ConeBases.IsRay Φ (W j) := by
    intro j
    fin_cases j
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact hv₀
    · exact hv₁
    · exact hv₂
  have hD : ∀ i j k, |detThree (dominoColumns s i) (dominoColumns s j)
      (dominoColumns s k)| ≤ 1 := by
    intro i j k
    have hd := hU (fun a : Fin 3 =>
      (⟨W (![i, j, k] a), hW _⟩ : {u // ConeBases.IsRay Φ u}))
    rw [RankThree.det_eq_coordinate_rows] at hd
    rw [detThree_eq]
    convert hd using 2
    congr 1
    ext a r
    fin_cases a <;> exact congrFun (hcoord _).symm r
  apply RankThree.fan_no_K4_dependence_pattern Φ hcomplete hregular hcriterion b
    (W ∘ dominoReindex) (fun j => hW (dominoReindex j))
  exact dependence_pattern_of_coordinates b (W ∘ dominoReindex)
    (dominoColumns s ∘ dominoReindex) (fun j => hcoord (dominoReindex j))
    (domino_uniform_has_K4_pattern s hD)

end
end Unimodular.SeriesParallel
