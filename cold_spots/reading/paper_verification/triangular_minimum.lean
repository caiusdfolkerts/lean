module
public import PaperVerification.TriangularPhases
public import PaperVerification.TriangularMaximum
public import PaperVerification.ThreeTermAMGM
public import Mathlib.Topology.Order.Compact
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem triangularProduct_pos {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    0 < triangularProduct α z :=
  mul_pos (mul_pos (triangularGaussian_pos hα _) (triangularGaussian_pos hα _))
    (triangularGaussian_pos hα _)

theorem continuous_triangularProduct {α : ℝ} (hα : 0 < α) :
    Continuous (triangularProduct α) :=
  ((continuous_triangularGaussian hα).mul
    ((continuous_triangularGaussian hα).comp (continuous_id.add continuous_const))).mul
      ((continuous_triangularGaussian hα).comp (continuous_id.sub continuous_const))

theorem triangularProduct_attains_minimum {α : ℝ} (hα : 0 < α) :
    ∃ z : TriPoint, ∀ w, triangularProduct α z ≤ triangularProduct α w := by
  have hc := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).prod
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  have hn : ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)).Nonempty :=
    ⟨(0,0),by norm_num⟩
  obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn hn (continuous_triangularProduct hα).continuousOn
  refine ⟨z,fun w ↦ ?_⟩
  have h := hmin (triFraction_mem w)
  rw [← triFraction_add_floor w,triangularProduct_periodic]
  exact h

theorem triangularProduct_cubic_bound {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    (triangularGaussian α 0 * triangularGaussian α triC ^ 2)^2 *
      triangularProduct α (triTheta z) ≤ triangularProduct α z ^ 3 := by
  let a := triangularGaussian α 0
  let b := triangularGaussian α triC
  let x := a * triangularGaussian α (triTheta z+triC)
  let y := a * triangularGaussian α (triTheta z-triC)
  let w := b * triangularGaussian α (triTheta z)
  have ha : 0 < a := triangularGaussian_pos hα _
  have hb : 0 < b := triangularGaussian_pos hα _
  have hx : 0 < x := mul_pos ha (triangularGaussian_pos hα _)
  have hy : 0 < y := mul_pos ha (triangularGaussian_pos hα _)
  have hw : 0 < w := mul_pos hb (triangularGaussian_pos hα _)
  have h := (three_term_amgm x y w hx.le hy.le hw.le).1
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ b^3/27 by positivity)
  have he : triangularProduct α z = b/3*(x+y+w) := by
    rw [triangular_cubic_identity hα]
    dsimp [a,b,x,y,w]
    ring
  rw [he]
  dsimp [a,b,x,y,w,triangularProduct] at hm ⊢
  nlinarith only [hm]

/-- The sharp scalar lower bound in Proposition 8.1 for every physical point. -/
theorem triangularProduct_minimum {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α 0 * triangularGaussian α triC ^ 2 ≤ triangularProduct α z := by
  obtain ⟨w,hw⟩ := triangularProduct_attains_minimum hα
  let K := triangularGaussian α 0 * triangularGaussian α triC ^ 2
  have hK : 0 < K := mul_pos (triangularGaussian_pos hα _) (sq_pos_of_pos (triangularGaussian_pos hα _))
  have hm : 0 < triangularProduct α w := triangularProduct_pos hα _
  have h := triangularProduct_cubic_bound hα w
  have h' := hw (triTheta w)
  have hp := mul_le_mul_of_nonneg_left h' (sq_nonneg K)
  have hsq : K^2 ≤ triangularProduct α w ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    calc
      K^2*triangularProduct α w ≤ K^2*triangularProduct α (triTheta w) := hp
      _ ≤ triangularProduct α w^3 := h
      _ = triangularProduct α w^2*triangularProduct α w := by ring
  have hle : K ≤ triangularProduct α w := (sq_le_sq₀ hK.le hm.le).mp hsq
  exact hle.trans (hw z)

theorem triangularProduct_equality_iff {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularProduct α z = triangularGaussian α 0 * triangularGaussian α triC ^ 2 ↔
      TriPhase z := by
  constructor
  · intro heq
    let a := triangularGaussian α 0
    let b := triangularGaussian α triC
    let x := a * triangularGaussian α (triTheta z+triC)
    let y := a * triangularGaussian α (triTheta z-triC)
    let w := b * triangularGaussian α (triTheta z)
    have ha : 0 < a := triangularGaussian_pos hα _
    have hb : 0 < b := triangularGaussian_pos hα _
    have hx : 0 < x := mul_pos ha (triangularGaussian_pos hα _)
    have hy : 0 < y := mul_pos ha (triangularGaussian_pos hα _)
    have hw : 0 < w := mul_pos hb (triangularGaussian_pos hα _)
    have htheta : triangularProduct α (triTheta z) = a*b^2 := by
      apply le_antisymm
      · have h := triangularProduct_cubic_bound hα z
        rw [heq] at h
        apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos (mul_pos ha (sq_pos_of_pos hb)))).mp
        calc
          (a*b^2)^2*triangularProduct α (triTheta z) ≤ (a*b^2)^3 := h
          _ = (a*b^2)^2*(a*b^2) := by ring
      · exact triangularProduct_minimum hα _
    have hsum : x+y+w = 3*a*b := by
      have hc : triangularProduct α z=b/3*(x+y+w) := by
        rw [triangular_cubic_identity hα]
        dsimp [a,b,x,y,w]
        ring
      have he : a*b^2=b/3*(x+y+w) := heq.symm.trans hc
      apply mul_left_cancel₀ hb.ne'
      calc
        b*(x+y+w)=3*(b/3*(x+y+w)) := by ring
        _ = 3*(a*b^2) := congrArg (fun t : ℝ ↦ 3*t) he.symm
        _ = b*(3*a*b) := by ring
    have hprod : x*y*w = a^3*b^3 := by
      have hp : x*y*w = a^2*b*triangularProduct α (triTheta z) := by
        dsimp [x,y,w,triangularProduct]
        ring
      rw [hp,htheta]
      ring
    have he : (x+y+w)^3 = 27*(x*y*w) := by rw [hsum,hprod]; ring
    have hequal := (three_term_amgm x y w hx.le hy.le hw.le).2.mp he
    have hwval : w = a*b := by linarith
    have hF : triangularGaussian α (triTheta z) = a := by
      apply mul_left_cancel₀ hb.ne'
      calc
        b*triangularGaussian α (triTheta z)=w := rfl
        _ = a*b := hwval
        _ = b*a := mul_comm _ _
    exact (triPhase_iff_theta_integral z).mpr ((triangularGaussian_maximum_iff hα _).mp hF)
  · intro hz
    exact triangularProduct_phase α hz

end PaperVerification.ColdSpots
