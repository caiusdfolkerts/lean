module

public import PaperVerification.E6UnscaledTheorems
public import PaperVerification.LatticeScaling
public import Mathlib.Data.Fin.Basic

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triTripleFlatten (z : TriTriple) (j : Fin 6) : ℝ :=
  Fin.addCases (m:=3) (n:=3) (motive:=fun _ ↦ ℝ)
    (fun i : Fin 3 ↦ (z i).1-(z i).2/2)
    (fun i : Fin 3 ↦ Real.sqrt 3*(z i).2/2) j

def triTripleUnflatten (x : Fin 6 → ℝ) : TriTriple := fun i ↦
  (x (Fin.castAdd 3 i)+x (Fin.natAdd 3 i)/Real.sqrt 3,
    2*x (Fin.natAdd 3 i)/Real.sqrt 3)

theorem triTripleUnflatten_flatten (z : TriTriple) :
    triTripleUnflatten (triTripleFlatten z)=z := by
  have hs : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  ext i <;> simp [triTripleUnflatten,triTripleFlatten,hs, -Fin.natAdd_eq_addNat] <;>
    field_simp <;> ring

theorem triTripleFlatten_unflatten (x : Fin 6 → ℝ) :
    triTripleFlatten (triTripleUnflatten x)=x := by
  have hs : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j
  all_goals
    simp [triTripleUnflatten,triTripleFlatten,hs, -Fin.natAdd_eq_addNat] <;>
      field_simp <;> ring

def triTripleEuclideanEquiv : TriTriple ≃ (Fin 6 → ℝ) where
  toFun := triTripleFlatten
  invFun := triTripleUnflatten
  left_inv := triTripleUnflatten_flatten
  right_inv := triTripleFlatten_unflatten

theorem triTripleFlatten_sqDist (z w : TriTriple) :
    sqDist (triTripleFlatten z) (triTripleFlatten w)=triTripleSqDist z w := by
  unfold sqDist triTripleSqDist
  rw [Fin.sum_univ_add (a:=3) (b:=3),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [triTripleFlatten,Fin.addCases_left,Fin.addCases_right]
  have h3 : Real.sqrt 3^2=(3:ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [triQ]
  nlinarith only [congrArg (fun t : ℝ ↦ t*((z i).2-(w i).2)^2) h3]

def l6EuclideanSet : Set (Fin 6 → ℝ) := triTripleFlatten '' l6Set

theorem l6EuclideanSet_nonempty : l6EuclideanSet.Nonempty :=
  ⟨triTripleFlatten (l6Point (0,0)),l6Point (0,0),⟨(0,0),rfl⟩,rfl⟩

def l6EuclideanIndexEquiv : E6Index ≃ l6EuclideanSet :=
  Equiv.ofBijective (fun p ↦ ⟨triTripleFlatten (l6Point p),l6Point p,⟨p,rfl⟩,rfl⟩)
    ⟨fun p q h ↦ l6Point_injective (triTripleEuclideanEquiv.injective
      (congrArg Subtype.val h)),by
      rintro ⟨x,z,⟨p,rfl⟩,rfl⟩
      exact ⟨p,rfl⟩⟩

theorem setGaussian_l6Euclidean (α : ℝ) (z : TriTriple) :
    setGaussian l6EuclideanSet α (triTripleFlatten z)=l6Gaussian α z := by
  unfold setGaussian l6Gaussian
  rw [← l6EuclideanIndexEquiv.tsum_eq]
  apply tsum_congr
  intro p
  exact congrArg (fun t : ℝ ↦ Real.exp (-α*t)) (triTripleFlatten_sqDist (l6Point p) z)

theorem squaredDepth_l6Euclidean (z : TriTriple) :
    squaredDepth l6EuclideanSet (triTripleFlatten z)=l6Depth z := by
  unfold squaredDepth l6Depth
  congr 1
  ext t
  constructor
  · rintro ⟨x,⟨w,⟨p,rfl⟩,rfl⟩,rfl⟩
    refine ⟨p,?_⟩
    change triTripleSqDist (l6Point p) z =
      sqDist (triTripleFlatten z) (triTripleFlatten (l6Point p))
    rw [sqDist_comm,triTripleFlatten_sqDist]
  · rintro ⟨p,rfl⟩
    refine ⟨triTripleFlatten (l6Point p),⟨l6Point p,⟨p,rfl⟩,rfl⟩,?_⟩
    change sqDist (triTripleFlatten z) (triTripleFlatten (l6Point p)) =
      triTripleSqDist (l6Point p) z
    rw [sqDist_comm,triTripleFlatten_sqDist]

theorem isColdSpot_l6Euclidean_iff (α : ℝ) (z : TriTriple) :
    IsColdSpot l6EuclideanSet α (triTripleFlatten z) ↔ IsL6ColdSpot α z := by
  constructor
  · intro h w
    simpa only [setGaussian_l6Euclidean] using h (triTripleFlatten w)
  · intro h x
    obtain ⟨w,rfl⟩ := triTripleEuclideanEquiv.surjective x
    change setGaussian l6EuclideanSet α (triTripleFlatten z) ≤
      setGaussian l6EuclideanSet α (triTripleFlatten w)
    simpa only [setGaussian_l6Euclidean] using h w

theorem isDeepHole_l6Euclidean_iff (z : TriTriple) :
    IsDeepHole l6EuclideanSet (triTripleFlatten z) ↔ IsL6DeepHole z := by
  constructor
  · intro h w
    simpa only [squaredDepth_l6Euclidean] using h (triTripleFlatten w)
  · intro h x
    obtain ⟨w,rfl⟩ := triTripleEuclideanEquiv.surjective x
    change squaredDepth l6EuclideanSet (triTripleFlatten w) ≤
      squaredDepth l6EuclideanSet (triTripleFlatten z)
    simpa only [squaredDepth_l6Euclidean] using h w

/-- The root-normalized lattice √2(E³+ℤ(c,c,c)), in ordinary Euclidean R⁶. -/
def e6Set : Set (Fin 6 → ℝ) := scaledSet (Real.sqrt 2) l6EuclideanSet

def e6PhysicalPoint (z : TriTriple) : Fin 6 → ℝ := scaleVec (Real.sqrt 2) (triTripleFlatten z)

theorem e6PhysicalPoint_surjective : Function.Surjective e6PhysicalPoint := by
  intro x
  refine ⟨triTripleUnflatten (scaleVec (Real.sqrt 2)⁻¹ x),?_⟩
  rw [e6PhysicalPoint,triTripleFlatten_unflatten,scaleVec_inv _ (by positivity)]

theorem e6Gaussian_scale (α : ℝ) (z : TriTriple) :
    setGaussian e6Set α (e6PhysicalPoint z)=l6Gaussian (2*α) z := by
  unfold e6Set e6PhysicalPoint
  rw [setGaussian_scaled _ (by positivity),Real.sq_sqrt (by norm_num),setGaussian_l6Euclidean]
  congr 1
  ring

theorem e6Depth_scale (z : TriTriple) :
    squaredDepth e6Set (e6PhysicalPoint z)=2*l6Depth z := by
  unfold e6Set e6PhysicalPoint
  rw [squaredDepth_scaled _ (by positivity) _ l6EuclideanSet_nonempty,
    Real.sq_sqrt (by norm_num),squaredDepth_l6Euclidean]

theorem coldSpot_E6_iff_deepHole {α : ℝ} (hα : 0 < α) (x : Fin 6 → ℝ) :
    IsColdSpot e6Set α x ↔ IsDeepHole e6Set x := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  unfold e6Set e6PhysicalPoint
  rw [isColdSpot_scaled_iff _ (by positivity),
    isDeepHole_scaled_iff _ (by positivity) _ l6EuclideanSet_nonempty,
    Real.sq_sqrt (by norm_num),isColdSpot_l6Euclidean_iff,isDeepHole_l6Euclidean_iff]
  exact coldSpot_L6_iff_deepHole (by positivity) z

theorem e6_covering_radius_squared (x : Fin 6 → ℝ) : squaredDepth e6Set x ≤ 4/3 := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  rw [e6Depth_scale]
  have h := l6Depth_upper z
  linarith

theorem e6_covering_radius_attained :
    squaredDepth e6Set (e6PhysicalPoint e6HoleWitness)=4/3 := by
  rw [e6Depth_scale,l6Depth_witness]
  norm_num

theorem e6_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, 3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 ≤
      setGaussian e6Set α x) ∧
    setGaussian e6Set α (e6PhysicalPoint e6HoleWitness)=
      3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 := by
  constructor
  · intro x
    obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
    rw [e6Gaussian_scale]
    exact l6Gaussian_lower (by positivity) z
  · rw [e6Gaussian_scale]
    exact l6Gaussian_witness (by positivity)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_E6_iff_deepHole
#print axioms PaperVerification.ColdSpots.e6_gaussian_minimum
