module
public import Papers.GPActualBoundaryExclusion
public import GPGeometry.Relations
public import GPGeometry.Cases.C000
public import GPGeometry.Cases.C001
public import GPGeometry.Cases.C002
public import GPGeometry.Cases.C003
public import GPGeometry.Cases.C004
public import GPGeometry.Cases.C005
public import GPGeometry.Cases.C006
public import GPGeometry.Cases.C007
public import GPGeometry.Cases.C008
public import GPGeometry.Cases.C009
public import GPGeometry.Cases.C010
public import GPGeometry.Cases.C011
public import GPGeometry.Cases.C012
public import GPGeometry.Cases.C013
public import GPGeometry.Cases.C014
public import GPGeometry.Cases.C015
public import GPGeometry.Cases.C016
public import GPGeometry.Cases.C017
public import GPGeometry.Cases.C018
public import GPGeometry.Cases.C019
public import GPGeometry.Cases.C020
public import GPGeometry.Cases.C021
public import GPGeometry.Cases.C022
public import GPGeometry.Cases.C023
public import GPGeometry.Cases.C024
public import GPGeometry.Cases.C025
public import GPGeometry.Cases.C026
public import GPGeometry.Cases.C027
public import GPGeometry.Cases.C028
public import GPGeometry.Cases.C029
public import GPGeometry.Cases.C030
public import GPGeometry.Cases.C031
public import GPGeometry.Cases.C032
public import GPGeometry.Cases.C033
public import GPGeometry.Cases.C034
public import GPGeometry.Cases.C035
public import GPGeometry.Cases.C036
public import GPGeometry.Cases.C037
public import GPGeometry.Cases.C038
public import GPGeometry.Cases.C039
public import GPGeometry.Cases.C040
public import GPGeometry.Cases.C041
public import GPGeometry.Cases.C042
public import GPGeometry.Cases.C043
public import GPGeometry.Cases.C044

@[expose] public section
noncomputable section
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
namespace Papers.RationalityTen.GPFiniteGeometry.Literal
/- Each statement below concerns an actual full-dimensional polytope.
   It has no supplied sign, rank, chart, or abstract oriented-matroid premise.
   All source remains pending the common Lean check. -/

theorem C000.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C000.boundary) : False :=
  C000.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C000.support_sign_contradiction

theorem C001.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C001.boundary) : False :=
  C001.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C001.support_sign_contradiction

theorem C002.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C002.boundary) : False :=
  C002.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C002.support_sign_contradiction

theorem C003.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C003.boundary) : False :=
  C003.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C003.support_sign_contradiction

theorem C004.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C004.boundary) : False :=
  C004.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C004.support_sign_contradiction

theorem C005.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C005.boundary) : False :=
  C005.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C005.support_sign_contradiction

theorem C006.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C006.boundary) : False :=
  C006.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C006.support_sign_contradiction

theorem C007.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C007.boundary) : False :=
  C007.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C007.support_sign_contradiction

theorem C008.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C008.boundary) : False :=
  C008.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C008.support_sign_contradiction

theorem C009.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C009.boundary) : False :=
  C009.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C009.support_sign_contradiction

theorem C010.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C010.boundary) : False :=
  C010.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C010.support_sign_contradiction

theorem C011.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C011.boundary) : False :=
  C011.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C011.support_sign_contradiction

theorem C012.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C012.boundary) : False :=
  C012.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C012.support_sign_contradiction

theorem C013.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C013.boundary) : False :=
  C013.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C013.support_sign_contradiction

theorem C014.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C014.boundary) : False :=
  C014.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C014.support_sign_contradiction

theorem C015.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C015.boundary) : False :=
  C015.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C015.support_sign_contradiction

theorem C016.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C016.boundary) : False :=
  C016.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C016.support_sign_contradiction

theorem C017.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C017.boundary) : False :=
  C017.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C017.support_sign_contradiction

theorem C018.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C018.boundary) : False :=
  C018.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C018.support_sign_contradiction

theorem C019.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C019.boundary) : False :=
  C019.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C019.support_sign_contradiction

theorem C020.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C020.boundary) : False :=
  C020.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C020.support_sign_contradiction

theorem C021.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C021.boundary) : False :=
  C021.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C021.support_sign_contradiction

theorem C022.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C022.boundary) : False :=
  C022.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C022.support_sign_contradiction

theorem C023.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C023.boundary) : False :=
  C023.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C023.support_sign_contradiction

theorem C024.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C024.boundary) : False :=
  C024.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C024.support_sign_contradiction

theorem C025.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C025.boundary) : False :=
  C025.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C025.support_sign_contradiction

theorem C026.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C026.boundary) : False :=
  C026.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C026.support_sign_contradiction

theorem C027.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C027.boundary) : False :=
  C027.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C027.support_sign_contradiction

theorem C028.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C028.boundary) : False :=
  C028.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C028.support_sign_contradiction

theorem C029.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C029.boundary) : False :=
  C029.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C029.support_sign_contradiction

theorem C030.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C030.boundary) : False :=
  C030.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C030.support_sign_contradiction

theorem C031.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C031.boundary) : False :=
  C031.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C031.support_sign_contradiction

theorem C032.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C032.boundary) : False :=
  C032.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C032.support_sign_contradiction

theorem C033.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C033.boundary) : False :=
  C033.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C033.support_sign_contradiction

theorem C034.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C034.boundary) : False :=
  C034.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C034.support_sign_contradiction

theorem C035.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C035.boundary) : False :=
  C035.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C035.support_sign_contradiction

theorem C036.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C036.boundary) : False :=
  C036.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C036.support_sign_contradiction

theorem C037.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C037.boundary) : False :=
  C037.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C037.support_sign_contradiction

theorem C038.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C038.boundary) : False :=
  C038.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C038.support_sign_contradiction

theorem C039.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C039.boundary) : False :=
  C039.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C039.support_sign_contradiction

theorem C040.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C040.boundary) : False :=
  C040.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C040.support_sign_contradiction

theorem C041.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C041.boundary) : False :=
  C041.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C041.support_sign_contradiction

theorem C042.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C042.boundary) : False :=
  C042.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C042.support_sign_contradiction

theorem C043.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C043.boundary) : False :=
  C043.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C043.support_sign_contradiction

theorem C044.no_actual_boundary
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (hB : RealizesBoundary P lab C044.boundary) : False :=
  C044.geometry.no_actual_realization hP hB allRelations
    Papers.RationalityTen.PureGP.Initializers.C044.support_sign_contradiction

end Papers.RationalityTen.GPFiniteGeometry.Literal
