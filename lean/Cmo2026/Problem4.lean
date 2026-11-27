module

public import Cmo2026.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

set_option autoImplicit false

@[expose] public section

namespace CMO2026
open EuclideanGeometry
noncomputable def your_answer_to_problem4:Set ℝ :=sorry
def prop_problem4_part1(A B C D:Plane):Prop:=(dist A D)/(dist B C)∈your_answer_to_problem4
def prop_problem4_part2:Prop:=
    ∀x:ℝ,x∈your_answer_to_problem4→(∃(A B C D E F G:Plane)(hQuadrilateral:IsStrictlyConvexQuadrilateral A B C D)(hE:IsSegmentIntersection E A C B D),dist A D=x*(dist B C)∧AffineSubspace.Parallel line[ℝ,A,D]  line[ℝ,B,C]∧
    F∈(Affine.Simplex.mk ![A,B,E] (AffineIndependentInStrictlyConvexQuadrilateral A B C D E hQuadrilateral hE).left).circumsphere∧F∈(Affine.Simplex.mk ![C,D,E] (AffineIndependentInStrictlyConvexQuadrilateral A B C D E hQuadrilateral hE).right).circumsphere∧F≠E∧
    G∈line[ℝ,E,F]∧AffineSubspace.Parallel line[ℝ,A,G] line[ℝ,B,D]∧
    (dist E F)*(dist E G)=(dist E A)^2)
def prop_problem4:Prop:=
    (∀(A B C D E F G:Plane)(hQuadrilateral:IsStrictlyConvexQuadrilateral A B C D)(hE:IsSegmentIntersection E A C B D),
    AffineSubspace.Parallel line[ℝ,A,D]  line[ℝ,B,C]→
    F∈(Affine.Simplex.mk ![A,B,E] (AffineIndependentInStrictlyConvexQuadrilateral A B C D E hQuadrilateral hE).left).circumsphere∧F∈(Affine.Simplex.mk ![C,D,E] (AffineIndependentInStrictlyConvexQuadrilateral A B C D E hQuadrilateral hE).right).circumsphere∧F≠E→
    G∈line[ℝ,E,F]∧AffineSubspace.Parallel line[ℝ,A,G] line[ℝ,B,D]→
    (dist E F)*(dist E G)=(dist E A)^2→
    prop_problem4_part1 A B C D)∧
    prop_problem4_part2
theorem problem4:prop_problem4:=by sorry
end CMO2026
