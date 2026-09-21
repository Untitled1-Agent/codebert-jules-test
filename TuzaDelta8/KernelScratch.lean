import TuzaDelta8.FiniteGraph

namespace TuzaDelta8

def allSubsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let ss := allSubsets xs
      ss ++ ss.map (fun s => x :: s)

namespace Edge
def touchesAny (e : Edge) (vs : List Nat) : Bool :=
  vs.contains e.u || vs.contains e.v
end Edge

namespace Tri
def meetsAny (t : Tri) (vs : List Nat) : Bool :=
  vs.contains t.a || vs.contains t.b || vs.contains t.c
end Tri

namespace FGraph

def isTrianglePacking (g : FGraph) (S : List Tri) : Bool :=
  (S.all g.isTriangle) && decide (S.flatMap Tri.edgeList).Nodup

def isTriangleTransversal (g : FGraph) (X : List Edge) : Bool :=
  decide X.Nodup &&
  X.all (fun e => g.edges.contains e) &&
  g.allTriangles.all (fun t => t.edgeList.any (fun e => X.contains e))

def hasTuzaWitness (g : FGraph) : Prop :=
  ∃ S : List Tri, ∃ X : List Edge,
    g.isTrianglePacking S = true ∧
    g.isTriangleTransversal X = true ∧
    X.length ≤ 2 * S.length

/-- Residual after an edge-set reduction: delete every edge in E0 or X. -/
def edgeResidual (g : FGraph) (E0 X : List Edge) : FGraph :=
  ⟨g.n, g.edges.filter (fun e => !E0.contains e && !X.contains e)⟩

/-- Executable edge-set reduction certificate. -/
def isEdgeReductionCertificate (g : FGraph) (E0 : List Edge)
    (S : List Tri) (X : List Edge) : Bool :=
  decide E0.Nodup && decide (E0 ≠ []) &&
  E0.all (fun e => g.edges.contains e) &&
  g.isTrianglePacking S &&
  decide X.Nodup && X.all (fun e => g.edges.contains e) &&
  decide (X.length ≤ 2 * S.length) &&
  g.allTriangles.all (fun t =>
    if t.edgeList.any (fun e => E0.contains e)
    then t.edgeList.any (fun e => X.contains e)
    else true) &&
  S.all (fun t =>
    t.edgeList.all (fun e =>
      if E0.contains e then true else X.contains e))

@[simp] theorem edgeResidual_n (g : FGraph) (E0 X : List Edge) :
    (g.edgeResidual E0 X).n = g.n := rfl

theorem mem_edgeResidual_edges_iff (g : FGraph) (E0 X : List Edge) (e : Edge) :
    e ∈ (g.edgeResidual E0 X).edges ↔
      e ∈ g.edges ∧ e ∉ E0 ∧ e ∉ X := by
  simp [edgeResidual, List.mem_filter, List.contains_iff_mem, and_assoc]

end FGraph
end TuzaDelta8
