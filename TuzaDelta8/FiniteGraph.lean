import Std

namespace TuzaDelta8

structure Edge where
  u : Nat
  v : Nat
deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace Edge
def norm (u v : Nat) : Edge := if u < v then ⟨u, v⟩ else ⟨v, u⟩
def wellFormed (n : Nat) (e : Edge) : Bool := decide (e.u < e.v ∧ e.v < n)
def touches (e : Edge) (x : Nat) : Bool := (e.u == x) || (e.v == x)
end Edge

structure Tri where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace Tri
def wellFormed (n : Nat) (t : Tri) : Bool := decide (t.a < t.b ∧ t.b < t.c ∧ t.c < n)
def edgeList (t : Tri) : List Edge := [Edge.norm t.a t.b, Edge.norm t.a t.c, Edge.norm t.b t.c]
def contains (t : Tri) (x : Nat) : Bool := (t.a == x) || (t.b == x) || (t.c == x)
end Tri

structure FGraph where
  n : Nat
  edges : List Edge
deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace FGraph
def wellFormed (g : FGraph) : Bool := (g.edges.all (fun e => e.wellFormed g.n)) && decide g.edges.Nodup
def hasEdge (g : FGraph) (u v : Nat) : Bool := if u == v then false else g.edges.contains (Edge.norm u v)
def degree (g : FGraph) (v : Nat) : Nat := (g.edges.filter (fun e => e.touches v)).length
def isTriangle (g : FGraph) (t : Tri) : Bool :=
  t.wellFormed g.n && g.hasEdge t.a t.b && g.hasEdge t.a t.c && g.hasEdge t.b t.c
def allTriangles (g : FGraph) : List Tri :=
  (List.range g.n).flatMap (fun a =>
    (List.range g.n).flatMap (fun b =>
      (List.range g.n).filterMap (fun c =>
        if a < b then
          if b < c then
            let t : Tri := ⟨a, b, c⟩
            if g.isTriangle t then some t else none
          else none
        else none)))
def commonNeighborCount (g : FGraph) (u v : Nat) : Nat :=
  ((List.range g.n).filter (fun w => g.hasEdge u w && g.hasEdge v w)).length
end FGraph

structure LocalCertificate where
  stage : Nat
  index : Nat
  n : Nat
  edges : List Edge
  hubU : Nat
  hubV : Nat
  degreeU : Nat
  degreeV : Nat
  codegree : Nat
  packing : List Tri
  cover : List Edge
deriving Repr

namespace LocalCertificate
def graph (c : LocalCertificate) : FGraph := ⟨c.n, c.edges⟩
def packingEdges (c : LocalCertificate) : List Edge := c.packing.flatMap Tri.edgeList
def coverTriangle (c : LocalCertificate) (t : Tri) : Bool := t.edgeList.any (fun e => c.cover.contains e)
def packingIsValid (c : LocalCertificate) : Bool :=
  let g := c.graph
  (c.packing.all g.isTriangle) && decide c.packingEdges.Nodup
def coverIsValid (c : LocalCertificate) : Bool :=
  let g := c.graph
  decide c.cover.Nodup && c.cover.all (fun e => g.edges.contains e)
def hubTrianglesCovered (c : LocalCertificate) : Bool :=
  c.graph.allTriangles.all (fun t => if t.contains c.hubU || t.contains c.hubV then c.coverTriangle t else true)
def packingProtection (c : LocalCertificate) : Bool :=
  c.packing.all (fun t =>
    t.edgeList.all (fun e => if e.touches c.hubU || e.touches c.hubV then true else c.cover.contains e))
def verify (c : LocalCertificate) : Bool :=
  let g := c.graph
  g.wellFormed &&
  decide (c.hubU < c.n ∧ c.hubV < c.n ∧ c.hubU ≠ c.hubV) &&
  (c.hubU == 0) && (c.hubV == 1) &&
  (c.stage == c.codegree) &&
  c.coverIsValid &&
  c.packingIsValid &&
  decide (c.cover.length ≤ 2 * c.packing.length) &&
  c.hubTrianglesCovered &&
  c.packingProtection &&
  (g.commonNeighborCount c.hubU c.hubV == c.codegree) &&
  (g.degree c.hubU == c.degreeU) &&
  (g.degree c.hubV == c.degreeV)
end LocalCertificate

structure WKEWitness where
  crossMatchingSize : Nat
  n : Nat
  edges : List Edge
  matching : List Edge
  coverVertices : List Nat
deriving Repr

namespace WKEWitness
def graph (w : WKEWitness) : FGraph := ⟨w.n, w.edges⟩
def matchingEndpoints (w : WKEWitness) : List Nat := w.matching.flatMap (fun e => [e.u, e.v])
def verify (w : WKEWitness) : Bool :=
  let g := w.graph
  g.wellFormed &&
  decide w.matching.Nodup &&
  w.matching.all (fun e => g.edges.contains e) &&
  decide w.matchingEndpoints.Nodup &&
  decide w.coverVertices.Nodup &&
  w.coverVertices.all (fun v => decide (v < w.n)) &&
  decide (w.coverVertices.length ≤ w.matching.length) &&
  g.edges.all (fun e =>
    w.matching.contains e || w.coverVertices.contains e.u || w.coverVertices.contains e.v)
end WKEWitness

end TuzaDelta8
