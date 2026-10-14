/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.MonotoneCuts

/-!
# The finite two-block carrier skeleton at six labels

This file checks the finite combinatorics used by the residual ordinary
six-label argument.  A two-block carrier is indexed by two nonadjacent center
vertices; its support consists of the two gaps incident to each center.

There are exactly nine such carriers.  Their block-preserving common-face
graph has twelve edges, while the full support complex has six additional
regrouping faces.  The oriented nine-cell chain is checked combinatorially:
every triangular face has exactly two occurrences with opposite incidence.
Nothing here asserts a closure zero or an analytic degree.
-/

namespace Gluck.Discrete
namespace N6Carrier

/-- A cyclic vertex or gap label in the six-label carrier complex. -/
abbrev Label := Fin 6

/-- The nine two-block carriers, numbered as in
`research/notes/ORDINARY_N6_MONOTONE_RESIDUE.md`. -/
abbrev Cell := Fin 9

/-- Cyclic successor on six labels. -/
def next : Label → Label := ![1, 2, 3, 4, 5, 0]

/-- Cyclic predecessor on six labels. -/
def prev : Label → Label := ![5, 0, 1, 2, 3, 4]

/-- Two distinct labels are cyclically nonadjacent. -/
def Nonadjacent (i j : Label) : Prop :=
  i ≠ j ∧ next i ≠ j ∧ next j ≠ i

instance decidableNonadjacent (i j : Label) : Decidable (Nonadjacent i j) := by
  unfold Nonadjacent
  infer_instance

/-- The smaller representative of the center pair of each carrier. -/
def firstCenter : Cell → Label := ![0, 0, 0, 1, 1, 1, 2, 2, 3]

/-- The larger representative of the center pair of each carrier. -/
def secondCenter : Cell → Label := ![2, 3, 4, 3, 4, 5, 4, 5, 5]

/-- The ordered center pair of a carrier. -/
def centerPair (k : Cell) : Label × Label :=
  (firstCenter k, secondCenter k)

/-- The unordered center set of a carrier. -/
def centers (k : Cell) : Finset Label :=
  {firstCenter k, secondCenter k}

/-- The two cyclic gaps incident to a center vertex. -/
def incidentGaps (i : Label) : Finset Label :=
  {prev i, i}

/-- The four active gaps of a two-block carrier. -/
def support (k : Cell) : Finset Label :=
  incidentGaps (firstCenter k) ∪ incidentGaps (secondCenter k)

/-- The explicit support table
`0125, 0235, 0345, 0123, 0134, 0145, 1234, 1245, 2345`. -/
def supportTable : Cell → Finset Label :=
  ![{0, 1, 2, 5}, {0, 2, 3, 5}, {0, 3, 4, 5},
    {0, 1, 2, 3}, {0, 1, 3, 4}, {0, 1, 4, 5},
    {1, 2, 3, 4}, {1, 2, 4, 5}, {2, 3, 4, 5}]

/-- The table lists every center pair in increasing order. -/
theorem firstCenter_lt_secondCenter (k : Cell) : firstCenter k < secondCenter k := by
  fin_cases k <;> decide

/-- Every listed center pair is nonadjacent. -/
theorem centers_nonadjacent (k : Cell) :
    Nonadjacent (firstCenter k) (secondCenter k) := by
  fin_cases k <;> decide

/-- The nine ordered center pairs are distinct. -/
theorem centerPair_injective : Function.Injective centerPair := by
  intro p q h
  fin_cases p <;> fin_cases q <;> simp_all [centerPair, firstCenter, secondCenter]

/-- The nine unordered center sets are distinct. -/
theorem centers_injective : Function.Injective centers := by
  intro p q h
  have hset := congrArg (fun s : Finset Label ↦ (s : Set Label)) h
  simp only [centers, Finset.coe_pair] at hset
  rcases Set.pair_eq_pair_iff.mp hset with hdirect | hswap
  · apply centerPair_injective
    exact Prod.ext hdirect.1 hdirect.2
  · have hp := firstCenter_lt_secondCenter p
    have hq := firstCenter_lt_secondCenter q
    rw [hswap.1, hswap.2] at hp
    exact (lt_asymm hp hq).elim

/-- Every unordered nonadjacent pair of six labels occurs in the table. -/
theorem exists_cell_of_nonadjacent (i j : Label) (h : Nonadjacent i j) :
    ∃ k : Cell, centers k = {i, j} := by
  fin_cases i <;> fin_cases j <;>
    simp [Nonadjacent, next] at h <;> decide

/-- Hence every unordered nonadjacent center pair determines a unique one of
the nine cells. -/
theorem existsUnique_cell_of_nonadjacent (i j : Label) (h : Nonadjacent i j) :
    ∃! k : Cell, centers k = {i, j} := by
  obtain ⟨k, hk⟩ := exists_cell_of_nonadjacent i j h
  refine ⟨k, hk, ?_⟩
  intro q hq
  exact centers_injective (hq.trans hk.symm)

/-- Each listed carrier activates four distinct gaps. -/
theorem support_card (k : Cell) : (support k).card = 4 := by
  fin_cases k <;> decide

/-- The definition by incident gaps agrees with the explicit nine-row support
table. -/
theorem support_eq_table (k : Cell) : support k = supportTable k := by
  fin_cases k <;> decide

/-! ## The reflection preserving the displayed C1 order chamber -/

/-- Under the vertex reflection `j ↦ 2-j`, a gap label transforms as
`j ↦ 1-j`. -/
def c1GapReflection : Label → Label := ![1, 0, 5, 4, 3, 2]

/-- The induced permutation of the nine pair cells.  It fixes cells 0, 4,
and 8 and exchanges `1↔7`, `2↔6`, and `3↔5`. -/
def c1CellReflection : Cell → Cell := ![0, 7, 6, 5, 4, 3, 2, 1, 8]

/-- The C1 gap reflection is an involution. -/
theorem c1GapReflection_involutive : Function.Involutive c1GapReflection := by
  intro i
  fin_cases i <;> rfl

/-- The induced cell permutation is an involution. -/
theorem c1CellReflection_involutive : Function.Involutive c1CellReflection := by
  intro k
  fin_cases k <;> rfl

/-- Reflecting every active gap of a cell gives exactly the support of the
induced reflected cell. -/
theorem image_c1GapReflection_support (k : Cell) :
    (support k).image c1GapReflection = support (c1CellReflection k) := by
  fin_cases k <;> decide

/-- In particular, the maximum-pair cell is fixed and the two proposed C1
full-cell repairs are reflected partners. -/
theorem c1Reflection_key_cells :
    c1CellReflection 0 = 0 ∧ c1CellReflection 1 = 7 ∧
      c1CellReflection 7 = 1 := by
  decide

/-- Two cells share a block-preserving codimension-one face when they share
one center and three active gaps. -/
def Adjacent (p q : Cell) : Prop :=
  (centers p ∩ centers q).card = 1 ∧ (support p ∩ support q).card = 3

instance decidableAdjacent (p q : Cell) : Decidable (Adjacent p q) := by
  unfold Adjacent
  infer_instance

/-- The exact neighbor table for the twelve-edge common-face graph. -/
def neighbors : Cell → Finset Cell :=
  ![{1, 7}, {0, 2, 3, 8}, {1, 4}, {1, 4}, {2, 3, 5, 6},
    {4, 7}, {4, 7}, {0, 5, 6, 8}, {1, 7}]

/-- Semantic common-face adjacency agrees with the explicit neighbor table. -/
theorem adjacent_iff_mem_neighbors (p q : Cell) :
    Adjacent p q ↔ q ∈ neighbors p := by
  fin_cases p <;> fin_cases q <;> decide

/-- Common-face adjacency is symmetric. -/
theorem adjacent_comm (p q : Cell) : Adjacent p q ↔ Adjacent q p := by
  simp only [Adjacent, Finset.inter_comm]

/-- The twelve unoriented graph edges, with their smaller endpoint first. -/
def edges : Finset (Cell × Cell) :=
  {(0, 1), (0, 7), (1, 2), (1, 3), (1, 8), (2, 4),
    (3, 4), (4, 5), (4, 6), (5, 7), (6, 7), (7, 8)}

/-- The displayed edge table has twelve distinct entries. -/
theorem edges_card : edges.card = 12 := by decide

/-- The edge table is exactly semantic adjacency, oriented by increasing cell
number. -/
theorem mem_edges_iff (p q : Cell) :
    (p, q) ∈ edges ↔ p < q ∧ Adjacent p q := by
  fin_cases p <;> fin_cases q <;> decide

/-- Consecutive cells of a list share block-preserving faces. -/
def IsPath : List Cell → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Adjacent p q ∧ IsPath (q :: rest)

instance decidableIsPath (path : List Cell) : Decidable (IsPath path) := by
  induction path with
  | nil => exact isTrue trivial
  | cons p rest ih =>
      cases rest with
      | nil => exact isTrue trivial
      | cons q tail =>
          unfold IsPath
          exact instDecidableAnd

/-- The canonical Type A min/min-to-max/max path. -/
theorem typeA_path : IsPath [2, 1, 8] := by decide

/-- The two short canonical Type B paths. -/
theorem typeB_paths : IsPath [1, 0, 7] ∧ IsPath [1, 8, 7] := by decide

/-- The four canonical Type C paths through the carrier graph. -/
theorem typeC_paths :
    IsPath [1, 0, 7, 6] ∧ IsPath [1, 2, 4, 6] ∧
      IsPath [1, 3, 4, 6] ∧ IsPath [1, 8, 7, 6] := by
  decide

/-- Two cells meet across a triangular support face. -/
def FaceAdjacent (p q : Cell) : Prop :=
  (support p ∩ support q).card = 3

/-- A triangular support face which changes the two-block grouping. -/
def RegroupingAdjacent (p q : Cell) : Prop :=
  FaceAdjacent p q ∧ ¬Adjacent p q

instance decidableFaceAdjacent (p q : Cell) : Decidable (FaceAdjacent p q) := by
  unfold FaceAdjacent
  infer_instance

instance decidableRegroupingAdjacent (p q : Cell) : Decidable (RegroupingAdjacent p q) := by
  unfold RegroupingAdjacent
  infer_instance

/-- The full triangular-face neighbor table of the nine cells. -/
def faceNeighbors : Cell → Finset Cell :=
  ![{1, 3, 5, 7}, {0, 2, 3, 8}, {1, 4, 5, 8},
    {0, 1, 4, 6}, {2, 3, 5, 6}, {0, 2, 4, 7},
    {3, 4, 7, 8}, {0, 5, 6, 8}, {1, 2, 6, 7}]

/-- Semantic triangular-face adjacency agrees with the full neighbor table. -/
theorem face_adjacent_iff_mem_face_neighbors (p q : Cell) :
    FaceAdjacent p q ↔ q ∈ faceNeighbors p := by
  fin_cases p <;> fin_cases q <;> decide

/-- Every cell has four triangular-face neighbors. -/
theorem face_neighbors_card (p : Cell) : (faceNeighbors p).card = 4 := by
  fin_cases p <;> decide

/-- Block-preserving adjacency is triangular-face adjacency. -/
theorem adjacent_imp_face_adjacent {p q : Cell} (h : Adjacent p q) : FaceAdjacent p q :=
  h.2

/-- Triangular-face adjacency is symmetric. -/
theorem face_adjacent_comm (p q : Cell) : FaceAdjacent p q ↔ FaceAdjacent q p := by
  simp only [FaceAdjacent, Finset.inter_comm]

/-- Every triangular-face adjacency is either block-preserving or regrouping. -/
theorem face_adjacent_iff_adjacent_or_regrouping (p q : Cell) :
    FaceAdjacent p q ↔ Adjacent p q ∨ RegroupingAdjacent p q := by
  by_cases h : Adjacent p q
  · exact ⟨fun _ ↦ Or.inl h, fun _ ↦ adjacent_imp_face_adjacent h⟩
  · exact ⟨fun hf ↦ Or.inr ⟨hf, h⟩, fun hd ↦ (hd.resolve_left h).1⟩

/-- The eighteen unoriented triangular-face edges, with smaller endpoint first. -/
def faceEdges : Finset (Cell × Cell) :=
  {(0, 1), (0, 3), (0, 5), (0, 7), (1, 2), (1, 3),
    (1, 8), (2, 4), (2, 5), (2, 8), (3, 4), (3, 6),
    (4, 5), (4, 6), (5, 7), (6, 7), (6, 8), (7, 8)}

/-- The full triangular-face graph has eighteen edges. -/
theorem face_edges_card : faceEdges.card = 18 := by decide

/-- The full edge table is exactly triangular-face adjacency in increasing order. -/
theorem mem_face_edges_iff (p q : Cell) :
    (p, q) ∈ faceEdges ↔ p < q ∧ FaceAdjacent p q := by
  fin_cases p <;> fin_cases q <;> decide

/-- The six triangular-face edges which change the two-block grouping. -/
def regroupingEdges : Finset (Cell × Cell) :=
  {(0, 3), (0, 5), (2, 5), (2, 8), (3, 6), (6, 8)}

/-- The full face graph is the union of block-preserving and regrouping edges. -/
theorem face_edges_eq_union : faceEdges = edges ∪ regroupingEdges := by decide

/-- There are exactly six regrouping edges. -/
theorem regrouping_edges_card : regroupingEdges.card = 6 := by decide

/-- The regrouping edge table has its semantic meaning in increasing order. -/
theorem mem_regrouping_edges_iff (p q : Cell) :
    (p, q) ∈ regroupingEdges ↔ p < q ∧ RegroupingAdjacent p q := by
  fin_cases p <;> fin_cases q <;> decide

/-- No triangular-face edge is both block-preserving and regrouping. -/
theorem edges_disjoint_regrouping_edges : Disjoint edges regroupingEdges := by decide

/-- The increasing support labels of each oriented tetrahedral cell. -/
def orientedSupport : Cell → Fin 4 → Label :=
  ![![0, 1, 2, 5], ![0, 2, 3, 5], ![0, 3, 4, 5],
    ![0, 1, 2, 3], ![0, 1, 3, 4], ![0, 1, 4, 5],
    ![1, 2, 3, 4], ![1, 2, 4, 5], ![2, 3, 4, 5]]

/-- The triangular face obtained by deleting one oriented support position. -/
def orientedFace (k : Cell) (a : Fin 4) : Finset Label :=
  support k \ {orientedSupport k a}

/-- Every oriented support entry belongs to its cell support. -/
theorem oriented_support_mem (k : Cell) (a : Fin 4) :
    orientedSupport k a ∈ support k := by
  fin_cases k <;> fin_cases a <;> decide

/-- The four oriented support positions of each cell have distinct labels. -/
theorem oriented_support_injective (k : Cell) : Function.Injective (orientedSupport k) := by
  intro a b h
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all [orientedSupport]

/-- Deleting one oriented support entry leaves three labels. -/
theorem oriented_face_card (k : Cell) (a : Fin 4) : (orientedFace k a).card = 3 := by
  rw [orientedFace, Finset.card_sdiff]
  rw [support_card]
  simp [oriented_support_mem]

/-- Distinct support positions determine distinct faces of one cell. -/
theorem oriented_face_injective (k : Cell) : Function.Injective (orientedFace k) := by
  intro a b h
  apply oriented_support_injective k
  by_contra hne
  have hmem : orientedSupport k a ∈ orientedFace k b := by
    simp [orientedFace, oriented_support_mem, hne]
  rw [← h] at hmem
  simp [orientedFace] at hmem

/-- Coefficients of `C0123-C0125+C0134+C0145-C0235-C0345+C1234+C1245+C2345`. -/
def orientationCoeff : Cell → ℤ :=
  ![-1, -1, -1, 1, 1, 1, 1, 1, 1]

/-- The incidence of a deleted support position in the oriented nine-cell chain. -/
def faceIncidence (k : Cell) (a : Fin 4) : ℤ :=
  orientationCoeff k * (-1 : ℤ) ^ a.val

/-- The other cell containing each oriented triangular face. -/
def faceMateCell : Cell → Fin 4 → Cell :=
  ![![7, 1, 5, 3], ![8, 2, 0, 3], ![8, 5, 1, 4],
    ![6, 1, 4, 0], ![6, 2, 5, 3], ![7, 2, 0, 4],
    ![8, 4, 7, 3], ![8, 5, 0, 6], ![2, 7, 1, 6]]

/-- The deleted support position at the other occurrence of each face. -/
def faceMatePosition : Cell → Fin 4 → Fin 4 :=
  ![![2, 2, 2, 3], ![2, 2, 1, 1], ![0, 1, 1, 1],
    ![3, 3, 3, 3], ![1, 3, 3, 2], ![1, 1, 2, 2],
    ![3, 0, 3, 0], ![1, 0, 0, 2], ![0, 0, 0, 0]]

/-- Every face mate belongs to a different cell. -/
theorem face_mate_ne (k : Cell) (a : Fin 4) : faceMateCell k a ≠ k := by
  fin_cases k <;> fin_cases a <;> decide

/-- A face and its tabulated mate have the same three labels. -/
theorem face_mate_eq (k : Cell) (a : Fin 4) :
    orientedFace k a = orientedFace (faceMateCell k a) (faceMatePosition k a) := by
  fin_cases k <;> fin_cases a <;> decide

/-- Taking the mate twice returns the original face occurrence. -/
theorem face_mate_involutive (k : Cell) (a : Fin 4) :
    faceMateCell (faceMateCell k a) (faceMatePosition k a) = k ∧
      faceMatePosition (faceMateCell k a) (faceMatePosition k a) = a := by
  fin_cases k <;> fin_cases a <;> decide

/-- The two occurrences of every triangular face have opposite incidence. -/
theorem face_mate_incidence_cancel (k : Cell) (a : Fin 4) :
    faceIncidence k a +
      faceIncidence (faceMateCell k a) (faceMatePosition k a) = 0 := by
  fin_cases k <;> fin_cases a <;> decide

/-- Any other cell occurrence of a face is its tabulated mate. -/
theorem eq_face_mate_of_shared_face {k q : Cell} {a b : Fin 4} (hne : q ≠ k)
    (hface : orientedFace k a = orientedFace q b) :
    q = faceMateCell k a ∧ b = faceMatePosition k a := by
  revert q b
  fin_cases k <;> fin_cases a <;> decide

/-- Every occurrence of an oriented face is either itself or its unique mate. -/
theorem shared_face_eq_self_or_mate {k q : Cell} {a b : Fin 4}
    (hface : orientedFace k a = orientedFace q b) :
    (q = k ∧ b = a) ∨ (q = faceMateCell k a ∧ b = faceMatePosition k a) := by
  by_cases hq : q = k
  · subst q
    exact Or.inl ⟨rfl, (oriented_face_injective k hface).symm⟩
  · exact Or.inr (eq_face_mate_of_shared_face hq hface)

/-- Distinct cell occurrences of a shared face have cancelling incidences. -/
theorem shared_face_incidence_cancel {p q : Cell} {a b : Fin 4} (hne : q ≠ p)
    (hface : orientedFace p a = orientedFace q b) :
    faceIncidence p a + faceIncidence q b = 0 := by
  obtain ⟨rfl, rfl⟩ := eq_face_mate_of_shared_face hne hface
  exact face_mate_incidence_cancel p a

/-- Two cells are face-adjacent exactly when distinct occurrences share a face. -/
theorem face_adjacent_iff_exists_shared_face (p q : Cell) :
    FaceAdjacent p q ↔ p ≠ q ∧ ∃ a b : Fin 4, orientedFace p a = orientedFace q b := by
  fin_cases p <;> fin_cases q <;> decide

/-! ## The minimum-star/extrema-bridge candidate -/

/-- A carrier together with every block-preserving neighbor. -/
def closedStar (k : Cell) : Finset Cell :=
  insert k (neighbors k)

/-- Existence of a block-preserving walk of at most the given length.  The
recursive step may either stay put or cross one common face. -/
def HasWalkWithin (p q : Cell) : ℕ → Prop
  | 0 => q = p
  | d + 1 => ∃ k, HasWalkWithin p k d ∧ (q = k ∨ Adjacent k q)

instance decidableHasWalkWithin (p q : Cell) (d : ℕ) :
    Decidable (HasWalkWithin p q d) := by
  induction d generalizing q with
  | zero =>
      simp only [HasWalkWithin]
      infer_instance
  | succ d ih =>
      simp only [HasWalkWithin]
      infer_instance

/-- Membership in a closed carrier star is equality or common-face
adjacency. -/
theorem mem_closed_star_iff (p q : Cell) :
    q ∈ closedStar p ↔ q = p ∨ Adjacent p q := by
  simp only [closedStar, Finset.mem_insert, adjacent_iff_mem_neighbors]

/-- Breadth-first closed-neighborhood expansion from one carrier. -/
def reachableWithin (p : Cell) : ℕ → Finset Cell
  | 0 => {p}
  | d + 1 => (reachableWithin p d).biUnion closedStar

/-- Breadth-first expansion constrained to a prescribed carrier family. -/
def reachableWithinSet (s : Finset Cell) (p : Cell) : ℕ → Finset Cell
  | 0 => if p ∈ s then {p} else ∅
  | d + 1 => (reachableWithinSet s p d).biUnion fun k ↦ closedStar k ∩ s

/-- Closed-neighborhood expansion computes walks of bounded length. -/
theorem mem_reachable_within_iff (p q : Cell) (d : ℕ) :
    q ∈ reachableWithin p d ↔ HasWalkWithin p q d := by
  induction d generalizing q with
  | zero => simp [reachableWithin, HasWalkWithin]
  | succ d ih =>
      simp only [reachableWithin, Finset.mem_biUnion, ih, mem_closed_star_iff,
        HasWalkWithin]

/-- The displayed length is the graph distance between two carriers. -/
def IsShortestDistance (p q : Cell) (d : ℕ) : Prop :=
  q ∈ reachableWithin p d ∧ ∀ e < d, q ∉ reachableWithin p e

instance decidableIsShortestDistance (p q : Cell) (d : ℕ) :
    Decidable (IsShortestDistance p q d) := by
  unfold IsShortestDistance
  infer_instance

/-- The union of the length-`d` geodesics between two carriers, computed by
splitting the distance at every possible intermediate carrier. -/
def geodesicBridgeAtDistance (p q : Cell) (d : ℕ) : Finset Cell :=
  Finset.univ.filter fun k ↦
    ∃ a ∈ Finset.range (d + 1),
      k ∈ reachableWithin p a ∧ q ∈ reachableWithin k (d - a)

/-- A carrier lies on a length-`d` geodesic when the two bounded walk
distances through it sum to `d`. -/
def OnGeodesicAtDistance (p q : Cell) (d : ℕ) (k : Cell) : Prop :=
  ∃ a ≤ d, HasWalkWithin p k a ∧ HasWalkWithin k q (d - a)

/-- The finite bridge computation has the stated bounded-walk semantics. -/
theorem mem_geodesic_bridge_at_distance_iff (p q k : Cell) (d : ℕ) :
    k ∈ geodesicBridgeAtDistance p q d ↔ OnGeodesicAtDistance p q d k := by
  simp only [geodesicBridgeAtDistance, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, Nat.lt_succ_iff, mem_reachable_within_iff,
    OnGeodesicAtDistance]

/-- A nonempty carrier family is connected when bounded expansion inside the
family reaches every member from every starting member. -/
def IsConnectedCarrierSet (s : Finset Cell) : Prop :=
  s.Nonempty ∧ ∀ p ∈ s, s ⊆ reachableWithinSet s p s.card

instance decidableIsConnectedCarrierSet (s : Finset Cell) :
    Decidable (IsConnectedCarrierSet s) := by
  unfold IsConnectedCarrierSet
  infer_instance

/-- The Type A minimum-star/extrema-bridge carrier family. -/
def typeACandidate : Finset Cell :=
  geodesicBridgeAtDistance 0 3 2 ∪ closedStar 0

/-- The Type B minimum-star/extrema-bridge carrier family. -/
def typeBCandidate : Finset Cell :=
  geodesicBridgeAtDistance 1 4 2 ∪ closedStar 1

/-- The Type C minimum-star/extrema-bridge carrier family. -/
def typeCCandidate : Finset Cell :=
  geodesicBridgeAtDistance 4 0 3 ∪ closedStar 4

/-- The representative Type A extrema carriers have graph distance two. -/
theorem type_a_shortest_distance : IsShortestDistance 0 3 2 := by decide

/-- The representative Type B extrema carriers have graph distance two. -/
theorem type_b_shortest_distance : IsShortestDistance 1 4 2 := by decide

/-- The representative Type C extrema carriers have graph distance three. -/
theorem type_c_shortest_distance : IsShortestDistance 4 0 3 := by decide

/-- The exact Type A union of shortest extrema paths. -/
theorem type_a_geodesic_bridge :
    geodesicBridgeAtDistance 0 3 2 = {0, 1, 3} := by decide

/-- The exact Type B union of shortest extrema paths. -/
theorem type_b_geodesic_bridge :
    geodesicBridgeAtDistance 1 4 2 = {1, 2, 3, 4} := by decide

/-- The exact Type C union of shortest extrema paths. -/
theorem type_c_geodesic_bridge :
    geodesicBridgeAtDistance 4 0 3 = {0, 1, 2, 3, 4, 5, 6, 7} := by decide

/-- The exact Type A candidate has four cells. -/
theorem type_a_candidate_eq : typeACandidate = {0, 1, 3, 7} := by decide

/-- The exact Type B candidate has six cells. -/
theorem type_b_candidate_eq : typeBCandidate = {0, 1, 2, 3, 4, 8} := by decide

/-- The exact Type C candidate has eight cells. -/
theorem type_c_candidate_eq : typeCCandidate = {0, 1, 2, 3, 4, 5, 6, 7} := by decide

/-- The three candidate carrier families have sizes four, six, and eight. -/
theorem candidate_cardinalities :
    typeACandidate.card = 4 ∧ typeBCandidate.card = 6 ∧
      typeCCandidate.card = 8 := by decide

/-- The Type A candidate carrier family is connected. -/
theorem type_a_candidate_connected : IsConnectedCarrierSet typeACandidate := by decide

/-- The Type B candidate carrier family is connected. -/
theorem type_b_candidate_connected : IsConnectedCarrierSet typeBCandidate := by decide

/-- The Type C candidate carrier family is connected. -/
theorem type_c_candidate_connected : IsConnectedCarrierSet typeCCandidate := by decide

/-! ## Half-turn symmetry of the Type B candidate -/

/-- Rotation by three on the six cyclic labels. -/
def halfTurnLabel : Label → Label := ![3, 4, 5, 0, 1, 2]

/-- The induced half-turn permutation of the nine carrier cells. -/
def halfTurnCell : Cell → Cell := ![8, 1, 3, 2, 4, 6, 5, 7, 0]

/-- Rotation by three is an involution on labels. -/
theorem half_turn_label_involutive : Function.Involutive halfTurnLabel := by
  intro k
  fin_cases k <;> rfl

/-- Rotation by three is an involution on carrier cells. -/
theorem half_turn_cell_involutive : Function.Involutive halfTurnCell := by
  intro k
  fin_cases k <;> rfl

/-- The cell half-turn is induced by rotating both centers. -/
theorem image_half_turn_label_centers (k : Cell) :
    (centers k).image halfTurnLabel = centers (halfTurnCell k) := by
  fin_cases k <;> decide

/-- The cell half-turn rotates all four active gaps. -/
theorem image_half_turn_label_support (k : Cell) :
    (support k).image halfTurnLabel = support (halfTurnCell k) := by
  fin_cases k <;> decide

/-- The half-turn preserves common-face adjacency. -/
theorem half_turn_cell_adjacent (p q : Cell) :
    Adjacent (halfTurnCell p) (halfTurnCell q) ↔ Adjacent p q := by
  fin_cases p <;> fin_cases q <;> decide

/-- The Type B shortest-path diamond is half-turn invariant. -/
theorem image_half_turn_type_b_geodesic_bridge :
    (geodesicBridgeAtDistance 1 4 2).image halfTurnCell =
      geodesicBridgeAtDistance 1 4 2 := by decide

/-- The closed star of the Type B minimum carrier is half-turn invariant. -/
theorem image_half_turn_type_b_closed_star :
    (closedStar 1).image halfTurnCell = closedStar 1 := by decide

/-- The entire Type B candidate carrier family is half-turn invariant. -/
theorem image_half_turn_type_b_candidate :
    typeBCandidate.image halfTurnCell = typeBCandidate := by decide

/-- The half-turn exchanges the two off-diamond Type B star leaves. -/
theorem half_turn_type_b_leaves :
    halfTurnCell 0 = 8 ∧ halfTurnCell 8 = 0 := by decide

end N6Carrier
end Gluck.Discrete
