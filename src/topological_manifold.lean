-- An n-dimensional topological manifold is a second countable Hausdorff space that is locally Euclidean of dimension n.

import analysis.real
import analysis.topology.topological_space
import data.vector
import .homeos

open topological_space

universes u

-- ℝ^n
def euclidean_space (n : ℕ) := vector ℝ n

local notation `ℝ^`n := euclidean_space n

instance euclidean_topology (n : ℕ) : topological_space ℝ^n := sorry

-- Lean doesn't recognize this for some reason
-- instance nbhds_topology {α : Type u} [topological_space α] {a : α} (s ∈ (nhds a).sets) : topological_space s := sorry

-- set_option trace.class_instances true

-- TODO: need to show R^n has a topology
-- TODO: would like to write ∃ s ∈ (nhds a).sets, but then lean doesn't know that s has a topology

-- todo: manifold with boundary

-- a chart is a homeomorphism from an open set on a manifold to an open set in ℝ^n (along with the other terms needed for that to make sense)

-- TODO: prove a chart can be found at every point in a manifold
-- TODO: prove open subset of a manifold is also a manifold -/

-- def open_set (α : Type u) [topological_space α] := { s : set α // is_open s }
-- -- TODO: coerce to set

-- A chart is a pair of a coordinate neighborhood in α and a homeomorphism from that nbhd to ℝ^n. There are several other equivalent formulations.
-- TODO: not sure which codomain to choose. picking simpler definition for now, because no messy open set arguments (not yet at least). revisit
structure chart (α : Type u) (n : ℕ) [topological_space α] : Type u :=
(coord_domain : set α)
(coord_map : homeo coord_domain ℝ^n)

-- hack to get around Lean not realizing s has a topology if just use the predicate
def neighborhood {α : Type u} [topological_space α] (a : α) := { s : set α // s ∈ (nhds a).sets }

-- chart at a with dimension n
structure nbhd_chart {α : Type u} (a : α) (n : ℕ) [topological_space α] : Type u :=
(coord_nbhd : neighborhood a)
(coord_map : homeo coord_nbhd.1 ℝ^n)
-- TODO: coerce to chart?

class topological_manifold (α : Type u) (n : ℕ) extends
  topological_space α,
  second_countable_topology α,
  t2_space α : Type u :=
(locally_euclidean_of_dim_n (a : α) : nbhd_chart a n)

-- could write: forall a, exists f : (nbhd a).sets -> R^n, is_homeo f
-- this seems not as good b/c we frequently use the charts and the functions so want to return those!!!
-- this is not the case for things like linear_map, continuous_linear_map, where all additional data are propositions. what about the derivative? seems like propositional data, but is it all that?
