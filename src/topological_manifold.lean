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
instance nbhds_topology {α : Type u} [topological_space α] {a : α} (s ∈ (nhds a).sets) : topological_space s := sorry

-- set_option trace.class_instances true

-- TODO: need to show R^n has a topology
-- TODO: would like to write ∃ s ∈ (nhds a).sets, but then lean doesn't know that s has a topology

-- set_option trace.class_instances true

class topological_manifold (n : ℕ) (α : Type u) extends
  topological_space α,
  second_countable_topology α,
  t2_space α : Type u :=
(locally_euclidean_of_dim_n {a : α} :
  -- there exist a set s and a function f from s to t such that s is a neighborhood of a and f is a homeomorphism
  ∃ (s : set α) (t : set ℝ^n) (f : s → t),
  s ∈ (nhds a).sets ∧ is_homeo f)

-- todo: manifold with boundary

-- a chart is a homeomorphism from an open set on a manifold to an open set in ℝ^n (along with the other terms needed for that to make sense)
-- TODO: this structure may need to be revised. depends on which properties are actually used
structure chart (α : Type u) (n : ℕ) [topological_manifold n α] :=
(s : set α)
(is_open_s : is_open s)

-- typically not made explicit
{t : set ℝ^n}
-- not necessary b/c homeo + is_open_s imply it
{is_open_t : is_open t}
(map : s → t)
(is_homeo : is_homeo map)

-- TODO: prove a chart can be found at every point in a manifold
-- TODO: prove open subset of a manifold is a also a manifold