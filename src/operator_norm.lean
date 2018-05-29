/- 
  The operator norm is the natural norm for linear operators between normed vector spaces. One can think of it as how much a map stretches unit vectors or as the smallest value that guarantees Cauchy-Schwarz (i.e. ∥L v∥ ≤ ∥L∥ * ∥v∥).

  The derivative of f : E → F is f' : E → continuous_linear_map E F.

  We need the operator norm both to define continuity for the definition of Caratheodory derivative and to take higher-order derivatives.
-/

-- TODO: We'd like op_norm to return an ennreal, but be able to restrict it to nonnegative reals when needed for a norm. Not sure how to do that yet. We can prove that the op_norm is finite for continuous/bounded linear maps. Should norm operate over nonnegative reals?

import differentiability.normed_space linear_algebra.linear_map_module analysis.ennreal order.complete_lattice

open lattice ennreal

noncomputable theory

universes u v w x

/- extended norm -/
-- TODO: of_real or of_nonneg_real?
def op_norm {k : Type u} {E : Type v} {F : Type w} [normed_field k] [normed_space k E] [normed_space k F] : linear_map E F → ennreal := λ L, Inf { M : ennreal | ∀ v : E, (of_nonneg_real ∥L v∥ norm_nonneg) ≤ M * (of_nonneg_real ∥v∥ norm_nonneg) }

section op_norm
variables {k : Type u} {E : Type v} {F : Type w}
variables [normed_field k] [normed_space k E] [normed_space k F]
variables {L M : linear_map E F}
include k

theorem op_norm_nonneg : op_norm L ≥ 0 := sorry

theorem op_norm_zero_iff_zero : op_norm L = 0 ↔ L = 0 := sorry

theorem op_norm_pos_homo : ∀ c (L : linear_map E F), op_norm (c•L) = (of_real ∥c∥) * op_norm L := sorry

theorem op_norm_triangle : op_norm (L + M) ≤ op_norm L + op_norm M := sorry

end op_norm

def op_dist {k : Type u} {E : Type v} {F : Type w} [normed_field k] [normed_space k E] [normed_space k F] : linear_map E F → linear_map E F → ennreal := λ L M, op_norm (L - M)

section op_dist
variables {k : Type u} {E : Type v} {F : Type w}
variables [normed_field k] [normed_space k E] [normed_space k F]
variables {L M N : linear_map E F}
include k

theorem op_dist_self : op_dist L L = 0 := sorry

theorem op_dist_eq_of_dist_eq_zero : op_dist L M = 0 → L = M := sorry

theorem op_dist_comm : op_dist L M = op_dist M L := sorry

theorem op_dist_triangle : op_dist L N ≤ op_dist L M + op_dist M N := sorry

end op_dist
