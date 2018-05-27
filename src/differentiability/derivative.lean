-- http://www.docentes.unal.edu.co/eacostag/docs/FreCarat_Acosta.pdf
-- TODO: try to formalize using arbitrary normed vector spaces.
-- If that is too much work, fall back to ℝ → ℝ and build up

import order.filter analysis.topology.continuity analysis.real .continuity tactic.ring .normed_space
open lattice clm

noncomputable theory

variables {k : Type*} [normed_field k] 
variables {E : Type*}  [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]
include k

local notation L `⬝`:70 v := clm_app_pair ⟨L, v⟩
local notation M `∘clm` L := clm_comp L M

namespace derivative
section

def is_ptws_diff (f : E → F) (a : E) (f'_a : clm E F) :=
  ∃ φ : E → clm E F,
  (∀ x, f x = f a + (φ x)⬝(x - a)) ∧
  is_ptws_cont φ a ∧
  f'_a = φ a

def is_diff (f : E → F) (f' : E → clm E F) := ∀ a : E, is_ptws_diff f a (f' a)

-- smooth (infinitely differentiable). maybe want C^k first?

-- frechet

-- caratheodory <=> frechet

-- diff => continuity
def diff_im_cont {f : E → F} {a : E} {f'_a : clm E F} : is_ptws_diff f a f'_a → is_ptws_cont f a := sorry

-- derivative is unique (although φ is not)
-- cor: we can define the differential operator (how to do that?)

-- chain rule
def chain_rule {f : E → F} {g : F → G} {a : E} {f'_a : clm E F} {g'_fa : clm F G} (Hf : is_ptws_diff f a f'_a) (Hg : is_ptws_diff g (f a) g'_fa) : is_ptws_diff (g ∘ f) a (g'_fa ∘clm f'_a) :=
begin
rcases Hf with ⟨φ, f_pf⟩,
rcases f_pf with ⟨f_form, f_cont, f_deriv⟩,
rcases Hg with ⟨ψ, g_pf⟩,
rcases g_pf with ⟨g_form, g_cont, g_deriv⟩,
split,
split,
{
  intros,
  calc
  (g ∘ f) x = g (f x) : by simp
        ... = g (f a) + (ψ (f x))⬝(f x - f a) : by apply g_form
        ... = g (f a) + (ψ (f x))⬝((φ x)⬝(x - a)) : by simp; conv { for (f _) [1] { rw f_form } }; simp
        ... = g (f a) + ((ψ (f x)) ∘clm (φ x))⬝(x - a) : by sorry,
},
split,
{
  -- should just be function composition, but having a different version of composition makes this difficult
  admit
},
{
  rw [f_deriv, g_deriv]
}
end

-- derivative of addition'
-- TODO: wrong
-- def add' : is_diff (λ (p : E×E), p.1 + p.2) (λ (a : E×E), (λ (p : E×E), p.1 + p.2⟩)) := sorry

-- derivative of addition (composed with two functions)
-- TODO: proof should follow the analogous continuity proof
def add {f g : E → F} {f' g' : E → clm E F} (hf : is_diff f f') (hg : is_diff g g') : is_diff (f + g) (f' + g') := sorry

-- derivative of smul'
-- derivative of smul

-- derivative of bilinear function'
-- derivative of bilinear function
end
end derivative