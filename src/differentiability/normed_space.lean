-- Inspired by Patrick Massot
-- This approach differs from that of Patrick's by using continuity instead of boundedness. As with Caratheodory, this hides norms and epsilon-deltas as much as possible.
-- Boundedness and continuity for linear operators are equivalent on the most common spaces of study, but may diverge on other spaces.
-- continuity also provides more general proofs than norm arguments.
-- admittedly, with the more powerful norm_num, the gap between the two approaches is smaller. I still believe continuous is the right way forward. It still replicates less work than boundedness
-- TODO: Lean still doesn't have pointwise continuity(!). We want that to make proofs more general. It's pretty simple to do.
-- TODO: continuous at 0/arbitrary point => continuous everywhere
-- see http://matrixeditions.com/FA.Chap3.1-4.pdf (among others)


import algebra.field
import tactic.norm_num
import analysis.topology.continuity
import .norm
import order.complete_lattice

open lattice

noncomputable theory
local attribute [instance] classical.prop_decidable

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)


variables {k : Type*} [normed_field k] 
variables {E : Type*} [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

include k
def is_continuous_linear_map (L : E → F) := (is_linear_map L) ∧ (continuous L)

-- ways to combine is_continuous_linear_map proofs
namespace is_continuous_linear_map

lemma zero : is_continuous_linear_map (λ (x:E), (0:F)) :=
⟨is_linear_map.map_zero, continuous_const⟩

lemma id : is_continuous_linear_map (λ (x:E), x) :=
⟨is_linear_map.id, continuous_id⟩

-- Remark: smul and add should follow immediately from the fact that normed vectors spaces are topological vector spaces

-- this seems harder than its bounded counterpart (which is admittedly nontrivial)
lemma smul {L : E → F} (c : k) (H : is_continuous_linear_map L) : is_continuous_linear_map (λ e, c•L e) := sorry

lemma neg {L : E → F} (H : is_continuous_linear_map L) :
is_continuous_linear_map (λ e, -L e) :=
begin
  rcases H with ⟨lin, cont⟩,
  split,
  { exact is_linear_map.map_neg lin },
  { exact continuous_neg cont }
end

lemma add {L : E → F} {M : E → F} (HL : is_continuous_linear_map L) (HM : is_continuous_linear_map M) : 
is_continuous_linear_map (λ e, L e + M e) :=
begin
  rcases HL with ⟨lin_L, cont_L⟩,
  rcases HM with ⟨lin_M , cont_M⟩,
  split,
  { exact is_linear_map.map_add lin_L lin_M },
  { exact continuous_add cont_L cont_M }
end

lemma sub {L : E → F} {M : E → F} (HL : is_continuous_linear_map L) (HM : is_continuous_linear_map M) : 
is_continuous_linear_map (λ e, L e - M e) := add HL (neg HM)

lemma comp {L : E → F} {M : F → G} (HL : is_continuous_linear_map L) (HM  : is_continuous_linear_map M) : is_continuous_linear_map (M ∘ L) :=
begin
rcases HL with ⟨lin_L, cont_L⟩,
rcases HM with ⟨lin_M, cont_M⟩,
split,
{ exact is_linear_map.comp lin_M lin_L },
{ exact continuous.comp cont_L cont_M }
end

end is_continuous_linear_map

-- some holdover code about bounded linear maps. it will eventually be useful, but not currently used, because is_continuous_linear_map is better

-- bounded in the linear map sense
def is_bounded (f : E → F) := ∃ M, M > 0 ∧ ∀ x : E, ∥f x∥ ≤ M * ∥x∥ 

def is_bounded_linear_map (L : E → F) := (is_linear_map L) ∧ (is_bounded L)

namespace is_bounded_linear_map

lemma continuous {L : E → F} (H : is_bounded_linear_map L) : continuous L :=
begin
  rcases H with ⟨lin, M, Mpos, ineq⟩,
  apply continuous_iff_tendsto.2,
  intro x,
  apply tendsto_iff_norm_tendsto_zero.2,
  replace ineq := λ e, calc ∥L e - L x∥ = ∥L (e - x)∥ : by rw [←(lin.sub e x)]
  ... ≤ M*∥e-x∥ : ineq (e-x),
  have lim1 : (λ (x:E), M) →_{x} M := tendsto_const_nhds,

  have lim2 : (λ e, e-x) →_{x} 0 := 
  begin 
    have limId := continuous_iff_tendsto.1 continuous_id x,
    have limx : (λ (e : E), -x) →_{x} -x := tendsto_const_nhds,
    have := tendsto_add limId limx, 
    simp at this,
    simpa using this,
  end,
  replace lim2 := filter.tendsto.comp lim2 lim_norm_zero,
  apply squeeze_zero,
  { simp[norm_nonneg] },
  { exact ineq },
  { simpa using tendsto_mul lim1 lim2 }
end


lemma lim_zero_bounded_linear_map {L : E → F} (H : is_bounded_linear_map L) : (L →_{0} 0) :=
by simpa [H.left.zero] using continuous_iff_tendsto.1 H.continuous 0

end is_bounded_linear_map

-- Next lemma is stated for real normed space but it would work as soon as the base field is an extension of ℝ
lemma bounded_continuous_linear_map {E : Type*}  [normed_space ℝ E] {F : Type*}  [normed_space ℝ F] {L : E → F} 
(h : is_continuous_linear_map L) : is_bounded L :=
begin
  rcases h with ⟨lin, cont⟩,
  replace cont := continuous_of_metric.1 cont 1 (by norm_num),
  swap, exact 0,
  rw[lin.zero] at cont,
  rcases cont with ⟨δ, δ_pos, H⟩,
  revert H,
  repeat { conv in (_ < _ ) { rw norm_dist } },
  intro H,
  existsi (δ/2)⁻¹,
  have half_δ_pos := half_pos δ_pos,
  split,
  exact (inv_pos half_δ_pos),
  intro x,
  by_cases h : x = 0,
  { simp [h, lin.zero] }, -- case x = 0
  { -- case x ≠ 0   
    have norm_x_pos : ∥x∥ > 0 := norm_pos_iff.2 h,
    have norm_x : ∥x∥ ≠ 0 := mt norm_zero_iff_zero.1 h,
    
    let p := ∥x∥*(δ/2)⁻¹,
    have p_pos : p > 0 := mul_pos norm_x_pos (inv_pos $ half_δ_pos),
    have p0 := ne_of_gt p_pos,

    let q := (δ/2)*∥x∥⁻¹,
    have q_pos : q > 0 := div_pos half_δ_pos norm_x_pos,
    have q0 := ne_of_gt q_pos,

    have triv := calc
     p*q = ∥x∥*((δ/2)⁻¹*(δ/2))*∥x∥⁻¹ : by simp[mul_assoc]
     ... = 1 : by simp [(inv_mul_cancel $ ne_of_gt half_δ_pos), mul_inv_cancel norm_x],
      
    have norm_calc := calc ∥q•x∥ = abs(q)*∥x∥ : by {rw norm_smul, refl}
    ... = q*∥x∥ : by rw [abs_of_nonneg $ le_of_lt q_pos]
    ... = δ/2 :  by simp [mul_assoc, inv_mul_cancel norm_x]
    ... < δ : half_lt_self δ_pos,
    
    exact calc 
    ∥L x∥ = ∥L (1•x)∥: by simp
    ... = ∥L ((p*q)•x) ∥ : by {rw [←triv] }
    ... = ∥L (p•q•x) ∥ : by rw mul_smul
    ... = ∥p•L (q•x) ∥ : by rw lin.smul
    ... = abs(p)*∥L (q•x) ∥ : by { rw norm_smul, refl}
    ... = p*∥L (q•x) ∥ : by rw [abs_of_nonneg $ le_of_lt $ p_pos]
    ... ≤ p*1 : le_of_lt $ mul_lt_mul_of_pos_left (H norm_calc) p_pos 
    ... = p : by simp
    ... = (δ/2)⁻¹*∥x∥ : by simp[mul_comm] }
end

/- Continuous Linear Maps -/

-- the following approach is based off that of poly in number_theory/dioph.lean, which also packages together functions with their proofs

-- for now, k is implicit
def clm {k : Type*} (E : Type*) (F : Type*) [normed_field k] [normed_space k E] [normed_space k F] := { L : E → F // is_continuous_linear_map L }

-- TODO: I think clm should be a structure/class (what's the difference?) that extends linear_map (which isn't a structure/class...) and continuous (which also isn't a structure/class). perhaps it should just be coercible instead

namespace clm
section

-- TODO: how to get multiplication notation?
-- we can treat a clm as a function
instance : has_coe_to_fun (clm E F) := ⟨_, λ L, L.1⟩

-- treat clm application as "multiplication" and give it the right space
-- Need it to be tupled so continuity makes sense naturally (could also use the approach in topological_structures.lean)
-- TODO: this feels really bad. The notation is always exposed. Need to find a better way
def clm_app_pair (p : (clm E F) × E) := p.1 p.2
local notation L `⬝`:70 v := clm_app_pair ⟨L, v⟩
@[simp] theorem clm_app_pair_eval (L : clm E F) (v) : (L⬝v) = L v := rfl

-- proof data
-- isc is short for is_clm
def isc (L : clm E F) : is_continuous_linear_map L := L.2

-- functional extensionality
def ext {L M : clm E F} (e : ∀ v, L⬝v = M⬝v) : L = M := 
subtype.eq (funext e)

-- construct isc given function that is extensionally equal
def subst (L : clm E F) (M : E → F) (e : ∀ v, L⬝v = M v) : clm E F :=
-- TODO: I don't know how the proof part works
⟨M, by rw ← (funext e : coe_fn L = M); exact L.isc⟩
-- TODO: this rewrite rule doesn't typecheck!! (it was taken directly from poly unless I messed that up)
-- @[simp] theorem subst_eval (L M e v) : subst L M e v = M v := rfl

-- composition
-- TODO: this should probably be an instance
def clm_comp : clm E F → clm F G → clm E G := λ L M, ⟨λ v, M (L v), is_continuous_linear_map.comp L.2 M.2⟩
local notation M `∘` L := clm_comp L M

-- each of the identities and operations comes with an instance that tells Lean what it is and a simplification lemma that gives Lean a hint about how to "evaluate" it

-- zero map
def zero : clm E F := ⟨λ v, 0, is_continuous_linear_map.zero⟩
instance : has_zero (clm E F) := ⟨clm.zero⟩
@[simp] theorem zero_eval (v) : (0 : clm E F)⬝v = 0 := rfl

-- identity map
-- TODO: not sure if this is necessary or even desirable
def one : clm E E := ⟨λ v, v, is_continuous_linear_map.id⟩
instance : has_one (clm E E) := ⟨clm.one⟩
@[simp] theorem one_eval (v) : (1 : clm E E)⬝v = v := rfl

def add : clm E F → clm E F → clm E F := λ L M, ⟨L + M, is_continuous_linear_map.add L.isc M.isc⟩
instance : has_add (clm E F) := ⟨clm.add⟩
@[simp] theorem add_eval : Π (L M : clm E F) v, (L + M)⬝v = L⬝v + M⬝v
| ⟨L, pL⟩ ⟨M, pM⟩ v := rfl

def neg : clm E F → clm E F := λ L, ⟨λ v, -(L⬝v), is_continuous_linear_map.neg L.isc⟩
instance : has_neg (clm E F) := ⟨clm.neg⟩

def sub : clm E F → clm E F → clm E F := λ L M, L + (-M)
instance : has_sub (clm E F) := ⟨clm.sub⟩
@[simp] theorem sub_eval : Π (L M : clm E F) v, (L - M)⬝v = L⬝v - M⬝v
| ⟨L, pL⟩ ⟨M, pM⟩ v := rfl

-- TODO: this proof doesn't work even though it does for poly
-- possibly b/c neg and sub are defined differently?
-- TODO: this feels weird being disconnected from neg
@[simp] theorem neg_eval (L : clm E F) (v) : (-L)⬝v = -(L⬝v) := sorry
-- show (0 - L) v = _, by simp

def smul : k → clm E F → clm E F := λ c L, ⟨λ v, c•(L⬝v), is_continuous_linear_map.smul c L.isc⟩
instance : has_scalar k (clm E F) := ⟨clm.smul⟩
-- TODO: prove it
@[simp] theorem smul_eval : Π c (L : clm E F) v, (c•L)⬝v = c•(L⬝v) := sorry

-- need these instances up here to prove stuff about the op norm
-- TODO: go straight to module?
instance : add_comm_group (clm E F) := by refine
{
  add := (+),
  zero := 0,
  neg := has_neg.neg,
  ..
};
{ intros; exact ext (λ v, by simp) }

-- TODO: use refine
instance : module k (clm E F) :=
{
  smul := (•),
 
  smul_add := by intros; exact ext (λ v, by simp [smul_add]),
  add_smul := by intros; exact ext (λ v, by simp [add_smul]),
  mul_smul := by intros; exact ext (λ v, by simp [mul_smul]),
  one_smul := by intros; exact ext (λ v, by simp [one_smul]),
}

/- Operator Norm -/

-- TODO: this might be better in a different section, but we'll keep it here for now

-- TODO: leverage boundedness proof above to show that Inf has a value
-- TODO: big ops should make this easier to define (I think)
def op_norm : clm E F → ℝ := λ L, Inf { M : ℝ | M ≥ 0 ∧ ∀ v : E, ∥L⬝v∥ ≤ M * ∥v∥ }
-- TODO: implement has_norm
-- instance : has_norm (clm E F) := ⟨clm.op_norm⟩

-- an alternate version that allows for easier proofs
theorem op_norm_alt : ∀ L : clm E F, op_norm L = Sup { c : ℝ | ∃ v, ∥v∥ ≤ 1 ∧ ∥L⬝v∥ = c } := sorry

theorem op_norm_inhabited {L : clm E F} : (0:ℝ) ∈ { c : ℝ | ∃ v, ∥v∥ ≤ 1 ∧ ∥L⬝v∥ = c } :=
begin
existsi (0:E),
split,
simp [zero_le_one],
apply norm_zero_iff_zero.2,
-- follows from L being a linear map
end

-- TODO: uglier than it should be
theorem op_norm_nonneg {L : clm E F} : op_norm L ≥ 0 :=
begin
unfold op_norm ge,
apply real.lb_le_Inf,
-- bounded
{
  simp,
  have : is_bounded L,
  begin
    -- exact bounded_continuous_linear_map L.isc,
    admit
  end,
  unfold is_bounded at this,
  cases this,
  cases this_h,
  existsi _,
  split,
  apply le_of_lt,
  assumption,
  assumption
},
{
  intro,
  simp,
  intros,
  assumption
}
end

theorem op_norm_zero_iff_zero {L : clm E F} : op_norm L = 0 ↔ L = 0 :=
begin
split,
{
  rw [op_norm_alt],
  admit
},
admit
end

theorem op_norm_pos_homo : ∀ c (L : clm E F), op_norm (c•L) = ∥c∥ * op_norm L := sorry

theorem op_norm_triangle : ∀ (L M : clm E F), op_norm (L + M) ≤ op_norm L + op_norm M :=
begin
intros,
simp [op_norm_alt],
admit
end

-- TODO: is there a way to get the auto-induced metric from a norm without doing any work? Don't do this for now

def op_dist : clm E F → clm E F → ℝ := λ L M, op_norm (L - M)

theorem op_dist_self : ∀ x : clm E F, op_dist x x = 0 :=
begin
intros,
unfold op_dist,
apply op_norm_zero_iff_zero.2,
simp [add_left_neg]
end

theorem op_dist_eq_of_dist_eq_zero : ∀ (x y : clm E F), op_dist x y = 0 → x = y :=
begin
unfold op_dist,
intros x y h,
apply sub_eq_zero.1,
apply op_norm_zero_iff_zero.1,
assumption
end
-- TODO: clm is an instance of normed_space

theorem op_dist_comm : ∀ (x y : clm E F), op_dist x y = op_dist y x :=
begin
intros,
simp [op_dist, op_norm],
congr,
funext,
admit,
-- the propositions are the same by the pos_homo for the underlying norm
end

theorem op_dist_triangle : ∀ (x y z : clm E F), op_dist x z ≤ op_dist x y + op_dist y z :=
begin
intros,
unfold op_dist,
calc
op_norm (x - z) = op_norm ((x - y) + (y - z)) : by simp
            ... ≤ op_norm (x - y) + op_norm (y - z) : by apply op_norm_triangle
end

/- Continuous Linear Maps form a normed vector space. -/

-- This is crucial for differentiation.

-- TODO: solve
instance : metric_space (clm E F) :=
{
  dist := op_dist,
  
  dist_self := op_dist_self,
  eq_of_dist_eq_zero := op_dist_eq_of_dist_eq_zero,
  dist_comm := op_dist_comm,
  dist_triangle := op_dist_triangle
}

instance : normed_space k (clm E F) :=
{
  norm := op_norm,

  dist_eq := by intros; refl,
  norm_smul := op_norm_pos_homo
}

end
end clm
