/- 
  Continuous Linear Maps

  These are a well-behaved subset of all linear maps. In finite dimensional normed vector spaces, all linear maps are continuous. For a certain type of normed space (which?), continuous linear maps and bounded linear maps are the same.

  The derivative of f : E → F is f' : E → continuous_linear_map E F.
 -/

import differentiability.normed_space

universes u v w x

-- TODO: maybe continuous should be a structure and not a regular prop
structure is_continuous_linear_map {k : Type u} {E : Type v} {F : Type w} [normed_field k] [normed_space k E] [normed_space k F] (L : E → F) extends is_linear_map L : Prop :=
(continuous : continuous L)

namespace is_continuous_linear_map
variables {k : Type u} {E : Type v} {F : Type w} {G : Type x}
variables [normed_field k] [normed_space k E] [normed_space k F] [normed_space k G]
variable {L : E → F}
include k

section
variable (hL : is_continuous_linear_map L)
include hL

-- linear map simp lemmas
@[simp] lemma zero : L 0 = 0 := hL.to_is_linear_map.zero
@[simp] lemma neg (v : E) : L (- v) = - L v := hL.to_is_linear_map.neg _
@[simp] lemma sub (v w : E) : L (v - w) = L v - L w := hL.to_is_linear_map.sub _ _
@[simp] lemma sum {ι : Type x} {t : finset ι} {f : ι → E} : L (t.sum f) = t.sum (λi, L (f i)) := hL.to_is_linear_map.sum

end

-- TODO: is_linear_map and continuous have different order conventions for this theorem. adopting is_linear_map's
lemma comp {M : G → E} : is_continuous_linear_map L → is_continuous_linear_map M → is_continuous_linear_map (L ∘ M)
| ⟨L_lin, L_cont⟩ ⟨M_lin, M_cont⟩ := ⟨is_linear_map.comp L_lin M_lin, continuous.comp M_cont L_cont⟩

lemma id : is_continuous_linear_map (id : E → E) := ⟨is_linear_map.id, continuous_id⟩

-- no inverse thm except for special circumstances

lemma map_zero : is_continuous_linear_map (λv, 0 : E → F) := ⟨is_linear_map.map_zero, continuous_const⟩

-- TODO: could move hypothesis to the left if continuous was a structure b/c then I could use to_is_continuous
lemma map_neg : is_continuous_linear_map L → is_continuous_linear_map (λv, - L v)
| ⟨lin, cont⟩ := ⟨is_linear_map.map_neg lin, continuous_neg cont⟩

lemma map_add {M : E → F} : is_continuous_linear_map L → is_continuous_linear_map M → is_continuous_linear_map (λv, L v + M v)
| ⟨L_lin, L_cont⟩ ⟨M_lin, M_cont⟩ := ⟨is_linear_map.map_add L_lin M_lin, continuous_add L_cont M_cont⟩

-- TODO: I don't understand this lemma so I don't want to translate it
/- lemma map_sum [decidable_eq δ] {t : finset δ} {f : δ → β → γ} :
  (∀d∈t, is_linear_map (f d)) → is_linear_map (λb, t.sum $ λd, f d b) -/

lemma map_sub {M : E → F} : is_continuous_linear_map L → is_continuous_linear_map M → is_continuous_linear_map (λv, L v - M v)
| ⟨L_lin, L_cont⟩ ⟨M_lin, M_cont⟩ := ⟨is_linear_map.map_sub L_lin M_lin, continuous_sub L_cont M_cont⟩

-- TODO: this requires topological vector spaces
/- lemma map_smul_right {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [module α β] [module α γ]
  {f : β → γ} {r : α} (hf : is_linear_map f) :
  is_linear_map (λb, r • f b) -/

-- TODO: this requires topological vector spaces
/- lemma map_smul_left {f : γ → α} (hf : is_linear_map f) : is_linear_map (λb, f b • x) -/

end is_continuous_linear_map

-- begins diverging from homeos approach
-- draw from linear_map_module and poly
-- TODO: convert poly-like theorems
def continuous_linear_map {k : Type u} (E : Type v) (F : Type w) [normed_field k] [normed_space k E] [normed_space k F] :=
subtype (@is_continuous_linear_map k E F _ _ _)

namespace continuous_linear_map
variables {k : Type u} {E : Type v} {F : Type w} {G : Type x}
variables [normed_field k] [normed_space k E] [normed_space k F] [normed_space k G]
variables {c : k} {v w : E} {L M : continuous_linear_map E F}
include k

instance : has_coe_to_fun (continuous_linear_map E F) := ⟨_, subtype.val⟩

@[extensionality]
theorem ext {M : continuous_linear_map E F} (h : ∀ v, L v = M v) : L = M := subtype.eq $ funext h

lemma is_clm (L : continuous_linear_map E F) : is_continuous_linear_map L := L.property

def subst (L : continuous_linear_map E F) (M : E → F) (e : ∀ v, L v = M v) : continuous_linear_map E F :=
⟨M, by rw ← (funext e : coe_fn L = M); exact L.is_clm⟩

def comp (L :continuous_linear_map F G) (M : continuous_linear_map E F) : continuous_linear_map E G := ⟨λv, L (M v), is_continuous_linear_map.comp L.is_clm M.is_clm⟩

@[simp] lemma map_add  : L (v + w) = L v + L w := L.is_clm.add v w
@[simp] lemma map_zero : L 0 = 0 := L.is_clm.zero
@[simp] lemma map_smul : L (c • v) = c • L v := L.is_clm.smul c v
@[simp] lemma map_neg  : L (-v) = -L v := L.is_clm.neg _
@[simp] lemma map_sub  : L (v - w) = L v - L w := L.is_clm.sub _ _

section add_comm_group

def add : continuous_linear_map E F → continuous_linear_map E F → continuous_linear_map E F := λ L M, ⟨L + M, is_continuous_linear_map.map_add L.is_clm M.is_clm⟩

def zero : continuous_linear_map E F := ⟨λv, 0, is_continuous_linear_map.map_zero⟩

def neg : continuous_linear_map E F → continuous_linear_map E F := λ L, ⟨λv, -(L v), is_continuous_linear_map.map_neg L.is_clm⟩

instance : has_add (continuous_linear_map E F) := ⟨add⟩
instance : has_zero (continuous_linear_map E F) := ⟨zero⟩
instance : has_neg (continuous_linear_map E F) := ⟨neg⟩

@[simp] lemma add_app : (L + M) v = L v + M v := rfl
@[simp] lemma zero_app : (0 : continuous_linear_map E F) v = 0 := rfl
@[simp] lemma neg_app : (-L) v = -L v := rfl

instance : add_comm_group (continuous_linear_map E F) :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..}; { intros, apply ext, simp }

end add_comm_group

section module

-- TODO: need to prove topological vector space stuff
def smul : k → continuous_linear_map E F → continuous_linear_map E F := λ c L, ⟨λ v, c•(L v), is_continuous_linear_map.smul_right c L.is_clm⟩

instance : has_scalar k (continuous_linear_map E F) := ⟨smul⟩

@[simp] lemma smul_app : (c • L) v = c • (L v) := rfl

instance : module k (continuous_linear_map E F) :=
by refine {smul := (•), ..continuous_linear_map.add_comm_group, ..};
  { intros, apply ext, simp [smul_add, add_smul, mul_smul] }

end module

section normed_vector_space

-- TODO!

end normed_vector_space

end continuous_linear_map
