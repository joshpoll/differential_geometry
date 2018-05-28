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
lemma comp {M : G → E} (hL : is_continuous_linear_map L) (hM : is_continuous_linear_map M) : is_continuous_linear_map L → is_continuous_linear_map M → is_continuous_linear_map (L ∘ M)
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
variables {k : Type u} {E : Type v} {F : Type w}
variables [normed_field k] [normed_space k E] [normed_space k F]
variables {c : k} {v w : E} {L : continuous_linear_map E F}
include k

instance : has_coe_to_fun (continuous_linear_map E F) := ⟨_, subtype.val⟩

@[extensionality]
theorem ext {M : continuous_linear_map E F} (h : ∀ v, L v = M v) : L = M := subtype.eq $ funext h

lemma is_continuous_linear_map_coe : is_continuous_linear_map L := L.property

@[simp] lemma map_add  : L (v + w) = L v + L w := is_continuous_linear_map_coe.add v w
@[simp] lemma map_smul : L (c • v) = c • L v := is_continuous_linear_map_coe.smul c v
@[simp] lemma map_zero : L 0 = 0 := is_continuous_linear_map_coe.zero
@[simp] lemma map_neg  : L (-v) = -L v := is_continuous_linear_map_coe.neg _
@[simp] lemma map_sub  : L (v - w) = L v - L w := is_continuous_linear_map_coe.sub _ _



end continuous_linear_map
