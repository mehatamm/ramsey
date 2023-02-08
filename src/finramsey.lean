import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic
import set_theory.cardinal.finite
import combinatorics.pigeonhole



#check order_embedding

noncomputable theory 
open_locale classical 
variables {α β γ : Type*} [preorder α] [preorder β] [preorder γ]

def order_embedding.refl : α ↪o α:=
  (order_iso.refl α).to_order_embedding

def order_embedding.comp (f: α ↪o β) (g: β ↪o γ)
: α ↪o γ:=
{ to_fun := g ∘ f,
  inj' := function.injective.comp g.inj' f.inj',
  map_rel_iff' := by simp }

@[simp] lemma order_embedding.comp_apply (f: α ↪o β) (g: β ↪o γ) (x : α) :
  f.comp g x = g (f x) :=
by {unfold order_embedding.comp, refl}

@[simp] lemma order_embedding.refl_comp (f: α ↪o β):
  order_embedding.refl.comp f = f :=
begin
  ext, refl,
end

def order_embedding.of_is_empty {a b : Type*} [preorder a] [preorder b] [is_empty a] : a ↪o b :=
⟨function.embedding.of_is_empty, is_empty_elim⟩




instance order_embedding.fintype [fintype α] [fintype β] : fintype (α ↪o β) := 
@fintype.of_finite (α ↪o β)
  (@finite.of_injective (α ↪o β) (α → β) _ (λ f, (f : α → β)) (fun_like.coe_injective))

@[simp] lemma order_embedding.comp_refl (f: α ↪o β):
  f.comp order_embedding.refl = f :=
begin
  ext, refl,
end

lemma mem_fin_2 (x : fin 2) : x = 0 ∨ x = 1 :=
begin
  cases x, cases x_val, left, refl,
  cases x_val, right, refl,
  exfalso, repeat {rw nat.succ_lt_succ_iff at x_property}, norm_num at x_property,
end

instance embedding_unique_of_linear_order {k : ℕ} : unique (fin k ↪o fin k):=
begin
  refine ⟨⟨order_embedding.refl⟩, _⟩, intro a, apply fin.order_embedding_eq, repeat {rw function.surjective.range_eq},
  all_goals{ apply finite.injective_iff_surjective.1 _, apply fintype.finite, apply fin.fintype, exact (_ : fin k ↪o fin k).inj', },
end

@[reducible] def E (n : ℕ): Type := fin 2 ↪o fin n

--instance edge_order {n : ℕ} : linear_order (E n):= sorry

def edge_upconvert {i : ℕ} {n : ℕ} (e : E i)(h: i ≤ n) : E n:=
{ to_fun := λ x, fin.cast_le h (e x),
  inj' := begin
    intros x y, simp, 
  end,
  map_rel_iff' := begin
    intros a b, simp,
  end }
/-
@[reducible] def edge {n: ℕ} {i j : fin n} (hl: i < j): E n:= --worst thing i've written in lean so far
{ to_fun := λ x, if h: x = 0 then i else j,
  inj' := begin
    intros a b abeq, cases mem_fin_2 a, {
      cases mem_fin_2 b, {
        simp [h, h_1],
      },
      dsimp at abeq, simp[h, h_1] at abeq, apply absurd abeq (ne_of_lt hl), --figure out how to use ite
    },
    cases mem_fin_2 b, dsimp at abeq, simp[h, h_1] at abeq, apply absurd abeq.symm (ne_of_lt hl), 
    simp [h, h_1],
  end,
  map_rel_iff' := begin
    intros a b, split, intro aleb,
    cases mem_fin_2 a, {
      cases mem_fin_2 b, 
      {
        simp [h, h_1, le_refl],
      },
      rw [h, h_1], norm_num,
    },
    cases mem_fin_2 b, 
    {
      simp [h, h_1] at aleb, apply absurd hl (not_lt_of_le aleb), 
    },
    simp [h, h_1, le_refl], intro aleb, 
    cases mem_fin_2 a, {
      cases mem_fin_2 b, 
      {
        simp [h, h_1], 
      },
      simp [h, h_1], apply le_of_lt hl, 
    },
    cases mem_fin_2 b, 
      {
        rw [h, h_1] at aleb, norm_num at aleb,
      },
      simp [h, h_1], 
  end }
-/
variables {η ζ : Type*}
theorem finset.exists_le_card_fiber_of_mul_le_card_to_type [decidable_eq ζ] [fintype ζ] [nonempty ζ] {s : finset η} (f : η → ζ) {n : ℕ} (hn : fintype.card ζ * n ≤ s.card) :
∃ (y : ζ), n ≤ (finset.filter (λ (x : η), f x = y) s).card:=
begin
  set t: finset ζ:= finset.univ with t_def, have hf: ∀ a: η, a ∈ s → f a ∈ t:= by simp, 
  have ht: t.nonempty, rw finset.nonempty, simp, 
  rw ← finset.card_univ at hn, rw ← t_def at hn,
  rcases finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hf ht hn with ⟨y, h, hy⟩,
  use y, apply hy,
end


@[reducible] def edges_from (n : ℕ) (v : fin n) : set (E n):= {e : E n | e 0 = v}

--@[reducible] def edges_from2 (n : ℕ) (v : fin n): Type := {e : E n // e 0 = v} --define as subtype to make pigeonhole easier



lemma edges_from_card {n k : ℕ} {v : fin n}(hvk : n = v + 1 + k)  : fintype.card (edges_from n v) = k :=
begin
  have eq: fin k ≃ edges_from n v:=
  {
    to_fun:=begin
      rintros ⟨i, lk⟩, have vltn: ((v:ℕ)+i+1) < n, linarith, have vlvi: (v:ℕ) < v+ i + 1,
      linarith, have vlvif: v < ⟨v+i+1, vltn⟩, apply vlvi, refine ⟨edge vlvif, _⟩, dsimp, refl, 
    end,
    inv_fun:=begin
      rintros ⟨e, e0⟩, have le12: (0:fin 2) ≤ (1:fin 2):= by norm_num, have e01:=e.map_rel_iff.2 le12, 
      have: e 0 = v, apply e0, rw this at e01, use e 1 - v, sorry,
    end,
    left_inv:=sorry,
    right_inv:=sorry,
  }
end

def has_favorite_color (n : ℕ) (v : fin n) (f : E n → fin 2) :=
∃ c: fin 2, ∀ (e ∈ edges_from n v), f e = c

#check function.surjective.range_eq
#check finite.injective_iff_surjective
#check fin_zero_elim

#check fintype.exists_le_card_fiber_of_mul_le_card
#check finset.order_emb_of_fin

lemma favcolor_procession (k : ℕ): 
∃ n₀: ℕ, ∀ n, n₀ ≤ n → ∀ f: E n → fin 2,
∃ s : (fin (k) ↪o fin n), ∀ v:fin (k), has_favorite_color n (s v) f:=
begin
    induction k with k ih, {use 0, intros n ng f, refine ⟨⟨⟨fin_zero_elim, fin_zero_elim⟩, fin_zero_elim⟩, fin_zero_elim⟩},
    {
      
      cases ih with n₀ hn₀, use 2*n₀+1, intros n nge2 f, 
      
      cases n, linarith, 
            
      set f0 := edges_from (n+1) ⊥ with f0_def, 
      have f0c: (fintype.card(fin 2))*n₀ ≤ f0.to_finset.card, sorry, --figure out how to represent f0 cardinality
      have pigeonhole: 
        ∃ friends : (finset (E (n+1))), friends ⊆ f0.to_finset ∧ n₀ ≤ finset.card friends ∧ ∃ c : fin 2, ∀ e ∈ friends, f e = c, 
      { 
        cases finset.exists_le_card_fiber_of_mul_le_card_to_type f f0c with y hy,
        use (finset.filter (λ (x: E n.succ), f x = y) f0.to_finset),
        refine ⟨_, hy, _⟩, simp, use y, intros e emem, exact (finset.mem_filter.1 emem).2, 
      }, 
      rcases pigeonhole with ⟨friends, fss, ⟨fcard, color, fcolor⟩⟩,
      have fclens: friends.card ≤ n.succ, sorry, --f0 card issue again
      set f_friends: E friends.card → fin 2:=λ x, f (edge_upconvert x fclens),
      cases hn₀ friends.card fcard f_friends with s₀ hs₀, --gets uncertain after this
      set friendvs := finset.image (λ (x : E n.succ), x 1) friends, 
      have vinj: set.inj_on (λ (x : E n.succ), x 1) friends,
      {
        intros x xf y yf xyv, ext, cases mem_fin_2 x_1, rw h, have xf0: x ∈ f0,
        apply set.mem_to_finset.1 (fss xf), have yf0: y ∈ f0,
        apply set.mem_to_finset.1 (fss yf), simp at xf0 yf0, simp [yf0, xf0], 
        rw h, dsimp at xyv, rw xyv, 
      }, 
      have fvemb:= finset.order_emb_of_fin friendvs (finset.card_image_of_inj_on vinj), 
      have proc_in_friends:= order_embedding.comp s₀ fvemb, 
    },
end

theorem finramsey: 
∀ k: ℕ, 2 ≤ k → ∃ n₀: ℕ, ∀ n, n₀ ≤ n → 
∀ f:E n → fin 2,
∃ s: (fin k ↪o fin n),
∃ c : fin 2, ∀ e:E k, f (e.comp s)=c :=
begin
  intros k kg2, induction k with k hk, norm_num at kg2, cases kg2 with ke2 kg2,
  { --valiant effort but wrong strategy
    use 2, intros n ng2 f, let s: fin 2 ↪o fin n := 
    {to_fun := λ x, ⟨x.val, lt_of_lt_of_le x.property ng2⟩,
    inj' := 
    begin
      intros a b h, dsimp at h, apply fin.eq_of_veq, apply fin.veq_of_eq h,
    end,
    map_rel_iff' := 
    begin
      intros a b, dsimp, refl,
    end},
    use s, use f s, intro e, congr, simp, have h: e=order_embedding.refl, {
      apply subsingleton.elim (_ : fin 2 ↪o fin 2) _, 
    }, rw h, simp,
  }, change 2 ≤ k at kg2, cases hk kg2 with n₀ hn₀, 
end