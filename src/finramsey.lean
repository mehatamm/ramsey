import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic


#check order_embedding

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

@[simp] lemma order_embedding.comp_refl (f: α ↪o β):
  f.comp order_embedding.refl = f :=
begin
  ext, refl,
end

@[reducible] def E (n : ℕ): Type := fin 2 ↪o fin n

def edges_from (n : ℕ) (v : fin n) : set (E n):= {e : E n | e 0 = v}

instance fintype_edges_from {n : ℕ}: fintype ( set (E n)):=
sorry


def has_favorite_color (n : ℕ) (v : fin n) (f : E n → fin 2) :=
∃ c: fin 2, ∀ (e: edges_from n v), f e = c



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

#check function.surjective.range_eq
#check finite.injective_iff_surjective
#check fin_zero_elim
lemma favcolor_procession (k : ℕ): 
∃ n₀: ℕ, ∀ n, n₀ ≤ n → ∀ f: E n → fin 2,
∃ s : (fin (k) ↪o fin n), ∀ v:fin (k), has_favorite_color n (s v) f:=
begin
    induction k with k ih, {use 0, intros n ng f, refine ⟨⟨⟨fin_zero_elim, fin_zero_elim⟩, fin_zero_elim⟩, fin_zero_elim⟩},
    {
      cases ih with n₀ hn₀, use 2*n₀+1, intros n nge2 f, have zltn: 0 < n, have: 0 < 2*n₀+1:= by linarith, apply lt_of_lt_of_le this nge2, 
      set f0 := edges_from n ⟨0, zltn⟩, have pigeonhole: ∃ friends ⊆ f0, fintype.card friends=n₀ → ∃ c : fin 2, ∀ e : friends, f e = c, 
      {

      }

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