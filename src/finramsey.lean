import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic

#check order_embedding

def order_embedding.comp {α β γ : Type*} [preorder α] [preorder β] [preorder γ] (f: α ↪o β) (g: β ↪o γ)
: α ↪o γ:=
{ to_fun := g ∘ f,
  inj' := function.injective.comp g.inj' f.inj',
  map_rel_iff' := by simp }

def E (n : ℕ): Type := fin 2 ↪o fin n

def order_embedding.id {α : Type*} [preorder α]: α ↪o α:=
{ to_fun := λ x, x,
  inj' := begin
    intros a b h, apply h,
  end,
  map_rel_iff' := begin
    intros a b, dsimp, refl,  
end }

lemma mem_fin_2 (x : fin 2) : x = 0 ∨ x = 1 :=
begin
  cases x, cases x_val, left, refl,
  cases x_val, right, refl,
  exfalso, repeat {rw nat.succ_lt_succ_iff at x_property}, norm_num at x_property,
end

lemma e2id : ∀ e : E 2, e= order_embedding.id:=
  sorry


theorem finramsey: 
∀ k: ℕ, 2 ≤ k → ∃ n₀: ℕ, ∀ n, n₀ ≤ n → 
∀ f:E n → fin 2,
∃ s: (fin k ↪o fin n),
∃ c : fin 2, ∀ e:E k, f (e.comp s)=c :=
begin
  intros k kg2, induction k with k hk, norm_num at kg2, cases kg2,
  {
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
    use s, use f s, intro e, congr, ext, sorry
  }
end