import tactic 

section mul 

variables {α : Type*} [has_mul α] [has_zero α] [partial_order α] 

def mul_left_order_embedding [pos_mul_mono_rev α] [pos_mul_mono α] {a : α} (ha : 0 < a) : α ↪o α :=
{ to_fun := λ n, a * n,
  inj' := λ _ _ h, 
  (le_of_mul_le_mul_of_pos_left h.le ha).antisymm (le_of_mul_le_mul_of_pos_left h.symm.le ha),  
  map_rel_iff' := λ _ _,  mul_le_mul_left ha}

@[simp] lemma mul_left_order_embedding_apply [pos_mul_mono_rev α] [pos_mul_mono α] {a : α} 
(ha : 0 < a) {x : α}:
  mul_left_order_embedding ha x = a * x := rfl 

def mul_right_order_embedding [mul_pos_mono_rev α] [mul_pos_mono α] {a : α} (ha : 0 < a) : α ↪o α :=
{ to_fun := λ n, n * a,
  inj' := λ _ _ h, 
  (le_of_mul_le_mul_of_pos_right h.le ha).antisymm (le_of_mul_le_mul_of_pos_right h.symm.le ha),  
  map_rel_iff' := λ _ _,  mul_le_mul_right ha}

@[simp] lemma mul_right_order_embedding_apply [mul_pos_mono_rev α] [mul_pos_mono α] {a : α} 
(ha : 0 < a) {x : α}:
  mul_right_order_embedding ha x = x * a := rfl 

end mul 

section update

variables {α β : Type*} [decidable_eq α]

lemma function.injective.update {f : α → β} {a : α} {b : β} (hf : f.injective) 
(h : ∀ a', f a' = b → a' = a) : (f.update a b).injective := 
begin
  intros x y hxy, 
  obtain ⟨rfl | hx, rfl | hy⟩ := ⟨eq_or_ne x a, eq_or_ne y a⟩, 
  { simp, }, 
  { rw [function.update_same, function.update_noteq hy] at hxy, 
    exact (hy (h _ hxy.symm)).elim},
  { rw [function.update_same, function.update_noteq hx] at hxy, 
    exact (hx (h _ hxy)).elim},
  rw [function.update_noteq hx, function.update_noteq hy] at hxy, 
  exact hf hxy, 
end   

variables  [partial_order α] [partial_order β]

/--
Update an order_embedding `e` by changing the value of `e a` to `b`. 
-/
def order_embedding.update (e : α ↪o β) (a : α) (b : β) (h_le : ∀ x ≠ a, x ≤ a ↔ e x ≤ b) 
(h_ge : ∀ x ≠ a, a ≤ x ↔ b ≤ e x) : α ↪o β :=
{ to_fun := function.update e a b,
  inj' := e.injective.update 
  begin
    rintros x rfl, 
    by_contradiction, 
    exact h (le_antisymm (by simpa using h_le _ h) (by simpa using h_ge _ h)), 
  end ,
  map_rel_iff' := by {
    intros x y, 
    simp only [function.embedding.coe_fn_mk, function.update_apply], 
    split_ifs with h h' h', 
    { simp [h,h']},
    { subst h, 
      rw h_ge _ h', },
    { subst h',
      rw h_le _ h,  },
    rw e.le_iff_le} }

@[simp] lemma order_embedding.update_apply (e : α ↪o β) (a : α) (b : β)
(h_le : ∀ x ≠ a, x ≤ a ↔ e x ≤ b) (h_ge : ∀ x ≠ a, a ≤ x ↔ b ≤ e x) (x : α) :
  (e.update a b h_le h_ge) x = if x = a then b else e x := 
  function.update_apply e a b x

end update
  


-- order_embedding.of_map_le_iff (function.update e a b) 
-- begin
--   intros x y , 
--   obtain ⟨rfl | hx, rfl | hy⟩ := ⟨eq_or_ne a x, eq_or_ne a y⟩, 
--   { simp, },
--   { rw [function.update_same, function.update_noteq hy.symm, hy.le_iff_lt], 


    
--     refine ⟨λ h, _,λ h, _⟩, 
--     { rw ← e.le_iff_le,
--       have := e.le_iff_le }, },
--   -- rw [function.update_apply, function.update_apply, le_iff_eq_or_lt], 
--   -- split_ifs,
--   -- { simp [h,h_1]}, 
--   -- { subst h, }

-- end 