import .order_emb 

open_locale classical 

lemma subseq.reachable_trans (S₀ S₁ : subseq) (h: ∀ i : ℕ, ∃ k : ℕ, S₀ k = S₁ i):
∃ T : subseq, S₁ = rel_embedding.trans T S₀:=
begin
  choose! f hf using h, use f, intros a b abeq, have:= hf b, rw abeq.symm at this, 
  rw hf a at this, apply S₁.inj' this, intros a b, dsimp, have:=S₁.map_rel_iff',
   nth_rewrite 1 ← this, show f a ≤ f b ↔ S₁ a ≤ S₁ b, rw ←hf a, rw ← hf b, 
   exact S₀.map_rel_iff'.symm, exact a, exact b, ext, 
   simp [hf x],
end

lemma subseq.trans_refl {S : subseq} : S = (@rel_embedding.refl ℕ (≤)).trans S:=
begin
  ext, simp,
end

lemma subseq.trans_assoc {a b c : subseq} : 
a.trans (b.trans c) = (a.trans b).trans c:=
begin
  ext, simp,
end

theorem constraints_apply (constraints: ℕ → subseq → Prop)
(constraints_stable: ∀ g : ℕ, ∀ S T : subseq, constraints g S → constraints g (rel_embedding.trans T S))
(constraints_reachable: ∀ (g : ℕ) (S : subseq), ∃ (T : subseq), 
  (∀ i ≤ g, T i = i) ∧ constraints g (rel_embedding.trans T S)) :
  ∀ S : subseq, ∃ T : subseq, ∀ g, constraints g (rel_embedding.trans T S) :=
begin
  intro S, 
  -- set s0 := @rel_embedding.refl ℕ (≤),  
  
  choose! f hf using constraints_reachable,  

  set f' : (ℕ × subseq) → (ℕ × subseq) := λ p, ⟨p.1 + 1, rel_embedding.trans (f p.1 p.2) p.2⟩ with hf',     

  set seqs : ℕ → subseq := λ i, (f'^[i] ⟨0,S⟩).2 with h_seqs,   

  set the_seq : ℕ → ℕ := λ i, (seqs i) i with h_the_seq,  
  have f'_iterate_count: ∀ n, (f'^[n] (0, S)).1=n, 
    { intro n, induction n with n hn,
    rw function.iterate_zero f', refl, rw function.iterate_succ_apply' f' n _, 
    nth_rewrite 0 hf', dsimp, rw hn,
    },
  have hterm : ∀ i j, i ≤ j → the_seq i = (seqs j) i, 
  { intros i j hle, 
    simp_rw [h_the_seq, h_seqs], 
    suffices: ∀ d i j, i ≤ j → j-i=d → ((f'^[i] (0, S)).snd) i = ((f'^[j] (0, S)).snd) i, 
    apply this (j-i) i j hle, refl, intro d, induction d with d hd, intros a b aleb asb, 
    have aeb: a = b, apply le_antisymm aleb (nat.sub_eq_zero_iff_le.1 asb), rw aeb,
    intros a b aleb abdiff, have a_eq_a_d:= hd a (a+d) (nat.le_add_right _ _) _,
    swap, rw add_comm, rw nat.add_sub_cancel d a, rw a_eq_a_d, 
    rw nat.sub_eq_iff_eq_add aleb at abdiff, rw nat.succ_add at abdiff, 
    rw add_comm at abdiff, rw abdiff, rw function.iterate_succ_apply' f' (a+d) _,
   nth_rewrite 1 hf', dsimp, rw f'_iterate_count (a+d),
    have:= (hf (a + d) (f'^[a + d] (0, S)).2).1 a (nat.le_add_right a d), rw this, 
  },
  set S₁:subseq :={to_fun := the_seq, inj' := 
    begin
      intros i j hij, 
    wlog hle: i ≤ j, 
    rw [hterm i j hle, hterm j j rfl.le] at hij, apply (seqs j).inj' hij, 
    end
  ,
  map_rel_iff' := 
    begin
      dsimp, 
    intros i j, wlog hle: i ≤ j, 
     rw [hterm i j hle, hterm j j rfl.le], exact (seqs j).map_rel_iff', 
     rw [hterm j i hle, hterm i i rfl.le], exact (seqs i).map_rel_iff',
    end,
  },
  have constr: ∀ i, constraints i (f'^[i.succ] (0, S)).2,
  intro i, rw function.iterate_succ_apply' f' i (0, S), nth_rewrite 0 hf', 
  dsimp, rw f'_iterate_count i, apply (hf i _).2, 
  have seqs_trans: ∀ i j, i ≤ j → ∃ T : subseq, seqs j = rel_embedding.trans T (seqs i),
  {
    intros i j hle, suffices: ∀ d i j : ℕ, i ≤ j → j-i=d → ∃ T : subseq, seqs j = rel_embedding.trans T (seqs i),
    apply this (j-i) i j hle, refl, intro d, induction d with d hd, intros a b aleb asb,
    have aeb: a = b, apply le_antisymm aleb (nat.sub_eq_zero_iff_le.1 asb), rw aeb,
    use @rel_embedding.refl ℕ (≤), exact subseq.trans_refl, intros a b aleb abdiff, 
    cases hd a (a+d) (nat.le_add_right _ _) _ with T₀ hT₀, 
    swap, rw add_comm, rw nat.add_sub_cancel d a, 
    rw nat.sub_eq_iff_eq_add aleb at abdiff, rw nat.succ_add at abdiff, 
    rw add_comm at abdiff, rw abdiff, 
    have seqs_succ: seqs ((a+d).succ) = (f' ((a+d), seqs (a+d))).2,
    {
      nth_rewrite 0 h_seqs, simp [function.iterate_succ_apply'], 
      rw f'_iterate_count (a+d),  
    },
    rw seqs_succ, rw hf', rw hT₀, dsimp, 
    use rel_embedding.trans (f (a + d) (rel_embedding.trans T₀ (seqs a))) T₀, 
    exact subseq.trans_assoc, 
  },
  have reachable_from_step: ∀ n : ℕ, ∃ T : subseq, S₁= rel_embedding.trans T (f'^[n] (0, S)).2,
  { intro n, 
    apply subseq.reachable_trans _ S₁, intro i, cases le_or_gt n i, 
    cases seqs_trans n i h with T ht, simp [h_the_seq, ht], simp [h_the_seq],
    use i, 
    exact (hterm i n (le_of_lt h.lt)).symm },
  cases reachable_from_step 0 with T₀ hT₀, 
  use T₀, intro g, simp at hT₀, rw ←hT₀, cases reachable_from_step g.succ with T₁ ht₁,
  rw ht₁, 
  apply constraints_stable g _ T₁, 
  apply constr g,  
end




