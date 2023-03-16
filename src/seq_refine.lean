import .canonical_infinite 

open_locale classical 

theorem constraints_apply (constraints: ℕ → subseq → Prop)
(constraints_stable: ∀ g : ℕ, ∀ S T : subseq, constraints g S → constraints g (rel_embedding.trans S T))
(constraints_reachable: ∀ (g : ℕ) (S : subseq), ∃ (T : subseq), 
  (∀ i ≤ g, T i = i) ∧ constraints g (rel_embedding.trans S T)) :
  ∀ S : subseq, ∃ T : subseq, ∀ g, constraints g (rel_embedding.trans S T) :=
begin
  intro S, 
  -- set s0 := @rel_embedding.refl ℕ (≤),  
  
  choose! f hf using constraints_reachable,  

  set f' : (ℕ × subseq) → (ℕ × subseq) := λ p, ⟨p.1 + 1, f p.1 p.2⟩ with hf',     

  set seqs : ℕ → subseq := λ i, (f'^[i] ⟨0,S⟩).2 with h_seqs,   

  set the_seq : ℕ → ℕ := λ i, (seqs i) i with h_the_seq,  
  
  have hterm : ∀ i j, i ≤ j → the_seq i = (seqs j) i, 
  { intros i j hle, 
    simp_rw [h_the_seq, h_seqs], 
    sorry},
  
  use the_seq, 
  { intros i j hij, 
    have hle : i ≤ j, sorry,   
    rw [hterm i j hle, hterm j j rfl.le] at hij, 
    sorry 
    -- Injectivity 
    },

  { dsimp, 
    sorry},
  
  intros g, simp_rw [h_the_seq, h_seqs], 
  

  -- have next_h : ∀ t seq, ∃ next_seq,   
  -- set next : (ℕ × subseq) → (ℕ × subseq) := λ p,   


end




