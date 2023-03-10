import tactic.interactive
import .order_emb
import order.order_iso_nat
import data.finset.sort

noncomputable theory

/-!
# The canonical Ramsey theorem
-/

/-!
### Vocabulary
-/

/-- An edge of the complete `d`-uniform hypergraph on `ℕ`. -/
@[reducible] def edge (d : ℕ) : Type* := fin d ↪o ℕ

instance edge_finite {d : ℕ} : infinite (edge d.succ):=
begin
  set f: ℕ → edge d.succ:= λ x, rel_embedding.trans (@fin.add_nat d.succ x) (fin.coe_order_embedding (d.succ+x)) with f_def,
  have f_inj: f.injective, intros x y xyeq, rw rel_embedding.ext_iff at xyeq, simp [f_def] at xyeq, assumption,
  apply infinite.of_injective f this,
end

/--
A set of indices for endpoints of a generic edge, identified by their
relative positions with respect to the ordering on `ℕ`. For example,
"the 1st, 3rd, and 4th smallest vertices contained in the edge".
-/
@[reducible] def index_set (d : ℕ) : Type* := set (fin d)

/--
A colouring of the complete `d`-uniform hypergraph on `ℕ`,
with colours taken from `α`.
-/
@[reducible] def colouring (d : ℕ) (α : Type*) : Type* := edge d → α

/-- An infinite subset of `ℕ`, viewed as a subsequence. -/
@[reducible] def subseq : Type := ℕ ↪o ℕ

/-!
### Notation
-/

variables {α β γ : Type*} {d : ℕ}

/--
The actual endpoints of a specific edge identified by an index set.
For example, the restriction of the 5-uniform edge (2, 3, 5, 7, 11)
to the index set "1st, 3rd, and 4th smallest" is (2, 5, 7).
-/
def edge.restrict (e : edge d) (I : index_set d) : I ↪o ℕ :=
rel_embedding.trans (order_embedding.subtype I) e

infix ` |e `:80 := edge.restrict

/--
For a given index set, the canonical colouring in which two edges have
the same colour iff they agree on that index set.
-/
def index_set.canonical (I : index_set d) : colouring d (I ↪o ℕ) :=
λ e, e |e I

/--
The restriction of a colouring to the edges contained in a given
infinite subsequence of `ℕ`.
-/
def colouring.restrict (f : colouring d α) (S : subseq) : colouring d α :=
λ e, f (rel_embedding.trans e S)

infix ` |c `:80 := colouring.restrict

/--
Two colourings are isomorphic iff they induce the same partition on
the set of edges of the `d`-uniform hypergraph on `ℕ`.
-/
def colouring.iso (f : colouring d α) (g : colouring d β) : Prop :=
∀ e₁ e₂, (f e₁ = f e₂) ↔ (g e₁ = g e₂)

infix ` ≃c `:25 := colouring.iso

/-!
### Main statements
-/

/--
The (statement of the) canonical Ramsey theorem:
every colouring contains a canonical subcolouring.
-/
def ramsey.statement (f : colouring d α) : Prop :=
∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical

/-!
The next two lemmas show that `ramsey.statement` is best possible:
each canonical colouring is a distinct fixed point for the operation
of passing to an infinite subsequence of ℕ.
-/

/-- Every subcolouring of a canonical colouring is isomorphic. -/
def canonical_subseq_iso_self.statement (I : index_set d) (S : subseq) : Prop :=
I.canonical |c S ≃c I.canonical

/-- Isomorphic canonical colourings come from identical index sets. -/
def canonical_inj.statement (I J : index_set d) : Prop :=
I.canonical ≃c J.canonical → I = J

/-!
### Constructions and lemmas
-/

/- `≃c` is an equivalence relation. -/
namespace colouring.iso
variables {f : colouring d α} {g : colouring d β} {h : colouring d γ}

@[refl] lemma refl (f : colouring d α) : f ≃c f :=
λ x y, iff.rfl

@[symm] lemma symm : (f ≃c g) → (g ≃c f) :=
λ fg x y, (fg x y).symm

@[trans] lemma trans : (f ≃c g) → (g ≃c h) → (f ≃c h) :=
λ fg gh x y, (fg x y).trans (gh x y)

end /-namespace-/ colouring.iso

/--
A subsequence of a subsequence is a subsequence.
This order of arguments makes `colouring.restrict_restrict` hold.
-/
def subseq.restrict (S T : subseq) : subseq :=
rel_embedding.trans T S

infix ` |s `:80 := subseq.restrict

def subseq.refl : subseq:=
  (order_iso.refl ℕ).to_order_embedding

lemma colouring.restrict_restrict (f : colouring d α) (S T : subseq) :
  f |c S |c T = f |c (S |s T) := rfl

/-- The first `d` endpoints of a `(d+1)`-edge. -/
def edge.head (e : edge (d+1)) : edge d :=
rel_embedding.trans fin.cast_succ e

/-- The last endpoint of a `(d+1)`-edge. -/
def edge.last (e : edge (d+1)) : ℕ := e (fin.last d)

/--
The smallest natural number which is
strictly bigger than all endpoints.
-/
def edge.lub : ∀ {d : ℕ}, edge d → ℕ
| 0     _ := 0
| (d+1) e := (e (fin.last d)) + 1

lemma edge.lt_lub (e : edge d) (i : fin d) :
  e i < e.lub :=
begin
  cases d,
  { exact fin.elim0 i },
  calc e i ≤ e (fin.last d) : e.le_iff_le.mpr (fin.le_last i)
  ...      < e.lub          : lt_add_one (e (fin.last d)),
end

lemma edge.head_lub_le_last (e : edge (d+1)) :
  e.head.lub ≤ e.last :=
begin
  cases d,
  { exact zero_le _ },
  change edge (d+2) at e, change (e ⟨d, _⟩) < e ⟨d+1, _⟩,
  simp only [e.lt_iff_lt, fin.mk_lt_mk, lt_add_one],
end

lemma edge.lub_le_iff {n : ℕ} (e : edge d) : 
  e.lub ≤ n ↔ ∀ i, e i < n := 
begin
  refine ⟨λ h i, (e.lt_lub _).trans_le h,λ h, _⟩, 
  cases d, exact nat.zero_le _, 
  exact nat.lt_iff_add_one_le.mpr (h _), 
end    



/--
The `(d+1)`-edge formed from a `d`-edge
by adding a new largest endpoint.
-/
def edge.of_lub_le (e : edge d) (n : ℕ) (h : e.lub ≤ n) : edge (d+1) :=
order_embedding.of_map_le_iff (@fin.last_cases _ (λ _, ℕ) n e)
begin
  rw [edge.lub_le_iff] at h,  
  refine @fin.last_cases _ _ _ (λ a, _), 
  all_goals {refine @fin.last_cases _ _ _ (λ b, _)},
  all_goals {simp only [fin.last_cases_last, fin.last_cases_cast_succ, fin.last_le_iff, rfl.le, 
    order_embedding.le_iff_le]}, 
  { exact iff_of_false (h _).not_le (b.cast_succ_lt_last.ne)}, 
  exact iff_of_true (h _).le (a.cast_succ_lt_last.le),   
end 
-- begin
--   intros i j,
--   obtain (h_last_le_i | h_i_lt_last) := le_or_lt (fin.last d) i,
--   {
--     rw fin.last_le_iff at h_last_le_i,
--     rw [h_last_le_i, fin.last_cases_last],
--     cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
--     {
--       rw fin.last_le_iff at h_last_le_j,
--       rw [h_last_le_j, fin.last_cases_last],
--       exact iff_of_true (le_refl n) (le_refl (fin.last d)),
--     },
--     {
--       set j' : fin d := j.cast_lt h_j_lt_last,
--       have : j'.cast_succ = j := j.cast_succ_cast_lt _,
--       rw [←this, fin.last_cases_cast_succ],
--       apply iff_of_false; apply not_le_of_lt,
--       calc e j' < e.lub : e.lt_lub j'
--       ...       ≤ n     : h,
--       exact j'.cast_succ_lt_last,
--     },
--   },
--   {
--     set i' : fin d := i.cast_lt h_i_lt_last,
--     have : i'.cast_succ = i := (i.cast_succ_cast_lt _),
--     rw [←this, fin.last_cases_cast_succ],
--     cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
--     {
--       rw fin.last_le_iff at h_last_le_j,
--       rw [h_last_le_j, fin.last_cases_last],
--       apply iff_of_true; apply le_of_lt,
--       calc e i' < e.lub : e.lt_lub i'
--       ...       ≤ n     : h,
--       exact i'.cast_succ_lt_last,
--     },
--     {
--       set j' : fin d := j.cast_lt h_j_lt_last,
--       have : j'.cast_succ = j := j.cast_succ_cast_lt _,
--       rw [←this, fin.last_cases_cast_succ],
--       simp_rw [order_embedding.le_iff_le],
--     },
--   },
-- end

@[simp] lemma edge.of_lub_le_head_eq (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h).head = e :=
by {ext, simp [edge.of_lub_le, edge.head]}

@[simp] lemma edge.of_lub_le_last_eq (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h).last = n :=
by {simp [edge.of_lub_le, edge.last]}

/-!
### Some API
-/



@[ext] lemma edge.ext {e₁ e₂ : edge d} (h : ∀ i, e₁ i = e₂ i) : e₁ = e₂ := 
by {ext, rw h}

@[simp] lemma index_set_apply (e : edge d) (I : index_set d) (i : I) :
  (e |e I) i = e i := rfl 

lemma iso_canonical_iff {I : index_set d} {f : colouring d α} :
  f ≃c I.canonical ↔ ∀ e₁ e₂, f e₁ = f e₂ ↔ ∀ (i : I), e₁ i = e₂ i := 
begin
  unfold colouring.iso index_set.canonical,
  simp_rw rel_embedding.ext_iff,
  refl, 
end 
 
def edge_one_equiv:  ℕ ≃ (edge 1):=
{ to_fun := λ x, finset.order_emb_of_fin {x} (finset.card_singleton x),
  inv_fun := λ x, x 0,
  left_inv := begin
    intro x, simp,
  end,
  right_inv := begin
    intro x, ext, simp,
  end }

/-!
### Main proofs
-/
namespace iterate

lemma order_embedding.le_self (x : ℕ) (f: ℕ ↪o ℕ):
x ≤ f x:=
begin
  induction x with x hx, exact nat.zero_le _, have:= f.map_rel_iff'.2 (le_of_lt (nat.lt_succ_self x)), 
  have inj: f x ≠ f x.succ, intro hf, have:= f.inj' hf, apply nat.succ_ne_self x this.symm,
  have:= lt_of_le_of_ne this inj, rw nat.succ_le_iff, exact lt_of_le_of_lt hx this,
end

#check finite.exists_infinite_fiber
#check nat.order_embedding_of_set


theorem polychromatic_pigeonhole {α β : Type} [infinite α] (f : α → β):
(∃ y : β, infinite (f ⁻¹' {y})) ∨ infinite (set.range f):=
begin
  by_cases (infinite (set.range f)),right, assumption,
  left, rw not_infinite_iff_finite at h,
  set f_aux : α → set.range f:= λ α, ⟨f α, set.mem_range_self α⟩,
  cases @finite.exists_infinite_fiber _ _ _ h f_aux with y hy, use y,
  have : f ⁻¹' {y} = f_aux ⁻¹' {y}, ext, simp [f_aux], split, intro fxy, ext, apply fxy, 
  intro fxy, have :f x ∈ set.range f, apply set.mem_range_self x, rw ← fxy, simp [this],
  rw this, apply hy,
end


lemma seq_mono_poly {α : Type} (f: colouring 1 α) : ∃ S: subseq,
(∀ a b : edge 1, (f |c S) a = (f |c S) b) ∨
(∀ a b : edge 1, a ≠ b → (f |c S) a ≠ (f |c S) b)
:=
begin
  rcases polychromatic_pigeonhole f with ⟨y, hy⟩, set pm:= {x: ℕ | edge_one_equiv x ∈ (f ⁻¹' {y})},
  haveI: infinite pm, set f_pm: pm → f ⁻¹' {y}:= λ x, ⟨edge_one_equiv x.val, x.property⟩ with f_pm_def,
  have f_pm_surj: f_pm.surjective, intro z, use edge_one_equiv.symm z.val, simp, 
  have:= set.mem_preimage.1 z.2, apply set.eq_of_mem_singleton this, rw f_pm_def, simp,
  apply @infinite.of_surjective _ _ hy f_pm f_pm_surj,
  set S:= (nat.subtype.order_iso_of_nat pm).to_order_embedding, 
end

structure mono_poly {d : ℕ} {α : Type} : Type :=
(f: colouring (d+1) α)
(seqhead: ℕ)
(seqtail: subseq)
(canonical: ∀ e : {e : edge d | e.lub ≤ seqhead},
  (∀ a b : {x : ℕ | seqhead ≤ seqtail x}, 
    (f |c seqtail) (e.1.of_lub_le a.1 (le_trans e.2 a.2))=
    (f |c seqtail) (e.1.of_lub_le b.1 (le_trans e.2 b.2))) ∨
  (∀ a b : {x : ℕ | seqhead ≤ seqtail x}, a ≠ b → 
    (f |c seqtail) (e.1.of_lub_le a.1 (le_trans e.2 a.2))≠
    (f |c seqtail) (e.1.of_lub_le b.1 (le_trans e.2 b.2)))
)


def mono_poly_init {d : ℕ} {α : Type} (f : colouring (d+1) α) : mono_poly := 
{ f := f,
  seqhead := {0},
  seqtail := if d=0 then ,
  head_le_tail := _,
  heads_canonical := _ }

def next : state → state
| ⟨ff, n⟩ := ⟨tt, n⟩
| ⟨tt, n⟩ := ⟨ff, n+1⟩

def postprocess : state → ℕ :=
λ (s : state), s.2

def my_seq : ℕ → ℕ :=
λ (n : ℕ), postprocess (nat.iterate next n init)

end /-namespace-/ iterate


variables (d : ℕ) (e : edge d) (a : (Π x : ℕ, e.lub ≤ x))
#check  

def subseq_filter_tail {d : ℕ} {α : Type} (f : colouring (d+1) α): 
∃ S : subseq, ∀ e : (edge d), 
(∀ a b : {x : ℕ | e.lub ≤ x}, 
(f |c S) (e.of_lub_le a.1 a.2) = (f |c S) (e.of_lub_le b.1 b.2)) ∨
∀ a b : {x : ℕ | e.lub ≤ x}, a ≠ b →
(f |c S) (e.of_lub_le a.1 a.2) ≠ (f |c S) (e.of_lub_le b.1 b.2)
:=
begin

end


#check subseq_filter_tail

lemma ramsey {d : ℕ} {α : Type} (f : colouring d α) :
  /- ∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical -/
  ramsey.statement f :=
begin
  change ∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical,
  induction d with d hd, use subseq.refl, use ∅, intros e₁ e₂, 
  have edge_eq: e₁=e₂, ext, apply fin_zero_elim x, simp [edge_eq],
  
end

lemma canonical_subseq_iso_self
  {d : ℕ} (I : index_set d) (S : subseq) :
  /- I.canonical |c S ≃c I.canonical -/
  canonical_subseq_iso_self.statement I S :=
begin
  change I.canonical |c S ≃c I.canonical,
  intros e₁ e₂,
  simp_rw [rel_embedding.ext_iff],
  change (∀ (i : I), S (e₁ i) = S (e₂ i)) ↔ (∀ (i : I), e₁ i = e₂ i),
  simp_rw [order_embedding.eq_iff_eq S],
end


lemma canonical_inj
  {d : ℕ} (I J : index_set d) :
  /- I.canonical ≃c J.canonical → I = J -/
  canonical_inj.statement I J :=
begin
  
  set f₁ : fin d → ℕ := λ i, 2 * i with hf₁_def, 
  have hf₁ : strict_mono f₁ := λ x x' h, by {simpa [hf₁_def]},
  set e₁ := order_embedding.of_strict_mono f₁ hf₁ with he₁, 

  set f₂ : fin d → fin d → ℕ := λ x i, if i = x then 2*i + 1 else 2*i with hf₂_def, 
  have hf₂ : ∀ x, strict_mono (f₂ x),
  { rintros ⟨x,hx⟩ ⟨i,hi⟩ ⟨i',hi'⟩ (hii' : i < i'), 
    simp only [hf₂_def], 
    split_ifs with h h' h',
    all_goals {linarith}}, 

  intro h, 
  ext,
  refine ⟨λ hx, by_contra (λ hx', _),λ hx, by_contra (λ hx', _ )⟩, 
  all_goals 
  { set e₂ := order_embedding.of_strict_mono _ (hf₂ x) with he₂, 
    specialize h e₁ e₂, 
    simp only [index_set.canonical, rel_embedding.ext_iff, index_set_apply, 
      order_embedding.coe_of_strict_mono, set_coe.forall, subtype.coe_mk, hf₁_def, hf₂_def] at h, },
  { simpa using h.mpr (λ i hij, by {rw if_neg, rintro rfl, exact hx' hij, }) _ hx},
  simpa using h.mp (λ i hij, by {rw if_neg, rintro rfl, exact hx' hij, }) _ hx,
end



/-!
### Junk
-/

example (d : ℕ) : fin (d+1) := fin.last d
example (d : ℕ) : fin d ↪o fin (d+1) := fin.cast_succ
example (α : Type) : Type :=
quot (λ (f g : ℕ → α), ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f m = g m)