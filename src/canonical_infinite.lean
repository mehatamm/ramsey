import tactic

/-!
# The canonical Ramsey theorem
-/

/-!
### Vocabulary
-/

/-- An edge of the complete `d`-uniform hypergraph on `ℕ`. -/
@[reducible] def edge (d : ℕ) : Type := fin d ↪o ℕ

/--
A subset of the endpoints of a generic edge, identified by their
relative positions with respect to the ordering on `ℕ`. For example,
"the 1st, 3rd, and 4th smallest vertices contained in the edge".
-/
@[reducible] def subedge (d : ℕ) : Type := set (fin d)

/--
A colouring of the complete `d`-uniform hypergraph on `ℕ`,
with colours taken from `α`.
-/
def colouring (d : ℕ) (α : Type) : Type := edge d → α

/-- An infinite subset of `ℕ`, viewed as a subsequence. -/
@[reducible] def subseq : Type := ℕ ↪o ℕ

/-!
### Notation
-/

/--
The actual endpoints of a specific edge identified by a subedge.
For example, the restriction of the 5-uniform edge (2, 3, 5, 7, 11)
to the subedge "1st, 3rd, and 4th smallest" is (2, 5, 7).
-/
def edge.restrict {d : ℕ} (e : edge d) (s : subedge d) : s ↪o ℕ :=
(order_embedding.subtype s).trans e

infix ` |e `:80 := edge.restrict

/--
For a given subedge, the canonical colouring in which two edges have
the same colour iff they agree when restricted to that subedge.
-/
def subedge.colouring {d : ℕ} (s : subedge d) : colouring d (s ↪o ℕ) :=
λ e, e |e s

/--
The restriction of a colouring to the edges contained in a given
infinite subsequence of `ℕ`.
-/
def colouring.restrict {d : ℕ} {α : Type}
  (f : colouring d α) (S : subseq) : colouring d α :=
λ e, f (rel_embedding.trans e S)

infix ` |c `:80 := colouring.restrict

/--
Two colourings are isomorphic iff they induce the same partition on
the set of edges of the `d`-uniform hypergraph on `ℕ`.
-/
def colouring.iso {d : ℕ} {α β : Type}
  (f : colouring d α) (g : colouring d β) : Prop :=
∀ e₁ e₂, (f e₁ = f e₂) ↔ (g e₁ = g e₂)

infix ` ≃c `:25 := colouring.iso

/-!
### Main statements
-/

/--
The (statement of the) canonical Ramsey theorem:
every colouring contains a canonical subcolouring.
-/
def ramsey.statement {d : ℕ} {α : Type} (f : colouring d α) : Prop :=
∃ (S : subseq) (s : subedge d), f |c S ≃c s.colouring

/-!
The next two lemmas show that `ramsey.statement` is best possible:
each canonical colouring is a distinct fixed point for the operation
of passing to an infinite subsequence of ℕ.
-/

/-- Every subcolouring of a canonical colouring is isomorphic. -/
def canonical_colouring_iso.statement
  {d : ℕ} (s : subedge d) (S : subseq) : Prop :=
s.colouring |c S ≃c s.colouring

/-- Isomorphic canonical colourings come from identical subedges. -/
def canonical_colouring_ext.statement
  {d : ℕ} (s t : subedge d) : Prop :=
s.colouring ≃c t.colouring → s = t

/-!
### Constructions and lemmas
-/

/- `≃c` is an equivalence relation. -/
namespace colouring.iso
variables {d : ℕ} {α β γ : Type}
  {f : colouring d α} {g : colouring d β} {h : colouring d γ}

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

lemma colouring.restrict_restrict {d : ℕ} {α : Type}
  (f : colouring d α) (S T : subseq) :
  f |c S |c T = f |c (S |s T) := rfl

/-- The first `d` endpoints of a `(d+1)`-edge. -/
def edge.head {d : ℕ} (e : edge (d+1)) : edge d :=
rel_embedding.trans fin.cast_succ e

/-- The last endpoint of a `(d+1)`-edge. -/
def edge.last {d : ℕ} (e : edge (d+1)) : ℕ := e (fin.last d)

/--
The smallest natural number which is
strictly bigger than all endpoints.
-/
def edge.lub : ∀ {d : ℕ}, edge d → ℕ
| 0     _ := 0
| (d+1) e := (e (fin.last d)) + 1

lemma edge.lt_lub {d : ℕ} (e : edge d) (i : fin d) :
  e i < e.lub :=
begin
  cases d,
  { exact fin.elim0 i },
  calc e i ≤ e (fin.last d) : e.le_iff_le.mpr (fin.le_last i)
  ...      < e.lub          : lt_add_one (e (fin.last d)),
end

lemma edge.head_lub_le_last {d : ℕ} (e : edge (d+1)) :
  e.head.lub ≤ e.last :=
begin
  cases d,
  { exact zero_le _ },
  change edge (d+2) at e, change (e ⟨d, _⟩) < e ⟨d+1, _⟩,
  simp only [e.lt_iff_lt, fin.mk_lt_mk, lt_add_one],
end

/--
The `(d+1)`-edge formed from a `d`-edge
by adding a new largest endpoint.
-/
def edge.of_lub_le {d : ℕ} (e : edge d) (n : ℕ) (h : e.lub ≤ n) : edge (d+1) :=
order_embedding.of_map_le_iff (@fin.last_cases _ (λ _, ℕ) n e)
begin
  intros i j,
  cases le_or_lt (fin.last d) i with h_last_le_i h_i_lt_last,
  {
    rw fin.last_le_iff at h_last_le_i,
    rw [h_last_le_i, fin.last_cases_last],
    cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
    {
      rw fin.last_le_iff at h_last_le_j,
      rw [h_last_le_j, fin.last_cases_last],
      exact iff_of_true (le_refl n) (le_refl (fin.last d)),
    },
    {
      set j' : fin d := j.cast_lt h_j_lt_last,
      have : j'.cast_succ = j := j.cast_succ_cast_lt _,
      rw [←this, fin.last_cases_cast_succ],
      apply iff_of_false; apply not_le_of_lt,
      calc e j' < e.lub : e.lt_lub j'
      ...       ≤ n     : h,
      exact j'.cast_succ_lt_last,
    },
  },
  {
    set i' : fin d := i.cast_lt h_i_lt_last,
    have : i'.cast_succ = i := (i.cast_succ_cast_lt _),
    rw [←this, fin.last_cases_cast_succ],
    cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
    {
      rw fin.last_le_iff at h_last_le_j,
      rw [h_last_le_j, fin.last_cases_last],
      apply iff_of_true; apply le_of_lt,
      calc e i' < e.lub : e.lt_lub i'
      ...       ≤ n     : h,
      exact i'.cast_succ_lt_last,
    },
    {
      set j' : fin d := j.cast_lt h_j_lt_last,
      have : j'.cast_succ = j := j.cast_succ_cast_lt _,
      rw [←this, fin.last_cases_cast_succ],
      simp_rw [order_embedding.le_iff_le],
    },
  },
end

lemma edge.of_lub_le_head_eq {d : ℕ} (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h).head = e :=
begin
  sorry,
end

lemma edge.of_lub_le_last_eq {d : ℕ} (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h).last = n :=
begin
  sorry,
end

/-!
### Main proofs
-/

def ramsey.statement {d : ℕ} {α : Type} (f : colouring d α) : Prop :=
∃ (S : subseq) (s : subedge d), f |c S ≃c s.colouring

lemma canonical_colouring_iso
  {d : ℕ} (s : subedge d) (S : subseq) :
  canonical_colouring_iso.statement s S :=
begin
  change s.colouring |c S ≃c s.colouring,
  intros e₁ e₂,
  simp_rw [rel_embedding.ext_iff],
  change (∀ (i : s), S (e₁ i) = S (e₂ i)) ↔ (∀ (i : s), e₁ i = e₂ i),
  simp_rw [order_embedding.eq_iff_eq S],
end

lemma canonical_colouring_ext
  {d : ℕ} (s t : subedge d) :
  canonical_colouring_ext.statement s t :=
begin
  change s.colouring ≃c t.colouring → s = t,
  sorry,
end

/-!
### Junk
-/

example (d : ℕ) : fin (d+1) := fin.last d
example (d : ℕ) : fin d ↪o fin (d+1) := fin.cast_succ
example (d : ℕ) : (edge (d+1)) ≃ (edge d) × ℕ := sorry

example (α : Type) : Type :=
quot (λ (f g : ℕ → α), ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f m = g m)