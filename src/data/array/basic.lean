import data.array.lemmas data.list.dict

namespace fin

def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

end fin

namespace array
variables {α : Type*} {n : ℕ}

def modify (a : array n α) (i : fin n) (f : α → α) : array n α :=
a.write i $ f $ a.read i

@[simp] theorem modify_id (a : array n α) (i : fin n) : a.modify i id = a :=
array.ext $ λ j, by by_cases h : i = j; simp [h, modify]

@[simp] theorem read_modify (a : array n α) (i : fin n) (f : α → α) :
  read (a.modify i f) i = f (read a i) :=
by simp [modify]

@[simp] theorem read_modify_of_ne {i j : fin n} (a : array n α) (f : α → α) (h : i ≠ j) :
  read (a.modify i f) j = read a j :=
by simp [modify, h]

@[simp] theorem rev_foldl_zero {β : Type*} {d : β} (a : array 0 α) (f : α → β → β) :
  a.rev_foldl d f = d :=
rfl

@[simp] theorem to_list_zero (a : array 0 α) : a.to_list = [] :=
rfl

@[simp] theorem rev_list_zero (a : array 0 α) : a.rev_list = [] :=
rfl

theorem read_pop_back {v : α} {a : array (n+1) α} :
  (∀ (i : fin (n+1)), a.read i = v) ↔
  a.read (fin.last n) = v ∧ ∀ (i : fin n), a.pop_back.read i = v :=
iff.intro
  (λ h, ⟨h (fin.last n), λ i, by rw ←h i.raise; cases i; refl⟩)
  (λ h i, begin
    cases i with i i_lt_succ_n,
    by_cases p : i = n,
    { subst p, rw ←h.1, refl },
    { rw ←h.2 ⟨i, nat.lt_of_le_and_ne (nat.le_of_lt_succ i_lt_succ_n) p⟩, refl }
  end)

theorem read_push_back {a : array n α} {v : α} {i : fin n} :
  a.read i = v ↔ (a.push_back v).read i.raise = v ∧ (a.push_back v).read (fin.last n) = v :=
by cases i with _ i_lt_n;
   simp [fin.raise, fin.last, read, push_back, d_array.read, ne_of_lt i_lt_n]

theorem push_back_pop_back {v : α} : ∀ {a : array (n+1) α},
  a.read (fin.last n) = v → a = a.pop_back.push_back v
| ⟨a⟩ h := array.ext $ λ ⟨i, i_lt_n⟩,
  by simp only [push_back, pop_back, read, d_array.read];
     by_cases e : i = n;
     simpa [e] using h

theorem pop_back_push_back (v : α) : ∀ {a : array n α}, a = (a.push_back v).pop_back
| ⟨a⟩ := array.ext $ λ ⟨i, i_lt_n⟩,
  by simp [read, d_array.read, push_back, pop_back, ne_of_lt i_lt_n]

theorem pop_back_rev_list {a : array (n+1) α} :
  a.read (fin.last n) :: a.pop_back.rev_list = a.rev_list :=
by rw ←push_back_rev_list; congr; exact (push_back_pop_back rfl).symm

theorem rev_list_repeat {v : α} : ∀ {n} {a : array n α},
  a.rev_list = list.repeat v n ↔ ∀ i, a.read i = v
| 0 _ := ⟨λ _ i, by cases i.is_lt, by simp⟩
| (n+1) a :=
  ⟨λ h, by rw [list.repeat, ←pop_back_rev_list] at h;
    exact read_pop_back.mpr ⟨list.head_eq_of_cons_eq h, rev_list_repeat.mp (list.tail_eq_of_cons_eq h)⟩,
   λ h, by rw [list.repeat, push_back_pop_back (h (fin.last n)),
    push_back_rev_list (pop_back a) v, rev_list_repeat.mpr (read_pop_back.mp h).2]⟩

theorem to_list_repeat {v : α} {a : array n α} :
  a.to_list = list.repeat v n ↔ ∀ i, a.read i = v :=
by rw [←rev_list_reverse, ←list.reverse_repeat, list.reverse_inj]; exact rev_list_repeat

theorem to_list_join_nil {n} {a : array n (list α)} : a.to_list.join = [] ↔ ∀ i, a.read i = [] :=
by simp [to_list_repeat.symm, list.join_eq_nil, list.eq_repeat]

end array
