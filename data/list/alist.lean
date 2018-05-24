import data.list

namespace list
universes u v
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s : _root_.sigma β}
variables {l l₁ l₂ : list (_root_.sigma β)}
variables [decidable_eq α]

def alist_find (a : α) : list (_root_.sigma β) → option (β a)
| []            := none
| (⟨a₂, b₂⟩::l) := if h : a₂ = a then some (h.rec_on b₂) else alist_find l

section alist_find

@[simp] theorem alist_find_nil : alist_find a ([] : list (_root_.sigma β)) = none :=
rfl

theorem alist_find_cons : alist_find a₁ (⟨a₂, b₂⟩ :: l) = if h : a₂ = a₁ then some (h.rec_on b₂) else alist_find a₁ l :=
rfl

local attribute [simp] alist_find_cons

@[simp] theorem alist_find_cons_eq (h : a₂ = a₁) : b₁ ∈ alist_find a₁ (⟨a₂, b₂⟩ :: l) ↔ b₁ = h.rec_on b₂ :=
by simp [h, eq_comm]

@[simp] theorem alist_find_cons_ne (h : a₂ ≠ a₁) : alist_find a₁ (⟨a₂, b₂⟩ :: l) = alist_find a₁ l :=
by simp [h]

end alist_find

def alist_mem (l : list (_root_.sigma β)) (a : α) : bool :=
(alist_find a l).is_some

section alist_mem

theorem alist_mem_iff_find : alist_mem l a ↔ (alist_find a l).is_some :=
iff.rfl

@[simp] theorem alist_mem_nil : alist_mem ([] : list (_root_.sigma β)) a ↔ false :=
by simp [alist_mem, option.is_some]

@[simp] theorem alist_mem_cons : alist_mem (⟨a₂, b₂⟩ :: l) a₁ ↔ a₂ = a₁ ∨ alist_mem l a₁ :=
by by_cases h : a₂ = a₁; simp [h, alist_mem, alist_find, option.is_some]

@[simp] theorem alist_mem_cons_eq (h : a₂ = a₁) : alist_mem (⟨a₂, b₂⟩ :: l) a₁ :=
by simp [h]

@[simp] theorem alist_mem_cons_ne (h : a₂ ≠ a₁) : alist_mem (⟨a₂, b₂⟩ :: l) a₁ ↔ alist_mem l a₁ :=
by simp [h]

@[simp] theorem alist_mem_singleton : alist_mem [⟨a₂, b₂⟩] a₁ ↔ a₂ = a₁ :=
by simp

theorem alist_mem_of_mem : sigma.mk a b ∈ l → alist_mem l a :=
begin
  induction l with hd tl ih,
  { simp },
  { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

instance decidable_alist_mem (a : α) : ∀ (l : list (_root_.sigma β)), decidable (alist_mem l a)
| []            := is_false (by simp)
| (⟨a₂, b₂⟩::l) :=
  if h : a₂ = a then
    is_true $ alist_mem_cons_eq h
  else
    have p : alist_mem (⟨a₂, b₂⟩ :: l) a ↔ alist_mem l a := alist_mem_cons_ne h,
    match decidable_alist_mem l with
    | is_true  h := is_true $ p.mpr h
    | is_false h := is_false $ (not_iff_not_of_iff p).mpr h
    end

end alist_mem

def alist_insert (x : _root_.sigma β) (l : list (_root_.sigma β)) : list (_root_.sigma β) :=
if alist_mem l x.1 then l else x :: l

def alist_keys : list (_root_.sigma β) → list α :=
map sigma.fst

section alist_keys

@[simp] theorem alist_keys_nil : alist_keys ([] : list (_root_.sigma β)) = [] :=
rfl

@[simp] theorem alist_keys_cons : alist_keys (⟨a, b⟩ :: l) = a :: alist_keys l :=
rfl

@[simp] theorem alist_keys_singleton : alist_keys [⟨a, b⟩] = [a] :=
rfl

theorem alist_mem_iff_alist_keys : alist_mem l a ↔ a ∈ alist_keys l :=
by induction l with hd tl ih; [simp, {cases hd, simp [eq_comm, ih]}]

theorem alist_find_iff_mem {l : list (_root_.sigma β)} (nd : (alist_keys l).nodup) :
  b ∈ alist_find a l ↔ sigma.mk a b ∈ l :=
begin
  induction l generalizing a b,
  case list.nil { simp },
  case list.cons : hd tl ih {
    cases hd with hd_a hd_b,
    simp at nd,
    by_cases p : hd_a = a,
    { induction p,
      split,
      { simp {contextual := tt} },
      { intro q,
        simp at q,
        cases q,
        case or.inl : q { simp [q] },
        case or.inr : q { exact absurd (alist_mem_iff_alist_keys.mp (alist_mem_of_mem q)) nd.1 } } },
    { rw [alist_find_cons_ne p, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro q,
        cases q,
        case or.inl : q { simp at q, exact absurd q.1.symm p },
        case or.inr : q { exact (ih nd.2).mpr q } }
    }
  }
end

end alist_keys

end list
