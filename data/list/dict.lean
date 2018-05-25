import data.list

namespace list
universes u v
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s : _root_.sigma β}
variables {l l₁ l₂ : list (_root_.sigma β)}
variables [decidable_eq α]

def dict_lookup (a : α) : list (_root_.sigma β) → option (β a)
| []            := none
| (⟨a₂, b₂⟩::l) := if h : a₂ = a then some (h.rec_on b₂) else dict_lookup l

section dict_lookup

@[simp] theorem dict_lookup_nil : dict_lookup a ([] : list (_root_.sigma β)) = none :=
rfl

theorem dict_lookup_cons : dict_lookup a₁ (⟨a₂, b₂⟩ :: l) = if h : a₂ = a₁ then some (h.rec_on b₂) else dict_lookup a₁ l :=
rfl

local attribute [simp] dict_lookup_cons

@[simp] theorem dict_lookup_cons_eq (h : a₂ = a₁) : b₁ ∈ dict_lookup a₁ (⟨a₂, b₂⟩ :: l) ↔ b₁ = h.rec_on b₂ :=
by simp [h, eq_comm]

@[simp] theorem dict_lookup_cons_ne (h : a₂ ≠ a₁) : dict_lookup a₁ (⟨a₂, b₂⟩ :: l) = dict_lookup a₁ l :=
by simp [h]

end dict_lookup

def dict_mem (l : list (_root_.sigma β)) (a : α) : bool :=
(dict_lookup a l).is_some

section dict_mem

theorem dict_mem_iff_find : dict_mem l a ↔ (dict_lookup a l).is_some :=
iff.rfl

@[simp] theorem dict_mem_nil : dict_mem ([] : list (_root_.sigma β)) a ↔ false :=
by simp [dict_mem, option.is_some]

@[simp] theorem dict_mem_cons : dict_mem (⟨a₂, b₂⟩ :: l) a₁ ↔ a₂ = a₁ ∨ dict_mem l a₁ :=
by by_cases h : a₂ = a₁; simp [h, dict_mem, dict_lookup, option.is_some]

@[simp] theorem dict_mem_cons_eq (h : a₂ = a₁) : dict_mem (⟨a₂, b₂⟩ :: l) a₁ :=
by simp [h]

@[simp] theorem dict_mem_cons_ne (h : a₂ ≠ a₁) : dict_mem (⟨a₂, b₂⟩ :: l) a₁ ↔ dict_mem l a₁ :=
by simp [h]

@[simp] theorem dict_mem_singleton : dict_mem [⟨a₂, b₂⟩] a₁ ↔ a₂ = a₁ :=
by simp

theorem dict_mem_of_mem : sigma.mk a b ∈ l → dict_mem l a :=
begin
  induction l with hd tl ih,
  { simp },
  { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

instance decidable_dict_mem (a : α) : ∀ (l : list (_root_.sigma β)), decidable (dict_mem l a)
| []            := is_false (by simp)
| (⟨a₂, b₂⟩::l) :=
  if h : a₂ = a then
    is_true $ dict_mem_cons_eq h
  else
    have p : dict_mem (⟨a₂, b₂⟩ :: l) a ↔ dict_mem l a := dict_mem_cons_ne h,
    match decidable_dict_mem l with
    | is_true  h := is_true $ p.mpr h
    | is_false h := is_false $ (not_iff_not_of_iff p).mpr h
    end

end dict_mem

def dict_insert (x : _root_.sigma β) (l : list (_root_.sigma β)) : list (_root_.sigma β) :=
if dict_mem l x.1 then l else x :: l

def dict_keys : list (_root_.sigma β) → list α :=
map sigma.fst

section dict_keys

@[simp] theorem dict_keys_nil : dict_keys ([] : list (_root_.sigma β)) = [] :=
rfl

@[simp] theorem dict_keys_cons : dict_keys (⟨a, b⟩ :: l) = a :: dict_keys l :=
rfl

@[simp] theorem dict_keys_singleton : dict_keys [⟨a, b⟩] = [a] :=
rfl

theorem dict_mem_iff_dict_keys : dict_mem l a ↔ a ∈ dict_keys l :=
by induction l with hd tl ih; [simp, {cases hd, simp [eq_comm, ih]}]

theorem dict_lookup_iff_mem {l : list (_root_.sigma β)} (nd : (dict_keys l).nodup) :
  b ∈ dict_lookup a l ↔ sigma.mk a b ∈ l :=
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
        case or.inr : q { exact absurd (dict_mem_iff_dict_keys.mp (dict_mem_of_mem q)) nd.1 } } },
    { rw [dict_lookup_cons_ne p, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro q,
        cases q,
        case or.inl : q { simp at q, exact absurd q.1.symm p },
        case or.inr : q { exact (ih nd.2).mpr q } }
    }
  }
end

end dict_keys

end list
