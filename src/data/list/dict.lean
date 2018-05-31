import data.list.perm
import data.sigma.on_fst

namespace list
universes u v
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s s₁ s₂ : sigma β}
variables {l l₁ l₂ : list (sigma β)}

def dict_lookups [decidable_eq α] (a : α) : list (sigma β) → list (β a)
| []            := []
| (⟨a₂, b₂⟩::l) := if h : a₂ = a then h.rec_on b₂ :: dict_lookups l else dict_lookups l

section dict_lookups
variables [decidable_eq α]

@[simp] theorem dict_lookups_nil : dict_lookups a ([] : list (sigma β)) = [] :=
rfl

theorem dict_lookups_cons :
  dict_lookups a₁ (sigma.mk a₂ b₂ :: l) = if h : a₂ = a₁ then h.rec_on b₂ :: dict_lookups a₁ l else dict_lookups a₁ l :=
rfl

local attribute [simp] dict_lookups_cons

@[simp] theorem dict_lookups_cons_eq (h : a₂ = a₁) : dict_lookups a₁ (sigma.mk a₂ b₂ :: l) = h.rec_on b₂ :: dict_lookups a₁ l :=
by simp [h]

@[simp] theorem dict_lookups_cons_ne (h : a₂ ≠ a₁) : dict_lookups a₁ (sigma.mk a₂ b₂ :: l) = dict_lookups a₁ l :=
by simp [h]

end dict_lookups

def dict_lookup [decidable_eq α] (a : α) : list (sigma β) → option (β a)
| []            := none
| (⟨a₂, b₂⟩::l) := if h : a₂ = a then some (h.rec_on b₂) else dict_lookup l

section dict_lookup
variables [decidable_eq α]

@[simp] theorem dict_lookup_nil : dict_lookup a ([] : list (sigma β)) = none :=
rfl

theorem dict_lookup_cons :
  dict_lookup a₁ (sigma.mk a₂ b₂ :: l) = if h : a₂ = a₁ then some (h.rec_on b₂) else dict_lookup a₁ l :=
rfl

local attribute [simp] dict_lookup_cons

@[simp] theorem dict_lookup_cons_eq (h : a₂ = a₁) : dict_lookup a₁ (sigma.mk a₂ b₂ :: l) = some (h.rec_on b₂) :=
by simp [h, eq_comm]

@[simp] theorem dict_lookup_cons_ne (h : a₂ ≠ a₁) : dict_lookup a₁ (sigma.mk a₂ b₂ :: l) = dict_lookup a₁ l :=
by simp [h]

end dict_lookup

def dict_contains [decidable_eq α] (l : list (sigma β)) (a : α) : bool :=
(dict_lookup a l).is_some

section dict_contains
variables [decidable_eq α]

theorem dict_contains_iff_find : l.dict_contains a ↔ (dict_lookup a l).is_some :=
iff.rfl

@[simp] theorem dict_contains_nil : ([] : list (sigma β)).dict_contains a ↔ false :=
by simp [dict_contains, option.is_some]

@[simp] theorem dict_contains_cons : (sigma.mk a₂ b₂ :: l).dict_contains a₁ ↔ a₂ = a₁ ∨ l.dict_contains a₁ :=
by by_cases h : a₂ = a₁; simp [h, dict_contains, dict_lookup, option.is_some]

@[simp] theorem dict_contains_cons_eq (h : a₂ = a₁) : (sigma.mk a₂ b₂ :: l).dict_contains a₁ :=
by simp [h]

@[simp] theorem dict_contains_cons_ne (h : a₂ ≠ a₁) : (sigma.mk a₂ b₂ :: l).dict_contains a₁ ↔ l.dict_contains a₁ :=
by simp [h]

@[simp] theorem dict_contains_singleton : [sigma.mk a₂ b₂].dict_contains a₁ ↔ a₂ = a₁ :=
by simp

theorem dict_contains_of_mem : sigma.mk a b ∈ l → l.dict_contains a :=
begin
  induction l with hd tl ih,
  { simp },
  { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

instance decidable_dict_contains (a : α) : ∀ (l : list (sigma β)), decidable (l.dict_contains a)
| []            := is_false (by simp)
| (⟨a₂, b₂⟩::l) :=
  if h : a₂ = a then
    is_true $ dict_contains_cons_eq h
  else
    have p : (sigma.mk a₂ b₂ :: l).dict_contains a ↔ l.dict_contains a := dict_contains_cons_ne h,
    match decidable_dict_contains l with
    | is_true  h := is_true $ p.mpr h
    | is_false h := is_false $ (not_iff_not_of_iff p).mpr h
    end

end dict_contains

def dict_insert [decidable_eq α] (s : sigma β) (l : list (sigma β)) : list (sigma β) :=
if l.dict_contains s.1 then l else s :: l

section dict_insert
variables [decidable_eq α]

local attribute [simp] dict_insert

@[simp] theorem dict_insert_of_dict_contains (h : l.dict_contains s.1) : l.dict_insert s = l :=
by simp [h]

@[simp] theorem dict_insert_of_not_dict_contains (h : ¬ l.dict_contains s.1) : l.dict_insert s = s :: l :=
by simp [h]

end dict_insert

def nodup_keys : list (sigma β) → Prop := pairwise (sigma.on_fst (≠))

section nodup_keys

@[simp] theorem nodup_keys_nil : @nodup_keys α β [] :=
pairwise.nil _

@[simp] theorem nodup_keys_cons {l : list (sigma β)} :
  nodup_keys (s :: l) ↔ (∀ (s' : sigma β), s' ∈ l → s.1 ≠ s'.1) ∧ nodup_keys l :=
by simp [nodup_keys, sigma.on_fst]

theorem perm_nodup_keys (p : l₁ ~ l₂) : l₁.nodup_keys ↔ l₂.nodup_keys :=
perm_pairwise (@sigma.on_fst.symm α β (≠) (@ne.symm α)) p

@[simp] theorem nodup_keys_cons_of_not_dict_contains [decidable_eq α]
{l : list (sigma β)} (s : sigma β) (h : ¬ l.dict_contains s.1) :
  nodup_keys (s :: l) ↔ nodup_keys l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    cases hd with a b,
    rw [dict_contains_cons, decidable.not_or_iff_and_not] at h,
    rw [perm_nodup_keys (perm.swap ⟨a, b⟩ s tl), nodup_keys_cons, ih h.2, nodup_keys_cons],
    simp [h.1]
  }
end

@[simp] theorem nodup_keys_dict_insert [decidable_eq α]
{l : list (sigma β)} (s : sigma β) :
  nodup_keys (l.dict_insert s) ↔ nodup_keys l :=
begin
  by_cases h : ↥(l.dict_contains s.1),
  { simp [nodup_keys, dict_insert, h] },
  { rw [dict_insert_of_not_dict_contains h, nodup_keys_cons_of_not_dict_contains s h] }
end

end nodup_keys

def dict_keys : list (sigma β) → list α :=
map sigma.fst

section dict_keys

@[simp] theorem dict_keys_nil : ([] : list (sigma β)).dict_keys = [] :=
rfl

@[simp] theorem dict_keys_cons : (s :: l).dict_keys = s.1 :: l.dict_keys :=
rfl

@[simp] theorem dict_keys_singleton : [sigma.mk a b].dict_keys = [a] :=
rfl

variables [decidable_eq α]

theorem dict_contains_iff_dict_keys : l.dict_contains a ↔ a ∈ l.dict_keys :=
by induction l with hd tl ih; [simp, {cases hd, simp [eq_comm, ih]}]

@[simp] theorem dict_keys_iff_ne_key_of_mem :
  (∀ (a₁ : α) (b₁ : β a₁), sigma.mk a₁ b₁ ∈ l → a ≠ a₁) ↔ a ∉ dict_keys l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    cases hd with a₂ b₂,
    split,
    { intro h,
      simp [decidable.not_or_iff_and_not] at h ⊢,
      exact ⟨h a₂ b₂ (or.inl ⟨rfl, heq.rfl⟩), ih.mp (λ a₃ b₃, h a₃ b₃ ∘ or.inr)⟩
    },
    { intros h₁ a₃ b₃ h₂,
      simp [decidable.not_or_iff_and_not] at h₁ h₂,
      cases h₂ with h₂ h₂,
      { rw h₂.1, exact h₁.1 },
      { exact ih.mpr h₁.2 a₃ b₃ h₂ }
      }
  }
end

theorem dict_lookup_iff_mem {l : list (sigma β)} (nd : l.nodup_keys) :
  b ∈ l.dict_lookup a ↔ sigma.mk a b ∈ l :=
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
        cases q with q q,
        { simp [q] },
        { exact absurd (dict_contains_iff_dict_keys.mp (dict_contains_of_mem q)) nd.1 } } },
    { rw [dict_lookup_cons_ne p, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro q,
        cases q with q q,
        { simp at q, exact absurd q.1.symm p },
        { exact (ih nd.2).mpr q } }
    }
  }
end

end dict_keys

theorem nodup_of_nodup_keys {l : list (sigma β)} : l.nodup_keys → l.nodup :=
pairwise.imp $ λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (h : a₁ ≠ a₂), by simp [h]

variables [decidable_eq α]

theorem perm_dict_lookups (a : α) (p : l₁ ~ l₂) :
  l₁.dict_lookups a ~ l₂.dict_lookups a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s₁ l₁ l₂ p ih {
    cases s₁ with a₁ b₁,
    by_cases h : a₁ = a; simp [h, ih, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l {
    cases s₁ with a₁ b₁,
    cases s₂ with a₂ b₂,
    by_cases h₁ : a₁ = a; by_cases h₂ : a₂ = a; simp [h₁, h₂, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
  }
end

theorem dict_lookup_eq_of_perm (a : α) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys)
  (p : l₁ ~ l₂) : l₁.dict_lookup a = l₂.dict_lookup a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s₁ l₁ l₂ p ih nd₁ nd₂ {
    cases s₁ with a₁ b₁,
    by_cases h : a₁ = a,
    { simp [h] },
    { simp at nd₁ nd₂, simp [h, ih nd₁.2 nd₂.2] }
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    cases s₁ with a₁ b₁,
    cases s₂ with a₂ b₂,
    simp [and.assoc] at nd₂₁ nd₁₂,
    by_cases h₂ : a₂ = a,
    { induction h₂, simp [eq.refl a₁, nd₁₂.1] },
    { by_cases h₁ : a₁ = a; simp [h₂, h₁] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact eq.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

theorem dict_keys_eq_of_perm (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys)
  (p : l₁ ~ l₂) : l₁.dict_keys ~ l₂.dict_keys :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s₁ l₁ l₂ p ih {
    simp at nd₁ nd₂,
    simp [perm.skip s₁.1 (ih nd₁.2 nd₂.2)]
  },
  case list.perm.swap : s₁ s₂ l {
    simp [perm.swap s₁.1 s₂.1 (dict_keys l)]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

end list
