import data.list.perm
import data.sigma.on_fst

namespace list
universes u v
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s s₁ s₂ t : sigma β}
variables {l l₁ l₂ : list (sigma β)}

def dict_lookup_all [decidable_eq α] (a : α) : list (sigma β) → list (β a)
| []     := []
| (s::l) := let l' := dict_lookup_all l in if h : s.1 = a then h.rec_on s.2 :: l' else l'

section dict_lookup_all
variables [decidable_eq α]

@[simp] theorem dict_lookup_all_nil : @dict_lookup_all _ β _ a [] = [] :=
rfl

local attribute [simp] dict_lookup_all

@[simp] theorem dict_lookup_all_cons_eq (h : s.1 = a) : dict_lookup_all a (s :: l) = h.rec_on s.2 :: dict_lookup_all a l :=
by simp [h]

@[simp] theorem dict_lookup_all_cons_ne (h : s.1 ≠ a) : dict_lookup_all a (s :: l) = dict_lookup_all a l :=
by simp [h]

end dict_lookup_all

def dict_lookup [decidable_eq α] (a : α) : list (sigma β) → option (β a)
| []     := none
| (s::l) := if h : s.1 = a then some (h.rec_on s.2) else dict_lookup l

section dict_lookup
variables [decidable_eq α]

@[simp] theorem dict_lookup_nil : @dict_lookup _ β _ a [] = none :=
rfl

local attribute [simp] dict_lookup

@[simp] theorem dict_lookup_cons_eq (h : s.1 = a) : dict_lookup a (s :: l) = some (h.rec_on s.2) :=
by simp [h]

@[simp] theorem dict_lookup_cons_ne (h : s.1 ≠ a) : dict_lookup a (s :: l) = dict_lookup a l :=
by simp [h]

end dict_lookup

def dict_contains [decidable_eq α] (l : list (sigma β)) (a : α) : bool :=
(dict_lookup a l).is_some

section dict_contains
variables [decidable_eq α]

@[simp] theorem dict_contains_nil : @dict_contains _ β _ [] a = ff :=
by simp [dict_contains, option.is_some]

@[simp] theorem dict_contains_cons : (s :: l).dict_contains a ↔ s.1 = a ∨ l.dict_contains a :=
by by_cases h : s.1 = a; simp [dict_contains, option.is_some, h]

@[simp] theorem dict_contains_cons_eq (h : s.1 = a) : (s :: l).dict_contains a :=
by simp [h]

@[simp] theorem dict_contains_cons_ne (h : s.1 ≠ a) : (s :: l).dict_contains a = l.dict_contains a :=
by simp [dict_contains, h]

@[simp] theorem dict_contains_singleton : [s].dict_contains a ↔ s.1 = a :=
by simp

theorem dict_contains_of_mem : s ∈ l → l.dict_contains s.1 :=
begin
  induction l with hd tl ih,
  { simp },
  { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

instance decidable_dict_contains (a : α) : ∀ (l : list (sigma β)), decidable (l.dict_contains a)
| []            := is_false (by simp)
| (⟨a₁, b₁⟩::l) :=
  if ha : a₁ = a then
    is_true $ dict_contains_cons_eq ha
  else
    match decidable_dict_contains l with
    | is_true  hl := is_true $ by simp [hl]
    | is_false hl := is_false $ by simp [ha, hl]
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

def dict_erase [decidable_eq α] (a : α) : list (sigma β) → list (sigma β)
| []     := []
| (s::l) := if h : s.1 = a then l else s :: dict_erase l

section dict_erase
variables [decidable_eq α]

@[simp] theorem dict_erase_nil : @dict_erase _ β _ a [] = [] :=
rfl

@[simp] theorem dict_erase_cons_eq (h : s.1 = a) : dict_erase a (s :: l) = l :=
by simp [dict_erase, h]

@[simp] theorem dict_erase_cons_ne (h : s.1 ≠ a) : dict_erase a (s :: l) = s :: dict_erase a l :=
by simp [dict_erase, h]

theorem mem_of_mem_dict_erase : s ∈ dict_erase a l → s ∈ l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    by_cases h : hd.1 = a,
    { simp [h] {contextual := tt} },
    { intro p, simp [h] at p, cases p with p p; simp [p, ih] }
  }
end

end dict_erase

def dict_erase_all [decidable_eq α] (a : α) : list (sigma β) → list (sigma β)
| []     := []
| (s::l) := let l' := dict_erase_all l in if h : s.1 = a then l' else s :: l'

section dict_erase_all
variables [decidable_eq α]

@[simp] theorem dict_erase_all_nil : @dict_erase_all _ β _ a [] = [] :=
rfl

@[simp] theorem dict_erase_all_cons_eq (h : s.1 = a) : dict_erase_all a (s :: l) = dict_erase_all a l :=
by simp [dict_erase_all, h]

@[simp] theorem dict_erase_all_cons_ne (h : s.1 ≠ a) : dict_erase_all a (s :: l) = s :: dict_erase_all a l :=
by simp [dict_erase_all, h]

end dict_erase_all

def dict_replace [decidable_eq α] (s : sigma β) : list (sigma β) → list (sigma β)
| []     := []
| (t::l) := if h : t.1 = s.1 then s :: l else t :: dict_replace l

section dict_replace
variables [decidable_eq α]

@[simp] theorem dict_replace_nil : dict_replace s [] = [] :=
rfl

@[simp] theorem dict_replace_cons_eq (h : t.1 = s.1) : (t :: l).dict_replace s = s :: l :=
by simp [dict_replace, h]

@[simp] theorem dict_replace_cons_ne (h : t.1 ≠ s.1) : (t :: l).dict_replace s = t :: l.dict_replace s :=
by simp [dict_replace, h]

theorem mem_cons_of_dict_ne (h : t.1 ≠ s.1) : s ∈ t :: l → s ∈ l :=
by cases s; cases t; simp [ne.symm h]

theorem mem_of_mem_dict_replace_ne (h : t.1 ≠ s.1) : s ∈ l.dict_replace t → s ∈ l :=
begin
  induction l generalizing s t,
  case list.nil { simp },
  case list.cons : hd tl ih {
    by_cases h₁ : hd.1 = t.1,
    { rw dict_replace_cons_eq h₁,
      exact mem_cons_of_mem hd ∘ mem_cons_of_dict_ne h },
    { rw dict_replace_cons_ne h₁,
      intro p,
      simp at p,
      cases p,
      { simp [p] },
      { simp [ih h p] } }
  }
end

end dict_replace

def nodup_keys : list (sigma β) → Prop := pairwise (sigma.on_fst (≠))

section nodup_keys

@[simp] theorem nodup_keys_nil : @nodup_keys α β [] :=
pairwise.nil _

@[simp] theorem nodup_keys_cons :
  (s :: l).nodup_keys ↔ (∀ {s' : sigma β}, s' ∈ l → s.1 ≠ s'.1) ∧ l.nodup_keys :=
by simp [nodup_keys, sigma.on_fst]

theorem perm_nodup_keys (p : l₁ ~ l₂) : l₁.nodup_keys ↔ l₂.nodup_keys :=
perm_pairwise (@sigma.on_fst.symm α β (≠) (@ne.symm α)) p

@[simp] theorem nodup_keys_cons_of_not_dict_contains [decidable_eq α]
(s : sigma β) (h : ¬ l.dict_contains s.1) :
  (s :: l).nodup_keys ↔ l.nodup_keys :=
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

@[simp] theorem nodup_keys_dict_insert [decidable_eq α] (s : sigma β) :
  (l.dict_insert s).nodup_keys ↔ l.nodup_keys  :=
begin
  by_cases h : ↥(l.dict_contains s.1),
  { simp [nodup_keys, dict_insert, h] },
  { rw [dict_insert_of_not_dict_contains h, nodup_keys_cons_of_not_dict_contains s h] }
end

@[simp] theorem nodup_keys_dict_erase [decidable_eq α] (a : α) :
  l.nodup_keys → (l.dict_erase a).nodup_keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd, rw nodup_keys_cons at nd,
    by_cases h : hd.1 = a,
    { simp [h, nd.2] },
    { rw [dict_erase_cons_ne h, nodup_keys_cons],
      split,
      { intros s p, exact nd.1 (mem_of_mem_dict_erase p) },
      { exact ih nd.2 } }
  }
end

@[simp] theorem nodup_keys_dict_replace [decidable_eq α] (s : sigma β) :
  l.nodup_keys → (l.dict_replace s).nodup_keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd, rw nodup_keys_cons at nd,
    by_cases h₁ : hd.1 = s.1,
    { cases hd with a₁ b₁,
      cases s with a₂ b₂,
      dsimp at h₁,
      induction h₁,
      rw [@dict_replace_cons_eq _ _ ⟨a₁, b₂⟩ ⟨a₁, b₁⟩ _ _ rfl, nodup_keys_cons],
      exact nd },
    { rw [dict_replace_cons_ne h₁, nodup_keys_cons],
      split,
      { intros s' p,
        by_cases h₂ : s.1 = s'.1,
        { rwa h₂ at h₁ },
        { exact nd.1 (mem_of_mem_dict_replace_ne h₂ p) } },
      { exact ih nd.2 } }
  }
end

end nodup_keys

def dict_keys : list (sigma β) → list α :=
map sigma.fst

section dict_keys

@[simp] theorem dict_keys_nil : ([] : list (sigma β)).dict_keys = [] :=
rfl

@[simp] theorem dict_keys_cons : (s :: l).dict_keys = s.1 :: l.dict_keys :=
rfl

@[simp] theorem dict_keys_singleton : [s].dict_keys = [s.1] :=
rfl

variables [decidable_eq α]

theorem dict_contains_iff_dict_keys : l.dict_contains a ↔ a ∈ l.dict_keys :=
by induction l with hd tl ih; [simp, {cases hd, simp [eq_comm, ih]}]

@[simp] theorem dict_keys_iff_ne_key_of_mem :
  (∀ (s : sigma β), s ∈ l → a ≠ s.1) ↔ a ∉ dict_keys l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih { simp [decidable.not_or_iff_and_not, ih] }
end

theorem dict_lookup_iff_mem (nd : l.nodup_keys) : s.2 ∈ l.dict_lookup s.1 ↔ s ∈ l :=
begin
  induction l generalizing s,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h : hd.1 = s.1,
    { rw dict_lookup_cons_eq h,
      cases s with a₁ b₁,
      cases hd with a₂ b₂,
      dsimp at h,
      induction h,
      split,
      { simp {contextual := tt} },
      { intro h,
        simp at h,
        cases h with h h,
        { simp [h] },
        { exact absurd (dict_contains_iff_dict_keys.mp (dict_contains_of_mem h)) nd.1 } } },
    { rw [dict_lookup_cons_ne h, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro p,
        cases p with p p,
        { induction p, exact false.elim (ne.irrefl h) },
        { exact (ih nd.2).mpr p } } }
  }
end

end dict_keys

theorem nodup_of_nodup_keys : l.nodup_keys → l.nodup :=
pairwise.imp $ λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (h : a₁ ≠ a₂), by simp [h]

variables [decidable_eq α]

theorem perm_dict_lookup_all (a : α) (p : l₁ ~ l₂) :
  l₁.dict_lookup_all a ~ l₂.dict_lookup_all a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s l₁ l₂ p ih {
    by_cases h : s.1 = a; simp [h, ih, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₁ : s₁.1 = a; by_cases h₂ : s₂.1 = a; simp [h₁, h₂, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
  }
end

theorem dict_lookup_eq_of_perm (a : α) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.dict_lookup a = l₂.dict_lookup a :=
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
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : a₁ = a; simp [h₂, h₁] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact eq.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

theorem dict_keys_eq_of_perm (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.dict_keys ~ l₂.dict_keys :=
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

theorem perm_dict_erase (a : α) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.dict_erase a ~ l₂.dict_erase a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s l₁ l₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : s.1 = a; simp [p, h, ih nd₁.2 nd₂.2, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    cases s₁ with a₁ b₁,
    cases s₂ with a₂ b₂,
    simp [and.assoc] at nd₁₂,
    by_cases h₂ : a₂ = a,
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : a₁ = a; simp [h₂, h₁, perm.swap] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

theorem perm_dict_erase_all (a : α) (p : l₁ ~ l₂) :
  l₁.dict_erase_all a ~ l₂.dict_erase_all a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s l₁ l₂ p ih {
    by_cases h : s.1 = a; simp [h, ih, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₁ : s₁.1 = a; by_cases h₂ : s₂.1 = a; simp [h₁, h₂, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
  }
end

theorem perm_dict_replace (s : sigma β) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.dict_replace s ~ l₂.dict_replace s :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : t l₁ l₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : t.1 = s.1; simp [p, h, ih nd₁.2 nd₂.2, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp [and.assoc] at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = s.1,
    { rw dict_replace_cons_eq h₂,
      by_cases h₁ : s₁.1 = s.1,
      { rw dict_replace_cons_eq h₁,
        exact absurd (h₂.trans h₁.symm) nd₂₁.1 },
      { simp [h₁, h₂, perm.swap] } },
    { by_cases h₁ : s₁.1 = s.1; simp [h₁, h₂, perm.swap] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

end list
