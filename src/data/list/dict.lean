import data.list.perm
import data.sigma.on_fst

local attribute [simp] decidable.not_or_iff_and_not and.assoc

namespace list
universes u v
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s s₁ s₂ t : sigma β}
variables {l l₁ l₂ l₃ l₄ : list (sigma β)}

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

def dict_mem [decidable_eq α] (a : α) (l : list (sigma β)) : Prop :=
(dict_lookup a l).is_some

local infix ` d∈ `:51 := dict_mem
local notation a ` d∉ `:51 l:51 := ¬ dict_mem a l

section dict_mem
variables [decidable_eq α]

@[simp] theorem dict_mem_nil : @dict_mem _ β _ a [] ↔ ff :=
by simp [dict_mem, option.is_some]

@[simp] theorem dict_mem_cons : a d∈ s :: l ↔ s.1 = a ∨ a d∈ l :=
by by_cases h : s.1 = a; simp [dict_mem, option.is_some, h]

@[simp] theorem dict_mem_cons_eq (h : s.1 = a) : a d∈ s :: l :=
by simp [h]

@[simp] theorem dict_mem_cons_ne (h : s.1 ≠ a) : a d∈ s :: l ↔ a d∈ l :=
by simp [dict_mem, h]

theorem dict_mem_cons_of_dict_mem (s : sigma β) : a d∈ l → a d∈ s :: l :=
dict_mem_cons.mpr ∘ or.inr

@[simp] theorem dict_mem_singleton : a d∈ [s] ↔ s.1 = a :=
by simp

@[simp] theorem dict_mem_append : a d∈ l₁ ++ l₂ ↔ a d∈ l₁ ∨ a d∈ l₂ :=
by induction l₁; simp [*, or_assoc]

theorem dict_mem_of_mem : s ∈ l → s.1 d∈ l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

theorem exists_mem_of_dict_mem : a d∈ l → ∃ (b : β a), sigma.mk a b ∈ l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro h,
    simp at h,
    cases h,
    case or.inl : h { cases hd with a₁ b₁, induction h, exact ⟨b₁, mem_cons_self ⟨a₁, b₁⟩ tl⟩ },
    case or.inr : h { cases ih h with b h, exact ⟨b, mem_cons_of_mem hd h⟩ }
  }
end

theorem not_dict_mem_cons_of_ne_of_not_dict_mem (h₁ : s.1 ≠ a) (h₂ : a d∉ l) : a d∉ s :: l :=
by simp [h₁, h₂]

theorem dict_mem_of_ne_of_dict_mem (h₁ : s.1 ≠ a) (h₂ : a d∈ s :: l) : a d∈ l :=
or.elim (dict_mem_cons.mp h₂) (λ p, absurd p h₁) id

instance decidable_dict_mem (a : α) : ∀ (l : list (sigma β)), decidable (a d∈ l)
| []            := is_false (by simp)
| (⟨a₁, b₁⟩::l) :=
  if ha : a₁ = a then
    is_true $ dict_mem_cons_eq ha
  else
    match decidable_dict_mem l with
    | is_true  hl := is_true $ by simp [hl]
    | is_false hl := is_false $ by simp [ha, hl]
    end

end dict_mem

def dict_subset [decidable_eq α] (l₁ l₂ : list (sigma β)) := ∀ ⦃a : α⦄, a d∈ l₁ → a d∈ l₂

local infix ` d⊆ `:51 := dict_subset

section dict_subset
variables [decidable_eq α]

theorem dict_subset_of_sublist : ∀ {l₁ l₂ : list (sigma β)}, l₁ <+ l₂ → l₁ d⊆ l₂
| _ _ sublist.slnil              _  h := h
| _ _ (sublist.cons  l₁ l₂ s sl) a₂ h :=
  dict_mem_cons_of_dict_mem s (dict_subset_of_sublist sl h)
| _ _ (sublist.cons2 l₁ l₂ s sl) a₂ h :=
  match dict_mem_cons.mp h with
  | or.inl h := dict_mem_cons_eq h
  | or.inr h := dict_mem_cons_of_dict_mem s (dict_subset_of_sublist sl h)
  end

end dict_subset

def dict_insert [decidable_eq α] (s : sigma β) (l : list (sigma β)) : list (sigma β) :=
if s.1 d∈ l then l else s :: l

section dict_insert
variables [decidable_eq α]

local attribute [simp] dict_insert

@[simp] theorem dict_insert_of_dict_mem (h : s.1 d∈ l) : l.dict_insert s = l :=
by simp [h]

@[simp] theorem dict_insert_of_not_dict_mem (h : s.1 d∉ l) : l.dict_insert s = s :: l :=
by simp [h]

@[simp] theorem dict_insert_cons_eq (h : s₂.1 = s₁.1) : (s₂ :: l).dict_insert s₁ = s₂ :: l :=
by simp [h]

@[simp] theorem dict_insert_cons_ne (h : s₂.1 ≠ s₁.1) :
  (s₂ :: l).dict_insert s₁ = if s₁.1 d∈ l then s₂ :: l else s₁ :: s₂ :: l :=
by by_cases h' : s₁.1 d∈ l; simp [h, h']

end dict_insert

def dict_erase [decidable_eq α] (a : α) : list (sigma β) → list (sigma β)
| []     := []
| (s::l) := if h : s.1 = a then l else s :: dict_erase l

section dict_erase
variables [decidable_eq α]

@[simp] theorem dict_erase_nil : @dict_erase _ β _ a [] = [] :=
rfl

@[simp] theorem dict_erase_cons_eq (h : s.1 = a) : (s :: l).dict_erase a = l :=
by simp [dict_erase, h]

@[simp] theorem dict_erase_cons_ne (h : s.1 ≠ a) : (s :: l).dict_erase a = s :: l.dict_erase a :=
by simp [dict_erase, h]

@[simp] theorem mem_dict_erase_nil : s ∈ @dict_erase _ β _ a [] ↔ false :=
by simp

@[simp] theorem dict_erase_of_not_dict_mem (h : a d∉ l) : l.dict_erase a = l :=
by induction l with _ _ ih; [refl, {simp at h, simp [h.1, ih h.2]}]

theorem exists_dict_erase_eq (h : a d∈ l) :
  ∃ (b : β a) (l₁ l₂ : list (sigma β)),
    a d∉ l₁ ∧
    l = l₁ ++ ⟨a, b⟩ :: l₂ ∧
    l.dict_erase a = l₁ ++ l₂ :=
begin
  induction l,
  case list.nil { cases h },
  case list.cons : hd tl ih {
    by_cases e : hd.1 = a,
    { induction e,
      exact ⟨hd.2, [], tl, by simp, by cases hd; refl, by simp⟩ },
    { simp at h,
      cases h,
      case or.inl : h { contradiction },
      case or.inr : h {
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩,
        exact ⟨b, hd::tl₁, tl₂, not_dict_mem_cons_of_ne_of_not_dict_mem e h₁,
               by rw h₂; refl, by simp [e, h₃]⟩
      } }
  }
end

theorem dict_erase_sublist (a : α) (l : list (sigma β)) : l.dict_erase a <+ l :=
if h : a d∈ l then
  match l, l.dict_erase a, exists_dict_erase_eq h with
  | ._, ._, ⟨b, l₁, l₂, _, rfl, rfl⟩ := by simp
  end
else
  by simp [h]

theorem dict_erase_subset (a : α) (l : list (sigma β)) : l.dict_erase a ⊆ l :=
subset_of_sublist (dict_erase_sublist a l)

theorem mem_of_mem_dict_erase : s ∈ l.dict_erase a → s ∈ l :=
@dict_erase_subset _ _ _ _ _ _

@[simp] theorem mem_dict_erase_of_ne (h : s.1 ≠ a) : s ∈ l.dict_erase a ↔ s ∈ l :=
iff.intro mem_of_mem_dict_erase $ λ p,
  if q : a d∈ l then
    match l, l.dict_erase a, exists_dict_erase_eq q, p with
    | ._, ._, ⟨b, l₁, l₂, _, rfl, rfl⟩, p :=
      by clear _match; cases s; simpa [h] using p
    end
  else
    by simp [q, p]

theorem dict_erase_dict_subset (a : α) (l : list (sigma β)) : l.dict_erase a d⊆ l :=
dict_subset_of_sublist (dict_erase_sublist a l)

theorem dict_mem_of_dict_mem_dict_erase : a d∈ l.dict_erase a₁ → a d∈ l :=
@dict_erase_dict_subset _ _ _ _ _ _

@[simp] theorem dict_mem_dict_erase_of_ne (h : a₂ ≠ a₁) : a₁ d∈ l.dict_erase a₂ ↔ a₁ d∈ l :=
iff.intro dict_mem_of_dict_mem_dict_erase $ λ p,
  if q : a₂ d∈ l then
    match l, l.dict_erase a₂, exists_dict_erase_eq q, p with
    | ._, ._, ⟨b, l₁, l₂, _, rfl, rfl⟩, p := by simpa [h] using p
    end
  else
    by simp [q, p]

theorem dict_erase_append_left : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  a d∈ l₁ → (l₁ ++ l₂).dict_erase a = l₁.dict_erase a ++ l₂
| []       _  h  := by cases h
| (s::tl₁) l₂ h₁ :=
  if h₂ : s.1 = a then
    by simp [h₂]
  else
    by simp at h₁; cases h₁; [contradiction, simp [h₂, dict_erase_append_left l₂ h₁]]

theorem dict_erase_append_right : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  a d∉ l₁ → (l₁ ++ l₂).dict_erase a = l₁ ++ l₂.dict_erase a
| []       _  h := rfl
| (s::tl₁) l₂ h := by simp at h; simp [h.1, dict_erase_append_right l₂ h.2]

theorem dict_erase_comm : (l.dict_erase a₁).dict_erase a₂ = (l.dict_erase a₂).dict_erase a₁ :=
if h : a₂ = a₁ then
  by simp [h]
else if ha₁ : a₁ d∈ l then
  if ha₂ : a₂ d∈ l then
    match l, l.dict_erase a₁, exists_dict_erase_eq ha₁, ha₂ with
    | ._, ._, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ :=
      if h' : a₂ d∈ l₁ then
        by simp [dict_erase_append_left _ h',
                 dict_erase_append_right _ (mt (dict_mem_dict_erase_of_ne h).mp a₁_nin_l₁)]
      else
        by simp [dict_erase_append_right _ h', dict_erase_append_right _ a₁_nin_l₁,
                 @dict_erase_cons_ne _ _ a₂ ⟨a₁, b₁⟩ _ _ (ne.symm h)]
    end
  else
    by simp [ha₂, mt dict_mem_of_dict_mem_dict_erase ha₂]
else
  by simp [ha₁, mt dict_mem_of_dict_mem_dict_erase ha₁]

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

/-- Left-biased append -/
def dict_append [decidable_eq α] : list (sigma β) → list (sigma β) → list (sigma β)
| []      l  := l
| (s::l₁) l₂ := s :: dict_append l₁ (dict_erase s.1 l₂)

local infixr ` d++ `:67 := dict_append

section dict_append
variables [decidable_eq α]

@[simp] theorem dict_append_nil : [] d++ l = l :=
rfl

@[simp] theorem dict_append_cons : (s :: l₁) d++ l₂ = s :: l₁ d++ dict_erase s.1 l₂ :=
rfl

theorem mem_dict_append : s ∈ l₁ d++ l₂ → s ∈ l₁ ∨ s ∈ l₂ :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro h,
    simp at h,
    cases h,
    case or.inl : h { simp [h] },
    case or.inr : h {
      cases ih h,
      case or.inl : h { simp [h] },
      case or.inr : h { simp [mem_of_mem_dict_erase h] }
    }
  }
end

end dict_append

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

@[simp] theorem nodup_keys_cons_of_not_dict_mem [decidable_eq α]
(s : sigma β) (h : s.1 d∉ l) :
  (s :: l).nodup_keys ↔ l.nodup_keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at h,
    rw [perm_nodup_keys (perm.swap hd s tl), nodup_keys_cons, ih h.2, nodup_keys_cons],
    simp [h.1]
  }
end

@[simp] theorem nodup_keys_dict_insert [decidable_eq α] (s : sigma β) :
  (l.dict_insert s).nodup_keys ↔ l.nodup_keys  :=
begin
  by_cases h : s.1 d∈ l,
  { simp [nodup_keys, dict_insert, h] },
  { rw [dict_insert_of_not_dict_mem h, nodup_keys_cons_of_not_dict_mem s h] }
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

theorem ne_of_nodup_keys_of_mem_dict_erase [decidable_eq α] : l.nodup_keys → s ∈ l.dict_erase a → a ≠ s.1 :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intros nd h₁,
    rw nodup_keys_cons at nd,
    by_cases h₂ : hd.1 = a; simp [h₂] at h₁,
    { induction h₂, exact nd.1 h₁ },
    { cases h₁,
      case or.inl : h { induction h, exact ne.symm h₂ },
      case or.inr : h { exact ih nd.2 h } }
  }
end

theorem nodup_keys_append [decidable_eq α] :
  l₁.nodup_keys → l₂.nodup_keys → (l₁ d++ l₂).nodup_keys :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp },
  case list.cons : hd tl ih l₂ {
    intros nd₁ nd₂,
    rw nodup_keys_cons at nd₁,
    rw [dict_append_cons, nodup_keys_cons],
    split,
    { exact λ _, or.rec (λ p, nd₁.1 p) (ne_of_nodup_keys_of_mem_dict_erase nd₂) ∘ mem_dict_append },
    { exact ih nd₁.2 (nodup_keys_dict_erase hd.1 nd₂) }
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

theorem dict_mem_iff_dict_keys : a d∈ l ↔ a ∈ l.dict_keys :=
by induction l with hd tl ih; [simp, {cases hd, simp [eq_comm, ih]}]

@[simp] theorem dict_keys_iff_ne_key_of_mem :
  (∀ (s : sigma β), s ∈ l → a ≠ s.1) ↔ a ∉ dict_keys l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih { simp [ih] }
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
        { exact absurd (dict_mem_iff_dict_keys.mp (dict_mem_of_mem h)) nd.1 } } },
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
    by_cases h : s₁.1 = a,
    { simp [h] },
    { simp at nd₁ nd₂, simp [h, ih nd₁.2 nd₂.2] }
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact eq.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

theorem perm_dict_subset (p : l₁ ~ l₂) : l₁ d⊆ l₂ :=
begin
  intro a,
  induction p,
  case list.perm.nil { exact id },
  case list.perm.skip : s₁ l₁ l₂ p ih {
    repeat {rw dict_mem_cons},
    exact or.rec or.inl (or.inr ∘ ih)
  },
  case list.perm.swap : s₁ s₂ l {
    repeat {rw dict_mem_cons},
    rw or.left_comm,
    exact id
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact ih₂₃ ∘ ih₁₂
  }
end

theorem dict_mem_of_perm (p : l₁ ~ l₂) : a d∈ l₁ ↔ a d∈ l₂ :=
⟨by apply perm_dict_subset p, by apply perm_dict_subset p.symm⟩

theorem perm_dict_insert (s : sigma β) (p : l₁ ~ l₂) :
  l₁.dict_insert s ~ l₂.dict_insert s :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : s' l₁ l₂ p ih {
    by_cases h : s'.1 = s.1,
    { simp [h, p, perm.skip] },
    { by_cases h₁ : s.1 d∈ l₁; by_cases h₂ : s.1 d∈ l₂,
      { simp [h, h₁, h₂, p, perm.skip] },
      { exact absurd ((dict_mem_of_perm p).mp h₁) h₂ },
      { exact absurd ((dict_mem_of_perm p).mpr h₂) h₁ },
      { simp [h, h₁, h₂, p, perm.skip] } }
  },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₂ : s₂.1 = s.1,
    { simp [h₂, perm.swap] },
    { by_cases h₁ : s₁.1 = s.1,
      { simp [h₂, h₁, perm.swap] },
      { by_cases h₃ : s.1 d∈ l; simp [h₃, h₂, h₁, perm.skip, perm.swap] } }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
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
    simp at nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁, perm.swap] }
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

theorem perm_dict_append_left (l : list (sigma β)) (p : l₁ ~ l₂) : l₁ d++ l ~ l₂ d++ l :=
begin
  induction p generalizing l,
  case list.perm.nil { refl },
  case list.perm.skip : s l₁ l₂ p ih {
    simp [ih (dict_erase s.1 l), perm.skip],
  },
  case list.perm.swap : s₁ s₂ l {
    simp [dict_erase_comm, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans (ih₁₂ l) (ih₂₃ l)
  }
end

theorem perm_dict_append_right : ∀ (l : list (sigma β)) {l₁ l₂ : list (sigma β)},
  l₁.nodup_keys → l₂.nodup_keys → l₁ ~ l₂ → l d++ l₁ ~ l d++ l₂
| []     _  _  _   _   p := p
| (s::l) l₁ l₂ nd₁ nd₂ p :=
  by simp [perm.skip s (perm_dict_append_right l (nodup_keys_dict_erase s.1 nd₁)
                                                 (nodup_keys_dict_erase s.1 nd₂)
                                                 (perm_dict_erase s.1 nd₁ nd₂ p))]

theorem perm_dict_append (nd₃ : l₃.nodup_keys) (nd₄ : l₄.nodup_keys)
  (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) : l₁ d++ l₃ ~ l₂ d++ l₄ :=
perm.trans (perm_dict_append_left l₃ p₁₂) (perm_dict_append_right l₂ nd₃ nd₄ p₃₄)

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
    simp at nd₂₁ nd₁₂,
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
