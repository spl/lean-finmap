import data.list.perm
import data.sigma.on_fst

universes u v

namespace option
variables {α : Type*} {o : option α}

@[simp] theorem is_some_eq_ff : is_some o = ff ↔ o = none :=
by cases o; simp [is_some]

end option

local attribute [simp] decidable.not_or_iff_and_not and.assoc
local attribute [-simp] sigma.forall

namespace list
variables {α : Type u} {β : α → Type v}
variables {a a₁ a₂ : α} {b : β a} {b₁ : β a₁} {b₂ : β a₂}
variables {s s₁ s₂ hd : sigma β}
variables {l l₁ l₂ l₃ l₄ tl : list (sigma β)}

/-- Keys: the list of keys from a list of dependent key-value pairs -/
def keys : list (sigma β) → list α :=
map sigma.fst

section keys

@[simp] theorem keys_nil : @keys α β [] = [] :=
rfl

@[simp] theorem keys_cons : (hd :: tl).keys = hd.1 :: tl.keys :=
rfl

@[simp] theorem keys_singleton : [s].keys = [s.1] :=
rfl

variables [decidable_eq α]

@[simp] theorem keys_iff_ne_key_of_mem :
  (∀ (s : sigma β), s ∈ l → a ≠ s.1) ↔ a ∉ keys l :=
by induction l; simp *

end keys

/-- Key-based single-pair membership test for a list of dependent key-value
pairs. This holds if at least one key is present. -/
def kmem [decidable_eq α] (a : α) (l : list (sigma β)) : Prop :=
a ∈ l.keys

local infix ` k∈ `:51 := kmem
local notation a ` k∉ `:51 l:51 := ¬ kmem a l

section kmem
variables [decidable_eq α]

@[simp] theorem kmem_nil : a k∉ @list.nil (sigma β) :=
by simp [kmem]

@[simp] theorem kmem_cons : a k∈ hd :: tl ↔ hd.1 = a ∨ a k∈ tl :=
by simp [kmem, eq_comm]

@[simp] theorem kmem_cons_eq (h : hd.1 = a) : a k∈ hd :: tl :=
kmem_cons.mpr $ or.inl h

theorem kmem_of_ne_of_kmem_cons (h₁ : hd.1 ≠ a) (h₂ : a k∈ hd :: tl) : a k∈ tl :=
or.elim (kmem_cons.mp h₂) (λ p, absurd p h₁) id

@[simp] theorem kmem_append : a k∈ l₁ ++ l₂ ↔ a k∈ l₁ ∨ a k∈ l₂ :=
by induction l₁; simp [*, or_assoc]

instance decidable_kmem (a : α) (l : list (sigma β)) : decidable (a k∈ l) :=
by unfold kmem; apply_instance

theorem kmem_cons_of_kmem (hd : sigma β) : a k∈ tl → a k∈ hd :: tl :=
by unfold kmem; rw keys_cons; exact mem_cons_of_mem hd.1

theorem eq_or_kmem_of_kmem_cons : a k∈ hd :: tl → a = hd.1 ∨ a k∈ tl :=
by unfold kmem; rw keys_cons; exact eq_or_mem_of_mem_cons

theorem kmem_of_mem : s ∈ l → s.1 k∈ l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih { cases hd, intro h, simp at h, cases h; simp [h, ih] }
end

theorem exists_mem_of_kmem : a k∈ l → ∃ (b : β a), sigma.mk a b ∈ l :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro h,
    simp at h,
    cases h with h h,
    { cases hd with a₁ b₁, induction h, exact ⟨b₁, mem_cons_self ⟨a₁, b₁⟩ tl⟩ },
    { cases ih h with b h, exact ⟨b, mem_cons_of_mem hd h⟩ }
  }
end

theorem not_kmem_cons_of_ne_of_not_kmem (h₁ : hd.1 ≠ a) (h₂ : a k∉ tl) :
  a k∉ hd :: tl :=
by simp [h₁, h₂]

theorem mem_of_ne_key_of_mem_cons (h : hd.1 ≠ s.1) : s ∈ hd :: tl → s ∈ tl :=
by cases s; cases hd; simp [ne.symm h]

end kmem

/-- Key-based subset test for a list of dependent key-value pairs. -/
def ksubset [decidable_eq α] (l₁ l₂ : list (sigma β)) : Prop :=
∀ ⦃a : α⦄, a k∈ l₁ → a k∈ l₂

local infix ` k⊆ `:51 := ksubset

section ksubset
variables [decidable_eq α]

@[simp] theorem ksubset.refl (l : list (sigma β)) : l k⊆ l :=
λ _ h, h

theorem ksubset.trans : l₁ k⊆ l₂ → l₂ k⊆ l₃ → l₁ k⊆ l₃ :=
λ h₁ h₂ _ m, h₂ (h₁ m)

theorem ksubset_of_sublist : ∀ {l₁ l₂ : list (sigma β)}, l₁ <+ l₂ → l₁ k⊆ l₂
| _ _ sublist.slnil              _  h := h
| _ _ (sublist.cons  l₁ l₂ s sl) a₂ h :=
  kmem_cons_of_kmem s (ksubset_of_sublist sl h)
| _ _ (sublist.cons2 l₁ l₂ s sl) a₂ h :=
  match kmem_cons.mp h with
  | or.inl h := kmem_cons_eq h
  | or.inr h := kmem_cons_of_kmem s (ksubset_of_sublist sl h)
  end

theorem keys_subset : l₁ k⊆ l₂ ↔ l₁.keys ⊆ l₂.keys :=
iff.rfl

end ksubset

/-- No duplicate keys in a list of dependent key-value pairs. -/
def nodup_keys : list (sigma β) → Prop := pairwise (sigma.on_fst (≠))

section nodup_keys

@[simp] theorem nodup_keys_nil : @nodup_keys α β [] :=
pairwise.nil _

@[simp] theorem nodup_keys_cons [decidable_eq α] :
  (hd :: tl).nodup_keys ↔ hd.1 k∉ tl ∧ tl.nodup_keys :=
by simp [nodup_keys, kmem, sigma.on_fst]

theorem nodup_of_nodup_keys : l.nodup_keys → l.nodup :=
pairwise.imp $ λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (h : a₁ ≠ a₂), by simp [h]

theorem keys_nodup_of_nodup_keys : l.nodup_keys → l.keys.nodup :=
(pairwise_map sigma.fst).mpr

theorem perm_nodup_keys (p : l₁ ~ l₂) : l₁.nodup_keys ↔ l₂.nodup_keys :=
perm_pairwise (@sigma.on_fst.symm α β (≠) (@ne.symm α)) p

@[simp] theorem nodup_keys_cons_of_not_kmem [decidable_eq α] (hd : sigma β) (h : hd.1 k∉ tl) :
  (hd :: tl).nodup_keys ↔ tl.nodup_keys :=
begin
  induction tl,
  case list.nil { simp },
  case list.cons : hd₁ tl ih {
    simp at h,
    simp [perm_nodup_keys (perm.swap hd₁ hd tl), ne.symm h.1, ih h.2],
  }
end

theorem perm_keys_of_perm [decidable_eq α] (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.keys ~ l₂.keys :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    simp [perm.skip hd.1 (ih nd₁.2 nd₂.2)]
  },
  case list.perm.swap : s₁ s₂ l {
    simp [perm.swap s₁.1 s₂.1 (keys l)]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

theorem perm_ksubset [decidable_eq α] (p : l₁ ~ l₂) : l₁ k⊆ l₂ :=
begin
  intro a,
  induction p,
  case list.perm.nil { exact id },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    repeat {rw kmem_cons},
    exact or.rec or.inl (or.inr ∘ ih)
  },
  case list.perm.swap : s₁ s₂ l {
    repeat {rw kmem_cons},
    rw or.left_comm,
    exact id
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact ih₂₃ ∘ ih₁₂
  }
end

theorem kmem_of_perm [decidable_eq α] (p : l₁ ~ l₂) : a k∈ l₁ ↔ a k∈ l₂ :=
⟨by apply perm_ksubset p, by apply perm_ksubset p.symm⟩

end nodup_keys

/-- Key-based single-value lookup for a list of dependent key-value pairs. The
result is the first key-matching value found, if one exists. -/
def klookup [decidable_eq α] (a : α) : list (sigma β) → option (β a)
| []         := none
| (hd :: tl) := if h : hd.1 = a then some (h.rec_on hd.2) else klookup tl

section klookup
variables [decidable_eq α]

@[simp] theorem klookup_nil : @klookup _ β _ a [] = none :=
rfl

local attribute [simp] klookup

@[simp] theorem klookup_cons_eq (h : hd.1 = a) :
  klookup a (hd :: tl) = some (h.rec_on hd.2) :=
by simp [h]

@[simp] theorem klookup_cons_ne (h : hd.1 ≠ a) :
  klookup a (hd :: tl) = klookup a tl :=
by simp [h]

@[simp] theorem klookup_eq (a : α) : ∀ (l : list (sigma β)),
  klookup a l = none ∨ ∃ (b : β a), klookup a l = some b
| []         := or.inl rfl
| (hd :: tl) :=
  if h₁ : hd.1 = a then
    or.inr ⟨h₁.rec_on hd.2, klookup_cons_eq h₁⟩
  else
    match klookup_eq tl with
    | or.inl h₂      := or.inl $ (klookup_cons_ne h₁).trans h₂
    | or.inr ⟨b, h₂⟩ := or.inr ⟨b, (klookup_cons_ne h₁).trans h₂⟩
    end

theorem klookup_not_kmem : a k∉ l ↔ klookup a l = none :=
by induction l with hd; [simp, {by_cases hd.1 = a; simp *}]

theorem klookup_iff_mem (nd : l.nodup_keys) : s.2 ∈ l.klookup s.1 ↔ s ∈ l :=
begin
  induction l generalizing s,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h : hd.1 = s.1,
    { rw klookup_cons_eq h,
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
        { exact absurd (kmem_of_mem h) nd.1 } } },
    { rw [klookup_cons_ne h, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro p,
        cases p with p p,
        { induction p, exact false.elim (ne.irrefl h) },
        { exact (ih nd.2).mpr p } } }
  }
end

theorem klookup_eq_of_perm (a : α) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.klookup a = l₂.klookup a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih nd₁ nd₂ {
    by_cases h : hd.1 = a,
    { simp [h] },
    { simp at nd₁ nd₂, simp [h, ih nd₁.2 nd₂.2] }
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [ne.symm nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact eq.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

end klookup

/-- Key-based multiple-value lookup for a list of dependent key-value pairs.
The result is a list of all key-matching values. -/
def klookup_all [decidable_eq α] (a : α) : list (sigma β) → list (β a)
| []         := []
| (hd :: tl) :=
   let tl' := klookup_all tl in
   if h : hd.1 = a then h.rec_on hd.2 :: tl' else tl'

section klookup_all
variables [decidable_eq α]

@[simp] theorem klookup_all_nil : @klookup_all _ β _ a [] = [] :=
rfl

local attribute [simp] klookup_all

@[simp] theorem klookup_all_cons_eq (h : hd.1 = a) :
  (hd :: tl).klookup_all a = h.rec_on hd.2 :: tl.klookup_all a :=
by simp [h]

@[simp] theorem klookup_all_cons_ne (h : hd.1 ≠ a) :
  (hd :: tl).klookup_all a = tl.klookup_all a :=
by simp [h]

theorem klookup_all_eq_head_klookup [inhabited (β a)] :
  (l.klookup_all a).head = (l.klookup a).iget :=
by induction l with hd; [refl, {by_cases hd.1 = a; simp *}]

theorem perm_klookup_all (a : α) (p : l₁ ~ l₂) :
  l₁.klookup_all a ~ l₂.klookup_all a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    by_cases h : hd.1 = a; simp [h, ih, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₁ : s₁.1 = a; by_cases h₂ : s₂.1 = a; simp [h₁, h₂, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
  }
end

end klookup_all

/-- Key-based single-pair erasure for a list of dependent key-value pairs. The
result is the list minus the first key-matching pair, if one exists. -/
def kerase [decidable_eq α] (a : α) : list (sigma β) → list (sigma β)
| []         := []
| (hd :: tl) := if h : hd.1 = a then tl else hd :: kerase tl

section kerase
variables [decidable_eq α]

@[simp] theorem kerase_nil : @kerase _ β _ a [] = [] :=
rfl

@[simp] theorem kerase_cons_eq (h : hd.1 = a) :
  (hd :: tl).kerase a = tl :=
by simp [kerase, h]

@[simp] theorem kerase_cons_ne (h : hd.1 ≠ a) :
  (hd :: tl).kerase a = hd :: tl.kerase a :=
by simp [kerase, h]

theorem kerase_cons (a : α) (hd : sigma β) (tl : list (sigma β)) :
  hd.1 = a ∧ (hd :: tl).kerase a = tl ∨
  hd.1 ≠ a ∧ (hd :: tl).kerase a = hd :: tl.kerase a :=
by by_cases h : hd.1 = a; simp [h]

@[simp] theorem mem_kerase_nil : s ∈ @kerase _ β _ a [] ↔ false :=
by simp

@[simp] theorem kerase_of_not_kmem (h : a k∉ l) : l.kerase a = l :=
by induction l with _ _ ih; [refl, {simp at h, simp [h.1, ih h.2]}]

theorem exists_kerase_eq (h : a k∈ l) :
  ∃ (b : β a) (l₁ l₂ : list (sigma β)),
    a k∉ l₁ ∧
    l = l₁ ++ ⟨a, b⟩ :: l₂ ∧
    l.kerase a = l₁ ++ l₂ :=
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
        exact ⟨b, hd :: tl₁, tl₂, not_kmem_cons_of_ne_of_not_kmem e h₁,
               by rw h₂; refl, by simp [e, h₃]⟩
      } }
  }
end

theorem kerase_sublist (a : α) (l : list (sigma β)) : l.kerase a <+ l :=
if h : a k∈ l then
  match l, l.kerase a, exists_kerase_eq h with
  | _, _, ⟨_, _, _, _, rfl, rfl⟩ := by simp
  end
else
  by simp [h]

theorem kerase_subset (a : α) (l : list (sigma β)) : l.kerase a ⊆ l :=
subset_of_sublist (kerase_sublist a l)

theorem mem_of_mem_kerase : s ∈ l.kerase a → s ∈ l :=
@kerase_subset _ _ _ _ _ _

@[simp] theorem mem_kerase_of_ne (h : s.1 ≠ a) : s ∈ l.kerase a ↔ s ∈ l :=
iff.intro mem_of_mem_kerase $ λ p,
  if q : a k∈ l then
    match l, l.kerase a, exists_kerase_eq q, p with
    | _, _, ⟨_, _, _, _, rfl, rfl⟩, p :=
      by clear _match; cases s; simpa [h] using p
    end
  else
    by simp [q, p]

theorem kerase_ksubset (a : α) (l : list (sigma β)) : l.kerase a k⊆ l :=
ksubset_of_sublist (kerase_sublist a l)

theorem kmem_of_kmem_kerase : a k∈ l.kerase a₁ → a k∈ l :=
@kerase_ksubset _ _ _ _ _ _

@[simp] theorem kmem_kerase_of_ne (h : a₂ ≠ a₁) : a₁ k∈ l.kerase a₂ ↔ a₁ k∈ l :=
iff.intro kmem_of_kmem_kerase $ λ p,
  if q : a₂ k∈ l then
    match l, l.kerase a₂, exists_kerase_eq q, p with
    | _, _, ⟨_, _, _, _, rfl, rfl⟩, p := by simpa [h] using p
    end
  else
    by simp [q, p]

theorem kerase_append_left : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  a k∈ l₁ → (l₁ ++ l₂).kerase a = l₁.kerase a ++ l₂
| []          _  h  := by cases h
| (hd :: tl₁) l₂ h₁ :=
  if h₂ : hd.1 = a then
    by simp [h₂]
  else
    by simp at h₁; cases h₁; [contradiction, simp [h₂, kerase_append_left l₂ h₁]]

theorem kerase_append_right : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  a k∉ l₁ → (l₁ ++ l₂).kerase a = l₁ ++ l₂.kerase a
| []         _  h := rfl
| (_ :: tl₁) l₂ h := by simp at h; simp [h.1, kerase_append_right l₂ h.2]

theorem kerase_comm (a₁ a₂ : α) (l : list (sigma β)) :
  (l.kerase a₁).kerase a₂ = (l.kerase a₂).kerase a₁ :=
if h : a₂ = a₁ then
  by simp [h]
else if ha₁ : a₁ k∈ l then
  if ha₂ : a₂ k∈ l then
    match l, l.kerase a₁, exists_kerase_eq ha₁, ha₂ with
    | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ :=
      if h' : a₂ k∈ l₁ then
        by simp [kerase_append_left _ h',
                 kerase_append_right _ (mt (kmem_kerase_of_ne h).mp a₁_nin_l₁)]
      else
        by simp [kerase_append_right _ h', kerase_append_right _ a₁_nin_l₁,
                 @kerase_cons_ne _ _ a₂ ⟨a₁, b₁⟩ _ _ (ne.symm h)]
    end
  else
    by simp [ha₂, mt kmem_of_kmem_kerase ha₂]
else
  by simp [ha₁, mt kmem_of_kmem_kerase ha₁]

@[simp] theorem nodup_keys_kerase (a : α) :
  l.nodup_keys → (l.kerase a).nodup_keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd,
    simp at nd,
    by_cases h : hd.1 = a,
    { simp [h, nd.2] },
    { rw [kerase_cons_ne h, nodup_keys_cons],
      exact ⟨mt (kmem_kerase_of_ne (ne.symm h)).mp nd.1, ih nd.2⟩ }
  }
end

@[simp] theorem not_kmem_kerase_self (nd : l.nodup_keys) :
  a k∉ l.kerase a :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h : hd.1 = a,
    { induction h, simp [nd.1] },
    { simp [h, ih nd.2] }
  }
end

@[simp] theorem klookup_kerase_of_nodup_keys (nd : l.nodup_keys) :
  (l.kerase a).klookup a = none :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h₁ : hd.1 = a,
    { by_cases h₂ : a k∈ tl,
      { induction h₁, exact absurd h₂ nd.1 },
      { simp [h₁, klookup_not_kmem.mp h₂] } },
    { simp [h₁, ih nd.2] }
  }
end

theorem ne_of_nodup_keys_of_mem_kerase :
  l.nodup_keys → s ∈ l.kerase a → a ≠ s.1 :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intros nd h,
    simp at nd,
    rcases kerase_cons a hd tl with ⟨he, p⟩ | ⟨hn, p⟩,
    { induction he,
      simp [p] at h,
      exact ne.symm (ne_of_mem_of_not_mem (kmem_of_mem h) nd.1) },
    { simp [hn] at h,
      cases h with h h,
      { induction h, exact ne.symm hn },
      { exact ih nd.2 h } }
  }
end

theorem perm_kerase (a : α) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.kerase a ~ l₂.kerase a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : hd.1 = a; simp [p, h, ih nd₁.2 nd₂.2, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [ne.symm nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁, perm.swap] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

end kerase

/-- Key-based multiple-pair erasure for a list of dependent key-value pairs.
The result is the list minus all key-matching pairs, if any exist. -/
def kerase_all [decidable_eq α] (a : α) : list (sigma β) → list (sigma β)
| []         := []
| (hd :: tl) :=
  let tl' := kerase_all tl in
  if h : hd.1 = a then tl' else hd :: tl'

section kerase_all
variables [decidable_eq α]

@[simp] theorem kerase_all_nil : @kerase_all _ β _ a [] = [] :=
rfl

@[simp] theorem kerase_all_cons_eq (h : hd.1 = a) :
  kerase_all a (hd :: tl) = kerase_all a tl :=
by simp [kerase_all, h]

@[simp] theorem kerase_all_cons_ne (h : hd.1 ≠ a) :
  kerase_all a (hd :: tl) = hd :: kerase_all a tl :=
by simp [kerase_all, h]

theorem perm_kerase_all (a : α) (p : l₁ ~ l₂) :
  l₁.kerase_all a ~ l₂.kerase_all a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    by_cases h : hd.1 = a; simp [h, ih, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₁ : s₁.1 = a; by_cases h₂ : s₂.1 = a; simp [h₁, h₂, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃
  }
end

end kerase_all

/-- Left-biased key-based append for a list of dependent key-value pairs.
The result of `l₁.kappend l₂` is constructed from `l₁` with `l₂` appended such
that the first pair matching each key in `l₁` is erased from `l₂`. Note that
the result can still have duplicates if duplicates exist in either argument. -/
def kappend [decidable_eq α] : list (sigma β) → list (sigma β) → list (sigma β)
| []         l := l
| (hd :: tl) l := hd :: kappend tl (kerase hd.1 l)

local infixr ` k++ `:67 := kappend

section kappend
variables [decidable_eq α]

@[simp] theorem nil_kappend (l : list (sigma β)) : [] k++ l = l :=
rfl

@[simp] theorem kappend_nil : ∀ (l : list (sigma β)), l k++ [] = l
| []        := rfl
| (_ :: tl) := by rw [kappend, kerase_nil, kappend_nil tl]

@[simp] theorem kappend_cons : (hd :: tl) k++ l = hd :: tl k++ kerase hd.1 l :=
rfl

@[simp] theorem kerase_kappend : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  l₁.kerase a k++ l₂.kerase a = (l₁ k++ l₂).kerase a
| []        _ := rfl
| (hd :: _) l := by by_cases h : hd.1 = a;
                    simp [h, kerase_comm a hd.1 l, kerase_kappend]

@[simp] theorem kappend_assoc (l₁ l₂ l₃ : list (sigma β)) :
  (l₁ k++ l₂) k++ l₃ = l₁ k++ (l₂ k++ l₃) :=
by induction l₁ generalizing l₂ l₃; simp *

theorem mem_kappend : s ∈ l₁ k++ l₂ → s ∈ l₁ ∨ s ∈ l₂ :=
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
      case or.inr : h { simp [mem_of_mem_kerase h] }
    }
  }
end

@[simp] theorem kmem_kappend : a k∈ l₁ k++ l₂ ↔ a k∈ l₁ ∨ a k∈ l₂ :=
by induction l₁ with hd generalizing l₂; [simp, {by_cases hd.1 = a; simp *}]

theorem nodup_keys_kappend (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) :
  (l₁ k++ l₂).nodup_keys :=
by induction l₁ generalizing l₂; simp at nd₁; simp *

theorem perm_kappend_left (l : list (sigma β)) (p : l₁ ~ l₂) : l₁ k++ l ~ l₂ k++ l :=
begin
  induction p generalizing l,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp [ih (kerase hd.1 l), perm.skip],
  },
  case list.perm.swap : s₁ s₂ l {
    simp [kerase_comm, perm.swap]
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans (ih₁₂ l) (ih₂₃ l)
  }
end

theorem perm_kappend_right : ∀ (l : list (sigma β)) {l₁ l₂ : list (sigma β)},
  l₁.nodup_keys → l₂.nodup_keys → l₁ ~ l₂ → l k++ l₁ ~ l k++ l₂
| []         _  _  _   _   p := p
| (hd :: tl) l₁ l₂ nd₁ nd₂ p :=
  by simp [perm.skip hd
    (perm_kappend_right tl (nodup_keys_kerase hd.1 nd₁)
                           (nodup_keys_kerase hd.1 nd₂)
                           (perm_kerase hd.1 nd₁ nd₂ p))]

theorem perm_kappend (nd₃ : l₃.nodup_keys) (nd₄ : l₄.nodup_keys)
  (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) : l₁ k++ l₃ ~ l₂ k++ l₄ :=
perm.trans (perm_kappend_left l₃ p₁₂) (perm_kappend_right l₂ nd₃ nd₄ p₃₄)

end kappend


/-- `cons` with `kerase` of the first `s`-key-matching pair -/
def kinsert [decidable_eq α] (s : sigma β) (l : list (sigma β)) : list (sigma β) :=
s :: l.kerase s.1

section kinsert
variables [decidable_eq α]

@[simp] theorem kinsert_eq_cons_kerase : l.kinsert s = s :: l.kerase s.1 :=
rfl

@[simp] theorem kinsert_kappend : l₁.kinsert s k++ l₂ = (l₁ k++ l₂).kinsert s :=
by simp

@[simp] theorem nodup_keys_kinsert (s : sigma β) (nd : l.nodup_keys) :
  (l.kinsert s).nodup_keys :=
(nodup_keys_cons_of_not_kmem _ (not_kmem_kerase_self nd)).mpr $ nodup_keys_kerase _ nd

theorem perm_kinsert (s : sigma β) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.kinsert s ~ l₂.kinsert s :=
perm.skip s $ perm_kerase s.1 nd₁ nd₂ p

end kinsert

/-- Key-based single-pair replacement for a list of dependent key-value pairs.
The result is the list with the first key-matching pair, if it exists, replaced
by the given pair. -/
def kreplace [decidable_eq α] (s : sigma β) : list (sigma β) → list (sigma β)
| []         := []
| (hd :: tl) := if h : hd.1 = s.1 then s :: tl else hd :: kreplace tl

section kreplace
variables [decidable_eq α]

@[simp] theorem kreplace_nil : kreplace s [] = [] :=
rfl

@[simp] theorem kreplace_cons_eq (h : hd.1 = s.1) :
  (hd :: tl).kreplace s = s :: tl :=
by simp [kreplace, h]

@[simp] theorem kreplace_cons_ne (h : hd.1 ≠ s.1) :
  (hd :: tl).kreplace s = hd :: tl.kreplace s :=
by simp [kreplace, h]

theorem kreplace_cons (s hd : sigma β) (tl : list (sigma β)) :
  hd.1 = s.1 ∧ (hd :: tl).kreplace s = s :: tl ∨
  hd.1 ≠ s.1 ∧ (hd :: tl).kreplace s = hd :: tl.kreplace s :=
by by_cases h : hd.1 = s.1; simp [h]

theorem mem_of_mem_kreplace_ne (h : s₂.1 ≠ s₁.1) : s₁ ∈ l.kreplace s₂ → s₁ ∈ l :=
begin
  induction l generalizing s₁ s₂,
  case list.nil { simp },
  case list.cons : hd tl ih {
    by_cases p : hd.1 = s₂.1,
    { rw kreplace_cons_eq p,
      exact mem_cons_of_mem hd ∘ mem_of_ne_key_of_mem_cons h },
    { rw [kreplace_cons_ne p, mem_cons_iff, mem_cons_iff],
      exact or.imp_right (ih h) }
  }
end

theorem kmem_of_kmem_kreplace_ne (h₁ : a ≠ s.1) (h₂ : a k∈ l.kreplace s) : a k∈ l :=
let ⟨b, h₃⟩ := exists_mem_of_kmem h₂ in
@kmem_of_mem _ _ ⟨a, b⟩ _ _ (mem_of_mem_kreplace_ne (ne.symm h₁) h₃)

@[simp] theorem nodup_keys_kreplace (s : sigma β) :
  l.nodup_keys → (l.kreplace s).nodup_keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd,
    simp at nd,
    by_cases p : hd.1 = s.1,
    { rw p at nd, simp [p, nd.1, nd.2] },
    { simp [p, nd.1, ih nd.2, mt (kmem_of_kmem_kreplace_ne p)] }
  }
end

theorem perm_kreplace (s : sigma β) (nd₁ : l₁.nodup_keys) (nd₂ : l₂.nodup_keys) (p : l₁ ~ l₂) :
  l₁.kreplace s ~ l₂.kreplace s :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : hd.1 = s.1; simp [p, h, ih nd₁.2 nd₂.2, perm.skip]
  },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = s.1,
    { rw kreplace_cons_eq h₂,
      by_cases h₁ : s₁.1 = s.1,
      { rw kreplace_cons_eq h₁,
        exact absurd (h₂.trans h₁.symm) nd₁₂.1 },
      { simp [h₁, h₂, perm.swap] } },
    { by_cases h₁ : s₁.1 = s.1; simp [h₁, h₂, perm.swap] }
  },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodup_keys := (perm_nodup_keys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃)
  }
end

end kreplace

/-- Key-based disjoint test for a list of dependent key-value pairs. -/
def kdisjoint [decidable_eq α] (l₁ l₂ : list (sigma β)) : Prop :=
∀ ⦃a : α⦄, a k∈ l₁ → a k∉ l₂

section kdisjoint
variables [decidable_eq α]

@[simp] theorem nil_kdisjoint : [].kdisjoint l :=
by simp [kdisjoint]

@[simp] theorem kdisjoint_nil : l.kdisjoint [] :=
by simp [kdisjoint]

@[simp] theorem kdisjoint_cons : (hd :: tl).kdisjoint l ↔ hd.1 k∉ l ∧ tl.kdisjoint l :=
by simp [kdisjoint, kmem]

@[simp] theorem map_kappend {γ : Type*} (f : sigma β → γ)
  (dj : l₁.kdisjoint l₂) : (l₁ k++ l₂).map f = l₁.map f ++ l₂.map f :=
by induction l₁ with _ _ ih; [refl, {simp at dj, simp [dj.1, ih dj.2]}]

theorem keys_kappend (dj : l₁.kdisjoint l₂) :
  (l₁ k++ l₂).keys = l₁.keys ++ l₂.keys :=
by simp [keys, dj]

end kdisjoint

end list
