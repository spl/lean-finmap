import data.list.perm
import data.sigma.on_fst

local attribute [simp] not_or_distrib and.assoc
local attribute [-simp] sigma.forall

namespace list

section αβ
variables {α : Type*} {β : α → Type*}

/-- Keys: the list of keys from a list of dependent key-value pairs -/
def keys : list (sigma β) → list α :=
map sigma.fst

section keys
variables {a : α} {s hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

@[simp] theorem keys_nil : @keys α β [] = [] :=
rfl

@[simp] theorem keys_cons : (hd :: tl).keys = hd.1 :: tl.keys :=
rfl

@[simp] theorem keys_singleton : [s].keys = [s.1] :=
rfl

@[simp] theorem keys_append : (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys :=
by simp [keys]

@[simp] theorem keys_iff_ne_key_of_mem :
  (∀ (s : sigma β), s ∈ l → a ≠ s.1) ↔ a ∉ l.keys :=
by induction l; simp *

theorem mem_of_ne_key_of_mem_cons (h : hd.1 ≠ s.1) : s ∈ hd :: tl → s ∈ tl :=
by cases s; cases hd; simp [ne.symm h]

theorem mem_keys_of_mem : s ∈ l → s.1 ∈ l.keys :=
mem_map_of_mem sigma.fst

theorem exists_mem_of_mem_keys (h : a ∈ l.keys) : ∃ (b : β a), sigma.mk a b ∈ l :=
let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_map h in
eq.rec_on e (exists.intro b' m)

theorem mem_keys : a ∈ l.keys ↔ ∃ (b : β a), sigma.mk a b ∈ l :=
⟨exists_mem_of_mem_keys, λ ⟨b, h⟩, mem_keys_of_mem h⟩

end keys

/-- No duplicate keys in a list of dependent key-value pairs. -/
def nodupkeys : list (sigma β) → Prop :=
pairwise (sigma.fst_rel (≠))

section nodupkeys
variables {s t hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

@[simp] theorem nodupkeys_nil : @nodupkeys α β [] :=
pairwise.nil _

@[simp] theorem nodupkeys_cons :
  (hd :: tl).nodupkeys ↔ hd.1 ∉ tl.keys ∧ tl.nodupkeys :=
by simp [nodupkeys, sigma.fst_rel]

theorem nodupkeys_cons_of_nodupkeys (h : hd.1 ∉ tl.keys)
  (t : nodupkeys tl) : nodupkeys (hd :: tl) :=
nodupkeys_cons.mpr ⟨h, t⟩

theorem nodupkeys_singleton (s : sigma β) : nodupkeys [s] :=
nodupkeys_cons_of_nodupkeys (not_mem_nil s.1) nodupkeys_nil

theorem nodup_of_nodupkeys : l.nodupkeys → l.nodup :=
pairwise.imp $ λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (h : a₁ ≠ a₂), by simp [h]

@[simp] theorem nodupkeys_iff : l.keys.nodup ↔ l.nodupkeys :=
pairwise_map sigma.fst

theorem perm_nodupkeys (p : l₁ ~ l₂) : l₁.nodupkeys ↔ l₂.nodupkeys :=
perm_pairwise (@sigma.fst_rel.symm α β (≠) (@ne.symm α)) p

@[simp] theorem nodupkeys_cons_of_not_mem_keys (h : hd.1 ∉ tl.keys) :
  (hd :: tl).nodupkeys ↔ tl.nodupkeys :=
begin
  induction tl,
  case list.nil { simp },
  case list.cons : hd₁ tl ih {
    simp at h,
    simp [perm_nodupkeys (perm.swap hd₁ hd tl), ne.symm h.1, ih h.2] }
end

variables {ls : list (list (sigma β))}

theorem nodupkeys_join : (join ls).nodupkeys ↔
  (∀ {l : list (sigma β)}, l ∈ ls → l.nodupkeys) ∧ pairwise disjoint (ls.map keys) :=
have ∀ (l₁ l₂ : list (sigma β)), (∀ (s ∈ l₁) (t ∈ l₂), sigma.fst_rel ne s t) ↔ disjoint l₁.keys l₂.keys :=
  λ l₁ l₂,
  have h₁ : (∀ (s : sigma β), s ∈ l₁ → s.1 ∉ l₂.keys) → disjoint l₁.keys l₂.keys :=
    λ f a mkas mkat, let ⟨b, mabs⟩ := exists_mem_of_mem_keys mkas in
    absurd mkat $ f ⟨a, b⟩ mabs,
  have h₂ : disjoint l₁.keys l₂.keys → ∀ (s : sigma β), s ∈ l₁ → s.1 ∉ l₂.keys :=
    λ dj s mss mkat, absurd mkat $ dj $ mem_keys_of_mem mss,
  ⟨by simpa using h₁, by simpa using h₂⟩,
pairwise_join.trans $ and_congr iff.rfl $ (pairwise.iff this).trans (pairwise_map _).symm

theorem nodup_enum_map_fst (l : list α) : (l.enum.map prod.fst).nodup :=
by simp [list.nodup_range]

theorem perm_keys_of_perm (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
  l₁.keys ~ l₂.keys :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    simp [perm.skip hd.1 (ih nd₁.2 nd₂.2)] },
  case list.perm.swap : s₁ s₂ l {
    simp [perm.swap s₁.1 s₂.1 (keys l)] },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodupkeys := (perm_nodupkeys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃) }
end

-- Is this useful?
theorem nodupkeys_functional (d : l.nodupkeys) (ms : s ∈ l) (mt : t ∈ l)
  (h : s.1 = t.1) : (eq.rec_on h s.2 : β t.1) = t.2 :=
begin
  induction d,
  case pairwise.nil { cases ms },
  case pairwise.cons : _ _ r _ ih {
    simp at ms mt,
    cases ms; cases mt,
    { subst ms, subst mt },
    { induction ms, exact absurd h (r _ mt) },
    { induction mt, exact absurd h (ne.symm (r _ ms)) },
    { exact ih ms mt } },
end

-- Is this useful?
theorem eq_of_nodupkeys_of_eq_fst (d : l.nodupkeys) (ms : s ∈ l) (mt : t ∈ l)
  (h : s.1 = t.1) : s = t :=
sigma.eq h $ nodupkeys_functional d ms mt h

end nodupkeys

section decidable_eq_α
variables [decidable_eq α]

/-- Key-based single-value lookup in a list of dependent key-value pairs. The
result is the first key-matching value found, if one exists. -/
def klookup (a : α) : list (sigma β) → option (β a)
| []         := none
| (hd :: tl) := if h : hd.1 = a then some (h.rec_on hd.2) else klookup tl

section klookup
variables {a : α} {s hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

@[simp] theorem klookup_nil : @klookup _ β _ a [] = none :=
rfl

@[simp] theorem klookup_cons_eq (h : hd.1 = a) :
  klookup a (hd :: tl) = some (h.rec_on hd.2) :=
by simp [klookup, h]

@[simp] theorem klookup_cons_ne (h : hd.1 ≠ a) :
  klookup a (hd :: tl) = klookup a tl :=
by simp [klookup, h]

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

theorem klookup_not_mem_keys : a ∉ l.keys ↔ klookup a l = none :=
by induction l with hd _ ih;
   [simp, {by_cases h : hd.1 = a; [simp [h], simp [h, ne.symm h, ih]]}]

theorem mem_klookup_of_nodupkeys (nd : l.nodupkeys) : s.2 ∈ l.klookup s.1 ↔ s ∈ l :=
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
        { exact absurd (mem_keys_of_mem h) nd.1 } } },
    { rw [klookup_cons_ne h, mem_cons_iff],
      split,
      { exact or.inr ∘ (ih nd.2).mp },
      { intro p,
        cases p with p p,
        { induction p, exact false.elim (ne.irrefl h) },
        { exact (ih nd.2).mpr p } } } }
end

theorem perm_klookup (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
  l₁.klookup a = l₂.klookup a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih nd₁ nd₂ {
    by_cases h : hd.1 = a,
    { simp [h] },
    { simp at nd₁ nd₂, simp [h, ih nd₁.2 nd₂.2] } },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁] } },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodupkeys := (perm_nodupkeys p₁₂).mp nd₁,
    exact eq.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃) }
end

end klookup

/-- Key-based multiple-value lookup in a list of dependent key-value pairs.
The result is a list of all key-matching values. -/
def klookup_all (a : α) : list (sigma β) → list (β a)
| []         := []
| (hd :: tl) :=
  let tl' := klookup_all tl in
  if h : hd.1 = a then h.rec_on hd.2 :: tl' else tl'

section klookup_all
variables {a : α} {hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

@[simp] theorem klookup_all_nil : @klookup_all _ β _ a [] = [] :=
rfl

@[simp] theorem klookup_all_cons_eq (h : hd.1 = a) :
  (hd :: tl).klookup_all a = h.rec_on hd.2 :: tl.klookup_all a :=
by simp [klookup_all, h]

@[simp] theorem klookup_all_cons_ne (h : hd.1 ≠ a) :
  (hd :: tl).klookup_all a = tl.klookup_all a :=
by simp [klookup_all, h]

theorem klookup_all_head [inhabited (β a)] :
  (l.klookup_all a).head = (l.klookup a).iget :=
by induction l with hd; [refl, {by_cases hd.1 = a; simp *}]

theorem perm_klookup_all (p : l₁ ~ l₂) : l₁.klookup_all a ~ l₂.klookup_all a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    by_cases h : hd.1 = a; simp [h, ih, perm.skip] },
  case list.perm.swap : s₁ s₂ l {
    by_cases h₁ : s₁.1 = a; by_cases h₂ : s₂.1 = a; simp [h₁, h₂, perm.swap] },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans ih₁₂ ih₂₃ }
end

end klookup_all

/-- Key-based single-pair erasure in a list of dependent key-value pairs. The
result is the list minus the first key-matching pair, if one exists. -/
def kerase (a : α) : list (sigma β) → list (sigma β)
| []         := []
| (hd :: tl) := if hd.1 = a then tl else hd :: kerase tl

section kerase
variables {a a₁ a₂ : α} {s hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

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

@[simp] theorem kerase_of_not_mem_keys (h : a ∉ l.keys) : l.kerase a = l :=
by induction l with _ _ ih;
   [refl, {simp at h, simp [h.1, ne.symm h.1, ih h.2]}]

theorem exists_kerase_eq (h : a ∈ l.keys) :
  ∃ (b : β a) (l₁ l₂ : list (sigma β)),
    a ∉ l₁.keys ∧
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
      case or.inl : h { exact absurd h (ne.symm e) },
      case or.inr : h {
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩,
        exact ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem (ne.symm e) h₁,
               by rw h₂; refl, by simp [e, h₃]⟩ } } }
end

theorem kerase_sublist (a : α) (l : list (sigma β)) : l.kerase a <+ l :=
if h : a ∈ l.keys then
  match l, l.kerase a, exists_kerase_eq h with
  | _, _, ⟨_, _, _, _, rfl, rfl⟩ := by simp
  end
else
  by simp [h]

theorem kerase_subset (a : α) (l : list (sigma β)) : l.kerase a ⊆ l :=
subset_of_sublist (kerase_sublist a l)

theorem kerase_sublist_kerase (a : α) : ∀ {l₁ l₂ : list (sigma β)},
  l₁ <+ l₂ → l₁.kerase a <+ l₂.kerase a
| _ _ sublist.slnil := sublist.slnil
| _ _ (sublist.cons  l₁ l₂ hd sl) :=
  if h : hd.1 = a then
    by rw [kerase_cons_eq h]; exact (kerase_sublist _ _).trans sl
  else
    by rw kerase_cons_ne h; exact (kerase_sublist_kerase sl).cons _ _ _
| _ _ (sublist.cons2 l₁ l₂ hd sl) :=
  if h : hd.1 = a then
    by repeat {rw kerase_cons_eq h}; exact sl
  else
    by repeat {rw kerase_cons_ne h}; exact (kerase_sublist_kerase sl).cons2 _ _ _

theorem mem_of_mem_kerase : s ∈ l.kerase a → s ∈ l :=
@kerase_subset _ _ _ _ _ _

@[simp] theorem mem_kerase_of_ne (h : s.1 ≠ a) : s ∈ l.kerase a ↔ s ∈ l :=
iff.intro mem_of_mem_kerase $ λ p,
  if q : a ∈ l.keys then
    match l, l.kerase a, exists_kerase_eq q, p with
    | _, _, ⟨_, _, _, _, rfl, rfl⟩, p :=
      by clear _match; cases s; simpa [h] using p
    end
  else
    by simp [q, p]

theorem kerase_subset_keys (a : α) (l : list (sigma β)) :
  (l.kerase a).keys ⊆ l.keys :=
subset_of_sublist (map_sublist_map _ (kerase_sublist a l))

theorem mem_keys_of_mem_keys_kerase : a₁ ∈ (l.kerase a₂).keys → a₁ ∈ l.keys :=
@kerase_subset_keys _ _ _ _ _ _

@[simp] theorem mem_keys_kerase_of_ne (h : a₂ ≠ a₁) :
  a₁ ∈ (l.kerase a₂).keys ↔ a₁ ∈ l.keys :=
iff.intro mem_keys_of_mem_keys_kerase $ λ p,
  if q : a₂ ∈ l.keys then
    match l, l.kerase a₂, exists_kerase_eq q, p with
    | _, _, ⟨_, _, _, _, rfl, rfl⟩, p := by simpa [ne.symm h] using p
    end
  else
    by simp [q, p]

@[simp] theorem nodupkeys_kerase (a : α) :
  l.nodupkeys → (l.kerase a).nodupkeys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd,
    simp at nd,
    by_cases h : hd.1 = a,
    { simp [h, nd.2] },
    { rw [kerase_cons_ne h, nodupkeys_cons],
      exact ⟨mt (mem_keys_kerase_of_ne (ne.symm h)).mp nd.1, ih nd.2⟩ } }
end

@[simp] theorem not_mem_keys_kerase_self (nd : l.nodupkeys) :
  a ∉ (l.kerase a).keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h : hd.1 = a,
    { induction h, simp [nd.1] },
    { simp [h, ne.symm h, ih nd.2] } }
end

theorem kerase_append_left : ∀ {l₁ l₂ : list (sigma β)},
  a ∈ l₁.keys → (l₁ ++ l₂).kerase a = l₁.kerase a ++ l₂
| []          _  h  := by cases h
| (hd :: tl₁) l₂ h₁ :=
  if h₂ : hd.1 = a then
    by simp [h₂]
  else
    by simp at h₁; cases h₁;
       [exact absurd h₁ (ne.symm h₂), simp [h₂, kerase_append_left h₁]]

theorem kerase_append_right : ∀ {l₁ l₂ : list (sigma β)},
  a ∉ l₁.keys → (l₁ ++ l₂).kerase a = l₁ ++ l₂.kerase a
| []         _  h := rfl
| (_ :: tl₁) l₂ h := by simp at h; simp [ne.symm h.1, kerase_append_right h.2]

theorem kerase_comm (a₁ a₂ : α) (l : list (sigma β)) :
  (l.kerase a₁).kerase a₂ = (l.kerase a₂).kerase a₁ :=
if h : a₂ = a₁ then
  by simp [h]
else if ha₁ : a₁ ∈ l.keys then
  if ha₂ : a₂ ∈ l.keys then
    match l, l.kerase a₁, exists_kerase_eq ha₁, ha₂ with
    | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ :=
      if h' : a₂ ∈ l₁.keys then
        by simp [kerase_append_left h',
                 kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
      else
        by simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
                 @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (ne.symm h)]
    end
  else
    by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
else
  by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]

@[simp] theorem klookup_kerase (nd : l.nodupkeys) : (l.kerase a).klookup a = none :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h₁ : hd.1 = a,
    { by_cases h₂ : a ∈ tl.keys,
      { induction h₁, exact absurd h₂ nd.1 },
      { simp [h₁, klookup_not_mem_keys.mp h₂] } },
    { simp [h₁, ih nd.2] } }
end

theorem ne_of_nodupkeys_of_mem_kerase :
  l.nodupkeys → s ∈ l.kerase a → a ≠ s.1 :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intros nd h,
    simp at nd,
    rcases kerase_cons a hd tl with ⟨he, p⟩ | ⟨hn, p⟩,
    { induction he,
      simp [p] at h,
      exact ne.symm (ne_of_mem_of_not_mem (mem_keys_of_mem h) nd.1) },
    { simp [hn] at h,
      cases h with h h,
      { induction h, exact ne.symm hn },
      { exact ih nd.2 h } } }
end

theorem nodupkeys_kerase_eq_filter (a : α) (nd : l.nodupkeys) :
  l.kerase a = filter (λ s, s.1 ≠ a) l :=
begin
  induction nd,
  case pairwise.nil { refl },
  case pairwise.cons : s l n p ih {
    by_cases h : s.1 = a,
    { have : filter (λ (t : sigma β), t.1 ≠ a) l = l :=
        filter_eq_self.mpr (λ t th, h ▸ ne.symm (n t th)),
      simp [h, kerase, filter, this] },
    { simp [h, ih] } }
end

@[simp] theorem mem_kerase_of_nodupkeys (nd : l.nodupkeys) :
  s ∈ l.kerase a ↔ s.1 ≠ a ∧ s ∈ l :=
by rw nodupkeys_kerase_eq_filter a nd; simp [and_comm]

theorem perm_kerase (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
  l₁.kerase a ~ l₂.kerase a :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : hd.1 = a; simp [p, h, ih nd₁.2 nd₂.2, perm.skip] },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₁₂,
    by_cases h₂ : s₂.1 = a,
    { induction h₂, simp [nd₁₂.1] },
    { by_cases h₁ : s₁.1 = a; simp [h₂, h₁, perm.swap] } },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodupkeys := (perm_nodupkeys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃) }
end

end kerase

/-- `cons` with `kerase` of the first `s`-key-matching pair -/
def kinsert (s : sigma β) (l : list (sigma β)) : list (sigma β) :=
s :: l.kerase s.1

section kinsert
variables {a : α} {s t hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

@[simp] theorem kinsert_eq_cons_kerase : tl.kinsert hd = hd :: tl.kerase hd.1 :=
rfl

@[simp] theorem mem_kinsert : s ∈ kinsert t l ↔ s = t ∨ s ∈ l.kerase t.1 :=
by simp [kinsert]

@[simp] theorem mem_keys_kinsert : a ∈ (l.kinsert s).keys ↔ s.1 = a ∨ a ∈ l.keys :=
by by_cases h : s.1 = a; [simp [h], simp [h, ne.symm h]]

@[simp] theorem nodupkeys_kinsert (s : sigma β) (nd : l.nodupkeys) :
  (l.kinsert s).nodupkeys :=
(nodupkeys_cons_of_not_mem_keys (not_mem_keys_kerase_self nd)).mpr $
  nodupkeys_kerase _ nd

theorem perm_kinsert (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
  l₁.kinsert s ~ l₂.kinsert s :=
perm.skip s $ perm_kerase nd₁ nd₂ p

end kinsert

/-- Key-based single-pair replacement in a list of dependent key-value pairs.
The result is the list with the first key-matching pair, if it exists, replaced
by the given pair. -/
def kreplace (s : sigma β) : list (sigma β) → list (sigma β)
| []         := []
| (hd :: tl) := if h : hd.1 = s.1 then s :: tl else hd :: kreplace tl

section kreplace
variables {a : α} {s t hd : sigma β} {l l₁ l₂ tl : list (sigma β)}

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

theorem mem_of_mem_kreplace_ne (h : t.1 ≠ s.1) : s ∈ l.kreplace t → s ∈ l :=
begin
  induction l generalizing s t,
  case list.nil { simp },
  case list.cons : hd tl ih {
    by_cases p : hd.1 = t.1,
    { rw kreplace_cons_eq p,
      exact mem_cons_of_mem hd ∘ mem_of_ne_key_of_mem_cons h },
    { rw [kreplace_cons_ne p, mem_cons_iff, mem_cons_iff],
      exact or.imp_right (ih h) } }
end

theorem mem_keys_of_mem_keys_kreplace_ne (h₁ : a ≠ s.1) (h₂ : a ∈ (l.kreplace s).keys) :
  a ∈ l.keys :=
let ⟨b, h₃⟩ := exists_mem_of_mem_keys h₂ in
@mem_keys_of_mem _ _ ⟨a, b⟩ _ (mem_of_mem_kreplace_ne (ne.symm h₁) h₃)

@[simp] theorem nodupkeys_kreplace (s : sigma β) :
  l.nodupkeys → (l.kreplace s).nodupkeys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    intro nd,
    simp at nd,
    by_cases p : hd.1 = s.1,
    { rw p at nd, simp [p, nd.1, nd.2] },
    { simp [p, nd.1, ih nd.2, mt (mem_keys_of_mem_keys_kreplace_ne p)] } }
end

theorem perm_kreplace (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
  l₁.kreplace s ~ l₂.kreplace s :=
begin
  induction p,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp at nd₁ nd₂,
    by_cases h : hd.1 = s.1; simp [p, h, ih nd₁.2 nd₂.2, perm.skip] },
  case list.perm.swap : s₁ s₂ l nd₂₁ nd₁₂ {
    simp at nd₂₁ nd₁₂,
    by_cases h₂ : s₂.1 = s.1,
    { rw kreplace_cons_eq h₂,
      by_cases h₁ : s₁.1 = s.1,
      { rw kreplace_cons_eq h₁,
        exact absurd (h₁.trans h₂.symm) nd₁₂.1 },
      { simp [h₁, h₂, perm.swap] } },
    { by_cases h₁ : s₁.1 = s.1; simp [h₁, h₂, perm.swap] } },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ nd₁ nd₃ {
    have nd₂ : l₂.nodupkeys := (perm_nodupkeys p₁₂).mp nd₁,
    exact perm.trans (ih₁₂ nd₁ nd₂) (ih₂₃ nd₂ nd₃) }
end

end kreplace

/-- Left-biased key-based union of lists of dependent key-value pairs.
The result of `l₁.kunion l₂` is constructed from `l₁` with `l₂` appended such
that the first pair matching each key in `l₁` is erased from `l₂`. Note that
the result can still have duplicates if duplicates exist in either argument. -/
def kunion : list (sigma β) → list (sigma β) → list (sigma β)
| []         l := l
| (hd :: tl) l := hd :: kunion tl (kerase hd.1 l)

section kunion
variables {a : α} {s hd : sigma β} {l l₁ l₂ l₃ l₄ tl : list (sigma β)}

@[simp] theorem nil_kunion (l : list (sigma β)) : [].kunion l = l :=
rfl

@[simp] theorem kunion_nil : ∀ (l : list (sigma β)), l.kunion [] = l
| []        := rfl
| (_ :: tl) := by rw [kunion, kerase_nil, kunion_nil tl]

@[simp] theorem kunion_cons : (hd :: tl).kunion l = hd :: tl.kunion (l.kerase hd.1) :=
rfl

@[simp] theorem kerase_kunion : ∀ {l₁ : list (sigma β)} (l₂ : list (sigma β)),
  (l₁.kerase a).kunion (l₂.kerase a) = (l₁.kunion l₂).kerase a
| []        _ := rfl
| (hd :: _) l := by by_cases h : hd.1 = a;
                    simp [h, kerase_comm a hd.1 l, kerase_kunion]

@[simp] theorem map_kunion {γ : Type*} (f : sigma β → γ)
  (dk : disjoint l₁.keys l₂.keys) : (l₁.kunion l₂).map f = l₁.map f ++ l₂.map f :=
by induction l₁ with _ _ ih; [refl, {simp at dk, simp [dk.1, ih dk.2.symm]}]

theorem keys_kunion (dk : disjoint l₁.keys l₂.keys) :
  (l₁.kunion l₂).keys = l₁.keys ++ l₂.keys :=
by simp [keys, dk]

@[simp] theorem kinsert_kunion : (l₁.kinsert s).kunion l₂ = (l₁.kunion l₂).kinsert s :=
by simp

@[simp] theorem kunion_assoc : (l₁.kunion l₂).kunion l₃ = l₁.kunion (l₂.kunion l₃) :=
by induction l₁ generalizing l₂ l₃; simp *

theorem mem_of_mem_kunion : s ∈ l₁.kunion l₂ → s ∈ l₁ ∨ s ∈ l₂ :=
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
      case or.inr : h { simp [mem_of_mem_kerase h] } } }
end

theorem mem_kunion_left (l₂ : list (sigma β)) (h : s ∈ l₁) : s ∈ l₁.kunion l₂ :=
by induction l₁ generalizing l₂; simp at h; cases h; simp *

theorem mem_kunion_right (h₁ : s.1 ∉ l₁.keys) (h₂ : s ∈ l₂) : s ∈ l₁.kunion l₂ :=
by induction l₁ generalizing l₂; simp at h₁; cases h₁; simp *

theorem mem_kunion_of_disjoint_keys (dk : disjoint l₁.keys l₂.keys) (h : s ∈ l₁ ∨ s ∈ l₂) :
  s ∈ l₁.kunion l₂ :=
begin
  cases h with h h,
  { exact mem_kunion_left _ h },
  { by_cases p : s.1 ∈ l₁.keys,
    { exact absurd h (mt mem_keys_of_mem (dk p)) },
    { exact mem_kunion_right p h } }
end

@[simp] theorem mem_kunion_iff (dk : disjoint l₁.keys l₂.keys) : s ∈ l₁.kunion l₂ ↔ s ∈ l₁ ∨ s ∈ l₂ :=
⟨mem_of_mem_kunion, mem_kunion_of_disjoint_keys dk⟩

@[simp] theorem mem_keys_kunion : a ∈ (l₁.kunion l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys :=
by induction l₁ with hd _ ih generalizing l₂;
   [simp, {by_cases h : hd.1 = a; [simp [h], simp [h, ne.symm h, ih]]}]

theorem nodupkeys_kunion (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) :
  (l₁.kunion l₂).nodupkeys :=
by induction l₁ generalizing l₂; simp at nd₁; simp *

theorem perm_kunion_left (l : list (sigma β)) (p : l₁ ~ l₂) : l₁.kunion l ~ l₂.kunion l :=
begin
  induction p generalizing l,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp [ih (kerase hd.1 l), perm.skip] },
  case list.perm.swap : s₁ s₂ l {
    simp [kerase_comm, perm.swap] },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans (ih₁₂ l) (ih₂₃ l) }
end

theorem perm_kunion_right : ∀ (l : list (sigma β)) {l₁ l₂ : list (sigma β)},
  l₁.nodupkeys → l₂.nodupkeys → l₁ ~ l₂ → l.kunion l₁ ~ l.kunion l₂
| []         _  _  _   _   p := p
| (hd :: tl) l₁ l₂ nd₁ nd₂ p :=
  by simp [perm.skip hd
    (perm_kunion_right tl (nodupkeys_kerase hd.1 nd₁)
                           (nodupkeys_kerase hd.1 nd₂)
                           (perm_kerase nd₁ nd₂ p))]

theorem perm_kunion (nd₂ : l₂.nodupkeys) (nd₄ : l₄.nodupkeys)
  (p₁₃ : l₁ ~ l₃) (p₂₄ : l₂ ~ l₄) : l₁.kunion l₂ ~ l₃.kunion l₄ :=
perm.trans (perm_kunion_left l₂ p₁₃) (perm_kunion_right l₃ nd₂ nd₄ p₂₄)

end kunion

end decidable_eq_α

end αβ

section α₁α₂α₃β₁β₂β₃
universes u v
variables {α₁ α₂ α₃ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}

section keys
variables {s : sigma β₁} {l : list (sigma β₁)} {f : sigma β₁ → sigma β₂}

theorem mem_keys_map_of_mem (f : sigma β₁ → sigma β₂) (ms : s ∈ l) :
  (f s).1 ∈ (l.map f).keys :=
mem_keys_of_mem (mem_map_of_mem f ms)

theorem mem_keys_map (ff : sigma.fst_functional f) (h : s.1 ∈ l.keys) :
  (f s).1 ∈ (l.map f).keys :=
let ⟨_, m, e⟩ := exists_of_mem_map h in ff e ▸ mem_keys_map_of_mem f m

theorem mem_keys_of_mem_keys_map (fi : sigma.fst_injective f) (h : (f s).1 ∈ (l.map f).keys) :
  s.1 ∈ l.keys :=
have h : (sigma.fst ∘ f) s ∈ map (sigma.fst ∘ f) l, by simpa [keys] using h,
let ⟨_, m, e⟩ := exists_of_mem_map h in fi e ▸ mem_keys_of_mem m

-- Is this useful?
theorem mem_keys_of_mem_map (fi : sigma.fst_injective f) (h : f s ∈ l.map f) : s.1 ∈ l.keys :=
let ⟨_, m, e⟩ := exists_of_mem_map h in
fi (sigma.eq_fst e) ▸ mem_keys_of_mem m

@[simp] theorem mem_keys_map_iff (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  (f s).1 ∈ (l.map f).keys ↔ s.1 ∈ l.keys :=
⟨mem_keys_of_mem_keys_map fi, mem_keys_map ff⟩

end keys

section nodupkeys
variables {s t : sigma β₁} {l : list (sigma β₁)} {f : sigma β₁ → sigma β₂}

-- Is this useful?
theorem nodupkeys_injective (fi : sigma.fst_injective f) (d : l.nodupkeys)
  (ms : s ∈ l) (mt : t ∈ l) (h : f s = f t) : s = t :=
eq_of_nodupkeys_of_eq_fst d ms mt $ fi $ sigma.eq_fst h

theorem nodupkeys_of_nodupkeys_map (ff : sigma.fst_functional f) :
  nodupkeys (map f l) → nodupkeys l :=
pairwise_of_pairwise_map f $ λ s t, mt (@ff s t)

theorem nodupkeys_map (fi : sigma.fst_injective f) :
  l.nodupkeys → (l.map f).nodupkeys :=
pairwise_map_of_pairwise f
  (λ s t (h : s ∈ l ∧ t ∈ l ∧ s.1 ≠ t.1), mt (@fi s t) h.2.2) ∘
  pairwise.and_mem.mp

theorem nodupkeys_map_iff (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  (l.map f).nodupkeys ↔ l.nodupkeys :=
⟨nodupkeys_of_nodupkeys_map ff, nodupkeys_map fi⟩

-- Is this useful?
theorem mem_map_of_mem_of_mem_keys_map (fi : sigma.fst_injective f) (d : l.nodupkeys)
  (ms : s ∈ l) (mfs : (f s).1 ∈ (l.map f).keys) : f s ∈ l.map f :=
begin
  simp [keys] at mfs,
  rcases mfs with ⟨a, b, mab, ef⟩,
  cases s with sa sb,
  have ea : a = sa := fi ef,
  subst ea,
  have eb : b = sb := nodupkeys_functional d mab ms rfl,
  subst eb,
  exact mem_map_of_mem f mab,
end

end nodupkeys

section map_disjoint
variables {l₁ l₂ : list (sigma β₁)} {f : sigma β₁ → sigma β₂}

theorem map_disjoint_keys_of_disjoint_keys (fi : sigma.fst_injective f)
  (dk : disjoint l₁.keys l₂.keys) : disjoint (l₁.map f).keys (l₂.map f).keys :=
λ a h₁ h₂,
have h₁ : a ∈ map (sigma.fst ∘ f) l₁, by simpa [keys] using h₁,
let ⟨s, m, e⟩ := exists_of_mem_map h₁ in
have e : (f s).1 = a := e,
dk (mem_keys_of_mem m) (mem_keys_of_mem_keys_map fi (e.symm ▸ h₂))

theorem disjoint_keys_of_map_disjoint_keys (ff : sigma.fst_functional f)
  (dk : disjoint (l₁.map f).keys (l₂.map f).keys) : disjoint l₁.keys l₂.keys :=
λ a h₁ h₂, let ⟨b₁, h₁⟩ := exists_mem_of_mem_keys h₁ in
dk (mem_keys_map_of_mem f h₁) (mem_keys_map ff h₂)

@[simp] theorem map_disjoint_keys (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  disjoint (l₁.map f).keys (l₂.map f).keys ↔ disjoint l₁.keys l₂.keys :=
⟨disjoint_keys_of_map_disjoint_keys ff, map_disjoint_keys_of_disjoint_keys fi⟩

end map_disjoint

section decidable_eq_α₁_α₂
variables [decidable_eq α₁] [decidable_eq α₂]

section map
variables {s : sigma β₁} {l : list (sigma β₁)} {f : sigma β₁ → sigma β₂}

@[simp] theorem map_kerase (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  (l.kerase s.1).map f = (l.map f).kerase (f s).1 :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    by_cases h : (f hd).1 = (f s).1,
    { simp [h, fi h] },
    { simp [h, mt (@ff _ _) h, ih] } }
end

@[simp] theorem map_kinsert (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  (l.kinsert s).map f = (l.map f).kinsert (f s) :=
by simp [ff, fi]

end map

end decidable_eq_α₁_α₂

end α₁α₂α₃β₁β₂β₃

section αβ₁β₂
universes u v
variables {α : Type u} {β₁ β₂ : α → Type v}

section nodupkeys
variables {l : list (sigma β₁)}

theorem nodupkeys_map_id_iff (f : ∀ a, β₁ a → β₂ a) :
  (l.map (sigma.map id f)).nodupkeys ↔ l.nodupkeys :=
nodupkeys_map_iff (sigma.map_id_fst_functional f) (sigma.map_id_fst_injective f)

end nodupkeys

end αβ₁β₂

end list
