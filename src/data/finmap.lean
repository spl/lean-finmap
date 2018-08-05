import data.finset data.multiset.dict

local attribute [-simp] sigma.forall sigma.exists

open multiset

universes u v

structure finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
(val : multiset (sigma β))
(nodup_keys : val.nodup_keys)

namespace finmap
variables {α : Type u} {β : α → Type v}

section val
variables {f g : finmap α β}

theorem eq_of_veq : ∀ {f g : finmap α β}, f.val = g.val → f = g
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; exact h

@[simp] theorem val_inj : f.val = g.val ↔ f = g :=
⟨eq_of_veq, congr_arg _⟩

end val

instance has_decidable_eq [decidable_eq α] [∀ a, decidable_eq (β a)] :
  decidable_eq (finmap α β)
| f g := decidable_of_iff _ val_inj

/- membership -/

section mem

instance : has_mem (sigma β) (finmap α β) :=
⟨λ s f, s ∈ f.val⟩

variables {s : sigma β} {m : multiset (sigma β)} {f : finmap α β}

theorem mem_def : s ∈ f ↔ s ∈ f.val :=
iff.rfl

@[simp] theorem mem_mk {nd : m.nodup_keys} :
  @has_mem.mem _ (finmap α β) _ s (finmap.mk m nd) ↔ s ∈ m :=
iff.rfl

instance decidable_mem [decidable_eq α] [∀ a, decidable_eq (β a)] (s : sigma β) (f : finmap α β) :
  decidable (s ∈ f) :=
multiset.decidable_mem _ _

end mem

/- set coercion -/

section set

def to_set (s : finmap α β) : set (sigma β) := {x | x ∈ s}

instance : has_lift (finmap α β) (set (sigma β)) := ⟨to_set⟩

variables {s : sigma β} {f : finmap α β}

@[simp] lemma mem_coe : s ∈ (↑f : set (sigma β)) ↔ s ∈ f :=
iff.rfl

end set

/- extensionality -/

section ext
variables {f g : finmap α β}

theorem ext : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
val_inj.symm.trans $
  nodup_ext (nodup_of_nodup_keys f.nodup_keys) (nodup_of_nodup_keys g.nodup_keys)

@[extensionality]
theorem ext' : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
ext.mpr

end ext

/- subset -/

section subset

instance : has_subset (finmap α β) :=
⟨λ f g, ∀ ⦃s : sigma β⦄, s ∈ f → s ∈ g⟩

variables {s : sigma β} {f g h : finmap α β}

theorem subset_def : f ⊆ g ↔ f.val ⊆ g.val :=
iff.rfl

@[simp] theorem subset.refl (f : finmap α β) : f ⊆ f :=
subset.refl _

theorem subset.trans : f ⊆ g → g ⊆ h → f ⊆ h :=
subset.trans

theorem mem_of_subset : f ⊆ g → s ∈ f → s ∈ g :=
mem_of_subset

theorem subset.antisymm (H₁ : f ⊆ g) (H₂ : g ⊆ f) : f = g :=
ext' $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff : f ⊆ g ↔ ∀ ⦃x⦄, x ∈ f → x ∈ g :=
iff.rfl

@[simp] theorem coe_subset : (↑f : set (sigma β)) ⊆ ↑g ↔ f ⊆ g :=
iff.rfl

@[simp] theorem val_le_iff : f.val ≤ g.val ↔ f ⊆ g :=
le_iff_subset (nodup_of_nodup_keys f.nodup_keys)

instance : has_ssubset (finmap α β) :=
⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance : partial_order (finmap α β) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _ _,
  le_antisymm := @subset.antisymm _ _ }

@[simp] theorem le_iff_subset : f ≤ g ↔ f ⊆ g := iff.rfl
@[simp] theorem lt_iff_ssubset : f < g ↔ f ⊂ g := iff.rfl

@[simp] theorem val_lt_iff : f.val < g.val ↔ f ⊂ g :=
and_congr val_le_iff $ not_congr val_le_iff

end subset

/- empty -/

section empty

protected def empty : finmap α β :=
⟨0, nodup_keys_zero⟩

instance : has_emptyc (finmap α β) :=
⟨finmap.empty⟩

instance : inhabited (finmap α β) :=
⟨∅⟩

@[simp] theorem empty_val : (∅ : finmap α β).val = 0 :=
rfl

@[simp] theorem not_mem_empty (s : sigma β) : s ∉ (∅ : finmap α β) :=
id

@[simp] theorem ne_empty_of_mem {s : sigma β} {f : finmap α β} (h : s ∈ f) : f ≠ ∅
| e := not_mem_empty s $ e ▸ h

@[simp] theorem empty_subset (f : finmap α β) : ∅ ⊆ f :=
zero_subset _

theorem eq_empty_of_forall_not_mem {f : finmap α β} (H : ∀x, x ∉ f) : f = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

@[simp] theorem val_eq_zero {f : finmap α β} : f.val = 0 ↔ f = ∅ :=
@val_inj _ _ f ∅

theorem subset_empty {f : finmap α β} : f ⊆ ∅ ↔ f = ∅ :=
subset_zero.trans val_eq_zero

theorem exists_mem_of_ne_empty {f : finmap α β} (h : f ≠ ∅) : ∃ s : sigma β, s ∈ f :=
exists_mem_of_ne_zero (mt val_eq_zero.mp h)

@[simp] lemma coe_empty : ↑(∅ : finmap α β) = (∅ : set (sigma β)) :=
by simp [set.ext_iff]

end empty

/- singleton -/

/-- `singleton s` is the set `{s}` containing `s` and nothing else. -/
def singleton (s : sigma β) : finmap α β :=
⟨⟦[s]⟧, nodup_keys_singleton s⟩

local prefix `ι`:90 := singleton

@[simp] theorem singleton_val (s : sigma β) : (ι s).val = s :: 0 := rfl

@[simp] theorem mem_singleton {a b : sigma β} : b ∈ ι a ↔ b = a :=
by simp [singleton]

theorem not_mem_singleton {a b : sigma β} : a ∉ ι b ↔ a ≠ b := by simp

theorem mem_singleton_self (a : sigma β) : a ∈ ι a := by simp

theorem singleton_inj {a b : sigma β} : ι a = ι b ↔ a = b :=
⟨λ h, mem_singleton.mp (h ▸ mem_singleton_self _), congr_arg _⟩

@[simp] theorem singleton_ne_empty (a : sigma β) : ι a ≠ ∅ := ne_empty_of_mem (mem_singleton_self _)

@[simp] lemma coe_singleton (a : sigma β) : ↑(ι a) = ({a} : set (sigma β)) :=
by simp [set.ext_iff]

/- keys -/

section keys

def keys (f : finmap α β) : finset α :=
⟨f.val.keys, nodup_keys_iff.mpr f.nodup_keys⟩

@[simp] theorem keys_val (f : finmap α β) : f.keys.val = f.val.keys :=
rfl

@[simp] theorem keys_empty : keys (∅ : finmap α β) = ∅ :=
rfl

@[simp] theorem mem_insert_keys [decidable_eq α] {a₁ a₂ : α} {f : finmap α β} :
  a₁ ∈ insert a₂ (keys f) ↔ a₁ = a₂ ∨ a₁ ∈ keys f :=
by simp

end keys

/- erase -/

section erase
variables [decidable_eq α]

def erase (f : finmap α β) (a : α) : finmap α β :=
⟨kerase a f.nodup_keys, nodup_keys_kerase a f.nodup_keys⟩

@[simp] theorem erase_val (f : finmap α β) (a : α) : (f.erase a).val = kerase a f.nodup_keys :=
rfl

@[simp] theorem mem_erase {s : sigma β} {a : α} {f : finmap α β} :
  s ∈ f.erase a ↔ s.1 ≠ a ∧ s ∈ f :=
mem_kerase f.nodup_keys

theorem not_mem_erase (a : α) (b : β a) (f : finmap α β) : sigma.mk a b ∉ f.erase a :=
by simp

@[simp] theorem mem_keys_erase {a₁ a₂ : α} {f : finmap α β} :
  a₁ ∈ keys (f.erase a₂) ↔ a₁ ≠ a₂ ∧ a₁ ∈ keys f :=
by simp [keys]

@[simp] theorem erase_empty (a : α) : erase ∅ a = (∅ : finmap α β) :=
rfl

theorem ne_of_mem_erase {s : sigma β} {a : α} {f : finmap α β} : s ∈ f.erase a → s.1 ≠ a :=
by simp {contextual := tt}

theorem erase_subset_erase (a : α) {f g : finmap α β} (h : f ⊆ g) : f.erase a ⊆ g.erase a :=
val_le_iff.mp $ kerase_le_kerase _ (val_le_iff.mpr h) _ _

theorem erase_subset (a : α) {f : finmap α β} : f.erase a ⊆ f :=
kerase_subset a f.nodup_keys

end erase

/- insert -/

section insert
variables [decidable_eq α]

instance : has_insert (sigma β) (finmap α β) :=
⟨λ s f, ⟨kinsert s f.nodup_keys, nodup_keys_kinsert s f.nodup_keys⟩⟩

@[simp] theorem insert_val (s : sigma β) (f : finmap α β) :
  (insert s f).val = kinsert s f.nodup_keys :=
rfl

@[simp] theorem insert_empty (s : sigma β) : insert s (∅ : finmap α β) = {s} :=
rfl

@[simp] theorem mem_insert (s₁ s₂ : sigma β) (f : finmap α β) :
  s₁ ∈ insert s₂ f ↔ s₁ = s₂ ∨ s₁ ∈ f.erase s₂.1 :=
mem_kinsert f.nodup_keys

variables {a : α} {s : sigma β} {f : finmap α β}

@[simp] theorem mem_keys_insert : a ∈ keys (insert s f) ↔ a = s.1 ∨ a ∈ keys f :=
by simp [keys]

@[simp] theorem insert_keys : keys (insert s f) = insert s.1 (keys f) :=
finset.ext' $ by simp

end insert

/- lookup -/

section lookup
variables [decidable_eq α]

def lookup (a : α) (f : finmap α β) : option (β a) :=
klookup a f.nodup_keys

theorem lookup_empty (a : α) : lookup a (∅ : finmap α β) = none :=
rfl

end lookup

/- replace -/

section replace
variables [decidable_eq α]

def replace (s : sigma β) (f : finmap α β) : finmap α β :=
⟨kreplace s f.nodup_keys, nodup_keys_kreplace s f.nodup_keys⟩

@[simp] theorem replace_empty (s : sigma β) : replace s ∅ = ∅ :=
rfl

end replace

/- union -/

section union
variables [decidable_eq α]

protected def union (f : finmap α β) (g : finmap α β) : finmap α β :=
⟨kunion f.nodup_keys g.nodup_keys, nodup_keys_kunion f.nodup_keys g.nodup_keys⟩

instance : has_union (finmap α β) :=
⟨finmap.union⟩

@[simp] theorem union_val {f g : finmap α β} : (f ∪ g).val = kunion f.nodup_keys g.nodup_keys :=
rfl

@[simp] theorem mem_union [decidable_eq α] {s : sigma β}
  {f g : finmap α β} (dk : disjoint f.keys g.keys) : s ∈ f ∪ g ↔ s ∈ f ∨ s ∈ g :=
mem_kunion f.nodup_keys g.nodup_keys (finset.disjoint_val.mp dk)

variables {a : α} {f g : finmap α β}

@[simp] theorem mem_keys_union : a ∈ keys (f ∪ g) ↔ a ∈ keys f ∨ a ∈ keys g :=
mem_keys_kunion f.nodup_keys g.nodup_keys

@[simp] theorem union_keys : (f ∪ g).keys = f.keys ∪ g.keys :=
finset.ext' $ by simp

end union

/- map -/

section map
variables {α₁ α₂ α₃ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}

def map (p : β₁ s↪ β₂) (f : finmap α₁ β₁) : finmap α₂ β₂ :=
⟨f.val.map p, nodup_keys_map p.fst_inj f.nodup_keys⟩

@[simp] theorem map_val (p : β₁ s↪ β₂) (f : finmap α₁ β₁) : (f.map p).val = f.val.map p :=
rfl

@[simp] theorem map_empty (p : β₁ s↪ β₂) : map p ∅ = ∅ :=
rfl

variables {p : β₁ s↪ β₂} {q : β₂ s↪ β₃} {f g : finmap α₁ β₁} {s₁ : sigma β₁} {s₂ : sigma β₂}

@[simp] theorem mem_map : s₂ ∈ f.map p ↔ ∃ s₁ ∈ f, p s₁ = s₂ :=
by simp [mem_def]

@[simp] theorem mem_map_of_mem (h : s₁ ∈ f) : p s₁ ∈ f.map p :=
mem_map.mpr ⟨_, h, rfl⟩

theorem map_refl : f.map (sigma.embedding.refl _) = f :=
ext' $ by simp [sigma.embedding.refl]

theorem map_map : (f.map p).map q = f.map (p.trans q) :=
eq_of_veq $ by simp [erase_dup_map_erase_dup_eq]

theorem map_subset_map (h : f ⊆ g) : f.map p ⊆ g.map p :=
by simp [subset_def, map_subset_map h]

variables {s : sigma β₁}

theorem mem_keys_map (pf : sigma.fst_functional p) :
  s.1 ∈ f.keys → (p s).1 ∈ (f.map p).keys :=
mem_keys_map pf

theorem mem_keys_of_mem_keys_map : (p s).1 ∈ (f.map p).keys → s.1 ∈ f.keys :=
mem_keys_of_mem_keys_map p.fst_inj

theorem mem_keys_map_iff (pf : sigma.fst_functional p) :
  (p s).1 ∈ (f.map p).keys ↔ s.1 ∈ f.keys :=
⟨mem_keys_of_mem_keys_map, mem_keys_map pf⟩

theorem map_disjoint_keys [decidable_eq α₁] [decidable_eq α₂] (pf : sigma.fst_functional p) :
  disjoint (f.map p).keys (g.map p).keys ↔ disjoint f.keys g.keys :=
by simp only [finset.disjoint_val]; exact multiset.map_disjoint_keys pf p.fst_inj

theorem map_union [decidable_eq α₁] [decidable_eq α₂] (pf : sigma.fst_functional p)
  (dk : disjoint f.keys g.keys) : (f ∪ g).map p = f.map p ∪ g.map p :=
ext' $ by simp [dk, map_disjoint_keys pf, or_and_distrib_right, exists_or_distrib]

end map

section map_snd
variables {β₁ β₂ : α → Type v} {s : sigma β₁} {f : finmap α β₁}

def map_snd (p : ∀ a, β₁ a → β₂ a) : finmap α β₁ → finmap α β₂ :=
map (sigma.embedding.mk₂ p)

@[simp] theorem map_snd_val (p : ∀ (a : α), β₁ a → β₂ a) (f : finmap α β₁) :
  (f.map_snd p).val = f.val.map_snd p :=
rfl

@[simp] theorem mem_keys_map_snd (p : ∀ a, β₁ a → β₂ a) :
  s.1 ∈ (f.map_snd p).keys ↔ s.1 ∈ f.keys :=
by simp [keys]

-- Is this useful?
@[simp] theorem mem_keys_map_snd_inh [inhabited (∀ a, β₁ a)] {a} (p : ∀ a, β₁ a → β₂ a) :
  a ∈ (f.map_snd p).keys ↔ a ∈ f.keys :=
by simp [keys]

-- Is this useful?
@[simp] theorem map_snd_keys [inhabited (∀ a, β₁ a)] (p : ∀ a, β₁ a → β₂ a) :
  (f.map_snd p).keys = f.keys :=
finset.ext' $ λ _, mem_keys_map_snd_inh p

end map_snd

end finmap
