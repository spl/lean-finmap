import data.array.basic data.list.dict data.pnat

universes u v

/-- A hash map with an `n`-sized array of association list buckets, a hash
function, and proofs that the buckets have no duplicate keys and that every
bucket is correctly hashed. -/
structure hashmap {α : Type u} (β : α → Type v) :=
/- Number of buckets -/
(n : ℕ)
/- Hash function from key to bucket index -/
(hash : α → fin n)
/- Array of association list buckets -/
(buckets : array n (list (sigma β)))
/- Each bucket has no duplicate keys. -/
(nodupkeys : ∀ (i : fin n), (buckets.read i).nodupkeys)
/- Each bucket member has a hash equal to the bucket index. -/
(hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ buckets.read i → hash s.1 = i)

namespace hashmap
open list

/- default number of buckets -/

/-- Default number of buckets (8) -/
def default_n : ℕ :=
8

/-- Default positive number of buckets (default_n) -/
def default_pn : ℕ+ :=
⟨default_n, dec_trivial⟩

/- constructing empty hashmaps -/

/-- Construct an empty hashmap -/
def mk_empty {α} (β : α → Type v) (n : ℕ := default_n) (f : α → fin n) : hashmap β :=
⟨n, f, mk_array n [], λ i, nodupkeys_nil, λ _ _ h, by cases h⟩

/-- Create a hash function from a function `f : α → ℕ` using the result modulo
the number of buckets -/
def hash_mod {α} (n : ℕ+ := default_pn) (f : α → ℕ) (a : α) : fin n.val :=
⟨f a % n.val, nat.mod_lt _ n.property⟩

/-- Construct an empty nat-modulo hashmap -/
def mk_empty_mod {α} (β : α → Type v) (n : ℕ+ := default_pn) (f : α → ℕ) : hashmap β :=
mk_empty β n (hash_mod n f)

section αβ
variables {α : Type u} {β : α → Type v}

/- extensionality -/

theorem ext_core {m₁ m₂ : hashmap β} :
  m₁.n = m₂.n →
  m₁.hash == m₂.hash →
  m₁.buckets == m₂.buckets →
  m₁ = m₂ :=
begin
  cases m₁,
  cases m₂,
  dsimp,
  intros hn hh hb,
  congr,
  repeat { assumption },
  { apply proof_irrel_heq, substs hn hb, refl },
  { apply proof_irrel_heq, substs hn hh hb, refl }
end

theorem ext {m₁ m₂ : hashmap β}
  (hn : m₁.n = m₂.n)
  (hh : ∀ (a : α), (eq.rec_on hn (m₁.hash a) : fin m₂.n) = m₂.hash a)
  (hb : ∀ (i : fin m₁.n), m₁.buckets.read i = m₂.buckets.read (eq.rec_on hn i)) :
  m₁ = m₂ :=
ext_core hn
  (function.hfunext rfl (λ a₁ a₂ p, heq_of_eq_rec_left hn (by rw eq_of_heq p; apply hh)))
  (by cases m₁; cases m₂; dsimp at hn; subst hn; exact heq_of_eq (array.ext hb))

/- nodupkeys -/

theorem nodupkeys_of_mem_buckets {l : list (sigma β)} {m : hashmap β} (h : l ∈ m.buckets) :
  l.nodupkeys :=
let ⟨i, e⟩ := h in e ▸ m.nodupkeys i

/- empty -/

/-- A hashmap is empty if all buckets are empty -/
def empty (m : hashmap β) : Prop :=
∀ (i : fin m.n), m.buckets.read i = []

section empty
variables {m : hashmap β}

theorem empty_mk_empty (β) (n : ℕ) (f : α → fin n) : empty (mk_empty β n f) :=
λ _, rfl

theorem empty_mk_empty_mod (β) (n : ℕ+) (f : α → ℕ) : empty (mk_empty_mod β n f) :=
λ _, rfl

@[simp] theorem empty_zero (h : m.n = 0) : empty m :=
λ i, by cases (h.rec_on i : fin 0).is_lt

end empty

/- to_lists -/

/-- Bucket list of a hashmap -/
def to_lists (m : hashmap β) : list (list (sigma β)) :=
m.buckets.to_list

section to_lists
variables {m : hashmap β} {i : ℕ} {l : list (sigma β)}

@[simp] theorem mem_to_lists : l ∈ m.to_lists ↔ l ∈ m.buckets :=
array.mem_to_list _ _

theorem hash_idx_of_to_lists_enum (he : (i, l) ∈ m.to_lists.enum)
  {s : sigma β} (hl : s ∈ l) : (m.hash s.1).1 = i :=
have e₁ : ∃ p, m.buckets.read ⟨i, p⟩ = l := m.buckets.mem_to_list_enum.1 he,
have e₂ : ∃ p, m.hash s.1 = ⟨i, p⟩ := e₁.imp (λ _ h, m.hash_index $ h.symm ▸ hl),
let ⟨_, h⟩ := e₂ in by rw h

theorem disjoint_to_lists_map_keys (m : hashmap β) :
  pairwise disjoint (m.to_lists.map keys) :=
begin
  rw [←enum_map_snd m.to_lists, pairwise_map, pairwise_map],
  refine pairwise.imp_of_mem _ ((pairwise_map _).mp (nodup_enum_map_fst _)),
  rw prod.forall,
  intros n₁ l₁,
  rw prod.forall,
  intros n₂ l₂,
  intros me₁ me₂ e a mka₁ mka₂,
  apply e,
  cases exists_mem_of_mem_keys mka₁ with b₁ mab₁,
  cases exists_mem_of_mem_keys mka₂ with b₂ mab₂,
  rw [←hash_idx_of_to_lists_enum me₁ mab₁, ←hash_idx_of_to_lists_enum me₂ mab₂]
end

end to_lists

/- to_list -/

/-- Association list of a hashmap -/
def to_list (m : hashmap β) : list (sigma β) :=
m.to_lists.join

section to_list
variables {m : hashmap β} {i : ℕ} {l : list (sigma β)} {s : sigma β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem to_list_val : (mk n hash bs ndk @hash_index).to_list = bs.to_list.join :=
rfl

theorem empty_to_list : empty m ↔ m.to_list = [] :=
array.to_list_join_nil.symm

end val

theorem nodupkeys_to_list (m : hashmap β) : m.to_list.nodupkeys :=
nodupkeys_join.mpr $ and.intro
  (λ l ml, by simp [to_lists] at ml; cases ml with i e; induction e; exact m.nodupkeys i)
  m.disjoint_to_lists_map_keys

end to_list

/- foldl -/

/-- Left-fold of a hashmap -/
def foldl {γ : Type*} (m : hashmap β) (f : γ → sigma β → γ) (d : γ) : γ :=
m.buckets.foldl d (λ b r, b.foldl f r)

/- keys -/

/-- List of keys in a hashmap -/
def keys (m : hashmap β) : list α :=
m.to_list.keys

section keys
variables {m : hashmap β}

theorem nodup_keys (m : hashmap β) : m.keys.nodup :=
nodupkeys_iff.mpr m.nodupkeys_to_list

end keys

/- has_repr -/

instance [has_repr α] [∀ a, has_repr (β a)] : has_repr (hashmap β) :=
⟨λ m, "{" ++ string.intercalate ", " (m.to_list.map repr) ++ "}"⟩

section decidable_eq_α
variables [decidable_eq α]

/- lookup -/

/-- Look up a possible value in a hashmap given a key -/
def lookup (a : α) (m : hashmap β) : option (β a) :=
klookup a $ m.buckets.read $ m.hash a

section lookup
variables {a : α} {s : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem lookup_val :
  lookup a (mk n hash bs ndk @hash_index) = klookup a (bs.read (hash a)) :=
rfl

end val

@[simp] theorem lookup_empty (a : α) (h : empty m) : lookup a m = none :=
by simp [lookup, h (m.hash a)]

theorem lookup_iff_mem_buckets : s.2 ∈ m.lookup s.1 ↔ ∃ l, l ∈ m.buckets ∧ s ∈ l :=
calc s.2 ∈ m.lookup s.1 ↔ s ∈ m.buckets.read (m.hash s.1) :
    by cases m with _ h _ ndk; simp [ndk (h s.1)]
  ... ↔ m.buckets.read (m.hash s.1) ∈ m.buckets ∧ s ∈ m.buckets.read (m.hash s.1) :
    ⟨λ h, ⟨array.read_mem _ _, h⟩, λ ⟨_, h⟩, h⟩
  ... ↔ ∃ l, l ∈ m.buckets ∧ s ∈ l :
    ⟨λ ⟨p, q⟩, ⟨_, p, q⟩, λ ⟨_, ⟨i, p⟩, q⟩,
     by rw ←p at q; rw m.hash_index q; exact ⟨array.read_mem m.buckets i, q⟩⟩

end lookup

/- has_key -/

/-- Test for the presence of a key in a hashmap -/
def has_key (m : hashmap β) (a : α) : bool :=
(m.lookup a).is_some

section has_key
variables {a : α} {m : hashmap β}

theorem has_key_def : m.has_key a = (m.lookup a).is_some :=
rfl

-- TODO
-- theorem mem_keys_iff_has_key : ∀ (m : hashmap β), a ∈ m.keys ↔ m.has_key a

end has_key

/- mem -/

instance : has_mem (sigma β) (hashmap β) :=
⟨λ s m, s.2 ∈ m.lookup s.1⟩

section mem
variables {s : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_val : s ∈ mk n hash bs ndk @hash_index ↔ s ∈ bs.read (hash s.1) :=
mem_klookup_of_nodupkeys (ndk (hash s.1))

end val

theorem mem_def : s ∈ m ↔ s.2 ∈ m.lookup s.1 :=
iff.rfl

@[simp] theorem mem_to_list : s ∈ m.to_list ↔ s ∈ m :=
calc s ∈ m.to_list ↔ ∃ l, l ∈ m.to_lists ∧ s ∈ l : mem_join
  ... ↔ ∃ l, l ∈ m.buckets ∧ s ∈ l : by simp only [mem_to_lists]
  ... ↔ s ∈ m : lookup_iff_mem_buckets.symm

end mem

/- erase -/

/-- Erase a hashmap entry with the given key -/
def erase (m : hashmap β) (a : α) : hashmap β :=
{ buckets := m.buckets.modify (m.hash a) (kerase a),
  nodupkeys := λ i, by by_cases e : m.hash a = i; simp [e, m.nodupkeys i],
  hash_index := λ i s h, m.hash_index $
    by by_cases e : m.hash a = i; simp [e] at h; [exact mem_of_mem_kerase h, exact h],
  ..m }

section erase
variables {a : α} {s : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_erase_val :
  s ∈ (mk n hash bs ndk @hash_index).erase a ↔ s.1 ≠ a ∧ s ∈ bs.read (hash s.1) :=
begin
  unfold erase,
  by_cases h : hash s.1 = hash a,
  { simp [h, ndk (hash a)] },
  { simp [ne.symm h, mt (congr_arg _) h] }
end

end val

theorem lookup_erase (m : hashmap β) : (m.erase a).lookup a = none :=
by simp [erase, lookup, m.nodupkeys (m.hash a)]

@[simp] theorem mem_erase : s ∈ m.erase a ↔ s.1 ≠ a ∧ s ∈ m :=
by cases m; simp

end erase

/- insert -/

/-- Insert a new entry in a hashmap -/
protected def insert (s : sigma β) (m : hashmap β) : hashmap β :=
{ buckets := m.buckets.modify (m.hash s.1) (kinsert s),
  nodupkeys := λ i, by by_cases e : m.hash s.1 = i; simp [e, m.nodupkeys i],
  hash_index := λ i s' h, begin
    by_cases e : m.hash s.1 = i; simp [e] at h,
    { cases h with h h,
      { induction h, exact e },
      { exact m.hash_index (mem_of_mem_kerase h) } },
    { exact m.hash_index h }
  end,
  ..m }

instance : has_insert (sigma β) (hashmap β) :=
⟨hashmap.insert⟩

section insert
variables {s t : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_index : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_insert_val :
  s ∈ insert t (mk n hash bs ndk @hash_index) ↔ s = t ∨ s.1 ≠ t.1 ∧ s ∈ bs.read (hash s.1) :=
begin
  unfold insert has_insert.insert hashmap.insert,
  by_cases h : hash s.1 = hash t.1,
  { simp [h, ndk (hash t.1)] },
  { have h' : s.1 ≠ t.1 := mt (congr_arg _) h, simp [ne.symm h, h', mt sigma.eq_fst h'] }
end

end val

@[simp] theorem mem_insert : s ∈ insert t m ↔ s = t ∨ s.1 ≠ t.1 ∧ s ∈ m :=
by cases m; simp

end insert

/-- Insert a list of entries in a hashmap -/
def insert_list (l : list (sigma β)) (m : hashmap β) : hashmap β :=
l.foldl (flip insert) m

/-- Construct a hashmap from an association list -/
def of_list (n : ℕ := default_n) (f : α → fin n) (l : list (sigma β)) : hashmap β :=
insert_list l $ mk_empty _ n f

/-- Construct a nat-modulo hashmap from an association list -/
def of_list_mod (n : ℕ+ := default_pn) (f : α → ℕ) (l : list (sigma β)) : hashmap β :=
insert_list l $ mk_empty_mod _ n f

end decidable_eq_α

end αβ

end hashmap
