import data.array.basic data.list.dict data.pnat

universes u v

/-- A hash map with an `n`-sized array of association list buckets, a hash
function, and a proof that every bucket is correctly hashed. -/
structure hashmap {α : Type u} (β : α → Type v) :=
/- Number of buckets -/
(n : ℕ)
/- Hash function -/
(hash : α → fin n)
/- Array of association list buckets -/
(buckets : array n (list (sigma β)))
/- Each bucket has no duplicate keys. -/
(nodupkeys : ∀ (i : fin n), (buckets.read i).nodupkeys)
/- Each member of a bucket has a key hash equal to the index of that bucket. -/
(hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ buckets.read i → hash s.1 = i)

/-- Default number of buckets (8) -/
def hashmap.default_n : ℕ :=
8

/-- Default positive number of buckets (default_n) -/
def hashmap.default_pn : ℕ+ :=
⟨hashmap.default_n, dec_trivial⟩

variables {α : Type u} {β : α → Type v}

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a hash function -/
def mk_hashmap (β) (n : ℕ := hashmap.default_n) (f : α → fin n) : hashmap β :=
⟨n, f, mk_array n [], λ i, list.nodupkeys_nil, λ _ _ h, by cases h⟩

/-- Create a hash function from a function `f : α → ℕ` using the result modulo
the number of buckets -/
def hashmap.mk_mod_hash (n : ℕ+ := hashmap.default_pn) (f : α → ℕ) (a : α) : fin n.val :=
⟨f a % n.val, nat.mod_lt _ n.property⟩

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a modulo hash function -/
def mk_hashmap_mod (β) (n : ℕ+ := hashmap.default_pn) (f : α → ℕ) : hashmap β :=
mk_hashmap β n (hashmap.mk_mod_hash n f)

namespace hashmap
open list

def empty (m : hashmap β) : Prop :=
∀ (i : fin m.n), m.buckets.read i = []

section empty
variables {m : hashmap β}

theorem empty_mk (β) (n : ℕ) (f : α → fin n) : empty (mk_hashmap β n f) :=
λ _, rfl

theorem empty_mk_mod (β) (n : ℕ+) (f : α → ℕ) : empty (mk_hashmap_mod β n f) :=
λ _, rfl

@[simp] theorem empty_zero (h : m.n = 0) : empty m :=
λ i, by cases (h.rec_on i : fin 0).is_lt

end empty

def to_list (m : hashmap β) : list (sigma β) :=
m.buckets.to_list.join

section to_list
variables {m : hashmap β} {i : ℕ} {l : list (sigma β)}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem to_list_val : (mk n hash bs ndk @hash_idx).to_list = bs.to_list.join :=
rfl

end val

-- TODO
-- theorem empty_to_list : empty m ↔ m.to_list = [] :=

theorem nodupkeys_of_mem_buckets (h : l ∈ m.buckets) : l.nodupkeys :=
let ⟨i, e⟩ := h in e ▸ m.nodupkeys i

theorem hash_idx_of_enum (he : (i, l) ∈ m.buckets.to_list.enum)
  {s : sigma β} (hl : s ∈ l) : (m.hash s.1).1 = i :=
have e₁ : ∃ p, m.buckets.read ⟨i, p⟩ = l := m.buckets.mem_to_list_enum.1 he,
have e₂ : ∃ p, m.hash s.1 = ⟨i, p⟩ := e₁.imp (λ _ h, m.hash_idx $ h.symm ▸ hl),
let ⟨_, h⟩ := e₂ in by rw h

theorem disjoint_bucket_keys (m : hashmap β) :
  pairwise disjoint (m.buckets.to_list.map keys) :=
begin
  rw [←enum_map_snd m.buckets.to_list, pairwise_map, pairwise_map],
  refine pairwise.imp_of_mem _ ((pairwise_map _).mp (nodup_enum_map_fst _)),
  rw prod.forall,
  intros n₁ l₁,
  rw prod.forall,
  intros n₂ l₂,
  intros me₁ me₂ e a mka₁ mka₂,
  apply e,
  cases exists_mem_of_mem_keys mka₁ with b₁ mab₁,
  cases exists_mem_of_mem_keys mka₂ with b₂ mab₂,
  rw [←hash_idx_of_enum me₁ mab₁, ←hash_idx_of_enum me₂ mab₂]
end

theorem nodupkeys_to_list (m : hashmap β) : m.to_list.nodupkeys :=
nodupkeys_join.mpr $ and.intro
  (λ l ml, by simp at ml; cases ml with i e; induction e; exact m.nodupkeys i)
  m.disjoint_bucket_keys

end to_list

def foldl {γ : Type*} (m : hashmap β) (f : γ → sigma β → γ) (d : γ) : γ :=
m.buckets.foldl d (λ b r, b.foldl f r)

def keys (m : hashmap β) : list α :=
m.to_list.keys

section keys
variables {m : hashmap β}

theorem nodup_keys (m : hashmap β) : m.keys.nodup :=
nodupkeys_iff.mpr m.nodupkeys_to_list

end keys

instance [has_repr α] [∀ a, has_repr (β a)] : has_repr (hashmap β) :=
⟨λ m, "{" ++ string.intercalate ", " (m.to_list.map repr) ++ "}"⟩

section decidable_eq_α
variables [decidable_eq α]

def lookup (a : α) (m : hashmap β) : option (β a) :=
klookup a $ m.buckets.read $ m.hash a

section lookup
variables {a : α} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem lookup_val :
  lookup a (mk n hash bs ndk @hash_idx) = klookup a (bs.read (hash a)) :=
rfl

end val

@[simp] theorem lookup_empty (a : α) (h : empty m) : lookup a m = none :=
by simp [lookup, h (m.hash a)]

end lookup

def has_key (m : hashmap β) (a : α) : bool :=
(m.lookup a).is_some

section has_key
variables {a : α} {b : β a} {m : hashmap β}

theorem lookup_has_key : (m.lookup a).is_some = m.has_key a :=
rfl

-- TODO
-- theorem mem_keys_iff_has_key : ∀ (m : hashmap β), a ∈ m.keys ↔ m.has_key a

end has_key

instance : has_mem (sigma β) (hashmap β) :=
⟨λ s m, s.2 ∈ m.lookup s.1⟩

section mem
variables {a : α} {b : β a} {s : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_val : s ∈ mk n hash bs ndk @hash_idx ↔ s ∈ bs.read (hash s.1) :=
mem_klookup_of_nodupkeys (ndk (hash s.1))

end val

theorem mem_lookup : s ∈ m ↔ s.2 ∈ m.lookup s.1 :=
iff.rfl

end mem

def erase (m : hashmap β) (a : α) : hashmap β :=
{ buckets := m.buckets.modify (m.hash a) (kerase a),
  nodupkeys := λ i,
    by by_cases e : m.hash a = i; simp [e, m.nodupkeys i],
  hash_idx := λ i s h, m.hash_idx $
    by by_cases e : m.hash a = i; simp [e] at h;
       [exact mem_of_mem_kerase h, exact h],
  ..m }

section erase
variables {a : α} {s : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_erase_val :
  s ∈ (mk n hash bs ndk @hash_idx).erase a ↔ s.1 ≠ a ∧ s ∈ bs.read (hash s.1) :=
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

protected def insert (s : sigma β) (m : hashmap β) : hashmap β :=
{ buckets := m.buckets.modify (m.hash s.1) (kinsert s),
  nodupkeys := λ i,
    by by_cases e : m.hash s.1 = i; simp [e, m.nodupkeys i],
  hash_idx := λ i s' h,
  begin
    by_cases e : m.hash s.1 = i; simp [e] at h,
    { cases h with h h,
      { induction h, exact e },
      { exact m.hash_idx (mem_of_mem_kerase h) } },
    { exact m.hash_idx h }
  end,
  ..m }

instance : has_insert (sigma β) (hashmap β) :=
⟨hashmap.insert⟩

section insert
variables {s t : sigma β} {m : hashmap β}

section val
variables {n : ℕ} {hash : α → fin n} {bs : array n (list (sigma β))}
  {ndk : ∀ (i : fin n), (bs.read i).nodupkeys}
  {hash_idx : ∀ {i : fin n} {s : sigma β}, s ∈ bs.read i → hash s.1 = i}

@[simp] theorem mem_insert_val :
  s ∈ insert t (mk n hash bs ndk @hash_idx) ↔ s = t ∨ s.1 ≠ t.1 ∧ s ∈ bs.read (hash s.1) :=
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

def insert_list (l : list (sigma β)) (m : hashmap β) : hashmap β :=
l.foldl (flip insert) m

def of_list (n : ℕ := default_n) (f : α → fin n) (l : list (sigma β)) : hashmap β :=
insert_list l $ mk_hashmap _ n f

def of_list_mod (n : ℕ+ := default_pn) (f : α → ℕ) (l : list (sigma β)) : hashmap β :=
insert_list l $ mk_hashmap_mod _ n f

end decidable_eq_α

end hashmap
