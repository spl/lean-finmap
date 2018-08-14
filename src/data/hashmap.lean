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
(nodup_keys : ∀ (i : fin n), (buckets.read i).nodup_keys)
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
⟨n, f, mk_array n [], λ i, list.nodup_keys_nil, λ _ _ h, by cases h⟩

/-- Create a hash function from a function `f : α → ℕ` using the result modulo
the number of buckets -/
def hashmap.mk_mod_hash (n : ℕ+ := hashmap.default_pn) (f : α → ℕ) (a : α) : fin n.val :=
⟨f a % n.val, nat.mod_lt _ n.property⟩

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a modulo hash function -/
def mk_mod_hashmap (β) (n : ℕ+ := hashmap.default_pn) (f : α → ℕ) : hashmap β :=
mk_hashmap β n (hashmap.mk_mod_hash n f)

namespace hashmap
open list

def empty (m : hashmap β) : Prop :=
∀ (i : fin m.n), m.buckets.read i = []

theorem empty_mk (β) (n : ℕ) (f : α → fin n) : empty (mk_hashmap β n f) :=
λ _, rfl

theorem empty_mk_mod (β) (n : ℕ+) (f : α → ℕ) : empty (mk_mod_hashmap β n f) :=
λ _, rfl

theorem empty_zero (m : hashmap β) (h : m.n = 0) : empty m :=
λ i, by cases (h.rec_on i : fin 0).is_lt

def lookup [decidable_eq α] (a : α) (m : hashmap β) : option (β a) :=
klookup a $ m.buckets.read $ m.hash a

instance [decidable_eq α] : has_mem α (hashmap β) :=
⟨λ a m, (m.lookup a).is_some⟩

def foldl {γ : Type*} (m : hashmap β) (f : γ → sigma β → γ) (d : γ) : γ :=
m.buckets.foldl d (λ b r, b.foldl f r)

def to_list (m : hashmap β) : list (sigma β) :=
m.buckets.to_list.join

def keys (m : hashmap β) : list α :=
m.to_list.keys

def erase [decidable_eq α] (m : hashmap β) (a : α) : hashmap β :=
{ buckets := m.buckets.modify (m.hash a) (kerase a),
  nodup_keys := λ i,
    by by_cases e : m.hash a = i; simp [e, m.nodup_keys i],
  hash_idx := λ i s h, m.hash_idx $
    by by_cases e : m.hash a = i; simp [e] at h;
       [exact mem_of_mem_kerase h, exact h],
  ..m }

def insert [decidable_eq α] (s : sigma β) (m : hashmap β) : hashmap β :=
{ buckets := m.buckets.modify (m.hash s.1) (kinsert s),
  nodup_keys := λ i,
    by by_cases e : m.hash s.1 = i; simp [e, m.nodup_keys i],
  hash_idx := λ i s' h,
  begin
    by_cases e : m.hash s.1 = i; simp [e] at h,
    { cases h with h h,
      { induction h, exact e },
      { exact m.hash_idx (mem_of_mem_kerase h) } },
    { exact m.hash_idx h }
  end,
  ..m }

end hashmap
