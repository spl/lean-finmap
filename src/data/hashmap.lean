import data.finmap
import data.pnat
import data.array.basic data.array.lemmas

universes u v

/-- A hash map with an `n`-sized array of association list buckets, a hash
function, and a proof that every bucket is correctly hashed. -/
structure hashmap (α : Type u) [decidable_eq α] (β : α → Type v) :=
/- Number of buckets (positive) -/
(n : ℕ+)
/- Hash function -/
(hash : α → fin n.val)
/- Array of finite map buckets -/
(buckets : array n.val (finmap α β))
/- Each bucket `i` contains members such that that hash of each member is `i`. -/
(hash_mem : ∀ {i a}, a ∈ (buckets.read i).keys → hash a = i)

/-- Default number of buckets (8) -/
def hashmap.default_n : ℕ+ :=
8

variables {α : Type u} [decidable_eq α] {β : α → Type v}

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a hash function -/
def mk_hashmap (n : ℕ+ := hashmap.default_n) (f : α → fin n.val) : hashmap α β :=
⟨n, f, mk_array n.val ∅, λ _ _ h, by cases h⟩

/-- Create a hash function from a function `f : α → ℕ` using the result modulo
the number of buckets -/
def hashmap.mk_mod_hash (n : ℕ+ := hashmap.default_n) (f : α → ℕ) (a : α) : fin n.val :=
⟨f a % n.val, nat.mod_lt _ n.property⟩

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a modulo hash function -/
def mk_mod_hashmap (n : ℕ+ := hashmap.default_n) (f : α → ℕ) : hashmap α β :=
mk_hashmap n (hashmap.mk_mod_hash n f)

-- theorem array_read_val {n : ℕ} (a : array n (finmap α β)) : ((a.read i).val)

/-- Erase a key-value pair from the map -/
def erase (m : hashmap α β) (a : α) : hashmap α β :=
/-
match m with ⟨hash_fn, size, n, buckets, v⟩ :=
  if hc : contains_aux a (buckets.read hash_fn a) then
  { hash_fn  := hash_fn,
    size     := size - 1,
    nbuckets := n,
    buckets  := buckets.modify hash_fn a (erase_aux a),
    is_valid := v.erase _ a hc }
  else m
end
-/
match m with ⟨n, hash, buckets, hash_mem⟩ :=
{ n := n,
  hash := hash,
  buckets := buckets.modify (hash a) (λ f, f.erase a),
  hash_mem := λ i b p,
    have h : a ∈ (buckets.read i).keys → hash a = i := @hash_mem i a,
    begin
      simp at *,
    end }
end
