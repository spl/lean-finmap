namespace quot
universes u₁ u₂ v
variables {α : Sort u₁} {β : Sort u₂}
variables {ra : α → α → Prop} {rb : β → β → Prop} {φ : quot ra → quot rb → Sort v}

local notation `⟦`:max a `⟧` := quot.mk _ a

protected def hrec_on₂ (qa : quot ra) (qb : quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
  (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → f a₁ b == f a₂ b)
  (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → f a b₁ == f a b₂) : φ qa qb :=
quot.hrec_on qa (λ a, quot.hrec_on qb (f a) (λ b₁ b₂ pb, cb pb)) $ λ a₁ a₂ pa,
  quot.induction_on qb $ λ b,
    calc @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)
          == f a₁ b                                     : by simp
      ... == f a₂ b                                     : ca pa
      ... == @quot.hrec_on _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) : by simp

end quot

namespace quotient
universes u₁ u₂ v
variables {α : Sort u₁} {β : Sort u₂}
variables [sa : setoid α] [sb : setoid β]
variables {φ : quotient sa → quotient sb → Sort v}

protected def hrec_on₂ (qa : quotient sa) (qb : quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
  (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ == f a₂ b₂) : φ qa qb :=
quot.hrec_on₂ qa qb f
  (λ _ _ _ p, c _ _ _ _ p (setoid.refl _))
  (λ _ _ _ p, c _ _ _ _ (setoid.refl _) p)

end quotient
