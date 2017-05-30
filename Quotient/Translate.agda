module Quotient.Translate where

open import Quotient.Basic
open import Quotient.Function
open import Quotient.Setoid
open import Quotient.ISetoid
open import Quotient.ISetoid.Algebraic

_[_↔_] : ∀ {c d p q} {S S′ : Setoid c p} → S ↔ S′ → ISetoid (Of S) d q → ISetoid (Of S′) d q → Set (c ⊔ d ⊔ p ⊔ q)
eq [ T ↔ T′ ] = ∀ x x′ → < _ , _ , eq >[ x ≈ x′ ] → T at x ↔ T′ at x′


liftIso : ∀ {c d p q} {S S′ : Setoid c p} {T : ISetoid (Of S) d q} {T′ : ISetoid (Of S′) d q} (e1 : S ↔ S′) → e1 [ T ↔ T′ ] → Σ S T ↔ Σ S′ T′
liftIso {S = S} {S′} {T} {T′} e1 e2 = record
  { iso₁ = record
    { _∙_ = λ x → iso₁ e1 ∙ fst x , iso₁ (e2 _ _ (refl S′)) ∙ snd x
    ; cong = λ eq → cong (iso₁ e1) (fst eq) , {!!}
      -- (begin[ T′ ]
      --   iso₁ (e2 _ _ (refl S′)) ∙ snd _
      -- ≈⟨ ? ⟩
      --   iso₁ (e2 _ _ (refl S′)) ∙ snd _
      -- ∎)
    }
  ; iso₂ = record
    { _∙_ = λ x → iso₂ e1 ∙ fst x , iso₂ (e2 _ _ (symHet S′ S (sym (Iso _ _) e1) _ _ (refl S))) ∙ snd x
    ; cong = {!!}
    }
  ; inverse₁ = {!!}
  ; inverse₂ = {!!}
  }
