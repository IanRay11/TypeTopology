Martin Escardo, 15th November 2023.

Lesser Limited Principle of Omniscience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Taboos.LLPO where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Spartan
open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import Naturals.Properties
open import Naturals.Parity
open import Taboos.WLPO
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.FunExt

T : (ℕ → 𝟚) → 𝓤₀ ̇
T α = Σ n ꞉ ℕ , α n ＝ ₁

to-T-＝ : {α : ℕ → 𝟚}
          {n n' : ℕ}
        → n ＝ n'
        → {e : α n ＝ ₁} {e' : α n' ＝ ₁}
        → (n , e) ＝[ T α ] (n' , e')
to-T-＝ p = to-subtype-＝ (λ - → 𝟚-is-set) p

index-uniqueness : (α : ℕ → 𝟚)
                 → is-prop (T α)
                 → {n n' : ℕ} → α n ＝ ₁ → α n' ＝ ₁ → n ＝ n'
index-uniqueness α i {n} {n'} e e' = ap pr₁ (i (n , e) (n' , e'))

index-uniqueness-converse : (α : ℕ → 𝟚)
                          → ({n n' : ℕ} → α n ＝ ₁ → α n' ＝ ₁ → n ＝ n')
                          → is-prop (T α)
index-uniqueness-converse α ϕ (n , e) (n' , e') = to-T-＝ (ϕ e e')

untruncated-LLPO : 𝓤₀ ̇
untruncated-LLPO = (α : ℕ → 𝟚)
                 → is-prop (T α)
                 → ((n : ℕ) → α ( double n) ＝ ₀)
                 + ((n : ℕ) → α (sdouble n) ＝ ₀)

untruncated-LLPO' : 𝓤₀ ̇
untruncated-LLPO' = (β γ : ℕ → 𝟚)
                  → is-prop (T β)
                  → is-prop (T γ)
                  → ¬ (T β × T γ) → ¬ T β + ¬ T γ

¬T : (ℕ → 𝟚) → 𝓤₀ ̇
¬T α = (n : ℕ) → α n ＝ ₀

not-T-gives-¬T : {α : ℕ → 𝟚} → ¬ (T α) → ¬T α
not-T-gives-¬T {α} ϕ n = different-from-₁-equal-₀ (λ (e : α n ＝ ₁) → ϕ (n , e))

¬T-gives-not-T : {α : ℕ → 𝟚} → ¬T α → ¬ (T α)
¬T-gives-not-T {α} ψ (n , e) = zero-is-not-one ((ψ n)⁻¹ ∙ e)

unprime : untruncated-LLPO' → untruncated-LLPO
unprime llpo' α h = III
 where
  β γ : ℕ → 𝟚
  β n = α ( double n)
  γ n = α (sdouble n)

  i : is-prop (T β)
  i (n , e) (n' , e') = to-T-＝ (double-lc (index-uniqueness α h e e'))

  j : is-prop (T γ)
  j (n , e) (n' , e') = to-T-＝ (sdouble-lc (index-uniqueness α h e e'))

  I : ¬ (T β × T γ)
  I ((k , e) , (k' , e')) = even-not-odd' k k' (index-uniqueness α h e e')

  II : ¬ T β + ¬ T γ
  II = llpo' β γ i j I

  III : ((n : ℕ) → α (double n) ＝ ₀) + ((n : ℕ) → α (sdouble n) ＝ ₀)
  III = +functor not-T-gives-¬T not-T-gives-¬T II

prime : untruncated-LLPO → untruncated-LLPO'
prime llpo β γ i j ν = III
 where
  f : (n : ℕ) → is-even' n + is-odd' n → 𝟚
  f n (inl (k , _)) = β k
  f n (inr (k , _)) = γ k

  α : ℕ → 𝟚
  α n = f n (even-or-odd' n)

  α-β : (n : ℕ) → α (double n) ＝ β n
  α-β n = a (even-or-odd' (double n))
   where
    a : (d : is-even' (double n) + is-odd' (double n)) → f (double n) d ＝ β n
    a (inl (k , e)) = ap β (double-lc e)
    a (inr (k , e)) = 𝟘-elim (even-not-odd' n k (e ⁻¹))

  α-γ : (n : ℕ) → α (sdouble n) ＝ γ n
  α-γ n = a (even-or-odd' (sdouble n))
   where
    a : (d : is-even' (sdouble n) + is-odd' (sdouble n)) → f (sdouble n) d ＝ γ n
    a (inl (k , e)) = 𝟘-elim (even-not-odd' k n e)
    a (inr (k , e)) = ap γ (sdouble-lc e)

  I : is-prop (T α)
  I (n , e) (n' , e') = a (even-or-odd' n) (even-or-odd' n')
   where
    a : (d  : is-even' n  + is-odd' n )
        (d' : is-even' n' + is-odd' n')
      → (n , e) ＝[ T α ] (n' , e')
    a (inl (k , refl)) (inl (k' , refl)) =
     to-T-＝ (ap  double (index-uniqueness β i ((α-β k)⁻¹ ∙ e) ((α-β k') ⁻¹ ∙ e')))
    a (inl (k , refl)) (inr (k' , refl)) =
     𝟘-elim (ν ((k  , ((α-β k )⁻¹ ∙ e )) , (k' , (( α-γ k')⁻¹ ∙ e'))))
    a (inr (k , refl)) (inl (k' , refl)) =
     𝟘-elim (ν ((k' , ((α-β k')⁻¹ ∙ e')) , (k  , (( α-γ k )⁻¹ ∙ e ))))
    a (inr (k , refl)) (inr (k' , refl)) =
     to-T-＝ (ap sdouble (index-uniqueness γ j ((α-γ k)⁻¹ ∙ e) ((α-γ k') ⁻¹ ∙ e')))

  II : ((n : ℕ) → α (double n) ＝ ₀) + ((n : ℕ) → α (sdouble n) ＝ ₀)
  II = llpo α I

  III : ¬ T β + ¬ T γ
  III = +functor
         (λ (ψ : (n : ℕ) → α ( double n) ＝ ₀)
               → ¬T-gives-not-T (λ n → (α-β n)⁻¹ ∙ ψ n))
         (λ (ψ : (n : ℕ) → α (sdouble n) ＝ ₀)
               → ¬T-gives-not-T (λ n → (α-γ n)⁻¹ ∙ ψ n))
         II

{-
untruncated-LLPO-gives-WLPO : funext₀ → untruncated-LLPO' → WLPO
untruncated-LLPO-gives-WLPO fe llpo = wlpo
 where
  ℕ∞' = Σ α ꞉ (ℕ → 𝟚) , is-prop (T α)

  H : ℕ∞' → 𝓤₀ ̇
  H (α , i) = T α

  ℕ∞'-to-ℕ→𝟚 : ℕ∞' → (ℕ → 𝟚)
  ℕ∞'-to-ℕ→𝟚 = pr₁

  ℕ∞'-to-ℕ→𝟚-prop : (u : ℕ∞') → is-prop (T (ℕ∞'-to-ℕ→𝟚 u))
  ℕ∞'-to-ℕ→𝟚-prop = pr₂

  ∞' : ℕ∞'
  ∞' = (λ _ → ₀) , (λ (n , e) (n' , e') → 𝟘-elim (zero-is-not-one e))

  ϕ : (u v : ℕ∞') → ¬ H u + ¬ H v → 𝟚
  ϕ u v (inl l) = ₀
  ϕ u v (inr r) = ₁

  l₀ : (u : ℕ∞') → ¬ H u + ¬ H ∞'
  l₀ u = llpo (ℕ∞'-to-ℕ→𝟚 u)      (ℕ∞'-to-ℕ→𝟚 ∞')
              (ℕ∞'-to-ℕ→𝟚-prop u) (ℕ∞'-to-ℕ→𝟚-prop ∞')
              (λ (_ , (_ , e)) → zero-is-not-one e)

  l₁ : (u : ℕ∞') → ¬ H ∞' + ¬ H u
  l₁ u = llpo (ℕ∞'-to-ℕ→𝟚 ∞')      (ℕ∞'-to-ℕ→𝟚 u)
              (ℕ∞'-to-ℕ→𝟚-prop ∞') (ℕ∞'-to-ℕ→𝟚-prop u)
              (λ ((_ , e) , _) → zero-is-not-one e)

  l-property : l₁ ∞' ＝ l₀ ∞'
  l-property = ap (llpo (ℕ∞'-to-ℕ→𝟚 ∞')      (ℕ∞'-to-ℕ→𝟚 ∞')
                  (ℕ∞'-to-ℕ→𝟚-prop ∞') (ℕ∞'-to-ℕ→𝟚-prop ∞'))
                  (dfunext fe (λ (((_ , e) , _) : T (λ _ → ₀) × T (λ _ → ₀))
                                                → 𝟘-elim (zero-is-not-one e)))

  f₀ f₁ : ℕ∞' → 𝟚
  f₀ u = ϕ u  ∞' (l₀ u)
  f₁ u = ϕ ∞' u  (l₁ u)

  f-property : ¬ ((f₀ ∞' ＝ ₁) × (f₁ ∞' ＝ ₀))
  f-property (e₀ , e₁) =
   zero-is-not-one
    (₀               ＝⟨ e₁ ⁻¹ ⟩
     f₁ ∞'           ＝⟨ refl ⟩
     ϕ ∞' ∞' (l₁ ∞') ＝⟨ ap (ϕ ∞' ∞') l-property ⟩
     ϕ ∞' ∞' (l₀ ∞') ＝⟨ refl ⟩
     f₀ ∞'           ＝⟨ e₀ ⟩
     ₁               ∎ )

  ϕ₀-property : (u : ℕ∞') (d : ¬ H u + ¬ H ∞') → H u → ϕ u ∞' d ＝ ₁
  ϕ₀-property u (inl l) h = 𝟘-elim (l h)
  ϕ₀-property u (inr _) h = refl

  ϕ₁-property : (u : ℕ∞') (d : ¬ H ∞' + ¬ H u) → H u → ϕ ∞' u d ＝ ₀
  ϕ₁-property u (inl _) h = refl
  ϕ₁-property u (inr r) h = 𝟘-elim (r h)

  f₀-property : (u : ℕ∞') → H u → f₀ u ＝ ₁
  f₀-property u = ϕ₀-property u (l₀ u)

  f₁-property : (u : ℕ∞') → H u → f₁ u ＝ ₀
  f₁-property u = ϕ₁-property u (l₁ u)

  wlpo₀ : f₀ ∞' ＝ ₀ → WLPO
  wlpo₀ = {!because f₀ is discontinuous!}

  wlpo₁ : f₁ ∞' ＝ ₁ → WLPO
  wlpo₁ = {!because f₀ is discontinuous!}

  wlpo : WLPO
  wlpo = Cases (𝟚-possibilities (f₀ ∞'))
          (λ (e₀ : f₀ ∞' ＝ ₀) → wlpo₀ e₀)
          (λ (e₀ : f₀ ∞' ＝ ₁)
                 → Cases (𝟚-possibilities (f₁ ∞'))
                    (λ (e₁ : f₁ ∞' ＝ ₀) → 𝟘-elim (f-property (e₀ , e₁)))
                    (λ (e₁ : f₁ ∞' ＝ ₁) → wlpo₁ e₁))

WLPO-gives-untruncated-LLPO : WLPO-traditional → untruncated-LLPO
WLPO-gives-untruncated-LLPO = {!!}
-}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 LLPO : 𝓤₀ ̇
 LLPO = (α : ℕ → 𝟚)
      → is-prop (Σ n ꞉ ℕ , α n ＝ ₁)
      → ((n : ℕ) → α (double n) ＝ ₀) ∨ ((n : ℕ) → α (sdouble n) ＝ ₀)

 untruncated-LLPO-gives-LLPO : untruncated-LLPO → LLPO
 untruncated-LLPO-gives-LLPO ullpo α i = ∣ ullpo α i ∣

 ℕ-∞-LLPO : 𝓤₀ ̇
 ℕ-∞-LLPO = (u v : ℕ∞) → ¬ (is-finite u × is-finite v) → (u ＝ ∞) ∨ (v ＝ ∞)

\end{code}

LLPO doesn't imply WLPO (find reference with a counter-model).
