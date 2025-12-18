
\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Nominal where

open import MLTT.Spartan hiding (_+_)
open import MLTT.Bool
open import MLTT.List
open import Naturals.Addition
open import Naturals.Order
open import Quotient.Type
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

\end{code}

Before developing our nominal data type example we will develop some
well-foundedness results that will let us appease the termination
checker.

\begin{code}

module _ {A : 𝓤₀  ̇} (_⊰_ : A → A → 𝓤₀  ̇)
         where

 data Acc (x : A) : 𝓤₀  ̇ where
   acc : ((y : A) → y ⊰ x → Acc y) → Acc x

 prev-acc : (x : A)
          → Acc x
          → (y : A) → y ⊰ x → Acc y
 prev-acc x (acc a) = a
  
wfℕ : (x : ℕ) → Acc _<ℕ_ x
wfℕ zero = acc (λ y o → unique-from-𝟘 o)
wfℕ (succ x) = acc (I (wfℕ x))
 where
  I : Acc _<ℕ_ x → (y : ℕ) → y <ℕ succ x → Acc _<ℕ_ y
  I a y o = cases (λ - → prev-acc _<ℕ_ x a y -)
                  (λ - → transport (Acc _<ℕ_) (- ⁻¹) a)
                  (<-split y x o)

\end{code}

Now we begin by inductively defining our type of terms.

\begin{code}

module _ (Var : 𝓤₀  ̇) (d : is-discrete Var) where

 data Λ : 𝓤₀  ̇ where
  V : Var → Λ
  L : Var → Λ → Λ
  A : Λ → Λ → Λ

 help-decide : (x y : Var)
             → is-decidable (x ＝ y)
             → Bool
 help-decide x y (inl x＝y) = true
 help-decide x y (inr ¬x＝y) = false

 syntax help-decide x y d = x is[ d ] y

 swapVar : Var → Var → Var → Var
 swapVar x y z = if (x is[ d x y ] y) then y
                 else (if (x is[ d x y ] y) then x else z)

 swap : Var → Var → Λ → Λ
 swap x y (V z) = V (swapVar x y z)
 swap x y (L z t) = L (swapVar x y z) (swap x y t)
 swap x y (A t t') = A (swap x y t) (swap x y t')

 termSize : Λ → ℕ
 termSize (V x) = 1
 termSize (L x t) = (termSize t) + 1
 termSize (A t t') = (termSize t) + (termSize t')

 termSize->-0 : (t : Λ) → 0 <ℕ (termSize t)
 termSize->-0 (V x) = ⋆
 termSize->-0 (L x t) = ⋆
 termSize->-0 (A t s) = <-+ 0 (termSize t) (termSize s) (termSize->-0 t)

 swap-same-size : (x y : Var) (t : Λ)
                → termSize t ＝ termSize (swap x y t)
 swap-same-size x y (V z) = refl
 swap-same-size x y (L z t) = ap succ (swap-same-size x y t)
 swap-same-size x y (A t t') = I
  where
   I = termSize t + termSize t'
         ＝⟨ ap (_+ termSize t') (swap-same-size x y t) ⟩
       termSize (swap x y t) +  termSize t'
         ＝⟨ ap (termSize (swap x y t) +_) (swap-same-size x y t') ⟩
       termSize (swap x y t) + termSize (swap x y t')  ∎

\end{code}

In the absence of develop the full theory of constructive nominals sets we will
simply use a very niave notion of freshness.

\begin{code}

 var : Λ → List Var
 var (V x) = [ x ]
 var (L x t) = x ∷ (var t)
 var (A t t') = var t ++ var t'

 _fresh_ : Var → Λ → 𝓤₀  ̇
 a fresh t = ¬ member a (var t)

\end{code}

We need to show that the natural definition of α-equivalence terminates using
well-foundedness of ℕ relative to the size of terms in Λ.

We need some lemmas.

\begin{code}

 Lemma1 : (n m : ℕ) → (0 <ℕ m) → (n <ℕ m + n)
 Lemma1 n m o =
  transport (λ - → - <ℕ m + n) (zero-left-neutral n)
   (<-n-monotone-right 0 m n o)
 Lemma2 : (n m : ℕ) → (0 <ℕ m) → (n <ℕ n + m)
 Lemma2 n m o = transport (λ - → n <ℕ -) (addition-commutativity m n)
                 (Lemma1 n m o)

 α-equiv : (t t' : Λ)
         → Acc _<ℕ_ (termSize t)
         → Acc _<ℕ_ (termSize t')
         → 𝓤₀  ̇
 α-equiv (V x) (V y) _ _ = x ＝ y
 α-equiv (V x) (L y t') _ _ = 𝟘
 α-equiv (V x) (A t' s') _ _ = 𝟘
 α-equiv (L x t) (V y) _ _ = 𝟘
 α-equiv (L x t) (L y t') (acc a) (acc a')
  = (z : Var)
  → z ≠ x → z fresh t
  → z ≠ y → z fresh t'
  → α-equiv (swap x z t) (swap y z t')
     (a (termSize (swap x z t)) (I x z t))
     (a' (termSize (swap y z t')) (I y z t'))
  where
   I : (w z : Var) (s : Λ)
     → termSize (swap w z s) ≤ℕ termSize s
   I w z s = transport (λ - → - ≤ℕ termSize s) (swap-same-size w z s)
          (≤-refl (termSize s))
 α-equiv (L x t) (A t' s') _ _ = 𝟘
 α-equiv (A t s) (V y) _ _ = 𝟘
 α-equiv (A t s) (L y t') _ _ = 𝟘
 α-equiv (A t s) (A t' s') (acc a) (acc a')
  = α-equiv t t'
     (a (termSize t) (Lemma2 (termSize t) (termSize s) (termSize->-0 s)))
     (a' (termSize t') (Lemma2 (termSize t') (termSize s') (termSize->-0 s')))
  × α-equiv s s'
     (a (termSize s) (Lemma1 (termSize s) (termSize t) (termSize->-0 t)))
     (a' (termSize s') (Lemma1 (termSize s') (termSize t') (termSize->-0 t')))

 α-equiv-refl : (t : Λ)
              → (a : Acc _<ℕ_ (termSize t))
              → α-equiv t t a a
 α-equiv-refl (V x) a = refl
 α-equiv-refl (L x t) (acc a) z z≠x z∉t r r'
  = α-equiv-refl (swap x z t) (a (termSize (swap x z t))
     (transport (λ - → - ≤ℕ termSize t) (swap-same-size x z t)
      (≤-refl (termSize t))))
 α-equiv-refl (A t t') (acc a)
  = (α-equiv-refl t
     (a (termSize t) (Lemma2 (termSize t) (termSize t') (termSize->-0 t')))
    , α-equiv-refl t'
     (a (termSize t') (Lemma1 (termSize t') (termSize t) (termSize->-0 t))))

 α-equiv-sym : (t t' : Λ)
             → (a : Acc _<ℕ_ (termSize t))
             → (a' : Acc _<ℕ_ (termSize t'))
             → α-equiv t t' a a'
             → α-equiv t' t a' a
 α-equiv-sym t t' a a' x = {!!}

 α-equiv-tran : (t t' t'' : Λ)
              → (a : Acc _<ℕ_ (termSize t))
              → (a' : Acc _<ℕ_ (termSize t'))
              → (a'' : Acc _<ℕ_ (termSize t''))
              → α-equiv t t' a a'
              → α-equiv t' t'' a' a''
              → α-equiv t t'' a a''
 α-equiv-tran = {!!}

 _＝α_ : Λ → Λ → 𝓤₀  ̇
 t ＝α s = α-equiv t s (wfℕ (termSize t)) (wfℕ (termSize s))

\end{code}

Now we will quotient Λ by ＝α.

Note that to prove that ＝α is prop valued we would likely need to add an
assumption that Λ is a set (maybe not?). One could do this with records to
simulate higher inductive types. Showing ＝α is an equivalence relation is
reduced to asking if the terminating version is an equivalence relation.

\begin{code}

 ＝α-is-prop-valued : (t t' : Λ)
                    → is-prop (t ＝α t')
 ＝α-is-prop-valued = {!?proof?!}

 ＝α-is-equivalence-relation : is-equiv-relation _＝α_
 ＝α-is-equivalence-relation = (＝α-is-prop-valued , I , II , III)
  where
   I : reflexive _＝α_
   I t = α-equiv-refl t (wfℕ (termSize t))
   II : symmetric _＝α_
   II t t' = α-equiv-sym t t' (wfℕ (termSize t)) (wfℕ (termSize t'))
   III : transitive _＝α_
   III t t' t'' = α-equiv-tran t t' t''
                   (wfℕ (termSize t)) (wfℕ (termSize t')) (wfℕ (termSize t''))

 module _ (sq : general-set-quotients-exist (_⁺)) where

  open general-set-quotients-exist sq

  Λ/＝α : 𝓤₀ ⁺  ̇
  Λ/＝α = Λ / (_＝α_ , ＝α-is-equivalence-relation)

  Λ-inc : Λ → Λ/＝α
  Λ-inc = η/ (_＝α_ , ＝α-is-equivalence-relation)

  Λ/＝α-induction : {P : Λ/＝α → 𝓦 ̇ }
                  → ((x' : Λ/＝α) → is-prop (P x'))
                  → ((x : Λ) → P (Λ-inc x)) → (y : Λ/＝α) → P y
  Λ/＝α-induction = /-induction (_＝α_ , ＝α-is-equivalence-relation)

  Λ/＝α-universality : {Y : 𝓦 ̇ }
                     → is-set Y
                     → (f : Λ → Y)
                     → identifies-related-points
                        (_＝α_ , ＝α-is-equivalence-relation) f
                     → ∃! f̅ ꞉ (Λ/＝α → Y) , f̅ ∘ Λ-inc ∼ f
  Λ/＝α-universality = /-universality (_＝α_ , ＝α-is-equivalence-relation)

  Λ/＝α-recursion : {Y : 𝓦 ̇ }
                  → is-set Y
                  → (f : Λ → Y)
                  → identifies-related-points
                     (_＝α_ , ＝α-is-equivalence-relation) f
                  → Λ/＝α → Y
  Λ/＝α-recursion set-Y f i = ∃!-witness (Λ/＝α-universality set-Y f i)

\end{code}

TODO:
       Capture avoiding substitution?
       Nominal Abstract Data Types?

This may not be so easy...

\begin{code}

  capture-avoiding-substitution : (x : Var) (t : Λ)
                                → Λ/＝α → Λ/＝α
  capture-avoiding-substitution x t s
   = Λ/＝α-recursion (/-is-set (_＝α_ , ＝α-is-equivalence-relation))
      {!!} {!!} {!!}

\end{code}
