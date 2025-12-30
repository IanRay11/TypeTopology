Ian Ray

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
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

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

module _ (Var : 𝓤₀  ̇) (𝓮 : ℕ ≃ Var) (fe : Fun-Ext) where

 disc-var : is-discrete Var
 disc-var = equiv-to-discrete 𝓮 ℕ-is-discrete

 var-set : is-set Var
 var-set = discrete-types-are-sets disc-var

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
 swapVar x y z = if (z is[ disc-var z x ] x) then y
                 else (if (z is[ disc-var z y ] y) then x else z)

 syntax swapVar x y z = ⁅ x ∣ y ⁆ z

 swapVar-equivariant : {x y z w u v : Var}
                     → swapVar x z u ＝ v
                     → swapVar x w u ＝ v
 swapVar-equivariant {x} {y} {z} {w} {u} {v} refl = {!!}

 swap : Var → Var → Λ → Λ
 swap x y (V z) = V (⁅ x ∣ y ⁆ z)
 swap x y (L z t) = L (⁅ x ∣ y ⁆ z) (swap x y t)
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

 swap-no-bigger : (w z : Var) (s : Λ)
                → termSize (swap w z s) ≤ℕ termSize s
 swap-no-bigger w z s = transport (λ - → - ≤ℕ termSize s) (swap-same-size w z s)
                         (≤-refl (termSize s))

\end{code}

In the absence of develop the full theory of constructive nominals sets we will
simply use a very niave notion of freshness.

\begin{code}

 var : Λ → List Var
 var (V x) = [ x ]
 var (L x t) = x ∷ (var t)
 var (A t t') = var t ++ var t'

 _fresh'_ : Var → Λ → 𝓤₀  ̇
 a fresh' t = ¬ member a (var t)

 _fresh_ : Var → Λ → 𝓤₀  ̇
 a fresh t = (x : Var) → member x (var t) → a ≠ x

 list-max : List ℕ → ℕ
 list-max [] = 0
 list-max (x ∷ xs) = max x (list-max xs)

 less-than-list-max : (n : ℕ) (xs : List ℕ)
                    → member n xs
                    → n ≤ℕ (list-max xs)
 less-than-list-max n (n ∷ xs) in-head = max-≤-upper-bound n (list-max xs)
 less-than-list-max n (x ∷ xs) (in-tail m) =
  ≤-trans n (list-max xs) (max x (list-max xs)) I
   (max-≤-upper-bound' (list-max xs) x)
  where
   I : n ≤ℕ list-max xs
   I = less-than-list-max n xs m

 choose-a-fresh-name : (t : Λ)
                     → Σ x ꞉ Var , x fresh t
 choose-a-fresh-name t = (⌜ 𝓮 ⌝ II , IV)
  where
   I : List ℕ
   I = map ⌜ 𝓮 ⌝⁻¹ (var t)
   II : ℕ
   II = (list-max I) + 1
   III' : (n : ℕ) → member n I → n <ℕ II
   III' n m = less-than-list-max n I m
   III : (n : ℕ) → member n I → II ≠ n
   III n m p = not-less-than-itself n (transport (λ - → n <ℕ -) p (III' n m))
   IV : (⌜ 𝓮 ⌝ II) fresh t
   IV x x-in-t p = III (⌜ 𝓮 ⌝⁻¹ x) (member-map ⌜ 𝓮 ⌝⁻¹ x (var t) x-in-t)
                    (inverses-are-retractions' 𝓮 II ⁻¹ ∙ ap ⌜ 𝓮 ⌝⁻¹ p)

 fresh-name : (t : Λ)
            → Var
 fresh-name t = pr₁ (choose-a-fresh-name t)

 freshness : (t : Λ)
           → (fresh-name t) fresh t
 freshness t = pr₂ (choose-a-fresh-name t)

\end{code}

We need to show that the natural definition of α-equivalence terminates using
well-foundedness of ℕ relative to the size of terms in Λ.

We need some lemmas about order on ℕ.

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
     (a (termSize (swap x z t)) (swap-no-bigger x z t))
     (a' (termSize (swap y z t')) (swap-no-bigger y z t'))
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

\end{code}

We need to show that α-equiv is equivariant (unchanged underswapping)

\begin{code}

 α-equiv-equivariant : (x y z w : Var) (t t' : Λ)
                     → (a : (y : ℕ) → y <ℕ (succ (termSize t))
                         → Acc (_<ℕ_) y)
                     → (a' : (y : ℕ) → y <ℕ (succ (termSize t'))
                         → Acc (_<ℕ_) y)
                     → α-equiv (swap x z t) (swap y z t')
                        (a (termSize (swap x z t)) (swap-no-bigger x z t))
                        (a' (termSize (swap y z t')) (swap-no-bigger y z t'))
                     → α-equiv (swap x w t) (swap y w t')
                        (a (termSize (swap x w t)) (swap-no-bigger x w t))
                        (a' (termSize (swap y w t')) (swap-no-bigger y w t'))
 α-equiv-equivariant x y z w (V u) (V v) a a' α-v
  = {!!}
 α-equiv-equivariant x y z w (L u t) (L v t') a a' α-v = {!!}
 α-equiv-equivariant x y z w (A t s) (A t' s') a a' α-v = {!!}

\end{code}

We begin the laborous task of showing that α-equiv is indeed an equivalence
relation.

\begin{code}

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
 α-equiv-sym (V x) (V y) _ _ = _⁻¹ 
 α-equiv-sym (V x) (L y t') _ _ = id
 α-equiv-sym (V x) (A t' s') _ _ = id
 α-equiv-sym (L x t) (V y) _ _ = id
 α-equiv-sym (L x t) (L y t') (acc a) (acc a') f z z≠y z♯t' z≠x z♯t
  = α-equiv-sym (swap x z t) (swap y z t')
     (a (termSize (swap x z t)) (swap-no-bigger x z t))
     (a' (termSize (swap  y z t')) (swap-no-bigger y z t'))
     (f z z≠x z♯t z≠y z♯t')
 α-equiv-sym (L x t) (A t' s') _ _ = id
 α-equiv-sym (A t s) (V y) _ _ = id
 α-equiv-sym (A t s) (L y t') _ _ = id
 α-equiv-sym (A t s) (A t' s') (acc a) (acc a') (f , g)
  = (I , II)
  where
   I : α-equiv t' t
         (a' (termSize t')
          (Lemma2 (termSize t') (termSize s') (termSize->-0 s')))
         (a (termSize t)
          (Lemma2 (termSize t) (termSize s) (termSize->-0 s)))
   I = α-equiv-sym t t'
       (a (termSize t) (Lemma2 (termSize t) (termSize s) (termSize->-0 s)))
       (a' (termSize t') (Lemma2 (termSize t') (termSize s') (termSize->-0 s')))
       f
   II : α-equiv s' s
          (a' (termSize s')
           (Lemma1 (termSize s') (termSize t') (termSize->-0 t')))
          (a (termSize s)
           (Lemma1 (termSize s) (termSize t) (termSize->-0 t)))
   II = α-equiv-sym s s'
       (a (termSize s) (Lemma1 (termSize s) (termSize t) (termSize->-0 t)))
       (a' (termSize s') (Lemma1 (termSize s') (termSize t') (termSize->-0 t')))
       g

\end{code}

Before showing transitivity we need some lemmas about lists.

\begin{code}

 lemma : (x : Var) (l l' : List Var)
       → member x l
       → member x (l ++ l')
 lemma x (y ∷ l) l' in-head = in-head
 lemma x (y ∷ l) l' (in-tail m) = in-tail (lemma x l l' m)

 lemma' : (x : Var) (l l' : List Var)
        → member x l'
        → member x (l ++ l')
 lemma' x [] (y' ∷ l') in-head = in-head
 lemma' x (y ∷ l) (y' ∷ l') in-head = in-tail (lemma' x l (x ∷ l') in-head)
 lemma' x [] (y' ∷ l') (in-tail m) = in-tail m
 lemma' x (y ∷ l) (y' ∷ l') (in-tail m)
  = in-tail (lemma' x l (y' ∷ l') (in-tail m))

 lemma'' : (x : Var) (l l' l'' : List Var)
         → member x l'
         → member x (l ++ l' ++ l'')
 lemma'' x l l' l'' m = lemma' x l (l' ++ l'') I
  where
   I : member x (l' ++ l'')
   I = lemma x l' l'' m

 α-equiv-trans : (t t' t'' : Λ)
               → (a : Acc _<ℕ_ (termSize t))
               → (a' : Acc _<ℕ_ (termSize t'))
               → (a'' : Acc _<ℕ_ (termSize t''))
               → α-equiv t t' a a'
               → α-equiv t' t'' a' a''
               → α-equiv t t'' a a''
 α-equiv-trans (V x) (V y) (V z) _ _ _ = _∙_
 α-equiv-trans (L x t) (L y t') (L z t'') (acc a) (acc a') (acc a'')
  f g w w≠x w♯t w≠z w♯t'' 
  = α-equiv-equivariant x z v w t t'' a a'' I
  where
   v : Var
   v = fresh-name (A (V x) (A (V y) (A (V z) (A t (A t' t'')))))
   v-fresh : v fresh (A (V x) (A (V y) (A (V z) (A t (A t' t'')))))
   v-fresh = freshness (A (V x) (A (V y) (A (V z) (A t (A t' t'')))))
   I = α-equiv-trans (swap x v t) (swap y v t') (swap z v t'')
        (a (termSize (swap x v t)) (swap-no-bigger x v t))
        (a' (termSize (swap y v t')) (swap-no-bigger y v t'))
        (a'' (termSize (swap z v t'')) (swap-no-bigger z v t''))
        (f v (v-fresh x in-head)
             (λ - m → v-fresh - (in-tail (in-tail (in-tail
              (lemma - (var t) (var t' ++ var t'') m)))))
             (v-fresh y (in-tail in-head))
             (λ - m → v-fresh - (in-tail (in-tail (in-tail
              (lemma'' - (var t) (var t') (var t'') m))))))
        (g v (v-fresh y (in-tail in-head))
             (λ - m → v-fresh - (in-tail (in-tail (in-tail
              (lemma'' - (var t) (var t') (var t'') m)))))
             (v-fresh z (in-tail (in-tail in-head)))
             (λ - m → v-fresh - (in-tail (in-tail (in-tail
              (transport (member -) (++-assoc (var t) (var t') (var t''))
               (lemma' - (var t ++ var t') (var t'') m)))))))
 α-equiv-trans (A t s) (A t' s') (A t'' s'') (acc a) (acc a') (acc a'')
  (p , p') (q , q')
  = (α-equiv-trans t t' t''
      (a (termSize t) (Lemma2 (termSize t) (termSize s) (termSize->-0 s)))
      (a' (termSize t') (Lemma2 (termSize t') (termSize s') (termSize->-0 s')))
      (a'' (termSize t'')
       (Lemma2 (termSize t'') (termSize s'') (termSize->-0 s''))) p q
   , α-equiv-trans s s' s''
      (a (termSize s) (Lemma1 (termSize s) (termSize t) (termSize->-0 t)))
      (a' (termSize s') (Lemma1 (termSize s') (termSize t') (termSize->-0 t')))
      (a'' (termSize s'')
       (Lemma1 (termSize s'') (termSize t'') (termSize->-0 t''))) p' q')

\end{code}

We need function extensionality to show α-equiv is prop valued.

\begin{code}

 α-equiv-prop-valued : (t t' : Λ)
                     → (a : Acc _<ℕ_ (termSize t))
                     → (a' : Acc _<ℕ_ (termSize t'))
                     → is-prop (α-equiv t t' a a')
 α-equiv-prop-valued (V x) (V y) _ _ = var-set
 α-equiv-prop-valued (V x) (L y t') _ _ = 𝟘-is-prop
 α-equiv-prop-valued (V x) (A t' s') _ _ = 𝟘-is-prop
 α-equiv-prop-valued (L x t) (V y) _ _ = 𝟘-is-prop
 α-equiv-prop-valued (L x t) (L y t') (acc a) (acc a')
  = Π-is-prop fe
     (λ z → Π-is-prop fe
      (λ _ → Π-is-prop fe
       (λ _ → Π-is-prop fe
        (λ _ → Π-is-prop fe
         (λ _ → α-equiv-prop-valued (swap x z t) (swap y z t')
                 (a (termSize (swap x z t)) (swap-no-bigger x z t))
                 (a' (termSize (swap y z t')) (swap-no-bigger y z t')))))))
 α-equiv-prop-valued (L x t) (A t' s') _ _ = 𝟘-is-prop
 α-equiv-prop-valued (A t s) (V y) _ _ = 𝟘-is-prop
 α-equiv-prop-valued (A t s) (L y t') _ _ = 𝟘-is-prop
 α-equiv-prop-valued (A t s) (A t' s') (acc a) (acc a')
  = ×-is-prop (α-equiv-prop-valued t t'
     (a (termSize t) (Lemma2 (termSize t) (termSize s) (termSize->-0 s)))
     (a' (termSize t') (Lemma2 (termSize t') (termSize s') (termSize->-0 s'))))
    (α-equiv-prop-valued s s'
     (a (termSize s) (Lemma1 (termSize s) (termSize t) (termSize->-0 t)))
     (a' (termSize s') (Lemma1 (termSize s') (termSize t') (termSize->-0 t'))))

 _＝α_ : Λ → Λ → 𝓤₀  ̇
 t ＝α s = α-equiv t s (wfℕ (termSize t)) (wfℕ (termSize s))

\end{code}

TODO. Finish α-equiv-equivariance.

\begin{code}

 ＝α-is-prop-valued : (t t' : Λ)
                    → is-prop (t ＝α t')
 ＝α-is-prop-valued t t'
  = α-equiv-prop-valued t t' (wfℕ (termSize t)) (wfℕ (termSize t'))

 ＝α-is-equivalence-relation : is-equiv-relation _＝α_
 ＝α-is-equivalence-relation = (＝α-is-prop-valued , I , II , III)
  where
   I : reflexive _＝α_
   I t = α-equiv-refl t (wfℕ (termSize t))
   II : symmetric _＝α_
   II t t' = α-equiv-sym t t' (wfℕ (termSize t)) (wfℕ (termSize t'))
   III : transitive _＝α_
   III t t' t'' = α-equiv-trans t t' t''
                   (wfℕ (termSize t)) (wfℕ (termSize t')) (wfℕ (termSize t''))

\end{code}

Now we will quotient Λ by ＝α.

\begin{code}

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
