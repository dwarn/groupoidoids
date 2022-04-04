{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to prop-rec)

-- a universe polymorphic version of compEquiv
compEquiv' : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → A ≃ B → B ≃ C → A ≃ C
compEquiv' f g .fst = g .fst ∘ f .fst
compEquiv' {A = A} {C = C} f g .snd .equiv-proof c = contr
  where
  contractG = g .snd .equiv-proof c .snd

  secFiller : (a : A) (p : g .fst (f .fst a) ≡ c) → _ {- square in A -}
  secFiller a p = compPath-filler (cong (invEq f ∘ fst) (contractG (_ , p))) (retEq f a)

  contr : isContr (fiber (g .fst ∘ f .fst) c)
  contr .fst .fst = invEq f (invEq g c)
  contr .fst .snd = cong (g .fst) (secEq f (invEq g c)) ∙ secEq g c
  contr .snd (a , p) i .fst = secFiller a p i1 i
  contr .snd (a , p) i .snd j =
    hcomp
      (λ k → λ
        { (i = i1) → fSquare k
        ; (j = i0) → g .fst (f .fst (secFiller a p k i))
        ; (j = i1) → contractG (_  , p) i .snd k
        })
      (g .fst (secEq f (contractG (_ , p) i .fst) j))
    where
    fSquare : I → C
    fSquare k =
      hcomp
        (λ l → λ
          { (j = i0) → g .fst (f .fst (retEq f a k))
          ; (j = i1) → p (k ∧ l)
          ; (k = i0) → g .fst (secEq f (f .fst a) j)
          ; (k = i1) → p (j ∧ l)
          })
        (g .fst (f .snd .equiv-proof (f .fst a) .snd (a , refl) k .snd j))

_∘ₑ_ = compEquiv'

-- Egbert Rijke's 'fundamental theorem of identity types'. it is a slight generalisation of what's
-- stated in the Cubical Agda library at the moment, but the proof is the same.
fundamentalTheoremOfId' : {ℓ ℓ' : Level} {A : Type ℓ} (x : A) (Eqx : A → Type ℓ') →
                          Eqx x → isProp (Σ A Eqx) → (y : A) → (x ≡ y) ≃ Eqx y
fst (fundamentalTheoremOfId' x Eqx Rfl isprop y) p = subst Eqx p Rfl
snd (fundamentalTheoremOfId' x Eqx Rfl isprop y) = fiberEquiv ((x ≡_)) Eqx (λ _ p → subst Eqx p Rfl)
  (isEquivFromIsContr _ (isContrSingl x) (inhProp→isContr (x , Rfl) isprop)) y

-- to prove ∀ b → P b it suffices to prove ∀ a → P (f a) for some surjection f : A ↠ B
surjection-forall : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} (P : B → Type ℓ'') (isprop : (b : B) → isProp (P b))
                    {f : A → B} → isSurjection f → ((a : A) → P (f a)) → (b : B) → P b
surjection-forall P isprop fsurj Pa b = prop-rec (isprop b) (λ (a , p) → subst _ p (Pa a)) (fsurj b)
