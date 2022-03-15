{-# OPTIONS --cubical --no-import-sorts --sized-types --guardedness #-}

open import Size
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma.Properties

record XSu : Type₂ where
  field
    X : Type₀
    S : Type₁
    u : S → X → Type₁

open XSu

module _ (G : XSu) where
  ptd : X G → Type₁
  ptd x = Σ[ P ∈ _ ] u G P x

  module _ (P : (x : X G) → ptd x) where
    alpha : S G → Type₁
    alpha Q = (x : X G) (q : u G Q x) → P x ≡ (Q , q)

    beta : Type₁
    beta = Σ _ alpha
  
    nxt : XSu
    X nxt = X G
    S nxt = beta
    u nxt Q = u G (fst Q) 

record gpd (G : XSu) : Type₁ where
  coinductive
  field
    P : (x : X G) → ptd G x
    τ : gpd (nxt G P)

open gpd

record pshf {G : XSu} (g : gpd G) (Q : S G) : Type₁ where
    coinductive
    field
      μ : alpha G (P g) Q
      τ' : pshf (τ g) (Q , μ)

open pshf

repr' : {G : XSu} (g : gpd G) (x : X G) (Q : S G) (p : Q ≡ fst (P g x)) → pshf g Q
μ (repr' g x Q p) = let ((_ , homo) , pt) = P (τ g) x in
                    subst⁻ (alpha _ (P g)) (p ∙ cong fst (homo x pt)) homo
τ' (repr' g x Q p) = let ((_ , homo) , pt) = P (τ g) x in
                     repr' (τ g) x _ (ΣPathP (p ∙ cong fst (homo x pt) , symP (transport⁻-filler _ _)))

repr : {G : XSu} (g : gpd G) (x : X G) → pshf g (fst (P g x))
repr g x = repr' g x _ refl

record pshf-bisimP {G : I → XSu} (g : (i : I) → gpd (G i)) (Q : (i : I) → S (G i))
  (f₀ : pshf (g i0) (Q i0)) (f₁ : pshf (g i1) (Q i1)) : Type₁ where
  coinductive
  field
    μ-path : PathP (λ i → alpha (G i) (P (g i)) (Q i)) (μ f₀) (μ f₁)
    τ-bisim : pshf-bisimP (λ i → τ (g i)) (λ i → (Q i , μ-path i)) (τ' f₀) (τ' f₁)

open pshf-bisimP

pathP-of-bisim : {G : I → XSu} {g : (i : I) → gpd (G i)} {Q : (i : I) → S (G i)}
                 {f₀ : pshf (g i0) (Q i0)} {f₁ : pshf (g i1) (Q i1)} (h : pshf-bisimP g Q f₀ f₁)
                 → PathP (λ i → pshf (g i) (Q i)) f₀ f₁
μ (pathP-of-bisim h i) = μ-path h i
τ' (pathP-of-bisim h i) = pathP-of-bisim (τ-bisim h) i

foo : {G : XSu} {g : gpd G} {x : X G} {Q₀ Q₁ : S G} (f₀ : pshf g Q₀) (f₂ : pshf g Q₁) (q₀ : u G Q₀ x) (q₁ : u G Q₁ x) →
         (Q₀ , q₀) ≡ (Q₁ , q₁)
foo f₀ f₁ q₀ q₁ = sym (μ f₀ _ q₀) ∙ μ f₁ _ q₁

ptd-pshf-bisimP : {G : XSu} (g : gpd G) (x : X G)
                    (Q₀ Q₁ : S G) (f₀ : pshf g Q₀) (f₁ : pshf g Q₁) (q₀ : u G Q₀ x) (q₁ : u G Q₁ x)
                    (p : Q₀ ≡ Q₁) (hp : p ≡ cong fst (foo f₀ f₁ q₀ q₁))
                    → pshf-bisimP (λ _ → g) (λ i → p i) f₀ f₁
μ-path (ptd-pshf-bisimP {G} g x Q₀ Q₁ f₀ f₁ q₀ q₁ p hp) =
  subst⁻ (λ p' → PathP (λ i → alpha G (P g) (p' i)) (μ f₀) (μ f₁))
  (hp ∙ subst (λ t → cong fst (sym (μ f₀ x q₀) ∙ snd (fst (fst t)) x (snd t)) ≡
      cong (fst ∘ fst) (sym (μ (τ' f₀) x q₀) ∙ snd (fst t) x (snd t))) (foo (τ' (τ' f₀)) (τ' (τ' f₁)) q₀ q₁)
      (cong (cong fst) (lCancel (μ f₀ x q₀)) ∙ sym (cong (cong (fst ∘ fst)) (lCancel (μ (τ' f₀) x q₀)))))
  (cong (snd ∘ fst) (foo (τ' f₀) (τ' f₁) q₀ q₁))
τ-bisim (ptd-pshf-bisimP g x Q₀ Q₁ f₀ f₁ q₀ q₁ p hp) =
  ptd-pshf-bisimP (τ g) x _ _ _ _ q₀ q₁ _ (isoInvInjective ΣPathIsoPathΣ _ _ (ΣPathP (_ , symP (transport⁻-filler _ _))))

