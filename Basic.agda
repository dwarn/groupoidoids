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
    alpha Q = (x : X G) (f : u G Q x) → P x ≡ (Q , f)

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

record pshf (i : Size) (G : XSu) (g : gpd G) (Q : S G) : Type₁ where
    coinductive
    field
      μ : alpha G (P g) Q
      τ' : {j : Size< i} → pshf j (nxt G (P g)) (τ g) (Q , μ)

open pshf

repr : {i : Size} (G : XSu) (g : gpd G) (x : X G) → pshf i G g (fst (P g x))
μ (repr G g x) = let ((_ , homo) , pt) = P (τ g) x in
                 subst⁻ (alpha G (P g) ∘ fst) (homo x pt) homo
τ' (repr G g x) {j = j} = let ((_ , homo) , pt) = P (τ g) x in
                          transport⁻
                            (cong (pshf j (nxt G (P g)) (τ g)) (ΣPathP (cong fst (homo x pt) , symP (transport⁻-filler _ _))))
                            (repr (nxt G (P g)) (τ g) x)
