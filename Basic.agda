{-# OPTIONS --cubical --no-import-sorts --guardedness #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma.Properties
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to prop-rec)
open import Cubical.Foundations.Equiv.Fiberwise

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
  
    nxt : XSu
    X nxt = X G
    S nxt = Σ _ alpha
    u nxt Q = u G (fst Q) 

record gpd (G : XSu) : Type₁ where
  coinductive
  field
    P : (x : X G) → ptd G x
    τ : gpd (nxt G P)

open gpd

record pshf {G : XSu} (g : gpd G) (Q : S G) : Type₁ where
    constructor pshf-mk
    coinductive
    field
      μ : alpha G (P g) Q
      τ' : pshf (τ g) (Q , μ)

open pshf

pshf-eta : {G : XSu} {g : gpd G} {Q : S G} (f : pshf g Q) → pshf-mk (μ f) (τ' f) ≡ f
μ (pshf-eta f i) = μ f
τ' (pshf-eta f i) = τ' f

repr : {G : XSu} (g : gpd G) (x : X G) (Q : S G) (p : Q ≡ fst (P g x)) → pshf g Q
μ (repr g x Q p) = let ((_ , homo) , pt) = P (τ g) x in
                    subst⁻ (alpha _ (P g)) (p ∙ cong fst (homo x pt)) homo
τ' (repr g x Q p) = repr (τ g) x _ (ΣPathP (_ , symP (transport⁻-filler _ _)))

record pshf-bisimP {G : I → XSu} (g : (i : I) → gpd (G i)) (Q : (i : I) → S (G i))
  (f₀ : pshf (g i0) (Q i0)) (f₁ : pshf (g i1) (Q i1)) : Type₁ where
  coinductive
  field
    μ-path : PathP (λ i → alpha (G i) (P (g i)) (Q i)) (μ f₀) (μ f₁)
    τ'-bisim : pshf-bisimP (λ i → τ (g i)) (λ i → (Q i , μ-path i)) (τ' f₀) (τ' f₁)

open pshf-bisimP

bisim→pathP : {G : I → XSu} {g : (i : I) → gpd (G i)} {Q : (i : I) → S (G i)}
                 {f₀ : pshf (g i0) (Q i0)} {f₁ : pshf (g i1) (Q i1)} (h : pshf-bisimP g Q f₀ f₁)
                 → PathP (λ i → pshf (g i) (Q i)) f₀ f₁
μ (bisim→pathP h i) = μ-path h i
τ' (bisim→pathP h i) = bisim→pathP (τ'-bisim h) i

record gpd-bisimP (G : I → XSu) (g₀ : gpd (G i0)) (g₁ : gpd (G i1)) : Type₁ where
  coinductive
  field
    P-path : PathP (λ i → (x : X (G i)) → ptd (G i) x) (P g₀) (P g₁)
    τ-bisim : gpd-bisimP (λ i → nxt (G i) (P-path i)) (τ g₀) (τ g₁)

open gpd-bisimP

gpd-bisim→PathP : {G : I → XSu} {g₀ : gpd (G i0)} {g₁ : gpd (G i1)} →
                      gpd-bisimP G g₀ g₁ → PathP (λ i → gpd (G i)) g₀ g₁
P (gpd-bisim→PathP h i) = P-path h i
τ (gpd-bisim→PathP h i) = gpd-bisim→PathP (τ-bisim h) i

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
τ'-bisim (ptd-pshf-bisimP g x Q₀ Q₁ f₀ f₁ q₀ q₁ p hp) =
  ptd-pshf-bisimP (τ g) x _ _ _ _ q₀ q₁ _ (isoInvInjective ΣPathIsoPathΣ _ _ (ΣPathP (_ , symP (transport⁻-filler _ _))))

record conGpd (G : XSu) : Type₂ where
  constructor conGpd-mk
  field
    BG : Type₁
    inc : X G → BG
    BG-to-S : BG → S G
    pt-inc : (x : X G) → u G (BG-to-S (inc x)) x
    ptd-prop : (x : X G) → isProp (Σ[ y ∈ BG ] u G (BG-to-S y) x)
    merely-pointed : (y : BG) → ∥ Σ[ x ∈ X G ] u G (BG-to-S y) x ∥

open conGpd

con-tail : {G : XSu} → (cg : conGpd G) → conGpd (nxt G λ x → _ , pt-inc cg x)
BG (con-tail cg) = BG cg
inc (con-tail cg) = inc cg
BG-to-S (con-tail cg) = λ y → BG-to-S cg y , λ x q → cong (λ t → BG-to-S cg (fst t) , snd t) (ptd-prop cg x _ _)
pt-inc (con-tail cg) = pt-inc cg
ptd-prop (con-tail cg) = ptd-prop cg
merely-pointed (con-tail cg) = merely-pointed cg

conGpd→gpd : {G : XSu} → conGpd G → gpd G
P (conGpd→gpd cg) = λ x → _ , pt-inc cg x
τ (conGpd→gpd cg) = conGpd→gpd (con-tail cg)

completion : {G : XSu} → gpd G → Type₁
completion {G} g = Σ[ Q ∈ S G ] Σ[ f ∈ pshf g Q ] ∥ Σ[ x ∈ X G ] u G Q x ∥

gpd→conGpd : {G : XSu} → gpd G → conGpd G
BG (gpd→conGpd g) = completion g
inc (gpd→conGpd g) x = fst (P g x) , repr g x _ refl , ∣ x , snd (P g x) ∣
BG-to-S (gpd→conGpd g) y = fst y
pt-inc (gpd→conGpd g) x = snd (P g x)
ptd-prop (gpd→conGpd g) x ((Q₀ , f₀ , _) , q₀) ((Q₁ , f₁ , _) , q₁) =
  ΣPathP ((ΣPathP (cong fst (foo f₀ f₁ q₀ q₁) , ΣPathP (bisim→pathP
  (ptd-pshf-bisimP g x Q₀ Q₁ f₀ f₁ q₀ q₁ _ refl) , isProp→PathP (λ i → squash) _ _))) , cong snd (foo f₀ f₁ q₀ q₁))
merely-pointed (gpd→conGpd g) (Q , f , hxq) = hxq

record conGpd-pathData {G : XSu} (cg cg' : conGpd G) : Type₁ where
  field
    BG-fun : BG cg → BG cg'
    BG-to-S-path : (y : BG cg) → BG-to-S cg y ≡ BG-to-S cg' (BG-fun y)

open conGpd-pathData

fundamentalTheoremOfId' : {ℓ ℓ' : Level} {A : Type ℓ} (x : A) (Eqx : A → Type ℓ') →
                          Eqx x → isProp (Σ A Eqx) → (y : A) → (x ≡ y) ≃ Eqx y
fst (fundamentalTheoremOfId' x Eqx Rfl isprop y) p = subst Eqx p Rfl
snd (fundamentalTheoremOfId' x Eqx Rfl isprop y) = fiberEquiv ((x ≡_)) Eqx (λ _ p → subst Eqx p Rfl)
  (isEquivFromIsContr _ (isContrSingl x) (inhProp→isContr (x , Rfl) isprop)) y

surjection-forall : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} (P : B → Type ℓ'') (isprop : (b : B) → isProp (P b))
                    (f : A → B) → isSurjection f → ((a : A) → P (f a)) → (b : B) → P b
surjection-forall P isprop f fsurj Pa b = prop-rec (isprop b) (λ (a , p) → subst _ p (Pa a)) (fsurj b)

inc-eq-equiv : {G : XSu} (cg : conGpd G) (x : X G) (y : BG cg) → (inc cg x ≡ y) ≃ u G (BG-to-S cg y) x
inc-eq-equiv cg x y = fundamentalTheoremOfId' (inc cg x) _ (pt-inc cg x) (ptd-prop cg x) _

inc-surjection : {G : XSu} (cg : conGpd G) → isSurjection (inc cg)
inc-surjection cg y = prop-rec squash (λ (x , q) →  ∣ x , equivFun (invEquiv (inc-eq-equiv cg x y)) q ∣) (merely-pointed cg y)

BG-fun-isEquiv : {G : XSu} {cg cg' : conGpd G} (h : conGpd-pathData cg cg') → isEquiv (BG-fun h)
equiv-proof (BG-fun-isEquiv {G} {cg} {cg'} h) = surjection-forall (λ y → isContr (fiber (BG-fun h) y))
  (λ _ → isPropIsContr) (inc cg') (inc-surjection cg')
  λ x → subst (λ p → isContr (Σ[ y ∈ BG cg ] p y))
    (funExt λ y → ua (inc-eq-equiv cg x y) ∙ cong (λ Q → u G Q x) (BG-to-S-path h y) ∙ sym (ua (inc-eq-equiv cg' x (BG-fun h y))) ∙ ua (isoToEquiv symIso))
    (isContrSingl (inc cg x))

conGpd-pathData-toPath : {G : XSu} (cg cg' : conGpd G) → conGpd-pathData cg cg' → cg ≡ cg'
conGpd-pathData-toPath {G} cg cg' h = EquivJ (λ BG' e → {BG-to-S' : _} →
     (BG-to-S-path' : (y : BG') → BG-to-S' y ≡ BG-to-S cg' (equivFun e y)) →
     (inc' : _) → (pt-inc' : _) → (ptd-prop' : _) → (merely-pointed' : _) →
                    conGpd-mk BG' inc' BG-to-S' pt-inc' ptd-prop' merely-pointed' ≡ cg')
                (λ {BG-to-S'} BG-to-S-path' inc' →
                subst⁻ (λ BG-to-S'' → (pt-inc' : _) → (ptd-prop' : _) → (merely-pointed' : _) →
                       conGpd-mk (BG cg') inc' BG-to-S'' pt-inc' ptd-prop' merely-pointed' ≡ cg')
                (funExt BG-to-S-path')
                λ pt-inc' ptd-prop' merely-pointed' i →
                conGpd-mk (BG cg') (λ x → cong fst (ptd-prop cg' x (inc' x , pt-inc' x) (inc cg' x , pt-inc cg' x)) i)
                (BG-to-S cg') (λ x → cong snd (ptd-prop cg' x (inc' x , pt-inc' x) (inc cg' x  , pt-inc cg' x)) i)
                (λ x → isPropIsProp (ptd-prop' x) (ptd-prop cg' x) i)
                λ y → squash (merely-pointed' y) (merely-pointed cg' y) i)
                ((BG-fun h , BG-fun-isEquiv h))
                (BG-to-S-path h) _ _ _ _

τ-completion : {G : XSu} (g : gpd G) → completion g ≃ completion (τ g)
τ-completion g = isoToEquiv (iso
    (λ y → (fst y , μ (fst (snd y))) , τ' (fst (snd y)) , snd (snd y))
    (λ y → fst (fst y) , pshf-mk (snd (fst y)) (fst (snd y)) , snd (snd y))
    (λ y → refl)
    (λ y → ΣPathP (refl , ΣPathP (pshf-eta _ , refl))))

BG-to-S-pshf : {G : XSu} (cg : conGpd G) (y : BG cg) → pshf (conGpd→gpd cg) (BG-to-S cg y)
μ (BG-to-S-pshf cg y) = snd (BG-to-S (con-tail cg) y)
τ' (BG-to-S-pshf cg y) = BG-to-S-pshf (con-tail cg) y

BG→completion : {G : XSu} (cg : conGpd G) → BG cg → completion (conGpd→gpd cg)
BG→completion cg y = BG-to-S cg y , BG-to-S-pshf cg y , merely-pointed cg y

conGpd-eta : {G : XSu} (cg : conGpd G) → conGpd-pathData cg (gpd→conGpd (conGpd→gpd cg))
BG-fun (conGpd-eta cg) = BG→completion cg
BG-to-S-path (conGpd-eta cg) = λ y → refl

con-tail-τ : {G : XSu} → (g : gpd G) → conGpd-pathData (con-tail (gpd→conGpd g)) (gpd→conGpd (τ g))
BG-fun (con-tail-τ g) = equivFun (τ-completion g)
BG-to-S-path (con-tail-τ g) = λ y → {!!} -- ΣPathP (refl , funExt λ x → funExt λ q → {!!})

gpd-eta : {G : I → XSu} → (g : gpd (G i0)) (g' : gpd (G i1))
  (p : PathP (λ i → gpd (G i)) (conGpd→gpd (gpd→conGpd g)) g') → gpd-bisimP (λ i → G i) g g'
P-path (gpd-eta g g' p) i = P (p i) 
τ-bisim (gpd-eta {G} g g' p) = gpd-eta (τ g) (τ g') (subst⁻ (λ h → PathP (λ i → gpd (nxt (G i) (P (p i)))) h (τ g')) bla λ i → τ (p i))
  where bla : conGpd→gpd (gpd→conGpd (τ g)) ≡ τ (conGpd→gpd (gpd→conGpd g))
        bla = cong conGpd→gpd (sym (conGpd-pathData-toPath _ _ (con-tail-τ _)))

