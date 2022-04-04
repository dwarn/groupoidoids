{-# OPTIONS --cubical --guardedness #-}

{-
The goal of this file is to give a coinductive definition of internal oo-groupoids in homotopy type theory.

What is an internal (oo-)groupoid? Any map f : X -> Y induces a groupoid structure on X, where a 'morphism'
x -> x' is a path f x ≡ f x'. We could say this is an 'equivalence relation', i.e. we have reflexivity,
symmetry, and transitivity. But there are also coherences in the form of associativity and unit laws,
as well as higher coherences in the form of MacLane's pentagon et cetera. Instead of trying to make this
precise, let us just say that a (concrete) groupoid structure on X is *defined* to be a surjective
map f : X -> Y. It is reasonable to expect that the groupoid structure on X is enough to recover Y
-- as a quotient, or completion -- but only assuming surjectivity. With this definition in hand, one might
still wonder if it is possible to give a more 'algebraic' definition of groupoids. This is what we aim to
do.

Just as one often needs to strengthen a lemma in order to prove it by induction, we will need to define
something more general than groupoids. In general, we suppose given a span of types

S* --> X
|
|
v
S

(In the formalization, S* is presented by a type family S → X → Type.)
A groupoid _structured_ by this span is a diagram like

P --> S* --> X
|     |
|     |
v     v
Y --> S

where the square is a pullback and the top vertical composite is an equivalence. Note that a structured
groupoid in particular gives a map X -> Y.

-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma.Properties
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to prop-rec)
open import Cubical.Foundations.Equiv.Fiberwise
open import Lib

-- an element of this record is a span of types, presented using a sigma-type
record span : Type₂ where
  field
    X : Type₀
    S : Type₁
    u : S → X → Type₁

open span

ptd : (sp : span) → X sp → Type₁
ptd sp x = Σ[ Q ∈ S sp ] u sp Q x

-- α P Q says that Q is 'modelled on P': whenever you point it, it looks like P
α : {sp : span} (P : (x : X sp) → ptd sp x) → S sp → Type₁
α {sp = sp} P Q = (x : X sp) (q : u sp Q x) → P x ≡ (Q , q)

-- given a span and a section of the right leg, hs P is a new span, consisting of things
-- modelled on P
hs : (sp : span) → ((x : X sp) → ptd sp x) → span
X (hs sp _) = X sp
S (hs sp P) = Σ _ (α P)
u (hs sp _) Q = u sp (fst Q) 

-- our 'algebraic' description of 'a groupoid structured by a span'
record gpd (sp : span) : Type₁ where
  coinductive
  field
    P : (x : X sp) → ptd sp x
    τ-gpd : gpd (hs sp P)

open gpd

-- a type of bisimulation between groupoid structures. used to characterise the path(over) types in gpd.
record gpd-bisim (sp : I → span) (g₀ : gpd (sp i0)) (g₁ : gpd (sp i1)) : Type₁ where
  coinductive
  field
    P-path : PathP (λ i → (x : X (sp i)) → ptd (sp i) x) (P g₀) (P g₁)
    τ-gpd-bisim : gpd-bisim (λ i → hs _ (P-path i)) (τ-gpd g₀) (τ-gpd g₁)

open gpd-bisim

{- bisimilarity implies equality. in cubical agda, this is just true and easy to prove. in non-cubical agda, or coq,
if we use the builtin coinductive types we would *not* be able to prove this. we would have to either
- postulate this 'coinductive extensionality' as an axiom, or
- use an *implementation* of coinductive types using pi-types and inductive types. in this case coinductive extensionality
  follows from FunExt -}
gpd-bisim→Path : {sp : I → span} {g₀ : gpd (sp i0)} {g₁ : gpd (sp i1)} →
                      gpd-bisim sp g₀ g₁ → PathP (λ i → gpd (sp i)) g₀ g₁
P (gpd-bisim→Path h i) = P-path h i
τ-gpd (gpd-bisim→Path h i) = gpd-bisim→Path (τ-gpd-bisim h) i

-- pshf g Q expresses that Q 'survives' through all the spans produced by g. in cases of interest
-- it corresponds to saying that Q has the structure of a (representable) presheaf (or, in the
-- (-1)-truncated case, an equivalence relation).
record pshf {sp : span} (g : gpd sp) (Q : S sp) : Type₁ where
    constructor mk-pshf
    coinductive
    field
      μ : α (P g) Q
      τ-pshf : pshf (τ-gpd g) (Q , μ)

open pshf

-- bisimulations between presheaf structures (essentially repeating gpd-bisim)
record pshf-bisim {sp : I → span} (g : (i : I) → gpd (sp i)) (Q : (i : I) → S (sp i))
  (f₀ : pshf (g i0) (Q i0)) (f₁ : pshf (g i1) (Q i1)) : Type₁ where
  coinductive
  field
    μ-path : PathP (λ i → α (P (g i)) (Q i)) (μ f₀) (μ f₁)
    τ-pshf-bisim : pshf-bisim (λ i → τ-gpd (g i)) (λ i → (Q i , μ-path i)) (τ-pshf f₀) (τ-pshf f₁)

open pshf-bisim

-- coinductive extensionality for pshf (esentially repeating gpd→bisim→pathP)
pshf-bisim→Path : {sp : I → span} {g : (i : I) → gpd (sp i)} {Q : (i : I) → S (sp i)}
                 {f₀ : pshf (g i0) (Q i0)} {f₁ : pshf (g i1) (Q i1)} (h : pshf-bisim g Q f₀ f₁)
                 → PathP (λ i → pshf (g i) (Q i)) f₀ f₁
μ (pshf-bisim→Path h i) = μ-path h i
τ-pshf (pshf-bisim→Path h i) = pshf-bisim→Path (τ-pshf-bisim h) i

-- this gives us 'representable presheaves' / Yoneda embeddings / quotient maps. the arguments
-- Q and p may look redundant, but we need to state the definition in this way in order for the
-- recursive call to make sense.
repr : {sp : span} (g : gpd sp) (x : X sp) (Q : S sp) (p : Q ≡ fst (P g x)) → pshf g Q
-- here we need to show that P g x is modelled on itself. we know that P (τ-gpd g) x is modelled
-- on P g x, and also that it equals P g x, so we prove this by transport (more precisely, subst⁻)
μ (repr g x Q p) = let ((_ , homo) , pt) = P (τ-gpd g) x in
                   subst⁻ (α (P g)) (p ∙ cong fst (homo x pt)) homo
-- we now need to show that the element of S (τ-gpd g) so constructed is a presheaf. recursively,
-- we may assume that P (τ-gpd g) x is a presheaf, and by construction what we have equals
-- P (τ-gpd g) x, so we done by recursive call.
τ-pshf (repr g x Q p) = repr (τ-gpd g) x _ (ΣPathP (_ , symP (transport⁻-filler _ _)))

-- a unit law 1 * a = a
one-mul : {sp : span} (g : gpd sp) (x : X sp) → μ (repr g x _ refl) x (snd (P g x)) ≡ refl
one-mul {sp} g x = let ((_ , homo) , pt) = P (τ-gpd g) x in
                   cong (λ p → subst⁻ (α (P g)) p homo x (snd (P g x))) (sym (lUnit (cong fst (homo x pt)))) ∙ 
                   foo (homo x pt) homo ∙
                   lCancel _
-- we compute a transport using the J-rule (how else to do it?)                   
  where foo : {px' : ptd sp x} (pxeq : P g x ≡ px') (al : α (P g) (fst px')) →
                   subst⁻ (α (P g)) (cong fst pxeq) al x (snd (P g x)) ≡ al x (snd px') ∙ sym pxeq
        foo = J (λ px' pxeq → (al : α (P g) (fst px')) → subst⁻ (α (P g)) (cong fst pxeq) al x (snd (P g x)) ≡ al x (snd px') ∙ sym pxeq)
              λ al → cong (λ f → f x (snd (P g x))) (transportRefl al) ∙ rUnit _

-- given Qᵢ , qᵢ (i = 0 , 1) two presheaves pointed at x, we have P g x ≡ Qᵢ , qᵢ by μ fᵢ x qᵢ, so they are equal to each other.
pshf→Path : {sp : span} {g : gpd sp} {x : X sp} {Q₀ Q₁ : S sp} (f₀ : pshf g Q₀) (f₂ : pshf g Q₁) (q₀ : u sp Q₀ x) (q₁ : u sp Q₁ x) →
         (Q₀ , q₀) ≡ (Q₁ , q₁)
pshf→Path f₀ f₁ q₀ q₁ = sym (μ f₀ _ q₀) ∙ μ f₁ _ q₁

-- this lemma is key. it is a generalisation of the fact that any two pointed torsors are equal, or that any object of a representable
-- presheaf on a groupoid is a universal object. the idea, roughly speaking, is that each component of fᵢ proves the earlier components
-- on each side (i = 0, 1) match up. so all the components match up.
-- the proof is really less scary than it looks -- most of the code is really simple equational reasoning.
-- as before, p and hp are redundant but we need to state the definition this way for the recursive call to make sense.
-- we could have stated the lemma as 'every pointed presheaf equals repr' but then this seems harder to prove.
ptd-pshf-bisim : {sp : span} (g : gpd sp) (x : X sp)
                    (Q₀ Q₁ : S sp) (f₀ : pshf g Q₀) (f₁ : pshf g Q₁) (q₀ : u sp Q₀ x) (q₁ : u sp Q₁ x)
                    (p : Q₀ ≡ Q₁) (hp : p ≡ cong fst (pshf→Path f₀ f₁ q₀ q₁))
                    → pshf-bisim (λ _ → g) (λ i → p i) f₀ f₁
μ-path (ptd-pshf-bisim {sp} g x Q₀ Q₁ f₀ f₁ q₀ q₁ p hp) =
  subst⁻ (λ p' → PathP (λ i → α (P g) (p' i)) (μ f₀) (μ f₁))
  (hp ∙ subst (λ t → cong fst (sym (μ f₀ x q₀) ∙ snd (fst (fst t)) x (snd t)) ≡
      cong (fst ∘ fst) (sym (μ (τ-pshf f₀) x q₀) ∙ snd (fst t) x (snd t))) (pshf→Path (τ-pshf (τ-pshf f₀)) (τ-pshf (τ-pshf f₁)) q₀ q₁)
      (cong (cong fst) (lCancel (μ f₀ x q₀)) ∙ sym (cong (cong (fst ∘ fst)) (lCancel (μ (τ-pshf f₀) x q₀)))))
  (cong (snd ∘ fst) (pshf→Path (τ-pshf f₀) (τ-pshf f₁) q₀ q₁))
τ-pshf-bisim (ptd-pshf-bisim g x Q₀ Q₁ f₀ f₁ q₀ q₁ p hp) =
  ptd-pshf-bisim (τ-gpd g) x _ _ _ _ q₀ q₁ _ (isoInvInjective ΣPathIsoPathΣ _ _ (ΣPathP (_ , symP (transport⁻-filler _ _))))

-- finally, we get to give the concrete definition of structured groupoids. it is cryptomorphic to the diagrammatic
-- definition in the docstring at the beginning of this file (with a surjectivity requirement).
record conGpd (sp : span) : Type₂ where
  constructor conGpd-mk
  field
    Y : Type₁
    arr : X sp → Y
    Y→S : Y → S sp
    pt-arr : (x : X sp) → u sp (Y→S (arr x)) x
    ptd-prop : (x : X sp) → isProp (Σ[ y ∈ Y ] u sp (Y→S y) x)
    merely-pointed : (y : Y) → ∥ Σ[ x ∈ X sp ] u sp (Y→S y) x ∥

open conGpd

-- every concrete groupoid has a head and a *tail*.
τ-conGpd : {sp : span} → (cg : conGpd sp) → conGpd (hs sp λ x → Y→S cg (arr cg x) , pt-arr cg x)
Y (τ-conGpd cg) = Y cg
arr (τ-conGpd cg) = arr cg
Y→S (τ-conGpd cg) = λ y → Y→S cg y , λ x q → cong (λ t → Y→S cg (fst t) , snd t) (ptd-prop cg x _ _)
pt-arr (τ-conGpd cg) = pt-arr cg
ptd-prop (τ-conGpd cg) = ptd-prop cg
merely-pointed (τ-conGpd cg) = merely-pointed cg

-- thus a concrete groupoid gives an algebraic groupoid.
conGpd→gpd : {sp : span} → conGpd sp → gpd sp
P (conGpd→gpd cg) = λ x → _ , pt-arr cg x
τ-gpd (conGpd→gpd cg) = conGpd→gpd (τ-conGpd cg)

-- we want to show that algebraic groupoids are also concrete groupoids. the first step is to define the underlying type,
-- i.e. the completion / quotient of an algebraic groupoid. we can think of it as something like 'image of Yoneda embedding'.
completion : {sp : span} → gpd sp → Type₁
completion {sp = sp} g = Σ[ Q ∈ S sp ] Σ[ f ∈ pshf g Q ] ∥ Σ[ x ∈ X sp ] u sp Q x ∥

-- putting things together, algebraic groupoids are concrete groupoids.
gpd→conGpd : {sp : span} → gpd sp → conGpd sp
Y (gpd→conGpd g) = completion g
arr (gpd→conGpd g) x = fst (P g x) , repr g x _ refl , ∣ x , snd (P g x) ∣
Y→S (gpd→conGpd g) y = fst y
pt-arr (gpd→conGpd g) x = snd (P g x)
ptd-prop (gpd→conGpd g) x ((Q₀ , f₀ , _) , q₀) ((Q₁ , f₁ , _) , q₁) =
  ΣPathP ((ΣPathP (cong fst (pshf→Path f₀ f₁ q₀ q₁) , ΣPathP (pshf-bisim→Path
  (ptd-pshf-bisim g x Q₀ Q₁ f₀ f₁ q₀ q₁ _ refl) , isProp→PathP (λ i → squash) _ _))) , cong snd (pshf→Path f₀ f₁ q₀ q₁))
merely-pointed (gpd→conGpd g) (Q , f , hxq) = hxq

-- we will use this for an extensionality principle for concrete groupoids. conveniently, it has much fewer fields
-- than gpd→conGpd itself
record conGpd-pathData {sp : span} (cg cg' : conGpd sp) : Type₁ where
  field
    Y-fun : Y cg → Y cg'
    Y→S-path : (y : Y cg) → Y→S cg y ≡ Y→S cg' (Y-fun y)

open conGpd-pathData

-- a concrete groupoid has two type families X → Y → Type: one given by arr x ≡ y and one by u.
-- in either case the sigma type Σ[ y ∈ Y ] P x y is contractible which lets us show the type families are equivalent.
arr-eq-equiv : {sp : span} (cg : conGpd sp) (x : X sp) (y : Y cg) → (arr cg x ≡ y) ≃ u sp (Y→S cg y) x
arr-eq-equiv cg x y = fundamentalTheoremOfId' (arr cg x) _ (pt-arr cg x) (ptd-prop cg x) _

arr-surjection : {sp : span} (cg : conGpd sp) → isSurjection (arr cg)
arr-surjection cg y = prop-rec squash (λ (x , q) →  ∣ x , equivFun (invEquiv (arr-eq-equiv cg x y)) q ∣) (merely-pointed cg y)

Y-fun-isEquiv : {sp : span} {cg cg' : conGpd sp} (h : conGpd-pathData cg cg') → isEquiv (Y-fun h)
equiv-proof (Y-fun-isEquiv {sp} {cg} {cg'} h) = surjection-forall (λ y → isContr (fiber (Y-fun h) y))
  (λ _ → isPropIsContr) (arr-surjection cg') λ x → subst (λ p → isContr (Σ[ y ∈ Y cg ] p y))
    (funExt λ y → ua (arr-eq-equiv cg x y ∘ₑ
                       ((pathToEquiv (cong (λ Q → u sp Q x) (Y→S-path h y))) ∘ₑ
                       ((invEquiv (arr-eq-equiv cg' x (Y-fun h y))) ∘ₑ
                       (isoToEquiv symIso) ))))
    (isContrSingl (arr cg x))
    
-- putting everything together, we get the desired extensionality principle for conGpd.
-- the proof is less scary than it looks -- most of the code is just spelling out what type families we
-- are transporting along.
conGpd-pathData-toPath : {sp : span} {cg cg' : conGpd sp} → conGpd-pathData cg cg' → cg ≡ cg'
conGpd-pathData-toPath {sp} {cg} {cg'} h = EquivJ (λ Y' e → {Y→S' : _} →
     (Y→S-path' : (y : Y') → Y→S' y ≡ Y→S cg' (equivFun e y)) →
     (arr' : _) → (pt-arr' : _) → (ptd-prop' : _) → (merely-pointed' : _) →
                    conGpd-mk Y' arr' Y→S' pt-arr' ptd-prop' merely-pointed' ≡ cg')
                (λ {Y→S'} Y→S-path' arr' →
                subst⁻ (λ Y→S'' → (pt-arr' : _) → (ptd-prop' : _) → (merely-pointed' : _) →
                       conGpd-mk (Y cg') arr' Y→S'' pt-arr' ptd-prop' merely-pointed' ≡ cg')
                (funExt Y→S-path')
                λ pt-arr' ptd-prop' merely-pointed' i →
                conGpd-mk (Y cg') (λ x → cong fst (ptd-prop cg' x (arr' x , pt-arr' x) (arr cg' x , pt-arr cg' x)) i)
                (Y→S cg') (λ x → cong snd (ptd-prop cg' x (arr' x , pt-arr' x) (arr cg' x  , pt-arr cg' x)) i)
                (λ x → isPropIsProp (ptd-prop' x) (ptd-prop cg' x) i)
                λ y → squash (merely-pointed' y) (merely-pointed cg' y) i)
                ((Y-fun h , Y-fun-isEquiv h))
                (Y→S-path h) _ _ _ _
  
Y→S-pshf : {sp : span} (cg : conGpd sp) (y : Y cg) → pshf (conGpd→gpd cg) (Y→S cg y)
μ (Y→S-pshf cg y) = snd (Y→S (τ-conGpd cg) y)
τ-pshf (Y→S-pshf cg y) = Y→S-pshf (τ-conGpd cg) y

-- every concrete groupoid is the completion of an algebraic groupoid
conGpd-eta : {sp : span} (cg : conGpd sp) → conGpd-pathData cg (gpd→conGpd (conGpd→gpd cg))
Y-fun (conGpd-eta cg) y = Y→S cg y , Y→S-pshf cg y , merely-pointed cg y
Y→S-path (conGpd-eta cg) = λ y → refl

-- the map gpd→conGpd respects tails
gpd→conGpd-τ : {sp : span} → (g : gpd sp) → conGpd-pathData (τ-conGpd (gpd→conGpd g)) (gpd→conGpd (τ-gpd g))
Y-fun (gpd→conGpd-τ g) (Q , (f , hq)) = (Q , μ f) , τ-pshf f , hq
Y→S-path (gpd→conGpd-τ g) = λ (Q , (f , _)) → ΣPathP (refl , funExt λ x → funExt λ q →
                             cong (λ p → sym p ∙ μ f x q) (one-mul g x) ∙ sym (lUnit _))

-- every algebraic groupoid is the kernel of a concrete groupoid
gpd-eta : {sp : I → span} → (g : gpd (sp i0)) (g' : gpd (sp i1))
  (p : PathP (λ i → gpd (sp i)) (conGpd→gpd (gpd→conGpd g)) g') → gpd-bisim (λ i → sp i) g g'
P-path (gpd-eta g g' p) i = P (p i) 
τ-gpd-bisim (gpd-eta {sp} g g' p) = gpd-eta (τ-gpd g) (τ-gpd g')
                                    (subst⁻ (λ h → PathP (λ i → gpd (hs _ (P (p i)))) h (τ-gpd g'))
                                     (cong conGpd→gpd (sym (conGpd-pathData-toPath (gpd→conGpd-τ _))))
                                     λ i → τ-gpd (p i))

gpd≃conGpd : {sp : span} → gpd sp ≃ conGpd sp
gpd≃conGpd = isoToEquiv (iso gpd→conGpd
                             conGpd→gpd
                             (λ cg → sym (conGpd-pathData-toPath (conGpd-eta cg)))
                             λ g → sym (gpd-bisim→Path (gpd-eta g _ refl)))

terminal-span : Type₀ → span
X (terminal-span X) = X
S (terminal-span X) = X → Type₀
u (terminal-span X) Q x = Lift (Q x)

-- we'd like to show that concrete groupoids structured by the terminal span are simply surjections.
-- currently the formalisation is stalled by universe issues (one will need a good notion of 'small' types
-- and the principle of replacement coming from the join construction)
{-
conGpd-terminal-span : (X : Type₀) → conGpd (terminal-span X) ≃ (Σ[ Y ∈ Type₁ ] X ↠ Y)
conGpd-terminal-span X = isoToEquiv (iso
  (λ cg → Y cg , arr cg , arr-surjection cg)
  (λ (Y , (f , fsurj)) → conGpd-mk Y f (λ y x → {!f x ≡ y!}) {!!} {!!} {!!})
  {!!}
  {!!})
-}
