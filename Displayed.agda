{-# OPTIONS --cubical --guardedness #-}

open import Basic
open import Cubical.Foundations.Everything

open span

record spanover (sp : span) : Type₂ where
  field
    Y : X sp → Type₀
    T : S sp → Type₁
    v : (Q : S sp) (R : T Q) (x : X sp) → Y x → u sp Q x → Type₁

open spanover

dPtd : (sp : span) (dsp : spanover sp) (x : X sp) → Y dsp x → ptd sp x → Type₁
dPtd sp dsp x y (Q , q) = Σ[ R ∈ T dsp Q ] v dsp Q R x y q

dα : {sp : span} {dsp : spanover sp} (P : (x : X sp) → ptd sp x) (dP : (x : X sp) (y : Y dsp x) → dPtd sp dsp x y (P x)) →
     (Q : S sp) (R : T dsp Q) → α P Q → Type₁
dα {sp} {dsp} P dP Q R μ = (x : X sp) (y : Y dsp x) (q : u sp Q x) (r : v dsp Q R x y q) →
                           PathP (λ i → dPtd sp dsp x y (μ x q i)) (dP x y) (R , r)
