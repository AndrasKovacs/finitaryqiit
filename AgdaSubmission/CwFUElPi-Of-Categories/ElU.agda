
{- Universe (of set-valued functors) in ℂat, part of QIIT code syntax #-}

open import Level

module CwFUElPi-Of-Categories.ElU {α : Level} where

open import StrictLib hiding (id; _∘_)
open import CwFUElPi-Of-Categories.CwF {suc α}{α} public

-- U ~ const 𝕊et
-- hence: Tm Γ U ~ [Γ, 𝕊et]
U : {Γ : Con {suc α}{α}} → Ty Γ
U {Γ} = mkTy (λ i → Set α) (λ i _ j → i → j) (λ x → x) (λ f g x → f (g x))
             refl̃ refl̃ refl̃

abstract
-- postulate
  U[] : ∀{Γ Δ}(σ : Sub  Γ Δ) → U [ σ ]T ≡ U
  U[] {Γ}{Δ} σ = mkTy≡
    (λ _ → refl)
    (λ { refl̃ refl̃ → refl })
    (λ { {i}{ii₀}{ii₀} refl̃ → uncoe ((λ f → ii₀ → ii₀) & (σ.id ⁻¹)) _})
    λ { {i}{j}{k}{f}{g}{ii₀}{ii₀} refl̃ {jj₀}{jj₀} refl̃ {kk₀}{kk₀} refl̃ {ff₀}{ff₀} refl̃ {gg₀}{gg₀} refl̃ →
        uncoe ((λ f₁ → ii₀ → kk₀) & (σ.∘ ⁻¹)) (λ x → ff₀ (gg₀ x))}
    where module σ = Sub σ; module Γ = Con Γ; module Δ = Con Δ

-- [Γ, 𝕊et] are "discrete" displayed categories
-- analogously to how sets are discrete categories
El : ∀{Γ}(a : Tm  {γ = suc α}{α} Γ U) → Ty Γ
El {Γ} a = mkTy
  (λ i → Lift (a.Obj i))
  (λ {i}{j} ii f jj → a.⇒ f (lower ii) ≡ lower jj)
  (λ {i}{ii} → happly a.id (lower ii))
  (λ {i}{j}{k}{f}{g}{ii}{jj}{kk} ff gg → happly a.∘ (lower ii) ◾ (a.⇒ f) & gg ◾ ff)
  (λ { {i}{j}{f}{lift ii}{lift jj}{ff} → (UIP _ _ ~) ◾̃ uncoe ((λ f → a.⇒ f ii ≡ jj) & Γ.idl ⁻¹) ff })
  (λ { {i}{j}{f}{lift ii}{lift jj}{ff} → (UIP _ _ ~) ◾̃ uncoe ((λ f → a.⇒ f ii ≡ jj) & Γ.idr ⁻¹) ff })
  (λ { {i}{j}{k}{l}{f}{g}{h}{lift ii}{lift jj}{lift kk}{lift ll}{ff}{gg}{hh} →
       (UIP _ _ ~ ) ◾̃ uncoe ((λ f → a.⇒ f ii ≡ ll) & Γ.ass ⁻¹) _})
  where module a = Tm a; module Γ = Con Γ

abstract
  El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → El a [ σ ]T ≡ El (coe (Tm Γ & U[] σ) (_[_]t {Γ}{Δ}{U} a σ))
  El[] {Γ}{Δ}{σ}{a} =
    mkTy≡
      (λ i → Lift & obj i)
      mor
      id
      comp
    where
    module a = Tm a; module σ = Sub σ; module Δ = Con Δ; module Γ = Con Γ

    obj :
        (i : Γ.Obj) →
        (a.Obj (σ.Obj i)) ≡
        (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) i)
    obj i = uñ (
         ap2̃̃ (λ (A : Ty Γ)(t : Tm {γ = suc α}{α} Γ A) → Tm.Obj {D = A} t i)
             (U[] σ)
             (uncoe (Tm Γ & U[] σ) (a [ σ ]t) ⁻¹̃))

    mor :
        {i j : Γ.Obj} {ii₀ : Lift (a.Obj (σ.Obj i))}
        {ii₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) i)} →
        ii₀ ≃ ii₁ →
        {f : i Γ.⇒ j} {jj₀ : Lift (a.Obj (σ.Obj j))}
        {jj₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) j)} →
        jj₀ ≃ jj₁ →
        (El a Ty.⇒[ ii₀ ] σ.⇒ f) jj₀ ≡
        (Tm.⇒ (coe (Tm Γ & U[] σ) (a [ σ ]t)) f (lower ii₁) ≡ lower jj₁)
    mor {i} {j} {lift ii₀} {lift ii₁} ii₂ {f} {lift jj₀} {lift jj₁} jj₂ =
      let p1 = ap2̃̃ (λ (A : Ty Γ) t → Tm.⇒ {γ = suc α}{α}{D = A} t {i}{j} f)
                    (U[] σ) (uncoe (Tm Γ & U[] σ) (a [ σ ]t) ⁻¹̃)
          p2 = happlỹ (obj i) (obj j) p1 (ap2̃̃ (λ A → lower {A = A}) (obj i) ii₂)
      in ap3̃ (λ A (l r : A) → l ≡ r) (obj j) p2 (ap2̃̃ (λ A → lower {A = A}) (obj j) jj₂)

    id :
      {i : Γ.Obj} {ii₀ : Lift (a.Obj (σ.Obj i))}
      {ii₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) i)} →
      ii₀ ≃ ii₁ →
      coe ((λ f → (El a Ty.⇒[ ii₀ ] f) ii₀) & (σ.id ⁻¹)) (Ty.id (El a)) ≃
      happly (Tm.id (coe (Tm Γ & U[] σ) (a [ σ ]t))) (lower ii₁)
    id {i} {lift ii₀} {lift ii₁} ii₂ =
        uncoe ((λ f → (El a Ty.⇒[ lift ii₀ ] f) (lift ii₀)) & (σ.id ⁻¹)) _
      ◾̃ uncoe ((λ x → a.⇒ x ii₀ ≡ ii₀) & (σ.id ⁻¹) ◾ mor ii₂ ii₂)
        (Ty.id (El a)) ⁻¹̃ ◾̃ (UIP _ _ ~)

    comp :
      {i j k : Γ.Obj} {f : j Γ.⇒ k} {g : i Γ.⇒ j}
        {ii₀ : Lift (a.Obj (σ.Obj i))}
        {ii₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) i)} →
        ii₀ ≃ ii₁ →
        {jj₀ : Lift (a.Obj (σ.Obj j))}
        {jj₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) j)} →
        jj₀ ≃ jj₁ →
        {kk₀ : Lift (a.Obj (σ.Obj k))}
        {kk₁ : Lift (Tm.Obj (coe (Tm Γ & U[] σ) (a [ σ ]t)) k)} →
        kk₀ ≃ kk₁ →
        {ff₀ : (El a Ty.⇒[ jj₀ ] σ.⇒ f) kk₀}
        {ff₁
         : Tm.⇒ (coe (Tm Γ & U[] σ) (a [ σ ]t)) f (lower jj₁) ≡ lower kk₁} →
        ff₀ ≃ ff₁ →
        {gg₀ : (El a Ty.⇒[ ii₀ ] σ.⇒ g) jj₀}
        {gg₁
         : Tm.⇒ (coe (Tm Γ & U[] σ) (a [ σ ]t)) g (lower ii₁) ≡ lower jj₁} →
        gg₀ ≃ gg₁ →
        coe ((λ f₁ → (El a Ty.⇒[ ii₀ ] f₁) kk₀) & (σ.∘ ⁻¹))
        ((El a Ty.∘ ff₀) gg₀)
        ≃
        (happly (Tm.∘ (coe (Tm Γ & U[] σ) (a [ σ ]t))) (lower ii₁) ◾
         Tm.⇒ (coe (Tm Γ & U[] σ) (a [ σ ]t)) f & gg₁ ◾ ff₁)
    comp {i} {j} {k} {f} {g} {lift ii₀} {lift ii₁} ii₂ {lift jj₀} {lift jj₁} jj₂
         {lift kk₀} {lift kk₁} kk₂ {ff₀} {ff₁} ff₂ {gg₀} {gg₁} gg₂ =
        uncoe (mor ii₂ kk₂)
              (coe ((λ f₁ → (El a Ty.⇒[ lift ii₀ ] f₁) (lift kk₀)) & (σ.∘ ⁻¹)) ((El a Ty.∘ ff₀) gg₀)) ⁻¹̃
      ◾̃ (UIP _ _ ~)

infixl 5 _^U
_^U : {Γ Δ : Con}(σ : Sub Γ Δ) → Sub (Γ ▶ U) (Δ ▶ U)
_^U {Γ}{Δ} σ = (σ ∘ₛ wk) ,s coe (Tm (Γ ▶ U) & (U[] wk ◾ U[] (σ ∘ₛ wk) ⁻¹)) vz

-- Not enough memory to check
-- infixl 5 _^U
-- _^El : {Γ Δ : Con}(σ : Sub Γ Δ)(a : Tm Δ U) → Sub (Γ ▶ El (coe (Tm Γ & U[] σ) (a [ σ ]t))) (Δ ▶ El a)
-- _^El {Γ}{Δ} σ a = (σ ∘ₛ wk) ,s
--   coe (Tm (Γ ▶ El (coe (Tm Γ & U[] σ) (a [ σ ]t))) &
--                                   ((_[ wk ]T) & (El[] {Γ}{Δ}{σ}{a} ⁻¹) ◾
--                                   ([][]T (El a) wk σ)))
--       vz
