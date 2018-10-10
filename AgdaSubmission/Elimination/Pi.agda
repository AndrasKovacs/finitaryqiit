{-# OPTIONS --rewriting --allow-unsolved-metas #-}

import Syntax as S

open import StrictLib hiding (_∘_;id)

import InitialAlg.Eliminators as IA
open import InitialAlg.Eliminators using (Conᶜ; Tmᶜ; Subᶜ; Tyᶜ)

import ADS as ADS
open import ADS using (Conʳ; Tyʳ ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ)

module Elimination.Pi (Ω : S.Con)(ω : Conʳ Ω .ᴰ (Conᶜ Ω Ω S.id)) where

open import Elimination.CwF Ω ω
open import Elimination.ElU Ω ω

Π : {Γ : S.Con} {Γᴱ : Con Γ} {a : S.Tm Γ (S.U {Γ})} (aᴱ : Tm {Γ} Γᴱ
      {S.U {Γ}} (U {Γ} {Γᴱ}) a) {B : S.Ty (Γ S.▶ S.El {Γ} a)} → Ty {Γ
      S.▶ S.El {Γ} a} (_▶_ {Γ} Γᴱ {S.El {Γ} a} (El {Γ} {Γᴱ} {a} aᴱ)) B
      → Ty {Γ} Γᴱ (S.Π {Γ} a B)
Π {Γ}{Γᴱ}{a} aᴱ {B} Bᴱ ν t α =
  let α'  = coe ((ᴬ (Tmʳ a) & (Subᶜ Ω ν S.id ⁻¹)) ◾ Tmᶜ Ω a ν ⁻¹ ) α
      p1  = S.app t S.[ S.id S.,s α' ]t
      p2  = Bᴱ (ν S.,s α') (coe cheat p1) -- REWRITE spec
  in {!aᴱ ν!}


-- λ α₁ →
--   coe
--   (ᴰ (Tmʳ a) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id))
--    (ᴰ (Subʳ ν) (Conᶜ Ω Ω S.id) ω)
--    &
--    (lower & Tmᶜ Ω (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹) α₁) S.id ⁻¹ ◾
--     coecoe⁻¹ (Tmᶜ Ω (a S.[ ν ]t) S.id) α₁))
--   (lower
--    (Tmʳ (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹) α₁) .ᴰ (Conᶜ Ω Ω S.id) ω))
