/-
Copyright (c) 2026 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- A basic test for the `←` modifier on local simp rules.
example {α β : Prop} (h : α ↔ β) (ha : α) : β := by
  aesop (rule_sets := [-builtin,-default]) (add simp [← h])

-- `←` turns an equality around.
example (h : a = b) : b = a := by
  aesop (rule_sets := [-builtin,-default]) (add simp [← h])

-- `←` combined with an explicit phase.
example {α β : Prop} (h : α ↔ β) (ha : α) : β := by
  aesop (rule_sets := [-builtin,-default]) (add norm simp [← h])

-- `←` on one rule among several.
example {α β δ γ : Prop} (h₁ : α → β) (h₂ : δ ↔ γ) (ha : α) (hd : δ) :
    β ∧ γ := by
  aesop (rule_sets := [-builtin,-default]) (add simp [h₁, ← h₂])

/--
error: aesop: ← is only supported for simp rules
-/
#guard_msgs in
example {α : Prop} (h : α) : α := by
  aesop (add safe apply [← h])
