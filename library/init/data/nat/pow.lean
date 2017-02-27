/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Exponentiation on natural numbers

This is a work-in-progress, and contains additions to other theories.
-/
prelude
import init.data.nat.basic init.core

namespace nat

def pow (e : ℕ) : ℕ → ℕ
  | zero := 1
  | (succ n) := e * pow n

infix `^` := pow

end nat
