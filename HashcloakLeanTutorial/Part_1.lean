import Mathlib.Data.ZMod.Basic

/-
The result of following HashCloak's Lean tutorial:
https://hashcloak.com/blog/tutorial-introduction-to-formal-verification-with-lean-(part-1)
-/

-- Simple modular arithmetic via ZMod, which defines the integers modulo n
#eval (5: ZMod 7) + (6: ZMod 7) -- (5 + 6) mod 7 == 4

-- Part 1: defining a BitString and XOR

-- Define the BitString type, which is a Vector of ZMod 2, of length L
def BitString (L : ℕ) : Type := Vector (ZMod 2) L

-- The tutorial states that BitString is a "dependent type, which gives a
-- different instantiation for different values L in ℕ"
-- According to the Lean 4 documentation, "dependent types are types that
-- contain non-type expressions. A common source of dependent types is a named
-- argument to a function."
-- https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/#dependent-types

-- Dependent types are a vast topic, so for now we can treat them as a black box.

#check BitString 5

-- i.e. (BitString 5) is a length-5 BitString type

namespace BitString
-- Define xor. Its body uses the zipWith function, whose type is:
    -- def zipWith (f : α → β → φ) (as : Vector α n) (bs : Vector β n) : Vector φ n
def xor {L : ℕ} (x y : BitString L) : (BitString L) :=
  Vector.zipWith (fun a b => a + b) x y

-- Try out xor on sample inputs:

def a : BitString 4 := #v[0, 1, 0, 1]
def b : BitString 4 := #v[1, 0, 1, 0]

-- should evaluate to [1, 1, 1, 1]
#eval (BitString.xor a b).toList.map (fun x => x.val)

-- Part 2: proving properties of XOR

-- Commutativity: x ⊕ y = y ⊕ x

lemma xor_comm_property {L : ℕ} (x y : BitString L) : xor x y = xor y x :=
  by
    -- The tutorial omits this step, but it's crucial to running the code in the CLI.
    -- `unfold` changes the goal from `x.xor y = y.xor x` to `xor x y = xor y x`
    unfold BitString at x y
    -- An extensionality lemma: two things are identical if their components
    -- are the same
    apply Vector.ext
    -- Fixes the free variable i, and introduces an assumption that i < L
    intro i h_i_lt_L
    -- The tutorial uses the `simp[xor]` and `simp[add_comm]` tactics to make
    -- Lean try all relevant lemmas to make progress.
    -- simp [xor, add_comm]
    -- Without `simp`, we can instead use:
    unfold xor
    repeat rw [Vector.getElem_zipWith]
    apply add_comm

    -- Claude suggests changing `def BitString ...` to `abbrev BitString` so as
    -- to "mark it reducible so simp and instance search see through it
    -- everywhere", but I will stick to `def` to keep this file as close to the
    -- tutorial as possible.

-- Associativity: x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z
lemma xor_assoc_property {L : ℕ} (x y z : BitString L) : xor x (xor y z) = xor (xor x y) z :=
  by
    -- `unfold` changes the goal to `x.xor (y.xor z) = (x.xor y).xor z`
    unfold BitString at x y z
    apply Vector.ext
    simp[xor, add_assoc]

-- Define the identity element and prove correctness
-- The identity element ID is a bit string with all 0s. For all `x: x ⊕ ID = x`.
def BitString_ID {L : ℕ} : BitString L := Vector.replicate L 0

lemma xor_show_identity {L : ℕ} (x : BitString L) : xor x BitString_ID = x :=
    by 
      unfold BitString at x
      apply Vector.ext
      simp [xor, BitString_ID]
    -- The above can also be written as:
    -- Vector.ext fun i i_less_than_L => by unfold BitString at x; simp [xor, BitString_ID]
    -- Note the `unfold` step which the tutorial omits.

-- Self-inverse of XOR: x ⊕ x = ID
lemma xor_self_inverse {L : ℕ} (x : BitString L) : xor x x = BitString_ID :=
  by
    unfold BitString at x
    apply Vector.ext
    intro i i_less_than_L
    simp [xor, BitString_ID]
    exact CharTwo.add_eq_zero.mpr rfl

-- Part 3: define a Shannon cipher
structure ShannonCipher (K M C : Type) where
  enc : K → M → C
  dec : K → C → M
  correctness : ∀ (k : K) (m : M), dec k (enc k m) = m

-- Shows that we can instantiate a ShannonCipher with ℕ, String, or Bool
-- (question: what would the values of a bit look like in String form?
#check ShannonCipher Nat String Bool

-- Part 4: prove that the one-time pad is a ShannonCipher
def OneTimePad (L : ℕ) : ShannonCipher (BitString L) (BitString L) (BitString L) :=
{
  enc k m := xor k m
  dec k c := xor k c
  correctness :=
    by
      simp[xor_assoc_property]
      simp[xor_self_inverse]
      simp[xor_comm_property]
      simp[xor_show_identity]
}

end BitString
