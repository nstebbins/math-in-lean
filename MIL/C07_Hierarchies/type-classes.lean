import Mathlib.Algebra.Group.Basic
-- import Mathlib.Algebra.Group.Defs

namespace Add

/-
  structures allow you to define multiple 'add' variants for the same input type
-/

structure AddStructure (α : Type) where
  add : α → α → α

def addNat1 : AddStructure Nat where
  add := Nat.add

def addNat2 : AddStructure Nat where
  add := fun a b => a + b + 1 -- one extra

#eval addNat1.add 1 2 -- 3
#eval addNat2.add 1 2 -- 4

/-
  classes give you one 'add' per type but now that 'add' is implicitly selected!
-/

class AddClass (α : Type) where
  add : α → α → α

instance : AddClass Nat where
  add := Nat.add

@[instance]
def myAddNat : AddClass Nat where
  add := fun a b => a + b + 1 -- one extra

#eval AddClass.add 1 2 -- 4 b/c myAddNat is selected by Lean

#synth AddClass Nat -- doesn't seem to work :/

/-
  when to use class?

  when it's clear what the canonical instance should be for the input type and there
  will never be multiple variants... e.g. ℕ add is pretty universally agreed upon
-/

/-
  now let's work with a class that has a proposition & builds off AddClass
-/

class AddComm (α : Type) extends AddClass α where
  add_comm : ∀ a b : α, add a b = add b a

instance : AddComm Nat where
  add := Nat.add
  add_comm := Nat.add_comm

-- how do I use AddComm though in proofs?

end Add

namespace GroupProd

/-
  let's define a group cartesian product structure
-/

universe u

@[ext]
structure DirectProduct (α: Type u)[Group α] where
  fst : α
  snd : α

@[simp]
def dpMul{α : Type u}[Group α](d₁ d₂: DirectProduct α): DirectProduct α where
  fst := d₁.fst * d₂.fst
  snd := d₁.snd * d₂.snd

@[simp]
def dpInv{α : Type u}[Group α](d₁: DirectProduct α): DirectProduct α where
  fst := d₁.fst⁻¹
  snd := d₁.snd⁻¹

@[simp]
def dpOne{α : Type u}[Group α]: DirectProduct α where
  fst := 1
  snd := 1

variable{α : Type u}[Group α]
instance : Group (DirectProduct α) where
  one := dpOne
  mul := dpMul
  inv := dpInv
  mul_assoc := by
    intros a b c
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    ext
    apply mul_assoc a₁ b₁ c₁ -- why does apply work here?
    apply mul_assoc a₂ b₂ c₂
  one_mul := by
    intros a
    ext
    obtain ⟨a₁, a₂⟩ := a
    apply one_mul a₁
    obtain ⟨a₁, a₂⟩ := a
    apply one_mul a₂
  mul_one := by sorry
  mul_left_inv := by sorry

end GroupProd

namespace SimpleClass

class MulAssoc(α: Type) extends Mul α where
  mul_assoc: ∀ a b c : α, (a * b) * c = a * (b * c)

@[ext]
structure Point where
  x : Nat
  y : Nat

def mul (a b: Point): Point := ⟨a.x * b.x, a.y * b.y⟩

instance : MulAssoc Point where
  mul := mul
  mul_assoc := by
    intros a b c
    ext
    repeat apply Nat.mul_assoc

end SimpleClass
