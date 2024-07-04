import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

structure NonnegativeGroup (n : Nat) where
  V : Fin n → Nat
  bigger_than_two : ∀ i : Fin n, V i ≥ 2

def myNonnegGroup : NonnegativeGroup 3 where
  V := fun i => i + 2
  bigger_than_two := by
    intros i
    apply Nat.succ_le_succ
    apply Nat.succ_le_succ
    simp

structure Group₁Cat where
  α : Type*
  str : Group₁ α

section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check f.toFun
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check f.right_inv
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check f.symm
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) := by
  rfl  -- the trans function is basically just g ∘ f if you look in the def

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

-- proving some basic theorems about equivalence relations
section test
-- variable (α β γ : Type*)
-- variable (f : α ≃ β) (g : β ≃ γ)

-- symm just gives you a function that goes the other way
-- and satisfies all of the same Equiv properties like
example {α β : Type*} (f : α ≃ β) : f = f.symm.symm := by
  rfl

end test

-- basically reverse engineering Equiv.refl
def symm_one (α: Type*) : Equiv.Perm α where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by sorry
  right_inv := by sorry

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  inv : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_inv : ∀ x : α, add (inv x) x = zero
  -- fill in the rest

@[ext]
structure Point where
  x : Int
  y : Int
  z : Int
  deriving Repr

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point := ⟨-1 * a.x, -1 * a.y, -1 * a.z⟩

def p := Point.mk 4 3 2

#check neg
#check add

#eval add p p
#eval neg p

def zero : Point := ⟨0, 0, 0⟩

-- showing that the group axioms hold for the Point type
def addGroupPoint : AddGroup₁ Point where
  add := Point.add
  zero := Point.zero
  inv := Point.neg
  add_assoc := by
    intros x y z
    ext
    case x =>
      simp [add]
      rw [add_assoc]
    case y =>
      simp [add]
      rw [add_assoc]
    case z =>
      simp [add]
      rw [add_assoc]
  add_zero := by
    intros x
    rw [Point.add]
    ext <;> simp
    repeat rfl
  zero_add := by
    intros x
    rw [Point.add]
    ext <;> simp
    repeat rfl
  add_left_inv := by
    intros x
    rw [Point.neg, Point.add]
    ext <;> simp
    repeat rfl

end Point

section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n


example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_right_inv, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

class AddGroup₂ (α : Type*) where
  add : α → α → α
  -- fill in the rest
