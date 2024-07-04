import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

structure OrderedPair (α: Type*) where
  x: α
  y: α
  deriving Repr

def add (a b: OrderedPair Nat): OrderedPair Nat :=
  ⟨a.x + b.x, a.y + b.y⟩

def add2 (a b: OrderedPair Nat): OrderedPair Nat :=
  OrderedPair.mk (a.x + b.x) (a.y + b.y)

def add3 (a b: OrderedPair Nat): OrderedPair Nat where
  x := a.x + b.x
  y := a.y + b.y

def add4: OrderedPair Nat → OrderedPair Nat → OrderedPair Nat
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

def add5: OrderedPair Nat → OrderedPair Nat → OrderedPair Nat
  | OrderedPair.mk x₁ y₁, OrderedPair.mk x₂ y₂ => OrderedPair.mk (x₁ + x₂) (y₁ + y₂)

def add6 (x y: OrderedPair Nat): OrderedPair Nat :=
  match x, y with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def one: OrderedPair Nat := ⟨1, 2⟩
def two: OrderedPair Nat := ⟨10, 10⟩
#eval add one two
#eval add2 one two
#eval add3 one two
#eval add4 one two
#eval add5 one two
#eval add6 one two

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

@[ext]
structure MyPoint where
  a : ℕ
  b : ℕ
  deriving Repr

def testPoint: MyPoint := ⟨1, 2⟩

example (p q: MyPoint) : p.a = q.a ∧ p.b = q.b → p = q := by
  intro h  -- h : p.a = q.a ∧ p.b = q.b
  cases' h with l r  -- l : p.a = q.a, r : p.b = q.b
  ext  -- goal is to prove p.a = q.a and p.b = q.b
  repeat' assumption

#eval testPoint
#eval testPoint.a

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

theorem point_add_comm2 (a b : Point) : add a b = add b a := by
  repeat rw [Point.add]
  ext <;> simp
  <;> rw [add_comm]

theorem point_add_comm (a b : Point) : add a b = add b a := by
  repeat rw [Point.add]
  ext <;> dsimp;
  repeat rw [add_comm]


protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  repeat rw [Point.add]
  ext <;> simp
  repeat rw [add_assoc]

def smul (r : ℝ) (a : Point) : Point where
  x := r * a.x
  y := r * a.y
  z := r * a.z

#check smul
def testPoint2: Point := smul 2 myPoint1

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  repeat rw [Point.add]
  repeat rw [Point.smul]
  ext <;> simp
  repeat rw [mul_add]


end Point

@[ext]
structure BigNumber where
x : ℕ
y : ℕ
h : x ≥ 1000
h₂ : y ≥ 1000
deriving Repr

#eval BigNumber.mk 1000 1000 (by norm_num) (by norm_num)
-- #eval BigNumber.mk 10 10  -- cannot do this

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1


structure NonnegativeReal where
  x : ℝ
  nonneg : x ≥ 0

protected def double(a: NonnegativeReal): NonnegativeReal where
  x := 2 * a.x
  nonneg := by
    norm_num
    exact a.nonneg

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def midpointTest (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := by
    have h : a.x ≥ 0 := by
      exact a.x_nonneg
    have h₂ : b.x ≥ 0 := by
      exact b.x_nonneg
    have h₃ : a.x + b.x ≥ 0 := by
      linarith
    exact div_nonneg h₃ (by norm_num) -- two proofs required
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := by
    apply add_nonneg
    case ha =>
      apply mul_nonneg
      assumption
      exact a.x_nonneg
    case hb =>
      apply mul_nonneg
      norm_num
      assumption
      exact b.x_nonneg
  y_nonneg := by
    apply add_nonneg
    <;> apply mul_nonneg
    case ha.ha =>
      assumption
    case ha.hb =>
      exact a.y_nonneg
    case hb.ha =>
      norm_num
      assumption
    case hb.hb =>
      exact b.y_nonneg
  z_nonneg := by sorry
  sum_eq := by sorry

end

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

#check IsLinear'

def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
