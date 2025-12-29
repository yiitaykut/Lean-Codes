import Mathlib

open scoped BigOperators

variable {G H : Type} [Group G] [Group H]

def q1_ker (φ : G →* H) : Subgroup G where
  carrier := {g | φ g = 1}
  one_mem' := by
    -- Hedef: φ 1 = 1
    [cite_start]simp [φ.map_one] [cite: 1]
  mul_mem' := by
    -- Hedef: φ (x * y) = 1
    intro x y hx hy
    simp at * -- hx: φ x = 1, hy: φ y = 1 haline getirir
    [cite_start]rw [φ.map_mul, hx, hy, mul_one] [cite: 1]
  inv_mem' := by
    -- Hedef: φ x⁻¹ = 1
    intro x hx
    simp at * -- hx: φ x = 1 haline getirir
    [cite_start]rw [φ.map_inv, hx, inv_one] [cite: 1]

theorem q2_injective_iff_ker_eq_bot (φ : G →* H) :
    Function.Injective φ ↔ φ.ker = ⊥ := by
  constructor
  · -- (=>) Birebir ise çekirdek birimdir
    intro h
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_ker] at hx
      -- φ(x) = 1 ve φ(1) = 1 olduğu için, birebirlikten x = 1 gelir
      apply h
      rw [hx, φ.map_one]
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact φ.ker.one_mem
  · -- (<=) Çekirdek birim ise homomorfizma birebirdir
    intro h x y hxy
    -- φ(x) = φ(y) => φ(x * y⁻¹) = 1
    have : φ (x * y⁻¹) = 1 := by
      rw [φ.map_mul, φ.map_inv, hxy, mul_inv_self]
    -- Bu da x * y⁻¹ elemanının çekirdekte olduğunu gösterir
    have h_mem : x * y⁻¹ ∈ φ.ker := this
    -- Çekirdek birim olduğu için x * y⁻¹ = 1, yani x = y
    rw [h] at h_mem
    simp at h_mem
    exact eq_of_mul_inv_eq_one h_mem


def q3_range (φ : G →* H) : Subgroup H where
  carrier := {h | ∃ g : G, φ g = h}
  one_mem' := by
    -- 1_H görüntüdür çünkü φ(1_G) = 1_H
    use 1
    exact φ.map_one
  mul_mem' := by
    -- Görüntüdeki iki elemanın çarpımı da görüntüdür
    intro a b ⟨g1, h1⟩ ⟨g2, h2⟩
    use g1 * g2
    rw [φ.map_mul, h1, h2]
  inv_mem' := by
    -- Görüntüdeki bir elemanın tersi de görüntüdür
    intro a ⟨g, hg⟩
    use g⁻¹
    rw [φ.map_inv, hg]


theorem q4_abelian_of_cyclic (g : G) (h : ∀ x : G, ∃ n : ℕ, x = g^n)
  (a b : G) : a * b = b * a := by
  rcases h a with ⟨n, rfl⟩
  rcases h b with ⟨m, rfl⟩
  -- gⁿ * gᵐ = gⁿ⁺ᵐ ve gᵐ * gⁿ = gᵐ⁺ⁿ olduğunu gösterelim
  rw [← pow_add, ← pow_add, add_comm]
