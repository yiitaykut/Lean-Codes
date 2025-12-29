import Mathlib
open Real

def LimitAt (f : ℝ → ℝ) (a ℓ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → |f x - ℓ| < ε

theorem LimitAt_iff {f : ℝ → ℝ} {a ℓ : ℝ} :
    LimitAt f a ℓ ↔
      ∀ ε > 0, ∃ δ > 0,
        ∀ x, 0 < |x - a| → |x - a| < δ → |f x - ℓ| < ε := by
  rfl

theorem LimitAt.congr {f g : ℝ → ℝ} {a ℓ : ℝ}
    (h : ∀ x, x ≠ a → g x = f x)
    (hf : LimitAt f a ℓ) :
    LimitAt g a ℓ := by
  unfold LimitAt at *
  intro ε hε
  rcases hf ε hε with ⟨δ, hδpos, hδ⟩
  norm_num
  refine ⟨ δ, hδpos, ?_ ⟩
  intro x hxnot0 hxδ
  have xnota : x ≠ a := by
    intro hxa
    apply hxnot0
    simp [hxa]
  have hgequalf : g x = f x := h x xnota
  simp at hδ
  simp [hgequalf]
  exact hδ x hxnot0 hxδ

example : LimitAt (fun x => if x = 4 then 0 else x/2) 4 2 := by
  -- 1️⃣ if'li fonksiyonu x/2 ile değiştiriyoruz
  apply LimitAt.congr
  · intro x hx
    -- hx : x ≠ 4
    simp [hx]

  -- 2️⃣ şimdi lim x→4 x/2 = 2 gösterilecek
  intro ε hε
  -- |x/2 - 2| < ε istiyoruz
  -- |x/2 - 2| = |x - 4| / 2
  use 2*ε
  constructor
  · linarith
  · intro x hx0 hxδ
    have : |x/2 - 2| = |x - 4| / 2 := by
      ring_nf
    simp [this]
    linarith
  

example : LimitAt (fun x => if x = -1 then 2 else x^2 + 2*x + 1) (-1) 0 := by 
  apply LimitAt.congr
  · intro x hx
    -- hx : x ≠ -1
    simp [hx]

  · intro ε hε
    use Real.sqrt ε
    constructor
    · exact Real.sqrt_pos.mpr hε
    intro x hx0 hxδ
    have h1 : x^2 + 2*x + 1 = (x + 1)^2 := by ring
    have h2 : |(x + 1)^2| = |x + 1|^2 := by simp
    have h3 : |x + 1| < Real.sqrt ε := by
      simpa using hxδ
    have h4 : |x + 1|^2 < ε := by
      nlinarith
    rw [h1, h2]
    simp h4



example : LimitAt (fun x => (x - 1) * cos (1 / (x - 1))) 1 0 := by
  apply LimitAt.congr
  · intro x hx
    -- hx : x ≠ 1
    rfl

  -- ε–δ tanımı
  intro ε hε
  use ε
  constructor
  · exact hε
  · intro x hx0 hxδ
    have h0 : |cos (1 / (x - 1))| ≤ 1 := by
      exact abs_cos_le_one _
    have h1 : |(x - 1) * cos (1 / (x - 1))|
        ≤ |x - 1| := by
      calc
        |(x - 1) * cos (1 / (x - 1))|
            = |x - 1| * |cos (1 / (x - 1))| := by
                simp
        _ ≤ |x - 1| * 1 := by
                nlinarith
        _ = |x - 1| := by
                ring
    have h2 : |(x - 1) * cos (1 / (x - 1))| < ε := by
      exact lt_of_le_of_lt h1 hxδ -- iki eşitsizliği birleştiriyor burası

    simpa using h2


theorem limit_mul_zero {f g : ℝ → ℝ} {a M : ℝ} :
  LimitAt f a 0 → LimitAt g a M → LimitAt (fun x => f x * g x) a 0 := sorry

theorem limit_shift {f : ℝ → ℝ} {a L : ℝ} :
  LimitAt f a L ↔ LimitAt (fun h => f (a + h)) 0 L := by
  constructor
  -- ileri yön başlıyor
  · intro hf ε hε
    rcases hf ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro h h0 hδ_h
    have : |(a + h) - a| = |h| := by ring_nf
    rw [this] at hδ
    apply hδ (a + h)
    · simpa [this] using h0
    · simpa [this] using hδ_h
  -- şimdi geri yön
  · intro hh ε hε
    rcases hh ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx0 hxδ
    -- h = x - a seçiyoruz
    let h := x - a
    have h_eq : x = a + h := by simp
    rw [h_eq]
    apply hδ h
    · simpa [h] using hx0
    · simpa [h] using hxδ
    
