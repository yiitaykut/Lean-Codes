import Mathlib
open Set

variable {α : Type} (A B C : Set α)

example : A ∩ (A ∪ B) = A := by
  ext x -- birinden alınan elemanın diğerinde olduğunu göstermek için kullanıyoruz.
  constructor -- çift yönlü kanıtlamayı parçalamak için
  · intro hx -- x'in A ve A ∪ B'nin elemanı olduğunu gösterir
    have h0 : x ∈ A := hx.left -- sol tarafını yani x'in A'nın elemanı olduğunu alır (istenen şey)
    exact h0
  · intro h1 -- burada ters yön başladı (x'in A'nın elemanı olduğunu gösteriyor)
    have h2 : x ∈ A ∪ B := by 
      left -- burada x'in A'nın elemanı(left) olduğunu kullanarak A ∪ B'nin elemanı olduğunu gösterdik
      exact h1
    have h3 : x ∈ A ∧ x ∈ A ∪ B := And.intro h1 h2 -- burada ise h1 ve h2'yi birleştirip istediğimizi elde ettik.
    exact h3

example (h : A ⊆ B) : C \ B ⊆ C \ A := by
  intro x hx -- bir eleman aldık ve hx ile onun C\B'den olduğunu kabul ettik.
  have h0 : x ∈ C := hx.left -- h0 ile hx'in solu yani x'in C'den olduğunu söyledik.
  have h1 : x ∉ B := hx.right -- h1 ile hx'in sağı yani x'in B'den olmadığını söyledik.
  have h2 : x ∉ A := by -- x'in A'da olmadığını göstereceğiz
    intro h3 -- A'da olduğunu kabul ediyoruz.
    have h4 : x ∈ B := h h3 -- A'da olduğundan dolayı x B'nin de elemanı oluyor. Contradiction oluyor. Yani x A'nın elemanı değil
    exact h1 h4
  have h5 : x ∈ C ∧ x ∉ A := And.intro h0 h2 -- ikisini birleştiriyoruz ve istediğimiz sonucu buluyoruz.
  exact h5

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x -- birinden alınan elemanın diğerinde olduğunu göstermek için kullanıyoruz.
  constructor -- çift yönlü kanıtlamayı parçalamak için
  · intro hx 
    have h0: x ∉ A := by -- X'in A'nın elemanı olmadığını göstermek istiyoruz
      intro h1 
      have h2 : x ∈ A ∪ B := by left
      exact hx h2
    
    have h3: x ∉ B := by -- X'in B'nın elemanı olmadığını göstermek istiyoruz
      intro h4
      have h5 : x ∈ A ∪ B := by right
      exact hx h5

    
    have h6 : x ∉ A ∧ x ∉ B := And.intro h0 h3

    intro hx -- şimdi ters yöne başlıyoruz

    have h7 : x ∉ A := hx.left
    have h8 : x ∉ B := hx.right
    have h9 : x ∉ A ∪ B by
      intro h10
      have h11 : x ∈ A := by left
      have h12 : x ∈ B := by right -- ters yönü yapmayı beceremedim.

    

    
