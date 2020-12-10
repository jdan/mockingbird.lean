import tactic

namespace mockingbird

inductive Bird
| Ap : Bird -> Bird -> Bird

/- A * B = Bird.Ap A B -/
instance : has_mul Bird := ⟨Bird.Ap⟩

structure forest : Prop :=
  /-
    (the composition condition)
    For any two birds A and B, there is a bird C such that
    for any bird x, Cx = A(Bx)
  -/
  (comp (A B : Bird) : ∃ C, ∀ x, C * x = A * (B * x))

  /-
    (the mockingbird condition)
    The forest contains a mockingbird M
  -/
  (mockingbird : ∃ (M : Bird), ∀ x, M * x = x * x)

/--
  1. One rumor is that Every bird in the forest is fond of
  at least one bird
-/
theorem all_birds_fond (h : forest) (A : Bird)
  : ∃ B, B = A * B :=
begin
  obtain ⟨M, hM⟩ := h.mockingbird,
  obtain ⟨C, hC⟩ := h.comp A M,
  use C * C,
  rw [←hM, ←hC, hM],
end

/--
  2. A bird x is called "egocentric" if it is fond of itself.
  Prove using C₁ and C₂ that at least one bird is egocentric.
-/
theorem egocentric_bird_exists (h : forest)
  : ∃ (x : Bird), x = x * x :=
begin
  obtain ⟨M, hM⟩ := h.mockingbird,
  obtain ⟨B, hB⟩ := all_birds_fond h M,
  rw hM B at hB,
  use [B, hB],
end

/-
  3. We are not given that there is a mockingbird; instead,
  we are given that there is an agreeable bird A.

  Is this enough to guarantee that every bird is fond of
  at least one bird?
-/
structure forest₂ : Prop :=
  (comp (A B : Bird) : ∃ C, ∀ x, C * x = A * (B * x))
  (agreeable : ∃ (A : Bird), ∀ B, ∃ x, A * x = B * x)

theorem all_birds_fond₂ (h : forest₂) (B : Bird)
  : ∃ H, H = B * H :=
begin
  obtain ⟨A, hA⟩ := h.agreeable,
  obtain ⟨C, hC⟩ := h.comp B A,
  obtain ⟨y, hy⟩ := hA C,   /- Ay = Cy -/
  rw hC y at hy,           /- Ay = B(Ay) -/
  use [A * y, hy],         /- B is fond of Ay -/
end

end mockingbird
