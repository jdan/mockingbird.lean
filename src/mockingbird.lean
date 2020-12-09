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
  cases h.mockingbird with M Hm,
  cases all_birds_fond h M with B Hb,  /- B = MB -/
  rw Hm B at Hb,                       /- B = BB -/
  use [B, Hb],
end

end mockingbird
