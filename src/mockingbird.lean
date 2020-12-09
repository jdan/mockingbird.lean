import tactic

namespace mockingbird

inductive Bird
| Ap : Bird -> Bird -> Bird
open Bird

/--
  1. One rumor is that Every bird in the forest is fond of
  at least one bird
-/
theorem all_birds_fond
  /-
    (the composition condition)
    For any two birds A and B, there is a bird C such that
    for any bird x, Cx = A(Bx)
  -/
  (C₁ : ∀ A B, ∃ C, ∀ x, Ap C x = Ap A (Ap B x))

  /-
    (the mockingbird condition)
    The forest contains a mockingbird M
  -/
  (C₂ : ∃ M, ∀ x, Ap M x = Ap x x)

  : ∀ A, ∃ B, B = Ap A B :=
begin
  intro A,
  cases C₂ with M Hm,
  cases (C₁ A M) with C Hc,   /- Cx = A(Mx) -/
  have CC := Hc C,            /- CC = A(MC) -/
  rw Hm at CC,                /- CC = A(CC) -/
  existsi Ap C C,
  exact CC,
end

/--
  2. A bird x is called "egocentric" if it is fond of itself.
  Prove using C₁ and C₂ that at least one bird is egocentric.
-/
theorem egocentric_bird_exists
  (C₁ : ∀ A B, ∃ C, ∀ x, Ap C x = Ap A (Ap B x))
  (C₂ : ∃ M, ∀ x, Ap M x = Ap x x)
  : ∃ x, x = Ap x x :=
begin
  have C₂' := C₂,
  cases C₂ with M Hm,
  cases all_birds_fond C₁ C₂' M with B Hb,  /- B = MB -/
  rw Hm B at Hb,                            /- B = BB -/
  existsi B,
  exact Hb,
end

end mockingbird
