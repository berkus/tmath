#print Bool.noConfusionType

theorem bool_d: ∀b, Bool.noConfusionType P b b :=
  Bool.rec id id

example (h: false = true): False :=
  Eq.ndrec (bool_d false) h

example (h: false = true): False :=
  Bool.noConfusion h

#check λ(h: false = true) => (Bool.noConfusion h : False)

#print funext
#print propext

#print Quot
#print Quot.mk
-- (f: α → β) → (∀a b, r a b → f a = f b) → (Quot r → β)
#print Quot.lift
-- (∀(a: α), β (Quot.mk r a)) → ∀(q: Quot r), β q
#print Quot.ind
#print Quot

-- r a b → Quot.mk r a = Quot.mk r b
#print Quot.sound

example {α: Sort u}{β: α → Sort v}{f g: (x:α) → β x}(h: ∀x, f x = g x): f = g :=
  let r := λf g => ∀x, f x = g x
  let qApp (f: Quot r): (x:α) → β x :=
    λx => (f.liftOn (λf => f x) (λf g (h: ∀x, f x = g x) => h x) : β x)
  congrArg qApp (Quot.sound h : Quot.mk _ f = Quot.mk _ g)

#print propext
#print Classical.em

open Classical in
  def eq_choose {U V: α → Prop}(uv: U = V)
  : (eu: ∃x, U x) → (ev: ∃x, V x) → choose eu = choose ev :=
    uv ▸ (λ_ _ => rfl)

open Classical in
  example (P: Prop) : P ∨ ¬P :=
    let U := λx => (x = true) ∨ P
    let V := λx => (x = false) ∨ P
    let eu: ∃x, U x := ⟨true, Or.inl rfl⟩
    let ev: ∃x, V x := ⟨false, Or.inl rfl⟩
    let u := choose eu;  let v := choose ev
    let p_uv: P → u = v :=
      λp =>
        let uv: U = V :=
          funext $ λ_ => propext ⟨λ_ => Or.inr p, λ_ => Or.inr p⟩
        eq_choose uv eu ev
    match (choose_spec eu), (choose_spec ev) with
    | Or.inr p, _        => Or.inl p
    | _,        Or.inr p => Or.inl p
    | Or.inl (ut: u = true),
      Or.inl (vf: v = false) => Or.inr $ mt p_uv (ut ▸ vf ▸ Bool.noConfusion)

def fls (_:Nat): Bool := false

#check (⟨false, ⟨0, rfl⟩⟩ : {b:Bool // ∃n, fls n = b})
#check (⟨false, ⟨1, rfl⟩⟩ : {b:Bool // ∃n, fls n = b})
