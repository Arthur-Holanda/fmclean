
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro h,
  intro g,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases h : P,
  intro g,
  assumption,
  intro g,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  by_cases h : P,
  intro g,
  assumption,
  intro g,
  contradiction,
  intro h,
  intro g,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hp,
  cases hp,
  right,
  assumption,
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hp,
  split,
  cases hp,
  assumption,
  cases hp,
  assumption,
  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hp,
  intro g,
  cases hp,
  contradiction,
  exact hp,

end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hp,
  intro g,
  cases hp,
  contradiction,
  exact hp,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hp,
  intro g,
  intro p,
  have q := hp p,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hp,
  intro p,
  by_contra,
  have np := hp h,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro hp,
  intro q,
  intro p,
  have qo := hp p,
  contradiction,
  intro hp,
  intro nq,
  by_contra,
  have qc := hp h,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hp,
  have LEM : P∨¬P,
    right,
    intro p,
    have LEM2 : P∨¬P,
      left,
      assumption,
    contradiction,
  contradiction,
    
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  have novopq : (P → Q),
  intro p,
  contradiction,
  have p := pqp  novopq,
  contradiction,
  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro npq,
  cases npq,
  cases pq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro npq,
  cases pq,
  cases npq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  have peq : (P ∨ Q),
  left,
  assumption,
  contradiction,
  intro q,
  have peq : (P ∨ Q),
  right,
  assumption,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  intro pq,
  cases pq,
  cases npnq,
  contradiction,
  cases npnq,
  contradiction,

end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_contra nqp,
  apply npq,
  split,
  by_contra np,
  apply nqp,
  right,
  assumption,
  by_contra nq,
  apply nqp,
  left,
  assumption,
  
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqnp,
  intro npq,
  cases nqnp,
  apply nqnp,
  cases npq,
  assumption,
  apply nqnp,
  cases npq,
  assumption,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro npq,
  by_contra nqp,
  apply npq,
  split,
  by_contra np,
  apply nqp,
  right,
  assumption,
  by_contra nq,
  apply nqp,
  left,
  assumption,
  intro nqnp,
  intro npq,
  cases nqnp,
  apply nqnp,
  cases npq,
  assumption,
  apply nqnp,
  cases npq,
  assumption,

end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro npq,
  split,
  intro p,
  have peq : (P ∨ Q),
  left,
  assumption,
  contradiction,
  intro q,
  have peq : (P ∨ Q),
  right,
  assumption,
  contradiction,
  intro npnq,
  intro pq,
  cases pq,
  cases npnq,
  contradiction,
  cases npnq,
  contradiction,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr,
  cases pqr_right,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  split,
  cases pqpr,
  cases pqpr,
  assumption,
  cases pqpr,
  assumption,
  cases pqpr,
  cases pqpr,
  left,
  assumption,
  cases pqpr,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split,
  cases pqr,
  left,
  assumption,
  cases pqr,
  right,
  assumption,
  cases pqr,
  left,
  assumption,
  cases pqr,
  right,
  assumption,

end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr,
  cases pqpr_right,
  left,
  assumption,
  cases pqpr_left,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  have pq : (P∧Q),
  split,
  assumption,
  assumption,
  have r :R := pqr pq,
  assumption,

end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pqr,
  intro pq,
  cases pq,
  have qr: (Q→R) := pqr pq_left, 
  have r : R := qr pq_right,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp,
  assumption,
  intro p,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp,
  assumption,
  assumption,
  intro p,
  left,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro expx,
  intro axnpx,
  intro np,
  apply expx,
  existsi axnpx,
  assumption,

end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro xAnpx,
  intro nxEPx,
  cases nxEPx with x px,
  have npx : ¬P x := xAnpx x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro xAPx,
  by_contra xEnpx,
  apply xAPx,
  intro x,
  by_contra npx,
  apply xEnpx,
  existsi x, 
  exact npx,

end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro xEnPx, 
  intro xAPx,
  cases xEnPx with  x npx,
  have px : P x := xAPx x,
  contradiction,

end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro xAPx,
  by_contra xEnpx,
  apply xAPx,
  intro x,
  by_contra npx,
  apply xEnpx,
  existsi x, 
  exact npx,
  intro xEnPx, 
  intro xAPx,
  cases xEnPx with  x npx,
  have px : P x := xAPx x,
  contradiction,

end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro expx,
  intro axnpx,
  intro np,
  apply expx,
  existsi axnpx,
  assumption,
  intro xAnpx,
  intro nxEPx,
  cases nxEPx with x px,
  have npx : ¬P x := xAnpx x,
  contradiction,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro xEPx,
  intro xAnPx,
  cases xEPx with  x npx,
  have npx : ¬P x := xAnPx x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro xAPx,
  intro xnEnPx,
  cases xnEnPx with  x npx,
   have px : P x := xAPx x,
   contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro xnEnPx,
  intro xAPx,
  by_cases pnp : P xAPx,
  assumption,
  have xEnPx : (∃x, ¬P x),
    existsi xAPx,
    assumption,
  contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
    intro xnAnPx,
  by_contra xnEPx,
  have xAnPx : ∀x, ¬P x,
    intro x,
    intro px,
    have xEPx: ∃x, P x,
      existsi x,
      exact px,
    contradiction,
  contradiction,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro xAPx,
  intro xnEnPx,
  cases xnEnPx with  x npx,
   have px : P x := xAPx x,
   contradiction,
    intro xnEnPx,
  intro xAPx,
  by_cases pnp : P xAPx,
  assumption,
  have xEnPx : (∃x, ¬P x),
    existsi xAPx,
    assumption,
  contradiction,

end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
   intro xEPx,
  intro xAnPx,
  cases xEPx with  x npx,
  have npx : ¬P x := xAnPx x,
  contradiction,
    intro xnAnPx,
  by_contra xnEPx,
  have xAnPx : ∀x, ¬P x,
    intro x,
    intro px,
    have xEPx: ∃x, P x,
      existsi x,
      exact px,
    contradiction,
  contradiction,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro xEPxQx, 
  cases xEPxQx with a PaQa,
  cases PaQa,
  split,
  existsi a,
  assumption,
  existsi a,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro xEPxQx,
  cases xEPxQx with a PaQa,
  cases PaQa,
  left,
  existsi a,
  exact PaQa,
  right,
  existsi a,
  exact PaQa,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
    intro xEPxouxEQx,
  cases xEPxouxEQx,
  cases xEPxouxEQx with a Pa,
  have PaQa : P a ∨ Q a,
    left,
    exact Pa,
  existsi a,
  exact PaQa,
  cases xEPxouxEQx with a Qa,
  have PaQa : P a ∨ Q a,
    right,
    exact Qa, 
  existsi a,
  exact PaQa,

end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro xAPxeQx,
  split,
  intro x,
  have PxQx := xAPxeQx x,
  cases PxQx with Px Qx,
  assumption,
  intro x,
  have PxQx := xAPxeQx x,
  cases PxQx with Px Qx,
  assumption,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro xAPxxAQx,
  cases xAPxxAQx,
  intro a,
  have Pa: P a := xAPxxAQx_left a,
  have Qa: Q a := xAPxxAQx_right a,
  split,
  exact Pa,
  exact Qa,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
   intro xAPxouxAQx,
  intro x,
  cases xAPxouxAQx with xAPx xAQx,
  have Px := xAPx x,
  left,
  assumption,
  have Qx := xAQx x,
  right,
  assumption,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
