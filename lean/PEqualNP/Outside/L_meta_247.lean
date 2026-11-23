import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_247_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 4 → Bool) : Bool :=
  !x 3 || (x 2 && (x 0 || x 1))

private def gateValue (g : Gate) (wires : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => wires.getD i false)

private def appendGate (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [gateValue g wires]

private def relevantInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private def gateBudget (g : Gate) : ℕ :=
  match g.op with
  | .not => 0
  | _ => 1

private def Agrees (x y : List Bool) (S : Finset ℕ) : Prop :=
  ∀ i ∈ S, x.getD i false = y.getD i false

private theorem read_new (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

private theorem read_old (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · simp only [List.getD, List.getElem?_append_left h]
  · have h₁ : w.length ≤ i := by omega
    have h₂ : (w ++ [b]).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ h₁, List.getD_eq_default _ _ h₂]

private theorem read_input {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD, List.getElem?_ofFn]
  split <;> rfl

private theorem gateValue_relevant (g : Gate) (w : List Bool) :
    gateValue g w = g.op.eval ((relevantInputs g).map fun i => w.getD i false) := by
  cases hop : g.op <;> simp [gateValue, relevantInputs, hop]
  cases g.inputs <;> simp [GateOp.eval]

private theorem relevant_card (g : Gate) (h : g.inputs.length ≤ 2) :
    (relevantInputs g).toFinset.card ≤ 1 + gateBudget g := by
  have hc := List.toFinset_card_le (relevantInputs g)
  cases hop : g.op <;> simp [relevantInputs, gateBudget, hop, List.length_take] at hc ⊢ <;>
    omega

-- When a required wire is the new output, replace it by the inputs it reads.
private theorem step_support (g : Gate) (n : ℕ) (S : Finset ℕ) (h : g.inputs.length ≤ 2) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gateBudget g ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        Agrees x y T → Agrees (appendGate x g) (appendGate y g) S := by
  by_cases hn : n ∈ S
  · refine ⟨S.erase n ∪ (relevantInputs g).toFinset, ?_, ?_⟩
    · have hcard := Finset.card_union_le (S.erase n) (relevantInputs g).toFinset
      rw [Finset.card_erase_of_mem hn] at hcard
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨n, hn⟩
      have hg := relevant_card g h
      omega
    · intro x y hx hy agree i hi
      by_cases he : i = n
      · subst i
        unfold appendGate
        rw [← hx, read_new, hx, ← hy, read_new, gateValue_relevant, gateValue_relevant]
        apply congrArg (g.op.eval)
        apply List.map_congr_left
        intro j hj
        exact agree j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
      · have hix : i ≠ x.length := hx ▸ he
        have hiy : i ≠ y.length := hy ▸ he
        simpa only [appendGate, read_old _ _ _ hix, read_old _ _ _ hiy] using
          agree i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hi⟩))
  · refine ⟨S, by omega, ?_⟩
    intro x y hx hy agree i hi
    have hne : i ≠ n := fun h' => hn (h' ▸ hi)
    have hix : i ≠ x.length := hx ▸ hne
    have hiy : i ≠ y.length := hy ▸ hne
    simpa only [appendGate, read_old _ _ _ hix, read_old _ _ _ hiy] using agree i hi

private theorem support (gs : List Gate) (n : ℕ) (S : Finset ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ T : Finset ℕ, T.card ≤ S.card + (gs.map gateBudget).sum ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        Agrees x y T → Agrees (gs.foldl appendGate x) (gs.foldl appendGate y) S := by
  induction gs generalizing n S with
  | nil =>
    exact ⟨S, by simp, fun _ _ _ _ agree => agree⟩
  | cons g gs ih =>
    obtain ⟨T, hT, htail⟩ := ih (n + 1) S (fun a ha => h a (List.mem_cons_of_mem _ ha))
    obtain ⟨U, hU, hhead⟩ := step_support g n T (h g List.mem_cons_self)
    refine ⟨U, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · intro x y hx hy agree
      exact htail _ _ (by simp [appendGate, hx]) (by simp [appendGate, hy])
        (hhead x y hx hy agree)

private theorem budget_le (gs : List Gate) : (gs.map gateBudget).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : gateBudget g ≤ 1 := by cases hop : g.op <;> simp [gateBudget, hop]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem budget_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) :
    (gs.map gateBudget).sum < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, hop⟩ := h
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · have hg : gateBudget a = 0 := by simp [gateBudget, hop]
      have hgs := budget_le gs
      omega
    · have hg : gateBudget g ≤ 1 := by cases he : g.op <;> simp [gateBudget, he]
      have hgs := ih ⟨a, ha, hop⟩
      omega

private def Below (x y : List Bool) : Prop :=
  ∀ i, x.getD i false = true → y.getD i false = true

private theorem monotone_gate (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (x y : List Bool) (h : Below x y) :
    gateValue g x = true → gateValue g y = true := by
  rcases hg with hg | hg
  · simp only [gateValue, hg, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hx b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i (hx _ ⟨i, hi, rfl⟩)
  · simp only [gateValue, hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

private theorem monotone_wires (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (x y : List Bool) (hlen : x.length = y.length) (h : Below x y) :
    Below (gs.foldl appendGate x) (gs.foldl appendGate y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) (appendGate x g) (appendGate y g)
    · simp [appendGate, hlen]
    · intro i hi
      by_cases he : i = x.length
      · rw [he, appendGate, read_new] at hi
        rw [he, hlen, appendGate, read_new]
        exact monotone_gate g (hg g List.mem_cons_self) x y h hi
      · have hey : i ≠ y.length := he ∘ (fun e => e.trans hlen.symm)
        simp only [appendGate, read_old _ _ _ he] at hi
        simp only [appendGate, read_old _ _ _ hey]
        exact h i hi

set_option maxRecDepth 10000 in
private theorem essential :
    ∀ i : Fin 4, ∃ x y : Fin 4 → Bool, (∀ j, j ≠ i → x j = y j) ∧ target x ≠ target y := by
  decide

private theorem support_needs_four (C : Circuit) (S : Finset ℕ)
    (hc : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = target x)
    (hs : ∀ x y : List Bool, x.length = 4 → y.length = 4 →
      Agrees x y S → Agrees (C.gates.foldl appendGate x) (C.gates.foldl appendGate y)
        {C.output}) :
    4 ≤ S.card := by
  apply le_trans (show 4 ≤ (Finset.range 4).card by simp)
  apply Finset.card_le_card
  intro i hi
  have hi4 := Finset.mem_range.mp hi
  by_contra hmiss
  obtain ⟨x, y, hxy, htarget⟩ := essential ⟨i, hi4⟩
  have hagree : Agrees (List.ofFn x) (List.ofFn y) S := by
    intro j hj
    by_cases hj4 : j < 4
    · have hji : (⟨j, hj4⟩ : Fin 4) ≠ ⟨i, hi4⟩ := by
        intro he
        have he' : j = i := congrArg Fin.val he
        exact hmiss (he' ▸ hj)
      simpa only [read_input, dite_eq_left hj4] using hxy ⟨j, hj4⟩ hji
    · simp only [read_input, dite_eq_right hj4]
  have hout := hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) hagree C.output (by simp)
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at hout
  exact htarget ((hc x).symm.trans (hout.trans (hc y)))

private theorem lower (s : ℕ) (h : HasCircuitSize 4 target s) : 4 ≤ s := by
  obtain ⟨C, hfan, hsize, hcorrect⟩ := h
  by_cases hnot : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨S, hs, hagree⟩ := support C.gates 4 {C.output} (fun g hg => (hfan g hg).2)
    have hfour := support_needs_four C S hcorrect hagree
    have hb := budget_lt C.gates hnot
    simp only [Finset.card_singleton] at hs
    change C.gates.length ≤ s at hsize
    omega
  · have hg : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
      intro g hmem
      have h : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        simpa using (hfan g hmem).1
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnot ⟨g, hmem, h⟩).elim
    let x : Fin 4 → Bool := fun _ => false
    let y : Fin 4 → Bool := fun i => decide (i = 3)
    have hbefore : Below (List.ofFn x) (List.ofFn y) := by
      intro i hi
      rw [read_input] at hi
      by_cases hir : i < 4 <;> simp [x, hir] at hi
    have hafter := monotone_wires C.gates hg (List.ofFn x) (List.ofFn y) (by simp) hbefore
    have hx : C.eval (List.ofFn x) = true := (hcorrect x).trans (by decide)
    have hy : C.eval (List.ofFn y) = false := (hcorrect y).trans (by decide)
    have hy' : C.eval (List.ofFn y) = true := hafter C.output hx
    rw [hy] at hy'
    cases hy'

private theorem upper (s : ℕ) (hs : 4 ≤ s) : HasCircuitSize 4 target s := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [3]⟩, ⟨.or, [6, 5]⟩], 7⟩, ?_, hs, ?_⟩
  · simp [FanInTwo]
  · decide

theorem exact_size (s : ℕ) : HasCircuitSize 4 target s ↔ 4 ≤ s :=
  ⟨lower s, upper s⟩

end PEqualNP.Outside.L_meta_247_aux

theorem PEqualNP.Outside.L_meta_247 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (!(x 3)) || (x 2 && (x 0 || x 1))) s ↔ 4 ≤ s := by
  exact PEqualNP.Outside.L_meta_247_aux.exact_size
