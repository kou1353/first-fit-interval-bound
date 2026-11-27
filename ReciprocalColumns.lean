import Std
import Lean.Elab.Tactic.Omega

/-!
End-to-end price 17/5 bound for nonempty closed-interval First-Fit walls.
Round fees and incomes are scaled by five. The interval data determine the
ordered columns, their evolution, the terminal certificate, and the bound.
-/
namespace ReciprocalColumns

/-- If I and J meet, a point between a hit of I and a hit of J cannot
separate both of their active blocks. Endpoints are integer ranks. -/
theorem between_hits {l r a b p q z : Int} (hp : l ≤ p) (hq : q ≤ b)
    (hinter : a ≤ r) (hpz : p ≤ z) (hzq : z ≤ q) :
    (l ≤ z ∧ z ≤ r) ∨ (a ≤ z ∧ z ≤ b) := by
  by_cases h : z ≤ r
  · exact Or.inl ⟨by omega, h⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- An occupied slot's incomes through, and including, its death round. -/
inductive EndsInDeath : Nat → List Nat → Prop where
  | die {cash : Nat} (h : cash ≤ 5) : EndsInDeath cash [0]
  | step {cash pay : Nat} {tail : List Nat} (h : 5 ≤ cash + pay)
      (next : EndsInDeath (cash + pay - 5) tail) :
      EndsInDeath cash (pay :: tail)

theorem death_budget {c : Nat} {xs : List Nat} (h : EndsInDeath c xs) :
    c + xs.sum ≤ 5 * xs.length := by
  induction h with
  | die h => simpa using h
  | step h _ ih =>
    simp only [List.sum_cons, List.length_cons]
    omega

/-- During a vacant tenure, a real round of the terminal column costs 5. -/
theorem vacant_budget (xs : List Nat) (h : ∀ x ∈ xs, x ≤ 5) :
    xs.sum ≤ 5 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ 5 := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons]
    omega

/-- Each epoch either ends in the occupant's death or pays a bounded vacancy charge. -/
inductive Epoch : List Nat → Prop where
  | occupied {cash xs} (h : EndsInDeath cash xs) : Epoch xs
  | vacant {xs} (h : ∀ x ∈ xs, x ≤ 5) : Epoch xs

theorem epoch_budget {xs : List Nat} (h : Epoch xs) : xs.sum ≤ 5 * xs.length := by
  cases h with
  | occupied h => have ht := death_budget h; omega
  | vacant h => exact vacant_budget xs h

/-- Consecutive epochs in one direction, in chronological order. -/
inductive Side : List Nat → Prop where
  | empty : Side []
  | append {xs ys} (h : Epoch xs) (rest : Side ys) : Side (xs ++ ys)

private theorem sum_cat (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem side_budget {xs : List Nat} (h : Side xs) : xs.sum ≤ 5 * xs.length := by
  induction h with
  | empty => simp
  | append he _ ih =>
    have hx := epoch_budget he
    simp only [sum_cat, List.length_append]
    omega

/-- Per-round demand paid by the two directions, with real/borrowed counts. -/
inductive Pays : List Nat → List Nat → Nat → Nat → Prop where
  | empty : Pays [] [] 0 0
  | real {x y xs ys r b} (h : 10 ≤ x + y) (prev : Pays xs ys r b) :
      Pays (x :: xs) (y :: ys) (r+1) b
  | borrowed {x y xs ys r b} (h : 17 ≤ x + y) (prev : Pays xs ys r b) :
      Pays (x :: xs) (y :: ys) r (b+1)
  | other {x y xs ys r b} (prev : Pays xs ys r b) :
      Pays (x :: xs) (y :: ys) r b

theorem total_demand {xs ys r b} (h : Pays xs ys r b) :
    10*r + 17*b ≤ xs.sum + ys.sum := by
  induction h with
  | empty => simp
  | real h _ ih => simp only [List.sum_cons]; omega
  | borrowed h _ ih => simp only [List.sum_cons]; omega
  | other _ ih => simp only [List.sum_cons]; omega

structure Certificate (m width : Nat) where
  rounds : Nat
  realCount : Nat
  borrowCount : Nat
  left : List Nat
  right : List Nat
  leftEpochs : Side left
  rightEpochs : Side right
  leftLength : left.length = rounds
  rightLength : right.length = rounds
  reciprocal : Pays left right realCount borrowCount
  terminalCash : 5*rounds ≤ 17*realCount + 5*borrowCount + 5
  topSurvives : m + 3 ≤ rounds
  clique : realCount ≤ width

theorem rational_bound {m width : Nat} (c : Certificate m width) :
    35*m + 20 ≤ 239*width := by
  have hl := side_budget c.leftEpochs
  have hr := side_budget c.rightEpochs
  rw [c.leftLength] at hl
  rw [c.rightLength] at hr
  have hd := total_demand c.reciprocal
  have hcash := c.terminalCash
  have htime := c.topSurvives
  have hclique := c.clique
  have hs : 10*c.realCount + 17*c.borrowCount ≤ 10*c.rounds := by omega
  have hc := Nat.mul_le_mul_left 17 hcash
  have hb := Nat.mul_le_mul_left 5 hs
  omega

/-! ## Intervals and simultaneous column evolution -/


abbrev Interval := Int × Int
def Contains (I : Interval) (x : Int) : Prop := I.1 ≤ x ∧ x ≤ I.2
instance (I : Interval) (x : Int) : Decidable (Contains I x) :=
  inferInstanceAs (Decidable (_ ∧ _))
def Meets (I J : Interval) : Prop := I.1 ≤ J.2 ∧ J.1 ≤ I.2

structure Coloring (intervals : List Interval) (color : Fin intervals.length → Nat) : Prop where
  nonempty : 0 < intervals.length
  valid : ∀ v, (intervals.get v).1 ≤ (intervals.get v).2
  positive : ∀ v, 1 ≤ color v
  proper : ∀ v w, v ≠ w → Meets (intervals.get v) (intervals.get w) → color v ≠ color w
  witness : ∀ v i, 1 ≤ i → i < color v →
    ∃ w, color w = i ∧ Meets (intervals.get v) (intervals.get w)

private theorem fin_mem {n} (v : Fin n) : v ∈ List.finRange n := by
  apply List.mem_iff_getElem.mpr
  exact ⟨v.val, by simp, by simp⟩

private def insertPoint (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys
                else y :: insertPoint x ys

private theorem insert_mem {x y : Int} {xs : List Int} :
    y ∈ insertPoint x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertPoint]
  | cons z zs ih =>
    simp only [insertPoint]
    split
    · simp
    · split
      · subst x; simp [List.mem_cons]
      · simp [List.mem_cons, ih, or_left_comm]

private theorem insert_sorted (x : Int) {xs : List Int} (h : xs.Pairwise (· < ·)) :
    (insertPoint x xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insertPoint]
  | cons y ys ih =>
    obtain ⟨hy,ht⟩ := List.pairwise_cons.mp h
    simp only [insertPoint]
    split
    · rename_i hxy
      apply List.pairwise_cons.mpr ⟨?_,h⟩
      intro z hz
      cases List.mem_cons.mp hz with
      | inl e => simpa [e] using hxy
      | inr hz => exact Int.lt_trans hxy (hy _ hz)
    · split
      · exact h
      · rename_i hne
        apply List.pairwise_cons.mpr ⟨?_,ih ht⟩
        intro z hz
        cases insert_mem.mp hz with
        | inl e => omega
        | inr hz => exact hy _ hz

def endpoints : List Interval → List Int
  | [] => []
  | I :: rest => insertPoint I.1 (endpoints rest)

theorem endpoints_sorted (xs : List Interval) : (endpoints xs).Pairwise (· < ·) := by
  induction xs with
  | nil => exact .nil
  | cons _ _ ih => exact insert_sorted _ ih

private theorem endpoint_mem {I} {xs : List Interval} (h : I ∈ xs) : I.1 ∈ endpoints xs := by
  induction xs with
  | nil => simp at h
  | cons J js ih =>
    apply insert_mem.mpr
    cases List.mem_cons.mp h with
    | inl e => simp [e]
    | inr ht => exact Or.inr (ih ht)

private def biggest : List Nat → Nat
  | [] => 0
  | x :: xs => max x (biggest xs)

private theorem le_biggest {a : Nat} {xs : List Nat} (h : a ∈ xs) : a ≤ biggest xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [biggest]
    cases List.mem_cons.mp h with
    | inl e => omega
    | inr h => have := ih h; omega

private theorem biggest_mem {xs : List Nat} (h : xs ≠ []) : biggest xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp [biggest]
    | cons y ys =>
      have ht := ih (by simp)
      by_cases hx : biggest (y::ys) ≤ x
      · rw [biggest, Nat.max_eq_left hx]; simp
      · rw [biggest, Nat.max_eq_right (by omega)]
        exact List.mem_cons_of_mem _ ht

def height {xs : List Interval} (color : Fin xs.length → Nat) : Nat :=
  biggest ((List.finRange xs.length).map color)

def palette (xs : List Interval) (color : Fin xs.length → Nat) (x : Int) : List Nat :=
  ((List.finRange xs.length).filter (fun v => decide (Contains (xs.get v) x))).map color

def depth (xs : List Interval) : Nat :=
  biggest ((endpoints xs).map fun x =>
    ((List.finRange xs.length).filter fun v => decide (Contains (xs.get v) x)).length)

private theorem palette_spec {xs color x c} : c ∈ palette xs color x ↔
    ∃ v, Contains (xs.get v) x ∧ color v = c := by
  simp [palette, List.mem_map, List.mem_filter, fin_mem]

private theorem color_le {xs : List Interval} (color : Fin xs.length → Nat) (v) : color v ≤ height color :=
  le_biggest (List.mem_map.mpr ⟨v,fin_mem v,rfl⟩)

private theorem attained {xs color} (g : Coloring xs color) : ∃ v, color v = height color := by
  suffices h : height color ∈ (List.finRange xs.length).map color by
    obtain ⟨v,_,hv⟩ := List.mem_map.mp h
    exact ⟨v,hv⟩
  apply biggest_mem
  intro e
  let v : Fin xs.length := ⟨0,g.nonempty⟩
  have h : color v ∈ (List.finRange xs.length).map color := List.mem_map.mpr ⟨v,fin_mem v,rfl⟩
  simp [e] at h

structure Board where
  live : List Int
  cash : Int → Nat

def Between (x z y : Int) := (x < z ∧ z < y) ∨ (y < z ∧ z < x)
instance (x z y : Int) : Decidable (Between x z y) := inferInstanceAs (Decidable (_ ∨ _))
def near (ps : List Int) (x y : Int) : Bool :=
  decide (x ≠ y) && ps.all (fun z => !decide (Between x z y))

private theorem near_spec {ps x y} : near ps x y = true ↔
    x ≠ y ∧ ∀ z ∈ ps, ¬ Between x z y := by simp [near,List.all_eq_true]

private theorem near_swap {ps x y} (h : near ps x y = true) : near ps y x = true := by
  obtain ⟨hn,hb⟩ := near_spec.mp h
  exact near_spec.mpr ⟨Ne.symm hn, fun z hz he => hb z hz (by
    simpa [Between, or_comm] using he)⟩

private theorem near_mono {ps qs : List Int} {x y} (sub : ∀ z ∈ qs, z ∈ ps)
    (h : near ps x y = true) : near qs x y = true := by
  obtain ⟨hn,hb⟩ := near_spec.mp h
  exact near_spec.mpr ⟨hn, fun z hz => hb z (sub z hz)⟩

def directed (left : Bool) (x y : Int) : Bool := if left then decide (y < x) else decide (x < y)
def slot (ps : List Int) (x : Int) (left : Bool) : Option Int :=
  ps.find? fun y => directed left x y && near ps x y

private theorem slot_info {ps x dir y} (e : slot ps x dir = some y) :
    y ∈ ps ∧ directed dir x y = true ∧ near ps x y = true := by
  exact ⟨List.mem_of_find?_eq_some e, by simpa using List.find?_some e⟩

private theorem slot_of {ps x dir y} (hy : y ∈ ps) (hd : directed dir x y = true)
    (hn : near ps x y = true) : slot ps x dir = some y := by
  cases e : slot ps x dir with
  | none =>
    have no := List.find?_eq_none.mp e y hy
    simp [hd,hn] at no
  | some z =>
    obtain ⟨hz,hzdir,hzn⟩ := slot_info e
    have h1 := (near_spec.mp hn).2 z hz
    have h2 := (near_spec.mp hzn).2 y hy
    congr 1
    cases dir <;> simp [directed,Between] at * <;> omega



abbrev Hits := Nat → Int → Bool

def realRows (xs : List Interval) (color : Fin xs.length → Nat) : Hits :=
  fun row x => (palette xs color x).contains row

def borrowedHit (s : Board) (h : Int → Bool) (x : Int) : Bool :=
  s.live.any fun y => near s.live x y && h y

def income (s : Board) (h : Int → Bool) (x : Int) : Nat :=
  if h x then 17 else if borrowedHit s h x then 5 else 0

def keep (s : Board) (h : Int → Bool) (x : Int) : Bool :=
  decide (income s h x ≠ 0 ∨ 5 < s.cash x)

def advance (s : Board) (h : Int → Bool) : Board :=
  ⟨s.live.filter (keep s h), fun x => s.cash x + income s h x - 5⟩

def run (ps : List Int) (hits : Hits) : Nat → Board
  | 0 => ⟨ps,fun _ => 0⟩
  | t+1 => advance (run ps hits t) (hits (t+1))

private theorem income_cases (s h x) : income s h x = 17 ∨ income s h x = 5 ∨ income s h x = 0 := by
  simp only [income]; split <;> simp_all

private theorem alive_step {s h x} : x ∈ (advance s h).live ↔
    x ∈ s.live ∧ (income s h x ≠ 0 ∨ 5 < s.cash x) := by
  simp [advance,List.mem_filter,keep]

private theorem earn_real {s h x} (hr : h x = true) : income s h x = 17 := by simp [income,hr]

private theorem earned_real {s h x} (hr : income s h x = 17) : h x = true := by
  cases e : h x <;> simp [income,e] at *
  split at hr <;> contradiction

private theorem earn_adj {s h x y} (hy : y ∈ s.live) (hn : near s.live x y = true)
    (hr : h y = true) : 5 ≤ income s h x := by
  have hb : borrowedHit s h x = true :=
    List.any_eq_true.mpr ⟨y,hy,by simp [hn,hr]⟩
  simp only [income,hb]; split <;> decide

private theorem borrowed_witness {s h x} (hb : income s h x = 5) :
    ∃ y ∈ s.live, near s.live x y = true ∧ h y = true := by
  have h' : borrowedHit s h x = true := by
    cases e : borrowedHit s h x <;> simp [income,e] at *
    split at hb <;> contradiction
  simpa [borrowedHit,List.any_eq_true] using h'

private theorem live_mono {ps hits t u x} (le : t ≤ u) (hx : x ∈ (run ps hits u).live) :
    x ∈ (run ps hits t).live := by
  induction u with
  | zero =>
    have e : t=0 := by omega
    simpa [e] using hx
  | succ u ih =>
    by_cases e : t=u+1
    · simpa [e] using hx
    · exact ih (by omega) (alive_step.mp hx).1

theorem active_sorted {xs : List Interval} {hits} (t : Nat) :
    (run (endpoints xs) hits t).live.Pairwise (· < ·) := by
  induction t with
  | zero => exact endpoints_sorted xs
  | succ t ih => exact ih.filter _

private def gap (p q : Int) := (max p q - min p q).toNat

private theorem bridge {I J : Interval} {ps : List Int} (meet : Meets I J)
    (p q : Int) (hp : p ∈ ps) (hq : q ∈ ps) (pi : Contains I p) (qj : Contains J q) :
    ∃ x ∈ ps, Contains I x ∧ ∃ y ∈ ps, Contains J y ∧ (x=y ∨ near ps x y = true) := by
  classical
  by_cases e : p=q
  · exact ⟨p,hp,pi,q,hq,qj,Or.inl e⟩
  by_cases hn : near ps p q = true
  · exact ⟨p,hp,pi,q,hq,qj,Or.inr hn⟩
  have ex : ∃ z ∈ ps, Between p z q := by
    apply Classical.byContradiction
    intro no
    exact hn (near_spec.mpr ⟨e,fun z hz hb => no ⟨z,hz,hb⟩⟩)
  obtain ⟨z,hz,hbet⟩ := ex
  have hor : Contains I z ∨ Contains J z := by
    simp only [Contains, Meets, Between] at *; omega
  cases hor with
  | inl zi => exact bridge meet z q hz hq zi qj
  | inr zj => exact bridge meet p z hp hz pi zj
termination_by gap p q
decreasing_by all_goals unfold gap; simp only [Between] at hbet; omega

private theorem covers_step {xs color} (g : Coloring xs color) {s : Board} {i : Nat} (pos : 1 ≤ i)
    (cov : ∀ v, i ≤ color v → ∃ x ∈ s.live, Contains (xs.get v) x) :
    ∀ v, i ≤ color v → ∃ x ∈ (advance s (realRows xs color i)).live, Contains (xs.get v) x := by
  intro v hv
  obtain ⟨p,hp,pi⟩ := cov v hv
  have hit : ∀ w y, Contains (xs.get w) y → color w = i → realRows xs color i y = true := by
    intro w y hy hc
    simpa [realRows] using (palette_spec.mpr ⟨w,hy,hc⟩ : i ∈ palette xs color y)
  by_cases e : color v = i
  · have h17 := earn_real (s:=s) (hit v p pi e)
    exact ⟨p,alive_step.mpr ⟨hp,Or.inl (by omega)⟩,pi⟩
  obtain ⟨w,hw,meet⟩ := g.witness v i pos (by omega)
  obtain ⟨q,hq,qj⟩ := cov w (by omega)
  obtain ⟨x,hx,xi,y,hy,yj,rel⟩ := bridge meet p q hp hq pi qj
  have hr := hit w y yj hw
  apply Exists.intro x
  refine ⟨alive_step.mpr ⟨hx,Or.inl ?_⟩,xi⟩
  cases rel with
  | inl he => subst x; have := earn_real (s:=s) hr; omega
  | inr hn => have := earn_adj (s:=s) hy hn hr; omega

abbrev evolution (xs : List Interval) (color : Fin xs.length → Nat) :=
  run (endpoints xs) (realRows xs color)

theorem coverage {xs color} (g : Coloring xs color) (t : Nat) :
    ∀ v, t ≤ color v → ∃ x ∈ (evolution xs color t).live, Contains (xs.get v) x := by
  induction t with
  | zero =>
    intro v _
    exact ⟨(xs.get v).1,endpoint_mem (xs.get_mem v),Int.le_refl _,g.valid v⟩
  | succ t ih => exact covers_step g (by omega) (fun v hv => ih v (by omega))



private theorem no_hit {xs color i} (late : height color < i) (x) :
    realRows xs color i x = false := by
  cases h : realRows xs color i x with
  | false => rfl
  | true =>
    have hm : i ∈ palette xs color x := by simpa [realRows] using h
    obtain ⟨v,_,e⟩ := palette_spec.mp hm
    have := color_le color v
    omega

private theorem no_pay {xs color i} (late : height color < i) (s : Board) (x) :
    income s (realRows xs color i) x = 0 := by
  simp [income,borrowedHit,no_hit late]

private theorem cash_bound {ps hits} (t x) : (run ps hits t).cash x ≤ 17*t := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    change (run ps hits t).cash x + income _ _ x - 5 ≤ _
    have := income_cases (run ps hits t) (hits (t+1)) x
    omega

private theorem cash_drain {xs color} (n x) :
    (evolution xs color (height color+n)).cash x =
      (evolution xs color (height color)).cash x - 5*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (evolution xs color (height color+n)).cash x +
      income (evolution xs color (height color+n)) (realRows xs color (height color+n+1)) x - 5 = _
    rw [no_pay (by omega : height color < height color+n+1),ih]
    omega

theorem eventual_extinction {xs color} :
    (evolution xs color (height color+17*height color+1)).live = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨_,hk⟩ := alive_step.mp hx
  rw [no_pay (by omega : height color < height color+17*height color+1)] at hk
  change 0 ≠ 0 ∨ 5 < (evolution xs color (height color+17*height color)).cash x at hk
  rw [cash_drain] at hk
  have := cash_bound (ps:=endpoints xs) (hits:=realRows xs color) (height color) x
  change (evolution xs color (height color)).cash x ≤ _ at this
  omega

private theorem death_boundary {f : Nat → List Int} (start : f 0 ≠ []) {t}
    (dead : f t = []) : ∃ k, f k ≠ [] ∧ f (k+1) = [] := by
  induction t with
  | zero => contradiction
  | succ t ih =>
    by_cases e : f t = []
    · exact ih e
    · exact ⟨t,e,dead⟩

theorem top_tail {xs color} (g : Coloring xs color) :
    ∃ x, x ∈ (evolution xs color (height color+2)).live := by
  obtain ⟨v,hv⟩ := attained g
  obtain ⟨x,hx,hi⟩ := coverage g (height color) v (by omega)
  have hr : realRows xs color (height color) x = true := by
    simpa [realRows] using (palette_spec.mpr ⟨v,hi,hv⟩ : height color ∈ palette xs color x)
  have hpos := g.positive v
  have bank : 12 ≤ (evolution xs color (height color)).cash x := by
    cases e : height color with
    | zero => omega
    | succ t =>
      rw [e] at hr
      change 12 ≤ (evolution xs color t).cash x + income _ _ x - 5
      rw [earn_real hr]; omega
  have h1 : x ∈ (evolution xs color (height color+1)).live :=
    alive_step.mpr ⟨hx, Or.inr (show 5 < (evolution xs color (height color)).cash x by omega)⟩
  have bank' : 7 ≤ (evolution xs color (height color+1)).cash x := by
    change 7 ≤ (evolution xs color (height color)).cash x + income _ _ x - 5
    omega
  exact ⟨x,alive_step.mpr ⟨h1,Or.inr (show 5 < (evolution xs color (height color+1)).cash x by omega)⟩⟩

private theorem last_round_bound {xs color t} (g : Coloring xs color)
    (empty : (evolution xs color (t+1)).live = []) : height color+3 ≤ t+1 := by
  obtain ⟨x,hx⟩ := top_tail g
  apply Classical.byContradiction
  intro no
  have he := live_mono (t:=t+1) (by omega) hx
  change x ∈ (evolution xs color (t+1)).live at he
  rw [empty] at he; contradiction

theorem terminal_exists {xs color} (g : Coloring xs color) :
    ∃ t, (evolution xs color t).live ≠ [] ∧ (evolution xs color (t+1)).live = [] ∧
      height color + 3 ≤ t+1 := by
  obtain ⟨x,hx⟩ := top_tail g
  have h0 := live_mono (t:=0) (by omega) hx
  have start : (evolution xs color 0).live ≠ [] := by
    intro e; rw [e] at h0; contradiction
  obtain ⟨t,ht,hd⟩ := death_boundary (f:=fun i => (evolution xs color i).live) start
    (eventual_extinction (xs:=xs) (color:=color))
  exact ⟨t,ht,hd,last_round_bound g hd⟩



private theorem slot_stays {s h x dir y} (cur : slot s.live x dir = some y)
    (hy : y ∈ (advance s h).live) : slot (advance s h).live x dir = some y := by
  obtain ⟨_,hd,hn⟩ := slot_info cur
  exact slot_of hy hd (near_mono (fun _ hz => (alive_step.mp hz).1) hn)

def sideIncome (s : Board) (h : Int → Bool) (x : Int) (dir : Bool) : Nat :=
  match slot s.live x dir with
  | none => if h x then 5 else 0
  | some y => income s h y

private def rows (f : Nat → Nat) (t : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => f t :: rows f (t+1) n

private theorem rows_length (f t n) : (rows f t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [rows,ih]

def sideTrace (ps : List Int) (hits : Hits) (x : Int) (dir : Bool) :=
  rows fun t => sideIncome (run ps hits t) (hits (t+1)) x dir

/-- The open first epoch carries the actual opening balance of its occupant. -/
private def Plan (opening : Option Nat) (xs : List Nat) : Prop :=
  match opening with
  | none => Side xs
  | some c => ∃ es tail, xs = es ++ tail ∧ EndsInDeath c es ∧ Side tail

private theorem Plan.closed {o xs} (h : Plan o xs) : Side xs := by
  cases o with
  | none => exact h
  | some c =>
    obtain ⟨es,tail,rfl,hd,ht⟩ := h
    exact .append (.occupied hd) ht

private theorem slot_plan (ps hits x dir t n)
    (endEmpty : (run ps hits (t+n)).live = []) :
    Plan ((slot (run ps hits t).live x dir).map (run ps hits t).cash)
      (sideTrace ps hits x dir t n) := by
  induction n generalizing t with
  | zero =>
    simp only [Nat.add_zero] at endEmpty
    simp [endEmpty,slot,Plan,sideTrace,rows,Side.empty]
  | succ n ih =>
    let s := run ps hits t
    let h := hits (t+1)
    let next := advance s h
    let rest := sideTrace ps hits x dir (t+1) n
    have nxt : Plan ((slot next.live x dir).map next.cash) rest := ih (t+1) (by
      rw [show t+1+n=t+(n+1) by omega]; exact endEmpty)
    change Plan ((slot s.live x dir).map s.cash) (sideIncome s h x dir :: rest)
    cases cur : slot s.live x dir with
    | none =>
      change Side (sideIncome s h x dir :: rest)
      have v : sideIncome s h x dir ≤ 5 := by simp [sideIncome,cur]; split <;> decide
      exact Side.append (xs:=[sideIncome s h x dir]) (.vacant (by simpa using v)) nxt.closed
    | some y =>
      simp only [Option.map_some,sideIncome,cur]
      obtain ⟨hy,_,_⟩ := slot_info cur
      by_cases alive : y ∈ next.live
      · have stable : slot next.live x dir = some y := slot_stays cur alive
        rw [stable] at nxt
        obtain ⟨es,tail,eqn,hd,ht⟩ := nxt
        obtain ⟨_,hk⟩ := alive_step.mp alive
        change income s h y ≠ 0 ∨ 5 < s.cash y at hk
        have hc := income_cases s h y
        refine ⟨income s h y :: es,tail,by simp [eqn],?_,ht⟩
        exact EndsInDeath.step (by omega) hd
      · have nd : ¬(income s h y ≠ 0 ∨ 5 < s.cash y) :=
          fun e => alive (alive_step.mpr ⟨hy,e⟩)
        have zero : income s h y = 0 := by omega
        rw [zero]
        exact ⟨[0],rest,rfl,EndsInDeath.die (by omega),nxt.closed⟩

private theorem real_side {s h x} (hx : x ∈ s.live) (rx : h x = true) (dir) :
    5 ≤ sideIncome s h x dir := by
  cases e : slot s.live x dir with
  | none => simp [sideIncome,e,rx]
  | some y =>
    obtain ⟨_,_,hn⟩ := slot_info e
    simpa [sideIncome,e] using earn_adj hx (near_swap hn) rx

private theorem borrow_sides {s h x} (hb : income s h x = 5) :
    17 ≤ sideIncome s h x true + sideIncome s h x false := by
  obtain ⟨y,hy,hn,hr⟩ := borrowed_witness hb
  have hne := (near_spec.mp hn).1
  by_cases lt : y < x
  · have e := slot_of (dir:=true) hy (by simp [directed,lt]) hn
    have a : sideIncome s h x true = 17 := by simp [sideIncome,e,earn_real hr]
    omega
  · have gt : x < y := by omega
    have e := slot_of (dir:=false) hy (by simp [directed,gt]) hn
    have a : sideIncome s h x false = 17 := by simp [sideIncome,e,earn_real hr]
    omega



private def tally (p : Nat → Bool) (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if p t then tally p (t+1) n + 1 else tally p (t+1) n

def reals (hits : Hits) (x : Int) := tally fun t => hits (t+1) x
def borrows (ps : List Int) (hits : Hits) (x : Int) :=
  tally fun t => decide (income (run ps hits t) (hits (t+1)) x = 5)

private def AliveThrough (ps : List Int) (hits : Hits) (x : Int) (t n : Nat) :=
  ∀ j, j < n → x ∈ (run ps hits (t+j)).live

private theorem alive_tail {ps hits x t n} (h : AliveThrough ps hits x t (n+1)) :
    AliveThrough ps hits x (t+1) n := by
  intro j hj
  rw [show t+1+j=t+(j+1) by omega]
  exact h _ (by omega)

private theorem trace_pays (ps hits x t n) (h : AliveThrough ps hits x t n) :
    Pays (sideTrace ps hits x true t n) (sideTrace ps hits x false t n)
      (reals hits x t n) (borrows ps hits x t n) := by
  induction n generalizing t with
  | zero => exact .empty
  | succ n ih =>
    have past := ih (t+1) (alive_tail h)
    have hx : x ∈ (run ps hits t).live := by simpa using h 0 (by omega)
    let s := run ps hits t
    let hit := hits (t+1)
    change Pays (sideIncome s hit x true :: _) (sideIncome s hit x false :: _)
      (if hit x then reals hits x (t+1) n+1 else reals hits x (t+1) n)
      (if decide (income s hit x = 5) then borrows ps hits x (t+1) n+1 else borrows ps hits x (t+1) n)
    simp only [decide_eq_true_eq]
    cases hr : hit x with
    | true =>
      have e := earn_real (s:=s) hr
      have l := real_side (s:=s) hx hr true
      have r := real_side (s:=s) hx hr false
      simp [e]
      exact .real (by omega) past
    | false =>
      by_cases e : income s hit x = 5
      · simpa [e] using Pays.borrowed (borrow_sides e) past
      · simpa [e] using Pays.other (x:=sideIncome s hit x true) (y:=sideIncome s hit x false) past

private theorem own_account (ps hits x t n) (h : AliveThrough ps hits x t n) :
    5*n ≤ (run ps hits t).cash x + 17*reals hits x t n + 5*borrows ps hits x t n + 5 := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    by_cases nz : n=0
    · omega
    have tail := alive_tail h
    have hx : x ∈ (run ps hits (t+1)).live := by simpa using tail 0 (by omega)
    have hk := (alive_step.mp hx).2
    let s := run ps hits t
    let hit := hits (t+1)
    have budget := ih (t+1) tail
    change 5*n ≤ (s.cash x + income s hit x - 5) + _ + _ + 5 at budget
    change income s hit x ≠ 0 ∨ 5 < s.cash x at hk
    change 5*(n+1) ≤ s.cash x +
      17*(if hit x then reals hits x (t+1) n+1 else reals hits x (t+1) n) +
      5*(if decide (income s hit x = 5) then borrows ps hits x (t+1) n+1 else borrows ps hits x (t+1) n) + 5
    simp only [decide_eq_true_eq]
    cases hr : hit x with
    | true =>
      have he := earn_real (s:=s) hr
      simp [he] at budget ⊢
      omega
    | false =>
      by_cases hb : income s hit x = 5
      · simp [hb] at budget ⊢; omega
      · have hc := income_cases s hit x
        have not17 : income s hit x ≠ 17 := fun e => Bool.noConfusion (hr.symm.trans (earned_real e))
        have zero : income s hit x = 0 := by omega
        simp [zero] at budget ⊢; omega

private def above (xs : List Nat) (t : Nat) := (xs.filter (fun c => decide (t < c))).length

private theorem above_step (xs : List Nat) (t : Nat) :
    above xs (t+1) + (if t+1 ∈ xs then 1 else 0) ≤ above xs t := by
  induction xs with
  | nil => simp [above]
  | cons c xs ih =>
    by_cases eq : c=t+1
    · subst c
      simpa [above,List.filter_cons,Nat.lt_succ_self] using
        (show above xs (t+1) ≤ above xs t by omega)
    · by_cases lt : t+1 < c
      · have lt' : t < c := by omega
        simp [above,List.filter_cons,lt,lt',List.mem_cons,Ne.symm eq] at ih ⊢
        omega
      · have lt' : ¬t<c := by omega
        simpa [above,List.filter_cons,lt,lt',List.mem_cons,Ne.symm eq] using ih

private theorem real_budget (xs color x t n) :
    reals (realRows xs color) x t n ≤ above (palette xs color x) t := by
  induction n generalizing t with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := ih (t+1)
    simp [reals,realRows] at h
    have p := above_step (palette xs color x) t
    by_cases mem : t+1 ∈ palette xs color x
    · simp [reals,tally,realRows,mem]
      simp [mem] at p
      exact Nat.le_trans (Nat.add_le_add_right h 1) p
    · simp [reals,tally,realRows,mem]
      simp [mem] at p
      exact Nat.le_trans h p

private theorem reals_le_depth {xs color x n} (hx : x ∈ endpoints xs) :
    reals (realRows xs color) x 0 n ≤ depth xs := by
  have h := real_budget xs color x 0 n
  have bound : above (palette xs color x) 0 ≤ (palette xs color x).length :=
    List.length_filter_le ..
  apply Nat.le_trans (Nat.le_trans h bound)
  simp only [palette,List.length_map,depth]
  exact le_biggest (List.mem_map.mpr ⟨x,hx,rfl⟩)



/-- A certificate for any column active immediately before the first empty state. -/
def certificateAt {xs color} (g : Coloring xs color) (t : Nat) (x : Int)
    (hx : x ∈ (evolution xs color t).live) (empty : (evolution xs color (t+1)).live = []) :
    Certificate (height color) (depth xs) := by
  let ps := endpoints xs
  let hits := realRows xs color
  have alive : AliveThrough ps hits x 0 (t+1) := by
    intro j hj
    exact live_mono (by omega : 0+j ≤ t) hx
  have initial : x ∈ ps := by simpa [run] using alive 0 (by omega)
  exact {
    rounds := t+1
    realCount := reals hits x 0 (t+1)
    borrowCount := borrows ps hits x 0 (t+1)
    left := sideTrace ps hits x true 0 (t+1)
    right := sideTrace ps hits x false 0 (t+1)
    leftEpochs := (slot_plan ps hits x true 0 (t+1) (by simpa using empty)).closed
    rightEpochs := (slot_plan ps hits x false 0 (t+1) (by simpa using empty)).closed
    leftLength := rows_length ..
    rightLength := rows_length ..
    reciprocal := trace_pays ps hits x 0 (t+1) alive
    terminalCash := by simpa [run] using own_account ps hits x 0 (t+1) alive
    topSurvives := last_round_bound g empty
    clique := reals_le_depth initial
  }

private def scanToDeath {xs color} (g : Coloring xs color) (fuel t : Nat)
    (live : (evolution xs color t).live ≠ [])
    (dead : (evolution xs color (t+fuel)).live = []) :
    Certificate (height color) (depth xs) := by
  cases fuel with
  | zero => exact False.elim (live (by simpa using dead))
  | succ f =>
    by_cases e : (evolution xs color (t+1)).live = []
    · exact certificateAt g t _ (List.head_mem live) e
    · exact scanToDeath g f (t+1) e (by rw [show t+1+f=t+(f+1) by omega]; exact dead)
termination_by fuel

/-- Select the first column of the last nonempty state and return its certificate. -/
def intervalCertificate {xs color} (g : Coloring xs color) :
    Certificate (height color) (depth xs) := by
  apply scanToDeath g (height color + 17*height color + 1) 0
  · intro e
    let v : Fin xs.length := ⟨0,g.nonempty⟩
    have mem := endpoint_mem (xs.get_mem v)
    change endpoints xs = [] at e
    rw [e] at mem; contradiction
  · simpa using (eventual_extinction (xs:=xs) (color:=color))


end ReciprocalColumns

/-- The First-Fit height of a nonempty closed-interval wall obeys the rational
bound, with d the maximum stabbing depth at its left endpoints. -/
theorem first_fit_interval_rational_bound
    (intervals : List (Int × Int)) (color : Fin intervals.length → Nat)
    (g : ReciprocalColumns.Coloring intervals color) :
    35 * ReciprocalColumns.height color + 20 ≤ 239 * ReciprocalColumns.depth intervals :=
  ReciprocalColumns.rational_bound (ReciprocalColumns.intervalCertificate g)

#print axioms first_fit_interval_rational_bound
