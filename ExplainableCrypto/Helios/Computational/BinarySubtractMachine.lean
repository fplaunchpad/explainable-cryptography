import ExplainableCrypto.Helios.Computational.UniformOperandCodec
import ExplainableCrypto.Helios.Computational.TM2ReturnLink
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic.Linarith

/-! One guarded subtraction for binary long division. The modulus is retained;
underflow returns the original operand. This is not the complete modulo sampler. -/
namespace ExplainableCrypto.Helios.Computational.BinarySubtractMachine
open Turing.TM2

private def digit (a b carry : Bool) : Bool := xor (xor a b) carry
private def borrow (a b carry : Bool) : Bool := (!a && b) || (!(xor a b) && carry)

private def difference : List Bool → List Bool → Bool → List Bool × Bool
  | [],[],c => ([],c)
  | a::xs,[],c => let r := difference xs [] (borrow a false c); (digit a false c :: r.1,r.2)
  | [],b::ys,c => let r := difference [] ys (borrow false b c); (digit false b c :: r.1,r.2)
  | a::xs,b::ys,c => let r := difference xs ys (borrow a b c); (digit a b c :: r.1,r.2)
termination_by xs ys _ => xs.length+ys.length

private theorem difference_length (xs ys : List Bool) (c : Bool) :
    (difference xs ys c).1.length = max xs.length ys.length := by
  fun_induction difference xs ys c <;>
    simp_all [List.length_cons, Nat.succ_max_succ] <;> assumption

private theorem digit_balance (a b c : Bool) :
    a.toNat + 2*(borrow a b c).toNat = (digit a b c).toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem difference_balance (xs ys : List Bool) (c : Bool) :
    bitsValue xs + 2^(max xs.length ys.length)*(difference xs ys c).2.toNat =
      bitsValue (difference xs ys c).1 + bitsValue ys+c.toNat := by
  fun_induction difference xs ys c with
  | case1 c => cases c <;> rfl
  | case2 a xs c r ih =>
    have h := digit_balance a false c
    simp only [List.length_cons,List.length_nil,Nat.max_zero,Nat.pow_succ] at *
    change Nat.bit a (bitsValue xs) + (2^xs.length*2)*(difference xs [] (borrow a false c)).2.toNat =
      Nat.bit (digit a false c) (bitsValue (difference xs [] (borrow a false c)).1)+0+c.toNat
    simp only [Nat.bit_val, Bool.toNat_false, bitsValue, List.foldr_nil] at *
    nlinarith
  | case3 b ys c r ih =>
    have h := digit_balance false b c
    simp only [List.length_cons,List.length_nil,Nat.zero_max,Nat.pow_succ] at *
    change 0+(2^ys.length*2)*(difference [] ys (borrow false b c)).2.toNat =
      Nat.bit (digit false b c) (bitsValue (difference [] ys (borrow false b c)).1)+Nat.bit b (bitsValue ys)+c.toNat
    simp only [Nat.bit_val, Bool.toNat_false, bitsValue, List.foldr_nil] at *
    nlinarith
  | case4 a xs b ys c r ih =>
    have h := digit_balance a b c
    simp only [List.length_cons,Nat.succ_max_succ,Nat.pow_succ] at *
    change Nat.bit a (bitsValue xs) + (2^(max xs.length ys.length)*2)*(difference xs ys (borrow a b c)).2.toNat =
      Nat.bit (digit a b c) (bitsValue (difference xs ys (borrow a b c)).1)+Nat.bit b (bitsValue ys)+c.toNat
    simp only [Nat.bit_val, bitsValue] at *
    nlinarith

inductive Stack where
  | left | right | diff | savedLeft | savedRight | out
  deriving DecidableEq
open Stack
instance : Fintype Stack where
  elems := {left,right,diff,savedLeft,savedRight,out}
  complete s := by cases s <;> simp
inductive Label where
  | scan (carry : Bool) | restoreRight (carry : Bool) | shift (bit : Bool)
  | clearDiff | restoreLeft | clearLeft | trim | reverse
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨scan false⟩
instance : Fintype Label where
  elems := {scan false,scan true,restoreRight false,restoreRight true,shift false,shift true,
    clearDiff,restoreLeft,clearLeft,trim,reverse}
  complete l := by cases l <;> simp
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def emit (a c : Bool) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .push diff (fun b => digit a (b.getD false) c)
    (.goto (fun b => scan (borrow a (b.getD false) c)))
private def readRight (a : Option Bool) (c : Bool) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop right (fun _ b => b) <| .branch Option.isSome
    (.push savedRight (fun b => b.getD false) (emit (a.getD false) c))
    (if a.isSome then emit (a.getD false) c else .goto (fun _ => restoreRight c))

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | shift b => .peek left (fun _ a => a) <| .branch (fun a => a.isSome || b)
      (.push left (fun _ => b) (.goto (fun _ => scan false))) (.goto (fun _ => scan false))
  | scan c => .pop left (fun _ a => a) <| .branch Option.isSome
      (.push savedLeft (fun a => a.getD false) <| .branch (fun a => a.getD false)
        (readRight (some true) c) (readRight (some false) c)) (readRight none c)
  | restoreRight c => .pop savedRight (fun _ b => b) <| .branch Option.isSome
      (.push right (fun b => b.getD false) (.goto (fun _ => restoreRight c)))
      (.goto (fun _ => if c then clearDiff else clearLeft))
  | clearDiff => .pop diff (fun _ b => b) <| .branch Option.isSome
      (.goto (fun _ => clearDiff)) (.goto (fun _ => restoreLeft))
  | restoreLeft => .pop savedLeft (fun _ b => b) <| .branch Option.isSome
      (.push out (fun b => b.getD false) (.goto (fun _ => restoreLeft)))
      (.load (fun _ => some false) .halt)
  | clearLeft => .pop savedLeft (fun _ b => b) <| .branch Option.isSome
      (.goto (fun _ => clearLeft)) (.goto (fun _ => trim))
  | trim => .peek diff (fun _ b => b) <| .branch (fun b => decide (b = some false))
      (.pop diff (fun _ b => b) (.goto (fun _ => trim))) (.goto (fun _ => reverse))
  | reverse => .pop diff (fun _ b => b) <| .branch Option.isSome
      (.push out (fun b => b.getD false) (.goto (fun _ => reverse)))
      (.load (fun _ => some true) .halt)

def tick (c : Config) : Config := (step program c).getD c

def state (phase : Option Label) (x y d sx sy result : List Bool) (v : Option Bool := none) : Config :=
  ⟨phase,v,fun | left => x | right => y | diff => d | savedLeft => sx | savedRight => sy | out => result⟩

theorem supports : Supports program Finset.univ := by
  constructor
  · simp
  · intro l _; cases l <;> simp [program,readRight,emit,SupportsStmt]

private theorem scan_left (a : Bool) (xs d sx sy : List Bool) (c : Bool) (v : Option Bool) :
    tick (state (some (scan c)) (a::xs) [] d sx sy [] v) =
      state (some (scan (borrow a false c))) xs [] (digit a false c::d) (a::sx) sy [] none := by
  cases a <;> cases c <;> simp [tick,state,program,readRight,emit,digit,borrow]
  all_goals funext k; cases k <;> rfl

private theorem scan_right (b : Bool) (ys d sx sy : List Bool) (c : Bool) (v : Option Bool) :
    tick (state (some (scan c)) [] (b::ys) d sx sy [] v) =
      state (some (scan (borrow false b c))) [] ys (digit false b c::d) sx (b::sy) [] (some b) := by
  cases b <;> cases c <;> simp [tick,state,program,readRight,emit,digit,borrow]
  all_goals funext k; cases k <;> rfl

private theorem scan_both (a b : Bool) (xs ys d sx sy : List Bool) (c : Bool) (v : Option Bool) :
    tick (state (some (scan c)) (a::xs) (b::ys) d sx sy [] v) =
      state (some (scan (borrow a b c))) xs ys (digit a b c::d) (a::sx) (b::sy) [] (some b) := by
  cases a <;> cases b <;> cases c <;> simp [tick,state,program,readRight,emit,digit,borrow]
  all_goals funext k; cases k <;> rfl

private theorem scan_run (xs ys : List Bool) (c : Bool) (d sx sy : List Bool) (v : Option Bool) :
    tick^[max xs.length ys.length+1] (state (some (scan c)) xs ys d sx sy [] v) =
      state (some (restoreRight (difference xs ys c).2)) [] []
        ((difference xs ys c).1.reverse++d) (xs.reverse++sx) (ys.reverse++sy) [] none := by
  fun_induction difference xs ys c generalizing d sx sy v with
  | case1 c => simp [tick,state,program,readRight]
  | case2 a xs c r ih =>
    simp only [List.length_cons,List.length_nil,Nat.max_zero] at ih ⊢
    rw [Function.iterate_succ_apply,scan_left,ih]
    simp [r,List.reverse_cons,List.append_assoc]
  | case3 b ys c r ih =>
    simp only [List.length_cons,List.length_nil,Nat.zero_max] at ih ⊢
    rw [Function.iterate_succ_apply,scan_right,ih]
    simp [r,List.reverse_cons,List.append_assoc]
  | case4 a xs b ys c r ih =>
    simp only [List.length_cons,Nat.succ_max_succ]
    rw [Function.iterate_succ_apply,scan_both,ih]
    simp [r,List.reverse_cons,List.append_assoc]

private theorem restore_right_run (y d sx sy : List Bool) (c : Bool) (v : Option Bool) :
    tick^[sy.length+1] (state (some (restoreRight c)) [] y d sx sy [] v) =
      state (some (if c then clearDiff else clearLeft)) [] (sy.reverse++y) d sx [] [] none := by
  induction sy generalizing y v with
  | nil => simp [tick,state,program]
  | cons b sy ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : tick (state (some (restoreRight c)) [] y d sx (b::sy) [] v) =
        state (some (restoreRight c)) [] (b::y) d sx sy [] (some b) := by
      simp [tick,state,program]; funext k; cases k <;> rfl
    rw [hs,ih]; simp

private theorem clear_diff_run (y d sx : List Bool) (v : Option Bool) :
    tick^[d.length+1] (state (some clearDiff) [] y d sx [] [] v) =
      state (some restoreLeft) [] y [] sx [] [] none := by
  induction d generalizing v with
  | nil => simp [tick,state,program]
  | cons b d ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : tick (state (some clearDiff) [] y (b::d) sx [] [] v) =
        state (some clearDiff) [] y d sx [] [] (some b) := by
      simp [tick,state,program]; funext k; cases k <;> rfl
    rw [hs,ih]

private theorem restore_left_run (y sx result : List Bool) (v : Option Bool) :
    tick^[sx.length+1] (state (some restoreLeft) [] y [] sx [] result v) =
      state none [] y [] [] [] (sx.reverse++result) (some false) := by
  induction sx generalizing result v with
  | nil => simp [tick,state,program]
  | cons b sx ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : tick (state (some restoreLeft) [] y [] (b::sx) [] result v) =
        state (some restoreLeft) [] y [] sx [] (b::result) (some b) := by
      simp [tick,state,program]; funext k; cases k <;> rfl
    rw [hs,ih]; simp

private theorem clear_left_run (y d sx : List Bool) (v : Option Bool) :
    tick^[sx.length+1] (state (some clearLeft) [] y d sx [] [] v) =
      state (some trim) [] y d [] [] [] none := by
  induction sx generalizing v with
  | nil => simp [tick,state,program]
  | cons b sx ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : tick (state (some clearLeft) [] y d (b::sx) [] [] v) =
        state (some clearLeft) [] y d sx [] [] (some b) := by
      simp [tick,state,program]; funext k; cases k <;> rfl
    rw [hs,ih]

private theorem trim_run (y d : List Bool) (v : Option Bool) :
    ∃ fuel, fuel+(d.dropWhile (! ·)).length = d.length+1 ∧
      tick^[fuel] (state (some trim) [] y d [] [] [] v) =
        state (some reverse) [] y (d.dropWhile (! ·)) [] [] [] (d.dropWhile (! ·)).head? := by
  induction d generalizing v with
  | nil => exact ⟨1,rfl,rfl⟩
  | cons b d ih =>
    cases b with
    | true => exact ⟨1,by simp; omega,rfl⟩
    | false =>
      obtain ⟨u,hu,hr⟩ := ih (some false)
      refine ⟨u+1,by change u+1+(d.dropWhile (! ·)).length = d.length+1+1; omega,?_⟩
      rw [Function.iterate_succ_apply]
      have hs : tick (state (some trim) [] y (false::d) [] [] [] v) =
          state (some trim) [] y d [] [] [] (some false) := by
        simp [tick,state,program]; funext k; cases k <;> rfl
      rw [hs,hr]; rfl

private theorem reverse_run (y d result : List Bool) (v : Option Bool) :
    tick^[d.length+1] (state (some reverse) [] y d [] [] result v) =
      state none [] y [] [] [] (d.reverse++result) (some true) := by
  induction d generalizing result v with
  | nil => simp [tick,state,program]
  | cons b d ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : tick (state (some reverse) [] y (b::d) [] [] result v) =
        state (some reverse) [] y d [] [] (b::result) (some b) := by
      simp [tick,state,program]; funext k; cases k <;> rfl
    rw [hs,ih]; simp

private theorem bitsValue_lt (xs : List Bool) : bitsValue xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    change Nat.bit b (bitsValue xs) < 2^(xs.length+1)
    cases b <;> simp only [Nat.bit_val,Bool.toNat_false,Bool.toNat_true,Nat.pow_succ] <;> omega

private theorem trim_bits (xs : List Bool) :
    (xs.reverse.dropWhile (! ·)).reverse = (bitsValue xs).bits := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    by_cases hz : bitsValue xs = 0
    · have hr : xs.reverse.dropWhile (! ·) = [] := by
        apply List.reverse_eq_nil_iff.mp
        rw [ih,hz]; rfl
      rw [List.reverse_cons,List.dropWhile_append,hr]
      change _ = (Nat.bit b (bitsValue xs)).bits
      rw [hz]
      cases b <;> simp [Nat.bit_val]
    · have hr : (xs.reverse.dropWhile (! ·)).isEmpty ≠ true := by
        intro he
        have he' : xs.reverse.dropWhile (! ·) = [] := List.isEmpty_iff.mp he
        rw [he'] at ih
        have hv := congrArg bitsValue ih
        rw [bitsValue_bits] at hv
        exact hz hv.symm
      rw [List.reverse_cons,List.dropWhile_append,if_neg hr,List.reverse_append]
      change b :: (xs.reverse.dropWhile (! ·)).reverse = (Nat.bit b (bitsValue xs)).bits
      rw [ih,Nat.bits_append_bit _ _ (by intro h; exact (hz h).elim)]

private theorem difference_borrow (xs ys : List Bool) :
    (difference xs ys false).2 = decide (bitsValue xs < bitsValue ys) := by
  have hx := (bitsValue_lt xs).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left xs.length ys.length))
  have hd := bitsValue_lt (difference xs ys false).1
  rw [difference_length] at hd
  have h := difference_balance xs ys false
  cases hb : (difference xs ys false).2 <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at h
  · exact (show false = decide (bitsValue xs < bitsValue ys) by simp; omega)
  · exact (show true = decide (bitsValue xs < bitsValue ys) by simp; omega)

private theorem difference_value (xs ys : List Bool) (h : bitsValue ys ≤ bitsValue xs) :
    bitsValue (difference xs ys false).1 = bitsValue xs-bitsValue ys := by
  have hb := difference_borrow xs ys
  have hv := difference_balance xs ys false
  simp only [hb,show ¬bitsValue xs < bitsValue ys from by omega,decide_false,
    Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hv
  omega

/-- For all bit words, the actual program preserves the modulus, clears scratch,
and returns the canonical difference on success or the exact original left word
on underflow. Fuel is linear in loaded bit lengths, not represented values. -/
theorem run (xs ys : List Bool) :
    ∃ fuel ≤ 3*(xs.length+ys.length)+5,
      tick^[fuel] (state (some (scan false)) xs ys [] [] [] []) =
        state none [] ys [] [] []
          (if bitsValue ys ≤ bitsValue xs then (bitsValue xs-bitsValue ys).bits else xs)
          (some (decide (bitsValue ys ≤ bitsValue xs))) := by
  let r := difference xs ys false
  have hlen : r.1.length = max xs.length ys.length := difference_length xs ys false
  have before : tick^[(ys.length+1)+(max xs.length ys.length+1)]
      (state (some (scan false)) xs ys [] [] [] []) =
      state (some (if r.2 then clearDiff else clearLeft)) [] ys r.1.reverse xs.reverse [] [] none := by
    rw [Function.iterate_add_apply,scan_run]
    simp only [List.append_nil]
    rw [show ys.length = ys.reverse.length from List.length_reverse.symm,restore_right_run]
    simp [r]
  by_cases h : bitsValue ys ≤ bitsValue xs
  · have hb : r.2 = false := by simpa [r,show ¬bitsValue xs < bitsValue ys from by omega] using difference_borrow xs ys
    rw [hb] at before
    simp only [Bool.false_eq_true,if_false] at before
    obtain ⟨u,hu,ht⟩ := trim_run ys r.1.reverse none
    have ha : tick^[xs.length+1] (state (some clearLeft) [] ys r.1.reverse xs.reverse [] [] none) =
        state (some trim) [] ys r.1.reverse [] [] [] none := by
      simpa only [List.length_reverse] using clear_left_run ys r.1.reverse xs.reverse none
    let d := r.1.reverse.dropWhile (! ·)
    refine ⟨(d.length+1)+(u+((xs.length+1)+((ys.length+1)+(max xs.length ys.length+1)))),?_,?_⟩
    · dsimp only [d]; simp only [List.length_reverse,hlen] at hu; omega
    · rw [Function.iterate_add_apply tick (d.length+1),
        Function.iterate_add_apply tick u,
        Function.iterate_add_apply tick (xs.length+1),before,ha,ht,reverse_run]
      simp only [List.append_nil]
      have he : d.reverse = (bitsValue xs-bitsValue ys).bits := by
        rw [trim_bits,difference_value xs ys h]
      simp [h,d,he] at *
  · have hb : r.2 = true := by simpa [r,show bitsValue xs < bitsValue ys from by omega] using difference_borrow xs ys
    rw [hb] at before
    simp only [if_true] at before
    refine ⟨(xs.length+1)+((r.1.length+1)+((ys.length+1)+(max xs.length ys.length+1))),?_,?_⟩
    · rw [hlen]; omega
    · rw [Function.iterate_add_apply tick (xs.length+1),
        Function.iterate_add_apply tick (r.1.length+1),before]
      rw [show r.1.length = r.1.reverse.length from List.length_reverse.symm,clear_diff_run]
      rw [show xs.length = xs.reverse.length from List.length_reverse.symm,restore_left_run]
      simp [h]

private theorem shift_step (r q : Nat) (b : Bool) :
    tick (state (some (shift b)) r.bits q.bits [] [] [] []) =
      state (some (scan false)) (Nat.bit b r).bits q.bits [] [] [] [] r.bits.head? := by
  by_cases hr : r = 0
  · subst r; cases b <;> simp [tick,state,program,Nat.bit_val]
    all_goals funext k; cases k <;> rfl
  · have hn : r.bits ≠ [] := by
      intro h; have hv := congrArg bitsValue h
      rw [bitsValue_bits] at hv
      exact hr hv
    rw [Nat.bits_append_bit _ _ (by intro h; exact (hr h).elim)]
    cases hb : r.bits with
    | nil => exact (hn hb).elim
    | cons a bs =>
      simp [tick,state,program]
      funext k; cases k <;> rfl

/-- One actual binary long-division update, including the shift/zero case.
The next remainder is canonical and the modulus is retained for reuse. -/
theorem remainder_step (r q : Nat) (b : Bool) (hr : r < q) :
    ∃ fuel ≤ 6*q.size+9,
      tick^[fuel] (state (some (shift b)) r.bits q.bits [] [] [] []) =
        state none [] q.bits [] [] [] ((Nat.bit b r)%q).bits
          (some (decide (q ≤ Nat.bit b r))) := by
  have hx : Nat.bit b r < 2*q := by cases b <;> simp only [Nat.bit_val,Bool.toNat_false,Bool.toNat_true] <;> omega
  have hs : (Nat.bit b r).size ≤ q.size+1 := by
    apply Nat.size_le.mpr
    have hq := Nat.lt_size_self q
    rw [Nat.pow_succ]
    omega
  have hm : (if q ≤ Nat.bit b r then Nat.bit b r-q else Nat.bit b r) = (Nat.bit b r)%q := by
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega : Nat.bit b r-q < q)]
    · exact (Nat.mod_eq_of_lt (by omega)).symm
  obtain ⟨u,hu,h⟩ := run (Nat.bit b r).bits q.bits
  simp only [bitsValue_bits,Nat.size_eq_bits_len] at hu h
  refine ⟨u+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,shift_step]
  have hv : ∀ v, tick (state (some (scan false)) (Nat.bit b r).bits q.bits [] [] [] [] v) =
      tick (state (some (scan false)) (Nat.bit b r).bits q.bits [] [] [] [] none) := by
    intro v; rfl
  have he : ∀ v, tick^[u] (state (some (scan false)) (Nat.bit b r).bits q.bits [] [] [] [] v) =
      tick^[u] (state (some (scan false)) (Nat.bit b r).bits q.bits [] [] [] [] none) := by
    intro v
    cases u with
    | zero =>
      have hf := congrArg Cfg.l h
      cases hf
    | succ u => rw [Function.iterate_succ_apply,Function.iterate_succ_apply,hv]
  rw [he,h]
  have hbits : (if q ≤ Nat.bit b r then (Nat.bit b r-q).bits else (Nat.bit b r).bits) =
      ((Nat.bit b r)%q).bits := by
    split_ifs with hc <;> exact congrArg Nat.bits (by simpa [hc] using hm)
  rw [hbits]

/-- Eight minus one propagates borrow through three zero bits. -/
theorem borrow_control :
    ∃ fuel ≤ 20, tick^[fuel] (state (some (scan false)) [false,false,false,true] [true] [] [] [] []) =
      state none [] [true] [] [] [] [true,true,true] (some true) := by
  have hd : (7 : Nat).bits = [true,true,true] := by decide
  simpa [bitsValue, Nat.bit_val, hd] using run [false,false,false,true] [true]

/-- Underflow preserves the literal left word, including high zero padding. -/
theorem underflow_control :
    ∃ fuel ≤ 20, tick^[fuel] (state (some (scan false)) [true,false,false] [false,true] [] [] [] []) =
      state none [] [false,true] [] [] [] [true,false,false] (some false) := by
  simpa [bitsValue, Nat.bits, Nat.bit_val] using run [true,false,false] [false,true]

/-- Equality succeeds with zero output; unequal word lengths do not affect value. -/
theorem equal_control :
    ∃ fuel ≤ 20, tick^[fuel] (state (some (scan false)) [true,false,false] [true,false] [] [] [] []) =
      state none [] [true,false] [] [] [] [] (some true) := by
  simpa [bitsValue, Nat.bits, Nat.bit_val] using run [true,false,false] [true,false]

/-- Subtracting one from seven returns nonpalindromic little-endian six. -/
theorem order_control :
    ∃ fuel ≤ 17, tick^[fuel] (state (some (scan false)) [true,true,true] [true] [] [] [] []) =
      state none [] [true] [] [] [] [false,true,true] (some true) := by
  have hd : (6 : Nat).bits = [false,true,true] := by decide
  simpa [bitsValue, Nat.bit_val, hd] using run [true,true,true] [true]

/-- Remainder eight, next bit one, modulus eleven: 17 becomes six. -/
theorem remainder_control :
    ∃ fuel ≤ 33, tick^[fuel] (state (some (shift true)) [false,false,false,true] [true,true,false,true] [] [] [] []) =
      state none [] [true,true,false,true] [] [] [] [false,true,true] (some true) := by
  exact remainder_step 8 11 true (by decide)

/-- The zero shift is canonical and the no-subtraction branch retains it. -/
theorem zero_control :
    ∃ fuel ≤ 33, tick^[fuel] (state (some (shift false)) [] [true,true,false,true] [] [] [] []) =
      state none [] [true,true,false,true] [] [] [] [] (some false) := by
  exact remainder_step 0 11 false (by decide)

#print axioms supports
#print axioms run
#print axioms remainder_step
#print axioms borrow_control
#print axioms underflow_control
#print axioms equal_control
#print axioms order_control
#print axioms remainder_control
#print axioms zero_control
end ExplainableCrypto.Helios.Computational.BinarySubtractMachine
