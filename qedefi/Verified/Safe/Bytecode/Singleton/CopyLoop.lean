import Verified.Safe.Bytecode.Singleton.Ctx

/-!
# The singleton's memory copy loops

solc 0.7.6 copies memory word by word in eight places of the singleton (ABI encoding of
`bytes`/arrays, return data): the same 27-byte loop
`for (i = 0; i < len; i += 32) mstore(dst + i, mload(src + i))`, with stack
`i, src, dst, len` at its head. `copy_h` (head `h`, exit `h + 27`): from the head, the frame
reaches the exit with the memory below `dst` unchanged, by induction on `len - i`.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable {msg : Message} {ctx : Context}
  {Halt : Prop} {G : World → Prop} {R : Machine → Prop} {K : Word → Prop}
  {C : Machine → CallRequest → Prop} {Dm D B : Machine → Prop}

set_option maxHeartbeats 4000000 in
theorem copy_2094 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 2094 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 2121 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [2094, 2121]
  · rw [iszero_eq_zero, lt_ne_zero] at hc2102
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_2285 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 2285 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 2312 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [2285, 2312]
  · rw [iszero_eq_zero, lt_ne_zero] at hc2293
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_3501 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 3501 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 3528 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [3501, 3528]
  · rw [iszero_eq_zero, lt_ne_zero] at hc3509
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_4348 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 4348 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 4375 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [4348, 4375]
  · rw [iszero_eq_zero, lt_ne_zero] at hc4356
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_5779 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 5779 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 5806 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [5779, 5806]
  · rw [iszero_eq_zero, lt_ne_zero] at hc5787
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_9949 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 9949 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 9976 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [9949, 9976]
  · rw [iszero_eq_zero, lt_ne_zero] at hc9957
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_17648 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 17648 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 17675 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [17648, 17675]
  · rw [iszero_eq_zero, lt_ne_zero] at hc17656
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

set_option maxHeartbeats 4000000 in
theorem copy_18381 :
    ∀ n (i a b len : Word) (rest : List Word) (mem : Memory) (w : World) (m : Machine),
      Fr (fix msg ctx) m 18381 (i :: a :: b :: len :: rest) mem w →
      len.toNat - i.toNat = n → b.toNat + len.toNat + 32 < 2 ^ 256 →
      (∀ (i' : Word) (mem' : Memory) (m' : Machine),
        Fr (fix msg ctx) m' 18408 (i' :: a :: b :: len :: rest) mem' w →
        (∀ o, o + 32 ≤ b.toNat → mem'.loadWord o = mem.loadWord o) →
        OwnB Halt G R (Own.SstoreOk K) C Dm D B m') →
      OwnB Halt G R (Own.SstoreOk K) C Dm D B m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i a b len rest mem w m hF hn hb hk
  own_explore [18381, 18408]
  · rw [iszero_eq_zero, lt_ne_zero] at hc18389
    have hi : (i + 32#256).toNat = i.toNat + 32 := toNat_add_of_lt (by simp; omega)
    have hbi : (b + i).toNat = b.toNat + i.toNat := toNat_add_of_lt (by omega)
    refine ih _ (by omega) (i + 32#256) a b len rest _ w m hF rfl hb
      fun i' mem' m' hF' hpres => hk i' mem' m' hF' fun o ho => (hpres o ho).trans ?_
    rw [Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl (by omega)), Memory.loadWord_expand,
      Memory.loadWord_expand]
  · exact hk i mem m hF fun _ _ => rfl

/-! ## Without bounds: by coinduction

When nothing bounds the length (the memory may have been overwritten), the loop may wrap
around; `copyC_h` proves the frame judgment from the head by an invariant, for any memory
after the loop. -/

set_option maxHeartbeats 4000000 in
theorem copyC_2094 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 2121 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 2094 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 2094 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [2094, 2121]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_2285 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 2312 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 2285 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 2285 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [2285, 2312]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_3501 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 3528 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 3501 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 3501 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [3501, 3528]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_4348 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 4375 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 4348 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 4348 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [4348, 4375]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_5779 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 5806 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 5779 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 5779 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [5779, 5806]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_9949 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 9976 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 9949 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 9949 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [9949, 9976]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_17648 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 17675 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 17648 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 17648 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [17648, 17675]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

set_option maxHeartbeats 4000000 in
theorem copyC_18381 {a b len : Word} {rest : List Word} {w : World}
    (hk : ∀ (i' : Word) (mem' : Memory) (m' : Machine),
      Fr (fix msg ctx) m' 18408 (i' :: a :: b :: len :: rest) mem' w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m') :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 18381 (i :: a :: b :: len :: rest) mem w →
      OwnG Halt G R (Own.SstoreOk K) C Dm D m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem, Fr (fix msg ctx) x 18381 (i :: a :: b :: len :: rest) mem w)
    ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  own_explore [18381, 18408]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · exact .leaf (.inr (hk _ _ _ hF))

end Dep

end Verified.Safe.Guard
