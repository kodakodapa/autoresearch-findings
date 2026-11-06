import Programme.«20261101-0614-proof-complexity».SingletonPositive00
import Programme.«20261101-0614-proof-complexity».SingletonPositive01
import Programme.«20261101-0614-proof-complexity».SingletonPositive02
import Programme.«20261101-0614-proof-complexity».SingletonPositive03
import Programme.«20261101-0614-proof-complexity».SingletonPositive04
import Programme.«20261101-0614-proof-complexity».SingletonPositive05
import Programme.«20261101-0614-proof-complexity».SingletonPositive06
import Programme.«20261101-0614-proof-complexity».SingletonPositive07
import Programme.«20261101-0614-proof-complexity».SingletonPositive08
import Programme.«20261101-0614-proof-complexity».SingletonPositive09
import Programme.«20261101-0614-proof-complexity».SingletonPositive10
import Programme.«20261101-0614-proof-complexity».SingletonPositive11
import Programme.«20261101-0614-proof-complexity».SingletonPositive12
import Programme.«20261101-0614-proof-complexity».SingletonPositive13
import Programme.«20261101-0614-proof-complexity».SingletonPositive14
import Programme.«20261101-0614-proof-complexity».SingletonPositive15
import Programme.«20261101-0614-proof-complexity».SingletonPositive16
import Programme.«20261101-0614-proof-complexity».SingletonPositive17
import Programme.«20261101-0614-proof-complexity».SingletonPositive18
import Programme.«20261101-0614-proof-complexity».SingletonPositive19
import Programme.«20261101-0614-proof-complexity».SingletonPositive20
import Programme.«20261101-0614-proof-complexity».SingletonPositive21
import Programme.«20261101-0614-proof-complexity».SingletonPositive22
import Programme.«20261101-0614-proof-complexity».SingletonPositive23
import Programme.«20261101-0614-proof-complexity».SingletonPositive24
import Programme.«20261101-0614-proof-complexity».SingletonPositive25
import Programme.«20261101-0614-proof-complexity».SingletonPositive26
import Programme.«20261101-0614-proof-complexity».SingletonPositive27
import Programme.«20261101-0614-proof-complexity».SingletonPositive28
import Programme.«20261101-0614-proof-complexity».SingletonPositive29
import Programme.«20261101-0614-proof-complexity».SingletonPositive30
import Programme.«20261101-0614-proof-complexity».SingletonPositive31
import Programme.«20261101-0614-proof-complexity».SingletonPositive32
import Programme.«20261101-0614-proof-complexity».SingletonPositive33
import Programme.«20261101-0614-proof-complexity».SingletonPositive34
import Programme.«20261101-0614-proof-complexity».SingletonPositive35
import Programme.«20261101-0614-proof-complexity».SingletonPositive36
import Programme.«20261101-0614-proof-complexity».SingletonPositive37
import Programme.«20261101-0614-proof-complexity».SingletonPositive38
import Programme.«20261101-0614-proof-complexity».SingletonPositive39

namespace Programme.«20261101-0614-proof-complexity».SingletonFinite
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SingletonData Programme.«20261101-0614-proof-complexity».SignedDual
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem positive : ∀ m ∈ FiniteWords.words (FiniteWords.alphabet vars) 3,
    0 ≤ score weights m := by
  intro m hm
  change m ∈ ([[]] ++ (FiniteWords.alphabet vars).flatMap (fun l =>
    (FiniteWords.words (FiniteWords.alphabet vars) 2).map (l :: ·))) at hm
  simp only [List.mem_append, List.mem_singleton,
    List.mem_flatMap, List.mem_map] at hm
  rcases hm with rfl | ⟨l,hl,m,hm,rfl⟩
  · decide +kernel
  · simp only [FiniteWords.alphabet, vars, List.flatMap_cons, List.flatMap_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc] at hl
    rcases hl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst l; exact SingletonPositive00.checked m hm
    · subst l; exact SingletonPositive01.checked m hm
    · subst l; exact SingletonPositive02.checked m hm
    · subst l; exact SingletonPositive03.checked m hm
    · subst l; exact SingletonPositive04.checked m hm
    · subst l; exact SingletonPositive05.checked m hm
    · subst l; exact SingletonPositive06.checked m hm
    · subst l; exact SingletonPositive07.checked m hm
    · subst l; exact SingletonPositive08.checked m hm
    · subst l; exact SingletonPositive09.checked m hm
    · subst l; exact SingletonPositive10.checked m hm
    · subst l; exact SingletonPositive11.checked m hm
    · subst l; exact SingletonPositive12.checked m hm
    · subst l; exact SingletonPositive13.checked m hm
    · subst l; exact SingletonPositive14.checked m hm
    · subst l; exact SingletonPositive15.checked m hm
    · subst l; exact SingletonPositive16.checked m hm
    · subst l; exact SingletonPositive17.checked m hm
    · subst l; exact SingletonPositive18.checked m hm
    · subst l; exact SingletonPositive19.checked m hm
    · subst l; exact SingletonPositive20.checked m hm
    · subst l; exact SingletonPositive21.checked m hm
    · subst l; exact SingletonPositive22.checked m hm
    · subst l; exact SingletonPositive23.checked m hm
    · subst l; exact SingletonPositive24.checked m hm
    · subst l; exact SingletonPositive25.checked m hm
    · subst l; exact SingletonPositive26.checked m hm
    · subst l; exact SingletonPositive27.checked m hm
    · subst l; exact SingletonPositive28.checked m hm
    · subst l; exact SingletonPositive29.checked m hm
    · subst l; exact SingletonPositive30.checked m hm
    · subst l; exact SingletonPositive31.checked m hm
    · subst l; exact SingletonPositive32.checked m hm
    · subst l; exact SingletonPositive33.checked m hm
    · subst l; exact SingletonPositive34.checked m hm
    · subst l; exact SingletonPositive35.checked m hm
    · subst l; exact SingletonPositive36.checked m hm
    · subst l; exact SingletonPositive37.checked m hm
    · subst l; exact SingletonPositive38.checked m hm
    · subst l; exact SingletonPositive39.checked m hm

#print axioms positive
end Programme.«20261101-0614-proof-complexity».SingletonFinite
