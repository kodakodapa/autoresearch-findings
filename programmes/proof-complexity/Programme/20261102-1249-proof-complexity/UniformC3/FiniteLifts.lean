import Programme.«20261102-1249-proof-complexity».UniformC3.Finite2Data
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row0
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row1
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row2
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row3
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row4
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row5
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row6
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row7
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row8
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row9
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row10
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row11
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row12
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row13
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row14
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row15
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row16
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row17
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row18
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row19
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row20
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row21
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row22
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row23
import Programme.«20261102-1249-proof-complexity».UniformC3.Finite3Row24

namespace Programme.«20261102-1249-proof-complexity».UniformC3
open Programme.«20261026-1402-proof-complexity».ExtLemma

theorem squareCheck3 (a b : Fin 25) : SquareCheck3 a b := by
  rcases a with ⟨a,ha⟩
  match a with
  | 0 => exact squareCheck3_0 b
  | 1 => exact squareCheck3_1 b
  | 2 => exact squareCheck3_2 b
  | 3 => exact squareCheck3_3 b
  | 4 => exact squareCheck3_4 b
  | 5 => exact squareCheck3_5 b
  | 6 => exact squareCheck3_6 b
  | 7 => exact squareCheck3_7 b
  | 8 => exact squareCheck3_8 b
  | 9 => exact squareCheck3_9 b
  | 10 => exact squareCheck3_10 b
  | 11 => exact squareCheck3_11 b
  | 12 => exact squareCheck3_12 b
  | 13 => exact squareCheck3_13 b
  | 14 => exact squareCheck3_14 b
  | 15 => exact squareCheck3_15 b
  | 16 => exact squareCheck3_16 b
  | 17 => exact squareCheck3_17 b
  | 18 => exact squareCheck3_18 b
  | 19 => exact squareCheck3_19 b
  | 20 => exact squareCheck3_20 b
  | 21 => exact squareCheck3_21 b
  | 22 => exact squareCheck3_22 b
  | 23 => exact squareCheck3_23 b
  | 24 => exact squareCheck3_24 b
  | a+25 => omega

def integralLift2 : IntegralLift 2 where
  coeff := squareCoeff2
  unit := fun g _ _ => squareCoeff2_unit g
  harmonic := by
    intro g hg hl
    obtain ⟨a,rfl⟩ : ∃ a, g = [a] := by
      match g, hl with
      | [a], _ => exact ⟨a,rfl⟩
    have ha : a < 9 := CM_lt hg (by simp)
    have h := squareCheck2 ⟨a,ha⟩
    constructor
    · intro i hi hf
      exact h.1 ⟨i,hi⟩ hf
    · intro j hj hf
      exact h.2 ⟨j,hj⟩ hf

def integralLift3 : IntegralLift 3 where
  coeff := squareCoeff3
  unit := fun g _ _ => squareCoeff3_unit g
  harmonic := by
    intro g hg hl
    obtain ⟨a,b,rfl⟩ : ∃ a b, g = [a,b] := by
      match g, hl with
      | [a,b], _ => exact ⟨a,b,rfl⟩
    have ha : a < 25 := CM_lt hg (by simp)
    have hb : b < 25 := CM_lt hg (by simp)
    have hab : a ≠ b := by
      have h := CM_nodup hg
      simpa using h
    have h := squareCheck3 ⟨a,ha⟩ ⟨b,hb⟩ hab hg.2
    constructor
    · intro i hi hf
      exact h.1 ⟨i,hi⟩ hf
    · intro j hj hf
      exact h.2 ⟨j,hj⟩ hf

#print axioms integralLift2
#print axioms integralLift3
end Programme.«20261102-1249-proof-complexity».UniformC3
