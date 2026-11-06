import Programme.«20261101-0614-proof-complexity».Singleton
import Programme.«20261101-0614-proof-complexity».FiniteWords

namespace Programme.«20261101-0614-proof-complexity».SingletonData
open Programme.«20261031-2024-proof-complexity».NativeIter
open Programme.«20261101-0614-proof-complexity».SignedDual
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def vars : List Var := [(0,0), (0,1), (1,0), (1,1), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (2,0), (2,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8)]

def point (mask : Nat) : Assignment := fun v =>
  if v.1 = 0 then v.2 < 2 && mask.testBit v.2
  else v.1 ≤ 2 && v.2 < 9 && mask.testBit (2 + (v.1-1)*9 + v.2)

def weights : List (Int × Nat) := [
  (353, 0),
  (177, 1),
  (-361, 2),
  (-1, 5),
  (-111, 8),
  (-101, 9),
  (-54, 10),
  (-61, 16),
  (-8, 17),
  (63, 18),
  (162, 32),
  (-431, 33),
  (52, 37),
  (-28, 40),
  (80, 41),
  (3, 49),
  (-26, 64),
  (-7, 65),
  (37, 66),
  (12, 73),
  (5, 81),
  (-30, 128),
  (37, 130),
  (7, 136),
  (7, 144),
  (2, 146),
  (14, 256),
  (-48, 257),
  (14, 265),
  (-14, 288),
  (66, 289),
  (14, 512),
  (-48, 513),
  (14, 521),
  (-14, 544),
  (66, 545),
  (-222, 1024),
  (-61, 1025),
  (70, 1026),
  (31, 1032),
  (14, 1033),
  (22, 1041),
  (-14, 1056),
  (66, 1057),
  (2, 1089),
  (7, 1153),
  (5, 2050),
  (12, 2058),
  (5, 2066),
  (5, 2114),
  (10, 2178),
  (-68, 4096),
  (-47, 4097),
  (-15, 4098),
  (60, 4104),
  (19, 4105),
  (-80, 4128),
  (68, 4129),
  (2, 4160),
  (5, 4353),
  (5, 4609),
  (66, 5120),
  (2, 5121),
  (-42, 8192),
  (19, 8193),
  (33, 8194),
  (12, 8200),
  (7, 8208),
  (2, 8320),
  (2, 9216),
  (52, 16386),
  (-11, 32768),
  (-13, 32769),
  (-122, 32770),
  (1, 32773),
  (60, 32778),
  (18, 32784),
  (-76, 32800),
  (64, 32801),
  (7, 32896),
  (10, 32898),
  (66, 33792),
  (15, 34818),
  (-100, 36864),
  (66, 36866),
  (3, 36880),
  (64, 36896),
  (-86, 65536),
  (-14, 65537),
  (13, 65538),
  (12, 65544),
  (4, 65552),
  (18, 65569),
  (12, 65600),
  (5, 65602),
  (15, 65793),
  (15, 66049),
  (2, 66560),
  (17, 66568),
  (20, 69632),
  (19, 73728),
  (52, 131074),
  (18, 163842),
  (-8, 262146),
  (12, 262154),
  (3, 262162),
  (5, 262210),
  (10, 262274),
  (15, 264194),
  (15, 266242),
  (33, 294914),
  (-24, 524288),
  (-200, 524289),
  (-135, 524290),
  (19, 524293),
  (-28, 524296),
  (47, 524297),
  (30, 524298),
  (22, 524304),
  (-98, 524320),
  (99, 524321),
  (28, 524328),
  (12, 524352),
  (23, 524354),
  (7, 524416),
  (11, 524418),
  (-14, 524544),
  (33, 524545),
  (14, 524576),
  (-14, 524800),
  (33, 524801),
  (14, 524832),
  (38, 525312),
  (33, 525313),
  (14, 525344),
  (18, 526338),
  (-16, 528384),
  (35, 528385),
  (16, 528416),
  (35, 532482),
  (18, 540674),
  (-16, 557056),
  (19, 557057),
  (12, 557088),
  (33, 561152),
  (52, 589826)]

def samples : List Sample := weights.map fun s => ((s.1 : Rat) * (1 / 325), point s.2)

def score (ws : List (Int × Nat)) (m : List Lit) : Int :=
  (ws.map fun s => if m.all (holds (point s.2)) then s.1 else 0).sum

theorem eval_score (ws : List (Int × Nat)) (m : List Lit) :
    evaluate (ws.map fun s => ((s.1 : Rat) * (1 / 325), point s.2)) (conjunction m) =
      (score ws m : Rat) * (1 / 325) := by
  induction ws with
  | nil => simp [evaluate, score]
  | cons s ss ih =>
    simp only [List.map_cons, evaluate, List.sum_cons] at *
    rw [ih]
    simp only [score, List.map_cons, List.sum_cons, Rat.intCast_add, Rat.add_mul]
    congr 1
    unfold conjunction
    split <;> simp

theorem positive_one : ∀ m ∈ FiniteWords.words (FiniteWords.alphabet vars) 1,
    0 ≤ score weights m := by decide +kernel

#print axioms eval_score
end Programme.«20261101-0614-proof-complexity».SingletonData
