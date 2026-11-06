import Programme.«20261101-1618-proof-complexity».Lossy42Norm0
import Programme.«20261101-1618-proof-complexity».Lossy42Norm1
import Programme.«20261101-1618-proof-complexity».Lossy42Norm2
import Programme.«20261101-1618-proof-complexity».Lossy42Norm3
import Programme.«20261101-1618-proof-complexity».Lossy42Norm4
import Programme.«20261101-1618-proof-complexity».Lossy42Norm5
import Programme.«20261101-1618-proof-complexity».Lossy42Norm6
import Programme.«20261101-1618-proof-complexity».Lossy42Norm7
import Programme.«20261101-1618-proof-complexity».Lossy42Norm8
import Programme.«20261101-1618-proof-complexity».Lossy42Norm9
import Programme.«20261101-1618-proof-complexity».Lossy42Norm10
import Programme.«20261101-1618-proof-complexity».Lossy42Norm11
import Programme.«20261101-1618-proof-complexity».Lossy42Norm12
import Programme.«20261101-1618-proof-complexity».Lossy42Norm13
import Programme.«20261101-1618-proof-complexity».Lossy42Norm14
import Programme.«20261101-1618-proof-complexity».Lossy42Norm15
import Programme.«20261101-1618-proof-complexity».Lossy42Norm16
import Programme.«20261101-1618-proof-complexity».Lossy42Norm17
import Programme.«20261101-1618-proof-complexity».Lossy42Norm18
import Programme.«20261101-1618-proof-complexity».Lossy42Norm19
import Programme.«20261101-1618-proof-complexity».Lossy42Norm20
import Programme.«20261101-1618-proof-complexity».Lossy42Norm21
import Programme.«20261101-1618-proof-complexity».Lossy42Norm22
import Programme.«20261101-1618-proof-complexity».Lossy42Norm23
import Programme.«20261101-1618-proof-complexity».Lossy42Norm24
import Programme.«20261101-1618-proof-complexity».Lossy42Norm25
import Programme.«20261101-1618-proof-complexity».Lossy42Norm26
import Programme.«20261101-1618-proof-complexity».Lossy42Norm27
import Programme.«20261101-1618-proof-complexity».Lossy42Norm28
import Programme.«20261101-1618-proof-complexity».Lossy42Norm29
import Programme.«20261101-1618-proof-complexity».Lossy42Norm30
import Programme.«20261101-1618-proof-complexity».Lossy42Norm31
import Programme.«20261101-1618-proof-complexity».Lossy42Norm32
import Programme.«20261101-1618-proof-complexity».Lossy42Norm33
import Programme.«20261101-1618-proof-complexity».Lossy42Norm34
import Programme.«20261101-1618-proof-complexity».Lossy42Norm35
import Programme.«20261101-1618-proof-complexity».Lossy42Norm36
import Programme.«20261101-1618-proof-complexity».Lossy42Norm37
import Programme.«20261101-1618-proof-complexity».Lossy42Norm38
import Programme.«20261101-1618-proof-complexity».Lossy42Norm39
import Programme.«20261101-1618-proof-complexity».Lossy42Norm40
import Programme.«20261101-1618-proof-complexity».Lossy42Norm41
import Programme.«20261101-1618-proof-complexity».Lossy42Norm42
import Programme.«20261101-1618-proof-complexity».Lossy42Norm43
import Programme.«20261101-1618-proof-complexity».Lossy42Norm44
import Programme.«20261101-1618-proof-complexity».Lossy42Norm45
import Programme.«20261101-1618-proof-complexity».Lossy42Norm46
import Programme.«20261101-1618-proof-complexity».Lossy42Norm47
namespace Programme.«20261101-1618-proof-complexity».Lossy42Upper
open Programme.«20261101-1618-proof-complexity».Lossy42Norm Programme.«20261101-1618-proof-complexity».BooleanPolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem eval_append (c d : LinearCertificate.Certificate) (a) :
    LinearCertificate.eval (c ++ d) a = LinearCertificate.eval c a + LinearCertificate.eval d a := by
  simp only [LinearCertificate.eval, List.map_append, List.sum_append]
 theorem certificate_identity : ∀ a,
    LinearCertificate.eval Lossy42Data.cert a = -1 := by
  intro a
  have s0 : peval p0 a + peval a1 a = peval a0 a := by
    have h := congrArg (fun p => peval p a) step0
    rw [add_eval] at h
    exact h
  have s1 : peval p1 a + peval a2 a = peval a1 a := by
    have h := congrArg (fun p => peval p a) step1
    rw [add_eval] at h
    exact h
  have s2 : peval p2 a + peval a3 a = peval a2 a := by
    have h := congrArg (fun p => peval p a) step2
    rw [add_eval] at h
    exact h
  have s3 : peval p3 a + peval a4 a = peval a3 a := by
    have h := congrArg (fun p => peval p a) step3
    rw [add_eval] at h
    exact h
  have s4 : peval p4 a + peval a5 a = peval a4 a := by
    have h := congrArg (fun p => peval p a) step4
    rw [add_eval] at h
    exact h
  have s5 : peval p5 a + peval a6 a = peval a5 a := by
    have h := congrArg (fun p => peval p a) step5
    rw [add_eval] at h
    exact h
  have s6 : peval p6 a + peval a7 a = peval a6 a := by
    have h := congrArg (fun p => peval p a) step6
    rw [add_eval] at h
    exact h
  have s7 : peval p7 a + peval a8 a = peval a7 a := by
    have h := congrArg (fun p => peval p a) step7
    rw [add_eval] at h
    exact h
  have s8 : peval p8 a + peval a9 a = peval a8 a := by
    have h := congrArg (fun p => peval p a) step8
    rw [add_eval] at h
    exact h
  have s9 : peval p9 a + peval a10 a = peval a9 a := by
    have h := congrArg (fun p => peval p a) step9
    rw [add_eval] at h
    exact h
  have s10 : peval p10 a + peval a11 a = peval a10 a := by
    have h := congrArg (fun p => peval p a) step10
    rw [add_eval] at h
    exact h
  have s11 : peval p11 a + peval a12 a = peval a11 a := by
    have h := congrArg (fun p => peval p a) step11
    rw [add_eval] at h
    exact h
  have s12 : peval p12 a + peval a13 a = peval a12 a := by
    have h := congrArg (fun p => peval p a) step12
    rw [add_eval] at h
    exact h
  have s13 : peval p13 a + peval a14 a = peval a13 a := by
    have h := congrArg (fun p => peval p a) step13
    rw [add_eval] at h
    exact h
  have s14 : peval p14 a + peval a15 a = peval a14 a := by
    have h := congrArg (fun p => peval p a) step14
    rw [add_eval] at h
    exact h
  have s15 : peval p15 a + peval a16 a = peval a15 a := by
    have h := congrArg (fun p => peval p a) step15
    rw [add_eval] at h
    exact h
  have s16 : peval p16 a + peval a17 a = peval a16 a := by
    have h := congrArg (fun p => peval p a) step16
    rw [add_eval] at h
    exact h
  have s17 : peval p17 a + peval a18 a = peval a17 a := by
    have h := congrArg (fun p => peval p a) step17
    rw [add_eval] at h
    exact h
  have s18 : peval p18 a + peval a19 a = peval a18 a := by
    have h := congrArg (fun p => peval p a) step18
    rw [add_eval] at h
    exact h
  have s19 : peval p19 a + peval a20 a = peval a19 a := by
    have h := congrArg (fun p => peval p a) step19
    rw [add_eval] at h
    exact h
  have s20 : peval p20 a + peval a21 a = peval a20 a := by
    have h := congrArg (fun p => peval p a) step20
    rw [add_eval] at h
    exact h
  have s21 : peval p21 a + peval a22 a = peval a21 a := by
    have h := congrArg (fun p => peval p a) step21
    rw [add_eval] at h
    exact h
  have s22 : peval p22 a + peval a23 a = peval a22 a := by
    have h := congrArg (fun p => peval p a) step22
    rw [add_eval] at h
    exact h
  have s23 : peval p23 a + peval a24 a = peval a23 a := by
    have h := congrArg (fun p => peval p a) step23
    rw [add_eval] at h
    exact h
  have s24 : peval p24 a + peval a25 a = peval a24 a := by
    have h := congrArg (fun p => peval p a) step24
    rw [add_eval] at h
    exact h
  have s25 : peval p25 a + peval a26 a = peval a25 a := by
    have h := congrArg (fun p => peval p a) step25
    rw [add_eval] at h
    exact h
  have s26 : peval p26 a + peval a27 a = peval a26 a := by
    have h := congrArg (fun p => peval p a) step26
    rw [add_eval] at h
    exact h
  have s27 : peval p27 a + peval a28 a = peval a27 a := by
    have h := congrArg (fun p => peval p a) step27
    rw [add_eval] at h
    exact h
  have s28 : peval p28 a + peval a29 a = peval a28 a := by
    have h := congrArg (fun p => peval p a) step28
    rw [add_eval] at h
    exact h
  have s29 : peval p29 a + peval a30 a = peval a29 a := by
    have h := congrArg (fun p => peval p a) step29
    rw [add_eval] at h
    exact h
  have s30 : peval p30 a + peval a31 a = peval a30 a := by
    have h := congrArg (fun p => peval p a) step30
    rw [add_eval] at h
    exact h
  have s31 : peval p31 a + peval a32 a = peval a31 a := by
    have h := congrArg (fun p => peval p a) step31
    rw [add_eval] at h
    exact h
  have s32 : peval p32 a + peval a33 a = peval a32 a := by
    have h := congrArg (fun p => peval p a) step32
    rw [add_eval] at h
    exact h
  have s33 : peval p33 a + peval a34 a = peval a33 a := by
    have h := congrArg (fun p => peval p a) step33
    rw [add_eval] at h
    exact h
  have s34 : peval p34 a + peval a35 a = peval a34 a := by
    have h := congrArg (fun p => peval p a) step34
    rw [add_eval] at h
    exact h
  have s35 : peval p35 a + peval a36 a = peval a35 a := by
    have h := congrArg (fun p => peval p a) step35
    rw [add_eval] at h
    exact h
  have s36 : peval p36 a + peval a37 a = peval a36 a := by
    have h := congrArg (fun p => peval p a) step36
    rw [add_eval] at h
    exact h
  have s37 : peval p37 a + peval a38 a = peval a37 a := by
    have h := congrArg (fun p => peval p a) step37
    rw [add_eval] at h
    exact h
  have s38 : peval p38 a + peval a39 a = peval a38 a := by
    have h := congrArg (fun p => peval p a) step38
    rw [add_eval] at h
    exact h
  have s39 : peval p39 a + peval a40 a = peval a39 a := by
    have h := congrArg (fun p => peval p a) step39
    rw [add_eval] at h
    exact h
  have s40 : peval p40 a + peval a41 a = peval a40 a := by
    have h := congrArg (fun p => peval p a) step40
    rw [add_eval] at h
    exact h
  have s41 : peval p41 a + peval a42 a = peval a41 a := by
    have h := congrArg (fun p => peval p a) step41
    rw [add_eval] at h
    exact h
  have s42 : peval p42 a + peval a43 a = peval a42 a := by
    have h := congrArg (fun p => peval p a) step42
    rw [add_eval] at h
    exact h
  have s43 : peval p43 a + peval a44 a = peval a43 a := by
    have h := congrArg (fun p => peval p a) step43
    rw [add_eval] at h
    exact h
  have s44 : peval p44 a + peval a45 a = peval a44 a := by
    have h := congrArg (fun p => peval p a) step44
    rw [add_eval] at h
    exact h
  have s45 : peval p45 a + peval a46 a = peval a45 a := by
    have h := congrArg (fun p => peval p a) step45
    rw [add_eval] at h
    exact h
  have s46 : peval p46 a + peval a47 a = peval a46 a := by
    have h := congrArg (fun p => peval p a) step46
    rw [add_eval] at h
    exact h
  have s47 : peval p47 a + peval b47 a = peval a47 a := by
    have h := congrArg (fun p => peval p a) step47
    rw [add_eval] at h
    exact h
  have h : LinearCertificate.eval Lossy42Data.cert a + 1 = 0 := by
    simp only [Lossy42Data.cert, eval_append]
    rw [← cert_eval Lossy42Data.part0 a, p0_correct, ← cert_eval Lossy42Data.part1 a, p1_correct, ← cert_eval Lossy42Data.part2 a, p2_correct, ← cert_eval Lossy42Data.part3 a, p3_correct, ← cert_eval Lossy42Data.part4 a, p4_correct, ← cert_eval Lossy42Data.part5 a, p5_correct, ← cert_eval Lossy42Data.part6 a, p6_correct, ← cert_eval Lossy42Data.part7 a, p7_correct, ← cert_eval Lossy42Data.part8 a, p8_correct, ← cert_eval Lossy42Data.part9 a, p9_correct, ← cert_eval Lossy42Data.part10 a, p10_correct, ← cert_eval Lossy42Data.part11 a, p11_correct, ← cert_eval Lossy42Data.part12 a, p12_correct, ← cert_eval Lossy42Data.part13 a, p13_correct, ← cert_eval Lossy42Data.part14 a, p14_correct, ← cert_eval Lossy42Data.part15 a, p15_correct, ← cert_eval Lossy42Data.part16 a, p16_correct, ← cert_eval Lossy42Data.part17 a, p17_correct, ← cert_eval Lossy42Data.part18 a, p18_correct, ← cert_eval Lossy42Data.part19 a, p19_correct, ← cert_eval Lossy42Data.part20 a, p20_correct, ← cert_eval Lossy42Data.part21 a, p21_correct, ← cert_eval Lossy42Data.part22 a, p22_correct, ← cert_eval Lossy42Data.part23 a, p23_correct, ← cert_eval Lossy42Data.part24 a, p24_correct, ← cert_eval Lossy42Data.part25 a, p25_correct, ← cert_eval Lossy42Data.part26 a, p26_correct, ← cert_eval Lossy42Data.part27 a, p27_correct, ← cert_eval Lossy42Data.part28 a, p28_correct, ← cert_eval Lossy42Data.part29 a, p29_correct, ← cert_eval Lossy42Data.part30 a, p30_correct, ← cert_eval Lossy42Data.part31 a, p31_correct, ← cert_eval Lossy42Data.part32 a, p32_correct, ← cert_eval Lossy42Data.part33 a, p33_correct, ← cert_eval Lossy42Data.part34 a, p34_correct, ← cert_eval Lossy42Data.part35 a, p35_correct, ← cert_eval Lossy42Data.part36 a, p36_correct, ← cert_eval Lossy42Data.part37 a, p37_correct, ← cert_eval Lossy42Data.part38 a, p38_correct, ← cert_eval Lossy42Data.part39 a, p39_correct, ← cert_eval Lossy42Data.part40 a, p40_correct, ← cert_eval Lossy42Data.part41 a, p41_correct, ← cert_eval Lossy42Data.part42 a, p42_correct, ← cert_eval Lossy42Data.part43 a, p43_correct, ← cert_eval Lossy42Data.part44 a, p44_correct, ← cert_eval Lossy42Data.part45 a, p45_correct, ← cert_eval Lossy42Data.part46 a, p46_correct, ← cert_eval Lossy42Data.part47 a, p47_correct]
    have hb : (1 : Rat) = peval b47 a := by
      simp only [b47, peval, meval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_nil, ↓reduceIte, Rat.mul_one, Rat.add_zero]
      decide +kernel
    rw [hb]
    simp only [Rat.add_assoc]
    rw [s47, s46, s45, s44, s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0]
    rfl
  have he := congrArg (fun r : Rat => r + (-1)) h
  simpa only [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add] using he
 theorem refutes : ClauseLinear.Refutes (LossySource.cnf 2 4 2) 3 :=
  LinearCertificate.refutes Lossy42Data.cert_valid certificate_identity
#print axioms certificate_identity
#print axioms refutes
end Programme.«20261101-1618-proof-complexity».Lossy42Upper
