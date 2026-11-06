import Programme.«20261027-0607-proof-complexity».P7Chk0
import Programme.«20261027-0607-proof-complexity».P7Chk1
import Programme.«20261027-0607-proof-complexity».P7Chk2
import Programme.«20261027-0607-proof-complexity».P7Chk3
import Programme.«20261027-0607-proof-complexity».P7Chk4
import Programme.«20261027-0607-proof-complexity».P7Chk5
import Programme.«20261027-0607-proof-complexity».P7Chk6
import Programme.«20261027-0607-proof-complexity».P7Chk7

/-! The full kernel check `okT tree = true`, assembled from the chunk theorems `ok_t…`. -/

namespace Programme.«20261027-0607-proof-complexity».P7

set_option maxRecDepth 100000 in
theorem chk : okT tree = true := by
  have h : allT fT tree = true := by
    simp only [tree, allT, ok_t000000, ok_t000001, ok_t000010, ok_t000011, ok_t000100, ok_t000101, ok_t000110, ok_t000111, ok_t001000, ok_t001001, ok_t001010, ok_t001011, ok_t001100, ok_t001101, ok_t001110, ok_t001111, ok_t010000, ok_t010001, ok_t010010, ok_t010011, ok_t010100, ok_t010101, ok_t010110, ok_t010111, ok_t011000, ok_t011001, ok_t011010, ok_t011011, ok_t011100, ok_t011101, ok_t011110, ok_t011111, ok_t100000, ok_t100001, ok_t100010, ok_t100011, ok_t100100, ok_t100101, ok_t100110, ok_t100111, ok_t101000, ok_t101001, ok_t101010, ok_t101011, ok_t101100, ok_t101101, ok_t101110, ok_t101111, ok_t110000, ok_t110001, ok_t110010, ok_t110011, ok_t110100, ok_t110101, ok_t110110, ok_t110111, ok_t111000, ok_t111001, ok_t111010, ok_t111011, ok_t111100, ok_t111101, ok_t111110, ok_t111111, Bool.and_true, Bool.true_and]
    decide +kernel
  rw [allT_eq] at h
  exact h

end Programme.«20261027-0607-proof-complexity».P7
