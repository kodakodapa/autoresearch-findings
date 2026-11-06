import Programme.«20261101-1618-proof-complexity».Lossy62Data
namespace Programme.«20261101-1618-proof-complexity».Lossy62Check16
open Programme.«20261101-1618-proof-complexity».Lossy62Data
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem forward : covered t16 source = true := by decide +kernel
theorem backward : covered s16 translated = true := by decide +kernel
end Programme.«20261101-1618-proof-complexity».Lossy62Check16
