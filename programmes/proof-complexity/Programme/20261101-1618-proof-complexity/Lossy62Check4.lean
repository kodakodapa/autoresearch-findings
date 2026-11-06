import Programme.«20261101-1618-proof-complexity».Lossy62Data
namespace Programme.«20261101-1618-proof-complexity».Lossy62Check4
open Programme.«20261101-1618-proof-complexity».Lossy62Data
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem forward : covered t4 source = true := by decide +kernel
theorem backward : covered s4 translated = true := by decide +kernel
end Programme.«20261101-1618-proof-complexity».Lossy62Check4
