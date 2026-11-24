module

public import RigidGHZ.Supplement.Periodic.ElevenBitData
public import RigidGHZ.Supplement.Periodic.BitOutput

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem output_019 : bits.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ 0 0 = [{31, 30}, {32, 31, 30}, {30, 28}, {32, 30, 28}, {31, 27}, {28, 27}, {29, 28, 27}, {24}, {32, 24}, {29, 24}, {32, 29, 24}, {26, 24}, {29, 26, 24}, {25, 24}, {32, 25, 24}, {26, 25, 24}, {24, 22}, {29, 24, 22}, {26, 24, 22}, {29, 26, 24, 22}, {28, 21}, {28, 26, 21}, {23, 21}, {25, 23, 21}, {23, 22, 21}, {30, 20}, {32, 30, 20}, {27, 20}, {29, 27, 20}, {21, 20}, {26, 21, 20}, {30, 28, 19}, {24, 19}, {26, 24, 19}, {25, 24, 19}, {26, 25, 24, 19}, {30, 20, 19}] := by decide

theorem output_020 : bits.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18} 65 8 = [{31, 18}, {28, 18}, {29, 28, 18}, {20, 18}, {29, 20, 18}, {28, 19, 18}, {20, 19, 18}] := by decide

theorem output_021 : bits.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} 256 96 = [{30, 28, 17}, {24, 17}, {26, 24, 17}, {25, 24, 17}, {26, 25, 24, 17}, {30, 20, 17}, {28, 18, 17}, {20, 18, 17}] := by decide

theorem output_022 : bits.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} 134 0 = [{24, 16}, {29, 24, 16}, {23, 21, 16}, {24, 19, 16}, {24, 17, 16}] := by decide

end RigidGHZ.Supplement.Periodic.Eleven
