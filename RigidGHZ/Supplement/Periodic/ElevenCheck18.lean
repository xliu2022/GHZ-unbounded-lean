module

public import RigidGHZ.Supplement.Periodic.ElevenCheck17

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_576 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 21} Certificate (by decide)
  decide

theorem node_577 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 21} Certificate (by decide)
    ?_ node_576
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 21} Certificate (by decide)
  decide

theorem node_578 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 26, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 26, 21} Certificate (by decide)
  decide

theorem node_579 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 21} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {26, 21} Certificate (by decide)
    ?_ node_578
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 21} Certificate (by decide)
  decide

theorem node_580 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 21} Certificate (by decide)
  decide

theorem node_581 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21} Certificate (by decide)
    ?_ node_573
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21} Certificate (by decide)
    ?_ node_575
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {21} Certificate (by decide)
    ?_ node_577
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {21} Certificate (by decide)
    ?_ node_579
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {21} Certificate (by decide)
    ?_ node_580
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21} Certificate (by decide)
  decide

theorem node_582 :
    (scheme.enumerateFrom [30, 31, 32] {29, 23, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 23, 22} Certificate (by decide)
  decide

theorem node_583 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {23, 22} Certificate (by decide)
    ?_ node_582
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 22} Certificate (by decide)
  decide

theorem node_584 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 24, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 24, 22} Certificate (by decide)
  decide

theorem node_585 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 24, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 24, 22} Certificate (by decide)
    ?_ node_584
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 24, 22} Certificate (by decide)
  decide

theorem node_586 :
    (scheme.enumerateFrom [30, 31, 32] {29, 24, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 24, 22} Certificate (by decide)
  decide

theorem node_587 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 22} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {24, 22} Certificate (by decide)
    ?_ node_585
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 22} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {24, 22} Certificate (by decide)
    ?_ node_586
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 22} Certificate (by decide)
  decide

theorem node_588 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 22} Certificate (by decide)
  decide

theorem node_589 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 22} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 22} Certificate (by decide)
    ?_ node_588
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 22} Certificate (by decide)
  decide

theorem node_590 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22} Certificate (by decide)
  decide

theorem node_591 :
    (scheme.enumerateFrom [31, 32] {30, 22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 22} Certificate (by decide)
  decide

theorem node_592 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22} Certificate (by decide)
    ?_ node_583
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {22} Certificate (by decide)
    ?_ node_587
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {22} Certificate (by decide)
    ?_ node_589
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22} Certificate (by decide)
    ?_ node_590
  apply scheme.check_enumeration_split 30 [31, 32] {22} Certificate (by decide)
    ?_ node_591
  apply scheme.check_enumeration_skip 31 [32] {22} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22} Certificate (by decide)
  decide

theorem node_593 :
    (scheme.enumerateFrom [] {32, 25, 23}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_594 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 23}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 23} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {25, 23} Certificate (by decide)
    ?_ node_593
  decide

theorem node_595 :
    (scheme.enumerateFrom [] {32, 29, 23}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_596 :
    (scheme.enumerateFrom [30, 31, 32] {29, 23}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 23} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 23} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 23} Certificate (by decide)
    ?_ node_595
  decide

theorem node_597 :
    (scheme.enumerateFrom [] {32, 23}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_598 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {23} Certificate (by decide)
    ?_ node_594
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {23} Certificate (by decide)
    ?_ node_596
  apply scheme.check_enumeration_skip 30 [31, 32] {23} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {23} Certificate (by decide)
    ?_ node_597
  decide

theorem node_599 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 24} Certificate (by decide)
  decide

theorem node_600 :
    (scheme.enumerateFrom [] {32, 25, 24}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_601 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 24} Certificate (by decide)
    ?_ node_599
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 24} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {25, 24} Certificate (by decide)
    ?_ node_600
  decide

theorem node_602 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 24} Certificate (by decide)
  decide

theorem node_603 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 24} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 24} Certificate (by decide)
    ?_ node_602
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 24} Certificate (by decide)
  decide

theorem node_604 :
    (scheme.enumerateFrom [] {32, 29, 24}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_605 :
    (scheme.enumerateFrom [30, 31, 32] {29, 24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 24} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 24} Certificate (by decide)
    ?_ node_604
  decide

theorem node_606 :
    (scheme.enumerateFrom [] {32, 24}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_607 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {24} Certificate (by decide)
    ?_ node_601
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {24} Certificate (by decide)
    ?_ node_603
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {24} Certificate (by decide)
    ?_ node_605
  apply scheme.check_enumeration_skip 30 [31, 32] {24} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {24} Certificate (by decide)
    ?_ node_606
  decide

end RigidGHZ.Supplement.Periodic.Eleven
