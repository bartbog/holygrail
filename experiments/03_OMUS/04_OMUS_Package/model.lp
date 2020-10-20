\ Model MIPOptConstrHS
\ LP format - for model browsing. Use MPS format to capture full model detail.
Minimize
  2 x[0] + 2 x[1] + 3 x[2] + 3 x[3] + 3 x[4] + 3 x[5] + x[6] + 3 x[7]
   + 4 x[8] + 2 x[9] + 1e+100 x[10] + 1e+100 x[11] + x[12] + 1e+100 x[13]
   + 1e+100 x[14] + 1e+100 x[17]
Subject To
 R0: x[15] + x[16] + x[17] + x[18] + x[19] = 1
 R1: x[0] + x[1] + x[2] + x[3] + x[4] + x[5] + x[6] + x[7] + x[8] + x[9]
   >= 1
 R2: x[10] + x[11] + x[17] + x[18] + x[19] >= 1
 R3: x[10] + x[11] + x[17] + x[18] + x[19] >= 1
 R4: x[6] + x[10] + x[11] + x[12] + x[18] + x[19] >= 1
 R5: x[10] + x[11] + x[13] + x[17] + x[19] >= 1
 R6: x[10] + x[11] + x[14] + x[17] + x[18] >= 1
Bounds
Binaries
 x[0] x[1] x[2] x[3] x[4] x[5] x[6] x[7] x[8] x[9] x[10] x[11] x[12] x[13]
 x[14] x[15] x[16] x[17] x[18] x[19]
End
