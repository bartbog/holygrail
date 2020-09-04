\ Model MIPOptConstrHS
\ LP format - for model browsing. Use MPS format to capture full model detail.
Minimize
  20 x[0] + 20 x[1] + 20 x[2] + 20 x[3] + x[4] + 1e+100 x[5] + 1e+100 x[6]
   + 1e+100 x[7]
Subject To
 R0: x[7] + x[8] + x[9] = 1
 R1: x[0] + x[4] + x[8] + x[9] >= 1
 R2: x[2] + x[5] + x[7] + x[9] >= 1
 R3: x[3] + x[6] + x[7] + x[8] >= 1
 R4: x[1] + x[5] + x[6] + x[7] >= 1
Bounds
Binaries
 x[0] x[1] x[2] x[3] x[4] x[5] x[6] x[7] x[8] x[9]
End
