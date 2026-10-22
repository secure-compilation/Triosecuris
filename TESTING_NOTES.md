# Testing notes

## Current generation produces programs with UB due to discrepancy in call stack

For example:

```
block 0 (callable):
   (0, 0)  store[0] <- (2 ? 0 : X3)
   (0, 1)  branch 2 to 4
   (0, 2)  jump 1
block 1:
   (1, 0)  X4 <- load[0]
   (1, 1)  store[1] <- 2
   (1, 2)  exit
block 2:
   (2, 0)  exit
block 3 (callable):
   (3, 0)  branch (X5 ? 1 : 2) to 1
   (3, 1)  X0 := X0
   (3, 2)  jump 4
block 4:
   (4, 0)  ret
block 5 (callable):
   (5, 0)  jump 6
block 6:
   (6, 0)  ret
block 7 (callable):
   (7, 0)  jump 2
block 8:
   (8, 0)  ret
```

This program would earlier terminate correctly due to `ret` in (4, 0), called after (0, 1). But now we distinguish between termination and return, caused by discrepancies in stack frames, and thus it gets stuck.