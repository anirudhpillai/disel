From DiSeL.Core
Require Import DiSeLExtraction.
From DiSeL.Examples
Require Import SimplePaxosApp.

Cd "extraction".
  Cd "Paxos".
    Separate Extraction DepMaps.DepMaps.dmap init_state p_runner a_runner1 a_runner2 a_runner3.
  Cd "..".
Cd "..".
