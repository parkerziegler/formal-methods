bit s = 0, g = 0, w = 0, c = 0
ltl river_crossing_invariants {
  [] (w == g || c == g -> g == s) &&
  <> (s == g && g == w && w == c && c == 1)
}

proctype RiverCross() {
  do
  :: (s == g) -> atomic { s = 1 - s; g = 1 - g }
  :: (s == w && g != c) -> atomic { s = 1 - s; w = 1 - w }
  :: (s == c && g != w) -> atomic { s = 1 - s; c = 1 - c }
  :: (s == g && g == w && w == c && c == 1) -> skip
  od;
}

init {
  run RiverCross()
}