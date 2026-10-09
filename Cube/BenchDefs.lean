import Cube.Kph1
set_option compiler.extract_closed false
def benchScan (n : Nat) : Nat := Id.run do
  let mut d := ByteArray.emptyWithCapacity n
  for _ in [0:n] do d := d.push 255
  let mut c := 0
  for i in [0:n] do
    if d.get! i == 255 then c := c + 1
  return c
def benchNext (n : Nat) : Nat := Id.run do
  let mut c := 0
  for i in [0:n] do
    for m in [0:18] do
      c := c + next (i * 7919 % NN) m % 2
  return c
