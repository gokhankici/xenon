#!/usr/bin/env python3

from pytimeparse.timeparse import timeparse
from datetime import timedelta

times = [ ("MIPS"     , "2.42"       , "3.13")
        , ("RISC-V"   , "13.21"      , "10.23")
        , ("SHA-256"  , "7.21"       , "8.90")
        , ("FPU"      , "9.10"       , "11.54")
        , ("ALU"      , "2.01"       , "2.29")
        , ("FPU2"     , "1.31"       , "3.65")
        , ("RSA"      , "2.87"       , "1.51")
        , ("AES-256"  , "6:05:01.82" , "2.74")
        , ("SCARV"    , "14:20.93"   , "8:35.46")
        ]

def parse_time(s):
    t = timeparse(s)
    if t:
        return t
    else:
        return float(s)

def sec_to_delta(n):
    m0, s = divmod(n, 60)
    h, m = divmod(m0, 60)
    return timedelta(seconds=s, minutes=m, hours=h)

tsum1, tsum2 = 0, 0

for n, s1, s2 in times:
    t1 = parse_time(s1)
    t2 = parse_time(s2)
    tsum1 += t1
    tsum2 += t2

    print(f"{n:<10} {t1:>10} {t2:>10} {((t1 - t2) / t1):>7.4}")

print('-' * 80)

print("{0}    {1}".format(sec_to_delta(tsum1), sec_to_delta(tsum2)))