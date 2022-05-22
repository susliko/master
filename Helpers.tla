---- MODULE Helpers ----
LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers

Range(f) == {f[x]: x \in DOMAIN f}

Heads(seqs) == {Head(s): s \in {s \in Range(seqs): Len(s) > 0}}

Matching(f, val) == CHOOSE x \in {x \in DOMAIN f: f[x] = val}: TRUE

Abs(number) == IF number < 0 THEN -1 * number ELSE number

=====
