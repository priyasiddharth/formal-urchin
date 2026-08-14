# Correction: fail-test conformance counts were overstated by 2

[OBS 2026-08-14] The per-milestone fail-test counts reported today were
each 2 too high: the true progression is 21/75 (initial suite) → 25/75
(protectors + statics) → 33/75 (enums + dealloc/Box), all verified by
counting `status == supported` fail entries in conformance/manifest.json.
The suite pass totals (30 / 34 / 42) were always correct — the error was
only in my running "N/75" tally, which double-counted two entries when
summarizing. Why I was misled: I updated the headline number
incrementally in prose instead of recounting from the manifest; the
manifest itself was always right.

Corrected claims live in conformance/README.md (33/75, 29 line-accurate,
9 pass scenarios, 67 unsupported). Superseded figures are marked in
[[2026-08-14-obseq3-conformance-landed]] and
[[2026-08-14-protectors-and-statics-landed]].
